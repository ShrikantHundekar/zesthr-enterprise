"""Payroll calculation.

    net = basic - deduction + overtime_pay

Per-day pay is the basic salary divided by the calendar days of the month; a half
day counts as 0.5 absent day; the deduction never exceeds the basic salary.

Overtime pay (employees whose schedule is overtime-eligible only):

    hourly rate  = per-day pay / paid hours of a normal shift
    overtime pay = overtime hours x hourly rate x the schedule's multiplier

An employee with no overtime gets no overtime term at all, so their figures are exactly
what they were before overtime existed.
"""

"""Payroll calculation and payroll business rules."""

import calendar
from dataclasses import dataclass
from datetime import date
from decimal import Decimal, ROUND_HALF_UP

from django.apps import apps
from django.core.exceptions import ValidationError, PermissionDenied
from django.db import transaction
from django.db.models import Count, Q, Prefetch
from apps.organizations.tenancy import scope_queryset

from .. import roles
from ..models import Attendance, Employee, Salary, PayrollEvent, EmployeePayrollComponent, PayrollAdjustment
from . import schedules

from django.utils import timezone

from ..models import (
    PayrollAdjustment,
    PayrollRun,
)

CENT = Decimal("0.01")


def money(value):
    return Decimal(value).quantize(CENT, rounding=ROUND_HALF_UP)


@dataclass(frozen=True)
class PayrollCalculation:
    employee: Employee
    month: int
    year: int
    calendar_days: int
    present_days: int
    half_days: int
    absent_days_count: int
    leave_days: int
    absent_equivalent_days: Decimal
    basic_salary: Decimal
    per_day_pay: Decimal
    absence_deduction: Decimal
    overtime_minutes: int
    overtime_pay: Decimal
    gross_pay: Decimal
    net_pay: Decimal
    additional_earnings: Decimal = Decimal("0")
    additional_deductions: Decimal = Decimal("0")
    statutory_deductions: Decimal = Decimal("0")
    employer_contributions: Decimal = Decimal("0")
    expense_reimbursements: Decimal = Decimal("0")
    statutory_details: dict = None
    expense_details: tuple = ()
    components: tuple = ()

    @property
    def total_deduction(self):
        return self.absence_deduction + self.additional_deductions + self.statutory_deductions

    def __getitem__(self, key):
        """Compatibility with the report's established dictionary-style row API."""
        fields = {
            "emp": self.employee,
            "present": self.present_days,
            "half": self.half_days,
            "absent": self.absent_days_count,
            "leave": self.leave_days,
            "absent_days": self.absent_equivalent_days,
            "per_day": self.per_day_pay,
            "deduction": self.total_deduction,
            "overtime_minutes": self.overtime_minutes,
            "overtime_pay": self.overtime_pay,
            "gross": self.gross_pay,
            "net": self.net_pay,
            "statutory_deductions": self.statutory_deductions,
            "employer_contributions": self.employer_contributions,
            "statutory_details": self.statutory_details or {},
        }
        try:
            return fields[key]
        except KeyError:
            raise KeyError(key) from None


def validate_period(month, year):
    if not 1 <= int(month) <= 12:
        raise ValidationError("Month must be between 1 and 12.")

    if int(year) < 2000 or int(year) > 2100:
        raise ValidationError("Invalid payroll year.")


def get_attendance_totals(employee, month, year):
    if hasattr(employee, "_period_attendance"):
        return {key: sum(record.status == status for record in employee._period_attendance)
                for key, status in (("present", "P"), ("half", "H"), ("absent", "A"), ("leave", "L"))}
    result = employee.attendance.filter(
        date__month=month,
        date__year=year,
    ).aggregate(
        present=Count(
            "id",
            filter=Q(status="P"),
        ),
        half=Count(
            "id",
            filter=Q(status="H"),
        ),
        absent=Count(
            "id",
            filter=Q(status="A"),
        ),
        leave=Count(
            "id",
            filter=Q(status="L"),
        ),
    )

    return {
        "present": result["present"] or 0,
        "half": result["half"] or 0,
        "absent": result["absent"] or 0,
        "leave": result["leave"] or 0,
    }


def calculate_overtime(employee, month, year, per_day_pay):
    resolver = schedules.ScheduleResolver()

    records = (
        Attendance.objects
        .filter(
            emp=employee,
            date__month=month,
            date__year=year,
            status="P",
            check_out__isnull=False,
        )
        .select_related(
            "emp__work_schedule",
            "emp__department__work_schedule",
        )
    )

    total_minutes = 0
    multiplier = Decimal("1.00")
    scheduled_minutes = 0

    if hasattr(employee, "_period_attendance"):
        records = [record for record in employee._period_attendance if record.status == "P" and record.check_out]
    for record in records:
        schedule = getattr(employee, "_payroll_schedule", None) or resolver.for_employee(employee)

        if not schedule or not schedule.overtime_eligible:
            continue

        evaluation = schedules.evaluate(record, schedule)

        if not evaluation:
            continue

        if evaluation.overtime_minutes <= 0:
            continue

        total_minutes += evaluation.overtime_minutes
        multiplier = schedule.overtime_multiplier
        scheduled_minutes = schedules.scheduled_minutes(schedule)

    if not total_minutes or not scheduled_minutes:
        return 0, Decimal("0.00")

    overtime_pay = (
        Decimal(total_minutes)
        * per_day_pay
        * multiplier
        / Decimal(scheduled_minutes)
    )

    return total_minutes, money(overtime_pay)


def calculate_employee_payroll(employee, month, year):
    validate_period(month, year)

    calendar_days = calendar.monthrange(year, month)[1]

    totals = get_attendance_totals(
        employee,
        month,
        year,
    )

    basic_salary = money(employee.basic_salary)

    per_day_pay = money(
        basic_salary / Decimal(calendar_days)
    )

    absent_equivalent_days = (
        Decimal(totals["absent"])
        + Decimal(totals["half"]) / Decimal("2")
    )

    absence_deduction = money(
        min(
            absent_equivalent_days * per_day_pay,
            basic_salary,
        )
    )

    overtime_minutes, overtime_pay = calculate_overtime(
        employee,
        month,
        year,
        per_day_pay,
    )

    first, last = date(year, month, 1), date(year, month, calendar_days)
    components = []
    assignment_ranges = {}
    assignments = (employee._payroll_components if hasattr(employee, "_payroll_components") else
                   employee.payroll_components.select_related("component").filter(active=True, component__active=True))
    for assignment in assignments:
        if assignment.component.organization_id != employee.organization_id:
            raise ValidationError("Payroll component belongs to another organization.")
        start = max(first, assignment.effective_from)
        end = min(last, assignment.effective_to or last)
        if start <= end:
            previous = assignment_ranges.setdefault(assignment.component_id, [])
            if any(start <= old_end and end >= old_start for old_start, old_end in previous):
                raise ValidationError(f"Overlapping payroll component assignments for {employee.name}.")
            previous.append((start, end))
            amount = money(assignment.amount * Decimal((end - start).days + 1) / calendar_days)
            components.append((assignment.component.name, assignment.component.component_type, str(amount)))
    adjustments = (employee._payroll_adjustments if hasattr(employee, "_payroll_adjustments") else
                   employee.payroll_adjustments.filter(month=month, year=year, approved=True))
    for adjustment in adjustments:
        components.append((adjustment.description, adjustment.component_type, str(money(adjustment.amount))))
    earnings = sum((Decimal(amount) for _, kind, amount in components if kind == "EARNING"), Decimal(0))
    gross_pay = money(basic_salary + overtime_pay + earnings)

    # Statutory calculations
    from .statutory import calculate_statutory_deductions
    statutory_config = getattr(employee.organization, "statutory_config", None)
    statutory_profile = getattr(employee, "statutory_profile", None)
    statutory_res = calculate_statutory_deductions(
        employee=employee,
        basic_salary=basic_salary,
        gross_pay=gross_pay,
        month=month,
        year=year,
        config=statutory_config,
        profile=statutory_profile,
    )
    for stat_desc, stat_kind, stat_amount in statutory_res.breakdown:
        components.append((stat_desc, stat_kind, stat_amount))

    additional_deductions = sum((Decimal(amount) for desc, kind, amount in components if kind == "DEDUCTION" and desc not in [b[0] for b in statutory_res.breakdown]), Decimal(0))
    statutory_deductions = statutory_res.total_employee_deductions
    total_deductions = money(absence_deduction + additional_deductions + statutory_deductions)

    if total_deductions > gross_pay:
        raise ValidationError(f"Deductions exceed gross pay for {employee.name}; review the adjustments.")

    # Expense Reimbursements (non-taxable payout to employee)
    unpaid_claims = (
        employee._unpaid_expense_claims
        if hasattr(employee, "_unpaid_expense_claims")
        else (list(employee.expense_claims.filter(status="APPROVED", payroll_run__isnull=True)) if hasattr(employee, "expense_claims") else [])
    )
    expense_reimbursements = money(sum((claim.amount for claim in unpaid_claims), Decimal("0.00")))
    for claim in unpaid_claims:
        components.append((f"Expense Reimbursement: {claim.title}", "REIMBURSEMENT", str(money(claim.amount))))

    net_pay = money(gross_pay - total_deductions + expense_reimbursements)

    statutory_details = {
        "epf_wage": str(statutory_res.epf_wage),
        "epf_employee": str(statutory_res.epf_employee),
        "epf_employer_eps": str(statutory_res.epf_employer_eps),
        "epf_employer_epf": str(statutory_res.epf_employer_epf),
        "epf_employer_total": str(statutory_res.epf_employer_total),
        "esi_eligible": statutory_res.esi_eligible,
        "esi_employee": str(statutory_res.esi_employee),
        "esi_employer": str(statutory_res.esi_employer),
        "pt_amount": str(statutory_res.pt_amount),
        "tds_amount": str(statutory_res.tds_amount),
        "total_employee_deductions": str(statutory_res.total_employee_deductions),
        "total_employer_contributions": str(statutory_res.total_employer_contributions),
    }

    return PayrollCalculation(
        employee=employee,
        month=month,
        year=year,
        calendar_days=calendar_days,
        present_days=totals["present"],
        half_days=totals["half"],
        absent_days_count=totals["absent"],
        leave_days=totals["leave"],
        absent_equivalent_days=absent_equivalent_days,
        basic_salary=basic_salary,
        per_day_pay=per_day_pay,
        absence_deduction=absence_deduction,
        overtime_minutes=overtime_minutes,
        overtime_pay=overtime_pay,
        gross_pay=gross_pay,
        net_pay=net_pay,
        additional_earnings=earnings,
        additional_deductions=additional_deductions,
        statutory_deductions=statutory_deductions,
        employer_contributions=statutory_res.total_employer_contributions,
        expense_reimbursements=expense_reimbursements,
        statutory_details=statutory_details,
        expense_details=tuple((c.claim_number, c.title, str(c.amount)) for c in unpaid_claims),
        components=tuple(components),
    )


def calculate_payroll_rows(month, year, *, user=None, organization=None):
    validate_period(month, year)

    employees = (
        Employee.objects
        .filter(is_active=True)
        .select_related(
            "department",
            "position",
            "work_schedule", "department__work_schedule", "organization",
            "organization__statutory_config", "statutory_profile", "bank_account",
        )
        .prefetch_related(
            Prefetch("attendance", queryset=Attendance.objects.filter(date__month=month, date__year=year), to_attr="_period_attendance"),
            Prefetch("payroll_components", queryset=EmployeePayrollComponent.objects.filter(active=True, component__active=True).select_related("component"), to_attr="_payroll_components"),
            Prefetch("payroll_adjustments", queryset=PayrollAdjustment.objects.filter(month=month, year=year, approved=True), to_attr="_payroll_adjustments"),
            Prefetch("expense_claims", queryset=apps.get_model("core", "ExpenseClaim").objects.filter(status="APPROVED", payroll_run__isnull=True), to_attr="_unpaid_expense_claims"),
        )
        .order_by("name")
    )

    if user is not None:
        employees = scope_queryset(employees, user)
    if organization is not None:
        employees = employees.filter(organization=organization)
    resolver = schedules.ScheduleResolver()
    employees = list(employees)
    for employee in employees:
        employee._payroll_schedule = resolver.for_employee(employee)
    return [
        calculate_employee_payroll(
            employee,
            month,
            year,
        )
        for employee in employees
    ]


def calculation_snapshot(row):
    bank = getattr(row.employee, "bank_account", None)
    bank_details = {
        "bank_name": bank.bank_name,
        "account_holder_name": bank.account_holder_name,
        "account_number": bank.masked_account_number,
        "raw_account_number": bank.account_number,
        "ifsc_code": bank.ifsc_code,
        "payment_method": bank.payment_method,
        "is_verified": bank.is_verified,
    } if bank else {}

    return {
        "employee_id": row.employee.pk,
        "name": row.employee.name,
        "designation": row.employee.designation,
        "currency": row.employee.organization.default_currency,
        "basic": str(row.basic_salary),
        "gross": str(row.gross_pay),
        "net": str(row.net_pay),
        "deduction": str(row.total_deduction),
        "absence_deduction": str(row.absence_deduction),
        "statutory_deductions": str(row.statutory_deductions),
        "employer_contributions": str(row.employer_contributions),
        "expense_reimbursements": str(row.expense_reimbursements),
        "statutory_details": row.statutory_details or {},
        "expense_details": row.expense_details,
        "bank_details": bank_details,
        "absent_days": str(row.absent_equivalent_days),
        "per_day_pay": str(row.per_day_pay),
        "overtime_minutes": row.overtime_minutes,
        "overtime_pay": str(row.overtime_pay),
        "components": row.components,
        "month": row.month,
        "year": row.year,
        "counts": {
            "present": row.present_days,
            "half": row.half_days,
            "absent": row.absent_days_count,
            "leave": row.leave_days,
        },
    }


def _persist_snapshot(items):
    for item in items:
        employee = Employee.objects.get(pk=item["employee_id"])
        defaults = {field: item[field] for field in ("gross", "net", "deduction", "absent_days",
                                                     "per_day_pay", "overtime_minutes", "overtime_pay")}
        defaults["calculation_snapshot"] = item
        Salary.objects.update_or_create(emp=employee, month=item["month"], year=item["year"], defaults=defaults)


@transaction.atomic
def generate_payroll(month, year, *, user=None):
    rows = calculate_payroll_rows(month, year, user=user)
    organization_ids = sorted({row.employee.organization_id for row in rows})
    for organization_id in organization_ids:
        run, _ = PayrollRun.objects.select_for_update().get_or_create(
            organization_id=organization_id, month=month, year=year, defaults={"created_by": user})
        if run.status != PayrollRun.DRAFT:
            raise ValidationError("Only draft payroll can be recalculated.")
    _persist_snapshot([calculation_snapshot(row) for row in rows])
    return len(rows)


def attendance_totals(salary):
    if salary.calculation_snapshot:
        return salary.calculation_snapshot["counts"]
    result = salary.emp.attendance.filter(
        date__month=salary.month,
        date__year=salary.year,
    ).aggregate(
        present=Count(
            "id",
            filter=Q(status="P"),
        ),
        half=Count(
            "id",
            filter=Q(status="H"),
        ),
        absent=Count(
            "id",
            filter=Q(status="A"),
        ),
        leave=Count(
            "id",
            filter=Q(status="L"),
        ),
    )

    return result

def _authorize_run(run, user, permission):
    if user is None:
        return
    if not user.has_perm(permission) or not scope_queryset(
            PayrollRun.objects.filter(pk=run.pk), user).exists():
        raise PermissionDenied


def _event(run, action, user=None, reason=""):
    PayrollEvent.objects.create(run=run, action=action, actor=user, reason=reason[:255])


@transaction.atomic
def create_payroll_run(month, year, user, *, organization=None):
    from apps.organizations.models import Organization
    validate_period(month, year)
    organizations = scope_queryset(Organization.objects.all(), user, "pk")
    if organization is None:
        choices = list(organizations[:2])
        if len(choices) != 1:
            raise ValidationError("Select one organization.")
        organization = choices[0]
    if not organizations.filter(pk=organization.pk).exists() or not user.has_perm(roles.GENERATE_PAYROLL):
        raise PermissionDenied
    run, created = PayrollRun.objects.select_for_update().get_or_create(
        organization=organization, month=month, year=year,
        defaults={"created_by": user, "policy_version": "2.0"})
    if run.is_locked:
        raise ValidationError("A finalized or reversed payroll cannot be regenerated.")
    if created:
        _event(run, "CREATED", user)
    return run


@transaction.atomic
def submit_payroll_for_approval(run, user=None):
    run = PayrollRun.objects.select_for_update().get(pk=run.pk)
    _authorize_run(run, user, roles.GENERATE_PAYROLL)
    if run.status != PayrollRun.DRAFT:
        raise ValidationError("Only draft payroll runs can be submitted.")
    rows = calculate_payroll_rows(run.month, run.year, organization=run.organization)
    if not rows:
        raise ValidationError("There are no active employees to process.")
    run.calculation_snapshot = [calculation_snapshot(row) for row in rows]
    run.policy_version = "2.0"
    run.status = PayrollRun.PENDING_APPROVAL
    run.save(update_fields=["calculation_snapshot", "policy_version", "status"])
    _event(run, "SUBMITTED", user)
    return run


@transaction.atomic
def approve_payroll(run, user):
    run = PayrollRun.objects.select_for_update().get(pk=run.pk)
    _authorize_run(run, user, "core.approve_payroll")
    if run.created_by_id == user.pk:
        raise ValidationError("A different authorized reviewer must approve this payroll.")
    if run.status != PayrollRun.PENDING_APPROVAL:
        raise ValidationError("Only payroll awaiting approval can be approved.")
    run.status, run.approved_by, run.approved_at = PayrollRun.APPROVED, user, timezone.now()
    run.save(update_fields=["status", "approved_by", "approved_at"])
    _event(run, "APPROVED", user)
    return run


@transaction.atomic
def finalize_payroll(run, user):
    run = PayrollRun.objects.select_for_update().get(pk=run.pk)
    _authorize_run(run, user, "core.finalize_payroll")
    if run.status != PayrollRun.APPROVED or not run.calculation_snapshot:
        raise ValidationError("Only approved payroll with a calculation snapshot can be finalized.")
    _persist_snapshot(run.calculation_snapshot)
    from .expenses import mark_expenses_reimbursed_for_run
    mark_expenses_reimbursed_for_run(run)
    run.status, run.finalized_by, run.finalized_at = PayrollRun.FINALIZED, user, timezone.now()
    run.save(update_fields=["status", "finalized_by", "finalized_at"])
    _event(run, "FINALIZED", user)
    return run


@transaction.atomic
def reverse_payroll(run, *, user, reason):
    run = PayrollRun.objects.select_for_update().get(pk=run.pk)
    _authorize_run(run, user, "core.reverse_payroll")
    if run.status != PayrollRun.FINALIZED or not reason.strip():
        raise ValidationError("Only finalized payroll can be reversed, with an explanation.")
    from core.models_expenses import ExpenseClaim
    ExpenseClaim.objects.filter(payroll_run=run).update(status=ExpenseClaim.STATUS_APPROVED, payroll_run=None)
    run.status = PayrollRun.REVERSED
    run.save(update_fields=["status"])
    _event(run, "REVERSED", user, reason)
    return run
