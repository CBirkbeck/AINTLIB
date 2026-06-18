# T-II-3-002: Divisor.degree

**Status**: DONE (verified axiom-clean 2026-04-22: `Divisor.degree`, `Divisor.degreeHom` depend only on `[propext, Classical.choice, Quot.sound]`)
**Silverman**: II.3 (definition)
**Module**: `HasseWeil/Curves/Divisors.lean`
**Owner**: worker-A
**Checked out at**: 2026-04-17T08:26Z
**Estimated lines**: 20
**Difficulty**: easy
**Stream**: A

## Depends on
- T-II-3-001 (Divisor)

## Blocks
- T-II-3-003 (deg-zero subgroup)

## Statement
The **degree** of a divisor `D = Σ n_P (P)` is `Σ n_P ∈ ℤ`.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- The degree of a divisor.
    Reference: Silverman II.3 (definition). -/
def Divisor.degree (D : Divisor C) : ℤ := D.sum (fun _ n => n)

@[simp] theorem Divisor.degree_zero : Divisor.degree (0 : Divisor C) = 0
@[simp] theorem Divisor.degree_add (D₁ D₂ : Divisor C) :
    (D₁ + D₂).degree = D₁.degree + D₂.degree

/-- The degree map as a group homomorphism. -/
def Divisor.degreeHom (C : SmoothPlaneCurve F) : Divisor C →+ ℤ where
  toFun := Divisor.degree
  map_zero' := Divisor.degree_zero
  map_add' := Divisor.degree_add

end HasseWeil.Curves
```

## Progress log

- 2026-04-17T08:26Z [worker-A] checkout. Trivial wrapper around
  `Finsupp.sum (·) (fun _ n => n)`; simp lemmas follow from
  `Finsupp` API. Plan: place definition and lemmas in
  `HasseWeil/Curves/Divisors.lean` (right after `Divisor`).
- 2026-04-17T08:28Z [worker-A] Complete.
  - Added `Divisor.degree`, `degree_zero`, `degree_add`,
    `degreeHom`, `degreeHom_apply` per the ticket.
  - Also added `degree_neg` and `degree_sub` as free simp-lemmas
    (derived from `degreeHom`); these are needed by T-II-3-003
    and T-II-3-009 downstream.
  - `lake build HasseWeil.Curves.Divisors` passes with 0 errors;
    no sorries in the file.
  - Status → REVIEW.
