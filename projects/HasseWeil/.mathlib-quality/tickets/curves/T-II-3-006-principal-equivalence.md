# T-II-3-006: Principal divisor and linear equivalence

**Status**: DONE (worker-I, 2026-04-20; verified axiom-clean 2026-04-22: `IsPrincipal`, `principalSubgroup` depend only on `[propext, Classical.choice, Quot.sound]`)
**Silverman**: II.3 (definition)
**Module**: `HasseWeil/Curves/Divisors.lean`
**Owner**: worker-I
**Estimated lines**: 25 (delivered ~80 including Pic, linear-equiv transport)
**Difficulty**: easy
**Stream**: A

## Depends on
- T-II-3-005 (div(f))

## Blocks
- T-II-3-007 (Pic, Pic⁰)
- T-III-3-005 (D principal iff)

## Statement
A divisor `D ∈ Div(C)` is **principal** if `D = div(f)` for some `f ∈ K̄(C)*`.
Two divisors `D₁, D₂` are **linearly equivalent**, written `D₁ ~ D₂`, if
`D₁ - D₂` is principal.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- A divisor is principal if it equals div(f) for some f. -/
def Divisor.IsPrincipal (D : Divisor C) : Prop :=
  ∃ f : C.FunctionFieldˣ, D = divisorHom C f

/-- The subgroup of principal divisors. -/
def Divisor.principalSubgroup (C : SmoothPlaneCurve F) : AddSubgroup (Divisor C) :=
  (divisorHom C).range.toAddSubgroup

/-- Linear equivalence: D₁ ~ D₂ iff D₁ - D₂ is principal. -/
def Divisor.LinearlyEquiv (D₁ D₂ : Divisor C) : Prop :=
  D₁ - D₂ ∈ Divisor.principalSubgroup C

infixl:50 " ~_div " => Divisor.LinearlyEquiv

end HasseWeil.Curves
```

## Progress log

- **2026-04-20** (worker-I): delivered in `HasseWeil/Curves/Divisors.lean`.
  Added `divisorOf_inv` (`div(f⁻¹) = -div(f)` via `ord_P_inv`), then:
  - `IsPrincipal D := ∃ f ≠ 0, divisorOf f = D`.
  - `isPrincipal_zero` (via `divisorOf_one`).
  - `IsPrincipal.add` (via `divisorOf_mul`).
  - `IsPrincipal.neg` (via `divisorOf_inv`).
  - `principalSubgroup : AddSubgroup (Divisor C)` using the above.
  - `LinearlyEquiv D₁ D₂ := IsPrincipal (D₁ - D₂)` + `.refl`/`.symm`/`.trans`.
  All axiom-clean.
