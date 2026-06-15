# T-II-3-003: Div⁰ — degree-zero divisors

**Status**: DONE (verified axiom-clean 2026-04-22: `Divisor.degZero` depends only on `[propext, Classical.choice, Quot.sound]`)
**Silverman**: II.3 (definition)
**Module**: `HasseWeil/Curves/Divisors.lean`
**Owner**: worker-A
**Checked out at**: 2026-04-17T08:29Z
**Estimated lines**: 15
**Difficulty**: trivial
**Stream**: A

## Depends on
- T-II-3-002 (Divisor.degree)

## Blocks
- T-II-3-007 (Pic⁰)
- T-III-3-004 (Pic⁰(E) ≅ E)

## Statement
The subgroup of divisors of degree zero:

```
Div⁰(C) := { D ∈ Div(C) : deg(D) = 0 }.
```

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- The subgroup of degree-zero divisors. -/
def Divisor.degZero (C : SmoothPlaneCurve F) : AddSubgroup (Divisor C) :=
  (Divisor.degreeHom C).ker

abbrev Divisor⁰ (C : SmoothPlaneCurve F) := Divisor.degZero C

end HasseWeil.Curves
```

## Progress log

- 2026-04-17T08:29Z [worker-A] checkout. Pure definition via
  `AddMonoidHom.ker degreeHom`.
- 2026-04-17T08:31Z [worker-A] Complete.
  - Added `Divisor.degZero` (the kernel subgroup) and the
    `mem_degZero` simp-characterization in
    `HasseWeil/Curves/Divisors.lean`.
  - Also added the `Divisor₀` abbrev requested by the acceptance
    criteria (renamed from `Divisor⁰` because a unicode-superscript
    `0` would clash with the elaborator).
  - `lake build HasseWeil.Curves.Divisors` passes, 0 sorries.
  - Status → REVIEW.
