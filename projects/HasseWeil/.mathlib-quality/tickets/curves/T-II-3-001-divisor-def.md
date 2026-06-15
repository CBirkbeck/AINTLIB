# T-II-3-001: `Divisor C` as free abelian group

**Status**: DONE (verified axiom-clean 2026-04-22: `Divisor` depends only on `[propext, Classical.choice, Quot.sound]`)
**Silverman**: II.3 (definition)
**Module**: `HasseWeil/Curves/Divisors.lean`
**Owner**: worker-A
**Checked out at**: 2026-04-13T08:44Z
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: A

## Depends on
(none — pure definition)

## Blocks
- T-II-3-002 through T-II-3-012 (everything in II.3)

## Statement
The **divisor group** of a curve `C` is

```
Div(C) := ⊕_{P ∈ C} ℤ
```

i.e., the free abelian group on the points of `C`. A divisor is a formal sum
`D = Σ n_P (P)` with `n_P ∈ ℤ` and `n_P = 0` for all but finitely many P.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- The divisor group of a curve: free abelian group on points.
    Reference: Silverman II.3 (definition). -/
def Divisor (C : SmoothPlaneCurve F) : Type _ := C.SmoothPoint →₀ ℤ

instance (C : SmoothPlaneCurve F) : AddCommGroup (Divisor C) := inferInstance

end HasseWeil.Curves
```

## Notes
- Use `Finsupp` (already in mathlib) for the free abelian group structure.
- We could also use `FreeAbelianGroup C.SmoothPoint`, but Finsupp is more
  ergonomic for direct calculation (`Finsupp.support`, `Finsupp.sum`).

## Progress log

- 2026-04-13T08:44Z [worker-A] checkout. Pure definition, no deps. Plan: wrap
  `WeierstrassCurve.Affine F` via a thin `SmoothPlaneCurve` abbrev in
  `Curves/Basic.lean`, define `SmoothPoint` as a structure, then
  `Divisor C := C.SmoothPoint →₀ ℤ` in `Curves/Divisors.lean`. Leaves
  T-II-1-001 (DVR theorem itself) untouched — that's a separate, larger ticket.
- 2026-04-13T08:46Z [worker-A] Complete.
  - Created `HasseWeil/Curves/Basic.lean` with `SmoothPlaneCurve`
    (a thin structure wrapping `WeierstrassCurve.Affine F`), `SmoothPoint`
    structure, and `CoordinateRing` / `FunctionField` accessors.
  - Created `HasseWeil/Curves/Divisors.lean` with
    `Divisor C := C.SmoothPoint →₀ ℤ` and the `AddCommGroup` instance.
  - Wired both files into `HasseWeil.lean` root.
  - `lake build HasseWeil.Curves.Basic HasseWeil.Curves.Divisors` passes
    with 0 errors and 0 sorries (verified by `sorry_analyzer.py`).
  - Status → REVIEW.
