# T-II-4-006: f regular at P ⇒ df/dt regular at P

**Status**: OPEN
**Silverman**: II.4.3(b)
**Module**: `HasseWeil/Curves/Differentials.lean`
**Owner**: (unassigned)
**Estimated lines**: 70
**Difficulty**: medium
**Stream**: A

## Depends on
- T-II-4-005 (ω = g·dt for unique g)

## Blocks
- T-II-4-008 (order of f·dx)

## Statement (Silverman II.4.3(b))
Let `t` be a uniformizer at `P`. If `f ∈ K(C)` is regular at `P` (i.e. `ord_P f ≥ 0`),
then so is the function `df/dt` (the unique `g` with `df = g·dt`).

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- df/dt is regular at P whenever f is, given uniformizer t at P.
    Reference: Silverman II.4.3(b). -/
theorem Differentials.coeff_d_regular_at (C : SmoothPlaneCurve F) (P : C)
    (t : C.FunctionField) (ht : C.IsUniformizerAt P t)
    (f : C.FunctionField) (hf : 0 ≤ C.ord P f) :
    0 ≤ C.ord P (Differentials.coeff C P t ht (Differentials.d f))

end HasseWeil.Curves
```

## Notes
- This is essentially the chain rule for the derivation `d/dt` on the local ring
  `O_{C,P}`. Mathlib's `Derivation` API on the local ring should let us state
  this.
- Use the local-ring structure: write `f = a₀ + a₁ t + a₂ t² + ...` formally;
  then `df = (a₁ + 2 a₂ t + ...) dt`, which is regular.

## Progress log
