# T-II-4-009: ord_P(ω) = 0 for almost all P

**Status**: OPEN
**Silverman**: II.4.3(e)
**Module**: `HasseWeil/Curves/Differentials.lean`
**Owner**: (unassigned)
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: A

## Depends on
- T-II-4-007 (ord_P(ω) defined)
- T-II-4-008 (formula for ord(f·dx))

## Blocks
- T-II-4-010 (div(ω))

## Statement (Silverman II.4.3(e))
For any nonzero `ω ∈ Ω_C`, the set `{ P ∈ C : ord_P(ω) ≠ 0 }` is finite.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- A nonzero differential has ord_P = 0 for all but finitely many P.
    Reference: Silverman II.4.3(e). -/
theorem Differentials.ord_finite_support (C : SmoothPlaneCurve F)
    (ω : Differentials C) (hω : ω ≠ 0) :
    Set.Finite { P : C | Differentials.ord C P ω ≠ 0 }

end HasseWeil.Curves
```

## Notes
- Write `ω = f · dx` for some `f, x ∈ K(C)`. Then `f` has finitely many zeros
  and poles (T-II-1 results), and `dx` has finitely many zeros and poles
  (formula from T-II-4-008 + finiteness of ramification).
- This is needed to make `div(ω)` a well-defined element of `Div(C)`.

## Progress log
