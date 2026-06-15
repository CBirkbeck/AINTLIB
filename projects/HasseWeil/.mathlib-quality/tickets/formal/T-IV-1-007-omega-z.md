# T-IV-1-007: ω(z) invariant differential as power series

**Status**: PARTIAL (FormalGroup.lean)
**Silverman**: IV.1
**Module**: `HasseWeil/FormalGroup/Curve.lean`
**Owner**: (existing)
**Estimated lines**: 30
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-1-006 (x(z), y(z))

## Blocks
- T-IV-4-003 (normalized invariant differential)

## Statement (Silverman IV.1)
The invariant differential `ω = dx/(2y + a₁ x + a₃)` of the curve, expressed in
the local parameter `z`, is a power series:
`ω(z) = (1 + a₁ z + (a₁² + a₂) z² + ...) dz ∈ ℤ[a₁..a₆][[z]] dz`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- The invariant differential as a power series in z. -/
def WeierstrassCurve.omegaSeries (E : WeierstrassCurve F) : PowerSeries F

theorem WeierstrassCurve.omegaSeries_constantCoeff (E : WeierstrassCurve F) :
    (E.omegaSeries.coeff F 0) = 1

end HasseWeil.FormalGroup
```

## Notes
- Existing in `HasseWeil/FormalGroup.lean`.

## Progress log
- 2026-04-08 [auto] PARTIAL — exists in HasseWeil/FormalGroup.lean
