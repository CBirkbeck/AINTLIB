# T-IV-1-006: x(z), y(z) as Laurent series in z

**Status**: OPEN
**Silverman**: IV.1
**Module**: `HasseWeil/FormalGroup/Curve.lean`
**Owner**: (unassigned)
**Estimated lines**: 40
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-1-002 (w(z))

## Blocks
- T-IV-1-007 (formal differential)
- T-IV-1-008 (formal addition)

## Statement (Silverman IV.1)
Express `x` and `y` as Laurent series in `z`:
- `x(z) = z/w = z⁻² − a₁ z⁻¹ − a₂ − a₃ z + ...`
- `y(z) = -1/w = -z⁻³ − a₁ z⁻² − a₂ z⁻¹ − a₃ + ...`

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- The x-coordinate as a Laurent series in z. -/
def WeierstrassCurve.xSeries (E : WeierstrassCurve F) : LaurentSeries F

/-- The y-coordinate as a Laurent series in z. -/
def WeierstrassCurve.ySeries (E : WeierstrassCurve F) : LaurentSeries F

end HasseWeil.FormalGroup
```

## Notes
- Use `LaurentSeries F` from mathlib.
- The formal expressions are `x = z * w⁻¹` and `y = -w⁻¹`.

## Progress log
