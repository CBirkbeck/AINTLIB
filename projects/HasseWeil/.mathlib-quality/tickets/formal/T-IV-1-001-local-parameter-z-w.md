# T-IV-1-001: Local parameter z = -x/y, w = -1/y at O

**Status**: PARTIAL (FormalGroup.lean)
**Silverman**: IV.1 (definition)
**Module**: `HasseWeil/FormalGroup.lean` → `HasseWeil/FormalGroup/Curve.lean`
**Owner**: (existing)
**Estimated lines**: 20
**Difficulty**: easy
**Stream**: D

## Depends on
- T-III-1-001 (Weierstrass)

## Blocks
- T-IV-1-002 (w(z) exists)
- T-IV-1-006 (x(z), y(z))

## Statement (Silverman IV.1)
For an elliptic curve `E : Y² + a₁ XY + a₃ Y = X³ + a₂ X² + a₄ X + a₆`, the
functions `z := -X/Y` and `w := -1/Y` form a uniformizer at the point at
infinity `O`. In particular, `z` is a uniformizer (`ord_O(z) = 1`).

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- The local parameter z = -x/y at the point at infinity. -/
def WeierstrassCurve.zAt0 (E : WeierstrassCurve F) : E.toAffine.FunctionField

/-- The auxiliary function w = -1/y. -/
def WeierstrassCurve.wAt0 (E : WeierstrassCurve F) : E.toAffine.FunctionField

theorem WeierstrassCurve.zAt0_isUniformizer (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)] :
    E.toAffine.IsUniformizerAt 0 E.zAt0

end HasseWeil.FormalGroup
```

## Notes
- Existing in `HasseWeil/FormalGroup.lean`.

## Progress log
- 2026-04-08 [auto] PARTIAL — exists in HasseWeil/FormalGroup.lean
