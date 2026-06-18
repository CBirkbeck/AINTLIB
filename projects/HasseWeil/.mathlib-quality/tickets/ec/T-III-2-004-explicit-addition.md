# T-III-2-004: Explicit addition algorithm

**Status**: DONE
**Silverman**: III.2.3
**Module**: `Mathlib.AlgebraicGeometry.EllipticCurve.Affine`
**Owner**: mathlib
**Estimated lines**: 0
**Difficulty**: trivial
**Stream**: B

## Depends on
- T-III-2-001 (composition)

## Blocks
- T-III-2-005 (doubling formula)
- T-III-2-006 (even functions)

## Statement (Silverman III.2.3)
For `P_i = (x_i, y_i) ∈ E`, the addition is given by the explicit rational
formulas in Silverman III.2.3.

## Acceptance criteria

```lean
#check WeierstrassCurve.Affine.addX
#check WeierstrassCurve.Affine.addY
#check WeierstrassCurve.Affine.negY
```

## Progress log
- 2026-04-08 [auto] marked DONE — `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula`
