# T-III-1-004: Nonsingular ⇔ Δ ≠ 0

**Status**: DONE
**Silverman**: III.1.4(a)
**Module**: `Mathlib.AlgebraicGeometry.EllipticCurve.Affine`
**Owner**: mathlib
**Estimated lines**: 0 (mathlib)
**Difficulty**: trivial
**Stream**: B

## Depends on
- T-III-1-001 (Weierstrass + Δ defined)

## Blocks
- T-III-1-005 (node case)
- T-III-1-006 (cusp case)

## Statement (Silverman III.1.4(a))
A Weierstrass curve `E` is nonsingular at every point iff `Δ ≠ 0`.

## Acceptance criteria

Already in mathlib as `WeierstrassCurve.Affine.nonsingular_iff` (or similar).
```lean
#check WeierstrassCurve.Affine.equation
#check WeierstrassCurve.Affine.Nonsingular
```

## Notes
- The mathlib `EllipticCurve` structure bundles the assumption Δ ≠ 0 as an
  invertible element.

## Progress log
- 2026-04-08 [auto] marked DONE
