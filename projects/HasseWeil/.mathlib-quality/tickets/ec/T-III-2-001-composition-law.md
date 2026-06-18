# T-III-2-001: Composition law via line construction

**Status**: DONE
**Silverman**: III.2.1
**Module**: `Mathlib.AlgebraicGeometry.EllipticCurve.Affine` (Group)
**Owner**: mathlib
**Estimated lines**: 0
**Difficulty**: trivial
**Stream**: B

## Depends on
- T-III-1-001 (Weierstrass)

## Blocks
- T-III-2-002 (group axioms)

## Statement (Silverman III.2.1)
Let `E` be an elliptic curve. For `P, Q ∈ E`, let `L` be the line through `P` and
`Q` (tangent line if `P = Q`). Then `L` meets `E` at exactly one other point `R`.
Define `P + Q := -R'` where `R'` is the third intersection of the line through
`R` and `O`.

## Acceptance criteria

Mathlib provides this:
```lean
#check WeierstrassCurve.Affine.Point.add
#check @WeierstrassCurve.Affine.Point.add
```

## Progress log
- 2026-04-08 [auto] marked DONE — mathlib coverage
