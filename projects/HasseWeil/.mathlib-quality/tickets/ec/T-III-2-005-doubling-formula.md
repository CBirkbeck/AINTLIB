# T-III-2-005: Doubling formula x([2]P)

**Status**: DONE
**Silverman**: III.2.3(d)
**Module**: `Mathlib.AlgebraicGeometry.EllipticCurve.Affine`
**Owner**: mathlib
**Estimated lines**: 0
**Difficulty**: trivial
**Stream**: B

## Depends on
- T-III-2-004 (explicit addition)

## Blocks
- T-III-2-006 (even functions in K(x))
- T-III-4-003 (multiplication-by-m)

## Statement (Silverman III.2.3(d))
For `P = (x, y) ∈ E`, the x-coordinate of `[2]P` is
`x([2]P) = (x⁴ - b₄ x² - 2b₆ x - b₈) / (4 x³ + b₂ x² + 2 b₄ x + b₆)`.

## Acceptance criteria

```lean
-- existing in mathlib via the addition formula applied at P = Q
```

## Progress log
- 2026-04-08 [auto] marked DONE
