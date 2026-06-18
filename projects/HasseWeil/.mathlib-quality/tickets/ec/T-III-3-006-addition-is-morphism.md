# T-III-3-006: Addition is a morphism (extends as rational map)

**Status**: DONE (mathlib)
**Silverman**: III.3.6
**Module**: `Mathlib.AlgebraicGeometry.EllipticCurve.Affine`
**Owner**: mathlib
**Estimated lines**: 0
**Difficulty**: trivial
**Stream**: B

## Depends on
- T-III-2-001 (composition law)

## Blocks
- T-III-4-001 (Isogeny defined as morphism)

## Statement (Silverman III.3.6)
The addition map `+ : E × E → E` and the negation map `[-1] : E → E` are morphisms
of varieties.

## Acceptance criteria

```lean
-- via the explicit rational formulas in mathlib
#check WeierstrassCurve.Affine.Point.add  -- definition + group instance
```

## Notes
- mathlib's group instance gives functions, not morphisms in scheme-theoretic
  sense. For our purposes the rational maps are enough since we use them via
  the function field.

## Progress log
- 2026-04-08 [auto] marked DONE
