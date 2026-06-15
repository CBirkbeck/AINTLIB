# T-III-2-002: (E, +, O) is an abelian group

**Status**: DONE
**Silverman**: III.2.2
**Module**: `Mathlib.AlgebraicGeometry.EllipticCurve.Affine`
**Owner**: mathlib
**Estimated lines**: 0
**Difficulty**: trivial
**Stream**: B

## Depends on
- T-III-2-001 (composition)

## Blocks
- T-III-2-003 (E(K) subgroup)

## Statement (Silverman III.2.2)
With the operation defined in III.2.1, `(E(K̄), +)` forms an abelian group with
identity `O`.

## Acceptance criteria

```lean
#check WeierstrassCurve.Affine.Point.instAddCommGroup
```

## Notes
- All axioms in mathlib.

## Progress log
- 2026-04-08 [auto] marked DONE
