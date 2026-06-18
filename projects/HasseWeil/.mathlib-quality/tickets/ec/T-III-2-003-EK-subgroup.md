# T-III-2-003: E(K) is a subgroup

**Status**: DONE
**Silverman**: III.2.2(f)
**Module**: `Mathlib.AlgebraicGeometry.EllipticCurve.Affine`
**Owner**: mathlib
**Estimated lines**: 0
**Difficulty**: trivial
**Stream**: B

## Depends on
- T-III-2-002 (E group)

## Blocks
- T-V-1-001 (E(F_q) = ker(1-π))

## Statement (Silverman III.2.2(f))
For any subfield `K ⊂ K̄`, the set of `K`-rational points `E(K)` is a subgroup
of `E(K̄)`.

## Acceptance criteria

Mathlib provides this via base change:
```lean
-- E(K) is the type WeierstrassCurve.Affine.Point E for E : WeierstrassCurve K
-- Galois invariance proven via the explicit formulas
```

## Progress log
- 2026-04-08 [auto] marked DONE
