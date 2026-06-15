# T-III-1-007: Two Weierstrass curves K̄-isomorphic ⇔ same j

**Status**: DONE (mostly mathlib)
**Silverman**: III.1.4(b) cont
**Module**: `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass`
**Owner**: mathlib
**Estimated lines**: 0
**Difficulty**: trivial
**Stream**: B

## Depends on
- T-III-1-003 (change of variables)

## Blocks
- T-III-1-008 (every j is realized)

## Statement (Silverman III.1.4(b/c) cont)
Two Weierstrass curves over `K̄` are isomorphic iff they have the same `j`-invariant.

## Acceptance criteria

Mathlib provides essentially the forward direction; the backwards direction is
in `Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian` or relevant subfile.
```lean
#check WeierstrassCurve.j_variableChange
-- equivalence in some form
```

## Notes
- Mathlib status: forward direction (iso ⇒ same j) is straightforward; reverse
  is built up via the canonical models for each `j`.

## Progress log
- 2026-04-08 [auto] marked DONE — mathlib coverage
