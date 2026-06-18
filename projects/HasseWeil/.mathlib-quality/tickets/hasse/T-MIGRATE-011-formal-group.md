# T-MIGRATE-011: Refactor formal group files → FormalGroup/

**Status**: OPEN
**Module**: multiple
**Owner**: (unassigned)
**Estimated lines**: 0 (refactor)
**Difficulty**: medium
**Stream**: M

## Depends on
- T-MIGRATE-001

## Blocks
- T-MIGRATE-015

## Statement
Refactor:
- `HasseWeil/FormalGroup.lean` → split into `HasseWeil/FormalGroup/Curve.lean`
  (curve-specific) and `HasseWeil/FormalGroup/Definition.lean` (abstract)
- `HasseWeil/FormalGroupAssoc.lean` → `HasseWeil/FormalGroup/Operations.lean`
  + `HasseWeil/FormalGroup/Associated.lean`
- `HasseWeil/FormalGroupCorrespondence.lean` → `HasseWeil/FormalGroup/Bridge.lean`
- `HasseWeil/LocalExpansion.lean` → merged into `HasseWeil/FormalGroup/Curve.lean`
  (formalU, formalU_inv, formalX, formalY, localParam, localExpand)

Update imports.

## Notes
- `LocalExpansion.lean` provides `formalU/formalX/formalY` (corresponding to
  T-IV-1-006) and the `localExpand : K(E) →+* LaurentSeries F` ring hom
  (corresponding to a piece of T-IV-BRIDGE-001). It currently has 7 sorries
  for the Weierstrass equation verification and the universal-property
  construction of `localExpand`. These sorries are tracked under T-IV-1-006
  and T-IV-BRIDGE-001 respectively.

## Progress log
