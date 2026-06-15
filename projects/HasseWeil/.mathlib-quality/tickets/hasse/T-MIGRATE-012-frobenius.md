# T-MIGRATE-012: Refactor Frobenius files → Frobenius/

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
- `HasseWeil/FrobeniusIsogeny.lean` → `HasseWeil/Frobenius/AsAlgHom.lean`
- `HasseWeil/Frobenius.lean` → `HasseWeil/Frobenius/PointFix.lean`
  + `HasseWeil/Frobenius/Inseparable.lean` (the "purely inseparable" part)
- Move the `#E(F_q) = ker(1 - π)` part to `HasseWeil/Hasse/PointCount.lean`.

Update imports.

## Progress log
