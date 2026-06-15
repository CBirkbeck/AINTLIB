# T-MIGRATE-002: Move Universal.lean → Auxiliary/Universal.lean

**Status**: DONE
**Module**: `HasseWeil/Universal.lean` → `HasseWeil/Auxiliary/Universal.lean`
**Owner**: worker-C
**Checked out at**: 2026-04-08
**Estimated lines**: 0 (refactor)
**Difficulty**: trivial
**Stream**: M

## Depends on
- T-MIGRATE-001 (directories)

## Blocks
- T-MIGRATE-015 (root file)

## Statement
Move `HasseWeil/Universal.lean` to `HasseWeil/Auxiliary/Universal.lean`. Update
all imports.

## Acceptance criteria
- File is in new location
- All imports updated
- `lake build` succeeds

## Progress log
- 2026-04-08 [worker-C] DONE. `mv` to new location, updated imports in
  `DivisionPolynomial.lean` and `FrobeniusIsogeny.lean`. Build clean.
