# T-MIGRATE-007: Refactor Valuation.lean + Ramification.lean → Curves/Basic.lean + Curves/Maps.lean

**Status**: OPEN
**Module**: multiple
**Owner**: (unassigned)
**Estimated lines**: 0 (refactor)
**Difficulty**: medium
**Stream**: M

## Depends on
- T-MIGRATE-001
- T-II-1-001..006 (definitions can move into the new files)

## Blocks
- T-MIGRATE-015

## Statement
Move material from `HasseWeil/Valuation.lean` and `HasseWeil/Ramification.lean`
into the new files:
- `HasseWeil/Curves/Basic.lean` — DVR, ord_P, uniformizers (general curves)
- `HasseWeil/Curves/Maps.lean` — morphisms, ramification index, separable degree

Update imports throughout.

## Notes
- The old files were elliptic-curve-specific. The new files should be over
  general smooth curves where possible, with elliptic curves as a special case.

## Progress log
