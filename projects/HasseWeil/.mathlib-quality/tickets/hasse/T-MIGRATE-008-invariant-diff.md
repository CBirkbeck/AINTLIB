# T-MIGRATE-008: Consolidate invariant differential files → EC/InvariantDiff.lean

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
Consolidate the following files into `HasseWeil/EC/InvariantDiff.lean`:
- `HasseWeil/InvariantDifferential.lean`
- `HasseWeil/OmegaPullbackCoeff.lean`
- `HasseWeil/PullbackCoeff.lean`
- `HasseWeil/InvariantDifferentialPullback.lean`

Update all imports.

## Notes
- These four files all relate to the invariant differential `ω` and how it
  pulls back through isogenies. They should live together.

## Progress log
