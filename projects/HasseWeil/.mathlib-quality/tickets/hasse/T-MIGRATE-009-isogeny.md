# T-MIGRATE-009: Refactor isogeny files → EC/Isogeny.lean

**Status**: OPEN
**Module**: multiple
**Owner**: (unassigned)
**Estimated lines**: 0 (refactor)
**Difficulty**: hard
**Stream**: M

## Depends on
- T-MIGRATE-001

## Blocks
- T-MIGRATE-015

## Statement
Consolidate into `HasseWeil/EC/Isogeny.lean`:
- `HasseWeil/Basic.lean` (Isogeny structure)
- `HasseWeil/Isogeny.lean` (PullbackIsogeny — merge or deprecate)
- `HasseWeil/SeparableDegree.lean`
- `HasseWeil/Endomorphism.lean` (operations on End E)
- `HasseWeil/MulByIntPullback.lean`

Refactor the existing `Isogeny` to be less axiomatic if possible (point being
that the proof of correspondence with curve morphisms should be inside the
file, not assumed).

## Notes
- This is the largest refactor. The existing `Isogeny` is somewhat awkward.
- See user feedback memory: "16 sorries remain, root cause is axiomatic Isogeny"
  — fixing this is part of T-MIGRATE-009.

## Progress log
