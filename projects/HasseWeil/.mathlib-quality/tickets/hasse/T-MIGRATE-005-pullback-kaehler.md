# T-MIGRATE-005: Move PullbackKaehler.lean → Auxiliary/

**Status**: DONE
**Module**: `HasseWeil/PullbackKaehler.lean` → `HasseWeil/Auxiliary/PullbackKaehler.lean`
**Owner**: worker-C
**Checked out at**: 2026-04-08
**Estimated lines**: 0 (refactor)
**Difficulty**: trivial
**Stream**: M

## Depends on
- T-MIGRATE-001

## Blocks
- T-MIGRATE-015

## Statement
Move to Auxiliary. Update imports.

## Notes
- This file provides the generic Kähler-pullback functor used by II.4.4 and III.5.

## Progress log
- 2026-04-08 [worker-C] DONE. `mv` to Auxiliary; updated
  `InvariantDifferentialPullback.lean` and `HasseWeil.lean` root. Build clean.
