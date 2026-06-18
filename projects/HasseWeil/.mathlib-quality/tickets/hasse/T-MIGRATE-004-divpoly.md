# T-MIGRATE-004: Move DivisionPolynomial.lean → Auxiliary/

**Status**: DONE
**Module**: `HasseWeil/DivisionPolynomial.lean` → `HasseWeil/Auxiliary/DivisionPolynomial.lean`
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

## Progress log
- 2026-04-08 [worker-C] DONE. `mv` to Auxiliary; updated 3 importers
  (`MulByIntPullback.lean`, `FormalGroupCorrespondence.lean`, `HasseWeil.lean`
  root). Build clean.
