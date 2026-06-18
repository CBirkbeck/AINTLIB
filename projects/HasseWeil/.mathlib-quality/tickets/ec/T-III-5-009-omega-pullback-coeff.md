# T-III-5-009: omegaPullbackCoeff (existing definition)

**Status**: DONE
**Silverman**: III.5
**Module**: `HasseWeil/OmegaPullbackCoeff.lean` → `HasseWeil/EC/InvariantDiff.lean`
**Owner**: (existing)
**Estimated lines**: 0 (existing)
**Difficulty**: trivial
**Stream**: B/E

## Depends on
- T-III-1-002 (invariant differential)

## Blocks
- T-III-5-006 (ring hom)

## Statement
The function `omegaPullbackCoeff α : F` extracting the coefficient `a_α` from
the equation `α* ω = a_α ω`.

## Acceptance criteria

```lean
#check HasseWeil.omegaPullbackCoeff
```

## Progress log
- 2026-04-08 [auto] marked DONE — exists in HasseWeil/OmegaPullbackCoeff.lean
