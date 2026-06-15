# T-III-5-010: Chain rule a_{α∘β} = a_α · a_β (existing)

**Status**: DONE
**Silverman**: III.5.6(a)
**Module**: `HasseWeil/InvariantDifferentialPullback.lean` → `HasseWeil/EC/InvariantDiff.lean`
**Owner**: (existing)
**Estimated lines**: 0 (existing)
**Difficulty**: trivial
**Stream**: B/E

## Depends on
- T-III-5-009 (omegaPullbackCoeff)

## Blocks
- T-III-5-006 (ring hom)

## Statement
For composable isogenies `α : E₂ → E₃, β : E₁ → E₂`,
`omegaPullbackCoeff (α ∘ β) = omegaPullbackCoeff α * omegaPullbackCoeff β`
(or up to base change conventions).

## Acceptance criteria

```lean
#check HasseWeil.invariantDifferentialPullback_chain  -- or similar name
```

## Progress log
- 2026-04-08 [auto] marked DONE — exists in HasseWeil/InvariantDifferentialPullback.lean
