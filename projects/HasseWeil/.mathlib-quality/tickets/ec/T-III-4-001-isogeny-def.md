# T-III-4-001: Isogeny structure (morphism with O ↦ O)

**Status**: DONE (refactor needed — currently in HasseWeil/Basic.lean)
**Silverman**: III.4 (definition)
**Module**: `HasseWeil/Basic.lean` → `HasseWeil/EC/Isogeny.lean`
**Owner**: (existing)
**Estimated lines**: 0 (existing)
**Difficulty**: trivial
**Stream**: C

## Depends on
- T-III-3-001 (EC defined)
- T-III-3-006 (addition is morphism)

## Blocks
- T-III-4-002 (deg, deg_s, etc.)
- T-III-4-003 ([m] : E → E)

## Statement (Silverman III.4 def)
An **isogeny** from `E₁` to `E₂` is a morphism `φ : E₁ → E₂` of varieties that
is either constant (sending everything to `O₂`) or sends `O₁` to `O₂`.

## Acceptance criteria

Existing in `HasseWeil/Basic.lean`. Confirm:
```lean
#check HasseWeil.Isogeny
```

## Notes
- This ticket is DONE in the current codebase but the definition is somewhat
  axiomatic (it's a structure with a `field`-side ring hom rather than a
  scheme morphism). Refactoring to a more concrete morphism is part of the
  T-MIGRATE-009 ticket.

## Progress log
- 2026-04-08 [auto] marked DONE — exists in HasseWeil/Basic.lean
