# T-IV-1-008: Formal addition F(z₁, z₂)

**Status**: DONE (FormalGroup.lean)
**Silverman**: IV.1
**Module**: `HasseWeil/FormalGroup.lean` → `HasseWeil/FormalGroup/Curve.lean`
**Owner**: (existing)
**Estimated lines**: 0 (existing)
**Difficulty**: trivial
**Stream**: D

## Depends on
- T-IV-1-002 (w(z))
- T-IV-1-006 (x(z), y(z))

## Blocks
- T-IV-2-005 (Ê)
- T-IV-BRIDGE-003 (formal addition for isogenies)

## Statement (Silverman IV.1)
The group law on `E` written in the `(z, w)` chart at `O` gives a formal power
series `F(z₁, z₂) ∈ ℤ[a₁..a₆][[z₁, z₂]]` such that `z(P + Q) = F(z(P), z(Q))`
formally near `O`.

## Acceptance criteria

Existing in `HasseWeil/FormalGroup.lean`. Confirm:
```lean
#check HasseWeil.formalGroupLaw  -- or similar name
```

## Progress log
- 2026-04-08 [auto] marked DONE — exists in HasseWeil/FormalGroup.lean
