# T-IV-1-005: Hensel's Lemma (for power series rings)

**Status**: PARTIAL (mathlib has Hensel for various contexts)
**Silverman**: IV.1.2
**Module**: `HasseWeil/FormalGroup/Curve.lean` (or via mathlib)
**Owner**: (mostly mathlib)
**Estimated lines**: 30
**Difficulty**: easy (use mathlib)
**Stream**: D

## Depends on
- (mathlib)

## Blocks
- T-IV-1-002 (w(z) exists)

## Statement (Silverman IV.1.2)
Let `R` be a complete local ring with maximal ideal `m`. Let
`f(W) ∈ R[[W]]`. If `f(0) ∈ m` and `f'(0) ∉ m`, then there exists a unique
`α ∈ m` with `f(α) = 0`.

## Acceptance criteria

```lean
-- Mathlib has IsAdicComplete.HenselsLemma or similar.
-- Adapt to PowerSeries with the (X)-adic topology.
```

## Notes
- mathlib has hensel-style lemmas in several places (`Polynomial.Hensel`,
  `IsLocalRing.completion`). Pick the right one for our context.

## Progress log
