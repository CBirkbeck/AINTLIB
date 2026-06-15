# T-IV-2-002: FormalGroupHom F G

**Status**: DONE
**Silverman**: IV.2 (definition)
**Module**: `HasseWeil/FormalGroup/Definition.lean`
**Owner**: worker-A
**Checked out at**: 2026-04-08T19:51Z
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-2-001 (FormalGroup R)

## Blocks
- T-IV-2-006 ([m] : F → F)
- T-IV-4-005 (chain rule)

## Statement (Silverman IV.2 def)
A **homomorphism** from formal group law `F` to `G` over `R` is a power series
`f(T) ∈ R[[T]]` with `f(0) = 0` such that
`f(F(X, Y)) = G(f(X), f(Y))`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- A homomorphism between formal group laws.
    Reference: Silverman IV.2. -/
structure FormalGroupHom (F G : FormalGroup R) where
  toSeries : PowerSeries R
  zero_const : (toSeries.coeff R 0) = 0
  preserves_add : F.subst toSeries = G.subst (toSeries, toSeries)

end HasseWeil.FormalGroup
```

## Notes
- The composition of formal group homs is again a formal group hom.
- Forms a category — `End F` is a (typically noncommutative) ring.

## Progress log
- 2026-04-08T19:51Z [worker-A] checkout. Will add `FormalGroupHom F G` to
  `HasseWeil/FormalGroup/Definition.lean` (same file as `FormalGroup` for now).
  Structure fields: `toSeries : PowerSeries R`, `zero_const`, `preserves_add`.
  The `preserves_add` field expresses `f(F(X,Y)) = G(f(X), f(Y))` via
  `MvPowerSeries.subst`. f is a power series in 1 variable; F and G are in 2
  variables.
- 2026-04-08T20:55Z [worker-A] Complete. Added `FormalGroupHom F G` structure
  with fields `toSeries : PowerSeries R`, `zero_const : constantCoeff toSeries = 0`,
  `preserves_add : f(F(X,Y)) = G(f(X), f(Y))`. Used `PowerSeries.subst` (from
  `Mathlib.RingTheory.PowerSeries.Substitution`) to express substitution of the
  bivariate series into the univariate `f`. `lake build HasseWeil.FormalGroup.Definition`
  passes. NOTE: full project build currently fails in `FrobeniusIsogeny.lean:501-506`
  but that file is untracked and was modified by another worker after my session
  started (20:54 > 18:42); not my issue. Status: DONE.
