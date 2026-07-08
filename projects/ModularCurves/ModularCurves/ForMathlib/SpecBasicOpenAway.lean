import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# `Spec` of an away-localization is the basic open (ForMathlib, c4.2a)

`specBasicOpenIsoAway` : `Spec (Localization.Away f) ≅ (Spec A).basicOpen f` as schemes.

Mathlib knows both halves — `Spec.map (algebraMap A (Localization.Away f))` is an open immersion,
and `PrimeSpectrum.localization_away_comap_range` computes its range as the basic open — but does
not package the resulting isomorphism. This is the adapter that turns a morphism defined on
`Spec (Localization.Away f)` into one defined on the open subscheme `D(f)`, which is what gluing
along a basic-open cover needs.

Upstream candidate.
-/

open AlgebraicGeometry CategoryTheory

/-- `Spec` of an away-localization is (isomorphic to) the corresponding basic open. -/
noncomputable def specBasicOpenIsoAway (A : CommRingCat) (f : A) :
    letI U : (Spec A).Opens := PrimeSpectrum.basicOpen f
    Spec (CommRingCat.of (Localization.Away f)) ≅ U.toScheme := by
  letI U : (Spec A).Opens := PrimeSpectrum.basicOpen f
  refine IsOpenImmersion.isoOfRangeEq
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))) U.ι ?_
  rw [Scheme.Opens.range_ι]
  exact PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
