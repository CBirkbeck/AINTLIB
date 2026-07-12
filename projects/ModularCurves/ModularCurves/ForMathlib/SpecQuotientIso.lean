/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.ForMathlib.SurjectiveFreeSameRank
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Same-rank closed immersion of affines is an isomorphism (YFULL route γ)

If `R` is a finite flat `R₀`-algebra and `I : Ideal R` is such that the quotient `R ⧸ I` is
again finite flat over `R₀` of the *same rank at every prime of `R₀`*, then the quotient map
`R ⟶ R ⧸ I` is an isomorphism (equivalently `I = ⊥`), and `Spec.map` of it is an
isomorphism of schemes.

This is the affine, ready-to-consume form of the same-degree-effective-Cartier-divisor
equality (`Y(N)` clopen argument): a closed subscheme of a finite locally free `R₀`-scheme
that has the same fibre rank everywhere is the whole scheme. It is a direct application of
`bijective_of_surjective_ringHom_of_flat_rankAtStalk_eq`.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

/-- A quotient of a finite flat `R₀`-algebra `R` by an ideal `I` whose quotient has the same
stalkwise rank as `R` is the trivial quotient: `Ideal.Quotient.mk I` is bijective. -/
theorem bijective_quotient_of_flat_rankAtStalk_eq {R₀ R : Type u} [CommRing R₀] [CommRing R]
    [Algebra R₀ R] [Module.Finite R₀ R] [Module.Flat R₀ R] (I : Ideal R)
    [Module.Finite R₀ (R ⧸ I)] [Module.Flat R₀ (R ⧸ I)]
    (h : ∀ p : PrimeSpectrum R₀,
      Module.rankAtStalk (R := R₀) R p = Module.rankAtStalk (R := R₀) (R ⧸ I) p) :
    Function.Bijective (Ideal.Quotient.mk I) :=
  bijective_of_surjective_ringHom_of_flat_rankAtStalk_eq h (Ideal.Quotient.mk I)
    (fun _ => rfl) Ideal.Quotient.mk_surjective

/-- Under the hypotheses above, `Spec.map (Ideal.Quotient.mk I)` is an isomorphism — the
closed immersion `Spec (R ⧸ I) ⟶ Spec R` is an isomorphism. -/
theorem isIso_SpecMap_quotient_of_flat_rankAtStalk_eq {R₀ R : Type u} [CommRing R₀] [CommRing R]
    [Algebra R₀ R] [Module.Finite R₀ R] [Module.Flat R₀ R] (I : Ideal R)
    [Module.Finite R₀ (R ⧸ I)] [Module.Flat R₀ (R ⧸ I)]
    (h : ∀ p : PrimeSpectrum R₀,
      Module.rankAtStalk (R := R₀) R p = Module.rankAtStalk (R := R₀) (R ⧸ I) p) :
    IsIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  haveI : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_quotient_of_flat_rankAtStalk_eq I h)
  infer_instance

end ModularCurves
