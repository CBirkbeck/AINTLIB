import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Scheme fibre-rank of `Spec S → Spec R` over a domain = the `R`-rank of `S`

This is the algebraic core of the **K4** bridge in the endomorphism-degree keystone
(STREAM-KM): the scheme-theoretic fibre rank `Scheme.Hom.finrank` of a finite flat affine
morphism `Spec S ⟶ Spec R`, when `R` is a domain, is *constant* and equal to the module rank
`Module.finrank R S`. Over a domain this rank is the degree `[Frac S : Frac R]` of the
generic-fibre extension — the classical "degree = function-field extension degree" identity
that connects `Scheme.Hom.finrank` (scheme world) to HasseWeil's `Isogeny.degree`
(function-field world).

The proof is a two-step composition of existing mathlib API:
* `Scheme.Hom.finrank_SpecMap_algebraMap` : `finrank (Spec.map (algebraMap R S)) x = rankAtStalk S x`;
* `Module.rankAtStalk_eq` + `Ideal.finrank_fiber_eq_finrank` (the latter needs `IsDomain R`) :
  `rankAtStalk S x = finrank κ(x) (Fiber S x) = finrank R S`.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

/-- **(K4 algebraic core)** For a finite flat algebra `S` over a **domain** `R`, the
scheme-theoretic fibre rank of `Spec S ⟶ Spec R` at any point equals the `R`-module rank of
`S`. Over a domain this module rank is the generic-fibre degree `[Frac S : Frac R]`, so this is
the "scheme fibre-rank = function-field degree" identity in affine algebraic form. -/
lemma finrank_SpecMap_algebraMap_eq_finrank (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [IsDomain R] [Module.Finite R S] [Module.Flat R S] (x : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).finrank x = Module.finrank R S := by
  rw [Scheme.Hom.finrank_SpecMap_algebraMap R S x, Module.rankAtStalk_eq]
  exact x.asIdeal.finrank_fiber_eq_finrank

/-- **(K4 algebraic core, `RingHom` form)** For a finite flat algebra `S` over a **domain** `R`, the
`RingHom.finrank` of `algebraMap R S` at any prime equals the `R`-module rank of `S`. This is the
bare `RingHom.finrank` counterpart of `finrank_SpecMap_algebraMap_eq_finrank`: it turns the `appTop`
ring-map rank produced by `finrank_of_isAffine` (on the affine `Z`-chart of the model) into a
concrete module rank `Module.finrank Γ(Z) Γ([N]⁻¹Z)`, which is then the fibre degree of `[N]`. -/
lemma finrank_algebraMap_eq_module_finrank (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [Module.Finite R S] [Module.Flat R S] (x : PrimeSpectrum R) :
    (algebraMap R S).finrank x = Module.finrank R S := by
  rw [RingHom.finrank_algebraMap, Module.rankAtStalk_eq]
  exact x.asIdeal.finrank_fiber_eq_finrank

end ModularCurves
