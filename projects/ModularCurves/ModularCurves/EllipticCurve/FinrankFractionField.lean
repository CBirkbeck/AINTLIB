import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Algebraic.Integral

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

/-- **(K4 bridge, function-field form)** For a finite flat algebra `S` over a **domain** `R` with
`R → S` faithful (`S` a domain too), the scheme fibre rank of `Spec S ⟶ Spec R` equals the degree
`[Frac S : Frac R]` of the induced extension of fraction fields, for *any* chosen fraction fields
`FR = Frac R`, `FS = Frac S` sitting in a compatible scalar tower. Combines the affine
fibre-rank = module-rank identity (`finrank_SpecMap_algebraMap_eq_finrank`) with the
localisation-invariance of `finrank` (`Algebra.IsAlgebraic.finrank_of_isFractionRing`, valid since a
finite algebra is integral hence algebraic). This is the "scheme fibre rank = function-field degree"
bridge in its reusable affine form — the identity at the heart of the `[N]`-degree keystone (with
`FR = FS = K(E)` and the extension taken along `[N]`) and its arbitrary-`E/S` generalisation. -/
lemma finrank_SpecMap_eq_functionField_finrank (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [IsDomain R] [IsDomain S] [Module.Finite R S] [Module.Flat R S] [FaithfulSMul R S]
    (FR FS : Type u) [Field FR] [Field FS] [Algebra R FR] [IsFractionRing R FR] [Algebra S FS]
    [IsFractionRing S FS] [Algebra R FS] [Algebra FR FS] [IsScalarTower R FR FS]
    [IsScalarTower R S FS] (x : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).finrank x = Module.finrank FR FS := by
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  haveI : Algebra.IsAlgebraic R S := Algebra.IsIntegral.isAlgebraic
  rw [finrank_SpecMap_algebraMap_eq_finrank R S x]
  exact (Algebra.IsAlgebraic.finrank_of_isFractionRing R FR S FS).symm

end ModularCurves
