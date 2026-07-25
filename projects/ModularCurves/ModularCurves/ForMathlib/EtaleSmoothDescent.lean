/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.EtaleH1Descent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smoothness descends along finite étale faithfully flat covers

**[T-YR-6 (c1-E)]** If `B` is a finite étale faithfully flat `A`-algebra which is
smooth over a noetherian base `k`, then `A` is smooth over `k`.

* the `Ω`-half: `Ω[B⁄k] ≃ B ⊗[A] Ω[A⁄k]` (étale base change), so flatness of
  `Ω[A⁄k]` descends and finite presentation upgrades it to projectivity;
* the `H¹`-half is `Algebra.subsingleton_h1Cotangent_of_etale_faithfullyFlat`;
* finite presentation of `A` over `k` is the Artin–Tate lemma.
-/

open TensorProduct

namespace Algebra

section Dimension

variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]

/-- The relative dimension of a standard smooth algebra is unique. -/
theorem IsStandardSmoothOfRelativeDimension.eq_of_nontrivial [Nontrivial C] {m n : ℕ}
    [IsStandardSmoothOfRelativeDimension m R C]
    [IsStandardSmoothOfRelativeDimension n R C] : m = n := by
  have h1 : Module.rank C Ω[C⁄R] = m :=
    IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential m
  have h2 : Module.rank C Ω[C⁄R] = n :=
    IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  exact_mod_cast h1.symm.trans h2

/-- A standard smooth algebra is standard smooth of relative dimension the rank of
its module of differentials. -/
theorem IsStandardSmoothOfRelativeDimension.of_isStandardSmooth [Nontrivial C]
    [Algebra.FinitePresentation R C] [IsStandardSmooth R C] :
    IsStandardSmoothOfRelativeDimension (Module.finrank C Ω[C⁄R]) R C := by
  rw [IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  exact (Module.finrank_eq_rank C Ω[C⁄R]).symm

end Dimension


variable (k A B : Type*) [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- **[T-YR-6 (c1-E), `Ω`-half]** Projectivity of the module of differentials
descends along formally étale faithfully flat extensions. -/
theorem projective_kaehlerDifferential_of_formallyEtale_faithfullyFlat
    [Algebra.FormallyEtale A B] [Module.FaithfullyFlat A B]
    [Algebra.FinitePresentation k A] [Module.Projective B Ω[B⁄k]] :
    Module.Projective A Ω[A⁄k] := by
  haveI : Module.Flat B (B ⊗[A] Ω[A⁄k]) :=
    Module.Flat.of_linearEquiv
      (KaehlerDifferential.isBaseChange_of_formallyEtale k A B).equiv
  haveI : Module.Flat A Ω[A⁄k] :=
    Module.Flat.of_flat_tensorProduct (R := A) Ω[A⁄k] B
  exact Module.Flat.projective_of_finitePresentation

/-- **[T-YR-6 (c1-E)]** Smoothness descends along finite étale faithfully flat
extensions (over a noetherian base). -/
theorem smooth_of_etale_faithfullyFlat [IsNoetherianRing k]
    [Algebra.Etale A B] [Module.Finite A B] [Module.FaithfullyFlat A B]
    [Algebra.Smooth k B] : Algebra.Smooth k A := by
  haveI : Algebra.FiniteType k A :=
    ⟨fg_of_fg_of_fg (A := k) (B := A) (C := B)
      Algebra.FiniteType.out Module.Finite.fg_top
      (FaithfulSMul.algebraMap_injective A B)⟩
  haveI : Algebra.FinitePresentation k A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨⟨projective_kaehlerDifferential_of_formallyEtale_faithfullyFlat k A B,
    subsingleton_h1Cotangent_of_etale_faithfullyFlat k A B⟩, inferInstance⟩

section RelativeDimension

variable [IsNoetherianRing k] [Algebra.Etale A B] [Module.Finite A B]
  [Module.FaithfullyFlat A B]

/-- (Implementation) On a standard smooth basic open `A[1/f]` of `A`, the relative
dimension over `k` is forced to be `1` by comparison with the étale cover. -/
theorem isStandardSmoothOfRelativeDimension_one_localizationAway
    [IsStandardSmoothOfRelativeDimension 1 k B]
    (p : Ideal A) [p.IsPrime] (f : A) (hf : f ∉ p)
    [IsStandardSmooth k (Localization.Away f)] :
    IsStandardSmoothOfRelativeDimension 1 k (Localization.Away f) := by
  -- `A[1/f]` is nontrivial, being a localization away from a prime's complement
  haveI hprime : (Ideal.map (algebraMap A (Localization.Away f)) p).IsPrime := by
    apply IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_›
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  haveI hntA : Nontrivial (Localization.Away f) := by
    rcases subsingleton_or_nontrivial (Localization.Away f) with h | h
    · refine absurd (Ideal.eq_top_iff_one _ |>.mpr ?_) hprime.ne_top
      rw [Subsingleton.elim (1 : Localization.Away f) 0]
      exact Submodule.zero_mem _
    · exact h
  -- a prime of `B` over `p`, so `B[1/f]` is nontrivial too
  obtain ⟨P, hP, hPo⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := B) p
  haveI := hP
  have hfP : algebraMap A B f ∉ P := by
    intro h
    exact hf (by rw [hPo.over]; exact h)
  haveI hprimeB : (Ideal.map (algebraMap B (Localization.Away (algebraMap A B f))) P).IsPrime := by
    apply IsLocalization.isPrime_of_isPrime_disjoint (.powers (algebraMap A B f)) _ _ ‹_›
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  haveI hntB : Nontrivial (Localization.Away (algebraMap A B f)) := by
    rcases subsingleton_or_nontrivial (Localization.Away (algebraMap A B f)) with h | h
    · refine absurd (Ideal.eq_top_iff_one _ |>.mpr ?_) hprimeB.ne_top
      rw [Subsingleton.elim (1 : Localization.Away (algebraMap A B f)) 0]
      exact Submodule.zero_mem _
    · exact h
  -- the localized cover `A[1/f] → B[1/f]`
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap A B f)) :=
    (Localization.awayMap (algebraMap A B) f).toAlgebra
  haveI : IsScalarTower A (Localization.Away f)
      (Localization.Away (algebraMap A B f)) :=
    IsScalarTower.of_algebraMap_eq' (by
      show (algebraMap B (Localization.Away (algebraMap A B f))).comp (algebraMap A B) =
        (Localization.awayMap (algebraMap A B) f).comp (algebraMap A (Localization.Away f))
      exact (IsLocalization.map_comp
        (M := Submonoid.powers f) (S := Localization.Away f)
        (T := Submonoid.powers (algebraMap A B f))
        (Q := Localization.Away (algebraMap A B f)) _).symm)
  haveI : IsScalarTower k (Localization.Away f)
      (Localization.Away (algebraMap A B f)) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [IsScalarTower.algebraMap_apply k A (Localization.Away f),
      ← IsScalarTower.algebraMap_apply A (Localization.Away f)
        (Localization.Away (algebraMap A B f)),
      IsScalarTower.algebraMap_apply A B (Localization.Away (algebraMap A B f)),
      ← IsScalarTower.algebraMap_apply k A B,
      ← IsScalarTower.algebraMap_apply k B (Localization.Away (algebraMap A B f))]
  haveI : Algebra.Etale (Localization.Away f) (Localization.Away (algebraMap A B f)) :=
    Algebra.Etale.of_restrictScalars A (Localization.Away f)
      (Localization.Away (algebraMap A B f))
  haveI hssB : IsStandardSmooth k B :=
    IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  haveI hsmB : Algebra.Smooth k B := inferInstance
  haveI hsmA : Algebra.Smooth k A := smooth_of_etale_faithfullyFlat k A B
  haveI : Algebra.FinitePresentation k A := hsmA.finitePresentation
  haveI : Algebra.FinitePresentation k (Localization.Away f) :=
    Algebra.FinitePresentation.trans (R := k) (A := A) (B := Localization.Away f)
  -- both relative dimensions land on `B[1/f]`
  haveI h0 : IsStandardSmoothOfRelativeDimension 0 (Localization.Away f)
      (Localization.Away (algebraMap A B f)) :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  haveI hn : IsStandardSmoothOfRelativeDimension
      (Module.finrank (Localization.Away f) Ω[Localization.Away f⁄k]) k
      (Localization.Away f) :=
    IsStandardSmoothOfRelativeDimension.of_isStandardSmooth
  haveI hcomp1 := IsStandardSmoothOfRelativeDimension.trans
    (n := Module.finrank (Localization.Away f) Ω[Localization.Away f⁄k]) (m := 0)
    (R := k) (S := Localization.Away f) (T := Localization.Away (algebraMap A B f))
  haveI hloc0 : IsStandardSmoothOfRelativeDimension 0 B
      (Localization.Away (algebraMap A B f)) :=
    IsStandardSmoothOfRelativeDimension.localization_away (algebraMap A B f)
  haveI hcomp2 := IsStandardSmoothOfRelativeDimension.trans (n := 1) (m := 0)
    (R := k) (S := B) (T := Localization.Away (algebraMap A B f))
  have hone : Module.finrank (Localization.Away f) Ω[Localization.Away f⁄k] = 1 := by
    have := IsStandardSmoothOfRelativeDimension.eq_of_nontrivial
      (R := k) (C := Localization.Away (algebraMap A B f))
      (m := 0 + Module.finrank (Localization.Away f) Ω[Localization.Away f⁄k]) (n := 0 + 1)
    omega
  exact hone ▸ hn

end RelativeDimension

universe u

/-- **[T-YR-6 (c1)]** Smoothness of relative dimension one descends along finite
étale faithfully flat covers: if `B` is finite étale and faithfully flat over `A`
and standard smooth of relative dimension one over the noetherian base `k`, then
`A` is locally standard smooth of relative dimension one over `k`. -/
theorem locally_isStandardSmoothOfRelativeDimension_one_of_etale_faithfullyFlat
    (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [IsNoetherianRing k] [Algebra.Etale A B] [Module.Finite A B]
    [Module.FaithfullyFlat A B] [IsStandardSmoothOfRelativeDimension 1 k B] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap k A) := by
  haveI hssB : IsStandardSmooth k B :=
    IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  haveI hsmA : Algebra.Smooth k A := smooth_of_etale_faithfullyFlat k A B
  haveI : Algebra.FinitePresentation k A := hsmA.finitePresentation
  -- at every prime of `A`, a standard smooth basic open neighbourhood
  have hsm : ∀ p : PrimeSpectrum A, IsSmoothAt k p.asIdeal := fun p => by
    have h := Algebra.smoothLocus_eq_univ (R := k) (A := A)
    have : p ∈ Algebra.smoothLocus k A := by rw [h]; trivial
    exact this
  choose f hf hstd using fun p : PrimeSpectrum A =>
    @IsSmoothAt.exists_notMem_isStandardSmooth k A _ _ _ _ p.asIdeal p.isPrime (hsm p)
  refine RingHom.locally_of_exists
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso) _ f ?_
    (fun p => Localization.Away (f p)) (fun p => ?_)
  · -- the `f p` generate the unit ideal: none of them lies in its own prime
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    haveI : m.IsPrime := hm.isPrime
    exact hf ⟨m, inferInstance⟩ (hle (Ideal.subset_span ⟨⟨m, inferInstance⟩, rfl⟩))
  · haveI := hstd p
    haveI : IsStandardSmoothOfRelativeDimension 1 k (Localization.Away (f p)) :=
      isStandardSmoothOfRelativeDimension_one_localizationAway k A B
        p.asIdeal (f p) (hf p)
    rw [show (algebraMap A (Localization.Away (f p))).comp (algebraMap k A) =
      algebraMap k (Localization.Away (f p)) from
      (IsScalarTower.algebraMap_eq k A (Localization.Away (f p))).symm]
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr inferInstance

end Algebra

namespace AlgebraicGeometry

open Algebra

universe u

/-- **[T-YR-6 (c1), scheme level]** If `Spec B ⟶ Spec A` is a finite étale
faithfully flat cover and `Spec B ⟶ Spec k` is smooth of relative dimension one,
then so is `Spec A ⟶ Spec k`. -/
theorem smoothOfRelativeDimension_one_spec_map_of_etale_faithfullyFlat
    (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [IsNoetherianRing k] [Algebra.Etale A B] [Module.Finite A B]
    [Module.FaithfullyFlat A B] [IsStandardSmoothOfRelativeDimension 1 k B] :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact locally_isStandardSmoothOfRelativeDimension_one_of_etale_faithfullyFlat k A B

end AlgebraicGeometry
