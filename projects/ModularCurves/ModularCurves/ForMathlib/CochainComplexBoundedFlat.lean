/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Flat.Localization
import ModularCurves.ForMathlib.LowDegreeFiniteProjectiveReplacement

/-!
# Bounded flat cochain complexes

This file translates between categorical homology of cochain complexes of modules and the
explicit kernels and quotients used by the algebraic base-change API.
-/

open CategoryTheory
open TensorProduct
open scoped BigOperators

universe u v w

namespace ModularCurves

variable {R : Type u} [CommRing R]

/-- Flat scalar extension carries an explicit kernel/range homology quotient to the
categorical homology of the base-changed short complex. -/
noncomputable def LinearMap.baseChangeHomologyEquiv_of_flat
    {P Q T : Type v}
    [AddCommGroup P] [AddCommGroup Q] [AddCommGroup T]
    [Module R P] [Module R Q] [Module R T]
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) (h : g ∘ₗ f = 0)
    (A : Type w) [CommRing A] [Algebra R A] [Module.Flat R A] :
    (A ⊗[R]
      (LinearMap.ker g ⧸
        LinearMap.range (LinearMap.codRestrictToKer f g h))) ≃ₗ[A]
      (ShortComplex.moduleCatMk
        (f.baseChange A) (g.baseChange A)
        (LinearMap.baseChange_comp_eq_zero f g h A)).homology := by
  let p := LinearMap.range (LinearMap.codRestrictToKer f g h)
  let eTensor :=
    TensorProduct.AlgebraTensorModule.tensorQuotientEquiv
      (R := R) A R A p
  have hrange :
      LinearMap.range
          ((LinearMap.codRestrictToKer f g h).baseChange A) =
        LinearMap.range
          (TensorProduct.AlgebraTensorModule.lTensor A A p.subtype) := by
    change LinearMap.range
        (TensorProduct.AlgebraTensorModule.lTensor A A
          (LinearMap.codRestrictToKer f g h)) =
      LinearMap.range
        (TensorProduct.AlgebraTensorModule.lTensor A A p.subtype)
    apply SetLike.ext
    intro x
    change x ∈ LinearMap.range
        (LinearMap.lTensor A (LinearMap.codRestrictToKer f g h)) ↔
      x ∈ LinearMap.range (LinearMap.lTensor A p.subtype)
    rw [LinearMap.lTensor_range A]
  let eRange := Submodule.quotEquivOfEq
    (LinearMap.range
      (TensorProduct.AlgebraTensorModule.lTensor A A p.subtype))
    (LinearMap.range
      ((LinearMap.codRestrictToKer f g h).baseChange A))
    hrange.symm
  let eHomology := LinearMap.baseChangeHomologyOneEquiv
    f g h A (kerBaseChangeComparison_bijective_of_flat A g)
  exact eTensor.trans eRange |>.trans eHomology

/-- Under flat scalar extension, exactness of a pair is equivalent to vanishing of the
tensor extension of its explicit homology. -/
theorem LinearMap.baseChange_exact_iff_subsingleton_tensor_homology_of_flat
    {P Q T : Type v}
    [AddCommGroup P] [AddCommGroup Q] [AddCommGroup T]
    [Module R P] [Module R Q] [Module R T]
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) (h : g ∘ₗ f = 0)
    (A : Type w) [CommRing A] [Algebra R A] [Module.Flat R A] :
    Function.Exact (f.baseChange A) (g.baseChange A) ↔
      Subsingleton
        (A ⊗[R]
          (LinearMap.ker g ⧸
            LinearMap.range
              (LinearMap.codRestrictToKer f g h))) := by
  let S := ShortComplex.moduleCatMk
    (f.baseChange A) (g.baseChange A)
    (LinearMap.baseChange_comp_eq_zero f g h A)
  let e := LinearMap.baseChangeHomologyEquiv_of_flat f g h A
  constructor
  · intro hexact
    have hS : S.Exact :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
        hexact
    have hzero : Limits.IsZero S.homology :=
      (S.exact_iff_isZero_homology).mp hS
    have hsub : Subsingleton S.homology :=
      ModuleCat.isZero_iff_subsingleton.mp hzero
    exact (Equiv.subsingleton_congr e.toEquiv).mpr hsub
  · intro hsub
    letI : Subsingleton
        (A ⊗[R]
          (LinearMap.ker g ⧸
            LinearMap.range
              (LinearMap.codRestrictToKer f g h))) := hsub
    letI : Subsingleton S.homology :=
      (Equiv.subsingleton_congr e.toEquiv).mp inferInstance
    have hzero : Limits.IsZero S.homology :=
      ModuleCat.isZero_iff_subsingleton.mpr inferInstance
    exact
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp
        ((S.exact_iff_isZero_homology).mpr hzero)

/-- Exactness of a pair with finite homology after localization at a prime spreads to a
principal neighborhood of that prime. -/
theorem LinearMap.exists_away_baseChange_exact_of_localizationAtPrime_of_finite_homology
    {P Q T : Type v}
    [AddCommGroup P] [AddCommGroup Q] [AddCommGroup T]
    [Module R P] [Module R Q] [Module R T]
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) (h : g ∘ₗ f = 0)
    [Module.Finite R
      (LinearMap.ker g ⧸
        LinearMap.range (LinearMap.codRestrictToKer f g h))]
    (p : Ideal R) [p.IsPrime]
    (hexact : Function.Exact
      (f.baseChange (Localization.AtPrime p))
      (g.baseChange (Localization.AtPrime p))) :
    ∃ r : R, r ∉ p ∧
      Function.Exact
        (f.baseChange (Localization.Away r))
        (g.baseChange (Localization.Away r)) := by
  let H :=
    LinearMap.ker g ⧸
      LinearMap.range (LinearMap.codRestrictToKer f g h)
  letI : Subsingleton ((Localization.AtPrime p) ⊗[R] H) :=
    (LinearMap.baseChange_exact_iff_subsingleton_tensor_homology_of_flat
      f g h (Localization.AtPrime p)).mp hexact
  letI : Subsingleton (LocalizedModule p.primeCompl H) :=
    (LocalizedModule.equivTensorProduct
      p.primeCompl H).toEquiv.subsingleton_congr.mpr inferInstance
  obtain ⟨r, hr, haway⟩ :=
    LocalizedModule.exists_subsingleton_away (M := H) p
  have htensor : Subsingleton (Localization.Away r ⊗[R] H) :=
    (LocalizedModule.equivTensorProduct
      (Submonoid.powers r) H).toEquiv.subsingleton_congr.mp haway
  exact ⟨r, hr,
    (LinearMap.baseChange_exact_iff_subsingleton_tensor_homology_of_flat
      f g h (Localization.Away r)).mpr htensor⟩

/-- Exactness in a finite range after localization at a prime spreads to one common
principal neighborhood when every explicit homology module in that range is finite. -/
theorem LinearMap.exists_away_baseChange_exact_of_bounded_localizationAtPrime_of_finite_homology
    (M : ℕ → Type v)
    [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (d : ∀ n, M n →ₗ[R] M (n + 1))
    (N : ℕ)
    (hcomp : ∀ n, d (n + 1) ∘ₗ d n = 0)
    (hfinite : ∀ n, n < N →
      Module.Finite R
        (LinearMap.ker (d (n + 1)) ⧸
          LinearMap.range
            (LinearMap.codRestrictToKer
              (d n) (d (n + 1)) (hcomp n))))
    (p : Ideal R) [p.IsPrime]
    (hexact : ∀ n, n < N →
      Function.Exact
        ((d n).baseChange (Localization.AtPrime p))
        ((d (n + 1)).baseChange (Localization.AtPrime p))) :
    ∃ r : R, r ∉ p ∧
      ∀ n, n < N →
        Function.Exact
          ((d n).baseChange (Localization.Away r))
          ((d (n + 1)).baseChange (Localization.Away r)) := by
  let H : Fin N → Type v := fun i ↦
    LinearMap.ker (d (i + 1)) ⧸
      LinearMap.range
        (LinearMap.codRestrictToKer
          (d i) (d (i + 1)) (hcomp i))
  letI hFinite (i : Fin N) : Module.Finite R (H i) :=
    hfinite i i.isLt
  letI hLocal (i : Fin N) :
      Subsingleton (LocalizedModule p.primeCompl (H i)) := by
    have htensor :
        Subsingleton ((Localization.AtPrime p) ⊗[R] H i) :=
      (LinearMap.baseChange_exact_iff_subsingleton_tensor_homology_of_flat
        (d i) (d (i + 1)) (hcomp i)
        (Localization.AtPrime p)).mp
          (hexact i i.isLt)
    exact
      (LocalizedModule.equivTensorProduct
        p.primeCompl (H i)).toEquiv.subsingleton_congr.mpr htensor
  choose r hr haway using fun i : Fin N ↦
    LocalizedModule.exists_subsingleton_away (M := H i) p
  let s : R := ∏ i, r i
  have hs : s ∉ p := by
    exact p.primeCompl.prod_mem fun i _ ↦ hr i
  refine ⟨s, hs, ?_⟩
  intro n hn
  let i : Fin N := ⟨n, hn⟩
  have hsupp :
      Module.support R (H i) ⊆
        PrimeSpectrum.zeroLocus {r i} :=
    LocalizedModule.subsingleton_iff_support_subset.mp (haway i)
  have hsuppS :
      Module.support R (H i) ⊆
        PrimeSpectrum.zeroLocus {s} := by
    intro x hx
    have hri : r i ∈ x.asIdeal := by
      simpa using hsupp hx
    have hdiv : r i ∣ s := by
      dsimp only [s]
      exact Finset.dvd_prod_of_mem (fun j ↦ r j)
        (Finset.mem_univ i)
    obtain ⟨t, ht⟩ := hdiv
    have hst : s ∈ x.asIdeal := by
      rw [ht]
      exact x.asIdeal.mul_mem_right t hri
    simpa using hst
  have hawayS : Subsingleton (LocalizedModule.Away s (H i)) :=
    LocalizedModule.subsingleton_iff_support_subset.mpr hsuppS
  have htensorS : Subsingleton (Localization.Away s ⊗[R] H i) :=
    (LocalizedModule.equivTensorProduct
      (Submonoid.powers s) (H i)).toEquiv.subsingleton_congr.mp
        hawayS
  exact
    (LinearMap.baseChange_exact_iff_subsingleton_tensor_homology_of_flat
      (d n) (d (n + 1)) (hcomp n)
      (Localization.Away s)).mpr htensorS

/-- Flat scalar extension preserves finite generation of the homology of a short complex of
modules. -/
theorem ShortComplex.moduleFinite_baseChangeHomology_of_flat
    (S : ShortComplex (ModuleCat.{v} R))
    (A : Type w) [CommRing A] [Algebra R A] [Module.Flat R A]
    [Module.Finite R S.homology] :
    Module.Finite A
      (ShortComplex.moduleCatMk
        (S.f.hom.baseChange A) (S.g.hom.baseChange A)
        (LinearMap.baseChange_comp_eq_zero S.f.hom S.g.hom
          (shortComplexModuleCatCompEqZero S) A)).homology := by
  let h := shortComplexModuleCatCompEqZero S
  letI : Module.Finite R
      (LinearMap.ker S.g.hom ⧸
        LinearMap.range
          (LinearMap.codRestrictToKer S.f.hom S.g.hom h)) := by
    change Module.Finite R
      (LinearMap.ker S.g.hom ⧸
        LinearMap.range S.moduleCatToCycles)
    exact Module.Finite.quotient_range_moduleCatToCycles S
  letI : Module.Finite A
      (A ⊗[R]
        (LinearMap.ker S.g.hom ⧸
          LinearMap.range
            (LinearMap.codRestrictToKer S.f.hom S.g.hom h))) :=
    Module.Finite.base_change R A _
  exact Module.Finite.equiv
    (LinearMap.baseChangeHomologyEquiv_of_flat
      S.f.hom S.g.hom h A)

/-- Flat categorical extension of scalars preserves finite generation of short-complex
homology. -/
theorem ShortComplex.moduleFinite_map_extendScalars_homology_of_flat
    (S : ShortComplex (ModuleCat.{v} R))
    (A : Type v) [CommRing A] [Algebra R A] [Module.Flat R A]
    [Module.Finite R S.homology] :
    Module.Finite A
      ((S.map
        (ModuleCat.extendScalars.{u, v, v} (algebraMap R A))).homology) := by
  letI :=
    ModularCurves.ShortComplex.moduleFinite_baseChangeHomology_of_flat S A
  exact Module.Finite.equiv
    (ShortComplex.homologyMapIso
      (shortComplexModuleCatMkBaseChangeIso S A)).toLinearEquiv

/-- A bounded cochain complex of flat modules with finite homology is exact over the base when
it is exact after every field base change. -/
theorem HomologicalComplex.functionExact_of_bounded_flat_forall_field_baseChange_exact_of_finite_homology
    (C : CochainComplex (ModuleCat.{v} R) ℕ)
    [∀ q, Module.Flat R (C.X q)]
    [∀ q, Module.Finite R (C.homology q)]
    (N : ℕ) [Subsingleton (C.X (N + 1))]
    (hfield : ∀ q, q < N → ∀ (K : Type u) [Field K] [Algebra R K],
      Function.Exact
        ((C.d q (q + 1)).hom.baseChange K)
        ((C.d (q + 1) (q + 2)).hom.baseChange K))
    (q : ℕ) (hq : q < N) :
    Function.Exact (C.d q (q + 1)).hom (C.d (q + 1) (q + 2)).hom := by
  let M : ℕ → Type v := fun i ↦ C.X i
  let d : ∀ i, M i →ₗ[R] M (i + 1) := fun i ↦ (C.d i (i + 1)).hom
  have hcomp : ∀ i, d (i + 1) ∘ₗ d i = 0 := by
    intro i
    exact shortComplexModuleCatCompEqZero (C.sc' i (i + 1) (i + 2))
  have hfinite : ∀ i, i < N →
      Module.Finite R
        (LinearMap.ker (d (i + 1)) ⧸
          LinearMap.range
            (LinearMap.codRestrictToKer (d i) (d (i + 1)) (hcomp i))) := by
    intro i _
    let S := C.sc' i (i + 1) (i + 2)
    have hprev : (ComplexShape.up ℕ).prev (i + 1) = i :=
      CochainComplex.prev_nat_succ i
    have hnext : (ComplexShape.up ℕ).next (i + 1) = i + 2 := by
      rw [CochainComplex.next]
      omega
    letI : Module.Finite R S.homology :=
      Module.Finite.equiv
        (C.homologyIsoSc' i (i + 1) (i + 2) hprev hnext).toLinearEquiv
    exact Module.Finite.quotient_range_moduleCatToCycles S
  exact LinearMap.exact_of_bounded_flat_forall_field_baseChange_exact_of_finite_homology
    M d N hcomp hfinite hfield q hq

/-- A bounded flat cochain complex with finite homology over a local ring is exact when its
residue-field base change is exact. -/
theorem
  HomologicalComplex.functionExact_of_bounded_flat_residueField_baseChange_exact_of_finite_homology
    [IsLocalRing R]
    (C : CochainComplex (ModuleCat.{v} R) ℕ)
    [∀ q, Module.Flat R (C.X q)]
    [∀ q, Module.Finite R (C.homology q)]
    (N : ℕ) [Subsingleton (C.X (N + 1))]
    (hresidue : ∀ q, q < N →
      Function.Exact
        ((C.d q (q + 1)).hom.baseChange (IsLocalRing.ResidueField R))
        ((C.d (q + 1) (q + 2)).hom.baseChange
          (IsLocalRing.ResidueField R)))
    (q : ℕ) (hq : q < N) :
    Function.Exact
      (C.d q (q + 1)).hom
      (C.d (q + 1) (q + 2)).hom := by
  let M : ℕ → Type v := fun i ↦ C.X i
  let d : ∀ i, M i →ₗ[R] M (i + 1) :=
    fun i ↦ (C.d i (i + 1)).hom
  have hcomp : ∀ i, d (i + 1) ∘ₗ d i = 0 := by
    intro i
    exact shortComplexModuleCatCompEqZero
      (C.sc' i (i + 1) (i + 2))
  have hfinite : ∀ i, i < N →
      Module.Finite R
        (LinearMap.ker (d (i + 1)) ⧸
          LinearMap.range
            (LinearMap.codRestrictToKer
              (d i) (d (i + 1)) (hcomp i))) := by
    intro i _
    let S := C.sc' i (i + 1) (i + 2)
    have hprev : (ComplexShape.up ℕ).prev (i + 1) = i :=
      CochainComplex.prev_nat_succ i
    have hnext : (ComplexShape.up ℕ).next (i + 1) = i + 2 := by
      rw [CochainComplex.next]
      omega
    letI : Module.Finite R S.homology :=
      Module.Finite.equiv
        (C.homologyIsoSc' i (i + 1) (i + 2)
          hprev hnext).toLinearEquiv
    exact Module.Finite.quotient_range_moduleCatToCycles S
  exact
    LinearMap.exact_of_bounded_flat_residueField_baseChange_exact_of_finite_homology
      M d N hcomp hfinite hresidue q hq

/-- For a bounded flat cochain complex with finite homology, exactness on a residue fibre
implies exactness after localization at that fibre's prime. -/
theorem
  HomologicalComplex.functionExact_localizationAtPrime_of_residueField_exact_of_finite_homology
    (C : CochainComplex (ModuleCat.{v} R) ℕ)
    [∀ q, Module.Flat R (C.X q)]
    [∀ q, Module.Finite R (C.homology q)]
    (N : ℕ) [Subsingleton (C.X (N + 1))]
    (p : Ideal R) [p.IsPrime]
    (hresidue : ∀ q, q < N →
      Function.Exact
        ((C.d q (q + 1)).hom.baseChange p.ResidueField)
        ((C.d (q + 1) (q + 2)).hom.baseChange p.ResidueField))
    (q : ℕ) (hq : q < N) :
    Function.Exact
      ((C.d q (q + 1)).hom.baseChange (Localization.AtPrime p))
      ((C.d (q + 1) (q + 2)).hom.baseChange
        (Localization.AtPrime p)) := by
  let A := Localization.AtPrime p
  let M : ℕ → Type (max u v) :=
    fun i ↦ A ⊗[R] C.X i
  let d : ∀ i, M i →ₗ[A] M (i + 1) :=
    fun i ↦ (C.d i (i + 1)).hom.baseChange A
  letI : Module.Flat R A := by
    dsimp only [A]
    infer_instance
  letI : ∀ i, AddCommGroup (M i) := fun i ↦ inferInstance
  letI : ∀ i, Module A (M i) := fun i ↦ inferInstance
  letI : ∀ i, Module.Flat A (M i) := fun i ↦
    Module.Flat.baseChange R A (C.X i)
  letI : Subsingleton (M (N + 1)) := inferInstance
  have hcomp : ∀ i, d (i + 1) ∘ₗ d i = 0 := by
    intro i
    exact LinearMap.baseChange_comp_eq_zero
      (C.d i (i + 1)).hom
      (C.d (i + 1) (i + 2)).hom
      (shortComplexModuleCatCompEqZero
        (C.sc' i (i + 1) (i + 2))) A
  have hfinite : ∀ i, i < N →
      Module.Finite A
        (LinearMap.ker (d (i + 1)) ⧸
          LinearMap.range
            (LinearMap.codRestrictToKer
              (d i) (d (i + 1)) (hcomp i))) := by
    intro i _
    let S := C.sc' i (i + 1) (i + 2)
    have hprev : (ComplexShape.up ℕ).prev (i + 1) = i :=
      CochainComplex.prev_nat_succ i
    have hnext : (ComplexShape.up ℕ).next (i + 1) = i + 2 := by
      rw [CochainComplex.next]
      omega
    letI : Module.Finite R S.homology :=
      Module.Finite.equiv
        (C.homologyIsoSc' i (i + 1) (i + 2)
          hprev hnext).toLinearEquiv
    let SA := ShortComplex.moduleCatMk
      (d i) (d (i + 1)) (hcomp i)
    letI : Module.Finite A SA.homology :=
      ModularCurves.ShortComplex.moduleFinite_baseChangeHomology_of_flat S A
    exact Module.Finite.quotient_range_moduleCatToCycles SA
  have hresidueLocal : ∀ i, i < N →
      Function.Exact
        ((d i).baseChange (IsLocalRing.ResidueField A))
        ((d (i + 1)).baseChange
          (IsLocalRing.ResidueField A)) := by
    intro i hi
    exact (LinearMap.baseChange_baseChange_exact_iff
      A (IsLocalRing.ResidueField A)
      (C.d i (i + 1)).hom
      (C.d (i + 1) (i + 2)).hom).mpr
        (hresidue i hi)
  exact
    LinearMap.exact_of_bounded_flat_residueField_baseChange_exact_of_finite_homology
      M d N hcomp hfinite hresidueLocal q hq

/-- Finite degree-zero homology of a cochain complex gives a finite kernel of its first
differential. -/
theorem HomologicalComplex.finite_kernel_zero_of_finite_homology
    (C : CochainComplex (ModuleCat.{v} R) ℕ)
    [Module.Finite R (C.homology 0)] :
    Module.Finite R (LinearMap.ker (C.d 0 1).hom) := by
  let S := C.sc' 0 0 1
  have hprev : (ComplexShape.up ℕ).prev 0 = 0 :=
    CochainComplex.prev_nat_zero
  have hnext : (ComplexShape.up ℕ).next 0 = 1 := by simp
  letI : Module.Finite R S.homology :=
    Module.Finite.equiv
      (C.homologyIsoSc' 0 0 1 hprev hnext).toLinearEquiv
  have hto : S.moduleCatToCycles = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (C.d 0 0).hom x = 0
    rw [C.shape 0 0 (by simp)]
    rfl
  have hrange : LinearMap.range S.moduleCatToCycles = ⊥ := by
    rw [hto, LinearMap.range_zero]
  let e : S.homology ≃ₗ[R] LinearMap.ker (C.d 0 1).hom :=
    S.moduleCatHomologyIso.toLinearEquiv.trans
      ((LinearMap.range S.moduleCatToCycles).quotEquivOfEqBot hrange)
  exact Module.Finite.equiv e

end ModularCurves
