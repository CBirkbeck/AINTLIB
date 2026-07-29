/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.LowDegreeFiniteProjectiveReplacement

/-!
# Bounded flat cochain complexes

This file translates between categorical homology of cochain complexes of modules and the
explicit kernels and quotients used by the algebraic base-change API.
-/

open CategoryTheory
open TensorProduct

universe u v w

namespace ModularCurves

variable {R : Type u} [CommRing R]

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
  let p := LinearMap.range S.moduleCatToCycles
  letI : Module.Finite R
      (LinearMap.ker S.g.hom ⧸ p) :=
    Module.Finite.quotient_range_moduleCatToCycles S
  letI : Module.Finite A
      (A ⊗[R] (LinearMap.ker S.g.hom ⧸ p)) :=
    Module.Finite.base_change R A _
  let eTensor :=
    TensorProduct.AlgebraTensorModule.tensorQuotientEquiv
      (R := R) A R A p
  have hrange :
      LinearMap.range (S.moduleCatToCycles.baseChange A) =
        LinearMap.range
          (TensorProduct.AlgebraTensorModule.lTensor A A p.subtype) := by
    change LinearMap.range
        (TensorProduct.AlgebraTensorModule.lTensor A A
          S.moduleCatToCycles) =
      LinearMap.range
        (TensorProduct.AlgebraTensorModule.lTensor A A p.subtype)
    apply SetLike.ext
    intro x
    change x ∈ LinearMap.range
        (LinearMap.lTensor A S.moduleCatToCycles) ↔
      x ∈ LinearMap.range (LinearMap.lTensor A p.subtype)
    rw [LinearMap.lTensor_range A]
  let eRange := Submodule.quotEquivOfEq
    (LinearMap.range
      (TensorProduct.AlgebraTensorModule.lTensor A A p.subtype))
    (LinearMap.range (S.moduleCatToCycles.baseChange A))
    hrange.symm
  let eHomology := LinearMap.baseChangeHomologyOneEquiv
    S.f.hom S.g.hom (shortComplexModuleCatCompEqZero S) A
    (kerBaseChangeComparison_bijective_of_flat A S.g.hom)
  exact Module.Finite.equiv (eTensor.trans eRange |>.trans eHomology)

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
