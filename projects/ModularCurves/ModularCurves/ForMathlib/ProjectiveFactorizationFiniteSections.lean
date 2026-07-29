/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.ProjectiveFactorizationCechFinite
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechZero

/-!
# Finite sections for projective factorizations

Degree-zero ordered Cech homology on a projective coordinate cover controls
global sections. The dimension-bumped projective factorization theorem therefore
gives finite base-linear global sections without a nontrivial-coordinate
hypothesis.
-/

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.IsProjectiveFactorization

variable {X : Scheme.{u}} {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {f : X ⟶ Spec (.of R)}

private theorem finite_kernel_zero_of_finite_homology
    {A : Type u} [CommRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℕ)
    [Module.Finite A (C.homology 0)] :
    Module.Finite A (LinearMap.ker (C.d 0 1).hom) := by
  let S := C.sc' 0 0 1
  have hprev : (ComplexShape.up ℕ).prev 0 = 0 :=
    CochainComplex.prev_nat_zero
  have hnext : (ComplexShape.up ℕ).next 0 = 1 := by simp
  letI : Module.Finite A S.homology :=
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
  let e : S.homology ≃ₗ[A] LinearMap.ker (C.d 0 1).hom :=
    S.moduleCatHomologyIso.toLinearEquiv.trans
      ((LinearMap.range S.moduleCatToCycles).quotEquivOfEqBot hrange)
  exact Module.Finite.equiv e

/-- A finite-type quasicoherent module on a projective scheme has finite
base-linear global sections. -/
theorem baseSections_module_finite
    (hf : AlgebraicGeometry.IsProjectiveFactorization f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      (Scheme.Modules.baseSections f M) := by
  obtain ⟨d, i, _, hi, hfinite⟩ :=
    hf.exists_orderedBaseCechHomologyFinite M
  let U := fun j ↦
    i ⁻¹ᵁ MvPolynomial.coordinateOpenCover
      (R := R) (σ := Fin (d + 1)) j
  let C := Scheme.Modules.orderedBaseCechComplex f M U
  letI : Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      (C.homology 0) := hfinite 0
  have hker : Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      (LinearMap.ker (C.d 0 1).hom) :=
    finite_kernel_zero_of_finite_homology C
  letI : Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      (LinearMap.ker (C.d 0 1).hom) := hker
  have hU : IsOpenCover U := by
    exact i.iSup_preimage_eq_top
      (MvPolynomial.iSup_coordinateOpenCover_eq_top
        (R := R) (σ := Fin (d + 1)))
  let e :=
    Scheme.Modules.baseSectionsIsoKernelOrderedBaseCechDifferential
      f M U hU
  exact Module.Finite.equiv e.symm.toLinearEquiv

private theorem finite_cycles_zero_of_finite_kernel
    {A : Type u} [CommRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℕ)
    [Module.Finite A (LinearMap.ker (C.d 0 1).hom)] :
    Module.Finite A (C.cycles 0) := by
  let S := C.sc' 0 0 1
  have hprev : (ComplexShape.up ℕ).prev 0 = 0 :=
    CochainComplex.prev_nat_zero
  have hnext : (ComplexShape.up ℕ).next 0 = 1 := by simp
  let e :
      C.cycles 0 ≃ₗ[A] LinearMap.ker (C.d 0 1).hom :=
    (C.cyclesIsoSc' 0 0 1 hprev hnext).toLinearEquiv.trans
      S.moduleCatCyclesIso.toLinearEquiv
  exact Module.Finite.equiv e.symm

/-- Degree-zero ordered base-Cech homology of a finite-type
quasicoherent module on a projective scheme is finite for every
ordered open cover. -/
theorem orderedBaseCechComplex_homology_zero_module_finite
    (hf : AlgebraicGeometry.IsProjectiveFactorization f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) :
    Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      ((Scheme.Modules.orderedBaseCechComplex f M U).homology 0) := by
  let C := Scheme.Modules.orderedBaseCechComplex f M U
  letI : Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      (Scheme.Modules.baseSections f M) :=
    hf.baseSections_module_finite M
  let e :=
    Scheme.Modules.baseSectionsIsoKernelOrderedBaseCechDifferential
      f M U hU
  letI : Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      (LinearMap.ker (C.d 0 1).hom) :=
    Module.Finite.equiv e.toLinearEquiv
  letI : Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      (C.cycles 0) :=
    finite_cycles_zero_of_finite_kernel C
  exact Module.Finite.of_surjective (C.homologyπ 0).hom
    ((ModuleCat.epi_iff_surjective (C.homologyπ 0)).mp inferInstance)

end AlgebraicGeometry.IsProjectiveFactorization
