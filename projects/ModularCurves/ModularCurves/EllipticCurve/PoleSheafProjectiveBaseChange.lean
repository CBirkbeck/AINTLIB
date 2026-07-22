/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafProjectiveCech
import ModularCurves.ForMathlib.SchemeModuleBaseSectionsBaseChange

/-!
# Base change for projectively presented pole-section modules

This file proves formation of global sections of `O(n[0])` commutes with every affine base
change for a projectively presented fibrewise elliptic family over a Noetherian ring.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open TensorProduct

universe u

namespace ModularCurves

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Global sections of `O(n[0])` on a projectively presented fibrewise elliptic family commute
with every affine base change. -/
noncomputable def
    FibrewiseElliptic.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (h : FibrewiseElliptic
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
    {n : ℕ} (hn : 1 ≤ n) {T : Scheme.{u}} [IsAffine T]
    (t : T ⟶ Spec (.of R)) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz n
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    let MT := sectionPoleSheafPower πT zT hzT n
    let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    A ⊗[B] Scheme.Modules.baseSections π M ≃ₗ[A]
      Scheme.Modules.baseSections πT MT := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  let MT := sectionPoleSheafPower πT zT hzT n
  let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  let A := Γ(T, (⊤ : T.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  letI : M.IsQuasicoherent := sectionPoleSheafPower_isQuasicoherent hsm z hz n
  let U := fun j => f ⁻¹ᵁ MvPolynomial.coordinateOpenCover
    (R := R) (σ := σ) j
  have hU : IsOpenCover U := by
    exact f.iSup_preimage_eq_top
      (MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
  have hUaff : ∀ j, IsAffineOpen (U j) := by
    intro j
    exact (MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) j).preimage f
  let hdata :=
    h.sectionPoleSheafPower_projectiveClosed_orderedBaseCech_kernel_data
      f hsm z hz hn
  let ePullback :=
    Scheme.Modules.baseSectionsBaseChangeLinearEquivOfOrderedCechKernelComparison
      π t M U hU hUaff (hdata.2.2.1 A)
  let ePole := (Scheme.Modules.baseSectionsMapIso πT
    (sectionPoleSheafPowerBaseChangeIso hsm z hz t n)).toLinearEquiv
  exact ePullback.trans ePole

/-- The projective pole-section base-change equivalence agrees on pure tensors
with the pullback unit followed by the canonical pole-sheaf pullback isomorphism. -/
theorem
    FibrewiseElliptic.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv_one_tmul
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (h : FibrewiseElliptic
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
    {n : ℕ} (hn : 1 ≤ n) {T : Scheme.{u}} [IsAffine T]
    (t : T ⟶ Spec (.of R))
    (s : Scheme.Modules.baseSections
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (sectionPoleSheafPower
        (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz n)) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz n
    let g := pullback.fst π t
    let πT := pullback.snd π t
    let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    h.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv
        f hsm z hz hn t ((1 : A) ⊗ₜ[B] s) =
      (Scheme.Modules.baseSectionsMapIso πT
        (sectionPoleSheafPowerBaseChangeIso hsm z hz t n)).hom
          (Scheme.Modules.affinePullbackUnitTop g M s) := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let g := pullback.fst π t
  let πT := pullback.snd π t
  let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  let A := Γ(T, (⊤ : T.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  letI : M.IsQuasicoherent := sectionPoleSheafPower_isQuasicoherent hsm z hz n
  let U := fun j => f ⁻¹ᵁ MvPolynomial.coordinateOpenCover
    (R := R) (σ := σ) j
  have hU : IsOpenCover U := by
    exact f.iSup_preimage_eq_top
      (MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
  have hUaff : ∀ j, IsAffineOpen (U j) := by
    intro j
    exact (MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) j).preimage f
  let hdata :=
    h.sectionPoleSheafPower_projectiveClosed_orderedBaseCech_kernel_data
      f hsm z hz hn
  let ePullback :=
    Scheme.Modules.baseSectionsBaseChangeLinearEquivOfOrderedCechKernelComparison
      π t M U hU hUaff (hdata.2.2.1 A)
  let ePole := (Scheme.Modules.baseSectionsMapIso πT
    (sectionPoleSheafPowerBaseChangeIso hsm z hz t n)).toLinearEquiv
  dsimp only [
    FibrewiseElliptic.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv]
  change ePole (ePullback ((1 : A) ⊗ₜ[B] s)) = _
  rw [Scheme.Modules.baseSectionsBaseChangeLinearEquivOfOrderedCechKernelComparison_one_tmul]
  rfl

end ModularCurves
