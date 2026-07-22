/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafBaseCechHigher
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCechFinite
import ModularCurves.ForMathlib.CochainComplexBoundedFlat

/-!
# Projective Cech data for pole sheaves

Package flatness, finite homology, boundedness, field exactness, and the degree-zero field rank
on the same ordered coordinate-cover Cech complex of a pole sheaf on a projective family.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace ModularCurves

attribute [local instance] MvPolynomial.gradedAlgebra

/-- For a fibrewise elliptic family embedded as a closed subscheme of finite projective space,
the ordered coordinate-cover Cech complex of `O(n[0])` is a common model with flat terms, finite
homology, bounded support, field-fibre exactness, and an `n`-dimensional degree-zero kernel. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_projectiveClosed_orderedBaseCech_data
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
    {n : ℕ} (hn : 1 ≤ n) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz n
    let U := fun j => f ⁻¹ᵁ MvPolynomial.coordinateOpenCover
      (R := R) (σ := σ) j
    let C := Scheme.Modules.orderedBaseCechComplex π M U
    (∀ q, Module.Flat Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens)) (C.X q)) ∧
      (∀ q, Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
        (C.homology q)) ∧
      (∀ q, Fintype.card (ULift.{u} σ) ≤ q → Subsingleton (C.X q)) ∧
      (∀ (K : Type u) [Field K]
        [Algebra Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens)) K] (q : ℕ),
        Function.Exact
          ((C.d q (q + 1)).hom.baseChange K)
          ((C.d (q + 1) (q + 2)).hom.baseChange K)) ∧
      ∀ (K : Type u) [Field K]
        [Algebra Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens)) K],
        Module.finrank K (LinearMap.ker ((C.d 0 1).hom.baseChange K)) = n := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let U := fun j => f ⁻¹ᵁ MvPolynomial.coordinateOpenCover
    (R := R) (σ := σ) j
  letI : IsProper π := by
    letI : Algebra.FiniteType R (MvPolynomial σ R) := by
      infer_instance
    letI : IsScalarTower R
        (MvPolynomial.homogeneousSubmodule σ R 0) (MvPolynomial σ R) :=
      IsScalarTower.of_algebraMap_eq'
        (R := R) (S := MvPolynomial.homogeneousSubmodule σ R 0)
        (A := MvPolynomial σ R) (by ext r; rfl)
    letI : Algebra.FiniteType
        (MvPolynomial.homogeneousSubmodule σ R 0) (MvPolynomial σ R) :=
      Algebra.FiniteType.of_restrictScalars_finiteType R
        (MvPolynomial.homogeneousSubmodule σ R 0) (MvPolynomial σ R)
    letI : IsProper
        (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule σ R)) :=
      inferInstance
    letI : IsFinite
        (Spec.map (CommRingCat.ofHom
          (algebraMap R (MvPolynomial.homogeneousSubmodule σ R 0)))) :=
      (IsFinite.SpecMap_iff _).mpr
        (RingHom.finite_algebraMap.mpr (by infer_instance))
    dsimp only [π, MvPolynomial.homogeneousProjπ]
    infer_instance
  letI : SmoothOfRelativeDimension 1 π := hsm
  letI : Smooth π := SmoothOfRelativeDimension.smooth 1 π
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  letI : M.IsQuasicoherent :=
    sectionPoleSheafPower_isQuasicoherent hsm z hz n
  letI : M.IsFinitePresentation :=
    sectionPoleSheafPower_isFinitePresentation hsm z hz n
  letI : M.IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation M
  have hU : IsOpenCover U := by
    exact f.iSup_preimage_eq_top
      (MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
  have hUaff : ∀ j, IsAffineOpen (U j) := by
    intro j
    exact (MvPolynomial.coordinateOpenCover_isAffineOpen
      (R := R) j).preimage f
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q
    exact Scheme.Modules.orderedBaseCechObject_flat_of_isInvertible
      π M (sectionPoleSheafPower_isInvertible hsm z hz n) U hUaff q
  · intro q
    exact MvPolynomial.closedImmersion_finiteType_orderedBaseCechComplex_homology_module_finite
      f M q
  · intro q hq
    exact Scheme.Modules.orderedBaseCechObject_subsingleton_of_card_le
      π M U q hq
  · intro K _ _ q
    exact h.sectionPoleSheafPower_field_orderedBaseCech_differential_exact
      hsm z hz U hU hUaff K hn q
  · intro K _ _
    exact h.sectionPoleSheafPower_field_orderedBaseCech_kernel_finrank
      hsm z hz U hU hUaff K hn

/-- For a projectively presented fibrewise elliptic family over a Noetherian ring, the
degree-zero kernel in the common pole-sheaf Cech complex is finite projective, commutes with
arbitrary algebra base change, and has constant rank equal to the pole order. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_projectiveClosed_orderedBaseCech_kernel_data
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
    {n : ℕ} (hn : 1 ≤ n) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz n
    let U := fun j => f ⁻¹ᵁ MvPolynomial.coordinateOpenCover
      (R := R) (σ := σ) j
    let C := Scheme.Modules.orderedBaseCechComplex π M U
    let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    Module.Finite B (LinearMap.ker (C.d 0 1).hom) ∧
      Module.Projective B (LinearMap.ker (C.d 0 1).hom) ∧
      (∀ (A : Type u) [CommRing A] [Algebra B A],
        Function.Bijective (kerBaseChangeComparison A (C.d 0 1).hom)) ∧
      Module.rankAtStalk (R := B) (LinearMap.ker (C.d 0 1).hom) = fun _ ↦ n := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let U := fun j => f ⁻¹ᵁ MvPolynomial.coordinateOpenCover
    (R := R) (σ := σ) j
  let C := Scheme.Modules.orderedBaseCechComplex π M U
  let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  obtain ⟨hflat, hfinite, hbounded, hfield, hrank⟩ :=
    h.sectionPoleSheafPower_projectiveClosed_orderedBaseCech_data
      f hsm z hz hn
  letI (q : ℕ) : Module.Flat B (C.X q) := hflat q
  letI (q : ℕ) : Module.Finite B (C.homology q) := hfinite q
  let N := Fintype.card (ULift.{u} σ)
  letI : Subsingleton (C.X (N + 1)) := hbounded (N + 1) (Nat.le_succ N)
  have hexact : ∀ q, q < N →
      Function.Exact (C.d q (q + 1)).hom (C.d (q + 1) (q + 2)).hom := by
    intro q hq
    exact
      HomologicalComplex.functionExact_of_bounded_flat_forall_field_baseChange_exact_of_finite_homology
        C N (fun i _ K _ _ ↦ hfield K i) q hq
  have hkerFinite : Module.Finite B (LinearMap.ker (C.d 0 1).hom) :=
    HomologicalComplex.finite_kernel_zero_of_finite_homology C
  letI : Module.Finite B (LinearMap.ker (C.d 0 1).hom) := hkerFinite
  letI : IsNoetherianRing B := by
    exact isNoetherianRing_of_ringEquiv R
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  have hkerProjective : Module.Projective B (LinearMap.ker (C.d 0 1).hom) :=
    Module.Projective.ker_of_bounded_exact_of_finite
      (fun q ↦ C.X q) (fun q ↦ (C.d q (q + 1)).hom) N hexact
  letI : Module.Projective B (LinearMap.ker (C.d 0 1).hom) := hkerProjective
  have hbase : ∀ (A : Type u) [CommRing A] [Algebra B A],
      Function.Bijective (kerBaseChangeComparison A (C.d 0 1).hom) := by
    intro A _ _
    exact kerBaseChangeComparison_bijective_of_bounded_exact
      A (fun q ↦ C.X q) (fun q ↦ (C.d q (q + 1)).hom) N hexact
  have hrankAt :
      Module.rankAtStalk (R := B) (LinearMap.ker (C.d 0 1).hom) = fun _ ↦ n := by
    letI : Module.Flat B (LinearMap.ker (C.d 0 1).hom) := inferInstance
    funext p
    rw [Module.rankAtStalk_eq]
    let e : p.asIdeal.Fiber (LinearMap.ker (C.d 0 1).hom) ≃ₗ[p.asIdeal.ResidueField]
        LinearMap.ker ((C.d 0 1).hom.baseChange p.asIdeal.ResidueField) :=
      LinearEquiv.ofBijective
        (kerBaseChangeComparison p.asIdeal.ResidueField (C.d 0 1).hom)
        (hbase p.asIdeal.ResidueField)
    exact e.finrank_eq.trans (hrank p.asIdeal.ResidueField)
  exact ⟨hkerFinite, hkerProjective, hbase, hrankAt⟩

/-- On a projectively presented fibrewise elliptic family over a Noetherian ring, global
sections of `O(n[0])` form a finite projective module of constant rank `n`. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_projectiveClosed_baseSections_data
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
    {n : ℕ} (hn : 1 ≤ n) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz n
    let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    Module.Finite B (Scheme.Modules.baseSections π M) ∧
      Module.Projective B (Scheme.Modules.baseSections π M) ∧
      Module.rankAtStalk (R := B) (Scheme.Modules.baseSections π M) = fun _ ↦ n := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let U := fun j => f ⁻¹ᵁ MvPolynomial.coordinateOpenCover
    (R := R) (σ := σ) j
  let C := Scheme.Modules.orderedBaseCechComplex π M U
  let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  obtain ⟨hfinite, hprojective, _, hrank⟩ :=
    h.sectionPoleSheafPower_projectiveClosed_orderedBaseCech_kernel_data
      f hsm z hz hn
  letI : Module.Finite B (LinearMap.ker (C.d 0 1).hom) := hfinite
  letI : Module.Projective B (LinearMap.ker (C.d 0 1).hom) := hprojective
  have hU : IsOpenCover U := by
    exact f.iSup_preimage_eq_top
      (MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
  let e := (sectionPoleSheafPower_baseSectionsIsoKernelOrderedBaseCechDifferential
    z hz n U hU).toLinearEquiv
  have hsectionsFinite : Module.Finite B (Scheme.Modules.baseSections π M) :=
    Module.Finite.equiv e.symm
  have hsectionsProjective : Module.Projective B (Scheme.Modules.baseSections π M) :=
    Module.Projective.of_equiv' e.symm
  have hsectionsRank :
      Module.rankAtStalk (R := B) (Scheme.Modules.baseSections π M) = fun _ ↦ n :=
    (Module.rankAtStalk_eq_of_equiv e).trans hrank
  exact ⟨hsectionsFinite, hsectionsProjective, hsectionsRank⟩

end ModularCurves
