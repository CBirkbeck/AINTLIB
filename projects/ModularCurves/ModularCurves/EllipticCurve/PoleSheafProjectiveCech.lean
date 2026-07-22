/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafBaseCechHigher
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCechFinite

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

end ModularCurves
