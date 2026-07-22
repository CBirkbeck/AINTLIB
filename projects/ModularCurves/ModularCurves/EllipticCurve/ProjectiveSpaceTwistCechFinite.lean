/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCechHigher
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistFinitePresentation
import ModularCurves.ForMathlib.FiniteHomologySequence
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechExact
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechFunctor
import ModularCurves.Picard.InvertibleSheafLocallyFree

/-!
# Finite homology for finite families of projective twists

This file combines the degree-zero and positive-degree finiteness theorems for a projective twist,
then transfers the result to finite coproducts using additivity of ordered Cech homology.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Ordered base-Cech homology of an integer coordinate-hyperplane twist is finite in every
degree over a Noetherian coefficient ring. -/
theorem coordinateHyperplaneTwist_orderedBaseCechComplex_homology_module_finite_all
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    (j : σ) (d : ℤ) (q : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (σ := σ))).homology q) := by
  cases q with
  | zero =>
      exact coordinateHyperplaneTwist_orderedBaseCechComplex_homology_zero_module_finite j d
  | succ n =>
      exact coordinateHyperplaneTwist_orderedBaseCechComplex_homology_module_finite j d n

/-- Ordered base-Cech homology of a finite coproduct of integer coordinate-hyperplane twists is
finite in every degree over a Noetherian coefficient ring. -/
theorem coordinateHyperplaneTwistCoproduct_orderedBaseCechComplex_homology_module_finite
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {I : Type} [Finite I] (j : I → σ) (d : I → ℤ) (q : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
        (homogeneousProjπ (R := R) (σ := σ))
        (∐ fun i : I ↦ coordinateHyperplaneTwist (R := R) (j i) (d i))
        (coordinateOpenCover (R := R) (σ := σ))).homology q) := by
  classical
  letI := Fintype.ofFinite I
  letI : HasFiniteBiproducts (Proj (homogeneousSubmodule σ R)).Modules :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let A := Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
  letI : HasFiniteBiproducts (ModuleCat.{u} A) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let M : I → (Proj (homogeneousSubmodule σ R)).Modules :=
    fun i ↦ coordinateHyperplaneTwist (R := R) (j i) (d i)
  let F := AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplexFunctor
      (homogeneousProjπ (R := R) (σ := σ))
      (coordinateOpenCover (R := R) (σ := σ)) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℕ) q
  letI : F.Additive := by
    dsimp only [F]
    infer_instance
  letI : PreservesFiniteBiproducts F :=
    Functor.preservesFiniteBiproductsOfAdditive F
  letI (i : I) : Module.Finite A (F.obj (M i)) :=
    coordinateHyperplaneTwist_orderedBaseCechComplex_homology_module_finite_all
      (R := R) (j i) (d i) q
  letI : Module.Finite A (∀ i : I, F.obj (M i)) := Module.Finite.pi
  change Module.Finite A (F.obj (∐ M))
  let e₀ : F.obj (∐ M) ≅ F.obj (⨁ M) :=
    F.mapIso (biproduct.isoCoproduct M).symm
  let e₁ : F.obj (⨁ M) ≅ ⨁ (F.obj ∘ M) := F.mapBiproduct M
  let e₂ : (⨁ (F.obj ∘ M)) ≅ ∏ᶜ (F.obj ∘ M) :=
    biproduct.isoProduct (F.obj ∘ M)
  let e₃ : (∏ᶜ (F.obj ∘ M)) ≅ ModuleCat.of A (∀ i : I, F.obj (M i)) :=
    ModuleCat.piIsoPi (F.obj ∘ M)
  exact Module.Finite.equiv
    ((e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃).symm.toLinearEquiv)

/-- Ordered base-Cech homology of a finite coproduct of nonnegative powers of coordinate
hyperplane ideal modules is finite in every degree over a Noetherian coefficient ring. -/
theorem coordinateHyperplaneIdealModulePowerCoproduct_orderedBaseCechComplex_homology_module_finite
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {I : Type} [Finite I] (j : I → σ) (n : I → ℕ) (q : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
        (homogeneousProjπ (R := R) (σ := σ))
        (∐ fun i : I ↦ coordinateHyperplaneIdealModulePower (R := R) (j i) (n i))
        (coordinateOpenCover (R := R) (σ := σ))).homology q) := by
  let d : I → ℤ := fun i ↦
    match n i with
    | 0 => 0
    | k + 1 => .negSucc k
  have hd (i : I) :
      coordinateHyperplaneTwist (R := R) (j i) (d i) =
        coordinateHyperplaneIdealModulePower (R := R) (j i) (n i) := by
    rcases hn : n i with _ | k
    · simp [d, hn, coordinateHyperplaneTwist]
    · simp [d, hn, coordinateHyperplaneTwist]
  have hfamily :
      (fun i : I ↦ coordinateHyperplaneTwist (R := R) (j i) (d i)) =
        fun i : I ↦ coordinateHyperplaneIdealModulePower (R := R) (j i) (n i) :=
    funext hd
  rw [← hfamily]
  exact coordinateHyperplaneTwistCoproduct_orderedBaseCechComplex_homology_module_finite
    (R := R) j d q

private theorem orderedBaseCechComplex_homology_module_finite_of_card_le
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (q : ℕ)
    (hq : Fintype.card (ULift.{u} σ) ≤ q) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
        (homogeneousProjπ (R := R) (σ := σ)) M
        (coordinateOpenCover (R := R) (σ := σ))).homology q) := by
  let C := AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
    (homogeneousProjπ (R := R) (σ := σ)) M
    (coordinateOpenCover (R := R) (σ := σ))
  have hX : IsZero (C.X q) := by
    dsimp only [C, AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex]
    exact AlgebraicGeometry.Scheme.Modules.orderedBaseCechObject_isZero_of_card_le
      (homogeneousProjπ (R := R) (σ := σ)) M
      (coordinateOpenCover (R := R) (σ := σ)) q hq
  have hH : IsZero (C.homology q) :=
    ShortComplex.isZero_homology_of_isZero_X₂ (C.sc q) hX
  letI : Subsingleton (C.homology q) := ModuleCat.subsingleton_of_isZero hH
  change Module.Finite
    Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
    (C.homology q)
  infer_instance

private theorem finiteType_orderedBaseCechComplex_homology_module_finite_of_card_le_add
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (q n : ℕ)
    (hcard : Fintype.card (ULift.{u} σ) ≤ q + n) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
        (homogeneousProjπ (R := R) (σ := σ)) M
        (coordinateOpenCover (R := R) (σ := σ))).homology q) := by
  letI : IsNoetherianRing
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
    isNoetherianRing_of_ringEquiv R
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  induction n generalizing M q with
  | zero =>
      exact orderedBaseCechComplex_homology_module_finite_of_card_le M q (by
        simpa using hcard)
  | succ n ih =>
      by_cases hq : Fintype.card (ULift.{u} σ) ≤ q
      · exact orderedBaseCechComplex_homology_module_finite_of_card_le M q hq
      · obtain ⟨r, j, d, f, hf⟩ := exists_fin_coordinateNegativeTwist_quotient M
        let L : Fin r → (Proj (homogeneousSubmodule σ R)).Modules := fun i ↦
          coordinateHyperplaneIdealModulePower (R := R) (j i) (d i)
        let Q : (Proj (homogeneousSubmodule σ R)).Modules := ∐ L
        letI : Epi f := hf
        letI : Q.IsQuasicoherent := by
          dsimp only [Q]
          apply AlgebraicGeometry.Scheme.Modules.isQuasicoherent_coproduct
          intro i
          exact AlgebraicGeometry.Scheme.Modules.IsInvertible.isQuasicoherent
            (coordinateHyperplaneIdealModulePower_isInvertible
              (R := R) (j i) (d i))
        letI : Q.IsFiniteType := by
          dsimp only [Q]
          apply AlgebraicGeometry.Scheme.Modules.isFiniteType_fin_coproduct L
          · intro i
            exact AlgebraicGeometry.Scheme.Modules.IsInvertible.isQuasicoherent
              (coordinateHyperplaneIdealModulePower_isInvertible
                (R := R) (j i) (d i))
          · intro i
            letI : (L i).IsFinitePresentation :=
              AlgebraicGeometry.Scheme.Modules.IsInvertible.isFinitePresentation
                (coordinateHyperplaneIdealModulePower_isInvertible
                  (R := R) (j i) (d i))
            refine { exists_localGeneratorsData := ?_ }
            obtain ⟨p, hp⟩ :=
              SheafOfModules.IsFinitePresentation.exists_quasicoherentData (L i)
            refine ⟨p.localGeneratorsData, ?_⟩
            constructor
            intro k
            exact (hp.isFinite_presentation k).isFiniteType_generators
        letI : LocallyOfFiniteType
            (homogeneousProjπ (R := R) (σ := σ)) :=
          homogeneousProjπ_locallyOfFiniteType (R := R) (σ := σ)
        letI : IsLocallyNoetherian (Proj (homogeneousSubmodule σ R)) :=
          LocallyOfFiniteType.isLocallyNoetherian
            (homogeneousProjπ (R := R) (σ := σ))
        letI : (kernel f).IsQuasicoherent :=
          AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel f
        letI : (kernel f).IsFiniteType :=
          AlgebraicGeometry.Scheme.Modules.isFiniteType_kernel f
        have hcard' : Fintype.card (ULift.{u} σ) ≤ (q + 1) + n := by
          omega
        letI : Module.Finite
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
              (homogeneousProjπ (R := R) (σ := σ)) (kernel f)
              (coordinateOpenCover (R := R) (σ := σ))).homology (q + 1)) :=
          ih (kernel f) (q + 1) hcard'
        letI : Module.Finite
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
              (homogeneousProjπ (R := R) (σ := σ)) Q
              (coordinateOpenCover (R := R) (σ := σ))).homology q) := by
          dsimp only [Q, L]
          exact
            coordinateHyperplaneIdealModulePowerCoproduct_orderedBaseCechComplex_homology_module_finite
              (R := R) j d q
        let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
        have hT : T.ShortExact := { exact := ShortComplex.exact_kernel f }
        have hTC := hT.map_orderedBaseCechComplexFunctor_of_affine_openCover
          (homogeneousProjπ (R := R) (σ := σ))
          (coordinateOpenCover (R := R) (σ := σ))
          (coordinateOpenCover_isAffineOpen (R := R))
        let F := AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplexFunctor
          (homogeneousProjπ (R := R) (σ := σ))
          (coordinateOpenCover (R := R) (σ := σ))
        letI : Module.Finite
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            ((T.map F).X₂.homology q) := by
          change Module.Finite
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
              (homogeneousProjπ (R := R) (σ := σ)) Q
              (coordinateOpenCover (R := R) (σ := σ))).homology q)
          infer_instance
        letI : Module.Finite
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            ((T.map F).X₁.homology (q + 1)) := by
          change Module.Finite
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
              (homogeneousProjπ (R := R) (σ := σ)) (kernel f)
              (coordinateOpenCover (R := R) (σ := σ))).homology (q + 1))
          infer_instance
        change Module.Finite
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          ((T.map F).X₃.homology q)
        exact ModularCurves.CategoryTheory.ShortComplex.ShortExact.finite_homology_X3
          hTC q (q + 1) (by simp [ComplexShape.up_Rel])

/-- Ordered base-Cech homology of a finite-type quasicoherent module on polynomial projective
space is finite in every degree over a Noetherian coefficient ring. -/
theorem finiteType_orderedBaseCechComplex_homology_module_finite
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
        (homogeneousProjπ (R := R) (σ := σ)) M
        (coordinateOpenCover (R := R) (σ := σ))).homology q) := by
  exact finiteType_orderedBaseCechComplex_homology_module_finite_of_card_le_add
    M q (Fintype.card (ULift.{u} σ)) (by omega)

end

end MvPolynomial
