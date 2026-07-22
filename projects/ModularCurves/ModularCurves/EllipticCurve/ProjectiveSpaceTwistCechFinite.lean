/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCechHigher
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechFunctor

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

end

end MvPolynomial
