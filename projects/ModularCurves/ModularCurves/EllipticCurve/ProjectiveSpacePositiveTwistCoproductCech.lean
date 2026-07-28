/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCechHigher
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechFunctor

/-!
# Cech exactness for finite coproducts of positive projective twists

The ordered standard-cover Cech complex of a finite coproduct of
nonnegative coordinate twists is exact in every positive degree.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Finite coproducts of nonnegative coordinate twists are ordered-Cech
acyclic in every positive degree. -/
theorem coordinateHyperplanePoleSheafPowerCoproduct_orderedBaseCechComplex_exactAt_succ
    [Fintype σ] [LinearOrder σ] {I : Type} [Finite I]
    (j : I → σ) (n : I → ℕ) (q : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
      (homogeneousProjπ (R := R) (σ := σ))
      (∐ fun i : I ↦ coordinateHyperplanePoleSheafPower (R := R) (j i) (n i))
      (coordinateOpenCover (R := R) (σ := σ))).ExactAt (q + 1) := by
  classical
  letI := Fintype.ofFinite I
  letI : HasFiniteBiproducts (Proj (homogeneousSubmodule σ R)).Modules :=
    HasFiniteBiproducts.of_hasFiniteProducts
  letI : HasFiniteBiproducts
      (ModuleCat.{u}
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let M : I → (Proj (homogeneousSubmodule σ R)).Modules := fun i ↦
    coordinateHyperplanePoleSheafPower (R := R) (j i) (n i)
  let F := AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplexFunctor
      (homogeneousProjπ (R := R) (σ := σ))
      (coordinateOpenCover (R := R) (σ := σ)) ⋙
    HomologicalComplex.homologyFunctor
      (ModuleCat.{u}
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)))
      (ComplexShape.up ℕ) (q + 1)
  letI : F.Additive := by
    dsimp only [F]
    infer_instance
  letI : PreservesFiniteBiproducts F :=
    Functor.preservesFiniteBiproductsOfAdditive F
  have hcomponent (i : I) : IsZero (F.obj (M i)) := by
    change IsZero
      ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplanePoleSheafPower (R := R) (j i) (n i))
        (coordinateOpenCover (R := R) (σ := σ))).homology (q + 1))
    apply HomologicalComplex.ExactAt.isZero_homology
      (coordinateHyperplaneTwist_orderedBaseCechComplex_exactAt_succ
        (R := R) (j i) (n i : ℤ) (Int.natCast_nonneg (n i)) q)
  letI (i : I) : Subsingleton (F.obj (M i)) :=
    ModuleCat.subsingleton_of_isZero (hcomponent i)
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  change IsZero (F.obj (∐ M))
  let e₀ : F.obj (∐ M) ≅ F.obj (⨁ M) :=
    F.mapIso (biproduct.isoCoproduct M).symm
  let e₁ : F.obj (⨁ M) ≅ ⨁ (F.obj ∘ M) := F.mapBiproduct M
  let e₂ : (⨁ (F.obj ∘ M)) ≅ ∏ᶜ (F.obj ∘ M) :=
    biproduct.isoProduct (F.obj ∘ M)
  let e₃ : (∏ᶜ (F.obj ∘ M)) ≅
      ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (∀ i : I, F.obj (M i)) :=
    ModuleCat.piIsoPi (F.obj ∘ M)
  apply (e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃).isZero_iff.mpr
  exact ModuleCat.isZero_of_subsingleton _

end

end MvPolynomial
