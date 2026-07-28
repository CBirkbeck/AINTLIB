/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpacePositiveTwistCoproductCech
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistShiftIso
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistTensorEquivalence

/-!
# Cech exactness after an additional positive projective twist

Positive coordinate twists add under tensor product. Consequently,
tensoring a finite coproduct of positive twists by another positive twist
preserves its positive-degree ordered-Cech exactness.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousIdeal
  MonoidalCategory Opposite TopologicalSpace

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance positiveTwistTensorMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- Reassociating two positive coordinate twists adds their degrees. -/
noncomputable def moduleTensorCoordinateHyperplanePoleSheafPowerAddIso
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j : σ) (m n : ℕ) :
    (M ⊗ coordinateHyperplanePoleSheafPower (R := R) j m) ⊗
        coordinateHyperplanePoleSheafPower (R := R) j n ≅
      M ⊗ coordinateHyperplanePoleSheafPower (R := R) j (m + n) :=
  α_ M
      (coordinateHyperplanePoleSheafPower (R := R) j m)
      (coordinateHyperplanePoleSheafPower (R := R) j n) ≪≫
    (Iso.refl M ⊗ᵢ
      (coordinateHyperplanePoleSheafPower_addIso
        (R := R) j m n).symm)

/-- Tensoring a finite coproduct of positive coordinate twists by another
positive twist adds its degree to every summand. -/
noncomputable def
    coordinateHyperplanePoleSheafPowerCoproductTensorIso
    {I : Type} [Finite I] (j : σ) (n : I → ℕ) (N : ℕ) :
    (∐ fun i : I ↦
        coordinateHyperplanePoleSheafPower (R := R) j (n i)) ⊗
        coordinateHyperplanePoleSheafPower (R := R) j N ≅
      ∐ fun i : I ↦
        coordinateHyperplanePoleSheafPower (R := R) j (n i + N) := by
  let E :=
    coordinateHyperplanePoleSheafPowerTensorEquivalence
      (R := R) j N
  let L : I → (Proj (homogeneousSubmodule σ R)).Modules := fun i ↦
    coordinateHyperplanePoleSheafPower (R := R) j (n i)
  let P : I → (Proj (homogeneousSubmodule σ R)).Modules := fun i ↦
    coordinateHyperplanePoleSheafPower (R := R) j (n i + N)
  let e₀ : E.functor.obj (∐ L) ≅ ∐ fun i ↦ E.functor.obj (L i) :=
    PreservesCoproduct.iso E.functor L
  let e₁ : (∐ fun i ↦ E.functor.obj (L i)) ≅ ∐ P :=
    Sigma.mapIso fun i =>
      (coordinateHyperplanePoleSheafPower_addIso
        (R := R) j (n i) N).symm
  exact e₀ ≪≫ e₁

/-- A finite coproduct of positive twists remains ordered-Cech acyclic in
positive degrees after tensoring by another positive twist. -/
theorem
    coordinateHyperplanePoleSheafPowerCoproductTensor_orderedBaseCechComplex_exactAt_succ
    [Fintype σ] [LinearOrder σ] {I : Type} [Finite I]
    (j : σ) (n : I → ℕ) (N q : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
      (homogeneousProjπ (R := R) (σ := σ))
      ((∐ fun i : I ↦
          coordinateHyperplanePoleSheafPower (R := R) j (n i)) ⊗
        coordinateHyperplanePoleSheafPower (R := R) j N)
      (coordinateOpenCover (R := R) (σ := σ))).ExactAt (q + 1) := by
  let F :=
    AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplexFunctor
      (homogeneousProjπ (R := R) (σ := σ))
      (coordinateOpenCover (R := R) (σ := σ))
  let e :=
    coordinateHyperplanePoleSheafPowerCoproductTensorIso
      (R := R) j n N
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply
    (HomologicalComplex.homologyMapIso
      (F.mapIso e) (q + 1)).isZero_iff.mpr
  apply HomologicalComplex.ExactAt.isZero_homology
  exact
    coordinateHyperplanePoleSheafPowerCoproduct_orderedBaseCechComplex_exactAt_succ
      (R := R) (fun _ : I ↦ j) (fun i ↦ n i + N) q

end

end MvPolynomial
