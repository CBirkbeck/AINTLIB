/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's
`CoherentCohomologyFinite.SegreStandardChartEquivalence`.
-/
import ModularCurves.ForMathlib.SegreImageChartGeneration

/-!
# The standard Segre chart equivalence

The forward dehomogenization map and the anchor-insertion map are inverse
on every standard affine chart.
-/

open HomogeneousLocalization
open scoped TensorProduct

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

lemma segreChartForwardAlgHom_left_ratio
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (a : Fin (m + 1)) :
    segreChartForwardAlgHom R m n i j
        (segreLeftChartToImageAlgHom R m n i j
          (projectiveCoordinateRatio R i a)) =
      (Algebra.TensorProduct.includeLeft :
        ProjectiveCoordinateAway R i →ₐ[R]
          SegreProductChartRing R m n i j)
        (projectiveCoordinateRatio R i a) := by
  rw [segreLeftChartToImageAlgHom_ratio,
    segreChartForwardAlgHom_ratio]
  simp

lemma segreChartForwardAlgHom_comp_left
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreChartForwardAlgHom R m n i j).comp
        (segreLeftChartToImageAlgHom R m n i j) =
      (Algebra.TensorProduct.includeLeft :
        ProjectiveCoordinateAway R i →ₐ[R]
          SegreProductChartRing R m n i j) := by
  apply
    (AlgHom.cancel_right
      (projectiveCoordinateDehomogenization_surjective R i)).mp
  ext a
  simp

lemma segreChartForwardAlgHom_right_ratio
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (b : Fin (n + 1)) :
    segreChartForwardAlgHom R m n i j
        (segreRightChartToImageAlgHom R m n i j
          (projectiveCoordinateRatio R j b)) =
      (Algebra.TensorProduct.includeRight :
        ProjectiveCoordinateAway R j →ₐ[R]
          SegreProductChartRing R m n i j)
        (projectiveCoordinateRatio R j b) := by
  rw [segreRightChartToImageAlgHom_ratio,
    segreChartForwardAlgHom_ratio]
  simp

lemma segreChartForwardAlgHom_comp_right
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreChartForwardAlgHom R m n i j).comp
        (segreRightChartToImageAlgHom R m n i j) =
      (Algebra.TensorProduct.includeRight :
        ProjectiveCoordinateAway R j →ₐ[R]
          SegreProductChartRing R m n i j) := by
  apply
    (AlgHom.cancel_right
      (projectiveCoordinateDehomogenization_surjective R j)).mp
  ext b
  simp

/-- Dehomogenization after anchor insertion is the identity on the product chart. -/
lemma segreChartForwardAlgHom_comp_inverse
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreChartForwardAlgHom R m n i j).comp
        (segreChartInverseAlgHom R m n i j) =
      AlgHom.id R (SegreProductChartRing R m n i j) := by
  apply Algebra.TensorProduct.ext
  · ext x
    change
      segreChartForwardAlgHom R m n i j
          (segreChartInverseAlgHom R m n i j
            ((Algebra.TensorProduct.includeLeft :
              ProjectiveCoordinateAway R i →ₐ[R]
                SegreProductChartRing R m n i j) x)) =
        (Algebra.TensorProduct.includeLeft :
          ProjectiveCoordinateAway R i →ₐ[R]
            SegreProductChartRing R m n i j) x
    rw [show
      segreChartInverseAlgHom R m n i j
          ((Algebra.TensorProduct.includeLeft :
            ProjectiveCoordinateAway R i →ₐ[R]
              SegreProductChartRing R m n i j) x) =
        segreLeftChartToImageAlgHom R m n i j x by
      simp [segreChartInverseAlgHom]]
    exact
      AlgHom.congr_fun
        (segreChartForwardAlgHom_comp_left R m n i j) x
  · ext y
    change
      segreChartForwardAlgHom R m n i j
          (segreChartInverseAlgHom R m n i j
            ((Algebra.TensorProduct.includeRight :
              ProjectiveCoordinateAway R j →ₐ[R]
                SegreProductChartRing R m n i j) y)) =
        (Algebra.TensorProduct.includeRight :
          ProjectiveCoordinateAway R j →ₐ[R]
            SegreProductChartRing R m n i j) y
    rw [show
      segreChartInverseAlgHom R m n i j
          ((Algebra.TensorProduct.includeRight :
            ProjectiveCoordinateAway R j →ₐ[R]
              SegreProductChartRing R m n i j) y) =
        segreRightChartToImageAlgHom R m n i j y by
      simp [segreChartInverseAlgHom]]
    exact
      AlgHom.congr_fun
        (segreChartForwardAlgHom_comp_right R m n i j) y

/-- Anchor insertion after dehomogenization fixes each standard Segre ratio. -/
lemma segreChartInverseAlgHom_forward_ratio
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreChartInverseAlgHom R m n i j
        (segreChartForwardAlgHom R m n i j
          (segreImageChartRatio R m n i a j b)) =
      segreImageChartRatio R m n i a j b := by
  rw [segreChartForwardAlgHom_ratio]
  change
    Algebra.TensorProduct.lift
        (segreLeftChartToImageAlgHom R m n i j)
        (segreRightChartToImageAlgHom R m n i j)
        (segreChartAnchorMaps_commute R m n i j)
        (projectiveCoordinateRatio R i a ⊗ₜ[R]
          projectiveCoordinateRatio R j b) =
      _
  rw [Algebra.TensorProduct.lift_tmul,
    segreLeftChartToImageAlgHom_ratio,
    segreRightChartToImageAlgHom_ratio,
    segreImageChartRatio_mul_anchorRatios]

/-- The two explicit chart maps are inverse in the other order. -/
lemma segreChartInverseAlgHom_comp_forward
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreChartInverseAlgHom R m n i j).comp
        (segreChartForwardAlgHom R m n i j) =
      AlgHom.id R (SegreImageChartRing R m n i j) := by
  apply AlgHom.ext_of_adjoin_eq_top
    (segreImageCoordinateRatio_adjoin_eq_top
      R m n (segrePairIndex m n i j))
  intro x hx
  obtain ⟨s, rfl⟩ := hx
  let a := (segreIndexEquiv m n s).1
  let b := (segreIndexEquiv m n s).2
  have hs : segrePairIndex m n a b = s := by
    exact (segreIndexEquiv m n).symm_apply_apply s
  rw [← hs, segreImageCoordinateRatio_segrePairIndex]
  exact segreChartInverseAlgHom_forward_ratio R m n i a j b

/-- The coordinate-ring equivalence on a standard Segre chart. -/
def segreStandardChartAlgEquiv
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    SegreImageChartRing R m n i j ≃ₐ[R]
      SegreProductChartRing R m n i j :=
  { segreChartForwardAlgHom R m n i j with
    invFun := segreChartInverseAlgHom R m n i j
    left_inv := fun x =>
      AlgHom.congr_fun
        (segreChartInverseAlgHom_comp_forward R m n i j) x
    right_inv := fun x =>
      AlgHom.congr_fun
        (segreChartForwardAlgHom_comp_inverse R m n i j) x }

end MvPolynomial
