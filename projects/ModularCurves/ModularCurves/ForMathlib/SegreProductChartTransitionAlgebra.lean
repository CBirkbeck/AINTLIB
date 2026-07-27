/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's
`CoherentCohomologyFinite.SegreProductChartTransitionAlgebra`.
-/
import ModularCurves.ForMathlib.SegreProductOverlapLocalization

/-!
# Transition algebra between product charts

On the overlap of two product charts, each projective transition ratio becomes a unit because
their tensor product is the element inverted in the overlap ring.
-/

open HomogeneousLocalization
open scoped TensorProduct

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The first factor of a product chart, mapped to the localized overlap ring. -/
def segreProductOverlapLeftRingHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateAway R i →+*
      SegreProductChartOverlapRing R m n i a j b :=
  (algebraMap
      (SegreProductChartRing R m n i j)
      (SegreProductChartOverlapRing R m n i a j b)).comp
    (Algebra.TensorProduct.includeLeftRingHom :
      ProjectiveCoordinateAway R i →+*
        SegreProductChartRing R m n i j)

/-- The second factor of a product chart, mapped to the localized overlap ring. -/
def segreProductOverlapRightRingHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateAway R j →+*
      SegreProductChartOverlapRing R m n i a j b :=
  (algebraMap
      (SegreProductChartRing R m n i j)
      (SegreProductChartOverlapRing R m n i a j b)).comp
    ((Algebra.TensorProduct.includeRight :
      ProjectiveCoordinateAway R j →ₐ[R]
        SegreProductChartRing R m n i j).toRingHom)

/-- The transition ratio in the first projective factor is a unit on the product overlap. -/
lemma segreProductOverlapLeftRatio_isUnit
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    IsUnit
      (segreProductOverlapLeftRingHom R m n i a j b
        (projectiveCoordinateRatio R i a)) := by
  have hproduct :
      IsUnit
        (algebraMap
          (SegreProductChartRing R m n i j)
          (SegreProductChartOverlapRing R m n i a j b)
          (segreProductChartTransition R m n i a j b)) :=
    IsLocalization.Away.algebraMap_isUnit
      (segreProductChartTransition R m n i a j b)
  have hmul :
      segreProductOverlapLeftRingHom R m n i a j b
            (projectiveCoordinateRatio R i a) *
          segreProductOverlapRightRingHom R m n i a j b
            (projectiveCoordinateRatio R j b) =
        algebraMap
          (SegreProductChartRing R m n i j)
          (SegreProductChartOverlapRing R m n i a j b)
          (segreProductChartTransition R m n i a j b) := by
    simp [segreProductOverlapLeftRingHom,
      segreProductOverlapRightRingHom, segreProductChartTransition]
    rw [← map_mul]
    simp
  rw [← hmul] at hproduct
  exact (IsUnit.mul_iff.mp hproduct).1

/-- The transition ratio in the second projective factor is a unit on the product overlap. -/
lemma segreProductOverlapRightRatio_isUnit
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    IsUnit
      (segreProductOverlapRightRingHom R m n i a j b
        (projectiveCoordinateRatio R j b)) := by
  have hproduct :
      IsUnit
        (algebraMap
          (SegreProductChartRing R m n i j)
          (SegreProductChartOverlapRing R m n i a j b)
          (segreProductChartTransition R m n i a j b)) :=
    IsLocalization.Away.algebraMap_isUnit
      (segreProductChartTransition R m n i a j b)
  have hmul :
      segreProductOverlapLeftRingHom R m n i a j b
            (projectiveCoordinateRatio R i a) *
          segreProductOverlapRightRingHom R m n i a j b
            (projectiveCoordinateRatio R j b) =
        algebraMap
          (SegreProductChartRing R m n i j)
          (SegreProductChartOverlapRing R m n i a j b)
          (segreProductChartTransition R m n i a j b) := by
    simp [segreProductOverlapLeftRingHom,
      segreProductOverlapRightRingHom, segreProductChartTransition]
    rw [← map_mul]
    simp
  rw [← hmul] at hproduct
  exact (IsUnit.mul_iff.mp hproduct).2

end MvPolynomial
