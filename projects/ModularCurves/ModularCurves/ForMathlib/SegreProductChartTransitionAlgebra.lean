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

/-- The double homogeneous localization attached to two standard projective charts. -/
abbrev ProjectiveCoordinateOverlapAway
    (R : Type u) [CommRing R] {σ : Type} (i a : σ) :=
  Away (homogeneousSubmodule σ R) (X i * X a)

private lemma projectiveCoordinateRatio_eq_isLocalizationElem
    (R : Type u) [CommRing R] {σ : Type} (i a : σ) :
    projectiveCoordinateRatio R i a =
      Away.isLocalizationElem
        (X_mem_homogeneousSubmodule_one R i)
        (X_mem_homogeneousSubmodule_one R a) := by
  change Away.mk _ _ 1 (X a) _ = Away.mk _ _ 1 (X a ^ 1) _
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, pow_one]

/-- The first projective chart maps canonically to the double homogeneous localization. -/
def projectiveFirstChartToOverlapAway
    (R : Type u) [CommRing R] {σ : Type} (i a : σ) :
    ProjectiveCoordinateAway R i →+*
      ProjectiveCoordinateOverlapAway R i a :=
  awayMap
    (homogeneousSubmodule σ R)
    (X_mem_homogeneousSubmodule_one R a)
    rfl

/-- The second projective chart maps canonically to the double homogeneous localization. -/
def projectiveSecondChartToOverlapAway
    (R : Type u) [CommRing R] {σ : Type} (i a : σ) :
    ProjectiveCoordinateAway R a →+*
      ProjectiveCoordinateOverlapAway R i a :=
  awayMap
    (homogeneousSubmodule σ R)
    (X_mem_homogeneousSubmodule_one R i)
    (mul_comm (X i) (X a))

/-- Extend the first projective factor from its first chart to the common double overlap. -/
def segreProductLeftOverlapLift
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateOverlapAway R i a →+*
      SegreProductChartOverlapRing R m n i a j b := by
  letI := (projectiveFirstChartToOverlapAway R i a).toAlgebra
  letI :
      IsLocalization.Away
        (projectiveCoordinateRatio R i a)
        (ProjectiveCoordinateOverlapAway R i a) := by
    rw [projectiveCoordinateRatio_eq_isLocalizationElem]
    exact Away.isLocalization_mul
      (X_mem_homogeneousSubmodule_one R i)
      (X_mem_homogeneousSubmodule_one R a)
      rfl Nat.one_ne_zero
  exact IsLocalization.Away.lift
    (projectiveCoordinateRatio R i a)
    (segreProductOverlapLeftRatio_isUnit R m n i a j b)

/-- Extend the second projective factor from its first chart to the common double overlap. -/
def segreProductRightOverlapLift
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateOverlapAway R j b →+*
      SegreProductChartOverlapRing R m n i a j b := by
  letI := (projectiveFirstChartToOverlapAway R j b).toAlgebra
  letI :
      IsLocalization.Away
        (projectiveCoordinateRatio R j b)
        (ProjectiveCoordinateOverlapAway R j b) := by
    rw [projectiveCoordinateRatio_eq_isLocalizationElem]
    exact Away.isLocalization_mul
      (X_mem_homogeneousSubmodule_one R j)
      (X_mem_homogeneousSubmodule_one R b)
      rfl Nat.one_ne_zero
  exact IsLocalization.Away.lift
    (projectiveCoordinateRatio R j b)
    (segreProductOverlapRightRatio_isUnit R m n i a j b)

end MvPolynomial
