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

universe u v

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
    (R : Type u) [CommRing R] {σ : Type v} (i a : σ) :=
  Away (homogeneousSubmodule σ R) (X i * X a)

private lemma projectiveCoordinateRatio_eq_isLocalizationElem
    (R : Type u) [CommRing R] {σ : Type v} (i a : σ) :
    projectiveCoordinateRatio R i a =
      Away.isLocalizationElem
        (X_mem_homogeneousSubmodule_one R i)
        (X_mem_homogeneousSubmodule_one R a) := by
  change Away.mk _ _ 1 (X a) _ = Away.mk _ _ 1 (X a ^ 1) _
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, pow_one]

/-- The first projective chart maps canonically to the double homogeneous localization. -/
def projectiveFirstChartToOverlapAway
    (R : Type u) [CommRing R] {σ : Type v} (i a : σ) :
    ProjectiveCoordinateAway R i →+*
      ProjectiveCoordinateOverlapAway R i a :=
  awayMap
    (homogeneousSubmodule σ R)
    (X_mem_homogeneousSubmodule_one R a)
    rfl

/-- The second projective chart maps canonically to the double homogeneous localization. -/
def projectiveSecondChartToOverlapAway
    (R : Type u) [CommRing R] {σ : Type v} (i a : σ) :
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

/-- The first-factor overlap lift extends its map from the first projective chart. -/
lemma segreProductLeftOverlapLift_comp_first
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductLeftOverlapLift R m n i a j b).comp
        (projectiveFirstChartToOverlapAway R i a) =
      segreProductOverlapLeftRingHom R m n i a j b := by
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
  change
    (IsLocalization.Away.lift
        (projectiveCoordinateRatio R i a)
        (segreProductOverlapLeftRatio_isUnit R m n i a j b)).comp
          (algebraMap
            (ProjectiveCoordinateAway R i)
            (ProjectiveCoordinateOverlapAway R i a)) =
      segreProductOverlapLeftRingHom R m n i a j b
  exact IsLocalization.Away.lift_comp
    (projectiveCoordinateRatio R i a)
    (segreProductOverlapLeftRatio_isUnit R m n i a j b)

/-- The second-factor overlap lift extends its map from the first projective chart. -/
lemma segreProductRightOverlapLift_comp_first
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductRightOverlapLift R m n i a j b).comp
        (projectiveFirstChartToOverlapAway R j b) =
      segreProductOverlapRightRingHom R m n i a j b := by
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
  change
    (IsLocalization.Away.lift
        (projectiveCoordinateRatio R j b)
        (segreProductOverlapRightRatio_isUnit R m n i a j b)).comp
          (algebraMap
            (ProjectiveCoordinateAway R j)
            (ProjectiveCoordinateOverlapAway R j b)) =
      segreProductOverlapRightRingHom R m n i a j b
  exact IsLocalization.Away.lift_comp
    (projectiveCoordinateRatio R j b)
    (segreProductOverlapRightRatio_isUnit R m n i a j b)

private def projectiveFirstChartToOverlapAwayAlgHom
    (R : Type u) [CommRing R] {σ : Type v} (i a : σ) :
    ProjectiveCoordinateAway R i →ₐ[R]
      ProjectiveCoordinateOverlapAway R i a where
  __ := projectiveFirstChartToOverlapAway R i a
  commutes' r := HomogeneousLocalization.awayMap_fromZeroRingHom
    (homogeneousSubmodule σ R)
    (X_mem_homogeneousSubmodule_one R a)
    rfl
    (algebraMap R (homogeneousSubmodule σ R 0) r)

private def projectiveSecondChartToOverlapAwayAlgHom
    (R : Type u) [CommRing R] {σ : Type v} (i a : σ) :
    ProjectiveCoordinateAway R a →ₐ[R]
      ProjectiveCoordinateOverlapAway R i a where
  __ := projectiveSecondChartToOverlapAway R i a
  commutes' r := HomogeneousLocalization.awayMap_fromZeroRingHom
    (homogeneousSubmodule σ R)
    (X_mem_homogeneousSubmodule_one R i)
    (mul_comm (X i) (X a))
    (algebraMap R (homogeneousSubmodule σ R 0) r)

private def segreProductOverlapLeftAlgHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateAway R i →ₐ[R]
      SegreProductChartOverlapRing R m n i a j b where
  __ := segreProductOverlapLeftRingHom R m n i a j b
  commutes' r := by
    simp [segreProductOverlapLeftRingHom]
    change
      algebraMap
          (SegreProductChartRing R m n i j)
          (SegreProductChartOverlapRing R m n i a j b)
          (algebraMap R (SegreProductChartRing R m n i j) r) =
        algebraMap R (SegreProductChartOverlapRing R m n i a j b) r
    exact
      (IsScalarTower.algebraMap_apply
        R
        (SegreProductChartRing R m n i j)
        (SegreProductChartOverlapRing R m n i a j b)
        r).symm

private def segreProductOverlapRightAlgHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateAway R j →ₐ[R]
      SegreProductChartOverlapRing R m n i a j b where
  __ := segreProductOverlapRightRingHom R m n i a j b
  commutes' r := by
    simp [segreProductOverlapRightRingHom]
    change
      algebraMap
          (SegreProductChartRing R m n i j)
          (SegreProductChartOverlapRing R m n i a j b)
          (algebraMap R (SegreProductChartRing R m n i j) r) =
        algebraMap R (SegreProductChartOverlapRing R m n i a j b) r
    exact
      (IsScalarTower.algebraMap_apply
        R
        (SegreProductChartRing R m n i j)
        (SegreProductChartOverlapRing R m n i a j b)
        r).symm

private def segreProductLeftOverlapLiftAlgHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateOverlapAway R i a →ₐ[R]
      SegreProductChartOverlapRing R m n i a j b where
  __ := segreProductLeftOverlapLift R m n i a j b
  commutes' r := by
    rw [← (projectiveFirstChartToOverlapAwayAlgHom R i a).commutes r]
    change
      ((segreProductLeftOverlapLift R m n i a j b).comp
        (projectiveFirstChartToOverlapAway R i a))
          (algebraMap R (ProjectiveCoordinateAway R i) r) =
        algebraMap R (SegreProductChartOverlapRing R m n i a j b) r
    rw [segreProductLeftOverlapLift_comp_first]
    exact (segreProductOverlapLeftAlgHom R m n i a j b).commutes r

private def segreProductRightOverlapLiftAlgHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateOverlapAway R j b →ₐ[R]
      SegreProductChartOverlapRing R m n i a j b where
  __ := segreProductRightOverlapLift R m n i a j b
  commutes' r := by
    rw [← (projectiveFirstChartToOverlapAwayAlgHom R j b).commutes r]
    change
      ((segreProductRightOverlapLift R m n i a j b).comp
        (projectiveFirstChartToOverlapAway R j b))
          (algebraMap R (ProjectiveCoordinateAway R j) r) =
        algebraMap R (SegreProductChartOverlapRing R m n i a j b) r
    rw [segreProductRightOverlapLift_comp_first]
    exact (segreProductOverlapRightAlgHom R m n i a j b).commutes r

/-- The first factor of the second product chart, expressed in the common overlap ring. -/
def segreProductSecondLeftAlgHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateAway R a →ₐ[R]
      SegreProductChartOverlapRing R m n i a j b :=
  (segreProductLeftOverlapLiftAlgHom R m n i a j b).comp
    (projectiveSecondChartToOverlapAwayAlgHom R i a)

/-- The second factor of the second product chart, expressed in the common overlap ring. -/
def segreProductSecondRightAlgHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateAway R b →ₐ[R]
      SegreProductChartOverlapRing R m n i a j b :=
  (segreProductRightOverlapLiftAlgHom R m n i a j b).comp
    (projectiveSecondChartToOverlapAwayAlgHom R j b)

/-- The ring homomorphism underlying the first factor of the second product chart. -/
abbrev segreProductSecondLeftRingHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateAway R a →+*
      SegreProductChartOverlapRing R m n i a j b :=
  (segreProductSecondLeftAlgHom R m n i a j b).toRingHom

/-- The ring homomorphism underlying the second factor of the second product chart. -/
abbrev segreProductSecondRightRingHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateAway R b →+*
      SegreProductChartOverlapRing R m n i a j b :=
  (segreProductSecondRightAlgHom R m n i a j b).toRingHom

end MvPolynomial
