/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's
`CoherentCohomologyFinite.SegreStandardChartInverse`.
-/
import ModularCurves.ForMathlib.SegreStandardChartForward

/-!
# The inverse map on a standard Segre chart

Fixing one anchor coordinate includes either factor's homogeneous coordinate
ring into the Segre coordinate image. These graded maps induce maps on standard
projective charts, whose tensor-product lift is the inverse candidate to
Segre dehomogenization.
-/

open HomogeneousLocalization
open scoped TensorProduct

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Insert the left variables into the Segre variables along the fixed right anchor `j`. -/
def segreLeftAnchorHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (j : Fin (n + 1)) :
    MvPolynomial (Fin (m + 1)) R →ₐ[R] SegreCoordinateRing R m n :=
  (segreRangeCoordinateHom R m n).comp
    (MvPolynomial.rename (fun a => segrePairIndex m n a j))

@[simp]
lemma segreLeftAnchorHom_X
    (R : Type u) [CommRing R] (m n : ℕ)
    (j : Fin (n + 1)) (a : Fin (m + 1)) :
    segreLeftAnchorHom R m n j (X a) =
      segreImageCoordinate R m n (segrePairIndex m n a j) := by
  simp [segreLeftAnchorHom, segreImageCoordinate]

lemma segreLeftAnchorHom_mem_grading
    (R : Type u) [CommRing R] (m n : ℕ)
    (j : Fin (n + 1)) {d : ℕ}
    {p : MvPolynomial (Fin (m + 1)) R}
    (hp : p ∈ homogeneousSubmodule (Fin (m + 1)) R d) :
    segreLeftAnchorHom R m n j p ∈ segreImageGrading R m n d := by
  apply segreRangeCoordinateHom_mem_imageGrading
  exact hp.rename_isHomogeneous

/-- The left-anchor insertion as a graded ring homomorphism. -/
def segreLeftAnchorGradedHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (j : Fin (n + 1)) :
    homogeneousSubmodule (Fin (m + 1)) R →+*ᵍ segreImageGrading R m n where
  __ := (segreLeftAnchorHom R m n j).toRingHom
  map_mem := segreLeftAnchorHom_mem_grading R m n j

@[simp]
lemma segreLeftAnchorGradedHom_X
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreLeftAnchorGradedHom R m n j (X i) =
      segreImageCoordinate R m n (segrePairIndex m n i j) := by
  exact segreLeftAnchorHom_X R m n j i

/-- Map the left projective chart into the Segre-image chart. -/
def segreLeftChartToImageRingHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ProjectiveCoordinateAway R i →+* SegreImageChartRing R m n i j :=
  HomogeneousLocalization.map
    (segreLeftAnchorGradedHom R m n j)
    (by
      rintro _ ⟨q, rfl⟩
      exact ⟨q, by simp [segreLeftAnchorGradedHom_X R m n i j]⟩)

@[simp]
lemma segreLeftChartToImageRingHom_ratio
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j : Fin (n + 1)) :
    segreLeftChartToImageRingHom R m n i j
        (projectiveCoordinateRatio R i a) =
      segreImageChartRatio R m n i a j j := by
  unfold segreLeftChartToImageRingHom
  unfold projectiveCoordinateRatio segreImageChartRatio
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.map_mk,
    HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.val_mk,
    segreLeftAnchorGradedHom_X R m n a j]

/-- Insert the right variables into the Segre variables along the fixed left anchor `i`. -/
def segreRightAnchorHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] SegreCoordinateRing R m n :=
  (segreRangeCoordinateHom R m n).comp
    (MvPolynomial.rename (fun b => segrePairIndex m n i b))

@[simp]
lemma segreRightAnchorHom_X
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (b : Fin (n + 1)) :
    segreRightAnchorHom R m n i (X b) =
      segreImageCoordinate R m n (segrePairIndex m n i b) := by
  simp [segreRightAnchorHom, segreImageCoordinate]

lemma segreRightAnchorHom_mem_grading
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) {d : ℕ}
    {p : MvPolynomial (Fin (n + 1)) R}
    (hp : p ∈ homogeneousSubmodule (Fin (n + 1)) R d) :
    segreRightAnchorHom R m n i p ∈ segreImageGrading R m n d := by
  apply segreRangeCoordinateHom_mem_imageGrading
  exact hp.rename_isHomogeneous

/-- The right-anchor insertion as a graded ring homomorphism. -/
def segreRightAnchorGradedHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) :
    homogeneousSubmodule (Fin (n + 1)) R →+*ᵍ segreImageGrading R m n where
  __ := (segreRightAnchorHom R m n i).toRingHom
  map_mem := segreRightAnchorHom_mem_grading R m n i

@[simp]
lemma segreRightAnchorGradedHom_X
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreRightAnchorGradedHom R m n i (X j) =
      segreImageCoordinate R m n (segrePairIndex m n i j) := by
  exact segreRightAnchorHom_X R m n i j

/-- Map the right projective chart into the Segre-image chart. -/
def segreRightChartToImageRingHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ProjectiveCoordinateAway R j →+* SegreImageChartRing R m n i j :=
  HomogeneousLocalization.map
    (segreRightAnchorGradedHom R m n i)
    (by
      rintro _ ⟨q, rfl⟩
      exact ⟨q, by simp [segreRightAnchorGradedHom_X R m n i j]⟩)

@[simp]
lemma segreRightChartToImageRingHom_ratio
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreRightChartToImageRingHom R m n i j
        (projectiveCoordinateRatio R j b) =
      segreImageChartRatio R m n i i j b := by
  unfold segreRightChartToImageRingHom
  unfold projectiveCoordinateRatio segreImageChartRatio
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.map_mk,
    HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.val_mk,
    segreRightAnchorGradedHom_X R m n i b]

/-- The left chart ring map preserves coefficients. -/
lemma segreLeftChartToImageRingHom_algebraMap
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) (r : R) :
    segreLeftChartToImageRingHom R m n i j
        (algebraMap R (ProjectiveCoordinateAway R i) r) =
      algebraMap R (SegreImageChartRing R m n i j) r := by
  rw [algebraMap_homogeneousAway_X_eq_awayConst]
  rw [segreImageAway_algebraMap_eq_mk R m n
    (segreImageCoordinate R m n (segrePairIndex m n i j))
    (segreImageCoordinate_mem_degreeOne R m n (segrePairIndex m n i j)) r]
  unfold awayConst segreLeftChartToImageRingHom
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.map_mk,
    HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.val_mk,
    segreLeftAnchorGradedHom,
    segreLeftAnchorHom]

/-- The right chart ring map preserves coefficients. -/
lemma segreRightChartToImageRingHom_algebraMap
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) (r : R) :
    segreRightChartToImageRingHom R m n i j
        (algebraMap R (ProjectiveCoordinateAway R j) r) =
      algebraMap R (SegreImageChartRing R m n i j) r := by
  rw [algebraMap_homogeneousAway_X_eq_awayConst]
  rw [segreImageAway_algebraMap_eq_mk R m n
    (segreImageCoordinate R m n (segrePairIndex m n i j))
    (segreImageCoordinate_mem_degreeOne R m n (segrePairIndex m n i j)) r]
  unfold awayConst segreRightChartToImageRingHom
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.map_mk,
    HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.val_mk,
    segreRightAnchorGradedHom,
    segreRightAnchorHom]

/-- The left projective-chart map as a coefficient-algebra map. -/
def segreLeftChartToImageAlgHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ProjectiveCoordinateAway R i →ₐ[R] SegreImageChartRing R m n i j where
  __ := segreLeftChartToImageRingHom R m n i j
  commutes' := segreLeftChartToImageRingHom_algebraMap R m n i j

/-- The right projective-chart map as a coefficient-algebra map. -/
def segreRightChartToImageAlgHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ProjectiveCoordinateAway R j →ₐ[R] SegreImageChartRing R m n i j where
  __ := segreRightChartToImageRingHom R m n i j
  commutes' := segreRightChartToImageRingHom_algebraMap R m n i j

@[simp]
lemma segreLeftChartToImageAlgHom_ratio
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j : Fin (n + 1)) :
    segreLeftChartToImageAlgHom R m n i j
        (projectiveCoordinateRatio R i a) =
      segreImageChartRatio R m n i a j j :=
  segreLeftChartToImageRingHom_ratio R m n i a j

@[simp]
lemma segreRightChartToImageAlgHom_ratio
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreRightChartToImageAlgHom R m n i j
        (projectiveCoordinateRatio R j b) =
      segreImageChartRatio R m n i i j b :=
  segreRightChartToImageRingHom_ratio R m n i j b

lemma segreChartAnchorMaps_commute
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (x : ProjectiveCoordinateAway R i)
    (y : ProjectiveCoordinateAway R j) :
    Commute
      (segreLeftChartToImageAlgHom R m n i j x)
      (segreRightChartToImageAlgHom R m n i j y) :=
  Commute.all _ _

/-- Multiply the two anchor maps to obtain the inverse candidate on the product chart. -/
def segreChartInverseAlgHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    SegreProductChartRing R m n i j →ₐ[R] SegreImageChartRing R m n i j :=
  Algebra.TensorProduct.lift
    (segreLeftChartToImageAlgHom R m n i j)
    (segreRightChartToImageAlgHom R m n i j)
    (segreChartAnchorMaps_commute R m n i j)

end MvPolynomial
