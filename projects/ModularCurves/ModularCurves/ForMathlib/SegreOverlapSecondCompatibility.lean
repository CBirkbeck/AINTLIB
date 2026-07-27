/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's
`CoherentCohomologyFinite.SegreProductChartTransitionGeometry`.
-/
import ModularCurves.ForMathlib.SegreOverlapFirstProjFactorization
import ModularCurves.ForMathlib.SegreProductChartTransitionGeometry

/-!
# Second-chart compatibility of the localized Segre equivalence

The first and second standard charts map to a common double homogeneous localization. Their
coordinate ratios satisfy the usual projective transition identities there.
-/

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

noncomputable section

universe u v

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Projective coordinate ratios obey the standard transition identity on a double chart. -/
lemma projectiveChartOverlap_ratio_transition
    (R : Type u) [CommRing R] {σ : Type v} (i a c : σ) :
    projectiveSecondChartToOverlapAway R i a
          (projectiveCoordinateRatio R a c) *
        projectiveFirstChartToOverlapAway R i a
          (projectiveCoordinateRatio R i a) =
      projectiveFirstChartToOverlapAway R i a
        (projectiveCoordinateRatio R i c) := by
  apply HomogeneousLocalization.val_injective
  simp only [projectiveSecondChartToOverlapAway,
    projectiveFirstChartToOverlapAway,
    projectiveCoordinateRatio,
    HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_eq_r']
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, one_mul, pow_one]
  ring

/-- The first Segre-image chart maps to the common double homogeneous localization. -/
def segreImageFirstChartToOverlapAway
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    SegreImageChartRing R m n i j →+*
      SegreImageChartOverlapRing R m n i a j b :=
  HomogeneousLocalization.awayMap
    (segreImageGrading R m n)
    (segreImageCoordinate_mem_degreeOne R m n
      (segrePairIndex m n a b))
    rfl

/-- The second Segre-image chart maps to the same double homogeneous localization. -/
def segreImageSecondChartToOverlapAway
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    SegreImageChartRing R m n a b →+*
      SegreImageChartOverlapRing R m n i a j b :=
  HomogeneousLocalization.awayMap
    (segreImageGrading R m n)
    (segreImageCoordinate_mem_degreeOne R m n
      (segrePairIndex m n i j))
    (mul_comm
      (segreImageCoordinate R m n (segrePairIndex m n i j))
      (segreImageCoordinate R m n (segrePairIndex m n a b)))

/-- The left Segre-image coordinate ratio obeys the chart-transition formula. -/
lemma segreImageChartOverlap_leftRatio_transition
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a c : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreImageSecondChartToOverlapAway R m n i a j b
          (segreImageChartRatio R m n a c b b) *
        segreImageFirstChartToOverlapAway R m n i a j b
          (segreImageChartRatio R m n i a j j) =
      segreImageFirstChartToOverlapAway R m n i a j b
        (segreImageChartRatio R m n i c j j) := by
  apply HomogeneousLocalization.val_injective
  simp only [segreImageSecondChartToOverlapAway,
    segreImageFirstChartToOverlapAway,
    segreImageChartRatio,
    HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_eq_r']
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, one_mul, pow_one]
  rw [← segreImageCoordinate_cross_relation R m n i c j b]
  have hanchor :=
    segreImageCoordinate_cross_relation R m n i a j b
  calc
    _ =
        segreImageCoordinate R m n (segrePairIndex m n i j) *
          segreImageCoordinate R m n (segrePairIndex m n a b) *
          (segreImageCoordinate R m n (segrePairIndex m n c j) *
            (segreImageCoordinate R m n (segrePairIndex m n a j) *
              segreImageCoordinate R m n (segrePairIndex m n i b)) *
            segreImageCoordinate R m n (segrePairIndex m n a b)) := by
      ring
    _ = _ := by
      rw [hanchor]
      ring

/-- The right Segre-image coordinate ratio obeys the chart-transition formula. -/
lemma segreImageChartOverlap_rightRatio_transition
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b c : Fin (n + 1)) :
    segreImageSecondChartToOverlapAway R m n i a j b
          (segreImageChartRatio R m n a a b c) *
        segreImageFirstChartToOverlapAway R m n i a j b
          (segreImageChartRatio R m n i i j b) =
      segreImageFirstChartToOverlapAway R m n i a j b
        (segreImageChartRatio R m n i i j c) := by
  apply HomogeneousLocalization.val_injective
  simp only [segreImageSecondChartToOverlapAway,
    segreImageFirstChartToOverlapAway,
    segreImageChartRatio,
    HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_eq_r']
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, one_mul, pow_one]
  rw [← segreImageCoordinate_cross_relation R m n i a j c]
  have hanchor :=
    segreImageCoordinate_cross_relation R m n i a j b
  calc
    _ =
        segreImageCoordinate R m n (segrePairIndex m n i j) *
          segreImageCoordinate R m n (segrePairIndex m n a b) *
          (segreImageCoordinate R m n (segrePairIndex m n i c) *
            (segreImageCoordinate R m n (segrePairIndex m n a j) *
              segreImageCoordinate R m n (segrePairIndex m n i b)) *
            segreImageCoordinate R m n (segrePairIndex m n a b)) := by
      ring
    _ = _ := by
      rw [hanchor]
      ring

/-- The left projective coordinate ratio obeys the product-overlap transition formula. -/
lemma segreProductOverlap_leftRatio_transition
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a c : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreProductSecondLeftRingHom R m n i a j b
          (projectiveCoordinateRatio R a c) *
        segreProductOverlapLeftRingHom R m n i a j b
          (projectiveCoordinateRatio R i a) =
      segreProductOverlapLeftRingHom R m n i a j b
        (projectiveCoordinateRatio R i c) := by
  change
    segreProductLeftOverlapLift R m n i a j b
          (projectiveSecondChartToOverlapAway R i a
            (projectiveCoordinateRatio R a c)) *
        segreProductOverlapLeftRingHom R m n i a j b
          (projectiveCoordinateRatio R i a) =
      segreProductOverlapLeftRingHom R m n i a j b
        (projectiveCoordinateRatio R i c)
  rw [
    ← DFunLike.congr_fun
      (segreProductLeftOverlapLift_comp_first R m n i a j b)
      (projectiveCoordinateRatio R i a),
    ← DFunLike.congr_fun
      (segreProductLeftOverlapLift_comp_first R m n i a j b)
      (projectiveCoordinateRatio R i c),
    RingHom.comp_apply,
    ← map_mul,
    projectiveChartOverlap_ratio_transition]
  rfl

/-- The right projective coordinate ratio obeys the product-overlap transition formula. -/
lemma segreProductOverlap_rightRatio_transition
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b c : Fin (n + 1)) :
    segreProductSecondRightRingHom R m n i a j b
          (projectiveCoordinateRatio R b c) *
        segreProductOverlapRightRingHom R m n i a j b
          (projectiveCoordinateRatio R j b) =
      segreProductOverlapRightRingHom R m n i a j b
        (projectiveCoordinateRatio R j c) := by
  change
    segreProductRightOverlapLift R m n i a j b
          (projectiveSecondChartToOverlapAway R j b
            (projectiveCoordinateRatio R b c)) *
        segreProductOverlapRightRingHom R m n i a j b
          (projectiveCoordinateRatio R j b) =
      segreProductOverlapRightRingHom R m n i a j b
        (projectiveCoordinateRatio R j c)
  rw [
    ← DFunLike.congr_fun
      (segreProductRightOverlapLift_comp_first R m n i a j b)
      (projectiveCoordinateRatio R j b),
    ← DFunLike.congr_fun
      (segreProductRightOverlapLift_comp_first R m n i a j b)
      (projectiveCoordinateRatio R j c),
    RingHom.comp_apply,
    ← map_mul,
    projectiveChartOverlap_ratio_transition]
  rfl

/-- The localized Segre equivalence sends a first-chart left ratio to the left factor. -/
lemma segreStandardChartOverlapRingEquiv_firstLeftRatio
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a c : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreStandardChartOverlapRingEquiv R m n i a j b
        (segreImageFirstChartToOverlapAway R m n i a j b
          (segreImageChartRatio R m n i c j j)) =
      segreProductOverlapLeftRingHom R m n i a j b
        (projectiveCoordinateRatio R i c) := by
  unfold segreImageFirstChartToOverlapAway
  rw [
    segreStandardChartOverlapRingEquiv_awayMap,
    ← segreLeftChartToImageAlgHom_ratio R m n i c j,
    segreChartForwardAlgHom_left_ratio]
  rfl

/-- The localized Segre equivalence sends a first-chart right ratio to the right factor. -/
lemma segreStandardChartOverlapRingEquiv_firstRightRatio
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b c : Fin (n + 1)) :
    segreStandardChartOverlapRingEquiv R m n i a j b
        (segreImageFirstChartToOverlapAway R m n i a j b
          (segreImageChartRatio R m n i i j c)) =
      segreProductOverlapRightRingHom R m n i a j b
        (projectiveCoordinateRatio R j c) := by
  unfold segreImageFirstChartToOverlapAway
  rw [
    segreStandardChartOverlapRingEquiv_awayMap,
    ← segreRightChartToImageAlgHom_ratio R m n i j c,
    segreChartForwardAlgHom_right_ratio]
  rfl

end MvPolynomial
