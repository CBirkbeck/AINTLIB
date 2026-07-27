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

/-- The localized Segre equivalence sends a second-chart left ratio to the left factor. -/
lemma segreStandardChartOverlapRingEquiv_secondLeftRatio
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a c : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreStandardChartOverlapRingEquiv R m n i a j b
        (segreImageSecondChartToOverlapAway R m n i a j b
          (segreImageChartRatio R m n a c b b)) =
      segreProductSecondLeftRingHom R m n i a j b
        (projectiveCoordinateRatio R a c) := by
  apply
    (segreProductOverlapLeftRatio_isUnit R m n i a j b).mul_right_cancel
  calc
    _ =
        segreStandardChartOverlapRingEquiv R m n i a j b
            (segreImageSecondChartToOverlapAway R m n i a j b
              (segreImageChartRatio R m n a c b b)) *
          segreStandardChartOverlapRingEquiv R m n i a j b
            (segreImageFirstChartToOverlapAway R m n i a j b
              (segreImageChartRatio R m n i a j j)) := by
      rw [
        segreStandardChartOverlapRingEquiv_firstLeftRatio
          R m n i a a j b]
    _ =
        segreStandardChartOverlapRingEquiv R m n i a j b
          (segreImageSecondChartToOverlapAway R m n i a j b
                (segreImageChartRatio R m n a c b b) *
            segreImageFirstChartToOverlapAway R m n i a j b
              (segreImageChartRatio R m n i a j j)) := by
      rw [map_mul]
    _ =
        segreStandardChartOverlapRingEquiv R m n i a j b
          (segreImageFirstChartToOverlapAway R m n i a j b
            (segreImageChartRatio R m n i c j j)) := by
      rw [segreImageChartOverlap_leftRatio_transition]
    _ =
        segreProductOverlapLeftRingHom R m n i a j b
          (projectiveCoordinateRatio R i c) :=
      segreStandardChartOverlapRingEquiv_firstLeftRatio
        R m n i a c j b
    _ =
        segreProductSecondLeftRingHom R m n i a j b
              (projectiveCoordinateRatio R a c) *
            segreProductOverlapLeftRingHom R m n i a j b
              (projectiveCoordinateRatio R i a) :=
      (segreProductOverlap_leftRatio_transition
        R m n i a c j b).symm

/-- The localized Segre equivalence sends a second-chart right ratio to the right factor. -/
lemma segreStandardChartOverlapRingEquiv_secondRightRatio
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b c : Fin (n + 1)) :
    segreStandardChartOverlapRingEquiv R m n i a j b
        (segreImageSecondChartToOverlapAway R m n i a j b
          (segreImageChartRatio R m n a a b c)) =
      segreProductSecondRightRingHom R m n i a j b
        (projectiveCoordinateRatio R b c) := by
  apply
    (segreProductOverlapRightRatio_isUnit R m n i a j b).mul_right_cancel
  calc
    _ =
        segreStandardChartOverlapRingEquiv R m n i a j b
            (segreImageSecondChartToOverlapAway R m n i a j b
              (segreImageChartRatio R m n a a b c)) *
          segreStandardChartOverlapRingEquiv R m n i a j b
            (segreImageFirstChartToOverlapAway R m n i a j b
              (segreImageChartRatio R m n i i j b)) := by
      rw [
        segreStandardChartOverlapRingEquiv_firstRightRatio
          R m n i a j b b]
    _ =
        segreStandardChartOverlapRingEquiv R m n i a j b
          (segreImageSecondChartToOverlapAway R m n i a j b
                (segreImageChartRatio R m n a a b c) *
            segreImageFirstChartToOverlapAway R m n i a j b
              (segreImageChartRatio R m n i i j b)) := by
      rw [map_mul]
    _ =
        segreStandardChartOverlapRingEquiv R m n i a j b
          (segreImageFirstChartToOverlapAway R m n i a j b
            (segreImageChartRatio R m n i i j c)) := by
      rw [segreImageChartOverlap_rightRatio_transition]
    _ =
        segreProductOverlapRightRingHom R m n i a j b
          (projectiveCoordinateRatio R j c) :=
      segreStandardChartOverlapRingEquiv_firstRightRatio
        R m n i a j b c
    _ =
        segreProductSecondRightRingHom R m n i a j b
              (projectiveCoordinateRatio R b c) *
            segreProductOverlapRightRingHom R m n i a j b
              (projectiveCoordinateRatio R j b) :=
      (segreProductOverlap_rightRatio_transition
        R m n i a j b c).symm

/-- The Segre-image away algebra map is the degree-zero localization inclusion. -/
lemma segreImageAway_algebraMap_eq_fromZero
    (R : Type u) [CommRing R] (m n : ℕ)
    (f : SegreCoordinateRing R m n) (r : R) :
    algebraMap R
        (Away (segreImageGrading R m n) f) r =
      HomogeneousLocalization.fromZeroRingHom
        (segreImageGrading R m n)
        (Submonoid.powers f)
        (algebraMap R (segreImageGrading R m n 0) r) := rfl

/-- The first Segre-image chart map to the overlap preserves coefficients. -/
lemma segreImageFirstChartToOverlapAway_algebraMap
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1))
    (r : R) :
    segreImageFirstChartToOverlapAway R m n i a j b
        (algebraMap R (SegreImageChartRing R m n i j) r) =
      algebraMap R
        (SegreImageChartOverlapRing R m n i a j b) r := by
  rw [segreImageAway_algebraMap_eq_fromZero
    R m n
    (segreImageCoordinate R m n (segrePairIndex m n i j))
    r]
  rw [segreImageAway_algebraMap_eq_fromZero
    R m n
    (segreImageCoordinate R m n (segrePairIndex m n i j) *
      segreImageCoordinate R m n (segrePairIndex m n a b))
    r]
  exact
    HomogeneousLocalization.awayMap_fromZeroRingHom
      (segreImageGrading R m n)
      (segreImageCoordinate_mem_degreeOne R m n
        (segrePairIndex m n a b))
      rfl
      (algebraMap R (segreImageGrading R m n 0) r)

/-- The second Segre-image chart map to the overlap preserves coefficients. -/
lemma segreImageSecondChartToOverlapAway_algebraMap
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1))
    (r : R) :
    segreImageSecondChartToOverlapAway R m n i a j b
        (algebraMap R (SegreImageChartRing R m n a b) r) =
      algebraMap R
        (SegreImageChartOverlapRing R m n i a j b) r := by
  rw [segreImageAway_algebraMap_eq_fromZero
    R m n
    (segreImageCoordinate R m n (segrePairIndex m n a b))
    r]
  rw [segreImageAway_algebraMap_eq_fromZero
    R m n
    (segreImageCoordinate R m n (segrePairIndex m n i j) *
      segreImageCoordinate R m n (segrePairIndex m n a b))
    r]
  exact
    HomogeneousLocalization.awayMap_fromZeroRingHom
      (segreImageGrading R m n)
      (segreImageCoordinate_mem_degreeOne R m n
        (segrePairIndex m n i j))
      (mul_comm
        (segreImageCoordinate R m n (segrePairIndex m n i j))
        (segreImageCoordinate R m n (segrePairIndex m n a b)))
      (algebraMap R (segreImageGrading R m n 0) r)

/-- The localized Segre ring equivalence preserves coefficients. -/
lemma segreStandardChartOverlapRingEquiv_algebraMap
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1))
    (r : R) :
    segreStandardChartOverlapRingEquiv R m n i a j b
        (algebraMap R
          (SegreImageChartOverlapRing R m n i a j b) r) =
      algebraMap R
        (SegreProductChartOverlapRing R m n i a j b) r := by
  rw [← segreImageFirstChartToOverlapAway_algebraMap
    R m n i a j b r]
  unfold segreImageFirstChartToOverlapAway
  rw [segreStandardChartOverlapRingEquiv_awayMap]
  rw [(segreChartForwardAlgHom R m n i j).commutes]
  exact
    (IsScalarTower.algebraMap_apply
      R
      (SegreProductChartRing R m n i j)
      (SegreProductChartOverlapRing R m n i a j b)
      r).symm

/-- The localized Segre chart equivalence as an equivalence of coefficient algebras. -/
def segreStandardChartOverlapAlgEquiv
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    SegreImageChartOverlapRing R m n i a j b ≃ₐ[R]
      SegreProductChartOverlapRing R m n i a j b :=
  { segreStandardChartOverlapRingEquiv R m n i a j b with
    commutes' :=
      segreStandardChartOverlapRingEquiv_algebraMap
        R m n i a j b }

/-- The second Segre-image chart, mapped to the common product overlap. -/
def segreStandardSecondChartOverlapAlgHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    SegreImageChartRing R m n a b →ₐ[R]
      SegreProductChartOverlapRing R m n i a j b where
  __ :=
    (segreStandardChartOverlapRingEquiv
      R m n i a j b).toRingHom.comp
      (segreImageSecondChartToOverlapAway
        R m n i a j b)
  commutes' r := by
    change
      segreStandardChartOverlapRingEquiv R m n i a j b
          (segreImageSecondChartToOverlapAway R m n i a j b
            (algebraMap R
              (SegreImageChartRing R m n a b) r)) =
        algebraMap R
          (SegreProductChartOverlapRing R m n i a j b) r
    rw [segreImageSecondChartToOverlapAway_algebraMap,
      segreStandardChartOverlapRingEquiv_algebraMap]

/-- The second Segre-image chart map restricts to the expected left factor map. -/
lemma segreStandardSecondChartOverlapAlgHom_comp_left
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreStandardSecondChartOverlapAlgHom
        R m n i a j b).comp
        (segreLeftChartToImageAlgHom R m n a b) =
      segreProductSecondLeftAlgHom R m n i a j b := by
  apply
    (AlgHom.cancel_right
      (projectiveCoordinateDehomogenization_surjective R a)).mp
  ext c
  simp only [AlgHom.comp_apply,
    projectiveCoordinateDehomogenization_X]
  change
    segreStandardChartOverlapRingEquiv R m n i a j b
        (segreImageSecondChartToOverlapAway R m n i a j b
          (segreLeftChartToImageAlgHom R m n a b
            (projectiveCoordinateRatio R a c))) =
      segreProductSecondLeftRingHom R m n i a j b
        (projectiveCoordinateRatio R a c)
  rw [segreLeftChartToImageAlgHom_ratio,
    segreStandardChartOverlapRingEquiv_secondLeftRatio]

/-- The second Segre-image chart map restricts to the expected right factor map. -/
lemma segreStandardSecondChartOverlapAlgHom_comp_right
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreStandardSecondChartOverlapAlgHom
        R m n i a j b).comp
        (segreRightChartToImageAlgHom R m n a b) =
      segreProductSecondRightAlgHom R m n i a j b := by
  apply
    (AlgHom.cancel_right
      (projectiveCoordinateDehomogenization_surjective R b)).mp
  ext c
  simp only [AlgHom.comp_apply,
    projectiveCoordinateDehomogenization_X]
  change
    segreStandardChartOverlapRingEquiv R m n i a j b
        (segreImageSecondChartToOverlapAway R m n i a j b
          (segreRightChartToImageAlgHom R m n a b
            (projectiveCoordinateRatio R b c))) =
      segreProductSecondRightRingHom R m n i a j b
        (projectiveCoordinateRatio R b c)
  rw [segreRightChartToImageAlgHom_ratio,
    segreStandardChartOverlapRingEquiv_secondRightRatio]

/-- The second-chart overlap map composed with the Segre inverse is the product transition. -/
lemma segreStandardSecondChartOverlapAlgHom_comp_inverse
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreStandardSecondChartOverlapAlgHom
        R m n i a j b).comp
        (segreChartInverseAlgHom R m n a b) =
      segreProductSecondChartAlgHom R m n i a j b := by
  apply Algebra.TensorProduct.ext
  · ext x
    change
      segreStandardSecondChartOverlapAlgHom R m n i a j b
          (segreChartInverseAlgHom R m n a b
            ((Algebra.TensorProduct.includeLeft :
              ProjectiveCoordinateAway R a →ₐ[R]
                SegreProductChartRing R m n a b) x)) =
        segreProductSecondChartAlgHom R m n i a j b
          ((Algebra.TensorProduct.includeLeft :
            ProjectiveCoordinateAway R a →ₐ[R]
              SegreProductChartRing R m n a b) x)
    rw [show
      segreChartInverseAlgHom R m n a b
          ((Algebra.TensorProduct.includeLeft :
            ProjectiveCoordinateAway R a →ₐ[R]
              SegreProductChartRing R m n a b) x) =
        segreLeftChartToImageAlgHom R m n a b x by
      simp [segreChartInverseAlgHom]]
    rw [show
      segreProductSecondChartAlgHom R m n i a j b
          ((Algebra.TensorProduct.includeLeft :
            ProjectiveCoordinateAway R a →ₐ[R]
              SegreProductChartRing R m n a b) x) =
        segreProductSecondLeftAlgHom R m n i a j b x by
      exact
        DFunLike.congr_fun
          (segreProductSecondChartAlgHom_comp_left
            R m n i a j b) x]
    exact
      DFunLike.congr_fun
        (segreStandardSecondChartOverlapAlgHom_comp_left
          R m n i a j b) x
  · ext y
    change
      segreStandardSecondChartOverlapAlgHom R m n i a j b
          (segreChartInverseAlgHom R m n a b
            ((Algebra.TensorProduct.includeRight :
              ProjectiveCoordinateAway R b →ₐ[R]
                SegreProductChartRing R m n a b) y)) =
        segreProductSecondChartAlgHom R m n i a j b
          ((Algebra.TensorProduct.includeRight :
            ProjectiveCoordinateAway R b →ₐ[R]
              SegreProductChartRing R m n a b) y)
    rw [show
      segreChartInverseAlgHom R m n a b
          ((Algebra.TensorProduct.includeRight :
            ProjectiveCoordinateAway R b →ₐ[R]
              SegreProductChartRing R m n a b) y) =
        segreRightChartToImageAlgHom R m n a b y by
      simp [segreChartInverseAlgHom]]
    rw [show
      segreProductSecondChartAlgHom R m n i a j b
          ((Algebra.TensorProduct.includeRight :
            ProjectiveCoordinateAway R b →ₐ[R]
              SegreProductChartRing R m n a b) y) =
        segreProductSecondRightAlgHom R m n i a j b y by
      exact
        DFunLike.congr_fun
          (segreProductSecondChartAlgHom_comp_right
            R m n i a j b) y]
    exact
      DFunLike.congr_fun
        (segreStandardSecondChartOverlapAlgHom_comp_right
          R m n i a j b) y

/-- The second-image-chart overlap map is the standard forward map followed by transition. -/
lemma segreStandardSecondChartOverlapAlgHom_eq
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreStandardSecondChartOverlapAlgHom R m n i a j b =
      (segreProductSecondChartAlgHom R m n i a j b).comp
        (segreChartForwardAlgHom R m n a b) := by
  ext x
  have hx :=
    DFunLike.congr_fun
      (segreChartInverseAlgHom_comp_forward R m n a b) x
  have hx' :
      segreChartInverseAlgHom R m n a b
          (segreChartForwardAlgHom R m n a b x) =
        x := by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using hx
  calc
    _ =
        segreStandardSecondChartOverlapAlgHom R m n i a j b
          (segreChartInverseAlgHom R m n a b
            (segreChartForwardAlgHom R m n a b x)) := by
      exact
        congrArg
          (segreStandardSecondChartOverlapAlgHom
            R m n i a j b) hx'.symm
    _ =
        segreProductSecondChartAlgHom R m n i a j b
          (segreChartForwardAlgHom R m n a b x) :=
      DFunLike.congr_fun
        (segreStandardSecondChartOverlapAlgHom_comp_inverse
          R m n i a j b)
        (segreChartForwardAlgHom R m n a b x)
    _ = _ := rfl

/-- The double Segre-image chart maps to its second standard chart. -/
def segreImageOverlapToSecondChart
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec
        (CommRingCat.of
          (SegreImageChartOverlapRing R m n i a j b)) ⟶
      Spec
        (CommRingCat.of
          (SegreImageChartRing R m n a b)) :=
  Spec.map
    (CommRingCat.ofHom
      (segreImageSecondChartToOverlapAway R m n i a j b))

/-- The product-overlap isomorphism intertwines the second standard charts. -/
@[reassoc]
lemma segreProductOverlapIsoSegreImage_hom_toSecondChart
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductOverlapIsoSegreImage R m n i a j b).hom ≫
        segreImageOverlapToSecondChart R m n i a j b =
      Spec.map
          (CommRingCat.ofHom
            (segreProductSecondChartAlgHom
              R m n i a j b).toRingHom) ≫
        Spec.map
          (CommRingCat.ofHom
            (segreChartForwardAlgHom
              R m n a b).toRingHom) := by
  simp only [segreProductOverlapIsoSegreImage,
    segreImageOverlapToSecondChart,
    Scheme.Spec_map, Functor.mapIso_hom, Iso.op_hom,
    Quiver.Hom.unop_op, ← Spec.map_comp]
  congr 1
  ext x
  exact
    DFunLike.congr_fun
      (segreStandardSecondChartOverlapAlgHom_eq
        R m n i a j b) x

/-- The double Segre-image chart factors through its second standard chart into `Proj`. -/
lemma segreImageOverlapToSecondChart_toProj
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreImageOverlapToSecondChart R m n i a j b ≫
        Proj.awayι
          (segreImageGrading R m n)
          (segreImageCoordinate R m n
            (segrePairIndex m n a b))
          (segreImageCoordinate_mem_degreeOne R m n
            (segrePairIndex m n a b))
          Nat.zero_lt_one =
      segreImageOverlapToProj R m n i a j b := by
  change
    Spec.map
          (CommRingCat.ofHom
            (awayMap
              (segreImageGrading R m n)
              (segreImageCoordinate_mem_degreeOne R m n
                (segrePairIndex m n i j))
              (mul_comm
                (segreImageCoordinate R m n
                  (segrePairIndex m n i j))
                (segreImageCoordinate R m n
                  (segrePairIndex m n a b))))) ≫
        Proj.awayι
          (segreImageGrading R m n)
          (segreImageCoordinate R m n
            (segrePairIndex m n a b))
          (segreImageCoordinate_mem_degreeOne R m n
            (segrePairIndex m n a b))
          Nat.zero_lt_one =
      Proj.awayι
        (segreImageGrading R m n)
        (segreImageCoordinate R m n
            (segrePairIndex m n i j) *
          segreImageCoordinate R m n
            (segrePairIndex m n a b))
        (SetLike.mul_mem_graded
          (segreImageCoordinate_mem_degreeOne R m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne R m n
            (segrePairIndex m n a b)))
        (by omega)
  rw [Proj.awayι, Proj.awayι, Iso.eq_inv_comp,
    Proj.basicOpenIsoSpec_hom,
    Proj.basicOpenToSpec_SpecMap_awayMap_assoc,
    ← Proj.basicOpenIsoSpec_hom _ _ _ _,
    Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]
  · exact
      segreImageCoordinate_mem_degreeOne R m n
        (segrePairIndex m n a b)
  · exact Nat.zero_lt_one

/-- The product-overlap localization model maps to the affine spectrum of the second chart. -/
def segreProductOverlapToSecondChartSpec
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec
        (CommRingCat.of
          (SegreProductChartOverlapRing R m n i a j b)) ⟶
      Spec
        (CommRingCat.of
          (SegreProductChartRing R m n a b)) :=
  Spec.map
    (CommRingCat.ofHom
      (segreProductSecondChartAlgHom R m n i a j b).toRingHom)

/-- The product-overlap localization model maps to the second standard product chart. -/
def segreProductChartOverlapToSecondChart
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec
        (CommRingCat.of
          (SegreProductChartOverlapRing R m n i a j b)) ⟶
      segreProductStandardChart R m n a b :=
  segreProductOverlapToSecondChartSpec R m n i a j b ≫
    (segreProductStandardChartIsoSpec R m n a b).inv

/-- The second product-chart presentation of the overlap induces the canonical double-chart
morphism to the Segre-image `Proj`. -/
lemma segreProductChartOverlapToSecondChart_toImageProj
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreProductChartOverlapToSecondChart R m n i a j b ≫
        segreProductStandardChartToImageProj R m n a b =
      (segreProductOverlapIsoSegreImage R m n i a j b).hom ≫
        segreImageOverlapToProj R m n i a j b := by
  rw [segreProductStandardChartToImageProj_eq]
  unfold segreProductChartOverlapToSecondChart
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  unfold segreProductOverlapToSecondChartSpec
  rw [← segreProductOverlapIsoSegreImage_hom_toSecondChart_assoc]
  rw [segreImageOverlapToSecondChart_toProj]

/-- The two chartwise Segre maps agree on the explicit product-overlap localization model. -/
lemma segreProductChartToImageProj_overlap_compatible
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreProductChartOverlapToChart R m n i a j b ≫
        segreProductStandardChartToImageProj R m n i j =
      segreProductChartOverlapToSecondChart R m n i a j b ≫
        segreProductStandardChartToImageProj R m n a b := by
  rw [segreProductChartOverlapToChart_toImageProj,
    segreProductChartOverlapToSecondChart_toImageProj]

end MvPolynomial
