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

end MvPolynomial
