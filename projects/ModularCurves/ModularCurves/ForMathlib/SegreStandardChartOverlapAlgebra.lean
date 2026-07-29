/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's
`CoherentCohomologyFinite.SegreStandardChartOverlapAlgebra`.
-/
import ModularCurves.ForMathlib.SegreProductStandardCover

/-!
# Algebra on overlaps of standard Segre charts

The overlap with a second standard chart is localization at the corresponding coordinate
ratio. The standard Segre chart equivalence sends that ratio to the product of the two
projective transition ratios, so it extends canonically to the overlap rings.
-/

open HomogeneousLocalization
open scoped TensorProduct

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The transition function on a product standard chart. -/
def segreProductChartTransition
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    SegreProductChartRing R m n i j :=
  projectiveCoordinateRatio R i a ⊗ₜ[R]
    projectiveCoordinateRatio R j b

/-- The ring of the intersection of two standard charts of the Segre-image `Proj`. -/
abbrev SegreImageChartOverlapRing
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :=
  Away
    (segreImageGrading R m n)
    (segreImageCoordinate R m n (segrePairIndex m n i j) *
      segreImageCoordinate R m n (segrePairIndex m n a b))

/-- The product-chart overlap, presented as localization at its transition function. -/
abbrev SegreProductChartOverlapRing
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :=
  Localization.Away
    (segreProductChartTransition R m n i a j b)

@[simp]
lemma segreChartForwardAlgHom_transition
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreChartForwardAlgHom R m n i j
        (segreImageChartRatio R m n i a j b) =
      segreProductChartTransition R m n i a j b :=
  segreChartForwardAlgHom_ratio R m n i a j b

lemma segreImageChartRatio_eq_isLocalizationElem
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreImageChartRatio R m n i a j b =
      Away.isLocalizationElem
        (segreImageCoordinate_mem_degreeOne R m n
          (segrePairIndex m n i j))
        (segreImageCoordinate_mem_degreeOne R m n
          (segrePairIndex m n a b)) := by
  change
    Away.mk _ _ 1
        (segreImageCoordinate R m n (segrePairIndex m n a b)) _ =
      Away.mk _ _ 1
        (segreImageCoordinate R m n (segrePairIndex m n a b) ^ 1) _
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, pow_one]

/-- The standard-chart Segre equivalence localized to an overlap with a second chart. -/
def segreStandardChartOverlapRingEquiv
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    SegreImageChartOverlapRing R m n i a j b ≃+*
      SegreProductChartOverlapRing R m n i a j b := by
  letI :=
    (HomogeneousLocalization.awayMap
      (segreImageGrading R m n)
      (segreImageCoordinate_mem_degreeOne R m n
        (segrePairIndex m n a b))
      (rfl :
        segreImageCoordinate R m n (segrePairIndex m n i j) *
            segreImageCoordinate R m n (segrePairIndex m n a b) =
          segreImageCoordinate R m n (segrePairIndex m n i j) *
            segreImageCoordinate R m n (segrePairIndex m n a b))).toAlgebra
  letI :
      IsLocalization.Away
        (segreImageChartRatio R m n i a j b)
        (SegreImageChartOverlapRing R m n i a j b) := by
    rw [segreImageChartRatio_eq_isLocalizationElem]
    exact
      Away.isLocalization_mul
        (segreImageCoordinate_mem_degreeOne R m n
          (segrePairIndex m n i j))
        (segreImageCoordinate_mem_degreeOne R m n
          (segrePairIndex m n a b))
        rfl Nat.one_ne_zero
  exact
    IsLocalization.ringEquivOfRingEquiv
      (M := Submonoid.powers
        (segreImageChartRatio R m n i a j b))
      (T := Submonoid.powers
        (segreProductChartTransition R m n i a j b))
      (SegreImageChartOverlapRing R m n i a j b)
      (SegreProductChartOverlapRing R m n i a j b)
      (segreStandardChartAlgEquiv R m n i j).toRingEquiv
      (by
        rw [Submonoid.map_powers]
        exact
          congrArg
            (fun x : SegreProductChartRing R m n i j =>
              Submonoid.powers x)
            (segreChartForwardAlgHom_transition R m n i a j b))

end MvPolynomial
