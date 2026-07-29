/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from the first-chart `Proj`-factorization block of Clawristotle's
`CoherentCohomologyFinite.SegreStandardOverlapCompatibility`.
-/
import ModularCurves.ForMathlib.SegreOverlapFirstCompatibility

/-!
# First-chart factorization through a double Segre-image chart

The first local Segre morphism on a source overlap factors through the canonical double
homogeneous-localization chart of the Segre-image `Proj`.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The double Segre-image chart maps into the Segre-image `Proj`. -/
def segreImageOverlapToProj
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec (CommRingCat.of
      (SegreImageChartOverlapRing R m n i a j b)) ⟶
        segreImageProj R m n :=
  Proj.awayι
    (segreImageGrading R m n)
    (segreImageCoordinate R m n (segrePairIndex m n i j) *
      segreImageCoordinate R m n (segrePairIndex m n a b))
    (SetLike.mul_mem_graded
      (segreImageCoordinate_mem_degreeOne R m n
        (segrePairIndex m n i j))
      (segreImageCoordinate_mem_degreeOne R m n
        (segrePairIndex m n a b)))
    (by omega)

/-- The double-chart inclusion factors through its first standard chart by the canonical
homogeneous away map. -/
@[reassoc]
lemma segreImageOverlapToFirstChart_toProj
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreImageOverlapToFirstChart R m n i a j b ≫
        Proj.awayι
          (segreImageGrading R m n)
          (segreImageCoordinate R m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne R m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one =
      segreImageOverlapToProj R m n i a j b :=
  Proj.SpecMap_awayMap_awayι
    (segreImageGrading R m n)
    (segreImageCoordinate_mem_degreeOne R m n
      (segrePairIndex m n i j))
    Nat.zero_lt_one
    (segreImageCoordinate_mem_degreeOne R m n
      (segrePairIndex m n a b))
    rfl

/-- The standard product-chart map to the Segre-image `Proj`, written through its affine
spectrum presentation. -/
lemma segreProductStandardChartToImageProj_eq
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChartToImageProj R m n i j =
      (segreProductStandardChartIsoSpec R m n i j).hom ≫
        Spec.map
          (CommRingCat.ofHom
            (segreChartForwardAlgHom R m n i j).toRingHom) ≫
        Proj.awayι
          (segreImageGrading R m n)
          (segreImageCoordinate R m n (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne R m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one := by
  unfold segreProductStandardChartToImageProj
  unfold segreProductStandardChartIsoImageChart
  unfold segreImageStandardChart
  simp only [Iso.trans_hom, Category.assoc]
  rfl

/-- The chartwise Segre morphism, restricted to the localization model of a pairwise overlap,
is the double-chart morphism. -/
@[reassoc]
lemma segreProductChartOverlapToChart_toImageProj
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreProductChartOverlapToChart R m n i a j b ≫
        segreProductStandardChartToImageProj R m n i j =
      (segreProductOverlapIsoSegreImage R m n i a j b).hom ≫
        segreImageOverlapToProj R m n i a j b := by
  rw [segreProductStandardChartToImageProj_eq]
  unfold segreProductChartOverlapToChart
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← segreImageOverlapToFirstChart_toProj]
  rw [segreProductOverlapIsoSegreImage_hom_toFirstChart_assoc]

/-- The first restriction of the chartwise Segre morphisms on an actual pullback overlap has
the explicit double-chart factorization. -/
lemma pullback_fst_segreProductStandardChartToImageProj
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    pullback.fst
        (segreProductStandardChartMap R m n i j)
        (segreProductStandardChartMap R m n a b) ≫
        segreProductStandardChartToImageProj R m n i j =
      (segreProductStandardOverlapIso R m n i a j b).hom ≫
        (segreProductOverlapIsoSegreImage R m n i a j b).hom ≫
        segreImageOverlapToProj R m n i a j b := by
  rw [← segreProductStandardOverlapIso_hom_toChart_assoc,
    segreProductChartOverlapToChart_toImageProj]

end MvPolynomial
