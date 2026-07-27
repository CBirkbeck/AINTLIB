/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's
`CoherentCohomologyFinite.SegreProductChartTransitionGeometry`.
-/
import ModularCurves.ForMathlib.SegreOverlapSecondCompatibility

/-!
# The inverse morphism for the Segre product comparison

The standard affine cover of the Segre image is reindexed by pairs of projective
coordinates. The inverse of each local Segre chart isomorphism then gives a map
back to the product of projective spaces.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard affine cover of the Segre image, reindexed by pairs of coordinates. -/
def segreImagePairAffineOpenCover
    (R : Type u) [CommRing R] (m n : ℕ) :
    (segreImageProj R m n).AffineOpenCover := by
  letI : AddSubgroupClass (Submodule R (SegreCoordinateRing R m n))
      (SegreCoordinateRing R m n) :=
    @Submodule.addSubgroupClass R (SegreCoordinateRing R m n) _ _ inferInstance
  exact Proj.affineOpenCoverOfIrrelevantLESpan
    (segreImageGrading R m n)
    (fun q : Fin (m + 1) × Fin (n + 1) =>
      segreImageCoordinate R m n
        (segrePairIndex m n q.1 q.2))
    (m := fun _ => 1)
    (fun q : Fin (m + 1) × Fin (n + 1) =>
      segreImageCoordinate_mem_degreeOne R m n
        (segrePairIndex m n q.1 q.2))
    (fun _ => Nat.zero_lt_one)
    (by
      refine
        (segreImageIrrelevant_le_coordinateIdeal
          R m n).trans ?_
      rw [Ideal.span_le]
      rintro _ ⟨p, rfl⟩
      apply Ideal.subset_span
      refine ⟨segreIndexEquiv m n p, ?_⟩
      simp [segrePairIndex])

/-- The affine-spectrum presentation of a pair-indexed Segre-image chart. -/
def segreImagePairChartIsoSpec
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreImageStandardChart R m n
        (segrePairIndex m n i j)).toScheme ≅
      Spec
        (CommRingCat.of
          (SegreImageChartRing R m n i j)) :=
  Proj.basicOpenIsoSpec
    (segreImageGrading R m n)
    (segreImageCoordinate R m n
      (segrePairIndex m n i j))
    (segreImageCoordinate_mem_degreeOne R m n
      (segrePairIndex m n i j))
    Nat.zero_lt_one

/-- The inverse chart presentation followed by its inclusion is the homogeneous basic open. -/
lemma segreImagePairChartIsoSpec_inv_ι
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreImagePairChartIsoSpec R m n i j).inv ≫
        (segreImageStandardChart R m n
          (segrePairIndex m n i j)).ι =
      Proj.awayι
        (segreImageGrading R m n)
        (segreImageCoordinate R m n
          (segrePairIndex m n i j))
        (segreImageCoordinate_mem_degreeOne R m n
          (segrePairIndex m n i j))
        Nat.zero_lt_one := by
  rfl

/-- The inverse of a local Segre chart, followed by its product-chart inclusion. -/
def segreImagePairChartToProduct
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Spec
        (CommRingCat.of
          (SegreImageChartRing R m n i j)) ⟶
      segreProductProj R m n :=
  (segreImagePairChartIsoSpec R m n i j).inv ≫
    (segreProductStandardChartIsoImageChart
      R m n i j).inv ≫
    (segreProductStandardOpenCover R m n).f (i, j)

/-- Each local inverse followed by the global Segre map is its target-chart inclusion. -/
lemma segreImagePairChartToProduct_segreProductToImageProj_awayι
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreImagePairChartToProduct R m n i j ≫
        segreProductToImageProj R m n =
      Proj.awayι
        (segreImageGrading R m n)
        (segreImageCoordinate R m n
          (segrePairIndex m n i j))
        (segreImageCoordinate_mem_degreeOne R m n
          (segrePairIndex m n i j))
        Nat.zero_lt_one := by
  let pairInv :=
    (segreImagePairChartIsoSpec R m n i j).inv
  let chartIso :=
    segreProductStandardChartIsoImageChart R m n i j
  let chartInv := chartIso.inv
  let productChartMap :=
    (segreProductStandardOpenCover R m n).f (i, j)
  let localSegreMap :=
    segreProductStandardChartToImageProj R m n i j
  let targetInclusion :=
    (segreImageStandardChart R m n
      (segrePairIndex m n i j)).ι
  have hforward :
      productChartMap ≫ segreProductToImageProj R m n =
        localSegreMap := by
    exact
      segreProductStandardOpenCover_f_segreProductToImageProj
        R m n i j
  have hchart :
      chartIso.hom ≫ targetInclusion = localSegreMap := by
    exact
      segreProductStandardChartIsoImageChart_hom_ι
        R m n i j
  have hcancel :
      chartInv ≫ (chartIso.hom ≫ targetInclusion) =
        targetInclusion := by
    exact Iso.inv_hom_id_assoc chartIso targetInclusion
  unfold segreImagePairChartToProduct
  calc
    _ =
        pairInv ≫
          ((chartInv ≫ productChartMap) ≫
            segreProductToImageProj R m n) :=
      Category.assoc pairInv
        (chartInv ≫ productChartMap)
        (segreProductToImageProj R m n)
    _ =
        pairInv ≫
          (chartInv ≫
            (productChartMap ≫
              segreProductToImageProj R m n)) :=
      congrArg (fun q => pairInv ≫ q)
        (Category.assoc chartInv productChartMap
          (segreProductToImageProj R m n))
    _ = pairInv ≫ (chartInv ≫ localSegreMap) :=
      congrArg (fun q => pairInv ≫ (chartInv ≫ q))
        hforward
    _ =
        pairInv ≫
          (chartInv ≫ (chartIso.hom ≫ targetInclusion)) :=
      congrArg (fun q => pairInv ≫ (chartInv ≫ q))
        hchart.symm
    _ = pairInv ≫ targetInclusion :=
      congrArg (fun q => pairInv ≫ q) hcancel
    _ = _ :=
      segreImagePairChartIsoSpec_inv_ι
        R m n i j

/-- The local left-inverse identity expressed through the pair-indexed affine cover. -/
lemma segreImagePairChartToProduct_segreProductToImageProj
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreImagePairChartToProduct R m n i j ≫
        segreProductToImageProj R m n =
      (segreImagePairAffineOpenCover R m n).f (i, j) := by
  change
    segreImagePairChartToProduct R m n i j ≫
        segreProductToImageProj R m n =
      Proj.awayι
        (segreImageGrading R m n)
        (segreImageCoordinate R m n
          (segrePairIndex m n i j))
        (segreImageCoordinate_mem_degreeOne R m n
          (segrePairIndex m n i j))
        Nat.zero_lt_one
  exact
    segreImagePairChartToProduct_segreProductToImageProj_awayι
      R m n i j

/-- On the double-chart model, the inverse Segre chart equivalence followed by the
first product-chart presentation is the first target-chart restriction followed by
its inverse chart map. -/
@[reassoc]
lemma segreImageOverlapToFirstProductChart
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductOverlapIsoSegreImage
        R m n i a j b).inv ≫
        segreProductChartOverlapToChart
          R m n i a j b =
      segreImageOverlapToFirstChart R m n i a j b ≫
        (segreImagePairChartIsoSpec R m n i j).inv ≫
        (segreProductStandardChartIsoImageChart
          R m n i j).inv := by
  rw [← cancel_mono
    (segreProductStandardChartIsoImageChart
      R m n i j).hom]
  simp only [Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  dsimp only [segreProductChartOverlapToChart,
    segreProductStandardChartIsoImageChart,
    segreImagePairChartIsoSpec]
  simp only [Iso.trans_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  change
    (segreProductOverlapIsoSegreImage
          R m n i a j b).inv ≫
        segreProductChartLocalizationMap R m n i a j b ≫
        Spec.map
          (CommRingCat.ofHom
            (segreChartForwardAlgHom
              R m n i j).toRingHom) ≫
        (segreImagePairChartIsoSpec
          R m n i j).inv =
      segreImageOverlapToFirstChart R m n i a j b ≫
        (segreImagePairChartIsoSpec
          R m n i j).inv
  rw [←
    segreProductOverlapIsoSegreImage_hom_toFirstChart_assoc]
  simp

/-- The analogous identification for the second product-chart presentation of the
same double-chart model. -/
@[reassoc]
lemma segreImageOverlapToSecondProductChart
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductOverlapIsoSegreImage
        R m n i a j b).inv ≫
        segreProductChartOverlapToSecondChart
          R m n i a j b =
      segreImageOverlapToSecondChart R m n i a j b ≫
        (segreImagePairChartIsoSpec R m n a b).inv ≫
        (segreProductStandardChartIsoImageChart
          R m n a b).inv := by
  rw [← cancel_mono
    (segreProductStandardChartIsoImageChart
      R m n a b).hom]
  simp only [Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  dsimp only [segreProductChartOverlapToSecondChart,
    segreProductOverlapToSecondChartSpec,
    segreProductStandardChartIsoImageChart,
    segreImagePairChartIsoSpec]
  simp only [Iso.trans_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  change
    (segreProductOverlapIsoSegreImage
          R m n i a j b).inv ≫
        Spec.map
          (CommRingCat.ofHom
            (segreProductSecondChartAlgHom
              R m n i a j b).toRingHom) ≫
        Spec.map
          (CommRingCat.ofHom
            (segreChartForwardAlgHom
              R m n a b).toRingHom) ≫
        (segreImagePairChartIsoSpec
          R m n a b).inv =
      segreImageOverlapToSecondChart R m n i a j b ≫
        (segreImagePairChartIsoSpec
          R m n a b).inv
  rw [←
    segreProductOverlapIsoSegreImage_hom_toSecondChart_assoc]
  simp

end MvPolynomial
