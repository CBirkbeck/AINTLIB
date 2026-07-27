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

/-- The canonical affine-spectrum presentation of the overlap of two pair-indexed
standard charts of the Segre image. -/
def segreImagePairOverlapIso
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    pullback
        (Proj.awayι
          (segreImageGrading R m n)
          (segreImageCoordinate R m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne R m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one)
        (Proj.awayι
          (segreImageGrading R m n)
          (segreImageCoordinate R m n
            (segrePairIndex m n a b))
          (segreImageCoordinate_mem_degreeOne R m n
            (segrePairIndex m n a b))
          Nat.zero_lt_one) ≅
      Spec
        (CommRingCat.of
          (SegreImageChartOverlapRing
            R m n i a j b)) :=
  Proj.pullbackAwayιIso
    (segreImageGrading R m n)
    (segreImageCoordinate_mem_degreeOne R m n
      (segrePairIndex m n i j))
    Nat.zero_lt_one
    (segreImageCoordinate_mem_degreeOne R m n
      (segrePairIndex m n a b))
    Nat.zero_lt_one
    rfl

/-- The first pullback projection of a target-chart overlap is the canonical
first-chart localization map. -/
@[reassoc]
lemma segreImagePairOverlapIso_inv_fst
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreImagePairOverlapIso R m n i a j b).inv ≫
        pullback.fst
          (Proj.awayι
            (segreImageGrading R m n)
            (segreImageCoordinate R m n
              (segrePairIndex m n i j))
            (segreImageCoordinate_mem_degreeOne R m n
              (segrePairIndex m n i j))
            Nat.zero_lt_one)
          (Proj.awayι
            (segreImageGrading R m n)
            (segreImageCoordinate R m n
              (segrePairIndex m n a b))
            (segreImageCoordinate_mem_degreeOne R m n
              (segrePairIndex m n a b))
            Nat.zero_lt_one) =
      segreImageOverlapToFirstChart R m n i a j b := by
  exact
    Proj.pullbackAwayιIso_inv_fst
      (segreImageGrading R m n)
      (segreImageCoordinate_mem_degreeOne R m n
        (segrePairIndex m n i j))
      Nat.zero_lt_one
      (segreImageCoordinate_mem_degreeOne R m n
        (segrePairIndex m n a b))
      Nat.zero_lt_one
      rfl

/-- The second pullback projection of a target-chart overlap is the canonical
second-chart localization map. -/
@[reassoc]
lemma segreImagePairOverlapIso_inv_snd
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreImagePairOverlapIso R m n i a j b).inv ≫
        pullback.snd
          (Proj.awayι
            (segreImageGrading R m n)
            (segreImageCoordinate R m n
              (segrePairIndex m n i j))
            (segreImageCoordinate_mem_degreeOne R m n
              (segrePairIndex m n i j))
            Nat.zero_lt_one)
          (Proj.awayι
            (segreImageGrading R m n)
            (segreImageCoordinate R m n
              (segrePairIndex m n a b))
            (segreImageCoordinate_mem_degreeOne R m n
              (segrePairIndex m n a b))
            Nat.zero_lt_one) =
      segreImageOverlapToSecondChart R m n i a j b := by
  exact
    Proj.pullbackAwayιIso_inv_snd
      (segreImageGrading R m n)
      (segreImageCoordinate_mem_degreeOne R m n
        (segrePairIndex m n i j))
      Nat.zero_lt_one
      (segreImageCoordinate_mem_degreeOne R m n
        (segrePairIndex m n a b))
      Nat.zero_lt_one
      rfl

private lemma segreImagePairChartToProduct_eq_chartMap
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreImagePairChartToProduct R m n i j =
      (segreImagePairChartIsoSpec R m n i j).inv ≫
        (segreProductStandardChartIsoImageChart
          R m n i j).inv ≫
        segreProductStandardChartMap R m n i j := by
  simp only [segreImagePairChartToProduct,
    segreProductStandardOpenCover_f]

/-- The inverse chart maps agree on every pairwise overlap of the explicit
homogeneous basic-open charts. -/
lemma segreImagePairChartToProduct_compatible_awayι
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    pullback.fst
          (Proj.awayι
            (segreImageGrading R m n)
            (segreImageCoordinate R m n
              (segrePairIndex m n i j))
            (segreImageCoordinate_mem_degreeOne R m n
              (segrePairIndex m n i j))
            Nat.zero_lt_one)
          (Proj.awayι
            (segreImageGrading R m n)
            (segreImageCoordinate R m n
              (segrePairIndex m n a b))
            (segreImageCoordinate_mem_degreeOne R m n
              (segrePairIndex m n a b))
            Nat.zero_lt_one) ≫
        segreImagePairChartToProduct R m n i j =
      pullback.snd
          (Proj.awayι
            (segreImageGrading R m n)
            (segreImageCoordinate R m n
              (segrePairIndex m n i j))
            (segreImageCoordinate_mem_degreeOne R m n
              (segrePairIndex m n i j))
            Nat.zero_lt_one)
          (Proj.awayι
            (segreImageGrading R m n)
            (segreImageCoordinate R m n
              (segrePairIndex m n a b))
            (segreImageCoordinate_mem_degreeOne R m n
              (segrePairIndex m n a b))
            Nat.zero_lt_one) ≫
        segreImagePairChartToProduct R m n a b := by
  rw [← cancel_epi
    (segreImagePairOverlapIso
      R m n i a j b).inv]
  rw [segreImagePairOverlapIso_inv_fst_assoc,
    segreImagePairOverlapIso_inv_snd_assoc]
  rw [segreImagePairChartToProduct_eq_chartMap,
    segreImagePairChartToProduct_eq_chartMap]
  rw [← segreImageOverlapToFirstProductChart_assoc,
    ← segreImageOverlapToSecondProductChart_assoc]
  have htransition :
      segreProductChartOverlapToChart R m n i a j b ≫
          segreProductStandardChartMap R m n i j =
        segreProductChartOverlapToSecondChart R m n i a j b ≫
          segreProductStandardChartMap R m n a b := by
    simpa only [segreProductStandardOpenCover_f] using
      segreProductChartOverlap_transition
        R m n i a j b
  exact
    congrArg
      (fun z =>
        (segreProductOverlapIsoSegreImage
          R m n i a j b).inv ≫ z)
      htransition

/-- The inverse chart maps satisfy the cocycle condition on the actual
pair-indexed affine cover of the Segre image. -/
lemma segreImagePairChartToProduct_compatible
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    pullback.fst
          ((segreImagePairAffineOpenCover
            R m n).openCover.f (i, j))
          ((segreImagePairAffineOpenCover
            R m n).openCover.f (a, b)) ≫
        segreImagePairChartToProduct R m n i j =
      pullback.snd
          ((segreImagePairAffineOpenCover
            R m n).openCover.f (i, j))
          ((segreImagePairAffineOpenCover
            R m n).openCover.f (a, b)) ≫
        segreImagePairChartToProduct R m n a b := by
  change
    pullback.fst
          (Proj.awayι
            (segreImageGrading R m n)
            (segreImageCoordinate R m n
              (segrePairIndex m n i j))
            (segreImageCoordinate_mem_degreeOne R m n
              (segrePairIndex m n i j))
            Nat.zero_lt_one)
          (Proj.awayι
            (segreImageGrading R m n)
            (segreImageCoordinate R m n
              (segrePairIndex m n a b))
            (segreImageCoordinate_mem_degreeOne R m n
              (segrePairIndex m n a b))
            Nat.zero_lt_one) ≫
        segreImagePairChartToProduct R m n i j =
      pullback.snd
          (Proj.awayι
            (segreImageGrading R m n)
            (segreImageCoordinate R m n
              (segrePairIndex m n i j))
            (segreImageCoordinate_mem_degreeOne R m n
              (segrePairIndex m n i j))
            Nat.zero_lt_one)
          (Proj.awayι
            (segreImageGrading R m n)
            (segreImageCoordinate R m n
              (segrePairIndex m n a b))
            (segreImageCoordinate_mem_degreeOne R m n
              (segrePairIndex m n a b))
            Nat.zero_lt_one) ≫
        segreImagePairChartToProduct R m n a b
  exact
    segreImagePairChartToProduct_compatible_awayι
      R m n i a j b

/-- The global inverse to the glued Segre morphism, obtained by gluing the inverse
affine-chart maps on the pair-indexed target cover. -/
def segreImageProjToProduct
    (R : Type u) [CommRing R] (m n : ℕ) :
    segreImageProj R m n ⟶ segreProductProj R m n :=
  (segreImagePairAffineOpenCover R m n).openCover.glueMorphisms
    (fun q =>
      segreImagePairChartToProduct
        R m n q.1 q.2)
    (fun q r =>
      segreImagePairChartToProduct_compatible
        R m n q.1 r.1 q.2 r.2)

/-- The glued inverse restricts to the prescribed inverse morphism on every
pair-indexed target chart. -/
@[reassoc]
lemma segreImagePairOpenCover_f_segreImageProjToProduct
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreImagePairAffineOpenCover
          R m n).openCover.f (i, j) ≫
        segreImageProjToProduct R m n =
      segreImagePairChartToProduct R m n i j := by
  apply Scheme.Cover.ι_glueMorphisms

/-- The isomorphism from a standard product chart to the corresponding
pair-indexed affine-spectrum chart of the Segre image. -/
def segreProductStandardChartIsoPairChart
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChart R m n i j ≅
      Spec
        (CommRingCat.of
          (SegreImageChartRing R m n i j)) :=
  segreProductStandardChartIsoImageChart R m n i j ≪≫
    segreImagePairChartIsoSpec R m n i j

/-- The product-to-target chart isomorphism followed by the homogeneous
basic-open immersion is the prescribed local Segre morphism. -/
@[reassoc]
lemma segreProductStandardChartIsoPairChart_hom_awayι
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardChartIsoPairChart
          R m n i j).hom ≫
        Proj.awayι
          (segreImageGrading R m n)
          (segreImageCoordinate R m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne R m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one =
      segreProductStandardChartToImageProj R m n i j := by
  rw [← segreImagePairChartIsoSpec_inv_ι]
  simp only [segreProductStandardChartIsoPairChart,
    Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc,
    segreProductStandardChartIsoImageChart_hom_ι]

/-- The inverse local chart map is the inverse product-to-target chart
isomorphism followed by the canonical source-chart inclusion. -/
lemma segreImagePairChartToProduct_eq
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreImagePairChartToProduct R m n i j =
      (segreProductStandardChartIsoPairChart
          R m n i j).inv ≫
        segreProductStandardChartMap R m n i j := by
  rw [segreImagePairChartToProduct_eq_chartMap]
  rfl

/-- On a homogeneous target chart, the global inverse restricts to the explicit
inverse chart map. -/
@[reassoc]
lemma segreImagePairAwayι_segreImageProjToProduct
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Proj.awayι
          (segreImageGrading R m n)
          (segreImageCoordinate R m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne R m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one ≫
        segreImageProjToProduct R m n =
      segreImagePairChartToProduct R m n i j := by
  change
    (segreImagePairAffineOpenCover
          R m n).openCover.f (i, j) ≫
        segreImageProjToProduct R m n =
      segreImagePairChartToProduct R m n i j
  exact
    segreImagePairOpenCover_f_segreImageProjToProduct
      R m n i j

/-- The inverse-forward composite is the identity after restriction to each
pair-indexed target chart. -/
lemma segreImagePairAwayι_inverse_right
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Proj.awayι
          (segreImageGrading R m n)
          (segreImageCoordinate R m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne R m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one ≫
        (segreImageProjToProduct R m n ≫
          segreProductToImageProj R m n) =
      Proj.awayι
          (segreImageGrading R m n)
          (segreImageCoordinate R m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne R m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one ≫
        𝟙 (segreImageProj R m n) := by
  calc
    _ =
        (Proj.awayι
            (segreImageGrading R m n)
            (segreImageCoordinate R m n
              (segrePairIndex m n i j))
            (segreImageCoordinate_mem_degreeOne R m n
              (segrePairIndex m n i j))
            Nat.zero_lt_one ≫
          segreImageProjToProduct R m n) ≫
            segreProductToImageProj R m n :=
      (Category.assoc _ _ _).symm
    _ =
        segreImagePairChartToProduct R m n i j ≫
          segreProductToImageProj R m n :=
      congrArg
        (fun q => q ≫ segreProductToImageProj R m n)
        (segreImagePairAwayι_segreImageProjToProduct
          R m n i j)
    _ =
        Proj.awayι
          (segreImageGrading R m n)
          (segreImageCoordinate R m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne R m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one :=
      segreImagePairChartToProduct_segreProductToImageProj_awayι
        R m n i j
    _ = _ := (Category.comp_id _).symm

/-- The forward-inverse composite is the identity after restriction to each
standard product chart. -/
lemma segreProductStandardChart_inverse_left
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChartMap R m n i j ≫
        (segreProductToImageProj R m n ≫
          segreImageProjToProduct R m n) =
      segreProductStandardChartMap R m n i j ≫
        𝟙 (segreProductProj R m n) := by
  have hforward :
      segreProductStandardChartMap R m n i j ≫
          segreProductToImageProj R m n =
        segreProductStandardChartToImageProj R m n i j := by
    change
      (segreProductStandardOpenCover R m n).f (i, j) ≫
          segreProductToImageProj R m n =
        segreProductStandardChartToImageProj R m n i j
    exact
      segreProductStandardOpenCover_f_segreProductToImageProj
        R m n i j
  calc
    _ =
        (segreProductStandardChartMap R m n i j ≫
          segreProductToImageProj R m n) ≫
            segreImageProjToProduct R m n :=
      (Category.assoc _ _ _).symm
    _ =
        segreProductStandardChartToImageProj R m n i j ≫
          segreImageProjToProduct R m n :=
      congrArg
        (fun q => q ≫ segreImageProjToProduct R m n)
        hforward
    _ =
        ((segreProductStandardChartIsoPairChart
              R m n i j).hom ≫
            Proj.awayι
              (segreImageGrading R m n)
              (segreImageCoordinate R m n
                (segrePairIndex m n i j))
              (segreImageCoordinate_mem_degreeOne R m n
                (segrePairIndex m n i j))
              Nat.zero_lt_one) ≫
          segreImageProjToProduct R m n := by
      rw [segreProductStandardChartIsoPairChart_hom_awayι]
    _ =
        (segreProductStandardChartIsoPairChart
              R m n i j).hom ≫
          (Proj.awayι
              (segreImageGrading R m n)
              (segreImageCoordinate R m n
                (segrePairIndex m n i j))
              (segreImageCoordinate_mem_degreeOne R m n
                (segrePairIndex m n i j))
              Nat.zero_lt_one ≫
            segreImageProjToProduct R m n) :=
      Category.assoc _ _ _
    _ =
        (segreProductStandardChartIsoPairChart
              R m n i j).hom ≫
          segreImagePairChartToProduct R m n i j :=
      congrArg
        (fun q =>
          (segreProductStandardChartIsoPairChart
            R m n i j).hom ≫ q)
        (segreImagePairAwayι_segreImageProjToProduct
          R m n i j)
    _ =
        (segreProductStandardChartIsoPairChart
              R m n i j).hom ≫
          ((segreProductStandardChartIsoPairChart
              R m n i j).inv ≫
            segreProductStandardChartMap R m n i j) :=
      congrArg
        (fun q =>
          (segreProductStandardChartIsoPairChart
            R m n i j).hom ≫ q)
        (segreImagePairChartToProduct_eq R m n i j)
    _ = segreProductStandardChartMap R m n i j :=
      Iso.hom_inv_id_assoc
        (segreProductStandardChartIsoPairChart
          R m n i j)
        (segreProductStandardChartMap R m n i j)
    _ = _ := (Category.comp_id _).symm

/-- The glued inverse is a right inverse to the global Segre morphism. -/
lemma segreImageProjToProduct_segreProductToImageProj
    (R : Type u) [CommRing R] (m n : ℕ) :
    segreImageProjToProduct R m n ≫
        segreProductToImageProj R m n =
      𝟙 (segreImageProj R m n) := by
  apply
    (segreImagePairAffineOpenCover
      R m n).openCover.hom_ext
  intro q
  exact
    segreImagePairAwayι_inverse_right
      R m n q.1 q.2

/-- The global Segre morphism is a right inverse to the glued inverse. -/
lemma segreProductToImageProj_segreImageProjToProduct
    (R : Type u) [CommRing R] (m n : ℕ) :
    segreProductToImageProj R m n ≫
        segreImageProjToProduct R m n =
      𝟙 (segreProductProj R m n) := by
  apply
    (segreProductStandardOpenCover
      R m n).hom_ext
  intro q
  change
    segreProductStandardChartMap R m n q.1 q.2 ≫
        (segreProductToImageProj R m n ≫
          segreImageProjToProduct R m n) =
      segreProductStandardChartMap R m n q.1 q.2 ≫
        𝟙 (segreProductProj R m n)
  exact
    segreProductStandardChart_inverse_left
      R m n q.1 q.2

/-- The global Segre morphism is an isomorphism, with inverse given by the
glued inverse chart maps. -/
instance isIso_segreProductToImageProj
    (R : Type u) [CommRing R] (m n : ℕ) :
    IsIso (segreProductToImageProj R m n) :=
  IsIso.mk'
    ⟨segreImageProjToProduct R m n,
      segreImageProjToProduct_segreProductToImageProj
        R m n,
      segreProductToImageProj_segreImageProjToProduct
        R m n⟩

end MvPolynomial
