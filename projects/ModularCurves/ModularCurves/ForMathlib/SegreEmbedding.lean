/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's `CoherentCohomologyFinite.ProjectiveFactorization`
and `CoherentCohomologyFinite.SegreProductChartTransitionGeometry`.
-/
import ModularCurves.ForMathlib.SegreGlobalInverse
import ModularCurves.ForMathlib.ProjToSpecZero

/-!
# The binary Segre embedding over an affine base

The product of two polynomial projective spaces is identified with the `Proj`
of the Segre-image coordinate ring. Composing this isomorphism with the closed
immersion of the Segre image gives a closed embedding into one polynomial
projective space, compatible with the structural maps to the coefficient ring.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The structural morphism from the product of two polynomial projective spaces. -/
def segreProductπ
    (R : Type u) [CommRing R] (m n : ℕ) :
    segreProductProj R m n ⟶ Spec (.of R) :=
  pullback.fst
      (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
      (homogeneousProjπ (R := R) (σ := Fin (n + 1))) ≫
    homogeneousProjπ (R := R) (σ := Fin (m + 1))

/-- The structural morphism from the `Proj` of the Segre-image coordinate ring. -/
def segreImageProjπ
    (R : Type u) [CommRing R] (m n : ℕ) :
    segreImageProj R m n ⟶ Spec (.of R) :=
  Proj.toSpecZero (segreImageGrading R m n) ≫
    Spec.map
      (CommRingCat.ofHom
        (algebraMap R (segreImageGrading R m n 0)))

private lemma segreProductStandardChartIsoSpecInvFst_comp_homogeneousProjπ
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChartIsoSpecInvFst R m n i j ≫
          coordinateChartMap R (Fin (m + 1)) i ≫
          homogeneousProjπ (R := R) (σ := Fin (m + 1)) =
      Spec.map
        (CommRingCat.ofHom
          (algebraMap R (SegreProductChartRing R m n i j))) := by
  rw [segreProductStandardChartIsoSpec_inv_chartFst,
    coordinateAffineOpenCover_comp_homogeneousProjπ,
    ← Spec.map_comp]
  congr 1

private lemma segreProductStandardChartIsoSpec_inv_comp_segreProductπ
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardChartIsoSpec R m n i j).inv ≫
        segreProductStandardChartMap R m n i j ≫
        segreProductπ R m n =
      Spec.map
        (CommRingCat.ofHom
          (algebraMap R (SegreProductChartRing R m n i j))) := by
  unfold segreProductπ
  calc
    _ =
        (segreProductStandardChartIsoSpec R m n i j).inv ≫
          (segreProductStandardChartMap R m n i j ≫
            pullback.fst
              (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
              (homogeneousProjπ (R := R) (σ := Fin (n + 1)))) ≫
          homogeneousProjπ (R := R) (σ := Fin (m + 1)) := by
      simp only [Category.assoc]
    _ =
        (segreProductStandardChartIsoSpec R m n i j).inv ≫
          (segreProductStandardChartFst R m n i j ≫
            coordinateChartMap R (Fin (m + 1)) i) ≫
          homogeneousProjπ (R := R) (σ := Fin (m + 1)) := by
      rw [segreProductStandardChartMap_fst]
    _ =
        segreProductStandardChartIsoSpecInvFst R m n i j ≫
          coordinateChartMap R (Fin (m + 1)) i ≫
          homogeneousProjπ (R := R) (σ := Fin (m + 1)) := by
      simp only [segreProductStandardChartIsoSpecInvFst,
        Category.assoc]
    _ = _ :=
      segreProductStandardChartIsoSpecInvFst_comp_homogeneousProjπ
        R m n i j

/-- The affine-spectrum presentation of a product chart identifies its structural
map with the coefficient-algebra map. -/
lemma segreProductStandardChartIsoSpec_hom_segreProductπ
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardChartIsoSpec R m n i j).hom ≫
        Spec.map
          (CommRingCat.ofHom
            (algebraMap R (SegreProductChartRing R m n i j))) =
      (segreProductStandardOpenCover R m n).f (i, j) ≫
        segreProductπ R m n := by
  change
    (segreProductStandardChartIsoSpec R m n i j).hom ≫
          Spec.map
            (CommRingCat.ofHom
              (algebraMap R (SegreProductChartRing R m n i j))) =
      segreProductStandardChartMap R m n i j ≫
        segreProductπ R m n
  apply (cancel_epi (segreProductStandardChartIsoSpec R m n i j).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  exact
    (segreProductStandardChartIsoSpec_inv_comp_segreProductπ
      R m n i j).symm

/-- A standard Segre-image chart carries the coefficient-algebra structural map. -/
lemma segreImageStandardChart_ι_comp_segreImageProjπ
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Proj.awayι
          (segreImageGrading R m n)
          (segreImageCoordinate R m n (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne R m n (segrePairIndex m n i j))
          Nat.zero_lt_one ≫
        segreImageProjπ R m n =
      Spec.map
        (CommRingCat.ofHom
          (algebraMap R (SegreImageChartRing R m n i j))) := by
  unfold segreImageProjπ
  rw [← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp]
  rfl

/-- Every standard product-chart Segre morphism respects the structural maps. -/
lemma segreProductStandardChartToImageProj_comp_segreImageProjπ
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChartToImageProj R m n i j ≫
        segreImageProjπ R m n =
      (segreProductStandardOpenCover R m n).f (i, j) ≫
        segreProductπ R m n := by
  have hCoefficients :
      CommRingCat.ofHom
            (algebraMap R (SegreImageChartRing R m n i j)) ≫
          CommRingCat.ofHom
            (segreChartForwardAlgHom R m n i j).toRingHom =
        CommRingCat.ofHom
          (algebraMap R (SegreProductChartRing R m n i j)) := by
    ext r
    exact (segreChartForwardAlgHom R m n i j).commutes r
  rw [segreProductStandardChartToImageProj_eq]
  simp only [Category.assoc]
  rw [segreImageStandardChart_ι_comp_segreImageProjπ,
    ← Spec.map_comp, hCoefficients]
  exact
    segreProductStandardChartIsoSpec_hom_segreProductπ
      R m n i j

/-- The global Segre isomorphism respects the structural maps to the base. -/
lemma segreProductToImageProj_comp_segreImageProjπ
    (R : Type u) [CommRing R] (m n : ℕ) :
    segreProductToImageProj R m n ≫
        segreImageProjπ R m n =
      segreProductπ R m n := by
  apply (segreProductStandardOpenCover R m n).hom_ext
  rintro ⟨i, j⟩
  change
    segreProductStandardChartMap R m n i j ≫
          (segreProductToImageProj R m n ≫
            segreImageProjπ R m n) =
      segreProductStandardChartMap R m n i j ≫
        segreProductπ R m n
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
  have hlocal :
      segreProductStandardChartToImageProj R m n i j ≫
          segreImageProjπ R m n =
        segreProductStandardChartMap R m n i j ≫
          segreProductπ R m n := by
    change
      segreProductStandardChartToImageProj R m n i j ≫
          segreImageProjπ R m n =
        (segreProductStandardOpenCover R m n).f (i, j) ≫
          segreProductπ R m n
    exact
      segreProductStandardChartToImageProj_comp_segreImageProjπ
        R m n i j
  calc
    _ =
        (segreProductStandardChartMap R m n i j ≫
            segreProductToImageProj R m n) ≫
          segreImageProjπ R m n :=
      (Category.assoc _ _ _).symm
    _ =
        segreProductStandardChartToImageProj R m n i j ≫
          segreImageProjπ R m n :=
      congrArg (fun q => q ≫ segreImageProjπ R m n) hforward
    _ = _ := hlocal

private lemma segreImageGradedHom_zero_algebraMap
    (R : Type u) [CommRing R] (m n : ℕ) (r : R) :
    ModularCurves.gradedRingHomZero
          (segreImageGradedHom R m n)
          (algebraMap R
            (homogeneousSubmodule
              (Fin (segreDimension m n + 1)) R 0) r) =
      algebraMap R (segreImageGrading R m n 0) r := by
  apply Subtype.ext
  exact (segreRangeCoordinateHom R m n).commutes r

private lemma segreImageGradedHom_zero_comp_algebraMap
    (R : Type u) [CommRing R] (m n : ℕ) :
    CommRingCat.ofHom
          (algebraMap R
            (homogeneousSubmodule
              (Fin (segreDimension m n + 1)) R 0)) ≫
        CommRingCat.ofHom
          (ModularCurves.gradedRingHomZero
            (segreImageGradedHom R m n)) =
      CommRingCat.ofHom
        (algebraMap R (segreImageGrading R m n 0)) := by
  ext r
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply, CommRingCat.hom_ofHom] using
    congrArg Subtype.val
      (congrArg Subtype.val
        (segreImageGradedHom_zero_algebraMap R m n r))

/-- The closed Segre-image inclusion respects the structural maps to the base. -/
lemma segreImageProjι_comp_homogeneousProjπ
    (R : Type u) [CommRing R] (m n : ℕ) :
    segreImageProjι R m n ≫
        homogeneousProjπ
          (R := R)
          (σ := Fin (segreDimension m n + 1)) =
      segreImageProjπ R m n := by
  unfold segreImageProjι homogeneousProjπ segreImageProjπ
  rw [← Category.assoc,
    ModularCurves.map_comp_toSpecZero]
  rw [Category.assoc, ← Spec.map_comp]
  rw [segreImageGradedHom_zero_comp_algebraMap]

/-- The binary Segre embedding into one polynomial projective space. -/
def segreProductEmbedding
    (R : Type u) [CommRing R] (m n : ℕ) :
    segreProductProj R m n ⟶
      Proj
        (homogeneousSubmodule
          (Fin (segreDimension m n + 1)) R) :=
  segreProductToImageProj R m n ≫
    segreImageProjι R m n

/-- The binary Segre embedding is a closed immersion. -/
lemma segreProductEmbedding_isClosedImmersion
    (R : Type u) [CommRing R] (m n : ℕ) :
    IsClosedImmersion (segreProductEmbedding R m n) := by
  haveI :
      IsClosedImmersion
        (segreProductToImageProj R m n) := by
    infer_instance
  haveI :
      IsClosedImmersion (segreImageProjι R m n) :=
    segreImageProjι_isClosedImmersion R m n
  unfold segreProductEmbedding
  infer_instance

/-- The binary Segre embedding is a morphism over the coefficient spectrum. -/
lemma segreProductEmbedding_comp_homogeneousProjπ
    (R : Type u) [CommRing R] (m n : ℕ) :
    segreProductEmbedding R m n ≫
        homogeneousProjπ
          (R := R)
          (σ := Fin (segreDimension m n + 1)) =
      segreProductπ R m n := by
  unfold segreProductEmbedding
  rw [Category.assoc,
    segreImageProjι_comp_homogeneousProjπ,
    segreProductToImageProj_comp_segreImageProjπ]

end MvPolynomial
