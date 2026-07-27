/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's
`CoherentCohomologyFinite.SegreProductStandardCover`.
-/
import ModularCurves.ForMathlib.SegreStandardChartEquivalence
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The standard affine cover of a product of projective spaces

The product of the standard coordinate covers of two polynomial projective spaces is an
affine cover. Each product chart is the spectrum of the tensor product of the factor chart
rings and hence, by the local Segre algebra equivalence, isomorphic to the corresponding
standard chart of the Segre-image `Proj`.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard coordinate basic opens, presented by their homogeneous-localization spectra. -/
def coordinateAffineOpenCover
    (R : Type u) [CommRing R] (σ : Type) :
    (Proj (homogeneousSubmodule σ R)).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan
    (homogeneousSubmodule σ R)
    (X : σ → MvPolynomial σ R)
    (m := fun _ => 1)
    (X_mem_homogeneousSubmodule_one R)
    (fun _ => Nat.zero_lt_one)
    irrelevant_toIdeal_le_span_range_X

@[simp]
lemma coordinateAffineOpenCover_opensRange
    (R : Type u) [CommRing R] (σ : Type) (i : σ) :
    @Scheme.Hom.opensRange _ _
        ((coordinateAffineOpenCover R σ).f i)
        ((coordinateAffineOpenCover R σ).map_prop i) =
      coordinateOpen (R := R) i :=
  Proj.opensRange_awayι
    (homogeneousSubmodule σ R)
    (X i)
    (X_mem_homogeneousSubmodule_one R i)
    Nat.zero_lt_one

/-- A standard projective chart carries the canonical structural map induced by its
coefficient algebra. -/
lemma coordinateAffineOpenCover_comp_homogeneousProjπ
    (R : Type u) [CommRing R] (σ : Type) (i : σ) :
    (coordinateAffineOpenCover R σ).f i ≫
        homogeneousProjπ (R := R) (σ := σ) =
      Spec.map
        (CommRingCat.ofHom
          (algebraMap R (ProjectiveCoordinateAway R i))) := by
  change
    Proj.awayι
        (homogeneousSubmodule σ R)
        (X i)
        (X_mem_homogeneousSubmodule_one R i)
        Nat.zero_lt_one ≫
      homogeneousProjπ (R := R) (σ := σ) =
        Spec.map
          (CommRingCat.ofHom
            (algebraMap R (ProjectiveCoordinateAway R i)))
  rw [homogeneousProjπ, ← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The fibre product of two polynomial projective spaces used by the Segre comparison. -/
abbrev segreProductProj
    (R : Type u) [CommRing R] (m n : ℕ) : Scheme.{u} :=
  pullback
    (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
    (homogeneousProjπ (R := R) (σ := Fin (n + 1)))

/-- The product of the standard coordinate covers on the two projective factors. -/
abbrev segreProductStandardOpenCover
    (R : Type u) [CommRing R] (m n : ℕ) :
    (segreProductProj R m n).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight
    (coordinateAffineOpenCover R (Fin (m + 1))).openCover
    (coordinateAffineOpenCover R (Fin (n + 1))).openCover
    (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
    (homogeneousProjπ (R := R) (σ := Fin (n + 1)))

/-- A standard product chart is the spectrum of the tensor product of its two factor rings. -/
def segreProductStandardChartIsoSpec
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardOpenCover R m n).X (i, j) ≅
      Spec
        (CommRingCat.of
          (SegreProductChartRing R m n i j)) :=
  pullback.congrHom
      (coordinateAffineOpenCover_comp_homogeneousProjπ R (Fin (m + 1)) i)
      (coordinateAffineOpenCover_comp_homogeneousProjπ R (Fin (n + 1)) j) ≪≫
    pullbackSpecIso
      R
      (ProjectiveCoordinateAway R i)
      (ProjectiveCoordinateAway R j)

/-- A standard product chart is canonically isomorphic to the corresponding Segre-image chart. -/
def segreProductStandardChartIsoImageChart
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardOpenCover R m n).X (i, j) ≅
      (segreImageStandardChart R m n
        (segrePairIndex m n i j)).toScheme :=
  segreProductStandardChartIsoSpec R m n i j ≪≫
    Scheme.Spec.mapIso
      ((segreStandardChartAlgEquiv R m n i j).toRingEquiv.toCommRingCatIso).op ≪≫
    (Proj.basicOpenIsoSpec
      (segreImageGrading R m n)
      (segreImageCoordinate R m n (segrePairIndex m n i j))
      (segreImageCoordinate_mem_degreeOne R m n (segrePairIndex m n i j))
      Nat.zero_lt_one).symm

/-- The product-chart isomorphism followed by the open inclusion is its chartwise Segre map. -/
def segreProductStandardChartToImageProj
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardOpenCover R m n).X (i, j) ⟶
      segreImageProj R m n :=
  (segreProductStandardChartIsoImageChart R m n i j).hom ≫
    (segreImageStandardChart R m n (segrePairIndex m n i j)).ι

@[reassoc]
lemma segreProductStandardChartIsoImageChart_hom_ι
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardChartIsoImageChart R m n i j).hom ≫
        (segreImageStandardChart R m n
          (segrePairIndex m n i j)).ι =
      segreProductStandardChartToImageProj R m n i j :=
  rfl

end MvPolynomial
