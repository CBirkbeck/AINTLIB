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

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace.Opens

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The open immersion of a standard coordinate chart into polynomial `Proj`. -/
abbrev coordinateChartMap
    (R : Type u) [CommRing R] (σ : Type) (i : σ) :
    Spec (CommRingCat.of (ProjectiveCoordinateAway R i)) ⟶
      Proj (homogeneousSubmodule σ R) :=
  Proj.awayι
    (homogeneousSubmodule σ R)
    (X i)
    (X_mem_homogeneousSubmodule_one R i)
    Nat.zero_lt_one

/-- The standard coordinate basic opens, presented by their homogeneous-localization spectra. -/
abbrev coordinateAffineOpenCover
    (R : Type u) [CommRing R] (σ : Type) :
    (Proj (homogeneousSubmodule σ R)).AffineOpenCover where
  I₀ := σ
  X i := .of (ProjectiveCoordinateAway R i)
  f i := coordinateChartMap R σ i
  idx x :=
    (mem_iSup.mp
      ((Proj.iSup_basicOpen_eq_top
        (homogeneousSubmodule σ R)
        (X : σ → MvPolynomial σ R)
        irrelevant_toIdeal_le_span_range_X).ge
          (Set.mem_univ x))).choose
  covers x := by
    change x ∈
      (Proj.awayι
        (homogeneousSubmodule σ R)
        (X _)
        (X_mem_homogeneousSubmodule_one R _)
        Nat.zero_lt_one).opensRange
    rw [Proj.opensRange_awayι]
    exact
      (mem_iSup.mp
        ((Proj.iSup_basicOpen_eq_top
          (homogeneousSubmodule σ R)
          (X : σ → MvPolynomial σ R)
          irrelevant_toIdeal_le_span_range_X).ge
            (Set.mem_univ x))).choose_spec

/-- The scheme open cover underlying `coordinateAffineOpenCover`, with its
index type definitionally equal to the coordinate type. -/
@[simps! I₀ X f]
def coordinateSchemeOpenCover
    (R : Type u) [CommRing R] (σ : Type) :
    (Proj (homogeneousSubmodule σ R)).OpenCover where
  I₀ := σ
  X i := Spec ((coordinateAffineOpenCover R σ).X i)
  f i := coordinateChartMap R σ i
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ (coordinateAffineOpenCover R σ).map_prop i⟩
    obtain ⟨y, hy⟩ := (coordinateAffineOpenCover R σ).covers x
    exact ⟨(coordinateAffineOpenCover R σ).idx x, y, hy⟩

@[simp]
lemma coordinateAffineOpenCover_opensRange
    (R : Type u) [CommRing R] (σ : Type) (i : σ) :
    @Scheme.Hom.opensRange _ _
        (coordinateChartMap R σ i)
        ((coordinateSchemeOpenCover R σ).map_prop i) =
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
    coordinateChartMap R σ i ≫
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

/-- A standard affine chart in the product of two polynomial projective spaces. -/
abbrev segreProductStandardChart
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) : Scheme.{u} :=
  pullback
    (coordinateChartMap R (Fin (m + 1)) i ≫
      homogeneousProjπ (R := R) (σ := Fin (m + 1)))
    (coordinateChartMap R (Fin (n + 1)) j ≫
      homogeneousProjπ (R := R) (σ := Fin (n + 1)))

/-- The first projection from a standard product chart. -/
def segreProductStandardChartFst
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChart R m n i j ⟶
      Spec (CommRingCat.of (ProjectiveCoordinateAway R i)) :=
  pullback.fst
    (coordinateChartMap R (Fin (m + 1)) i ≫
      homogeneousProjπ (R := R) (σ := Fin (m + 1)))
    (coordinateChartMap R (Fin (n + 1)) j ≫
      homogeneousProjπ (R := R) (σ := Fin (n + 1)))

/-- The second projection from a standard product chart. -/
def segreProductStandardChartSnd
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChart R m n i j ⟶
      Spec (CommRingCat.of (ProjectiveCoordinateAway R j)) :=
  pullback.snd
    (coordinateChartMap R (Fin (m + 1)) i ≫
      homogeneousProjπ (R := R) (σ := Fin (m + 1)))
    (coordinateChartMap R (Fin (n + 1)) j ≫
      homogeneousProjπ (R := R) (σ := Fin (n + 1)))

/-- The map from a standard product chart to the product of projective spaces. -/
def segreProductStandardChartMap
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChart R m n i j ⟶ segreProductProj R m n :=
  pullback.map
    (coordinateChartMap R (Fin (m + 1)) i ≫
      homogeneousProjπ (R := R) (σ := Fin (m + 1)))
    (coordinateChartMap R (Fin (n + 1)) j ≫
      homogeneousProjπ (R := R) (σ := Fin (n + 1)))
    (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
    (homogeneousProjπ (R := R) (σ := Fin (n + 1)))
    (coordinateChartMap R (Fin (m + 1)) i)
    (coordinateChartMap R (Fin (n + 1)) j)
    (𝟙 (Spec (CommRingCat.of R)))
    (Category.comp_id _)
    (Category.comp_id _)

/-- The product of the standard coordinate covers on the two projective factors. -/
@[simps! I₀ X f]
def segreProductStandardOpenCover
    (R : Type u) [CommRing R] (m n : ℕ) :
    (segreProductProj R m n).OpenCover where
  I₀ := Fin (m + 1) × Fin (n + 1)
  X ij := segreProductStandardChart R m n ij.1 ij.2
  f ij := segreProductStandardChartMap R m n ij.1 ij.2
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      obtain ⟨i, xi, hi⟩ :=
        (coordinateSchemeOpenCover R (Fin (m + 1))).exists_eq
          (pullback.fst
            (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
            (homogeneousProjπ (R := R) (σ := Fin (n + 1))) x)
      obtain ⟨j, yj, hj⟩ :=
        (coordinateSchemeOpenCover R (Fin (n + 1))).exists_eq
          (pullback.snd
            (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
            (homogeneousProjπ (R := R) (σ := Fin (n + 1))) x)
      refine ⟨(i, j), ?_⟩
      change x ∈ Set.range
        (pullback.map
          (coordinateChartMap R (Fin (m + 1)) i ≫ homogeneousProjπ)
          (coordinateChartMap R (Fin (n + 1)) j ≫ homogeneousProjπ)
          (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
          (homogeneousProjπ (R := R) (σ := Fin (n + 1)))
          (coordinateChartMap R (Fin (m + 1)) i)
          (coordinateChartMap R (Fin (n + 1)) j)
          (𝟙 (Spec (CommRingCat.of R)))
          (Category.comp_id _)
          (Category.comp_id _))
      rw [Scheme.Pullback.range_map
        (coordinateChartMap R (Fin (m + 1)) i ≫ homogeneousProjπ)
        (coordinateChartMap R (Fin (n + 1)) j ≫ homogeneousProjπ)
        (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
        (homogeneousProjπ (R := R) (σ := Fin (n + 1)))
        (coordinateChartMap R (Fin (m + 1)) i)
        (coordinateChartMap R (Fin (n + 1)) j)
        (𝟙 (Spec (CommRingCat.of R)))
        (Category.comp_id _)
        (Category.comp_id _)]
      exact ⟨⟨xi, hi⟩, ⟨yj, hj⟩⟩
    · intro ij
      letI : IsOpenImmersion (coordinateChartMap R (Fin (m + 1)) ij.1) :=
        (coordinateSchemeOpenCover R (Fin (m + 1))).map_prop ij.1
      letI : IsOpenImmersion (coordinateChartMap R (Fin (n + 1)) ij.2) :=
        (coordinateSchemeOpenCover R (Fin (n + 1))).map_prop ij.2
      change IsOpenImmersion
        (pullback.map
          (coordinateChartMap R (Fin (m + 1)) ij.1 ≫ homogeneousProjπ)
          (coordinateChartMap R (Fin (n + 1)) ij.2 ≫ homogeneousProjπ)
          (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
          (homogeneousProjπ (R := R) (σ := Fin (n + 1)))
          (coordinateChartMap R (Fin (m + 1)) ij.1)
          (coordinateChartMap R (Fin (n + 1)) ij.2)
          (𝟙 (Spec (CommRingCat.of R)))
          (Category.comp_id _)
          (Category.comp_id _))
      exact Scheme.pullback_map_isOpenImmersion
        (coordinateChartMap R (Fin (m + 1)) ij.1 ≫ homogeneousProjπ)
        (coordinateChartMap R (Fin (n + 1)) ij.2 ≫ homogeneousProjπ)
        (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
        (homogeneousProjπ (R := R) (σ := Fin (n + 1)))
        (coordinateChartMap R (Fin (m + 1)) ij.1)
        (coordinateChartMap R (Fin (n + 1)) ij.2)
        (𝟙 (Spec (CommRingCat.of R)))
        (Category.comp_id _)
        (Category.comp_id _)

/-- A standard product chart is the spectrum of the tensor product of its two factor rings. -/
def segreProductStandardChartIsoSpec
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChart R m n i j ≅
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

/-- The inverse tensor-spectrum chart isomorphism followed by the first chart projection. -/
def segreProductStandardChartIsoSpecInvFst
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Spec (CommRingCat.of (SegreProductChartRing R m n i j)) ⟶
      Spec (CommRingCat.of (ProjectiveCoordinateAway R i)) :=
  (segreProductStandardChartIsoSpec R m n i j).inv ≫
    segreProductStandardChartFst R m n i j

/-- The inverse tensor-spectrum chart isomorphism followed by the second chart projection. -/
def segreProductStandardChartIsoSpecInvSnd
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Spec (CommRingCat.of (SegreProductChartRing R m n i j)) ⟶
      Spec (CommRingCat.of (ProjectiveCoordinateAway R j)) :=
  (segreProductStandardChartIsoSpec R m n i j).inv ≫
    segreProductStandardChartSnd R m n i j

/-- A standard product chart is canonically isomorphic to the corresponding Segre-image chart. -/
def segreProductStandardChartIsoImageChart
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChart R m n i j ≅
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
    segreProductStandardChart R m n i j ⟶
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
