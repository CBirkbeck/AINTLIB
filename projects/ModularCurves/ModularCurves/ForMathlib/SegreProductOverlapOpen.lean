/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from the overlap-open calculation in Clawristotle's
`CoherentCohomologyFinite.SegreProductStandardOverlap`.
-/
import ModularCurves.ForMathlib.SegreProductCoverGeometry

/-!
# Double overlaps in the standard Segre product cover

This file identifies the intersection of two standard product charts with the distinguished
open cut out by the product of the two projective coordinate transitions.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The inverse image of a coordinate chart inside another coordinate chart is the
distinguished open cut out by the corresponding coordinate ratio. -/
@[simp]
lemma coordinateChartMap_preimage_coordinateOpen
    (R : Type u) [CommRing R] (σ : Type) (i j : σ) :
    coordinateChartMap R σ i ⁻¹ᵁ coordinateOpen (R := R) j =
      PrimeSpectrum.basicOpen (projectiveCoordinateRatio R i j) := by
  have hratio :
      HomogeneousLocalization.Away.isLocalizationElem
          (X_mem_homogeneousSubmodule_one R i)
          (X_mem_homogeneousSubmodule_one R j) =
        projectiveCoordinateRatio R i j := by
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.Away.val_mk, pow_one]
  rw [← hratio]
  exact Proj.awayι_preimage_basicOpen
    (𝒜 := homogeneousSubmodule σ R)
    (X_mem_homogeneousSubmodule_one R i)
    Nat.zero_lt_one
    (X_mem_homogeneousSubmodule_one R j)
    Nat.zero_lt_one

private lemma segreProductStandardChartMap_isOpenImmersion
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    IsOpenImmersion (segreProductStandardChartMap R m n i j) := by
  rw [← segreProductStandardOpenCover_f R m n (i, j)]
  exact (segreProductStandardOpenCover R m n).map_prop (i, j)

private lemma opensRange_segreProductStandardChartMap
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    @Scheme.Hom.opensRange _ _
        (segreProductStandardChartMap R m n i j)
        (segreProductStandardChartMap_isOpenImmersion R m n i j) =
      pullback.fst
          (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
          (homogeneousProjπ (R := R) (σ := Fin (n + 1))) ⁻¹ᵁ
          coordinateOpen (R := R) i ⊓
        pullback.snd
            (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
            (homogeneousProjπ (R := R) (σ := Fin (n + 1))) ⁻¹ᵁ
          coordinateOpen (R := R) j := by
  have h := opensRange_segreProductStandardOpenCover_f R m n i j
  change @Scheme.Hom.opensRange _ _
      (segreProductStandardChartMap R m n i j)
      (segreProductStandardChartMap_isOpenImmersion R m n i j) = _ at h
  exact h

private lemma segreProductStandardChartMap_fst
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChartMap R m n i j ≫
        pullback.fst
          (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
          (homogeneousProjπ (R := R) (σ := Fin (n + 1))) =
      segreProductStandardChartFst R m n i j ≫
        coordinateChartMap R (Fin (m + 1)) i := by
  unfold segreProductStandardChartMap segreProductStandardChartFst
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

private lemma segreProductStandardChartMap_snd
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChartMap R m n i j ≫
        pullback.snd
          (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
          (homogeneousProjπ (R := R) (σ := Fin (n + 1))) =
      segreProductStandardChartSnd R m n i j ≫
        coordinateChartMap R (Fin (n + 1)) j := by
  unfold segreProductStandardChartMap segreProductStandardChartSnd
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  exact pullback.lift_snd _ _ _

/-- The intersection with the `(a, b)` chart, regarded as an open of the `(i, j)`
product chart. -/
def segreProductChartOverlapOpen
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductStandardChart R m n i j).Opens :=
  segreProductStandardChartMap R m n i j ⁻¹ᵁ
    @Scheme.Hom.opensRange _ _
      (segreProductStandardChartMap R m n a b)
      (segreProductStandardChartMap_isOpenImmersion R m n a b)

/-- The distinguished open cut out by the product transition function in the affine-spectrum
model of the `(i, j)` chart. -/
def segreProductChartTransitionOpen
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (Spec (CommRingCat.of (SegreProductChartRing R m n i j))).Opens :=
  PrimeSpectrum.basicOpen
    (segreProductChartTransition R m n i a j b)

private lemma segreProductStandardChartIsoSpec_inv_preimage_fst
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j : Fin (n + 1)) :
    ((segreProductStandardChartIsoSpec R m n i j).inv ≫
        segreProductStandardChartMap R m n i j) ⁻¹ᵁ
      (pullback.fst
          (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
          (homogeneousProjπ (R := R) (σ := Fin (n + 1))) ⁻¹ᵁ
        coordinateOpen (R := R) a) =
      PrimeSpectrum.basicOpen
        (Algebra.TensorProduct.includeLeftRingHom
          (projectiveCoordinateRatio R i a) :
            SegreProductChartRing R m n i j) := by
  rw [← Scheme.Hom.comp_preimage, Category.assoc,
    segreProductStandardChartMap_fst, ← Category.assoc]
  rw [Scheme.Hom.comp_preimage]
  change segreProductStandardChartIsoSpecInvFst R m n i j ⁻¹ᵁ _ = _
  rw [segreProductStandardChartIsoSpec_inv_chartFst]
  rw [coordinateChartMap_preimage_coordinateOpen,
    SpecMap_preimage_basicOpen]
  rfl

private lemma segreProductStandardChartIsoSpec_inv_preimage_snd
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j b : Fin (n + 1)) :
    ((segreProductStandardChartIsoSpec R m n i j).inv ≫
        segreProductStandardChartMap R m n i j) ⁻¹ᵁ
      (pullback.snd
          (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
          (homogeneousProjπ (R := R) (σ := Fin (n + 1))) ⁻¹ᵁ
        coordinateOpen (R := R) b) =
      PrimeSpectrum.basicOpen
        ((Algebra.TensorProduct.includeRight :
            ProjectiveCoordinateAway R j →ₐ[R]
              SegreProductChartRing R m n i j)
          (projectiveCoordinateRatio R j b)) := by
  rw [← Scheme.Hom.comp_preimage, Category.assoc,
    segreProductStandardChartMap_snd, ← Category.assoc]
  rw [Scheme.Hom.comp_preimage]
  change segreProductStandardChartIsoSpecInvSnd R m n i j ⁻¹ᵁ _ = _
  rw [segreProductStandardChartIsoSpec_inv_chartSnd]
  rw [coordinateChartMap_preimage_coordinateOpen,
    SpecMap_preimage_basicOpen]
  rfl

private lemma basicOpen_segreProductChartTransition
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    PrimeSpectrum.basicOpen
        (Algebra.TensorProduct.includeLeftRingHom
          (projectiveCoordinateRatio R i a) :
            SegreProductChartRing R m n i j) ⊓
      PrimeSpectrum.basicOpen
        ((Algebra.TensorProduct.includeRight :
            ProjectiveCoordinateAway R j →ₐ[R]
              SegreProductChartRing R m n i j)
          (projectiveCoordinateRatio R j b)) =
      PrimeSpectrum.basicOpen
        (segreProductChartTransition R m n i a j b) := by
  rw [← PrimeSpectrum.basicOpen_mul]
  congr 1
  simp [segreProductChartTransition]

/-- In the affine-spectrum model of the `(i, j)` product chart, its intersection with the
`(a, b)` chart is the distinguished open of the product transition function. -/
lemma segreProductStandardChartIsoSpec_inv_preimage
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductStandardChartIsoSpec R m n i j).inv ⁻¹ᵁ
        segreProductChartOverlapOpen R m n i a j b =
      segreProductChartTransitionOpen R m n i a j b := by
  rw [segreProductChartOverlapOpen,
    segreProductChartTransitionOpen,
    ← Scheme.Hom.comp_preimage,
    opensRange_segreProductStandardChartMap,
    Scheme.Hom.preimage_inf,
    segreProductStandardChartIsoSpec_inv_preimage_fst,
    segreProductStandardChartIsoSpec_inv_preimage_snd]
  exact basicOpen_segreProductChartTransition R m n i a j b

end MvPolynomial
