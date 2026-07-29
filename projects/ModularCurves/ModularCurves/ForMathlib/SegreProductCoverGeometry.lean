/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from the first geometric block of Clawristotle's
`CoherentCohomologyFinite.SegreProductStandardOverlap`.
-/
import ModularCurves.ForMathlib.SegreProductStandardCover
import ModularCurves.ForMathlib.SegreStandardChartOverlapAlgebra

/-!
# Geometry of the standard cover on a product of projective spaces

This file computes the ranges and the two projections of the standard product-cover maps.
It also computes the projections of the affine tensor-product presentation of each chart.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The range of a standard product chart is the intersection of the inverse images of
the two factor charts. -/
lemma opensRange_segreProductStandardOpenCover_f
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    @Scheme.Hom.opensRange _ _
        ((segreProductStandardOpenCover R m n).f (i, j))
        ((segreProductStandardOpenCover R m n).map_prop (i, j)) =
      pullback.fst
          (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
          (homogeneousProjπ (R := R) (σ := Fin (n + 1))) ⁻¹ᵁ
          coordinateOpen (R := R) i ⊓
        pullback.snd
            (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
            (homogeneousProjπ (R := R) (σ := Fin (n + 1))) ⁻¹ᵁ
          coordinateOpen (R := R) j := by
  apply TopologicalSpace.Opens.ext
  change
    Set.range
        (pullback.map
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
          (Category.comp_id _)) =
      _
  rw [Scheme.Pullback.range_map]
  rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
    coordinateAffineOpenCover_opensRange,
    coordinateAffineOpenCover_opensRange]
  rfl

@[reassoc]
lemma segreProductStandardOpenCover_f_fst
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardOpenCover R m n).f (i, j) ≫
        pullback.fst
          (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
          (homogeneousProjπ (R := R) (σ := Fin (n + 1))) =
      segreProductStandardChartFst R m n i j ≫
        coordinateChartMap R (Fin (m + 1)) i := by
  rw [segreProductStandardOpenCover_f]
  unfold segreProductStandardChartMap segreProductStandardChartFst
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

@[reassoc]
lemma segreProductStandardOpenCover_f_snd
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardOpenCover R m n).f (i, j) ≫
        pullback.snd
          (homogeneousProjπ (R := R) (σ := Fin (m + 1)))
          (homogeneousProjπ (R := R) (σ := Fin (n + 1))) =
      segreProductStandardChartSnd R m n i j ≫
        coordinateChartMap R (Fin (n + 1)) j := by
  rw [segreProductStandardOpenCover_f]
  unfold segreProductStandardChartMap segreProductStandardChartSnd
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  exact pullback.lift_snd _ _ _

private lemma pullback_congrHom_inv_fst
    {X Y Z : Scheme} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
    [HasPullback f₁ g₁] [HasPullback f₂ g₂]
    (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) :
    (pullback.congrHom h₁ h₂).inv ≫ pullback.fst f₁ g₁ =
      pullback.fst f₂ g₂ := by
  rw [pullback.congrHom_inv]
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  rw [pullback.lift_fst, Category.comp_id]

private lemma pullback_congrHom_inv_snd
    {X Y Z : Scheme} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
    [HasPullback f₁ g₁] [HasPullback f₂ g₂]
    (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) :
    (pullback.congrHom h₁ h₂).inv ≫ pullback.snd f₁ g₁ =
      pullback.snd f₂ g₂ := by
  rw [pullback.congrHom_inv]
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  rw [pullback.lift_snd, Category.comp_id]

lemma segreProductStandardChartIsoSpec_inv_chartFst
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChartIsoSpecInvFst R m n i j =
      Spec.map
        (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom :
            ProjectiveCoordinateAway R i →+*
              SegreProductChartRing R m n i j)) := by
  simp only [segreProductStandardChartIsoSpecInvFst,
    segreProductStandardChartIsoSpec, segreProductStandardChartFst,
    Iso.trans_inv, Category.assoc, pullback_congrHom_inv_fst,
    pullbackSpecIso_inv_fst]

lemma segreProductStandardChartIsoSpec_inv_chartSnd
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChartIsoSpecInvSnd R m n i j =
      Spec.map
        (CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight :
            ProjectiveCoordinateAway R j →ₐ[R]
              SegreProductChartRing R m n i j).toRingHom)) := by
  simp only [segreProductStandardChartIsoSpecInvSnd,
    segreProductStandardChartIsoSpec, segreProductStandardChartSnd,
    Iso.trans_inv, Category.assoc, pullback_congrHom_inv_snd,
    pullbackSpecIso_inv_snd, AlgHom.toRingHom_eq_coe]

lemma segreProductStandardChartIsoSpec_inv_fst
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChartIsoSpecInvFst R m n i j ≫
        coordinateChartMap R (Fin (m + 1)) i =
      Spec.map
          (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom :
              ProjectiveCoordinateAway R i →+*
                SegreProductChartRing R m n i j)) ≫
        coordinateChartMap R (Fin (m + 1)) i := by
  rw [segreProductStandardChartIsoSpec_inv_chartFst]

lemma segreProductStandardChartIsoSpec_inv_snd
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChartIsoSpecInvSnd R m n i j ≫
        coordinateChartMap R (Fin (n + 1)) j =
      Spec.map
          (CommRingCat.ofHom
            ((Algebra.TensorProduct.includeRight :
              ProjectiveCoordinateAway R j →ₐ[R]
                SegreProductChartRing R m n i j).toRingHom)) ≫
        coordinateChartMap R (Fin (n + 1)) j := by
  rw [segreProductStandardChartIsoSpec_inv_chartSnd]

end MvPolynomial
