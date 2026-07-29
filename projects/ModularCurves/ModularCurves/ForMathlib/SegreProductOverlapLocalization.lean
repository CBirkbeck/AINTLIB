/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from the localization-model block of Clawristotle's
`CoherentCohomologyFinite.SegreProductStandardOverlap`.
-/
import ModularCurves.ForMathlib.SegreProductOverlapOpen

/-!
# Localization models of standard Segre product overlaps

Each double overlap in the standard cover of a product of projective spaces is identified
with the spectrum of the product-chart ring localized at its transition function.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The distinguished localization morphism into the affine-spectrum model of a product chart. -/
def segreProductChartLocalizationMap
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec (CommRingCat.of
      (SegreProductChartOverlapRing R m n i a j b)) ⟶
        Spec (CommRingCat.of
          (SegreProductChartRing R m n i j)) :=
  Spec.map
    (CommRingCat.ofHom
      (algebraMap
        (SegreProductChartRing R m n i j)
        (SegreProductChartOverlapRing R m n i a j b)))

instance isOpenImmersion_segreProductChartLocalizationMap
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    IsOpenImmersion
      (segreProductChartLocalizationMap R m n i a j b) :=
  IsOpenImmersion.of_isLocalization
    (segreProductChartTransition R m n i a j b)

lemma opensRange_segreProductChartLocalizationMap
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductChartLocalizationMap R m n i a j b).opensRange =
      segreProductChartTransitionOpen R m n i a j b := by
  apply TopologicalSpace.Opens.ext
  exact
    PrimeSpectrum.localization_away_comap_range
      (SegreProductChartOverlapRing R m n i a j b)
      (segreProductChartTransition R m n i a j b)

/-- The localization model of an overlap, mapped into its first product chart. -/
def segreProductChartOverlapToChart
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec (CommRingCat.of
      (SegreProductChartOverlapRing R m n i a j b)) ⟶
        segreProductStandardChart R m n i j :=
  segreProductChartLocalizationMap R m n i a j b ≫
    (segreProductStandardChartIsoSpec R m n i j).inv

instance isOpenImmersion_segreProductChartOverlapToChart
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    IsOpenImmersion
      (segreProductChartOverlapToChart R m n i a j b) := by
  unfold segreProductChartOverlapToChart
  infer_instance

private lemma opensRange_comp_iso_inv_eq_of_preimage
    {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f]
    (e : Z ≅ Y) (U : Z.Opens) (V : Y.Opens)
    (hf : f.opensRange = V)
    (he : e.inv ⁻¹ᵁ U = V) :
    (f ≫ e.inv).opensRange = U := by
  calc
    (f ≫ e.inv).opensRange =
        e.inv ''ᵁ f.opensRange :=
      Scheme.Hom.opensRange_comp f e.inv
    _ = e.inv ''ᵁ V := by rw [hf]
    _ = e.inv ''ᵁ e.inv ⁻¹ᵁ U := by rw [he]
    _ = e.inv.opensRange ⊓ U :=
      e.inv.image_preimage_eq_opensRange_inf U
    _ = ⊤ ⊓ U := by
      rw [Scheme.Hom.opensRange_of_isIso]
    _ = U := by simp

lemma opensRange_segreProductChartOverlapToChart
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductChartOverlapToChart R m n i a j b).opensRange =
      segreProductChartOverlapOpen R m n i a j b :=
  opensRange_comp_iso_inv_eq_of_preimage
    (segreProductChartLocalizationMap R m n i a j b)
    (segreProductStandardChartIsoSpec R m n i j)
    (segreProductChartOverlapOpen R m n i a j b)
    (segreProductChartTransitionOpen R m n i a j b)
    (opensRange_segreProductChartLocalizationMap
      R m n i a j b)
    (segreProductStandardChartIsoSpec_inv_preimage
      R m n i a j b)

private lemma isOpenImmersion_segreProductStandardChartMap
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    IsOpenImmersion (segreProductStandardChartMap R m n i j) := by
  rw [← segreProductStandardOpenCover_f R m n (i, j)]
  exact (segreProductStandardOpenCover R m n).map_prop (i, j)

/-- The actual pullback overlap of two product charts, identified with the distinguished
localization of the first chart ring. -/
def segreProductStandardOverlapIso
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    pullback
        (segreProductStandardChartMap R m n i j)
        (segreProductStandardChartMap R m n a b) ≅
      Spec (CommRingCat.of
        (SegreProductChartOverlapRing R m n i a j b)) := by
  letI : IsOpenImmersion
      (segreProductStandardChartMap R m n a b) :=
    isOpenImmersion_segreProductStandardChartMap R m n a b
  exact IsOpenImmersion.isoOfRangeEq
    (pullback.fst
      (segreProductStandardChartMap R m n i j)
      (segreProductStandardChartMap R m n a b))
    (segreProductChartOverlapToChart R m n i a j b)
    (by
      rw [← Scheme.Hom.coe_opensRange,
        ← Scheme.Hom.coe_opensRange,
        Scheme.Hom.opensRange_pullbackFst,
        opensRange_segreProductChartOverlapToChart]
      rfl)

@[reassoc]
lemma segreProductStandardOverlapIso_hom_toChart
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductStandardOverlapIso R m n i a j b).hom ≫
        segreProductChartOverlapToChart R m n i a j b =
      pullback.fst
        (segreProductStandardChartMap R m n i j)
        (segreProductStandardChartMap R m n a b) := by
  letI : IsOpenImmersion
      (segreProductStandardChartMap R m n a b) :=
    isOpenImmersion_segreProductStandardChartMap R m n a b
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end MvPolynomial
