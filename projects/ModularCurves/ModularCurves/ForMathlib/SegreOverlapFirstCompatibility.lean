/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from the first-chart block of Clawristotle's
`CoherentCohomologyFinite.SegreStandardOverlapCompatibility`.
-/
import ModularCurves.ForMathlib.SegreProductOverlapLocalization

/-!
# First-chart compatibility of the localized Segre equivalence

The localized standard-chart equivalence extends the original Segre chart map. Contravariantly,
the corresponding affine-spectrum isomorphism commutes with the maps to the first charts.
-/

open CategoryTheory AlgebraicGeometry
open HomogeneousLocalization

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The localized Segre chart equivalence extends the unlocalized forward chart map. -/
lemma segreStandardChartOverlapRingEquiv_awayMap
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1))
    (x : SegreImageChartRing R m n i j) :
    segreStandardChartOverlapRingEquiv R m n i a j b
        (HomogeneousLocalization.awayMap
          (segreImageGrading R m n)
          (segreImageCoordinate_mem_degreeOne R m n
            (segrePairIndex m n a b))
          rfl x) =
      algebraMap
        (SegreProductChartRing R m n i j)
        (SegreProductChartOverlapRing R m n i a j b)
        (segreChartForwardAlgHom R m n i j x) := by
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
  have hmap :
      (Submonoid.powers
        (segreImageChartRatio R m n i a j b)).map
          (segreStandardChartAlgEquiv
            R m n i j).toRingEquiv.toMonoidHom =
        Submonoid.powers
          (segreProductChartTransition R m n i a j b) := by
    rw [Submonoid.map_powers]
    apply congrArg
    exact
      segreChartForwardAlgHom_transition
        R m n i a j b
  change
    IsLocalization.ringEquivOfRingEquiv
        (SegreImageChartOverlapRing R m n i a j b)
        (SegreProductChartOverlapRing R m n i a j b)
        (segreStandardChartAlgEquiv R m n i j).toRingEquiv
        hmap
        ((algebraMap
          (SegreImageChartRing R m n i j)
          (SegreImageChartOverlapRing R m n i a j b)) x) =
      algebraMap
        (SegreProductChartRing R m n i j)
        (SegreProductChartOverlapRing R m n i a j b)
        ((segreStandardChartAlgEquiv R m n i j).toRingEquiv x)
  exact IsLocalization.ringEquivOfRingEquiv_eq hmap x

/-- The affine-spectrum isomorphism induced by the localized Segre chart equivalence. -/
def segreProductOverlapIsoSegreImage
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec (CommRingCat.of
      (SegreProductChartOverlapRing R m n i a j b)) ≅
        Spec (CommRingCat.of
          (SegreImageChartOverlapRing R m n i a j b)) :=
  Scheme.Spec.mapIso
    (segreStandardChartOverlapRingEquiv
      R m n i a j b).toCommRingCatIso.op

/-- The double Segre-image chart maps to its first standard chart by the canonical
homogeneous away map. -/
def segreImageOverlapToFirstChart
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec (CommRingCat.of
      (SegreImageChartOverlapRing R m n i a j b)) ⟶
        Spec (CommRingCat.of
          (SegreImageChartRing R m n i j)) :=
  Spec.map
    (CommRingCat.ofHom
      (HomogeneousLocalization.awayMap
        (segreImageGrading R m n)
        (segreImageCoordinate_mem_degreeOne R m n
          (segrePairIndex m n a b))
        rfl))

/-- On affine spectra, the localized Segre equivalence intertwines the first-chart
localization maps. -/
@[reassoc]
lemma segreProductOverlapIsoSegreImage_hom_toFirstChart
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductOverlapIsoSegreImage R m n i a j b).hom ≫
        segreImageOverlapToFirstChart R m n i a j b =
      segreProductChartLocalizationMap R m n i a j b ≫
        Spec.map
          (CommRingCat.ofHom
            (segreChartForwardAlgHom R m n i j).toRingHom) := by
  simp only [segreProductOverlapIsoSegreImage,
    segreImageOverlapToFirstChart,
    Scheme.Spec_map, Functor.mapIso_hom, Iso.op_hom,
    Quiver.Hom.unop_op, segreProductChartLocalizationMap,
    ← Spec.map_comp]
  congr 1
  ext x
  exact
    segreStandardChartOverlapRingEquiv_awayMap
      R m n i a j b x

end MvPolynomial
