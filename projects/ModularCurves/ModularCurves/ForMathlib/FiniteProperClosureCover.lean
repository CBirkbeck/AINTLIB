import ModularCurves.ForMathlib.FiniteProperClosurePreimage

/-!
# Proper surjective covers from finite proper closures

This file proves that the glued morphism from the union of inverse-image charts is proper and,
when the common source is scheme-theoretically dense in the target, surjective.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FiniteProperClosure

noncomputable section

variable {S X T : Scheme.{u}} {ι : Type u} [Finite ι]
variable {U Z : ι → Scheme.{u}}
variable (p : ∀ i, Z i ⟶ S) (j : ∀ i, U i ⟶ Z i)
variable [∀ i, IsOpenImmersion (j i)]
variable (q : T ⟶ S) (g : ∀ i, T ⟶ U i)
variable (hf : ∀ i, (g i ≫ j i) ≫ p i = q)

private abbrev coordinates : ∀ i, T ⟶ Z i := fun i ↦ g i ≫ j i

variable (a : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (a i)]
variable (xπ : X ⟶ S) [IsSeparated xπ]
variable (ha : ∀ i, a i ≫ xπ = j i ≫ p i)
variable (hga : ∀ i k, g i ≫ a i = g k ≫ a k)
variable [QuasiCompact (diagonal p q (coordinates j g) hf)]

private abbrev unionMap : (chartUnion p j q g hf).toScheme ⟶ X :=
  chartUnionToTarget p j q g hf a xπ ha hga

/-- The inverse image of a target chart is proper over that chart. -/
lemma targetPreimageToFactor_isProper (hp : ∀ i, IsProper (p i)) (i : ι) :
    IsProper (targetPreimageToFactor p j q g hf a xπ ha hga i) := by
  letI : IsIso (chartToPreimage p j q g hf a xπ ha hga i) :=
    chartToPreimage_isIso p j q g hf a xπ ha hga hp i
  letI : IsProper (chartToFactor p j q g hf i) :=
    chartToFactor_isProper p j q g hf hp i
  have heq : targetPreimageToFactor p j q g hf a xπ ha hga i =
      inv (chartToPreimage p j q g hf a xπ ha hga i) ≫
        chartToFactor p j q g hf i := by
    rw [← cancel_epi (chartToPreimage p j q g hf a xπ ha hga i)]
    simp only [chartToPreimage_targetPreimageToFactor, IsIso.hom_inv_id_assoc]
  rw [heq]
  infer_instance

lemma targetPreimageToFactor_isoOpensRange_hom (i : ι) :
    targetPreimageToFactor p j q g hf a xπ ha hga i ≫
      (a i).isoOpensRange.hom =
        unionMap p j q g hf a xπ ha hga ∣_ (a i).opensRange := by
  rw [← cancel_mono (a i).opensRange.ι]
  simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι,
    targetPreimageToFactor_comp, morphismRestrict_ι]

/-- The restriction of the glued map over each target chart is proper. -/
lemma restrict_chartUnionToTarget_isProper (hp : ∀ i, IsProper (p i)) (i : ι) :
    IsProper (unionMap p j q g hf a xπ ha hga ∣_ (a i).opensRange) := by
  letI : IsProper (targetPreimageToFactor p j q g hf a xπ ha hga i) :=
    targetPreimageToFactor_isProper p j q g hf a xπ ha hga hp i
  rw [← targetPreimageToFactor_isoOpensRange_hom p j q g hf a xπ ha hga i]
  infer_instance

/-- The glued morphism from the closure chart union is proper. -/
lemma chartUnionToTarget_isProper (hp : ∀ i, IsProper (p i))
    (hcover : ⨆ i, (a i).opensRange = ⊤) :
    IsProper (unionMap p j q g hf a xπ ha hga) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @IsProper) (fun i ↦ (a i).opensRange) hcover
  exact restrict_chartUnionToTarget_isProper p j q g hf a xπ ha hga hp

/-- If the common source is scheme-theoretically dense in the target, the proper glued morphism
from the closure chart union is surjective. -/
lemma chartUnionToTarget_surjective (hp : ∀ i, IsProper (p i))
    (hcover : ⨆ i, (a i).opensRange = ⊤) (i : ι)
    [IsSchemeTheoreticallyDominant (g i ≫ a i)] :
    Surjective (unionMap p j q g hf a xπ ha hga) := by
  letI : IsProper (unionMap p j q g hf a xπ ha hga) :=
    chartUnionToTarget_isProper p j q g hf a xπ ha hga hp hcover
  haveI : IsSchemeTheoreticallyDominant
      (toChartUnion p j q g hf i ≫ unionMap p j q g hf a xπ ha hga) := by
    rw [toChartUnion_chartUnionToTarget]
    infer_instance
  letI : IsSchemeTheoreticallyDominant (unionMap p j q g hf a xπ ha hga) :=
    IsSchemeTheoreticallyDominant.of_comp (toChartUnion p j q g hf i)
      (unionMap p j q g hf a xπ ha hga)
  letI : QuasiCompact (unionMap p j q g hf a xπ ha hga) := inferInstance
  letI : IsDominant (unionMap p j q g hf a xπ ha hga) := inferInstance
  exact surjective_of_isDominant_of_isClosed_range
    (unionMap p j q g hf a xπ ha hga)
    (unionMap p j q g hf a xπ ha hga).isClosedMap.isClosed_range

end

end AlgebraicGeometry.Scheme.FiniteProperClosure
