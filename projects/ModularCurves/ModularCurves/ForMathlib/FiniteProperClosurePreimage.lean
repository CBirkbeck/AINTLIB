import ModularCurves.ForMathlib.FiniteProperClosureUnion

/-!
# Target preimages in finite proper closure chart unions

This file compares each inverse-image chart in a finite proper closure with the inverse image of
the corresponding target chart under the glued morphism from the chart union.
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

/-- The inverse image in the chart union of the `i`-th original chart. -/
abbrev targetPreimage (i : ι) : (chartUnion p j q g hf).toScheme.Opens :=
  unionMap p j q g hf a xπ ha hga ⁻¹ᵁ (a i).opensRange

/-- The canonical map from the `i`-th closure chart to the inverse image of the corresponding
original chart. -/
def chartToPreimage (i : ι) :
    (chart p j q g hf i).toScheme ⟶ (targetPreimage p j q g hf a xπ ha hga i).toScheme :=
  IsOpenImmersion.lift (targetPreimage p j q g hf a xπ ha hga i).ι
    ((obj p q (coordinates j g) hf).homOfLE
      (le_iSup (fun k ↦ chart p j q g hf k) i)) (by
        rintro _ ⟨x, rfl⟩
        refine ⟨⟨((obj p q (coordinates j g) hf).homOfLE
          (le_iSup (fun k ↦ chart p j q g hf k) i)) x, ?_⟩, rfl⟩
        change unionMap p j q g hf a xπ ha hga
          (((obj p q (coordinates j g) hf).homOfLE
            (le_iSup (fun k ↦ chart p j q g hf k) i)) x) ∈ (a i).opensRange
        exact Scheme.Hom.mem_opensRange.mpr
          ⟨chartToFactor p j q g hf i x, by
            simpa only [unionMap, chartToTarget, Scheme.Hom.comp_apply] using
              congrArg (fun h : (chart p j q g hf i).toScheme ⟶ X ↦ h x)
                (homOfLE_chartUnionToTarget p j q g hf a xπ ha hga i).symm⟩)

@[reassoc (attr := simp)]
lemma chartToPreimage_ι (i : ι) :
    chartToPreimage p j q g hf a xπ ha hga i ≫
      (targetPreimage p j q g hf a xπ ha hga i).ι =
        (obj p q (coordinates j g) hf).homOfLE
          (le_iSup (fun k ↦ chart p j q g hf k) i) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The inverse image of the `i`-th original chart maps canonically to that chart. -/
def targetPreimageToFactor (i : ι) :
    (targetPreimage p j q g hf a xπ ha hga i).toScheme ⟶ U i :=
  IsOpenImmersion.lift (a i)
    ((targetPreimage p j q g hf a xπ ha hga i).ι ≫
      unionMap p j q g hf a xπ ha hga) (by
        rintro _ ⟨x, rfl⟩
        exact Scheme.Hom.mem_opensRange.mp x.2)

@[reassoc (attr := simp)]
lemma targetPreimageToFactor_comp (i : ι) :
    targetPreimageToFactor p j q g hf a xπ ha hga i ≫ a i =
      (targetPreimage p j q g hf a xπ ha hga i).ι ≫
        unionMap p j q g hf a xπ ha hga :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
lemma chartToPreimage_targetPreimageToFactor (i : ι) :
    chartToPreimage p j q g hf a xπ ha hga i ≫
      targetPreimageToFactor p j q g hf a xπ ha hga i =
        chartToFactor p j q g hf i := by
  rw [← cancel_mono (a i)]
  simp only [Category.assoc, targetPreimageToFactor_comp,
    chartToPreimage_ι_assoc, homOfLE_chartUnionToTarget, chartToTarget]

/-- The closure chart is open in the corresponding target preimage. -/
lemma chartToPreimage_isOpenImmersion (i : ι) :
    IsOpenImmersion (chartToPreimage p j q g hf a xπ ha hga i) := by
  haveI : IsOpenImmersion
      (chartToPreimage p j q g hf a xπ ha hga i ≫
        (targetPreimage p j q g hf a xπ ha hga i).ι) := by
    rw [chartToPreimage_ι]
    infer_instance
  exact IsOpenImmersion.of_comp
    (chartToPreimage p j q g hf a xπ ha hga i)
    (targetPreimage p j q g hf a xπ ha hga i).ι

@[reassoc]
lemma targetPreimageToFactor_comp_base (i : ι) :
    targetPreimageToFactor p j q g hf a xπ ha hga i ≫ (j i ≫ p i) =
      ((targetPreimage p j q g hf a xπ ha hga i).ι ≫
        (chartUnion p j q g hf).ι) ≫ π p q (coordinates j g) hf := by
  calc
    targetPreimageToFactor p j q g hf a xπ ha hga i ≫ (j i ≫ p i) =
        targetPreimageToFactor p j q g hf a xπ ha hga i ≫ (a i ≫ xπ) := by
      rw [ha i]
    _ = (targetPreimageToFactor p j q g hf a xπ ha hga i ≫ a i) ≫ xπ :=
      (Category.assoc _ _ _).symm
    _ = ((targetPreimage p j q g hf a xπ ha hga i).ι ≫
          unionMap p j q g hf a xπ ha hga) ≫ xπ := by
      rw [targetPreimageToFactor_comp]
    _ = (targetPreimage p j q g hf a xπ ha hga i).ι ≫
          (unionMap p j q g hf a xπ ha hga ≫ xπ) :=
      Category.assoc _ _ _
    _ = (targetPreimage p j q g hf a xπ ha hga i).ι ≫
          ((chartUnion p j q g hf).ι ≫ π p q (coordinates j g) hf) := by
      rw [chartUnionToTarget_comp]
    _ = ((targetPreimage p j q g hf a xπ ha hga i).ι ≫
          (chartUnion p j q g hf).ι) ≫ π p q (coordinates j g) hf :=
      (Category.assoc _ _ _).symm

/-- The map from a target preimage back to its original chart is separated. -/
lemma targetPreimageToFactor_isSeparated (hp : ∀ i, IsProper (p i)) (i : ι) :
    IsSeparated (targetPreimageToFactor p j q g hf a xπ ha hga i) := by
  letI : IsProper (π p q (coordinates j g) hf) :=
    π_isProper p q (coordinates j g) hf hp
  haveI : IsSeparated
      (((targetPreimage p j q g hf a xπ ha hga i).ι ≫
        (chartUnion p j q g hf).ι) ≫ π p q (coordinates j g) hf) := by
    infer_instance
  haveI : IsSeparated
      (targetPreimageToFactor p j q g hf a xπ ha hga i ≫ (j i ≫ p i)) := by
    rw [targetPreimageToFactor_comp_base p j q g hf a xπ ha hga i]
    infer_instance
  exact IsSeparated.of_comp
    (targetPreimageToFactor p j q g hf a xπ ha hga i) (j i ≫ p i)

/-- The closure chart is proper over the corresponding target preimage. -/
lemma chartToPreimage_isProper (hp : ∀ i, IsProper (p i)) (i : ι) :
    IsProper (chartToPreimage p j q g hf a xπ ha hga i) := by
  letI : IsProper (chartToFactor p j q g hf i) :=
    chartToFactor_isProper p j q g hf hp i
  letI : IsSeparated (targetPreimageToFactor p j q g hf a xπ ha hga i) :=
    targetPreimageToFactor_isSeparated p j q g hf a xπ ha hga hp i
  haveI : IsProper
      (chartToPreimage p j q g hf a xπ ha hga i ≫
        targetPreimageToFactor p j q g hf a xπ ha hga i) := by
    rw [chartToPreimage_targetPreimageToFactor]
    infer_instance
  exact IsProper.of_comp
    (chartToPreimage p j q g hf a xπ ha hga i)
    (targetPreimageToFactor p j q g hf a xπ ha hga i)

/-- The common source lifted to the target preimage. -/
def toTargetPreimage (i : ι) :
    T ⟶ (targetPreimage p j q g hf a xπ ha hga i).toScheme :=
  IsOpenImmersion.lift (targetPreimage p j q g hf a xπ ha hga i).ι
    (toChartUnion p j q g hf i) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨toChartUnion p j q g hf i x, ?_⟩, rfl⟩
      change unionMap p j q g hf a xπ ha hga
        (toChartUnion p j q g hf i x) ∈ (a i).opensRange
      exact Scheme.Hom.mem_opensRange.mpr ⟨g i x, by
        simpa only [unionMap, Scheme.Hom.comp_apply] using
          congrArg (fun h : T ⟶ X ↦ h x)
            (toChartUnion_chartUnionToTarget p j q g hf a xπ ha hga i).symm⟩)

@[reassoc (attr := simp)]
lemma toTargetPreimage_ι (i : ι) :
    toTargetPreimage p j q g hf a xπ ha hga i ≫
      (targetPreimage p j q g hf a xπ ha hga i).ι =
        toChartUnion p j q g hf i :=
  IsOpenImmersion.lift_fac _ _ _

/-- The common source is scheme-theoretically dense in every target preimage. -/
lemma toTargetPreimage_isSchemeTheoreticallyDominant (i : ι) :
    IsSchemeTheoreticallyDominant
      (toTargetPreimage p j q g hf a xπ ha hga i) := by
  let inclusion :=
    (targetPreimage p j q g hf a xπ ha hga i).ι ≫
      (chartUnion p j q g hf).ι
  have hcomp : toTargetPreimage p j q g hf a xπ ha hga i ≫ inclusion =
      toClosure p q (coordinates j g) hf := by
    dsimp only [inclusion]
    calc
      (toTargetPreimage p j q g hf a xπ ha hga i ≫
          (targetPreimage p j q g hf a xπ ha hga i).ι) ≫
            (chartUnion p j q g hf).ι =
        toChartUnion p j q g hf i ≫ (chartUnion p j q g hf).ι := by
          rw [toTargetPreimage_ι]
      _ = toClosure p q (coordinates j g) hf :=
        toChartUnion_ι p j q g hf i
  have H : Set.range (toClosure p q (coordinates j g) hf) ⊆
      Set.range inclusion := by
    rintro _ ⟨x, rfl⟩
    exact ⟨toTargetPreimage p j q g hf a xπ ha hga i x,
      congrArg (fun h : T ⟶ obj p q (coordinates j g) hf ↦ h x) hcomp⟩
  let direct := IsOpenImmersion.lift inclusion
    (toClosure p q (coordinates j g) hf) H
  letI : IsSchemeTheoreticallyDominant (toClosure p q (coordinates j g) hf) :=
    toClosure_isSchemeTheoreticallyDominant p q (coordinates j g) hf
  letI : IsSchemeTheoreticallyDominant direct :=
    IsSchemeTheoreticallyDominant.lift_of_isOpenImmersion
      (toClosure p q (coordinates j g) hf) inclusion H
  have heq : toTargetPreimage p j q g hf a xπ ha hga i = direct := by
    apply IsOpenImmersion.lift_uniq inclusion
      (toClosure p q (coordinates j g) hf) H
    exact hcomp
  rw [heq]
  infer_instance

@[reassoc]
lemma toChart_chartToPreimage (i : ι) :
    toChart p j q g hf i ≫ chartToPreimage p j q g hf a xπ ha hga i =
      toTargetPreimage p j q g hf a xπ ha hga i := by
  rw [← cancel_mono (targetPreimage p j q g hf a xπ ha hga i).ι]
  simp only [Category.assoc, chartToPreimage_ι, toChart_homOfLE_chartUnion,
    toTargetPreimage_ι]

/-- The closure chart is scheme-theoretically dense in the corresponding target preimage. -/
lemma chartToPreimage_isSchemeTheoreticallyDominant (i : ι) :
    IsSchemeTheoreticallyDominant
      (chartToPreimage p j q g hf a xπ ha hga i) := by
  letI : IsSchemeTheoreticallyDominant
      (toTargetPreimage p j q g hf a xπ ha hga i) :=
    toTargetPreimage_isSchemeTheoreticallyDominant p j q g hf a xπ ha hga i
  haveI : IsSchemeTheoreticallyDominant
      (toChart p j q g hf i ≫ chartToPreimage p j q g hf a xπ ha hga i) := by
    rw [toChart_chartToPreimage]
    infer_instance
  exact IsSchemeTheoreticallyDominant.of_comp (toChart p j q g hf i)
    (chartToPreimage p j q g hf a xπ ha hga i)

/-- The closure chart surjects onto the corresponding target preimage. -/
lemma chartToPreimage_surjective (hp : ∀ i, IsProper (p i)) (i : ι) :
    Surjective (chartToPreimage p j q g hf a xπ ha hga i) := by
  letI : IsProper (chartToPreimage p j q g hf a xπ ha hga i) :=
    chartToPreimage_isProper p j q g hf a xπ ha hga hp i
  letI : IsSchemeTheoreticallyDominant
      (chartToPreimage p j q g hf a xπ ha hga i) :=
    chartToPreimage_isSchemeTheoreticallyDominant p j q g hf a xπ ha hga i
  letI : QuasiCompact (chartToPreimage p j q g hf a xπ ha hga i) := inferInstance
  letI : IsDominant (chartToPreimage p j q g hf a xπ ha hga i) := inferInstance
  exact surjective_of_isDominant_of_isClosed_range
    (chartToPreimage p j q g hf a xπ ha hga i)
    (chartToPreimage p j q g hf a xπ ha hga i).isClosedMap.isClosed_range

/-- The closure chart is isomorphic to the inverse image of the corresponding target chart. -/
lemma chartToPreimage_isIso (hp : ∀ i, IsProper (p i)) (i : ι) :
    IsIso (chartToPreimage p j q g hf a xπ ha hga i) := by
  letI : IsOpenImmersion (chartToPreimage p j q g hf a xπ ha hga i) :=
    chartToPreimage_isOpenImmersion p j q g hf a xπ ha hga i
  letI : Surjective (chartToPreimage p j q g hf a xπ ha hga i) :=
    chartToPreimage_surjective p j q g hf a xπ ha hga hp i
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

end

end AlgebraicGeometry.Scheme.FiniteProperClosure
