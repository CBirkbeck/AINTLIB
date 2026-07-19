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

end

end AlgebraicGeometry.Scheme.FiniteProperClosure
