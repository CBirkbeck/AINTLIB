import ModularCurves.ForMathlib.FiniteProperClosureChart
import ModularCurves.ForMathlib.SpecBasicOpenAway

/-!
# Unions of charts in finite proper closures

This file forms the union of the inverse-image charts in a finite proper closure and glues their
compatible maps to a separated target.
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

/-- The union of the inverse-image charts in the finite proper closure. -/
abbrev chartUnion : (obj p q (coordinates j g) hf).Opens :=
  ⨆ i, chart p j q g hf i

/-- The common source lifted to the union of the inverse-image charts. -/
def toChartUnion (i : ι) : T ⟶ (chartUnion p j q g hf).toScheme :=
  IsOpenImmersion.lift (chartUnion p j q g hf).ι
    (toClosure p q (coordinates j g) hf) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨toClosure p q (coordinates j g) hf x,
        TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩⟩, rfl⟩
      change (proj p q (coordinates j g) hf i)
        (toClosure p q (coordinates j g) hf x) ∈ (j i).opensRange
      exact Scheme.Hom.mem_opensRange.mpr ⟨g i x, by
        simpa only [Scheme.Hom.comp_apply] using
          congrArg (fun h : T ⟶ Z i ↦ h x)
            (toClosure_proj p q (coordinates j g) hf i).symm⟩)

@[reassoc (attr := simp)]
lemma toChartUnion_ι (i : ι) :
    toChartUnion p j q g hf i ≫ (chartUnion p j q g hf).ι =
      toClosure p q (coordinates j g) hf :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
lemma toChart_homOfLE_chartUnion (i : ι) :
    toChart p j q g hf i ≫
      (obj p q (coordinates j g) hf).homOfLE
        (le_iSup (fun k ↦ chart p j q g hf k) i) =
      toChartUnion p j q g hf i := by
  rw [← cancel_mono (chartUnion p j q g hf).ι]
  simp only [Category.assoc, Scheme.homOfLE_ι, toChart_ι, toChartUnion_ι]

/-- The common source is scheme-theoretically dense in the union of inverse-image charts. -/
lemma toChartUnion_isSchemeTheoreticallyDominant
    [QuasiCompact (diagonal p q (coordinates j g) hf)] (i : ι) :
    IsSchemeTheoreticallyDominant (toChartUnion p j q g hf i) := by
  letI : IsSchemeTheoreticallyDominant (toClosure p q (coordinates j g) hf) :=
    toClosure_isSchemeTheoreticallyDominant p q (coordinates j g) hf
  exact IsSchemeTheoreticallyDominant.lift_of_isOpenImmersion
    (toClosure p q (coordinates j g) hf) (chartUnion p j q g hf).ι _

variable (a : ∀ i, U i ⟶ X) (xπ : X ⟶ S)
variable (ha : ∀ i, a i ≫ xπ = j i ≫ p i)
variable (hga : ∀ i k, g i ≫ a i = g k ≫ a k)

/-- The morphism from the union of the inverse-image charts to the original scheme. -/
def chartUnionToTarget [IsSeparated xπ]
    [QuasiCompact (diagonal p q (coordinates j g) hf)] :
    (chartUnion p j q g hf).toScheme ⟶ X :=
  (Scheme.Opens.iSupOpenCover (fun i ↦ chart p j q g hf i)).glueMorphisms
    (fun i ↦ chartToTarget p j q g hf a i)
    (glueMorphisms_hf_of_agree (fun i ↦ chart p j q g hf i)
      (fun i ↦ chartToTarget p j q g hf a i)
      (chartToTarget_agree p j q g hf a xπ ha hga))

@[reassoc (attr := simp)]
lemma homOfLE_chartUnionToTarget [IsSeparated xπ]
    [QuasiCompact (diagonal p q (coordinates j g) hf)] (i : ι) :
    (obj p q (coordinates j g) hf).homOfLE
        (le_iSup (fun k ↦ chart p j q g hf k) i) ≫
      chartUnionToTarget p j q g hf a xπ ha hga =
        chartToTarget p j q g hf a i :=
  (Scheme.Opens.iSupOpenCover (fun i ↦ chart p j q g hf i)).ι_glueMorphisms _ _ i

@[reassoc]
lemma toChartUnion_chartUnionToTarget [IsSeparated xπ]
    [QuasiCompact (diagonal p q (coordinates j g) hf)] (i : ι) :
    toChartUnion p j q g hf i ≫
      chartUnionToTarget p j q g hf a xπ ha hga = g i ≫ a i := by
  calc
    toChartUnion p j q g hf i ≫
        chartUnionToTarget p j q g hf a xπ ha hga =
      (toChart p j q g hf i ≫
        (obj p q (coordinates j g) hf).homOfLE
          (le_iSup (fun k ↦ chart p j q g hf k) i)) ≫
            chartUnionToTarget p j q g hf a xπ ha hga := by
      rw [toChart_homOfLE_chartUnion]
    _ = toChart p j q g hf i ≫
        ((obj p q (coordinates j g) hf).homOfLE
          (le_iSup (fun k ↦ chart p j q g hf k) i) ≫
            chartUnionToTarget p j q g hf a xπ ha hga) :=
      Category.assoc _ _ _
    _ = toChart p j q g hf i ≫ chartToTarget p j q g hf a i := by
      rw [homOfLE_chartUnionToTarget]
    _ = (toChart p j q g hf i ≫ chartToFactor p j q g hf i) ≫ a i := by
      simp only [chartToTarget, Category.assoc]
    _ = g i ≫ a i := by rw [toChart_chartToFactor]

@[reassoc]
lemma chartUnionToTarget_comp [IsSeparated xπ]
    [QuasiCompact (diagonal p q (coordinates j g) hf)] :
    chartUnionToTarget p j q g hf a xπ ha hga ≫ xπ =
      (chartUnion p j q g hf).ι ≫ π p q (coordinates j g) hf := by
  apply (Scheme.Opens.iSupOpenCover
    (fun i ↦ chart p j q g hf i)).hom_ext
  intro i
  change ι at i
  change ((obj p q (coordinates j g) hf).homOfLE
      (le_iSup (fun k ↦ chart p j q g hf k) i) ≫
        chartUnionToTarget p j q g hf a xπ ha hga) ≫ xπ =
    ((obj p q (coordinates j g) hf).homOfLE
      (le_iSup (fun k ↦ chart p j q g hf k) i) ≫
        (chartUnion p j q g hf).ι) ≫ π p q (coordinates j g) hf
  calc
    ((obj p q (coordinates j g) hf).homOfLE
        (le_iSup (fun k ↦ chart p j q g hf k) i) ≫
          chartUnionToTarget p j q g hf a xπ ha hga) ≫ xπ =
        chartToTarget p j q g hf a i ≫ xπ := by
      rw [homOfLE_chartUnionToTarget]
    _ = (chart p j q g hf i).ι ≫ π p q (coordinates j g) hf :=
      chartToTarget_comp p j q g hf a xπ ha i
    _ = ((obj p q (coordinates j g) hf).homOfLE
          (le_iSup (fun k ↦ chart p j q g hf k) i) ≫
            (chartUnion p j q g hf).ι) ≫
              π p q (coordinates j g) hf := by
      rw [Scheme.homOfLE_ι]

end

end AlgebraicGeometry.Scheme.FiniteProperClosure
