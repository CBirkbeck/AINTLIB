import ModularCurves.ForMathlib.FiniteProperClosure

/-!
# Charts in finite proper closures

This file constructs the inverse images of a compatible family of open charts in a finite proper
closure. It proves that the induced maps from these inverse-image charts to a separated target
agree on pairwise overlaps.
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

/-- The inverse image in the closure of the `i`-th open chart. -/
abbrev chart (i : ι) : (obj p q (coordinates j g) hf).Opens :=
  proj p q (coordinates j g) hf i ⁻¹ᵁ (j i).opensRange

/-- The projection from the inverse-image chart to its original affine chart. -/
def chartToFactor (i : ι) :
    (chart p j q g hf i).toScheme ⟶ U i :=
  IsOpenImmersion.lift (j i)
    ((chart p j q g hf i).ι ≫ proj p q (coordinates j g) hf i) (by
      rintro _ ⟨x, rfl⟩
      exact Scheme.Hom.mem_opensRange.mp x.2)

@[reassoc (attr := simp)]
lemma chartToFactor_comp (i : ι) :
    chartToFactor p j q g hf i ≫ j i =
      (chart p j q g hf i).ι ≫ proj p q (coordinates j g) hf i :=
  IsOpenImmersion.lift_fac _ _ _

/-- An inverse-image chart is the base change of its closure projection along the original
open immersion. -/
lemma chartToFactor_isPullback (i : ι) :
    IsPullback (chartToFactor p j q g hf i)
      (chart p j q g hf i).ι (j i)
      (proj p q (coordinates j g) hf i) := by
  apply IsOpenImmersion.isPullback
  · exact (chartToFactor_comp p j q g hf i).symm
  · rw [Scheme.Opens.opensRange_ι]

/-- Each inverse-image chart is proper over the corresponding original chart. -/
lemma chartToFactor_isProper (hp : ∀ i, IsProper (p i)) (i : ι) :
    IsProper (chartToFactor p j q g hf i) := by
  letI : IsProper (proj p q (coordinates j g) hf i) :=
    proj_isProper p q (coordinates j g) hf hp i
  exact MorphismProperty.of_isPullback
    (chartToFactor_isPullback p j q g hf i).flip inferInstance

variable (a : ∀ i, U i ⟶ X)

/-- The map from an inverse-image chart to the original scheme. -/
def chartToTarget (i : ι) : (chart p j q g hf i).toScheme ⟶ X :=
  chartToFactor p j q g hf i ≫ a i

variable (xπ : X ⟶ S)

@[reassoc]
lemma chartToTarget_comp (ha : ∀ i, a i ≫ xπ = j i ≫ p i) (i : ι) :
    chartToTarget p j q g hf a i ≫ xπ =
      (chart p j q g hf i).ι ≫ π p q (coordinates j g) hf := by
  calc
    chartToTarget p j q g hf a i ≫ xπ =
        chartToFactor p j q g hf i ≫ (a i ≫ xπ) := by
          simp only [chartToTarget, Category.assoc]
    _ = chartToFactor p j q g hf i ≫ (j i ≫ p i) := by rw [ha i]
    _ = (chartToFactor p j q g hf i ≫ j i) ≫ p i :=
      (Category.assoc _ _ _).symm
    _ = ((chart p j q g hf i).ι ≫
          proj p q (coordinates j g) hf i) ≫ p i := by
      rw [chartToFactor_comp]
    _ = (chart p j q g hf i).ι ≫
          (proj p q (coordinates j g) hf i ≫ p i) :=
      Category.assoc _ _ _
    _ = (chart p j q g hf i).ι ≫ π p q (coordinates j g) hf := by
      rw [proj_comp]

private abbrev chartOverlap (i k : ι) : (obj p q (coordinates j g) hf).Opens :=
  chart p j q g hf i ⊓ chart p j q g hf k

private def toChartOverlap (i k : ι) :
    T ⟶ (chartOverlap p j q g hf i k).toScheme :=
  IsOpenImmersion.lift (chartOverlap p j q g hf i k).ι
    (toClosure p q (coordinates j g) hf) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨toClosure p q (coordinates j g) hf x, ?_⟩, rfl⟩
      constructor
      · change (proj p q (coordinates j g) hf i)
          (toClosure p q (coordinates j g) hf x) ∈ (j i).opensRange
        exact Scheme.Hom.mem_opensRange.mpr ⟨g i x, by
          simpa only [Scheme.Hom.comp_apply] using
            congrArg (fun h : T ⟶ Z i ↦ h x)
              (toClosure_proj p q (coordinates j g) hf i).symm⟩
      · change (proj p q (coordinates j g) hf k)
          (toClosure p q (coordinates j g) hf x) ∈ (j k).opensRange
        exact Scheme.Hom.mem_opensRange.mpr ⟨g k x, by
          simpa only [Scheme.Hom.comp_apply] using
            congrArg (fun h : T ⟶ Z k ↦ h x)
              (toClosure_proj p q (coordinates j g) hf k).symm⟩)

@[reassoc (attr := simp)]
private lemma toChartOverlap_ι (i k : ι) :
    toChartOverlap p j q g hf i k ≫ (chartOverlap p j q g hf i k).ι =
      toClosure p q (coordinates j g) hf :=
  IsOpenImmersion.lift_fac _ _ _

private lemma toChartOverlap_isSchemeTheoreticallyDominant
    [QuasiCompact (diagonal p q (coordinates j g) hf)] (i k : ι) :
    IsSchemeTheoreticallyDominant (toChartOverlap p j q g hf i k) := by
  letI : IsSchemeTheoreticallyDominant (toClosure p q (coordinates j g) hf) :=
    toClosure_isSchemeTheoreticallyDominant p q (coordinates j g) hf
  exact IsSchemeTheoreticallyDominant.lift_of_isOpenImmersion
    (toClosure p q (coordinates j g) hf)
    (chartOverlap p j q g hf i k).ι _

private lemma toChartOverlap_toFactor_left (i k : ι) :
    toChartOverlap p j q g hf i k ≫
        (obj p q (coordinates j g) hf).homOfLE inf_le_left ≫
          chartToFactor p j q g hf i = g i := by
  rw [← cancel_mono (j i)]
  calc
    (toChartOverlap p j q g hf i k ≫
          (obj p q (coordinates j g) hf).homOfLE inf_le_left ≫
            chartToFactor p j q g hf i) ≫ j i =
        toChartOverlap p j q g hf i k ≫
          (obj p q (coordinates j g) hf).homOfLE inf_le_left ≫
            (chartToFactor p j q g hf i ≫ j i) := by
      simp only [Category.assoc]
    _ = toChartOverlap p j q g hf i k ≫
          (obj p q (coordinates j g) hf).homOfLE inf_le_left ≫
            ((chart p j q g hf i).ι ≫
              proj p q (coordinates j g) hf i) := by
      rw [chartToFactor_comp]
    _ = toChartOverlap p j q g hf i k ≫
          (((obj p q (coordinates j g) hf).homOfLE inf_le_left ≫
              (chart p j q g hf i).ι) ≫
                proj p q (coordinates j g) hf i) := by
      simp only [Category.assoc]
    _ = toChartOverlap p j q g hf i k ≫
          ((chartOverlap p j q g hf i k).ι ≫
            proj p q (coordinates j g) hf i) := by
      rw [Scheme.homOfLE_ι]
    _ = (toChartOverlap p j q g hf i k ≫
          (chartOverlap p j q g hf i k).ι) ≫
            proj p q (coordinates j g) hf i :=
      (Category.assoc _ _ _).symm
    _ = toClosure p q (coordinates j g) hf ≫
          proj p q (coordinates j g) hf i := by
      rw [toChartOverlap_ι]
    _ = g i ≫ j i := toClosure_proj p q (coordinates j g) hf i

private lemma toChartOverlap_toFactor_right (i k : ι) :
    toChartOverlap p j q g hf i k ≫
        (obj p q (coordinates j g) hf).homOfLE inf_le_right ≫
          chartToFactor p j q g hf k = g k := by
  rw [← cancel_mono (j k)]
  calc
    (toChartOverlap p j q g hf i k ≫
          (obj p q (coordinates j g) hf).homOfLE inf_le_right ≫
            chartToFactor p j q g hf k) ≫ j k =
        toChartOverlap p j q g hf i k ≫
          (obj p q (coordinates j g) hf).homOfLE inf_le_right ≫
            (chartToFactor p j q g hf k ≫ j k) := by
      simp only [Category.assoc]
    _ = toChartOverlap p j q g hf i k ≫
          (obj p q (coordinates j g) hf).homOfLE inf_le_right ≫
            ((chart p j q g hf k).ι ≫
              proj p q (coordinates j g) hf k) := by
      rw [chartToFactor_comp]
    _ = toChartOverlap p j q g hf i k ≫
          (((obj p q (coordinates j g) hf).homOfLE inf_le_right ≫
              (chart p j q g hf k).ι) ≫
                proj p q (coordinates j g) hf k) := by
      simp only [Category.assoc]
    _ = toChartOverlap p j q g hf i k ≫
          ((chartOverlap p j q g hf i k).ι ≫
            proj p q (coordinates j g) hf k) := by
      rw [Scheme.homOfLE_ι]
    _ = (toChartOverlap p j q g hf i k ≫
          (chartOverlap p j q g hf i k).ι) ≫
            proj p q (coordinates j g) hf k :=
      (Category.assoc _ _ _).symm
    _ = toClosure p q (coordinates j g) hf ≫
          proj p q (coordinates j g) hf k := by
      rw [toChartOverlap_ι]
    _ = g k ≫ j k := toClosure_proj p q (coordinates j g) hf k

private lemma toChartOverlap_chartToTarget_left (i k : ι) :
    toChartOverlap p j q g hf i k ≫
        (obj p q (coordinates j g) hf).homOfLE inf_le_left ≫
          chartToTarget p j q g hf a i = g i ≫ a i := by
  simpa only [chartToTarget, Category.assoc] using congrArg (fun h ↦ h ≫ a i)
    (toChartOverlap_toFactor_left p j q g hf i k)

private lemma toChartOverlap_chartToTarget_right (i k : ι) :
    toChartOverlap p j q g hf i k ≫
        (obj p q (coordinates j g) hf).homOfLE inf_le_right ≫
          chartToTarget p j q g hf a k = g k ≫ a k := by
  simpa only [chartToTarget, Category.assoc] using congrArg (fun h ↦ h ≫ a k)
    (toChartOverlap_toFactor_right p j q g hf i k)

/-- The maps from two inverse-image charts to a separated target agree on their overlap. -/
lemma chartToTarget_agree [IsSeparated xπ]
    [QuasiCompact (diagonal p q (coordinates j g) hf)]
    (ha : ∀ i, a i ≫ xπ = j i ≫ p i)
    (hga : ∀ i k, g i ≫ a i = g k ≫ a k) (i k : ι) :
    (obj p q (coordinates j g) hf).homOfLE inf_le_left ≫
        chartToTarget p j q g hf a i =
      (obj p q (coordinates j g) hf).homOfLE inf_le_right ≫
        chartToTarget p j q g hf a k := by
  letI : IsSchemeTheoreticallyDominant
      (toChartOverlap p j q g hf i k) :=
    toChartOverlap_isSchemeTheoreticallyDominant p j q g hf i k
  apply ext_of_isSchemeTheoreticallyDominant_of_isSeparated xπ
    (ι := toChartOverlap p j q g hf i k)
  · calc
      ((obj p q (coordinates j g) hf).homOfLE inf_le_left ≫
          chartToTarget p j q g hf a i) ≫ xπ =
          (obj p q (coordinates j g) hf).homOfLE inf_le_left ≫
            (chartToTarget p j q g hf a i ≫ xπ) :=
        Category.assoc _ _ _
      _ = (obj p q (coordinates j g) hf).homOfLE inf_le_left ≫
            ((chart p j q g hf i).ι ≫
              π p q (coordinates j g) hf) := by
        rw [chartToTarget_comp p j q g hf a xπ ha i]
      _ = ((obj p q (coordinates j g) hf).homOfLE inf_le_left ≫
            (chart p j q g hf i).ι) ≫
              π p q (coordinates j g) hf :=
        (Category.assoc _ _ _).symm
      _ = (chartOverlap p j q g hf i k).ι ≫
            π p q (coordinates j g) hf := by
        rw [Scheme.homOfLE_ι]
      _ = ((obj p q (coordinates j g) hf).homOfLE inf_le_right ≫
            (chart p j q g hf k).ι) ≫
              π p q (coordinates j g) hf := by
        rw [Scheme.homOfLE_ι]
      _ = (obj p q (coordinates j g) hf).homOfLE inf_le_right ≫
            ((chart p j q g hf k).ι ≫
              π p q (coordinates j g) hf) :=
        Category.assoc _ _ _
      _ = (obj p q (coordinates j g) hf).homOfLE inf_le_right ≫
            (chartToTarget p j q g hf a k ≫ xπ) := by
        rw [chartToTarget_comp p j q g hf a xπ ha k]
      _ = ((obj p q (coordinates j g) hf).homOfLE inf_le_right ≫
            chartToTarget p j q g hf a k) ≫ xπ :=
        (Category.assoc _ _ _).symm
  · calc
      toChartOverlap p j q g hf i k ≫
          ((obj p q (coordinates j g) hf).homOfLE inf_le_left ≫
            chartToTarget p j q g hf a i) =
          (toChartOverlap p j q g hf i k ≫
            (obj p q (coordinates j g) hf).homOfLE inf_le_left) ≫
              chartToTarget p j q g hf a i :=
        (Category.assoc _ _ _).symm
      _ = g i ≫ a i :=
        toChartOverlap_chartToTarget_left p j q g hf a i k
      _ = g k ≫ a k := hga i k
      _ = (toChartOverlap p j q g hf i k ≫
            (obj p q (coordinates j g) hf).homOfLE inf_le_right) ≫
              chartToTarget p j q g hf a k :=
        (toChartOverlap_chartToTarget_right p j q g hf a i k).symm
      _ = toChartOverlap p j q g hf i k ≫
          ((obj p q (coordinates j g) hf).homOfLE inf_le_right ≫
            chartToTarget p j q g hf a k) :=
        Category.assoc _ _ _

end

end AlgebraicGeometry.Scheme.FiniteProperClosure
