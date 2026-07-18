/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue.MeasureHelpers
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue

/-!
# Multi-point principal value: measurability and integrability

Measurability and integrability lemmas for the multi-point Cauchy principal value
integrand. Includes the AE-strong-measurability of the cutout integrand on the
"good set" `{t : ∀ s ∈ S, ε < ‖γ t - s‖}`, a domination-by-bound integrability
helper, and a dominated-convergence wrapper specialised to the PV setting.

## Main results

* `aEStronglyMeasurable_of_continuousOn_off_finite` — continuous-off-finite ⇒ AE strongly
  measurable on `Icc a b`.
* `aEStronglyMeasurable_pv_integrand_decomposed` — AE strong measurability for the
  decomposed (regular + residue) cutout integrand.
* `integrableOn_of_bounded_aeMeasurable` — bounded + AE measurable ⇒ integrable on `Icc a b`.
* `tendsto_integral_of_dominated'` — dominated convergence specialised to right
  filters of `ε ↘ 0`.
* `intervalIntegrable_residueTerm` — interval integrability of a single residue term.
* `aEStronglyMeasurable_pv_sum_residue` — measurability of the residue sum integrand.

The dominated-convergence helpers used downstream
(`dominated_convergence_multipoint_helper`, `multipointPV_diff_tendsto`,
`multipointPV_eq_sum_of_integral_zero`) live in
`LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue.MultipointPV.DominatedConvergence`.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

private lemma measurableSet_norm_gt_of_continuousOn {f : ℝ → ℂ} {s : Set ℝ} (ε : ℝ)
    (hf : ContinuousOn f s) (hs : MeasurableSet s) :
    MeasurableSet ({t | ε < ‖f t‖} ∩ s) := by
  obtain ⟨U, hU_open, hU_eq⟩ := isOpen_induced_iff.mp
    (isOpen_Ioi.preimage hf.norm.restrict)
  have h_eq : {t | ε < ‖f t‖} ∩ s = U ∩ s := by
    ext x
    refine ⟨fun ⟨hx_far, hx_s⟩ ↦ ⟨?_, hx_s⟩, fun ⟨hx_U, hx_s⟩ ↦ ⟨?_, hx_s⟩⟩
    · have h1 : (⟨x, hx_s⟩ : ↑s) ∈ (s.restrict (fun t ↦ ‖f t‖)) ⁻¹' Set.Ioi ε := hx_far
      rw [← hU_eq] at h1; exact h1
    · have h1 : (⟨x, hx_s⟩ : ↑s) ∈ Subtype.val ⁻¹' U := hx_U
      rw [hU_eq] at h1; exact h1
  rw [h_eq]
  exact hU_open.measurableSet.inter hs

private lemma measurableSet_norm_gt_Icc {f : ℝ → ℂ} {a b : ℝ} (ε : ℝ)
    (hf : ContinuousOn f (Icc a b)) :
    MeasurableSet ({t | ε < ‖f t‖} ∩ Icc a b) :=
  measurableSet_norm_gt_of_continuousOn ε hf isClosed_Icc.measurableSet

/-- A function continuous off a finite set is a.e. strongly measurable on `Icc a b`. -/
theorem aEStronglyMeasurable_of_continuousOn_off_finite {f : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ}
    (hf_cont : ContinuousOn f (Icc a b \ P)) :
    AEStronglyMeasurable f (volume.restrict (Icc a b)) := by
  have hP_meas_zero : volume (↑P ∩ Icc a b) = 0 :=
    (P.finite_toSet.inter_of_left (Icc a b)).measure_zero volume
  have h_disj : Disjoint (Icc a b \ P) (↑P ∩ Icc a b) :=
    Set.disjoint_left.mpr fun _ ⟨_, hx_nP⟩ ⟨hx_P, _⟩ ↦ hx_nP hx_P
  have h_eq : volume.restrict (Icc a b) =
      volume.restrict (Icc a b \ P) + volume.restrict (↑P ∩ Icc a b) := by
    rw [← Measure.restrict_union h_disj
      (P.finite_toSet.measurableSet.inter isClosed_Icc.measurableSet)]
    congr 1; ext x; simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]; tauto
  rw [h_eq]
  apply AEStronglyMeasurable.add_measure
    (hf_cont.aestronglyMeasurable
      (isClosed_Icc.measurableSet.diff P.finite_toSet.measurableSet))
  simp only [Measure.restrict_eq_zero.mpr hP_meas_zero]
  exact aestronglyMeasurable_zero_measure f

private lemma measurableSet_multipoint_condition {γ : ℝ → ℂ} {a b ε : ℝ} (S : Finset ℂ)
    (hγ : ContinuousOn γ (Icc a b)) :
    MeasurableSet ({t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} ∩ Icc a b) := by
  have h_eq : {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} ∩ Icc a b =
      ⋃ s ∈ S, ({t | ‖γ t - s‖ ≤ ε} ∩ Icc a b) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    tauto
  rw [h_eq]
  refine Finset.measurableSet_biUnion _ fun s _ ↦ ?_
  have h_eq' : {t | ‖γ t - s‖ ≤ ε} ∩ Icc a b =
      Icc a b \ ({t | ε < ‖γ t - s‖} ∩ Icc a b) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_sdiff, not_and]
    refine ⟨fun ⟨h_le, h_Icc⟩ ↦ ⟨h_Icc, fun h_gt _ ↦ absurd h_gt (not_lt.mpr h_le)⟩,
      fun ⟨h_Icc, h⟩ ↦ ⟨not_lt.mp fun h_gt ↦ h h_gt h_Icc, h_Icc⟩⟩
  rw [h_eq']
  exact isClosed_Icc.measurableSet.diff
    (measurableSet_norm_gt_Icc ε (hγ.sub continuousOn_const))

private lemma measurableSet_multipoint_goodset {γ : ℝ → ℂ} {a b ε : ℝ} (S : Finset ℂ)
    (hγ : ContinuousOn γ (Icc a b)) :
    MeasurableSet ({t | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b) := by
  have h_eq : {t | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b =
      Icc a b \ ({t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} ∩ Icc a b) := by
    ext t
    refine ⟨fun ⟨h_good, ht_Icc⟩ ↦
      ⟨ht_Icc, fun ⟨⟨s, hs, h_le⟩, _⟩ ↦ by linarith [h_good s hs]⟩,
      fun ⟨ht_Icc, h_not⟩ ↦ ⟨fun s hs ↦ ?_, ht_Icc⟩⟩
    by_contra h_le
    push Not at h_le
    exact h_not ⟨⟨s, hs, h_le⟩, ht_Icc⟩
  rw [h_eq]
  exact isClosed_Icc.measurableSet.diff (measurableSet_multipoint_condition S hγ)

private lemma aEStronglyMeasurable_residueProd_on_goodset {γ : ℝ → ℂ} {a b ε : ℝ}
    {P : Finset ℝ} {s c : ℂ} (hε : 0 < ε) (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) :
    AEStronglyMeasurable (fun t ↦ (c / (γ t - s)) * deriv γ t)
      (volume.restrict ({t : ℝ | ε < ‖γ t - s‖} ∩ Icc a b)) := by
  have h_ratio : AEStronglyMeasurable (fun t ↦ c / (γ t - s))
      (volume.restrict ({t : ℝ | ε < ‖γ t - s‖} ∩ Icc a b)) :=
    ((continuousOn_const.div ((hγ.mono Set.inter_subset_right).sub continuousOn_const)
      fun t ⟨ht_good, _⟩ ↦ norm_ne_zero_iff.mp
        (ne_of_gt (lt_trans hε ht_good)))).aestronglyMeasurable
      (measurableSet_norm_gt_Icc ε (hγ.sub continuousOn_const))
  exact h_ratio.mul ((aEStronglyMeasurable_of_continuousOn_off_finite
    hγ'_off_P).mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))

private theorem aEStronglyMeasurable_pv_integrand_residue {γ : ℝ → ℂ} {a b ε : ℝ}
    {P : Finset ℝ} {s c : ℂ} (hε : 0 < ε) (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) :
    AEStronglyMeasurable (fun t ↦ if ‖γ t - s‖ > ε then (c / (γ t - s)) * deriv γ t
      else 0) (volume.restrict (Icc a b)) := by
  have hGoodSet_meas : MeasurableSet ({t | ε < ‖γ t - s‖} ∩ Icc a b) :=
    measurableSet_norm_gt_Icc ε (hγ.sub continuousOn_const)
  have h_zero_meas : AEStronglyMeasurable (fun _ : ℝ ↦ (0 : ℂ))
      (volume.restrict ({t : ℝ | ε < ‖γ t - s‖} ∩ Icc a b)ᶜ) := aestronglyMeasurable_const
  have h_prod_meas : AEStronglyMeasurable (fun t ↦ (c / (γ t - s)) * deriv γ t)
      (volume.restrict ({t | ε < ‖γ t - s‖} ∩ Icc a b)) :=
    aEStronglyMeasurable_residueProd_on_goodset hε hγ hγ'_off_P
  refine ((AEStronglyMeasurable.piecewise hGoodSet_meas h_prod_meas
    h_zero_meas).mono_measure Measure.restrict_le_self).congr ?_
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
  simp only [Set.piecewise, Set.mem_inter_iff, Set.mem_setOf_eq, gt_iff_lt]
  by_cases h1 : ε < ‖γ t - s‖
  · simp only [h1, ht, and_self, ↓reduceIte]
  · simp only [h1, ht, false_and, ↓reduceIte]

private lemma aEStronglyMeasurable_singularSum_on_goodset {γ : ℝ → ℂ} {a b ε : ℝ}
    (S : Finset ℂ) (coeffs : ℂ → ℂ) (hε : 0 < ε) (hγ : ContinuousOn γ (Icc a b)) :
    AEStronglyMeasurable (fun t ↦ ∑ s ∈ S, coeffs s / (γ t - s))
      (volume.restrict ({t : ℝ | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b)) :=
  Finset.aestronglyMeasurable_fun_sum S fun s hs ↦
    (continuousOn_const.div ((hγ.mono Set.inter_subset_right).sub continuousOn_const)
      fun _ ⟨ht_good, _⟩ ↦ norm_ne_zero_iff.mp
        (ne_of_gt (lt_trans hε (ht_good s hs)))).aestronglyMeasurable
      (measurableSet_multipoint_goodset S hγ)

private lemma aEStronglyMeasurable_decomposed_on_goodset {g_reg : ℂ → ℂ} {γ : ℝ → ℂ}
    {a b ε : ℝ} {P : Finset ℝ} (S : Finset ℂ) (coeffs : ℂ → ℂ) (hε : 0 < ε)
    (hg : ContinuousOn g_reg (γ '' Icc a b)) (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) :
    AEStronglyMeasurable (fun t ↦ (g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s)) * deriv γ t)
      (volume.restrict ({t : ℝ | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b)) := by
  have hgγ_meas : AEStronglyMeasurable (fun t ↦ g_reg (γ t)) (volume.restrict (Icc a b)) :=
    (hg.comp hγ fun _ ↦ Set.mem_image_of_mem _).aestronglyMeasurable
      isClosed_Icc.measurableSet
  have h_f_meas := (hgγ_meas.mono_measure
    (Measure.restrict_mono Set.inter_subset_right le_rfl)).add
    (aEStronglyMeasurable_singularSum_on_goodset S coeffs hε hγ)
  exact h_f_meas.mul ((aEStronglyMeasurable_of_continuousOn_off_finite
    hγ'_off_P).mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))

private lemma goodset_piecewise_ae_eq_decomposed {g_reg : ℂ → ℂ} {γ : ℝ → ℂ} {a b ε : ℝ}
    (S : Finset ℂ) (coeffs : ℂ → ℂ) :
    (fun t ↦ if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0
      else (g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s)) * deriv γ t)
      =ᵐ[volume.restrict (Icc a b)]
    ({t : ℝ | ∀ s ∈ S, ε < ‖γ t - s‖} ∩ Icc a b).piecewise
      (fun t ↦ (g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s)) * deriv γ t)
      (fun _ ↦ 0) := by
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
  simp only [Set.piecewise, Set.mem_inter_iff, Set.mem_setOf_eq]
  by_cases ht_good : (∀ s ∈ S, ε < ‖γ t - s‖) ∧ t ∈ Icc a b
  · have : ¬∃ s ∈ S, ‖γ t - s‖ ≤ ε := by push Not; exact ht_good.1
    rw [if_pos ht_good]; simp only [this, if_false]
  · have : ∃ s ∈ S, ‖γ t - s‖ ≤ ε := by
      by_contra h_not; push Not at h_not; exact ht_good ⟨h_not, ht⟩
    rw [if_neg ht_good]; simp only [this, if_true]

theorem aEStronglyMeasurable_pv_integrand_decomposed {g_reg : ℂ → ℂ} {γ : ℝ → ℂ}
    {a b ε : ℝ} {P : Finset ℝ} (S : Finset ℂ) (coeffs : ℂ → ℂ) (hε : 0 < ε)
    (hg : ContinuousOn g_reg (γ '' Icc a b)) (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) :
    AEStronglyMeasurable (fun t ↦ if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0
      else (g_reg (γ t) + ∑ s ∈ S, coeffs s / (γ t - s)) * deriv γ t)
      (volume.restrict (Icc a b)) :=
  ((AEStronglyMeasurable.piecewise (measurableSet_multipoint_goodset S hγ)
    (aEStronglyMeasurable_decomposed_on_goodset S coeffs hε hg hγ hγ'_off_P)
    aestronglyMeasurable_const).mono_measure Measure.restrict_le_self).congr
    (goodset_piecewise_ae_eq_decomposed S coeffs).symm

theorem integrableOn_of_bounded_aeMeasurable {f : ℝ → ℂ} {a b : ℝ} (M : ℝ)
    (hf_meas : AEStronglyMeasurable f (volume.restrict (Icc a b)))
    (hf_bound : ∀ x ∈ Icc a b, ‖f x‖ ≤ M) :
    IntegrableOn f (Icc a b) volume := by
  apply IntegrableOn.of_bound measure_Icc_lt_top hf_meas (max M 0)
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with x hx
  calc ‖f x‖ ≤ M := hf_bound x hx
    _ ≤ max M 0 := le_max_left M 0

theorem tendsto_integral_of_dominated' {a b : ℝ} {F : ℝ → ℝ → ℂ} {f : ℝ → ℂ} {g : ℝ → ℝ}
    (hF_meas : ∀ ε > 0, AEStronglyMeasurable (F ε) (volume.restrict (Ι a b)))
    (hF_le : ∀ ε > 0, ∀ᵐ t ∂volume, t ∈ Ι a b → ‖F ε t‖ ≤ g t)
    (hg_int : IntervalIntegrable g volume a b)
    (hF_lim : ∀ᵐ t ∂volume, t ∈ Ι a b →
      Tendsto (fun ε ↦ F ε t) (𝓝[>] 0) (𝓝 (f t))) :
    Tendsto (fun ε ↦ ∫ t in a..b, F ε t) (𝓝[>] 0) (𝓝 (∫ t in a..b, f t)) :=
  intervalIntegral.tendsto_integral_filter_of_dominated_convergence g
    (by filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε); exact hF_meas ε hε)
    (by filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε); exact hF_le ε hε)
    hg_int hF_lim

/-- Continuous functions on a compact image are bounded. -/
lemma continuousOn_image_bounded {g : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hγ_cont : ContinuousOn γ (Icc a b)) (hg_cont : ContinuousOn g (γ '' Icc a b)) :
    ∃ Mg : ℝ, ∀ z ∈ γ '' Icc a b, ‖g z‖ ≤ Mg :=
  (isCompact_Icc.image_of_continuousOn hγ_cont).exists_bound_of_continuousOn hg_cont

private lemma piecewiseC1Immersion_deriv_continuousOn_off_partition (γ : PiecewiseC1Immersion) :
    ContinuousOn (deriv γ.toFun) (Icc γ.a γ.b \ γ.partition) := by
  intro t ⟨ht_Icc, ht_notP⟩
  by_cases ht_Ioo : t ∈ Ioo γ.a γ.b
  · exact (γ.toPiecewiseC1Curve.deriv_continuous_off_partition
      t ht_Ioo ht_notP).continuousWithinAt
  · simp only [Set.mem_Ioo, not_and, not_lt] at ht_Ioo
    rcases ht_Icc.1.lt_or_eq with h | h
    · exact absurd (le_antisymm ht_Icc.2 (ht_Ioo h) ▸
        γ.toPiecewiseC1Curve.endpoints_in_partition.2) ht_notP
    · exact absurd (h ▸ γ.toPiecewiseC1Curve.endpoints_in_partition.1) ht_notP

/-- Residue term integrand is interval integrable. -/
lemma intervalIntegrable_residueTerm {γ : PiecewiseC1Immersion} {s c : ℂ} {ε : ℝ}
    (hε : 0 < ε) :
    IntervalIntegrable
      (fun t ↦ if ‖γ.toFun t - s‖ > ε then (c / (γ.toFun t - s)) * deriv γ.toFun t else 0)
      volume γ.a γ.b := by
  obtain ⟨Mγ', hMγ'⟩ := piecewiseC1Immersion_deriv_bounded γ
  let M := ‖c‖ / ε * |Mγ'| + 1
  have h_bound : ∀ t ∈ Icc γ.a γ.b,
      ‖if ‖γ.toFun t - s‖ > ε then (c / (γ.toFun t - s)) * deriv γ.toFun t else 0‖ ≤ M := by
    intro t ht
    split_ifs with h
    · calc ‖(c / (γ.toFun t - s)) * deriv γ.toFun t‖
          = ‖c / (γ.toFun t - s)‖ * ‖deriv γ.toFun t‖ := norm_mul _ _
        _ ≤ (‖c‖ / ε) * |Mγ'| := mul_le_mul
              (by rw [norm_div]
                  exact div_le_div_of_nonneg_left (norm_nonneg c) hε h.le)
              ((hMγ' t ht).trans (le_abs_self _)) (norm_nonneg _) (by positivity)
        _ ≤ M := by simp only [M]; linarith
    · simp only [norm_zero, M]; positivity
  have h_meas : AEStronglyMeasurable
      (fun t ↦ if ‖γ.toFun t - s‖ > ε then (c / (γ.toFun t - s)) * deriv γ.toFun t else 0)
      (volume.restrict (Icc γ.a γ.b)) :=
    aEStronglyMeasurable_pv_integrand_residue hε γ.toPiecewiseC1Curve.continuous_toFun
      (piecewiseC1Immersion_deriv_continuousOn_off_partition γ)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le γ.hab.le]
  exact (integrableOn_of_bounded_aeMeasurable M h_meas h_bound).mono_set Ioc_subset_Icc_self

lemma aEStronglyMeasurable_pv_sum_residue (S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (ε : ℝ) (hε : 0 < ε) (a b : ℝ) {P : Finset ℝ} (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) (Icc a b \ P)) :
    AEStronglyMeasurable
      (fun t ↦ ∑ s ∈ S, if ‖γ t - s‖ > ε
        then residueSimplePole f s / (γ t - s) * deriv γ t else 0)
      (volume.restrict (Icc a b)) := by
  induction S using Finset.induction_on with
  | empty => exact aestronglyMeasurable_const
  | @insert x S' hx ih =>
    refine (AEStronglyMeasurable.add (aEStronglyMeasurable_pv_integrand_residue
      (s := x) (c := residueSimplePole f x) hε hγ_cont hγ'_off_P) ih).congr ?_
    refine ae_of_all _ (fun t ↦ ?_)
    simp only [Pi.add_apply, Finset.sum_insert hx]

end
