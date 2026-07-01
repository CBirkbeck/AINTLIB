/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.PVInfrastructure.AnnulusBounds

/-!
# PV Infrastructure: Singular Annulus Bounds

Bounds on singular annular integrals, including the linearized model,
symmetric cancellation, measurability, and the explicit epsilon-independent
bound used in the dyadic PV convergence proof.

## Main Results

* `singular_annulus_bound_explicit` — epsilon-independent bound on singular integral
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

private lemma norm_annulus_condition_iff {t₀ : ℝ} {L : ℂ} {ε₁ ε₂ : ℝ} (hL_pos : 0 < ‖L‖) (t : ℝ) :
    (ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁) ↔
    (ε₂ / ‖L‖ < |t - t₀| ∧ |t - t₀| ≤ ε₁ / ‖L‖) := by
  rw [div_lt_iff₀ hL_pos, le_div_iff₀ hL_pos, mul_comm ‖L‖]

private lemma intervalIntegral_eq_zero_of_ae_eq_zero {a b : ℝ} {φ : ℝ → ℂ}
    (h_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → φ t = 0) :
    ∫ t in a..b, φ t = 0 :=
  (intervalIntegral.integral_congr_ae (by
    filter_upwards [h_ae] with t ht ht_mem; exact ht ht_mem)).trans
    intervalIntegral.integral_zero

private lemma integral_split_five {a p₁ p₂ p₃ p₄ b : ℝ}
    {φ : ℝ → ℂ}
    (h₁ : IntervalIntegrable φ volume a p₁)
    (h₂ : IntervalIntegrable φ volume p₁ p₂)
    (h₃ : IntervalIntegrable φ volume p₂ p₃)
    (h₄ : IntervalIntegrable φ volume p₃ p₄)
    (h₅ : IntervalIntegrable φ volume p₄ b) :
    ∫ t in a..b, φ t =
      (∫ t in a..p₁, φ t) + (∫ t in p₁..p₂, φ t) +
      (∫ t in p₂..p₃, φ t) + (∫ t in p₃..p₄, φ t) +
      (∫ t in p₄..b, φ t) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (h₁.trans h₂ |>.trans h₃ |>.trans h₄) h₅,
      ← intervalIntegral.integral_add_adjacent_intervals (h₁.trans h₂ |>.trans h₃) h₄,
      ← intervalIntegral.integral_add_adjacent_intervals (h₁.trans h₂) h₃,
      ← intervalIntegral.integral_add_adjacent_intervals h₁ h₂]

private lemma singular_tAnnLin_cancel (t₀ : ℝ) {L : ℂ} (hL_pos : 0 < ‖L‖) (ε₁ ε₂ : ℝ)
    (hε₂_pos : 0 < ε₂) (hε₂_le : ε₂ ≤ ε₁) :
    let c₁ := ε₂ / ‖L‖
    let c₂ := ε₁ / ‖L‖
    (∫ t in (t₀ - c₂)..(t₀ - c₁), (↑(t - t₀) : ℂ)⁻¹) +
      (∫ t in (t₀ + c₁)..(t₀ + c₂), (↑(t - t₀) : ℂ)⁻¹) = 0 :=
  integral_inv_symm t₀ _ _ (div_pos hε₂_pos hL_pos)
    (div_pos (hε₂_pos.trans_le hε₂_le) hL_pos)
    (div_le_div_of_nonneg_right hε₂_le hL_pos.le)

private lemma singular_symmDiff_sup_bound {t₀ c : ℝ} (hc_pos : 0 < c) {t : ℝ}
    (ht_lower : c ≤ |t - t₀|) :
    ‖(↑(t - t₀) : ℂ)⁻¹‖ ≤ 1 / c := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, one_div]
  exact inv_anti₀ hc_pos ht_lower

private lemma measurableSet_Lmul_annulus {t₀ : ℝ} {L : ℂ} {ε₁ ε₂ : ℝ} :
    MeasurableSet {t : ℝ | ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁} :=
  .inter (isOpen_lt continuous_const (continuous_const.mul
      (continuous_abs.comp (continuous_id.sub continuous_const)))).measurableSet
    (isClosed_le (continuous_const.mul
      (continuous_abs.comp (continuous_id.sub continuous_const)))
      continuous_const).measurableSet

private lemma singular_annulus_f_lin_measurable {t₀ : ℝ} {L : ℂ} {ε₁ ε₂ : ℝ} :
    Measurable (fun t : ℝ ↦
      if ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁
      then (↑(t - t₀) : ℂ)⁻¹ else 0) := by
  refine Measurable.ite measurableSet_Lmul_annulus ?_ measurable_const
  exact (Complex.measurable_ofReal.comp (measurable_id.sub_const t₀)).inv

private lemma singular_annulus_f_lin_bound {t₀ : ℝ} {L : ℂ} {ε₁ ε₂ : ℝ}
    (hL_pos : 0 < ‖L‖) (hε₂_pos : 0 < ε₂) (t : ℝ) :
    ‖(if ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁
      then (↑(t - t₀) : ℂ)⁻¹ else (0 : ℂ))‖ ≤ 2 * ‖L‖ / ε₂ := by
  by_cases hcond : ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁
  · rw [if_pos hcond]
    have hlo : ε₂ / (2 * ‖L‖) ≤ |t - t₀| := by
      calc ε₂ / (2 * ‖L‖)
          ≤ ε₂ / ‖L‖ := (div_lt_div_of_pos_left hε₂_pos hL_pos (by linarith)).le
        _ ≤ |t - t₀| := by rw [div_le_iff₀ hL_pos, mul_comm]; exact hcond.1.le
    exact (singular_symmDiff_sup_bound (by positivity) hlo).trans
      (by rw [one_div, inv_div])
  · simp only [hcond, ite_false, norm_zero]; positivity

private lemma singular_annulus_f_lin_intervalIntegrable {t₀ : ℝ} {L : ℂ} {ε₁ ε₂ : ℝ}
    (hL_pos : 0 < ‖L‖) (hε₂_pos : 0 < ε₂) (u v : ℝ) :
    IntervalIntegrable (fun t ↦
      if ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁
      then (↑(t - t₀) : ℂ)⁻¹ else 0) volume u v := by
  rw [intervalIntegrable_iff]
  exact .of_bound measure_Ioc_lt_top
    singular_annulus_f_lin_measurable.aestronglyMeasurable.restrict (2 * ‖L‖ / ε₂)
    (.of_forall (singular_annulus_f_lin_bound hL_pos hε₂_pos))

private lemma lin_indicator_zero_left {a t₀ c₁ c₂ : ℝ} (hc₂_nonneg : 0 ≤ c₂)
    (ha_lt_mc₂ : a < t₀ - c₂) {φ : ℝ → ℂ}
    (hφ_zero : ∀ t, ¬(c₁ < |t - t₀| ∧ |t - t₀| ≤ c₂) → φ t = 0) :
    ∫ t in a..(t₀ - c₂), φ t = 0 :=
  intervalIntegral_eq_zero_of_ae_eq_zero (by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
      (MeasureTheory.measure_singleton (t₀ - c₂))] with t ht_ne ht_mem
    rw [Set.uIoc_of_le ha_lt_mc₂.le] at ht_mem
    exact hφ_zero t (fun ⟨_, hle⟩ ↦ absurd hle
      (not_le.mpr (by
        rw [abs_of_nonpos (by linarith [ht_mem.2] : t - t₀ ≤ 0)]
        linarith [lt_of_le_of_ne ht_mem.2 ht_ne]))))

private lemma lin_indicator_zero_right {t₀ c₁ c₂ b : ℝ} (hc₂_nonneg : 0 ≤ c₂)
    (hpc₂_lt_b : t₀ + c₂ < b) {φ : ℝ → ℂ}
    (hφ_zero : ∀ t, ¬(c₁ < |t - t₀| ∧ |t - t₀| ≤ c₂) → φ t = 0) :
    ∫ t in (t₀ + c₂)..b, φ t = 0 :=
  intervalIntegral_eq_zero_of_ae_eq_zero (by
    filter_upwards with t ht_mem
    rw [Set.uIoc_of_le hpc₂_lt_b.le] at ht_mem
    exact hφ_zero t (fun ⟨_, hle⟩ ↦ absurd hle
      (not_le.mpr (by
        rw [abs_of_nonneg (by linarith [ht_mem.1] : 0 ≤ t - t₀)]
        linarith [ht_mem.1]))))

private lemma lin_indicator_zero_middle {t₀ c₁ c₂ : ℝ}
    (hmc₁_le_pc₁ : t₀ - c₁ ≤ t₀ + c₁) {φ : ℝ → ℂ}
    (hφ_zero : ∀ t, ¬(c₁ < |t - t₀| ∧ |t - t₀| ≤ c₂) → φ t = 0) :
    ∫ t in (t₀ - c₁)..(t₀ + c₁), φ t = 0 :=
  (intervalIntegral.integral_congr (fun t ht ↦ by
    rw [Set.uIcc_of_le hmc₁_le_pc₁] at ht
    exact hφ_zero t (fun ⟨hgt, _⟩ ↦ absurd
      (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (not_le.mpr hgt)))).trans intervalIntegral.integral_zero

private lemma lin_indicator_eq_inv_left {t₀ c₁ c₂ : ℝ} (hc₁_nonneg : 0 ≤ c₁)
    (hmc₂_le_mc₁ : t₀ - c₂ ≤ t₀ - c₁) {φ : ℝ → ℂ}
    (hφ_val : ∀ t, c₁ < |t - t₀| ∧ |t - t₀| ≤ c₂ → φ t = (↑(t - t₀) : ℂ)⁻¹) :
    ∫ t in (t₀ - c₂)..(t₀ - c₁), φ t =
    ∫ t in (t₀ - c₂)..(t₀ - c₁), (↑(t - t₀) : ℂ)⁻¹ := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
    (MeasureTheory.measure_singleton (t₀ - c₁))] with t ht_ne ht_mem
  rw [Set.uIoc_of_le hmc₂_le_mc₁] at ht_mem
  have h_np : t - t₀ ≤ 0 := by linarith [ht_mem.2]
  exact hφ_val t
    ⟨by rw [abs_of_nonpos h_np]; linarith [lt_of_le_of_ne ht_mem.2 ht_ne],
     by rw [abs_of_nonpos h_np]; linarith [ht_mem.1]⟩

private lemma lin_indicator_eq_inv_right {t₀ c₁ c₂ : ℝ} (hc₁_nonneg : 0 ≤ c₁)
    (hpc₁_le_pc₂ : t₀ + c₁ ≤ t₀ + c₂) {φ : ℝ → ℂ}
    (hφ_val : ∀ t, c₁ < |t - t₀| ∧ |t - t₀| ≤ c₂ → φ t = (↑(t - t₀) : ℂ)⁻¹) :
    ∫ t in (t₀ + c₁)..(t₀ + c₂), φ t =
    ∫ t in (t₀ + c₁)..(t₀ + c₂), (↑(t - t₀) : ℂ)⁻¹ := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t ht_mem
  rw [Set.uIoc_of_le hpc₁_le_pc₂] at ht_mem
  have h_nn : 0 ≤ t - t₀ := by linarith [ht_mem.1]
  exact hφ_val t
    ⟨by rw [abs_of_nonneg h_nn]; linarith [ht_mem.1],
     by rw [abs_of_nonneg h_nn]; linarith [ht_mem.2]⟩

private lemma singular_annulus_lin_integral_zero {a b t₀ : ℝ} {L : ℂ} {ε₁ ε₂ : ℝ}
    (hL_pos : 0 < ‖L‖) (hε₂_pos : 0 < ε₂) (hε₂_le : ε₂ ≤ ε₁)
    (hε₁_lt_Ldist : ε₁ < ‖L‖ * min (t₀ - a) (b - t₀)) :
    (∫ t in a..b,
      if ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁
      then (↑(t - t₀) : ℂ)⁻¹ else 0) = 0 := by
  set c₁ := ε₂ / ‖L‖
  set c₂ := ε₁ / ‖L‖
  have hc₁_pos : 0 < c₁ := div_pos hε₂_pos hL_pos
  have hc₂_pos : 0 < c₂ := div_pos (hε₂_pos.trans_le hε₂_le) hL_pos
  have hc₁_le_c₂ : c₁ ≤ c₂ := div_le_div_of_nonneg_right hε₂_le hL_pos.le
  have hc₂_lt_dist : c₂ < min (t₀ - a) (b - t₀) := by
    rw [div_lt_iff₀ hL_pos]; linarith [mul_comm ‖L‖ (min (t₀ - a) (b - t₀))]
  set φ : ℝ → ℂ := fun t ↦
    if ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁
    then (↑(t - t₀) : ℂ)⁻¹ else 0
  have hφ_int := singular_annulus_f_lin_intervalIntegrable hL_pos hε₂_pos
    (ε₁ := ε₁) (t₀ := t₀)
  have h_cond_iff := norm_annulus_condition_iff hL_pos
    (ε₁ := ε₁) (ε₂ := ε₂) (t₀ := t₀)
  have hφ_zero : ∀ t, ¬(c₁ < |t - t₀| ∧ |t - t₀| ≤ c₂) → φ t = 0 :=
    fun t hnt ↦ if_neg (mt (h_cond_iff t).mp hnt)
  have hφ_val : ∀ t, c₁ < |t - t₀| ∧ |t - t₀| ≤ c₂ → φ t = (↑(t - t₀) : ℂ)⁻¹ :=
    fun t ht ↦ if_pos ((h_cond_iff t).mpr ht)
  have ha_lt_mc₂ : a < t₀ - c₂ := by linarith [hc₂_lt_dist.trans_le (min_le_left _ _)]
  have hpc₂_lt_b : t₀ + c₂ < b := by linarith [hc₂_lt_dist.trans_le (min_le_right _ _)]
  rw [integral_split_five (hφ_int a (t₀ - c₂)) (hφ_int (t₀ - c₂) (t₀ - c₁))
      (hφ_int (t₀ - c₁) (t₀ + c₁)) (hφ_int (t₀ + c₁) (t₀ + c₂)) (hφ_int (t₀ + c₂) b),
    lin_indicator_zero_left hc₂_pos.le ha_lt_mc₂ hφ_zero,
    lin_indicator_zero_right hc₂_pos.le hpc₂_lt_b hφ_zero,
    lin_indicator_zero_middle (by linarith : t₀ - c₁ ≤ t₀ + c₁) hφ_zero,
    lin_indicator_eq_inv_left hc₁_pos.le (by linarith : t₀ - c₂ ≤ t₀ - c₁) hφ_val,
    lin_indicator_eq_inv_right hc₁_pos.le (by linarith : t₀ + c₁ ≤ t₀ + c₂) hφ_val]
  simp only [zero_add, add_zero]
  exact singular_tAnnLin_cancel t₀ hL_pos ε₁ ε₂ hε₂_pos hε₂_le

private lemma singular_annulus_diff_pointwise_bound {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ}
    {ε₁ ε₂ : ℝ} {δ₁ δ_up : ℝ} (hL_pos : 0 < ‖L‖) (hε₂_pos : 0 < ε₂)
    (h_localize : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < δ₁)
    (hδ₁_le_δ_up : δ₁ ≤ δ_up)
    (h_upper : ∀ t, 0 < |t - t₀| → |t - t₀| < δ_up → ‖γ t - γ t₀‖ ≤ 2 * ‖L‖ * |t - t₀|)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ‖(if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0) -
     (if ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0)‖ ≤
    2 * ‖L‖ / ε₂ := by
  have hbound_pos : 0 < 2 * ‖L‖ / ε₂ := by positivity
  have h_sup : ∀ h_lo : ε₂ / (2 * ‖L‖) ≤ |t - t₀|,
      ‖(↑(t - t₀) : ℂ)⁻¹‖ ≤ 2 * ‖L‖ / ε₂ := fun h_lo ↦
    (singular_symmDiff_sup_bound (by positivity) h_lo).trans (by rw [one_div, inv_div])
  by_cases hγ : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ <;>
    by_cases hlin : ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁
  · simpa [hγ, hlin] using hbound_pos.le
  · simp only [hγ, hlin, ↓reduceIte, sub_zero]
    have ht_ne : t ≠ t₀ := fun heq ↦ by simp [heq] at hγ; linarith
    have ht_pos : 0 < |t - t₀| := abs_pos.mpr (sub_ne_zero.mpr ht_ne)
    refine h_sup (le_of_lt ?_)
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * ‖L‖)]
    linarith [h_upper t ht_pos ((h_localize t ht hγ.2).trans_le hδ₁_le_δ_up)]
  · simp only [hγ, hlin, ↓reduceIte, zero_sub, norm_neg]
    refine h_sup (le_of_lt ?_)
    calc ε₂ / (2 * ‖L‖)
        < ε₂ / ‖L‖ := div_lt_div_of_pos_left hε₂_pos hL_pos (by linarith)
      _ ≤ |t - t₀| := by rw [div_le_iff₀ hL_pos, mul_comm]; exact hlin.1.le
  · simpa [hγ, hlin] using hbound_pos.le

private lemma symmDiff_ae_version_null {γ : ℝ → ℂ} {a b t₀ : ℝ}
    {ε₁ ε₂ δ₀' : ℝ} {h' : ℝ → ℝ}
    (hh'_ae : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ‖γ t - γ t₀‖ = h' t) :
    volume (symmDiff
      {t | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧ ε₂ < h' t ∧ h' t ≤ ε₁}
      {t | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧ ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁}) = 0 := by
  have h_sd_subset : symmDiff
      {t | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧ ε₂ < h' t ∧ h' t ≤ ε₁}
      {t | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧ ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁} ⊆
      {t | t ∈ Set.Icc a b ∧ h' t ≠ ‖γ t - γ t₀‖} := by
    intro t ht
    simp only [Set.mem_symmDiff, Set.mem_setOf_eq] at ht ⊢
    rcases ht with ⟨h_in, h_not⟩ | ⟨h_in, h_not⟩
    · exact ⟨h_in.1, fun heq ↦ h_not ⟨h_in.1, h_in.2.1, heq ▸ h_in.2.2.1, heq ▸ h_in.2.2.2⟩⟩
    · exact ⟨h_in.1, fun heq ↦ h_not ⟨h_in.1, h_in.2.1,
        heq.symm ▸ h_in.2.2.1, heq.symm ▸ h_in.2.2.2⟩⟩
  have h_null : volume {t | t ∈ Set.Icc a b ∧ h' t ≠ ‖γ t - γ t₀‖} = 0 := by
    rw [show {t | t ∈ Set.Icc a b ∧ h' t ≠ ‖γ t - γ t₀‖} =
        {t | ¬(‖γ t - γ t₀‖ = h' t)} ∩ Set.Icc a b from by
      ext t
      simp [Set.mem_setOf_eq, eq_comm, and_comm],
      ← MeasureTheory.Measure.restrict_apply' measurableSet_Icc]
    exact MeasureTheory.ae_iff.mp hh'_ae
  exact measure_mono_null h_sd_subset h_null

private lemma singular_annulus_symmDiff_vol_via_ae
    {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ} {ε₁ ε₂ : ℝ} {δ₀' δ_meas Kmeas : ℝ}
    (hε₂_pos : 0 < ε₂) (hε₂_le : ε₂ ≤ ε₁) (hε₁_lt_δ_meas : ε₁ < δ_meas)
    (h_meas : ∀ ε₁' ε₂' : ℝ, 0 < ε₂' → ε₂' ≤ ε₁' → ε₁' < δ_meas →
      volume (symmDiff
        {t | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧ ε₂' < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁'}
        {t | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
          ε₂' < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁'}) ≤
        ENNReal.ofReal (Kmeas * ε₁' ^ 2 / ‖L‖ ^ 3))
    (h' : ℝ → ℝ) (hh'_ae : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), ‖γ t - γ t₀‖ = h' t) :
    volume (symmDiff
      {t | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧ ε₂ < h' t ∧ h' t ≤ ε₁}
      {t | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧ ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁}) ≤
    ENNReal.ofReal (Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3) := by
  refine (MeasureTheory.measure_symmDiff_le _
    {t | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧ ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁} _).trans ?_
  rw [symmDiff_ae_version_null hh'_ae, zero_add]
  exact h_meas ε₁ ε₂ hε₂_pos hε₂_le hε₁_lt_δ_meas

/-- Explicit `ε`-independent bound on the singular annular integral for `C²` curves with
nonzero derivative: the integral `∫ a..b (1[ε₂ < ‖γ t − γ t₀‖ ≤ ε₁]) · (t − t₀)⁻¹` is at most
`Csing · ε₁` for all sufficiently small `ε₁` with `ε₂ ≤ ε₁ ≤ 2 ε₂`. -/
lemma singular_annulus_bound_explicit {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ} (hab : a < b)
    (hat₀ : t₀ ∈ Set.Ioo a b) (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L)
    (hL : L ≠ 0) (hγ_cont : ContinuousOn γ (Set.Icc a b))
    (h_inj : ∀ t ∈ Set.Icc a b, γ t = γ t₀ → t = t₀) :
    ∃ Csing > 0, ∃ δ > 0, ∀ ε₁ ε₂ : ℝ,
    0 < ε₂ → ε₂ ≤ ε₁ → ε₁ ≤ 2 * ε₂ → ε₁ < δ →
    ‖∫ t in a..b,
      if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0‖ ≤
      Csing * ε₁ := by
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  obtain ⟨Kmeas, hKmeas_pos, δ₀', hδ₀'_pos, δ_meas, hδ_meas_pos, h_meas⟩ :=
    annulus_symmDiff_measure_bound hab hat₀ hγ_C2 hγ_deriv hL
  have hγ_hasderiv : HasDerivAt γ L t₀ :=
    hγ_deriv ▸ (hγ_C2.differentiableAt two_ne_zero).hasDerivAt
  obtain ⟨δ_lo, hδ_lo_pos, _⟩ := gamma_lower_bound_of_hasDerivAt hL hγ_hasderiv
  obtain ⟨δ_up, hδ_up_pos, h_upper⟩ := gamma_upper_bound_of_hasDerivAt hL hγ_hasderiv
  let δ₁ := min δ₀' (min δ_lo δ_up)
  have hδ₁_pos : 0 < δ₁ := lt_min hδ₀'_pos (lt_min hδ_lo_pos hδ_up_pos)
  obtain ⟨ρ, hρ_pos, h_far_bound⟩ :=
    no_return_of_inj_continuous hδ₁_pos hγ_cont h_inj
  have h_dist_pos : 0 < min (t₀ - a) (b - t₀) :=
    lt_min (sub_pos.mpr hat₀.1) (sub_pos.mpr hat₀.2)
  let δ := min (min δ_meas ρ) (min (‖L‖ * min (t₀ - a) (b - t₀)) (‖L‖ * δ₀'))
  have hδ_pos : 0 < δ :=
    lt_min (lt_min hδ_meas_pos hρ_pos)
      (lt_min (mul_pos hL_pos h_dist_pos) (mul_pos hL_pos hδ₀'_pos))
  let Csing := 4 * Kmeas / ‖L‖^2
  refine ⟨Csing, by positivity, δ, hδ_pos, fun ε₁ ε₂ hε₂_pos hε₂_le h_ratio hε₁_lt ↦ ?_⟩
  have hε₁_pos : 0 < ε₁ := hε₂_pos.trans_le hε₂_le
  have hε₁_lt_δ_meas : ε₁ < δ_meas :=
    (hε₁_lt.trans_le (min_le_left _ _)).trans_le (min_le_left _ _)
  have hε₁_lt_ρ : ε₁ < ρ :=
    (hε₁_lt.trans_le (min_le_left _ _)).trans_le (min_le_right _ _)
  have hε₁_lt_Ldist : ε₁ < ‖L‖ * min (t₀ - a) (b - t₀) :=
    (hε₁_lt.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hε₁_lt_Lδ₀' : ε₁ < ‖L‖ * δ₀' :=
    (hε₁_lt.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have h_localize : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < δ₁ := fun t ht hγt ↦ by
    by_contra h_not_lt
    push Not at h_not_lt
    linarith [h_far_bound t ht h_not_lt]
  have hJ_lin_zero :
      (∫ t in a..b,
        if ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁
        then (↑(t - t₀) : ℂ)⁻¹ else 0) = 0 :=
    singular_annulus_lin_integral_zero hL_pos hε₂_pos hε₂_le hε₁_lt_Ldist
  set f_γ : ℝ → ℂ := fun t ↦
    if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
    then (↑(t - t₀) : ℂ)⁻¹ else 0 with hf_γ_def
  set f_lin : ℝ → ℂ := fun t ↦
    if ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁
    then (↑(t - t₀) : ℂ)⁻¹ else 0 with hf_lin_def
  set d : ℝ → ℂ := fun t ↦ f_γ t - f_lin t with hd_def
  set bound := 2 * ‖L‖ / ε₂ with hbound_def
  have hbound_pos : 0 < bound := by positivity
  have hd_bound_on_Icc : ∀ t ∈ Set.Icc a b, ‖d t‖ ≤ bound := fun t ht ↦
    singular_annulus_diff_pointwise_bound hL_pos hε₂_pos h_localize
      ((min_le_right _ _).trans (min_le_right _ _)) h_upper t ht
  have hf_lin_meas : Measurable f_lin := singular_annulus_f_lin_measurable
  have hf_lin_bound : ∀ t : ℝ, ‖f_lin t‖ ≤ bound :=
    fun t ↦ singular_annulus_f_lin_bound hL_pos hε₂_pos t
  have hf_lin_int : IntervalIntegrable f_lin volume a b := by
    rw [intervalIntegrable_iff]
    exact .of_bound measure_Ioc_lt_top
      hf_lin_meas.aestronglyMeasurable.restrict bound (.of_forall hf_lin_bound)
  have hf_γ_eq : ∀ t, f_γ t = d t + f_lin t := fun _ ↦ by simp [d]
  have h_norm_aesm : AEStronglyMeasurable (fun t ↦ ‖γ t - γ t₀‖)
      (volume.restrict (Set.Icc a b)) :=
    ((hγ_cont.sub continuousOn_const).norm).aestronglyMeasurable measurableSet_Icc
  set h' := h_norm_aesm.mk (fun t ↦ ‖γ t - γ t₀‖) with hh'_def
  have hh'_sm : StronglyMeasurable h' := h_norm_aesm.stronglyMeasurable_mk
  have hh'_ae : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), ‖γ t - γ t₀‖ = h' t :=
    h_norm_aesm.ae_eq_mk
  set f_γ' : ℝ → ℂ := fun t ↦
    if ε₂ < h' t ∧ h' t ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0 with hf_γ'_def
  have hf_γ'_meas : Measurable f_γ' := by
    refine Measurable.ite (.inter ?_ ?_) ?_ measurable_const
    · exact hh'_sm.measurable measurableSet_Ioi
    · exact hh'_sm.measurable measurableSet_Iic
    · exact (Complex.measurable_ofReal.comp (measurable_id.sub_const t₀)).inv
  have hf_γ_ae_eq : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), f_γ t = f_γ' t := by
    filter_upwards [hh'_ae] with t ht_eq
    simp [f_γ, f_γ', ht_eq]
  have hf_γ_aesm : AEStronglyMeasurable f_γ (volume.restrict (Set.Ioc a b)) :=
    (hf_γ'_meas.aestronglyMeasurable.congr (Filter.EventuallyEq.symm hf_γ_ae_eq)).mono_measure
      (MeasureTheory.Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
  have hd_int : IntervalIntegrable d volume a b := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hab.le]
    exact .of_bound measure_Ioc_lt_top
      (hf_γ_aesm.sub hf_lin_meas.aestronglyMeasurable.restrict) bound
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
        (.of_forall fun t ht ↦ hd_bound_on_Icc t (Set.Ioc_subset_Icc_self ht)))
  rw [show (∫ t in a..b, f_γ t) = (∫ t in a..b, d t) + (∫ t in a..b, f_lin t) by
      rw [← intervalIntegral.integral_add hd_int hf_lin_int]
      exact intervalIntegral.integral_congr fun t _ ↦ hf_γ_eq t,
    hJ_lin_zero, add_zero, intervalIntegral.integral_of_le hab.le]
  set γAnn' := {t : ℝ | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧ ε₂ < h' t ∧ h' t ≤ ε₁}
  set tAnnLin_loc := {t : ℝ | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
    ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁}
  set S' := symmDiff γAnn' tAnnLin_loc with hS'_def
  have habs_meas : MeasurableSet {t : ℝ | |t - t₀| < δ₀'} :=
    (isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const))
      continuous_const).measurableSet
  have hLmul_meas : MeasurableSet
      {t : ℝ | ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁} :=
    measurableSet_Lmul_annulus
  have hγAnn'_meas : MeasurableSet γAnn' :=
    measurableSet_Icc.inter (habs_meas.inter ((hh'_sm.measurable measurableSet_Ioi).inter
      (hh'_sm.measurable measurableSet_Iic)))
  have htAnnLin_meas : MeasurableSet tAnnLin_loc :=
    measurableSet_Icc.inter (habs_meas.inter hLmul_meas)
  have hS'_meas : MeasurableSet S' := hγAnn'_meas.symmDiff htAnnLin_meas
  set d' : ℝ → ℂ := fun t ↦ f_γ' t - f_lin t with hd'_def
  have hd_ae_eq : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), d t = d' t := by
    filter_upwards [hf_γ_ae_eq] with t ht_eq; simp [d, d', ht_eq]
  rw [show (∫ t in Set.Ioc a b, d t ∂volume) = ∫ t in Set.Ioc a b, d' t ∂volume by
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioc
    filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hd_ae_eq]
      with t h_eq ht_Ioc
    exact h_eq (Set.Ioc_subset_Icc_self ht_Ioc)]
  set g_comp : ℝ → ℝ := S'.indicator (fun _ ↦ bound) with hg_comp_def
  have hS'_finite : volume S' < ⊤ :=
    (MeasureTheory.measure_mono (fun t ht ↦ by
      rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h.1 :
      S' ⊆ Set.Icc a b)).trans_lt measure_Icc_lt_top
  have hS'_vol_bound : volume S' ≤ ENNReal.ofReal (Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3) :=
    singular_annulus_symmDiff_vol_via_ae hε₂_pos hε₂_le hε₁_lt_δ_meas h_meas h' hh'_ae
  have hg_int_Ioc : Integrable g_comp (volume.restrict (Set.Ioc a b)) :=
    (MeasureTheory.integrableOn_const (hs := measure_Ioc_lt_top.ne)).indicator hS'_meas
  have h_pw_le_restrict : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖d' t‖ ≤ g_comp t := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, Filter.eventually_iff_exists_mem]
    refine ⟨{t | t ∈ Set.Icc a b → d t = d' t},
      (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hd_ae_eq, ?_⟩
    intro t ht ht_Ioc
    have ht_Icc := Set.Ioc_subset_Icc_self ht_Ioc
    simp only [g_comp, hg_comp_def, S', Set.indicator]
    by_cases ht_S : t ∈ symmDiff γAnn' tAnnLin_loc
    · simp only [ht_S, ↓reduceIte]; rw [← ht ht_Icc]; exact hd_bound_on_Icc t ht_Icc
    simp only [ht_S, ↓reduceIte]
    suffices h_dt_zero : d t = 0 by rw [(ht ht_Icc).symm, h_dt_zero, norm_zero]
    show f_γ t - f_lin t = 0
    have hfγ_eq : f_γ t = f_γ' t := sub_left_inj.mp (ht ht_Icc)
    by_cases hδ : |t - t₀| < δ₀'
    · have h_not_sd := ht_S
      rw [Set.mem_symmDiff] at h_not_sd
      push Not at h_not_sd
      have h'_iff_lin :
          (ε₂ < h' t ∧ h' t ≤ ε₁) ↔ (ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁) :=
        ⟨fun ⟨h1, h2⟩ ↦ (h_not_sd.1 ⟨ht_Icc, hδ, h1, h2⟩).2.2,
         fun ⟨h1, h2⟩ ↦ (h_not_sd.2 ⟨ht_Icc, hδ, h1, h2⟩).2.2⟩
      have h_agree :
          (ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁) ↔
          (ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁) := by
        by_cases ht_eq : t = t₀
        · subst ht_eq; simp
        have hinv_ne : (↑(t - t₀) : ℂ)⁻¹ ≠ 0 :=
          inv_ne_zero (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr ht_eq))
        refine ⟨fun hγ_cond ↦ ?_, fun hlin_cond ↦ ?_⟩
        · by_contra h_neg
          rw [show f_γ t = (↑(t - t₀) : ℂ)⁻¹ from if_pos hγ_cond,
            show f_γ' t = 0 from if_neg (mt h'_iff_lin.mp h_neg)] at hfγ_eq
          exact hinv_ne hfγ_eq
        · by_contra h_neg
          rw [show f_γ' t = (↑(t - t₀) : ℂ)⁻¹ from if_pos (h'_iff_lin.mpr hlin_cond),
            show f_γ t = 0 from if_neg h_neg] at hfγ_eq
          exact hinv_ne hfγ_eq.symm
      by_cases hcond : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
      · simp [f_γ, f_lin, hcond, h_agree.mp hcond]
      · simp [f_γ, f_lin, hcond, mt h_agree.mpr hcond]
    · have hγ_fail : ¬(ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁) :=
        fun ⟨_, h_up⟩ ↦ hδ ((h_localize t ht_Icc h_up).trans_le (min_le_left _ _))
      have hlin_fail : ¬(ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁) := fun ⟨_, h_le⟩ ↦ by
        linarith [mul_le_mul_of_nonneg_left (not_lt.mp hδ) hL_pos.le]
      simp [f_γ, f_lin, hγ_fail, hlin_fail]
  calc ‖∫ t in Set.Ioc a b, d' t‖
      ≤ ∫ t in Set.Ioc a b, g_comp t :=
        MeasureTheory.norm_integral_le_of_norm_le hg_int_Ioc h_pw_le_restrict
    _ = ∫ t in (Set.Ioc a b) ∩ S', (fun _ ↦ bound) t := by
        rw [MeasureTheory.setIntegral_indicator hS'_meas]
    _ = volume.real ((Set.Ioc a b) ∩ S') * bound := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul]
    _ ≤ volume.real S' * bound :=
        mul_le_mul_of_nonneg_right
          (measureReal_mono Set.inter_subset_right hS'_finite.ne) hbound_pos.le
    _ ≤ (Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3) * bound :=
        mul_le_mul_of_nonneg_right
          (ENNReal.toReal_le_of_le_ofReal (by positivity) hS'_vol_bound) hbound_pos.le
    _ ≤ Csing * ε₁ := by
        rw [show Csing * ε₁ = 4 * Kmeas * ε₁ / ‖L‖ ^ 2 by simp [Csing]; ring,
          show Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3 * bound = 2 * Kmeas * ε₁ ^ 2 * ‖L‖ / (‖L‖ ^ 3 * ε₂) by
            simp [bound]; ring,
          div_le_div_iff₀ (by positivity : (0:ℝ) < ‖L‖ ^ 3 * ε₂)
            (by positivity : (0:ℝ) < ‖L‖ ^ 2)]
        have key : ε₁ ^ 2 ≤ ε₁ * (2 * ε₂) := by
          rw [sq]; exact mul_le_mul_of_nonneg_left h_ratio hε₁_pos.le
        nlinarith [mul_pos hKmeas_pos (pow_pos hL_pos 3),
          show ‖L‖ ^ 3 = ‖L‖ * ‖L‖ ^ 2 from by ring]


end
