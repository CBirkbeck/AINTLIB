/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.PVInfrastructure.GammaAnalysis
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.PVInfrastructure.RemainderAnalysis
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.PVInfrastructure.StepBounds

/-!
# PV Infrastructure: Annulus Bounds

Measure-theoretic and analytic bounds on annular regions around crossing points, used in
the dyadic PV convergence proof.

## Main Results

* `annulus_t_measure_bound`: the parameter `|t - t₀|` is controlled by `ε₁ / ‖L‖` on the
  gamma-annulus.
* `remainder_integral_bound_on_annulus`: the remainder integral over the gamma-annulus is
  `O(ε)`.
* `shell_vol_le`: volume of a shell where `‖L‖ * |t - t₀|` is `Δ`-close to a threshold `ε`.
* `annulus_symmDiff_measure_bound`: symmetric difference between the gamma-annulus and the
  linear-model annulus has measure `O(ε₁²)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

lemma annulus_t_measure_bound {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ} {ε₁ ε₂ δ₁ : ℝ} (hL : L ≠ 0)
    (hε₁_pos : 0 < ε₁)
    (h_lower : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₁ → ‖γ t - γ t₀‖ ≥ (‖L‖ / 2) * |t - t₀|)
    (h_localize : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₁ δ₁)
    (t : ℝ) (ht_ab : t ∈ Set.Icc a b) (ht_ne : t ≠ t₀) (_hγ_lower : ε₂ < ‖γ t - γ t₀‖)
    (hγ_upper : ‖γ t - γ t₀‖ ≤ ε₁) :
    |t - t₀| ≤ 2 * ε₁ / ‖L‖ :=
  t_bound_from_gamma_annulus hL hε₁_pos h_lower t (abs_pos.mpr (sub_ne_zero.mpr ht_ne))
    (lt_of_lt_of_le (h_localize t ht_ab hγ_upper) (min_le_right _ _)) hγ_upper

private lemma remainder_annulus_zero_of_far {γ : ℝ → ℂ} {a b t₀ : ℝ} {δ₁ ε₁ ε₂ : ℝ} {L : ℂ}
    (hL : L ≠ 0) (hε₁_pos : 0 < ε₁) (hε₂_pos : 0 < ε₂)
    (h_lower : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₁ → ‖γ t - γ t₀‖ ≥ (‖L‖ / 2) * |t - t₀|)
    (h_localize : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₁ δ₁) (hab : a < b)
    {r : ℝ → ℂ} (t : ℝ) (ht : t ∈ Set.uIoc a b) (h_far : 2 * ε₁ / ‖L‖ < |t - t₀|) :
    (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0) = 0 := by
  by_cases hcond : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
  · exfalso
    have ht_in_Icc : t ∈ Set.Icc a b := by
      rw [Set.uIoc_eq_union] at ht
      rcases ht with ht_ab | ht_ba
      · exact Set.Ioc_subset_Icc_self ht_ab
      · rw [Set.Ioc_eq_empty_of_le hab.le] at ht_ba
        exact absurd ht_ba (Set.notMem_empty t)
    by_cases ht_eq : t = t₀
    · simp only [ht_eq, sub_self, norm_zero] at hcond
      exact absurd hcond.1 (not_lt.mpr hε₂_pos.le)
    exact not_lt.mpr
      (annulus_t_measure_bound hL hε₁_pos h_lower
        (fun s hs hγs ↦ by
          simpa only [min_self] using (h_localize s hs hγs).trans_le (min_le_right _ _))
        t ht_in_Icc ht_eq hcond.1 hcond.2) h_far
  · simp [hcond]

private lemma remainder_annulus_pw_bound {γ : ℝ → ℂ} {a b t₀ : ℝ} {C δ₀ δ₁ ε₁ ε₂ : ℝ}
    (hε₂_pos : 0 < ε₂)
    (hr_bounded : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₀ →
      ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ C)
    (h_localize : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₀ δ₁)
    (hab : a < b) (t : ℝ) (ht : t ∈ Set.uIoc a b) :
    ‖if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
      then (γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹
      else 0‖ ≤ max 0 C := by
  by_cases hcond : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
  · rw [if_pos hcond]
    have ht_in_Icc : t ∈ Set.Icc a b := by
      rw [Set.uIoc_eq_union] at ht
      rcases ht with h | h
      · exact Set.Ioc_subset_Icc_self h
      · exact absurd (Set.Ioc_eq_empty_of_le hab.le ▸ h) (Set.notMem_empty t)
    by_cases ht_eq : t = t₀
    · simp only [ht_eq, sub_self, norm_zero] at hcond
      exact absurd hcond.1 (not_lt.mpr hε₂_pos.le)
    exact (hr_bounded t (abs_pos.mpr (sub_ne_zero.mpr ht_eq))
      ((h_localize t ht_in_Icc hcond.2).trans_le (min_le_left _ _))).trans (le_max_right 0 C)
  · simp [hcond]

lemma remainder_integral_bound_on_annulus {γ : ℝ → ℂ} {a b t₀ : ℝ} {C δ₀ δ₁ ε₁ ε₂ : ℝ} {L : ℂ}
    (hL : L ≠ 0) (hε₁_pos : 0 < ε₁) (hε₂_pos : 0 < ε₂)
    (hr_bounded : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₀ →
      ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ C)
    (h_lower : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₁ → ‖γ t - γ t₀‖ ≥ (‖L‖ / 2) * |t - t₀|)
    (h_localize : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₀ δ₁)
    (hat₀ : t₀ ∈ Set.Ioo a b) :
    let r := fun t ↦ (γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹
    ‖∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0‖ ≤
      max 0 C * (4 * ε₁ / ‖L‖) := by
  intro r
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hab : a < b := (Set.mem_Ioo.mp hat₀).1.trans_le (Set.mem_Ioo.mp hat₀).2.le
  have h_loc_δ₁ : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₁ δ₁ := fun s hs hγs ↦ by
    simpa only [min_self] using (h_localize s hs hγs).trans_le (min_le_right _ _)
  set R := 2 * ε₁ / ‖L‖
  have hR_pos : 0 < R := by positivity
  set Icontain := Set.Icc (t₀ - R) (t₀ + R)
  set g_comp : ℝ → ℝ := Icontain.indicator (fun _ ↦ max 0 C)
  have hg_int : IntervalIntegrable g_comp volume a b := by
    constructor <;>
      exact (MeasureTheory.integrableOn_const
        (hs := measure_Ioc_lt_top.ne)).indicator measurableSet_Icc
  have h_pw_le : ∀ᵐ t ∂volume, t ∈ Set.Ioc a b →
      ‖if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
        then r t else 0‖ ≤ g_comp t := by
    refine Filter.Eventually.of_forall fun t ht ↦ ?_
    simp only [g_comp, Set.indicator]
    by_cases ht_in : t ∈ Icontain
    · simp only [ht_in, ↓reduceIte]
      exact remainder_annulus_pw_bound hε₂_pos hr_bounded h_localize hab
        t (Set.uIoc_of_le hab.le ▸ ht)
    · simp only [ht_in, ↓reduceIte]
      have h_far : R < |t - t₀| := by
        simp only [Icontain, Set.mem_Icc, not_and_or, not_le] at ht_in
        rcases ht_in with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [remainder_annulus_zero_of_far hL hε₁_pos hε₂_pos h_lower h_loc_δ₁ hab
        t (Set.uIoc_of_le hab.le ▸ ht) h_far, norm_zero]
  calc ‖∫ t in a..b,
      if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
        then r t else 0‖
      ≤ ∫ t in a..b, g_comp t :=
        intervalIntegral.norm_integral_le_of_norm_le hab.le h_pw_le hg_int
    _ ≤ max 0 C * (4 * ε₁ / ‖L‖) := by
        rw [intervalIntegral.integral_of_le hab.le,
          MeasureTheory.integral_indicator measurableSet_Icc,
          MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ (le_max_left 0 C)
        unfold MeasureTheory.Measure.real
        refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
        calc (volume.restrict (Set.Ioc a b)) Icontain
            ≤ volume Icontain := MeasureTheory.Measure.restrict_apply_le _ _
          _ = ENNReal.ofReal ((t₀ + R) - (t₀ - R)) := Real.volume_Icc
          _ = ENNReal.ofReal (4 * ε₁ / ‖L‖) := by simp only [R]; ring_nf

private lemma norm_linear_approx_bound {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} {K₀ δ₀ : ℝ}
    (h_quad : ∀ t, |t - t₀| < δ₀ → ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ K₀ * |t - t₀|^2)
    {t : ℝ} (ht : |t - t₀| < δ₀) :
    abs (‖γ t - γ t₀‖ - ‖L‖ * |t - t₀|) ≤ K₀ * |t - t₀|^2 := by
  have h2 := abs_norm_sub_norm_le (γ t - γ t₀) ((t - t₀) • L)
  rw [norm_smul (t - t₀) L, mul_comm] at h2
  exact h2.trans (h_quad t ht)

private lemma volume_shell_le {t₀ r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) :
    volume {t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} ≤ ENNReal.ofReal (2 * (r₂ - r₁)) := by
  have h_sub : {t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} ⊆
      Set.Ico (t₀ - r₂) (t₀ - r₁) ∪ Set.Ioc (t₀ + r₁) (t₀ + r₂) := by
    intro t ⟨h_lower, h_upper⟩
    by_cases ht : t ≥ t₀
    · rw [abs_of_nonneg (sub_nonneg.mpr ht)] at h_lower h_upper
      exact Or.inr ⟨by linarith, by linarith⟩
    · push Not at ht
      rw [abs_of_neg (sub_neg.mpr ht)] at h_lower h_upper
      exact Or.inl ⟨by linarith, by linarith⟩
  calc volume {t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂}
      ≤ volume (Set.Ico (t₀ - r₂) (t₀ - r₁) ∪ Set.Ioc (t₀ + r₁) (t₀ + r₂)) :=
        MeasureTheory.measure_mono h_sub
    _ ≤ volume (Set.Ico (t₀ - r₂) (t₀ - r₁)) + volume (Set.Ioc (t₀ + r₁) (t₀ + r₂)) :=
        MeasureTheory.measure_union_le _ _
    _ = ENNReal.ofReal (r₂ - r₁) + ENNReal.ofReal (r₂ - r₁) := by
        simp only [Real.volume_Ico, Real.volume_Ioc]; ring_nf
    _ = ENNReal.ofReal (2 * (r₂ - r₁)) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf

private lemma symmDiff_subset_boundaryLayers {g x e ε₁ ε₂ : ℝ} (h_approx : |g - x| ≤ e)
    (h_xor : Xor (ε₂ < g ∧ g ≤ ε₁) (ε₂ < x ∧ x ≤ ε₁)) :
    |x - ε₂| ≤ e ∨ |x - ε₁| ≤ e := by
  have h_abs := abs_le.mp h_approx
  rcases h_xor with ⟨⟨hg_lo, hg_hi⟩, hnotB⟩ | ⟨⟨hx_lo, hx_hi⟩, hnotA⟩
  · by_cases hx_le_ε₂ : x ≤ ε₂
    · exact Or.inl (abs_le.mpr ⟨by linarith, by linarith⟩)
    · push Not at hx_le_ε₂
      have : ε₁ < x := lt_of_not_ge fun h ↦ hnotB ⟨hx_le_ε₂, h⟩
      exact Or.inr (abs_le.mpr ⟨by linarith, by linarith⟩)
  · by_cases hg_le_ε₂ : g ≤ ε₂
    · exact Or.inl (abs_le.mpr ⟨by linarith, by linarith⟩)
    · push Not at hg_le_ε₂
      have : ε₁ < g := lt_of_not_ge fun h ↦ hnotA ⟨hg_le_ε₂, h⟩
      exact Or.inr (abs_le.mpr ⟨by linarith, by linarith⟩)

private lemma shell_vol_le_of_small_eps {t₀ ε Δ L_norm : ℝ}
    (hL_pos : 0 < L_norm) (_hΔ_nonneg : 0 ≤ Δ) (h : ε ≤ Δ) :
    volume {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ} ≤
      ENNReal.ofReal (4 * Δ / L_norm) := by
  have h_sub : {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ} ⊆
      {t : ℝ | |t - t₀| ≤ (ε + Δ) / L_norm} := by
    intro t ht
    simp only [Set.mem_setOf_eq] at ht ⊢
    calc |t - t₀| = (L_norm * |t - t₀|) / L_norm := by field_simp
      _ ≤ (ε + Δ) / L_norm := div_le_div_of_nonneg_right
          (by linarith [(abs_le.mp ht).2]) hL_pos.le
  calc volume {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ}
      ≤ volume {t : ℝ | |t - t₀| ≤ (ε + Δ) / L_norm} :=
        MeasureTheory.measure_mono h_sub
    _ = volume (Set.Icc (t₀ - (ε + Δ) / L_norm) (t₀ + (ε + Δ) / L_norm)) := by
        congr 1
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
        constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
    _ = ENNReal.ofReal (2 * (ε + Δ) / L_norm) := by rw [Real.volume_Icc]; ring_nf
    _ ≤ ENNReal.ofReal (4 * Δ / L_norm) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc 2 * (ε + Δ) / L_norm ≤ 2 * (2 * Δ) / L_norm :=
              div_le_div_of_nonneg_right (by linarith) hL_pos.le
          _ = 4 * Δ / L_norm := by ring

private lemma volume_abs_eq_null {t₀ r₁ : ℝ} (hr₁_pos : 0 < r₁) :
    volume {t : ℝ | |t - t₀| = r₁} = 0 := by
  have h_sub : {t : ℝ | |t - t₀| = r₁} ⊆ {t₀ - r₁, t₀ + r₁} := fun t ht ↦ by
    simp only [Set.mem_setOf_eq] at ht
    rcases (abs_eq hr₁_pos.le).mp ht with h1 | h1
    · exact Or.inr (by simp; linarith)
    · exact Or.inl (by linarith)
  exact measure_mono_null h_sub ((Set.toFinite _).measure_zero volume)

private lemma shell_vol_le_of_large_eps {t₀ ε Δ L_norm : ℝ}
    (hL_pos : 0 < L_norm) (hΔ_nonneg : 0 ≤ Δ) (h : Δ < ε) :
    volume {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ} ≤
      ENNReal.ofReal (4 * Δ / L_norm) := by
  let r₁ := (ε - Δ) / L_norm
  let r₂ := (ε + Δ) / L_norm
  have hr₁_pos : 0 < r₁ := div_pos (by linarith) hL_pos
  have hr₁_le_r₂ : r₁ ≤ r₂ :=
    div_le_div_of_nonneg_right (by linarith) hL_pos.le
  have h_sub : {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ} ⊆
      {t : ℝ | r₁ ≤ |t - t₀| ∧ |t - t₀| ≤ r₂} := by
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    have h_abs := abs_le.mp ht
    exact ⟨by calc r₁ = (ε - Δ) / L_norm := rfl
              _ ≤ (L_norm * |t - t₀|) / L_norm :=
                  div_le_div_of_nonneg_right (by linarith [h_abs.1]) hL_pos.le
              _ = |t - t₀| := by field_simp,
           by calc |t - t₀| = (L_norm * |t - t₀|) / L_norm := by field_simp
              _ ≤ (ε + Δ) / L_norm :=
                  div_le_div_of_nonneg_right (by linarith [h_abs.2]) hL_pos.le⟩
  calc volume {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ}
      ≤ volume {t : ℝ | r₁ ≤ |t - t₀| ∧ |t - t₀| ≤ r₂} :=
        MeasureTheory.measure_mono h_sub
    _ ≤ volume ({t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} ∪ {t : ℝ | |t - t₀| = r₁}) :=
        MeasureTheory.measure_mono (fun t ⟨h1, h2⟩ ↦ by
          by_cases heq : |t - t₀| = r₁
          · exact Or.inr heq
          · exact Or.inl ⟨lt_of_le_of_ne h1 (Ne.symm heq), h2⟩)
    _ ≤ volume {t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} +
        volume {t : ℝ | |t - t₀| = r₁} := MeasureTheory.measure_union_le _ _
    _ = volume {t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} := by
        rw [volume_abs_eq_null hr₁_pos, add_zero]
    _ ≤ ENNReal.ofReal (2 * (r₂ - r₁)) := volume_shell_le hr₁_le_r₂
    _ = ENNReal.ofReal (4 * Δ / L_norm) := by
        congr 1
        simp only [r₁, r₂]; field_simp; ring

lemma shell_vol_le {t₀ ε Δ L_norm : ℝ} (hL_pos : 0 < L_norm) (hΔ_nonneg : 0 ≤ Δ)
    (_hε_pos : 0 < ε) :
    volume {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ} ≤ ENNReal.ofReal (4 * Δ / L_norm) := by
  by_cases h : ε ≤ Δ
  · exact shell_vol_le_of_small_eps hL_pos hΔ_nonneg h
  · exact shell_vol_le_of_large_eps hL_pos hΔ_nonneg (not_le.mp h)

lemma annulus_symmDiff_measure_bound {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ} (_hab : a < b)
    (_ht₀ : t₀ ∈ Set.Ioo a b) (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L)
    (hL : L ≠ 0) :
    ∃ K > 0, ∃ δ₀' > 0, ∃ δ > 0, ∀ ε₁ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ ε₁ → ε₁ < δ →
    let γAnn := {t : ℝ | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
      ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁}
    let tAnnLin := {t : ℝ | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
      ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁}
    volume (symmDiff γAnn tAnnLin) ≤ ENNReal.ofReal (K * ε₁^2 / ‖L‖^3) := by
  obtain ⟨K₀, δ₀, hδ₀_pos, hK₀_pos, h_quad⟩ :=
    quadratic_approx_of_contDiffAt_two hγ_C2 hγ_deriv
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  let δ₁ := min δ₀ (‖L‖ / (4 * K₀))
  have hδ₁_pos : 0 < δ₁ := lt_min hδ₀_pos (div_pos hL_norm_pos (by linarith))
  have hδ₁_le_δ₀ : δ₁ ≤ δ₀ := min_le_left _ _
  have hδ₁_le_L_over_2K : δ₁ ≤ ‖L‖ / (2 * K₀) :=
    (min_le_right _ _).trans <| by
      refine div_le_div_of_nonneg_left hL_norm_pos.le (by linarith) ?_
      linarith
  let δ := ‖L‖ * δ₁ / 2
  have hδ_pos : 0 < δ := by simp only [δ]; positivity
  refine ⟨32 * K₀, by linarith, δ₁, hδ₁_pos, δ, hδ_pos, ?_⟩
  intro ε₁ ε₂ hε₂_pos hε₂_le hε₁_lt γAnn tAnnLin
  have hε₁_pos : 0 < ε₁ := hε₂_pos.trans_le hε₂_le
  have hK₀_nonneg : 0 ≤ K₀ := hK₀_pos.le
  have h_lower_bound : ∀ t, |t - t₀| < δ₁ → ‖γ t - γ t₀‖ ≥ ‖L‖ / 2 * |t - t₀| := by
    intro t ht_lt
    have h_approx := h_quad t (ht_lt.trans_le hδ₁_le_δ₀)
    have h_smul_norm : ‖(t - t₀) • L‖ = |t - t₀| * ‖L‖ := norm_smul (t - t₀) L
    have h_tri := abs_le.mp (abs_norm_sub_norm_le (γ t - γ t₀) ((t - t₀) • L))
    have hKt_lt : K₀ * |t - t₀| < ‖L‖ / 2 := by
      have h4b : K₀ * |t - t₀| < K₀ * (‖L‖ / (2 * K₀)) :=
        mul_lt_mul_of_pos_left (ht_lt.trans_le hδ₁_le_L_over_2K) hK₀_pos
      have h4c : K₀ * (‖L‖ / (2 * K₀)) = ‖L‖ / 2 := by field_simp
      linarith
    nlinarith [abs_nonneg (t - t₀), sq_abs (t - t₀), sq_nonneg (t - t₀)]
  have h_localize_γAnn : ∀ t, t ∈ γAnn → |t - t₀| < δ₁ := fun _ ⟨_, h, _, _⟩ ↦ h
  have h_localize_tAnnLin : ∀ t, t ∈ tAnnLin → |t - t₀| < δ₁ := fun _ ⟨_, h, _, _⟩ ↦ h
  let R_max := 2 * ε₁ / ‖L‖
  let Δ := K₀ * R_max^2
  have hΔ_nonneg : 0 ≤ Δ := mul_nonneg hK₀_nonneg (sq_nonneg _)
  let g : ℝ → ℝ := fun t ↦ ‖γ t - γ t₀‖
  let x : ℝ → ℝ := fun t ↦ ‖L‖ * |t - t₀|
  let e : ℝ → ℝ := fun t ↦ K₀ * |t - t₀|^2
  let shell₁ := {t : ℝ | |x t - ε₁| ≤ Δ}
  let shell₂ := {t : ℝ | |x t - ε₂| ≤ Δ}
  have h_subset : symmDiff γAnn tAnnLin ⊆ shell₁ ∪ shell₂ := by
    intro t ht
    rw [Set.mem_symmDiff] at ht
    have hxor : Xor (t ∈ γAnn) (t ∈ tAnnLin) := ht
    have ht_localized : |t - t₀| < δ₁ := by
      rcases hxor with ⟨ht_γAnn, _⟩ | ⟨ht_tAnn, _⟩
      · exact h_localize_γAnn t ht_γAnn
      · exact h_localize_tAnnLin t ht_tAnn
    have ht_lt_δ₀ : |t - t₀| < δ₀ := ht_localized.trans_le (min_le_left _ _)
    have h_gx_bound : |g t - x t| ≤ e t := by
      convert norm_linear_approx_bound h_quad ht_lt_δ₀ using 2
    have ht_Icc : t ∈ Set.Icc a b := by
      rcases hxor with ⟨⟨ht_Icc, _, _, _⟩, _⟩ | ⟨⟨ht_Icc, _, _, _⟩, _⟩ <;> exact ht_Icc
    have hxor' : Xor (ε₂ < g t ∧ g t ≤ ε₁) (ε₂ < x t ∧ x t ≤ ε₁) := by
      rcases hxor with ⟨⟨_, _, hγ_lo, hγ_hi⟩, hnotB⟩ | ⟨⟨_, _, ht_lo, ht_hi⟩, hnotA⟩
      · exact Or.inl ⟨⟨hγ_lo, hγ_hi⟩,
          fun ⟨h1, h2⟩ ↦ hnotB ⟨ht_Icc, ht_localized, h1, h2⟩⟩
      · exact Or.inr ⟨⟨ht_lo, ht_hi⟩,
          fun ⟨h1, h2⟩ ↦ hnotA ⟨ht_Icc, ht_localized, h1, h2⟩⟩
    have hR_bound : |t - t₀| ≤ R_max := by
      simp only [R_max]
      rcases hxor with ⟨ht_γAnn, _⟩ | ⟨ht_tAnn, _⟩
      · have h_lb := h_lower_bound t ht_localized
        have ⟨_, _, _, ht_upper⟩ := ht_γAnn
        have h1 : ‖L‖ / 2 * |t - t₀| ≤ ε₁ := h_lb.trans ht_upper
        rw [le_div_iff₀ hL_norm_pos]
        nlinarith [abs_nonneg (t - t₀)]
      · have ⟨_, _, _, ht_upper⟩ := ht_tAnn
        rw [le_div_iff₀ hL_norm_pos]
        nlinarith [hL_norm_pos.le, abs_nonneg (t - t₀)]
    have he_le_Δ : e t ≤ Δ := by
      simp only [e, Δ, R_max]
      exact mul_le_mul_of_nonneg_left
        (sq_le_sq' (by linarith [abs_nonneg (t - t₀)]) hR_bound) hK₀_nonneg
    rcases symmDiff_subset_boundaryLayers h_gx_bound hxor' with h_near₂ | h_near₁
    · exact Or.inr (h_near₂.trans he_le_Δ)
    · exact Or.inl (h_near₁.trans he_le_Δ)
  have h_shell₁_vol : volume shell₁ ≤ ENNReal.ofReal (4 * Δ / ‖L‖) :=
    shell_vol_le hL_norm_pos hΔ_nonneg hε₁_pos
  have h_shell₂_vol : volume shell₂ ≤ ENNReal.ofReal (4 * Δ / ‖L‖) :=
    shell_vol_le hL_norm_pos hΔ_nonneg hε₂_pos
  calc volume (symmDiff γAnn tAnnLin)
      ≤ volume (shell₁ ∪ shell₂) := MeasureTheory.measure_mono h_subset
    _ ≤ volume shell₁ + volume shell₂ := MeasureTheory.measure_union_le _ _
    _ ≤ ENNReal.ofReal (4 * Δ / ‖L‖) + ENNReal.ofReal (4 * Δ / ‖L‖) :=
        add_le_add h_shell₁_vol h_shell₂_vol
    _ = ENNReal.ofReal (4 * Δ / ‖L‖ + 4 * Δ / ‖L‖) := by
        rw [← ENNReal.ofReal_add] <;> positivity
    _ = ENNReal.ofReal (32 * K₀ * ε₁^2 / ‖L‖^3) := by
        congr 1
        simp only [Δ, R_max]; field_simp; ring

end
