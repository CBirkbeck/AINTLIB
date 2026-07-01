/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# PV Infrastructure: Step Bounds

Building blocks for principal value convergence: integral cancellation, cutoff
integrand integrability, dyadic Cauchy criterion, geometric ε-bracketing, and
telescoping bounds.

## Main Results

* `integral_inv_symm` — symmetric cancellation of `1/(t - t₀)`
* `cutoff_integrand_intervalIntegrable` — integrability of cutoff
* `cutoff_diff_eq_annulus_integral` — difference equals annulus integral
* `cauchySeq_pv_dyadic` — dyadic sequence is Cauchy under summable step bounds
* `t_bound_from_gamma_annulus` — `t`-space radius bound from `γ`-annulus
* `exists_dyadic_bracket` — `ε` lies between two consecutive dyadic levels
* `telescoping_sum_bound` — accumulated bound from geometric step bounds
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Symmetric cancellation of 1/(t-t₀). -/
lemma integral_inv_symm (t₀ ε₁ ε₂ : ℝ) (_hε₁ : 0 < ε₁) (_hε₂ : 0 < ε₂) (_hε₁₂ : ε₁ ≤ ε₂) :
    (∫ t in (t₀ - ε₂)..(t₀ - ε₁), (↑(t - t₀) : ℂ)⁻¹) +
      (∫ t in (t₀ + ε₁)..(t₀ + ε₂), (↑(t - t₀) : ℂ)⁻¹) = 0 := by
  have h_odd : ∀ u : ℝ, (↑(-u) : ℂ)⁻¹ = -((↑u : ℂ)⁻¹) := by
    intro u
    simp only [ofReal_neg, neg_inv]
  have h_reflect : ∫ t in (t₀ - ε₂)..(t₀ - ε₁), (↑(t - t₀) : ℂ)⁻¹ =
      -(∫ t in (t₀ + ε₁)..(t₀ + ε₂), (↑(t - t₀) : ℂ)⁻¹) := by
    have h1 := intervalIntegral.integral_comp_sub_left
      (f := fun x ↦ (↑(x - t₀) : ℂ)⁻¹) (d := 2 * t₀) (a := t₀ + ε₁) (b := t₀ + ε₂)
    simp only [show 2 * t₀ - (t₀ + ε₂) = t₀ - ε₂ by ring,
      show 2 * t₀ - (t₀ + ε₁) = t₀ - ε₁ by ring,
      show ∀ x, 2 * t₀ - x - t₀ = -(x - t₀) from fun x ↦ by ring, h_odd] at h1
    rw [intervalIntegral.integral_neg] at h1
    exact h1.symm
  rw [h_reflect, neg_add_cancel]

/-- Cutoff integrand is interval integrable. -/
lemma cutoff_integrand_intervalIntegrable {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ}
    (hat₀ : t₀ ∈ Set.Ioo a b) (_hL : L ≠ 0) (hγ_meas : Measurable γ)
    (hγ_cont_deriv : ContinuousOn (deriv γ) (Set.Icc a b)) (ε : ℝ) (hε_pos : 0 < ε) :
    IntervalIntegrable
      (fun t ↦ if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0)
      MeasureTheory.volume a b := by
  have h_deriv_bdd : ∃ M > 0, ∀ t ∈ Set.Icc a b, ‖deriv γ t‖ ≤ M := by
    obtain ⟨x_max, _, hx_max⟩ := isCompact_Icc.exists_isMaxOn
      ⟨t₀, Set.Ioo_subset_Icc_self hat₀⟩ (continuous_norm.comp_continuousOn hγ_cont_deriv)
    exact ⟨max (‖deriv γ x_max‖) 1, lt_max_of_lt_right one_pos,
      fun t ht ↦ le_max_of_le_left (hx_max ht)⟩
  obtain ⟨M_deriv, hM_pos, hM_deriv⟩ := h_deriv_bdd
  have hM_bound_pos : 0 < M_deriv / ε := div_pos hM_pos hε_pos
  have h_norm_bound_ae : ∀ t ∈ Set.uIoc a b,
      ‖(if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0)‖ ≤ M_deriv / ε := by
    intro t ht_uIoc
    have ht : t ∈ Set.Icc a b := by
      rw [Set.uIoc_of_le (hat₀.1.trans hat₀.2).le] at ht_uIoc
      exact Set.Ioc_subset_Icc_self ht_uIoc
    by_cases h_in : ε < ‖γ t - γ t₀‖
    · simp only [h_in, ↓reduceIte]
      have h_bound : ‖(γ t - γ t₀)⁻¹‖ ≤ 1 / ε := by
        rw [norm_inv, one_div]
        exact inv_anti₀ hε_pos h_in.le
      calc ‖(γ t - γ t₀)⁻¹ * deriv γ t‖
          = ‖(γ t - γ t₀)⁻¹‖ * ‖deriv γ t‖ := norm_mul _ _
        _ ≤ (1 / ε) * M_deriv :=
            mul_le_mul h_bound (hM_deriv t ht) (norm_nonneg _)
              (one_div_pos.mpr hε_pos).le
        _ = M_deriv / ε := by ring
    · simp only [h_in, ↓reduceIte, norm_zero, hM_bound_pos.le]
  rw [intervalIntegrable_iff]
  apply MeasureTheory.IntegrableOn.of_bound
  · exact measure_Ioc_lt_top
  · apply AEStronglyMeasurable.indicator
    · apply Measurable.aestronglyMeasurable
      exact ((hγ_meas.sub_const (γ t₀)).inv.mul (measurable_deriv γ))
    · exact (measurable_norm.comp (hγ_meas.sub_const (γ t₀))) measurableSet_Ioi
  · rw [MeasureTheory.ae_restrict_iff']
    · filter_upwards with t ht using h_norm_bound_ae t ht
    · exact measurableSet_uIoc

/-- Cutoff difference equals annulus integral. -/
lemma cutoff_diff_eq_annulus_integral {f : ℝ → ℂ} {γ : ℝ → ℂ} {a b t₀ : ℝ} {ε₁ ε₂ : ℝ}
    (h_le : ε₁ ≤ ε₂)
    (h_int₁ : IntervalIntegrable (fun t ↦ if ε₁ < ‖γ t - γ t₀‖ then f t else 0)
      MeasureTheory.volume a b)
    (h_int₂ : IntervalIntegrable (fun t ↦ if ε₂ < ‖γ t - γ t₀‖ then f t else 0)
      MeasureTheory.volume a b) :
    (∫ t in a..b, if ε₁ < ‖γ t - γ t₀‖ then f t else 0) -
      (∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ then f t else 0) =
        ∫ t in a..b, if ε₁ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₂ then f t else 0 := by
  rw [← intervalIntegral.integral_sub h_int₁ h_int₂]
  congr 1
  ext t
  grind

/-- Dyadic sequence is Cauchy with bounded remainder. -/
lemma cauchySeq_pv_dyadic {I : ℝ → ℂ} {δ₀ C : ℝ} (_hδ₀_pos : 0 < δ₀) (_hC_pos : 0 < C)
    (h_step : ∀ n, ‖I (δ₀ / 2 ^ (n + 1)) - I (δ₀ / 2 ^ n)‖ ≤ C * δ₀ / 2 ^ n) :
    CauchySeq (fun n ↦ I (δ₀ / 2 ^ n)) := by
  refine cauchySeq_of_le_geometric (1 / 2) (C * δ₀) (by norm_num) (fun n ↦ ?_)
  rw [dist_comm, dist_eq_norm]
  calc ‖I (δ₀ / 2 ^ (n + 1)) - I (δ₀ / 2 ^ n)‖
      ≤ C * δ₀ / 2 ^ n := h_step n
    _ = C * δ₀ * (1 / 2) ^ n := by rw [one_div, inv_pow, ← div_eq_mul_inv]

/-- t-space bound from γ-annulus. -/
lemma t_bound_from_gamma_annulus {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} {δ₁ ε : ℝ} (hL : L ≠ 0)
    (_hε_pos : 0 < ε)
    (h_lower : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₁ → ‖γ t - γ t₀‖ ≥ (‖L‖ / 2) * |t - t₀|)
    (t : ℝ) (ht_pos : 0 < |t - t₀|) (ht_lt : |t - t₀| < δ₁)
    (hγ_bound : ‖γ t - γ t₀‖ ≤ ε) :
    |t - t₀| ≤ 2 * ε / ‖L‖ := by
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  calc |t - t₀|
      = 2 * ((‖L‖ / 2) * |t - t₀|) / ‖L‖ := by field_simp
    _ ≤ 2 * ‖γ t - γ t₀‖ / ‖L‖ :=
        div_le_div_of_nonneg_right (by linarith [h_lower t ht_pos ht_lt]) hL_norm_pos.le
    _ ≤ 2 * ε / ‖L‖ :=
        div_le_div_of_nonneg_right (by linarith) hL_norm_pos.le

/-- Bracket ε between dyadic points: for ε ∈ (0, δ], find n with δ/2^(n+1) < ε ≤ δ/2^n. -/
lemma exists_dyadic_bracket {δ ε : ℝ} (hδ_pos : 0 < δ) (hε_pos : 0 < ε) (hε_le : ε ≤ δ) :
    ∃ n : ℕ, δ / 2 ^ (n + 1) < ε ∧ ε ≤ δ / 2 ^ n := by
  have h_tendsto : Tendsto (fun n : ℕ ↦ δ / 2 ^ n) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
    have hi : Tendsto (fun n : ℕ ↦ 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
      simp_rw [one_div]
      exact tendsto_inv_atTop_zero.comp hp
    have h_eq : (fun n : ℕ ↦ δ / 2 ^ n) = (fun n ↦ δ * (1 / 2 ^ n)) := by
      ext n
      ring
    rw [h_eq, show (0 : ℝ) = δ * 0 by ring]
    exact Tendsto.const_mul δ hi
  rw [Metric.tendsto_atTop] at h_tendsto
  obtain ⟨N, hN⟩ := h_tendsto ε hε_pos
  have h_exists : ∃ n : ℕ, δ / 2 ^ n < ε := by
    use N
    specialize hN N le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_pos (div_pos hδ_pos (by positivity))] at hN
    exact hN
  let m := Nat.find h_exists
  have hm_lt : δ / 2 ^ m < ε := Nat.find_spec h_exists
  by_cases hm_zero : m = 0
  · simp only [hm_zero, pow_zero, div_one] at hm_lt
    exact absurd hε_le (not_le.mpr hm_lt)
  · obtain ⟨n, hn_eq⟩ := Nat.exists_eq_succ_of_ne_zero hm_zero
    use n
    refine ⟨?_, ?_⟩
    · rw [show n + 1 = m from hn_eq.symm]
      exact hm_lt
    · by_contra! h_not
      exact Nat.find_min h_exists (by omega : n < m) h_not

/-- Telescoping sum bound for geometric step bounds. -/
lemma telescoping_sum_bound {X : Type*} [SeminormedAddCommGroup X] {I : ℕ → X} {K δ : ℝ}
    (_hK_pos : 0 < K) (_hδ_pos : 0 < δ)
    (h_step : ∀ n, ‖I (n + 1) - I n‖ ≤ K * δ / 2 ^ n) (N : ℕ) :
    ∀ M, M > N → ‖I M - I N‖ ≤ 2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ M := by
  intro M hM_gt_N
  obtain ⟨d, hd_eq⟩ : ∃ d, M = N + d + 1 := by
    use M - N - 1
    omega
  subst hd_eq
  induction d with
  | zero =>
    calc ‖I (N + 0 + 1) - I N‖
        = ‖I (N + 1) - I N‖ := by ring_nf
      _ ≤ K * δ / 2 ^ N := h_step N
      _ = 2 * K * δ / 2 ^ N - K * δ / 2 ^ N := by ring
      _ = 2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ (N + 1) := by
          rw [pow_succ]
          ring
      _ = 2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ (N + 0 + 1) := by ring_nf
  | succ d' ih =>
    have ih' := ih (by omega : N + d' + 1 > N)
    change ‖I (N + (d' + 1) + 1) - I N‖ ≤
      2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ (N + (d' + 1) + 1)
    simp only [show N + (d' + 1) + 1 = N + d' + 2 by omega]
    rw [(sub_add_sub_cancel (I (N + d' + 2)) (I (N + d' + 1)) (I N)).symm]
    have h_step_d' : ‖I (N + d' + 2) - I (N + d' + 1)‖ ≤ K * δ / 2 ^ (N + d' + 1) := by
      conv_lhs => rw [show N + d' + 2 = (N + d' + 1) + 1 by omega]
      exact h_step (N + d' + 1)
    calc ‖(I (N + d' + 2) - I (N + d' + 1)) + (I (N + d' + 1) - I N)‖
        ≤ ‖I (N + d' + 2) - I (N + d' + 1)‖ + ‖I (N + d' + 1) - I N‖ :=
          norm_add_le _ _
      _ ≤ K * δ / 2 ^ (N + d' + 1) +
          (2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ (N + d' + 1)) := by
            linarith [h_step_d', ih']
      _ = 2 * K * δ / 2 ^ N - K * δ / 2 ^ (N + d' + 1) := by ring
      _ = 2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ (N + d' + 2) := by
          have h_pow : (2 : ℝ) ^ (N + d' + 2) = 2 * 2 ^ (N + d' + 1) := by
            rw [pow_succ]
            ring
          field_simp [h_pow]
          ring

end
