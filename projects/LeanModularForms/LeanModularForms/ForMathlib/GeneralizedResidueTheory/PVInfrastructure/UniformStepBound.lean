/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.PVInfrastructure.AnnulusBounds
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.PVInfrastructure.SingularAnnulus

/-!
# PV Infrastructure: Uniform Step Bound

The main uniform step bound for dyadic PV convergence.
Combines the remainder analysis, gamma bounds, and singular
annulus bound into a single epsilon-independent estimate.

## Main Results

* `pv_step_bound_ratio_two_uniform` — uniform step bound
    with epsilon-independent constant
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Uniform step bound with epsilon-independent constant. -/
lemma pv_step_bound_ratio_two_uniform {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ} (hab : a < b)
    (hat₀ : t₀ ∈ Set.Ioo a b) (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L)
    (hL : L ≠ 0) (hγ_meas : Measurable γ)
    (hγ_cont_deriv : ContinuousOn (deriv γ) (Set.Icc a b))
    (hγ_cont : ContinuousOn γ (Set.Icc a b))
    (h_inj : ∀ t ∈ Set.Icc a b, γ t = γ t₀ → t = t₀) :
    ∃ Kstep > 0, ∃ δ > 0, ∀ ε₁ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ ε₁ → ε₁ ≤ 2 * ε₂ → ε₁ < δ →
      let I := fun ε ↦
        ∫ t in a..b, if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0
      ‖I ε₂ - I ε₁‖ ≤ Kstep * ε₁ := by
  obtain ⟨C, δ₀, hδ₀_pos, hr_bounded⟩ := remainder_bounded_of_C2 hL hγ_C2 hγ_deriv
  obtain ⟨Csing, _, δ_sing, _, h_singular⟩ :=
    singular_annulus_bound_explicit hab hat₀ hγ_C2 hγ_deriv hL hγ_cont h_inj
  have hγ_hasderiv : HasDerivAt γ L t₀ :=
    hγ_deriv ▸ (hγ_C2.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasDerivAt
  obtain ⟨δ_lo, hδ_lo_pos, h_lower⟩ := gamma_lower_bound_of_hasDerivAt hL hγ_hasderiv
  obtain ⟨δ_up, hδ_up_pos, h_upper⟩ := gamma_upper_bound_of_hasDerivAt hL hγ_hasderiv
  let δ₁ := min δ_lo δ_up
  have hδ₁_pos : 0 < δ₁ := lt_min hδ_lo_pos hδ_up_pos
  obtain ⟨ρ, hρ_pos, h_far_bound⟩ :=
    no_return_of_inj_continuous (lt_min hδ₀_pos hδ₁_pos) hγ_cont h_inj
  let Kstep := 4 * max 0 C / ‖L‖ + Csing
  have hKstep_pos : 0 < Kstep := by positivity
  let δ := min (min δ_sing (min δ₀ δ₁)) (ρ / 2)
  have hδ_pos : 0 < δ := by simp only [δ, δ₁]; positivity
  use Kstep, hKstep_pos, δ, hδ_pos
  intro ε₁ ε₂ hε₂_pos hε₂_le h_ratio hε₁_lt I
  have hε₁_pos : 0 < ε₁ := lt_of_lt_of_le hε₂_pos hε₂_le
  have h_localize : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₀ δ₁ := by
    intro t ht hγ_le
    have hε₁_lt_ρ : ε₁ < ρ := hε₁_lt.trans_le (min_le_right _ _) |>.trans (by linarith)
    by_contra h_not_lt
    push Not at h_not_lt
    linarith [h_far_bound t ht h_not_lt]
  have hI_int₂ :=
    cutoff_integrand_intervalIntegrable hat₀ hL hγ_meas hγ_cont_deriv ε₂ hε₂_pos
  have hI_int₁ :=
    cutoff_integrand_intervalIntegrable hat₀ hL hγ_meas hγ_cont_deriv ε₁ hε₁_pos
  let f := fun t ↦ (γ t - γ t₀)⁻¹ * deriv γ t
  have h_diff : I ε₂ - I ε₁ =
      ∫ t in a..b,
        (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then f t else 0) := by
    simp only [I, f]
    exact cutoff_diff_eq_annulus_integral hε₂_le hI_int₂ hI_int₁
  let r := fun t ↦ f t - (↑(t - t₀))⁻¹
  have h_pw : ∀ t,
      (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then f t else 0) =
        (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0) +
          (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0) := by
    intro t
    by_cases hcond : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
    · rw [if_pos hcond, if_pos hcond, if_pos hcond]
      simp only [r, f]
      ring
    · rw [if_neg hcond, if_neg hcond, if_neg hcond, add_zero]
  have h_sing_int : IntervalIntegrable
      (fun t ↦ if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0)
      MeasureTheory.volume a b := by
    rw [intervalIntegrable_iff]
    have h_meas_cond : MeasurableSet
        {t : ℝ | ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁} :=
      (measurableSet_lt measurable_const (hγ_meas.sub_const (γ t₀)).norm).inter
        (measurableSet_le (hγ_meas.sub_const (γ t₀)).norm measurable_const)
    refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
      (Measurable.ite h_meas_cond
        (Complex.measurable_ofReal.comp
          (measurable_id.sub measurable_const)).inv
        measurable_const).aestronglyMeasurable
      (2 * ‖L‖ / ε₂) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [min_eq_left hab.le, max_eq_right hab.le] at ht
    have ht_Icc : t ∈ Set.Icc a b := Set.Ioc_subset_Icc_self ht
    by_cases hcond : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
    · rw [if_pos hcond, norm_inv, Complex.norm_real, Real.norm_eq_abs]
      have h_t_ne : t ≠ t₀ := by
        intro heq
        subst heq
        simp only [sub_self, norm_zero] at hcond
        linarith [hcond.1]
      have h_abs_pos : 0 < |t - t₀| := abs_pos.mpr (sub_ne_zero.mpr h_t_ne)
      have h_lt_δ_up : |t - t₀| < δ_up :=
        lt_of_lt_of_le (h_localize t ht_Icc hcond.2)
          (le_trans (min_le_right _ _) (min_le_right _ _))
      have h_up := h_upper t h_abs_pos h_lt_δ_up
      have h_t_lower : ε₂ / (2 * ‖L‖) < |t - t₀| := by
        rw [div_lt_iff₀ (by positivity : 0 < 2 * ‖L‖)]
        linarith [hcond.1]
      calc |t - t₀|⁻¹
          ≤ (ε₂ / (2 * ‖L‖))⁻¹ := inv_anti₀ (by positivity) (le_of_lt h_t_lower)
        _ = 2 * ‖L‖ / ε₂ := by rw [inv_div]
    · rw [if_neg hcond, norm_zero]
      positivity
  have h_rem_int : IntervalIntegrable
      (fun t ↦ if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0)
      MeasureTheory.volume a b := by
    have hf_annulus_int : IntervalIntegrable
        (fun t ↦ if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then f t else 0)
        MeasureTheory.volume a b := by
      refine (hI_int₂.sub hI_int₁).congr fun t _ ↦ ?_
      change (if ε₂ < ‖γ t - γ t₀‖ then f t else 0) -
          (if ε₁ < ‖γ t - γ t₀‖ then f t else 0) =
        if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then f t else 0
      by_cases h₂ : ε₂ < ‖γ t - γ t₀‖
      · rw [if_pos h₂]
        by_cases h₁ : ε₁ < ‖γ t - γ t₀‖
        · rw [if_pos h₁, sub_self, if_neg (fun h ↦ absurd h₁ (not_lt.mpr h.2))]
        · push Not at h₁
          rw [if_neg (not_lt.mpr h₁), sub_zero, if_pos ⟨h₂, h₁⟩]
      · rw [if_neg h₂, zero_sub]
        by_cases h₁ : ε₁ < ‖γ t - γ t₀‖
        · exact absurd (hε₂_le.trans_lt h₁) h₂
        · rw [if_neg h₁, neg_zero, if_neg (fun h ↦ h₂ h.1)]
    refine (hf_annulus_int.sub h_sing_int).congr (fun t _ ↦ ?_)
    change (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then f t else 0) -
        (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0) =
      if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0
    by_cases hcond : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
    · simp only [if_pos hcond]
      ring
    · simp only [if_neg hcond, sub_zero]
  have h_annulus_split :
      ∫ t in a..b, (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then f t else 0) =
        (∫ t in a..b,
          if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0) +
          ∫ t in a..b,
            if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0 := by
    have h_eq :
        (fun t ↦ if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then f t else 0) =
          fun t ↦
            (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0) +
              (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0) :=
      funext (h_pw ·)
    rw [h_eq]
    exact intervalIntegral.integral_add h_sing_int h_rem_int
  have h_sing_bound :
      ‖∫ t in a..b,
          if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0‖ ≤
        Csing * ε₁ :=
    h_singular ε₁ ε₂ hε₂_pos hε₂_le h_ratio
      (lt_of_lt_of_le hε₁_lt (le_trans (min_le_left _ _) (min_le_left _ _)))
  have h_rem_bound :
      ‖∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0‖ ≤
        max 0 C * (4 * ε₁ / ‖L‖) := by
    simp only [r, f]
    exact remainder_integral_bound_on_annulus hL hε₁_pos hε₂_pos hr_bounded h_lower
      (fun t ht hγ ↦ lt_of_lt_of_le (h_localize t ht hγ)
        (min_le_min_left δ₀ (min_le_left δ_lo δ_up))) hat₀
  rw [h_diff, h_annulus_split]
  calc ‖(∫ t in a..b,
          if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0) +
        ∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0‖
      ≤ ‖∫ t in a..b,
            if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0‖ +
          ‖∫ t in a..b,
            if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0‖ := norm_add_le _ _
    _ ≤ Csing * ε₁ + max 0 C * (4 * ε₁ / ‖L‖) := add_le_add h_sing_bound h_rem_bound
    _ = Kstep * ε₁ := by simp only [Kstep]; ring

end
