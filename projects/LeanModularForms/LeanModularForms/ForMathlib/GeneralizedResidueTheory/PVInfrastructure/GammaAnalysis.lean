/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# PV Infrastructure: Gamma Analysis

Derivative-based bounds on curves near crossing points. These are
used in the dyadic PV limit proof for principal value convergence.

## Main Results

* `gamma_lower_bound_of_hasDerivAt` — lower bound
    ‖γ - γ₀‖ ≥ (‖L‖/2)|t - t₀|
* `gamma_upper_bound_of_hasDerivAt` — upper bound
    ‖γ - γ₀‖ ≤ 2‖L‖|t - t₀|
* `no_return_of_inj_continuous` — γ bounded away from γ(t₀)
    outside nbhd
-/

open Complex Set Filter Topology
open scoped Real

noncomputable section

private lemma hasDerivAt_remainder_bound {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ : HasDerivAt γ L t₀) : ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < |t - t₀| → |t - t₀| < δ →
      ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ ε * |t - t₀| := by
  intro ε hε
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hγ
  obtain ⟨s, hs_mem, hs⟩ := (hγ hε).exists_mem
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.mem_nhds_iff.mp hs_mem
  refine ⟨δ, hδ_pos, fun t _ ht_lt => ?_⟩
  simpa only [Real.norm_eq_abs] using
    hs t (hδ_ball (by simp [Metric.mem_ball, Real.dist_eq, ht_lt]))

private lemma norm_real_smul (x : ℝ) (L : ℂ) : ‖x • L‖ = |x| * ‖L‖ := by simp

/-- Lower bound on ‖γ t - γ t₀‖ from non-zero derivative.
Uses `hasDerivAt_remainder_bound` + reverse triangle inequality. -/
lemma gamma_lower_bound_of_hasDerivAt {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) :
    ∃ δ > 0, ∀ t, 0 < |t - t₀| → |t - t₀| < δ →
      ‖γ t - γ t₀‖ ≥ (‖L‖ / 2) * |t - t₀| := by
  have hLnorm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  obtain ⟨δ, hδ_pos, hδ_bound⟩ :=
    hasDerivAt_remainder_bound hγ_hasderiv (‖L‖ / 2) (half_pos hLnorm_pos)
  refine ⟨δ, hδ_pos, fun t ht_pos ht_lt => ?_⟩
  have h_rem : ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ (‖L‖ / 2) * |t - t₀| :=
    hδ_bound t ht_pos ht_lt
  have h_tri : ‖γ t - γ t₀‖ ≥ ‖(t - t₀) • L‖ - ‖γ t - γ t₀ - (t - t₀) • L‖ := by
    rw [show ‖γ t - γ t₀‖ = ‖(t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L)‖ by ring_nf]
    exact norm_sub_le_norm_add _ _
  calc ‖γ t - γ t₀‖
      ≥ ‖(t - t₀) • L‖ - ‖γ t - γ t₀ - (t - t₀) • L‖ := h_tri
    _ ≥ |t - t₀| * ‖L‖ - (‖L‖ / 2) * |t - t₀| := by
        rw [norm_real_smul]
        linarith
    _ = (‖L‖ / 2) * |t - t₀| := by ring

/-- Upper bound on ‖γ t - γ t₀‖ from non-zero derivative.
Uses `hasDerivAt_remainder_bound` + triangle inequality. -/
lemma gamma_upper_bound_of_hasDerivAt {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) :
    ∃ δ > 0, ∀ t, 0 < |t - t₀| → |t - t₀| < δ →
      ‖γ t - γ t₀‖ ≤ 2 * ‖L‖ * |t - t₀| := by
  have hLnorm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  obtain ⟨δ, hδ_pos, hδ_bound⟩ :=
    hasDerivAt_remainder_bound hγ_hasderiv ‖L‖ hLnorm_pos
  refine ⟨δ, hδ_pos, fun t ht_pos ht_lt => ?_⟩
  have h_rem : ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ ‖L‖ * |t - t₀| := hδ_bound t ht_pos ht_lt
  have h_tri : ‖γ t - γ t₀‖ ≤ ‖(t - t₀) • L‖ + ‖γ t - γ t₀ - (t - t₀) • L‖ := by
    rw [show ‖γ t - γ t₀‖ = ‖(t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L)‖ by ring_nf]
    exact norm_add_le _ _
  calc ‖γ t - γ t₀‖
      ≤ ‖(t - t₀) • L‖ + ‖γ t - γ t₀ - (t - t₀) • L‖ := h_tri
    _ ≤ |t - t₀| * ‖L‖ + ‖L‖ * |t - t₀| := by
        rw [norm_real_smul]
        linarith
    _ = 2 * ‖L‖ * |t - t₀| := by ring

/-- If γ is continuous on [a,b] and injective at γ(t₀), then γ stays bounded away
from γ(t₀) outside any neighborhood of t₀. -/
lemma no_return_of_inj_continuous {γ : ℝ → ℂ} {a b t₀ : ℝ} {c : ℝ} (hc_pos : 0 < c)
    (hγ_cont : ContinuousOn γ (Set.Icc a b))
    (h_inj : ∀ t ∈ Set.Icc a b, γ t = γ t₀ → t = t₀) :
    ∃ ρ > 0, ∀ t ∈ Set.Icc a b, c ≤ |t - t₀| → ρ ≤ ‖γ t - γ t₀‖ := by
  let S := Set.Icc a b ∩ {t | c ≤ |t - t₀|}
  have hS_compact : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_le continuous_const
      (continuous_abs.comp (continuous_id.sub continuous_const)))
  have hf_cont : ContinuousOn (fun t => ‖γ t - γ t₀‖) S :=
    ((hγ_cont.mono Set.inter_subset_left).sub continuousOn_const).norm
  have hf_pos : ∀ t ∈ S, (0 : ℝ) < ‖γ t - γ t₀‖ := by
    intro t ⟨ht_Icc, ht_dist⟩
    rw [norm_pos_iff, sub_ne_zero]
    intro h_eq
    have h_t_eq := h_inj t ht_Icc h_eq
    subst h_t_eq
    simp only [Set.mem_setOf_eq, sub_self, abs_zero] at ht_dist
    linarith
  obtain ⟨ρ, hρ_pos, hρ_le⟩ := hS_compact.exists_forall_le' hf_cont hf_pos
  exact ⟨ρ, hρ_pos, fun t ht h_dist => hρ_le t ⟨ht, h_dist⟩⟩

end
