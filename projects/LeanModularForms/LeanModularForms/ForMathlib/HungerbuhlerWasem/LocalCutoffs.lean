/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CPVExistenceMulti

/-!
# Localized exit-time cutoffs for multi-crossing CPV existence (T-BR-Y6c)

This file adapts the exit-time cutoff infrastructure in
`CrossingDataBuilder.lean` from **global** uniqueness on `Icc 0 1` to
**local** uniqueness on a window `Icc (t₀ - r) (t₀ + r)`. This is the
infrastructure required by the multi-crossing CPV discharge programme:
each crossing parameter `t_i ∈ M.crossings` is equipped with its own
local cutoffs `δ_left^i, δ_right^i : ℝ → ℝ`, threshold `θ_i`, and
asymmetric far/near bounds. These per-crossing bundles, when combined,
discharge the `h_multi_cpv` oracle in
`residueTheorem_crossing_asymmetric_multiPole`.

## Setup

Throughout this file we fix a closed piecewise-`C¹` immersion `γ` (with
range avoidance `x : ℂ`), a pole `s : ℂ`, and a crossing parameter
`t₀ : ℝ`. The local window is `Icc (t₀ - r) (t₀ + r)` for some `r > 0`
with `Icc (t₀ - r) (t₀ + r) ⊆ Icc 0 1`. We assume:
* `h_at` — `γ(t₀) = s`;
* `h_off` — `t₀` is off the legacy partition;
* `h_local_unique` — `t₀` is the unique crossing on the window.

These local-uniqueness assumptions come from `multi_pole_local_uniqueness`
in `CPVExistenceMulti.lean` (applied with the common radius `r` from
`multi_pole_common_radius`).

## Main results

* `exists_right_cutoff_local` — right exit-time cutoff `δ_right : ℝ → ℝ`
  with threshold above which `δ_right(ε) < r` and the far-bound holds on
  `(t₀ + δ_right(ε), t₀ + r]`.
* `exists_left_cutoff_local` — symmetric on the left.
* `LocalDerivedCutoffs` — bundle structure containing both cutoffs and
  all asymmetric far/near bounds.
* `localDerivedCutoffs` — noncomputable builder from local geometric data.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2 §3.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

private theorem strict_mono_inverse_exists_local
    (f : ℝ → ℝ) {r : ℝ} (hr : 0 < r) (hf₀ : f 0 = 0)
    (hf_strict : StrictMonoOn f (Set.Icc 0 r))
    (hf_cont : ContinuousOn f (Set.Icc 0 r)) :
    ∀ ε ∈ Set.Ioo (0 : ℝ) (f r),
      ∃! τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) r ∧ f τ = ε := by
  intro ε hε
  have hε_in : ε ∈ Set.Ioo (f 0) (f r) := by rwa [hf₀]
  obtain ⟨τ, hτ_mem, hfτ⟩ := intermediate_value_Ioo hr.le hf_cont hε_in
  refine ⟨τ, ⟨hτ_mem, hfτ⟩, fun τ' ⟨hτ'_mem, hfτ'⟩ =>
    hf_strict.injOn (Set.Ioo_subset_Icc_self hτ'_mem)
      (Set.Ioo_subset_Icc_self hτ_mem) (hfτ'.trans hfτ.symm)⟩

/-- **Abstract exit-time cutoff from a strictly-monotone exit profile.** This is
the directionless core shared by `exists_right_cutoff_local` and
`exists_left_cutoff_local`. Given a profile `f : ℝ → ℝ` (the distance
`‖γ(t₀ ± τ) - s‖` reparametrised by signed offset `τ`) that vanishes at `0`, is
strictly monotone and continuous on `[0, R]`, together with a far-bound `m` on
`(R, r]`, it produces the inverse cutoff `δ` and threshold with the near/far
estimates stated on the profile. The two callers add only the thin
`f τ = ‖γ(t₀ ± τ) - s‖` rewrite. -/
private theorem cutoff_inverse_of_exitProfile
    (f : ℝ → ℝ) {R r m : ℝ} (hR_pos : 0 < R) (hm_pos : 0 < m)
    (hf₀ : f 0 = 0) (hf_strict : StrictMonoOn f (Set.Icc 0 R))
    (hf_cont : ContinuousOn f (Set.Icc 0 R))
    (h_far : ∀ τ, R < τ → τ ≤ r → m ≤ f τ) :
    ∃ (δ : ℝ → ℝ) (threshold : ℝ), 0 < threshold ∧ threshold ≤ m ∧
      (∀ ε, 0 < ε → ε < threshold → δ ε ∈ Set.Ioo (0 : ℝ) R ∧ f (δ ε) = ε) ∧
      (∀ ε, 0 < ε → ε < threshold → ∀ τ, δ ε < τ → τ ≤ r → ε < f τ) ∧
      (∀ ε, 0 < ε → ε < threshold → ∀ τ, 0 ≤ τ → τ ≤ δ ε → f τ ≤ ε) := by
  classical
  have hf_r_pos : 0 < f R := by
    rw [show (0 : ℝ) = f 0 from hf₀.symm]
    exact hf_strict (Set.left_mem_Icc.mpr hR_pos.le)
      (Set.right_mem_Icc.mpr hR_pos.le) hR_pos
  set threshold : ℝ := min (f R) m with hthr_def
  refine ⟨fun ε =>
    if h : ε ∈ Set.Ioo (0 : ℝ) (f R) then
      (strict_mono_inverse_exists_local f hR_pos hf₀ hf_strict hf_cont ε h).choose
    else R / 2, threshold, lt_min hf_r_pos hm_pos, min_le_right _ _, ?_, ?_, ?_⟩
  · intro ε hε_pos hε_lt
    have hε_in : ε ∈ Set.Ioo (0 : ℝ) (f R) := ⟨hε_pos, hε_lt.trans_le (min_le_left _ _)⟩
    simp only [dif_pos hε_in]
    exact (strict_mono_inverse_exists_local f hR_pos hf₀ hf_strict hf_cont ε hε_in).choose_spec.1
  · intro ε hε_pos hε_lt τ hτ_gt hτ_le
    have hε_in : ε ∈ Set.Ioo (0 : ℝ) (f R) := ⟨hε_pos, hε_lt.trans_le (min_le_left _ _)⟩
    obtain ⟨hδ_in, hfδ⟩ :=
      (strict_mono_inverse_exists_local f hR_pos hf₀ hf_strict hf_cont ε hε_in).choose_spec.1
    simp only [dif_pos hε_in] at hτ_gt ⊢
    by_cases hτ_R : τ ≤ R
    · have := hf_strict ⟨hδ_in.1.le, hδ_in.2.le⟩ ⟨hδ_in.1.le.trans hτ_gt.le, hτ_R⟩ hτ_gt
      rwa [hfδ] at this
    · linarith [h_far τ (lt_of_not_ge hτ_R) hτ_le, hε_lt.trans_le (min_le_right _ _)]
  · intro ε hε_pos hε_lt τ hτ_ge hτ_le
    have hε_in : ε ∈ Set.Ioo (0 : ℝ) (f R) := ⟨hε_pos, hε_lt.trans_le (min_le_left _ _)⟩
    obtain ⟨hδ_in, hfδ⟩ :=
      (strict_mono_inverse_exists_local f hR_pos hf₀ hf_strict hf_cont ε hε_in).choose_spec.1
    simp only [dif_pos hε_in] at hτ_le ⊢
    have := hf_strict.monotoneOn ⟨hτ_ge, hτ_le.trans hδ_in.2.le⟩ ⟨hδ_in.1.le, hδ_in.2.le⟩ hτ_le
    rwa [hfδ] at this

/-- **Localized right cutoff existence (corner-friendly).** Given a closed
pw-`C¹` immersion `γ` crossing `s` at an **interior** parameter `t₀`
(smooth OR corner — no off-partition assumption), with local uniqueness on
the window `[t₀ - r, t₀ + r] ⊆ [0, 1]`, produce a right cutoff
`δ_right : ℝ → ℝ` and threshold satisfying the asymmetric far/near bounds. -/
private theorem exists_right_cutoff_local
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ r : ℝ}
    (h_window_pos : 0 < r)
    (h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∃ (δ_right : ℝ → ℝ) (threshold : ℝ),
      0 < threshold ∧
      (∀ ε, 0 < ε → ε < threshold → 0 < δ_right ε) ∧
      (∀ ε, 0 < ε → ε < threshold → δ_right ε < r) ∧
      (∀ ε, 0 < ε → ε < threshold →
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + δ_right ε) - s‖ = ε) ∧
      (∀ ε, 0 < ε → ε < threshold → ∀ t,
        t₀ + δ_right ε < t → t ≤ t₀ + r →
        ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖) ∧
      (∀ ε, 0 < ε → ε < threshold → ∀ t,
        t₀ ≤ t → t - t₀ ≤ δ_right ε →
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε) := by
  classical
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
  have h_t₀_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨by linarith [(h_window_Icc ⟨le_rfl, by linarith⟩ :
        (t₀ - r) ∈ Set.Icc (0 : ℝ) 1).1],
     by linarith [(h_window_Icc ⟨by linarith, le_rfl⟩ :
        (t₀ + r) ∈ Set.Icc (0 : ℝ) 1).2]⟩
  obtain ⟨L, hL_ne, hL_right⟩ := exists_right_deriv_limit γ h_t₀_Ioo
  have hγ_cont_all : Continuous γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  obtain ⟨r₀, hr₀_pos, hmono⟩ :=
    norm_sub_strictMonoOn_right h_at hL_ne hL_right hγ_cont_all.continuousAt
      (eventually_differentiable_right γ h_t₀_Ioo)
  set r_eff_mono : ℝ := min r₀ (r / 2)
  have hr_eff_pos : 0 < r_eff_mono := lt_min hr₀_pos (by linarith)
  have hr_eff_lt_r : r_eff_mono < r := (min_le_right _ _).trans_lt (by linarith)
  have hmono_r : StrictMonoOn (fun t => ‖γf t - s‖) (Set.Icc t₀ (t₀ + r_eff_mono)) :=
    hmono.mono (Set.Icc_subset_Icc le_rfl (by linarith [min_le_left r₀ (r/2)]))
  set f : ℝ → ℝ := fun τ => ‖γf (t₀ + τ) - s‖ with hf_def
  have hf₀ : f 0 = 0 := by
    show ‖γf (t₀ + 0) - s‖ = 0
    rw [add_zero, show γf t₀ = s from h_at, sub_self, norm_zero]
  have hf_cont : ContinuousOn f (Set.Icc 0 r_eff_mono) :=
    (((hγ_cont_all.comp (continuous_const.add continuous_id)).sub
      continuous_const).norm).continuousOn
  have hf_strict : StrictMonoOn f (Set.Icc 0 r_eff_mono) := fun a ha b hb hab =>
    hmono_r ⟨by linarith [ha.1], by linarith [ha.2]⟩
      ⟨by linarith [hb.1], by linarith [hb.2]⟩ (by linarith)
  obtain ⟨m, hm_pos, _h_far_left, h_far_right⟩ :=
    multi_pole_local_far_bound γ h_window_pos h_local_unique hr_eff_pos
      hr_eff_lt_r.le
  obtain ⟨δ_right, threshold, hthresh_pos, _, hδ_spec, h_far, h_near⟩ :=
    cutoff_inverse_of_exitProfile (r := r) f hr_eff_pos hm_pos hf₀ hf_strict hf_cont
      (fun τ hτ_gt hτ_le => by
        rw [hf_def]; exact h_far_right (t₀ + τ) ⟨by linarith, by linarith⟩)
  have h_eq_t : ∀ t, f (t - t₀) = ‖γf t - s‖ := fun t => by
    show ‖γf (t₀ + (t - t₀)) - s‖ = ‖γf t - s‖
    rw [show t₀ + (t - t₀) = t by ring]
  refine ⟨δ_right, threshold, hthresh_pos, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ε hε_pos hε_lt => (hδ_spec ε hε_pos hε_lt).1.1
  · exact fun ε hε_pos hε_lt => (hδ_spec ε hε_pos hε_lt).1.2.trans hr_eff_lt_r
  · exact fun ε hε_pos hε_lt => (hδ_spec ε hε_pos hε_lt).2
  · intro ε hε_pos hε_lt t ht_gt ht_le
    have := h_far ε hε_pos hε_lt (t - t₀) (by linarith) (by linarith)
    rwa [h_eq_t] at this
  · intro ε hε_pos hε_lt t ht_ge hgap
    have := h_near ε hε_pos hε_lt (t - t₀) (by linarith) (by linarith)
    rwa [h_eq_t] at this

/-- **Localized left cutoff existence (corner-friendly).** Symmetric
counterpart of `exists_right_cutoff_local`. -/
private theorem exists_left_cutoff_local
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ r : ℝ}
    (h_window_pos : 0 < r)
    (h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∃ (δ_left : ℝ → ℝ) (threshold : ℝ),
      0 < threshold ∧
      (∀ ε, 0 < ε → ε < threshold → 0 < δ_left ε) ∧
      (∀ ε, 0 < ε → ε < threshold → δ_left ε < r) ∧
      (∀ ε, 0 < ε → ε < threshold →
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - δ_left ε) - s‖ = ε) ∧
      (∀ ε, 0 < ε → ε < threshold → ∀ t,
        t₀ - r ≤ t → t < t₀ - δ_left ε →
        ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖) ∧
      (∀ ε, 0 < ε → ε < threshold → ∀ t,
        t₀ - δ_left ε ≤ t → t ≤ t₀ →
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε) := by
  classical
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
  have h_t₀_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨by linarith [(h_window_Icc ⟨le_rfl, by linarith⟩ :
        (t₀ - r) ∈ Set.Icc (0 : ℝ) 1).1],
     by linarith [(h_window_Icc ⟨by linarith, le_rfl⟩ :
        (t₀ + r) ∈ Set.Icc (0 : ℝ) 1).2]⟩
  obtain ⟨L, hL_ne, hL_left⟩ := exists_left_deriv_limit γ h_t₀_Ioo
  have hγ_cont_all : Continuous γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  obtain ⟨r₀, hr₀_pos, hanti⟩ :=
    norm_sub_strictAntiOn_left h_at hL_ne hL_left hγ_cont_all.continuousAt
      (eventually_differentiable_left γ h_t₀_Ioo)
  set r_eff_mono : ℝ := min r₀ (r / 2)
  have hr_eff_pos : 0 < r_eff_mono := lt_min hr₀_pos (by linarith)
  have hr_eff_lt_r : r_eff_mono < r := (min_le_right _ _).trans_lt (by linarith)
  have hanti_r : StrictAntiOn (fun t => ‖γf t - s‖) (Set.Icc (t₀ - r_eff_mono) t₀) :=
    hanti.mono (Set.Icc_subset_Icc (by linarith [min_le_left r₀ (r/2)]) le_rfl)
  set f : ℝ → ℝ := fun τ => ‖γf (t₀ - τ) - s‖ with hf_def
  have hf₀ : f 0 = 0 := by
    show ‖γf (t₀ - 0) - s‖ = 0
    rw [sub_zero, show γf t₀ = s from h_at, sub_self, norm_zero]
  have hf_cont : ContinuousOn f (Set.Icc 0 r_eff_mono) :=
    (((hγ_cont_all.comp (continuous_const.sub continuous_id)).sub
      continuous_const).norm).continuousOn
  have hf_strict : StrictMonoOn f (Set.Icc 0 r_eff_mono) := fun a ha b hb hab =>
    hanti_r ⟨by linarith [hb.2], by linarith [hb.1]⟩
      ⟨by linarith [ha.2], by linarith [ha.1]⟩ (by linarith)
  obtain ⟨m, hm_pos, h_far_left, _h_far_right⟩ :=
    multi_pole_local_far_bound γ h_window_pos h_local_unique hr_eff_pos
      hr_eff_lt_r.le
  obtain ⟨δ_left, threshold, hthresh_pos, _, hδ_spec, h_far, h_near⟩ :=
    cutoff_inverse_of_exitProfile (r := r) f hr_eff_pos hm_pos hf₀ hf_strict hf_cont
      (fun τ hτ_gt hτ_le => by
        rw [hf_def]; exact h_far_left (t₀ - τ) ⟨by linarith, by linarith⟩)
  have h_eq_t : ∀ t, f (t₀ - t) = ‖γf t - s‖ := fun t => by
    show ‖γf (t₀ - (t₀ - t)) - s‖ = ‖γf t - s‖
    rw [show t₀ - (t₀ - t) = t by ring]
  refine ⟨δ_left, threshold, hthresh_pos, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ε hε_pos hε_lt => (hδ_spec ε hε_pos hε_lt).1.1
  · exact fun ε hε_pos hε_lt => (hδ_spec ε hε_pos hε_lt).1.2.trans hr_eff_lt_r
  · exact fun ε hε_pos hε_lt => (hδ_spec ε hε_pos hε_lt).2
  · intro ε hε_pos hε_lt t ht_ge ht_lt
    have := h_far ε hε_pos hε_lt (t₀ - t) (by linarith) (by linarith)
    rwa [h_eq_t] at this
  · intro ε hε_pos hε_lt t ht_ge ht_le
    have := h_near ε hε_pos hε_lt (t₀ - t) (by linarith) (by linarith)
    rwa [h_eq_t] at this

/-- **Per-crossing local cutoffs** for a multi-crossing scenario. Each
crossing parameter `t₀` is equipped with its own asymmetric cutoffs
`δ_left, δ_right : ℝ → ℝ`, threshold, and far/near bounds on the local
window `[t₀ - r, t₀ + r]`. -/
structure LocalDerivedCutoffs (γ : ClosedPwC1Immersion x) (s : ℂ) (t₀ r : ℝ) where
  /-- Left cutoff function. -/
  δ_left : ℝ → ℝ
  /-- Right cutoff function. -/
  δ_right : ℝ → ℝ
  /-- Threshold below which all bounds hold. -/
  threshold : ℝ
  hthresh : 0 < threshold
  hδ_left_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_left ε
  hδ_right_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_right ε
  hδ_left_lt : ∀ ε, 0 < ε → ε < threshold → δ_left ε < r
  hδ_right_lt : ∀ ε, 0 < ε → ε < threshold → δ_right ε < r
  h_exit_left : ∀ ε, 0 < ε → ε < threshold →
    ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - δ_left ε) - s‖ = ε
  h_exit_right : ∀ ε, 0 < ε → ε < threshold →
    ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + δ_right ε) - s‖ = ε
  h_far_left : ∀ ε, 0 < ε → ε < threshold → ∀ t,
    t₀ - r ≤ t → t < t₀ - δ_left ε →
    ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖
  h_far_right : ∀ ε, 0 < ε → ε < threshold → ∀ t,
    t₀ + δ_right ε < t → t ≤ t₀ + r →
    ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖
  h_near_left : ∀ ε, 0 < ε → ε < threshold → ∀ t,
    t₀ - δ_left ε ≤ t → t ≤ t₀ →
    ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε
  h_near_right : ∀ ε, 0 < ε → ε < threshold → ∀ t,
    t₀ ≤ t → t - t₀ ≤ δ_right ε →
    ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε

/-- **Builder for `LocalDerivedCutoffs`** from a single-crossing local
geometric data: window radius `r > 0`, window-in-unit-interval, off-partition,
local uniqueness on the window. The far-bound information is derived
internally from `multi_pole_local_far_bound`.

(The `h_flat` hypothesis is recorded but not used in the proof body: the
flatness is implicit in the strict-monotonicity result, which uses only
the nonzero one-sided derivative limits provided by the immersion.) -/
noncomputable def localDerivedCutoffs
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ r : ℝ}
    (h_window_pos : 0 < r)
    (h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    LocalDerivedCutoffs γ s t₀ r :=
  let dR := exists_right_cutoff_local γ h_window_pos h_window_Icc h_at
    h_local_unique
  let dL := exists_left_cutoff_local γ h_window_pos h_window_Icc h_at
    h_local_unique
  let dR_props := dR.choose_spec.choose_spec
  let dL_props := dL.choose_spec.choose_spec
  { δ_left := dL.choose
    δ_right := dR.choose
    threshold := min dR.choose_spec.choose dL.choose_spec.choose
    hthresh := lt_min dR_props.1 dL_props.1
    hδ_left_pos := fun ε hε hεt =>
      dL_props.2.1 ε hε (hεt.trans_le (min_le_right _ _))
    hδ_right_pos := fun ε hε hεt =>
      dR_props.2.1 ε hε (hεt.trans_le (min_le_left _ _))
    hδ_left_lt := fun ε hε hεt =>
      dL_props.2.2.1 ε hε (hεt.trans_le (min_le_right _ _))
    hδ_right_lt := fun ε hε hεt =>
      dR_props.2.2.1 ε hε (hεt.trans_le (min_le_left _ _))
    h_exit_left := fun ε hε hεt =>
      dL_props.2.2.2.1 ε hε (hεt.trans_le (min_le_right _ _))
    h_exit_right := fun ε hε hεt =>
      dR_props.2.2.2.1 ε hε (hεt.trans_le (min_le_left _ _))
    h_far_left := fun ε hε hεt =>
      dL_props.2.2.2.2.1 ε hε (hεt.trans_le (min_le_right _ _))
    h_far_right := fun ε hε hεt =>
      dR_props.2.2.2.2.1 ε hε (hεt.trans_le (min_le_left _ _))
    h_near_left := fun ε hε hεt =>
      dL_props.2.2.2.2.2 ε hε (hεt.trans_le (min_le_right _ _))
    h_near_right := fun ε hε hεt =>
      dR_props.2.2.2.2.2 ε hε (hεt.trans_le (min_le_left _ _)) }

/-- **Right-side chord-quotient radius existence**: given a right one-sided
derivative limit `L ≠ 0`, there exists `r > 0` such that the chord quotient
`(γ(b) - s) / (γ(a) - s) ∈ Complex.slitPlane` for all `t₀ < a ≤ b ≤ t₀ + r`.

Pure repackaging of `exists_slitPlane_chord_quotient_right`. Provided as a
companion to the exact-radius API so that callers can derive their per-crossing
threshold radius before invoking `cpvFullSetup_local_exact`. -/
theorem exists_chord_slitPlane_radius_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Set.Ioi t₀) t₀)
    (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane :=
  exists_slitPlane_chord_quotient_right h_deriv h_at hL

/-- **Left-side chord-quotient radius existence (forward direction)**: given a
left one-sided derivative limit `L ≠ 0`, there exists `r > 0` such that the
chord quotient `(γ(b) - s) / (γ(a) - s) ∈ Complex.slitPlane` for all
`t₀ - r ≤ a ≤ b < t₀`.

Pure repackaging of `exists_slitPlane_chord_quotient_left_forward`. -/
theorem exists_chord_slitPlane_radius_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Set.Iio t₀) t₀)
    (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane :=
  exists_slitPlane_chord_quotient_left_forward h_deriv h_at hL

/-- **Right boundary slit-plane radius existence**: given a right one-sided
derivative limit `L ≠ 0`, there exists `r > 0` such that for every
`0 < r' ≤ r`, the boundary chord-to-tangent quotient
`(γ(t₀ + r') - s) / L ∈ Complex.slitPlane`.

The proof uses the normalized chord bound
`‖(γ(t₀ + r') - s) / (L · r') - 1‖ ≤ 1/4`, which yields
`Re((γ(t₀ + r') - s) / (L · r')) ≥ 3/4`. Multiplying by the positive real
`r'` (which preserves slit-plane membership) gives the desired result. -/
theorem exists_chord_div_endpoint_slitPlane_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Set.Ioi t₀) t₀)
    (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      (γ (t₀ + r') - s) / L ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_right h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun r' hr'_pos hr'_le => ?_⟩
  have h_in : (t₀ + r') ∈ Set.Ioc t₀ (t₀ + r) := ⟨by linarith, by linarith⟩
  have h_simp : (((t₀ + r') - t₀ : ℝ) : ℂ) = ((r' : ℝ) : ℂ) := by push_cast; ring
  have h_close : ‖(γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)) - 1‖ ≤ 1 / 4 := by
    rw [← h_simp]; exact hr_close (t₀ + r') h_in
  have h_re_close : (3 / 4 : ℝ) ≤
      ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))).re := by
    have h_abs_le :
        |((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)) - 1).re| ≤ 1 / 4 :=
      (Complex.abs_re_le_norm _).trans h_close
    have h_re_eq : ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)) - 1).re =
        ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))).re - 1 := by simp
    rw [h_re_eq] at h_abs_le
    linarith [(abs_le.mp h_abs_le).1]
  have hr'_C_ne : ((r' : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hr'_pos.ne'
  have h_div_eq : (γ (t₀ + r') - s) / L =
      ((r' : ℝ) : ℂ) * ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))) := by
    field_simp
  rw [h_div_eq, Complex.mem_slitPlane_iff]
  left
  have h_re_calc :
      (((r' : ℝ) : ℂ) * ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ)))).re =
        r' * ((γ (t₀ + r') - s) / (L * ((r' : ℝ) : ℂ))).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
  rw [h_re_calc]
  exact lt_of_lt_of_le (by positivity : (0 : ℝ) < r' * (3 / 4))
    (mul_le_mul_of_nonneg_left h_re_close hr'_pos.le)

/-- **Left boundary slit-plane radius existence**: given a left one-sided
derivative limit `L ≠ 0`, there exists `r > 0` such that for every
`0 < r' ≤ r` with `γ(t₀ - r') ≠ s`, the negated boundary quotient
`-L / (γ(t₀ - r') - s) ∈ Complex.slitPlane`.

The `γ(t₀ - r') ≠ s` hypothesis is supplied by the caller (typically via
local uniqueness on the window). The proof uses `‖−q − 1‖ ≤ 1/4` where
`q = (γ(t₀ - r') - s) / (L · r')`, then deduces `‖q‖ ≥ 3/4`, then
`‖−1/q − 1‖ ≤ 1/3`, then `Re(−1/q) ≥ 2/3`, and finally multiplies by `1/r' > 0`. -/
theorem exists_chord_div_endpoint_slitPlane_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Set.Iio t₀) t₀)
    (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r → γ (t₀ - r') ≠ s →
      (-L) / (γ (t₀ - r') - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_left h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun r' hr'_pos hr'_le h_γ_ne => ?_⟩
  have h_in : (t₀ - r') ∈ Set.Ico (t₀ - r) t₀ :=
    ⟨by linarith, by linarith⟩
  have h_simp_in : (((t₀ - r') - t₀ : ℝ) : ℂ) = -((r' : ℝ) : ℂ) := by
    push_cast; ring
  have h_close : ‖(γ (t₀ - r') - s) / (L * -((r' : ℝ) : ℂ)) - 1‖ ≤ 1 / 4 := by
    rw [← h_simp_in]; exact hr_close (t₀ - r') h_in
  have hr'_C_ne : ((r' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr'_pos.ne'
  have h_γMinus_ne : γ (t₀ - r') - s ≠ 0 := sub_ne_zero.mpr h_γ_ne
  set q : ℂ := (γ (t₀ - r') - s) / (L * ((r' : ℝ) : ℂ)) with hq_def
  have hq_close : ‖-q - 1‖ ≤ 1 / 4 := by
    have h_eq : (γ (t₀ - r') - s) / (L * -((r' : ℝ) : ℂ)) = -q := by
      rw [hq_def, mul_neg, div_neg]
    rwa [h_eq] at h_close
  have hq_norm : 3 / 4 ≤ ‖q‖ := by
    have h_rev : ‖(-1 : ℂ)‖ - ‖q‖ ≤ ‖-1 - q‖ := norm_sub_norm_le _ _
    rw [norm_neg, norm_one, show (-1 : ℂ) - q = -(q + 1) from by ring,
      norm_neg, show q + 1 = -(-q - 1) from by ring, norm_neg] at h_rev
    linarith
  have hq_ne : q ≠ 0 := fun h_eq => by
    rw [h_eq, norm_zero] at hq_norm; linarith
  have h_neg_inv_q_close : ‖(-1 / q) - 1‖ ≤ 1 / 3 := by
    have h_eq : ((-1 : ℂ) / q) - 1 = -((1 + q) / q) := by field_simp; ring
    rw [h_eq, norm_neg, norm_div,
      show ‖(1 : ℂ) + q‖ = ‖-q - 1‖ from by
        rw [show (1 : ℂ) + q = -(-q - 1) from by ring, norm_neg],
      div_le_iff₀ (norm_pos_iff.mpr hq_ne)]
    calc ‖-q - 1‖ ≤ 1 / 4 := hq_close
      _ ≤ (1 / 3) * (3 / 4) := by norm_num
      _ ≤ (1 / 3) * ‖q‖ := mul_le_mul_of_nonneg_left hq_norm (by norm_num)
  have h_eq_target : (-L) / (γ (t₀ - r') - s) =
      (((1 / r' : ℝ)) : ℂ) * (-1 / q) := by
    rw [hq_def]; push_cast; field_simp
  rw [h_eq_target, Complex.mem_slitPlane_iff]
  left
  have h_re_calc :
      ((((1 / r' : ℝ)) : ℂ) * (-1 / q)).re = (1 / r') * (-1 / q).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
  rw [h_re_calc]
  have h_abs_re_le : |(-1 / q - 1).re| ≤ 1 / 3 :=
    (Complex.abs_re_le_norm _).trans h_neg_inv_q_close
  have h_re_eq : (-1 / q - 1).re = (-1 / q).re - 1 := by simp
  rw [h_re_eq] at h_abs_re_le
  have h_inv_r_pos : 0 < 1 / r' := by positivity
  linarith [mul_le_mul_of_nonneg_left
    (show (2 / 3 : ℝ) ≤ (-1 / q).re by linarith [(abs_le.mp h_abs_re_le).1])
    h_inv_r_pos.le,
    show 0 < (1 / r') * (2 / 3 : ℝ) by positivity]

/-- **One-sided derivative limit setup at an interior crossing.** Extracts the
nonzero one-sided derivatives `L_R, L_L` and the corresponding
`HasDerivWithinAt` witnesses on `Ioi t₀, Iio t₀` from the immersion
infrastructure. This is the radius-independent substrate of
`cpvFullSetup_local`. -/
theorem oneSided_deriv_setup
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ (L_R L_L : ℂ),
      L_R ≠ 0 ∧ L_L ≠ 0 ∧
      HasDerivWithinAt γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_R
        (Set.Ioi t₀) t₀ ∧
      HasDerivWithinAt γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_L
        (Set.Iio t₀) t₀ := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ)
  obtain ⟨L_R, hL_R_ne, hL_R_tendsto⟩ := exists_right_deriv_limit γ ht₀
  obtain ⟨L_L, hL_L_ne, hL_L_tendsto⟩ := exists_left_deriv_limit γ ht₀
  have hγf_cont : ContinuousAt γf t₀ :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousAt
  obtain ⟨S_R, hS_R_mem, hS_R_diff⟩ :=
    (eventually_differentiable_right γ ht₀).exists_mem
  obtain ⟨S_L, hS_L_mem, hS_L_diff⟩ :=
    (eventually_differentiable_left γ ht₀).exists_mem
  refine ⟨L_R, L_L, hL_R_ne, hL_L_ne,
    hasDerivWithinAt_Ioi_iff_Ici.mpr
      (hasDerivWithinAt_Ici_of_tendsto_deriv
        (fun t ht => (hS_R_diff t ht).differentiableWithinAt)
        hγf_cont.continuousWithinAt hS_R_mem hL_R_tendsto),
    hasDerivWithinAt_Iio_iff_Iic.mpr
      (hasDerivWithinAt_Iic_of_tendsto_deriv
        (fun t ht => (hS_L_diff t ht).differentiableWithinAt)
        hγf_cont.continuousWithinAt hS_L_mem hL_L_tendsto)⟩

/-- **Annular log-difference on a crossing-free subinterval.** The directionless
core shared by `right_annular_log_diff_local` and `left_annular_log_diff_local`:
on any `[a, b] ⊆ [0, 1]` avoiding the pole (`γ ≠ s` throughout) and satisfying
the slit-plane chord condition, the integral of `γ'/(γ-s)` equals the log of the
chord quotient. Both callers supply `a`, `b` and discharge `γ ≠ s` from local
uniqueness. -/
private theorem annular_log_diff_of_window
    (γ : ClosedPwC1Immersion x) {s : ℂ} {a b : ℝ} (hab : a ≤ b)
    (h_ab_in_unit : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1)
    (h_ne : ∀ t ∈ Set.Icc a b,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t ≠ s)
    (h_slit : ∀ t ∈ Set.Icc a b,
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈ Complex.slitPlane) :
    ∫ t in a..b,
      deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s) =
    Complex.log
      ((γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s)) := by
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  have ha_in_01 : a ∈ Set.Icc (0 : ℝ) 1 := h_ab_in_unit ⟨le_rfl, hab⟩
  have hb_in_01 : b ∈ Set.Icc (0 : ℝ) 1 := h_ab_in_unit ⟨hab, le_rfl⟩
  have ha_ne : γf a - s ≠ 0 := sub_ne_zero.mpr (h_ne a ⟨le_rfl, hab⟩)
  have hγ_cont : ContinuousOn γf (Set.Icc a b) :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousOn
  have hP_count : (↑γ.toPwC1Immersion.toPiecewiseC1Path.partition : Set ℝ).Countable :=
    γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.countable
  have hγ_diff : ∀ t ∈ Set.Ioo a b \ ↑γ.toPwC1Immersion.toPiecewiseC1Path.partition,
      HasDerivAt γf (deriv γf t) t := fun t ht =>
    (γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off_extend t
      ⟨lt_of_le_of_lt ha_in_01.1 ht.1.1, lt_of_lt_of_le ht.1.2 hb_in_01.2⟩ ht.2).hasDerivAt
  have h_int : IntervalIntegrable
      (fun t => deriv γf t / (γf t - s)) MeasureTheory.volume a b :=
    ((inv_sub_mul_deriv_intervalIntegrable γ hab h_ab_in_unit h_ne).congr
      (fun t _ => by simp only [hγf_def]; ring))
  exact segment_log_FTC hab hP_count hγ_cont hγ_diff ha_ne h_slit h_int

/-- **Local right annular log-difference**: integral on `[t₀ + δ_R, t₀ + r]`
of `γ'/(γ-s)` equals the log of the chord quotient. Local-uniqueness version
of `right_annular_log_diff`. -/
private theorem right_annular_log_diff_local
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    {L_right : ℂ} (_hL_right_ne : L_right ≠ 0)
    (_h_deriv_right : HasDerivWithinAt
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_right (Set.Ioi t₀) t₀)
    (_h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    {r δ_R : ℝ} (hδ_R_pos : 0 < δ_R) (hδ_R_lt : δ_R < r) (_hr_pos : 0 < r)
    (h_window_in_unit : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_slit_R : ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
        Complex.slitPlane)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∫ t in (t₀ + δ_R)..(t₀ + r),
      deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s) =
    Complex.log
      ((γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + r) - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + δ_R) - s)) := by
  have hwin_lo : 0 ≤ t₀ - r := (h_window_in_unit (Set.left_mem_Icc.mpr (by linarith))).1
  have hwin_hi : t₀ + r ≤ 1 := (h_window_in_unit (Set.right_mem_Icc.mpr (by linarith))).2
  refine annular_log_diff_of_window γ (by linarith)
    (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩) (fun t ht h_eq => ?_)
    (fun t ht => h_slit_R (t₀ + δ_R) t (by linarith) ht.1 ht.2)
  have : t = t₀ := h_local_unique t ⟨by linarith [ht.1], by linarith [ht.2]⟩ h_eq
  linarith [ht.1]

/-- **Local left annular log-difference**: integral on `[t₀ - r, t₀ - δ_L]`
of `γ'/(γ-s)` equals the log of the chord quotient. Local-uniqueness version
of `left_annular_log_diff`. -/
private theorem left_annular_log_diff_local
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    {L_left : ℂ} (_hL_left_ne : L_left ≠ 0)
    (_h_deriv_left : HasDerivWithinAt
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_left (Set.Iio t₀) t₀)
    (_h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    {r δ_L : ℝ} (hδ_L_pos : 0 < δ_L) (hδ_L_lt : δ_L < r) (_hr_pos : 0 < r)
    (h_window_in_unit : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_slit_L : ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
        Complex.slitPlane)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∫ t in (t₀ - r)..(t₀ - δ_L),
      deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s) =
    Complex.log
      ((γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - δ_L) - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - r) - s)) := by
  have hwin_lo : 0 ≤ t₀ - r := (h_window_in_unit (Set.left_mem_Icc.mpr (by linarith))).1
  have hwin_hi : t₀ + r ≤ 1 := (h_window_in_unit (Set.right_mem_Icc.mpr (by linarith))).2
  refine annular_log_diff_of_window γ (by linarith)
    (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩) (fun t ht h_eq => ?_)
    (fun t ht => h_slit_L (t₀ - r) t le_rfl ht.1 (by linarith [ht.2]))
  have : t = t₀ := h_local_unique t ⟨by linarith [ht.1], by linarith [ht.2]⟩ h_eq
  linarith [ht.2]

/-- **Abstract `δ → 0⁺` from a near-bound profile.** Directionless core shared by
`δ_right_tendsto_zero` and `δ_left_tendsto_zero`: if the exit cutoff `δ` is
positive below the threshold and the distance profile `dist d = ‖γ(t₀ ± d) - s‖`
is positive on `(0, r)` while staying `≤ ε` for `d ≤ δ ε`, then `δ ε → 0⁺`. -/
private lemma tendsto_nhdsGT_zero_of_near
    {δ : ℝ → ℝ} {threshold r : ℝ} (hr_pos : 0 < r) (hthresh : 0 < threshold)
    (dist : ℝ → ℝ)
    (hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε)
    (h_dist_pos : ∀ d, 0 < d → d < r → 0 < dist d)
    (h_near : ∀ ε, 0 < ε → ε < threshold → ∀ d, 0 ≤ d → d ≤ δ ε → dist d ≤ ε) :
    Tendsto δ (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro δ₀ hδ₀_pos
    set δ₀' : ℝ := min δ₀ (r / 2)
    have hδ₀'_pos : 0 < δ₀' := lt_min hδ₀_pos (by linarith)
    have hδ₀'_lt_r : δ₀' < r := (min_le_right _ _).trans_lt (by linarith)
    have hm_pos : 0 < dist δ₀' := h_dist_pos δ₀' hδ₀'_pos hδ₀'_lt_r
    filter_upwards [Ioo_mem_nhdsGT (lt_min hm_pos hthresh)] with ε hε
    have hδ_pos' := hδ_pos ε hε.1 (hε.2.trans_le (min_le_right _ _))
    by_contra h_ge
    push Not at h_ge
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ_pos'] at h_ge
    linarith [h_near ε hε.1 (hε.2.trans_le (min_le_right _ _)) δ₀'
      (by linarith) ((min_le_left _ _).trans h_ge),
      hε.2.trans_le (min_le_left _ _)]
  · filter_upwards [Ioo_mem_nhdsGT hthresh] with ε hε
    exact hδ_pos ε hε.1 hε.2

/-- **`δ_right` of a `LocalDerivedCutoffs` tends to `0⁺` as `ε → 0⁺`**. -/
theorem LocalDerivedCutoffs.δ_right_tendsto_zero
    {γ : ClosedPwC1Immersion x} {s : ℂ} {t₀ r : ℝ} (_hr_pos : 0 < r)
    (_h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (D : LocalDerivedCutoffs γ s t₀ r) :
    Tendsto D.δ_right (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ)
  refine tendsto_nhdsGT_zero_of_near _hr_pos D.hthresh (fun d => ‖γf (t₀ + d) - s‖)
    (fun ε => D.hδ_right_pos ε) (fun d hd_pos hd_lt => norm_pos_iff.mpr
      (sub_ne_zero.mpr fun h_eq => by
        linarith [h_local_unique _ ⟨by linarith, by linarith⟩ h_eq]))
    (fun ε hε_pos hε_lt d hd0 hdδ =>
      D.h_near_right ε hε_pos hε_lt (t₀ + d) (by linarith) (by linarith))

/-- **`δ_left` of a `LocalDerivedCutoffs` tends to `0⁺` as `ε → 0⁺`**. -/
theorem LocalDerivedCutoffs.δ_left_tendsto_zero
    {γ : ClosedPwC1Immersion x} {s : ℂ} {t₀ r : ℝ} (_hr_pos : 0 < r)
    (_h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_local_unique : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (D : LocalDerivedCutoffs γ s t₀ r) :
    Tendsto D.δ_left (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ)
  refine tendsto_nhdsGT_zero_of_near _hr_pos D.hthresh (fun d => ‖γf (t₀ - d) - s‖)
    (fun ε => D.hδ_left_pos ε) (fun d hd_pos hd_lt => norm_pos_iff.mpr
      (sub_ne_zero.mpr fun h_eq => by
        linarith [h_local_unique _ ⟨by linarith, by linarith⟩ h_eq]))
    (fun ε hε_pos hε_lt d hd0 hdδ =>
      D.h_near_left ε hε_pos hε_lt (t₀ - d) (by linarith) (by linarith))

/-- **`D.δ_right ε < r` for `ε` near `0⁺`** (within the threshold window). -/
private lemma LocalDerivedCutoffs.δ_right_lt_r_eventually
    {γ : ClosedPwC1Immersion x} {s : ℂ} {t₀ r : ℝ}
    (D : LocalDerivedCutoffs γ s t₀ r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), D.δ_right ε < r := by
  filter_upwards [Ioo_mem_nhdsGT D.hthresh] with ε hε
  exact D.hδ_right_lt ε hε.1 hε.2

/-- **`D.δ_left ε < r` for `ε` near `0⁺`** (within the threshold window). -/
private lemma LocalDerivedCutoffs.δ_left_lt_r_eventually
    {γ : ClosedPwC1Immersion x} {s : ℂ} {t₀ r : ℝ}
    (D : LocalDerivedCutoffs γ s t₀ r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), D.δ_left ε < r := by
  filter_upwards [Ioo_mem_nhdsGT D.hthresh] with ε hε
  exact D.hδ_left_lt ε hε.1 hε.2

/-- **`0 < D.δ_right ε` for `ε` near `0⁺`** (within the threshold window). -/
private lemma LocalDerivedCutoffs.δ_right_pos_eventually
    {γ : ClosedPwC1Immersion x} {s : ℂ} {t₀ r : ℝ}
    (D : LocalDerivedCutoffs γ s t₀ r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < D.δ_right ε := by
  filter_upwards [Ioo_mem_nhdsGT D.hthresh] with ε hε
  exact D.hδ_right_pos ε hε.1 hε.2

/-- **`0 < D.δ_left ε` for `ε` near `0⁺`** (within the threshold window). -/
private lemma LocalDerivedCutoffs.δ_left_pos_eventually
    {γ : ClosedPwC1Immersion x} {s : ℂ} {t₀ r : ℝ}
    (D : LocalDerivedCutoffs γ s t₀ r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < D.δ_left ε := by
  filter_upwards [Ioo_mem_nhdsGT D.hthresh] with ε hε
  exact D.hδ_left_pos ε hε.1 hε.2

/-- **Real/imaginary decomposition of `Complex.log (a / b)`** for nonzero `a`, `b`:
the real part is `log ‖a‖ - log ‖b‖` and the imaginary part is `arg (a / b)`. -/
private lemma log_div_re_im_decomp {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Complex.log (a / b) =
      ((Real.log ‖a‖ - Real.log ‖b‖ : ℝ) : ℂ) + ((a / b).arg : ℂ) * Complex.I := by
  refine Complex.ext ?_ ?_
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, Complex.ofReal_im, sub_zero, add_zero]
    rw [Complex.log_re, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb)]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_one, Complex.ofReal_re, zero_add]
    rw [Complex.log_im]; ring

/-- **Per-window cutoff integral converges, exact-radius form** (T-BR-Y9c).

Like `perCrossing_window_integral_tendsto`, but takes the window radius `r`
and all slit-plane chord-quotient/boundary data as INPUTS rather than deriving
them via `cpvFullSetup_local` (which would shrink `r`). This unblocks
multi-crossing aggregation: each crossing supplies its threshold radius
`r_i`, the caller takes `r = min_i r_i`, and every crossing's window uses the
SAME fixed radius `r`.

The caller is responsible for ensuring the slit-plane bounds hold at the
chosen `r`. The companion theorems
`exists_chord_slitPlane_radius_right/left` and
`exists_chord_div_endpoint_slitPlane_right/left` produce per-crossing
threshold radii. -/
theorem perCrossing_window_integral_tendsto_exact
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    {r : ℝ} (hr_pos : 0 < r)
    (h_window_Icc : Set.Icc (t₀ - r) (t₀ + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_local_unique_r : ∀ t ∈ Set.Icc (t₀ - r) (t₀ + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    {L_R L_L : ℂ} (hL_R_ne : L_R ≠ 0) (hL_L_ne : L_L ≠ 0)
    (h_deriv_right : HasDerivWithinAt
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_R (Set.Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_L (Set.Iio t₀) t₀)
    (h_slit_R : ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
          Complex.slitPlane)
    (h_slit_L : ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
          Complex.slitPlane)
    (h_γPlus_div_LR :
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + r) - s) / L_R ∈
        Complex.slitPlane)
    (h_LL_neg_div_γMinus :
      (-L_L) /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - r) - s) ∈
        Complex.slitPlane) :
    ∃ L_i : ℂ,
      Tendsto (fun ε : ℝ =>
        ∫ t in (t₀ - r)..(t₀ + r),
          cpvIntegrand (fun z => (z - s)⁻¹)
            γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε t)
        (𝓝[>] (0 : ℝ)) (𝓝 L_i) := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  set D := localDerivedCutoffs γ hr_pos h_window_Icc h_at h_local_unique_r
  have hδR_tendsto : Tendsto D.δ_right (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    LocalDerivedCutoffs.δ_right_tendsto_zero hr_pos h_window_Icc h_local_unique_r D
  have hδL_tendsto : Tendsto D.δ_left (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    LocalDerivedCutoffs.δ_left_tendsto_zero hr_pos h_window_Icc h_local_unique_r D
  have hδR_lt_r : ∀ᶠ ε in 𝓝[>] (0 : ℝ), D.δ_right ε < r :=
    D.δ_right_lt_r_eventually
  have hδL_lt_r : ∀ᶠ ε in 𝓝[>] (0 : ℝ), D.δ_left ε < r :=
    D.δ_left_lt_r_eventually
  have hδR_pos_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < D.δ_right ε :=
    D.δ_right_pos_eventually
  have hδL_pos_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < D.δ_left ε :=
    D.δ_left_pos_eventually
  set Λ_R : ℝ → ℂ := fun ε =>
    Complex.log ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)) with hΛR_def
  set Λ_L : ℝ → ℂ := fun ε =>
    Complex.log ((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)) with hΛL_def
  have h_arg_R_clean : Tendsto (fun ε : ℝ =>
      Complex.arg ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((γf (t₀ + r) - s) / L_R).arg) :=
    arg_right_annular_tendsto h_deriv_right h_at hL_R_ne h_γPlus_div_LR
      hδR_pos_ev hδR_tendsto
  have h_arg_L_clean : Tendsto (fun ε : ℝ =>
      Complex.arg ((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((-L_L) / (γf (t₀ - r) - s)).arg) :=
    arg_left_annular_tendsto h_deriv_left h_at hL_L_ne h_LL_neg_div_γMinus
      hδL_pos_ev hδL_tendsto
  set argR_lim : ℝ := ((γf (t₀ + r) - s) / L_R).arg with hargR_def
  set argL_lim : ℝ := ((-L_L) / (γf (t₀ - r) - s)).arg with hargL_def
  set logNorm_diff : ℝ :=
    Real.log ‖γf (t₀ + r) - s‖ - Real.log ‖γf (t₀ - r) - s‖ with hlogND_def
  set L_i : ℂ := ((logNorm_diff : ℝ) : ℂ) +
    (((argR_lim + argL_lim : ℝ) : ℂ) * Complex.I)
  refine ⟨L_i, ?_⟩
  have h_eventually_eq :
      (fun ε : ℝ => ∫ t in (t₀ - r)..(t₀ + r),
        cpvIntegrand (fun z => (z - s)⁻¹) γf s ε t) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε => Λ_L ε + Λ_R ε) := by
    filter_upwards [Ioo_mem_nhdsGT D.hthresh, hδR_lt_r, hδL_lt_r,
        hδR_pos_ev, hδL_pos_ev] with ε hε_thresh hδR_r hδL_r hδR_pos hδL_pos
    have hε_pos : 0 < ε := hε_thresh.1
    have hε_lt_thresh : ε < D.threshold := hε_thresh.2
    set F : ℝ → ℂ := fun t =>
      cpvIntegrand (fun z => (z - s)⁻¹) γf s ε t with hF_def
    set integrand : ℝ → ℂ := fun t => (γf t - s)⁻¹ * deriv γf t with hI_def
    have h_left_lt : t₀ - r < t₀ - D.δ_left ε := by linarith
    have h_mid_lt : t₀ - D.δ_left ε < t₀ + D.δ_right ε := by linarith
    have h_right_lt : t₀ + D.δ_right ε < t₀ + r := by linarith
    have hF_left_ae : ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIoc (t₀ - r) (t₀ - D.δ_left ε) → F t = integrand t := by
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
        (((Set.finite_singleton (t₀ - D.δ_left ε)).measure_zero
          MeasureTheory.volume))] with t ht_ne ht_mem
      rw [Set.uIoc_of_le h_left_lt.le] at ht_mem
      have ht_lt : t < t₀ - D.δ_left ε :=
        lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (Set.mem_singleton_iff.mpr h))
      simp only [hF_def, hI_def, cpvIntegrand]
      rw [if_pos]
      exact D.h_far_left ε hε_pos hε_lt_thresh t ht_mem.1.le ht_lt
    have hF_mid : ∀ t ∈ Set.uIoc (t₀ - D.δ_left ε) (t₀ + D.δ_right ε), F t = 0 := by
      intro t ht
      rw [Set.uIoc_of_le h_mid_lt.le] at ht
      simp only [hF_def, cpvIntegrand]
      rw [if_neg (not_lt.mpr _)]
      by_cases h_t_le : t ≤ t₀
      · refine D.h_near_left ε hε_pos hε_lt_thresh t ?_ h_t_le
        linarith [ht.1]
      · push Not at h_t_le
        refine D.h_near_right ε hε_pos hε_lt_thresh t h_t_le.le ?_
        linarith [ht.2]
    have hF_right_ae : ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIoc (t₀ + D.δ_right ε) (t₀ + r) → F t = integrand t := by
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
        (((Set.finite_singleton (t₀ + D.δ_right ε)).measure_zero
          MeasureTheory.volume))] with t _ ht_mem
      rw [Set.uIoc_of_le h_right_lt.le] at ht_mem
      simp only [hF_def, hI_def, cpvIntegrand]
      rw [if_pos]
      exact D.h_far_right ε hε_pos hε_lt_thresh t ht_mem.1 ht_mem.2
    have h_in_window_left : Set.Icc (t₀ - r) (t₀ - D.δ_left ε) ⊆
        Set.Icc (0 : ℝ) 1 := fun u hu => by
      have := (h_window_Icc (Set.left_mem_Icc.mpr (by linarith))).1
      exact ⟨by linarith [hu.1], by linarith [hu.2, ht₀.2]⟩
    have h_in_window_right : Set.Icc (t₀ + D.δ_right ε) (t₀ + r) ⊆
        Set.Icc (0 : ℝ) 1 := fun u hu => by
      have := (h_window_Icc (Set.right_mem_Icc.mpr (by linarith))).2
      exact ⟨by linarith [hu.1, ht₀.1], by linarith [hu.2]⟩
    have h_int_left :
        IntervalIntegrable integrand MeasureTheory.volume (t₀ - r) (t₀ - D.δ_left ε) := by
      have h_ne_left : ∀ t ∈ Set.Icc (t₀ - r) (t₀ - D.δ_left ε), γf t ≠ s := fun t ht h_eq =>
        absurd (h_local_unique_r t ⟨ht.1, by linarith [ht.2]⟩ h_eq) (by linarith [ht.2])
      exact (inv_sub_mul_deriv_intervalIntegrable γ h_left_lt.le
        h_in_window_left h_ne_left).congr (fun t _ => by ring)
    have h_int_right :
        IntervalIntegrable integrand MeasureTheory.volume (t₀ + D.δ_right ε) (t₀ + r) := by
      have h_ne_right : ∀ t ∈ Set.Icc (t₀ + D.δ_right ε) (t₀ + r), γf t ≠ s := fun t ht h_eq =>
        absurd (h_local_unique_r t ⟨by linarith [ht.1], ht.2⟩ h_eq) (by linarith [ht.1])
      exact (inv_sub_mul_deriv_intervalIntegrable γ h_right_lt.le
        h_in_window_right h_ne_right).congr (fun t _ => by ring)
    have hF_int_left : IntervalIntegrable F MeasureTheory.volume
        (t₀ - r) (t₀ - D.δ_left ε) :=
      h_int_left.congr_ae
        ((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr
          (hF_left_ae.mono (fun t ht hm => (ht hm).symm)))
    have hF_int_mid :
        IntervalIntegrable F MeasureTheory.volume
          (t₀ - D.δ_left ε) (t₀ + D.δ_right ε) :=
      (IntervalIntegrable.zero (μ := MeasureTheory.volume)
        (a := t₀ - D.δ_left ε) (b := t₀ + D.δ_right ε)).congr
        (fun t ht => (hF_mid t ht).symm)
    have hF_int_right : IntervalIntegrable F MeasureTheory.volume
        (t₀ + D.δ_right ε) (t₀ + r) :=
      h_int_right.congr_ae
        ((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr
          (hF_right_ae.mono (fun t ht hm => (ht hm).symm)))
    have h_split : ∫ t in (t₀ - r)..(t₀ + r), F t =
        (∫ t in (t₀ - r)..(t₀ - D.δ_left ε), F t) +
        (∫ t in (t₀ - D.δ_left ε)..(t₀ + D.δ_right ε), F t) +
        (∫ t in (t₀ + D.δ_right ε)..(t₀ + r), F t) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
            (hF_int_left.trans hF_int_mid) hF_int_right,
          ← intervalIntegral.integral_add_adjacent_intervals hF_int_left hF_int_mid]
    rw [h_split,
        intervalIntegral.integral_zero_ae (MeasureTheory.ae_of_all _ hF_mid),
        intervalIntegral.integral_congr_ae hF_left_ae,
        intervalIntegral.integral_congr_ae hF_right_ae, add_zero]
    have h_LL := left_annular_log_diff_local γ hL_L_ne h_deriv_left h_at
      hδL_pos hδL_r hr_pos h_window_Icc h_slit_L h_local_unique_r
    have h_RR := right_annular_log_diff_local γ hL_R_ne h_deriv_right h_at
      hδR_pos hδR_r hr_pos h_window_Icc h_slit_R h_local_unique_r
    have h_congr_L : ∫ t in (t₀ - r)..(t₀ - D.δ_left ε), integrand t =
        ∫ t in (t₀ - r)..(t₀ - D.δ_left ε), deriv γf t / (γf t - s) :=
      intervalIntegral.integral_congr fun t _ => by
        simp only [hI_def, hγf_def]; rw [div_eq_mul_inv, mul_comm]
    have h_congr_R : ∫ t in (t₀ + D.δ_right ε)..(t₀ + r), integrand t =
        ∫ t in (t₀ + D.δ_right ε)..(t₀ + r), deriv γf t / (γf t - s) :=
      intervalIntegral.integral_congr fun t _ => by
        simp only [hI_def, hγf_def]; rw [div_eq_mul_inv, mul_comm]
    rw [h_congr_L, h_congr_R, h_LL, h_RR]
  refine Tendsto.congr' h_eventually_eq.symm ?_
  have h_decomp : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Λ_L ε + Λ_R ε = ((logNorm_diff : ℝ) : ℂ) +
        ((((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg +
          ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg : ℝ) : ℂ) * Complex.I := by
    filter_upwards [Ioo_mem_nhdsGT D.hthresh, hδR_lt_r, hδL_lt_r,
        hδR_pos_ev, hδL_pos_ev] with ε hε_thresh hδR_r hδL_r hδR_pos hδL_pos
    have hε_pos : 0 < ε := hε_thresh.1
    have hε_lt_thresh : ε < D.threshold := hε_thresh.2
    have h_eq_R : ‖γf (t₀ + D.δ_right ε) - s‖ = ε :=
      D.h_exit_right ε hε_pos hε_lt_thresh
    have h_eq_L : ‖γf (t₀ - D.δ_left ε) - s‖ = ε :=
      D.h_exit_left ε hε_pos hε_lt_thresh
    have h_γPlus_ne : γf (t₀ + r) - s ≠ 0 := fun h_eq =>
      absurd (h_local_unique_r _ (Set.right_mem_Icc.mpr (by linarith))
        (sub_eq_zero.mp h_eq)) (by linarith)
    have h_γMinus_ne : γf (t₀ - r) - s ≠ 0 := fun h_eq =>
      absurd (h_local_unique_r _ (Set.left_mem_Icc.mpr (by linarith))
        (sub_eq_zero.mp h_eq)) (by linarith)
    have h_γR_ne : γf (t₀ + D.δ_right ε) - s ≠ 0 := by
      rw [← norm_pos_iff, h_eq_R]; exact hε_pos
    have h_γL_ne : γf (t₀ - D.δ_left ε) - s ≠ 0 := by
      rw [← norm_pos_iff, h_eq_L]; exact hε_pos
    have h_log_R_decomp : Λ_R ε =
        ((Real.log ‖γf (t₀ + r) - s‖ - Real.log ‖γf (t₀ + D.δ_right ε) - s‖ : ℝ) : ℂ) +
        (((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg : ℂ) * Complex.I :=
      log_div_re_im_decomp h_γPlus_ne h_γR_ne
    have h_log_L_decomp : Λ_L ε =
        ((Real.log ‖γf (t₀ - D.δ_left ε) - s‖ - Real.log ‖γf (t₀ - r) - s‖ : ℝ) : ℂ) +
        (((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg : ℂ) * Complex.I :=
      log_div_re_im_decomp h_γL_ne h_γMinus_ne
    rw [h_log_L_decomp, h_log_R_decomp, h_eq_R, h_eq_L]
    simp only [hlogND_def]; push_cast; ring
  have h_decomp' : (fun ε : ℝ => ((logNorm_diff : ℝ) : ℂ) +
      ((((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg +
        ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg : ℝ) : ℂ) *
          Complex.I) =ᶠ[𝓝[>] (0 : ℝ)] (fun ε => Λ_L ε + Λ_R ε) := by
    filter_upwards [h_decomp] with ε hε using hε.symm
  refine Tendsto.congr' h_decomp' (tendsto_const_nhds.add ?_)
  have h_arg_sum : Tendsto (fun ε : ℝ =>
      ((γf (t₀ - D.δ_left ε) - s) / (γf (t₀ - r) - s)).arg +
        ((γf (t₀ + r) - s) / (γf (t₀ + D.δ_right ε) - s)).arg)
      (𝓝[>] (0 : ℝ)) (𝓝 (argL_lim + argR_lim)) := by
    simpa [hargL_def, hargR_def] using h_arg_L_clean.add h_arg_R_clean
  have h_target_eq : ((argL_lim + argR_lim : ℝ) : ℂ) * Complex.I =
      ((argR_lim + argL_lim : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [← h_target_eq]
  exact ((Complex.continuous_ofReal.tendsto _).comp h_arg_sum).mul tendsto_const_nhds

/-- **Smooth complement positive bound** for a multi-crossing setup.

Given a finite set of crossings `crossings : Finset ℝ` (each in `Icc 0 1`,
with `γ(t) = s` only when `t ∈ crossings`), and a common radius function
`r_at : crossings → ℝ` with each `r_at t_i > 0`, the function `t ↦ ‖γ(t) - s‖`
has a positive minimum on the **closed complement** `[0, 1] \ ⋃_i (t_i - r_at t_i,
t_i + r_at t_i)`. -/
theorem multi_pole_smooth_complement_far_bound
    (γ : ClosedPwC1Immersion x) {s : ℂ}
    {crossings : Finset ℝ}
    (h_complete : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t ∈ crossings)
    (r_at : ℝ → ℝ) (hr_at_pos : ∀ t ∈ crossings, 0 < r_at t) :
    ∃ m : ℝ, 0 < m ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (∀ t_i ∈ crossings, t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)) →
        m ≤ ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ := by
  classical
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
  have hγ_cont : Continuous γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  set C : Set ℝ := {t ∈ Set.Icc (0 : ℝ) 1 |
    ∀ t_i ∈ crossings, t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)} with hC_def
  have hC_subset : C ⊆ Set.Icc (0 : ℝ) 1 := fun t ht => ht.1
  have hC_closed : IsClosed C := by
    have h2 : IsClosed ({t : ℝ | ∀ t_i ∈ crossings,
        t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)}) := by
      have h_eq : {t : ℝ | ∀ t_i ∈ crossings,
            t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)} =
          ⋂ t_i ∈ crossings, (Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i))ᶜ := by
        ext t; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
      rw [h_eq]
      exact isClosed_biInter fun _ _ => isOpen_Ioo.isClosed_compl
    have hC_eq : C = Set.Icc (0 : ℝ) 1 ∩
        {t : ℝ | ∀ t_i ∈ crossings,
          t ∉ Set.Ioo (t_i - r_at t_i) (t_i + r_at t_i)} := by
      ext t; simp only [hC_def, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [hC_eq]
    exact isClosed_Icc.inter h2
  have hC_compact : IsCompact C :=
    isCompact_Icc.of_isClosed_subset hC_closed hC_subset
  by_cases hC_empty : C = ∅
  · exact ⟨1, one_pos, fun t ht h_avoid => by
      have : t ∈ C := ⟨ht, h_avoid⟩
      rw [hC_empty] at this; exact absurd this (Set.notMem_empty t)⟩
  · have h_norm_cont : ContinuousOn (fun t => ‖γf t - s‖) C :=
      (hγ_cont.continuousOn.sub continuousOn_const).norm
    obtain ⟨t_min, ht_min_mem, ht_min⟩ := hC_compact.exists_isMinOn
      (Set.nonempty_iff_ne_empty.mpr hC_empty) h_norm_cont
    refine ⟨‖γf t_min - s‖, ?_, fun t ht h_avoid => ht_min ⟨ht, h_avoid⟩⟩
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h_eq => ?_)
    have h_t_min_in_crossings : t_min ∈ crossings :=
      h_complete t_min (hC_subset ht_min_mem) h_eq
    exact ht_min_mem.2 t_min h_t_min_in_crossings
      ⟨by linarith [hr_at_pos t_min h_t_min_in_crossings],
       by linarith [hr_at_pos t_min h_t_min_in_crossings]⟩

end HungerbuhlerWasem

end
