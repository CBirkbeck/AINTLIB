/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CPVExistence

/-!
# Multi-crossing CPV existence — geometric foundations (T-BR-Y6b)

This file builds the geometric foundations needed to extend
`hasCauchyPV_inv_sub_of_flat_one_full` (the single-crossing CPV existence
theorem in `CPVExistence.lean`) to handle a **finite set of transverse
crossings** on the same pole `s`.

A "multi-crossing setup" consists of a closed piecewise-`C¹` immersion
`γ : ClosedPwC1Immersion x`, a pole `s : ℂ`, a finite set `crossings : Finset ℝ`
of crossing parameters lying in `Ioo 0 1`, each off a legacy partition, with
completeness: every `t ∈ Icc 0 1` satisfying `γ(t) = s` is in `crossings`. For
`card ≥ 2`, this file builds the supporting geometric scaffolding: a common
radius `r > 0` ensuring the windows `[t_i - r, t_i + r]` are pairwise disjoint,
contained in `(0, 1)`, and avoid all partition points.

## Main results

* `multi_pole_common_radius` — extracts a common `r > 0` from a multi-crossing
  setup satisfying the disjointness/interiority/partition-avoidance properties.
* `multi_pole_local_uniqueness` — on each window `[t_i - r, t_i + r]`, the only
  parameter mapping to `s` is `t_i` itself.
* `multi_pole_local_far_bound` — on each half-window excluding the crossing,
  `‖γ(t) - s‖` admits a positive lower bound.

The local-uniqueness statements established here provide the geometric
foundation needed to apply per-crossing single-crossing CPV machinery in a
multi-crossing setting. The full multi-crossing CPV existence theorem (with
matching value `2πi · generalizedWindingNumber γ s`) requires additionally
adapting the analytic infrastructure (`exit_log_diff_tendsto`, `cpvFullSetup`,
etc.) to work with local rather than global uniqueness, and then combining
per-crossing contributions through telescoping. The full discharge proceeds:
(1) per-crossing local data from `multi_pole_local_uniqueness`; (2) per-crossing
exit-time cutoffs from local strict-monotonicity of `‖γ(t) - s‖`; (3) global
cutoff function combining per-crossing thresholds; (4) cutoff integral
decomposition into annular plus smooth parts; (5) per-crossing convergence via
`exit_log_diff_tendsto`; (6) total convergence by `Tendsto.sum`; (7) polar-part
lift for higher-order parts via the multi-crossing analog of
`hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB`. Steps 1-3 are
dischargeable using the local-uniqueness lemmas below.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2 §3.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

private theorem min_pairwise_distance_pos
    {crossings : Finset ℝ} (h_card_ge_two : 2 ≤ crossings.card) :
    ∃ d > 0, ∀ t₁ ∈ crossings, ∀ t₂ ∈ crossings, t₁ ≠ t₂ → d ≤ |t₁ - t₂| := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h_card_ge_two
  obtain ⟨p_min, hp_min_mem, hp_min⟩ :=
    Finset.exists_min_image ((crossings ×ˢ crossings).filter (fun p ↦ p.1 ≠ p.2))
      (fun p ↦ |p.1 - p.2|)
      ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩⟩
  rw [Finset.mem_filter, Finset.mem_product] at hp_min_mem
  refine ⟨|p_min.1 - p_min.2|, abs_pos.mpr (sub_ne_zero.mpr hp_min_mem.2), ?_⟩
  exact fun t₁ ht₁ t₂ ht₂ ht_ne ↦
    hp_min (t₁, t₂) <| Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ht₁, ht₂⟩, ht_ne⟩

private theorem crossings_bounded_from_endpoints_finset
    {crossings : Finset ℝ} (h_nonempty : crossings.Nonempty)
    (h_Ioo : ∀ t ∈ crossings, t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ a > 0, ∀ t ∈ crossings, a ≤ t ∧ t ≤ 1 - a := by
  obtain ⟨t_min, ht_min_mem, ht_min⟩ :=
    Finset.exists_min_image crossings (fun t ↦ min t (1 - t)) h_nonempty
  have h_t_min_Ioo := h_Ioo t_min ht_min_mem
  refine ⟨min t_min (1 - t_min),
    lt_min h_t_min_Ioo.1 (by linarith [h_t_min_Ioo.2]), ?_⟩
  intro t ht
  have h_ge := ht_min t ht
  refine ⟨h_ge.trans (min_le_left _ _), ?_⟩
  linarith [h_ge.trans (min_le_right _ _)]

private theorem crossings_bounded_from_partition_finset
    {crossings partition : Finset ℝ} (h_nonempty : crossings.Nonempty)
    (h_off : ∀ t ∈ crossings, t ∉ partition) :
    ∃ b > 0, ∀ t ∈ crossings, ∀ p ∈ partition, b ≤ |t - p| := by
  by_cases hP_empty : partition = ∅
  · exact ⟨1, one_pos, fun _ _ p hp ↦ absurd (hP_empty ▸ hp) (Finset.notMem_empty p)⟩
  · obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hP_empty
    obtain ⟨t₀, ht₀⟩ := h_nonempty
    obtain ⟨q_min, hq_min_mem, hq_min⟩ :=
      Finset.exists_min_image (crossings ×ˢ partition) (fun q ↦ |q.1 - q.2|)
        ⟨(t₀, p₀), Finset.mem_product.mpr ⟨ht₀, hp₀⟩⟩
    rw [Finset.mem_product] at hq_min_mem
    refine ⟨|q_min.1 - q_min.2|, abs_pos.mpr fun h_eq ↦
      h_off q_min.1 hq_min_mem.1 (sub_eq_zero.mp h_eq ▸ hq_min_mem.2), ?_⟩
    exact fun t ht p hp ↦ hq_min (t, p) (Finset.mem_product.mpr ⟨ht, hp⟩)

/-- **Common local-uniqueness radius** for a multi-crossing setup. Returns
`r > 0` such that for every `t_i ∈ crossings`:
- `t_i - r ≥ 0` and `t_i + r ≤ 1` (the window stays in `[0, 1]`);
- No other crossing `t_j ≠ t_i` lies in `[t_i - r, t_i + r]` (distinct
  windows are pairwise disjoint up to width `2r`);
- No partition point lies in `[t_i - r, t_i + r]` (each window avoids the
  legacy partition). -/
theorem multi_pole_common_radius
    {crossings partition : Finset ℝ}
    (h_nonempty : crossings.Nonempty)
    (h_Ioo : ∀ t ∈ crossings, t ∈ Set.Ioo (0 : ℝ) 1)
    (h_off : ∀ t ∈ crossings, t ∉ partition) :
    ∃ r > 0,
      (∀ t ∈ crossings, r ≤ t ∧ t ≤ 1 - r) ∧
      (∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t →
        2 * r < |t - t'|) ∧
      (∀ t ∈ crossings, ∀ p ∈ partition, r < |t - p|) := by
  obtain ⟨a, ha_pos, h_endpts⟩ :=
    crossings_bounded_from_endpoints_finset h_nonempty h_Ioo
  obtain ⟨b, hb_pos, h_part⟩ :=
    crossings_bounded_from_partition_finset h_nonempty h_off
  by_cases h_card_one : crossings.card = 1
  · refine ⟨min a (b / 2), lt_min ha_pos (by linarith), ?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨h1, h2⟩ := h_endpts t ht
      exact ⟨(min_le_left _ _).trans h1, by linarith [min_le_left a (b / 2)]⟩
    · intro t ht t' ht' ht_ne
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h_card_one
      rw [hc, Finset.mem_singleton] at ht ht'
      exact absurd (ht'.trans ht.symm) ht_ne
    · intro t ht p hp
      linarith [h_part t ht p hp, min_le_right a (b / 2)]
  · have h_card_ge_two : 2 ≤ crossings.card := by
      have := Finset.card_pos.mpr h_nonempty
      omega
    obtain ⟨d, hd_pos, h_dist⟩ := min_pairwise_distance_pos h_card_ge_two
    refine ⟨min a (min (b / 2) (d / 4)),
      lt_min ha_pos (lt_min (by linarith) (by linarith)), ?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨h1, h2⟩ := h_endpts t ht
      exact ⟨(min_le_left _ _).trans h1,
        by linarith [min_le_left a (min (b / 2) (d / 4))]⟩
    · intro t ht t' ht' ht_ne
      have h_d := h_dist t' ht' t ht ht_ne
      rw [abs_sub_comm] at h_d
      linarith [(min_le_right a (min (b / 2) (d / 4))).trans (min_le_right (b / 2) (d / 4))]
    · intro t ht p hp
      linarith [h_part t ht p hp,
        (min_le_right a (min (b / 2) (d / 4))).trans (min_le_left (b / 2) (d / 4))]

/-- **Per-crossing local uniqueness.** Given a common radius `r` from
`multi_pole_common_radius` (in particular satisfying interiority of windows
and pairwise disjointness) and the completeness assumption that every
parameter `t ∈ Icc 0 1` with `γ(t) = s` lies in `crossings`, the only
parameter `t ∈ Icc (t_i - r) (t_i + r)` with
`γ.toPiecewiseC1Path.toPath.extend t = s` is `t = t_i`. -/
theorem multi_pole_local_uniqueness
    (γ : ClosedPwC1Immersion x) {s : ℂ}
    {crossings : Finset ℝ} {r : ℝ} (hr_pos : 0 < r)
    (h_endpts : ∀ t ∈ crossings, r ≤ t ∧ t ≤ 1 - r)
    (h_pairwise : ∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t →
      2 * r < |t - t'|)
    (h_complete : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t ∈ crossings)
    {t_i : ℝ} (ht_i_mem : t_i ∈ crossings)
    {t : ℝ} (ht_in : t ∈ Set.Icc (t_i - r) (t_i + r))
    (h_eq : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s) :
    t = t_i := by
  obtain ⟨h_t_i_ge, h_t_i_le⟩ := h_endpts t_i ht_i_mem
  have h_t_cross : t ∈ crossings :=
    h_complete t ⟨by linarith [ht_in.1], by linarith [ht_in.2]⟩ h_eq
  by_contra h_ne
  have h_dist := h_pairwise t_i ht_i_mem t h_t_cross h_ne
  have : |t_i - t| ≤ r := by
    rw [abs_sub_comm, abs_le]
    exact ⟨by linarith [ht_in.1], by linarith [ht_in.2]⟩
  linarith

/-- **Localized far-bound from local uniqueness.** On the window `[t_i - r, t_i + r]`,
since the only parameter where γ = s is `t_i`, the distance `‖γ(t) - s‖` has a positive
minimum on each closed half-window `[t_i - r, t_i - r']` and `[t_i + r', t_i + r]`,
for any `0 < r' < r`. -/
theorem multi_pole_local_far_bound
    (γ : ClosedPwC1Immersion x) {s : ℂ}
    {t_i : ℝ} {r : ℝ} (hr_pos : 0 < r)
    (h_local_unique : ∀ t ∈ Set.Icc (t_i - r) (t_i + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t_i)
    {r' : ℝ} (hr'_pos : 0 < r') (hr'_le : r' ≤ r) :
    ∃ m : ℝ, 0 < m ∧
      (∀ t ∈ Set.Icc (t_i - r) (t_i - r'),
        m ≤ ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖) ∧
      (∀ t ∈ Set.Icc (t_i + r') (t_i + r),
        m ≤ ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖) := by
  set γf : ℝ → ℂ := (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ)
  have h_norm_cont : Continuous (fun t ↦ ‖γf t - s‖) := by fun_prop
  obtain ⟨t_l, ht_l_mem, ht_l_min⟩ := isCompact_Icc.exists_isMinOn
    (s := Set.Icc (t_i - r) (t_i - r')) ⟨t_i - r, le_rfl, by linarith⟩
    h_norm_cont.continuousOn
  have hm_l_pos : 0 < ‖γf t_l - s‖ :=
    norm_pos_iff.mpr <| sub_ne_zero.mpr fun h_eq ↦
      absurd (h_local_unique t_l ⟨ht_l_mem.1, by linarith [ht_l_mem.2]⟩ h_eq)
        (fun h ↦ by linarith [h ▸ ht_l_mem.2])
  obtain ⟨t_r, ht_r_mem, ht_r_min⟩ := isCompact_Icc.exists_isMinOn
    (s := Set.Icc (t_i + r') (t_i + r)) ⟨t_i + r, by linarith, le_rfl⟩
    h_norm_cont.continuousOn
  have hm_r_pos : 0 < ‖γf t_r - s‖ :=
    norm_pos_iff.mpr <| sub_ne_zero.mpr fun h_eq ↦
      absurd (h_local_unique t_r ⟨by linarith [ht_r_mem.1], ht_r_mem.2⟩ h_eq)
        (fun h ↦ by linarith [h ▸ ht_r_mem.1])
  refine ⟨min ‖γf t_l - s‖ ‖γf t_r - s‖, lt_min hm_l_pos hm_r_pos, ?_, ?_⟩
  · exact fun t ht ↦ (min_le_left _ _).trans (ht_l_min ht)
  · exact fun t ht ↦ (min_le_right _ _).trans (ht_r_min ht)

end HungerbuhlerWasem

end
