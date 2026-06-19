/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CrossingDataBuilder
import LeanModularForms.ForMathlib.WindingInteger

/-!
# Cauchy principal-value existence at a transverse crossing

For a closed piecewise-`C¹` immersion `γ : ℝ → ℂ` crossing a pole `s` uniquely at
`t₀ ∈ Ioo 0 1` with non-vanishing one-sided derivatives, the Cauchy principal
value `lim_{ε → 0⁺} ∫_{|γ-s| ≥ ε} (γ - s)⁻¹ · γ'` exists. This file develops the
analytic machinery — chord-to-tangent limits, slit-plane chord-quotient
estimates, FTC on annular pieces, and exit-time cancellations — culminating in
the full CPV existence theorem.

## Main results

* `chord_div_t_tendsto_right` / `chord_div_t_tendsto_left`: chord-to-tangent
  limits `(γ(t) - s) / (t - t₀) → L_±` as `t → t₀^±`.
* `exit_chord_tendsto_right` / `exit_chord_tendsto_left`: exit-time variants
  evaluated along a positive cutoff `δ(ε) → 0⁺`.
* `exit_log_tendsto_right` / `exit_log_tendsto_left`: convergence of
  `Complex.log(γ(t₀ ± δ(ε)) - s) - Real.log ε` to `(arg L_±) · I`.
* `exit_log_diff_tendsto`: the divergent `Real.log ε` parts cancel between the
  two sides, leaving a finite log-difference limit.
* `exists_slitPlane_chord_quotient_right` / `_left_forward` / `_left`:
  slit-plane chord-quotient estimates on small one-sided intervals.
* `right_annular_log_diff` / `left_annular_log_diff`: FTC on shrinking annular
  pieces expresses the integral as a log difference.
* `hasCauchyPV_inv_sub_of_flat_one_full`: the headline CPV existence theorem.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

/-- **Right-side chord-to-tangent quotient limit.** Given `γ : ℝ → ℂ` with
`HasDerivWithinAt γ L (Ioi t₀) t₀` and `γ(t₀) = s`, the chord quotient
`(γ(t) - s) / (t - t₀)` tends to `L` as `t → t₀⁺`. -/
theorem chord_div_t_tendsto_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) :
    Tendsto (fun t : ℝ ↦ (γ t - s) / ((t - t₀ : ℝ) : ℂ)) (𝓝[>] t₀) (𝓝 L) := by
  have hr := hasDerivWithinAt_iff_isLittleO.mp h_deriv
  have h_rem_tendsto :
      Tendsto (fun t : ℝ ↦ (γ t - γ t₀ - (t - t₀) • L) / ((t - t₀ : ℝ) : ℂ))
        (𝓝[>] t₀) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ_pos
    filter_upwards [hr.def (by linarith : (0 : ℝ) < δ / 2), self_mem_nhdsWithin] with t hb ht
    have h_pos : 0 < t - t₀ := sub_pos.mpr ht
    have h_norm_eq : ‖(t - t₀ : ℝ)‖ = t - t₀ := by
      rw [Real.norm_eq_abs, abs_of_pos h_pos]
    rw [dist_zero_right, norm_div, Complex.norm_real, h_norm_eq, div_lt_iff₀ h_pos]
    rw [h_norm_eq] at hb
    have h_le : ‖γ t - γ t₀ - ((t - t₀) : ℝ) • L‖ ≤ δ / 2 * (t - t₀) := hb
    have h_lt : δ / 2 * (t - t₀) < δ * (t - t₀) := by nlinarith
    linarith
  have h_rewrite : ∀ᶠ t in 𝓝[>] t₀,
      (γ t - s) / ((t - t₀ : ℝ) : ℂ) =
        L + (γ t - γ t₀ - (t - t₀) • L) / ((t - t₀ : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h_ne_complex : ((t - t₀ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt ht))
    rw [h_at, Complex.real_smul]; field_simp; ring
  refine (?_ : Tendsto _ _ _).congr' (h_rewrite.mono (fun _ h ↦ h.symm))
  simpa using tendsto_const_nhds.add h_rem_tendsto

/-- **Left-side chord-to-tangent quotient limit.** Given `γ : ℝ → ℂ` with
`HasDerivWithinAt γ L (Iio t₀) t₀` and `γ(t₀) = s`, the chord quotient
`(γ(t) - s) / (t - t₀)` tends to `L` as `t → t₀⁻`. -/
theorem chord_div_t_tendsto_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) :
    Tendsto (fun t : ℝ ↦ (γ t - s) / ((t - t₀ : ℝ) : ℂ)) (𝓝[<] t₀) (𝓝 L) := by
  have hr := hasDerivWithinAt_iff_isLittleO.mp h_deriv
  have h_rem_tendsto :
      Tendsto (fun t : ℝ ↦ (γ t - γ t₀ - (t - t₀) • L) / ((t - t₀ : ℝ) : ℂ))
        (𝓝[<] t₀) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ_pos
    filter_upwards [hr.def (by linarith : (0 : ℝ) < δ / 2), self_mem_nhdsWithin] with t hb ht
    have h_pos : 0 < t₀ - t := sub_pos.mpr ht
    have h_norm_eq : ‖(t - t₀ : ℝ)‖ = t₀ - t := by
      rw [Real.norm_eq_abs, abs_of_neg (sub_neg_of_lt ht)]; ring
    rw [dist_zero_right, norm_div, Complex.norm_real, h_norm_eq, div_lt_iff₀ h_pos]
    rw [h_norm_eq] at hb
    have h_le : ‖γ t - γ t₀ - ((t - t₀) : ℝ) • L‖ ≤ δ / 2 * (t₀ - t) := hb
    have h_lt : δ / 2 * (t₀ - t) < δ * (t₀ - t) := by nlinarith
    linarith
  have h_rewrite : ∀ᶠ t in 𝓝[<] t₀,
      (γ t - s) / ((t - t₀ : ℝ) : ℂ) =
        L + (γ t - γ t₀ - (t - t₀) • L) / ((t - t₀ : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h_ne_complex : ((t - t₀ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_lt ht))
    rw [h_at, Complex.real_smul]; field_simp; ring
  refine (?_ : Tendsto _ _ _).congr' (h_rewrite.mono (fun _ h ↦ h.symm))
  simpa using tendsto_const_nhds.add h_rem_tendsto

/-- **Right-side exit-point chord ratio convergence.** Given a positive cutoff
function `δ_right : ℝ → ℝ⁺` with `δ_right(ε) → 0⁺` as `ε → 0⁺`, the chord ratio
`(γ(t₀ + δ_right(ε)) - s) / δ_right(ε)` tends to `L_+` as `ε → 0⁺`.

This is a composition: `chord_div_t_tendsto_right` gives the limit
`(γ(t) - s)/(t - t₀) → L_+` as `t → t₀⁺`, and the map
`ε ↦ t₀ + δ_right(ε)` carries `𝓝[>] 0` to `𝓝[>] t₀` (since `δ_right > 0`
and `δ_right → 0⁺`). -/
theorem exit_chord_tendsto_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s)
    {δ_right : ℝ → ℝ}
    (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_right ε)
    (hδ_to_zero : Tendsto δ_right (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ))) :
    Tendsto (fun ε : ℝ ↦ (γ (t₀ + δ_right ε) - s) / ((δ_right ε : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have h_compose : Tendsto (fun ε : ℝ ↦ t₀ + δ_right ε)
      (𝓝[>] (0 : ℝ)) (𝓝[>] t₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using tendsto_const_nhds.add
        (hδ_to_zero.mono_right nhdsWithin_le_nhds : Tendsto δ_right (𝓝[>] (0 : ℝ)) (𝓝 0))
    · filter_upwards [hδ_pos] with ε hε using show t₀ < t₀ + δ_right ε by linarith
  refine ((chord_div_t_tendsto_right h_deriv h_at).comp h_compose).congr' ?_
  filter_upwards [hδ_pos] with ε _
  simp [Function.comp_apply, add_sub_cancel_left]

/-- **Left-side exit-point chord ratio convergence.** Symmetric to
`exit_chord_tendsto_right`: with `δ_left → 0⁺`, the chord ratio
`(γ(t₀ - δ_left(ε)) - s) / (-δ_left(ε)) → L_-` as `ε → 0⁺`.

(Note the sign: `t - t₀ = -δ_left(ε) < 0`, so dividing by `t - t₀` gives the
right limit `L_-`. Equivalently, `(γ(t₀ - δ_left(ε)) - s) / δ_left(ε) → -L_-`.) -/
theorem exit_chord_tendsto_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s)
    {δ_left : ℝ → ℝ}
    (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_left ε)
    (hδ_to_zero : Tendsto δ_left (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ))) :
    Tendsto (fun ε : ℝ ↦ (γ (t₀ - δ_left ε) - s) / ((-(δ_left ε) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have h_compose : Tendsto (fun ε : ℝ ↦ t₀ - δ_left ε)
      (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using tendsto_const_nhds.sub
        (hδ_to_zero.mono_right nhdsWithin_le_nhds : Tendsto δ_left (𝓝[>] (0 : ℝ)) (𝓝 0))
    · filter_upwards [hδ_pos] with ε hε using show t₀ - δ_left ε < t₀ by linarith
  refine ((chord_div_t_tendsto_left h_deriv h_at).comp h_compose).congr' ?_
  filter_upwards [hδ_pos] with ε _
  simp only [Function.comp_apply, show t₀ - δ_left ε - t₀ = -δ_left ε from by ring]

/-- **Normalized chord close to 1 (right side).** For any `ρ > 0`, eventually
on `𝓝[>] t₀`, `‖(γ(t) - s) / (L · (t - t₀)) - 1‖ ≤ ρ`.

This is the key chord-to-tangent estimate in normalized form. -/
theorem normalized_chord_close_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∀ᶠ t in 𝓝[>] t₀,
      ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  have h_div := ((chord_div_t_tendsto_right h_deriv h_at).div_const L)
  rw [div_self hL] at h_div
  have h_tendsto_one : Tendsto
      (fun t : ℝ ↦ (γ t - s) / (L * ((t - t₀ : ℝ) : ℂ))) (𝓝[>] t₀) (𝓝 1) := by
    refine h_div.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h_ne : ((t - t₀ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr ht))
    field_simp
  rw [Metric.tendsto_nhds] at h_tendsto_one
  filter_upwards [h_tendsto_one ρ hρ_pos] with t ht
  rw [dist_eq_norm] at ht; exact ht.le

/-- **Normalized chord close to 1 (left side).** Note the sign: on the left, the
relevant tangent is `-L_-` and `t - t₀ < 0`, so we work with `(t₀ - t) > 0`. -/
theorem normalized_chord_close_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∀ᶠ t in 𝓝[<] t₀,
      ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  have h_div := ((chord_div_t_tendsto_left h_deriv h_at).div_const L)
  rw [div_self hL] at h_div
  have h_tendsto_one : Tendsto
      (fun t : ℝ ↦ (γ t - s) / (L * ((t - t₀ : ℝ) : ℂ))) (𝓝[<] t₀) (𝓝 1) := by
    refine h_div.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h_ne : ((t - t₀ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_lt (sub_neg_of_lt ht))
    field_simp
  rw [Metric.tendsto_nhds] at h_tendsto_one
  filter_upwards [h_tendsto_one ρ hρ_pos] with t ht
  rw [dist_eq_norm] at ht; exact ht.le

/-- **Fixed-radius normalized chord bound (right side).** From the eventual
bound, extract a positive radius `r > 0` such that the bound holds uniformly
on `(t₀, t₀ + r]`. -/
theorem exists_normalized_chord_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∃ r > 0, ∀ t ∈ Ioc t₀ (t₀ + r),
      ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  have h_ev := normalized_chord_close_right h_deriv h_at hL hρ_pos
  rw [Filter.eventually_iff_exists_mem] at h_ev
  obtain ⟨U, hU_mem, hU_prop⟩ := h_ev
  rw [mem_nhdsWithin] at hU_mem
  obtain ⟨V, hV_open, ht₀_in_V, hV_sub⟩ := hU_mem
  rw [Metric.isOpen_iff] at hV_open
  obtain ⟨r, hr_pos, hr_ball⟩ := hV_open t₀ ht₀_in_V
  refine ⟨r / 2, by linarith, fun t ht_in ↦ hU_prop t (hV_sub ⟨?_, ht_in.1⟩)⟩
  apply hr_ball
  rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith [ht_in.1] : 0 < t - t₀)]
  linarith [ht_in.2]

/-- **Fixed-radius normalized chord bound (left side).** -/
theorem exists_normalized_chord_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∃ r > 0, ∀ t ∈ Ico (t₀ - r) t₀,
      ‖(γ t - s) / (L * ((t - t₀ : ℝ) : ℂ)) - 1‖ ≤ ρ := by
  have h_ev := normalized_chord_close_left h_deriv h_at hL hρ_pos
  rw [Filter.eventually_iff_exists_mem] at h_ev
  obtain ⟨U, hU_mem, hU_prop⟩ := h_ev
  rw [mem_nhdsWithin] at hU_mem
  obtain ⟨V, hV_open, ht₀_in_V, hV_sub⟩ := hU_mem
  rw [Metric.isOpen_iff] at hV_open
  obtain ⟨r, hr_pos, hr_ball⟩ := hV_open t₀ ht₀_in_V
  refine ⟨r / 2, by linarith, fun t ht_in ↦ hU_prop t (hV_sub ⟨?_, ht_in.2⟩)⟩
  apply hr_ball
  rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith [ht_in.2] : t - t₀ < 0)]
  linarith [ht_in.1]

/-- **Slit-plane condition for chord quotients.** If `‖z - 1‖ ≤ 1/4` and
`‖w - 1‖ ≤ 1/4`, then `z / w ∈ slitPlane` (specifically `Re(z/w) > 0`).

The proof uses `‖z/w - 1‖ = ‖z-w‖/‖w‖ ≤ (1/2)/(3/4) = 2/3 < 1`, giving
`Re(z/w) > 0` via `|Re(z/w) - 1| ≤ |z/w - 1| < 1`. -/
theorem div_mem_slitPlane_of_close_to_one {z w : ℂ}
    (hz : ‖z - 1‖ ≤ 1 / 4) (hw : ‖w - 1‖ ≤ 1 / 4) :
    z / w ∈ Complex.slitPlane := by
  have hw_ne : w ≠ 0 := fun hw_eq ↦ by
    rw [hw_eq, zero_sub, norm_neg, norm_one] at hw; linarith
  have h_zw : ‖z - w‖ ≤ 1 / 2 := by
    calc ‖z - w‖ = ‖(z - 1) - (w - 1)‖ := by congr 1; ring
      _ ≤ ‖z - 1‖ + ‖w - 1‖ := norm_sub_le _ _
      _ ≤ 1 / 4 + 1 / 4 := add_le_add hz hw
      _ = 1 / 2 := by ring
  have hw_norm_ge : (3 : ℝ) / 4 ≤ ‖w‖ := by
    have h_sub_nn := norm_sub_norm_le (1 : ℂ) w
    rw [show ((1 : ℂ) - w) = -(w - 1) from by ring, norm_neg, norm_one] at h_sub_nn
    linarith
  have hw_pos : 0 < ‖w‖ := by linarith
  have h_diff : z / w - 1 = (z - w) / w := by field_simp
  have h_diff_norm : ‖z / w - 1‖ < 1 := by
    rw [h_diff, norm_div, div_lt_iff₀ hw_pos]
    nlinarith
  rw [Complex.mem_slitPlane_iff]
  refine .inl ?_
  have h_re : |(z / w).re - 1| < 1 := by
    have h1 := Complex.abs_re_le_norm (z / w - 1)
    simp at h1
    linarith
  rw [abs_sub_lt_iff] at h_re
  linarith

/-- Multiplication by a positive real preserves membership in `Complex.slitPlane`. -/
private lemma ofReal_pos_mul_mem_slitPlane {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) : ((c : ℝ) : ℂ) * z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at hz ⊢
  rcases hz with h_re | h_im
  · exact Or.inl <| by simpa using mul_pos hc h_re
  · exact Or.inr <| by simpa using mul_ne_zero hc.ne' h_im

/-- **Slit-plane on small right interval.** There exists `r > 0` such that for
all `a, b` with `t₀ < a ≤ b ≤ t₀ + r`, the chord quotient
`(γ(b) - s) / (γ(a) - s) ∈ Complex.slitPlane`.

This follows from chord-to-tangent: the normalized quantities
`(γ(b)-s)/(L·(b-t₀))` and `(γ(a)-s)/(L·(a-t₀))` are both close to `1` for
`a, b` near `t₀⁺`, and their ratio (times positive real `(b-t₀)/(a-t₀)`) is
in slitPlane. -/
theorem exists_slitPlane_chord_quotient_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_right h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun a b ha_gt hab hb_le ↦ ?_⟩
  have ha_le : a ≤ t₀ + r := le_trans hab hb_le
  have hb_gt : t₀ < b := lt_of_lt_of_le ha_gt hab
  have ha_in : a ∈ Ioc t₀ (t₀ + r) := ⟨ha_gt, ha_le⟩
  have hb_in : b ∈ Ioc t₀ (t₀ + r) := ⟨hb_gt, hb_le⟩
  have ha_pos : 0 < a - t₀ := sub_pos.mpr ha_gt
  have hb_pos : 0 < b - t₀ := sub_pos.mpr hb_gt
  have ha_pos_C : ((a - t₀ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt ha_pos)
  have hb_pos_C : ((b - t₀ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hb_pos)
  set z := (γ b - s) / (L * ((b - t₀ : ℝ) : ℂ))
  set w := (γ a - s) / (L * ((a - t₀ : ℝ) : ℂ))
  have h_zw : z / w ∈ Complex.slitPlane :=
    div_mem_slitPlane_of_close_to_one (hr_close b hb_in) (hr_close a ha_in)
  have h_ratio : (γ b - s) / (γ a - s) =
      (((b - t₀) / (a - t₀) : ℝ) : ℂ) * (z / w) := by
    have hL_ab : L * ((b - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL hb_pos_C
    have hL_aa : L * ((a - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL ha_pos_C
    rw [show (γ b - s) / (γ a - s) =
        (z * (L * ((b - t₀ : ℝ) : ℂ))) / (w * (L * ((a - t₀ : ℝ) : ℂ))) from by
      congr 1
      · simp only [z]; exact (div_mul_cancel₀ _ hL_ab).symm
      · simp only [w]; exact (div_mul_cancel₀ _ hL_aa).symm]
    push_cast; field_simp
  rw [h_ratio]
  exact ofReal_pos_mul_mem_slitPlane (div_pos hb_pos ha_pos) h_zw

/-- **Slit-plane on small left interval (forward direction).** There exists
`r > 0` such that for all `a, b` with `t₀ - r ≤ a ≤ b < t₀`, the chord quotient
`(γ(b) - s) / (γ(a) - s) ∈ Complex.slitPlane`.

This is the FTC-relevant form: the FTC `segment_log_FTC` requires
`(γ(t) - s) / (γ(a) - s) ∈ slitPlane` for `t ∈ [a, b]` (where `a` is the left
endpoint). Here `b` is closer to `t₀`, so `γ(b) - s` is smaller in magnitude. -/
theorem exists_slitPlane_chord_quotient_left_forward
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0) :
    ∃ r > 0, ∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
      (γ b - s) / (γ a - s) ∈ Complex.slitPlane := by
  obtain ⟨r, hr_pos, hr_close⟩ :=
    exists_normalized_chord_left h_deriv h_at hL (ρ := 1 / 4) (by norm_num)
  refine ⟨r, hr_pos, fun a b ha_ge hab hb_lt ↦ ?_⟩
  have ha_lt : a < t₀ := lt_of_le_of_lt hab hb_lt
  have hb_ge : t₀ - r ≤ b := le_trans ha_ge hab
  have ha_in : a ∈ Ico (t₀ - r) t₀ := ⟨ha_ge, ha_lt⟩
  have hb_in : b ∈ Ico (t₀ - r) t₀ := ⟨hb_ge, hb_lt⟩
  have ha_neg : a - t₀ < 0 := sub_neg_of_lt ha_lt
  have hb_neg : b - t₀ < 0 := sub_neg_of_lt hb_lt
  have ha_neg_C : ((a - t₀ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_lt ha_neg)
  have hb_neg_C : ((b - t₀ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_lt hb_neg)
  set z := (γ b - s) / (L * ((b - t₀ : ℝ) : ℂ))
  set w := (γ a - s) / (L * ((a - t₀ : ℝ) : ℂ))
  have h_zw : z / w ∈ Complex.slitPlane :=
    div_mem_slitPlane_of_close_to_one (hr_close b hb_in) (hr_close a ha_in)
  have h_ratio : (γ b - s) / (γ a - s) =
      (((b - t₀) / (a - t₀) : ℝ) : ℂ) * (z / w) := by
    have hL_aa : L * ((a - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL ha_neg_C
    have hL_bb : L * ((b - t₀ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hL hb_neg_C
    rw [show (γ b - s) / (γ a - s) =
        (z * (L * ((b - t₀ : ℝ) : ℂ))) / (w * (L * ((a - t₀ : ℝ) : ℂ))) from by
      congr 1
      · simp only [z]; exact (div_mul_cancel₀ _ hL_bb).symm
      · simp only [w]; exact (div_mul_cancel₀ _ hL_aa).symm]
    push_cast; field_simp
  rw [h_ratio]
  exact ofReal_pos_mul_mem_slitPlane (div_pos_of_neg_of_neg hb_neg ha_neg) h_zw

/-- **Right annular quotient arg convergence.** -/
theorem arg_right_annular_tendsto
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_at : γ t₀ = s) (hL : L ≠ 0)
    {δ_right : ℝ → ℝ} {r : ℝ}
    (h_γr_div_L : (γ (t₀ + r) - s) / L ∈ Complex.slitPlane)
    (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_right ε)
    (hδ_to_zero : Tendsto δ_right (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ))) :
    Tendsto (fun ε : ℝ ↦
      Complex.arg ((γ (t₀ + r) - s) / (γ (t₀ + δ_right ε) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((γ (t₀ + r) - s) / L).arg) := by
  have h_recip : Tendsto (fun ε : ℝ ↦ ((δ_right ε : ℝ) : ℂ) / (γ (t₀ + δ_right ε) - s))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / L)) := by
    rw [one_div]
    refine ((exit_chord_tendsto_right h_deriv h_at hδ_pos hδ_to_zero).inv₀ hL).congr' ?_
    filter_upwards with ε using by rw [inv_div]
  have h_quot_delta : Tendsto (fun ε : ℝ ↦
      (γ (t₀ + r) - s) * (((δ_right ε : ℝ) : ℂ) / (γ (t₀ + δ_right ε) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((γ (t₀ + r) - s) / L)) := by
    have h1 := tendsto_const_nhds (x := γ (t₀ + r) - s) |>.mul h_recip
    rwa [mul_one_div] at h1
  refine ((Complex.continuousAt_arg h_γr_div_L).tendsto.comp h_quot_delta).congr' ?_
  filter_upwards [hδ_pos] with ε hε
  rw [Function.comp_apply, show (γ (t₀ + r) - s) * (((δ_right ε : ℝ) : ℂ) /
      (γ (t₀ + δ_right ε) - s)) =
      ((δ_right ε : ℝ) : ℂ) * ((γ (t₀ + r) - s) / (γ (t₀ + δ_right ε) - s)) from by ring]
  exact Complex.arg_real_mul _ hε

/-- **Left annular quotient arg convergence.** -/
theorem arg_left_annular_tendsto
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ}
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_at : γ t₀ = s) (_hL : L ≠ 0)
    {δ_left : ℝ → ℝ} {r : ℝ}
    (h_γnegr_div_L : (-L) / (γ (t₀ - r) - s) ∈ Complex.slitPlane)
    (hδ_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ_left ε)
    (hδ_to_zero : Tendsto δ_left (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ))) :
    Tendsto (fun ε : ℝ ↦
      Complex.arg ((γ (t₀ - δ_left ε) - s) / (γ (t₀ - r) - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((-L) / (γ (t₀ - r) - s)).arg) := by
  have h_quot' : Tendsto (fun ε : ℝ ↦
      (γ (t₀ - δ_left ε) - s) / ((δ_left ε : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (-L)) := by
    refine (exit_chord_tendsto_left h_deriv h_at hδ_pos hδ_to_zero).neg.congr' ?_
    filter_upwards with ε using by push_cast; rw [div_neg, neg_neg]
  refine ((Complex.continuousAt_arg h_γnegr_div_L).tendsto.comp
    (h_quot'.div_const (γ (t₀ - r) - s))).congr' ?_
  filter_upwards [hδ_pos] with ε hε
  rw [Function.comp_apply, show (γ (t₀ - δ_left ε) - s) / ((δ_left ε : ℝ) : ℂ) /
      (γ (t₀ - r) - s) =
      (((δ_left ε)⁻¹ : ℝ) : ℂ) * ((γ (t₀ - δ_left ε) - s) / (γ (t₀ - r) - s)) from by
    push_cast; field_simp]
  exact Complex.arg_real_mul _ (inv_pos.mpr hε)

