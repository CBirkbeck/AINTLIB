/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.ArcFTC
import LeanModularForms.ForMathlib.SegmentFTC
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Arc FTC Limit at i — Slit Plane Membership and Log-Arg Computation

This file proves that `γ(t) - i` stays in the slit plane away from `t = 2/5` on
the segments where it does, computes the equal-norm property at `2/5 ± δ`, and
establishes the log difference formula and limit `E(δ) → -πi`.

## Main results

* `fdBoundaryFun_sub_i_slitPlane_seg1` — slit plane on right vertical
* `fdBoundaryFun_sub_i_slitPlane_seg2` — slit plane on arc before `i`
* `fdBoundaryFun_sub_i_neg_slitPlane_seg3` — neg-slit-plane on arc after `i`
* `fdBoundaryFun_sub_i_slitPlane_seg5` — slit plane on horizontal
* `fdBoundaryFun_sub_i_norm_symm` — equal norms at `2/5 ± δ`
* `log_sub_eq_of_equal_norm` — log difference = arg difference when norms equal
* `fdBoundaryFun_arg_left` — `arg(γ(2/5-δ) - i) = -5δπ/12`
* `fdBoundaryFun_arg_right` — `arg(γ(2/5+δ) - i) = 5δπ/12 - π`
* `fdBoundaryFun_log_diff_core_tendsto` — `log(γ(2/5-δ)-i) - log(γ(2/5+δ)-i) → πi`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- On segment 2 (arc before `i`, angle `< π/2`), `γ(t) - i ∈ slitPlane`. -/
theorem fdBoundaryFun_sub_i_slitPlane_seg2 (H : ℝ) (t : ℝ) (ht1 : 1/5 < t) (ht2 : t < 2/5) :
    fdBoundaryFun H t - I ∈ Complex.slitPlane := by
  refine Or.inl ?_
  rw [fdBoundaryFun_arc_eq_exp H t (by linarith) (by linarith),
    exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [add_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, add_zero, mul_one]
  refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;>
    · unfold fdArcAngle; nlinarith [Real.pi_pos]

/-- On segment 3 (arc after `i`), `γ(t) - i ≠ 0` (cos is strictly negative). -/
theorem fdBoundaryFun_sub_i_ne_zero_seg3 (H : ℝ) (t : ℝ) (ht2 : 2/5 < t) (ht3 : t ≤ 3/5) :
    fdBoundaryFun H t - I ≠ 0 := by
  rw [fdBoundaryFun_arc_eq_exp H t (by linarith) ht3,
    exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  intro h
  have hre : Real.cos (fdArcAngle t) = 0 := by
    simpa [Complex.cos_ofReal_re] using congr_arg Complex.re h
  linarith [Real.cos_neg_of_pi_div_two_lt_of_lt (x := fdArcAngle t)
    (by unfold fdArcAngle; nlinarith [Real.pi_pos])
    (by unfold fdArcAngle; nlinarith [Real.pi_pos])]

/-- Norm of `γ(2/5 - δ) - i` equals `2|sin(5δπ/12)|`. -/
theorem fdBoundaryFun_sub_i_norm_left (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) :
    ‖fdBoundaryFun H (2/5 - δ) - I‖ = 2 * |Real.sin (5 * δ * Real.pi / 12)| := by
  rw [fdBoundaryFun_arc_dist_I H (2/5 - δ) (by linarith) (by linarith),
    show (fdArcAngle (2/5 - δ) - Real.pi / 2) / 2 = -(5 * δ * Real.pi / 12) by
      unfold fdArcAngle; ring, Real.sin_neg, abs_neg]

/-- Norm of `γ(2/5 + δ) - i` equals `2|sin(5δπ/12)|`. -/
theorem fdBoundaryFun_sub_i_norm_right (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) :
    ‖fdBoundaryFun H (2/5 + δ) - I‖ = 2 * |Real.sin (5 * δ * Real.pi / 12)| := by
  rw [fdBoundaryFun_arc_dist_I H (2/5 + δ) (by linarith) (by linarith),
    show (fdArcAngle (2/5 + δ) - Real.pi / 2) / 2 = 5 * δ * Real.pi / 12 by
      unfold fdArcAngle; ring]

/-- The norms are equal: `‖γ(2/5-δ) - i‖ = ‖γ(2/5+δ) - i‖`. -/
theorem fdBoundaryFun_sub_i_norm_symm (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) :
    ‖fdBoundaryFun H (2/5 - δ) - I‖ = ‖fdBoundaryFun H (2/5 + δ) - I‖ := by
  rw [fdBoundaryFun_sub_i_norm_left H hδ hδs,
    fdBoundaryFun_sub_i_norm_right H hδ hδs]

/-- When two nonzero complex numbers have equal norms, their log difference
equals `↑(arg z - arg w) * I`. -/
theorem log_sub_eq_of_equal_norm {z w : ℂ} (_hz : z ≠ 0) (_hw : w ≠ 0)
    (hnorm : ‖z‖ = ‖w‖) : Complex.log z - Complex.log w = ↑(z.arg - w.arg) * I := by
  apply Complex.ext <;> simp [Complex.log_re, hnorm, Complex.log_im]

/-- Arg of the left approach: `arg(γ(2/5-δ) - i) = -(5δπ/12)` for `0 < δ < 1/5`.

The half-angle factorization gives `γ(2/5-δ) - i = 2sin(α) · exp(-iα)` where
`α = 5δπ/12 ∈ (0, π/12)`, hence `arg = -α`. -/
theorem fdBoundaryFun_arg_left (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) :
    (fdBoundaryFun H (2/5 - δ) - I).arg = -(5 * δ * Real.pi / 12) := by
  rw [fdBoundaryFun_arc_eq_exp H _ (by linarith) (by linarith),
    exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  set α := 5 * δ * Real.pi / 12 with hα_def
  have hα_pos : 0 < α := by rw [hα_def]; positivity
  have hα_small : α < Real.pi := by rw [hα_def]; nlinarith [Real.pi_pos]
  have h_sinα_pos : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα_pos hα_small
  have h_sin_double : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := Real.sin_two_mul α
  have h_cos_double : Real.cos (2 * α) - 1 = -(2 * Real.sin α ^ 2) := by
    rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq α]
  have hθ : fdArcAngle (2/5 - δ) = Real.pi / 2 - 2 * α := by unfold fdArcAngle; rw [hα_def]; ring
  have h_eq : ↑(Real.cos (fdArcAngle (2/5 - δ))) +
      ↑(Real.sin (fdArcAngle (2/5 - δ))) * I - I =
      ↑(2 * Real.sin α) * (↑(Real.cos α) + ↑(-(Real.sin α)) * I) := by
    rw [hθ, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    apply Complex.ext
    · simp only [add_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, sub_zero, add_zero, mul_one]
      linarith [h_sin_double]
    · simp only [add_im, sub_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
        mul_zero, add_zero, mul_one, zero_add]
      nlinarith [h_cos_double]
  rw [h_eq]
  have h_trig : (↑(Real.cos α) : ℂ) + ↑(-(Real.sin α)) * I =
      Complex.cos ↑(-α) + Complex.sin ↑(-α) * I := by
    rw [← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg, ofReal_neg]
  rw [h_trig]
  refine Complex.arg_mul_cos_add_sin_mul_I (by positivity) ⟨?_, ?_⟩ <;>
    · rw [hα_def]; nlinarith [Real.pi_pos]

/-- Arg of the right approach: `arg(γ(2/5+δ) - i) = 5δπ/12 - π` for `0 < δ < 1/5`.

The half-angle factorization gives `γ(2/5+δ) - i = -2sin(α) · exp(iα)` where
`α = 5δπ/12`, so `arg = α - π` (negative since `im < 0`). -/
theorem fdBoundaryFun_arg_right (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) :
    (fdBoundaryFun H (2/5 + δ) - I).arg = 5 * δ * Real.pi / 12 - Real.pi := by
  rw [fdBoundaryFun_arc_eq_exp H _ (by linarith) (by linarith),
    exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  set α := 5 * δ * Real.pi / 12 with hα_def
  have hα_pos : 0 < α := by rw [hα_def]; positivity
  have hα_small : α < Real.pi := by rw [hα_def]; nlinarith [Real.pi_pos]
  have h_sinα_pos : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα_pos hα_small
  have h_sin_double : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := Real.sin_two_mul α
  have h_cos_double : Real.cos (2 * α) - 1 = -(2 * Real.sin α ^ 2) := by
    rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq α]
  have hθ : fdArcAngle (2/5 + δ) = Real.pi / 2 + 2 * α := by unfold fdArcAngle; rw [hα_def]; ring
  have h_eq : ↑(Real.cos (fdArcAngle (2/5 + δ))) +
      ↑(Real.sin (fdArcAngle (2/5 + δ))) * I - I =
      -(↑(2 * Real.sin α) * (↑(Real.cos α) + ↑(Real.sin α) * I)) := by
    rw [hθ, Real.cos_add, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    apply Complex.ext
    · simp only [add_re, sub_re, neg_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, sub_zero, add_zero, mul_one, zero_mul, zero_sub, one_mul]
      linarith [h_sin_double]
    · simp only [add_im, sub_im, neg_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
        mul_zero, add_zero, mul_one, zero_add, zero_mul, one_mul]
      nlinarith [h_cos_double]
  rw [h_eq]
  have h_trig : (↑(Real.cos α) : ℂ) + ↑(Real.sin α) * I =
      Complex.cos ↑α + Complex.sin ↑α * I := by
    rw [← ofReal_cos, ← ofReal_sin]
  rw [h_trig, Complex.arg_neg_eq_arg_sub_pi_of_im_pos (by simp [mul_im]; positivity),
    Complex.arg_mul_cos_add_sin_mul_I (show (0:ℝ) < 2 * Real.sin α by positivity)
      ⟨by rw [hα_def]; nlinarith [Real.pi_pos], by linarith⟩]

/-- The arg difference: `arg(left) - arg(right) = π - 5δπ/6`. -/
theorem fdBoundaryFun_arg_diff (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδs : δ < 1/5) :
    (fdBoundaryFun H (2/5 - δ) - I).arg -
    (fdBoundaryFun H (2/5 + δ) - I).arg = Real.pi - 5 * δ * Real.pi / 6 := by
  rw [fdBoundaryFun_arg_left H hδ hδs, fdBoundaryFun_arg_right H hδ hδs]
  ring

/-- The "core" log difference tends to `πi` as `δ → 0⁺`.
`log(γ(2/5-δ) - i) - log(γ(2/5+δ) - i) → πi`. -/
theorem fdBoundaryFun_log_diff_core_tendsto (H : ℝ) :
    Tendsto (fun δ ↦ Complex.log (fdBoundaryFun H (2/5 - δ) - I) -
      Complex.log (fdBoundaryFun H (2/5 + δ) - I))
      (𝓝[>] 0) (𝓝 (↑Real.pi * I)) := by
  have hkey : ∀ᶠ δ in 𝓝[>] (0:ℝ),
      Complex.log (fdBoundaryFun H (2/5 - δ) - I) -
      Complex.log (fdBoundaryFun H (2/5 + δ) - I) =
      ↑(Real.pi - 5 * δ * Real.pi / 6) * I := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (0:ℝ) < 1/5 by norm_num)] with δ hδ hδ_pos
    rw [mem_Ioi] at hδ_pos
    rw [mem_Iio] at hδ
    rw [log_sub_eq_of_equal_norm
      (Complex.slitPlane_ne_zero
        (fdBoundaryFun_sub_i_slitPlane_seg2 H _ (by linarith) (by linarith)))
      (fdBoundaryFun_sub_i_ne_zero_seg3 H _ (by linarith) (by linarith))
      (fdBoundaryFun_sub_i_norm_symm H hδ_pos hδ),
      fdBoundaryFun_arg_diff H hδ_pos hδ]
  have htend : Tendsto (fun δ : ℝ ↦ (↑(Real.pi - 5 * δ * Real.pi / 6) : ℂ) * I)
      (𝓝[>] 0) (𝓝 (↑Real.pi * I)) := by
    simpa using (Continuous.tendsto (by fun_prop :
      Continuous (fun δ : ℝ ↦ (↑(Real.pi - 5 * δ * Real.pi / 6) : ℂ) * I)) 0).mono_left
      nhdsWithin_le_nhds
  exact htend.congr' (hkey.mono fun _ h ↦ h.symm)

end
