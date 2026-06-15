/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.GeneralizedWindingNumber
import LeanModularForms.ForMathlib.WindingInteger

/-!
# Winding number via continuous arg lift

For a closed piecewise C¹ path `γ` avoiding a point `w` (with positive distance), the
generalized winding number of `γ` around `w` equals `(θ(1) - θ(0)) / (2π)`, where
`θ : ℝ → ℝ` is the continuous arg lift along `γ - w` from
`Complex.exists_continuous_arg_lift_of_avoids` (W-1).

## Strategy

Choose a partition `s_j = j/N` of `[0, 1]` fine enough that on each `[s_j, s_{j+1}]`,
the ratio `(γ(t) - w) / (γ(s_j) - w)` lies in `Complex.slitPlane`. On each segment,
`Complex.log((γ(t) - w) / (γ(s_j) - w))` is a continuously differentiable primitive of
`γ'(t)/(γ(t) - w)` (chain rule + `HasDerivAt.clog_real`). Apply the FTC variant with
countable exception set (`MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`)
on each segment, and sum via `intervalIntegral.sum_integral_adjacent_intervals`.

## Main results

* `Complex.contourIntegral_inv_eq_sum_log_segRatio` — the contour integral of
  `(z - w)⁻¹` along `γ` equals a sum of complex logs of segment ratios.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Interval

noncomputable section

namespace Complex

variable {x y : ℂ}

/-- **Contour integral as a sum of segment logs.** For γ : PiecewiseC1Path with γ avoiding
w (positive distance), choose any monotone partition `s : ℕ → ℝ` of `[0, 1]` such that
each segment ratio lies in `slitPlane`. Then the contour integral telescopes through
`Complex.log`. -/
theorem contourIntegral_inv_eq_sum_log_segRatio
    (γ : PiecewiseC1Path x y) {w : ℂ}
    {N : ℕ} {s : ℕ → ℝ}
    (hs_zero : s 0 = 0) (hs_N : s N = 1) (hs_mono : Monotone s)
    (hs_in : ∀ j ≤ N, s j ∈ Icc (0 : ℝ) 1)
    (h_avoid : ∀ j ≤ N, γ.toPath.extend (s j) - w ≠ 0)
    (h_slit : ∀ j, j < N → ∀ t ∈ Icc (s j) (s (j + 1)),
      (γ.toPath.extend t - w) / (γ.toPath.extend (s j) - w) ∈ Complex.slitPlane)
    (h_int : IntervalIntegrable
      (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - w))
      MeasureTheory.volume 0 1) :
    γ.contourIntegral (fun z => (z - w)⁻¹) =
      ∑ j ∈ Finset.range N,
        Complex.log ((γ.toPath.extend (s (j + 1)) - w) /
          (γ.toPath.extend (s j) - w)) := by
  have h_eq_int : γ.contourIntegral (fun z => (z - w)⁻¹) =
      ∫ t in (0 : ℝ)..1, deriv γ.toPath.extend t / (γ.toPath.extend t - w) := by
    rw [PiecewiseC1Path.contourIntegral]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    change (γ.toPath.extend t - w)⁻¹ * deriv γ.toPath.extend t =
         deriv γ.toPath.extend t / (γ.toPath.extend t - w)
    rw [div_eq_mul_inv, mul_comm]
  rw [h_eq_int]
  have h_int_seg : ∀ k < N, IntervalIntegrable
      (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - w))
      MeasureTheory.volume (s k) (s (k + 1)) := by
    intro k hk
    refine h_int.mono_set ?_
    rw [uIcc_of_le (zero_le_one' ℝ), uIcc_of_le (hs_mono (Nat.le_succ k))]
    exact Icc_subset_Icc (hs_in k hk.le).1 (hs_in (k + 1) hk).2
  rw [show (0 : ℝ) = s 0 from hs_zero.symm, show (1 : ℝ) = s N from hs_N.symm,
      ← intervalIntegral.sum_integral_adjacent_intervals h_int_seg]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hγ_diff : ∀ t ∈ Ioo (s j) (s (j + 1)) \ (γ.partition : Set ℝ),
      HasDerivAt γ.toPath.extend (deriv γ.toPath.extend t) t := fun t ht =>
    (γ.differentiable_off_extend t
      ⟨(hs_in j hj.le).1.trans_lt ht.1.1,
       ht.1.2.trans_le (hs_in (j + 1) hj).2⟩ ht.2).hasDerivAt
  exact segment_log_FTC (hs_mono (Nat.le_succ j)) γ.partition.countable_toSet
    γ.toPath.continuous_extend.continuousOn hγ_diff (h_avoid j hj.le) (h_slit j hj)
    (h_int_seg j hj)

/-- **Real-imaginary decomposition of contour integral.** Under the same fine-partition
hypotheses, the contour integral splits as `↑(log‖γ 1 - w‖ - log‖γ 0 - w‖) + I · ↑(sum
of imaginary parts of segment logs)`. -/
theorem contourIntegral_inv_decomp
    (γ : PiecewiseC1Path x y) {w : ℂ}
    {N : ℕ} {s : ℕ → ℝ}
    (hs_zero : s 0 = 0) (hs_N : s N = 1) (hs_mono : Monotone s)
    (hs_in : ∀ j ≤ N, s j ∈ Icc (0 : ℝ) 1)
    (h_avoid : ∀ j ≤ N, γ.toPath.extend (s j) - w ≠ 0)
    (h_slit : ∀ j, j < N → ∀ t ∈ Icc (s j) (s (j + 1)),
      (γ.toPath.extend t - w) / (γ.toPath.extend (s j) - w) ∈ Complex.slitPlane)
    (h_int : IntervalIntegrable
      (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - w))
      MeasureTheory.volume 0 1) :
    γ.contourIntegral (fun z => (z - w)⁻¹) =
      ((Real.log ‖γ.toPath.extend 1 - w‖ - Real.log ‖γ.toPath.extend 0 - w‖ : ℝ) : ℂ) +
      Complex.I *
        ((∑ j ∈ Finset.range N,
            (Complex.log ((γ.toPath.extend (s (j + 1)) - w) /
                          (γ.toPath.extend (s j) - w))).im : ℝ) : ℂ) := by
  rw [contourIntegral_inv_eq_sum_log_segRatio γ hs_zero hs_N hs_mono hs_in h_avoid h_slit h_int]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    rw [Complex.re_sum]
    calc ∑ j ∈ Finset.range N,
            (Complex.log ((γ.toPath.extend (s (j + 1)) - w) /
                          (γ.toPath.extend (s j) - w))).re
        = ∑ j ∈ Finset.range N,
            (Real.log ‖γ.toPath.extend (s (j + 1)) - w‖ -
             Real.log ‖γ.toPath.extend (s j) - w‖) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mem_range] at hj
          rw [Complex.log_re, norm_div,
              Real.log_div (norm_ne_zero_iff.mpr (h_avoid (j + 1) hj))
                (norm_ne_zero_iff.mpr (h_avoid j hj.le))]
      _ = Real.log ‖γ.toPath.extend (s N) - w‖ -
            Real.log ‖γ.toPath.extend (s 0) - w‖ :=
          Finset.sum_range_sub (fun j => Real.log ‖γ.toPath.extend (s j) - w‖) N
      _ = _ := by rw [hs_N, hs_zero]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, zero_add, one_mul]
    exact Complex.im_sum _ _

/-- **W-2 (Winding via arg difference).** For a closed piecewise C¹ path `γ` avoiding `w`
with positive distance, there exists a continuous arg lift `θ` of `γ - w` such that
the generalized winding number of `γ` around `w` equals `(θ(1) - θ(0)) / (2π)`. -/
theorem hasGeneralizedWindingNumber_eq_arg_diff_W1_closed
    (γ : PiecewiseC1Path x x) {w : ℂ}
    (hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ.toPath.extend t - w‖)
    (h_int : IntervalIntegrable
      (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - w))
      MeasureTheory.volume 0 1) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t - w =
        (‖γ.toPath.extend t - w‖ : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))) ∧
      HasGeneralizedWindingNumber γ w (((θ 1 - θ 0 : ℝ) : ℂ) / (2 * Real.pi)) := by
  obtain ⟨d, hd_pos, hd_bd⟩ := hδ
  have h_avoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t ≠ w := fun t ht heq => by
    have := hd_bd t ht
    rw [heq, sub_self, norm_zero] at this
    linarith
  obtain ⟨N, s, _, hs_zero, hs_N, hs_mono, hs_in, hs_avoid, h_slit, hθ_cont, h_lift⟩ :=
    Complex.exists_continuous_arg_lift_with_partition
      γ.toPath.continuous_extend.continuousOn h_avoid
  set θ : ℝ → ℝ := fun t =>
    Complex.arg (γ.toPath.extend 0 - w) +
      ∑ j ∈ Finset.range N,
        (Complex.log (Complex.segRatio γ.toPath.extend w (s j) (s (j + 1)) t)).im
  refine ⟨θ, hθ_cont, h_lift, ?_⟩
  have h_contour := contourIntegral_inv_decomp γ hs_zero hs_N hs_mono hs_in
    hs_avoid h_slit h_int
  have h_θ_zero : θ 0 = Complex.arg (γ.toPath.extend 0 - w) := by
    change Complex.arg (γ.toPath.extend 0 - w) +
      ∑ j ∈ Finset.range N,
        (Complex.log (Complex.segRatio γ.toPath.extend w (s j) (s (j + 1)) 0)).im =
      Complex.arg (γ.toPath.extend 0 - w)
    rw [Finset.sum_eq_zero fun j hj => by
      rw [Finset.mem_range] at hj
      rw [Complex.segRatio_eq_one_of_le (hs_mono (Nat.le_succ _)) (hs_in j hj.le).1
            (hs_avoid j hj.le), Complex.log_one]; rfl, add_zero]
  have h_θ_one : θ 1 = Complex.arg (γ.toPath.extend 0 - w) +
      ∑ j ∈ Finset.range N,
        (Complex.log ((γ.toPath.extend (s (j + 1)) - w) /
                      (γ.toPath.extend (s j) - w))).im := by
    change Complex.arg (γ.toPath.extend 0 - w) +
      ∑ j ∈ Finset.range N,
        (Complex.log (Complex.segRatio γ.toPath.extend w (s j) (s (j + 1)) 1)).im = _
    exact congrArg (Complex.arg (γ.toPath.extend 0 - w) + ·)
      (Finset.sum_congr rfl fun j hj => by
        rw [Finset.mem_range] at hj
        rw [Complex.segRatio_eq_full (hs_mono (Nat.le_succ _)) (hs_N ▸ hs_mono hj)])
  have h_θ_diff : (θ 1 - θ 0 : ℝ) =
      ∑ j ∈ Finset.range N,
        (Complex.log ((γ.toPath.extend (s (j + 1)) - w) /
                      (γ.toPath.extend (s j) - w))).im := by
    rw [h_θ_one, h_θ_zero]; ring
  have h_re_zero : Real.log ‖γ.toPath.extend 1 - w‖ -
      Real.log ‖γ.toPath.extend 0 - w‖ = 0 := by
    simp
  have h_w := hasGeneralizedWindingNumber_of_avoids (γ := γ) (z₀ := w) ⟨d, hd_pos, hd_bd⟩
  rw [h_contour, h_re_zero, Complex.ofReal_zero, zero_add, ← h_θ_diff] at h_w
  rw [show ((θ 1 - θ 0 : ℝ) : ℂ) / (2 * Real.pi) =
      (2 * ↑Real.pi * Complex.I)⁻¹ * (Complex.I * ((θ 1 - θ 0 : ℝ) : ℂ)) by
    have : (Real.pi : ℂ) ≠ 0 := mod_cast Real.pi_ne_zero
    field_simp]
  exact h_w

/-- **W-3 (Winding integer-valued).** For a closed piecewise C¹ path `γ` avoiding `w`
with positive distance, the generalized winding number is an integer. -/
theorem hasGeneralizedWindingNumber_integer_of_closed
    (γ : PiecewiseC1Path x x) {w : ℂ}
    (hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ.toPath.extend t - w‖)
    (h_int : IntervalIntegrable
      (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - w))
      MeasureTheory.volume 0 1) :
    ∃ n : ℤ, HasGeneralizedWindingNumber γ w (n : ℂ) := by
  obtain ⟨θ, _, h_lift, h_winding⟩ :=
    hasGeneralizedWindingNumber_eq_arg_diff_W1_closed γ hδ h_int
  have h_eq_endpoints : γ.toPath.extend 1 = γ.toPath.extend 0 := by
    rw [γ.toPath.extend_one, γ.toPath.extend_zero]
  obtain ⟨_, _, hd_bd⟩ := hδ
  have h_avoid_0 : γ.toPath.extend 0 - w ≠ 0 := by
    intro heq
    have := hd_bd 0 ⟨le_rfl, zero_le_one⟩
    rw [heq, norm_zero] at this
    linarith
  have h_exp_eq : Complex.exp (Complex.I * (θ 0 : ℂ)) =
      Complex.exp (Complex.I * (θ 1 : ℂ)) := by
    refine mul_left_cancel₀
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h_avoid_0)) ?_
    calc (‖γ.toPath.extend 0 - w‖ : ℂ) * Complex.exp (Complex.I * (θ 0 : ℂ))
        = γ.toPath.extend 0 - w := (h_lift 0 ⟨le_rfl, zero_le_one⟩).symm
      _ = γ.toPath.extend 1 - w := by rw [h_eq_endpoints]
      _ = (‖γ.toPath.extend 1 - w‖ : ℂ) * Complex.exp (Complex.I * (θ 1 : ℂ)) :=
        h_lift 1 ⟨zero_le_one, le_rfl⟩
      _ = (‖γ.toPath.extend 0 - w‖ : ℂ) * Complex.exp (Complex.I * (θ 1 : ℂ)) := by
          rw [h_eq_endpoints]
  have h_exp_diff_one : Complex.exp (Complex.I * ((θ 1 - θ 0 : ℝ) : ℂ)) = 1 := by
    have h_split : Complex.I * ((θ 1 - θ 0 : ℝ) : ℂ) =
        Complex.I * (θ 1 : ℂ) - Complex.I * (θ 0 : ℂ) := by push_cast; ring
    rw [h_split, Complex.exp_sub, h_exp_eq, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h_exp_diff_one
  have h_diff_eq : ((θ 1 - θ 0 : ℝ) : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ)) := by
    refine mul_left_cancel₀ Complex.I_ne_zero ?_
    rw [hn]
    ring
  have h_winding_eq : ((θ 1 - θ 0 : ℝ) : ℂ) / (2 * Real.pi) = (n : ℂ) := by
    rw [h_diff_eq]
    have : (Real.pi : ℂ) ≠ 0 := mod_cast Real.pi_ne_zero
    field_simp
  exact ⟨n, h_winding_eq ▸ h_winding⟩

/-- For a Lipschitz `γ` avoiding `w` with positive distance, the integrand
`γ'(t)/(γ(t) − w)` is interval-integrable on `[0, 1]`. -/
theorem intervalIntegrable_div_lipschitz
    (γ : PiecewiseC1Path x y) {w : ℂ}
    {δ : ℝ} (hδ_pos : 0 < δ)
    (h_dist_lb : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ.toPath.extend t - w‖)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    IntervalIntegrable
      (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - w))
      MeasureTheory.volume 0 1 := by
  have h_deriv_int : IntervalIntegrable (deriv γ.toPath.extend)
      MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
    exact MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (stronglyMeasurable_deriv _).aestronglyMeasurable
      (ae_restrict_of_ae (Filter.Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hLip))
  have h_avoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t - w ≠ 0 := fun t ht heq => by
    have := h_dist_lb t ht
    rw [heq, norm_zero] at this
    linarith
  have h_cont : ContinuousOn (fun t => (γ.toPath.extend t - w)⁻¹) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (zero_le_one' ℝ)]
    exact (γ.toPath.continuous_extend.continuousOn.sub continuousOn_const).inv₀ h_avoid
  simp_rw [div_eq_mul_inv]
  exact h_deriv_int.mul_continuousOn h_cont

/-- **W-4 (Winding locally constant).** For a closed Lipschitz piecewise C¹ path `γ`
avoiding `w`, the generalized winding number is constant on a neighborhood of `w`. -/
theorem generalizedWindingNumber_locally_const_of_closed
    (γ : PiecewiseC1Path x x) {w : ℂ}
    (h_avoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t ≠ w)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
      generalizedWindingNumber γ w' = generalizedWindingNumber γ w := by
  obtain ⟨ε₀, hε₀_pos, h_dist_lb⟩ := ball_dist_to_curve_lb h_avoid
  have h_cont := generalizedWindingNumber_continuousAt_of_avoids h_avoid hLip
  rw [Metric.continuousAt_iff] at h_cont
  obtain ⟨ε, hε_pos, h_close⟩ := h_cont (1 / 2) (by norm_num)
  refine ⟨min ε ε₀, lt_min hε_pos hε₀_pos, ?_⟩
  intro w' hw'
  rw [Metric.mem_ball] at hw'
  have hw'_in_ε₀ : w' ∈ Metric.ball w ε₀ :=
    Metric.mem_ball.mpr (hw'.trans_le (min_le_right _ _))
  have hw_in : w ∈ Metric.ball w ε₀ := Metric.mem_ball_self hε₀_pos
  have winding_int : ∀ w'' ∈ Metric.ball w ε₀,
      ∃ n : ℤ, HasGeneralizedWindingNumber γ w'' (n : ℂ) := fun w'' hw'' =>
    hasGeneralizedWindingNumber_integer_of_closed γ
      ⟨ε₀, hε₀_pos, h_dist_lb w'' hw''⟩
      (intervalIntegrable_div_lipschitz γ hε₀_pos (h_dist_lb w'' hw'') hLip)
  obtain ⟨n_w', h_n_w'⟩ := winding_int w' hw'_in_ε₀
  obtain ⟨n_w, h_n_w⟩ := winding_int w hw_in
  have h_eq_w' : generalizedWindingNumber γ w' = (n_w' : ℂ) := h_n_w'.eq
  have h_eq_w : generalizedWindingNumber γ w = (n_w : ℂ) := h_n_w.eq
  have h_dist_int : dist ((n_w' : ℂ)) ((n_w : ℂ)) < 1 / 2 :=
    h_eq_w' ▸ h_eq_w ▸ h_close (hw'.trans_le (min_le_left _ _))
  have h_int_eq : n_w' = n_w := by
    by_contra h_ne
    have h_one_le : (1 : ℝ) ≤ |((n_w' - n_w : ℤ) : ℝ)| :=
      mod_cast Int.one_le_abs (sub_ne_zero.mpr h_ne)
    have h_norm_eq : ‖((n_w' : ℂ) - (n_w : ℂ))‖ = |((n_w' - n_w : ℤ) : ℝ)| := by
      rw [show ((n_w' : ℂ) - (n_w : ℂ)) = (((n_w' - n_w : ℤ) : ℂ)) by push_cast; ring,
        Complex.norm_intCast]
    rw [Complex.dist_eq, h_norm_eq] at h_dist_int
    linarith
  rw [h_eq_w', h_eq_w, h_int_eq]

end Complex

end
