/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.CrossingAtI
import LeanModularForms.ForMathlib.InteriorWinding
import LeanModularForms.ForMathlib.SmoothBoundaryWindingProof
import LeanModularForms.ForMathlib.WindingWeightProofs

/-!
# SmoothBoundaryWindingData for the arc (seg 2 ∪ seg 3)

At a point `z₀ = exp(iθ₀)` on the FD unit-circle arc, excluding the three
elliptic points (`θ₀ ∈ (π/3, 2π/3) \ {π/3, π/2, 2π/3}`), the distance is
`‖γ(t) - z₀‖ = 2|sin(5π/12 · (t - t₀))|` via the half-angle identity.
We reuse the `arcsinDelta` cutoff from `CrossingAtI.lean` which exactly
inverts this relation.

## Main results

* `smoothBoundaryData_arc_of_ftcHyp` -- constructs `SmoothBoundaryWindingData`
  at a generic smooth arc point from an external `ArcFTCHyp`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Crossing parameter on the arc for the angle `θ₀`:
`arcT₀(θ₀) = (6·θ₀ - π) / (5π)`. -/
def arcT₀ (θ₀ : ℝ) : ℝ := (6 * θ₀ - Real.pi) / (5 * Real.pi)

theorem arcT₀_gt_one_fifth {θ₀ : ℝ} (h : Real.pi / 3 < θ₀) : 1/5 < arcT₀ θ₀ := by
  rw [arcT₀, lt_div_iff₀ (by positivity : (0 : ℝ) < 5 * Real.pi)]
  nlinarith [Real.pi_pos]

theorem arcT₀_lt_three_fifths {θ₀ : ℝ} (h : θ₀ < 2 * Real.pi / 3) : arcT₀ θ₀ < 3/5 := by
  rw [arcT₀, div_lt_iff₀ (by positivity : (0 : ℝ) < 5 * Real.pi)]
  nlinarith [Real.pi_pos]

theorem arcT₀_mem_Ioo {θ₀ : ℝ} (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) :
    arcT₀ θ₀ ∈ Ioo (0 : ℝ) 1 :=
  ⟨(by norm_num : (0 : ℝ) < 1/5).trans (arcT₀_gt_one_fifth h_lo),
    (arcT₀_lt_three_fifths h_hi).trans (by norm_num : (3/5 : ℝ) < 1)⟩

/-- `fdArcAngle(arcT₀ θ₀) = θ₀`. -/
theorem fdArcAngle_arcT₀ (θ₀ : ℝ) : fdArcAngle (arcT₀ θ₀) = θ₀ := by
  rw [fdArcAngle, arcT₀]
  field_simp
  ring

/-- For `z₀ = exp(i·θ₀)` and `t ∈ (1/5, 3/5]`, the distance is
`2|sin(5π/12 · (t - arcT₀ θ₀))|`. -/
theorem arc_dist_eq (H : ℝ) (θ₀ t : ℝ) (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    ‖fdBoundaryFun H t - exp (↑θ₀ * I)‖ =
      2 * |Real.sin (5 * (t - arcT₀ θ₀) * Real.pi / 12)| := by
  rw [fdBoundaryFun_arc_eq_exp H t ht1 ht2, norm_exp_sub_exp,
    show (fdArcAngle t - θ₀) / 2 = 5 * (t - arcT₀ θ₀) * Real.pi / 12 by
      rw [fdArcAngle, arcT₀]
      field_simp
      ring]

/-- The half-angle absolute value, written in factored form. -/
private theorem arc_half_angle_abs (θ₀ t : ℝ) :
    |5 * (t - arcT₀ θ₀) * Real.pi / 12| =
      5 * Real.pi / 12 * |t - arcT₀ θ₀| := by
  rw [show 5 * (t - arcT₀ θ₀) * Real.pi / 12 = 5 * Real.pi / 12 * (t - arcT₀ θ₀) by ring,
    abs_mul, abs_of_pos (by positivity)]

/-- Near bound on the arc: for `|t - t₀| ≤ arcsinDelta(ε)` and `t ∈ (1/5, 3/5]`,
the distance is `≤ ε`. -/
theorem arc_near_generic (H : ℝ) {θ₀ ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3)
    {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) (ht : |t - arcT₀ θ₀| ≤ arcsinDelta ε) :
    ‖fdBoundaryFun H t - exp (↑θ₀ * I)‖ ≤ ε := by
  rw [arc_dist_eq H θ₀ t ht1 ht2]
  have hα_le_asin : |5 * (t - arcT₀ θ₀) * Real.pi / 12| ≤ Real.arcsin (ε / 2) := by
    rw [arc_half_angle_abs, ← half_angle_arcsinDelta]
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  have hα_le_pi : |5 * (t - arcT₀ θ₀) * Real.pi / 12| ≤ Real.pi := by
    linarith [Real.arcsin_le_pi_div_two (ε / 2), Real.pi_pos]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hα_le_pi]
  have h_sin_le : Real.sin |5 * (t - arcT₀ θ₀) * Real.pi / 12| ≤ ε / 2 := by
    rw [← Real.sin_arcsin (show (-1 : ℝ) ≤ ε / 2 by linarith)
      (show ε / 2 ≤ 1 by linarith)]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [abs_nonneg (5 * (t - arcT₀ θ₀) * Real.pi / 12)])
      (Real.arcsin_le_pi_div_two _) hα_le_asin
  linarith

/-- Far bound on the arc: for `t ∈ (1/5, 3/5]` with `arcsinDelta(ε) < |t - t₀|`,
and assuming `|t - t₀| ≤ 2/5` (which follows from `t, t₀ ∈ [1/5, 3/5]`),
the distance exceeds `ε`. -/
theorem arc_far_on_arc {H θ₀ ε t : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3)
    (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) (ht₀_lo : 1/5 ≤ arcT₀ θ₀) (ht₀_hi : arcT₀ θ₀ ≤ 3/5)
    (hδt : arcsinDelta ε < |t - arcT₀ θ₀|) :
    ε < ‖fdBoundaryFun H t - exp (↑θ₀ * I)‖ := by
  have hpi := Real.pi_pos
  rw [arc_dist_eq H θ₀ t ht1 ht2]
  have h_diff_le : |t - arcT₀ θ₀| ≤ 2/5 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hα_le_pi6 : |5 * (t - arcT₀ θ₀) * Real.pi / 12| ≤ Real.pi / 6 := by
    rw [arc_half_angle_abs]
    calc 5 * Real.pi / 12 * |t - arcT₀ θ₀|
        ≤ 5 * Real.pi / 12 * (2/5) := by gcongr
      _ = Real.pi / 6 := by ring
  have hα_le_pi : |5 * (t - arcT₀ θ₀) * Real.pi / 12| ≤ Real.pi := by linarith
  have hα_gt_asin : Real.arcsin (ε / 2) < |5 * (t - arcT₀ θ₀) * Real.pi / 12| := by
    rw [arc_half_angle_abs, ← half_angle_arcsinDelta]
    exact mul_lt_mul_of_pos_left hδt (by positivity)
  have harc_nn : 0 ≤ Real.arcsin (ε / 2) := Real.arcsin_nonneg.mpr (by linarith)
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hα_le_pi]
  have h_sin_gt : ε / 2 < Real.sin |5 * (t - arcT₀ θ₀) * Real.pi / 12| := by
    rw [← Real.sin_arcsin (show (-1 : ℝ) ≤ ε / 2 by linarith)
      (show ε / 2 ≤ 1 by linarith)]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hα_gt_asin
  linarith

/-- `(exp (↑θ₀ * I)).re = Real.cos θ₀`. -/
theorem arcZ₀_re_eq (θ₀ : ℝ) : (exp (↑θ₀ * I)).re = Real.cos θ₀ :=
  Complex.exp_ofReal_mul_I_re θ₀

/-- `(exp (↑θ₀ * I)).im = Real.sin θ₀`. -/
theorem arcZ₀_im_eq (θ₀ : ℝ) : (exp (↑θ₀ * I)).im = Real.sin θ₀ :=
  Complex.exp_ofReal_mul_I_im θ₀

/-- For `z₀ = exp(iθ₀)` with `θ₀ ∈ (π/3, 2π/3)`, we have `|z₀.re| < 1/2`. -/
theorem arcZ₀_abs_re_lt {θ₀ : ℝ} (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) :
    |(exp (↑θ₀ * I)).re| < 1/2 := by
  have hpi := Real.pi_pos
  rw [arcZ₀_re_eq, abs_lt]
  refine ⟨?_, ?_⟩
  · have h_cos_lt : Real.cos (2 * Real.pi / 3) < Real.cos θ₀ :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) h_hi
    have h_cos_2pi3 : Real.cos (2 * Real.pi / 3) = -1/2 := by
      rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]
      norm_num
    linarith
  · have h_cos_lt : Real.cos θ₀ < Real.cos (Real.pi / 3) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) h_lo
    rw [Real.cos_pi_div_three] at h_cos_lt
    linarith

/-- For `z₀ = exp(iθ₀)`, `z₀.im ≤ 1`. -/
theorem arcZ₀_im_le_one (θ₀ : ℝ) : (exp (↑θ₀ * I)).im ≤ 1 := by
  simpa [arcZ₀_im_eq] using Real.sin_le_one θ₀

/-- Gap from `t₀` to the arc boundaries `1/5` and `3/5`. Positive when
`t₀ ∈ (1/5, 3/5) \ {2/5}` (but also at `2/5`). -/
def arcGap (θ₀ : ℝ) : ℝ := min (arcT₀ θ₀ - 1/5) (3/5 - arcT₀ θ₀)

theorem arcGap_pos {θ₀ : ℝ} (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) :
    0 < arcGap θ₀ := by
  unfold arcGap
  refine lt_min ?_ ?_
  · linarith [arcT₀_gt_one_fifth h_lo]
  · linarith [arcT₀_lt_three_fifths h_hi]

/-- `arcsinDelta(ε) ≤ 3ε/5` via Jordan's inequality for small `ε`. -/
theorem arcsinDelta_le_three_fifths_eps {ε : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 2/3) :
    arcsinDelta ε ≤ 3 * ε / 5 := by
  unfold arcsinDelta
  have h_jordan : Real.arcsin (ε / 2) ≤ Real.pi / 2 * (ε / 2) :=
    arcsin_le_pi_half_mul (by linarith) (by linarith)
  calc 12 / (5 * Real.pi) * Real.arcsin (ε / 2)
      ≤ 12 / (5 * Real.pi) * (Real.pi / 2 * (ε / 2)) :=
        mul_le_mul_of_nonneg_left h_jordan (by positivity)
    _ = 3 * ε / 5 := by
      field_simp
      ring

/-- If `ε < 5*g/3` (for positive `g ≤ 1/5`), then `arcsinDelta(ε) < g`. -/
theorem arcsinDelta_lt_of_gap {g ε : ℝ} (hg_pos : 0 < g) (hg_le : g ≤ 1/5)
    (hε : 0 < ε) (hε_lt : ε < 5 * g / 3) :
    arcsinDelta ε < g := by
  have hε_le : ε ≤ 2/3 := by linarith
  calc arcsinDelta ε ≤ 3 * ε / 5 := arcsinDelta_le_three_fifths_eps hε hε_le
    _ < 3 * (5 * g / 3) / 5 := by linarith
    _ = g := by ring

/-- Threshold for the arc constructor:
`min(1/2 - |z₀.re|, H - 1, 1/3, 5*arcGap/3)`. All positive when `θ₀ ∈ (π/3, 2π/3)`
and `H > 1`. -/
def arcThreshold (H : ℝ) (θ₀ : ℝ) : ℝ :=
  min (min (1/2 - |(exp (↑θ₀ * I)).re|) (H - 1))
      (min (1/3) (5 * arcGap θ₀ / 3))

theorem arcThreshold_pos {H θ₀ : ℝ} (hH : 1 < H) (h_lo : Real.pi / 3 < θ₀)
    (h_hi : θ₀ < 2 * Real.pi / 3) : 0 < arcThreshold H θ₀ := by
  unfold arcThreshold
  refine lt_min (lt_min ?_ ?_) (lt_min ?_ ?_)
  · linarith [arcZ₀_abs_re_lt h_lo h_hi]
  · linarith
  · norm_num
  · linarith [arcGap_pos h_lo h_hi]

theorem arcThreshold_lt_re {H θ₀ ε : ℝ} (h : ε < arcThreshold H θ₀) :
    ε < 1/2 - |(exp (↑θ₀ * I)).re| :=
  h.trans_le ((min_le_left _ _).trans (min_le_left _ _))

theorem arcThreshold_lt_top {H θ₀ ε : ℝ} (h : ε < arcThreshold H θ₀) :
    ε < H - 1 :=
  h.trans_le ((min_le_left _ _).trans (min_le_right _ _))

theorem arcThreshold_lt_third {H θ₀ ε : ℝ} (h : ε < arcThreshold H θ₀) :
    ε < 1/3 :=
  h.trans_le ((min_le_right _ _).trans (min_le_left _ _))

theorem arcThreshold_lt_gap {H θ₀ ε : ℝ} (h : ε < arcThreshold H θ₀) :
    ε < 5 * arcGap θ₀ / 3 :=
  h.trans_le ((min_le_right _ _).trans (min_le_right _ _))

/-- `arcGap ≤ 1/5` always — the maximum is at `t₀ = 2/5`. -/
theorem arcGap_le_one_fifth (θ₀ : ℝ) : arcGap θ₀ ≤ 1/5 := by
  unfold arcGap
  rcases le_total (arcT₀ θ₀) (2/5) with h | h
  · exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (by linarith)

/-- For `ε` below the threshold, `arcsinDelta(ε) < arcGap θ₀`. -/
theorem arcsinDelta_lt_arcGap {H θ₀ ε : ℝ} (h_lo : Real.pi / 3 < θ₀)
    (h_hi : θ₀ < 2 * Real.pi / 3) (hε : 0 < ε) (hε_thr : ε < arcThreshold H θ₀) :
    arcsinDelta ε < arcGap θ₀ :=
  arcsinDelta_lt_of_gap (arcGap_pos h_lo h_hi) (arcGap_le_one_fifth θ₀)
    hε (arcThreshold_lt_gap hε_thr)

/-- Both gap bounds: `arcsinDelta ε < arcT₀ θ₀ - 1/5` and `arcsinDelta ε < 3/5 - arcT₀ θ₀`. -/
theorem arcsinDelta_lt_arcT₀_bounds {H θ₀ ε : ℝ} (h_lo : Real.pi / 3 < θ₀)
    (h_hi : θ₀ < 2 * Real.pi / 3) (hε : 0 < ε) (hε_thr : ε < arcThreshold H θ₀) :
    arcsinDelta ε < arcT₀ θ₀ - 1/5 ∧ arcsinDelta ε < 3/5 - arcT₀ θ₀ :=
  have h := arcsinDelta_lt_arcGap h_lo h_hi hε hε_thr
  ⟨h.trans_le (min_le_left _ _), h.trans_le (min_le_right _ _)⟩

/-- Combined far bound dispatching over segments. -/
theorem arc_far_bound {H : ℝ} (hH : 1 < H) {θ₀ : ℝ} (h_lo : Real.pi / 3 < θ₀)
    (h_hi : θ₀ < 2 * Real.pi / 3) {ε : ℝ} (hε_pos : 0 < ε)
    (hε_lt : ε < arcThreshold H θ₀) {t : ℝ} (_ht_mem : t ∈ Icc (0 : ℝ) 1)
    (hδt : arcsinDelta ε < |t - arcT₀ θ₀|) :
    ε < ‖fdBoundaryFun H t - exp (↑θ₀ * I)‖ := by
  have h_eps_re : ε < 1/2 - |(exp (↑θ₀ * I)).re| := arcThreshold_lt_re hε_lt
  have hre := arcZ₀_abs_re_lt h_lo h_hi
  by_cases h1 : t ≤ 1/5
  · exact h_eps_re.trans_le (fdBoundaryFun_seg1_re_dist hre h1)
  push Not at h1
  by_cases h2 : t ≤ 3/5
  · exact arc_far_on_arc hε_pos (arcThreshold_lt_third hε_lt) h1 h2
      (arcT₀_gt_one_fifth h_lo).le (arcT₀_lt_three_fifths h_hi).le hδt
  push Not at h2
  by_cases h3 : t ≤ 4/5
  · exact h_eps_re.trans_le (fdBoundaryFun_seg4_re_dist hre h2 h3)
  push Not at h3
  have him := arcZ₀_im_le_one θ₀
  have := fdBoundaryFun_seg5_im_dist (H := H) (z := exp (↑θ₀ * I)) (by linarith) h3
  linarith [arcThreshold_lt_top hε_lt]

/-- For a smooth arc point `z₀ = exp(iθ₀)` with `θ₀ ∈ (π/3, 2π/3) \ {π/2}`,
construct `SmoothBoundaryWindingData` from an external `ArcFTCHyp`. -/
def smoothBoundaryData_arc_of_ftcHyp {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {θ₀ : ℝ} (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    (ftcHyp : ArcFTCHyp γ (exp (↑θ₀ * I)) (arcT₀ θ₀) arcsinDelta
      (arcThreshold H θ₀) (-(↑Real.pi * I))) :
    SmoothBoundaryWindingData γ (exp (↑θ₀ * I)) where
  t₀ := arcT₀ θ₀
  ht₀ := arcT₀_mem_Ioo h_lo h_hi
  δ := arcsinDelta
  threshold := arcThreshold H θ₀
  hthresh := arcThreshold_pos hH h_lo h_hi
  hδ_pos := fun ε hε _ => arcsinDelta_pos hε
  hδ_small := fun ε hε hε_thr => by
    obtain ⟨hδ_lo, hδ_hi⟩ := arcsinDelta_lt_arcT₀_bounds h_lo h_hi hε hε_thr
    refine lt_min ?_ ?_
    · linarith [arcT₀_gt_one_fifth h_lo]
    · linarith [arcT₀_lt_three_fifths h_hi]
  h_far := fun ε hε hε_thr t ht hδt => by
    rw [hγ t ht]
    exact arc_far_bound hH h_lo h_hi hε hε_thr ht hδt
  h_near := fun ε hε hε_thr t ht => by
    obtain ⟨hδ_lo, hδ_hi⟩ := arcsinDelta_lt_arcT₀_bounds h_lo h_hi hε hε_thr
    obtain ⟨h_lo_bound, h_hi_bound⟩ := abs_le.mp ht
    rw [hγ t ⟨by linarith, by linarith⟩]
    exact arc_near_generic H hε (arcThreshold_lt_third hε_thr) (by linarith) (by linarith) ht
  ftcHyp := ftcHyp

end

