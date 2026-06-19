/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.BoundaryWinding
import LeanModularForms.ForMathlib.InteriorWinding
import LeanModularForms.ForMathlib.SmoothBoundaryWindingProof

/-!
# SmoothBoundaryWindingData for seg1 (right vertical edge)

At a point `z₀` strictly inside the right vertical edge of the FD boundary
(`z₀.re = 1/2`, `z₀.im ∈ (√3/2, H)`), we construct `SmoothBoundaryWindingData`
assuming the analytical `ArcFTCHyp` hypothesis is provided externally.

## Geometric setup

On seg1, `γ(t) = 1/2 + (H - K·t)·I` where `K = 5(H - √3/2)` is the vertical
speed. For `z₀ = 1/2 + c·I` with `c ∈ (√3/2, H)`, the crossing parameter is
`t₀ = (H - c)/K ∈ (0, 1/5)`, and the distance to `γ(t)` on seg1 is exactly
`‖γ(t) - z₀‖ = K·|t - t₀|`, giving the linear cutoff `δ(ε) = ε/K`.

## Main results

* `smoothBoundaryData_seg1_of_ftcHyp` -- constructs `SmoothBoundaryWindingData`
  at a generic smooth seg1 point from an external `ArcFTCHyp`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Vertical speed on seg1: `K = 5(H - √3/2)`. Positive when `H > √3/2`. -/
def seg1Speed (H : ℝ) : ℝ := 5 * (H - Real.sqrt 3 / 2)

theorem seg1Speed_pos {H : ℝ} (hH : Real.sqrt 3 / 2 < H) : 0 < seg1Speed H := by
  unfold seg1Speed; linarith

/-- Crossing parameter on seg1 for the point `1/2 + c·I`:
`t₀ = (H - c) / seg1Speed H`. -/
def seg1T₀ (H c : ℝ) : ℝ := (H - c) / seg1Speed H

theorem seg1T₀_pos {H c : ℝ} (hH : Real.sqrt 3 / 2 < H) (hc : c < H) :
    0 < seg1T₀ H c :=
  div_pos (by linarith) (seg1Speed_pos hH)

theorem seg1T₀_lt_one_fifth {H c : ℝ} (hH : Real.sqrt 3 / 2 < H) (hc : Real.sqrt 3 / 2 < c) :
    seg1T₀ H c < 1/5 := by
  rw [seg1T₀, div_lt_iff₀ (seg1Speed_pos hH), seg1Speed]; linarith

theorem seg1T₀_mem_Ioo {H c : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (hc_lo : Real.sqrt 3 / 2 < c) (hc_hi : c < H) :
    seg1T₀ H c ∈ Ioo (0 : ℝ) 1 :=
  ⟨seg1T₀_pos hH hc_hi,
    lt_trans (seg1T₀_lt_one_fifth hH hc_lo) (by norm_num : (1/5 : ℝ) < 1)⟩

private theorem fdBoundaryFun_seg1_im_speed (H t : ℝ) (ht : t ≤ 1/5) :
    (fdBoundaryFun H t).im = H - seg1Speed H * t := by
  rw [fdBoundaryFun_seg1_im H t ht]; unfold seg1Speed; ring

/-- For `z₀` on seg1 (i.e. `z₀.re = 1/2` and `z₀.im = c`), the distance from
`fdBoundaryFun H t` to `z₀` on seg1 equals `seg1Speed H · |t - seg1T₀ H c|`. -/
theorem fdBoundaryFun_seg1_dist_eq {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2) (t : ℝ) (ht : t ≤ 1/5) :
    ‖fdBoundaryFun H t - z₀‖ = seg1Speed H * |t - seg1T₀ H z₀.im| := by
  have hK_pos : 0 < seg1Speed H := seg1Speed_pos hH
  have h_re_zero : (fdBoundaryFun H t - z₀).re = 0 := by
    rw [sub_re, fdBoundaryFun_seg1_re H t ht, hz_re, sub_self]
  have h_im_eq : (fdBoundaryFun H t - z₀).im = seg1Speed H * (seg1T₀ H z₀.im - t) := by
    rw [sub_im, fdBoundaryFun_seg1_im_speed H t ht]
    unfold seg1T₀; field_simp; ring
  rw [Complex.norm_def, Complex.normSq_apply, h_re_zero, mul_zero, zero_add,
    ← sq, Real.sqrt_sq_eq_abs, h_im_eq, abs_mul, abs_of_pos hK_pos, abs_sub_comm]

/-- `K · t₀ = H - z₀.im` for the seg1 crossing parameter. -/
theorem seg1Speed_mul_t₀ {H c : ℝ} (hH : Real.sqrt 3 / 2 < H) :
    seg1Speed H * seg1T₀ H c = H - c := by
  simp [seg1T₀, mul_div_cancel₀ _ (seg1Speed_pos hH).ne']

/-- `K · (1/5 - t₀) = z₀.im - √3/2` for the seg1 crossing parameter. -/
theorem seg1Speed_mul_one_fifth_sub_t₀ {H c : ℝ} (hH : Real.sqrt 3 / 2 < H) :
    seg1Speed H * (1/5 - seg1T₀ H c) = c - Real.sqrt 3 / 2 := by
  rw [mul_sub, seg1Speed_mul_t₀ hH, seg1Speed]; ring

private theorem linDelta_lt_t₀ {H ε : ℝ} (hH : Real.sqrt 3 / 2 < H) {c : ℝ}
    (hε : ε < H - c) : linDelta (seg1Speed H) ε < seg1T₀ H c := by
  unfold linDelta
  rw [div_lt_iff₀ (seg1Speed_pos hH), mul_comm, seg1Speed_mul_t₀ hH]
  exact hε

private theorem linDelta_lt_one_fifth_sub_t₀ {H ε : ℝ} (hH : Real.sqrt 3 / 2 < H) {c : ℝ}
    (hε : ε < c - Real.sqrt 3 / 2) : linDelta (seg1Speed H) ε < 1/5 - seg1T₀ H c := by
  unfold linDelta
  rw [div_lt_iff₀ (seg1Speed_pos hH), mul_comm, seg1Speed_mul_one_fifth_sub_t₀ hH]
  exact hε

/-- Near bound on seg1: for `|t - t₀| ≤ ε/(seg1Speed H)` with `ε` small enough to keep
`t ≤ 1/5`, the distance is `≤ ε`. -/
theorem seg1_near_of_linDelta {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2) {ε : ℝ} (hε_lo : ε < z₀.im - Real.sqrt 3 / 2)
    {t : ℝ} (ht : |t - seg1T₀ H z₀.im| ≤ ε / seg1Speed H) :
    ‖fdBoundaryFun H t - z₀‖ ≤ ε := by
  have h_t₀_hi : ε / seg1Speed H < 1/5 - seg1T₀ H z₀.im := by
    rw [div_lt_iff₀ (seg1Speed_pos hH), mul_comm, seg1Speed_mul_one_fifth_sub_t₀ hH]
    exact hε_lo
  have h_t_hi : t ≤ 1/5 := by linarith [(abs_le.mp ht).2]
  rw [fdBoundaryFun_seg1_dist_eq hH hz_re t h_t_hi, mul_comm]
  exact (le_div_iff₀ (seg1Speed_pos hH)).mp ht

/-- Generic vertical-side norm bound: when `z₀.re ^ 2 = 1/4` and
`z₀.im > √3/2`, the norm `‖z₀‖` exceeds 1. -/
theorem norm_gt_one_of_re_sq_quarter {z₀ : ℂ} (hz_re_sq : z₀.re ^ 2 = 1/4)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) : 1 < ‖z₀‖ := by
  nlinarith [Complex.normSq_eq_norm_sq z₀, norm_nonneg z₀,
    Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num), hc_lo, Real.sqrt_nonneg 3,
    Complex.normSq_apply z₀, hz_re_sq, sq_nonneg z₀.im]

/-- For `z₀` on seg1 with `z₀.im > √3/2`, the norm `‖z₀‖` exceeds 1. -/
theorem norm_gt_one_of_seg1_interior {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) : 1 < ‖z₀‖ :=
  norm_gt_one_of_re_sq_quarter (by rw [hz_re]; norm_num) hc_lo

/-- Distance from a seg1 interior point to seg2/seg3 (unit-circle arcs):
at least `‖z₀‖ - 1 > 0`. -/
theorem seg1_dist_arc {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) {H t : ℝ}
    (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    ‖z₀‖ - 1 ≤ ‖fdBoundaryFun H t - z₀‖ :=
  fdBoundaryFun_arc_dist (norm_gt_one_of_seg1_interior hz_re hc_lo) ht1 ht2

/-- Distance from a seg1 point to seg4 (left vertical): at least 1. -/
theorem seg1_dist_seg4 {z₀ : ℂ} (hz_re : z₀.re = 1/2) {H t : ℝ}
    (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    1 ≤ ‖fdBoundaryFun H t - z₀‖ := by
  have := Complex.abs_re_le_norm (fdBoundaryFun H t - z₀)
  rw [sub_re, fdBoundaryFun_seg4_re H t ht3 ht4, hz_re] at this
  linarith [abs_le.mp this |>.1]

/-- Distance from a seg1 interior point to seg5 (horizontal top): at least `H - z₀.im`. -/
theorem seg1_dist_seg5 {z₀ : ℂ} (hz_hi : z₀.im < H) {t : ℝ}
    (ht : 4/5 < t) : H - z₀.im ≤ ‖fdBoundaryFun H t - z₀‖ :=
  fdBoundaryFun_seg5_im_dist hz_hi ht

/-- Far bound on seg1: for `t ∈ [0, 1/5]` with `ε/(seg1Speed H) < |t - t₀|`,
the distance exceeds `ε`. -/
theorem seg1_far_on_seg1 {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    {ε t : ℝ} (ht : t ≤ 1/5) (hδt : ε / seg1Speed H < |t - seg1T₀ H z₀.im|) :
    ε < ‖fdBoundaryFun H t - z₀‖ := by
  rw [fdBoundaryFun_seg1_dist_eq hH hz_re t ht, mul_comm]
  exact (div_lt_iff₀ (seg1Speed_pos hH)).mp hδt

/-- Generic vertical-side norm bound: when `z₀.re^2 = 1/4` and `z₀.im ≥ √3/2`,
the arc bound `‖z₀‖ - 1` is at most the vertical-width bound `z₀.im - √3/2`.
This lets us drop one of the constraints in the threshold computation.
Used for both the right vertical (`z₀.re = 1/2`) and the left vertical
(`z₀.re = -1/2`). -/
theorem norm_sub_one_le_im_sub_sqrt3_of_re_sq {z₀ : ℂ} (hz_re_sq : z₀.re ^ 2 = 1/4)
    (hc_lo : Real.sqrt 3 / 2 ≤ z₀.im) :
    ‖z₀‖ - 1 ≤ z₀.im - Real.sqrt 3 / 2 := by
  have h_sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 :=
    Real.mul_self_sqrt (by norm_num : (3 : ℝ) ≥ 0)
  have h_nn_rhs : 0 ≤ z₀.im + 1 - Real.sqrt 3 / 2 := by
    nlinarith [h_sqrt3_sq, hc_lo, Real.sqrt_nonneg 3]
  have h_sq_ineq : ‖z₀‖ ^ 2 ≤ (z₀.im + 1 - Real.sqrt 3 / 2) ^ 2 := by
    have h_norm_sq : ‖z₀‖ ^ 2 = 1/4 + z₀.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← sq, hz_re_sq]; ring
    rw [h_norm_sq]
    nlinarith [h_sqrt3_sq, hc_lo]
  have h_target := Real.sqrt_le_sqrt h_sq_ineq
  rw [Real.sqrt_sq (norm_nonneg z₀), Real.sqrt_sq h_nn_rhs] at h_target
  linarith

/-- For `z₀` on seg1 with `z₀.im > √3/2`, the arc-distance bound `‖z₀‖ - 1`
is at most the vertical-width bound `z₀.im - √3/2`. This lets us drop one of
the constraints in the threshold computation. -/
theorem norm_sub_one_le_im_sub_sqrt3 {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    (hc_lo : Real.sqrt 3 / 2 ≤ z₀.im) :
    ‖z₀‖ - 1 ≤ z₀.im - Real.sqrt 3 / 2 :=
  norm_sub_one_le_im_sub_sqrt3_of_re_sq (by rw [hz_re]; norm_num) hc_lo

/-- The threshold below which `ε` must lie for every near/far bound to hold
at a seg1 interior point `z₀`:
`min(‖z₀‖ - 1, 1, H - z₀.im)`. All three are positive. The arc bound
`‖z₀‖ - 1` dominates the seg1 vertical-width constraint `z₀.im - √3/2`. -/
def seg1Threshold (H : ℝ) (z₀ : ℂ) : ℝ :=
  min (min (‖z₀‖ - 1) 1) (H - z₀.im)

theorem seg1Threshold_pos {H : ℝ} {z₀ : ℂ}
    (hz_re : z₀.re = 1/2) (hc_lo : Real.sqrt 3 / 2 < z₀.im) (hc_hi : z₀.im < H) :
    0 < seg1Threshold H z₀ :=
  lt_min (lt_min (by linarith [norm_gt_one_of_seg1_interior hz_re hc_lo]) zero_lt_one)
    (by linarith)

/-- Far bound: for `t ∈ [0, 1]` outside the δ-window around `t₀`, the distance
to `z₀` exceeds `ε`. -/
theorem seg1_far_bound {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) (hc_hi : z₀.im < H)
    {ε : ℝ} (hε_lt : ε < seg1Threshold H z₀)
    {t : ℝ} (_ht_mem : t ∈ Icc (0 : ℝ) 1)
    (hδt : ε / seg1Speed H < |t - seg1T₀ H z₀.im|) :
    ε < ‖fdBoundaryFun H t - z₀‖ := by
  have h_eps_arc : ε < ‖z₀‖ - 1 :=
    hε_lt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h_eps_one : ε < 1 :=
    hε_lt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have h_eps_top : ε < H - z₀.im := hε_lt.trans_le (min_le_right _ _)
  rcases le_or_gt t (1/5) with h1 | h1
  · exact seg1_far_on_seg1 hH hz_re h1 hδt
  rcases le_or_gt t (3/5) with h2 | h2
  · exact h_eps_arc.trans_le (seg1_dist_arc hz_re hc_lo h1 h2)
  rcases le_or_gt t (4/5) with h3 | h3
  · exact h_eps_one.trans_le (seg1_dist_seg4 hz_re h2 h3)
  exact h_eps_top.trans_le (seg1_dist_seg5 hc_hi h3)

/-- For a smooth seg1 point `z₀` (i.e. `z₀.re = 1/2`, `z₀.im ∈ (√3/2, H)`),
construct `SmoothBoundaryWindingData` from an external `ArcFTCHyp`. -/
def smoothBoundaryData_seg1_of_ftcHyp {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {z₀ : ℂ} (hz_re : z₀.re = 1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) (hc_hi : z₀.im < H)
    (ftcHyp : ArcFTCHyp γ z₀ (seg1T₀ H z₀.im) (linDelta (seg1Speed H))
      (seg1Threshold H z₀) (-(↑Real.pi * I))) :
    SmoothBoundaryWindingData γ z₀ where
  t₀ := seg1T₀ H z₀.im
  ht₀ := seg1T₀_mem_Ioo hH hc_lo hc_hi
  δ := linDelta (seg1Speed H)
  threshold := seg1Threshold H z₀
  hthresh := seg1Threshold_pos hz_re hc_lo hc_hi
  hδ_pos := fun _ hε _ ↦ linDelta_pos (seg1Speed_pos hH) hε
  hδ_small := fun ε _ hε_thr ↦ by
    have h_lin_lt_t₀ := linDelta_lt_t₀ hH (hε_thr.trans_le (min_le_right _ _))
    refine lt_min h_lin_lt_t₀ (h_lin_lt_t₀.trans ?_)
    linarith [seg1T₀_lt_one_fifth hH hc_lo]
  h_far := fun _ _ hε_thr t ht hδt ↦ by
    rw [hγ t ht]; exact seg1_far_bound hH hz_re hc_lo hc_hi hε_thr ht hδt
  h_near := fun ε _ hε_thr t ht ↦ by
    have h_eps_arc : ε < ‖z₀‖ - 1 :=
      hε_thr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have h_eps_width : ε < z₀.im - Real.sqrt 3 / 2 :=
      h_eps_arc.trans_le (norm_sub_one_le_im_sub_sqrt3 hz_re hc_lo.le)
    have h_t_lo : 0 ≤ t := by
      linarith [(abs_le.mp ht).1, seg1T₀_pos hH hc_hi,
        linDelta_lt_t₀ hH (hε_thr.trans_le (min_le_right _ _))]
    have h_t_hi : t ≤ 1 := by
      linarith [(abs_le.mp ht).2, linDelta_lt_one_fifth_sub_t₀ hH h_eps_width]
    rw [hγ t ⟨h_t_lo, h_t_hi⟩]
    exact seg1_near_of_linDelta hH hz_re h_eps_width ht
  ftcHyp := ftcHyp

end
