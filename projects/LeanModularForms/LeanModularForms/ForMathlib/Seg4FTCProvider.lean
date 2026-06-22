/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.BoundaryWindingSeg4Proof
import LeanModularForms.ForMathlib.SegmentAnalysis
import LeanModularForms.ForMathlib.SegmentFTC
import LeanModularForms.ForMathlib.VertSegFTCProvider
import LeanModularForms.ForMathlib.WindingWeightProofs

/-!
# `ArcFTCHyp` for the left vertical edge (seg4) at a generic point

Symmetric to seg1, but the crossing direction is reversed (seg4 goes UP
while seg1 goes DOWN). Because of this reversed orientation, we use
`ftc_log_on_segment` (not `ftc_log_neg_on_segment`): for seg4 z₀ all
relevant trajectory pieces are themselves in `Complex.slitPlane`, so
log can be taken directly without negation.

The arc, seg3, and seg5 pieces are shared with `Seg1FTCProvider.lean` via
`VertSegFTCProvider.lean`.

## Main results

* `arcFTCHyp_seg4` — the full `ArcFTCHyp` at any seg4 interior point
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Local alias: the `t ≤ 1/5` piece reference is the shared `vertSeg_h₀`. -/
private abbrev seg4_h₀ := vertSeg_h₀

/-- Local alias: the arc reference is the shared `vertSeg_h_arc`. -/
private abbrev seg4_h_arc := vertSeg_h_arc

private lemma seg4_h_arc_slitPlane {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im)
    {t : ℝ} (ht1 : 1/5 ≤ t) (ht3 : t ≤ 3/5) :
    seg4_h_arc z₀ t ∈ Complex.slitPlane := by
  unfold seg4_h_arc vertSeg_h_arc
  rcases eq_or_lt_of_le ht3 with h_eq | ht3_lt
  · rw [Complex.mem_slitPlane_iff]
    right
    rw [h_eq]
    have hpi := Real.pi_pos
    rw [show (fdArcAngle (3/5) : ℝ) = 2 * Real.pi / 3 by unfold fdArcAngle; ring]
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_add, add_zero]
    intro h_eq2
    nlinarith
  · rw [Complex.mem_slitPlane_iff]
    left
    have hpi := Real.pi_pos
    have hθ_lo : Real.pi / 3 ≤ fdArcAngle t := by
      unfold fdArcAngle
      nlinarith
    have hθ_hi : fdArcAngle t < 2 * Real.pi / 3 := by
      unfold fdArcAngle
      nlinarith
    have h_cos_gt : Real.cos (fdArcAngle t) > -1/2 := by
      have h_2pi3 : (2 * Real.pi / 3) ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
      have hθ_Icc : fdArcAngle t ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
      have := Real.strictAntiOn_cos hθ_Icc h_2pi3 hθ_hi
      have h_cos_2pi3 : Real.cos (2 * Real.pi / 3) = -1/2 := by
        rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
            Real.cos_pi_sub, Real.cos_pi_div_three]
        norm_num
      linarith
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, mul_one]
    rw [hz_re]
    linarith

private lemma seg4_h₀_slitPlane {H : ℝ} {z₀ : ℂ} (hz_re : z₀.re = -1/2) (t : ℝ) :
    seg4_h₀ H z₀ t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  unfold seg4_h₀ vertSeg_h₀
  norm_num [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, hz_re]

/-- Local alias: the seg3 reference is the shared `vertSeg_h₃`. -/
private abbrev seg4_h₃ := vertSeg_h₃

private lemma seg4_h₃_eq_pure_im {H : ℝ} {z₀ : ℂ} (hz_re : z₀.re = -1/2) (t : ℝ) :
    seg4_h₃ H z₀ t =
      ((Real.sqrt 3 / 2 + (5 * t - 3) * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ) * I := by
  unfold seg4_h₃ vertSeg_h₃
  rw [show (-1/2 - z₀.re : ℝ) = 0 by rw [hz_re]; ring]
  simp

private lemma seg4_h₃_slitPlane_of_ne {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2) {t : ℝ} (h_ne : t ≠ seg4T₀ H z₀.im) :
    seg4_h₃ H z₀ t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  rw [seg4_h₃_eq_pure_im hz_re]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero]
  intro h_eq
  have hK : 0 < seg1Speed H := seg1Speed_pos hH
  have hK_eq_seg4 : seg1Speed H * (seg4T₀ H z₀.im - 3/5) = z₀.im - Real.sqrt 3 / 2 := by
    unfold seg4T₀; field_simp; ring
  refine h_ne ?_
  have h_speed_eq : seg1Speed H * (t - 3/5) = z₀.im - Real.sqrt 3 / 2 := by
    unfold seg1Speed; linarith
  have hcancel : t - 3/5 = seg4T₀ H z₀.im - 3/5 :=
    mul_left_cancel₀ (ne_of_gt hK) (h_speed_eq.trans hK_eq_seg4.symm)
  linarith

private lemma seg4_h₃_left_slitPlane {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    {δ : ℝ} (hδ_pos : 0 < δ)
    {t : ℝ} (htd : t ≤ seg4T₀ H z₀.im - δ) :
    seg4_h₃ H z₀ t ∈ Complex.slitPlane :=
  seg4_h₃_slitPlane_of_ne hH hz_re (by linarith)

private lemma seg4_h₃_right_slitPlane {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    {δ : ℝ} (hδ_pos : 0 < δ)
    {t : ℝ} (htd : seg4T₀ H z₀.im + δ ≤ t) :
    seg4_h₃ H z₀ t ∈ Complex.slitPlane :=
  seg4_h₃_slitPlane_of_ne hH hz_re (by linarith)

/-- Local alias: the top horizontal reference is the shared `vertSeg_h₅`. -/
private abbrev seg4_h₅ := vertSeg_h₅

private lemma seg4_seg1_ftc (H : ℝ) {z₀ : ℂ} (hz_re : z₀.re = -1/2) :
    IntervalIntegrable
      (fun t ↦ deriv (seg4_h₀ H z₀) t / seg4_h₀ H z₀ t) volume 0 (1/5) ∧
    ∫ t in (0:ℝ)..(1/5),
        deriv (seg4_h₀ H z₀) t / seg4_h₀ H z₀ t =
      Complex.log (seg4_h₀ H z₀ (1/5)) - Complex.log (seg4_h₀ H z₀ 0) := by
  apply LogDerivFTC.ftc_log_on_segment (by norm_num : (0 : ℝ) ≤ 1/5)
    (vertSeg_h₀_continuous H z₀).continuousOn
    (fun t _ ↦ (hasDerivAt_vertSeg_h₀ H z₀ t).differentiableAt)
    (funext (deriv_vertSeg_h₀ H z₀) ▸ continuousOn_const)
  intro t _
  exact seg4_h₀_slitPlane hz_re t

private lemma seg4_arc_ftc {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) :
    IntervalIntegrable
      (fun t ↦ deriv (seg4_h_arc z₀) t / seg4_h_arc z₀ t) volume (1/5) (3/5) ∧
    ∫ t in (1/5 : ℝ)..(3/5),
        deriv (seg4_h_arc z₀) t / seg4_h_arc z₀ t =
      Complex.log (seg4_h_arc z₀ (3/5)) - Complex.log (seg4_h_arc z₀ (1/5)) := by
  apply LogDerivFTC.ftc_log_on_segment (by norm_num : (1/5 : ℝ) ≤ 3/5)
    (vertSeg_h_arc_continuous z₀).continuousOn
    (fun t _ ↦ (hasDerivAt_vertSeg_h_arc z₀ t).differentiableAt)
    (vertSeg_h_arc_deriv_continuousOn z₀ _)
  intro t ⟨ht1, ht3⟩
  exact seg4_h_arc_slitPlane hz_re hc_lo ht1 ht3

private lemma seg4_left_ftc {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < seg4T₀ H z₀.im - 3/5) :
    IntervalIntegrable
      (fun t ↦ deriv (seg4_h₃ H z₀) t / seg4_h₃ H z₀ t) volume (3/5) (seg4T₀ H z₀.im - δ) ∧
    ∫ t in (3/5 : ℝ)..(seg4T₀ H z₀.im - δ),
        deriv (seg4_h₃ H z₀) t / seg4_h₃ H z₀ t =
      Complex.log (seg4_h₃ H z₀ (seg4T₀ H z₀.im - δ)) -
      Complex.log (seg4_h₃ H z₀ (3/5)) := by
  apply LogDerivFTC.ftc_log_on_segment (by linarith : (3/5 : ℝ) ≤ seg4T₀ H z₀.im - δ)
    (vertSeg_h₃_continuous H z₀).continuousOn
    (fun t _ ↦ (hasDerivAt_vertSeg_h₃ H z₀ t).differentiableAt)
    (funext (deriv_vertSeg_h₃ H z₀) ▸ continuousOn_const)
  intro t ⟨_, htd⟩
  exact seg4_h₃_left_slitPlane hH hz_re hδ_pos htd

private lemma seg4_right_ftc {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 4/5 - seg4T₀ H z₀.im) :
    IntervalIntegrable
      (fun t ↦ deriv (seg4_h₃ H z₀) t / seg4_h₃ H z₀ t) volume (seg4T₀ H z₀.im + δ) (4/5) ∧
    ∫ t in (seg4T₀ H z₀.im + δ)..(4/5 : ℝ),
        deriv (seg4_h₃ H z₀) t / seg4_h₃ H z₀ t =
      Complex.log (seg4_h₃ H z₀ (4/5)) -
      Complex.log (seg4_h₃ H z₀ (seg4T₀ H z₀.im + δ)) := by
  apply LogDerivFTC.ftc_log_on_segment (by linarith : seg4T₀ H z₀.im + δ ≤ 4/5)
    (vertSeg_h₃_continuous H z₀).continuousOn
    (fun t _ ↦ (hasDerivAt_vertSeg_h₃ H z₀ t).differentiableAt)
    (funext (deriv_vertSeg_h₃ H z₀) ▸ continuousOn_const)
  intro t ⟨htd, _⟩
  exact seg4_h₃_right_slitPlane hH hz_re hδ_pos htd

/-- Local alias for the shared seg5 FTC. -/
private alias seg4_seg5_ftc := vertSeg_h₅_ftc

private lemma seg4_junction_15 (H : ℝ) (z₀ : ℂ) :
    seg4_h₀ H z₀ (1/5) = seg4_h_arc z₀ (1/5) := by
  unfold seg4_h₀ vertSeg_h₀ seg4_h_arc vertSeg_h_arc
  have hθ : (fdArcAngle (1/5) : ℝ) = Real.pi / 3 := by unfold fdArcAngle; ring
  rw [hθ, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  apply Complex.ext <;> simp

private lemma seg4_closed (H : ℝ) (z₀ : ℂ) :
    seg4_h₀ H z₀ 0 = seg4_h₅ H z₀ 1 := by
  unfold seg4_h₀ vertSeg_h₀ seg4_h₅ vertSeg_h₅
  apply Complex.ext <;> simp; ring

private lemma seg4_log_diff_eq_neg_pi_I {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2) {δ : ℝ} (hδ_pos : 0 < δ) :
    Complex.log (seg4_h₃ H z₀ (seg4T₀ H z₀.im - δ)) -
    Complex.log (seg4_h₃ H z₀ (seg4T₀ H z₀.im + δ)) = -(↑Real.pi * I) := by
  have hK : 0 < seg1Speed H := seg1Speed_pos hH
  have hKδ : 0 < seg1Speed H * δ := mul_pos hK hδ_pos
  have hK_eq_seg4 : seg1Speed H * (seg4T₀ H z₀.im - 3/5) = z₀.im - Real.sqrt 3 / 2 := by
    unfold seg4T₀; field_simp; ring
  have h_minus : seg4_h₃ H z₀ (seg4T₀ H z₀.im - δ) =
      ((-(seg1Speed H * δ) : ℝ) : ℂ) * I := by
    rw [seg4_h₃_eq_pure_im hz_re]; congr 1
    have : Real.sqrt 3 / 2 + (5 * (seg4T₀ H z₀.im - δ) - 3) * (H - Real.sqrt 3 / 2) - z₀.im =
        -(seg1Speed H * δ) := by
      have : (5 * (seg4T₀ H z₀.im - δ) - 3) * (H - Real.sqrt 3 / 2) =
          seg1Speed H * (seg4T₀ H z₀.im - 3/5) - seg1Speed H * δ := by
        unfold seg1Speed; ring
      linarith [this, hK_eq_seg4]
    exact_mod_cast this
  have h_plus : seg4_h₃ H z₀ (seg4T₀ H z₀.im + δ) =
      ((seg1Speed H * δ : ℝ) : ℂ) * I := by
    rw [seg4_h₃_eq_pure_im hz_re]; congr 1
    have : Real.sqrt 3 / 2 + (5 * (seg4T₀ H z₀.im + δ) - 3) * (H - Real.sqrt 3 / 2) - z₀.im =
        seg1Speed H * δ := by
      have : (5 * (seg4T₀ H z₀.im + δ) - 3) * (H - Real.sqrt 3 / 2) =
          seg1Speed H * (seg4T₀ H z₀.im - 3/5) + seg1Speed H * δ := by
        unfold seg1Speed; ring
      linarith [this, hK_eq_seg4]
    exact_mod_cast this
  rw [h_minus, h_plus,
    show (((-(seg1Speed H * δ) : ℝ) : ℂ) * I) = ((seg1Speed H * δ : ℝ) : ℂ) * (-I) by
      push_cast; ring]
  exact vertSeg_log_diff_neg_I_pi hKδ

private lemma seg4_ae_eq_h₀ (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) (1/5) →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (seg4_h₀ H z₀) t / seg4_h₀ H z₀ t :=
  ae_eq_vertSeg_h₀ H z₀ (by norm_num) le_rfl

/-- Local alias for the shared ae-equality. -/
private alias seg4_ae_eq_h₃ := ae_eq_vertSeg_h₃

/-- The full FTC telescope for the seg4 crossing. -/
theorem fdBoundary_ftc_telescope_seg4 {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) (hc_hi : z₀.im < H)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_lo : δ < seg4T₀ H z₀.im - 3/5)
    (hδ_lt_hi : δ < 4/5 - seg4T₀ H z₀.im) :
    (∫ t in (0 : ℝ)..(seg4T₀ H z₀.im - δ),
        (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
    (∫ t in (seg4T₀ H z₀.im + δ)..(1 : ℝ),
        (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) =
    -(↑Real.pi * I) := by
  set t₀ := seg4T₀ H z₀.im
  have ht₀_lo : 3/5 < t₀ := seg4T₀_gt_three_fifths hH hc_lo
  have ht₀_hi : t₀ < 4/5 := seg4T₀_lt_four_fifths hH hc_hi
  have ⟨hint_seg1, h_int_seg1⟩ := vertSeg_ftc_transfer (seg4_seg1_ftc H hz_re)
    (seg4_ae_eq_h₀ H z₀)
  have ⟨hint_arc, h_int_arc⟩ := vertSeg_ftc_transfer (seg4_arc_ftc hz_re hc_lo)
    (ae_eq_vertSeg_h_arc H z₀)
  have ⟨hint_left, h_int_left⟩ := vertSeg_ftc_transfer
    (seg4_left_ftc hH hz_re hδ_pos hδ_lt_lo)
    (seg4_ae_eq_h₃ H z₀ (by linarith) le_rfl (by linarith))
  have ⟨hint_right, h_int_right⟩ := vertSeg_ftc_transfer
    (seg4_right_ftc hH hz_re hδ_pos hδ_lt_hi)
    (seg4_ae_eq_h₃ H z₀ (by linarith) (by linarith) le_rfl)
  have ⟨hint_seg5, h_int_seg5⟩ := vertSeg_ftc_transfer (seg4_seg5_ftc H hc_hi)
    (ae_eq_vertSeg_h₅ H z₀)
  have h_split_left :
      ∫ t in (0:ℝ)..(t₀ - δ), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      (∫ t in (0:ℝ)..(1/5),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (1/5:ℝ)..(3/5),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (3/5:ℝ)..(t₀ - δ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals hint_seg1 hint_arc
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hint_seg1.trans hint_arc) hint_left
    linear_combination -h1 - h2
  have h_split_right :
      ∫ t in (t₀ + δ)..(1 : ℝ), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      (∫ t in (t₀ + δ)..(4/5 : ℝ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (4/5 : ℝ)..(1 : ℝ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) := by
    have h := intervalIntegral.integral_add_adjacent_intervals hint_right hint_seg5
    linear_combination -h
  rw [h_split_left, h_split_right, h_int_seg1, h_int_arc, h_int_left, h_int_right, h_int_seg5,
      seg4_junction_15 H z₀,
      show seg4_h_arc z₀ (3/5) = seg4_h₃ H z₀ (3/5) from vertSeg_junction_35 H z₀,
      show seg4_h₃ H z₀ (4/5) = seg4_h₅ H z₀ (4/5) from vertSeg_junction_45 H z₀,
      seg4_closed H z₀]
  have h_alg :
      Complex.log (seg4_h_arc z₀ (1/5)) - Complex.log (seg4_h₅ H z₀ 1) +
      (Complex.log (seg4_h₃ H z₀ (3/5)) - Complex.log (seg4_h_arc z₀ (1/5))) +
      (Complex.log (seg4_h₃ H z₀ (t₀ - δ)) - Complex.log (seg4_h₃ H z₀ (3/5))) +
      ((Complex.log (seg4_h₅ H z₀ (4/5)) - Complex.log (seg4_h₃ H z₀ (t₀ + δ))) +
        (Complex.log (seg4_h₅ H z₀ 1) - Complex.log (seg4_h₅ H z₀ (4/5))))
      = Complex.log (seg4_h₃ H z₀ (t₀ - δ)) - Complex.log (seg4_h₃ H z₀ (t₀ + δ)) := by
    ring
  rw [h_alg]
  exact seg4_log_diff_eq_neg_pi_I hH hz_re hδ_pos

/-- Common bounds for `arcFTCHyp_seg4` clauses. -/
private structure ArcFTCHypSeg4Bounds (H : ℝ) (z₀ : ℂ) (ε : ℝ) : Prop where
  lin_pos : 0 < linDelta (seg1Speed H) ε
  lin_lt_lo : linDelta (seg1Speed H) ε < seg4T₀ H z₀.im - 3/5
  lin_lt_hi : linDelta (seg1Speed H) ε < 4/5 - seg4T₀ H z₀.im
  t₀_lo : 3/5 < seg4T₀ H z₀.im
  t₀_hi : seg4T₀ H z₀.im < 4/5

private lemma arcFTCHyp_seg4_bounds {H : ℝ} (hH : Real.sqrt 3 / 2 < H) {z₀ : ℂ}
    (hz_re : z₀.re = -1/2) (hc_lo : Real.sqrt 3 / 2 < z₀.im) (hc_hi : z₀.im < H)
    {ε : ℝ} (hε : 0 < ε) (hε_thr : ε < seg4Threshold H z₀) :
    ArcFTCHypSeg4Bounds H z₀ ε := by
  have hK_pos : 0 < seg1Speed H := seg1Speed_pos hH
  have h_eps_top : ε < H - z₀.im := lt_of_lt_of_le hε_thr (min_le_right _ _)
  have h_eps_arc : ε < ‖z₀‖ - 1 :=
    lt_of_lt_of_le hε_thr (le_trans (min_le_left _ _) (min_le_left _ _))
  have h_eps_width : ε < z₀.im - Real.sqrt 3 / 2 :=
    lt_of_lt_of_le h_eps_arc (norm_sub_one_le_im_sub_sqrt3_seg4 hz_re hc_lo.le)
  refine ⟨linDelta_pos hK_pos hε, ?_, ?_,
    seg4T₀_gt_three_fifths hH hc_lo, seg4T₀_lt_four_fifths hH hc_hi⟩
  · unfold linDelta
    rw [div_lt_iff₀ hK_pos, mul_comm, seg1Speed_mul_t₀_sub_three_fifths hH]; exact h_eps_width
  · unfold linDelta
    rw [div_lt_iff₀ hK_pos, mul_comm, seg1Speed_mul_four_fifths_sub_t₀ hH]; exact h_eps_top

/-- The full `ArcFTCHyp` at any seg4 interior point, with limit `-π · I`. -/
def arcFTCHyp_seg4 {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {z₀ : ℂ} (hz_re : z₀.re = -1/2)
    (hc_lo : Real.sqrt 3 / 2 < z₀.im) (hc_hi : z₀.im < H) :
    ArcFTCHyp γ z₀ (seg4T₀ H z₀.im) (linDelta (seg1Speed H))
      (seg4Threshold H z₀) (-(↑Real.pi * I)) where
  E := fun _ ↦ -(↑Real.pi * I)
  h_ftc := by
    intro ε hε hε_thr
    obtain ⟨h_lin_pos, h_lin_lt_lo, h_lin_lt_hi, h_t₀_lo, h_t₀_hi⟩ :=
      arcFTCHyp_seg4_bounds hH hz_re hc_lo hc_hi hε hε_thr
    have h1 : seg4T₀ H z₀.im - linDelta (seg1Speed H) ε ≤ 1 := by linarith
    have h2 : 0 ≤ seg4T₀ H z₀.im + linDelta (seg1Speed H) ε := by linarith
    rw [transfer_integral z₀ (by linarith) le_rfl h1 hγ,
        transfer_integral z₀ (by linarith) h2 le_rfl hγ]
    exact fdBoundary_ftc_telescope_seg4 hH hz_re hc_lo hc_hi h_lin_pos
      h_lin_lt_lo h_lin_lt_hi
  hint_left := by
    intro ε hε hε_thr
    obtain ⟨h_lin_pos, h_lin_lt_lo, _, h_t₀_lo, h_t₀_hi⟩ :=
      arcFTCHyp_seg4_bounds hH hz_re hc_lo hc_hi hε hε_thr
    have h1 : seg4T₀ H z₀.im - linDelta (seg1Speed H) ε ≤ 1 := by linarith
    apply transfer_integrability z₀ (by linarith) le_rfl h1 hγ
    have hint_seg1 := vertSeg_integrable_transfer (seg4_seg1_ftc H hz_re).1
      (seg4_ae_eq_h₀ H z₀)
    have hint_arc := vertSeg_integrable_transfer (seg4_arc_ftc hz_re hc_lo).1
      (ae_eq_vertSeg_h_arc H z₀)
    have hint_left := vertSeg_integrable_transfer
      (seg4_left_ftc hH hz_re h_lin_pos h_lin_lt_lo).1
      (seg4_ae_eq_h₃ H z₀ (by linarith) le_rfl (by linarith))
    exact (hint_seg1.trans hint_arc).trans hint_left
  hint_right := by
    intro ε hε hε_thr
    obtain ⟨h_lin_pos, _, h_lin_lt_hi, h_t₀_lo, h_t₀_hi⟩ :=
      arcFTCHyp_seg4_bounds hH hz_re hc_lo hc_hi hε hε_thr
    have h2 : 0 ≤ seg4T₀ H z₀.im + linDelta (seg1Speed H) ε := by linarith
    apply transfer_integrability z₀ (by linarith) h2 le_rfl hγ
    have hint_right := vertSeg_integrable_transfer
      (seg4_right_ftc hH hz_re h_lin_pos h_lin_lt_hi).1
      (seg4_ae_eq_h₃ H z₀ (by linarith) (by linarith) le_rfl)
    have hint_seg5 := vertSeg_integrable_transfer (seg4_seg5_ftc H hc_hi).1
      (ae_eq_vertSeg_h₅ H z₀)
    exact hint_right.trans hint_seg5
  h_limit := tendsto_const_nhds

end
