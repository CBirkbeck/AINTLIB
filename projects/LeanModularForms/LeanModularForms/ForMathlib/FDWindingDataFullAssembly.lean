/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.BoundaryWindingSeg1Proof
import LeanModularForms.ForMathlib.BoundaryWindingSeg4Proof
import LeanModularForms.ForMathlib.BoundaryWindingArcProof

/-!
# Assembly: `FDWindingDataFull` from per-segment FTC providers

Given:
1. A base `FDWindingData H` (interior + three elliptic corner winding numbers)
2. Per-segment `ArcFTCHyp` providers for seg1, seg4, and the arc

this file assembles `FDWindingDataFull H` unconditionally.

## Main results

* `mkFDWindingDataFull_of_ftcProviders` -- the main assembler
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- For `z` on the unit circle in the upper half-plane with `|z.re| < 1/2`,
the argument `arg z` lies in `(π/3, 2π/3)`. -/
theorem arg_mem_arc_range {z : ℂ} (hz_norm : ‖z‖ = 1) (hz_im : 0 < z.im)
    (hz_re : |z.re| < 1/2) :
    Real.pi / 3 < z.arg ∧ z.arg < 2 * Real.pi / 3 := by
  have hz_ne : z ≠ 0 := fun h => by simp [h] at hz_im
  have h_cos : Real.cos z.arg = z.re := by rw [Complex.cos_arg hz_ne, hz_norm, div_one]
  have h_sin : Real.sin z.arg = z.im := by rw [Complex.sin_arg, hz_norm, div_one]
  have h_arg_pos : 0 < z.arg := (Complex.arg_nonneg_iff.mpr hz_im.le).lt_of_ne fun h => by
    rw [← h, Real.sin_zero] at h_sin; linarith
  have h_arg_lt_pi : z.arg < Real.pi := (Complex.arg_le_pi z).lt_of_ne fun h => by
    rw [h, Real.sin_pi] at h_sin; linarith
  have h_cos_2pi3 : Real.cos (2 * Real.pi / 3) = -(1/2) := by
    rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  have hpi := Real.pi_pos
  refine ⟨?_, ?_⟩
  · by_contra! h_not
    have := Real.cos_le_cos_of_nonneg_of_le_pi h_arg_pos.le (by linarith) h_not
    rw [Real.cos_pi_div_three, h_cos] at this
    exact absurd (abs_lt.mp hz_re).2 (not_lt.mpr this)
  · by_contra! h_not
    have := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) h_arg_lt_pi.le h_not
    rw [h_cos_2pi3, h_cos] at this
    exact absurd (abs_lt.mp hz_re).1 (not_lt.mpr this)

/-- For `z` on the unit circle, `z = exp(i * arg z)`. -/
theorem eq_exp_arg_mul_I {z : ℂ} (hz_norm : ‖z‖ = 1) :
    z = exp (↑z.arg * I) := by
  simpa [hz_norm] using (Complex.norm_mul_exp_arg_mul_I z).symm

/-- Given `FDWindingData H` and FTC providers for seg1, seg4, and the arc,
construct `FDWindingDataFull H` unconditionally. -/
def mkFDWindingDataFull_of_ftcProviders {H : ℝ} (hH : 1 < H)
    (D : FDWindingData H)
    (ftc_seg1 : ∀ z₀ : ℂ, z₀.re = 1/2 →
      Real.sqrt 3 / 2 < z₀.im → z₀.im < H →
      ArcFTCHyp D.boundary z₀ (seg1T₀ H z₀.im) (linDelta (seg1Speed H))
        (seg1Threshold H z₀) (-(↑Real.pi * I)))
    (ftc_seg4 : ∀ z₀ : ℂ, z₀.re = -1/2 →
      Real.sqrt 3 / 2 < z₀.im → z₀.im < H →
      ArcFTCHyp D.boundary z₀ (seg4T₀ H z₀.im) (linDelta (seg1Speed H))
        (seg4Threshold H z₀) (-(↑Real.pi * I)))
    (ftc_arc : ∀ θ₀ : ℝ, Real.pi / 3 < θ₀ → θ₀ < 2 * Real.pi / 3 →
      ArcFTCHyp D.boundary (exp (↑θ₀ * I)) (arcT₀ θ₀) arcsinDelta
        (arcThreshold H θ₀) (-(↑Real.pi * I))) :
    FDWindingDataFull H := by
  have hH_sqrt3 : Real.sqrt 3 / 2 < H := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ), hH]
  refine mkFDWindingDataFull D ?_
  intro z hz_im_pos hz_im_lt hz_ne_I hz_ne_rho hz_ne_rho1 hz_not_int hz_nsq hz_re
  rcases smooth_boundary_classification z hz_im_pos hz_ne_I hz_ne_rho hz_ne_rho1 hz_not_int
      hz_nsq hz_re with ⟨h_re_half, h_norm_gt⟩ | ⟨h_norm, _, h_re_half_ne⟩
  · have h_im_gt : Real.sqrt 3 / 2 < z.im := by
      have h_re_sq : z.re ^ 2 = 1/4 := by
        rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1/2) |>.mp h_re_half with h | h <;> nlinarith
      have hn := Complex.normSq_apply z
      nlinarith [h_norm_gt, sq_nonneg (‖z‖ - 1), Complex.normSq_eq_norm_sq (z := z),
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ), hz_im_pos,
        sq_nonneg (z.im - Real.sqrt 3 / 2)]
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1/2) |>.mp h_re_half with h_pos | h_neg
    · exact (smoothBoundaryData_seg1_of_ftcHyp hH_sqrt3 D.boundary D.boundary_eq
        h_pos h_im_gt hz_im_lt (ftc_seg1 z h_pos h_im_gt hz_im_lt)).hasWindingNumber
    · have h_neg' : z.re = -1/2 := by linarith
      exact (smoothBoundaryData_seg4_of_ftcHyp hH_sqrt3 D.boundary D.boundary_eq
        h_neg' h_im_gt hz_im_lt (ftc_seg4 z h_neg' h_im_gt hz_im_lt)).hasWindingNumber
  · obtain ⟨h_arg_lo, h_arg_hi⟩ :=
      arg_mem_arc_range h_norm hz_im_pos (hz_re.lt_of_ne h_re_half_ne)
    rw [eq_exp_arg_mul_I h_norm]
    exact (smoothBoundaryData_arc_of_ftcHyp hH D.boundary D.boundary_eq
      h_arg_lo h_arg_hi (ftc_arc z.arg h_arg_lo h_arg_hi)).hasWindingNumber

end
