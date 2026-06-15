/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ValenceFormula.WindingWeights.Common
import LeanModularForms.ForMathlib.ContourIntegral.CrossingLimit

/-!
# Winding Number Weight at i

PV integral computation and generalized winding number of `fdBoundary_H`
around the point i.

## Main Results

* `pv_integral_at_i_tendsto` — PV integral converges to -iπ
* `gWN_fdBoundary_H_at_i` — gWN = -1/2 at i
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

private lemma trig_setup_i {δ : ℝ} (hδ : 0 < δ) (hδ_small : δ < 1) :
    Real.sin (δ * Real.pi / 6) =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (δ * Real.pi / 12) ∧
    Real.cos (δ * Real.pi / 6) - 1 =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.sin (δ * Real.pi / 12)) ∧
    0 < Real.sin (δ * Real.pi / 12) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) by ring, Real.sin_two_mul]
  · rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (δ * Real.pi / 12)]
  · exact ArcCalculus.sin_pos_of_mem_Ioo_zero_pi
      (by constructor <;> nlinarith [Real.pi_pos])

/-- Factor the displacement `↑(cos θ) + ↑(sin θ)·I - I` as `↑r·(↑(cos φ) + ↑(sin φ)·I)`
from the real/imaginary identities. Shared scaffold for the arc arg/norm lemmas at `i`. -/
private lemma eq_factor_i {cθ sθ r cφ sφ : ℝ} (hre : cθ = r * cφ) (him : sθ - 1 = r * sφ) :
    (↑cθ + ↑sθ * I - I : ℂ) = ↑r * (↑cφ + ↑sφ * I) := by
  apply Complex.ext <;> simp <;> linarith

private lemma arg_approach_i_left (hδ : 0 < δ) (hδ_small : δ < 1) :
    (fdBoundary_H H (2 - δ) - I).arg = -(δ * Real.pi / 12) := by
  have h1 : 1 < 2 - δ := by linarith
  have h3 : 2 - δ < 3 := by linarith
  rw [fdBoundary_H_eq_arc h1 h3]
  set θ := Real.pi / 2 - δ * Real.pi / 6 with hθ_def
  rw [show Real.pi * (1 + (2 - δ)) / 6 = θ by simp only [hθ_def]; ring]
  rw [show (↑θ : ℂ) * I = ↑θ * I from rfl, Complex.exp_ofReal_mul_I]
  have h_cos : Real.cos θ = Real.sin (δ * Real.pi / 6) := by
    rw [hθ_def, Real.cos_pi_div_two_sub]
  have h_sin : Real.sin θ = Real.cos (δ * Real.pi / 6) := by
    rw [hθ_def, Real.sin_pi_div_two_sub]
  obtain ⟨h_re_factor, h_im_factor, h_sin_pos⟩ := trig_setup_i hδ hδ_small
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - I =
      ↑(2 * Real.sin (δ * Real.pi / 12)) *
        (↑(Real.cos (δ * Real.pi / 12)) + ↑(-(Real.sin (δ * Real.pi / 12))) * I) := by
    rw [h_cos, h_sin]
    exact eq_factor_i (by linarith [h_re_factor]) (by linarith [h_im_factor])
  rw [h_eq]
  have h_trig : (↑(Real.cos (δ * Real.pi / 12)) : ℂ) +
      ↑(-(Real.sin (δ * Real.pi / 12))) * I =
      Complex.cos ↑(-(δ * Real.pi / 12)) + Complex.sin ↑(-(δ * Real.pi / 12)) * I := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, ofReal_neg]
  rw [h_trig]
  exact Complex.arg_mul_cos_add_sin_mul_I (mul_pos (by norm_num : (0:ℝ) < 2) h_sin_pos)
    ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩

private lemma arg_approach_i_right (hδ : 0 < δ) (hδ_small : δ < 1) :
    (fdBoundary_H H (2 + δ) - I).arg = δ * Real.pi / 12 - Real.pi := by
  have h1 : 1 < 2 + δ := by linarith
  have h3 : 2 + δ < 3 := by linarith
  rw [fdBoundary_H_eq_arc h1 h3]
  set θ := Real.pi / 2 + δ * Real.pi / 6 with hθ_def
  rw [show Real.pi * (1 + (2 + δ)) / 6 = θ by simp only [hθ_def]; ring]
  rw [show (↑θ : ℂ) * I = ↑θ * I from rfl, Complex.exp_ofReal_mul_I]
  have h_cos : Real.cos θ = -Real.sin (δ * Real.pi / 6) := by
    rw [hθ_def, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_sin : Real.sin θ = Real.cos (δ * Real.pi / 6) := by
    rw [hθ_def, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  obtain ⟨h_re_factor, h_im_factor, h_sin_pos⟩ := trig_setup_i hδ hδ_small
  set w := (↑(Real.cos (δ * Real.pi / 12)) : ℂ) +
    ↑(Real.sin (δ * Real.pi / 12)) * I with hw_def
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - I =
      -(↑(2 * Real.sin (δ * Real.pi / 12)) * w) := by
    rw [h_cos, h_sin]
    apply Complex.ext
    · simp only [hw_def, add_re, sub_re, neg_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one]; linarith [h_re_factor]
    · simp only [hw_def, add_im, sub_im, neg_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, add_zero, mul_one, zero_add]; linarith [h_im_factor]
  rw [h_eq]
  have hw_im_pos : 0 < w.im := by
    simp only [hw_def, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      mul_zero, add_zero, mul_one]
    linarith
  have hw_arg : w.arg = δ * Real.pi / 12 := by
    have hw_eq : w = ↑(1:ℝ) * (Complex.cos ↑(δ * Real.pi / 12) +
        Complex.sin ↑(δ * Real.pi / 12) * I) := by
      simp only [hw_def, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Complex.ofReal_one, one_mul]
    rw [hw_eq]
    exact Complex.arg_mul_cos_add_sin_mul_I (by norm_num : (0:ℝ) < 1)
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hrw_im_pos : 0 < (↑(2 * Real.sin (δ * Real.pi / 12)) * w).im := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    simp only [zero_mul, add_zero]
    exact mul_pos (mul_pos (by norm_num) h_sin_pos) hw_im_pos
  rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos hrw_im_pos,
      Complex.arg_real_mul w (mul_pos (by norm_num : (0:ℝ) < 2) h_sin_pos),
      hw_arg]

private lemma g_i_norm_left {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ‖fdBoundary_H H (2 - δ) - I‖ = 2 * Real.sin (δ * Real.pi / 12) := by
  have h1 : 1 < 2 - δ := by linarith
  have h3 : 2 - δ < 3 := by linarith
  rw [fdBoundary_H_eq_arc h1 h3, Complex.exp_ofReal_mul_I]
  set θ := Real.pi / 2 - δ * Real.pi / 6 with hθ_def
  rw [show Real.pi * (1 + (2 - δ)) / 6 = θ by simp only [hθ_def]; ring]
  have h_cos : Real.cos θ = Real.sin (δ * Real.pi / 6) := by
    rw [hθ_def, Real.cos_pi_div_two_sub]
  have h_sin : Real.sin θ = Real.cos (δ * Real.pi / 6) := by
    rw [hθ_def, Real.sin_pi_div_two_sub]
  obtain ⟨h_re_factor, h_im_factor, h_sin_pos⟩ := trig_setup_i hδ hδ1
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - I =
      (2 * Real.sin (δ * Real.pi / 12)) • Complex.exp (↑(-(δ * Real.pi / 12)) * I) := by
    rw [Complex.real_smul, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, h_cos, h_sin]
    exact eq_factor_i (by linarith [h_re_factor]) (by linarith [h_im_factor])
  rw [h_eq, norm_smul, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_of_nonneg (by linarith)]

private lemma g_i_norm_right {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ‖fdBoundary_H H (2 + δ) - I‖ = 2 * Real.sin (δ * Real.pi / 12) := by
  have h1 : 1 < 2 + δ := by linarith
  have h3 : 2 + δ < 3 := by linarith
  rw [fdBoundary_H_eq_arc h1 h3, Complex.exp_ofReal_mul_I]
  set θ := Real.pi / 2 + δ * Real.pi / 6 with hθ_def
  rw [show Real.pi * (1 + (2 + δ)) / 6 = θ by simp only [hθ_def]; ring]
  have h_cos : Real.cos θ = -Real.sin (δ * Real.pi / 6) := by
    rw [hθ_def, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_sin : Real.sin θ = Real.cos (δ * Real.pi / 6) := by
    rw [hθ_def, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  obtain ⟨h_re_factor, h_im_factor, h_sin_pos⟩ := trig_setup_i hδ hδ1
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - I =
      (-(2 * Real.sin (δ * Real.pi / 12))) • Complex.exp (↑(δ * Real.pi / 12) * I) := by
    rw [Complex.real_smul, Complex.exp_ofReal_mul_I, h_cos, h_sin]
    exact eq_factor_i (by linarith [h_re_factor]) (by linarith [h_im_factor])
  rw [h_eq, norm_smul, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by linarith)]

private lemma g_i_norm_ge_seg0 {t : ℝ} (ht1 : t ≤ 1) :
    1 / 2 ≤ ‖fdBoundary_H H t - I‖ := by
  have hre : (fdBoundary_H H t - I).re = 1 / 2 := by
    rw [fdBoundary_H_seg1 H ht1]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.div_ofNat_re,
      mul_zero, sub_zero, zero_mul, mul_one]
    norm_num
  calc (1 : ℝ) / 2 = |(fdBoundary_H H t - I).re| := by rw [hre]; norm_num
    _ ≤ ‖fdBoundary_H H t - I‖ := Complex.abs_re_le_norm _

private lemma g_i_norm_ge_seg4 (H : ℝ) (hH : 1 < H) {t : ℝ} (ht4 : 4 ≤ t) :
    H - 1 ≤ ‖fdBoundary_H H t - I‖ := by
  have him : (fdBoundary_H H t - I).im = H - 1 := by
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · rw [fdBoundary_H_at_four H]
      simp only [Complex.neg_im, Complex.div_ofNat_im, Complex.one_im, Complex.add_im,
        Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_im,
        Complex.ofReal_re]
      ring
    · rw [fdBoundary_H_seg5 H (by linarith) (by linarith) (by linarith) (by linarith)]
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.div_ofNat_im, Complex.im_ofNat]
      ring
  calc H - 1 = |(fdBoundary_H H t - I).im| := by rw [him, abs_of_pos (by linarith)]
    _ ≤ ‖fdBoundary_H H t - I‖ := Complex.abs_im_le_norm _

private lemma g_i_slitPlane_left {t : ℝ} (ht2 : t < 2) :
    fdBoundary_H H t - I ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  rcases le_or_gt t 1 with ht1 | ht1
  · rw [fdBoundary_H_seg1 H ht1]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.div_ofNat_re,
      mul_zero, sub_zero, zero_mul, mul_one]
    norm_num
  · rw [fdBoundary_H_seg2 H (by linarith) (by linarith)]
    set θ := Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3) with hθ_def
    rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      (↑θ : ℂ) * I by simp only [hθ_def]; push_cast; ring, Complex.exp_ofReal_mul_I]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero,
      mul_one]
    refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;>
      simp only [hθ_def] <;> nlinarith [Real.pi_pos]

private lemma g_i_seg3_value {t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) :
    fdBoundary_H H t - I =
      -1/2 + ↑(Real.sqrt 3 / 2 - 1 + (t - 3) * (H - Real.sqrt 3 / 2)) * I := by
  rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) ht4]
  push_cast; ring

private lemma g_i_seg4_value {t : ℝ} (ht4 : 4 < t) :
    fdBoundary_H H t - I = ↑(t - 9/2) + ↑(H - 1) * I := by
  rw [fdBoundary_H_seg5 H (by linarith) (by linarith) (by linarith) (by linarith)]
  push_cast; ring

private lemma g_i_norm_ge_seg3 {t : ℝ} (ht3 : 3 ≤ t) (ht4 : t ≤ 4) :
    1 / 2 ≤ ‖fdBoundary_H H t - I‖ := by
  have hre : (fdBoundary_H H t - I).re = -1 / 2 := by
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · rw [fdBoundary_H_at_three_eq_rho]
      simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
        Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.div_ofNat_re,
        Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero]
      norm_num
    · rw [g_i_seg3_value ht3' ht4]
      simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.one_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, add_zero, zero_mul]
  calc 1 / 2 = |(fdBoundary_H H t - I).re| := by rw [hre]; norm_num
    _ ≤ ‖fdBoundary_H H t - I‖ := Complex.abs_re_le_norm _

private lemma g_i_slitPlane_arc_right {t : ℝ} (ht2 : 2 < t) (ht3 : t ≤ 3) :
    fdBoundary_H H t - I ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  rcases eq_or_lt_of_le ht3 with rfl | ht3'
  · rw [fdBoundary_H_at_three_eq_rho]
    simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
      Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.div_ofNat_im, Complex.div_ofNat_re,
      Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, zero_div]
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num), sq_nonneg (2 - Real.sqrt 3)]
  · rw [fdBoundary_H_eq_arc (by linarith) ht3', Complex.exp_ofReal_mul_I]
    simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, zero_add]
    have hθ_bound : Real.pi / 2 < Real.pi * (1 + t) / 6 := by nlinarith [Real.pi_pos]
    have hθ_bound2 : Real.pi * (1 + t) / 6 < Real.pi + Real.pi / 2 := by nlinarith [Real.pi_pos]
    have h_cos_neg := Real.cos_neg_of_pi_div_two_lt_of_lt hθ_bound hθ_bound2
    have h_sin_lt : Real.sin (Real.pi * (1 + t) / 6) < 1 := by
      by_contra h_ge; push Not at h_ge
      have h_eq := le_antisymm (Real.sin_le_one _) h_ge
      have : Real.cos (Real.pi * (1 + t) / 6) = 0 := by
        nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (1 + t) / 6)]
      linarith
    linarith

private lemma g_i_norm_arc_right {t : ℝ} (ht2 : 2 < t) (ht3 : t < 3) :
    ‖fdBoundary_H H t - I‖ = 2 * Real.sin ((t - 2) * Real.pi / 12) := by
  have h := g_i_norm_right (H := H) (δ := t - 2) (by linarith) (by linarith)
  rwa [show 2 + (t - 2) = t by ring] at h

private lemma g_i_norm_arc_left {t : ℝ} (ht1 : 1 < t) (ht2 : t < 2) :
    ‖fdBoundary_H H t - I‖ = 2 * Real.sin ((2 - t) * Real.pi / 12) := by
  have h := g_i_norm_left (H := H) (δ := 2 - t) (by linarith) (by linarith)
  rwa [show 2 - (2 - t) = t by ring] at h

private noncomputable def t₀_i (H : ℝ) : ℝ :=
  3 + (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2)

private lemma t₀_i_gt_three (hH : 1 < H) : 3 < t₀_i H := by
  have h_num_pos : 0 < 1 - Real.sqrt 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num), sq_nonneg (2 - Real.sqrt 3)]
  have h_den_pos : 0 < H - Real.sqrt 3 / 2 := by nlinarith
  unfold t₀_i; linarith [div_pos h_num_pos h_den_pos]

private lemma t₀_i_lt_four (hH : 1 < H) : t₀_i H < 4 := by
  have h_den_pos : 0 < H - Real.sqrt 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num), sq_nonneg (2 - Real.sqrt 3)]
  have : (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) < 1 := by
    rw [div_lt_one h_den_pos]; linarith
  unfold t₀_i; linarith

private lemma g_i_t₀_im_eq_zero (hH : 1 < H) :
    Real.sqrt 3 / 2 - 1 + (t₀_i H - 3) * (H - Real.sqrt 3 / 2) = 0 := by
  have h_den_pos : 0 < H - Real.sqrt 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num), sq_nonneg (2 - Real.sqrt 3)]
  unfold t₀_i
  rw [show 3 + (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) - 3 =
    (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) by ring]
  rw [div_mul_cancel₀ _ (ne_of_gt h_den_pos)]; ring

private lemma g_i_at_t₀ (hH : 1 < H) :
    fdBoundary_H H (t₀_i H) - I = -1/2 := by
  rw [g_i_seg3_value (t₀_i_gt_three hH) (t₀_i_lt_four hH).le]
  rw [g_i_t₀_im_eq_zero hH]; simp only [ofReal_zero, zero_mul, add_zero]

private lemma g_i_seg3_im_neg {t : ℝ} (ht3 : 3 < t) (ht_t0 : t < t₀_i H)
    (hH : 1 < H) : (fdBoundary_H H t - I).im < 0 := by
  rw [g_i_seg3_value ht3 (by linarith [t₀_i_lt_four hH])]
  simp only [Complex.add_im, Complex.neg_im, Complex.div_ofNat_im, Complex.one_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, add_zero, mul_one]
  norm_num
  nlinarith [g_i_t₀_im_eq_zero (H := H) hH,
    Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num), sq_nonneg (2 - Real.sqrt 3)]

private lemma g_i_seg3_im_pos {t : ℝ} (ht_t0 : t₀_i H < t) (ht4 : t ≤ 4)
    (hH : 1 < H) : 0 < (fdBoundary_H H t - I).im := by
  rw [g_i_seg3_value (by linarith [t₀_i_gt_three hH]) ht4]
  simp only [Complex.add_im, Complex.neg_im, Complex.div_ofNat_im, Complex.one_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, add_zero, mul_one]
  norm_num
  nlinarith [g_i_t₀_im_eq_zero (H := H) hH,
    Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num), sq_nonneg (2 - Real.sqrt 3)]

private lemma g_i_ne_zero_seg3 {t : ℝ} (ht3 : 3 ≤ t) (ht4 : t ≤ 4) :
    fdBoundary_H H t - I ≠ 0 := by
  intro h
  have := congr_arg Complex.re h
  simp only [Complex.zero_re] at this
  rcases eq_or_lt_of_le ht3 with rfl | ht3'
  · rw [fdBoundary_H_at_three_eq_rho] at this
    simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
      Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.div_ofNat_re,
      Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero] at this
    norm_num at this
  · rw [g_i_seg3_value ht3' ht4] at this
    simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, add_zero, zero_mul] at this
    norm_num at this

private lemma log_neg_eq_add_pi_I {z : ℂ} (hz_im : z.im < 0) :
    Complex.log (-z) = Complex.log z + ↑Real.pi * I := by
  change ↑(Real.log ‖-z‖) + ↑((-z).arg) * I =
    ↑(Real.log ‖z‖) + ↑z.arg * I + ↑Real.pi * I
  rw [norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg hz_im]
  push_cast; ring

/-- **Imaginary part of `fdBoundary_H H 3 - I` is negative**.
At the corner `t = 3`, the path takes the value `ρ`, so `g 3 = ρ - i` has
imaginary part `sqrt 3 / 2 - 1 < 0`. -/
private lemma g_i_at_three_im_neg (H : ℝ) : (fdBoundary_H H 3 - I).im < 0 := by
  rw [fdBoundary_H_at_three_eq_rho]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
    Complex.sub_im, Complex.add_im, Complex.neg_im, Complex.div_ofNat_im,
    Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one,
    Complex.div_ofNat_re]
  nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
    sq_nonneg (2 - Real.sqrt 3)]

/-- **Triple property of `g = fdBoundary_H H t - I` on `[3, t₀]`** for the
seg3 piece: imaginary part `≤ 0`, function nonzero, and interior strict
imaginary negative. Used by `ftc_log_piece_lower`. -/
private lemma g_i_seg3_left_triple (H : ℝ) (hH : 1 < H) :
    (∀ t ∈ Icc (3:ℝ) (t₀_i H), (fdBoundary_H H t - I).im ≤ 0) ∧
    (∀ t ∈ Icc (3:ℝ) (t₀_i H), fdBoundary_H H t - I ≠ 0) ∧
    (∀ t ∈ Ioo (3:ℝ) (t₀_i H), (fdBoundary_H H t - I).im < 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ⟨ht3, ht_t0⟩
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · exact (g_i_at_three_im_neg H).le
    rcases eq_or_lt_of_le ht_t0 with rfl | ht_t0'
    · rw [g_i_at_t₀ hH]; norm_num
    · exact (g_i_seg3_im_neg ht3' ht_t0' hH).le
  · intro t ⟨ht3, ht_t0⟩
    exact g_i_ne_zero_seg3 ht3 (by linarith [t₀_i_lt_four hH])
  · intro t ⟨ht3, ht_t0⟩
    exact g_i_seg3_im_neg ht3 ht_t0 hH

/-- **Triple property of `g = fdBoundary_H H t - I` on `[t₀, 4]`** for the
seg3 piece: imaginary part `≥ 0`, function nonzero, and interior in
`slitPlane`. Used by `ftc_log_piece_upper`. -/
private lemma g_i_seg3_right_triple (H : ℝ) (hH : 1 < H) :
    (∀ t ∈ Icc (t₀_i H) (4:ℝ), 0 ≤ (fdBoundary_H H t - I).im) ∧
    (∀ t ∈ Icc (t₀_i H) (4:ℝ), fdBoundary_H H t - I ≠ 0) ∧
    (∀ t ∈ Ioo (t₀_i H) (4:ℝ), fdBoundary_H H t - I ∈ slitPlane) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ⟨ht_t0, ht4⟩
    rcases eq_or_lt_of_le ht_t0 with rfl | ht_t0'
    · rw [g_i_at_t₀ hH]; norm_num
    · exact (g_i_seg3_im_pos ht_t0' ht4 hH).le
  · intro t ⟨ht_t0, ht4⟩
    exact g_i_ne_zero_seg3 (by linarith [t₀_i_gt_three hH]) ht4
  · intro t ⟨ht_t0, ht4⟩
    rw [Complex.mem_slitPlane_iff]
    exact .inr (ne_of_gt (g_i_seg3_im_pos ht_t0 ht4.le hH))

/-- **Branch jump for `Complex.log` at `-1/2`**: `log(-(-1/2)) = log(-1/2) - πI`. -/
private lemma log_neg_neg_half_eq_log_neg_half_sub_pi_I :
    Complex.log (-((-1 : ℂ) / 2)) = Complex.log ((-1 : ℂ) / 2) - ↑Real.pi * I := by
  have key : Complex.log (-((-1 : ℂ) / 2)) - Complex.log ((-1 : ℂ) / 2) =
      -(↑Real.pi * I) := by
    rw [show -((-1 : ℂ) / 2) = (1 / 2 : ℂ) by ring,
        show ((-1 : ℂ) / 2) = ↑((1 : ℝ) / 2) * (-1 : ℂ) by push_cast; ring,
        Complex.log_ofReal_mul (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (-1 : ℂ) ≠ 0),
        Complex.log_neg_one,
        show (1 : ℂ) / 2 = ↑((1 : ℝ) / 2) by push_cast; ring,
        ← Complex.ofReal_log (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
    ring
  linear_combination key

private lemma ftc_logDeriv_telescope_i (H : ℝ) (hH : 1 < H) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let g := fun t => fdBoundary_H H t - I
    IntervalIntegrable (fun t => deriv g t / g t) volume 0 (2 - δ) ∧
    IntervalIntegrable (fun t => deriv g t / g t) volume (2 + δ) 5 ∧
    ((∫ t in (0:ℝ)..(2 - δ), deriv g t / g t) + (∫ t in (2 + δ)..(5:ℝ), deriv g t / g t) =
    Complex.log (g (2 - δ)) - Complex.log (g (2 + δ)) - 2 * ↑Real.pi * I) := by
  intro g
  set t₀ := t₀_i H
  have ht₀3 := t₀_i_gt_three hH
  have ht₀4 := t₀_i_lt_four hH
  set h₀ : ℝ → ℂ := fun t => 1/2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2) - 1) * I
  set h₁ : ℝ → ℂ := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - I
  set h₂ : ℝ → ℂ :=
    fun t => -1/2 + ↑(Real.sqrt 3 / 2 - 1 + (t - 3) * (H - Real.sqrt 3 / 2)) * I
  set h₃ : ℝ → ℂ := fun t => ↑(t - 9/2) + ↑(H - 1) * I
  have hg_eq_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := by
    intro t ht
    change fdBoundary_H H t - I = h₀ t
    rw [fdBoundary_H_seg1 H ht]
    simp only [h₀]
    ring
  have hg_eq_h₁ : ∀ t, 1 < t → t < 3 → g t = h₁ t := by
    intro t ht1 ht3
    change fdBoundary_H H t - I = h₁ t
    rw [fdBoundary_H_eq_arc ht1 ht3]
  have hg_eq_h₂ : ∀ t, 3 < t → t ≤ 4 → g t = h₂ t :=
    fun t ht3 ht4 => g_i_seg3_value ht3 ht4
  have hg_eq_h₃ : ∀ t, 4 < t → g t = h₃ t :=
    fun t ht4 => g_i_seg4_value ht4
  have hg0 : g 0 = h₀ 0 := hg_eq_h₀ 0 (by norm_num)
  have hg1_0 : g 1 = h₀ 1 := hg_eq_h₀ 1 le_rfl
  have hg1_1 : g 1 = h₁ 1 := by
    change fdBoundary_H H 1 - I = h₁ 1
    rw [fdBoundary_H_at_one_eq_rho_plus_one]
    simp only [h₁, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
      UpperHalfPlane.coe_mk]
    rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 by ring,
        show (↑(Real.pi / 3) : ℂ) * I = ↑(Real.pi / 3) * I from rfl,
        Complex.exp_ofReal_mul_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  have hg2mδ : g (2 - δ) = h₁ (2 - δ) := hg_eq_h₁ (2 - δ) (by linarith) (by linarith)
  have hg2pδ : g (2 + δ) = h₁ (2 + δ) := hg_eq_h₁ (2 + δ) (by linarith) (by linarith)
  have hg3_1 : g 3 = h₁ 3 := by
    change fdBoundary_H H 3 - I = h₁ 3
    rw [fdBoundary_H_at_three_eq_rho]
    simp only [h₁, ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    rw [show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 by ring]
    rw [show (↑(2 * Real.pi / 3) : ℂ) * I = ↑(2 * Real.pi / 3) * I from rfl,
        Complex.exp_ofReal_mul_I, cos_two_pi_div_three, sin_two_pi_div_three]
    push_cast; ring
  have hg3_2 : g 3 = h₂ 3 := by
    change fdBoundary_H H 3 - I = h₂ 3
    rw [fdBoundary_H_at_three_eq_rho]
    simp only [h₂, ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    push_cast; ring
  have hgt₀_2 : g t₀ = h₂ t₀ := hg_eq_h₂ t₀ ht₀3 ht₀4.le
  have hgt₀_val : g t₀ = (-1 : ℂ) / 2 := g_i_at_t₀ hH
  have hg4_2 : g 4 = h₂ 4 := hg_eq_h₂ 4 (by linarith) le_rfl
  have hg4_3 : g 4 = h₃ 4 := by
    change fdBoundary_H H 4 - I = h₃ 4
    rw [fdBoundary_H_at_four H]
    simp only [h₃]
    push_cast
    ring
  have hg5 : g 5 = h₃ 5 := hg_eq_h₃ 5 (by norm_num)
  have hd_h₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
    intro t; simp only [h₀]
    have ht := (hasDerivAt_id t).ofReal_comp.mul_const (↑H - ↑(Real.sqrt 3) / 2 : ℂ)
    have hinner := ((hasDerivAt_const t (↑H : ℂ)).sub ht).sub (hasDerivAt_const t (1:ℂ))
    exact ((hasDerivAt_const t ((1:ℂ)/2)).add (hinner.mul_const I)).congr_deriv
      (by push_cast; ring)
  have hd_h₁ : ∀ t : ℝ, HasDerivAt h₁
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t :=
    fun t => hasDerivAt_arc_sub_const I t
  have hd_h₂ : ∀ t : ℝ, HasDerivAt h₂ ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t :=
    hasDerivAt_aff_imI_pos_shift (-1/2 : ℂ) (H - Real.sqrt 3 / 2)
      (Real.sqrt 3 / 2 - 1) 3
  have hd_h₃ : ∀ t : ℝ, HasDerivAt h₃ 1 t :=
    hasDerivAt_seg5_line (9/2) (↑(H - 1) * I)
  have heq_01 : ∀ t ∈ Ioo (0:ℝ) 1, g t = h₀ t ∧ deriv g t = deriv h₀ t :=
    heq_deriv_of_eq_on_nhds (U := Iio (1:ℝ)) (fun _ ht => Iio_mem_nhds ht.2)
      (fun s hs => hg_eq_h₀ s hs.le)
  have heq_1_2mδ : ∀ t ∈ Ioo (1:ℝ) (2 - δ), g t = h₁ t ∧ deriv g t = deriv h₁ t :=
    heq_deriv_of_eq_on_nhds (U := Ioo (1:ℝ) 3)
      (fun _ ht => Ioo_mem_nhds ht.1 (by linarith [ht.2]))
      (fun s hs => hg_eq_h₁ s hs.1 hs.2)
  have heq_2pδ_3 : ∀ t ∈ Ioo (2 + δ) (3:ℝ), g t = h₁ t ∧ deriv g t = deriv h₁ t :=
    heq_deriv_of_eq_on_nhds (U := Ioo (1:ℝ) 3)
      (fun _ ht => Ioo_mem_nhds (by linarith [ht.1]) ht.2)
      (fun s hs => hg_eq_h₁ s hs.1 hs.2)
  have heq_3_t₀ : ∀ t ∈ Ioo (3:ℝ) t₀, g t = h₂ t ∧ deriv g t = deriv h₂ t :=
    heq_deriv_of_eq_on_nhds (U := Ioo (3:ℝ) 4)
      (fun _ ht => Ioo_mem_nhds ht.1 (by linarith [ht.2, t₀_i_lt_four hH]))
      (fun s hs => hg_eq_h₂ s hs.1 hs.2.le)
  have heq_t₀_4 : ∀ t ∈ Ioo t₀ (4:ℝ), g t = h₂ t ∧ deriv g t = deriv h₂ t :=
    heq_deriv_of_eq_on_nhds (U := Ioo (3:ℝ) 4)
      (fun _ ht => Ioo_mem_nhds (by linarith [ht.1, t₀_i_gt_three hH]) ht.2)
      (fun s hs => hg_eq_h₂ s hs.1 hs.2.le)
  have heq_45 : ∀ t ∈ Ioo (4:ℝ) 5, g t = h₃ t ∧ deriv g t = deriv h₃ t :=
    heq_deriv_of_eq_on_nhds (U := Ioi (4:ℝ))
      (fun _ ht => Ioi_mem_nhds ht.1) (fun s hs => hg_eq_h₃ s hs)
  have hh₀_cont : ContinuousOn h₀ (Icc 0 1) :=
    fun t _ => (hd_h₀ t).continuousAt.continuousWithinAt
  have hh₁_cont_12 : ContinuousOn h₁ (Icc 1 (2 - δ)) :=
    fun t _ => (hd_h₁ t).continuousAt.continuousWithinAt
  have hh₁_cont_23 : ContinuousOn h₁ (Icc (2 + δ) 3) :=
    fun t _ => (hd_h₁ t).continuousAt.continuousWithinAt
  have hh₂_cont_3t₀ : ContinuousOn h₂ (Icc 3 t₀) :=
    fun t _ => (hd_h₂ t).continuousAt.continuousWithinAt
  have hh₂_cont_t₀4 : ContinuousOn h₂ (Icc t₀ 4) :=
    fun t _ => (hd_h₂ t).continuousAt.continuousWithinAt
  have hh₃_cont : ContinuousOn h₃ (Icc 4 5) :=
    fun t _ => (hd_h₃ t).continuousAt.continuousWithinAt
  have hh₀_diff : ∀ t ∈ Ioo (0:ℝ) 1, DifferentiableAt ℝ h₀ t :=
    fun t _ => (hd_h₀ t).differentiableAt
  have hh₁_diff_12 : ∀ t ∈ Ioo (1:ℝ) (2 - δ), DifferentiableAt ℝ h₁ t :=
    fun t _ => (hd_h₁ t).differentiableAt
  have hh₁_diff_23 : ∀ t ∈ Ioo (2 + δ) (3:ℝ), DifferentiableAt ℝ h₁ t :=
    fun t _ => (hd_h₁ t).differentiableAt
  have hh₂_diff_3t₀ : ∀ t ∈ Ioo (3:ℝ) t₀, DifferentiableAt ℝ h₂ t :=
    fun t _ => (hd_h₂ t).differentiableAt
  have hh₂_diff_t₀4 : ∀ t ∈ Ioo t₀ (4:ℝ), DifferentiableAt ℝ h₂ t :=
    fun t _ => (hd_h₂ t).differentiableAt
  have hh₃_diff : ∀ t ∈ Ioo (4:ℝ) 5, DifferentiableAt ℝ h₃ t :=
    fun t _ => (hd_h₃ t).differentiableAt
  have hh₀_deriv_cont : ContinuousOn (deriv h₀) (Icc 0 1) :=
    continuousOn_deriv_of_const _ hd_h₀ 0 1
  have hh₁_deriv_cont : ∀ (a b : ℝ), ContinuousOn (deriv h₁) (Icc a b) :=
    continuousOn_deriv_of_arc_form hd_h₁
  have hh₂_deriv_cont : ∀ (a b : ℝ), ContinuousOn (deriv h₂) (Icc a b) :=
    continuousOn_deriv_of_const _ hd_h₂
  have hh₃_deriv_cont : ContinuousOn (deriv h₃) (Icc 4 5) :=
    continuousOn_deriv_of_const _ hd_h₃ 4 5
  have hh₀_slit : ∀ t ∈ Icc (0:ℝ) 1, h₀ t ∈ slitPlane := by
    intro t ⟨_, ht1⟩; rw [← hg_eq_h₀ t ht1]
    exact g_i_slitPlane_left (by linarith)
  have piece₀ := ftc_log_pieceFM (by norm_num : (0:ℝ) ≤ 1) hh₀_cont hh₀_diff
    hh₀_deriv_cont hh₀_slit heq_01 hg0 hg1_0
  have hh₁_slit_12 : ∀ t ∈ Icc (1:ℝ) (2 - δ), h₁ t ∈ slitPlane := by
    intro t ⟨ht1, ht2⟩
    rcases eq_or_lt_of_le ht1 with rfl | ht1'
    · rw [← hg1_1]; exact g_i_slitPlane_left (by linarith)
    · rw [← hg_eq_h₁ t ht1' (by linarith)]
      exact g_i_slitPlane_left (by linarith)
  have piece₁ := ftc_log_pieceFM (by linarith : (1:ℝ) ≤ 2 - δ) hh₁_cont_12 hh₁_diff_12
    (hh₁_deriv_cont 1 (2-δ)) hh₁_slit_12 heq_1_2mδ hg1_1 hg2mδ
  have hh₁_slit_23 : ∀ t ∈ Icc (2 + δ) (3:ℝ), h₁ t ∈ slitPlane := by
    intro t ⟨ht2, ht3⟩
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · rw [← hg3_1]; exact g_i_slitPlane_arc_right (by linarith) le_rfl
    · rw [← hg_eq_h₁ t (by linarith) ht3']
      exact g_i_slitPlane_arc_right (by linarith) ht3'.le
  have piece₂ := ftc_log_pieceFM (by linarith : (2 + δ) ≤ 3) hh₁_cont_23 hh₁_diff_23
    (hh₁_deriv_cont (2+δ) 3) hh₁_slit_23 heq_2pδ_3 hg2pδ hg3_1
  have hg_eq_h₂_left : ∀ t ∈ Icc (3:ℝ) t₀, g t = h₂ t := fun t ⟨ht3, ht_t0⟩ => by
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · exact hg3_2
    rcases eq_or_lt_of_le ht_t0 with rfl | ht_t0'
    · exact hgt₀_2
    · exact hg_eq_h₂ t ht3' (by linarith)
  have hg_eq_h₂_right : ∀ t ∈ Icc t₀ (4:ℝ), g t = h₂ t := fun t ⟨ht_t0, ht4⟩ => by
    rcases eq_or_lt_of_le ht_t0 with rfl | ht_t0'
    · exact hgt₀_2
    · exact hg_eq_h₂ t (by linarith) ht4
  obtain ⟨hg_im_np_3t₀, hg_ne_3t₀, hg_im_neg_int_3t₀⟩ := g_i_seg3_left_triple H hH
  have hh₂_im_np_3t₀ : ∀ t ∈ Icc (3:ℝ) t₀, (h₂ t).im ≤ 0 := fun t ht => by
    rw [← hg_eq_h₂_left t ht]; exact hg_im_np_3t₀ t ht
  have hh₂_ne_3t₀ : ∀ t ∈ Icc (3:ℝ) t₀, h₂ t ≠ 0 := fun t ht => by
    rw [← hg_eq_h₂_left t ht]; exact hg_ne_3t₀ t ht
  have hh₂_im_neg_int_3t₀ : ∀ t ∈ Ioo (3:ℝ) t₀, (h₂ t).im < 0 := fun t ⟨ht3, ht_t0⟩ => by
    rw [← hg_eq_h₂ t ht3 (by linarith)]
    exact hg_im_neg_int_3t₀ t ⟨ht3, ht_t0⟩
  have piece₃ := ftc_log_piece_lower (by linarith : (3:ℝ) ≤ t₀)
    hh₂_cont_3t₀ hh₂_diff_3t₀ (hh₂_deriv_cont 3 t₀) hh₂_im_np_3t₀ hh₂_ne_3t₀
    hh₂_im_neg_int_3t₀ heq_3_t₀ hg3_2 hgt₀_2
  obtain ⟨hg_im_nn_t₀4, hg_ne_t₀4, hg_slit_int_t₀4⟩ := g_i_seg3_right_triple H hH
  have hh₂_im_nn_t₀4 : ∀ t ∈ Icc t₀ (4:ℝ), 0 ≤ (h₂ t).im := fun t ht => by
    rw [← hg_eq_h₂_right t ht]; exact hg_im_nn_t₀4 t ht
  have hh₂_ne_t₀4 : ∀ t ∈ Icc t₀ (4:ℝ), h₂ t ≠ 0 := fun t ht => by
    rw [← hg_eq_h₂_right t ht]; exact hg_ne_t₀4 t ht
  have hh₂_slit_int_t₀4 : ∀ t ∈ Ioo t₀ (4:ℝ), h₂ t ∈ slitPlane := fun t ⟨ht_t0, ht4⟩ => by
    rw [← hg_eq_h₂ t (by linarith) ht4.le]
    exact hg_slit_int_t₀4 t ⟨ht_t0, ht4⟩
  have piece₄ := ftc_log_piece_upper (by linarith : t₀ ≤ 4)
    hh₂_cont_t₀4 hh₂_diff_t₀4 (hh₂_deriv_cont t₀ 4)
    hh₂_im_nn_t₀4 hh₂_ne_t₀4 hh₂_slit_int_t₀4 heq_t₀_4 hgt₀_2 hg4_2
  have hh₃_slit : ∀ t ∈ Icc (4:ℝ) 5, h₃ t ∈ slitPlane := by
    intro t ⟨ht4, _⟩
    rw [Complex.mem_slitPlane_iff]; right
    simp only [h₃, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
    linarith
  have piece₅ := ftc_log_pieceFM (by norm_num : (4:ℝ) ≤ 5) hh₃_cont hh₃_diff
    hh₃_deriv_cont hh₃_slit heq_45 hg4_3 hg5
  have hint_left : IntervalIntegrable (fun t => deriv g t / g t) volume 0 (2 - δ) :=
    piece₀.1.trans piece₁.1
  have hint_right : IntervalIntegrable (fun t => deriv g t / g t) volume (2 + δ) 5 :=
    piece₂.1.trans (piece₃.1.trans (piece₄.1.trans piece₅.1))
  refine ⟨hint_left, hint_right, ?_⟩
  rw [(intervalIntegral.integral_add_adjacent_intervals piece₀.1 piece₁.1).symm,
    (intervalIntegral.integral_add_adjacent_intervals piece₂.1
      (piece₃.1.trans (piece₄.1.trans piece₅.1))).symm,
    (intervalIntegral.integral_add_adjacent_intervals piece₃.1
      (piece₄.1.trans piece₅.1)).symm,
    (intervalIntegral.integral_add_adjacent_intervals piece₄.1 piece₅.1).symm,
    piece₀.2, piece₁.2, piece₂.2, piece₃.2, piece₄.2, piece₅.2]
  have h_branch_3 : Complex.log (-(g 3)) = Complex.log (g 3) + ↑Real.pi * I :=
    log_neg_eq_add_pi_I (g_i_at_three_im_neg H)
  have hg_closed : g 0 = g 5 := fdBoundary_H_sub_closed H I
  have h_branch_t₀' : Complex.log (-(g t₀)) = Complex.log (g t₀) - ↑Real.pi * I := by
    rw [hgt₀_val]; exact log_neg_neg_half_eq_log_neg_half_sub_pi_I
  rw [hg_closed, h_branch_3, h_branch_t₀']
  ring

private lemma i_delta_lt_one {ε : ℝ} (hε_pos : 0 < ε)
    (hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12)) :
    12 / Real.pi * Real.arcsin (ε / 2) < 1 :=
  twelve_div_pi_arcsin_half_lt_one (by linarith) hε_lt_2sin

/-- Strict arc-norm monotonicity: `2·sin(a·π/12) < 2·sin(d·π/12)` for `0 < a < d < 2`. -/
private lemma arc_sin_lt {a d : ℝ} (ha : 0 < a) (had : a < d) (hd2 : d < 2) :
    2 * Real.sin (a * Real.pi / 12) < 2 * Real.sin (d * Real.pi / 12) :=
  mul_lt_mul_of_pos_left (Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))
    (by norm_num)

/-- Non-strict arc-norm monotonicity: `2·sin(a·π/12) ≤ 2·sin(d·π/12)` for `0 ≤ a ≤ d`,
`d·π/12 ≤ π/2`. -/
private lemma arc_sin_le {a d : ℝ} (ha : 0 ≤ a) (had : a ≤ d)
    (hd : d * Real.pi / 12 ≤ Real.pi / 2) :
    2 * Real.sin (a * Real.pi / 12) ≤ 2 * Real.sin (d * Real.pi / 12) :=
  mul_le_mul_of_nonneg_left (Real.sin_le_sin_of_le_of_le_pi_div_two
    (by nlinarith [Real.pi_pos]) hd (by nlinarith [Real.pi_pos])) (by norm_num)

private lemma i_h_far (H : ℝ) (hH : 1 < H) :
    let threshold := min (min (min (1/2 : ℝ) (H - 1)) (2 * Real.sin (Real.pi / 12))) 1
    ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Icc (0:ℝ) 5,
        (12 / Real.pi * Real.arcsin (ε / 2)) < |t - 2| →
        ε < ‖fdBoundary_H H t - I‖ := by
  intro threshold ε hε_pos hε_lt t _ h_abs
  have hε_lt_half : ε < 1/2 := hε_lt.trans_le
    ((min_le_left _ _).trans <| (min_le_left _ _).trans (min_le_left _ _))
  have hε_lt_gap : ε < H - 1 := hε_lt.trans_le
    ((min_le_left _ _).trans <| (min_le_left _ _).trans (min_le_right _ _))
  have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := hε_lt.trans_le
    ((min_le_left _ _).trans (min_le_right _ _))
  have hε_half_pos : 0 < ε / 2 := by linarith
  have hε_half_le : ε / 2 ≤ 1 := by linarith
  have hε_half_neg : -1 ≤ ε / 2 := by linarith
  set δ := 12 / Real.pi * Real.arcsin (ε / 2) with hδ_def
  have hδ_pos : 0 < δ := mul_pos (div_pos (by norm_num) Real.pi_pos)
    (Real.arcsin_pos.mpr hε_half_pos)
  have hδ_lt_one : δ < 1 := i_delta_lt_one hε_pos hε_lt_2sin
  have hδ_angle : δ * Real.pi / 12 = Real.arcsin (ε / 2) := by rw [hδ_def]; field_simp
  have h_norm_L : ‖fdBoundary_H H (2 - δ) - I‖ = ε := by
    rw [g_i_norm_left hδ_pos hδ_lt_one, hδ_angle,
        Real.sin_arcsin hε_half_neg hε_half_le]; linarith
  have h_norm_R : ‖fdBoundary_H H (2 + δ) - I‖ = ε := by
    rw [g_i_norm_right hδ_pos hδ_lt_one, hδ_angle,
        Real.sin_arcsin hε_half_neg hε_half_le]; linarith
  rcases lt_or_ge t (2 - δ) with h_left | h_right
  · rcases le_or_gt t 1 with ht1 | ht1
    · calc ε < 1 / 2 := hε_lt_half
        _ ≤ ‖fdBoundary_H H t - I‖ := g_i_norm_ge_seg0 ht1
    · change ε < ‖fdBoundary_H H t - I‖
      rw [g_i_norm_arc_left ht1 (by linarith), ← h_norm_L, g_i_norm_left hδ_pos hδ_lt_one]
      exact arc_sin_lt hδ_pos (by linarith) (by linarith)
  · have h_gt : 2 + δ < t := by
      rcases le_or_gt (2 : ℝ) t with h2 | h2
      · rw [abs_of_nonneg (by linarith)] at h_abs
        linarith
      · rw [abs_of_neg (by linarith)] at h_abs
        linarith
    rcases lt_or_ge t 3 with ht3 | ht3
    · change ε < ‖fdBoundary_H H t - I‖
      rw [g_i_norm_arc_right (by linarith) ht3, ← h_norm_R, g_i_norm_right hδ_pos hδ_lt_one]
      exact arc_sin_lt hδ_pos (by linarith) (by linarith)
    · rcases le_or_gt t 4 with ht4 | ht4
      · calc ε < 1 / 2 := hε_lt_half
          _ ≤ ‖fdBoundary_H H t - I‖ := g_i_norm_ge_seg3 ht3 ht4
      · calc ε < H - 1 := hε_lt_gap
          _ ≤ ‖fdBoundary_H H t - I‖ := g_i_norm_ge_seg4 H hH ht4.le

private lemma i_h_near (H : ℝ) :
    let threshold := min (min (min (1/2 : ℝ) (H - 1)) (2 * Real.sin (Real.pi / 12))) 1
    ∀ ε, 0 < ε → ε < threshold →
      ∀ t, |t - 2| ≤ (12 / Real.pi * Real.arcsin (ε / 2)) →
        ‖fdBoundary_H H t - I‖ ≤ ε := by
  intro threshold ε hε_pos hε_lt t h_abs
  have hε_lt_one : ε < 1 := hε_lt.trans_le (min_le_right _ _)
  have hε_half_pos : 0 < ε / 2 := by linarith
  have hε_half_le : ε / 2 ≤ 1 := by linarith
  have hε_half_neg : -1 ≤ ε / 2 := by linarith
  have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := hε_lt.trans_le
    ((min_le_left _ _).trans (min_le_right _ _))
  set δ := 12 / Real.pi * Real.arcsin (ε / 2) with hδ_def
  have hδ_pos : 0 < δ := mul_pos (div_pos (by norm_num) Real.pi_pos)
    (Real.arcsin_pos.mpr hε_half_pos)
  have hδ_lt_one : δ < 1 := i_delta_lt_one hε_pos hε_lt_2sin
  have hδ_angle : δ * Real.pi / 12 = Real.arcsin (ε / 2) := by rw [hδ_def]; field_simp
  have hδpi12_le : δ * Real.pi / 12 ≤ Real.pi / 2 := by
    rw [hδ_angle]; exact (Real.arcsin_lt_pi_div_two.mpr (by linarith)).le
  rw [abs_le] at h_abs
  rcases le_or_gt t 2 with ht2 | ht2
  · rcases eq_or_lt_of_le ht2 with rfl | ht2'
    · rw [fdBoundary_H_at_two_eq_I, sub_self, norm_zero]; exact hε_pos.le
    · have ht1 : 1 < t := by linarith [h_abs.1]
      rw [g_i_norm_arc_left ht1 ht2']
      calc 2 * Real.sin ((2 - t) * Real.pi / 12)
          ≤ 2 * Real.sin (δ * Real.pi / 12) :=
            arc_sin_le (by linarith) (by linarith [h_abs.1]) hδpi12_le
        _ = ε := by
            rw [hδ_angle, Real.sin_arcsin hε_half_neg hε_half_le]; linarith
  · have ht3 : t < 3 := by linarith [h_abs.2]
    rw [g_i_norm_arc_right ht2 ht3]
    calc 2 * Real.sin ((t - 2) * Real.pi / 12)
        ≤ 2 * Real.sin (δ * Real.pi / 12) :=
          arc_sin_le (by linarith) (by linarith [h_abs.2]) hδpi12_le
      _ = ε := by
          rw [hδ_angle, Real.sin_arcsin hε_half_neg hε_half_le]; linarith

private lemma i_angle_bound {δ ε : ℝ} (H : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (h_norm_L : ‖fdBoundary_H H (2 - δ) - I‖ = ε) :
    δ * Real.pi / 12 < ε :=
  delta_pi_div_twelve_lt_eps hδ_pos hδ_lt_one.le
    (by linarith [g_i_norm_left (H := H) hδ_pos hδ_lt_one])

private lemma i_ftc_integrability (H : ℝ) (hH : 1 < H) {ε : ℝ}
    (hε_pos : 0 < ε) (hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12)) :
    let δ := 12 / Real.pi * Real.arcsin (ε / 2)
    IntervalIntegrable (fun t => (fdBoundary_H H t - I)⁻¹ * deriv (fdBoundary_H H) t)
        volume 0 (2 - δ) ∧
    IntervalIntegrable (fun t => (fdBoundary_H H t - I)⁻¹ * deriv (fdBoundary_H H) t)
        volume (2 + δ) 5 ∧
    ((∫ t in (0:ℝ)..(2 - δ), (fdBoundary_H H t - I)⁻¹ * deriv (fdBoundary_H H) t) +
     (∫ t in (2 + δ)..(5:ℝ), (fdBoundary_H H t - I)⁻¹ * deriv (fdBoundary_H H) t) =
     Complex.log (fdBoundary_H H (2 - δ) - I) -
     Complex.log (fdBoundary_H H (2 + δ) - I) - 2 * ↑Real.pi * I) := by
  intro δ
  have hδ_pos : 0 < δ := mul_pos (div_pos (by norm_num) Real.pi_pos)
    (Real.arcsin_pos.mpr (by linarith))
  have hδ_lt_one : δ < 1 := i_delta_lt_one hε_pos hε_lt_2sin
  obtain ⟨hL, hR, hsum⟩ := ftc_logDeriv_telescope_i H hH hδ_pos hδ_lt_one
  have h_congr := fun t => congr_fun (inv_mul_deriv_eq_logDeriv_sub H I) t
  refine ⟨(intervalIntegrable_congr (fun t _ => h_congr t)).mpr hL,
          (intervalIntegrable_congr (fun t _ => h_congr t)).mpr hR, ?_⟩
  simp_rw [h_congr]; exact hsum

private lemma i_E_tendsto (H : ℝ) (_ : 1 < H) (threshold : ℝ) (hthresh_pos : 0 < threshold)
    (hthresh_le_2sin : threshold ≤ 2 * Real.sin (Real.pi / 12))
    (hthresh_le_one : threshold ≤ 1) :
    Tendsto (fun ε =>
        Complex.log (fdBoundary_H H (2 - 12 / Real.pi * Real.arcsin (ε / 2)) - I) -
        Complex.log (fdBoundary_H H (2 + 12 / Real.pi * Real.arcsin (ε / 2)) - I) -
        2 * ↑Real.pi * I)
      (𝓝[>] 0) (𝓝 (-(I * ↑Real.pi))) := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro r hr
  refine ⟨min threshold (r/2), lt_min hthresh_pos (by linarith), ?_⟩
  intro ε hε_mem hε_dist
  simp only [Set.mem_Ioi] at hε_mem
  rw [Real.dist_eq, sub_zero, abs_of_pos hε_mem] at hε_dist
  have hε_pos : 0 < ε := hε_mem
  have hε_lt : ε < threshold := hε_dist.trans_le (min_le_left _ _)
  have hε_lt_r2 : ε < r / 2 := hε_dist.trans_le (min_le_right _ _)
  have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := hε_lt.trans_le hthresh_le_2sin
  have hε_half_neg : -1 ≤ ε / 2 := by linarith
  have hε_half_le : ε / 2 ≤ 1 := by linarith [hε_lt.trans_le hthresh_le_one]
  have hε_half_pos : 0 < ε / 2 := by linarith
  have hδ_pos : 0 < 12 / Real.pi * Real.arcsin (ε / 2) :=
    mul_pos (div_pos (by norm_num) hpi_pos) (Real.arcsin_pos.mpr hε_half_pos)
  have hδ_lt_one : 12 / Real.pi * Real.arcsin (ε / 2) < 1 :=
    i_delta_lt_one hε_pos hε_lt_2sin
  have hsin_eq : Real.sin ((12 / Real.pi * Real.arcsin (ε / 2)) * Real.pi / 12) = ε / 2 := by
    have : (12 / Real.pi * Real.arcsin (ε / 2)) * Real.pi / 12 = Real.arcsin (ε / 2) := by
      field_simp
    rw [this, Real.sin_arcsin hε_half_neg hε_half_le]
  have h_angle_bnd : (12 / Real.pi * Real.arcsin (ε / 2)) * Real.pi / 12 < ε :=
    i_angle_bound H hδ_pos hδ_lt_one (by rw [g_i_norm_left hδ_pos hδ_lt_one]; linarith)
  have h_nL : ‖fdBoundary_H H (2 - 12 / Real.pi * Real.arcsin (ε / 2)) - I‖ = ε := by
    rw [g_i_norm_left hδ_pos hδ_lt_one]; linarith
  have h_nR : ‖fdBoundary_H H (2 + 12 / Real.pi * Real.arcsin (ε / 2)) - I‖ = ε := by
    rw [g_i_norm_right hδ_pos hδ_lt_one]
    linarith [h_nL, g_i_norm_left (H := H) hδ_pos hδ_lt_one]
  have h_E_eq :
      Complex.log (fdBoundary_H H (2 - 12 / Real.pi * Real.arcsin (ε / 2)) - I) -
      Complex.log (fdBoundary_H H (2 + 12 / Real.pi * Real.arcsin (ε / 2)) - I) -
      2 * ↑Real.pi * I - -(I * ↑Real.pi) =
      -(↑((12 / Real.pi * Real.arcsin (ε / 2)) * Real.pi / 6) * I) := by
    rw [← Complex.re_add_im (Complex.log (fdBoundary_H H (2 - 12 / Real.pi * Real.arcsin (ε / 2)) - I)),
        ← Complex.re_add_im (Complex.log (fdBoundary_H H (2 + 12 / Real.pi * Real.arcsin (ε / 2)) - I)),
        Complex.log_re, Complex.log_re, Complex.log_im, Complex.log_im,
        arg_approach_i_left (H := H) hδ_pos hδ_lt_one,
        arg_approach_i_right (H := H) hδ_pos hδ_lt_one, h_nL, h_nR]
    push_cast; ring
  rw [Complex.dist_eq, h_E_eq, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  linarith

/-- The PV integral of `(γ-I)⁻¹ γ'` over `[0,5]` with ε-ball cutoff tends to `-iπ`.

Proof wires through `pv_tendsto_of_crossing_limit` with:
- `t₀ = 2` (arc crossing at `i`)
- `δ(ε) = 12/π · arcsin(ε/2)` (arc-length inverse of the norm formula)
- `E(ε) = log(g(2-δ)) - log(g(2+δ)) - 2πi` (FTC telescope with branch correction)
- `h_limit : E(ε) → -(I·π)` (arg computation shows the difference is constantly `-iπ`) -/
theorem pv_integral_at_i_tendsto (H : ℝ) (hH : 1 < H) :
    Tendsto (fun ε => ∫ t in (0:ℝ)..5, if ‖fdBoundary_H H t - I‖ > ε
      then (fdBoundary_H H t - I)⁻¹ *
           deriv (fun s => fdBoundary_H H s - I) t
      else 0) (𝓝[>] 0) (𝓝 (-(I * ↑Real.pi))) := by
  have hderiv_eq : ∀ t : ℝ, deriv (fun s => fdBoundary_H H s - I) t =
      deriv (fdBoundary_H H) t := fun t => deriv_sub_const (f := fdBoundary_H H) _
  simp_rw [hderiv_eq]
  have h2sin_pos := two_sin_pi_div_twelve_pos
  set threshold := min (min (min (1/2 : ℝ) (H - 1)) (2 * Real.sin (Real.pi / 12))) 1
  have hthresh_pos : 0 < threshold :=
    lt_min (lt_min (lt_min (by norm_num) (by linarith)) h2sin_pos) one_pos
  have hthresh_le_2sin : threshold ≤ 2 * Real.sin (Real.pi / 12) :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hthresh_le_one : threshold ≤ 1 := min_le_right _ _
  have hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < 12 / Real.pi * Real.arcsin (ε / 2) :=
    fun ε hε _ => mul_pos (div_pos (by norm_num) Real.pi_pos)
      (Real.arcsin_pos.mpr (by linarith))
  have hδ_small : ∀ ε, 0 < ε → ε < threshold →
      12 / Real.pi * Real.arcsin (ε / 2) < min (2 - 0) (5 - 2) := by
    intro ε hε_pos hε_lt
    have hδ1 : 12 / Real.pi * Real.arcsin (ε / 2) < 1 :=
      i_delta_lt_one hε_pos (hε_lt.trans_le hthresh_le_2sin)
    simp only [sub_zero]; apply lt_min <;> linarith
  apply ContourIntegral.pv_tendsto_of_crossing_limit
    (t₀ := 2) (ht₀ := by norm_num)
    (threshold := threshold) (hthresh := hthresh_pos)
    (δ := fun ε => 12 / Real.pi * Real.arcsin (ε / 2))
    (E := fun ε =>
      Complex.log (fdBoundary_H H (2 - 12 / Real.pi * Real.arcsin (ε / 2)) - I) -
      Complex.log (fdBoundary_H H (2 + 12 / Real.pi * Real.arcsin (ε / 2)) - I) -
      2 * ↑Real.pi * I)
  · exact hδ_pos
  · exact hδ_small
  · intro ε hε_pos hε_lt; exact i_h_far H hH ε hε_pos hε_lt
  · intro ε hε_pos hε_lt; exact i_h_near H ε hε_pos hε_lt
  · intro ε hε_pos hε_lt
    exact (i_ftc_integrability H hH hε_pos (hε_lt.trans_le hthresh_le_2sin)).2.2
  · intro ε hε_pos hε_lt
    exact (i_ftc_integrability H hH hε_pos (hε_lt.trans_le hthresh_le_2sin)).1
  · intro ε hε_pos hε_lt
    exact (i_ftc_integrability H hH hε_pos (hε_lt.trans_le hthresh_le_2sin)).2.1
  · exact i_E_tendsto H hH threshold hthresh_pos hthresh_le_2sin hthresh_le_one

end
