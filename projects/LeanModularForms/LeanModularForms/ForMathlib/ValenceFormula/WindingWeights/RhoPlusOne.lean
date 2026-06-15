/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ValenceFormula.WindingWeights.Common
import LeanModularForms.ForMathlib.ContourIntegral.CrossingLimit

/-!
# Winding Number Weight at ρ+1

PV integral computation and generalized winding number of `fdBoundary_H`
around the elliptic point ρ+1 = e^{πi/3}.

## Main Results

* `pv_integral_at_rho_plus_one_tendsto` — PV integral converges to -iπ/3
* `gWN_fdBoundary_H_at_rho_plus_one` — gWN = -1/6 at ρ+1
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

private lemma g_rho'_seg0_value {t : ℝ} (ht : t ≤ 1) :
    fdBoundary_H H t - ellipticPointRhoPlusOne =
    ↑((1 - t) * (H - Real.sqrt 3 / 2)) * I := by
  rw [fdBoundary_H_seg1 H ht]
  simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  push_cast; ring

private lemma g_rho'_norm_seg0 (hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht1 : t < 1) :
    ‖fdBoundary_H H t - ellipticPointRhoPlusOne‖ = (1 - t) * (H - Real.sqrt 3 / 2) := by
  rw [g_rho'_seg0_value ht1.le, norm_mul, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_of_nonneg (mul_nonneg (by linarith) (by linarith))]

private lemma g_rho'_arc_value {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    fdBoundary_H H t - ellipticPointRhoPlusOne =
    Complex.exp (↑(Real.pi * (1 + t) / 6) * I) - (↑(1/2 : ℝ) + ↑(Real.sqrt 3 / 2) * I) := by
  rw [fdBoundary_H_eq_arc ht1 ht3]
  simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  push_cast; ring

private lemma g_rho'_seg3_value {t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) :
    fdBoundary_H H t - ellipticPointRhoPlusOne =
    -1 + ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I := by
  rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) ht4]
  simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  push_cast; ring

private lemma g_rho'_seg4_value {t : ℝ} (ht4 : 4 < t) :
    fdBoundary_H H t - ellipticPointRhoPlusOne =
    ↑(t - 5) + ↑(H - Real.sqrt 3 / 2) * I := by
  rw [fdBoundary_H_seg5 H (by linarith) (by linarith) (by linarith) (by linarith)]
  simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  push_cast; ring

private lemma sin_ge_sqrt3_div_2_of_mem {θ : ℝ} (hlo : Real.pi / 3 ≤ θ)
    (hhi : θ ≤ 2 * Real.pi / 3) : Real.sqrt 3 / 2 ≤ Real.sin θ := by
  rw [← Real.sin_pi_div_three]
  by_cases h : θ ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos]) h hlo
  · push Not at h
    rw [show θ = Real.pi - (Real.pi - θ) by ring, Real.sin_pi_sub]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by nlinarith [Real.pi_pos]) (by nlinarith) (by nlinarith)

private lemma sin_gt_sqrt3_div_2_of_mem {θ : ℝ} (hlo : Real.pi / 3 < θ)
    (hhi : θ < 2 * Real.pi / 3) : Real.sqrt 3 / 2 < Real.sin θ := by
  rw [← Real.sin_pi_div_three]
  by_cases h : θ ≤ Real.pi / 2
  · exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by nlinarith [Real.pi_pos]) h hlo
  · push Not at h
    rw [show θ = Real.pi - (Real.pi - θ) by ring, Real.sin_pi_sub]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by nlinarith [Real.pi_pos]) (by nlinarith) (by nlinarith)

/-- Imaginary part of `γ(t) - ρ'` on the arc `(1, 3)`: `sin(π(1+t)/6) - √3/2`. -/
private lemma g_rho'_arc_im (H : ℝ) {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    (fdBoundary_H H t - ellipticPointRhoPlusOne).im =
      Real.sin (Real.pi * (1 + t) / 6) - Real.sqrt 3 / 2 := by
  rw [g_rho'_arc_value ht1 ht3]
  simp only [Complex.sub_im, Complex.exp_im, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero, Real.exp_zero, one_mul,
    add_im, ofReal_im, mul_im, ofReal_re, add_zero, zero_add]

private lemma g_rho'_im_nonneg (hH : Real.sqrt 3 / 2 < H) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 5) (hne : t ≠ 1) :
    0 ≤ (fdBoundary_H H t - ellipticPointRhoPlusOne).im := by
  rcases le_or_gt t 1 with h1 | h1
  · have ht1 : t < 1 := lt_of_le_of_ne h1 hne
    rw [g_rho'_seg0_value h1, mul_comm, Complex.I_mul_im, Complex.ofReal_re]
    exact mul_nonneg (by linarith) (by linarith)
  · rcases lt_or_ge t 3 with h3 | h3
    · rw [g_rho'_arc_im H h1 h3]
      linarith [sin_ge_sqrt3_div_2_of_mem (θ := Real.pi * (1 + t) / 6)
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
    · rcases eq_or_lt_of_le h3 with rfl | h3'
      · simp [fdBoundary_H_at_three_eq_rho, ellipticPointRho', ellipticPointRhoPlusOne']
      · rcases le_or_gt t 4 with h4 | h4
        · rw [g_rho'_seg3_value h3' h4]
          simp only [Complex.add_im, Complex.neg_im, Complex.one_im, Complex.mul_im,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, mul_zero,
            zero_add, neg_zero, mul_one, add_zero]
          exact mul_nonneg (by linarith) (by linarith)
        · rw [g_rho'_seg4_value h4]
          simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, mul_zero, mul_one, zero_add, add_zero]
          linarith

private lemma g_rho'_ne_zero (hH : Real.sqrt 3 / 2 < H) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 5) (hne : t ≠ 1) :
    fdBoundary_H H t - ellipticPointRhoPlusOne ≠ 0 := by
  intro h_eq
  rcases le_or_gt t 1 with h1 | h1
  · have ht1 : t < 1 := lt_of_le_of_ne h1 hne
    rw [g_rho'_seg0_value h1] at h_eq
    have := congr_arg Complex.im h_eq; simp at this
    rcases this with h | h <;> linarith
  · rcases lt_or_ge t 3 with h3 | h3
    · have him_pos : 0 < (fdBoundary_H H t - ellipticPointRhoPlusOne).im := by
        rw [g_rho'_arc_im H h1 h3]
        linarith [sin_gt_sqrt3_div_2_of_mem (θ := Real.pi * (1 + t) / 6)
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
      rw [h_eq] at him_pos
      simp only [Complex.zero_im, lt_irrefl] at him_pos
    · rcases eq_or_lt_of_le h3 with rfl | h3'
      · simp [fdBoundary_H_at_three_eq_rho, ellipticPointRho', ellipticPointRhoPlusOne',
          Complex.ext_iff] at h_eq
        linarith
      · rcases le_or_gt t 4 with h4 | h4
        · rw [g_rho'_seg3_value h3' h4] at h_eq
          have := congr_arg Complex.re h_eq; simp at this
        · rw [g_rho'_seg4_value h4] at h_eq
          have := congr_arg Complex.im h_eq; simp at this; linarith

private lemma g_rho'_slitPlane (hH : Real.sqrt 3 / 2 < H) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 5) (hne1 : t ≠ 1) (hne3 : t ≠ 3) :
    fdBoundary_H H t - ellipticPointRhoPlusOne ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  rcases le_or_gt t 1 with h1 | h1
  · have ht1 : t < 1 := lt_of_le_of_ne h1 hne1
    rw [g_rho'_seg0_value h1, mul_comm, Complex.I_mul_im, Complex.ofReal_re]
    exact ne_of_gt (mul_pos (by linarith) (by linarith))
  · rcases lt_or_ge t 3 with h3 | h3
    · rw [g_rho'_arc_im H h1 h3]
      have := sin_gt_sqrt3_div_2_of_mem (θ := Real.pi * (1 + t) / 6)
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      exact ne_of_gt (by linarith)
    · rcases eq_or_lt_of_le h3 with rfl | h3'
      · exact absurd rfl hne3
      · rcases le_or_gt t 4 with h4 | h4
        · rw [g_rho'_seg3_value h3' h4]
          simp only [Complex.add_im, Complex.neg_im, Complex.one_im, Complex.mul_im,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, mul_zero,
            zero_add, neg_zero, mul_one, add_zero]
          exact ne_of_gt (mul_pos (by linarith) (by linarith))
        · rw [g_rho'_seg4_value h4]
          simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, mul_zero, mul_one, zero_add, add_zero]
          exact ne_of_gt (by linarith)

private lemma arg_approach_rho'_left (hH : Real.sqrt 3 / 2 < H) {δ : ℝ} (hδ : 0 < δ) :
    (fdBoundary_H H (1 - δ) - ellipticPointRhoPlusOne).arg = Real.pi / 2 := by
  rw [g_rho'_seg0_value (by linarith : 1 - δ ≤ 1), show (1 - (1 - δ)) = δ by ring]
  exact arg_ofReal_mul_I (by nlinarith)

private lemma g_rho'_norm_seg0_at (hH : Real.sqrt 3 / 2 < H) {δ : ℝ} (hδ : 0 < δ) :
    ‖fdBoundary_H H (1 - δ) - ellipticPointRhoPlusOne‖ = δ * (H - Real.sqrt 3 / 2) := by
  rw [g_rho'_seg0_value (by linarith : 1 - δ ≤ 1), show (1 - (1 - δ)) = δ by ring,
    norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_of_nonneg (mul_nonneg hδ.le (by linarith))]

/-- Shared trig factoring: on the arc `t = 1 + δ`, the displacement from `ρ' = 1/2 + √3/2 i`
factors as `2 sin(δπ/12) · exp(i(5π/6 + δπ/12))`. -/
private lemma rho'_arc_factor (δ : ℝ) :
    (↑(Real.cos (Real.pi * (1 + (1 + δ)) / 6)) +
        ↑(Real.sin (Real.pi * (1 + (1 + δ)) / 6)) * I -
        (↑(1/2 : ℝ) + ↑(Real.sqrt 3 / 2) * I) : ℂ) =
      ↑(2 * Real.sin (δ * Real.pi / 12)) *
        (↑(Real.cos (5 * Real.pi / 6 + δ * Real.pi / 12)) +
         ↑(Real.sin (5 * Real.pi / 6 + δ * Real.pi / 12)) * I) := by
  set θ : ℝ := Real.pi * (1 + (1 + δ)) / 6 with hθ_def
  set φ := Real.pi / 3 + δ * Real.pi / 12 with hφ_def
  have hθ_eq : θ = Real.pi / 3 + δ * Real.pi / 6 := by simp only [hθ_def]; ring
  have h_cos_sub : Real.cos θ - 1 / 2 = -2 * Real.sin (δ * Real.pi / 12) * Real.sin φ := by
    have h := Real.cos_sub_cos θ (Real.pi / 3)
    rw [show (θ + Real.pi / 3) / 2 = φ by simp only [hφ_def, hθ_eq]; ring,
        show (θ - Real.pi / 3) / 2 = δ * Real.pi / 12 by rw [hθ_eq]; ring] at h
    linarith [Real.cos_pi_div_three]
  have h_sin_sub : Real.sin θ - Real.sqrt 3 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos φ := by
    have h := Real.sin_sub_sin θ (Real.pi / 3)
    rw [show (θ - Real.pi / 3) / 2 = δ * Real.pi / 12 by rw [hθ_eq]; ring,
        show (θ + Real.pi / 3) / 2 = φ by simp only [hφ_def, hθ_eq]; ring] at h
    linarith [Real.sin_pi_div_three]
  have h_neg_sin_eq : -Real.sin φ = Real.cos (5 * Real.pi / 6 + δ * Real.pi / 12) := by
    rw [show 5 * Real.pi / 6 + δ * Real.pi / 12 = Real.pi / 2 + φ by simp only [hφ_def]; ring,
      Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have h_cos_eq : Real.cos φ = Real.sin (5 * Real.pi / 6 + δ * Real.pi / 12) := by
    rw [show 5 * Real.pi / 6 + δ * Real.pi / 12 = Real.pi / 2 + φ by simp only [hφ_def]; ring,
      Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  rw [← h_neg_sin_eq, ← h_cos_eq]
  apply Complex.ext
  · simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, mul_one]
    linarith [h_cos_sub]
  · simp only [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, add_zero, mul_one]
    linarith [h_sin_sub]

private lemma arg_approach_rho'_right_helper (hδ : 0 < δ) (hδ_small : δ < 2) :
    (fdBoundary_H H (1 + δ) - ellipticPointRhoPlusOne).arg =
      5 * Real.pi / 6 + δ * Real.pi / 12 := by
  rw [g_rho'_arc_value (by linarith) (by linarith), Complex.exp_ofReal_mul_I, rho'_arc_factor δ,
    Complex.ofReal_cos, Complex.ofReal_sin]
  have h_sin_pos : 0 < Real.sin (δ * Real.pi / 12) :=
    sin_delta_pi_div_twelve_pos hδ hδ_small
  exact Complex.arg_mul_cos_add_sin_mul_I (mul_pos (by norm_num : (0:ℝ) < 2) h_sin_pos)
    ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩

private lemma g_rho'_norm_arc {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 2) :
    ‖fdBoundary_H H (1 + δ) - ellipticPointRhoPlusOne‖ = 2 * Real.sin (δ * Real.pi / 12) := by
  rw [g_rho'_arc_value (by linarith : 1 < 1 + δ) (by linarith : 1 + δ < 3),
    Complex.exp_ofReal_mul_I, rho'_arc_factor δ, ← Complex.exp_ofReal_mul_I]
  exact norm_two_sin_mul_exp hδ hδ2

private lemma g_rho'_norm_arc_full {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    ‖fdBoundary_H H t - ellipticPointRhoPlusOne‖ = 2 * Real.sin ((t - 1) * Real.pi / 12) := by
  convert g_rho'_norm_arc (δ := t - 1) (by linarith) (by linarith) using 2 <;> ring_nf

private lemma g_rho'_norm_ge_seg4 (hH : Real.sqrt 3 / 2 < H) {t : ℝ}
    (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    H - Real.sqrt 3 / 2 ≤ ‖fdBoundary_H H t - ellipticPointRhoPlusOne‖ := by
  have him : (fdBoundary_H H t - (ellipticPointRhoPlusOne : ℂ)).im = H - Real.sqrt 3 / 2 := by
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · have : fdBoundary_H H 4 - (ellipticPointRhoPlusOne : ℂ) =
          -1 + ↑(H - Real.sqrt 3 / 2) * I := by
        rw [fdBoundary_H_at_four]
        simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
        push_cast; ring
      rw [this, Complex.add_im, Complex.neg_im, Complex.one_im, mul_comm,
        Complex.I_mul_im, Complex.ofReal_re]; ring
    · rw [g_rho'_seg4_value ht4']
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, mul_zero, zero_add, add_zero, mul_one]
  calc H - Real.sqrt 3 / 2 = |(H - Real.sqrt 3 / 2 : ℝ)| := (abs_of_pos (by linarith)).symm
    _ = |(fdBoundary_H H t - (ellipticPointRhoPlusOne : ℂ)).im| := by rw [him]
    _ ≤ ‖fdBoundary_H H t - (ellipticPointRhoPlusOne : ℂ)‖ := Complex.abs_im_le_norm _

private lemma g_rho'_norm_ge_one_seg3 {t : ℝ} (ht3 : 3 ≤ t) (ht4 : t ≤ 4) :
    1 ≤ ‖fdBoundary_H H t - ellipticPointRhoPlusOne‖ := by
  rcases eq_or_lt_of_le ht3 with rfl | ht3'
  · rw [fdBoundary_H_at_three_eq_rho]
    simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
      ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    have : (-1/2 + ↑(Real.sqrt 3) / 2 * I - (1/2 + ↑(Real.sqrt 3) / 2 * I) : ℂ) = -1 := by
      ring
    rw [this, norm_neg, norm_one]
  · have hre : (fdBoundary_H H t - (ellipticPointRhoPlusOne : ℂ)).re = -1 := by
      rw [g_rho'_seg3_value (H := H) ht3' ht4]
      simp [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
    calc 1 = |(-1 : ℝ)| := by norm_num
      _ = |(fdBoundary_H H t - (ellipticPointRhoPlusOne : ℂ)).re| := by rw [hre]
      _ ≤ ‖fdBoundary_H H t - (ellipticPointRhoPlusOne : ℂ)‖ := Complex.abs_re_le_norm _

/-- **Triple property of `g = fdBoundary_H H t - ellipticPointRhoPlusOne` on
`[1 + δ_R, 3]`** (the right half of the arc-1 piece): nonneg imaginary part,
nonzero, and interior in `slitPlane`. -/
private lemma g_rho'_arc_right_triple (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {δ_R : ℝ} (hδ_R : 0 < δ_R) :
    (∀ t ∈ Icc (1 + δ_R) (3:ℝ),
      0 ≤ (fdBoundary_H H t - (ellipticPointRhoPlusOne : ℂ)).im) ∧
    (∀ t ∈ Icc (1 + δ_R) (3:ℝ),
      fdBoundary_H H t - (ellipticPointRhoPlusOne : ℂ) ≠ 0) ∧
    (∀ t ∈ Ioo (1 + δ_R) (3:ℝ),
      fdBoundary_H H t - (ellipticPointRhoPlusOne : ℂ) ∈ slitPlane) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ⟨ht1, ht3⟩
    exact g_rho'_im_nonneg hH ⟨by linarith, by linarith⟩ (by linarith)
  · intro t ⟨ht1, ht3⟩
    exact g_rho'_ne_zero hH ⟨by linarith, by linarith⟩ (by linarith)
  · intro t ⟨ht1, ht3⟩
    exact g_rho'_slitPlane hH ⟨by linarith, by linarith⟩ (by linarith) (by linarith)

/-- **Triple property of `g = fdBoundary_H H t - ellipticPointRhoPlusOne` on
`[3, 4]`** (segment 3): nonneg imaginary part, nonzero, and interior in
`slitPlane`. -/
private lemma g_rho'_seg3_triple (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    (∀ t ∈ Icc (3:ℝ) 4,
      0 ≤ (fdBoundary_H H t - (ellipticPointRhoPlusOne : ℂ)).im) ∧
    (∀ t ∈ Icc (3:ℝ) 4,
      fdBoundary_H H t - (ellipticPointRhoPlusOne : ℂ) ≠ 0) ∧
    (∀ t ∈ Ioo (3:ℝ) 4,
      fdBoundary_H H t - (ellipticPointRhoPlusOne : ℂ) ∈ slitPlane) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ⟨ht3, ht4⟩
    exact g_rho'_im_nonneg hH ⟨by linarith, by linarith⟩ (by linarith)
  · intro t ⟨ht3, ht4⟩
    exact g_rho'_ne_zero hH ⟨by linarith, by linarith⟩ (by linarith)
  · intro t ⟨ht3, ht4⟩
    exact g_rho'_slitPlane hH ⟨by linarith, by linarith⟩ (by linarith) (by linarith)

/-- **Slit-plane membership of `g = fdBoundary_H H t - ellipticPointRhoPlusOne`
on `[4, 5]`** (segment 4). -/
private lemma g_rho'_seg4_slit (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    ∀ t ∈ Icc (4:ℝ) 5,
      fdBoundary_H H t - (ellipticPointRhoPlusOne : ℂ) ∈ slitPlane := fun t ⟨ht4, ht5⟩ =>
  g_rho'_slitPlane hH ⟨by linarith, ht5⟩ (by linarith) (by linarith)

private lemma ftc_logDeriv_telescope_rho_plus_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {δ_L δ_R : ℝ} (hδ_L : 0 < δ_L) (hδ_L1 : δ_L < 1) (hδ_R : 0 < δ_R) (hδ_R1 : δ_R < 1) :
    let g := fun t => fdBoundary_H H t - (ellipticPointRhoPlusOne : ℂ)
    IntervalIntegrable (fun t => deriv g t / g t) volume 0 (1 - δ_L) ∧
    IntervalIntegrable (fun t => deriv g t / g t) volume (1 + δ_R) 5 ∧
    ((∫ t in (0:ℝ)..(1 - δ_L), deriv g t / g t) + (∫ t in (1 + δ_R)..(5:ℝ), deriv g t / g t) =
    Complex.log (g (1 - δ_L)) - Complex.log (g (1 + δ_R))) := by
  intro g
  set ρ' : ℂ := ellipticPointRhoPlusOne with hρ'_def
  set h₀ : ℝ → ℂ := fun t => ↑((1 - t) * (H - Real.sqrt 3 / 2)) * I
  set h₁ : ℝ → ℂ := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - ρ'
  set h₂ : ℝ → ℂ := fun t => -1 + ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I
  set h₃ : ℝ → ℂ := fun t => ↑(t - 5) + ↑(H - Real.sqrt 3 / 2) * I
  have hg_eq_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := fun t ht => by
    change fdBoundary_H H t - ρ' = h₀ t; rw [g_rho'_seg0_value ht]
  have hg_eq_h₁ : ∀ t, 1 < t → t < 3 → g t = h₁ t := fun t ht1 ht3 => by
    change fdBoundary_H H t - ρ' = h₁ t
    rw [g_rho'_arc_value ht1 ht3]
    simp only [h₁, hρ'_def, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
      UpperHalfPlane.coe_mk]
    push_cast; ring
  have hg_eq_h₂ : ∀ t, 3 < t → t ≤ 4 → g t = h₂ t := fun t ht3 ht4 => by
    change fdBoundary_H H t - ρ' = h₂ t; rw [g_rho'_seg3_value ht3 ht4]
  have hg_eq_h₃ : ∀ t, 4 < t → g t = h₃ t := fun t ht4 => by
    change fdBoundary_H H t - ρ' = h₃ t; rw [g_rho'_seg4_value ht4]
  have hg0 : g 0 = h₀ 0 := hg_eq_h₀ 0 (by norm_num)
  have hg1mδ : g (1 - δ_L) = h₀ (1 - δ_L) := hg_eq_h₀ (1 - δ_L) (by linarith)
  have hg1pδ : g (1 + δ_R) = h₁ (1 + δ_R) := hg_eq_h₁ (1 + δ_R) (by linarith) (by linarith)
  have hg3_1 : g 3 = h₁ 3 := by
    change fdBoundary_H H 3 - ρ' = h₁ 3
    rw [fdBoundary_H_at_three_eq_rho]
    simp only [h₁, hρ'_def, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
      ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
      show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 by ring]
    rw [Complex.exp_ofReal_mul_I, cos_two_pi_div_three, sin_two_pi_div_three]
    push_cast; ring
  have hg3_2 : g 3 = h₂ 3 := by
    change fdBoundary_H H 3 - ρ' = h₂ 3
    rw [fdBoundary_H_at_three_eq_rho]
    simp only [h₂, hρ'_def, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
      ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    push_cast; ring
  have hg4_2 : g 4 = h₂ 4 := hg_eq_h₂ 4 (by linarith) le_rfl
  have hg4_3 : g 4 = h₃ 4 := by
    change fdBoundary_H H 4 - ρ' = h₃ 4
    rw [fdBoundary_H_at_four H]
    simp only [hρ'_def, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
      UpperHalfPlane.coe_mk, h₃]
    push_cast; ring
  have hg5 : g 5 = h₃ 5 := hg_eq_h₃ 5 (by norm_num)
  have hd_h₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t :=
    hasDerivAt_aff_imI_neg (H - Real.sqrt 3 / 2) 1
  have hd_h₁ : ∀ t : ℝ, HasDerivAt h₁
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t :=
    fun t => hasDerivAt_arc_sub_const ρ' t
  have hd_h₂ : ∀ t : ℝ, HasDerivAt h₂ ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := fun t =>
    ((hasDerivAt_const t (-1:ℂ)).add
      (hasDerivAt_aff_imI_pos (H - Real.sqrt 3 / 2) 3 t)).congr_deriv (by simp [zero_add])
  have hd_h₃ : ∀ t : ℝ, HasDerivAt h₃ 1 t :=
    hasDerivAt_seg5_line 5 (↑(H - Real.sqrt 3 / 2) * I)
  have heq_0_1mδ : ∀ t ∈ Ioo (0:ℝ) (1 - δ_L),
      g t = h₀ t ∧ deriv g t = deriv h₀ t :=
    heq_deriv_of_eq_on_nhds (U := Iio (1:ℝ))
      (fun _ ht => Iio_mem_nhds (by linarith [ht.2]))
      (fun s hs => hg_eq_h₀ s hs.le)
  have heq_1pδ_3 : ∀ t ∈ Ioo (1 + δ_R) (3:ℝ),
      g t = h₁ t ∧ deriv g t = deriv h₁ t :=
    heq_deriv_of_eq_on_nhds (U := Ioo (1:ℝ) 3)
      (fun _ ht => Ioo_mem_nhds (by linarith [ht.1]) ht.2)
      (fun s hs => hg_eq_h₁ s hs.1 hs.2)
  have heq_34 : ∀ t ∈ Ioo (3:ℝ) 4, g t = h₂ t ∧ deriv g t = deriv h₂ t :=
    heq_deriv_of_eq_on_nhds (U := Ioo (3:ℝ) 4)
      (fun _ ht => Ioo_mem_nhds ht.1 ht.2)
      (fun s hs => hg_eq_h₂ s hs.1 hs.2.le)
  have heq_45 : ∀ t ∈ Ioo (4:ℝ) 5, g t = h₃ t ∧ deriv g t = deriv h₃ t :=
    heq_deriv_of_eq_on_nhds (U := Ioi (4:ℝ))
      (fun _ ht => Ioi_mem_nhds ht.1) (fun s hs => hg_eq_h₃ s hs)
  have hh₀_cont : ContinuousOn h₀ (Icc 0 (1 - δ_L)) :=
    fun t _ => (hd_h₀ t).continuousAt.continuousWithinAt
  have hh₁_cont : ContinuousOn h₁ (Icc (1 + δ_R) 3) :=
    fun t _ => (hd_h₁ t).continuousAt.continuousWithinAt
  have hh₂_cont : ContinuousOn h₂ (Icc 3 4) :=
    fun t _ => (hd_h₂ t).continuousAt.continuousWithinAt
  have hh₃_cont : ContinuousOn h₃ (Icc 4 5) :=
    fun t _ => (hd_h₃ t).continuousAt.continuousWithinAt
  have hh₀_diff : ∀ t ∈ Ioo (0:ℝ) (1 - δ_L), DifferentiableAt ℝ h₀ t :=
    fun t _ => (hd_h₀ t).differentiableAt
  have hh₁_diff : ∀ t ∈ Ioo (1 + δ_R) (3:ℝ), DifferentiableAt ℝ h₁ t :=
    fun t _ => (hd_h₁ t).differentiableAt
  have hh₂_diff : ∀ t ∈ Ioo (3:ℝ) 4, DifferentiableAt ℝ h₂ t :=
    fun t _ => (hd_h₂ t).differentiableAt
  have hh₃_diff : ∀ t ∈ Ioo (4:ℝ) 5, DifferentiableAt ℝ h₃ t :=
    fun t _ => (hd_h₃ t).differentiableAt
  have hh₀_deriv_cont : ContinuousOn (deriv h₀) (Icc 0 (1 - δ_L)) :=
    continuousOn_deriv_of_const _ hd_h₀ 0 (1 - δ_L)
  have hh₁_deriv_cont : ContinuousOn (deriv h₁) (Icc (1 + δ_R) 3) :=
    continuousOn_deriv_of_arc_form hd_h₁ (1 + δ_R) 3
  have hh₂_deriv_cont : ContinuousOn (deriv h₂) (Icc 3 4) :=
    continuousOn_deriv_of_const _ hd_h₂ 3 4
  have hh₃_deriv_cont : ContinuousOn (deriv h₃) (Icc 4 5) :=
    continuousOn_deriv_of_const _ hd_h₃ 4 5
  have hh₀_slit : ∀ t ∈ Icc (0:ℝ) (1 - δ_L), h₀ t ∈ slitPlane := fun t ⟨ht0, ht1⟩ => by
    rw [← hg_eq_h₀ t (by linarith)]
    exact g_rho'_slitPlane hH ⟨ht0, by linarith⟩ (by linarith) (by linarith)
  have piece₀ := ftc_log_pieceFM (by linarith : (0:ℝ) ≤ 1 - δ_L) hh₀_cont hh₀_diff
    hh₀_deriv_cont hh₀_slit heq_0_1mδ hg0 hg1mδ
  have hg_eq_h₁_on : ∀ t ∈ Icc (1 + δ_R) (3:ℝ), g t = h₁ t := fun t ⟨_, ht3⟩ => by
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · exact hg3_1
    · exact hg_eq_h₁ t (by linarith) ht3'
  obtain ⟨hg_im_nn_arc_R, hg_ne_arc_R, hg_slit_arc_R⟩ := g_rho'_arc_right_triple H hH hδ_R
  have hh₁_im_nn : ∀ t ∈ Icc (1 + δ_R) (3:ℝ), 0 ≤ (h₁ t).im := fun t ht => by
    rw [← hg_eq_h₁_on t ht]; exact hg_im_nn_arc_R t ht
  have hh₁_ne : ∀ t ∈ Icc (1 + δ_R) (3:ℝ), h₁ t ≠ 0 := fun t ht => by
    rw [← hg_eq_h₁_on t ht]; exact hg_ne_arc_R t ht
  have hh₁_slit_interior : ∀ t ∈ Ioo (1 + δ_R) (3:ℝ), h₁ t ∈ slitPlane := fun t ⟨ht1, ht3⟩ => by
    rw [← hg_eq_h₁ t (by linarith) ht3]; exact hg_slit_arc_R t ⟨ht1, ht3⟩
  have piece₁ := ftc_log_piece_upper (by linarith : (1 + δ_R) ≤ 3) hh₁_cont hh₁_diff
    hh₁_deriv_cont hh₁_im_nn hh₁_ne hh₁_slit_interior
    heq_1pδ_3 hg1pδ (hg3_2.symm ▸ hg3_1)
  have hg_eq_h₂_on : ∀ t ∈ Icc (3:ℝ) 4, g t = h₂ t := fun t ⟨ht3, ht4⟩ => by
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · exact hg3_2
    · exact hg_eq_h₂ t ht3' ht4
  obtain ⟨hg_im_nn_seg3, hg_ne_seg3, hg_slit_seg3⟩ := g_rho'_seg3_triple H hH
  have hh₂_im_nn : ∀ t ∈ Icc (3:ℝ) 4, 0 ≤ (h₂ t).im := fun t ht => by
    rw [← hg_eq_h₂_on t ht]; exact hg_im_nn_seg3 t ht
  have hh₂_ne : ∀ t ∈ Icc (3:ℝ) 4, h₂ t ≠ 0 := fun t ht => by
    rw [← hg_eq_h₂_on t ht]; exact hg_ne_seg3 t ht
  have hh₂_slit_interior : ∀ t ∈ Ioo (3:ℝ) 4, h₂ t ∈ slitPlane := fun t ⟨ht3, ht4⟩ => by
    rw [← hg_eq_h₂ t ht3 ht4.le]; exact hg_slit_seg3 t ⟨ht3, ht4⟩
  have piece₂ := ftc_log_piece_upper (by norm_num : (3:ℝ) ≤ 4) hh₂_cont hh₂_diff
    hh₂_deriv_cont hh₂_im_nn hh₂_ne hh₂_slit_interior heq_34 hg3_2 (hg4_3.symm ▸ hg4_2)
  have hg_slit_seg4 := g_rho'_seg4_slit H hH
  have hh₃_slit : ∀ t ∈ Icc (4:ℝ) 5, h₃ t ∈ slitPlane := fun t ⟨ht4, ht5⟩ => by
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · rw [← hg4_3]; exact hg_slit_seg4 4 ⟨le_rfl, by linarith⟩
    · rw [← hg_eq_h₃ t ht4']; exact hg_slit_seg4 t ⟨ht4'.le, ht5⟩
  have piece₃ := ftc_log_pieceFM (by norm_num : (4:ℝ) ≤ 5)
    hh₃_cont hh₃_diff hh₃_deriv_cont hh₃_slit heq_45 hg4_3 hg5
  refine ⟨piece₀.1, piece₁.1.trans (piece₂.1.trans piece₃.1), ?_⟩
  rw [(intervalIntegral.integral_add_adjacent_intervals piece₁.1
      (piece₂.1.trans piece₃.1)).symm,
    (intervalIntegral.integral_add_adjacent_intervals piece₂.1 piece₃.1).symm,
    piece₀.2, piece₁.2, piece₂.2, piece₃.2]
  have hg_closed : g 0 = g 5 := fdBoundary_H_sub_closed H ρ'
  rw [hg_closed]; ring

private lemma norm_le_middle_rho_plus_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {ε δ_L δ_R : ℝ} (hε : 0 < ε)
    (hδ_L_pos : 0 < δ_L) (hδ_L_lt_one : δ_L < 1)
    (hδ_R_pos : 0 < δ_R) (hδ_R_lt_one : δ_R < 1)
    (h_norm_L : ‖fdBoundary_H H (1 - δ_L) - ellipticPointRhoPlusOne‖ = ε)
    (h_norm_R : ‖fdBoundary_H H (1 + δ_R) - ellipticPointRhoPlusOne‖ = ε) :
    ∀ t, 1 - δ_L ≤ t → t ≤ 1 + δ_R →
      ¬(‖fdBoundary_H H t - (ellipticPointRhoPlusOne : ℂ)‖ > ε) := by
  intro t ht_lo ht_hi
  push Not
  have hpi_pos := Real.pi_pos
  have hH_gap : 0 < H - Real.sqrt 3 / 2 := by linarith
  rcases le_or_gt t 1 with ht1 | ht1
  · rcases eq_or_lt_of_le ht1 with rfl | ht1'
    · simp only [fdBoundary_H_at_one_eq_rho_plus_one, sub_self, norm_zero]
      exact hε.le
    · rw [g_rho'_norm_seg0 hH ht1',
          ← h_norm_L, g_rho'_norm_seg0_at hH hδ_L_pos]
      exact mul_le_mul_of_nonneg_right (by linarith) hH_gap.le
  · rw [g_rho'_norm_arc_full ht1 (by linarith : t < 3),
        ← h_norm_R, g_rho'_norm_arc hδ_R_pos (by linarith : δ_R < 2)]
    exact mul_le_mul_of_nonneg_left (Real.sin_le_sin_of_le_of_le_pi_div_two
        (by nlinarith) (by nlinarith) (by nlinarith [show t - 1 ≤ δ_R by linarith]))
      (by norm_num)

private lemma rho'_norm_gt_right_of_arc (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {ε δ_R : ℝ} (hε_lt_one : ε < 1) (hε_lt_gap : ε < H - Real.sqrt 3 / 2)
    (hδ_R_pos : 0 < δ_R) (hδ_R_lt_one : δ_R < 1)
    (h_norm_R : ‖fdBoundary_H H (1 + δ_R) - ellipticPointRhoPlusOne‖ = ε) :
    ∀ t ∈ Ioo (1 + δ_R) (5 : ℝ),
      ‖fdBoundary_H H t - (ellipticPointRhoPlusOne : ℂ)‖ > ε := by
  intro t ⟨ht1, ht5⟩
  rcases le_or_gt t 3 with ht3 | ht3
  · rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · calc ε < 1 := hε_lt_one
        _ ≤ _ := g_rho'_norm_ge_one_seg3 (le_refl 3) (by norm_num)
    · rw [g_rho'_norm_arc_full (by linarith : 1 < t) ht3',
          ← h_norm_R, g_rho'_norm_arc hδ_R_pos (by linarith : δ_R < 2)]
      have hpi_pos := Real.pi_pos
      apply mul_lt_mul_of_pos_left _ (by norm_num : (0:ℝ) < 2)
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by nlinarith) (by nlinarith)
        (by nlinarith [show δ_R < t - 1 by linarith])
  · rcases le_or_gt t 4 with ht4 | ht4
    · calc ε < 1 := hε_lt_one
        _ ≤ _ := g_rho'_norm_ge_one_seg3 ht3.le ht4
    · calc ε < H - Real.sqrt 3 / 2 := hε_lt_gap
        _ ≤ _ := g_rho'_norm_ge_seg4 hH ht4.le ht5.le

private lemma arc_angle_lt_epsilon {δ_R ε : ℝ} (hδ_R_pos : 0 < δ_R)
    (hδ_R_lt_one : δ_R < 1)
    (h_norm_R : ‖fdBoundary_H H (1 + δ_R) - (ellipticPointRhoPlusOne : ℂ)‖ = ε) :
    δ_R * Real.pi / 12 < ε :=
  delta_pi_div_twelve_lt_eps hδ_R_pos hδ_R_lt_one.le
    (by linarith [h_norm_R ▸ g_rho'_norm_arc (H := H) hδ_R_pos (by linarith : δ_R < 2)])

private lemma δ_right_lt_one_aux {ε : ℝ}
    (hε_half_neg : (-1 : ℝ) ≤ ε / 2)
    (hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12)) :
    12 / Real.pi * Real.arcsin (ε / 2) < 1 :=
  twelve_div_pi_arcsin_half_lt_one hε_half_neg hε_lt_2sin

/-- Common bookkeeping for `pv_integral_at_rho_plus_one_tendsto`: given `0 < ε < threshold`,
extract the basic ε-bounds, δ-bounds, and the resulting norm equalities at `1 ± δ`. -/
private lemma rho'_pv_setup (H : ℝ) (hH : Real.sqrt 3 / 2 < H) {ε : ℝ}
    (hε_pos : 0 < ε)
    (hε_lt : ε < min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12))) :
    let δ_L : ℝ := ε / (H - Real.sqrt 3 / 2)
    let δ_R : ℝ := 12 / Real.pi * Real.arcsin (ε / 2)
    ε < H - Real.sqrt 3 / 2 ∧ ε < 2 * Real.sin (Real.pi / 12) ∧
    -1 ≤ ε / 2 ∧ ε / 2 ≤ 1 ∧
    0 < δ_L ∧ δ_L < 1 ∧ 0 < δ_R ∧ δ_R < 1 ∧
    δ_R * Real.pi / 12 = Real.arcsin (ε / 2) ∧
    ‖fdBoundary_H H (1 - δ_L) - ellipticPointRhoPlusOne‖ = ε ∧
    ‖fdBoundary_H H (1 + δ_R) - ellipticPointRhoPlusOne‖ = ε := by
  have hH_gap : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hε_lt_gap : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
  have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := lt_of_lt_of_le hε_lt (min_le_right _ _)
  have hε_half_neg : (-1 : ℝ) ≤ ε / 2 := by linarith
  have hε_half_le : ε / 2 ≤ 1 := by linarith [Real.sin_le_one (Real.pi / 12)]
  intro δ_L δ_R
  have hδL_pos : 0 < δ_L := div_pos hε_pos hH_gap
  have hδL_lt_one : δ_L < 1 := by
    show ε / (H - Real.sqrt 3 / 2) < 1; rwa [div_lt_one hH_gap]
  have hδR_pos : 0 < δ_R :=
    mul_pos (div_pos (by norm_num) hpi_pos) (Real.arcsin_pos.mpr (by linarith))
  have hδR_lt_one : δ_R < 1 := δ_right_lt_one_aux hε_half_neg hε_lt_2sin
  have hδR_angle : δ_R * Real.pi / 12 = Real.arcsin (ε / 2) := by
    show 12 / Real.pi * Real.arcsin (ε / 2) * Real.pi / 12 = Real.arcsin (ε / 2); field_simp
  have h_norm_L : ‖fdBoundary_H H (1 - δ_L) - ellipticPointRhoPlusOne‖ = ε := by
    rw [g_rho'_norm_seg0_at hH hδL_pos]; exact div_mul_cancel₀ ε hH_gap.ne'
  have h_norm_R : ‖fdBoundary_H H (1 + δ_R) - ellipticPointRhoPlusOne‖ = ε := by
    rw [g_rho'_norm_arc hδR_pos (by linarith : δ_R < 2), hδR_angle,
        Real.sin_arcsin hε_half_neg hε_half_le]
    linarith
  exact ⟨hε_lt_gap, hε_lt_2sin, hε_half_neg, hε_half_le,
    hδL_pos, hδL_lt_one, hδR_pos, hδR_lt_one, hδR_angle, h_norm_L, h_norm_R⟩

/-- The PV integral of `(γ-ρ')⁻¹ γ'` over `[0,5]` with ε-ball cutoff tends to `-iπ/3`. -/
theorem pv_integral_at_rho_plus_one_tendsto (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    Tendsto (fun ε => ∫ t in (0:ℝ)..5, if ‖fdBoundary_H H t - ellipticPointRhoPlusOne‖ > ε
      then (fdBoundary_H H t - ellipticPointRhoPlusOne)⁻¹ *
           deriv (fun s => fdBoundary_H H s - ellipticPointRhoPlusOne) t
      else 0) (𝓝[>] 0) (𝓝 (-(I * ↑Real.pi / 3))) := by
  have hH_gap : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h2sin_pos := two_sin_pi_div_twelve_pos
  have hderiv_eq : ∀ t : ℝ, deriv (fun s => fdBoundary_H H s - (ellipticPointRhoPlusOne : ℂ)) t =
      deriv (fdBoundary_H H) t := fun t => deriv_sub_const (f := fdBoundary_H H) _
  simp_rw [hderiv_eq]
  set threshold := min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12)) with hthresh_def
  have hthresh_pos : 0 < threshold := lt_min hH_gap h2sin_pos
  set δ_left : ℝ → ℝ := fun ε => ε / (H - Real.sqrt 3 / 2) with hδL_def
  set δ_right : ℝ → ℝ := fun ε => 12 / Real.pi * Real.arcsin (ε / 2) with hδR_def
  set E : ℝ → ℂ := fun ε =>
    Complex.log (fdBoundary_H H (1 - δ_left ε) - ellipticPointRhoPlusOne) -
    Complex.log (fdBoundary_H H (1 + δ_right ε) - ellipticPointRhoPlusOne) with hE_def
  apply ContourIntegral.pv_tendsto_of_crossing_limit_asymmetric
      (γ := fdBoundary_H H) (s := ellipticPointRhoPlusOne) (a := 0) (b := 5) (t₀ := 1)
      (δ_left := δ_left) (δ_right := δ_right) (threshold := threshold) (E := E)
  · norm_num
  · exact hthresh_pos
  · exact fun ε hε_pos _ => div_pos hε_pos hH_gap
  · intro ε hε_pos _
    exact mul_pos (div_pos (by norm_num) hpi_pos) (Real.arcsin_pos.mpr (by linarith))
  · intro ε hε_pos hε_lt
    simp only [hδL_def]
    norm_num
    rw [div_lt_one hH_gap]
    exact lt_of_lt_of_le hε_lt (min_le_left _ _)
  · intro ε hε_pos hε_lt
    have hε_half_neg : (-1 : ℝ) ≤ ε / 2 := by linarith
    have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) :=
      lt_of_lt_of_le hε_lt (min_le_right _ _)
    linarith [δ_right_lt_one_aux hε_half_neg hε_lt_2sin]
  · intro ε hε_pos hε_lt t ht_mem
    simp only [hδL_def] at ht_mem
    have ht_lt_one : t < 1 := by linarith [div_pos hε_pos hH_gap, ht_mem.2]
    rw [g_rho'_norm_seg0 hH ht_lt_one]
    calc ε = ε / (H - Real.sqrt 3 / 2) * (H - Real.sqrt 3 / 2) :=
              (div_mul_cancel₀ ε hH_gap.ne').symm
        _ < (1 - t) * (H - Real.sqrt 3 / 2) :=
              mul_lt_mul_of_pos_right (by linarith [ht_mem.2]) hH_gap
  · intro ε hε_pos hε_lt t ht_mem
    obtain ⟨hε_lt_gap, _, _, _, _, _, hδR_pos, hδR_lt_one, _, _, h_norm_R⟩ :=
      rho'_pv_setup H hH hε_pos hε_lt
    have hε_lt_one : ε < 1 := by
      have hsin_bound : Real.sin (Real.pi / 12) < 1 / 2 :=
        (Real.sin_lt_sin_of_lt_of_le_pi_div_two (by nlinarith [Real.pi_pos])
            (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])).trans_eq
          Real.sin_pi_div_six
      linarith [lt_of_lt_of_le hε_lt (min_le_right _ _)]
    simp only [hδR_def] at ht_mem
    rcases eq_or_lt_of_le ht_mem.2 with rfl | ht_lt5
    · exact hε_lt_gap.trans_le (g_rho'_norm_ge_seg4 hH (by norm_num) le_rfl)
    · exact rho'_norm_gt_right_of_arc H hH hε_lt_one hε_lt_gap hδR_pos hδR_lt_one h_norm_R
        t ⟨ht_mem.1, ht_lt5⟩
  · intro ε hε_pos hε_lt t ht_mem
    obtain ⟨_, _, _, _, hδL_pos, hδL_lt_one, hδR_pos, hδR_lt_one, _, h_norm_L, h_norm_R⟩ :=
      rho'_pv_setup H hH hε_pos hε_lt
    exact not_lt.mp (norm_le_middle_rho_plus_one H hH hε_pos hδL_pos hδL_lt_one
      hδR_pos hδR_lt_one h_norm_L h_norm_R t ht_mem.1 ht_mem.2)
  · intro ε hε_pos hε_lt
    obtain ⟨_, _, _, _, hδL_pos, hδL_lt_one, hδR_pos, hδR_lt_one, _, _, _⟩ :=
      rho'_pv_setup H hH hε_pos hε_lt
    simp only [hE_def, hδL_def, hδR_def]
    simp_rw [inv_mul_deriv_eq_logDeriv_sub H ellipticPointRhoPlusOne]
    exact (ftc_logDeriv_telescope_rho_plus_one H hH hδL_pos hδL_lt_one hδR_pos hδR_lt_one).2.2
  · intro ε hε_pos hε_lt
    obtain ⟨_, _, _, _, hδL_pos, hδL_lt_one, hδR_pos, hδR_lt_one, _, _, _⟩ :=
      rho'_pv_setup H hH hε_pos hε_lt
    rw [inv_mul_deriv_eq_logDeriv_sub H ellipticPointRhoPlusOne]
    exact (ftc_logDeriv_telescope_rho_plus_one H hH hδL_pos hδL_lt_one hδR_pos hδR_lt_one).1
  · intro ε hε_pos hε_lt
    obtain ⟨_, _, _, _, hδL_pos, hδL_lt_one, hδR_pos, hδR_lt_one, _, _, _⟩ :=
      rho'_pv_setup H hH hε_pos hε_lt
    rw [inv_mul_deriv_eq_logDeriv_sub H ellipticPointRhoPlusOne]
    exact (ftc_logDeriv_telescope_rho_plus_one H hH hδL_pos hδL_lt_one hδR_pos hδR_lt_one).2.1
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro r hr
    refine ⟨min threshold r, lt_min hthresh_pos hr, ?_⟩
    intro ε hε_mem hε_dist
    simp only [Set.mem_Ioi] at hε_mem
    rw [Real.dist_eq, sub_zero, abs_of_pos hε_mem] at hε_dist
    have hε_lt : ε < threshold := lt_of_lt_of_le hε_dist (min_le_left _ _)
    obtain ⟨_, _, _, _, hδL_pos, _, hδR_pos, hδR_lt_one, _, h_norm_L, h_norm_R⟩ :=
      rho'_pv_setup H hH hε_mem hε_lt
    simp only [hE_def]
    set zL := fdBoundary_H H (1 - δ_left ε) - (ellipticPointRhoPlusOne : ℂ)
    set zR := fdBoundary_H H (1 + δ_right ε) - (ellipticPointRhoPlusOne : ℂ)
    rw [Complex.dist_eq, ← Complex.re_add_im (Complex.log zL),
      ← Complex.re_add_im (Complex.log zR), Complex.log_re, Complex.log_re,
      Complex.log_im, Complex.log_im, show ‖zL‖ = ε from h_norm_L,
      show ‖zR‖ = ε from h_norm_R, arg_approach_rho'_left hH hδL_pos,
      arg_approach_rho'_right_helper hδR_pos (by linarith : δ_right ε < 2),
      show ↑(Real.log ε) + ↑(Real.pi / 2) * I -
        (↑(Real.log ε) + ↑(5 * Real.pi / 6 + δ_right ε * Real.pi / 12) * I) -
        -(I * ↑Real.pi / 3) = ↑(-(δ_right ε * Real.pi / 12)) * I from by push_cast; ring,
      norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    exact lt_trans (arc_angle_lt_epsilon hδR_pos hδR_lt_one h_norm_R)
      (lt_of_lt_of_le hε_dist (min_le_right _ _))

end
