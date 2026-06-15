/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.FDBoundaryH
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.ArcCalculus

/-!
# Fundamental Domain Boundary – Bounds

Segment selectors, trigonometric helpers, and geometric bounds for the
fundamental domain boundary.

## Main Results

* `fdBoundary_H_im_pos` — positive imaginary part
* `fdBoundary_H_im_ge_sqrt3_div_2` — imaginary part ≥ √3/2
* `fdBoundary_H_re_abs_le_half` — |real part| ≤ 1/2
* `fdBoundary_continuous` — continuity of fixed-height boundary
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

lemma fdBoundary_H_eq_seg1_H {H t : ℝ} (ht : t ≤ 1) :
    fdBoundary_H H t = fdBoundary_seg1_H H t := by
  simp only [fdBoundary_H, ht, ite_true, fdBoundary_seg1_H]

lemma fdBoundary_H_eq_seg2_H {t : ℝ} (H : ℝ)
    (ht1 : 1 < t) (ht2 : t ≤ 2) :
    fdBoundary_H H t = fdBoundary_seg2_H t := by
  simp only [fdBoundary_H, not_le.mpr ht1, ht2, ite_true, ite_false,
    fdBoundary_seg2_H, fdBoundary_seg2]

lemma fdBoundary_H_eq_seg3_H {t : ℝ} (H : ℝ)
    (ht2 : 2 < t) (ht3 : t ≤ 3) :
    fdBoundary_H H t = fdBoundary_seg3_H t := by
  simp only [fdBoundary_H, not_le.mpr (show (1:ℝ) < t by linarith),
    not_le.mpr ht2, ht3, ite_true, ite_false,
    fdBoundary_seg3_H, fdBoundary_seg3]

lemma fdBoundary_H_eq_seg4_H {H t : ℝ}
    (ht3 : 3 < t) (ht4 : t ≤ 4) :
    fdBoundary_H H t = fdBoundary_seg4_H H t := by
  simp only [fdBoundary_H, not_le.mpr (show (1:ℝ) < t by linarith),
    not_le.mpr (show (2:ℝ) < t by linarith), not_le.mpr ht3,
    ht4, ite_true, ite_false, fdBoundary_seg4_H]

lemma fdBoundary_H_eq_seg5_H {H t : ℝ} (ht4 : 4 < t) :
    fdBoundary_H H t = fdBoundary_seg5_H H t := by
  simp only [fdBoundary_H, not_le.mpr (show (1:ℝ) < t by linarith),
    not_le.mpr (show (2:ℝ) < t by linarith), not_le.mpr (show (3:ℝ) < t by linarith),
    not_le.mpr ht4, ite_false, fdBoundary_seg5_H]

private lemma seg2_angle_in_range {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t ≤ 2) :
    Real.pi / 3 ≤ Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3) ∧
    Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3) ≤ 2 * Real.pi / 3 := by
  have hpi := Real.pi_pos
  refine ⟨?_, ?_⟩
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ t - 1) (by linarith : (0:ℝ) ≤ Real.pi / 6)]
  · nlinarith [mul_le_mul_of_nonneg_right (by linarith : t - 1 ≤ 1)
      (by linarith : (0:ℝ) ≤ Real.pi / 6)]

private lemma seg3_angle_in_range {t : ℝ} (ht2 : 2 ≤ t) (ht3 : t ≤ 3) :
    Real.pi / 3 ≤ Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2) ∧
    Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2) ≤ 2 * Real.pi / 3 := by
  have hpi := Real.pi_pos
  have h_nonneg : 0 ≤ (t - 2) * (2 * Real.pi / 3 - Real.pi / 2) := by nlinarith
  refine ⟨by nlinarith, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right (by linarith : t - 2 ≤ 1)
    (by linarith : (0:ℝ) ≤ Real.pi / 6)]

private lemma sin_pos_of_angle_in_range {θ : ℝ} (h1 : Real.pi / 3 ≤ θ)
    (h2 : θ ≤ 2 * Real.pi / 3) : 0 < Real.sin θ :=
  ArcCalculus.sin_pos_of_mem_Ioo_zero_pi ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

private lemma sin_ge_sqrt3_div_2_of_angle_in_range {θ : ℝ} (h1 : Real.pi / 3 ≤ θ)
    (h2 : θ ≤ 2 * Real.pi / 3) : Real.sqrt 3 / 2 ≤ Real.sin θ := by
  have hpi := Real.pi_pos
  rw [← Real.sin_pi_div_three]
  by_cases h : θ ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h h1
  · push Not at h
    rw [← Real.sin_pi_sub θ]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

private lemma abs_cos_le_half_of_angle_in_range {θ : ℝ} (h1 : Real.pi / 3 ≤ θ)
    (h2 : θ ≤ 2 * Real.pi / 3) : |Real.cos θ| ≤ 1 / 2 :=
  ArcCalculus.abs_cos_le_half_of_mem_Icc ⟨h1, h2⟩

private lemma seg1_H_im {H t : ℝ} :
    (fdBoundary_seg1_H H t).im = H - t * (H - Real.sqrt 3 / 2) := by
  simp [fdBoundary_seg1_H]

private lemma seg4_H_im {H t : ℝ} :
    (fdBoundary_seg4_H H t).im =
      Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2) := by
  simp [fdBoundary_seg4_H]

private lemma seg5_H_im {H t : ℝ} : (fdBoundary_seg5_H H t).im = H := by
  simp [fdBoundary_seg5_H]

private lemma seg2_as_trig (t : ℝ) :
    fdBoundary_seg2 t = ↑(Real.cos (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3))) +
      ↑(Real.sin (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3))) * I := by
  rw [fdBoundary_seg2, show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3) : ℂ) =
    ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) by push_cast; ring,
    exp_mul_I, ← ofReal_cos, ← ofReal_sin]

private lemma seg3_as_trig (t : ℝ) :
    fdBoundary_seg3 t = ↑(Real.cos (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2))) +
      ↑(Real.sin (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2))) * I := by
  rw [fdBoundary_seg3, show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2) : ℂ) =
    ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) by push_cast; ring,
    exp_mul_I, ← ofReal_cos, ← ofReal_sin]

private lemma seg2_im {t : ℝ} :
    (fdBoundary_seg2 t).im = Real.sin (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) := by
  rw [seg2_as_trig, add_im, ofReal_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  ring

private lemma seg3_im {t : ℝ} :
    (fdBoundary_seg3 t).im =
      Real.sin (Real.pi / 2 +
        (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) := by
  rw [seg3_as_trig, add_im, ofReal_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  ring

private lemma seg2_re {t : ℝ} :
    (fdBoundary_seg2 t).re = Real.cos (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) := by
  rw [seg2_as_trig, add_re, ofReal_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
  ring

private lemma seg3_re {t : ℝ} :
    (fdBoundary_seg3 t).re =
      Real.cos (Real.pi / 2 +
        (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) := by
  rw [seg3_as_trig, add_re, ofReal_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
  ring

lemma fdBoundary_H_im_pos (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    ∀ t ∈ Icc (0 : ℝ) 5, 0 < (fdBoundary_H H t).im := by
  intro t ⟨ht0, ht5⟩
  have hsqrt : 0 < Real.sqrt 3 / 2 := by positivity
  by_cases h1 : t ≤ 1
  · rw [fdBoundary_H_eq_seg1_H h1, seg1_H_im]; nlinarith
  push Not at h1
  by_cases h2 : t ≤ 2
  · rw [fdBoundary_H_eq_seg2_H H h1 h2, fdBoundary_seg2_H, seg2_im]
    obtain ⟨ha, hb⟩ := seg2_angle_in_range h1.le h2
    exact sin_pos_of_angle_in_range ha hb
  push Not at h2
  by_cases h3 : t ≤ 3
  · rw [fdBoundary_H_eq_seg3_H H h2 h3, fdBoundary_seg3_H, seg3_im]
    obtain ⟨ha, hb⟩ := seg3_angle_in_range h2.le h3
    exact sin_pos_of_angle_in_range ha hb
  push Not at h3
  by_cases h4 : t ≤ 4
  · rw [fdBoundary_H_eq_seg4_H h3 h4, seg4_H_im]; nlinarith
  push Not at h4
  rw [fdBoundary_H_eq_seg5_H h4, seg5_H_im]
  linarith

lemma fdBoundary_H_im_ge_sqrt3_div_2 (H : ℝ) (hH : Real.sqrt 3 / 2 ≤ H) :
    ∀ t ∈ Icc (0 : ℝ) 5, Real.sqrt 3 / 2 ≤ (fdBoundary_H H t).im := by
  intro t ⟨ht0, ht5⟩
  by_cases h1 : t ≤ 1
  · rw [fdBoundary_H_eq_seg1_H h1, seg1_H_im]; nlinarith
  push Not at h1
  by_cases h2 : t ≤ 2
  · rw [fdBoundary_H_eq_seg2_H H h1 h2, fdBoundary_seg2_H, seg2_im]
    obtain ⟨ha, hb⟩ := seg2_angle_in_range h1.le h2
    exact sin_ge_sqrt3_div_2_of_angle_in_range ha hb
  push Not at h2
  by_cases h3 : t ≤ 3
  · rw [fdBoundary_H_eq_seg3_H H h2 h3, fdBoundary_seg3_H, seg3_im]
    obtain ⟨ha, hb⟩ := seg3_angle_in_range h2.le h3
    exact sin_ge_sqrt3_div_2_of_angle_in_range ha hb
  push Not at h3
  by_cases h4 : t ≤ 4
  · rw [fdBoundary_H_eq_seg4_H h3 h4, seg4_H_im]; nlinarith
  push Not at h4
  rw [fdBoundary_H_eq_seg5_H h4, seg5_H_im]
  exact hH

private lemma seg1_H_re {H t : ℝ} : (fdBoundary_seg1_H H t).re = 1 / 2 := by
  simp [fdBoundary_seg1_H]

private lemma seg4_H_re {H t : ℝ} : (fdBoundary_seg4_H H t).re = -1 / 2 := by
  simp [fdBoundary_seg4_H]

private lemma seg5_H_re {H t : ℝ} : (fdBoundary_seg5_H H t).re = t - 9 / 2 := by
  simp [fdBoundary_seg5_H]

lemma fdBoundary_H_re_abs_le_half (H : ℝ) :
    ∀ t ∈ Icc (0 : ℝ) 5, |Complex.re (fdBoundary_H H t)| ≤ 1 / 2 := by
  intro t ⟨ht0, ht5⟩
  by_cases h1 : t ≤ 1
  · rw [fdBoundary_H_eq_seg1_H h1, seg1_H_re]; norm_num
  push Not at h1
  by_cases h2 : t ≤ 2
  · rw [fdBoundary_H_eq_seg2_H H h1 h2, fdBoundary_seg2_H, seg2_re]
    obtain ⟨ha, hb⟩ := seg2_angle_in_range h1.le h2
    exact abs_cos_le_half_of_angle_in_range ha hb
  push Not at h2
  by_cases h3 : t ≤ 3
  · rw [fdBoundary_H_eq_seg3_H H h2 h3, fdBoundary_seg3_H, seg3_re]
    obtain ⟨ha, hb⟩ := seg3_angle_in_range h2.le h3
    exact abs_cos_le_half_of_angle_in_range ha hb
  push Not at h3
  by_cases h4 : t ≤ 4
  · rw [fdBoundary_H_eq_seg4_H h3 h4, seg4_H_re]; norm_num
  push Not at h4
  rw [fdBoundary_H_eq_seg5_H h4, seg5_H_re, abs_le]
  constructor <;> linarith

lemma fdBoundary_H_im_le_H {H : ℝ} (hH : 1 ≤ H) :
    ∀ t ∈ Icc (0 : ℝ) 5, (fdBoundary_H H t).im ≤ H := by
  intro t ⟨ht0, ht5⟩
  have hH_sqrt3 : Real.sqrt 3 / 2 < H := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  by_cases h1 : t ≤ 1
  · rw [fdBoundary_H_eq_seg1_H h1, seg1_H_im]; nlinarith
  push Not at h1
  by_cases h2 : t ≤ 2
  · rw [fdBoundary_H_eq_seg2_H H h1 h2, fdBoundary_seg2_H, seg2_im]
    exact (Real.sin_le_one _).trans hH
  push Not at h2
  by_cases h3 : t ≤ 3
  · rw [fdBoundary_H_eq_seg3_H H h2 h3, fdBoundary_seg3_H, seg3_im]
    exact (Real.sin_le_one _).trans hH
  push Not at h3
  by_cases h4 : t ≤ 4
  · rw [fdBoundary_H_eq_seg4_H h3 h4, seg4_H_im]; nlinarith
  push Not at h4
  rw [fdBoundary_H_eq_seg5_H h4, seg5_H_im]

end
