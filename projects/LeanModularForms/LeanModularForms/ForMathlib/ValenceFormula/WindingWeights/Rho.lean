/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ContourIntegral.CrossingLimit
import LeanModularForms.ForMathlib.ValenceFormula.WindingWeights.Common

/-!
# Winding Number Weight at ρ

PV integral computation and generalized winding number of `fdBoundary_H`
around the elliptic point ρ = e^{2πi/3}.

## Main Results

* `pv_integral_at_rho_tendsto` — PV integral converges to -iπ/3
* `gWN_fdBoundary_H_at_rho` — gWN = -1/6 at ρ
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- On seg 0: `γ(t) - ρ` has `re = 1`. -/
theorem fdBoundary_H_sub_rho_seg0_re (H : ℝ) {t : ℝ} (ht : t ≤ 1) :
    (fdBoundary_H H t - ellipticPointRho).re = 1 := by
  rw [fdBoundary_H_seg1 H ht]; simp [ellipticPointRho, ellipticPointRho']; ring

/-- On seg 0: `γ(t) - ρ ∈ slitPlane` since `re = 1 > 0`. -/
theorem fdBoundary_H_sub_rho_seg0_slitPlane (H : ℝ) {t : ℝ} (ht : t ≤ 1) :
    fdBoundary_H H t - ellipticPointRho ∈ slitPlane :=
  Complex.mem_slitPlane_iff.mpr <| Or.inl <| by
    rw [fdBoundary_H_sub_rho_seg0_re H ht]; norm_num

/-- Real part of the arc displacement `↑(cos θ) + ↑(sin θ)·I - ρ` is `cos θ + 1/2`. -/
private lemma re_arc_sub_rho (θ : ℝ) :
    (↑(Real.cos θ) + ↑(Real.sin θ) * I - (-1 / 2 + ↑(Real.sqrt 3) / 2 * I) : ℂ).re =
      Real.cos θ + 1 / 2 := by
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.neg_re, Complex.one_re,
    Complex.div_ofNat_re, Complex.div_ofNat_im, zero_div]; ring

/-- On seg 1: `γ(t) - ρ` has `re = cos(θ(t)) + 1/2` where `θ ∈ [π/3, π/2]`,
    so `cos(θ) ∈ [0, 1/2]` and `re ∈ [1/2, 1] > 0`. -/
theorem fdBoundary_H_sub_rho_seg1_re (H : ℝ) {t : ℝ} (ht1 : 1 < t) (ht2 : t ≤ 2) :
    (fdBoundary_H H t - ellipticPointRho).re > 0 := by
  rw [fdBoundary_H_seg2 H (not_le.mpr ht1) ht2]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  set θ : ℝ := Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3) with hθ_def
  rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
    (↑θ : ℂ) * I by simp only [hθ_def]; push_cast; ring, Complex.exp_ofReal_mul_I, re_arc_sub_rho]
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by simp only [hθ_def]; nlinarith [Real.pi_pos],
      by simp only [hθ_def]; nlinarith [Real.pi_pos]⟩
  linarith

/-- On seg 2 (t ∈ (2, 3)): `γ(t) - ρ` has `re = cos(θ(t)) + 1/2 > 0` since
    `θ ∈ (π/2, 2π/3)` gives `cos ∈ (-1/2, 0)` hence `re ∈ (0, 1/2)`. -/
theorem fdBoundary_H_sub_rho_seg2_re (H : ℝ) {t : ℝ} (ht2 : 2 < t) (ht3 : t < 3) :
    (fdBoundary_H H t - ellipticPointRho).re > 0 := by
  rw [fdBoundary_H_seg3 H (by linarith) (by linarith) (le_of_lt ht3)]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  set θ : ℝ := Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2) with hθ_def
  rw [show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
    (↑θ : ℂ) * I by simp only [hθ_def]; push_cast; ring, Complex.exp_ofReal_mul_I, re_arc_sub_rho]
  have hcos_gt : Real.cos θ > -1 / 2 := by
    have := cos_two_pi_div_three
    rw [show (-1 : ℝ) / 2 = Real.cos (2 * Real.pi / 3) by linarith]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by simp only [hθ_def]; nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos]) (by simp only [hθ_def]; nlinarith [Real.pi_pos])
  linarith

/-- On seg 3 (t ∈ (3, 4]): `γ(t) - ρ = (y(t) - √3/2)I` with `y > √3/2`, so `im > 0`. -/
theorem fdBoundary_H_sub_rho_seg3_slitPlane (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) :
    fdBoundary_H H t - ellipticPointRho ∈ slitPlane := by
  have h_diff : fdBoundary_H H t - (ellipticPointRho : ℂ) =
      ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I := by
    rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) ht4]
    simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]; push_cast; ring
  rw [h_diff, Complex.mem_slitPlane_iff]; right
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  nlinarith

/-- On seg 4: `γ(t) - ρ` has `im = H - √3/2 > 0` for `H > √3/2`. -/
theorem fdBoundary_H_sub_rho_seg4_slitPlane (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht4 : 4 < t) (_ht5 : t ≤ 5) :
    fdBoundary_H H t - ellipticPointRho ∈ slitPlane := by
  have h_diff : fdBoundary_H H t - (ellipticPointRho : ℂ) =
      ↑(t - 4) + ↑(H - Real.sqrt 3 / 2) * I := by
    rw [fdBoundary_H_seg5 H (by linarith) (by linarith) (by linarith) (by linarith)]
    simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]; push_cast; ring
  rw [h_diff, Complex.mem_slitPlane_iff]; right
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re]
  linarith

/-- Combined: `γ(t) - ρ ∈ slitPlane` for all `t ∈ [0, 5]` with `t ≠ 3`. -/
theorem fdBoundary_H_sub_rho_slitPlane (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 5) (hne : t ≠ 3) :
    fdBoundary_H H t - ellipticPointRho ∈ slitPlane := by
  rcases le_or_gt t 1 with h1 | h1
  · exact fdBoundary_H_sub_rho_seg0_slitPlane H h1
  · rcases le_or_gt t 2 with h2 | h2
    · exact Complex.mem_slitPlane_iff.mpr (Or.inl (fdBoundary_H_sub_rho_seg1_re H h1 h2))
    · rcases lt_or_ge t 3 with h3 | h3
      · exact Complex.mem_slitPlane_iff.mpr (Or.inl (fdBoundary_H_sub_rho_seg2_re H h2 h3))
      · rcases eq_or_lt_of_le h3 with h3eq | h3lt
        · exact absurd h3eq.symm hne
        · rcases le_or_gt t 4 with h4 | h4
          · exact fdBoundary_H_sub_rho_seg3_slitPlane H hH h3lt h4
          · exact fdBoundary_H_sub_rho_seg4_slitPlane H hH h4 ht.2

private lemma rho_re_identity (δ : ℝ) :
    -Real.sin (Real.pi / 6 - δ * Real.pi / 6) + 1 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (Real.pi / 6 - δ * Real.pi / 12) := by
  have h := Real.sin_sub_sin (Real.pi / 6) (Real.pi / 6 - δ * Real.pi / 6)
  rw [show (Real.pi / 6 - (Real.pi / 6 - δ * Real.pi / 6)) / 2 = δ * Real.pi / 12 by ring,
      show (Real.pi / 6 + (Real.pi / 6 - δ * Real.pi / 6)) / 2 = Real.pi / 6 - δ * Real.pi / 12
      by ring] at h
  linarith [Real.sin_pi_div_six]

private lemma rho_im_identity (δ : ℝ) :
    Real.cos (Real.pi / 6 - δ * Real.pi / 6) - Real.sqrt 3 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.sin (Real.pi / 6 - δ * Real.pi / 12) := by
  have h := Real.cos_sub_cos (Real.pi / 6 - δ * Real.pi / 6) (Real.pi / 6)
  rw [show (Real.pi / 6 - δ * Real.pi / 6 + Real.pi / 6) / 2 = Real.pi / 6 - δ * Real.pi / 12
      by ring,
      show (Real.pi / 6 - δ * Real.pi / 6 - Real.pi / 6) / 2 = -(δ * Real.pi / 12) by ring,
      Real.sin_neg] at h
  nlinarith [Real.cos_pi_div_six,
    mul_comm (Real.sin (Real.pi / 6 - δ * Real.pi / 12)) (Real.sin (δ * Real.pi / 12))]

private lemma rho_cos_shift (δ : ℝ) :
    Real.cos (2 * Real.pi / 3 - δ * Real.pi / 6) =
      -Real.sin (Real.pi / 6 - δ * Real.pi / 6) := by
  rw [show 2 * Real.pi / 3 - δ * Real.pi / 6 =
      Real.pi / 2 + (Real.pi / 6 - δ * Real.pi / 6) by ring,
    Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

private lemma rho_sin_shift (δ : ℝ) :
    Real.sin (2 * Real.pi / 3 - δ * Real.pi / 6) =
      Real.cos (Real.pi / 6 - δ * Real.pi / 6) := by
  rw [show 2 * Real.pi / 3 - δ * Real.pi / 6 =
      Real.pi / 2 + (Real.pi / 6 - δ * Real.pi / 6) by ring,
    Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

private lemma rho_arc_factor (δ : ℝ) :
    (↑(Real.cos (2 * Real.pi / 3 - δ * Real.pi / 6)) +
        ↑(Real.sin (2 * Real.pi / 3 - δ * Real.pi / 6)) * I -
        (-1 / 2 + ↑(Real.sqrt 3) / 2 * I) : ℂ) =
      ↑(2 * Real.sin (δ * Real.pi / 12)) * (↑(Real.cos (Real.pi / 6 - δ * Real.pi / 12)) +
         ↑(Real.sin (Real.pi / 6 - δ * Real.pi / 12)) * I) := by
  rw [rho_cos_shift, rho_sin_shift]
  apply Complex.ext
  · simp only [add_re, sub_re, mul_re, neg_re, ofReal_re, ofReal_im, I_re, I_im,
      one_re, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, sub_zero, add_zero,
      mul_one, zero_div]
    linarith [rho_re_identity δ]
  · simp only [add_im, sub_im, mul_im, neg_im, ofReal_re, ofReal_im, I_re, I_im,
      one_im, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, add_zero,
      mul_one, zero_div]
    linarith [rho_im_identity δ]

private lemma arg_approach_rho_left_helper (hδ : 0 < δ) (hδ_small : δ < 1) :
    (fdBoundary_H H (3 - δ) - ellipticPointRho).arg = Real.pi / 6 - δ * Real.pi / 12 := by
  rw [fdBoundary_H_seg3 H (by linarith) (by linarith) (by linarith : 3 - δ ≤ 3)]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  rw [show (↑(Real.pi : ℝ) / 2 + (↑(3 - δ : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      (↑(2 * Real.pi / 3 - δ * Real.pi / 6) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I, rho_arc_factor δ, Complex.ofReal_cos, Complex.ofReal_sin]
  exact Complex.arg_mul_cos_add_sin_mul_I (mul_pos (by norm_num : (0:ℝ) < 2)
      (sin_delta_pi_div_twelve_pos hδ (by linarith)))
    ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩

private lemma g_seg3_value (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    fdBoundary_H H (3 + δ) - ellipticPointRho = ↑(δ * (H - Real.sqrt 3 / 2)) * I := by
  rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) (by linarith : 3 + δ ≤ 4)]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]; push_cast; ring

/-- The `arg` of the approach direction from the right (seg 3 side) at `ρ`.
    `γ(3+δ) - ρ = δ(H-√3/2)I`, so `arg = π/2` (exact, not just limit). -/
theorem arg_approach_rho_right (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1) :
    (fdBoundary_H H (3 + δ) - ellipticPointRho).arg = Real.pi / 2 := by
  rw [g_seg3_value H hδ hδ4]; exact arg_ofReal_mul_I (by nlinarith)

private lemma g_norm_seg3 (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ‖fdBoundary_H H (3 + δ) - ellipticPointRho‖ = δ * (H - Real.sqrt 3 / 2) := by
  rw [g_seg3_value H hδ hδ1, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by nlinarith : 0 ≤ δ * (H - Real.sqrt 3 / 2))]

private lemma g_norm_seg2 {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ‖fdBoundary_H H (3 - δ) - ellipticPointRho‖ = 2 * Real.sin (δ * Real.pi / 12) := by
  rw [fdBoundary_H_seg3 H (by linarith) (by linarith) (by linarith : 3 - δ ≤ 3)]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  rw [show (↑Real.pi / 2 + (↑(3 - δ : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      (↑(2 * Real.pi / 3 - δ * Real.pi / 6) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I, rho_arc_factor δ, ← Complex.exp_ofReal_mul_I]
  exact norm_two_sin_mul_exp hδ (by linarith)

private lemma g_norm_arc {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    ‖fdBoundary_H H t - ellipticPointRho‖ = 2 * Real.sin ((3 - t) * Real.pi / 12) := by
  rw [fdBoundary_H_eq_arc ht1 ht3]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  set δ := 3 - t with hδ_def
  have hδ : 0 < δ := by linarith
  rw [show Real.pi * (1 + t) / 6 = 2 * Real.pi / 3 - δ * Real.pi / 6 by
      simp only [hδ_def]; ring, Complex.exp_ofReal_mul_I, rho_arc_factor δ, ← Complex.exp_ofReal_mul_I]
  exact norm_two_sin_mul_exp hδ (by linarith)

private lemma g_norm_ge_one_seg0 {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 ≤ ‖fdBoundary_H H t - ellipticPointRho‖ := by
  calc 1 = |1| := (abs_of_pos one_pos).symm
    _ = |(fdBoundary_H H t - ellipticPointRho).re| := by rw [fdBoundary_H_sub_rho_seg0_re H ht1]
    _ ≤ ‖fdBoundary_H H t - ellipticPointRho‖ := Complex.abs_re_le_norm _

private lemma g_norm_ge_seg4 (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    H - Real.sqrt 3 / 2 ≤ ‖fdBoundary_H H t - ellipticPointRho‖ := by
  have him : (fdBoundary_H H t - (ellipticPointRho : ℂ)).im = H - Real.sqrt 3 / 2 := by
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · rw [show fdBoundary_H H 4 - (ellipticPointRho : ℂ) = ↑(H - Real.sqrt 3 / 2) * I by
          rw [fdBoundary_H_at_four H]
          simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]; push_cast; ring,
        mul_comm, Complex.I_mul_im, Complex.ofReal_re]
    · rw [show fdBoundary_H H t - (ellipticPointRho : ℂ) =
            ↑(t - 4) + ↑(H - Real.sqrt 3 / 2) * I by
          rw [fdBoundary_H_seg5 H (by linarith) (by linarith) (by linarith) (by linarith)]
          simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]; push_cast; ring,
        Complex.add_im, Complex.ofReal_im, zero_add, mul_comm, Complex.I_mul_im, Complex.ofReal_re]
  calc H - Real.sqrt 3 / 2 = |(H - Real.sqrt 3 / 2 : ℝ)| := (abs_of_pos (by linarith)).symm
    _ = |(fdBoundary_H H t - (ellipticPointRho : ℂ)).im| := by rw [him]
    _ ≤ ‖fdBoundary_H H t - (ellipticPointRho : ℂ)‖ := Complex.abs_im_le_norm _

private lemma ftc_logDeriv_telescope_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {δ_L δ_R : ℝ} (hδ_L : 0 < δ_L) (hδ_L1 : δ_L < 1) (hδ_R : 0 < δ_R) (hδ_R1 : δ_R < 1) :
    let g := fun t ↦ fdBoundary_H H t - (ellipticPointRho : ℂ)
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume 0 (3 - δ_L) ∧
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume (3 + δ_R) 5 ∧
    ((∫ t in (0:ℝ)..(3 - δ_L), deriv g t / g t) + (∫ t in (3 + δ_R)..(5:ℝ), deriv g t / g t) =
    Complex.log (g (3 - δ_L)) - Complex.log (g (3 + δ_R))) := by
  intro g
  set ρ : ℂ := ellipticPointRho with hρ_def
  set h₀ : ℝ → ℂ :=
    fun t ↦ 1 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2) - ↑(Real.sqrt 3) / 2) * I
  set h₁ : ℝ → ℂ := fun t ↦ exp (↑(Real.pi * (1 + t) / 6) * I) - ρ
  set h₂ : ℝ → ℂ := fun t ↦ ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I
  set h₃ : ℝ → ℂ := fun t ↦ ↑(t - 4) + ↑(H - Real.sqrt 3 / 2) * I
  have hg_eq_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := fun t ht ↦ by
    show fdBoundary_H H t - ρ = h₀ t
    rw [fdBoundary_H_seg1 H ht]
    simp only [hρ_def, ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk, h₀]; ring
  have hg_eq_h₁ : ∀ t, 1 < t → t < 3 → g t = h₁ t := fun t ht1 ht3 ↦
    show fdBoundary_H H t - ρ = h₁ t by rw [fdBoundary_H_eq_arc ht1 ht3]
  have hg_eq_h₂ : ∀ t, 3 < t → t ≤ 4 → g t = h₂ t := fun t ht3 ht4 ↦ by
    show fdBoundary_H H t - ρ = h₂ t
    rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) ht4]
    simp only [hρ_def, ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk, h₂]
    push_cast; ring
  have hg_eq_h₃ : ∀ t, 4 < t → g t = h₃ t := fun t ht4 ↦ by
    show fdBoundary_H H t - ρ = h₃ t
    rw [fdBoundary_H_seg5 H (by linarith) (by linarith) (by linarith) (by linarith)]
    simp only [hρ_def, ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk, h₃]
    push_cast; ring
  have hg0 : g 0 = h₀ 0 := hg_eq_h₀ 0 (by norm_num)
  have hg1_0 : g 1 = h₀ 1 := hg_eq_h₀ 1 le_rfl
  have hg1_1 : g 1 = h₁ 1 := by
    change fdBoundary_H H 1 - ρ = h₁ 1
    rw [fdBoundary_H_at_one_eq_rho_plus_one]
    simp only [h₁, hρ_def, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
      ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 by ring, Complex.exp_ofReal_mul_I,
        Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  have hg3mδ : g (3 - δ_L) = h₁ (3 - δ_L) := hg_eq_h₁ _ (by linarith) (by linarith)
  have hg3pδ : g (3 + δ_R) = h₂ (3 + δ_R) := hg_eq_h₂ _ (by linarith) (by linarith)
  have hg4_2 : g 4 = h₂ 4 := hg_eq_h₂ 4 (by linarith) le_rfl
  have hg4_3 : g 4 = h₃ 4 := by
    change fdBoundary_H H 4 - ρ = h₃ 4
    rw [fdBoundary_H_at_four H]
    simp only [hρ_def, ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk, h₃]
    push_cast; ring
  have hg5 : g 5 = h₃ 5 := hg_eq_h₃ 5 (by norm_num)
  have hd_h₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := fun t ↦ by
    set c : ℂ := ↑(H - Real.sqrt 3 / 2) * I
    have h_eq : h₀ = fun (s : ℝ) ↦ (1 + c) + (-c) * ↑s := by
      ext s; simp only [h₀, c]; push_cast; ring
    rw [h_eq, show -(↑(H - Real.sqrt 3 / 2) : ℂ) * I = -c by simp [c]; ring]
    exact ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-c)).const_add (1 + c)
      |>.congr_deriv (by simp [mul_one])
  have hd_h₁ : ∀ t : ℝ, HasDerivAt h₁
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t :=
    hasDerivAt_arc_sub_const ρ
  have hd_h₂ : ∀ t : ℝ, HasDerivAt h₂ ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t :=
    hasDerivAt_aff_imI_pos (H - Real.sqrt 3 / 2) 3
  have hd_h₃ : ∀ t : ℝ, HasDerivAt h₃ 1 t :=
    hasDerivAt_seg5_line 4 (↑(H - Real.sqrt 3 / 2) * I)
  have heq_01 : ∀ t ∈ Ioo (0:ℝ) 1, g t = h₀ t ∧ deriv g t = deriv h₀ t :=
    heq_deriv_of_eq_on_nhds (U := Iio (1:ℝ)) (fun _ ht ↦ Iio_mem_nhds ht.2)
      (fun s hs ↦ hg_eq_h₀ s hs.le)
  have heq_1_3mδ : ∀ t ∈ Ioo (1:ℝ) (3 - δ_L),
      g t = h₁ t ∧ deriv g t = deriv h₁ t :=
    heq_deriv_of_eq_on_nhds (U := Ioo (1:ℝ) 3)
      (fun _ ht ↦ Ioo_mem_nhds ht.1 (by linarith [ht.2]))
      (fun s hs ↦ hg_eq_h₁ s hs.1 hs.2)
  have heq_3pδ_4 : ∀ t ∈ Ioo (3 + δ_R) (4:ℝ),
      g t = h₂ t ∧ deriv g t = deriv h₂ t :=
    heq_deriv_of_eq_on_nhds (U := Ioo (3:ℝ) 4)
      (fun _ ht ↦ Ioo_mem_nhds (by linarith [ht.1]) ht.2)
      (fun s hs ↦ hg_eq_h₂ s hs.1 hs.2.le)
  have heq_45 : ∀ t ∈ Ioo (4:ℝ) 5, g t = h₃ t ∧ deriv g t = deriv h₃ t :=
    heq_deriv_of_eq_on_nhds (U := Ioi (4:ℝ))
      (fun _ ht ↦ Ioi_mem_nhds ht.1) (fun s hs ↦ hg_eq_h₃ s hs)
  have hh₀_cont : ContinuousOn h₀ (Icc 0 1) :=
    fun t _ ↦ (hd_h₀ t).continuousAt.continuousWithinAt
  have hh₁_cont : ContinuousOn h₁ (Icc 1 (3 - δ_L)) :=
    fun t _ ↦ (hd_h₁ t).continuousAt.continuousWithinAt
  have hh₂_cont : ContinuousOn h₂ (Icc (3 + δ_R) 4) :=
    fun t _ ↦ (hd_h₂ t).continuousAt.continuousWithinAt
  have hh₃_cont : ContinuousOn h₃ (Icc 4 5) :=
    fun t _ ↦ (hd_h₃ t).continuousAt.continuousWithinAt
  have hh₀_diff : ∀ t ∈ Ioo (0:ℝ) 1, DifferentiableAt ℝ h₀ t :=
    fun t _ ↦ (hd_h₀ t).differentiableAt
  have hh₁_diff : ∀ t ∈ Ioo (1:ℝ) (3 - δ_L), DifferentiableAt ℝ h₁ t :=
    fun t _ ↦ (hd_h₁ t).differentiableAt
  have hh₂_diff : ∀ t ∈ Ioo (3 + δ_R) (4:ℝ), DifferentiableAt ℝ h₂ t :=
    fun t _ ↦ (hd_h₂ t).differentiableAt
  have hh₃_diff : ∀ t ∈ Ioo (4:ℝ) 5, DifferentiableAt ℝ h₃ t :=
    fun t _ ↦ (hd_h₃ t).differentiableAt
  have hh₀_deriv_cont : ContinuousOn (deriv h₀) (Icc 0 1) :=
    continuousOn_deriv_of_const _ hd_h₀ 0 1
  have hh₁_deriv_cont : ContinuousOn (deriv h₁) (Icc 1 (3 - δ_L)) :=
    continuousOn_deriv_of_arc_form hd_h₁ 1 (3 - δ_L)
  have hh₂_deriv_cont : ContinuousOn (deriv h₂) (Icc (3 + δ_R) 4) :=
    continuousOn_deriv_of_const _ hd_h₂ (3 + δ_R) 4
  have hh₃_deriv_cont : ContinuousOn (deriv h₃) (Icc 4 5) :=
    continuousOn_deriv_of_const _ hd_h₃ 4 5
  have hh₀_slit : ∀ t ∈ Icc (0:ℝ) 1, h₀ t ∈ slitPlane := fun t ht ↦ by
    rw [← hg_eq_h₀ t ht.2]; exact fdBoundary_H_sub_rho_seg0_slitPlane H ht.2
  have hh₁_slit : ∀ t ∈ Icc (1:ℝ) (3 - δ_L), h₁ t ∈ slitPlane := fun t ⟨ht1, ht3⟩ ↦ by
    rcases eq_or_lt_of_le ht1 with rfl | ht1'
    · rw [← hg1_1]
      exact fdBoundary_H_sub_rho_slitPlane H hH ⟨by norm_num, by linarith⟩ (by linarith)
    · rw [← hg_eq_h₁ t ht1' (by linarith)]
      exact fdBoundary_H_sub_rho_slitPlane H hH ⟨by linarith, by linarith⟩ (by linarith)
  have hh₂_slit : ∀ t ∈ Icc (3 + δ_R) (4:ℝ), h₂ t ∈ slitPlane := fun t ⟨ht3, ht4⟩ ↦ by
    rw [← hg_eq_h₂ t (by linarith) ht4]
    exact fdBoundary_H_sub_rho_slitPlane H hH ⟨by linarith, by linarith⟩ (by linarith)
  have hh₃_slit : ∀ t ∈ Icc (4:ℝ) 5, h₃ t ∈ slitPlane := fun t ⟨ht4, ht5⟩ ↦ by
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · rw [← hg4_3]
      exact fdBoundary_H_sub_rho_slitPlane H hH ⟨by norm_num, by norm_num⟩ (by norm_num)
    · rw [← hg_eq_h₃ t ht4']
      exact fdBoundary_H_sub_rho_slitPlane H hH ⟨by linarith, ht5⟩ (by linarith)
  have piece₀ := ftc_log_pieceFM (by norm_num : (0:ℝ) ≤ 1)
    hh₀_cont hh₀_diff hh₀_deriv_cont hh₀_slit heq_01 hg0 hg1_0
  have piece₁ := ftc_log_pieceFM (by linarith : (1:ℝ) ≤ 3 - δ_L)
    hh₁_cont hh₁_diff hh₁_deriv_cont
    hh₁_slit heq_1_3mδ (hg1_0.symm ▸ hg1_1) hg3mδ
  have piece₂ := ftc_log_pieceFM (by linarith : (3 + δ_R) ≤ 4)
    hh₂_cont hh₂_diff hh₂_deriv_cont
    hh₂_slit heq_3pδ_4 hg3pδ (hg4_3.symm ▸ hg4_2)
  have piece₃ := ftc_log_pieceFM (by norm_num : (4:ℝ) ≤ 5)
    hh₃_cont hh₃_diff hh₃_deriv_cont hh₃_slit heq_45 hg4_3 hg5
  refine ⟨piece₀.1.trans piece₁.1, piece₂.1.trans piece₃.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals piece₀.1 piece₁.1,
      ← intervalIntegral.integral_add_adjacent_intervals piece₂.1 piece₃.1,
      piece₀.2, piece₁.2, piece₂.2, piece₃.2]
  have hg_closed : g 0 = g 5 := fdBoundary_H_sub_closed H ρ
  rw [hg_closed]
  ring

private lemma norm_le_middle_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {ε δ_L δ_R : ℝ} (hε : 0 < ε) (hδ_L_pos : 0 < δ_L) (hδ_L_lt_one : δ_L < 1)
    (hδ_R_pos : 0 < δ_R) (hδ_R_lt_one : δ_R < 1)
    (h_norm_L : ‖fdBoundary_H H (3 - δ_L) - ellipticPointRho‖ = ε)
    (h_norm_R : ‖fdBoundary_H H (3 + δ_R) - ellipticPointRho‖ = ε)
    (hH_gap : 0 < H - Real.sqrt 3 / 2) :
    ∀ t, 3 - δ_L ≤ t → t ≤ 3 + δ_R →
      ¬(‖fdBoundary_H H t - (ellipticPointRho : ℂ)‖ > ε) := by
  intro t ht_lo ht_hi
  push Not
  rcases le_or_gt t 3 with ht3 | ht3
  · rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · simp only [fdBoundary_H_at_three_eq_rho, sub_self, norm_zero]; exact hε.le
    · rw [g_norm_arc (by nlinarith : 1 < t) ht3',
          ← h_norm_L, g_norm_seg2 hδ_L_pos hδ_L_lt_one]
      exact mul_le_mul_of_nonneg_left
        (Real.sin_le_sin_of_le_of_le_pi_div_two
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos] : (3 - t) * Real.pi / 12 ≤ δ_L * Real.pi / 12))
        (by norm_num : (0:ℝ) ≤ 2)
  · rw [show t = 3 + (t - 3) by ring, g_norm_seg3 H hH (by linarith) (by linarith : t - 3 ≤ 1),
        ← h_norm_R, g_norm_seg3 H hH hδ_R_pos (le_of_lt hδ_R_lt_one)]
    exact mul_le_mul_of_nonneg_right (by linarith : t - 3 ≤ δ_R) hH_gap.le

private def δ_L_rho : ℝ → ℝ := fun ε ↦ 12 / Real.pi * Real.arcsin (ε / 2)

private def δ_R_rho (H : ℝ) : ℝ → ℝ := fun ε ↦ ε / (H - Real.sqrt 3 / 2)

private lemma δ_rho_props (H : ℝ) {ε : ℝ} (hε_pos : 0 < ε)
    (hε_lt : ε < min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12))) :
    0 < δ_L_rho ε ∧ δ_L_rho ε < 1 ∧ 0 < δ_R_rho H ε ∧ δ_R_rho H ε < 1 ∧
    ε / 2 ≤ 1 ∧ -1 ≤ ε / 2 ∧ Real.arcsin (ε / 2) < Real.pi / 12 ∧
    δ_L_rho ε * Real.pi / 12 = Real.arcsin (ε / 2) := by
  have hε_lt_gap : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
  have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := lt_of_lt_of_le hε_lt (min_le_right _ _)
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hH_gap : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hε_lt_sin : ε / 2 < Real.sin (Real.pi / 12) := by linarith
  have hsin_le : Real.sin (Real.pi / 12) ≤ 1 := Real.sin_le_one _
  have harcsin_pos : 0 < Real.arcsin (ε / 2) := Real.arcsin_pos.mpr (by linarith)
  have harcsin_lt : Real.arcsin (ε / 2) < Real.pi / 12 :=
    arcsin_half_lt_pi_div_twelve (by linarith) hε_lt_2sin
  have hδL_lt : δ_L_rho ε < 1 :=
    twelve_div_pi_arcsin_half_lt_one (by linarith) hε_lt_2sin
  have hδL_angle : δ_L_rho ε * Real.pi / 12 = Real.arcsin (ε / 2) := by
    change 12 / Real.pi * Real.arcsin (ε / 2) * Real.pi / 12 = Real.arcsin (ε / 2); field_simp
  exact ⟨mul_pos (div_pos (by norm_num) hpi_pos) harcsin_pos, hδL_lt,
    div_pos hε_pos hH_gap, (div_lt_one hH_gap).mpr hε_lt_gap,
    by linarith, by linarith, harcsin_lt, hδL_angle⟩

private lemma pv_norm_bounds_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    let g := fun t ↦ fdBoundary_H H t - (ellipticPointRho : ℂ)
    let threshold := min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12))
    (∀ ε : ℝ, 0 < ε → ε < threshold → ∀ t ∈ Ico (0 : ℝ) (3 - δ_L_rho ε), ε < ‖g t - 0‖) ∧
    (∀ ε : ℝ, 0 < ε → ε < threshold → ∀ t ∈ Ioc (3 + δ_R_rho H ε) (5 : ℝ), ε < ‖g t - 0‖) ∧
    (∀ ε : ℝ, 0 < ε → ε < threshold →
      ∀ t ∈ Icc (3 - δ_L_rho ε) (3 + δ_R_rho H ε), ‖g t - 0‖ ≤ ε) := by
  intro g _threshold
  have hH_gap : 0 < H - Real.sqrt 3 / 2 := by linarith
  have h_norm_L : ∀ ε : ℝ, 0 < ε → ε < min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12)) →
      ‖fdBoundary_H H (3 - δ_L_rho ε) - ellipticPointRho‖ = ε := by
    intro ε hε_pos hε_lt
    obtain ⟨h1, h2, _, _, hε2_le, hε2_neg, _, hδL_angle⟩ := δ_rho_props H hε_pos hε_lt
    rw [g_norm_seg2 h1 h2, hδL_angle, Real.sin_arcsin hε2_neg hε2_le]; linarith
  have h_norm_R : ∀ ε : ℝ, 0 < ε → ε < min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12)) →
      ‖fdBoundary_H H (3 + δ_R_rho H ε) - ellipticPointRho‖ = ε := by
    intro ε hε_pos hε_lt
    obtain ⟨_, _, h3, h4, _, _, _, _⟩ := δ_rho_props H hε_pos hε_lt
    rw [g_norm_seg3 H hH h3 (le_of_lt h4)]; exact div_mul_cancel₀ ε (ne_of_gt hH_gap)
  refine ⟨?_, ?_, ?_⟩
  · intro ε hε_pos hε_lt t ⟨ht0, ht3⟩
    simp only [g, sub_zero]
    obtain ⟨hδL_p, hδL_lt, _, _, _, _, _, _⟩ := δ_rho_props H hε_pos hε_lt
    have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := lt_of_lt_of_le hε_lt (min_le_right _ _)
    have hε_lt_one : ε < 1 := by
      have : Real.sin (Real.pi / 12) < 1 / 2 :=
        (Real.sin_lt_sin_of_lt_of_le_pi_div_two (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])).trans_eq
          Real.sin_pi_div_six
      linarith
    rcases le_or_gt t 1 with ht1 | ht1
    · exact hε_lt_one.trans_le (g_norm_ge_one_seg0 ht0 ht1)
    · rw [g_norm_arc ht1 (by linarith), ← h_norm_L ε hε_pos hε_lt, g_norm_seg2 hδL_p hδL_lt]
      exact mul_lt_mul_of_pos_left
        (Real.sin_lt_sin_of_lt_of_le_pi_div_two (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos])
          (by nlinarith : δ_L_rho ε * Real.pi / 12 < (3 - t) * Real.pi / 12))
        (by norm_num : (0:ℝ) < 2)
  · intro ε hε_pos hε_lt t ⟨ht3, ht5⟩
    simp only [g, sub_zero]
    obtain ⟨_, _, hδR_p, hδR_lt, _, _, _, _⟩ := δ_rho_props H hε_pos hε_lt
    have hε_lt_gap : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
    rcases le_or_gt t 4 with ht4 | ht4
    · rw [show t = 3 + (t - 3) by ring,
          g_norm_seg3 H hH (by linarith : 0 < t - 3) (by linarith : t - 3 ≤ 1),
          ← h_norm_R ε hε_pos hε_lt, g_norm_seg3 H hH hδR_p (le_of_lt hδR_lt)]
      exact mul_lt_mul_of_pos_right (by linarith : δ_R_rho H ε < t - 3) hH_gap
    · exact hε_lt_gap.trans_le (g_norm_ge_seg4 H hH (le_of_lt ht4) ht5)
  · intro ε hε_pos hε_lt t ⟨ht_lo, ht_hi⟩
    simp only [sub_zero]
    obtain ⟨hδL_p, hδL_lt, hδR_p, hδR_lt, _, _, _, _⟩ := δ_rho_props H hε_pos hε_lt
    exact not_lt.mp (norm_le_middle_rho H hH hε_pos hδL_p hδL_lt hδR_p hδR_lt
      (h_norm_L ε hε_pos hε_lt) (h_norm_R ε hε_pos hε_lt) hH_gap t ht_lo ht_hi)

private lemma pv_integrals_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    let g := fun t ↦ fdBoundary_H H t - (ellipticPointRho : ℂ)
    let threshold := min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12))
    (∀ ε : ℝ, 0 < ε → ε < threshold →
      (∫ t in (0:ℝ)..(3 - δ_L_rho ε), (g t - 0)⁻¹ * deriv g t) +
      (∫ t in (3 + δ_R_rho H ε)..(5:ℝ), (g t - 0)⁻¹ * deriv g t) =
      Complex.log (g (3 - δ_L_rho ε)) - Complex.log (g (3 + δ_R_rho H ε))) ∧
    (∀ ε : ℝ, 0 < ε → ε < threshold →
      IntervalIntegrable (fun t ↦ (g t - 0)⁻¹ * deriv g t) volume 0 (3 - δ_L_rho ε)) ∧
    (∀ ε : ℝ, 0 < ε → ε < threshold →
      IntervalIntegrable (fun t ↦ (g t - 0)⁻¹ * deriv g t) volume (3 + δ_R_rho H ε) 5) := by
  intro g _threshold
  have key : ∀ t : ℝ, (g t - 0)⁻¹ * deriv g t = deriv g t / g t :=
    fun t ↦ by simp only [sub_zero, div_eq_mul_inv, mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · intro ε hε_pos hε_lt
    obtain ⟨h1, h2, h3, h4, _⟩ := δ_rho_props H hε_pos hε_lt
    simp_rw [key]; exact (ftc_logDeriv_telescope_rho H hH h1 h2 h3 h4).2.2
  · intro ε hε_pos hε_lt
    obtain ⟨h1, h2, _, _, _⟩ := δ_rho_props H hε_pos hε_lt
    simp_rw [key]
    exact (ftc_logDeriv_telescope_rho H hH h1 h2
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)).1
  · intro ε hε_pos hε_lt
    obtain ⟨_, _, h3, h4, _⟩ := δ_rho_props H hε_pos hε_lt
    simp_rw [key]
    exact (ftc_logDeriv_telescope_rho H hH
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1) h3 h4).2.1

private lemma pv_log_limit_at_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    let g := fun t ↦ fdBoundary_H H t - (ellipticPointRho : ℂ)
    let δ_L : ℝ → ℝ := δ_L_rho
    let δ_R : ℝ → ℝ := δ_R_rho H
    Tendsto (fun ε ↦ Complex.log (g (3 - δ_L ε)) - Complex.log (g (3 + δ_R ε)))
      (nhdsWithin 0 (Ioi 0)) (nhds (-(I * ↑Real.pi / 3))) := by
  intro g δ_L δ_R
  have hH_gap : 0 < H - Real.sqrt 3 / 2 := by linarith
  have h2sin_pos := two_sin_pi_div_twelve_pos
  set threshold := min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12))
  have hthresh : 0 < threshold := lt_min hH_gap h2sin_pos
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro r hr
  refine ⟨min threshold r, lt_min hthresh hr, ?_⟩
  intro ε hε_mem hε_dist
  simp only [Set.mem_Ioi] at hε_mem
  rw [Real.dist_eq, sub_zero, abs_of_pos hε_mem] at hε_dist
  have hε_pos : 0 < ε := hε_mem
  have hε_lt : ε < threshold := lt_of_lt_of_le hε_dist (min_le_left _ _)
  have hε_lt_r : ε < r := lt_of_lt_of_le hε_dist (min_le_right _ _)
  obtain ⟨hδL_p, hδL_lt_one, hδR_p, hδR_lt_one, hε2_le, hε2_neg, _, hδL_angle⟩ :=
    δ_rho_props H hε_pos hε_lt
  have h_norm_L : ‖g (3 - δ_L ε)‖ = ε := by
    change ‖fdBoundary_H H (3 - δ_L ε) - ellipticPointRho‖ = ε
    rw [g_norm_seg2 hδL_p hδL_lt_one, hδL_angle, Real.sin_arcsin hε2_neg hε2_le]; linarith
  have h_norm_R : ‖g (3 + δ_R ε)‖ = ε := by
    change ‖fdBoundary_H H (3 + δ_R ε) - ellipticPointRho‖ = ε
    rw [g_norm_seg3 H hH hδR_p (le_of_lt hδR_lt_one)]
    exact div_mul_cancel₀ ε (ne_of_gt hH_gap)
  set zL := g (3 - δ_L ε)
  set zR := g (3 + δ_R ε)
  rw [Complex.dist_eq,
    ← Complex.re_add_im (Complex.log zL), ← Complex.re_add_im (Complex.log zR),
    Complex.log_re, Complex.log_re, Complex.log_im, Complex.log_im, h_norm_L, h_norm_R]
  rw [arg_approach_rho_left_helper hδL_p hδL_lt_one,
      arg_approach_rho_right H hH hδR_p (le_of_lt hδR_lt_one)]
  have h_simp : ↑(Real.log ε) + ↑(Real.pi / 6 - δ_L ε * Real.pi / 12) * I -
      (↑(Real.log ε) + ↑(Real.pi / 2) * I) - -(I * ↑Real.pi / 3) =
      ↑(-(δ_L ε * Real.pi / 12)) * I := by push_cast; ring
  rw [h_simp, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  have h_angle_bound : δ_L ε * Real.pi / 12 < ε :=
    delta_pi_div_twelve_lt_eps hδL_p hδL_lt_one.le
      (by linarith [h_norm_L ▸ g_norm_seg2 (H := H) hδL_p hδL_lt_one])
  linarith

/-- The PV integral of `(γ-ρ)⁻¹ γ'` over `[0,5]` with ε-ball cutoff tends to `-iπ/3`. -/
theorem pv_integral_at_rho_tendsto (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    Tendsto (fun ε ↦ ∫ t in (0:ℝ)..5, if ‖fdBoundary_H H t - ellipticPointRho‖ > ε
      then (fdBoundary_H H t - ellipticPointRho)⁻¹ *
           deriv (fun s ↦ fdBoundary_H H s - ellipticPointRho) t
      else 0) (𝓝[>] 0) (𝓝 (-(I * ↑Real.pi / 3))) := by
  set g := fun t ↦ fdBoundary_H H t - (ellipticPointRho : ℂ) with hg_def
  have hH_gap : 0 < H - Real.sqrt 3 / 2 := by linarith
  have h2sin_pos := two_sin_pi_div_twelve_pos
  let δ_L : ℝ → ℝ := δ_L_rho
  let δ_R : ℝ → ℝ := δ_R_rho H
  set threshold := min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12))
  obtain ⟨h_far_left, h_far_right, h_near⟩ := pv_norm_bounds_rho H hH
  obtain ⟨h_ftc_api, hint_left, hint_right⟩ := pv_integrals_rho H hH
  have h_tendsto := ContourIntegral.pv_tendsto_of_crossing_limit_asymmetric
    (γ := g) (a := 0) (b := 5) (s := 0) (L := -(I * ↑Real.pi / 3))
    (t₀ := 3) (by constructor <;> norm_num : (3 : ℝ) ∈ Ioo 0 5)
    (δ_left := δ_L) (δ_right := δ_R) (lt_min hH_gap h2sin_pos)
    (fun ε hp hl ↦ (δ_rho_props H hp hl).1)
    (fun ε hp hl ↦ (δ_rho_props H hp hl).2.2.1)
    (fun ε hp hl ↦ by simp only [sub_zero]; linarith [(δ_rho_props H hp hl).2.1])
    (fun ε hp hl ↦ by linarith [(δ_rho_props H hp hl).2.2.2.1])
    h_far_left h_far_right h_near
    (E := fun ε ↦ Complex.log (g (3 - δ_L ε)) - Complex.log (g (3 + δ_R ε)))
    h_ftc_api hint_left hint_right (pv_log_limit_at_rho H hH)
  have h_eq : (fun ε ↦ ∫ t in (0:ℝ)..5,
      if ‖fdBoundary_H H t - ellipticPointRho‖ > ε
      then (fdBoundary_H H t - ellipticPointRho)⁻¹ *
           deriv (fun s ↦ fdBoundary_H H s - ellipticPointRho) t
      else 0) = (fun ε ↦ ∫ t in (0:ℝ)..5,
      if ‖g t - 0‖ > ε then (g t - 0)⁻¹ * deriv g t else 0) := by
    funext ε; congr 1; funext t; simp only [hg_def, sub_zero]
  rw [h_eq]; exact h_tendsto

end
