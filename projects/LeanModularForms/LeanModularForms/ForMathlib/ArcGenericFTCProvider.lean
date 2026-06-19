/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.BoundaryWindingArcProof
import LeanModularForms.ForMathlib.BoundaryWindingSeg1Proof
import LeanModularForms.ForMathlib.SegmentAnalysis
import LeanModularForms.ForMathlib.SegmentFTC
import LeanModularForms.ForMathlib.WindingWeightProofs

/-!
# `ArcFTCHyp` for the unit-circle arc at a generic angle

For `z₀ = exp(i·θ₀)` with `θ₀ ∈ (π/3, 2π/3) \ {π/2}`, this file constructs
the analytical FTC hypothesis needed by `BoundaryWindingArcProof`.

## Branch structure

- seg1 (right vertical): `log(h)` since `h.re = 1/2 - cos θ₀ > 0`.
- arc left (1/5 → t₀-δ): `log(h)` since `arg(h) ∈ (-π/6, π/6)` (re > 0).
- arc right (t₀+δ → 3/5): `log(-h)` since `-h.re = cos θ₀ - cos θ > 0`.
- seg4 (left vertical): `log(-h)` since `-h.re = 1/2 + cos θ₀ > 0`.
- seg5 (top): `log(h)` since `h.im = H - sin θ₀ > 0`.

The branch correction at the 4/5 junction (between `log(-h_seg4)` and
`log(h_seg5)`) gives `-π · I`, while all other junctions cancel by
junction equalities. The crossing contribution at `t₀` converges to `0`.

## Main results

* `arcFTCHyp_arc_generic` — full `ArcFTCHyp` at any non-elliptic, non-I
  arc point, axiom-clean.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

private def arc_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((1/2 - z₀.re : ℝ) : ℂ) +
  ((H - 5 * t * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ) * I

private lemma fdBoundary_sub_eq_arc_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) (ht : t ≤ 1/5) :
    fdBoundaryFun H t - z₀ = arc_h₀ H z₀ t := by
  simp only [fdBoundaryFun, ht, ite_true, arc_h₀]
  apply Complex.ext <;> simp

private lemma arc_h₀_continuous (H : ℝ) (z₀ : ℂ) : Continuous (arc_h₀ H z₀) := by
  unfold arc_h₀; fun_prop

private lemma hasDerivAt_arc_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (arc_h₀ H z₀) (-(seg1Speed H : ℂ) * I) t := by
  have h_real : HasDerivAt (fun s : ℝ ↦ H - 5 * s * (H - Real.sqrt 3 / 2) - z₀.im)
      (-seg1Speed H) t := by
    have hd : HasDerivAt (fun s : ℝ ↦ 5 * s * (H - Real.sqrt 3 / 2))
        (5 * (H - Real.sqrt 3 / 2)) t :=
      (((hasDerivAt_id t).const_mul (5 : ℝ)).mul_const (H - Real.sqrt 3 / 2)).congr_deriv (by ring)
    exact (((hasDerivAt_const t H).sub hd).sub_const z₀.im).congr_deriv
      (by unfold seg1Speed; ring)
  have h1 : HasDerivAt
      (fun s : ℝ ↦ ((H - 5 * s * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ))
      (-(seg1Speed H : ℂ)) t :=
    h_real.ofReal_comp.congr_deriv (by push_cast; ring)
  exact ((hasDerivAt_const t (((1/2 - z₀.re : ℝ) : ℂ))).add (h1.mul_const I)).congr_deriv
    (by ring)

private lemma deriv_arc_h₀ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (arc_h₀ H z₀) t = -(seg1Speed H : ℂ) * I :=
  (hasDerivAt_arc_h₀ H z₀ t).deriv

private lemma arc_h₀_slitPlane {H : ℝ} {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) (t : ℝ) :
    arc_h₀ H (exp (↑θ₀ * I)) t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  unfold arc_h₀
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero]
  rw [arcZ₀_re_eq]
  have hpi := Real.pi_pos
  have h_cos : Real.cos θ₀ < Real.cos (Real.pi / 3) :=
    Real.strictAntiOn_cos ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h_lo
  rw [Real.cos_pi_div_three] at h_cos
  linarith

private def arc_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((5 * t - 9/2 - z₀.re : ℝ) : ℂ) + ((H - z₀.im : ℝ) : ℂ) * I

private lemma fdBoundary_sub_eq_arc_h₅ (H : ℝ) (z₀ : ℂ) {t : ℝ} (ht : 4/5 < t) :
    fdBoundaryFun H t - z₀ = arc_h₅ H z₀ t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 by linarith,
    show ¬t ≤ 2/5 by linarith, show ¬t ≤ 3/5 by linarith,
    show ¬t ≤ 4/5 by linarith, ite_false, arc_h₅]
  apply Complex.ext <;> simp

private lemma arc_h₅_continuous (H : ℝ) (z₀ : ℂ) : Continuous (arc_h₅ H z₀) := by
  unfold arc_h₅; fun_prop

private lemma hasDerivAt_arc_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (arc_h₅ H z₀) (5 : ℂ) t := by
  have h_real : HasDerivAt (fun s : ℝ ↦ 5 * s - 9/2 - z₀.re) 5 t :=
    ((((hasDerivAt_id t).const_mul 5).sub_const (9/2)).sub_const z₀.re).congr_deriv (by ring)
  have h1 : HasDerivAt (fun s : ℝ ↦ ((5 * s - 9/2 - z₀.re : ℝ) : ℂ)) 5 t :=
    h_real.ofReal_comp.congr_deriv (by push_cast; ring)
  exact (h1.add_const _).congr_deriv (by ring)

private lemma deriv_arc_h₅ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (arc_h₅ H z₀) t = 5 :=
  (hasDerivAt_arc_h₅ H z₀ t).deriv

private lemma arc_h₅_slitPlane {H : ℝ} (hH : 1 < H) {θ₀ : ℝ} (t : ℝ) :
    arc_h₅ H (exp (↑θ₀ * I)) t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  unfold arc_h₅
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
  rw [arcZ₀_im_eq]
  nlinarith [Real.sin_le_one θ₀]

private def arc_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) : ℂ :=
  ((-1/2 - z₀.re : ℝ) : ℂ) +
  ((Real.sqrt 3 / 2 + (5 * t - 3) * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ) * I

private lemma fdBoundary_sub_eq_arc_h₃ (H : ℝ) (z₀ : ℂ) {t : ℝ}
    (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    fdBoundaryFun H t - z₀ = arc_h₃ H z₀ t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 by linarith,
    show ¬t ≤ 2/5 by linarith, show ¬t ≤ 3/5 by linarith,
    ht4, ite_true, ite_false, arc_h₃]
  apply Complex.ext <;> simp

private lemma arc_h₃_continuous (H : ℝ) (z₀ : ℂ) : Continuous (arc_h₃ H z₀) := by
  unfold arc_h₃; fun_prop

private lemma hasDerivAt_arc_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (arc_h₃ H z₀) ((seg1Speed H : ℂ) * I) t := by
  have h_real : HasDerivAt
      (fun s : ℝ ↦ Real.sqrt 3 / 2 + (5 * s - 3) * (H - Real.sqrt 3 / 2) - z₀.im)
      (seg1Speed H) t := by
    have hd : HasDerivAt (fun s : ℝ ↦ 5 * s - 3) 5 t :=
      (((hasDerivAt_id t).const_mul 5).sub_const 3).congr_deriv (by ring)
    exact (((hd.mul_const (H - Real.sqrt 3 / 2)).const_add (Real.sqrt 3 / 2)).sub_const
      z₀.im).congr_deriv (by unfold seg1Speed; ring)
  have h1 : HasDerivAt
      (fun s : ℝ ↦
        ((Real.sqrt 3 / 2 + (5 * s - 3) * (H - Real.sqrt 3 / 2) - z₀.im : ℝ) : ℂ))
      ((seg1Speed H : ℂ)) t := h_real.ofReal_comp.congr_deriv (by ring)
  exact ((hasDerivAt_const t (((-1/2 - z₀.re : ℝ) : ℂ))).add (h1.mul_const I)).congr_deriv
    (by ring)

private lemma deriv_arc_h₃ (H : ℝ) (z₀ : ℂ) (t : ℝ) :
    deriv (arc_h₃ H z₀) t = (seg1Speed H : ℂ) * I :=
  (hasDerivAt_arc_h₃ H z₀ t).deriv

private lemma neg_arc_h₃_slitPlane {H : ℝ} {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) (t : ℝ) :
    -(arc_h₃ H (exp (↑θ₀ * I)) t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  unfold arc_h₃
  simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]
  rw [arcZ₀_re_eq]
  have hpi := Real.pi_pos
  have h_cos_2pi3 : Real.cos (2 * Real.pi / 3) = -1/2 := by
    rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  linarith [Real.strictAntiOn_cos (a := θ₀) ⟨by linarith, by linarith⟩
    ⟨by linarith, by linarith⟩ h_hi]

private def arc_h_arc (z₀ : ℂ) (t : ℝ) : ℂ :=
  exp (↑(fdArcAngle t) * I) - z₀

private lemma fdBoundary_sub_eq_arc_h_arc {H : ℝ} (z₀ : ℂ) {t : ℝ}
    (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    fdBoundaryFun H t - z₀ = arc_h_arc z₀ t := by
  unfold arc_h_arc; rw [fdBoundaryFun_arc_eq_exp H t ht1 ht2]

private lemma arc_h_arc_continuous (z₀ : ℂ) : Continuous (arc_h_arc z₀) := by
  unfold arc_h_arc; fun_prop

private lemma hasDerivAt_arc_h_arc (z₀ : ℂ) (t : ℝ) :
    HasDerivAt (arc_h_arc z₀)
      (↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I)) t := by
  unfold arc_h_arc
  have h1 : HasDerivAt fdArcAngle (5 * Real.pi / 6) t := by
    unfold fdArcAngle
    have h := ((hasDerivAt_id t).const_mul (5 : ℝ)).sub_const 1
    exact ((h.mul_const (Real.pi / 6)).const_add (Real.pi / 3)).congr_deriv (by ring)
  have h2 : HasDerivAt (fun s : ℝ ↦ (↑(fdArcAngle s) : ℂ) * I)
      (↑(5 * Real.pi / 6) * I) t :=
    (h1.ofReal_comp.mul_const I).congr_deriv (by push_cast; ring)
  exact (h2.cexp.congr_deriv (by ring)).sub_const z₀

private lemma deriv_arc_h_arc (z₀ : ℂ) (t : ℝ) :
    deriv (arc_h_arc z₀) t = ↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I) :=
  (hasDerivAt_arc_h_arc z₀ t).deriv

/-- Real part of the arc segment offset: `cos(angle) - cos θ₀`. -/
private lemma arc_h_arc_re (θ₀ t : ℝ) :
    (arc_h_arc (exp (↑θ₀ * I)) t).re = Real.cos (fdArcAngle t) - Real.cos θ₀ := by
  simp [arc_h_arc, exp_mul_I, Complex.cos_ofReal_re]

private lemma arc_h_arc_left_slitPlane {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    {t : ℝ} (ht1 : 1/5 ≤ t) (ht_lt : t < arcT₀ θ₀) :
    arc_h_arc (exp (↑θ₀ * I)) t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  unfold arc_h_arc
  rw [exp_mul_I, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cos, ← ofReal_sin]
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one]
  have hpi := Real.pi_pos
  have harc := fdArcAngle_arcT₀ θ₀
  have h_t_ge : Real.pi / 3 ≤ fdArcAngle t := by unfold fdArcAngle; nlinarith
  have h_t_arc : fdArcAngle t < θ₀ := by unfold fdArcAngle at *; nlinarith
  linarith [Real.strictAntiOn_cos (a := fdArcAngle t) (b := θ₀)
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h_t_arc]

private lemma neg_arc_h_arc_right_slitPlane {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    {t : ℝ} (ht_gt : arcT₀ θ₀ < t) (ht3 : t ≤ 3/5) :
    -(arc_h_arc (exp (↑θ₀ * I)) t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  unfold arc_h_arc
  rw [exp_mul_I, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cos, ← ofReal_sin]
  simp only [Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, mul_one]
  have hpi := Real.pi_pos
  have harc := fdArcAngle_arcT₀ θ₀
  have h_t_le : fdArcAngle t ≤ 2 * Real.pi / 3 := by unfold fdArcAngle; nlinarith
  have h_t_arc : θ₀ < fdArcAngle t := by unfold fdArcAngle at *; nlinarith
  linarith [Real.strictAntiOn_cos (a := θ₀) (b := fdArcAngle t)
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h_t_arc]

private lemma arc_seg1_ftc (H : ℝ) {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) :
    IntervalIntegrable
      (fun t ↦ deriv (arc_h₀ H (exp (↑θ₀ * I))) t / arc_h₀ H (exp (↑θ₀ * I)) t)
      volume 0 (1/5) ∧
    ∫ t in (0:ℝ)..(1/5),
        deriv (arc_h₀ H (exp (↑θ₀ * I))) t / arc_h₀ H (exp (↑θ₀ * I)) t =
      Complex.log (arc_h₀ H (exp (↑θ₀ * I)) (1/5)) -
      Complex.log (arc_h₀ H (exp (↑θ₀ * I)) 0) := by
  apply LogDerivFTC.ftc_log_on_segment (by norm_num : (0 : ℝ) ≤ 1/5)
    (arc_h₀_continuous H _).continuousOn
    (fun t _ ↦ (hasDerivAt_arc_h₀ H _ t).differentiableAt)
    (by
      rw [show deriv (arc_h₀ H (exp (↑θ₀ * I))) =
        fun _ ↦ -(seg1Speed H : ℂ) * I from funext (deriv_arc_h₀ H _)]
      exact continuousOn_const)
  intro t _
  exact arc_h₀_slitPlane h_lo h_hi t

private lemma arc_h_arc_deriv_continuousOn {θ₀ : ℝ} {s : Set ℝ} :
    ContinuousOn (deriv (arc_h_arc (exp (↑θ₀ * I)))) s := by
  rw [show deriv (arc_h_arc (exp (↑θ₀ * I))) =
    fun t ↦ ↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I) from
      funext (deriv_arc_h_arc _)]
  fun_prop

private lemma arc_arc_left_ftc {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < arcT₀ θ₀ - 1/5) :
    IntervalIntegrable
      (fun t ↦ deriv (arc_h_arc (exp (↑θ₀ * I))) t / arc_h_arc (exp (↑θ₀ * I)) t)
      volume (1/5) (arcT₀ θ₀ - δ) ∧
    ∫ t in (1/5 : ℝ)..(arcT₀ θ₀ - δ),
        deriv (arc_h_arc (exp (↑θ₀ * I))) t / arc_h_arc (exp (↑θ₀ * I)) t =
      Complex.log (arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - δ)) -
      Complex.log (arc_h_arc (exp (↑θ₀ * I)) (1/5)) := by
  apply LogDerivFTC.ftc_log_on_segment (by linarith : (1/5 : ℝ) ≤ arcT₀ θ₀ - δ)
    (arc_h_arc_continuous _).continuousOn
    (fun t _ ↦ (hasDerivAt_arc_h_arc _ t).differentiableAt)
    arc_h_arc_deriv_continuousOn
  intro t ⟨ht1, ht_lt⟩
  exact arc_h_arc_left_slitPlane h_lo h_hi ht1 (by linarith)

private lemma arc_arc_right_ftc {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 3/5 - arcT₀ θ₀) :
    IntervalIntegrable
      (fun t ↦ deriv (arc_h_arc (exp (↑θ₀ * I))) t / arc_h_arc (exp (↑θ₀ * I)) t)
      volume (arcT₀ θ₀ + δ) (3/5) ∧
    ∫ t in (arcT₀ θ₀ + δ)..(3/5 : ℝ),
        deriv (arc_h_arc (exp (↑θ₀ * I))) t / arc_h_arc (exp (↑θ₀ * I)) t =
      Complex.log (-(arc_h_arc (exp (↑θ₀ * I)) (3/5))) -
      Complex.log (-(arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ + δ))) := by
  apply LogDerivFTC.ftc_log_neg_on_segment (by linarith : arcT₀ θ₀ + δ ≤ 3/5)
    (arc_h_arc_continuous _).continuousOn
    (fun t _ ↦ (hasDerivAt_arc_h_arc _ t).differentiableAt)
    arc_h_arc_deriv_continuousOn
  intro t ⟨ht_gt, ht3⟩
  exact neg_arc_h_arc_right_slitPlane h_lo h_hi (by linarith) ht3

private lemma arc_seg4_ftc (H : ℝ) {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) :
    IntervalIntegrable
      (fun t ↦ deriv (arc_h₃ H (exp (↑θ₀ * I))) t / arc_h₃ H (exp (↑θ₀ * I)) t)
      volume (3/5) (4/5) ∧
    ∫ t in (3/5 : ℝ)..(4/5),
        deriv (arc_h₃ H (exp (↑θ₀ * I))) t / arc_h₃ H (exp (↑θ₀ * I)) t =
      Complex.log (-(arc_h₃ H (exp (↑θ₀ * I)) (4/5))) -
      Complex.log (-(arc_h₃ H (exp (↑θ₀ * I)) (3/5))) := by
  apply LogDerivFTC.ftc_log_neg_on_segment (by norm_num : (3/5 : ℝ) ≤ 4/5)
    (arc_h₃_continuous H _).continuousOn
    (fun t _ ↦ (hasDerivAt_arc_h₃ H _ t).differentiableAt)
    (by
      rw [show deriv (arc_h₃ H (exp (↑θ₀ * I))) =
        fun _ ↦ (seg1Speed H : ℂ) * I from funext (deriv_arc_h₃ H _)]
      exact continuousOn_const)
  intro t _
  exact neg_arc_h₃_slitPlane h_lo h_hi t

private lemma arc_seg5_ftc {H : ℝ} (hH : 1 < H) {θ₀ : ℝ} :
    IntervalIntegrable
      (fun t ↦ deriv (arc_h₅ H (exp (↑θ₀ * I))) t / arc_h₅ H (exp (↑θ₀ * I)) t)
      volume (4/5) 1 ∧
    ∫ t in (4/5 : ℝ)..(1 : ℝ),
        deriv (arc_h₅ H (exp (↑θ₀ * I))) t / arc_h₅ H (exp (↑θ₀ * I)) t =
      Complex.log (arc_h₅ H (exp (↑θ₀ * I)) 1) - Complex.log (arc_h₅ H (exp (↑θ₀ * I)) (4/5)) := by
  apply LogDerivFTC.ftc_log_on_segment (by norm_num : (4/5 : ℝ) ≤ 1)
    (arc_h₅_continuous H _).continuousOn
    (fun t _ ↦ (hasDerivAt_arc_h₅ H _ t).differentiableAt)
    (by
      rw [show deriv (arc_h₅ H (exp (↑θ₀ * I))) =
        fun _ ↦ (5 : ℂ) from funext (deriv_arc_h₅ H _)]
      exact continuousOn_const)
  intro t _
  exact arc_h₅_slitPlane hH t

private lemma arc_junction_15 (H : ℝ) (z₀ : ℂ) :
    arc_h₀ H z₀ (1/5) = arc_h_arc z₀ (1/5) := by
  unfold arc_h₀ arc_h_arc
  have hθ : (fdArcAngle (1/5) : ℝ) = Real.pi / 3 := by unfold fdArcAngle; ring
  rw [hθ, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  apply Complex.ext <;> simp

private lemma arc_junction_35 (H : ℝ) (z₀ : ℂ) :
    arc_h_arc z₀ (3/5) = arc_h₃ H z₀ (3/5) := by
  unfold arc_h_arc arc_h₃
  have hθ : (fdArcAngle (3/5) : ℝ) = 2 * Real.pi / 3 := by unfold fdArcAngle; ring
  rw [hθ, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  apply Complex.ext <;>
  · simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, Complex.sub_im,
      Complex.add_im, Complex.mul_im, mul_one, zero_add, add_zero]
    ring

private lemma arc_junction_45 (H : ℝ) (z₀ : ℂ) :
    arc_h₃ H z₀ (4/5) = arc_h₅ H z₀ (4/5) := by
  unfold arc_h₃ arc_h₅
  apply Complex.ext <;> · simp; ring

private lemma arc_closed (H : ℝ) (z₀ : ℂ) :
    arc_h₀ H z₀ 0 = arc_h₅ H z₀ 1 := by
  unfold arc_h₀ arc_h₅
  apply Complex.ext <;> simp
  ring

private lemma arc_branch_correction_45 {H : ℝ} (hH : 1 < H) (θ₀ : ℝ) :
    Complex.log (-(arc_h₃ H (exp (↑θ₀ * I)) (4/5))) -
    Complex.log (arc_h₅ H (exp (↑θ₀ * I)) (4/5)) = -(↑Real.pi * I) := by
  rw [arc_junction_45 H _]
  have h_val : arc_h₅ H (exp (↑θ₀ * I)) (4/5) =
      ((-1/2 - Real.cos θ₀ : ℝ) : ℂ) + ((H - Real.sin θ₀ : ℝ) : ℂ) * I := by
    unfold arc_h₅
    rw [arcZ₀_re_eq, arcZ₀_im_eq, show ((5 * (4/5) - 9/2 - Real.cos θ₀ : ℝ) : ℂ) =
      ((-1/2 - Real.cos θ₀ : ℝ) : ℂ) by push_cast; ring]
  rw [h_val]
  set w := ((-1/2 - Real.cos θ₀ : ℝ) : ℂ) + ((H - Real.sin θ₀ : ℝ) : ℂ) * I with hw_def
  have h_im_pos : 0 < w.im := by
    rw [hw_def]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
    linarith [Real.sin_le_one θ₀]
  rw [show Complex.log (-w) = Complex.log w - ↑Real.pi * I by
    rw [Complex.log, Complex.log,
      Complex.arg_neg_eq_arg_sub_pi_of_im_pos h_im_pos, norm_neg]; push_cast; ring]
  ring

/-- Common tail of the `arc_ae_eq_*` lemmas: from a pointwise and a local
`fdBoundaryFun H · - z₀ = g ·` equality, rewrite the boundary integrand as
`deriv g / g`. -/
private lemma arc_ae_eq_tail {H : ℝ} {z₀ : ℂ} {g : ℝ → ℂ} {t : ℝ}
    (h_pt : fdBoundaryFun H t - z₀ = g t)
    (h_evEq : (fun s ↦ fdBoundaryFun H s - z₀) =ᶠ[𝓝 t] g) :
    (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t = deriv g t / g t := by
  rw [h_pt, ← deriv_sub_const (f := fdBoundaryFun H) z₀, h_evEq.deriv_eq, div_eq_mul_inv,
    mul_comm]

private lemma arc_ae_eq_h₀ (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) (1/5) →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (arc_h₀ H z₀) t / arc_h₀ H z₀ t := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (1/5 : ℝ))] with t ht_ne ht_mem
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1/5)] at ht_mem
  have ht_lt : t < 1/5 :=
    lt_of_le_of_ne ht_mem.2 (fun h ↦ ht_ne (Set.mem_singleton_iff.mpr h))
  exact arc_ae_eq_tail (fdBoundary_sub_eq_arc_h₀ H z₀ t ht_lt.le)
    (Filter.eventually_of_mem (Iio_mem_nhds ht_lt)
      (fun s hs ↦ fdBoundary_sub_eq_arc_h₀ H z₀ s hs.le))

private lemma arc_ae_eq_h_arc (H : ℝ) (z₀ : ℂ) {a b : ℝ} (hab : a ≤ b)
    (ha_ge : 1/5 ≤ a) (hb_le : b ≤ 3/5) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (arc_h_arc z₀) t / arc_h_arc z₀ t := by
  have h_excl : ({a, b} : Set ℝ)ᶜ ∈ ae volume :=
    compl_mem_ae_iff.mpr ((Set.toFinite _).measure_zero volume)
  filter_upwards [h_excl] with t ht_ne ht_mem
  rw [uIoc_of_le hab] at ht_mem
  have ht_lt_b : t < b :=
    lt_of_le_of_ne ht_mem.2 (fun h ↦ ht_ne (Set.mem_insert_iff.mpr (Or.inr h)))
  have ht1 : 1/5 < t := ha_ge.trans_lt ht_mem.1
  have ht3_lt : t < 3/5 := ht_lt_b.trans_le hb_le
  exact arc_ae_eq_tail (fdBoundary_sub_eq_arc_h_arc z₀ ht1 ht3_lt.le)
    (Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht3_lt))
      fun _ ⟨hs1, hs3⟩ ↦ fdBoundary_sub_eq_arc_h_arc z₀ hs1 hs3.le)

private lemma arc_ae_eq_h₃ (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (3/5 : ℝ) (4/5) →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (arc_h₃ H z₀) t / arc_h₃ H z₀ t := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (4/5 : ℝ))] with t ht_ne ht_mem
  rw [uIoc_of_le (by norm_num : (3/5 : ℝ) ≤ 4/5)] at ht_mem
  have ht3 : 3/5 < t := ht_mem.1
  have ht4_lt : t < 4/5 :=
    lt_of_le_of_ne ht_mem.2 (fun h ↦ ht_ne (Set.mem_singleton_iff.mpr h))
  exact arc_ae_eq_tail (fdBoundary_sub_eq_arc_h₃ H z₀ ht3 ht4_lt.le)
    (Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht3) (Iio_mem_nhds ht4_lt))
      fun _ ⟨hs3, hs4⟩ ↦ fdBoundary_sub_eq_arc_h₃ H z₀ hs3 hs4.le)

private lemma arc_ae_eq_h₅ (H : ℝ) (z₀ : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (4/5 : ℝ) 1 →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (arc_h₅ H z₀) t / arc_h₅ H z₀ t := by
  refine ae_of_all _ (fun t ht_mem ↦ ?_)
  rw [uIoc_of_le (by norm_num : (4/5 : ℝ) ≤ 1)] at ht_mem
  have ht4 : 4/5 < t := ht_mem.1
  exact arc_ae_eq_tail (fdBoundary_sub_eq_arc_h₅ H z₀ ht4)
    (Filter.eventually_of_mem (Ioi_mem_nhds ht4) fun _ hs ↦ fdBoundary_sub_eq_arc_h₅ H z₀ hs)

/-- Lift the seg/arc FTC integrability to integrability of the `fdBoundary` integrand
by congruence on the interior. -/
private lemma arc_hint_of_ftc {H : ℝ} {z₀ : ℂ} {a b : ℝ} {f : ℝ → ℂ}
    (h_ftc : IntervalIntegrable (fun t ↦ deriv f t / f t) volume a b)
    (h_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t = deriv f t / f t) :
    IntervalIntegrable
      (fun t ↦ (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) volume a b :=
  h_ftc.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
    (h_ae.mono (fun _ ht hm ↦ (ht hm).symm)))

/-- **Transfer a segment FTC result to the `fdBoundaryFun` integrand.** Given a
segment's FTC pair (integrability + integral value `V` for `deriv f / f`) and the
a.e. equality with `(fdBoundaryFun H · - z₀)⁻¹ · deriv (fdBoundaryFun H)`, package
both the integrability and the integral value for the boundary integrand. Used
five times in `fdBoundary_ftc_telescope_arc_aux`. -/
private lemma arc_seg_transfer {H : ℝ} {z₀ : ℂ} {a b : ℝ} {f : ℝ → ℂ} {V : ℂ}
    (h_ftc : IntervalIntegrable (fun t ↦ deriv f t / f t) volume a b ∧
      ∫ t in a..b, deriv f t / f t = V)
    (h_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t = deriv f t / f t) :
    IntervalIntegrable
      (fun t ↦ (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) volume a b ∧
    ∫ t in a..b, (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t = V :=
  ⟨arc_hint_of_ftc h_ftc.1 h_ae, (intervalIntegral.integral_congr_ae h_ae).trans h_ftc.2⟩

private lemma arc_hint_seg1 (H : ℝ) {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) :
    IntervalIntegrable
      (fun t ↦ (fdBoundaryFun H t - exp (↑θ₀ * I))⁻¹ * deriv (fdBoundaryFun H) t)
      volume 0 (1/5) :=
  arc_hint_of_ftc (arc_seg1_ftc H h_lo h_hi).1 (arc_ae_eq_h₀ H _)

private lemma arc_hint_arc_left (H : ℝ) {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < arcT₀ θ₀ - 1/5) :
    IntervalIntegrable
      (fun t ↦ (fdBoundaryFun H t - exp (↑θ₀ * I))⁻¹ * deriv (fdBoundaryFun H) t)
      volume (1/5) (arcT₀ θ₀ - δ) := by
  have := arcT₀_lt_three_fifths h_hi
  exact arc_hint_of_ftc (arc_arc_left_ftc h_lo h_hi hδ_pos hδ_lt).1
    (arc_ae_eq_h_arc H _ (by linarith) le_rfl (by linarith))

private lemma arc_hint_arc_right (H : ℝ) {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 3/5 - arcT₀ θ₀) :
    IntervalIntegrable
      (fun t ↦ (fdBoundaryFun H t - exp (↑θ₀ * I))⁻¹ * deriv (fdBoundaryFun H) t)
      volume (arcT₀ θ₀ + δ) (3/5) := by
  have := arcT₀_gt_one_fifth h_lo
  exact arc_hint_of_ftc (arc_arc_right_ftc h_lo h_hi hδ_pos hδ_lt).1
    (arc_ae_eq_h_arc H _ (by linarith) (by linarith) le_rfl)

private lemma arc_hint_seg4 (H : ℝ) {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) :
    IntervalIntegrable
      (fun t ↦ (fdBoundaryFun H t - exp (↑θ₀ * I))⁻¹ * deriv (fdBoundaryFun H) t)
      volume (3/5) (4/5) :=
  arc_hint_of_ftc (arc_seg4_ftc H h_lo h_hi).1 (arc_ae_eq_h₃ H _)

private lemma arc_hint_seg5 {H : ℝ} (hH : 1 < H) (θ₀ : ℝ) :
    IntervalIntegrable
      (fun t ↦ (fdBoundaryFun H t - exp (↑θ₀ * I))⁻¹ * deriv (fdBoundaryFun H) t)
      volume (4/5) 1 :=
  arc_hint_of_ftc (arc_seg5_ftc hH (θ₀ := θ₀)).1 (arc_ae_eq_h₅ H _)

private theorem fdBoundary_ftc_telescope_arc_aux {H : ℝ} (hH : 1 < H) {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_lo : δ < arcT₀ θ₀ - 1/5)
    (hδ_lt_hi : δ < 3/5 - arcT₀ θ₀) :
    (∫ t in (0 : ℝ)..(arcT₀ θ₀ - δ),
        (fdBoundaryFun H t - exp (↑θ₀ * I))⁻¹ * deriv (fdBoundaryFun H) t) +
    (∫ t in (arcT₀ θ₀ + δ)..(1 : ℝ),
        (fdBoundaryFun H t - exp (↑θ₀ * I))⁻¹ * deriv (fdBoundaryFun H) t) =
    Complex.log (arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - δ)) -
    Complex.log (-(arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ + δ))) +
    (-(↑Real.pi * I)) := by
  set z₀ := exp (↑θ₀ * I) with hz₀_def
  have ht₀_lo : 1/5 < arcT₀ θ₀ := arcT₀_gt_one_fifth h_lo
  have ht₀_hi : arcT₀ θ₀ < 3/5 := arcT₀_lt_three_fifths h_hi
  have hseg1 := arc_seg_transfer (arc_seg1_ftc H h_lo h_hi) (arc_ae_eq_h₀ H z₀)
  have harcL := arc_seg_transfer (arc_arc_left_ftc h_lo h_hi hδ_pos hδ_lt_lo)
    (arc_ae_eq_h_arc H z₀ (by linarith) le_rfl (by linarith))
  have harcR := arc_seg_transfer (arc_arc_right_ftc h_lo h_hi hδ_pos hδ_lt_hi)
    (arc_ae_eq_h_arc H z₀ (by linarith) (by linarith) le_rfl)
  have hseg4 := arc_seg_transfer (arc_seg4_ftc H h_lo h_hi) (arc_ae_eq_h₃ H z₀)
  have hseg5 := arc_seg_transfer (arc_seg5_ftc hH (θ₀ := θ₀)) (arc_ae_eq_h₅ H z₀)
  have h_split_left :
      ∫ t in (0 : ℝ)..(arcT₀ θ₀ - δ),
        (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      (∫ t in (0:ℝ)..(1/5), (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (1/5:ℝ)..(arcT₀ θ₀ - δ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) := by
    have h := intervalIntegral.integral_add_adjacent_intervals hseg1.1 harcL.1
    linear_combination -h
  have h_split_right :
      ∫ t in (arcT₀ θ₀ + δ)..(1 : ℝ),
        (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t =
      (∫ t in (arcT₀ θ₀ + δ)..(3/5:ℝ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (3/5:ℝ)..(4/5),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (4/5:ℝ)..(1:ℝ),
          (fdBoundaryFun H t - z₀)⁻¹ * deriv (fdBoundaryFun H) t) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals harcR.1 hseg4.1
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (harcR.1.trans hseg4.1) hseg5.1
    linear_combination -h1 - h2
  rw [h_split_left, h_split_right, hseg1.2, harcL.2, harcR.2,
      hseg4.2, hseg5.2,
      arc_junction_15 H z₀, arc_junction_35 H z₀, arc_junction_45 H z₀,
      arc_closed H z₀]
  have h_branch_45 := arc_branch_correction_45 hH θ₀
  rw [arc_junction_45 H z₀] at h_branch_45
  linear_combination h_branch_45

private lemma log_div_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Complex.log (a / b) = Complex.log a - Complex.log b := by
  have ha_ne : a ≠ 0 := fun h ↦ by simp [h] at ha
  have hb_ne : b ≠ 0 := fun h ↦ by simp [h] at hb
  have hb_arg_ne_pi : b.arg ≠ Real.pi :=
    fun h ↦ by linarith [(Complex.arg_eq_pi_iff.mp h).1]
  have ha_abs_arg : |a.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha)
  have hb_abs_arg : |b.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  have hb_inv_arg : b⁻¹.arg = -b.arg := by rw [Complex.arg_inv]; simp [hb_arg_ne_pi]
  have h_sum : a.arg + b⁻¹.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [hb_inv_arg]
    refine ⟨?_, ?_⟩ <;> linarith [abs_lt.mp ha_abs_arg, abs_lt.mp hb_abs_arg]
  rw [div_eq_mul_inv, Complex.log_mul ha_ne (inv_ne_zero hb_ne) h_sum,
    Complex.log_inv b hb_arg_ne_pi]
  ring

private lemma arc_h_arc_ratio_eq {θ₀ : ℝ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_small : δ * (5 * Real.pi / 6) < Real.pi) :
    arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - δ) /
      (-(arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ + δ))) =
      exp (↑(-(5 * Real.pi / 6 * δ)) * I) := by
  unfold arc_h_arc
  have h_m : fdArcAngle (arcT₀ θ₀ - δ) = θ₀ - 5 * Real.pi / 6 * δ := by
    have h := fdArcAngle_arcT₀ θ₀
    unfold fdArcAngle at h ⊢
    linarith
  have h_p : fdArcAngle (arcT₀ θ₀ + δ) = θ₀ + 5 * Real.pi / 6 * δ := by
    have h := fdArcAngle_arcT₀ θ₀
    unfold fdArcAngle at h ⊢
    linarith
  rw [h_m, h_p]
  have hφ_pos : (0 : ℝ) < 5 * Real.pi / 6 * δ := by positivity
  have hφ_lt_pi : 5 * Real.pi / 6 * δ < Real.pi := by
    linarith [hδ_small, mul_comm δ (5 * Real.pi / 6)]
  have h_left : (↑(θ₀ - 5 * Real.pi / 6 * δ) * I : ℂ) =
      (↑θ₀ * I) - (↑(5 * Real.pi / 6 * δ) * I) := by push_cast; ring
  have h_right : (↑(θ₀ + 5 * Real.pi / 6 * δ) * I : ℂ) =
      (↑θ₀ * I) + (↑(5 * Real.pi / 6 * δ) * I) := by push_cast; ring
  have h_neg : (↑(-(5 * Real.pi / 6 * δ)) * I : ℂ) =
      -(↑(5 * Real.pi / 6 * δ) * I) := by push_cast; ring
  rw [h_left, h_right, h_neg, Complex.exp_sub, Complex.exp_add, Complex.exp_neg]
  set z := exp (↑θ₀ * I) with hz_def
  set w := exp (↑(5 * Real.pi / 6 * δ) * I) with hw_def
  have hz_ne : z ≠ 0 := exp_ne_zero _
  have hw_ne : w ≠ 0 := exp_ne_zero _
  have hw_ne_one : w ≠ 1 := by
    intro h
    have him := congr_arg Complex.im h
    rw [hw_def, exp_ofReal_mul_I_im, one_im] at him
    linarith [Real.sin_pos_of_pos_of_lt_pi hφ_pos hφ_lt_pi]
  have hzw_sub_ne : z * w - z ≠ 0 := by
    intro h
    apply hw_ne_one
    have h1 : z * (w - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h1 with hz | hw
    · exact absurd hz hz_ne
    · exact sub_eq_zero.mp hw
  rw [div_eq_iff (neg_ne_zero.mpr hzw_sub_ne)]
  field_simp
  ring

private lemma arc_log_diff_tendsto {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) :
    Tendsto (fun δ ↦ Complex.log (arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - δ)) -
        Complex.log (-(arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ + δ))))
      (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  have ht₀_lo : 1/5 < arcT₀ θ₀ := arcT₀_gt_one_fifth h_lo
  have ht₀_hi : arcT₀ θ₀ < 3/5 := arcT₀_lt_three_fifths h_hi
  have h_ratio_tendsto : Tendsto
      (fun δ : ℝ ↦ Complex.log (cexp (↑(-(5 * Real.pi / 6 * δ)) * I)))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 : (↑(-(5 * Real.pi / 6 * (0 : ℝ))) * I : ℂ) = 0 := by push_cast; ring
    have h_inner_cont : ContinuousAt
        (fun δ : ℝ ↦ cexp (↑(-(5 * Real.pi / 6 * δ)) * I)) 0 :=
      Complex.continuous_exp.continuousAt.comp
        ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const).continuousAt
    have hcont := h_inner_cont.clog (h1 ▸ Complex.exp_zero ▸ Complex.one_mem_slitPlane)
    have h_val_zero : Complex.log (cexp (↑(-(5 * Real.pi / 6 * (0 : ℝ))) * I)) = 0 := by
      rw [h1, Complex.exp_zero, Complex.log_one]
    exact (h_val_zero ▸ hcont.tendsto).mono_left nhdsWithin_le_nhds
  set gap := min (arcT₀ θ₀ - 1/5) (3/5 - arcT₀ θ₀) with h_gap_def
  have h_gap_pos : 0 < gap := lt_min (by linarith) (by linarith)
  have h_gap_le_fifth : gap ≤ 1/5 := by
    rcases le_total (arcT₀ θ₀ - 1/5) (3/5 - arcT₀ θ₀) with h | h
    · rw [h_gap_def, min_eq_left h]; linarith
    · rw [h_gap_def, min_eq_right h]; linarith
  have h_eventually_eq : ∀ᶠ δ in (𝓝[>] (0 : ℝ)),
      Complex.log (cexp (↑(-(5 * Real.pi / 6 * δ)) * I)) =
      Complex.log (arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - δ)) -
      Complex.log (-(arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ + δ))) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds h_gap_pos] with δ hδ_lt hδ_pos
    rw [mem_Ioi] at hδ_pos
    rw [mem_Iio] at hδ_lt
    have h_δ_lt_fifth : δ < 1/5 := hδ_lt.trans_le h_gap_le_fifth
    have hδ_small : δ * (5 * Real.pi / 6) < Real.pi := by
      nlinarith [Real.pi_pos, h_δ_lt_fifth]
    have harc := fdArcAngle_arcT₀ θ₀
    have h_δ_lt_gap_l : δ < arcT₀ θ₀ - 1/5 := hδ_lt.trans_le (min_le_left _ _)
    have h_δ_lt_gap_r : δ < 3/5 - arcT₀ θ₀ := hδ_lt.trans_le (min_le_right _ _)
    have h_a_re : 0 < (arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - δ)).re := by
      rw [arc_h_arc_re]
      have h_t_ge : Real.pi / 3 ≤ fdArcAngle (arcT₀ θ₀ - δ) := by
        unfold fdArcAngle; nlinarith
      have h_t_arc : fdArcAngle (arcT₀ θ₀ - δ) < θ₀ := by
        unfold fdArcAngle at *; nlinarith
      linarith [Real.strictAntiOn_cos (a := fdArcAngle (arcT₀ θ₀ - δ)) (b := θ₀)
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h_t_arc]
    have h_b_re : 0 < (-(arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ + δ))).re := by
      rw [Complex.neg_re, arc_h_arc_re]
      have h_t_le : fdArcAngle (arcT₀ θ₀ + δ) ≤ 2 * Real.pi / 3 := by
        unfold fdArcAngle; nlinarith
      have h_t_arc : θ₀ < fdArcAngle (arcT₀ θ₀ + δ) := by
        unfold fdArcAngle at *; nlinarith
      linarith [Real.strictAntiOn_cos (a := θ₀) (b := fdArcAngle (arcT₀ θ₀ + δ))
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h_t_arc]
    rw [← log_div_of_re_pos h_a_re h_b_re, arc_h_arc_ratio_eq hδ_pos hδ_small]
  exact h_ratio_tendsto.congr' h_eventually_eq

private lemma arc_arcsinDelta_tendsto :
    Tendsto arcsinDelta (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · change Tendsto (fun ε ↦ 12 / (5 * Real.pi) * Real.arcsin (ε / 2)) _ _
    have hcont : ContinuousAt (fun ε : ℝ ↦
        12 / (5 * Real.pi) * Real.arcsin (ε / 2)) 0 := by fun_prop
    simpa [Real.arcsin_zero] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (0:ℝ) < 1 by norm_num)] with ε _ hε
    exact mem_Ioi.mpr (arcsinDelta_pos (by rwa [mem_Ioi] at hε))

private def arc_E (θ₀ : ℝ) (ε : ℝ) : ℂ :=
  Complex.log (arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ - arcsinDelta ε)) -
    Complex.log (-(arc_h_arc (exp (↑θ₀ * I)) (arcT₀ θ₀ + arcsinDelta ε))) +
    (-(↑Real.pi * I))

private lemma arc_E_tendsto {θ₀ : ℝ}
    (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) :
    Tendsto (arc_E θ₀) (𝓝[>] 0) (𝓝 (-(↑Real.pi * I))) := by
  unfold arc_E
  simpa using ((arc_log_diff_tendsto h_lo h_hi).comp arc_arcsinDelta_tendsto).add
    (tendsto_const_nhds (x := -(↑Real.pi * I)))

private lemma arc_h_ftc_helper {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {θ₀ : ℝ} (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    (ε : ℝ) (hε : 0 < ε) (hε_thr : ε < arcThreshold H θ₀) :
    (∫ t in (0 : ℝ)..(arcT₀ θ₀ - arcsinDelta ε),
        (γ.toPath.extend t - exp (↑θ₀ * I))⁻¹ * deriv γ.toPath.extend t) +
    (∫ t in (arcT₀ θ₀ + arcsinDelta ε)..1,
        (γ.toPath.extend t - exp (↑θ₀ * I))⁻¹ * deriv γ.toPath.extend t) =
    arc_E θ₀ ε := by
  have h_δ_pos : 0 < arcsinDelta ε := arcsinDelta_pos hε
  have h_lt_gap : arcsinDelta ε < arcGap θ₀ :=
    arcsinDelta_lt_arcGap h_lo h_hi hε hε_thr
  have h_δ_lt_lo : arcsinDelta ε < arcT₀ θ₀ - 1/5 := h_lt_gap.trans_le (min_le_left _ _)
  have h_δ_lt_hi : arcsinDelta ε < 3/5 - arcT₀ θ₀ := h_lt_gap.trans_le (min_le_right _ _)
  have h_t₀_lo : (1/5 : ℝ) < arcT₀ θ₀ := arcT₀_gt_one_fifth h_lo
  have h_t₀_hi : arcT₀ θ₀ < 3/5 := arcT₀_lt_three_fifths h_hi
  rw [transfer_integral (exp (↑θ₀ * I)) (by linarith) le_rfl (by linarith) hγ,
      transfer_integral (exp (↑θ₀ * I)) (by linarith) (by linarith) le_rfl hγ]
  unfold arc_E
  exact fdBoundary_ftc_telescope_arc_aux hH h_lo h_hi h_δ_pos h_δ_lt_lo h_δ_lt_hi

private lemma arc_hint_left_helper {H : ℝ} (_hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {θ₀ : ℝ} (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    (ε : ℝ) (hε : 0 < ε) (hε_thr : ε < arcThreshold H θ₀) :
    IntervalIntegrable
      (fun t ↦ (γ.toPath.extend t - exp (↑θ₀ * I))⁻¹ * deriv γ.toPath.extend t)
      volume 0 (arcT₀ θ₀ - arcsinDelta ε) := by
  have h_δ_pos : 0 < arcsinDelta ε := arcsinDelta_pos hε
  have h_δ_lt_lo : arcsinDelta ε < arcT₀ θ₀ - 1/5 :=
    (arcsinDelta_lt_arcGap h_lo h_hi hε hε_thr).trans_le (min_le_left _ _)
  have h_t₀_lo : (1/5 : ℝ) < arcT₀ θ₀ := arcT₀_gt_one_fifth h_lo
  have h_t₀_hi : arcT₀ θ₀ < 3/5 := arcT₀_lt_three_fifths h_hi
  apply transfer_integrability (exp (↑θ₀ * I)) (by linarith) le_rfl (by linarith) hγ
  exact (arc_hint_seg1 H h_lo h_hi).trans
    (arc_hint_arc_left H h_lo h_hi h_δ_pos h_δ_lt_lo)

private lemma arc_hint_right_helper {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {θ₀ : ℝ} (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3)
    (ε : ℝ) (hε : 0 < ε) (hε_thr : ε < arcThreshold H θ₀) :
    IntervalIntegrable
      (fun t ↦ (γ.toPath.extend t - exp (↑θ₀ * I))⁻¹ * deriv γ.toPath.extend t)
      volume (arcT₀ θ₀ + arcsinDelta ε) 1 := by
  have h_δ_pos : 0 < arcsinDelta ε := arcsinDelta_pos hε
  have h_δ_lt_hi : arcsinDelta ε < 3/5 - arcT₀ θ₀ :=
    (arcsinDelta_lt_arcGap h_lo h_hi hε hε_thr).trans_le (min_le_right _ _)
  have h_t₀_lo : (1/5 : ℝ) < arcT₀ θ₀ := arcT₀_gt_one_fifth h_lo
  have h_t₀_hi : arcT₀ θ₀ < 3/5 := arcT₀_lt_three_fifths h_hi
  apply transfer_integrability (exp (↑θ₀ * I)) (by linarith) (by linarith) le_rfl hγ
  exact ((arc_hint_arc_right H h_lo h_hi h_δ_pos h_δ_lt_hi).trans
    (arc_hint_seg4 H h_lo h_hi)).trans (arc_hint_seg5 hH θ₀)

/-- The full `ArcFTCHyp` at any smooth arc point `z₀ = exp(i·θ₀)` with
`θ₀ ∈ (π/3, 2π/3)`. The limit is `-π · I`. -/
def arcFTCHyp_arc_generic {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {θ₀ : ℝ} (h_lo : Real.pi / 3 < θ₀) (h_hi : θ₀ < 2 * Real.pi / 3) :
    ArcFTCHyp γ (exp (↑θ₀ * I)) (arcT₀ θ₀) arcsinDelta
      (arcThreshold H θ₀) (-(↑Real.pi * I)) where
  E := arc_E θ₀
  h_ftc := arc_h_ftc_helper hH γ hγ h_lo h_hi
  hint_left := arc_hint_left_helper hH γ hγ h_lo h_hi
  hint_right := arc_hint_right_helper hH γ hγ h_lo h_hi
  h_limit := arc_E_tendsto h_lo h_hi

end

