/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.ArcFTCLimit
import LeanModularForms.ForMathlib.CrossingAtRho
import LeanModularForms.ForMathlib.SegmentAnalysis

/-!
# CornerFTCHyp at rho and rho+1

Constructs complete `CornerFTCHyp` instances for the corner crossings at:
- `rho` at `t0 = 3/5` (arc seg2-3 to vertical seg4, angle pi/3)
- `rho+1` at `t0 = 1/5` (vertical seg1 to arc seg2-3, angle pi/3)

## Main results

* `cornerFTCHyp_atRho` -- complete `CornerFTCHyp` at rho
* `cornerFTCHyp_atRhoPlusOne_unconditional` -- complete `CornerFTCHyp` at rho+1
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

private lemma fdHeightValid.sub_pos {H : ℝ} (hH : fdHeightValid H) :
    0 < H - Real.sqrt 3 / 2 := by simpa [fdHeightValid] using hH

private lemma cornerFTC_tendsto_aux (f : ℝ → ℝ) (hcont : ContinuousAt f 0)
    (hval : f 0 = -(Real.pi / 3)) :
    Tendsto (fun ε : ℝ ↦ (↑(f ε) : ℂ) * I) (𝓝[>] 0) (𝓝 (-(↑Real.pi / 3 * I))) := by
  rw [show -(↑Real.pi / 3 * I : ℂ) = ↑(-(Real.pi / 3)) * I by push_cast; ring]
  have h := hval ▸ hcont.tendsto
  exact ((continuous_ofReal.continuousAt.tendsto.comp h).mul_const I).mono_left
    nhdsWithin_le_nhds

private def arcRef_rho (t : ℝ) : ℂ := exp (↑(fdArcAngle t) * I) - ellipticPointRho

private lemma fdArcAngle_contDiff : ContDiff ℝ ⊤ fdArcAngle := by
  unfold fdArcAngle
  fun_prop

private lemma arcRef_rho_contDiff : ContDiff ℝ ⊤ arcRef_rho := by
  unfold arcRef_rho
  exact (Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp fdArcAngle_contDiff).mul
      contDiff_const)).sub contDiff_const

private lemma arcRef_rho_eq (H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    fdBoundaryFun H t - ellipticPointRho = arcRef_rho t := by
  unfold arcRef_rho
  rw [fdBoundaryFun_arc_eq_exp H t ht1 ht2]

private lemma arcRef_rho_slitPlane {t : ℝ} (ht1 : 1/5 ≤ t) (ht2 : t < 3/5) :
    arcRef_rho t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  unfold arcRef_rho
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
    add_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, neg_re, one_re, div_ofNat]
  have hlt : fdArcAngle t < 2 * Real.pi / 3 := by unfold fdArcAngle; nlinarith [Real.pi_pos]
  have hge : Real.pi / 3 ≤ fdArcAngle t := by unfold fdArcAngle; nlinarith [Real.pi_pos]
  have h_cos_gt : Real.cos (2 * Real.pi / 3) < Real.cos (fdArcAngle t) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) hlt
  rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three] at h_cos_gt
  linarith

private lemma arcRef_rho_eventuallyEq (H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t < 3/5) :
    (fun s ↦ fdBoundaryFun H s - ellipticPointRho) =ᶠ[𝓝 t] arcRef_rho :=
  Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht2))
    fun _ hs ↦ arcRef_rho_eq H hs.1 hs.2.le

private def ref_seg1_rho (H : ℝ) (t : ℝ) : ℂ :=
  1 + (↑H - ↑(Real.sqrt 3) / 2 - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I

private lemma ref_seg1_rho_contDiff (H : ℝ) : ContDiff ℝ ⊤ (ref_seg1_rho H) := by
  unfold ref_seg1_rho
  exact contDiff_const.add (((contDiff_const.sub
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const))).mul contDiff_const)

private lemma ref_seg1_rho_slitPlane (H : ℝ) (t : ℝ) :
    ref_seg1_rho H t ∈ Complex.slitPlane := by
  simp [Complex.mem_slitPlane_iff, ref_seg1_rho]

private lemma fdBoundary_sub_rho_eq_ref_seg1 (H : ℝ) (t : ℝ) (ht : t ≤ 1/5) :
    fdBoundaryFun H t - ellipticPointRho = ref_seg1_rho H t := by
  simp only [fdBoundaryFun, ht, ite_true, ellipticPointRho, ellipticPointRho',
    UpperHalfPlane.coe_mk, ref_seg1_rho]
  ring

private lemma fdBoundary_sub_rho_eeq_ref_seg1 (H : ℝ) {t : ℝ} (ht : t < 1/5) :
    (fun s ↦ fdBoundaryFun H s - ellipticPointRho) =ᶠ[𝓝 t] ref_seg1_rho H :=
  Filter.eventually_of_mem (Iio_mem_nhds ht) fun s hs ↦
    fdBoundary_sub_rho_eq_ref_seg1 H s hs.le

private def ref_seg4_rho (H : ℝ) (t : ℝ) : ℂ :=
  ↑(5 * (t - 3/5) * (H - Real.sqrt 3 / 2)) * I

private lemma ref_seg4_rho_contDiff (H : ℝ) : ContDiff ℝ ⊤ (ref_seg4_rho H) := by
  unfold ref_seg4_rho
  exact (Complex.ofRealCLM.contDiff.comp
    (((contDiff_const.mul ((contDiff_id (𝕜 := ℝ) (E := ℝ)).sub contDiff_const)).mul
      contDiff_const))).mul contDiff_const

private lemma ref_seg4_rho_slitPlane (H : ℝ) (hH : fdHeightValid H)
    {t : ℝ} (ht3 : 3/5 < t) (_ht4 : t ≤ 4/5) :
    ref_seg4_rho H t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  simp only [ref_seg4_rho, mul_im, ofReal_re, I_re, ofReal_im, I_im, mul_zero, mul_one,
    add_zero]
  exact ne_of_gt (by nlinarith [hH.sub_pos])

private lemma fdBoundary_sub_rho_eq_ref_seg4 (H : ℝ) {t : ℝ}
    (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    fdBoundaryFun H t - ellipticPointRho = ref_seg4_rho H t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 by linarith,
    show ¬t ≤ 2/5 by linarith, show ¬t ≤ 3/5 by linarith,
    ht4, ite_true, ite_false, ellipticPointRho, ellipticPointRho',
    UpperHalfPlane.coe_mk, ref_seg4_rho]
  push_cast
  ring

private lemma fdBoundary_sub_rho_eeq_ref_seg4 (H : ℝ) {t : ℝ}
    (ht3 : 3/5 < t) (ht4 : t < 4/5) :
    (fun s ↦ fdBoundaryFun H s - ellipticPointRho) =ᶠ[𝓝 t] ref_seg4_rho H :=
  Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht3) (Iio_mem_nhds ht4))
    fun _ hs ↦ fdBoundary_sub_rho_eq_ref_seg4 H hs.1 hs.2.le

private def ref_seg5_rho (H : ℝ) (t : ℝ) : ℂ :=
  (5 * ↑t - 4) + (↑H - ↑(Real.sqrt 3) / 2) * I

private lemma ref_seg5_rho_contDiff (H : ℝ) : ContDiff ℝ ⊤ (ref_seg5_rho H) := by
  unfold ref_seg5_rho
  exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).add contDiff_const

private lemma ref_seg5_rho_slitPlane (H : ℝ) (hH : fdHeightValid H) (t : ℝ) :
    ref_seg5_rho H t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  simp [ref_seg5_rho]
  linarith [hH.sub_pos]

private lemma fdBoundary_sub_rho_eq_ref_seg5 (H : ℝ) {t : ℝ} (ht : 4/5 < t) :
    fdBoundaryFun H t - ellipticPointRho = ref_seg5_rho H t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 by linarith,
    show ¬t ≤ 2/5 by linarith, show ¬t ≤ 3/5 by linarith,
    show ¬t ≤ 4/5 by linarith, ite_false, ellipticPointRho, ellipticPointRho',
    UpperHalfPlane.coe_mk, ref_seg5_rho]
  ring

private lemma fdBoundary_sub_rho_eeq_ref_seg5 (H : ℝ) {t : ℝ} (ht : 4/5 < t) :
    (fun s ↦ fdBoundaryFun H s - ellipticPointRho) =ᶠ[𝓝 t] ref_seg5_rho H :=
  Filter.eventually_of_mem (Ioi_mem_nhds ht) fun _ hs ↦ fdBoundary_sub_rho_eq_ref_seg5 H hs

private lemma integrand_form_eq' (f : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    (f t - z)⁻¹ * deriv f t = deriv (fun s ↦ f s - z) t / (f t - z) := by
  rw [show (fun s ↦ f s - z) = (fun s ↦ f s + (-z)) by ext; ring,
    deriv_add_const, div_eq_mul_inv, mul_comm]

private lemma ne_zero_of_norm_eq_pos {z : ℂ} {ε : ℝ} (hε : 0 < ε) (h : ‖z‖ = ε) : z ≠ 0 :=
  fun hz ↦ by rw [hz, norm_zero] at h; linarith

/-- Simplification of the `vertDelta` formula: `5 * (ε / (5 * c)) * c = ε` when `0 < c`. -/
private lemma vertDelta_norm_simp {ε H : ℝ} (hH : fdHeightValid H) :
    5 * (ε / (5 * (H - Real.sqrt 3 / 2))) * (H - Real.sqrt 3 / 2) = ε := by
  rw [show 5 * (ε / (5 * (H - Real.sqrt 3 / 2))) * (H - Real.sqrt 3 / 2) =
    ε / (5 * (H - Real.sqrt 3 / 2)) * (5 * (H - Real.sqrt 3 / 2)) by ring]
  exact div_mul_cancel₀ ε (ne_of_gt (by have := hH.sub_pos; positivity))

/-- Wrap the standard "piece for reference + a.e. match + endpoint rewrites" pattern. -/
private lemma neg_ftc_piece_wrap {a b : ℝ} {F G : ℝ → ℂ} {LR LL : ℂ}
    (h_piece : IntervalIntegrable (fun t ↦ deriv G t / G t) volume a b ∧
      ∫ t in a..b, deriv G t / G t = Complex.log (-(G b)) - Complex.log (-(G a)))
    (h_ae : ∀ᵐ t ∂volume, t ∈ Ι a b → deriv F t / F t = deriv G t / G t)
    (hFa : F a = G a) (hFb : F b = G b)
    (hLR : LR = Complex.log (-(F b))) (hLL : LL = Complex.log (-(F a))) :
    IntervalIntegrable (fun t ↦ deriv F t / F t) volume a b ∧
    ∫ t in a..b, deriv F t / F t = LR - LL := by
  refine ⟨h_piece.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
    (h_ae.mono fun _ ht hm ↦ (ht hm).symm)), ?_⟩
  rw [intervalIntegral.integral_congr_ae h_ae, h_piece.2, hLR, hLL, hFa, hFb]

private theorem seg1_ftc_rho (H : ℝ) :
    IntervalIntegrable (fun t ↦ deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRho) t /
      (fdBoundaryFun H t - ellipticPointRho)) volume 0 (1/5) ∧
    ∫ t in (0 : ℝ)..(1/5), deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRho) t /
      (fdBoundaryFun H t - ellipticPointRho) =
      Complex.log (fdBoundaryFun H (1/5) - ellipticPointRho) -
      Complex.log (fdBoundaryFun H 0 - ellipticPointRho) :=
  LogDerivFTC.ftc_log_pieceFM (by norm_num)
    (ref_seg1_rho_contDiff H).continuous.continuousOn
    (fun t _ ↦ ((ref_seg1_rho_contDiff H).differentiable (by norm_num)).differentiableAt)
    ((ref_seg1_rho_contDiff H).continuous_deriv le_top).continuousOn
    (fun t _ ↦ ref_seg1_rho_slitPlane H t)
    (fun t ht ↦ ⟨fdBoundary_sub_rho_eq_ref_seg1 H t (by linarith [ht.2]),
      (fdBoundary_sub_rho_eeq_ref_seg1 H (by linarith [ht.2])).deriv_eq⟩)
    (fdBoundary_sub_rho_eq_ref_seg1 H 0 (by norm_num))
    (fdBoundary_sub_rho_eq_ref_seg1 H (1/5) le_rfl)

private theorem arc_ftc_rho (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2/5) :
    IntervalIntegrable (fun t ↦ deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRho) t /
      (fdBoundaryFun H t - ellipticPointRho)) volume (1/5) (3/5 - δ) ∧
    ∫ t in (1/5 : ℝ)..(3/5 - δ), deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRho) t /
      (fdBoundaryFun H t - ellipticPointRho) =
      Complex.log (fdBoundaryFun H (3/5 - δ) - ellipticPointRho) -
      Complex.log (fdBoundaryFun H (1/5) - ellipticPointRho) := by
  apply LogDerivFTC.ftc_log_pieceFM (by linarith)
    arcRef_rho_contDiff.continuous.continuousOn
    (fun t _ ↦ arcRef_rho_contDiff.differentiable (by norm_num) |>.differentiableAt)
    (arcRef_rho_contDiff.continuous_deriv le_top).continuousOn
    (fun t ht ↦ arcRef_rho_slitPlane ht.1 (by linarith [ht.2]))
  · intro t ht
    exact ⟨arcRef_rho_eq H (by linarith [ht.1]) (by linarith [ht.2]),
      (arcRef_rho_eventuallyEq H (by linarith [ht.1]) (by linarith [ht.2])).deriv_eq⟩
  · rw [fdBoundaryFun_at_one_fifth, arcRef_rho, fdArcAngle_at_one_fifth, exp_mul_I,
      ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
    simp [ellipticPointRho, ellipticPointRho', ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']
  · exact arcRef_rho_eq H (by linarith) (by linarith)

private theorem seg4_ftc_rho (H : ℝ) (hH : fdHeightValid H) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1/5) :
    IntervalIntegrable (fun t ↦ deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRho) t /
      (fdBoundaryFun H t - ellipticPointRho)) volume (3/5 + δ) (4/5) ∧
    ∫ t in (3/5 + δ)..(4/5 : ℝ), deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRho) t /
      (fdBoundaryFun H t - ellipticPointRho) =
      Complex.log (fdBoundaryFun H (4/5) - ellipticPointRho) -
      Complex.log (fdBoundaryFun H (3/5 + δ) - ellipticPointRho) :=
  LogDerivFTC.ftc_log_pieceFM (by linarith)
    (ref_seg4_rho_contDiff H).continuous.continuousOn
    (fun t _ ↦ ((ref_seg4_rho_contDiff H).differentiable (by norm_num)).differentiableAt)
    ((ref_seg4_rho_contDiff H).continuous_deriv le_top).continuousOn
    (fun t ht ↦ ref_seg4_rho_slitPlane H hH (by linarith [ht.1]) ht.2)
    (fun t ht ↦ ⟨fdBoundary_sub_rho_eq_ref_seg4 H (by linarith [ht.1]) (by linarith [ht.2]),
      (fdBoundary_sub_rho_eeq_ref_seg4 H (by linarith [ht.1]) (by linarith [ht.2])).deriv_eq⟩)
    (fdBoundary_sub_rho_eq_ref_seg4 H (by linarith) (by linarith))
    (fdBoundary_sub_rho_eq_ref_seg4 H (by norm_num) le_rfl)

private theorem seg5_ftc_rho (H : ℝ) (hH : fdHeightValid H) :
    IntervalIntegrable (fun t ↦ deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRho) t /
      (fdBoundaryFun H t - ellipticPointRho)) volume (4/5) 1 ∧
    ∫ t in (4/5 : ℝ)..1, deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRho) t /
      (fdBoundaryFun H t - ellipticPointRho) =
      Complex.log (fdBoundaryFun H 1 - ellipticPointRho) -
      Complex.log (fdBoundaryFun H (4/5) - ellipticPointRho) := by
  refine LogDerivFTC.ftc_log_pieceFM (by norm_num)
    (ref_seg5_rho_contDiff H).continuous.continuousOn
    (fun t _ ↦ ((ref_seg5_rho_contDiff H).differentiable (by norm_num)).differentiableAt)
    ((ref_seg5_rho_contDiff H).continuous_deriv le_top).continuousOn
    (fun t _ ↦ ref_seg5_rho_slitPlane H hH t)
    (fun t ht ↦ ⟨fdBoundary_sub_rho_eq_ref_seg5 H (by linarith [ht.1]),
      (fdBoundary_sub_rho_eeq_ref_seg5 H (by linarith [ht.1])).deriv_eq⟩)
    ?_ ?_
  · rw [fdBoundaryFun_at_four_fifths]
    simp [ref_seg5_rho, ellipticPointRho, ellipticPointRho']
    ring
  · rw [fdBoundaryFun_at_one]
    simp [ref_seg5_rho, fdStart, ellipticPointRho, ellipticPointRho']
    ring

private theorem fdBoundary_ftc_telescope_rho (H : ℝ) (hH : 1 < H) {δL δR : ℝ}
    (hδL : 0 < δL) (hδL' : δL < 2/5) (hδR : 0 < δR) (hδR' : δR < 1/5) :
    (∫ t in (0 : ℝ)..(3/5 - δL),
        (fdBoundaryFun H t - ellipticPointRho)⁻¹ * deriv (fdBoundaryFun H) t) +
    (∫ t in (3/5 + δR)..(1 : ℝ),
        (fdBoundaryFun H t - ellipticPointRho)⁻¹ * deriv (fdBoundaryFun H) t) =
    Complex.log (fdBoundaryFun H (3/5 - δL) - ellipticPointRho) -
    Complex.log (fdBoundaryFun H (3/5 + δR) - ellipticPointRho) := by
  have hH_valid := fdHeightValid_of_one_lt H hH
  have h_form : ∀ t, (fdBoundaryFun H t - ellipticPointRho)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRho) t /
        (fdBoundaryFun H t - ellipticPointRho) :=
    fun t ↦ integrand_form_eq' (fdBoundaryFun H) ellipticPointRho t
  simp_rw [h_form]
  have p1 := seg1_ftc_rho H
  have p2 := arc_ftc_rho H hδL hδL'
  have p4 := seg4_ftc_rho H hH_valid hδR hδR'
  have p5 := seg5_ftc_rho H hH_valid
  have hleft :
    ∫ t in (0 : ℝ)..(3/5 - δL),
      deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRho) t /
        (fdBoundaryFun H t - ellipticPointRho) =
    Complex.log (fdBoundaryFun H (3/5 - δL) - ellipticPointRho) -
    Complex.log (fdBoundaryFun H 0 - ellipticPointRho) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals p1.1 p2.1, p1.2, p2.2]
    ring
  have hright :
    ∫ t in (3/5 + δR)..(1 : ℝ),
      deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRho) t /
        (fdBoundaryFun H t - ellipticPointRho) =
    Complex.log (fdBoundaryFun H 1 - ellipticPointRho) -
    Complex.log (fdBoundaryFun H (3/5 + δR) - ellipticPointRho) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals p4.1 p5.1, p4.2, p5.2]
    ring
  rw [hleft, hright, fdBoundaryFun_closed H]
  ring

private theorem fdBoundary_integrable_left_of_rho (H : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 2/5) :
    IntervalIntegrable
      (fun t ↦ (fdBoundaryFun H t - ellipticPointRho)⁻¹ * deriv (fdBoundaryFun H) t)
      volume 0 (3/5 - δ) := by
  simp_rw [fun t ↦ integrand_form_eq' (fdBoundaryFun H) ellipticPointRho t]
  exact (seg1_ftc_rho H).1.trans (arc_ftc_rho H hδ hδ').1

private theorem fdBoundary_integrable_right_of_rho (H : ℝ) (hH : fdHeightValid H)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) :
    IntervalIntegrable
      (fun t ↦ (fdBoundaryFun H t - ellipticPointRho)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (3/5 + δ) 1 := by
  simp_rw [fun t ↦ integrand_form_eq' (fdBoundaryFun H) ellipticPointRho t]
  exact (seg4_ftc_rho H hH hδ hδ').1.trans (seg5_ftc_rho H hH).1

private theorem arc_norm_at_rho (H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) :
    ‖fdBoundaryFun H (3/5 - arcsinDelta ε) - ellipticPointRho‖ = ε := by
  have hδ := arcsinDelta_pos hε
  have hδ' := arcsinDelta_lt_one_fifth hε hε_lt
  rw [fdBoundaryFun_arc_dist_rho H _ (by linarith) (by linarith)]
  rw [show fdArcAngle (3/5 - arcsinDelta ε) - 2 * Real.pi / 3 =
      -(5 * arcsinDelta ε * Real.pi / 6) by unfold fdArcAngle; ring,
    show -(5 * arcsinDelta ε * Real.pi / 6) / 2 = -(5 * Real.pi / 12 * arcsinDelta ε) by ring,
    Real.sin_neg, abs_neg, half_angle_arcsinDelta,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      (Real.arcsin_nonneg.mpr (by linarith))
      (le_trans (Real.arcsin_le_pi_div_two _) (by linarith [Real.pi_pos]))),
    Real.sin_arcsin (by linarith) (by linarith)]
  linarith

private theorem vert_norm_at_rho (H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε)
    (hε_lt : ε < H - Real.sqrt 3 / 2) :
    ‖fdBoundaryFun H (3/5 + vertDelta H ε) - ellipticPointRho‖ = ε := by
  rw [fdBoundaryFun_seg4_dist_rho H hH _ (by linarith [vertDelta_pos hH hε])
    (by linarith [vertDelta_lt_one_fifth hH hε_lt]),
    show 3/5 + vertDelta H ε - 3/5 = vertDelta H ε by ring, vertDelta,
    vertDelta_norm_simp hH]

private lemma cos_theta_rho_identity {α : ℝ} :
    Real.cos (2 * Real.pi / 3 - 2 * α) + 1/2 =
      2 * Real.sin α * Real.cos (Real.pi / 6 - α) := by
  rw [show (2 * Real.pi / 3 - 2 * α : ℝ) = (Real.pi - Real.pi / 3) - 2 * α by ring,
    Real.cos_sub,
    show Real.cos (Real.pi - Real.pi / 3) = -(1/2) by
      rw [Real.cos_pi_sub, Real.cos_pi_div_three],
    show Real.sin (Real.pi - Real.pi / 3) = Real.sqrt 3 / 2 by
      rw [Real.sin_pi_sub, Real.sin_pi_div_three],
    Real.cos_two_mul, Real.sin_two_mul, Real.cos_sub, Real.cos_pi_div_six, Real.sin_pi_div_six]
  nlinarith [Real.sin_sq_add_cos_sq α]

private lemma sin_theta_rho_identity {α : ℝ} :
    Real.sin (2 * Real.pi / 3 - 2 * α) - Real.sqrt 3 / 2 =
      2 * Real.sin α * Real.sin (Real.pi / 6 - α) := by
  rw [show (2 * Real.pi / 3 - 2 * α : ℝ) = (Real.pi - Real.pi / 3) - 2 * α by ring,
    Real.sin_sub,
    show Real.sin (Real.pi - Real.pi / 3) = Real.sqrt 3 / 2 by
      rw [Real.sin_pi_sub, Real.sin_pi_div_three],
    show Real.cos (Real.pi - Real.pi / 3) = -(1/2) by
      rw [Real.cos_pi_sub, Real.cos_pi_div_three],
    Real.cos_two_mul, Real.sin_two_mul, Real.sin_sub, Real.sin_pi_div_six,
    Real.cos_pi_div_six]
  ring_nf
  have h5 := Real.sin_sq_add_cos_sq α
  have h6 : Real.sqrt 3 * (Real.sin α ^ 2 + Real.cos α ^ 2) = Real.sqrt 3 := by rw [h5, mul_one]
  linarith

private lemma arcRef_sub_rho_decomp {θ α : ℝ} (hθ : θ = 2 * Real.pi / 3 - 2 * α) :
    (↑(Real.cos θ) + ↑(Real.sin θ) * I : ℂ) - ellipticPointRho =
      ↑(2 * Real.sin α) * (↑(Real.cos (Real.pi / 6 - α)) +
        ↑(Real.sin (Real.pi / 6 - α)) * I) := by
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  apply Complex.ext
  · simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, sub_zero, add_zero, mul_one, neg_re, one_re, div_ofNat, zero_mul]
    linarith [show Real.cos θ + 1/2 = _ from hθ ▸ cos_theta_rho_identity]
  · simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      mul_zero, add_zero, mul_one, zero_add, neg_im, one_im, div_ofNat, zero_mul]
    linarith [show Real.sin θ - Real.sqrt 3 / 2 = _ from hθ ▸ sin_theta_rho_identity]

private theorem arc_arg_at_rho (H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) :
    (fdBoundaryFun H (3/5 - arcsinDelta ε) - ellipticPointRho).arg =
      Real.pi / 6 - 5 * arcsinDelta ε * Real.pi / 12 := by
  have hδ := arcsinDelta_pos hε
  have hδ' := arcsinDelta_lt_one_fifth hε hε_lt
  rw [fdBoundaryFun_arc_eq_exp H _ (by linarith) (by linarith), exp_mul_I,
    ← ofReal_cos, ← ofReal_sin]
  set θ := fdArcAngle (3/5 - arcsinDelta ε)
  set α := 5 * arcsinDelta ε * Real.pi / 12 with α_def
  have hα_pos : 0 < α := by positivity
  have hα_small : α < Real.pi / 6 := by
    rw [α_def]; nlinarith [arcsinDelta_lt_one_fifth hε hε_lt]
  have hθ_eq : θ = 2 * Real.pi / 3 - 2 * α := by
    simp only [θ, α_def, fdArcAngle]; ring
  rw [arcRef_sub_rho_decomp hθ_eq, Complex.ofReal_cos _, Complex.ofReal_sin _]
  have h_sinα_pos : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα_pos (by linarith [Real.pi_pos])
  exact Complex.arg_mul_cos_add_sin_mul_I (show (0 : ℝ) < 2 * Real.sin α by positivity)
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

private theorem vert_arg_at_rho (H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε)
    (hε_lt : ε < H - Real.sqrt 3 / 2) :
    (fdBoundaryFun H (3/5 + vertDelta H ε) - ellipticPointRho).arg = Real.pi / 2 := by
  rw [fdBoundary_sub_rho_eq_ref_seg4 H (by linarith [vertDelta_pos hH hε])
    (by linarith [vertDelta_lt_one_fifth hH hε_lt])]
  change (↑(5 * (3/5 + vertDelta H ε - 3/5) * (H - Real.sqrt 3 / 2)) * I : ℂ).arg = _
  rw [show (5 * (3/5 + vertDelta H ε - 3/5) * (H - Real.sqrt 3 / 2) : ℝ) =
    5 * vertDelta H ε * (H - Real.sqrt 3 / 2) by ring]
  exact arg_ofReal_mul_I _ (by have := vertDelta_pos hH hε; have := hH.sub_pos; positivity)

private def E_atRho (H : ℝ) (ε : ℝ) : ℂ :=
  Complex.log (fdBoundaryFun H (3/5 - arcsinDelta ε) - ellipticPointRho) -
  Complex.log (fdBoundaryFun H (3/5 + vertDelta H ε) - ellipticPointRho)

private theorem E_atRho_eq (H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε)
    (hε_lt : ε < min (1/3) (H - Real.sqrt 3 / 2)) :
    E_atRho H ε = ↑(Real.pi / 6 - 5 * arcsinDelta ε * Real.pi / 12 - Real.pi / 2) * I := by
  have hε_13 : ε < 1/3 := hε_lt.trans_le (min_le_left _ _)
  have hε_H : ε < H - Real.sqrt 3 / 2 := hε_lt.trans_le (min_le_right _ _)
  unfold E_atRho
  rw [log_sub_eq_of_equal_norm (ne_zero_of_norm_eq_pos hε (arc_norm_at_rho H hε hε_13))
      (ne_zero_of_norm_eq_pos hε (vert_norm_at_rho H hH hε hε_H))
      (by rw [arc_norm_at_rho H hε hε_13, vert_norm_at_rho H hH hε hε_H]),
    arc_arg_at_rho H hε hε_13, vert_arg_at_rho H hH hε hε_H]

private theorem E_atRho_tendsto (H : ℝ) (hH : fdHeightValid H) :
    Tendsto (E_atRho H) (𝓝[>] 0) (𝓝 (-(↑Real.pi / 3 * I))) := by
  have hH' : 0 < H - Real.sqrt 3 / 2 := hH.sub_pos
  have hkey : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      E_atRho H ε = ↑(Real.pi / 6 - 5 * arcsinDelta ε * Real.pi / 12 - Real.pi / 2) * I := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (lt_min (by norm_num : (0 : ℝ) < 1/3) hH')] with ε hε hε_pos
    exact E_atRho_eq H hH (by rwa [mem_Ioi] at hε_pos) (by rwa [mem_Iio] at hε)
  refine (cornerFTC_tendsto_aux _ ?_ ?_).congr' (hkey.mono (fun ε h ↦ h.symm))
  · unfold arcsinDelta; fun_prop
  · simp [arcsinDelta, Real.arcsin_zero]; ring

/-- The complete `CornerFTCHyp` at rho. -/
def cornerFTCHyp_atRho {H : ℝ} (hH : 1 < H)
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t) :
    CornerFTCHyp γ ellipticPointRho (3/5)
      arcsinDelta (vertDelta H)
      (min (1/3) (H - Real.sqrt 3 / 2))
      (-(↑Real.pi / 3 * I)) where
  E := E_atRho H
  h_ftc := by
    intro ε hε hεt
    have hε_13 : ε < 1/3 := hεt.trans_le (min_le_left _ _)
    have hε_H : ε < H - Real.sqrt 3 / 2 := hεt.trans_le (min_le_right _ _)
    have hH_valid := fdHeightValid_of_one_lt H hH
    have hδL := arcsinDelta_pos hε
    have hδL' := arcsinDelta_lt_one_fifth hε hε_13
    have hδR := vertDelta_pos hH_valid hε
    have hδR' := vertDelta_lt_one_fifth hH_valid hε_H
    rw [transfer_integral ellipticPointRho (by linarith) (le_refl 0) (by linarith) hγ,
      transfer_integral ellipticPointRho (by linarith) (by linarith) (le_refl 1) hγ]
    exact fdBoundary_ftc_telescope_rho H hH hδL (by linarith) hδR hδR'
  hint_left := by
    intro ε hε hεt
    have hε_13 : ε < 1/3 := hεt.trans_le (min_le_left _ _)
    have hδL := arcsinDelta_pos hε
    have hδL' := arcsinDelta_lt_one_fifth hε hε_13
    exact transfer_integrability ellipticPointRho (by linarith) (le_refl 0) (by linarith) hγ
      (fdBoundary_integrable_left_of_rho H hδL (by linarith))
  hint_right := by
    intro ε hε hεt
    have hε_H : ε < H - Real.sqrt 3 / 2 := hεt.trans_le (min_le_right _ _)
    have hH_valid := fdHeightValid_of_one_lt H hH
    have hδR := vertDelta_pos hH_valid hε
    have hδR' := vertDelta_lt_one_fifth hH_valid hε_H
    exact transfer_integrability ellipticPointRho (by linarith) (by linarith) (le_refl 1) hγ
      (fdBoundary_integrable_right_of_rho H hH_valid hδR hδR')
  h_limit := E_atRho_tendsto H (fdHeightValid_of_one_lt H hH)

private def ref_seg1_rp1 (H : ℝ) (t : ℝ) : ℂ :=
  ↑(5 * (1/5 - t) * (H - Real.sqrt 3 / 2)) * I

private lemma ref_seg1_rp1_contDiff (H : ℝ) : ContDiff ℝ ⊤ (ref_seg1_rp1 H) := by
  unfold ref_seg1_rp1
  exact (Complex.ofRealCLM.contDiff.comp
    (((contDiff_const.mul (contDiff_const.sub (contDiff_id (𝕜 := ℝ) (E := ℝ)))).mul
      contDiff_const))).mul contDiff_const

private lemma ref_seg1_rp1_slitPlane (H : ℝ) (hH : fdHeightValid H)
    {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t < 1/5) :
    ref_seg1_rp1 H t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  simp only [ref_seg1_rp1, mul_im, ofReal_re, I_re, ofReal_im, I_im, mul_zero, mul_one,
    add_zero]
  exact ne_of_gt (by nlinarith [hH.sub_pos])

private lemma fdBoundary_sub_rp1_eq_ref_seg1 (H : ℝ) {t : ℝ}
    (_ht0 : 0 ≤ t) (ht1 : t ≤ 1/5) :
    fdBoundaryFun H t - ellipticPointRhoPlusOne = ref_seg1_rp1 H t := by
  simp only [fdBoundaryFun, ht1, ite_true, ellipticPointRhoPlusOne,
    ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk, ref_seg1_rp1]
  push_cast
  ring

private lemma fdBoundary_sub_rp1_eeq_ref_seg1 (H : ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1/5) :
    (fun s ↦ fdBoundaryFun H s - ellipticPointRhoPlusOne) =ᶠ[𝓝 t] ref_seg1_rp1 H :=
  Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht0) (Iio_mem_nhds ht1))
    fun _ hs ↦ fdBoundary_sub_rp1_eq_ref_seg1 H hs.1.le hs.2.le

private def arcRef_rp1 (t : ℝ) : ℂ := exp (↑(fdArcAngle t) * I) - ellipticPointRhoPlusOne

private lemma arcRef_rp1_contDiff : ContDiff ℝ ⊤ arcRef_rp1 := by
  unfold arcRef_rp1
  exact (Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp fdArcAngle_contDiff).mul
      contDiff_const)).sub contDiff_const

private lemma arcRef_rp1_eq (H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    fdBoundaryFun H t - ellipticPointRhoPlusOne = arcRef_rp1 t := by
  unfold arcRef_rp1
  rw [fdBoundaryFun_arc_eq_exp H t ht1 ht2]

private lemma arcRef_rp1_eventuallyEq (H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t < 3/5) :
    (fun s ↦ fdBoundaryFun H s - ellipticPointRhoPlusOne) =ᶠ[𝓝 t] arcRef_rp1 :=
  Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht2))
    fun _ hs ↦ arcRef_rp1_eq H hs.1 hs.2.le

private lemma arcRef_rp1_neg_slitPlane {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    -(arcRef_rp1 t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  unfold arcRef_rp1
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk,
    neg_sub, sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, one_re, div_ofNat]
  have hgt : Real.pi / 3 < fdArcAngle t := by unfold fdArcAngle; nlinarith [Real.pi_pos]
  have hle : fdArcAngle t ≤ 2 * Real.pi / 3 := by unfold fdArcAngle; nlinarith [Real.pi_pos]
  have h_cos_le : Real.cos (fdArcAngle t) ≤ Real.cos (Real.pi / 3) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) hgt.le
  rw [Real.cos_pi_div_three] at h_cos_le
  rcases eq_or_lt_of_le ht2 with rfl | ht2'
  · rw [fdArcAngle_at_three_fifths,
      show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  · have h_strict : Real.cos (fdArcAngle t) < Real.cos (Real.pi / 3) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos]) hgt
    rw [Real.cos_pi_div_three] at h_strict
    linarith

private theorem seg1_ftc_rp1 (H : ℝ) (hH : fdHeightValid H) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1/5) :
    IntervalIntegrable (fun t ↦ deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
      (fdBoundaryFun H t - ellipticPointRhoPlusOne)) volume 0 (1/5 - δ) ∧
    ∫ t in (0 : ℝ)..(1/5 - δ),
      deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
      (fdBoundaryFun H t - ellipticPointRhoPlusOne) =
      Complex.log (fdBoundaryFun H (1/5 - δ) - ellipticPointRhoPlusOne) -
      Complex.log (fdBoundaryFun H 0 - ellipticPointRhoPlusOne) :=
  LogDerivFTC.ftc_log_pieceFM (by linarith)
    (ref_seg1_rp1_contDiff H).continuous.continuousOn
    (fun t _ ↦ ((ref_seg1_rp1_contDiff H).differentiable (by norm_num)).differentiableAt)
    ((ref_seg1_rp1_contDiff H).continuous_deriv le_top).continuousOn
    (fun t ht ↦ ref_seg1_rp1_slitPlane H hH (by linarith [ht.1]) (by linarith [ht.2]))
    (fun t ht ↦ ⟨fdBoundary_sub_rp1_eq_ref_seg1 H (by linarith [ht.1]) (by linarith [ht.2]),
      (fdBoundary_sub_rp1_eeq_ref_seg1 H (by linarith [ht.1]) (by linarith [ht.2])).deriv_eq⟩)
    (fdBoundary_sub_rp1_eq_ref_seg1 H (by norm_num) (by norm_num))
    (fdBoundary_sub_rp1_eq_ref_seg1 H (by linarith) (by linarith))

private theorem arc_ftc_neg_rp1 (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2/5) :
    IntervalIntegrable (fun t ↦ deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
      (fdBoundaryFun H t - ellipticPointRhoPlusOne)) volume (1/5 + δ) (3/5) ∧
    ∫ t in (1/5 + δ)..(3/5 : ℝ),
      deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
      (fdBoundaryFun H t - ellipticPointRhoPlusOne) =
      Complex.log (-(fdBoundaryFun H (3/5) - ellipticPointRhoPlusOne)) -
      Complex.log (-(fdBoundaryFun H (1/5 + δ) - ellipticPointRhoPlusOne)) := by
  have hab : (1/5 + δ) ≤ (3/5 : ℝ) := by linarith
  have h_piece := LogDerivFTC.ftc_log_neg_on_segment hab
    arcRef_rp1_contDiff.continuous.continuousOn
    (fun t _ ↦ arcRef_rp1_contDiff.differentiable (by norm_num) |>.differentiableAt)
    (arcRef_rp1_contDiff.continuous_deriv le_top).continuousOn
    (fun t ht ↦ arcRef_rp1_neg_slitPlane (by linarith [ht.1]) ht.2)
  refine neg_ftc_piece_wrap h_piece ?_ (arcRef_rp1_eq H (by linarith) (by linarith))
    (arcRef_rp1_eq H (by linarith) le_rfl) rfl rfl
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (3/5 : ℝ))] with t ht_ne ht_mem
  rw [uIoc_of_le hab] at ht_mem
  have ht_lt : t < 3/5 := ht_mem.2.lt_of_ne (fun h ↦ ht_ne (mem_singleton_iff.mpr h))
  have ht_gt : 1/5 < t := by linarith [ht_mem.1]
  rw [arcRef_rp1_eq H ht_gt ht_lt.le, (arcRef_rp1_eventuallyEq H ht_gt ht_lt).deriv_eq]

private theorem vert_norm_at_rp1 (H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε)
    (hε_lt : ε < H - Real.sqrt 3 / 2) :
    ‖fdBoundaryFun H (1/5 - vertDelta H ε) - ellipticPointRhoPlusOne‖ = ε := by
  have hδ := vertDelta_pos hH hε
  have hδ' := vertDelta_lt_one_fifth hH hε_lt
  rw [fdBoundaryFun_seg1_dist_rhoPlusOne H hH _ (by linarith) (by linarith),
    show 1/5 - (1/5 - vertDelta H ε) = vertDelta H ε by ring, vertDelta,
    vertDelta_norm_simp hH]

private theorem arc_norm_at_rp1 (H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) :
    ‖fdBoundaryFun H (1/5 + arcsinDelta ε) - ellipticPointRhoPlusOne‖ = ε := by
  have hδ := arcsinDelta_pos hε
  have hδ' := arcsinDelta_lt_one_fifth hε hε_lt
  rw [fdBoundaryFun_arc_dist_rhoPlusOne H _ (by linarith) (by linarith),
    show fdArcAngle (1/5 + arcsinDelta ε) - Real.pi / 3 =
      5 * arcsinDelta ε * Real.pi / 6 by unfold fdArcAngle; ring,
    show 5 * arcsinDelta ε * Real.pi / 6 / 2 = 5 * Real.pi / 12 * arcsinDelta ε by ring,
    half_angle_arcsinDelta,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      (Real.arcsin_nonneg.mpr (by linarith))
      (le_trans (Real.arcsin_le_pi_div_two _) (by linarith [Real.pi_pos]))),
    Real.sin_arcsin (by linarith) (by linarith)]
  linarith

private theorem vert_arg_at_rp1 (H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε)
    (hε_lt : ε < H - Real.sqrt 3 / 2) :
    (fdBoundaryFun H (1/5 - vertDelta H ε) - ellipticPointRhoPlusOne).arg = Real.pi / 2 := by
  have hδ := vertDelta_pos hH hε
  have hδ' := vertDelta_lt_one_fifth hH hε_lt
  rw [fdBoundary_sub_rp1_eq_ref_seg1 H (by linarith) (by linarith)]
  change (↑(5 * (1/5 - (1/5 - vertDelta H ε)) * (H - Real.sqrt 3 / 2)) * I : ℂ).arg = _
  rw [show (5 * (1/5 - (1/5 - vertDelta H ε)) * (H - Real.sqrt 3 / 2) : ℝ) =
    5 * vertDelta H ε * (H - Real.sqrt 3 / 2) by ring]
  exact arg_ofReal_mul_I _ (by have := hH.sub_pos; positivity)

private lemma cos_theta_rp1_identity {α : ℝ} :
    Real.cos (Real.pi / 3 + 2 * α) - 1/2 =
      2 * Real.sin α * Real.cos (5 * Real.pi / 6 + α) := by
  have hc56 : Real.cos (5 * Real.pi / 6) = -(Real.sqrt 3 / 2) := by
    rw [show (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_six]
  have hs56 : Real.sin (5 * Real.pi / 6) = 1/2 := by
    rw [show (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_six]
  rw [Real.cos_add (Real.pi / 3) (2 * α), Real.cos_pi_div_three,
    Real.sin_pi_div_three, Real.cos_two_mul, Real.sin_two_mul,
    Real.cos_add (5 * Real.pi / 6) α, hc56, hs56]
  nlinarith [Real.sin_sq_add_cos_sq α]

private lemma sin_theta_rp1_identity {α : ℝ} :
    Real.sin (Real.pi / 3 + 2 * α) - Real.sqrt 3 / 2 =
      2 * Real.sin α * Real.sin (5 * Real.pi / 6 + α) := by
  have hc56 : Real.cos (5 * Real.pi / 6) = -(Real.sqrt 3 / 2) := by
    rw [show (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_six]
  have hs56 : Real.sin (5 * Real.pi / 6) = 1/2 := by
    rw [show (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_six]
  rw [Real.sin_add (Real.pi / 3) (2 * α), Real.sin_pi_div_three,
    Real.cos_pi_div_three, Real.cos_two_mul, Real.sin_two_mul,
    Real.sin_add (5 * Real.pi / 6) α, hc56, hs56]
  ring_nf
  have h5 := Real.sin_sq_add_cos_sq α
  have h6 : Real.sqrt 3 * (Real.sin α ^ 2 + Real.cos α ^ 2) = Real.sqrt 3 := by rw [h5, mul_one]
  linarith

private lemma arcRef_sub_rp1_decomp {θ α : ℝ} (hθ : θ = Real.pi / 3 + 2 * α) :
    (↑(Real.cos θ) + ↑(Real.sin θ) * I : ℂ) - ellipticPointRhoPlusOne =
      ↑(2 * Real.sin α) * (↑(Real.cos (5 * Real.pi / 6 + α)) +
        ↑(Real.sin (5 * Real.pi / 6 + α)) * I) := by
  simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  apply Complex.ext
  · simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, sub_zero, add_zero, mul_one, one_re, div_ofNat, zero_mul]
    linarith [show Real.cos θ - 1/2 = _ from hθ ▸ cos_theta_rp1_identity]
  · simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      mul_zero, add_zero, mul_one, zero_add, one_im, div_ofNat, zero_mul]
    linarith [show Real.sin θ - Real.sqrt 3 / 2 = _ from hθ ▸ sin_theta_rp1_identity]

private theorem arc_arg_at_rp1 (H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) :
    (fdBoundaryFun H (1/5 + arcsinDelta ε) - ellipticPointRhoPlusOne).arg =
      5 * Real.pi / 6 + 5 * arcsinDelta ε * Real.pi / 12 := by
  have hδ := arcsinDelta_pos hε
  have hδ' := arcsinDelta_lt_one_fifth hε hε_lt
  rw [fdBoundaryFun_arc_eq_exp H _ (by linarith) (by linarith), exp_mul_I,
    ← ofReal_cos, ← ofReal_sin]
  set θ := fdArcAngle (1/5 + arcsinDelta ε)
  set α := 5 * arcsinDelta ε * Real.pi / 12 with α_def
  have hα_pos : 0 < α := by positivity
  have hα_small : α < Real.pi / 6 := by
    rw [α_def]; nlinarith [arcsinDelta_lt_one_fifth hε hε_lt]
  have hθ_eq : θ = Real.pi / 3 + 2 * α := by
    simp only [θ, α_def, fdArcAngle]; ring
  rw [arcRef_sub_rp1_decomp hθ_eq, Complex.ofReal_cos _, Complex.ofReal_sin _]
  have h_sinα_pos : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα_pos (by linarith [Real.pi_pos])
  exact Complex.arg_mul_cos_add_sin_mul_I (show (0 : ℝ) < 2 * Real.sin α by positivity)
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

private def E_atRhoPlusOne (H : ℝ) (ε : ℝ) : ℂ :=
  Complex.log (fdBoundaryFun H (1/5 - vertDelta H ε) - ellipticPointRhoPlusOne) -
  Complex.log (fdBoundaryFun H (1/5 + arcsinDelta ε) - ellipticPointRhoPlusOne)

private theorem E_atRhoPlusOne_eq (H : ℝ) (hH : fdHeightValid H) {ε : ℝ} (hε : 0 < ε)
    (hε_lt : ε < min (1/3) (H - Real.sqrt 3 / 2)) :
    E_atRhoPlusOne H ε =
      ↑(Real.pi / 2 - (5 * Real.pi / 6 + 5 * arcsinDelta ε * Real.pi / 12)) * I := by
  have hε_13 : ε < 1/3 := hε_lt.trans_le (min_le_left _ _)
  have hε_H : ε < H - Real.sqrt 3 / 2 := hε_lt.trans_le (min_le_right _ _)
  unfold E_atRhoPlusOne
  rw [log_sub_eq_of_equal_norm (ne_zero_of_norm_eq_pos hε (vert_norm_at_rp1 H hH hε hε_H))
      (ne_zero_of_norm_eq_pos hε (arc_norm_at_rp1 H hε hε_13))
      (by rw [vert_norm_at_rp1 H hH hε hε_H, arc_norm_at_rp1 H hε hε_13]),
    vert_arg_at_rp1 H hH hε hε_H, arc_arg_at_rp1 H hε hε_13]

private theorem E_atRhoPlusOne_tendsto (H : ℝ) (hH : fdHeightValid H) :
    Tendsto (E_atRhoPlusOne H) (𝓝[>] 0) (𝓝 (-(↑Real.pi / 3 * I))) := by
  have hH' : 0 < H - Real.sqrt 3 / 2 := hH.sub_pos
  have hkey : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      E_atRhoPlusOne H ε =
        ↑(Real.pi / 2 - (5 * Real.pi / 6 + 5 * arcsinDelta ε * Real.pi / 12)) * I := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (lt_min (by norm_num : (0 : ℝ) < 1/3) hH')] with ε hε hε_pos
    exact E_atRhoPlusOne_eq H hH (by rwa [mem_Ioi] at hε_pos) (by rwa [mem_Iio] at hε)
  refine (cornerFTC_tendsto_aux _ ?_ ?_).congr' (hkey.mono (fun ε h ↦ h.symm))
  · unfold arcsinDelta; fun_prop
  · simp [arcsinDelta, Real.arcsin_zero]; ring

private def cornerFTCHyp_atRhoPlusOne {H : ℝ} (hH : 1 < H)
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (h_ftc_hyp : ∀ ε, 0 < ε → ε < min (1/3) (H - Real.sqrt 3 / 2) →
      (∫ t in (0 : ℝ)..(1/5 - vertDelta H ε),
          (fdBoundaryFun H t - ellipticPointRhoPlusOne)⁻¹ * deriv (fdBoundaryFun H) t) +
      (∫ t in (1/5 + arcsinDelta ε)..(1 : ℝ),
          (fdBoundaryFun H t - ellipticPointRhoPlusOne)⁻¹ * deriv (fdBoundaryFun H) t) =
      E_atRhoPlusOne H ε)
    (h_int_left : ∀ ε, 0 < ε → ε < min (1/3) (H - Real.sqrt 3 / 2) →
      IntervalIntegrable
        (fun t ↦ (fdBoundaryFun H t - ellipticPointRhoPlusOne)⁻¹ * deriv (fdBoundaryFun H) t)
        volume 0 (1/5 - vertDelta H ε))
    (h_int_right : ∀ ε, 0 < ε → ε < min (1/3) (H - Real.sqrt 3 / 2) →
      IntervalIntegrable
        (fun t ↦ (fdBoundaryFun H t - ellipticPointRhoPlusOne)⁻¹ * deriv (fdBoundaryFun H) t)
        volume (1/5 + arcsinDelta ε) 1) :
    CornerFTCHyp γ ellipticPointRhoPlusOne (1/5)
      (vertDelta H) arcsinDelta
      (min (1/3) (H - Real.sqrt 3 / 2))
      (-(↑Real.pi / 3 * I)) where
  E := E_atRhoPlusOne H
  h_ftc := by
    intro ε hε hεt
    have hε_H := hεt.trans_le (min_le_right (1/3) (H - Real.sqrt 3 / 2))
    have hε_13 := hεt.trans_le (min_le_left (1/3) (H - Real.sqrt 3 / 2))
    have hH_valid := fdHeightValid_of_one_lt H hH
    rw [transfer_integral ellipticPointRhoPlusOne
        (by linarith [vertDelta_pos hH_valid hε, vertDelta_lt_one_fifth hH_valid hε_H])
        (le_refl 0) (by linarith [vertDelta_pos hH_valid hε]) hγ,
      transfer_integral ellipticPointRhoPlusOne
        (by linarith [arcsinDelta_pos hε, arcsinDelta_lt_one_fifth hε hε_13])
        (by linarith [arcsinDelta_pos hε]) (le_refl 1) hγ]
    exact h_ftc_hyp ε hε hεt
  hint_left := by
    intro ε hε hεt
    have hε_H := hεt.trans_le (min_le_right (1/3) (H - Real.sqrt 3 / 2))
    have hH_valid := fdHeightValid_of_one_lt H hH
    exact transfer_integrability ellipticPointRhoPlusOne
      (by linarith [vertDelta_pos hH_valid hε, vertDelta_lt_one_fifth hH_valid hε_H])
      (le_refl 0) (by linarith [vertDelta_pos hH_valid hε]) hγ (h_int_left ε hε hεt)
  hint_right := by
    intro ε hε hεt
    have hε_13 := hεt.trans_le (min_le_left (1/3) (H - Real.sqrt 3 / 2))
    exact transfer_integrability ellipticPointRhoPlusOne
      (by linarith [arcsinDelta_pos hε, arcsinDelta_lt_one_fifth hε hε_13])
      (by linarith [arcsinDelta_pos hε]) (le_refl 1) hγ (h_int_right ε hε hεt)
  h_limit := E_atRhoPlusOne_tendsto H (fdHeightValid_of_one_lt H hH)

private def seg4Ref_rp1 (H : ℝ) (t : ℝ) : ℂ :=
  -1 + ↑((5 * t - 3) * (H - Real.sqrt 3 / 2)) * I

private lemma seg4Ref_rp1_contDiff (H : ℝ) : ContDiff ℝ ⊤ (seg4Ref_rp1 H) := by
  unfold seg4Ref_rp1
  exact contDiff_const.add
    ((Complex.ofRealCLM.contDiff.comp
      (((contDiff_const.mul (contDiff_id (𝕜 := ℝ) (E := ℝ))).sub contDiff_const).mul
        contDiff_const)).mul contDiff_const)

private lemma seg4Ref_rp1_neg_slitPlane (H : ℝ) (t : ℝ) :
    -(seg4Ref_rp1 H t) ∈ Complex.slitPlane := by
  simp [Complex.mem_slitPlane_iff, seg4Ref_rp1, neg_re]

private lemma seg4Ref_rp1_eq (H : ℝ) {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    fdBoundaryFun H t - ellipticPointRhoPlusOne = seg4Ref_rp1 H t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 by linarith,
    show ¬t ≤ 2/5 by linarith, show ¬t ≤ 3/5 by linarith,
    ht4, ite_true, ite_false, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
    UpperHalfPlane.coe_mk, seg4Ref_rp1]
  push_cast
  ring

private lemma seg4Ref_rp1_eventuallyEq (H : ℝ) {t : ℝ} (ht3 : 3/5 < t) (ht4 : t < 4/5) :
    (fun s ↦ fdBoundaryFun H s - ellipticPointRhoPlusOne) =ᶠ[𝓝 t] seg4Ref_rp1 H :=
  Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht3) (Iio_mem_nhds ht4))
    fun _ hs ↦ seg4Ref_rp1_eq H hs.1 hs.2.le

private lemma seg4Ref_rp1_eq_35 (H : ℝ) :
    fdBoundaryFun H (3/5) - ellipticPointRhoPlusOne = seg4Ref_rp1 H (3/5) := by
  rw [fdBoundaryFun_at_three_fifths]
  simp [ellipticPointRho, ellipticPointRho', ellipticPointRhoPlusOne,
    ellipticPointRhoPlusOne', seg4Ref_rp1]
  ring

private lemma seg4Ref_rp1_eq_45 (H : ℝ) :
    fdBoundaryFun H (4/5) - ellipticPointRhoPlusOne = seg4Ref_rp1 H (4/5) := by
  rw [fdBoundaryFun_at_four_fifths]
  simp [seg4Ref_rp1, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']
  ring

private theorem seg4_ftc_neg_rp1 (H : ℝ) :
    IntervalIntegrable (fun t ↦
      deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
      (fdBoundaryFun H t - ellipticPointRhoPlusOne)) volume (3/5) (4/5) ∧
    ∫ t in (3/5 : ℝ)..(4/5),
      deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
      (fdBoundaryFun H t - ellipticPointRhoPlusOne) =
      Complex.log (-(fdBoundaryFun H (4/5) - ellipticPointRhoPlusOne)) -
      Complex.log (-(fdBoundaryFun H (3/5) - ellipticPointRhoPlusOne)) := by
  have h_piece := LogDerivFTC.ftc_log_neg_on_segment (by norm_num : (3/5 : ℝ) ≤ 4/5)
    (seg4Ref_rp1_contDiff H).continuous.continuousOn
    (fun t _ ↦ (seg4Ref_rp1_contDiff H).differentiable (by norm_num) |>.differentiableAt)
    ((seg4Ref_rp1_contDiff H).continuous_deriv le_top).continuousOn
    (fun t _ ↦ seg4Ref_rp1_neg_slitPlane H t)
  refine neg_ftc_piece_wrap h_piece ?_ (seg4Ref_rp1_eq_35 H) (seg4Ref_rp1_eq_45 H) rfl rfl
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (4/5 : ℝ))] with t ht_ne ht_mem
  rw [uIoc_of_le (by norm_num : (3/5 : ℝ) ≤ 4/5)] at ht_mem
  have ht_lt : t < 4/5 := ht_mem.2.lt_of_ne (fun h ↦ ht_ne (mem_singleton_iff.mpr h))
  rw [seg4Ref_rp1_eq H (by linarith [ht_mem.1]) ht_lt.le,
    (seg4Ref_rp1_eventuallyEq H (by linarith [ht_mem.1]) ht_lt).deriv_eq]

private def seg5Ref_rp1 (H : ℝ) (t : ℝ) : ℂ :=
  (5 * ↑t - 5) + (↑H - ↑(Real.sqrt 3) / 2) * I

private lemma seg5Ref_rp1_contDiff (H : ℝ) : ContDiff ℝ ⊤ (seg5Ref_rp1 H) := by
  unfold seg5Ref_rp1
  exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).add contDiff_const

private lemma seg5Ref_rp1_neg_slitPlane (H : ℝ) (hH : fdHeightValid H) (t : ℝ) :
    -(seg5Ref_rp1 H t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  simp [seg5Ref_rp1, neg_im]
  linarith [hH.sub_pos]

private lemma seg5Ref_rp1_eq (H : ℝ) {t : ℝ} (ht : 4/5 < t) :
    fdBoundaryFun H t - ellipticPointRhoPlusOne = seg5Ref_rp1 H t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 by linarith,
    show ¬t ≤ 2/5 by linarith, show ¬t ≤ 3/5 by linarith,
    show ¬t ≤ 4/5 by linarith, ite_false, seg5Ref_rp1,
    ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  ring

private lemma seg5Ref_rp1_eventuallyEq (H : ℝ) {t : ℝ} (ht : 4/5 < t) :
    (fun s ↦ fdBoundaryFun H s - ellipticPointRhoPlusOne) =ᶠ[𝓝 t] seg5Ref_rp1 H :=
  Filter.eventually_of_mem (Ioi_mem_nhds ht) fun _ hs ↦ seg5Ref_rp1_eq H hs

private lemma seg5Ref_rp1_eq_45 (H : ℝ) :
    fdBoundaryFun H (4/5) - ellipticPointRhoPlusOne = seg5Ref_rp1 H (4/5) := by
  rw [fdBoundaryFun_at_four_fifths]
  simp [seg5Ref_rp1, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']
  ring

private lemma seg5Ref_rp1_eq_1 (H : ℝ) :
    fdBoundaryFun H 1 - ellipticPointRhoPlusOne = seg5Ref_rp1 H 1 := by
  rw [fdBoundaryFun_at_one]
  simp [seg5Ref_rp1, fdStart, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']
  ring

private theorem seg5_ftc_neg_rp1 (H : ℝ) (hH : fdHeightValid H) :
    IntervalIntegrable (fun t ↦
      deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
      (fdBoundaryFun H t - ellipticPointRhoPlusOne)) volume (4/5) 1 ∧
    ∫ t in (4/5 : ℝ)..1,
      deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
      (fdBoundaryFun H t - ellipticPointRhoPlusOne) =
      Complex.log (-(fdBoundaryFun H 1 - ellipticPointRhoPlusOne)) -
      Complex.log (-(fdBoundaryFun H (4/5) - ellipticPointRhoPlusOne)) := by
  have h_piece := LogDerivFTC.ftc_log_neg_on_segment (by norm_num : (4/5 : ℝ) ≤ 1)
    (seg5Ref_rp1_contDiff H).continuous.continuousOn
    (fun t _ ↦ (seg5Ref_rp1_contDiff H).differentiable (by norm_num) |>.differentiableAt)
    ((seg5Ref_rp1_contDiff H).continuous_deriv le_top).continuousOn
    (fun t _ ↦ seg5Ref_rp1_neg_slitPlane H hH t)
  refine neg_ftc_piece_wrap h_piece ?_ (seg5Ref_rp1_eq_45 H) (seg5Ref_rp1_eq_1 H) rfl rfl
  filter_upwards with t ht_mem
  rw [uIoc_of_le (by norm_num : (4/5 : ℝ) ≤ 1)] at ht_mem
  rw [seg5Ref_rp1_eq H (by linarith [ht_mem.1]),
    (seg5Ref_rp1_eventuallyEq H (by linarith [ht_mem.1])).deriv_eq]

private lemma log_neg_eq_sub_pi_I_rp1 {z : ℂ} (hz_im : 0 < z.im) :
    Complex.log (-z) = Complex.log z - ↑Real.pi * I := by
  change ↑(Real.log ‖-z‖) + ↑((-z).arg) * I =
    ↑(Real.log ‖z‖) + ↑z.arg * I - ↑Real.pi * I
  simp only [norm_neg]
  rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz_im]
  push_cast
  ring

private lemma fdBoundary_sub_rp1_at_start_im_pos (H : ℝ) (hH : fdHeightValid H) :
    0 < (fdBoundaryFun H 0 - ellipticPointRhoPlusOne).im := by
  rw [fdBoundaryFun_at_zero]
  simp [fdStart, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']
  linarith [hH.sub_pos]

private lemma arcRef_rp1_im_pos {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2/5) :
    0 < (arcRef_rp1 (1/5 + δ)).im := by
  unfold arcRef_rp1
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk,
    sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
    mul_zero, add_zero, mul_one, zero_add, one_im, div_ofNat]
  have hθ_gt : Real.pi / 3 < fdArcAngle (1/5 + δ) := by
    unfold fdArcAngle
    nlinarith [Real.pi_pos]
  have hθ_lt : fdArcAngle (1/5 + δ) < 2 * Real.pi / 3 := by
    unfold fdArcAngle
    nlinarith [Real.pi_pos]
  have : Real.sqrt 3 / 2 < Real.sin (fdArcAngle (1/5 + δ)) := by
    rcases le_or_gt (fdArcAngle (1/5 + δ)) (Real.pi / 2) with h | h
    · rw [← Real.sin_pi_div_three]
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by linarith [Real.pi_pos]) h hθ_gt
    · rw [← Real.sin_pi_sub (fdArcAngle (1/5 + δ)), ← Real.sin_pi_div_three]
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by linarith [Real.pi_pos]) (by linarith) (by linarith)
  linarith

private theorem ftc_right_neg_log_rp1 (H : ℝ) (hH : fdHeightValid H) {δR : ℝ}
    (hδR : 0 < δR) (hδR' : δR < 2/5) :
    ∫ t in (1/5 + δR)..(1 : ℝ),
      deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
        (fdBoundaryFun H t - ellipticPointRhoPlusOne) =
    Complex.log (-(fdBoundaryFun H 1 - ellipticPointRhoPlusOne)) -
    Complex.log (-(fdBoundaryFun H (1/5 + δR) - ellipticPointRhoPlusOne)) := by
  have p_arc := arc_ftc_neg_rp1 H hδR hδR'
  have p4 := seg4_ftc_neg_rp1 H
  have p5 := seg5_ftc_neg_rp1 H hH
  have hright_arc_seg4 :
    ∫ t in (1/5 + δR)..(4/5 : ℝ),
      deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
        (fdBoundaryFun H t - ellipticPointRhoPlusOne) =
    Complex.log (-(fdBoundaryFun H (4/5) - ellipticPointRhoPlusOne)) -
    Complex.log (-(fdBoundaryFun H (1/5 + δR) - ellipticPointRhoPlusOne)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals p_arc.1 p4.1,
      p_arc.2, p4.2]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (p_arc.1.trans p4.1) p5.1,
    hright_arc_seg4, p5.2]
  ring

private lemma branch_correction_arc_rp1 (H : ℝ) {δR : ℝ} (hδR : 0 < δR) (hδR' : δR < 2/5) :
    Complex.log (-(fdBoundaryFun H (1/5 + δR) - ellipticPointRhoPlusOne)) =
    Complex.log (fdBoundaryFun H (1/5 + δR) - ellipticPointRhoPlusOne) - ↑Real.pi * I := by
  have h_arc_eq := arcRef_rp1_eq H (show 1/5 < 1/5 + δR by linarith)
    (show 1/5 + δR ≤ 3/5 by linarith)
  exact log_neg_eq_sub_pi_I_rp1 (h_arc_eq ▸ arcRef_rp1_im_pos hδR hδR')

private lemma branch_correction_start_rp1 (H : ℝ) (hH : fdHeightValid H) :
    Complex.log (-(fdBoundaryFun H 0 - ellipticPointRhoPlusOne)) =
    Complex.log (fdBoundaryFun H 0 - ellipticPointRhoPlusOne) - ↑Real.pi * I :=
  log_neg_eq_sub_pi_I_rp1 (fdBoundary_sub_rp1_at_start_im_pos H hH)

private theorem fdBoundary_ftc_telescope_rp1 (H : ℝ) (hH : 1 < H) {δL δR : ℝ}
    (hδL : 0 < δL) (hδL' : δL < 1/5) (hδR : 0 < δR) (hδR' : δR < 2/5) :
    (∫ t in (0 : ℝ)..(1/5 - δL),
        (fdBoundaryFun H t - ellipticPointRhoPlusOne)⁻¹ * deriv (fdBoundaryFun H) t) +
    (∫ t in (1/5 + δR)..(1 : ℝ),
        (fdBoundaryFun H t - ellipticPointRhoPlusOne)⁻¹ * deriv (fdBoundaryFun H) t) =
    Complex.log (fdBoundaryFun H (1/5 - δL) - ellipticPointRhoPlusOne) -
    Complex.log (fdBoundaryFun H (1/5 + δR) - ellipticPointRhoPlusOne) := by
  have hH_valid := fdHeightValid_of_one_lt H hH
  have h_form : ∀ t,
      (fdBoundaryFun H t - ellipticPointRhoPlusOne)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
        (fdBoundaryFun H t - ellipticPointRhoPlusOne) :=
    fun t ↦ integrand_form_eq' (fdBoundaryFun H) ellipticPointRhoPlusOne t
  simp_rw [h_form]
  have p1 := seg1_ftc_rp1 H hH_valid hδL hδL'
  have hright' :
    ∫ t in (1/5 + δR)..(1 : ℝ),
      deriv (fun s ↦ fdBoundaryFun H s - ellipticPointRhoPlusOne) t /
        (fdBoundaryFun H t - ellipticPointRhoPlusOne) =
    Complex.log (fdBoundaryFun H 0 - ellipticPointRhoPlusOne) -
    Complex.log (fdBoundaryFun H (1/5 + δR) - ellipticPointRhoPlusOne) := by
    rw [ftc_right_neg_log_rp1 H hH_valid hδR hδR',
      branch_correction_arc_rp1 H hδR hδR',
      show -(fdBoundaryFun H 1 - ellipticPointRhoPlusOne) =
        -(fdBoundaryFun H 0 - ellipticPointRhoPlusOne) by rw [fdBoundaryFun_closed],
      branch_correction_start_rp1 H hH_valid]
    ring
  rw [p1.2, hright']
  ring

private theorem fdBoundary_integrable_left_of_rp1 (H : ℝ) (hH : fdHeightValid H)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/5) :
    IntervalIntegrable
      (fun t ↦ (fdBoundaryFun H t - ellipticPointRhoPlusOne)⁻¹ * deriv (fdBoundaryFun H) t)
      volume 0 (1/5 - δ) := by
  simp_rw [fun t ↦ integrand_form_eq' (fdBoundaryFun H) ellipticPointRhoPlusOne t]
  exact (seg1_ftc_rp1 H hH hδ hδ').1

private theorem fdBoundary_integrable_right_of_rp1 (H : ℝ) (hH : fdHeightValid H)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2/5) :
    IntervalIntegrable
      (fun t ↦ (fdBoundaryFun H t - ellipticPointRhoPlusOne)⁻¹ * deriv (fdBoundaryFun H) t)
      volume (1/5 + δ) 1 := by
  simp_rw [fun t ↦ integrand_form_eq' (fdBoundaryFun H) ellipticPointRhoPlusOne t]
  exact ((arc_ftc_neg_rp1 H hδ hδ').1.trans (seg4_ftc_neg_rp1 H).1).trans
    (seg5_ftc_neg_rp1 H hH).1

/-- The complete `CornerFTCHyp` at rho+1. -/
def cornerFTCHyp_atRhoPlusOne_unconditional {H : ℝ} (hH : 1 < H)
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t) :
    CornerFTCHyp γ ellipticPointRhoPlusOne (1/5)
      (vertDelta H) arcsinDelta
      (min (1/3) (H - Real.sqrt 3 / 2))
      (-(↑Real.pi / 3 * I)) :=
  cornerFTCHyp_atRhoPlusOne hH hγ
    (fun ε hε hεt ↦ by
      have hε_13 : ε < 1/3 := hεt.trans_le (min_le_left _ _)
      have hε_H : ε < H - Real.sqrt 3 / 2 := hεt.trans_le (min_le_right _ _)
      have hH_valid := fdHeightValid_of_one_lt H hH
      exact fdBoundary_ftc_telescope_rp1 H hH (vertDelta_pos hH_valid hε)
        (vertDelta_lt_one_fifth hH_valid hε_H) (arcsinDelta_pos hε)
        (by linarith [arcsinDelta_lt_one_fifth hε hε_13]))
    (fun ε hε hεt ↦ by
      have hε_H : ε < H - Real.sqrt 3 / 2 := hεt.trans_le (min_le_right _ _)
      have hH_valid := fdHeightValid_of_one_lt H hH
      exact fdBoundary_integrable_left_of_rp1 H hH_valid
        (vertDelta_pos hH_valid hε) (vertDelta_lt_one_fifth hH_valid hε_H))
    (fun ε hε hεt ↦ by
      have hε_13 : ε < 1/3 := hεt.trans_le (min_le_left _ _)
      exact fdBoundary_integrable_right_of_rp1 H (fdHeightValid_of_one_lt H hH)
        (arcsinDelta_pos hε) (by linarith [arcsinDelta_lt_one_fifth hε hε_13]))

end
