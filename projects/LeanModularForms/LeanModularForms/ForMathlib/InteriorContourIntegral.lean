/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.InteriorWinding
import LeanModularForms.ForMathlib.SegmentAnalysis
import LeanModularForms.ForMathlib.ArcFTCAtI

/-!
# Interior Contour Integral = -2πi

For `z` in the strict interior of the fundamental domain (`‖z‖ > 1`, `|Re z| < 1/2`,
`0 < Im z < H`), the contour integral of `(w - z)⁻¹` around the FD boundary equals
`-(2 * π * I)`.

## Strategy

On segments 1 and 5, `γ(t) - z` stays in the slit plane (positive real / imaginary part).
On segment 4, `-(γ(t) - z)` has positive real part. On the arc (segments 2-3), we
case-split on `z.re`: when `z.re ≤ 0`, `γ(t) - z ∈ slitPlane`; when `z.re > 0`,
`-(γ(t) - z) ∈ slitPlane`. The branch correction from segment 4 is `-2πi`.

## Main results

* `fdBoundary_contourIntegral_interior_eq`
* `fdBoundaryPC1Path_contourIntegral_interior_eq`
* `fdBoundary_interior_winding_complete`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

private lemma abs_lt_of_sq_lt {a b : ℝ} (h : a ^ 2 < b ^ 2) : |a| < |b| := by
  nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|),
    abs_nonneg a, abs_nonneg b]

theorem im_gt_sqrt3_div_two_of_interior {z : ℂ}
    (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : 0 < z.im) :
    Real.sqrt 3 / 2 < z.im := by
  have hnsq := Complex.one_lt_normSq_iff.mpr hz_norm
  simp only [Complex.normSq_apply] at hnsq
  have h_resq : z.re ^ 2 < 1/4 := by
    nlinarith [sq_abs z.re, abs_nonneg z.re]
  have h_imsq : (Real.sqrt 3 / 2) ^ 2 < z.im ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0).le]
    norm_num
    nlinarith
  nlinarith [sq_nonneg (z.im - Real.sqrt 3 / 2)]

private def ref1 (z : ℂ) (H : ℝ) (t : ℝ) : ℂ :=
  (1/2 - z.re : ℝ) + (H - 5 * t * (H - Real.sqrt 3 / 2) - z.im : ℝ) * I

private lemma ref1_cd (z : ℂ) (H : ℝ) : ContDiff ℝ ⊤ (ref1 z H) := by
  unfold ref1
  apply ContDiff.add contDiff_const
  exact (Complex.ofRealCLM.contDiff.comp
    ((contDiff_const.sub ((contDiff_const.mul contDiff_id).mul contDiff_const)).sub
      contDiff_const)).mul contDiff_const

private lemma ref1_eq (z : ℂ) (H : ℝ) {t : ℝ} (ht : t ≤ 1/5) :
    fdBoundaryFun H t - z = ref1 z H t := by
  simp only [fdBoundaryFun, ht, ite_true, ref1]
  apply Complex.ext <;> push_cast <;> simp [add_re, sub_re, mul_re, mul_im, ofReal_re,
    ofReal_im, I_re, I_im, add_im, sub_im]

private lemma ref1_slit (z : ℂ) (H : ℝ) (hz : z.re < 1/2) (t : ℝ) :
    ref1 z H t ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  left
  simp only [ref1, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero]
  linarith

private def ref5 (z : ℂ) (H : ℝ) (t : ℝ) : ℂ :=
  (5 * t - 9/2 - z.re : ℝ) + (H - z.im : ℝ) * I

private lemma ref5_cd (z : ℂ) (H : ℝ) : ContDiff ℝ ⊤ (ref5 z H) := by
  unfold ref5
  exact (Complex.ofRealCLM.contDiff.comp
    (((contDiff_const.mul contDiff_id).sub contDiff_const).sub contDiff_const)).add
    contDiff_const

private lemma ref5_eq (z : ℂ) (H : ℝ) {t : ℝ} (ht : 4/5 < t) :
    fdBoundaryFun H t - z = ref5 z H t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith, show ¬t ≤ 2/5 from by linarith,
    show ¬t ≤ 3/5 from by linarith, show ¬t ≤ 4/5 from by linarith, ite_false, ref5]
  apply Complex.ext <;> push_cast <;> simp [add_re, sub_re, mul_re, mul_im, ofReal_re,
    ofReal_im, I_re, I_im, add_im, sub_im]

private lemma ref5_slit (z : ℂ) (H : ℝ) (hz : z.im < H) (t : ℝ) :
    ref5 z H t ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  unfold ref5
  simp only [add_im, ofReal_im, mul_im, I_re, I_im, mul_zero, add_zero, mul_one, ne_eq]
  simp only [ofReal_re]
  linarith

private def ref4n (z : ℂ) (H : ℝ) (t : ℝ) : ℂ :=
  (z.re + 1/2 : ℝ) +
    (z.im - Real.sqrt 3 / 2 - (5 * t - 3) * (H - Real.sqrt 3 / 2) : ℝ) * I

private lemma ref4n_cd (z : ℂ) (H : ℝ) : ContDiff ℝ ⊤ (ref4n z H) := by
  unfold ref4n
  apply ContDiff.add contDiff_const
  exact (Complex.ofRealCLM.contDiff.comp
    (contDiff_const.sub (((contDiff_const.mul contDiff_id).sub contDiff_const).mul
      contDiff_const))).mul contDiff_const

private lemma ref4n_eq (z : ℂ) (H : ℝ) {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    -(fdBoundaryFun H t - z) = ref4n z H t := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith, show ¬t ≤ 2/5 from by linarith,
    show ¬t ≤ 3/5 from by linarith, ht4, ite_true, ite_false, ref4n]
  apply Complex.ext <;> push_cast <;> simp [neg_re, neg_im, add_re, sub_re, mul_re, mul_im,
    ofReal_re, ofReal_im, I_re, I_im, add_im, sub_im] <;> ring

private lemma ref4n_slit (z : ℂ) (H : ℝ) (hz : -1/2 < z.re) (t : ℝ) :
    ref4n z H t ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  left
  simp only [ref4n, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero]
  linarith

private theorem seg1F (z : ℂ) (H : ℝ) (hz : z.re < 1/2) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - z) t /
      (fdBoundaryFun H t - z)) volume 0 (1/5) ∧
    ∫ t in (0 : ℝ)..(1/5), deriv (fun s => fdBoundaryFun H s - z) t /
      (fdBoundaryFun H t - z) =
      Complex.log (fdBoundaryFun H (1/5) - z) - Complex.log (fdBoundaryFun H 0 - z) :=
  LogDerivFTC.ftc_log_pieceFM (by norm_num) (ref1_cd z H).continuous.continuousOn
    (fun t _ => (ref1_cd z H).differentiable (by norm_num) |>.differentiableAt)
    ((ref1_cd z H).continuous_deriv le_top).continuousOn
    (fun t _ => ref1_slit z H hz t)
    (fun t ht => ⟨ref1_eq z H (by linarith [ht.2]),
      Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem
        (Iio_mem_nhds (by linarith [ht.2] : t < 1/5))
        fun s hs => ref1_eq z H hs.le)⟩)
    (ref1_eq z H (by norm_num)) (ref1_eq z H le_rfl)

private theorem seg5F (z : ℂ) (H : ℝ) (hz : z.im < H) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - z) t /
      (fdBoundaryFun H t - z)) volume (4/5) 1 ∧
    ∫ t in (4/5 : ℝ)..1, deriv (fun s => fdBoundaryFun H s - z) t /
      (fdBoundaryFun H t - z) =
      Complex.log (fdBoundaryFun H 1 - z) - Complex.log (fdBoundaryFun H (4/5) - z) :=
  LogDerivFTC.ftc_log_pieceFM (by norm_num) (ref5_cd z H).continuous.continuousOn
    (fun t _ => (ref5_cd z H).differentiable (by norm_num) |>.differentiableAt)
    ((ref5_cd z H).continuous_deriv le_top).continuousOn
    (fun t _ => ref5_slit z H hz t)
    (fun t ht => ⟨ref5_eq z H (by linarith [ht.1]),
      Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem
        (Ioi_mem_nhds (by linarith [ht.1] : 4/5 < t))
        fun s hs => ref5_eq z H hs)⟩)
    (by
      unfold ref5
      rw [fdBoundaryFun_at_four_fifths]
      apply Complex.ext
      · push_cast
        simp [sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, sub_im]
        ring
      · push_cast
        simp [sub_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, add_im, sub_im])
    (ref5_eq z H (by norm_num))

private theorem seg4F (z : ℂ) (H : ℝ) (hz : -1/2 < z.re) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - z) t /
      (fdBoundaryFun H t - z)) volume (3/5) (4/5) ∧
    ∫ t in (3/5 : ℝ)..(4/5), deriv (fun s => fdBoundaryFun H s - z) t /
      (fdBoundaryFun H t - z) =
      Complex.log (-(fdBoundaryFun H (4/5) - z)) -
      Complex.log (-(fdBoundaryFun H (3/5) - z)) := by
  have hae : ∀ᵐ t ∂volume, t ∈ Ι (3/5 : ℝ) (4/5) →
      deriv (fun s => fdBoundaryFun H s - z) t / (fdBoundaryFun H t - z) =
      deriv (ref4n z H) t / ref4n z H t := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (4/5 : ℝ))] with t hne hm
    rw [uIoc_of_le (by norm_num : (3:ℝ)/5 ≤ 4/5)] at hm
    have hlt : t < 4/5 := lt_of_le_of_ne hm.2 (fun h => hne (mem_singleton_iff.mpr h))
    rw [show ref4n z H t = -(fdBoundaryFun H t - z) from (ref4n_eq z H hm.1 hlt.le).symm,
      show deriv (ref4n z H) t = deriv (fun s => -(fdBoundaryFun H s - z)) t from
        (Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem
          (Filter.inter_mem (Ioi_mem_nhds hm.1) (Iio_mem_nhds hlt))
          fun s ⟨hs3, hs4⟩ => ref4n_eq z H (mem_Ioi.mp hs3)
            (mem_Iio.mp hs4).le)).symm]
    have hd : deriv (fun s => -(fdBoundaryFun H s - z)) t =
        -(deriv (fun s => fdBoundaryFun H s - z) t) := by
      rw [show (fun s => -(fdBoundaryFun H s - z)) = (-(fun s => fdBoundaryFun H s - z)) by
        ext
        simp]
      exact deriv.neg
    rw [hd, neg_div_neg_eq]
  have hp := LogDerivFTC.ftc_log_pieceFM (by norm_num : (3:ℝ)/5 ≤ 4/5)
    (ref4n_cd z H).continuous.continuousOn
    (fun t _ => (ref4n_cd z H).differentiable (by norm_num) |>.differentiableAt)
    ((ref4n_cd z H).continuous_deriv le_top).continuousOn
    (fun t _ => ref4n_slit z H hz t)
    (fun t _ => ⟨rfl, rfl⟩) rfl rfl
  refine ⟨hp.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hae.mono fun t ht hm => (ht hm).symm)), ?_⟩
  rw [intervalIntegral.integral_congr_ae hae, hp.2]
  congr 1
  · rw [← ref4n_eq z H (by norm_num : (3:ℝ)/5 < 4/5) le_rfl]
  · congr 1
    unfold ref4n
    rw [fdBoundaryFun_at_three_fifths]
    simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    apply Complex.ext <;> push_cast <;> simp [neg_re, neg_im, add_re, sub_re, mul_re, mul_im,
      ofReal_re, ofReal_im, I_re, I_im, add_im, sub_im] <;> (ring_nf; try tauto)

private lemma fdArcAngle_contDiff' : ContDiff ℝ ⊤ fdArcAngle := by
  unfold fdArcAngle
  fun_prop

private def arcRef (z : ℂ) (t : ℝ) : ℂ := exp (↑(fdArcAngle t) * I) - z

private lemma arcRef_cd (z : ℂ) : ContDiff ℝ ⊤ (arcRef z) := by
  unfold arcRef
  exact (Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp fdArcAngle_contDiff').mul contDiff_const)).sub
    contDiff_const

private lemma arcRef_eq (z : ℂ) (H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    fdBoundaryFun H t - z = arcRef z t := by
  unfold arcRef
  rw [fdBoundaryFun_arc_eq_exp H t ht1 ht2]

private lemma arcRef_eq15 (z : ℂ) (H : ℝ) :
    fdBoundaryFun H (1/5) - z = arcRef z (1/5) := by
  unfold arcRef
  rw [fdArcAngle_at_one_fifth, fdBoundaryFun_at_one_fifth]
  simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

private lemma arcRef_eq35 (z : ℂ) (H : ℝ) :
    fdBoundaryFun H (3/5) - z = arcRef z (3/5) := by
  unfold arcRef
  rw [fdBoundaryFun_at_three_fifths]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  rw [show fdArcAngle (3/5) = Real.pi - Real.pi / 3 from by unfold fdArcAngle; ring,
    exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

private lemma arcRef_ee (z : ℂ) (H : ℝ) {t : ℝ} (ht1 : 1/5 < t) (ht2 : t < 3/5) :
    (fun s => fdBoundaryFun H s - z) =ᶠ[𝓝 t] arcRef z :=
  Filter.eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht2))
    fun _ ⟨hs1, hs2⟩ => arcRef_eq z H (mem_Ioi.mp hs1) (mem_Iio.mp hs2).le

private lemma arcRef_slit_nonpos {z : ℂ}
    (hz_norm : 1 < ‖z‖) (hz_re : z.re ≤ 0) (_hz_im : 0 < z.im)
    {t : ℝ} (_ht1 : 1/5 ≤ t) (_ht2 : t ≤ 3/5) :
    arcRef z t ∈ slitPlane := by
  unfold arcRef
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, mem_slitPlane_iff]
  simp only [add_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, add_zero, mul_one, add_im, sub_im, mul_im, zero_add]
  by_cases him : Real.sin (fdArcAngle t) - z.im = 0
  · left
    have hnsq := Complex.one_lt_normSq_iff.mpr hz_norm
    simp only [Complex.normSq_apply] at hnsq
    have hsin : Real.sin (fdArcAngle t) = z.im := by linarith
    have hcos_sq : Real.cos (fdArcAngle t) ^ 2 = 1 - z.im ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq (fdArcAngle t)]
    have : Real.cos (fdArcAngle t) ^ 2 < z.re ^ 2 := by nlinarith
    have : |Real.cos (fdArcAngle t)| < -z.re := by
      rw [show -z.re = |z.re| from (abs_of_nonpos hz_re).symm]
      exact abs_lt_of_sq_lt (by nlinarith [sq_abs (Real.cos (fdArcAngle t)), sq_abs z.re])
    linarith [neg_abs_le (Real.cos (fdArcAngle t))]
  · right
    exact him

private lemma arcRef_neg_slit_pos {z : ℂ}
    (hz_norm : 1 < ‖z‖) (hz_re : 0 < z.re) (_hz_im : 0 < z.im)
    {t : ℝ} (_ht1 : 1/5 ≤ t) (_ht2 : t ≤ 3/5) :
    -(arcRef z t) ∈ slitPlane := by
  unfold arcRef
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, mem_slitPlane_iff]
  simp only [neg_sub, sub_re, sub_im, ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im,
    I_re, I_im, mul_zero, sub_zero, add_zero, mul_one, zero_add]
  by_cases him : z.im - Real.sin (fdArcAngle t) = 0
  · left
    have hnsq := Complex.one_lt_normSq_iff.mpr hz_norm
    simp only [Complex.normSq_apply] at hnsq
    have hsin : Real.sin (fdArcAngle t) = z.im := by linarith
    have hcos_sq : Real.cos (fdArcAngle t) ^ 2 = 1 - z.im ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq (fdArcAngle t)]
    have : Real.cos (fdArcAngle t) ^ 2 < z.re ^ 2 := by nlinarith
    have : |Real.cos (fdArcAngle t)| < z.re := by
      rw [show z.re = |z.re| from (abs_of_pos hz_re).symm]
      exact abs_lt_of_sq_lt (by nlinarith [sq_abs (Real.cos (fdArcAngle t)), sq_abs z.re])
    linarith [le_abs_self (Real.cos (fdArcAngle t))]
  · right
    exact him

private theorem arcF_standard {z : ℂ} (hz_norm : 1 < ‖z‖)
    (_hz_re : |z.re| < 1/2) (hz_re_le : z.re ≤ 0) (hz_im : 0 < z.im) (H : ℝ) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - z) t /
      (fdBoundaryFun H t - z)) volume (1/5) (3/5) ∧
    ∫ t in (1/5 : ℝ)..(3/5), deriv (fun s => fdBoundaryFun H s - z) t /
      (fdBoundaryFun H t - z) =
      Complex.log (fdBoundaryFun H (3/5) - z) -
      Complex.log (fdBoundaryFun H (1/5) - z) :=
  LogDerivFTC.ftc_log_pieceFM (by norm_num) (arcRef_cd z).continuous.continuousOn
    (fun t _ => (arcRef_cd z).differentiable (by norm_num) |>.differentiableAt)
    ((arcRef_cd z).continuous_deriv le_top).continuousOn
    (fun t ht => arcRef_slit_nonpos hz_norm hz_re_le hz_im ht.1 ht.2)
    (fun t ht => ⟨arcRef_eq z H (by linarith [ht.1]) (by linarith [ht.2]),
      (arcRef_ee z H (by linarith [ht.1]) (by linarith [ht.2])).deriv_eq⟩)
    (arcRef_eq15 z H) (arcRef_eq35 z H)

/-- Branch correction: `log(-w) = log(w) + πi` when `w.im < 0`. -/
private lemma log_neg_add_pi_of_im_neg {w : ℂ} (him : w.im < 0) :
    Complex.log (-w) = Complex.log w + ↑Real.pi * I := by
  change ↑(Real.log ‖-w‖) + ↑((-w).arg) * I =
    ↑(Real.log ‖w‖) + ↑(w.arg) * I + ↑Real.pi * I
  simp only [norm_neg]
  rw [arg_neg_eq_arg_add_pi_of_im_neg him]
  push_cast
  ring

/-- Branch correction: `log(-w) = log(w) - πi` when `0 < w.im`. -/
private lemma log_neg_sub_pi_of_im_pos {w : ℂ} (him : 0 < w.im) :
    Complex.log (-w) = Complex.log w - ↑Real.pi * I := by
  change ↑(Real.log ‖-w‖) + ↑((-w).arg) * I =
    ↑(Real.log ‖w‖) + ↑(w.arg) * I - ↑Real.pi * I
  simp only [norm_neg]
  rw [arg_neg_eq_arg_sub_pi_of_im_pos him]
  push_cast
  ring

/-- At the arc endpoints `t = 1/5` and `t = 3/5`, the imaginary part of `γ(t) - z` is
negative for strict interior `z`. -/
private lemma arcEndpoint_im_neg {z : ℂ}
    (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : 0 < z.im)
    (H : ℝ) (p : ℝ) (hp : p ∈ ({1/5, 3/5} : Set ℝ)) :
    (fdBoundaryFun H p - z).im < 0 := by
  rcases hp with rfl | rfl
  · have : (fdBoundaryFun H (1/5)).im = Real.sqrt 3 / 2 := by
      rw [fdBoundaryFun_at_one_fifth]
      simp [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk,
        add_im, mul_im, I_re, I_im]
    simp only [sub_im]
    linarith [im_gt_sqrt3_div_two_of_interior hz_norm hz_re hz_im]
  · have : (fdBoundaryFun H (3/5)).im = Real.sqrt 3 / 2 := by
      rw [fdBoundaryFun_at_three_fifths]
      simp [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
        add_im, neg_im, mul_im, I_re, I_im]
    simp only [sub_im]
    linarith [im_gt_sqrt3_div_two_of_interior hz_norm hz_re hz_im]

private theorem arcF_negated {z : ℂ} (hz_norm : 1 < ‖z‖)
    (hz_re : |z.re| < 1/2) (hz_re_pos : 0 < z.re) (hz_im : 0 < z.im) (H : ℝ) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - z) t /
      (fdBoundaryFun H t - z)) volume (1/5) (3/5) ∧
    ∫ t in (1/5 : ℝ)..(3/5), deriv (fun s => fdBoundaryFun H s - z) t /
      (fdBoundaryFun H t - z) =
      Complex.log (fdBoundaryFun H (3/5) - z) -
      Complex.log (fdBoundaryFun H (1/5) - z) := by
  have hp := LogDerivFTC.ftc_log_neg_on_segment (by norm_num : (1:ℝ)/5 ≤ 3/5)
    (arcRef_cd z).continuous.continuousOn
    (fun t _ => (arcRef_cd z).differentiable (by norm_num) |>.differentiableAt)
    ((arcRef_cd z).continuous_deriv le_top).continuousOn
    (fun t ht => arcRef_neg_slit_pos hz_norm hz_re_pos hz_im ht.1 ht.2)
  have hae : ∀ᵐ t ∂volume, t ∈ Ι (1/5 : ℝ) (3/5) →
      deriv (fun s => fdBoundaryFun H s - z) t / (fdBoundaryFun H t - z) =
      deriv (arcRef z) t / arcRef z t := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (3/5 : ℝ))] with t hne hm
    rw [uIoc_of_le (by norm_num : (1:ℝ)/5 ≤ 3/5)] at hm
    have hlt : t < 3/5 := lt_of_le_of_ne hm.2 (fun h => hne (mem_singleton_iff.mpr h))
    rw [arcRef_eq z H (by linarith [hm.1]) hlt.le,
      (arcRef_ee z H (by linarith [hm.1]) hlt).deriv_eq]
  have hint := hp.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hae.mono fun t ht hm => (ht hm).symm))
  refine ⟨hint, ?_⟩
  rw [intervalIntegral.integral_congr_ae hae, hp.2, arcRef_eq15 z H, arcRef_eq35 z H]
  have him1 := arcRef_eq15 z H ▸ arcEndpoint_im_neg hz_norm hz_re hz_im H _ (Or.inl rfl)
  have him3 := arcRef_eq35 z H ▸ arcEndpoint_im_neg hz_norm hz_re hz_im H _ (Or.inr rfl)
  rw [log_neg_add_pi_of_im_neg him3, log_neg_add_pi_of_im_neg him1]
  ring

private theorem arcF {z : ℂ} (hz_norm : 1 < ‖z‖)
    (hz_re : |z.re| < 1/2) (hz_im : 0 < z.im) (H : ℝ) :
    IntervalIntegrable (fun t => deriv (fun s => fdBoundaryFun H s - z) t /
      (fdBoundaryFun H t - z)) volume (1/5) (3/5) ∧
    ∫ t in (1/5 : ℝ)..(3/5), deriv (fun s => fdBoundaryFun H s - z) t /
      (fdBoundaryFun H t - z) =
      Complex.log (fdBoundaryFun H (3/5) - z) -
      Complex.log (fdBoundaryFun H (1/5) - z) := by
  rcases le_or_gt z.re 0 with h | h
  · exact arcF_standard hz_norm hz_re h hz_im H
  · exact arcF_negated hz_norm hz_re h hz_im H

private lemma bc35 {z : ℂ} {H : ℝ}
    (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : 0 < z.im) :
    Complex.log (-(fdBoundaryFun H (3/5) - z)) =
      Complex.log (fdBoundaryFun H (3/5) - z) + ↑Real.pi * I :=
  log_neg_add_pi_of_im_neg (arcEndpoint_im_neg hz_norm hz_re hz_im H _ (Or.inr rfl))

private lemma bc45 {z : ℂ} {H : ℝ} (hz_im : z.im < H) :
    Complex.log (-(fdBoundaryFun H (4/5) - z)) =
      Complex.log (fdBoundaryFun H (4/5) - z) - ↑Real.pi * I := by
  refine log_neg_sub_pi_of_im_pos ?_
  have : (fdBoundaryFun H (4/5)).im = H := by
    rw [fdBoundaryFun_at_four_fifths]
    simp [add_im, neg_im, ofReal_im, mul_im, I_re, I_im]
  simp only [sub_im]
  linarith

private theorem ftc_full {z : ℂ} {H : ℝ}
    (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : 0 < z.im) (hzH : z.im < H) :
    ∫ t in (0 : ℝ)..1,
        (fdBoundaryFun H t - z)⁻¹ * deriv (fdBoundaryFun H) t = -(2 * ↑Real.pi * I) := by
  have hconv : ∀ t, (fdBoundaryFun H t - z)⁻¹ * deriv (fdBoundaryFun H) t =
      deriv (fun s => fdBoundaryFun H s - z) t / (fdBoundaryFun H t - z) := by
    intro t
    rw [show (fun s => fdBoundaryFun H s - z) = (fun s => fdBoundaryFun H s + (-z)) by
      ext
      ring, deriv_add_const, div_eq_mul_inv, mul_comm]
  simp_rw [hconv]
  have p1 := seg1F z H (by linarith [abs_lt.mp hz_re])
  have p23 := arcF hz_norm hz_re hz_im H
  have p4 := seg4F z H (by linarith [abs_lt.mp hz_re])
  have p5 := seg5F z H hzH
  set F : ℝ → ℂ := fun t => deriv (fun s => fdBoundaryFun H s - z) t / (fdBoundaryFun H t - z)
  have h13 : ∫ t in (0 : ℝ)..(3/5), F t = Complex.log (fdBoundaryFun H (3/5) - z) -
      Complex.log (fdBoundaryFun H 0 - z) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals p1.1 p23.1, p1.2, p23.2]
    ring
  have h4 : ∫ t in (3/5 : ℝ)..(4/5), F t = Complex.log (fdBoundaryFun H (4/5) - z) -
      Complex.log (fdBoundaryFun H (3/5) - z) - 2 * ↑Real.pi * I := by
    rw [p4.2, bc45 hzH, bc35 hz_norm hz_re hz_im]
    ring
  calc ∫ t in (0 : ℝ)..1, F t
      = (∫ t in (0 : ℝ)..(4/5), F t) + (∫ t in (4/5 : ℝ)..1, F t) :=
        (intervalIntegral.integral_add_adjacent_intervals
          ((p1.1.trans p23.1).trans p4.1) p5.1).symm
    _ = ((∫ t in (0 : ℝ)..(3/5), F t) + (∫ t in (3/5 : ℝ)..(4/5), F t)) +
        (∫ t in (4/5 : ℝ)..1, F t) := by
        congr 1
        exact (intervalIntegral.integral_add_adjacent_intervals
          (p1.1.trans p23.1) p4.1).symm
    _ = _ := by
        rw [h13, h4, p5.2, fdBoundaryFun_closed H]
        ring

private theorem xfer {z : ℂ} {H : ℝ}
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t) :
    γ.contourIntegral (fun w => (w - z)⁻¹) =
    ∫ t in (0 : ℝ)..1, (fdBoundaryFun H t - z)⁻¹ * deriv (fdBoundaryFun H) t := by
  unfold PiecewiseC1Path.contourIntegral
  apply intervalIntegral.integral_congr_ae
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ))] with t hne hm
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hm
  have ht01 : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨by linarith [hm.1], lt_of_le_of_ne hm.2 (fun h => hne (mem_singleton_iff.mpr h))⟩
  have hee : γ.toPath.extend =ᶠ[𝓝 t] fdBoundaryFun H :=
    Filter.eventually_of_mem (Ioo_mem_nhds ht01.1 ht01.2) fun s hs =>
      hγ s (Ioo_subset_Icc_self hs)
  change (γ.extendedPath t - z)⁻¹ * deriv γ.toPath.extend t =
    (fdBoundaryFun H t - z)⁻¹ * deriv (fdBoundaryFun H) t
  rw [show γ.extendedPath t = γ.toPath.extend t from rfl,
    hγ t (Ioo_subset_Icc_self ht01), hee.deriv_eq]

/-- **Interior contour integral = -2πi** for the FD boundary. -/
theorem fdBoundary_contourIntegral_interior_eq {H : ℝ}
    (_hH : H > Real.sqrt 3 / 2) {z : ℂ} (hz : FDStrictInterior z H)
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t) :
    γ.contourIntegral (fun w => (w - z)⁻¹) = -(2 * ↑Real.pi * I) := by
  rw [xfer hγ]
  exact ftc_full hz.norm_gt hz.re_abs_lt hz.im_pos hz.im_lt

/-- **Interior winding number = -1**. -/
theorem fdBoundary_interior_winding_complete {H : ℝ}
    (hH : H > Real.sqrt 3 / 2) {z : ℂ} (hz : FDStrictInterior z H)
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t) :
    HasGeneralizedWindingNumber γ z (-1) :=
  hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral γ hγ
    hz.norm_gt hz.re_abs_lt hz.im_pos hz.im_lt
    (fdBoundary_contourIntegral_interior_eq hH hz hγ)

end
