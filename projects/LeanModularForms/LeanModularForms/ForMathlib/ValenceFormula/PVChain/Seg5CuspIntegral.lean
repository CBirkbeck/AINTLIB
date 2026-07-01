/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ValenceFormula.PVChain.Helpers
import LeanModularForms.ForMathlib.ModularInvariance
import LeanModularForms.ForMathlib.ValenceFormula.Boundary.Smooth
import LeanModularForms.ForMathlib.ValenceFormula.Boundary.Bounds
import LeanModularForms.ForMathlib.SegmentFTC
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Seg5 Cusp Integral

This file contains the cusp-function infrastructure needed to prove that the
horizontal edge integral (seg5) of `logDeriv(f)` equals `2πi · orderAtCusp'(f)`.

The argument proceeds in two stages:

**Stage 1** (`seg5_integral_eq_circleIntegral_H`): Change of variables from the
parametric integral along seg5 to a circle integral in the q-plane.

**Stage 2** (`circleIntegral_logDeriv_cuspFunction_of_radius`): Compute the
circle integral using the factorization `F(q) = q^m · g(q)`:
- `∮ m/q dq = m · 2πi` from `circleIntegral_const_mul_inv`
- `∮ logDeriv(g) dq = 0` from `circleIntegral_logDeriv_regular_zero`

## Main Results

* `seg5_logDeriv_integral_eq_H` — the logDeriv integral along seg5 at height H
    equals `2πi · orderAtCusp' f`.
* `seg5_logDeriv_integral_value_bridge` — bridge to the form used in
    `PVChain.Assembly`.
-/

open Complex MeasureTheory Topology CongruenceSubgroup
open scoped Real UpperHalfPlane MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-- Convert `AnalyticOnNhd` on `Metric.eball 0 1` to `Metric.ball 0 1`. -/
private lemma eball_one_eq_ball {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F (Metric.eball 0 1)) :
    AnalyticOnNhd ℂ F (Metric.ball 0 1) :=
  hF.mono fun _x hx ↦ by
    simpa [Metric.mem_eball, Metric.mem_ball, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
      ← NNReal.coe_lt_coe, coe_nnnorm] using hx

/-- Modular-form wrapper for `UpperHalfPlane.hasFPowerSeries_cuspFunction`:
the q-expansion formal multilinear series is a power-series representation of the
cuspFunction on the unit ball. -/
private lemma hasFPowerSeries_cuspFunction_SL (g : ModularForm (Gamma 1) k) :
    HasFPowerSeriesOnBall (UpperHalfPlane.cuspFunction 1 g)
      (UpperHalfPlane.qExpansionFormalMultilinearSeries 1 g) 0 1 :=
  have _hMC : ModularFormClass (ModularForm (Gamma 1) k) 𝒮ℒ k :=
    Gamma_one_coe_eq_SL ▸ inferInstance
  UpperHalfPlane.hasFPowerSeries_cuspFunction g one_pos
    (ModularFormClass.analyticAt_cuspFunction_zero g one_pos one_mem_strictPeriods_SL)
    (UpperHalfPlane.hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex g one_mem_strictPeriods_SL)
      (ModularFormClass.holo g) (ModularFormClass.bdd_at_infty g))

private lemma qExpFMS_ne_zero (hf : f ≠ 0) :
    UpperHalfPlane.qExpansionFormalMultilinearSeries 1 f ≠ 0 := by
  intro h
  have hMC : ModularFormClass (ModularForm (Gamma 1) k) 𝒮ℒ k :=
    Gamma_one_coe_eq_SL ▸ inferInstance
  have hp := hasFPowerSeries_cuspFunction_SL f
  have hp0 : HasFPowerSeriesOnBall (UpperHalfPlane.cuspFunction (1 : ℝ) f)
      (0 : FormalMultilinearSeries ℂ ℂ ℂ) 0 1 := h ▸ hp
  have hF_eq_zero : Set.EqOn (UpperHalfPlane.cuspFunction (1 : ℝ) f) 0
      (Metric.ball 0 1) :=
    (eball_one_eq_ball hp.analyticOnNhd).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (Convex.isPreconnected (convex_ball 0 1)) (Metric.mem_ball_self one_pos)
      hp0.eventually_eq_zero
  refine hf (ModularForm.ext fun τ ↦ ?_)
  rw [← SlashInvariantFormClass.eq_cuspFunction f τ
    one_mem_strictPeriods_SL (by norm_num : (1:ℝ) ≠ 0)]
  exact hF_eq_zero (by simpa using τ.norm_qParam_lt_one 1)

/-- Auxiliary: the FMS order equals `(orderAtCusp' f).toNat`. -/
private lemma qExpFMS_order_eq (hf : f ≠ 0) :
    (UpperHalfPlane.qExpansionFormalMultilinearSeries 1 f).order =
    (orderAtCusp' f).toNat := by
  set p := UpperHalfPlane.qExpansionFormalMultilinearSeries 1 f
  set ps := UpperHalfPlane.qExpansion 1 f
  have h_norm : ∀ n, ‖p n‖ = ‖ps.coeff n‖ :=
    UpperHalfPlane.qExpansionFormalMultilinearSeries_apply_norm (f := f)
  have h_zero_iff : ∀ n, p n = 0 ↔ ps.coeff n = 0 := by
    intro n
    rw [← norm_eq_zero, h_norm, norm_eq_zero]
  have hps_ne : ps ≠ 0 := fun h ↦ qExpFMS_ne_zero f hf <|
    FormalMultilinearSeries.ext fun n ↦ (h_zero_iff n).mpr (by rw [h]; simp)
  unfold orderAtCusp'
  simp only [Int.toNat_natCast]
  have hps_order : ps.order = ↑ps.order.toNat :=
    (ENat.coe_toNat_eq_self.mpr (PowerSeries.order_eq_top.not.mpr hps_ne)).symm
  set m := ps.order.toNat
  have hm := (PowerSeries.order_eq_nat.mp (by exact_mod_cast hps_order) :
    ps.coeff m ≠ 0 ∧ ∀ i, i < m → ps.coeff i = 0)
  have hp_lt : ∀ i, i < m → p i = 0 := fun i hi ↦ (h_zero_iff i).mpr (hm.2 i hi)
  change p.order = m
  unfold FormalMultilinearSeries.order
  have hm_mem : m ∈ {n | p n ≠ 0} := (h_zero_iff m).not.mpr hm.1
  refine le_antisymm (Nat.sInf_le hm_mem) ?_
  by_contra h_lt
  push Not at h_lt
  exact Nat.sInf_mem ⟨m, hm_mem⟩ (hp_lt _ h_lt)

/-- The cuspFunction factors as `q^m * g(q)` on the open unit ball,
where `m = orderAtCusp' f` and `g` is differentiable with `g(0) ≠ 0`. -/
private lemma cuspFunction_factored (hf : f ≠ 0) :
    ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (Metric.ball 0 1) ∧
      g 0 ≠ 0 ∧
      ∀ q ∈ Metric.ball (0 : ℂ) 1,
        UpperHalfPlane.cuspFunction (1 : ℝ) f q =
        q ^ (orderAtCusp' f).toNat * g q := by
  set F := UpperHalfPlane.cuspFunction (1 : ℝ) f
  set p := UpperHalfPlane.qExpansionFormalMultilinearSeries 1 f
  have hp : HasFPowerSeriesOnBall F p 0 1 := hasFPowerSeries_cuspFunction_SL f
  have hp_order : p.order = (orderAtCusp' f).toNat := qExpFMS_order_eq f hf
  set g₀ := (Function.swap dslope 0)^[p.order] F
  have hF_analytic : AnalyticOnNhd ℂ F (Metric.ball 0 1) := eball_one_eq_ball hp.analyticOnNhd
  have hg_diff : DifferentiableOn ℂ g₀ (Metric.ball 0 1) := by
    suffices ∀ (k : ℕ), DifferentiableOn ℂ ((Function.swap dslope 0)^[k] F)
        (Metric.ball 0 1) from this p.order
    intro k
    induction k with
    | zero => simpa using hF_analytic.differentiableOn
    | succ j ih =>
      simp only [Function.iterate_succ', Function.comp_def]
      exact (Complex.differentiableOn_dslope (Metric.ball_mem_nhds 0 one_pos)).mpr ih
  have hg_ne : g₀ 0 ≠ 0 :=
    hp.hasFPowerSeriesAt.iterate_dslope_fslope_ne_zero (qExpFMS_ne_zero f hf)
  have hg_analytic : AnalyticOnNhd ℂ g₀ (Metric.ball 0 1) :=
    fun z hz ↦ hg_diff.analyticAt (Metric.isOpen_ball.mem_nhds hz)
  have hF_eq : Set.EqOn F (fun z ↦ (z - 0) ^ p.order • g₀ z) (Metric.ball 0 1) :=
    hF_analytic.eqOn_of_preconnected_of_eventuallyEq
      (fun z hz ↦ ((analyticAt_id.sub analyticAt_const).pow p.order).smul (hg_analytic z hz))
      (Convex.isPreconnected (convex_ball 0 1)) (Metric.mem_ball_self one_pos)
      (Filter.Eventually.of_forall hp.hasFPowerSeriesAt.eq_pow_order_mul_iterate_dslope)
  refine ⟨g₀, hg_diff, hg_ne, fun q hq ↦ ?_⟩
  have := hF_eq hq
  simp only [sub_zero, smul_eq_mul] at this
  rw [this, hp_order]

omit f hf in
/-- `∮ (m : ℂ) * q⁻¹ dq = m * 2πi` for nonzero radius. -/
private lemma circleIntegral_const_mul_inv (m : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (∮ q in C(0, R), m * q⁻¹) = m * (2 * ↑Real.pi * I) := by
  rw [circleIntegral.integral_const_mul, show (fun q : ℂ ↦ q⁻¹) = (fun q ↦ (q - 0)⁻¹) by simp,
    circleIntegral.integral_sub_center_inv 0 hR]

omit f hf in
/-- `∮ logDeriv(g) dq = 0` when `g` is differentiable on ball(0,1) and nonvanishing
on closedBall(0,R), where `0 < R < 1`. Uses Cauchy-Goursat: `logDeriv(g) = g'/g`
is holomorphic on ball(0,R) since `g` is differentiable and nonvanishing there. -/
private lemma circleIntegral_logDeriv_regular_zero
    (g : ℂ → ℂ) {R : ℝ} (hR_pos : 0 < R) (hR_lt : R < 1)
    (hg_diff : DifferentiableOn ℂ g (Metric.ball 0 1))
    (hg_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) R, g q ≠ 0) :
    (∮ q in C(0, R), logDeriv g q) = 0 := by
  have h_cb_sub : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball 0 1 :=
    Metric.closedBall_subset_ball hR_lt
  have hg_cont : ContinuousOn (logDeriv g) (Metric.closedBall (0 : ℂ) R) :=
    ContinuousOn.div
      (((hg_diff.contDiffOn (n := 1) Metric.isOpen_ball).continuousOn_deriv_of_isOpen
        Metric.isOpen_ball le_rfl).mono h_cb_sub)
      (hg_diff.continuousOn.mono h_cb_sub) hg_nonvan
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR_pos.le
    Set.countable_empty hg_cont (fun z hz ↦ ?_)
  have hz1 := (Metric.ball_subset_ball hR_lt.le) hz.1
  exact ((hg_diff.deriv Metric.isOpen_ball).differentiableAt
    (Metric.isOpen_ball.mem_nhds hz1)).div
    (hg_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hz1))
    (hg_nonvan z (Metric.ball_subset_closedBall hz.1))

omit f hf in
/-- `seg5_q_radius_H H > 0` for any `H`. -/
lemma seg5_q_radius_H_pos (H : ℝ) : 0 < seg5_q_radius_H H :=
  Real.exp_pos _

omit f hf in
/-- `seg5_q_radius_H H < 1` when `H > 0`. -/
private lemma seg5_q_radius_H_lt_one' {H : ℝ} (hH : 0 < H) : seg5_q_radius_H H < 1 :=
  Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])

/-- Circle integral of logDeriv(cuspFunction) at any radius `0 < R < 1`.

This is the radius-parameterized version. The factorization `F(q) = q^m · g(q)` gives:
`∮ logDeriv(F) = m · ∮ 1/q + ∮ logDeriv(g) = m · 2πi + 0`. -/
lemma circleIntegral_logDeriv_cuspFunction_of_radius (hf : f ≠ 0)
    {R : ℝ} (hR_pos : 0 < R) (hR_lt : R < 1) (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) R,
        q ≠ 0 → UpperHalfPlane.cuspFunction (1 : ℝ) f q ≠ 0) :
    (∮ q in C(0, R),
      logDeriv (UpperHalfPlane.cuspFunction (1 : ℝ) f) q) =
    2 * ↑Real.pi * I * ↑(orderAtCusp' f) := by
  set F := UpperHalfPlane.cuspFunction (1 : ℝ) f with hF_def
  set m := (orderAtCusp' f).toNat
  obtain ⟨g, hg_diff, hg_ne, hFg⟩ := cuspFunction_factored f hf
  have hg_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) R, g q ≠ 0 := fun q hq ↦ by
    by_cases hq0 : q = 0
    · exact hq0 ▸ hg_ne
    · have hF_ne := hcusp_nonvan q hq hq0
      rw [hF_def, hFg q (Metric.closedBall_subset_ball hR_lt hq)] at hF_ne
      exact right_ne_zero_of_mul hF_ne
  have h_split : ∀ q, q ∈ Metric.sphere (0 : ℂ) R →
      logDeriv F q = ↑m / q + logDeriv g q := by
    intro q hq
    have hq_ne : q ≠ 0 := fun h ↦ by
      simp only [h, Metric.mem_sphere, dist_self] at hq
      exact hR_pos.ne' hq.symm
    have hq_ball : q ∈ Metric.ball (0 : ℂ) 1 :=
      Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball hR_lt) hq
    have hF_eq : F =ᶠ[𝓝 q] (fun z ↦ z ^ m * g z) :=
      (Metric.isOpen_ball.eventually_mem hq_ball).mono hFg
    simp only [logDeriv_apply, hF_eq.eq_of_nhds, hF_eq.deriv.eq_of_nhds]
    have h_hd : HasDerivAt (fun z ↦ z ^ m * g z) (↑m * q ^ (m - 1) * g q + q ^ m * deriv g q) q :=
      (hasDerivAt_pow m q).mul
        (hg_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hq_ball)).hasDerivAt
    rw [h_hd.deriv]
    have hqm_ne : q ^ m ≠ 0 := pow_ne_zero m hq_ne
    field_simp
    rcases m with _ | n
    · ring
    · rw [Nat.succ_sub_one]
      have hgq_ne := hg_nonvan q (Metric.sphere_subset_closedBall hq)
      field_simp
      ring
  have hci_inv : CircleIntegrable (fun q ↦ (↑m : ℂ) * q⁻¹) 0 R := by
    refine (continuousOn_const.mul (ContinuousOn.inv₀ continuousOn_id fun z hz ↦ ?_)).circleIntegrable
      hR_pos.le
    simp only [Metric.mem_sphere, dist_zero_right] at hz
    exact norm_ne_zero_iff.mp (show ‖z‖ ≠ 0 by linarith)
  have hci_logDeriv : CircleIntegrable (fun q ↦ logDeriv g q) 0 R := by
    refine ContinuousOn.circleIntegrable hR_pos.le ?_
    have h_sphere_sub : Metric.sphere (0 : ℂ) R ⊆ Metric.ball 0 1 :=
      Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball hR_lt)
    change ContinuousOn (fun q ↦ deriv g q / g q) (Metric.sphere 0 R)
    exact ContinuousOn.div
      (((hg_diff.contDiffOn (n := 1) Metric.isOpen_ball).continuousOn_deriv_of_isOpen
        Metric.isOpen_ball le_rfl).mono h_sphere_sub)
      (hg_diff.continuousOn.mono h_sphere_sub)
      fun q hq ↦ hg_nonvan q (Metric.sphere_subset_closedBall hq)
  have h_congr : (∮ q in C(0, R), logDeriv F q) =
      ∮ q in C(0, R), ((↑m : ℂ) * q⁻¹ + logDeriv g q) := by
    refine intervalIntegral.integral_congr fun θ _ ↦ ?_
    simp only
    rw [h_split _ (circleMap_mem_sphere 0 hR_pos.le θ), div_eq_mul_inv]
  have hm_cast : (m : ℂ) = ↑(orderAtCusp' f) := by
    simp [m, orderAtCusp', Int.toNat_natCast]
  rw [h_congr, circleIntegral.integral_add hci_inv hci_logDeriv,
      circleIntegral_const_mul_inv (↑m : ℂ) hR_pos.ne',
      circleIntegral_logDeriv_regular_zero g hR_pos hR_lt hg_diff hg_nonvan,
      add_zero, hm_cast]
  ring

omit f hf in
/-- The q-parameter along seg5 at height H equals a circle map value:
`qParam 1 (fdBoundary_seg5_H H t) = circleMap 0 (seg5_q_radius_H H) (2π(t - 9/2))`. -/
private lemma qParam_seg5_H_eq_circleMap (H : ℝ) (t : ℝ) :
    Function.Periodic.qParam (1 : ℝ) (fdBoundary_seg5_H H t) =
    circleMap 0 (seg5_q_radius_H H) (2 * Real.pi * (t - 9 / 2)) := by
  simp only [Function.Periodic.qParam, fdBoundary_seg5_H, seg5_q_radius_H, circleMap_zero]
  rw [show (2 : ℂ) * ↑Real.pi * I * ((↑t : ℂ) - 9 / 2 + ↑H * I) / (1 : ℝ) =
        ↑(-2 * Real.pi * H) + ↑(2 * Real.pi * (t - 9 / 2)) * I by
      push_cast; linear_combination (2 * ↑Real.pi * ↑H) * I_sq,
    Complex.exp_add, Complex.ofReal_exp]

omit f hf in
/-- The imaginary part of `fdBoundary_seg5_H H t` is `H`, which is positive when `H > 0`. -/
private lemma im_fdBoundary_seg5_H_pos {H : ℝ} (hH : 0 < H) (t : ℝ) :
    0 < (fdBoundary_seg5_H H t).im := by
  simp [fdBoundary_seg5_H]; linarith

omit hf in
/-- Chain rule for logDeriv along seg5 at height H:
`logDeriv(f ∘ ofComplex)(z(t)) = logDeriv(cuspFn)(q(z(t))) · 2πi · q(z(t))`. -/
private lemma logDeriv_modularForm_eq_logDeriv_cuspFn_mul_qderiv_H
    {H : ℝ} (hH : 0 < H) (t : ℝ) :
    logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5_H H t) =
    logDeriv (UpperHalfPlane.cuspFunction (1 : ℝ) f)
      (Function.Periodic.qParam (1 : ℝ) (fdBoundary_seg5_H H t)) *
    (2 * ↑Real.pi * I * Function.Periodic.qParam (1 : ℝ) (fdBoundary_seg5_H H t)) := by
  have hMC : ModularFormClass (ModularForm (Gamma 1) k) 𝒮ℒ k :=
    Gamma_one_coe_eq_SL ▸ inferInstance
  set z := fdBoundary_seg5_H H t
  set F := UpperHalfPlane.cuspFunction (1 : ℝ) f
  set q_fn := Function.Periodic.qParam (1 : ℝ)
  have hz_im : 0 < z.im := im_fdBoundary_seg5_H_pos hH t
  have h_eq_at : ∀ w : ℂ, 0 < w.im →
      modularFormCompOfComplex f w = (F ∘ q_fn) w := by
    intro w hw
    simp only [modularFormCompOfComplex, Function.comp_def]
    have h_ofC : (UpperHalfPlane.ofComplex w : ℂ) = w := by
      simp [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    have h_rw : F (q_fn w) = F (q_fn (↑(UpperHalfPlane.ofComplex w))) := by rw [h_ofC]
    rw [h_rw]
    exact (SlashInvariantFormClass.eq_cuspFunction f
      (UpperHalfPlane.ofComplex w) one_mem_strictPeriods_SL
      (by norm_num : (1:ℝ) ≠ 0)).symm
  have hq_norm : ‖q_fn z‖ < 1 := by
    simp only [q_fn, Function.Periodic.norm_qParam]
    rw [show (-2 * Real.pi * z.im / (1 : ℝ)) = -2 * Real.pi * z.im by ring]
    exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hF_diff : DifferentiableAt ℂ F (q_fn z) :=
    ModularFormClass.differentiableAt_cuspFunction f one_pos
      one_mem_strictPeriods_SL hq_norm
  have h_eq_nhd : modularFormCompOfComplex f =ᶠ[𝓝 z] F ∘ q_fn :=
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.eventually_mem hz_im).mono h_eq_at
  have h_logDeriv_eq : logDeriv (modularFormCompOfComplex f) z = logDeriv (F ∘ q_fn) z := by
    simp only [logDeriv_apply]
    rw [h_eq_nhd.eq_of_nhds, h_eq_nhd.deriv.eq_of_nhds]
  rw [h_logDeriv_eq, logDeriv_comp hF_diff
    Function.Periodic.differentiable_qParam.differentiableAt]
  have hderiv : deriv q_fn z = 2 * ↑Real.pi * I * q_fn z := by
    have hfun : q_fn = (fun z : ℂ ↦ cexp (2 * ↑Real.pi * I * z)) := by
      ext w; simp [q_fn, Function.Periodic.qParam, div_one]
    rw [hfun, (by simpa using (hasDerivAt_id z).const_mul (2 * ↑Real.pi * I) :
      HasDerivAt (fun z ↦ 2 * ↑Real.pi * I * z) (2 * ↑Real.pi * I) z).cexp.deriv]
    ring
  rw [hderiv]

omit hf in
/-- **Stage 1 (H)**: The parametric integral of logDeriv(f) along seg5 at height H
equals the circle integral of logDeriv(cuspFunction) at radius `seg5_q_radius_H H`. -/
lemma seg5_integral_eq_circleIntegral_H {H : ℝ} (hH : 0 < H) :
    ∫ t in (4:ℝ)..5,
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5_H H t) =
    ∮ q in C(0, seg5_q_radius_H H),
      logDeriv (UpperHalfPlane.cuspFunction (1 : ℝ) f) q := by
  set F := UpperHalfPlane.cuspFunction (1 : ℝ) f
  set R := seg5_q_radius_H H
  simp_rw [logDeriv_modularForm_eq_logDeriv_cuspFn_mul_qderiv_H f hH]
  simp_rw [qParam_seg5_H_eq_circleMap H]
  set g : ℝ → ℂ := fun θ ↦ deriv (circleMap 0 (↑R)) θ • logDeriv F (circleMap 0 ↑R θ)
    with hg_def
  have h_eq_integral : (∫ t in (4:ℝ)..5,
        logDeriv F (circleMap 0 R (2 * Real.pi * (t - 9 / 2))) *
        (2 * ↑Real.pi * I * circleMap 0 R (2 * Real.pi * (t - 9 / 2)))) =
      ∫ t in (4:ℝ)..5, (2 * Real.pi : ℝ) • g (2 * Real.pi * (t - 9 / 2)) := by
    congr 1
    ext t
    simp only [hg_def, smul_eq_mul]
    rw [deriv_circleMap, Complex.real_smul]
    push_cast
    ring
  rw [h_eq_integral]
  rw [intervalIntegral.integral_smul]
  have hpi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [show (fun t : ℝ ↦ g (2 * Real.pi * (t - 9 / 2))) =
    (fun t : ℝ ↦ g (2 * Real.pi * t + (2 * Real.pi * (-9 / 2)))) by
    ext t; ring_nf]
  rw [intervalIntegral.integral_comp_mul_add g hpi_ne,
    show (2 * Real.pi * 4 + 2 * Real.pi * (-9 / 2) : ℝ) = -Real.pi by ring,
    show (2 * Real.pi * 5 + 2 * Real.pi * (-9 / 2) : ℝ) = Real.pi by ring]
  rw [smul_inv_smul₀ hpi_ne]
  have h_periodic : Function.Periodic g (2 * Real.pi) := fun θ ↦ by
    simp only [hg_def, smul_eq_mul]
    rw [deriv_circleMap, deriv_circleMap, periodic_circleMap 0 R θ]
  have h_shift := Function.Periodic.intervalIntegral_add_eq h_periodic (-Real.pi) 0
  simp only [zero_add, show (-Real.pi + 2 * Real.pi : ℝ) = Real.pi by ring] at h_shift
  rw [h_shift]
  simp only [circleIntegral, hg_def]

/-- Combination of Stages 1 and 2 at height H:
the logDeriv integral along seg5 at height H = 2πi · orderAtCusp'. -/
lemma seg5_logDeriv_integral_eq_H (hf : f ≠ 0) {H : ℝ} (hH : 0 < H)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H),
        q ≠ 0 → UpperHalfPlane.cuspFunction (1 : ℝ) f q ≠ 0) :
    ∫ t in (4:ℝ)..5,
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5_H H t) =
    2 * ↑Real.pi * I * ↑(orderAtCusp' f) := by
  rw [seg5_integral_eq_circleIntegral_H f hH]
  exact circleIntegral_logDeriv_cuspFunction_of_radius f hf
    (seg5_q_radius_H_pos H) (seg5_q_radius_H_lt_one' hH) hcusp_nonvan

include hf in
/-- Bridge lemma: the logDeriv integral along seg5 (with `deriv (fdBoundary_H H) t`)
equals `2πi · orderAtCusp' f`.

This connects `seg5_logDeriv_integral_eq_H` (which integrates just `logDeriv f(z(t))`)
to the form used in `PVChain.Assembly`, which integrates `logDeriv f(z(t)) * z'(t)`.

For `t > 4`, `fdBoundary_H H t = fdBoundary_seg5_H H t` and `deriv (fdBoundary_H H) t = 1`,
so the integrand with `* deriv ...` equals the integrand without. -/
theorem seg5_logDeriv_integral_value_bridge {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H),
      q ≠ 0 → UpperHalfPlane.cuspFunction (1 : ℝ) f q ≠ 0) :
    ∫ t in (4:ℝ)..5,
      logDeriv (modularFormCompOfComplex f) (fdBoundary_H H t) *
        deriv (fdBoundary_H H) t =
      2 * ↑Real.pi * I * (orderAtCusp' f : ℂ) := by
  have hH_pos : 0 < H := lt_trans (by positivity : (0 : ℝ) < Real.sqrt 3 / 2) hH
  have h_eq_ae : ∀ᵐ t ∂volume,
      t ∈ Set.uIoc 4 5 →
        logDeriv (modularFormCompOfComplex f) (fdBoundary_H H t) *
          deriv (fdBoundary_H H) t =
        logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5_H H t) := by
    filter_upwards with t ht
    rw [Set.uIoc_of_le (by norm_num : (4:ℝ) ≤ 5)] at ht
    have ht4 : (4 : ℝ) < t := ht.1
    rw [fdBoundary_H_eq_seg5_H ht4, (fdBoundary_H_hasDerivAt_seg5 H ht4).deriv, mul_one]
  calc ∫ t in (4:ℝ)..5,
        logDeriv (modularFormCompOfComplex f) (fdBoundary_H H t) *
          deriv (fdBoundary_H H) t
      = ∫ t in (4:ℝ)..5,
        logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5_H H t) :=
        intervalIntegral.integral_congr_ae h_eq_ae
    _ = 2 * ↑Real.pi * I * (orderAtCusp' f : ℂ) :=
        seg5_logDeriv_integral_eq_H f hf hH_pos hcusp_nonvan

end
