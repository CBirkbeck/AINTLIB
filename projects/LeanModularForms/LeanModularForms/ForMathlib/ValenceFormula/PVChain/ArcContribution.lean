/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ValenceFormula.PVChain.Helpers
import LeanModularForms.ForMathlib.ValenceFormula.PVChain.ResidueSideInfra
import LeanModularForms.ForMathlib.ModularInvariance
import LeanModularForms.ForMathlib.ValenceFormula.Boundary.Smooth

/-!
# Arc Contribution to the PV Chain

Proves that the ε-truncated arc integral of `f'/f` along the FD boundary
tends to `-(2πik/12)` as `ε → 0⁺`.

The proof uses S-symmetry: the modular S-transformation `z ↦ -1/z` is an
isometry on the unit circle, and the logDeriv functional equation gives
`F(4-t) + F(t) = -k·(iπ/6)·indicator(t)` pointwise. Integrating and using
the change of variables `t ↦ 4-t` yields `2·I(ε) = -k·(iπ/6)·m(ε)`,
where `m(ε) → 2`.

## Main Results

* `arc_cpv_contribution_tendsto` — Tendsto for `sArcOfS S`-only truncation
* `arc_cpv_eventually_eq_union` — bridge from `sArcOfS S ∪ sVertOfS S` to `sArcOfS S`
* `tendsto_pvIntegral_arc_bridge` — final bridge for Assembly.lean
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

private lemma deriv_fdBoundary_H_arc (H : ℝ) {t : ℝ} (h1 : 1 < t) (h3 : t < 3) :
    deriv (fdBoundary_H H) t = ↑(Real.pi / 6) * I * fdBoundary_H H t := by
  rw [fdBoundary_H_eq_arc h1 h3]
  erw [(fdBoundary_H_hasDerivAt_arc H h1 h3).deriv]
  push_cast
  ring

omit hf in
lemma logDeriv_modform_S_transform (z : ℂ) (hz : 0 < z.im) (hz_ne : z ≠ 0)
    (hgz : modularFormCompOfComplex f z ≠ 0) :
    logDeriv (modularFormCompOfComplex f) z =
    logDeriv (modularFormCompOfComplex f) (-(1:ℂ)/z) / z ^ 2 - ↑k / z := by
  set g := modularFormCompOfComplex f
  have h_uhp_open : IsOpen {w : ℂ | 0 < w.im} := UpperHalfPlane.isOpen_upperHalfPlaneSet
  have h_eq_nhd : (fun w ↦ g (-(1:ℂ)/w)) =ᶠ[𝓝 z] (fun w ↦ w ^ k * g w) := by
    filter_upwards [h_uhp_open.mem_nhds hz] with w hw
    exact modform_comp_ofComplex_S_identity f w hw
  have h_neg_inv_im : 0 < (-(1:ℂ)/z).im := by
    rw [show -(1:ℂ)/z = (-z)⁻¹ by field_simp, Complex.inv_im]
    exact div_pos (by simp [hz]) (Complex.normSq_pos.mpr (neg_ne_zero.mpr hz_ne))
  have h_diffOn_g : DifferentiableOn ℂ g {w | 0 < w.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp f.holo'
  have h_logDeriv_comp : logDeriv (fun w ↦ g (-(1:ℂ)/w)) z =
      logDeriv g (-(1:ℂ)/z) * deriv (fun w ↦ -(1:ℂ)/w) z :=
    logDeriv_comp (h_diffOn_g.differentiableAt (h_uhp_open.mem_nhds h_neg_inv_im))
      (DifferentiableAt.div (differentiableAt_const _) differentiableAt_id hz_ne)
  have h_deriv_S : deriv (fun w ↦ -(1:ℂ)/w) z = 1 / z ^ 2 := by
    have h2 : HasDerivAt (fun w : ℂ ↦ -(1:ℂ) / w) (1 / z ^ 2) z := by
      have h3 : HasDerivAt (fun w : ℂ ↦ -w⁻¹) (-(-(z ^ 2)⁻¹)) z := (hasDerivAt_inv hz_ne).neg
      convert h3 using 1 <;> [ext w; skip] <;> field_simp
    exact h2.deriv
  have h_logDeriv_mul : logDeriv (fun w ↦ w ^ k * g w) z =
      logDeriv (· ^ k) z + logDeriv g z :=
    logDeriv_mul z (zpow_ne_zero k hz_ne) hgz (differentiableAt_zpow.mpr (.inl hz_ne))
      (h_diffOn_g.differentiableAt (h_uhp_open.mem_nhds hz))
  have h_logDeriv_eq : logDeriv (fun w ↦ g (-(1:ℂ)/w)) z =
      logDeriv (fun w ↦ w ^ k * g w) z := by
    simp only [logDeriv_apply]
    rw [h_eq_nhd.eq_of_nhds, h_eq_nhd.deriv.eq_of_nhds]
  rw [h_logDeriv_eq, h_logDeriv_mul, logDeriv_zpow z k, h_deriv_S] at h_logDeriv_comp
  linear_combination h_logDeriv_comp

omit f hf in
lemma S_isometry_unit_circle (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖-(1:ℂ)/z - (-(1:ℂ)/w)‖ = ‖z - w‖ := by
  have hzne : z ≠ 0 := fun h ↦ by simp [h] at hz
  have hwne : w ≠ 0 := fun h ↦ by simp [h] at hw
  rw [show -(1:ℂ)/z - (-(1:ℂ)/w) = (z - w) / (z * w) by field_simp; ring,
      norm_div, norm_mul, hz, hw]
  norm_num

omit f hf in
lemma fdBoundary_arc_S_reverse (H : ℝ) (t : ℝ) (ht : t ∈ Set.Ioo (1:ℝ) 3) :
    fdBoundary_H H (4 - t) = -(1:ℂ) / fdBoundary_H H t := by
  rw [fdBoundary_H_eq_arc (by linarith [ht.2]) (by linarith [ht.1]),
      fdBoundary_H_eq_arc ht.1 ht.2, eq_div_iff (Complex.exp_ne_zero _), ← Complex.exp_add]
  convert exp_pi_mul_I using 2
  push_cast
  ring

omit f hf in
private lemma arc_indicator_symmetric_of_sArcOfS
    (S : Finset UpperHalfPlane) (H ε : ℝ) (t : ℝ) (ht : t ∈ Set.Ioo (1:ℝ) 3) :
    (∃ s ∈ sArcOfS S, ‖fdBoundary_H H (4 - t) - (s : ℂ)‖ ≤ ε) ↔
    (∃ s ∈ sArcOfS S, ‖fdBoundary_H H t - (s : ℂ)‖ ≤ ε) := by
  have h_S_unit := sArcOfS_unit S
  have h_S_closed := sArcOfS_closed S
  have h_arc_rev : fdBoundary_H H (4 - t) = -(1:ℂ) / fdBoundary_H H t :=
    fdBoundary_arc_S_reverse H t ht
  have h_norm_t : ‖fdBoundary_H H t‖ = 1 := by
    rw [fdBoundary_H_eq_arc ht.1 ht.2]
    exact Complex.norm_exp_ofReal_mul_I _
  constructor
  · rintro ⟨s₀, hs₀, h_le⟩
    refine ⟨-(1:ℂ)/s₀, h_S_closed s₀ hs₀, ?_⟩
    have h_norm_s := h_S_unit s₀ hs₀
    calc ‖fdBoundary_H H t - (-(1:ℂ)/s₀)‖ = ‖-(1:ℂ)/fdBoundary_H H t - (-(1:ℂ)/(-(1:ℂ)/s₀))‖ :=
          (S_isometry_unit_circle _ _ h_norm_t (by rw [norm_div, norm_neg, norm_one, h_norm_s, div_one])).symm
      _ = ‖-(1:ℂ)/fdBoundary_H H t - s₀‖ := by
          have hne : s₀ ≠ 0 := fun h ↦ by simp [h] at h_norm_s
          congr 2
          field_simp
      _ = ‖fdBoundary_H H (4 - t) - s₀‖ := by rw [← h_arc_rev]
      _ ≤ ε := h_le
  · rintro ⟨s₁, hs₁, h_le⟩
    refine ⟨-(1:ℂ)/s₁, h_S_closed s₁ hs₁, ?_⟩
    rw [h_arc_rev, S_isometry_unit_circle _ _ h_norm_t (h_S_unit s₁ hs₁)]
    exact h_le

private lemma cpv_integrand_intervalIntegrable_arc (S : Finset UpperHalfPlane)
    (H : ℝ) (ε : ℝ) (hε : 0 < ε) (h_oncurve : ∀ t ∈ Set.Ioo (1:ℝ) 3,
        modularFormCompOfComplex f (fdBoundary_H H t) = 0 →
        fdBoundary_H H t ∈ (↑(sArcOfS S) : Set ℂ)) :
    IntervalIntegrable (fun t ↦ cpvIntegrandOn (↑(sArcOfS S))
        (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t)
      volume 1 3 := by
  set g := modularFormCompOfComplex f
  set γ := fdBoundary_H H
  set S_arc := sArcOfS S
  set F := fun t ↦ cpvIntegrandOn (↑S_arc) (logDeriv g) γ ε t
  set K' := {t ∈ Set.Icc (1:ℝ) 3 | ∀ s ∈ S_arc, ε ≤ ‖γ t - (s : ℂ)‖}
  have hK'_compact : IsCompact K' := by
    refine IsCompact.of_isClosed_subset isCompact_Icc ?_ (fun _t ⟨ht, _⟩ ↦ ht)
    refine IsClosed.inter isClosed_Icc ?_
    convert (isClosed_iInter fun s ↦ isClosed_iInter fun _ ↦
      isClosed_le (f := fun _ ↦ ε) (g := fun t ↦ ‖γ t - s‖) continuous_const (by fun_prop)
      : IsClosed (⋂ (s : ℂ) (_ : s ∈ S_arc), {t : ℝ | ε ≤ ‖γ t - s‖})) using 1
    ext t; simp only [Set.mem_iInter, Set.mem_setOf]; exact Iff.rfl
  set K := {t ∈ Set.uIoc (1:ℝ) 3 | ¬∃ s ∈ (↑S_arc : Set ℂ), ‖γ t - s‖ ≤ ε}
  have hK_subset_K' : K ⊆ K' := fun t ⟨ht_uioc, h_not_near⟩ ↦ by
    have ht_Ioc : t ∈ Set.Ioc 1 3 := by rwa [Set.uIoc_of_le (by norm_num)] at ht_uioc
    refine ⟨⟨ht_Ioc.1.le, ht_Ioc.2⟩, fun s hs ↦ ?_⟩
    by_contra! h_contra
    exact h_not_near ⟨s, Finset.mem_coe.mpr hs, h_contra.le⟩
  have h_cont : ContinuousOn (fun t ↦ logDeriv g (γ t) * deriv γ t) K' := by
    intro t ⟨⟨ht1, ht3⟩, h_far⟩
    have ht_not_1 : t ≠ 1 := by
      rintro rfl
      have h1 := h_far _ (sArcOfS_rho_plus_one_in S)
      rw [show γ 1 = ellipticPointRhoPlusOne from fdBoundary_H_at_one H,
          sub_self, norm_zero] at h1; linarith
    have ht_not_3 : t ≠ 3 := by
      rintro rfl
      have h3 := h_far _ (sArcOfS_rho_in S)
      rw [show γ 3 = ellipticPointRho from fdBoundary_H_at_three H,
          sub_self, norm_zero] at h3; linarith
    have ht_ioo : t ∈ Set.Ioo (1:ℝ) 3 :=
      ⟨lt_of_le_of_ne ht1 (Ne.symm ht_not_1), lt_of_le_of_ne ht3 ht_not_3⟩
    have h_ne : g (γ t) ≠ 0 := fun h_zero ↦ by
      have h_dist := h_far _ (Finset.mem_coe.mp (h_oncurve t ht_ioo h_zero))
      rw [sub_self, norm_zero] at h_dist; linarith
    apply ContinuousAt.continuousWithinAt
    refine ContinuousAt.mul ?_ ?_
    · refine ContinuousAt.comp ?_ (fdBoundary_H_continuous H).continuousAt
      have h_im : 0 < (γ t).im := by
        rw [show γ t = _ from fdBoundary_H_eq_arc ht_ioo.1 ht_ioo.2,
            Complex.exp_ofReal_mul_I_im]
        exact Real.sin_pos_of_pos_of_lt_pi
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      exact (analyticAt_logDeriv_off_zeros' f (γ t) h_im h_ne).continuousAt
    · have h_deriv_eq : deriv γ =ᶠ[𝓝 t] fun s ↦ ↑(Real.pi / 6) * I * γ s := by
        filter_upwards [Ioo_mem_nhds ht_ioo.1 ht_ioo.2] with s hs
        exact deriv_fdBoundary_H_arc H hs.1 hs.2
      exact ((continuousAt_const.mul continuousAt_const).mul
        (fdBoundary_H_continuous H).continuousAt).congr h_deriv_eq.symm
  have h_int : IntegrableOn (fun t ↦ logDeriv g (γ t) * deriv γ t) K' :=
    ContinuousOn.integrableOn_compact hK'_compact h_cont
  have hK_meas : MeasurableSet K := by
    apply measurableSet_uIoc.inter
    apply MeasurableSet.compl
    suffices h : IsClosed (⋃ s ∈ (↑S_arc : Set ℂ), {t : ℝ | ‖γ t - s‖ ≤ ε}) by
      convert h.measurableSet using 1
      ext t
      simp only [Set.mem_iUnion, Set.mem_setOf, Finset.mem_coe, exists_prop]
      exact Iff.rfl
    exact S_arc.finite_toSet.isClosed_biUnion fun s _ ↦
      isClosed_le (by fun_prop) continuous_const
  have hF_K : EqOn F (fun t ↦ logDeriv g (γ t) * deriv γ t) K := by
    intro t ⟨_, h_not_near⟩
    change cpvIntegrandOn (↑S_arc) (logDeriv g) γ ε t = _
    simp only [cpvIntegrandOn]
    simp only [Finset.mem_coe] at h_not_near
    exact if_neg h_not_near
  have h_int_K : IntegrableOn F K :=
    (IntegrableOn.mono_set h_int hK_subset_K').congr_fun hF_K.symm hK_meas
  have h_compl_zero : EqOn F 0 (Set.uIoc (1:ℝ) 3 \ K) := by
    intro t ⟨ht_uioc, h_not_K⟩
    change cpvIntegrandOn (↑S_arc) (logDeriv g) γ ε t = 0
    simp only [cpvIntegrandOn]
    refine if_pos ?_
    by_contra h_far
    exact h_not_K ⟨ht_uioc, by simpa [Finset.mem_coe] using h_far⟩
  have hcompl_meas : MeasurableSet (Set.uIoc (1:ℝ) 3 \ K) :=
    measurableSet_uIoc.diff hK_meas
  have h_int_compl : IntegrableOn F (Set.uIoc (1:ℝ) 3 \ K) :=
    integrableOn_zero.congr_fun h_compl_zero.symm hcompl_meas
  have h_int_union : IntegrableOn F (Set.uIoc (1:ℝ) 3) := by
    have := h_int_K.union h_int_compl
    rwa [Set.union_sdiff_cancel (fun t ht ↦ ht.1)] at this
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1:ℝ) ≤ 3)]
  rwa [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 3)] at h_int_union

omit f hf in
private lemma arc_preimage_subsingleton (H : ℝ) (s : ℂ) :
    Set.Subsingleton ({t ∈ Set.Ioo (1:ℝ) 3 | fdBoundary_H H t = s}) := by
  intro t₁ ⟨ht₁, h₁⟩ t₂ ⟨ht₂, h₂⟩
  rw [fdBoundary_H_eq_arc ht₁.1 ht₁.2] at h₁
  rw [fdBoundary_H_eq_arc ht₂.1 ht₂.2] at h₂
  have h_re := congrArg Complex.re (h₁.trans h₂.symm)
  rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re] at h_re
  have hpi := Real.pi_pos
  have hθ₁ : Real.pi * (1 + t₁) / 6 ∈ Set.Icc 0 Real.pi :=
    ⟨by nlinarith [ht₁.1], by nlinarith [ht₁.2]⟩
  have hθ₂ : Real.pi * (1 + t₂) / 6 ∈ Set.Icc 0 Real.pi :=
    ⟨by nlinarith [ht₂.1], by nlinarith [ht₂.2]⟩
  linarith [mul_left_cancel₀ (ne_of_gt hpi)
    (show Real.pi * (1 + t₁) = Real.pi * (1 + t₂) from
      by linarith [Real.strictAntiOn_cos.injOn hθ₁ hθ₂ h_re])]

omit f hf in
private lemma arc_min_dist_pos (S : Finset UpperHalfPlane)
    (H : ℝ) {t : ℝ}
    (h_not_in : (fdBoundary_H H t : ℂ) ∉ (↑(sArcOfS S) : Set ℂ)) :
    ∃ δ > 0, ∀ s ∈ sArcOfS S, δ ≤ ‖fdBoundary_H H t - s‖ := by
  rcases (sArcOfS S).eq_empty_or_nonempty with h_empty | hne
  · exact ⟨1, one_pos, fun s hs ↦ absurd (h_empty ▸ hs) (Finset.notMem_empty s)⟩
  · obtain ⟨s₀, hs₀, h_min⟩ := (sArcOfS S).exists_min_image (fun s ↦ ‖fdBoundary_H H t - s‖) hne
    exact ⟨‖fdBoundary_H H t - s₀‖,
      norm_pos_iff.mpr (sub_ne_zero.mpr (fun h_eq ↦ by
        rw [h_eq] at h_not_in
        exact h_not_in (Finset.mem_coe.mpr hs₀))),
      h_min⟩

omit hf in
lemma arc_cpv_integral_S_identity (S : Finset UpperHalfPlane)
    (H : ℝ) (ε : ℝ) (hε : 0 < ε) (h_oncurve : ∀ t ∈ Set.Ioo (1:ℝ) 3,
        modularFormCompOfComplex f (fdBoundary_H H t) = 0 →
        fdBoundary_H H t ∈ (↑(sArcOfS S) : Set ℂ)) :
    (∫ t in (1:ℝ)..3, cpvIntegrandOn (sArcOfS S)
        (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) =
    -(↑k * (↑Real.pi / 12 * I)) *
      ↑(∫ t in (1:ℝ)..3,
        if (∃ s ∈ sArcOfS S, ‖fdBoundary_H H t - (s : ℂ)‖ ≤ ε)
        then (0:ℝ) else 1) := by
  set g := modularFormCompOfComplex f with hg_def
  set γ := fdBoundary_H H
  set S_arc := sArcOfS S
  set F := cpvIntegrandOn S_arc (logDeriv g) γ ε
  set ind := fun t ↦ ∃ s ∈ S_arc, ‖γ t - (s : ℂ)‖ ≤ ε
  have h_ind_1 : ind 1 :=
    ⟨_, sArcOfS_rho_plus_one_in S, by
      rw [show γ 1 = ellipticPointRhoPlusOne from fdBoundary_H_at_one H,
          sub_self, norm_zero]; linarith⟩
  have h_ind_3 : ind 3 :=
    ⟨_, sArcOfS_rho_in S, by
      rw [show γ 3 = ellipticPointRho from fdBoundary_H_at_three H,
          sub_self, norm_zero]; linarith⟩
  have h_cov : ∫ t in (1:ℝ)..3, F (4 - t) = ∫ t in (1:ℝ)..3, F t := by
    simpa only [show (4:ℝ) - 3 = 1 by norm_num, show (4:ℝ) - 1 = 3 by norm_num]
      using @intervalIntegral.integral_comp_sub_left ℂ _ _ 1 3 F 4
  have h_ind_sym : ∀ t ∈ Set.Ioo (1:ℝ) 3, (ind (4 - t) ↔ ind t) :=
    fun t ht ↦ arc_indicator_symmetric_of_sArcOfS S H ε t ht
  have h_arc_ne_zero : ∀ t, t ∈ Set.Ioo (1:ℝ) 3 → γ t ≠ 0 := fun t ht ↦ by
    rw [show γ t = _ from fdBoundary_H_eq_arc ht.1 ht.2]; exact exp_ne_zero _
  have h_arc_im_pos : ∀ t, t ∈ Set.Ioo (1:ℝ) 3 → 0 < (γ t).im := fun t ht ↦ by
    rw [show γ t = _ from fdBoundary_H_eq_arc ht.1 ht.2, Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [ht.1, Real.pi_pos])
      (by nlinarith [ht.2, Real.pi_pos])
  have h_4mt_ioo : ∀ t, t ∈ Set.Ioo (1:ℝ) 3 → (4 - t) ∈ Set.Ioo (1:ℝ) 3 :=
    fun t ht ↦ ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h_deriv_arc : ∀ t, t ∈ Set.Ioo (1:ℝ) 3 →
      deriv γ t = ↑(Real.pi / 6) * I * γ t :=
    fun t ht ↦ deriv_fdBoundary_H_arc H ht.1 ht.2
  have h_pw : ∀ t ∈ Set.uIcc (1:ℝ) 3,
      F (4 - t) + F t = -(↑k * (↑Real.pi / 6 * I)) *
        ↑(if ind t then (0:ℝ) else 1) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)] at ht
    by_cases h_near : ind t
    · have h_F_t : F t = 0 := by
        show cpvIntegrandOn _ _ _ _ _ = 0
        rw [cpvIntegrandOn, if_pos h_near]
      have h_ind_4mt : ind (4 - t) := by
        by_cases h1 : 1 < t ∧ t < 3
        · exact (h_ind_sym t ⟨h1.1, h1.2⟩).mpr h_near
        · push Not at h1
          rcases eq_or_lt_of_le ht.1 with rfl | h_lt
          · exact (show (4:ℝ) - 1 = 3 by norm_num) ▸ h_ind_3
          · have : t = 3 := le_antisymm ht.2 (h1 h_lt)
            subst this
            exact (show (4:ℝ) - 3 = 1 by norm_num) ▸ h_ind_1
      have h_F_4mt : F (4 - t) = 0 := by
        show cpvIntegrandOn _ _ _ _ _ = 0
        rw [cpvIntegrandOn, if_pos h_ind_4mt]
      rw [h_F_4mt, h_F_t]
      simp [h_near]
    · have ht_ioo : t ∈ Set.Ioo (1:ℝ) 3 :=
        ⟨lt_of_le_of_ne ht.1 (fun h ↦ h_near (h ▸ h_ind_1)),
         lt_of_le_of_ne ht.2 (fun h ↦ h_near (h ▸ h_ind_3))⟩
      have h_not_ind_4mt : ¬ind (4 - t) := fun h ↦ h_near ((h_ind_sym t ht_ioo).mp h)
      have h_F_t : F t = logDeriv g (γ t) * deriv γ t := by
        show cpvIntegrandOn _ _ _ _ _ = _
        unfold cpvIntegrandOn; rw [if_neg h_near]
      have h_F_4mt : F (4 - t) = logDeriv g (γ (4 - t)) * deriv γ (4 - t) := by
        show cpvIntegrandOn _ _ _ _ _ = _
        unfold cpvIntegrandOn; rw [if_neg h_not_ind_4mt]
      rw [h_F_4mt, h_F_t, if_neg h_near]
      simp only [Complex.ofReal_one, mul_one]
      have h_rev : γ (4 - t) = -(1:ℂ) / γ t := fdBoundary_arc_S_reverse H t ht_ioo
      have h_d_4mt := h_deriv_arc (4-t) (h_4mt_ioo t ht_ioo)
      have hg_ne : g (γ t) ≠ 0 := fun h_zero ↦ h_near
        ⟨γ t, by rw [← Finset.mem_coe]; exact h_oncurve t ht_ioo h_zero,
         by rw [sub_self, norm_zero]; linarith⟩
      have h_logD := logDeriv_modform_S_transform f (γ t) (h_arc_im_pos t ht_ioo)
        (h_arc_ne_zero t ht_ioo) hg_ne
      simp only [← hg_def] at h_logD
      rw [h_rev] at h_d_4mt ⊢
      rw [h_d_4mt, h_deriv_arc t ht_ioo, h_logD]
      field_simp [h_arc_ne_zero t ht_ioo]
      push_cast; ring
  have hF_int : IntervalIntegrable F volume 1 3 :=
    cpv_integrand_intervalIntegrable_arc f S H ε hε h_oncurve
  set I_val := ∫ t in (1:ℝ)..3, F t
  set m_val := ∫ t in (1:ℝ)..3, if ind t then (0:ℝ) else 1
  have h_sum_int : ∫ t in (1:ℝ)..3, (F (4 - t) + F t) =
      -(↑k * (↑Real.pi / 6 * I)) * ↑m_val := by
    calc ∫ t in (1:ℝ)..3, (F (4 - t) + F t)
        = ∫ t in (1:ℝ)..3, -(↑k * (↑Real.pi / 6 * I)) *
            ↑(if ind t then (0:ℝ) else 1) :=
          intervalIntegral.integral_congr h_pw
      _ = -(↑k * (↑Real.pi / 6 * I)) *
            ∫ t in (1:ℝ)..3, (↑(if ind t then (0:ℝ) else 1) : ℂ) :=
          intervalIntegral.integral_const_mul _ _
      _ = -(↑k * (↑Real.pi / 6 * I)) * ↑m_val := by
          congr 1; exact intervalIntegral.integral_ofReal
  have h_cov_int : IntervalIntegrable (fun t ↦ F (4 - t)) volume 1 3 := by
    convert (hF_int.comp_sub_left 4).symm using 2 <;> norm_num
  have h_2I : I_val + I_val = -(↑k * (↑Real.pi / 6 * I)) * ↑m_val := by
    have h_split := intervalIntegral.integral_add h_cov_int hF_int
    rw [h_cov] at h_split
    exact h_split ▸ h_sum_int
  apply mul_left_cancel₀ (two_ne_zero (α := ℂ))
  rw [show (2 : ℂ) * I_val = I_val + I_val by ring, h_2I]; ring

omit f hf in
lemma arc_non_excluded_measure_tendsto (S : Finset UpperHalfPlane) (H : ℝ) :
    Tendsto (fun ε ↦ ∫ t in (1:ℝ)..3,
        if (∃ s ∈ sArcOfS S, ‖fdBoundary_H H t - (s : ℂ)‖ ≤ ε)
        then (0:ℝ) else 1)
      (𝓝[>] 0) (𝓝 2) := by
  rw [show (2:ℝ) = ∫ _ in (1:ℝ)..3, (1:ℝ) by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]; norm_num]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (1:ℝ))
  · refine Eventually.of_forall fun ε ↦ Measurable.aestronglyMeasurable ?_
    apply measurable_const.ite _ measurable_const
    have h : {a | ∃ s ∈ sArcOfS S, ‖fdBoundary_H H a - s‖ ≤ ε} =
        ⋃ s ∈ (sArcOfS S : Finset ℂ), {a | ‖fdBoundary_H H a - s‖ ≤ ε} := by
      ext; simp [Set.mem_iUnion]
    rw [h]
    exact Finset.measurableSet_biUnion _ fun s _ ↦
      (isClosed_le (by fun_prop) continuous_const).measurableSet
  · refine Eventually.of_forall fun ε ↦ Eventually.of_forall fun t _ ↦ ?_
    split_ifs <;> norm_num
  · exact intervalIntegrable_const
  · rw [ae_iff]
    apply measure_mono_null (t := (⋃ s ∈ (sArcOfS S : Finset ℂ),
            {t ∈ Set.Ioo (1:ℝ) 3 | fdBoundary_H H t = ↑s}) ∪ {3})
    · intro t ht
      push Not at ht
      obtain ⟨ht_mem, ht_not⟩ := ht
      rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 3)] at ht_mem
      simp only [Set.mem_union, Set.mem_iUnion, Set.mem_sep_iff, Set.mem_singleton_iff]
      by_contra! h_not_in
      obtain ⟨h_pre, h_ne_3⟩ := h_not_in
      apply ht_not
      have ht_ioo : t ∈ Set.Ioo (1:ℝ) 3 :=
        ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 h_ne_3⟩
      have h_not_in_S : (fdBoundary_H H t : ℂ) ∉ (↑(sArcOfS S) : Set ℂ) :=
        fun h_mem ↦ h_pre _ (Finset.mem_coe.mp h_mem) ht_ioo rfl
      obtain ⟨δ, hδ_pos, hδ_le⟩ := arc_min_dist_pos S H h_not_in_S
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
      rw [Set.mem_Ioo] at hε
      rw [if_neg]
      push Not
      exact fun s hs ↦ (hε.2).trans_le (hδ_le s hs)
    · apply measure_union_null
      · exact ((sArcOfS S).finite_toSet.biUnion (fun s _ ↦
            (arc_preimage_subsingleton H s).finite)).measure_zero _
      · exact Real.volume_singleton

omit hf in
theorem arc_cpv_contribution_tendsto (S : Finset UpperHalfPlane)
    (H : ℝ) (h_oncurve : ∀ t ∈ Set.Ioo (1:ℝ) 3,
        modularFormCompOfComplex f (fdBoundary_H H t) = 0 →
        fdBoundary_H H t ∈ (↑(sArcOfS S) : Set ℂ)) :
    Tendsto (fun ε ↦ ∫ t in (1:ℝ)..3, cpvIntegrandOn (sArcOfS S)
        (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t)
      (𝓝[>] 0) (𝓝 (-(2 * ↑Real.pi * I * (k : ℂ) / 12))) := by
  set I_arc : ℝ → ℂ := fun ε ↦ ∫ t in (1:ℝ)..3, cpvIntegrandOn (sArcOfS S)
      (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t
  set m_fun : ℝ → ℝ := fun ε ↦ ∫ t in (1:ℝ)..3,
      if (∃ s ∈ sArcOfS S, ‖fdBoundary_H H t - (s : ℂ)‖ ≤ ε)
      then (0:ℝ) else 1
  set g_fun : ℝ → ℂ := fun x ↦ -(↑k * (↑Real.pi / 12 * I)) * (↑x : ℂ)
  have h_id : I_arc =ᶠ[𝓝[>] (0:ℝ)] (g_fun ∘ m_fun) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact arc_cpv_integral_S_identity f S H ε hε h_oncurve
  have h_g_cont : Tendsto g_fun (𝓝 2) (𝓝 (g_fun 2)) :=
    (continuous_const.mul Complex.continuous_ofReal).continuousAt
  rw [show -(2 * ↑Real.pi * I * (↑k : ℂ) / 12) = g_fun 2 by simp only [g_fun]; push_cast; ring]
  exact Tendsto.congr' h_id.symm (h_g_cont.comp (arc_non_excluded_measure_tendsto S H))

omit f hf in
private lemma arc_re_strictly_between (H : ℝ) (t : ℝ) (ht : t ∈ Set.Ioo (1:ℝ) 3) :
    -1/2 < (fdBoundary_H H t).re ∧ (fdBoundary_H H t).re < 1/2 := by
  rw [fdBoundary_H_eq_arc ht.1 ht.2, Complex.exp_ofReal_mul_I_re]
  have hpi := Real.pi_pos
  have hθ_lo : Real.pi / 3 < Real.pi * (1 + t) / 6 := by nlinarith [ht.1]
  have hθ_hi : Real.pi * (1 + t) / 6 < 2 * Real.pi / 3 := by nlinarith [ht.2]
  have hθ_Icc : Real.pi * (1 + t) / 6 ∈ Set.Icc 0 Real.pi :=
    ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have hpi3_Icc : Real.pi / 3 ∈ Set.Icc 0 Real.pi :=
    ⟨by nlinarith, by nlinarith⟩
  have h23_Icc : 2 * Real.pi / 3 ∈ Set.Icc 0 Real.pi :=
    ⟨by nlinarith, by nlinarith⟩
  refine ⟨?_, ?_⟩
  · have h1 := Real.strictAntiOn_cos hθ_Icc h23_Icc hθ_hi
    have h2 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]; ring
    linarith
  · have h1 := Real.strictAntiOn_cos hpi3_Icc hθ_Icc hθ_lo
    rw [Real.cos_pi_div_three] at h1
    linarith

omit f hf in
private lemma arc_ne_svert (H : ℝ) (S : Finset UpperHalfPlane)
    (s : ℂ) (hs_re : s.re = 1/2 ∨ s.re = -1/2) (hs_not : s ∉ sArcOfS S)
    (t : ℝ) (ht : t ∈ Set.Icc (1:ℝ) 3) :
    fdBoundary_H H t ≠ s := by
  intro h_eq
  rcases lt_or_eq_of_le ht.1 with ht1 | rfl
  · rcases lt_or_eq_of_le ht.2 with ht3 | rfl
    · have := arc_re_strictly_between H t ⟨ht1, ht3⟩
      rw [h_eq] at this
      rcases hs_re with h | h <;> linarith [this.1, this.2]
    · rw [fdBoundary_H_at_three H] at h_eq
      exact hs_not (h_eq ▸ sArcOfS_rho_in S)
  · rw [fdBoundary_H_at_one H] at h_eq
    exact hs_not (h_eq ▸ sArcOfS_rho_plus_one_in S)

omit f hf in
private lemma arc_min_dist_pos_of_svert (H : ℝ) (S : Finset UpperHalfPlane)
    (s : ℂ) (hs_re : s.re = 1/2 ∨ s.re = -1/2) (hs_not : s ∉ sArcOfS S) :
    ∃ δ > 0, ∀ t ∈ Set.Icc (1:ℝ) 3, δ ≤ ‖fdBoundary_H H t - s‖ := by
  obtain ⟨t₀, ht₀, ht₀_min⟩ := isCompact_Icc.exists_isMinOn
    (⟨1, le_refl _, by norm_num⟩ : (Set.Icc (1:ℝ) 3).Nonempty)
    (by fun_prop : Continuous (fun t ↦ ‖fdBoundary_H H t - s‖)).continuousOn
  exact ⟨‖fdBoundary_H H t₀ - s‖,
    norm_pos_iff.mpr (sub_ne_zero.mpr (arc_ne_svert H S s hs_re hs_not t₀ ht₀)),
    fun t ht ↦ ht₀_min ht⟩

omit f hf in
private lemma arc_svert_combined_dist (H : ℝ) (S : Finset UpperHalfPlane) :
    ∃ δ > 0, ∀ s ∈ sVertOfS S, s ∉ sArcOfS S →
      ∀ t ∈ Set.Icc (1:ℝ) 3, δ ≤ ‖fdBoundary_H H t - s‖ := by
  by_cases h_all_in : ∀ s ∈ sVertOfS S, s ∈ sArcOfS S
  · exact ⟨1, one_pos, fun s hs hs_not ↦ absurd (h_all_in s hs) hs_not⟩
  · suffices key : ∀ (SV : Finset ℂ), (∀ s ∈ SV, s ∈ sVertOfS S → s ∉ sArcOfS S →
          ∃ δ > 0, ∀ t ∈ Set.Icc (1:ℝ) 3, δ ≤ ‖fdBoundary_H H t - s‖) →
        ∃ δ > 0, ∀ s ∈ SV, s ∈ sVertOfS S → s ∉ sArcOfS S →
          ∀ t ∈ Set.Icc (1:ℝ) 3, δ ≤ ‖fdBoundary_H H t - s‖ by
      obtain ⟨δ, hδ_pos, hδ_bound⟩ := key (sVertOfS S) fun s hs hs_v ↦
        arc_min_dist_pos_of_svert H S s (sVertOfS_re S s hs_v)
      exact ⟨δ, hδ_pos, fun s hs hs_not t ht ↦ hδ_bound s hs hs hs_not t ht⟩
    intro SV
    induction SV using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, one_pos, fun s hs ↦ absurd hs (Finset.notMem_empty s)⟩
    | @insert a SV' _ha ih =>
      intro h_all
      obtain ⟨δ₁, hδ₁_pos, hδ₁_bound⟩ := ih (fun s hs ↦
        h_all s (Finset.mem_insert_of_mem hs))
      by_cases ha_need : a ∈ sVertOfS S ∧ a ∉ sArcOfS S
      · obtain ⟨δ₂, hδ₂_pos, hδ₂_bound⟩ :=
          h_all a (Finset.mem_insert_self _ _) ha_need.1 ha_need.2
        exact ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun s hs h_sv h_na t ht ↦ by
          rcases Finset.mem_insert.mp hs with rfl | h
          · exact le_trans (min_le_right _ _) (hδ₂_bound t ht)
          · exact le_trans (min_le_left _ _) (hδ₁_bound s h h_sv h_na t ht)⟩
      · push Not at ha_need
        exact ⟨δ₁, hδ₁_pos, fun s hs h_sv h_na t ht ↦ by
          rcases Finset.mem_insert.mp hs with rfl | h
          · exact absurd (ha_need h_sv) h_na
          · exact hδ₁_bound s h h_sv h_na t ht⟩

omit f hf in
lemma arc_cpv_eventually_eq_union (S : Finset UpperHalfPlane)
    (H : ℝ) (g : ℂ → ℂ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∫ t in (1:ℝ)..3, cpvIntegrandOn (sArcOfS S ∪ sVertOfS S)
          g (fdBoundary_H H) ε t =
      ∫ t in (1:ℝ)..3, cpvIntegrandOn (sArcOfS S)
          g (fdBoundary_H H) ε t := by
  obtain ⟨δ, hδ_pos, h_far⟩ := arc_svert_combined_dist H S
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hδ_pos)] with ε hε_lt
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)] at ht
  unfold cpvIntegrandOn
  by_cases h_sarc : ∃ s ∈ sArcOfS S, ‖fdBoundary_H H t - s‖ ≤ ε
  · obtain ⟨s, hs, hle⟩ := h_sarc
    rw [if_pos ⟨s, Finset.mem_union_left _ hs, hle⟩, if_pos ⟨s, hs, hle⟩]
  · refine (if_neg ?_).trans (if_neg h_sarc).symm
    rintro ⟨s, hs, hle⟩
    rcases Finset.mem_union.mp hs with h_arc | h_vert
    · exact h_sarc ⟨s, h_arc, hle⟩
    · by_cases hs_arc : s ∈ sArcOfS S
      · exact h_sarc ⟨s, hs_arc, hle⟩
      · exact absurd hle (not_le.mpr (lt_of_lt_of_le hε_lt (h_far s h_vert hs_arc t ht)))

omit hf in
theorem tendsto_pvIntegral_arc_bridge (S : Finset UpperHalfPlane)
    {H : ℝ} (_hH : Real.sqrt 3 / 2 < H) (h_oncurve_arc : ∀ t ∈ Set.Ioo (1 : ℝ) 3,
      modularFormCompOfComplex f (fdBoundary_H H t) = 0 →
      fdBoundary_H H t ∈ (↑(sArcOfS S) : Set ℂ)) :
    Tendsto (fun ε ↦
      ∫ t in (1:ℝ)..3,
        pvIntegrand f (fdBoundary_H H) (sArcOfS S ∪ sVertOfS S) ε t)
      (𝓝[>] 0) (𝓝 (-(2 * ↑Real.pi * I * ((k : ℂ) / 12)))) := by
  have h_tend := arc_cpv_contribution_tendsto f S H h_oncurve_arc
  rw [show -(2 * ↑Real.pi * I * (↑k : ℂ) / 12) =
      -(2 * ↑Real.pi * I * ((k : ℂ) / 12)) by ring] at h_tend
  exact h_tend.congr' ((arc_cpv_eventually_eq_union S H
    (logDeriv (modularFormCompOfComplex f))).mono fun _ h ↦ h.symm)

end
