/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ValenceFormula.OnCurvePV.EndpointCorner

/-!
# On-Curve PV: Main Theorem

For any point `s` on `fdBoundary_H H`, the CPV integral of `(z - s)⁻¹` exists.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Glue two adjacent CPV intervals `[a, b]` and `[b, c]` into `[a, c]`, discharging the
shared cutout integrability obligation from `0 ≤ a` and `c ≤ 5`. -/
private theorem cpv_concat_cutout (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (a b c : ℝ) (h_ab : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) a b s)
    (h_bc : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) b c s)
    (hab : a ≤ b) (hbc : b ≤ c) (h0a : 0 ≤ a) (hc5 : c ≤ 5) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) a c s := by
  apply cpv_concat _ _ a b c s h_ab h_bc hab hbc
  intro ε hε
  exact (fdBoundary_H_cutout_ii H hH s ε hε).mono_set (by
    rw [Set.uIcc_of_le (hab.trans hbc), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
    exact Set.Icc_subset_Icc h0a hc5)

/-- CPV existence on a smooth arc subinterval `[a', b'] ⊆ (1, 3)` around `t₀ ∈ (1, 3)`, packaging
the `ContDiffAt`, nonvanishing-derivative, continuity, and injectivity obligations for the arc. -/
private theorem arc_smooth_cpv (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ) {t₀ a' b' : ℝ}
    (ht₀_gt_1 : 1 < t₀) (ht₀_lt_3 : t₀ < 3) (ha' : a' < t₀) (hb' : t₀ < b')
    (ha1 : 1 < a') (hb3 : b' < 3) (hγt₀ : fdBoundary_H H t₀ = s) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) a' b' s := by
  apply cpv_exists_on_smooth_subinterval H hH s ⟨ha', hb'⟩ hγt₀
  · have heq : fdBoundary_H H =ᶠ[𝓝 t₀]
        (fun u => Complex.exp (↑(Real.pi * (1 + u) / 6) * I)) :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 1 3,
        Ioo_mem_nhds ht₀_gt_1 ht₀_lt_3, fun u hu => fdBoundary_H_eq_arc hu.1 hu.2⟩
    exact ContDiffAt.congr_of_eventuallyEq (((Complex.ofRealCLM.contDiff.contDiffAt.comp t₀
      (by fun_prop : ContDiffAt ℝ 2 (fun u : ℝ => Real.pi * (1 + u) / 6) t₀)).mul
        contDiffAt_const).cexp) heq
  · exact (fdBoundary_H_hasDerivAt_arc H ht₀_gt_1 ht₀_lt_3).deriv ▸
      mul_ne_zero (exp_ne_zero _)
        (mul_ne_zero (by norm_num [Complex.ofReal_ne_zero]) I_ne_zero)
  · exact (fdBoundary_H_deriv_continuousOn_Ioo_13 H).mono fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro t ht hγt
    have ht' : t ∈ Set.Ioo (1:ℝ) 3 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [fdBoundary_H_eq_arc ht'.1 ht'.2, fdBoundary_H_eq_arc ht₀_gt_1 ht₀_lt_3] at hγt
    exact arc_angle_injective ht' ⟨ht₀_gt_1, ht₀_lt_3⟩ hγt

private theorem cpv_exists_at_I_H_lt_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    (h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
        (fdBoundary_H H) (3/2) (5/2) I)
    (h_arc_I_iff : ∀ {t : ℝ}, 1 < t → t < 3 → (fdBoundary_H H t = I ↔ t = 2))
    (h_seg5_ne_I : ∀ {t : ℝ}, 4 < t → t ≤ 5 → fdBoundary_H H t ≠ I)
    (hγ3_ne_I : fdBoundary_H H 3 ≠ I) :
    CauchyPrincipalValueExists' (fun z => (z - I)⁻¹) (fdBoundary_H H) 0 5 I := by
  apply cpv_extend_to_full_interval H hH I (3/2) (5/2) (by norm_num) (by norm_num)
    (by norm_num) h_arc_cpv
  · intro t ht h_eq
    by_cases ht1 : t ≤ 1
    · have := fdBoundary_H_seg1_re' H ht.1 ht1
      rw [h_eq] at this; norm_num at this
    · push Not at ht1
      rw [(h_arc_I_iff ht1 (by linarith [ht.2])).mp h_eq] at ht
      linarith [ht.2]
  · intro t ht h_eq
    by_cases ht3 : t < 3
    · have ht1 : 1 < t := by linarith [ht.1]
      rw [(h_arc_I_iff ht1 ht3).mp h_eq] at ht
      linarith [ht.1]
    · push Not at ht3
      by_cases ht4 : t ≤ 4
      · rcases eq_or_lt_of_le ht3 with rfl | ht3'
        · exact hγ3_ne_I h_eq
        · have := fdBoundary_H_seg4_re' H ht3' ht4
          rw [h_eq] at this; norm_num at this
      · push Not at ht4
        exact h_seg5_ne_I ht4 ht.2 h_eq

private theorem cpv_exists_at_I_H_eq_one (hH : Real.sqrt 3 / 2 < (1 : ℝ))
    (h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
        (fdBoundary_H 1) (3/2) (5/2) I)
    (h_arc_I_iff : ∀ {t : ℝ}, 1 < t → t < 3 → (fdBoundary_H 1 t = I ↔ t = 2))
    (hγ3_ne_I : fdBoundary_H 1 3 ≠ I) :
    CauchyPrincipalValueExists' (fun z => (z - I)⁻¹) (fdBoundary_H 1) 0 5 I := by
  have hγ92 : fdBoundary_H 1 (9/2) = I := by
    rw [fdBoundary_H_eq_seg5_H (by norm_num : (4:ℝ) < 9/2)]; simp [fdBoundary_seg5_H]
  have h_seg5_cpv : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
      (fdBoundary_H 1) (17/4) (19/4) I := by
    apply cpv_exists_on_smooth_subinterval 1 hH I
      (⟨by norm_num, by norm_num⟩ : (9/2:ℝ) ∈ Set.Ioo (17/4:ℝ) (19/4)) hγ92
    · refine ContDiffAt.congr_of_eventuallyEq (f := fdBoundary_seg5_H 1) ?_
        (Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioi 4,
          Ioi_mem_nhds (by norm_num : (4:ℝ) < 9/2),
          fun s (hs : 4 < s) => fdBoundary_H_eq_seg5_H hs⟩)
      unfold fdBoundary_seg5_H
      exact (Complex.ofRealCLM.contDiff.contDiffAt.sub contDiffAt_const).add contDiffAt_const
    · exact (fdBoundary_H_hasDerivAt_seg5 1 (show (4:ℝ) < 9/2 by norm_num)).deriv ▸
        one_ne_zero
    · exact (fdBoundary_H_deriv_continuousOn_Ioo_45 1).mono fun t ht =>
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht hγt
      have ht4 : 4 < t := by linarith [ht.1]
      have ht5 : t ≤ 5 := by linarith [ht.2]
      have h_re_t := fdBoundary_H_seg5_re' 1 ht4 ht5
      have h_re_92 := fdBoundary_H_seg5_re' 1
        (show (4:ℝ) < 9/2 by norm_num) (show (9:ℝ)/2 ≤ 5 by norm_num)
      have : (fdBoundary_H 1 t).re = (fdBoundary_H 1 (9/2)).re := by rw [hγt]
      linarith
  have h_cpv_0_52 : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
      (fdBoundary_H 1) 0 (5/2) I :=
    cpv_concat_cutout 1 hH I 0 (3/2) (5/2)
      (cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous 1).continuousOn (by norm_num) (by
        intro t ht h_eq
        by_cases ht1 : t ≤ 1
        · have := fdBoundary_H_seg1_re' 1 ht.1 ht1
          rw [h_eq] at this; norm_num at this
        · push Not at ht1
          rw [(h_arc_I_iff ht1 (by linarith [ht.2])).mp h_eq] at ht
          linarith [ht.2]))
      h_arc_cpv (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h_cpv_52_194 : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
      (fdBoundary_H 1) (5/2) (19/4) I :=
    cpv_concat_cutout 1 hH I (5/2) (17/4) (19/4)
      (cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous 1).continuousOn (by norm_num) (by
        intro t ht h_eq
        by_cases ht3 : t < 3
        · have ht1 : 1 < t := by linarith [ht.1]
          rw [(h_arc_I_iff ht1 ht3).mp h_eq] at ht
          linarith [ht.1]
        · push Not at ht3
          by_cases ht4 : t ≤ 4
          · rcases eq_or_lt_of_le ht3 with rfl | ht3'
            · exact hγ3_ne_I h_eq
            · have := fdBoundary_H_seg4_re' 1 ht3' ht4
              rw [h_eq] at this; norm_num at this
          · push Not at ht4
            have := fdBoundary_H_seg5_re' 1 ht4 (by linarith [ht.2])
            rw [h_eq] at this; simp at this; linarith [ht.2]))
      h_seg5_cpv (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h_cpv_0_194 : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
      (fdBoundary_H 1) 0 (19/4) I :=
    cpv_concat_cutout 1 hH I 0 (5/2) (19/4) h_cpv_0_52 h_cpv_52_194
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h_cpv_194_5 : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
      (fdBoundary_H 1) (19/4) 5 I := by
    apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous 1).continuousOn (by norm_num)
    intro t ht h_eq
    have ht4 : 4 < t := by linarith [ht.1]
    have := fdBoundary_H_seg5_re' 1 ht4 ht.2
    rw [h_eq] at this; simp at this; linarith [ht.1]
  exact cpv_concat_cutout 1 hH I 0 (19/4) 5 h_cpv_0_194 h_cpv_194_5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem cpv_exists_generic_seg1 (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ)
    (ht₀_mem : 0 ≤ t₀ ∧ t₀ ≤ 5) (hγt₀ : fdBoundary_H H t₀ = s)
    (ht₀_ne_0 : t₀ ≠ 0)
    (ht₀_lt_1 : t₀ < 1) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s := by
  have ht₀_gt_0 : 0 < t₀ := ht₀_mem.1.lt_of_ne ht₀_ne_0.symm
  apply cpv_extend_to_full_interval H hH s (t₀ / 2) ((t₀ + 1) / 2)
    (by linarith) (by linarith) (by linarith)
  · apply cpv_exists_on_smooth_subinterval H hH s
      ⟨by linarith, by linarith⟩ hγt₀
    · have heq : fdBoundary_H H =ᶠ[𝓝 t₀]
          (fun t => (1/2 : ℂ) + ↑(H - t * (H - Real.sqrt 3 / 2)) * I) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Iio 1, Iio_mem_nhds ht₀_lt_1,
          fun t ht => by rw [fdBoundary_H_eq_seg1_H ht.le]; simp [fdBoundary_seg1_H]⟩
      exact ContDiffAt.congr_of_eventuallyEq
        (contDiffAt_const.add ((Complex.ofRealCLM.contDiff.contDiffAt.comp t₀
          (contDiffAt_const.sub (contDiffAt_id.mul contDiffAt_const))).mul contDiffAt_const)) heq
    · exact (fdBoundary_H_hasDerivAt_seg1 H ht₀_lt_1).deriv ▸
        mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hH.ne'))) I_ne_zero
    · exact (fdBoundary_H_deriv_continuousOn_Ioo_01 H).mono fun t ht =>
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht hγt
      have ht1 : t ≤ 1 := by linarith [ht.2]
      rw [fdBoundary_H_eq_seg1_H ht1,
          fdBoundary_H_eq_seg1_H ht₀_lt_1.le] at hγt
      simp only [fdBoundary_seg1_H] at hγt
      have h_im := congr_arg Complex.im hγt
      simp at h_im
      rcases h_im with rfl | h_abs
      · rfl
      · linarith
  · intro t ht h_eq
    have ht1 : t ≤ 1 := by linarith [ht.2]
    rw [fdBoundary_H_eq_seg1_H ht1,
        ← hγt₀, fdBoundary_H_eq_seg1_H ht₀_lt_1.le] at h_eq
    simp only [fdBoundary_seg1_H] at h_eq
    have h_im := congr_arg Complex.im h_eq
    simp at h_im
    rcases h_im with rfl | h_abs
    · linarith [ht.2]
    · linarith
  · have h_re_s : s.re = 1/2 := by
      rw [← hγt₀]; exact fdBoundary_H_seg1_re' H ht₀_gt_0.le ht₀_lt_1.le
    have h_im_s_lt : s.im < H := by
      rw [← hγt₀, fdBoundary_H_eq_seg1_H ht₀_lt_1.le]
      simp [fdBoundary_seg1_H]; nlinarith
    have h_norm_s_gt : 1 < Complex.normSq s := by
      rw [Complex.normSq_apply, h_re_s]
      have h_im_s_gt : Real.sqrt 3 / 2 < s.im := by
        rw [← hγt₀, fdBoundary_H_eq_seg1_H ht₀_lt_1.le]
        simp [fdBoundary_seg1_H]; nlinarith
      nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 3 by norm_num),
        mul_self_lt_mul_self (by positivity : (0:ℝ) ≤ Real.sqrt 3 / 2) h_im_s_gt]
    intro t ht h_eq
    by_cases ht1 : t ≤ 1
    · rw [fdBoundary_H_eq_seg1_H ht1,
          ← hγt₀, fdBoundary_H_eq_seg1_H ht₀_lt_1.le] at h_eq
      simp only [fdBoundary_seg1_H] at h_eq
      have h_im := congr_arg Complex.im h_eq
      simp at h_im
      rcases h_im with rfl | h_abs
      · linarith [ht.1]
      · linarith
    · push Not at ht1
      by_cases ht3 : t < 3
      · have h_norm_arc : Complex.normSq (fdBoundary_H H t) = 1 := by
          rw [fdBoundary_H_eq_arc ht1 ht3, Complex.normSq_apply,
            Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
          linarith [Real.sin_sq_add_cos_sq (Real.pi * (1 + t) / 6)]
        rw [h_eq] at h_norm_arc; linarith
      · push Not at ht3
        by_cases ht4 : t ≤ 4
        · rcases eq_or_lt_of_le ht3 with rfl | ht3'
          · rw [fdBoundary_H_at_three_eq_rho] at h_eq; exact hs_rho h_eq.symm
          · have h_re_t := fdBoundary_H_seg4_re' H ht3' ht4
            rw [h_eq] at h_re_t; linarith
        · push Not at ht4
          have h_im_t := fdBoundary_H_seg5_im' H ht4 ht.2
          rw [h_eq] at h_im_t; linarith

private theorem cpv_exists_generic_arc_seg5_cross (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ)
    (hγt₀ : fdBoundary_H H t₀ = s)
    (ht₀_gt_1 : 1 < t₀) (ht₀_lt_3 : t₀ < 3)
    (h_re_s_lt : s.re < 1/2) (h_re_s_gt : -(1:ℝ)/2 < s.re)
    (h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
        (fdBoundary_H H) ((t₀ + 1) / 2) ((t₀ + 3) / 2) s)
    (h_seg5_cross : s.im = H) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s := by
  set t₁ := s.re + 9/2 with ht₁_def
  have ht₁_gt4 : 4 < t₁ := by simp [ht₁_def]; linarith [h_re_s_gt]
  have ht₁_lt5 : t₁ < 5 := by simp [ht₁_def]; linarith [h_re_s_lt]
  have hγt₁ : fdBoundary_H H t₁ = s := by
    rw [fdBoundary_H_eq_seg5_H (by linarith : 4 < t₁)]
    refine Complex.ext ?_ ?_ <;> simp [fdBoundary_seg5_H, ht₁_def, h_seg5_cross]
  have h_seg5_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) ((t₁ + 4) / 2) ((t₁ + 5) / 2) s := by
    apply cpv_exists_on_smooth_subinterval H hH s
      ⟨by linarith, by linarith⟩ hγt₁
    · have heq : fdBoundary_H H =ᶠ[𝓝 t₁] (fun t => (↑(t - 9/2) : ℂ) + ↑H * I) :=
        Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Set.Ioi 4, Ioi_mem_nhds ht₁_gt4, fun u (hu : 4 < u) => by
            rw [fdBoundary_H_eq_seg5_H hu]; simp [fdBoundary_seg5_H]⟩
      exact ContDiffAt.congr_of_eventuallyEq ((Complex.ofRealCLM.contDiff.contDiffAt.comp t₁
        (contDiffAt_id.sub contDiffAt_const)).add contDiffAt_const) heq
    · exact (fdBoundary_H_hasDerivAt_seg5 H ht₁_gt4).deriv ▸ one_ne_zero
    · exact (fdBoundary_H_deriv_continuousOn_Ioo_45 H).mono fun t ht =>
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht hγt
      have h_re_t := fdBoundary_H_seg5_re' H (by linarith [ht.1] : 4 < t) (by linarith [ht.2])
      have h_re_t₁ := fdBoundary_H_seg5_re' H ht₁_gt4 ht₁_lt5.le
      have : (fdBoundary_H H t).re = (fdBoundary_H H t₁).re := by rw [hγt]
      linarith
  have h_cpv_0_t0h : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) 0 ((t₀ + 3) / 2) s :=
    cpv_concat_cutout H hH s 0 ((t₀ + 1) / 2) ((t₀ + 3) / 2)
      (cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous H).continuousOn (by linarith) (by
        intro t ht h_eq
        by_cases ht1 : t ≤ 1
        · have := fdBoundary_H_seg1_re' H ht.1 ht1
          rw [h_eq] at this; linarith
        · push Not at ht1
          have ht3 : t < 3 := by linarith [ht.2]
          have h_ne : t ≠ t₀ := by linarith [ht.2]
          exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₀_gt_1, ht₀_lt_3⟩ (by
            have := h_eq.trans hγt₀.symm
            rwa [fdBoundary_H_eq_arc ht1 ht3, fdBoundary_H_eq_arc ht₀_gt_1 ht₀_lt_3] at this))))
      h_arc_cpv (by linarith) (by linarith) (by linarith) (by linarith)
  have h_cpv_mid_avoid : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) ((t₀ + 3) / 2) ((t₁ + 4) / 2) s := by
    apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous H).continuousOn (by linarith)
    intro t ht h_eq
    by_cases ht3 : t < 3
    · have ht1 : 1 < t := by linarith [ht.1]
      have h_ne : t ≠ t₀ := by linarith [ht.1]
      exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₀_gt_1, ht₀_lt_3⟩ (by
        have := h_eq.trans hγt₀.symm
        rwa [fdBoundary_H_eq_arc ht1 ht3, fdBoundary_H_eq_arc ht₀_gt_1 ht₀_lt_3] at this))
    · push Not at ht3
      by_cases ht4 : t ≤ 4
      · rcases eq_or_lt_of_le ht3 with rfl | ht3'
        · rw [fdBoundary_H_at_three_eq_rho] at h_eq; exact hs_rho h_eq.symm
        · have := fdBoundary_H_seg4_re' H ht3' ht4
          rw [h_eq] at this; linarith
      · push Not at ht4
        have := fdBoundary_H_seg5_re' H ht4 (by linarith [ht.2])
        rw [h_eq] at this; simp [ht₁_def] at *
        linarith [ht.2]
  have h_cpv_mid : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) ((t₀ + 3) / 2) ((t₁ + 5) / 2) s :=
    cpv_concat_cutout H hH s ((t₀ + 3) / 2) ((t₁ + 4) / 2) ((t₁ + 5) / 2)
      h_cpv_mid_avoid h_seg5_cpv (by linarith) (by linarith) (by linarith) (by linarith)
  have h_cpv_0_t1h : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) 0 ((t₁ + 5) / 2) s :=
    cpv_concat_cutout H hH s 0 ((t₀ + 3) / 2) ((t₁ + 5) / 2)
      h_cpv_0_t0h h_cpv_mid (by linarith) (by linarith) (by linarith) (by linarith)
  have h_cpv_end : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) ((t₁ + 5) / 2) 5 s := by
    apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous H).continuousOn (by linarith)
    intro t ht h_eq
    have ht4 : 4 < t := by linarith [ht.1]
    have := fdBoundary_H_seg5_re' H ht4 ht.2
    rw [h_eq] at this; simp [ht₁_def] at *
    linarith [ht.1]
  exact cpv_concat_cutout H hH s 0 ((t₁ + 5) / 2) 5 h_cpv_0_t1h h_cpv_end
    (by linarith) (by linarith) (by linarith) (by linarith)

private theorem cpv_exists_generic_arc_no_cross (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ)
    (hγt₀ : fdBoundary_H H t₀ = s)
    (ht₀_gt_1 : 1 < t₀) (ht₀_lt_3 : t₀ < 3)
    (h_re_s_lt : s.re < 1/2) (h_re_s_gt : -(1:ℝ)/2 < s.re)
    (h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
        (fdBoundary_H H) ((t₀ + 1) / 2) ((t₀ + 3) / 2) s)
    (h_seg5_cross : ¬(s.im = H)) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s := by
  apply cpv_extend_to_full_interval H hH s ((t₀ + 1) / 2) ((t₀ + 3) / 2)
    (by linarith) (by linarith) (by linarith) h_arc_cpv
  · intro t ht h_eq
    by_cases ht1 : t ≤ 1
    · have := fdBoundary_H_seg1_re' H ht.1 ht1
      rw [h_eq] at this; linarith
    · push Not at ht1
      have ht3 : t < 3 := by linarith [ht.2]
      have h_ne : t ≠ t₀ := by linarith [ht.2]
      exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₀_gt_1, ht₀_lt_3⟩ (by
        have := h_eq.trans hγt₀.symm
        rwa [fdBoundary_H_eq_arc ht1 ht3, fdBoundary_H_eq_arc ht₀_gt_1 ht₀_lt_3] at this))
  · intro t ht h_eq
    by_cases ht3 : t < 3
    · have ht1 : 1 < t := by linarith [ht.1]
      have h_ne : t ≠ t₀ := by linarith [ht.1]
      exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₀_gt_1, ht₀_lt_3⟩ (by
        have := h_eq.trans hγt₀.symm
        rwa [fdBoundary_H_eq_arc ht1 ht3, fdBoundary_H_eq_arc ht₀_gt_1 ht₀_lt_3] at this))
    · push Not at ht3
      by_cases ht4 : t ≤ 4
      · rcases eq_or_lt_of_le ht3 with rfl | ht3'
        · rw [fdBoundary_H_at_three_eq_rho] at h_eq; exact hs_rho h_eq.symm
        · have := fdBoundary_H_seg4_re' H ht3' ht4
          rw [h_eq] at this; linarith
      · push Not at ht4
        have := fdBoundary_H_seg5_im' H ht4 ht.2
        rw [h_eq] at this; exact h_seg5_cross this

private theorem cpv_exists_generic_arc (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ)
    (hγt₀ : fdBoundary_H H t₀ = s)
    (ht₀_gt_1 : 1 < t₀) (ht₀_lt_3 : t₀ < 3) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s := by
  have h_re_s : s.re = Real.cos (Real.pi * (1 + t₀) / 6) := by
    rw [← hγt₀]; exact fdBoundary_H_arc_re' H ht₀_gt_1 ht₀_lt_3
  have h_im_s_arc : s.im = Real.sin (Real.pi * (1 + t₀) / 6) := by
    rw [← hγt₀]; exact fdBoundary_H_arc_im' H ht₀_gt_1 ht₀_lt_3
  have h_normSq_s : Complex.normSq s = 1 := by
    rw [Complex.normSq_apply, h_re_s, h_im_s_arc]
    linarith [Real.sin_sq_add_cos_sq (Real.pi * (1 + t₀) / 6)]
  have h_re_s_lt : s.re < 1/2 := by
    rw [h_re_s]
    have h1 : Real.pi * (1 + t₀) / 6 ∈ Set.Icc 0 Real.pi :=
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    have h2 : Real.pi / 3 ∈ Set.Icc 0 Real.pi :=
      ⟨by positivity, by linarith [Real.pi_pos]⟩
    have := Real.strictAntiOn_cos h2 h1 (by nlinarith [Real.pi_pos])
    linarith [Real.cos_pi_div_three]
  have h_re_s_gt : -(1:ℝ)/2 < s.re := by
    rw [h_re_s]
    have h1 : Real.pi * (1 + t₀) / 6 ∈ Set.Icc 0 Real.pi :=
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    have h2 : Real.pi * 2 / 3 ∈ Set.Icc 0 Real.pi :=
      ⟨by positivity, by nlinarith [Real.pi_pos]⟩
    have := Real.strictAntiOn_cos h1 h2 (by nlinarith [Real.pi_pos])
    have h_cos23 : Real.cos (Real.pi * 2 / 3) = -(1:ℝ)/2 := by
      rw [show Real.pi * 2 / 3 = Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three]
      ring
    linarith
  have h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) ((t₀ + 1) / 2) ((t₀ + 3) / 2) s :=
    arc_smooth_cpv H hH s ht₀_gt_1 ht₀_lt_3 (by linarith) (by linarith)
      (by linarith) (by linarith) hγt₀
  by_cases h_seg5_cross : s.im = H
  · exact cpv_exists_generic_arc_seg5_cross H hH s hs_rho t₀ hγt₀
      ht₀_gt_1 ht₀_lt_3 h_re_s_lt h_re_s_gt h_arc_cpv h_seg5_cross
  · exact cpv_exists_generic_arc_no_cross H hH s hs_rho t₀ hγt₀
      ht₀_gt_1 ht₀_lt_3 h_re_s_lt h_re_s_gt h_arc_cpv h_seg5_cross

private theorem cpv_exists_generic_seg4 (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ)
    (hγt₀ : fdBoundary_H H t₀ = s)
    (ht₀_gt_3 : 3 < t₀) (ht₀_lt_4 : t₀ < 4) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s := by
  apply cpv_extend_to_full_interval H hH s ((t₀ + 3) / 2) ((t₀ + 4) / 2)
    (by linarith) (by linarith) (by linarith)
  · apply cpv_exists_on_smooth_subinterval H hH s
      ⟨by linarith, by linarith⟩ hγt₀
    · have heq : fdBoundary_H H =ᶠ[𝓝 t₀] (fun t => -(1/2 : ℂ) +
            ↑(Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2)) * I) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 3 4,
          Ioo_mem_nhds ht₀_gt_3 ht₀_lt_4, fun u hu => by
            rw [fdBoundary_H_eq_seg4_H hu.1 hu.2.le]
            simp [fdBoundary_seg4_H]; norm_num⟩
      exact ContDiffAt.congr_of_eventuallyEq (contDiffAt_const.add
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp t₀ (contDiffAt_const.add
          ((contDiffAt_id.sub contDiffAt_const).mul contDiffAt_const))).mul contDiffAt_const)) heq
    · exact (fdBoundary_H_hasDerivAt_seg4 H ht₀_gt_3 ht₀_lt_4).deriv ▸
        mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hH.ne')) I_ne_zero
    · exact (fdBoundary_H_deriv_continuousOn_Ioo_34 H).mono fun t ht =>
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht hγt
      have h_im_t : (fdBoundary_H H t).im =
          Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2) := by
        rw [fdBoundary_H_eq_seg4_H (by linarith [ht.1]) (by linarith [ht.2])]
        simp [fdBoundary_seg4_H]
      have h_im_t₀ : (fdBoundary_H H t₀).im =
          Real.sqrt 3 / 2 + (t₀ - 3) * (H - Real.sqrt 3 / 2) := by
        rw [fdBoundary_H_eq_seg4_H ht₀_gt_3 ht₀_lt_4.le]; simp [fdBoundary_seg4_H]
      have h_im_eq : (fdBoundary_H H t).im = (fdBoundary_H H t₀).im := by rw [hγt]
      rw [h_im_t, h_im_t₀] at h_im_eq
      have hH_pos : (0:ℝ) < H - Real.sqrt 3 / 2 := by linarith
      linarith [mul_right_cancel₀ hH_pos.ne'
        (show (t - 3) * (H - Real.sqrt 3 / 2) = (t₀ - 3) * (H - Real.sqrt 3 / 2) by linarith)]
  · have h_re_s : s.re = -1/2 := by
      rw [← hγt₀]; exact fdBoundary_H_seg4_re' H ht₀_gt_3 ht₀_lt_4.le
    have h_norm_s_gt : 1 < Complex.normSq s := by
      rw [Complex.normSq_apply, h_re_s]
      have h_im_s_gt : Real.sqrt 3 / 2 < s.im := by
        rw [← hγt₀, fdBoundary_H_eq_seg4_H (by linarith : 3 < t₀) ht₀_lt_4.le]
        simp [fdBoundary_seg4_H]; nlinarith
      nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 3 by norm_num),
        mul_self_lt_mul_self (by positivity : (0:ℝ) ≤ Real.sqrt 3 / 2) h_im_s_gt]
    intro t ht h_eq
    by_cases ht1 : t ≤ 1
    · have := fdBoundary_H_seg1_re' H ht.1 ht1
      rw [h_eq] at this; linarith
    · push Not at ht1
      by_cases ht3 : t < 3
      · have h_norm_arc : Complex.normSq (fdBoundary_H H t) = 1 := by
          rw [fdBoundary_H_eq_arc ht1 ht3, Complex.normSq_apply,
            Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
          linarith [Real.sin_sq_add_cos_sq (Real.pi * (1 + t) / 6)]
        rw [h_eq] at h_norm_arc; linarith
      · push Not at ht3
        by_cases ht4 : t ≤ 4
        · rcases eq_or_lt_of_le ht3 with rfl | ht3'
          · rw [fdBoundary_H_at_three_eq_rho] at h_eq; exact hs_rho h_eq.symm
          · rw [fdBoundary_H_eq_seg4_H (by linarith : 3 < t) ht4,
                ← hγt₀, fdBoundary_H_eq_seg4_H (by linarith : 3 < t₀)
                ht₀_lt_4.le] at h_eq
            simp only [fdBoundary_seg4_H] at h_eq
            have h_im := congr_arg Complex.im h_eq
            simp at h_im
            rcases h_im with rfl | h_abs
            · linarith [ht.2]
            · linarith
        · push Not at ht4
          linarith [ht.2]
  · have h_re_s : s.re = -1/2 := by
      rw [← hγt₀]; exact fdBoundary_H_seg4_re' H ht₀_gt_3 ht₀_lt_4.le
    intro t ht h_eq
    by_cases ht4' : 4 < t
    · have := fdBoundary_H_seg5_re' H ht4' ht.2
      rw [h_eq] at this; linarith
    · push Not at ht4'
      have ht3' : 3 < t := by linarith [ht.1]
      by_cases ht4_eq : t = 4
      · subst ht4_eq
        have h_im_eq : s.im = H := by
          rw [← h_eq, fdBoundary_H_at_four]
          simp
        rw [← hγt₀,
          fdBoundary_H_eq_seg4_H (by linarith) ht₀_lt_4.le] at h_im_eq
        simp [fdBoundary_seg4_H] at h_im_eq; nlinarith
      · rw [fdBoundary_H_eq_seg4_H (by linarith : 3 < t) (by linarith : t ≤ 4),
            ← hγt₀, fdBoundary_H_eq_seg4_H (by linarith : 3 < t₀)
            ht₀_lt_4.le] at h_eq
        simp only [fdBoundary_seg4_H] at h_eq
        have h_im := congr_arg Complex.im h_eq
        simp at h_im
        rcases h_im with rfl | h_abs
        · linarith [ht.1]
        · linarith

private theorem cpv_exists_generic_seg5_normSq_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_rho : ¬s = ellipticPointRho) (hs_endpoint : ¬s = 1 / 2 + ↑H * I)
    (t₀ : ℝ)
    (ht₀_gt_4 : 4 < t₀) (ht₀_lt_5 : t₀ < 5)
    (h_im_s : s.im = H) (h_re_s : s.re = t₀ - 9/2)
    (h_seg5_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
        (fdBoundary_H H) ((t₀ + 4) / 2) ((t₀ + 5) / 2) s)
    (h_normSq : Complex.normSq s = 1) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s := by
  have h_re_s_lt : s.re < 1/2 := by linarith [h_re_s]
  have h_re_s_gt : -(1:ℝ)/2 < s.re := by linarith [h_re_s]
  have h_ivt : s.re ∈ (fun t => Real.cos (Real.pi * (1 + t) / 6)) ''
      Set.Icc (1:ℝ) 3 := by
    apply intermediate_value_Icc' (by norm_num : (1:ℝ) ≤ 3)
    · exact (Real.continuous_cos.comp
        (by fun_prop : Continuous (fun t => Real.pi * (1 + t) / 6))).continuousOn
    · constructor
      · rw [show Real.pi * (1 + 3) / 6 = Real.pi - Real.pi / 3 by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]
        linarith
      · rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 by ring,
          Real.cos_pi_div_three]
        linarith
  obtain ⟨t₁, ht₁_mem, ht₁_cos⟩ := h_ivt
  beta_reduce at ht₁_cos
  have ht₁_gt1 : 1 < t₁ := ht₁_mem.1.lt_of_ne fun h => by
    rw [← h, show Real.pi * (1 + 1) / 6 = Real.pi / 3 by ring,
      Real.cos_pi_div_three] at ht₁_cos
    linarith
  have ht₁_lt3 : t₁ < 3 := ht₁_mem.2.lt_of_ne fun h => by
    rw [h, show Real.pi * (1 + 3) / 6 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at ht₁_cos
    linarith
  have hγt₁ : fdBoundary_H H t₁ = s := by
    rw [fdBoundary_H_eq_arc ht₁_gt1 ht₁_lt3]
    apply Complex.ext
    · rw [Complex.exp_ofReal_mul_I_re]; exact ht₁_cos
    · rw [Complex.exp_ofReal_mul_I_im]
      have h_sin_pos : 0 < Real.sin (Real.pi * (1 + t₁) / 6) :=
        Real.sin_pos_of_pos_of_lt_pi
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      refine (sq_eq_sq₀ h_sin_pos.le
        (by rw [h_im_s]; linarith [hH, Real.sqrt_nonneg 3] : (0:ℝ) ≤ s.im)).mp ?_
      have h1 := Real.sin_sq_add_cos_sq (Real.pi * (1 + t₁) / 6)
      rw [ht₁_cos] at h1
      rw [Complex.normSq_apply] at h_normSq
      nlinarith
  have h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) ((t₁ + 1) / 2) ((t₁ + 3) / 2) s :=
    arc_smooth_cpv H hH s ht₁_gt1 ht₁_lt3 (by linarith) (by linarith)
      (by linarith) (by linarith) hγt₁
  have h_avoid_start : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) 0 ((t₁ + 1) / 2) s := by
    apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous H).continuousOn (by linarith)
    intro t ht h_eq
    by_cases ht0 : t = 0
    · subst ht0; exact hs_endpoint (by rw [← h_eq, fdBoundary_H_at_zero])
    · by_cases ht1 : t ≤ 1
      · have h_im_t : (fdBoundary_H H t).im < H := by
          rw [fdBoundary_H_eq_seg1_H ht1]
          simp [fdBoundary_seg1_H]; nlinarith [ht.1, ht.1.lt_of_ne (Ne.symm ht0)]
        rw [h_eq] at h_im_t; linarith [h_im_s]
      · push Not at ht1
        have ht3 : t < 3 := by linarith [ht.2]
        have h_ne : t ≠ t₁ := by linarith [ht.2]
        exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₁_gt1, ht₁_lt3⟩ (by
          have := h_eq.trans hγt₁.symm
          rwa [fdBoundary_H_eq_arc ht1 ht3, fdBoundary_H_eq_arc ht₁_gt1 ht₁_lt3] at this))
  have h_cpv_0_t1h : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) 0 ((t₁ + 3) / 2) s :=
    cpv_concat_cutout H hH s 0 ((t₁ + 1) / 2) ((t₁ + 3) / 2)
      h_avoid_start h_arc_cpv (by linarith) (by linarith) (by linarith) (by linarith)
  have h_avoid_mid : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) ((t₁ + 3) / 2) ((t₀ + 4) / 2) s := by
    apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous H).continuousOn (by linarith)
    intro t ht h_eq
    by_cases ht3 : t < 3
    · have ht1 : 1 < t := by linarith [ht.1]
      have h_ne : t ≠ t₁ := by linarith [ht.1]
      exact h_ne (arc_angle_injective ⟨ht1, ht3⟩ ⟨ht₁_gt1, ht₁_lt3⟩ (by
        have := h_eq.trans hγt₁.symm
        rwa [fdBoundary_H_eq_arc ht1 ht3, fdBoundary_H_eq_arc ht₁_gt1 ht₁_lt3] at this))
    · push Not at ht3
      by_cases ht4 : t ≤ 4
      · rcases eq_or_lt_of_le ht3 with rfl | ht3'
        · rw [fdBoundary_H_at_three_eq_rho] at h_eq; exact hs_rho h_eq.symm
        · have := fdBoundary_H_seg4_re' H ht3' ht4
          rw [h_eq] at this; linarith [h_re_s]
      · push Not at ht4
        have := fdBoundary_H_seg5_re' H ht4 (by linarith [ht.2])
        rw [h_eq] at this; linarith [h_re_s, ht.2]
  have h_cpv_mid : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) ((t₁ + 3) / 2) ((t₀ + 5) / 2) s :=
    cpv_concat_cutout H hH s ((t₁ + 3) / 2) ((t₀ + 4) / 2) ((t₀ + 5) / 2)
      h_avoid_mid h_seg5_cpv (by linarith) (by linarith) (by linarith) (by linarith)
  have h_cpv_0_t0h : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) 0 ((t₀ + 5) / 2) s :=
    cpv_concat_cutout H hH s 0 ((t₁ + 3) / 2) ((t₀ + 5) / 2)
      h_cpv_0_t1h h_cpv_mid (by linarith) (by linarith) (by linarith) (by linarith)
  have h_cpv_end : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) ((t₀ + 5) / 2) 5 s := by
    apply cpv_avoidance _ _ _ _ _ (fdBoundary_H_continuous H).continuousOn (by linarith)
    intro t ht h_eq
    have ht4 : 4 < t := by linarith [ht.1]
    have := fdBoundary_H_seg5_re' H ht4 ht.2
    rw [h_eq] at this; linarith [h_re_s, ht.1]
  exact cpv_concat_cutout H hH s 0 ((t₀ + 5) / 2) 5 h_cpv_0_t0h h_cpv_end
    (by linarith) (by linarith) (by linarith) (by linarith)

private theorem cpv_exists_generic_seg5_normSq_ne_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_rho : ¬s = ellipticPointRho)
    (t₀ : ℝ)
    (ht₀_gt_4 : 4 < t₀) (ht₀_lt_5 : t₀ < 5)
    (h_re_s : s.re = t₀ - 9/2)
    (h_seg5_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
        (fdBoundary_H H) ((t₀ + 4) / 2) ((t₀ + 5) / 2) s)
    (h_normSq : ¬Complex.normSq s = 1)
    (hs_endpoint : ¬s = 1 / 2 + ↑H * I)
    (h_im_s : s.im = H) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s := by
  apply cpv_extend_to_full_interval H hH s ((t₀ + 4) / 2) ((t₀ + 5) / 2)
    (by linarith) (by linarith) (by linarith) h_seg5_cpv
  · intro t ht h_eq
    by_cases ht0 : t = 0
    · subst ht0; exact hs_endpoint (by rw [← h_eq, fdBoundary_H_at_zero])
    · by_cases ht1 : t ≤ 1
      · have h_im_t : (fdBoundary_H H t).im < H := by
          rw [fdBoundary_H_eq_seg1_H ht1]
          simp [fdBoundary_seg1_H]; nlinarith [ht.1, ht.1.lt_of_ne (Ne.symm ht0)]
        rw [h_eq] at h_im_t; linarith [h_im_s]
      · push Not at ht1
        by_cases ht3 : t < 3
        · have h_norm_arc : Complex.normSq (fdBoundary_H H t) = 1 := by
            rw [fdBoundary_H_eq_arc ht1 ht3, Complex.normSq_apply,
              Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
            linarith [Real.sin_sq_add_cos_sq (Real.pi * (1 + t) / 6)]
          rw [h_eq] at h_norm_arc; exact h_normSq h_norm_arc
        · push Not at ht3
          by_cases ht4 : t ≤ 4
          · rcases eq_or_lt_of_le ht3 with rfl | ht3'
            · rw [fdBoundary_H_at_three] at h_eq; exact hs_rho h_eq.symm
            · have := fdBoundary_H_seg4_re' H ht3' ht4
              rw [h_eq] at this; linarith [h_re_s]
          · push Not at ht4
            have := fdBoundary_H_seg5_re' H ht4 (by linarith [ht.2])
            rw [h_eq] at this; linarith [h_re_s, ht.2]
  · intro t ht h_eq
    have ht4 : 4 < t := by linarith [ht.1]
    have := fdBoundary_H_seg5_re' H ht4 ht.2
    rw [h_eq] at this; linarith [h_re_s, ht.1]

private theorem cpv_exists_generic_seg5 (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_rho : ¬s = ellipticPointRho) (t₀ : ℝ)
    (ht₀_mem : 0 ≤ t₀ ∧ t₀ ≤ 5) (hγt₀ : fdBoundary_H H t₀ = s)
    (hs_endpoint : ¬s = 1 / 2 + ↑H * I)
    (ht₀_ne_5 : t₀ ≠ 5)
    (ht₀_gt_4 : 4 < t₀) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s := by
  have ht₀_lt_5 : t₀ < 5 := ht₀_mem.2.lt_of_ne ht₀_ne_5
  have h_im_s : s.im = H := by
    rw [← hγt₀]; exact fdBoundary_H_seg5_im' H ht₀_gt_4 ht₀_lt_5.le
  have h_re_s : s.re = t₀ - 9/2 := by
    rw [← hγt₀]; exact fdBoundary_H_seg5_re' H ht₀_gt_4 ht₀_lt_5.le
  have h_seg5_cpv : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundary_H H) ((t₀ + 4) / 2) ((t₀ + 5) / 2) s := by
    apply cpv_exists_on_smooth_subinterval H hH s
      ⟨by linarith, by linarith⟩ hγt₀
    · have heq_fn : ∀ u ∈ Set.Ioi (4:ℝ), fdBoundary_H H u =
          (↑(u - 9/2) : ℂ) + ↑H * I := fun u (hu : 4 < u) => by
        rw [fdBoundary_H_eq_seg5_H hu]; simp [fdBoundary_seg5_H]
      have heq : fdBoundary_H H =ᶠ[𝓝 t₀] (fun t => (↑(t - 9/2) : ℂ) + ↑H * I) :=
        Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Set.Ioi 4, Ioi_mem_nhds ht₀_gt_4, heq_fn⟩
      exact ContDiffAt.congr_of_eventuallyEq ((Complex.ofRealCLM.contDiff.contDiffAt.comp t₀
        (contDiffAt_id.sub contDiffAt_const)).add contDiffAt_const) heq
    · exact (fdBoundary_H_hasDerivAt_seg5 H ht₀_gt_4).deriv ▸ one_ne_zero
    · exact (fdBoundary_H_deriv_continuousOn_Ioo_45 H).mono fun t ht =>
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht hγt
      have ht4 : 4 < t := by linarith [ht.1]
      have ht5 : t ≤ 5 := by linarith [ht.2]
      have h_re_t := fdBoundary_H_seg5_re' H ht4 ht5
      have h_re_t₀ := fdBoundary_H_seg5_re' H ht₀_gt_4 ht₀_lt_5.le
      have : (fdBoundary_H H t).re = (fdBoundary_H H t₀).re := by rw [hγt]
      linarith
  by_cases h_normSq : Complex.normSq s = 1
  · exact cpv_exists_generic_seg5_normSq_one H hH s hs_rho hs_endpoint t₀
      ht₀_gt_4 ht₀_lt_5 h_im_s h_re_s h_seg5_cpv h_normSq
  · exact cpv_exists_generic_seg5_normSq_ne_one H hH s hs_rho t₀
      ht₀_gt_4 ht₀_lt_5 h_re_s h_seg5_cpv h_normSq hs_endpoint h_im_s

/-- For any point on `fdBoundary_H H`, the CPV integral of `(z - s)⁻¹` exists. -/
theorem fdBoundary_H_cpv_exists_of_onCurve (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (h_on : ∃ t ∈ Set.Icc (0:ℝ) 5, fdBoundary_H H t = s) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s := by
  by_cases hs_rho : s = ellipticPointRho
  · subst hs_rho; exact cpv_exists_at_rho H hH
  by_cases hs_rho' : s = ellipticPointRhoPlusOne
  · subst hs_rho'; exact cpv_exists_at_rho_plus_one H hH
  by_cases hs_i : s = I
  · subst hs_i
    by_cases hH1 : 1 < H
    · exact cpv_exists_at_i H hH1
    · push Not at hH1
      have hγ2 : fdBoundary_H H 2 = I := by
        rw [fdBoundary_H_eq_arc (by norm_num : (1:ℝ) < 2) (by norm_num : (2:ℝ) < 3),
          show Real.pi * (1 + 2) / 6 = Real.pi / 2 by ring,
          show (↑(Real.pi / 2) : ℂ) * I = ↑Real.pi / 2 * I by push_cast; ring]
        exact Complex.exp_pi_div_two_mul_I
      have h_arc_cpv : CauchyPrincipalValueExists' (fun z => (z - I)⁻¹)
          (fdBoundary_H H) (3/2) (5/2) I :=
        arc_smooth_cpv H hH I (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) hγ2
      have h_arc_I_iff : ∀ {t : ℝ}, 1 < t → t < 3 →
          (fdBoundary_H H t = I ↔ t = 2) := by
        intro t ht1 ht3
        constructor
        · intro h_eq
          have h1 := fdBoundary_H_eq_arc (H := H) ht1 ht3
          have h2 := fdBoundary_H_eq_arc (H := H)
            (by norm_num : (1:ℝ) < 2) (by norm_num : (2:ℝ) < 3)
          exact arc_angle_injective ⟨ht1, ht3⟩ ⟨by norm_num, by norm_num⟩
            ((h1.symm.trans h_eq).trans (h2.symm.trans hγ2).symm)
        · rintro rfl; exact hγ2
      have hγ3_ne_I : fdBoundary_H H 3 ≠ I := by
        rw [fdBoundary_H_at_three H]; exact (hs_rho ·.symm)
      rcases hH1.lt_or_eq with hH_lt | hH_eq
      · refine cpv_exists_at_I_H_lt_one H hH h_arc_cpv h_arc_I_iff ?_ hγ3_ne_I
        intro t ht4 ht5 h_eq
        have := fdBoundary_H_seg5_im' H ht4 ht5
        rw [h_eq] at this; simp at this; linarith
      · subst hH_eq; exact cpv_exists_at_I_H_eq_one hH h_arc_cpv h_arc_I_iff hγ3_ne_I
  · obtain ⟨t₀, ht₀_mem, hγt₀⟩ := h_on
    by_cases hs_endpoint : s = (1/2 : ℂ) + ↑H * I
    · subst hs_endpoint; exact cpv_at_endpoint H hH
    by_cases hs_corner : s = -(1/2 : ℂ) + ↑H * I
    · subst hs_corner; exact cpv_at_corner H hH
    · have ht₀_ne_0 : t₀ ≠ 0 := by
        rintro rfl; exact hs_endpoint (by rw [← hγt₀, fdBoundary_H_at_zero])
      have ht₀_ne_1 : t₀ ≠ 1 := by
        rintro rfl; exact hs_rho' (by rw [← hγt₀, fdBoundary_H_at_one])
      have ht₀_ne_3 : t₀ ≠ 3 := by
        rintro rfl; exact hs_rho (by rw [← hγt₀, fdBoundary_H_at_three])
      have ht₀_ne_4 : t₀ ≠ 4 := by
        rintro rfl; exact hs_corner (by rw [← hγt₀, fdBoundary_H_at_four]; ring)
      have ht₀_ne_5 : t₀ ≠ 5 := by
        rintro rfl; exact hs_endpoint (by rw [← hγt₀, fdBoundary_H_at_five])
      rw [Set.mem_Icc] at ht₀_mem
      by_cases ht₀_lt_1 : t₀ < 1
      · exact cpv_exists_generic_seg1 H hH s hs_rho t₀
          ht₀_mem hγt₀ ht₀_ne_0 ht₀_lt_1
      · push Not at ht₀_lt_1
        have ht₀_gt_1 : 1 < t₀ := ht₀_lt_1.lt_of_ne ht₀_ne_1.symm
        by_cases ht₀_lt_3 : t₀ < 3
        · exact cpv_exists_generic_arc H hH s hs_rho t₀
            hγt₀ ht₀_gt_1 ht₀_lt_3
        · push Not at ht₀_lt_3
          have ht₀_gt_3 : 3 < t₀ := ht₀_lt_3.lt_of_ne ht₀_ne_3.symm
          by_cases ht₀_lt_4 : t₀ < 4
          · exact cpv_exists_generic_seg4 H hH s hs_rho t₀
              hγt₀ ht₀_gt_3 ht₀_lt_4
          · push Not at ht₀_lt_4
            have ht₀_gt_4 : 4 < t₀ := ht₀_lt_4.lt_of_ne ht₀_ne_4.symm
            exact cpv_exists_generic_seg5 H hH s hs_rho t₀
              ht₀_mem hγt₀ hs_endpoint ht₀_ne_5 ht₀_gt_4

end
