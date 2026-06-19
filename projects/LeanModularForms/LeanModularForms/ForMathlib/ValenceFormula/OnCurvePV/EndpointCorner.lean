/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ValenceFormula.OnCurvePV.Basic

/-!
# On-Curve PV: Endpoint and Corner CPV

Cauchy principal value existence at the endpoint `1/2 + H*I` and corner `-1/2 + H*I`
of the fundamental domain boundary `fdBoundary_H H`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Algebraic helper: `(a * b)⁻¹ * b = a⁻¹` for `b ≠ 0`. -/
private lemma mul_inv_rev_cancel (a b : ℂ) (hb : b ≠ 0) : (a * b)⁻¹ * b = a⁻¹ := by
  field_simp

/-- For `Real.sqrt 3 / 2 < H` and `r = ±1/2`, the point `r + H*I` has norm > 1. -/
private lemma one_lt_norm_corner (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_re : s.re ^ 2 = 1/4) (hs_im : s.im = H) : 1 < ‖s‖ := by
  have hH0 : 0 < H := by linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)]
  rw [show ‖s‖ = Real.sqrt (Complex.normSq s) from rfl, Real.lt_sqrt (by norm_num)]
  rw [Complex.normSq_apply, hs_im, show s.re * s.re = s.re ^ 2 from by ring, hs_re]
  nlinarith [mul_lt_mul hH hH.le (by positivity : (0:ℝ) < Real.sqrt 3 / 2) hH0.le,
             Real.mul_self_sqrt (show (0:ℝ) ≤ 3 by norm_num)]

/-- `∫ t in a..1, t⁻¹ = log 1 - log a` for `0 < a ≤ 1`. -/
private lemma integral_inv_eq_log_sub (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∫ t in a..1, (↑t : ℂ)⁻¹ = Complex.log ↑(1:ℝ) - Complex.log ↑a := by
  simp_rw [← Complex.ofReal_inv]
  rw [intervalIntegral.integral_ofReal]
  have hderiv : ∀ t ∈ Set.uIcc a 1,
      HasDerivAt (fun t ↦ Real.log t) (t⁻¹) t := by
    intro t ht
    rw [Set.uIcc_of_le ha1] at ht
    exact Real.hasDerivAt_log (by linarith [ht.1] : t ≠ 0)
  have hint : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) MeasureTheory.volume a 1 := by
    refine ContinuousOn.intervalIntegrable (ContinuousOn.inv₀ continuousOn_id fun t ht ↦ ?_)
    rw [Set.uIcc_of_le ha1, Set.mem_Icc] at ht; linarith [ht.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, Real.log_one,
    Complex.ofReal_one, Complex.log_one, ← Complex.ofReal_log ha.le]
  push_cast; ring

/-- `∫ t in 4..(5 - η), (t - 5)⁻¹ = log η` for `0 < η < 1`. -/
private lemma integral_shifted_inv_eq_log (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∫ t in (4:ℝ)..(5 - η), (↑(t - 5) : ℂ)⁻¹ = ↑(Real.log η) := by
  simp_rw [← Complex.ofReal_inv]
  rw [intervalIntegral.integral_ofReal]
  congr 1
  have h5η : (4:ℝ) ≤ 5 - η := by linarith
  have hderiv : ∀ t ∈ Set.uIcc 4 (5 - η),
      HasDerivAt (fun t ↦ Real.log (t - 5)) ((t - 5)⁻¹) t := by
    intro t ht
    rw [Set.uIcc_of_le h5η] at ht
    have : t - 5 ≠ 0 := ne_of_lt (by linarith [ht.2])
    have h1 := (Real.hasDerivAt_log this).comp t ((hasDerivAt_id t).sub_const 5)
    simp only [Function.comp_def, mul_one] at h1
    exact h1
  have hint : IntervalIntegrable (fun t ↦ (t - 5)⁻¹) MeasureTheory.volume 4 (5 - η) := by
    refine ContinuousOn.intervalIntegrable (ContinuousOn.inv₀
      (continuousOn_id.sub continuousOn_const) fun t ht ↦ ?_)
    rw [Set.uIcc_of_le h5η, Set.mem_Icc] at ht
    exact ne_of_lt (by linarith [ht.2])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [show 5 - η - 5 = -η by ring, show (4:ℝ) - 5 = -(1:ℝ) by ring]
  rw [Real.log_neg_eq_log, Real.log_neg_eq_log, Real.log_one, sub_zero]

/-- The endpoint `s = 1/2 + H*I` is not hit by segments 1--4 of `fdBoundary_H H`. -/
private lemma endpoint_avoid_14 (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    let s := (1/2 : ℂ) + ↑H * I
    ∀ t ∈ Set.Icc (1:ℝ) 4, fdBoundary_H H t ≠ s := by
  intro s t ht habs
  rw [Set.mem_Icc] at ht
  by_cases ht3 : t ≤ 3
  · by_cases ht1 : t = 1
    · subst ht1
      rw [fdBoundary_H_at_one] at habs
      have h_im := congr_arg Complex.im habs
      simp [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', s] at h_im
      linarith
    · have h_norm : ‖fdBoundary_H H t‖ = 1 :=
        fdBoundary_H_eq_arc (lt_of_le_of_ne ht.1 (Ne.symm ht1))
          (lt_of_le_of_ne ht3 (by
          intro h
          subst h
          rw [fdBoundary_H_at_three] at habs
          have him := congr_arg Complex.im habs
          simp [ellipticPointRho, ellipticPointRho', s] at him
          linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)])) |>.symm ▸
        Complex.norm_exp_ofReal_mul_I _
      rw [habs] at h_norm
      have : 1 < ‖s‖ := one_lt_norm_corner H hH s
        (by simp [s, Complex.add_re, Complex.mul_re]; ring)
        (by simp [s, Complex.add_im, Complex.mul_im])
      linarith
  · push Not at ht3
    have h_re_t := fdBoundary_H_seg4_re' H ht3 ht.2
    rw [habs] at h_re_t
    simp [s, Complex.add_re, Complex.mul_re] at h_re_t
    norm_num at h_re_t

/-- The endpoint `s = 1/2 + H*I` has positive distance to the boundary on `[1, 4]`. -/
private lemma endpoint_min_dist (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    let s := (1/2 : ℂ) + ↑H * I
    ∃ δ > 0, ∀ t ∈ Set.Icc (1:ℝ) 4, δ ≤ ‖fdBoundary_H H t - s‖ := by
  intro s
  have h_cont_norm : ContinuousOn (fun t ↦ ‖fdBoundary_H H t - s‖)
      (Set.Icc (1:ℝ) 4) := by fun_prop
  have h_pos_norm : ∀ t ∈ Set.Icc (1:ℝ) 4, 0 < ‖fdBoundary_H H t - s‖ :=
    fun t ht ↦ norm_pos_iff.mpr (sub_ne_zero.mpr (endpoint_avoid_14 H hH t ht))
  exact isCompact_Icc.exists_forall_le' h_cont_norm h_pos_norm

/-- Segment 1 difference: `fdBoundary_H H t - s = (-t) * c * I` for the endpoint. -/
private lemma endpoint_diff_seg1 (H : ℝ) (s : ℂ) (hs_def : s = (1/2 : ℂ) + ↑H * I)
    (c : ℝ) (hc_def : c = H - Real.sqrt 3 / 2) (t : ℝ) (ht1 : t ≤ 1) :
    fdBoundary_H H t - s = ↑((-t) * c) * I := by
  rw [fdBoundary_H_eq_seg1_H ht1, hs_def]
  simp only [fdBoundary_seg1_H, hc_def]; push_cast; ring

/-- Segment 5 difference: `fdBoundary_H H t - s = t - 5` for the endpoint. -/
private lemma endpoint_diff_seg5 (H : ℝ) (s : ℂ) (hs_def : s = (1/2 : ℂ) + ↑H * I)
    (t : ℝ) (ht4 : 4 < t) : fdBoundary_H H t - s = ↑(t - 5) := by
  rw [fdBoundary_H_eq_seg5_H ht4, hs_def]
  simp only [fdBoundary_seg5_H]; push_cast; ring

/-- Norm on seg1: `‖fdBoundary_H H t - s‖ = t * c` for the endpoint. -/
private lemma endpoint_norm_seg1 (H : ℝ) (s : ℂ) (hs_def : s = (1/2 : ℂ) + ↑H * I)
    (c : ℝ) (hc_def : c = H - Real.sqrt 3 / 2) (hc : 0 < c)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖fdBoundary_H H t - s‖ = t * c := by
  rw [endpoint_diff_seg1 H s hs_def c hc_def t ht1, norm_mul, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_of_nonpos (by nlinarith : (-t) * c ≤ 0)]
  ring

/-- Norm on seg5: `‖fdBoundary_H H t - s‖ = 5 - t` for the endpoint. -/
private lemma endpoint_norm_seg5 (H : ℝ) (s : ℂ) (hs_def : s = (1/2 : ℂ) + ↑H * I)
    (t : ℝ) (ht4 : 4 < t) (ht5 : t ≤ 5) : ‖fdBoundary_H H t - s‖ = 5 - t := by
  rw [endpoint_diff_seg5 H s hs_def t ht4, Complex.norm_real, Real.norm_of_nonpos (by linarith)]
  ring

/-- Integrand on seg1: `(γ t - s)⁻¹ * γ'(t) = t⁻¹` for the endpoint. -/
private lemma endpoint_integrand_seg1 (H : ℝ) (s : ℂ) (hs_def : s = (1/2 : ℂ) + ↑H * I)
    (c : ℝ) (hc_def : c = H - Real.sqrt 3 / 2) (hc : 0 < c) (t : ℝ) (ht1 : t < 1) :
    (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t = (↑t : ℂ)⁻¹ := by
  rw [endpoint_diff_seg1 H s hs_def c hc_def t ht1.le]
  erw [(fdBoundary_H_hasDerivAt_seg1 H ht1).deriv]
  have hc_eq : (↑H - ↑(Real.sqrt 3) / 2 : ℂ) = ↑c := by push_cast [hc_def]; ring
  rw [show (-(↑H - ↑(Real.sqrt 3) / 2 : ℂ)) * I = -(↑c : ℂ) * I from by rw [hc_eq],
    show (↑(-t * c) : ℂ) * I = ↑t * (-(↑c : ℂ) * I) from by push_cast; ring]
  exact mul_inv_rev_cancel ↑t _
    (mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hc.ne')) I_ne_zero)

/-- Integrand on seg5: `(γ t - s)⁻¹ * γ'(t) = (t - 5)⁻¹` for the endpoint. -/
private lemma endpoint_integrand_seg5 (H : ℝ) (s : ℂ) (hs_def : s = (1/2 : ℂ) + ↑H * I)
    (t : ℝ) (ht4 : 4 < t) :
    (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t = (↑(t - 5) : ℂ)⁻¹ := by
  rw [endpoint_diff_seg5 H s hs_def t ht4]
  erw [(fdBoundary_H_hasDerivAt_seg5 H ht4).deriv]
  rw [mul_one]

lemma cpv_at_endpoint (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    CauchyPrincipalValueExists' (fun z ↦ (z - ((1/2 : ℂ) + ↑H * I))⁻¹)
      (fdBoundary_H H) 0 5 ((1/2 : ℂ) + ↑H * I) := by
  set s := (1/2 : ℂ) + ↑H * I with hs_def
  set c := H - Real.sqrt 3 / 2 with hc_def
  have hc : 0 < c := sub_pos.mpr hH
  have hc_ne : c ≠ 0 := hc.ne'
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := endpoint_min_dist H hH
  set ε₀ := min c (min 1 δ)
  have hε₀ : 0 < ε₀ := lt_min hc (lt_min one_pos hδ_pos)
  set F := fun ε ↦ ∫ t in (0:ℝ)..5,
    if ε < ‖fdBoundary_H H t - s‖ then (fdBoundary_H H t - s)⁻¹ *
      deriv (fdBoundary_H H) t else 0
  set C := ∫ t in (1:ℝ)..4, (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t
  suffices h_ev : ∀ ε, 0 < ε → ε < ε₀ → F ε = F (ε₀ / 2) from
    ⟨F (ε₀ / 2), tendsto_const_nhds.congr'
      (Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioo 0 ε₀, Ioo_mem_nhdsGT hε₀,
        fun ε ⟨hε_pos, hε_lt⟩ ↦ (h_ev ε hε_pos hε_lt).symm⟩)⟩
  intro ε hε hε_lt
  have hε_c : ε < c := lt_of_lt_of_le hε_lt (min_le_left _ _)
  have hε_1 : ε < 1 := by linarith [min_le_right c (min 1 δ), min_le_left 1 δ]
  have hε_δ : ε < δ := by linarith [min_le_right c (min 1 δ), min_le_right 1 δ]
  have hε₀2_pos : 0 < ε₀ / 2 := by positivity
  have hε₀2_c : ε₀ / 2 < c := by linarith [min_le_left c (min 1 δ)]
  have hε₀2_1 : ε₀ / 2 < 1 := by linarith [min_le_right c (min 1 δ), min_le_left 1 δ]
  have hε₀2_δ : ε₀ / 2 < δ := by linarith [min_le_right c (min 1 δ), min_le_right 1 δ]
  suffices h_formula : ∀ η, 0 < η → η < c → η < 1 → η < δ →
      F η = ↑(Real.log c) + C by
    rw [h_formula ε hε hε_c hε_1 hε_δ,
      h_formula (ε₀/2) hε₀2_pos hε₀2_c hε₀2_1 hε₀2_δ]
  intro η hη hη_c hη_1 hη_δ
  have hη_div_c_pos : 0 < η / c := div_pos hη hc
  have hη_div_c_lt_1 : η / c < 1 := (div_lt_one hc).mpr hη_c
  have h_norm_seg1 : ∀ t, 0 ≤ t → t ≤ 1 → ‖fdBoundary_H H t - s‖ = t * c :=
    endpoint_norm_seg1 H s hs_def c hc_def hc
  have h_norm_seg5 : ∀ t, 4 < t → t ≤ 5 → ‖fdBoundary_H H t - s‖ = 5 - t :=
    endpoint_norm_seg5 H s hs_def
  have h_integrand_seg1 : ∀ t, t < 1 →
      (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t = (↑t : ℂ)⁻¹ :=
    endpoint_integrand_seg1 H s hs_def c hc_def hc
  have h_integrand_seg5 : ∀ t, 4 < t →
      (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t = (↑(t - 5) : ℂ)⁻¹ :=
    endpoint_integrand_seg5 H s hs_def
  have hii := fdBoundary_H_cutout_ii H hH s η hη
  have hii_sub : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ 5 →
      IntervalIntegrable (fun t ↦ if η < ‖fdBoundary_H H t - s‖
        then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) volume a b :=
    fun ha hab hb ↦ hii.mono_set <| by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc ha hb
  have h_split : F η = (∫ t in (0:ℝ)..1, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) +
    (∫ t in (1:ℝ)..4, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) +
    (∫ t in (4:ℝ)..5, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) := by
    change (∫ t in (0:ℝ)..5, _) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (hii_sub (by norm_num) (by norm_num) (by norm_num))
        (hii_sub (by norm_num) (by norm_num) (by norm_num) :
          IntervalIntegrable _ _ (1:ℝ) 5),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hii_sub (by norm_num) (by norm_num) (by norm_num) :
          IntervalIntegrable _ _ (1:ℝ) 4)
        (hii_sub (by norm_num) (by norm_num) (by norm_num) :
          IntervalIntegrable _ _ (4:ℝ) 5), ← add_assoc]
  have h_I14 : (∫ t in (1:ℝ)..4, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) = C :=
    intervalIntegral.integral_congr fun t ht ↦ by
      rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 4)] at ht
      exact if_pos (lt_of_lt_of_le hη_δ (hδ_bound t ht))
  have h_I01 : (∫ t in (0:ℝ)..1, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) =
    ∫ t in (η / c)..1, (↑t : ℂ)⁻¹ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hii_sub le_rfl hη_div_c_pos.le (by linarith))
      (hii_sub hη_div_c_pos.le hη_div_c_lt_1.le (by norm_num))]
    have h_zero : (∫ t in (0:ℝ)..(η / c),
        if η < ‖fdBoundary_H H t - s‖
        then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℂ)) (fun t ht ↦ by
        rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ η / c)] at ht
        rw [if_neg]
        push Not
        rw [h_norm_seg1 t ht.1 (by linarith [ht.2])]
        calc t * c ≤ (η / c) * c := mul_le_mul_of_nonneg_right ht.2 hc.le
          _ = η := by field_simp), intervalIntegral.integral_zero]
    rw [h_zero, zero_add]
    refine intervalIntegral.integral_congr_ae' ?_
      (by filter_upwards with t ht; exfalso; linarith [ht.1, ht.2])
    filter_upwards [compl_mem_ae_iff.mpr (show volume {η / c} = 0 by simp),
                    compl_mem_ae_iff.mpr (show volume {(1:ℝ)} = 0 by simp)]
      with t _ ht_ne_high ht
    have ht_high : t < 1 := lt_of_le_of_ne ht.2 fun h ↦ ht_ne_high (Set.mem_singleton_iff.mpr h)
    have ht_pos : 0 < t := lt_of_lt_of_le hη_div_c_pos ht.1.le
    rw [if_pos, h_integrand_seg1 t ht_high]
    rw [h_norm_seg1 t ht_pos.le ht_high.le]
    calc η = (η / c) * c := by field_simp
      _ < t * c := mul_lt_mul_of_pos_right ht.1 hc
  have h_I45 : (∫ t in (4:ℝ)..5, if η < ‖fdBoundary_H H t - s‖
      then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) =
    ∫ t in (4:ℝ)..(5 - η), (↑(t - 5) : ℂ)⁻¹ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hii_sub (by norm_num : (0:ℝ) ≤ 4) (by linarith : (4:ℝ) ≤ 5 - η) (by linarith))
      (hii_sub (by linarith : (0:ℝ) ≤ 5 - η) (by linarith : 5 - η ≤ 5) le_rfl)]
    have h_zero : (∫ t in (5 - η)..5,
        if η < ‖fdBoundary_H H t - s‖
        then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℂ)) (fun t ht ↦ by
        rw [Set.uIcc_of_le (by linarith : 5 - η ≤ 5)] at ht
        rw [if_neg]
        push Not
        by_cases ht5 : t = 5
        · rw [ht5, fdBoundary_H_at_five, hs_def, sub_self, norm_zero]; exact hη.le
        · by_cases ht4 : t ≤ 4
          · linarith [ht.1]
          · push Not at ht4
            rw [h_norm_seg5 t ht4 ht.2]; linarith [ht.1]), intervalIntegral.integral_zero]
    rw [h_zero, add_zero]
    refine intervalIntegral.integral_congr_ae' ?_
      (by filter_upwards with t ht; exfalso; linarith [ht.1, ht.2])
    filter_upwards [compl_mem_ae_iff.mpr (show volume {5 - η} = 0 by simp)] with t ht_ne_high ht
    have ht_strict : t < 5 - η := lt_of_le_of_ne ht.2 fun h ↦
      ht_ne_high (Set.mem_singleton_iff.mpr h)
    rw [if_pos, h_integrand_seg5 t ht.1]
    rw [h_norm_seg5 t ht.1 (by linarith)]; linarith
  rw [h_split, h_I14, h_I01, h_I45,
    integral_inv_eq_log_sub (η / c) hη_div_c_pos hη_div_c_lt_1.le,
    integral_shifted_inv_eq_log η hη hη_1, Complex.ofReal_one, Complex.log_one,
    ← Complex.ofReal_log hη_div_c_pos.le, Real.log_div hη.ne' hc_ne, Complex.ofReal_sub]
  ring

/-- The corner `s = -1/2 + H*I` avoids the boundary on `[0, 3]`. -/
private lemma corner_cpv_03 (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    CauchyPrincipalValueExists' (fun z ↦ (z - (-(1/2 : ℂ) + ↑H * I))⁻¹)
      (fdBoundary_H H) 0 3 (-(1/2 : ℂ) + ↑H * I) := by
  set s := -(1/2 : ℂ) + ↑H * I with hs_def
  apply cpv_avoidance _ _ _ _ _ ((fdBoundary_H_continuous H).continuousOn.mono
    (Set.Icc_subset_Icc_right (by norm_num : (3:ℝ) ≤ 5))) (by norm_num)
  intro t ht habs
  rw [Set.mem_Icc] at ht
  by_cases ht1 : t ≤ 1
  · have hre := fdBoundary_H_seg1_re' H ht.1 ht1
    rw [habs, hs_def] at hre
    simp [Complex.add_re, Complex.mul_re] at hre
    linarith
  · push Not at ht1
    by_cases ht3 : t < 3
    · have h_norm : ‖fdBoundary_H H t‖ = 1 := by
        rw [fdBoundary_H_eq_arc (H := H) ht1 ht3, Complex.norm_exp_ofReal_mul_I]
      rw [habs] at h_norm
      have : 1 < ‖s‖ := one_lt_norm_corner H hH s
        (by simp [hs_def, Complex.add_re, Complex.mul_re]; ring)
        (by simp [hs_def, Complex.add_im, Complex.mul_im])
      linarith
    · have ht3_eq : t = 3 := le_antisymm ht.2 (by linarith)
      subst ht3_eq
      rw [fdBoundary_H_at_three] at habs
      have him_s : s.im = H := by
        simp [hs_def, Complex.add_im, Complex.mul_im]
      rw [← habs] at him_s
      have him_rho : (ellipticPointRho : ℂ).im = Real.sqrt 3 / 2 := by
        simp [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
          Complex.add_im, Complex.mul_im, Complex.div_ofNat]
      linarith [him_rho]

lemma cpv_at_corner (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    CauchyPrincipalValueExists' (fun z ↦ (z - (-(1/2 : ℂ) + ↑H * I))⁻¹)
      (fdBoundary_H H) 0 5 (-(1/2 : ℂ) + ↑H * I) := by
  set s := -(1/2 : ℂ) + ↑H * I with hs_def
  set c := H - Real.sqrt 3 / 2 with hc_def
  have hc : 0 < c := sub_pos.mpr hH
  have h_cpv_03 : CauchyPrincipalValueExists' (fun z ↦ (z - s)⁻¹)
      (fdBoundary_H H) 0 3 s := corner_cpv_03 H hH
  have h_cpv_35 : CauchyPrincipalValueExists' (fun z ↦ (z - s)⁻¹)
      (fdBoundary_H H) 3 5 s := by
    set ε₀ := min c 1
    have hε₀ : 0 < ε₀ := lt_min hc one_pos
    set F := fun ε ↦ ∫ t in (3:ℝ)..5,
      if ε < ‖fdBoundary_H H t - s‖ then (fdBoundary_H H t - s)⁻¹ *
        deriv (fdBoundary_H H) t else 0
    suffices h_ev : ∀ ε, 0 < ε → ε < ε₀ → F ε = F (ε₀ / 2) from
      ⟨F (ε₀ / 2), tendsto_const_nhds.congr'
        (Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioo 0 ε₀, Ioo_mem_nhdsGT hε₀,
          fun ε ⟨hε_pos, hε_lt⟩ ↦ (h_ev ε hε_pos hε_lt).symm⟩)⟩
    intro ε hε hε_lt
    have hε_c : ε < c := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have hε_1 : ε < 1 := lt_of_lt_of_le hε_lt (min_le_right _ _)
    have hε₀2_pos : 0 < ε₀ / 2 := by positivity
    have hε₀2_c : ε₀ / 2 < c := by linarith [min_le_left c 1]
    have hε₀2_1 : ε₀ / 2 < 1 := by linarith [min_le_right c 1]
    suffices h_formula : ∀ η, 0 < η → η < c → η < 1 →
        F η = -↑(Real.log c) by
      rw [h_formula ε hε hε_c hε_1, h_formula (ε₀/2) hε₀2_pos hε₀2_c hε₀2_1]
    intro η hη hη_c hη_1
    have hη_div_c_pos : 0 < η / c := div_pos hη hc
    have hη_div_c_lt_1 : η / c < 1 := (div_lt_one hc).mpr hη_c
    have hc_ne : c ≠ 0 := hc.ne'
    have hii := fdBoundary_H_cutout_ii H hH s η hη
    have hii_sub : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ 5 →
        IntervalIntegrable (fun t ↦ if η < ‖fdBoundary_H H t - s‖
          then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) volume a b :=
      fun ha hab hb ↦ hii.mono_set <| by
        rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
        exact Set.Icc_subset_Icc ha hb
    have h_diff_seg4 : ∀ t, 3 < t → t ≤ 4 →
        fdBoundary_H H t - s = ↑((t - 4) * c) * I := fun t ht3 ht4 ↦ by
      rw [fdBoundary_H_eq_seg4_H ht3 ht4, hs_def]
      simp only [fdBoundary_seg4_H, hc_def]; push_cast; ring
    have h_diff_seg5 : ∀ t, 4 < t → fdBoundary_H H t - s = ↑(t - 4) := fun t ht4 ↦ by
      rw [fdBoundary_H_eq_seg5_H ht4, hs_def]
      simp only [fdBoundary_seg5_H]; push_cast; ring
    have h_norm_seg4 : ∀ t, 3 < t → t ≤ 4 →
        ‖fdBoundary_H H t - s‖ = (4 - t) * c := fun t ht3 ht4 ↦ by
      rw [h_diff_seg4 t ht3 ht4, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_of_nonpos (by nlinarith : (t - 4) * c ≤ 0)]; ring
    have h_norm_seg5 : ∀ t, 4 < t → ‖fdBoundary_H H t - s‖ = t - 4 := fun t ht4 ↦ by
      rw [h_diff_seg5 t ht4, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have h_integrand_seg4 : ∀ t, 3 < t → t < 4 →
        (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t = (↑(t - 4) : ℂ)⁻¹ :=
        fun t ht3 ht4 ↦ by
      rw [h_diff_seg4 t ht3 ht4.le]
      erw [(fdBoundary_H_hasDerivAt_seg4 H ht3 ht4).deriv]
      have hc_eq : (↑H - ↑(Real.sqrt 3) / 2 : ℂ) = ↑c := by push_cast [hc_def]; ring
      rw [show (↑H - ↑(Real.sqrt 3) / 2 : ℂ) * I = (↑c : ℂ) * I from by rw [hc_eq],
        show (↑((t - 4) * c) : ℂ) * I = ↑(t - 4) * (↑c * I) from by push_cast; ring]
      exact mul_inv_rev_cancel ↑(t - 4) _
        (mul_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne') I_ne_zero)
    have h_integrand_seg5 : ∀ t, 4 < t →
        (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t = (↑(t - 4) : ℂ)⁻¹ :=
        fun t ht4 ↦ by
      rw [h_diff_seg5 t ht4]
      erw [(fdBoundary_H_hasDerivAt_seg5 H ht4).deriv]; rw [mul_one]
    have h_split : F η = (∫ t in (3:ℝ)..4, if η < ‖fdBoundary_H H t - s‖
        then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) +
      (∫ t in (4:ℝ)..5, if η < ‖fdBoundary_H H t - s‖
        then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) := by
      change (∫ t in (3:ℝ)..5, _) = _
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hii_sub (by norm_num) (by norm_num) (by norm_num) :
          IntervalIntegrable _ _ (3:ℝ) 4)
        (hii_sub (by norm_num) (by norm_num) (by norm_num) :
          IntervalIntegrable _ _ (4:ℝ) 5)]
    have h_I34 : (∫ t in (3:ℝ)..4, if η < ‖fdBoundary_H H t - s‖
        then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) =
      ∫ t in (3:ℝ)..(4 - η / c), (↑(t - 4) : ℂ)⁻¹ := by
      have h_4mc_le : 4 - η / c ≤ 4 := by linarith [hη_div_c_pos]
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hii_sub (by norm_num : (0:ℝ) ≤ 3) (by linarith : (3:ℝ) ≤ 4 - η / c) (by linarith))
        (hii_sub (by linarith : (0:ℝ) ≤ 4 - η / c) h_4mc_le (by norm_num))]
      have h_zero : (∫ t in (4 - η / c)..4,
          if η < ‖fdBoundary_H H t - s‖
          then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℂ)) (fun t ht ↦ by
          rw [Set.uIcc_of_le h_4mc_le] at ht
          rw [if_neg]
          push Not
          rw [h_norm_seg4 t (by linarith [ht.1]) ht.2]
          have h1 : 4 - t ≤ η / c := by linarith [ht.1]
          calc (4 - t) * c ≤ (η / c) * c := mul_le_mul_of_nonneg_right h1 hc.le
            _ = η := by field_simp), intervalIntegral.integral_zero]
      rw [h_zero, add_zero]
      refine intervalIntegral.integral_congr_ae' ?_
        (by filter_upwards with t ht; exfalso; linarith [ht.1, ht.2])
      filter_upwards [compl_mem_ae_iff.mpr (show volume {4 - η / c} = 0 by simp)]
        with t ht_ne ht
      have ht4_strict : t < 4 - η / c :=
        lt_of_le_of_ne ht.2 fun h ↦ ht_ne (Set.mem_singleton_iff.mpr h)
      have ht4 : t < 4 := by linarith [hη_div_c_pos]
      rw [if_pos, h_integrand_seg4 t ht.1 ht4]
      rw [h_norm_seg4 t ht.1 ht4.le]
      calc η = (η / c) * c := by field_simp
        _ < (4 - t) * c := mul_lt_mul_of_pos_right (by linarith) hc
    have h_I45 : (∫ t in (4:ℝ)..5, if η < ‖fdBoundary_H H t - s‖
        then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) =
      ∫ t in (4 + η)..5, (↑(t - 4) : ℂ)⁻¹ := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hii_sub (by norm_num : (0:ℝ) ≤ 4) (by linarith : (4:ℝ) ≤ 4 + η) (by linarith))
        (hii_sub (by linarith : (0:ℝ) ≤ 4 + η) (by linarith : 4 + η ≤ 5) le_rfl)]
      have h_zero : (∫ t in (4:ℝ)..(4 + η),
          if η < ‖fdBoundary_H H t - s‖
          then (fdBoundary_H H t - s)⁻¹ * deriv (fdBoundary_H H) t else 0) = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℂ)) (fun t ht ↦ by
          rw [Set.uIcc_of_le (by linarith : (4:ℝ) ≤ 4 + η)] at ht
          rw [if_neg]
          push Not
          by_cases ht4 : t = 4
          · subst ht4
            rw [fdBoundary_H_at_four H, hs_def]; norm_num; linarith
          · rw [h_norm_seg5 t (lt_of_le_of_ne ht.1 (Ne.symm ht4))]
            linarith [ht.2]), intervalIntegral.integral_zero]
      rw [h_zero, zero_add]
      refine intervalIntegral.integral_congr_ae' ?_
        (by filter_upwards with t ht; exfalso; linarith [ht.1, ht.2])
      filter_upwards with t ht
      have ht4 : 4 < t := by linarith [ht.1]
      rw [if_pos, h_integrand_seg5 t ht4]
      rw [h_norm_seg5 t ht4]; linarith [ht.1]
    have h_sub34 : (∫ t in (3:ℝ)..(4 - η / c), (↑(t - 4) : ℂ)⁻¹) =
        ∫ u in (-1:ℝ)..(-η / c), (↑u : ℂ)⁻¹ := by
      simp_rw [← Complex.ofReal_inv, intervalIntegral.integral_ofReal,
        show (-η / c : ℝ) = -(η / c) by ring]
      simp [show (3:ℝ) - 4 = -1 by ring, show (4 - η / c) - 4 = -(η / c) by ring]
    have h_sub45 : (∫ t in (4 + η)..5, (↑(t - 4) : ℂ)⁻¹) =
        ∫ u in η..1, (↑u : ℂ)⁻¹ := by
      simp_rw [← Complex.ofReal_inv, intervalIntegral.integral_ofReal]
      simp [show (4 + η) - 4 = η by ring, show (5:ℝ) - 4 = 1 by ring]
    have h_neg_axis : (∫ u in (-1:ℝ)..(-η / c), (↑u : ℂ)⁻¹) =
        -(∫ u in (η / c)..1, (↑u : ℂ)⁻¹) := by
      simp_rw [← Complex.ofReal_inv]
      rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
        ← Complex.ofReal_neg, Complex.ofReal_inj,
        show (-η / c : ℝ) = -(η / c) by ring]
      have key : (∫ x in (η / c)..(1:ℝ), (-x)⁻¹) =
          ∫ x in (-1:ℝ)..-(η / c), x⁻¹ :=
        intervalIntegral.integral_comp_neg (fun u : ℝ ↦ u⁻¹) (a := η / c) (b := 1)
      rw [intervalIntegral.integral_congr (g := fun x ↦ -(x⁻¹))
        (fun _ _ ↦ neg_inv.symm), intervalIntegral.integral_neg] at key
      exact key.symm
    rw [h_split, h_I34, h_I45, h_sub34, h_sub45, h_neg_axis,
      integral_inv_eq_log_sub (η / c) hη_div_c_pos hη_div_c_lt_1.le,
      integral_inv_eq_log_sub η hη hη_1.le, Complex.ofReal_one, Complex.log_one,
      ← Complex.ofReal_log hη.le, ← Complex.ofReal_log hη_div_c_pos.le,
      Real.log_div hη.ne' hc_ne, Complex.ofReal_sub]
    ring
  exact cpv_concat _ _ 0 3 5 s h_cpv_03 h_cpv_35 (by norm_num) (by norm_num)
    (fdBoundary_H_cutout_ii H hH s)

end
