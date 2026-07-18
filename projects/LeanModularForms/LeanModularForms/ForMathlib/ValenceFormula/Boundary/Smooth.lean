/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ValenceFormula.Boundary.Bounds

/-!
# Fundamental Domain Boundary – Smoothness

Differentiability, derivatives, limits, and curve/immersion constructions
for the fundamental domain boundary.

## Main Definitions

* `fdBoundary_HCurve` — H-parameterized boundary as `PiecewiseC1Curve`
* `fdBoundary_HImmersion` — H-parameterized boundary as `PiecewiseC1Immersion`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

private lemma arc_hasDerivAt (s : ℝ) :
    HasDerivAt (fun s' : ℝ ↦ exp ((↑Real.pi * (↑s' + 1) / 6) * I))
      (exp ((↑Real.pi * (↑s + 1) / 6) * I) * (↑Real.pi / 6 * I)) s := by
  have h := ArcCalculus.unitArc_hasDerivAt
    (Real.pi / 3) (Real.pi * 2 / 3) (1 : ℝ) (3 : ℝ) s (by norm_num)
  have hfun : ArcCalculus.unitArc (Real.pi / 3) (Real.pi * 2 / 3) (1 : ℝ) (3 : ℝ) =
      fun s' : ℝ ↦ exp ((↑Real.pi * (↑s' + 1) / 6) * I) := by
    funext s'; simp only [ArcCalculus.unitArc]; push_cast; ring_nf
  rw [hfun] at h
  convert h using 1
  congr 2; push_cast; ring

private lemma fdBoundary_H_eq_arc_near {H : ℝ} {s : ℝ} (hs1 : 1 < s) (hs3 : s < 3) :
    fdBoundary_H H =ᶠ[𝓝 s] fun s' ↦ exp ((↑Real.pi * (↑s' + 1) / 6) * I) := by
  filter_upwards [Ioi_mem_nhds hs1, Iio_mem_nhds hs3] with s' hs1' hs3'
  simp only [fdBoundary_H, show ¬s' ≤ 1 from not_le.mpr hs1']
  by_cases hs2' : s' ≤ 2
  · simp only [hs2', ite_true, ite_false]; congr 1; ring
  · simp only [show ¬s' ≤ 2 from hs2',
      show s' ≤ 3 from le_of_lt hs3', ite_true, ite_false]
    congr 1; ring

@[fun_prop]
private lemma arc_deriv_continuous :
    Continuous (fun s : ℝ ↦ exp ((↑Real.pi * (↑s + 1) / 6) * I) * (↑Real.pi / 6 * I)) := by
  fun_prop

private lemma arc_limit_ne_zero (c : ℝ) :
    exp ((↑Real.pi * (↑c + 1) / 6) * I) * (↑Real.pi / 6 * I) ≠ 0 :=
  mul_ne_zero (exp_ne_zero _)
    (mul_ne_zero (div_ne_zero (mod_cast Real.pi_pos.ne') (by norm_num : (6 : ℂ) ≠ 0)) I_ne_zero)

lemma fdBoundary_H_hasDerivAt_seg1 (H : ℝ) {t : ℝ} (ht : t < 1) :
    HasDerivAt (fdBoundary_H H) (-(H - Real.sqrt 3 / 2) * I) t := by
  have heq : fdBoundary_H H =ᶠ[𝓝 t]
      fun s ↦ (1 : ℂ) / 2 + (↑H - ↑s * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    simp only [fdBoundary_H, show s ≤ 1 from le_of_lt hs, ite_true]
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  have h := ((((hasDerivAt_const t (↑H : ℂ)).sub
      ((hasDerivAt_id t).ofReal_comp.mul_const (↑H - ↑(Real.sqrt 3) / 2))).mul_const I).const_add
      ((1 : ℂ) / 2))
  simpa using h

lemma fdBoundary_H_hasDerivAt_seg4' (H : ℝ) (t : ℝ) (ht : t ∈ Ioo (3 : ℝ) 4) :
    HasDerivAt (fdBoundary_H H) ((H - Real.sqrt 3 / 2) * I) t := by
  have heq : fdBoundary_H H =ᶠ[𝓝 t] fun s : ℝ ↦ (-1 : ℂ) / 2 +
      (↑(Real.sqrt 3) / 2 + (↑s - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s ⟨hs1, hs2⟩
    simp only [fdBoundary_H, show ¬s ≤ 1 by linarith,
      show ¬s ≤ 2 by linarith, show ¬s ≤ 3 by linarith,
      show s ≤ 4 by linarith, ite_true, ite_false]
  have h_lin : HasDerivAt (fun s : ℝ ↦ (↑s : ℂ) - 3) 1 t := by
    have h := ((hasDerivAt_id t).ofReal_comp).sub (hasDerivAt_const t (3 : ℂ))
    convert h using 1 <;> first | rfl | simp
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  have h := ((h_lin.mul_const (↑H - ↑(Real.sqrt 3) / 2)).const_add
    (↑(Real.sqrt 3) / 2 : ℂ)).mul_const I |>.const_add ((-1 : ℂ) / 2)
  simpa using h

lemma fdBoundary_H_hasDerivAt_seg5 (H : ℝ) {t : ℝ} (h4 : 4 < t) :
    HasDerivAt (fdBoundary_H H) 1 t := by
  have heq : fdBoundary_H H =ᶠ[𝓝 t] fun s : ℝ ↦ (↑s - 9/2 : ℂ) + ↑H * I := by
    filter_upwards [Ioi_mem_nhds h4] with s (hs : (4:ℝ) < s)
    simp only [fdBoundary_H, show ¬s ≤ 1 by linarith,
      show ¬s ≤ 2 by linarith, show ¬s ≤ 3 by linarith,
      show ¬s ≤ 4 by linarith, ite_false]
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  have h := (((hasDerivAt_id t).ofReal_comp.sub
    (hasDerivAt_const t (9/2 : ℂ))).add_const (↑H * I : ℂ))
  simpa using h

private lemma fdBoundary_H_hasDerivAt_seg1' (H : ℝ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fdBoundary_H H) (-(H - Real.sqrt 3 / 2) * I) t :=
  fdBoundary_H_hasDerivAt_seg1 H ht.2

private lemma fdBoundary_H_hasDerivAt_seg5' (H : ℝ) (t : ℝ) (ht : t ∈ Ioo (4 : ℝ) 5) :
    HasDerivAt (fdBoundary_H H) 1 t :=
  fdBoundary_H_hasDerivAt_seg5 H ht.1

private lemma seg_vertical_deriv_ne_zero {H : ℝ} (hH : Real.sqrt 3 / 2 < H) :
    (↑H - ↑(Real.sqrt 3) / 2) * I ≠ (0 : ℂ) := by
  apply mul_ne_zero _ I_ne_zero
  intro h
  apply_fun Complex.re at h
  simp only [sub_re, ofReal_re, div_ofNat, zero_re] at h
  linarith

lemma fdBoundary_H_differentiableAt_off_partition (H : ℝ) (t : ℝ)
    (htp : t ∉ fdBoundary_H_partition) : DifferentiableAt ℝ (fdBoundary_H H) t := by
  simp only [fdBoundary_H_partition, Finset.mem_insert, Finset.mem_singleton] at htp
  push Not at htp
  obtain ⟨ht1, ht3, ht4⟩ := htp
  by_cases h1 : t < 1
  · exact (fdBoundary_H_hasDerivAt_seg1 H h1).differentiableAt
  · by_cases h3 : t < 3
    · exact ((arc_hasDerivAt t).congr_of_eventuallyEq
        (fdBoundary_H_eq_arc_near (H := H)
          (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm ht1)) h3)).differentiableAt
    · by_cases h4 : t < 4
      · exact (fdBoundary_H_hasDerivAt_seg4' H t
          ⟨lt_of_le_of_ne (not_lt.mp h3) (Ne.symm ht3), h4⟩).differentiableAt
      · exact (fdBoundary_H_hasDerivAt_seg5 H
          (lt_of_le_of_ne (not_lt.mp h4) (Ne.symm ht4))).differentiableAt

lemma fdBoundary_H_deriv_ne_zero_off_fullPartition (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 5) (htp : t ∉ fdBoundaryFullPartition) :
    deriv (fdBoundary_H H) t ≠ 0 := by
  simp only [fdBoundaryFullPartition, Finset.mem_insert, Finset.mem_singleton] at htp
  push Not at htp
  obtain ⟨ht0, ht1, _, ht3, ht4, ht5⟩ := htp
  have ht' : t ∈ Ioo (0 : ℝ) 5 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht5⟩
  by_cases h1 : t < 1
  · rw [show deriv (fdBoundary_H H) t = _ from (fdBoundary_H_hasDerivAt_seg1' H t
      ⟨ht'.1, h1⟩).deriv, neg_mul]
    exact neg_ne_zero.mpr (seg_vertical_deriv_ne_zero hH)
  · push Not at h1
    by_cases h3 : t < 3
    · rw [show deriv (fdBoundary_H H) t = _ from ((arc_hasDerivAt t).congr_of_eventuallyEq
        (fdBoundary_H_eq_arc_near (H := H) (lt_of_le_of_ne h1 (Ne.symm ht1)) h3)).deriv]
      exact arc_limit_ne_zero t
    · push Not at h3
      by_cases h4 : t < 4
      · rw [show deriv (fdBoundary_H H) t = _ from (fdBoundary_H_hasDerivAt_seg4' H t
          ⟨lt_of_le_of_ne h3 (Ne.symm ht3), h4⟩).deriv]
        exact seg_vertical_deriv_ne_zero hH
      · push Not at h4
        rw [show deriv (fdBoundary_H H) t = _ from (fdBoundary_H_hasDerivAt_seg5' H t
          ⟨lt_of_le_of_ne h4 (Ne.symm ht4), ht'.2⟩).deriv]
        exact one_ne_zero

lemma fdBoundary_H_deriv_continuousAt_off_fullPartition (H : ℝ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 5) (htp : t ∉ fdBoundaryFullPartition) :
    ContinuousAt (deriv (fdBoundary_H H)) t := by
  simp only [fdBoundaryFullPartition, Finset.mem_insert, Finset.mem_singleton] at htp
  push Not at htp
  obtain ⟨_, ht1, _, ht3, ht4, _⟩ := htp
  by_cases h1 : t < 1
  · apply ContinuousAt.congr continuousAt_const
    filter_upwards [Ioo_mem_nhds ht.1 h1] with s hs
    exact (fdBoundary_H_hasDerivAt_seg1' H s hs).deriv.symm
  · push Not at h1
    have h1' : 1 < t := lt_of_le_of_ne h1 (Ne.symm ht1)
    by_cases h3 : t < 3
    · have hderiv_eq : deriv (fdBoundary_H H) =ᶠ[𝓝 t]
          fun s ↦ exp ((↑Real.pi * (↑s + 1) / 6) * I) * (↑Real.pi / 6 * I) := by
        filter_upwards [(fdBoundary_H_eq_arc_near (H := H) h1' h3).deriv] with s hs
        exact hs ▸ (arc_hasDerivAt s).deriv
      exact (continuousAt_congr hderiv_eq).mpr arc_deriv_continuous.continuousAt
    · push Not at h3
      have h3' : 3 < t := lt_of_le_of_ne h3 (Ne.symm ht3)
      by_cases h4 : t < 4
      · apply ContinuousAt.congr continuousAt_const
        filter_upwards [Ioo_mem_nhds h3' h4] with s hs
        exact (fdBoundary_H_hasDerivAt_seg4' H s hs).deriv.symm
      · push Not at h4
        apply ContinuousAt.congr continuousAt_const
        filter_upwards [Ioo_mem_nhds (lt_of_le_of_ne h4 (Ne.symm ht4)) ht.2] with s hs
        exact (fdBoundary_H_hasDerivAt_seg5' H s hs).deriv.symm

private lemma tendsto_of_eventually_const_left {c : ℂ} {p : ℝ} {f : ℝ → ℂ} {a : ℝ}
    (ha : a < p) (hf : ∀ s ∈ Ioo a p, f s = c) : Tendsto f (𝓝[<] p) (𝓝 c) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [Ioo_mem_nhdsLT ha] with s hs
    exact (hf s hs).symm)

private lemma tendsto_of_eventually_const_right {c : ℂ} {p : ℝ} {f : ℝ → ℂ} {b : ℝ}
    (hb : p < b) (hf : ∀ s ∈ Ioo p b, f s = c) : Tendsto f (𝓝[>] p) (𝓝 c) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [Ioo_mem_nhdsGT hb] with s hs
    exact (hf s hs).symm)

private lemma arc_tendsto_left {H : ℝ} (p : ℝ) (h1p : 1 < p) (hp3 : p ≤ 3) :
    Tendsto (deriv (fdBoundary_H H)) (𝓝[<] p) (𝓝 (exp ((↑Real.pi * (↑p + 1) / 6) * I) *
      (↑Real.pi / 6 * I))) := by
  apply arc_deriv_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [Ioo_mem_nhdsLT h1p] with s hs
  have heq := fdBoundary_H_eq_arc_near (H := H) hs.1 (lt_of_lt_of_le hs.2 hp3)
  exact ((Filter.EventuallyEq.deriv_eq heq).trans (arc_hasDerivAt s).deriv).symm

private lemma arc_tendsto_right {H : ℝ} (p : ℝ) (hp1 : 1 ≤ p) (hp3 : p < 3) :
    Tendsto (deriv (fdBoundary_H H)) (𝓝[>] p) (𝓝 (exp ((↑Real.pi * (↑p + 1) / 6) * I) *
      (↑Real.pi / 6 * I))) := by
  apply arc_deriv_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [Ioo_mem_nhdsGT hp3] with s hs
  have heq := fdBoundary_H_eq_arc_near (H := H) (lt_of_le_of_lt hp1 hs.1) hs.2
  exact ((Filter.EventuallyEq.deriv_eq heq).trans (arc_hasDerivAt s).deriv).symm

lemma fdBoundary_H_left_deriv_limit (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (p : ℝ)
    (hp : p ∈ fdBoundaryFullPartition) (hp' : (0 : ℝ) < p) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv (fdBoundary_H H)) (𝓝[<] p) (𝓝 L) := by
  simp only [fdBoundaryFullPartition, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · linarith
  · refine ⟨-(↑H - ↑(Real.sqrt 3) / 2) * I, ?_, ?_⟩
    · rw [neg_mul]
      exact neg_ne_zero.mpr (seg_vertical_deriv_ne_zero hH)
    · exact tendsto_of_eventually_const_left (show (0 : ℝ) < 1 by norm_num)
        (fun s hs ↦ (fdBoundary_H_hasDerivAt_seg1' H s hs).deriv)
  · exact ⟨_, arc_limit_ne_zero 2, arc_tendsto_left 2 (by norm_num) (by norm_num)⟩
  · exact ⟨_, arc_limit_ne_zero 3, arc_tendsto_left 3 (by norm_num) (by norm_num)⟩
  · exact ⟨_, seg_vertical_deriv_ne_zero hH,
      tendsto_of_eventually_const_left (show (3 : ℝ) < 4 by norm_num)
        (fun s hs ↦ (fdBoundary_H_hasDerivAt_seg4' H s hs).deriv)⟩
  · exact ⟨1, one_ne_zero,
      tendsto_of_eventually_const_left (show (4 : ℝ) < 5 by norm_num)
        (fun s hs ↦ (fdBoundary_H_hasDerivAt_seg5' H s hs).deriv)⟩

lemma fdBoundary_H_hasDerivAt_seg4 (H : ℝ) {t : ℝ} (h3 : 3 < t) (h4 : t < 4) :
    HasDerivAt (fdBoundary_H H) ((H - Real.sqrt 3 / 2) * I) t :=
  fdBoundary_H_hasDerivAt_seg4' H t ⟨h3, h4⟩

lemma hasDerivAt_fdBoundary_seg1_H (H t : ℝ) :
    HasDerivAt (fdBoundary_seg1_H H) (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
  have hfun : fdBoundary_seg1_H H = fun s : ℝ ↦
      ((1 : ℂ) / 2 + ↑H * I) + ↑s * (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) := by
    ext s; simp only [fdBoundary_seg1_H]; push_cast; ring
  rw [hfun]
  exact (((hasDerivAt_id t).ofReal_comp).mul_const _).const_add _
    |>.congr_deriv (by push_cast; ring)

lemma hasDerivAt_fdBoundary_seg4_H (H t : ℝ) :
    HasDerivAt (fdBoundary_seg4_H H) ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
  have hfun : fdBoundary_seg4_H H = fun s : ℝ ↦
      ((-1 : ℂ) / 2 + ↑(Real.sqrt 3) / 2 * I) +
        ↑(s - 3) * ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) := by
    ext s; simp only [fdBoundary_seg4_H]; push_cast; ring
  rw [hfun]
  have h_sub : HasDerivAt (fun s : ℝ ↦ (↑(s - 3) : ℂ)) 1 t := by
    have := ((hasDerivAt_id t).sub (hasDerivAt_const t (3 : ℝ))).ofReal_comp
    simp only [sub_zero, ofReal_one] at this; exact this
  exact (h_sub.mul_const _).const_add _ |>.congr_deriv (by push_cast; ring)

lemma hasDerivAt_fdBoundary_seg5_H (H t : ℝ) :
    HasDerivAt (fdBoundary_seg5_H H) 1 t := by
  have hfun : fdBoundary_seg5_H H = fun s : ℝ ↦
      ((-9 / 2 : ℂ) + ↑H * I) + ↑s * (1 : ℂ) := by
    ext s; simp only [fdBoundary_seg5_H]; ring
  rw [hfun]
  exact (((hasDerivAt_id t).ofReal_comp).mul_const _).const_add _
    |>.congr_deriv (by norm_cast)

private lemma seg4_eventuallyEq_left_4 (H : ℝ) :
    fdBoundary_seg4_H H =ᶠ[𝓝[≤] 4] fdBoundary_H H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨Ioo 3 5 ∩ Iic 4, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin, fun s hs ↦ ?_⟩
  rcases eq_or_lt_of_le (show s ≤ 4 from hs.2) with rfl | h
  · simp only [fdBoundary_seg4_H, fdBoundary_H_at_four]; push_cast; ring
  · exact (fdBoundary_H_eq_seg4_H (by linarith [hs.1.1]) (le_of_lt h)).symm

private lemma seg5_eventuallyEq_right_4 (H : ℝ) :
    fdBoundary_seg5_H H =ᶠ[𝓝[≥] 4] fdBoundary_H H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨Ioo 3 5 ∩ Ici 4, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin, fun s hs ↦ ?_⟩
  rcases eq_or_lt_of_le (show (4:ℝ) ≤ s from hs.2) with rfl | h
  · simp only [fdBoundary_seg5_H, fdBoundary_H_at_four]; push_cast; ring
  · exact (fdBoundary_H_eq_seg5_H h).symm

private lemma re_arc_deriv_eq (θ : ℝ) :
    (↑(Real.pi / 6) * I * exp (↑θ * I)).re = -(Real.pi / 6) * Real.sin θ := by
  rw [mul_assoc, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    I_mul_re, exp_ofReal_mul_I_im]
  ring

lemma fdBoundary_H_not_differentiableAt_4 {H : ℝ} (hH : Real.sqrt 3 / 2 < H) :
    ¬DifferentiableAt ℝ (fdBoundary_H H) 4 := by
  intro hdiff
  have hleft : HasDerivWithinAt (fdBoundary_H H)
      ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) (Iic 4) 4 :=
    ((seg4_eventuallyEq_left_4 H).hasDerivWithinAt_iff (by
      simp only [fdBoundary_seg4_H, fdBoundary_H_at_four]; push_cast; ring)).mp
      (hasDerivAt_fdBoundary_seg4_H H 4).hasDerivWithinAt
  have hright : HasDerivWithinAt (fdBoundary_H H) 1 (Ici 4) 4 :=
    ((seg5_eventuallyEq_right_4 H).hasDerivWithinAt_iff (by
      simp only [fdBoundary_seg5_H, fdBoundary_H_at_four]; push_cast; ring)).mp
      (hasDerivAt_fdBoundary_seg5_H H 4).hasDerivWithinAt
  have hd := hdiff.hasDerivAt
  have him := congr_arg Complex.im
    (((uniqueDiffWithinAt_Iic (4 : ℝ)).eq_deriv _ hleft hd.hasDerivWithinAt).trans
      ((uniqueDiffWithinAt_Ici (4 : ℝ)).eq_deriv _ hright hd.hasDerivWithinAt).symm)
  simp only [mul_im, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, one_im] at him
  linarith [sub_pos.mpr hH]

private lemma arc_val_at_3 (H : ℝ) :
    (fun s ↦ exp ((↑Real.pi * (↑s + 1) / 6) * I)) 3 = fdBoundary_H H 3 := by
  rw [show fdBoundary_H H 3 = fdBoundary 3 from
    (fdBoundary_H_at_three H).trans fdBoundary_at_three.symm]
  simp only [fdBoundary, show ¬(3:ℝ) ≤ 1 by norm_num, ↓reduceIte,
    show ¬(3:ℝ) ≤ 2 by norm_num, show (3:ℝ) ≤ 3 from le_rfl]
  congr 1; push_cast; ring

private lemma seg4_val_at_3 (H : ℝ) :
    fdBoundary_seg4_H H 3 = fdBoundary_H H 3 := by
  rw [show fdBoundary_H H 3 = fdBoundary 3 from
    (fdBoundary_H_at_three H).trans fdBoundary_at_three.symm, fdBoundary_at_three]
  simp only [fdBoundary_seg4_H, ellipticPointRho, ellipticPointRho',
    UpperHalfPlane.coe_mk]
  push_cast; ring

private lemma arc_eventuallyEq_left_3 (H : ℝ) :
    (fun s ↦ exp ((↑Real.pi * (↑s + 1) / 6) * I)) =ᶠ[𝓝[≤] 3] fdBoundary_H H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨Ioo 2 4 ∩ Iic 3, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin, fun s hs ↦ ?_⟩
  rcases eq_or_lt_of_le (show s ≤ 3 from hs.2) with rfl | hs3'
  · exact arc_val_at_3 H
  · exact (fdBoundary_H_eq_arc_near (by linarith [hs.1.1]) hs3').symm.eq_of_nhds

private lemma seg4_eventuallyEq_right_3 (H : ℝ) :
    fdBoundary_seg4_H H =ᶠ[𝓝[≥] 3] fdBoundary_H H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨Ioo 2 4 ∩ Ici 3, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin, fun s hs ↦ ?_⟩
  rcases eq_or_lt_of_le (show (3:ℝ) ≤ s from hs.2) with rfl | h
  · exact seg4_val_at_3 H
  · exact (fdBoundary_H_eq_seg4_H h (by linarith [hs.1.2])).symm

lemma fdBoundary_H_not_differentiableAt_3 {H : ℝ} (_hH : Real.sqrt 3 / 2 < H) :
    ¬DifferentiableAt ℝ (fdBoundary_H H) 3 := by
  intro hdiff
  have hval_arc := arc_val_at_3 H
  have hval_seg4 := seg4_val_at_3 H
  have hleft : HasDerivWithinAt (fdBoundary_H H)
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * 4 / 6) * I)) (Iic 3) 3 :=
    ((arc_eventuallyEq_left_3 H).hasDerivWithinAt_iff hval_arc).mp
      ((arc_hasDerivAt 3).hasDerivWithinAt.congr_deriv (by push_cast; ring_nf))
  have hright : HasDerivWithinAt (fdBoundary_H H)
      ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) (Ici 3) 3 :=
    ((seg4_eventuallyEq_right_3 H).hasDerivWithinAt_iff hval_seg4).mp
      (hasDerivAt_fdBoundary_seg4_H H 3).hasDerivWithinAt
  have hd := hdiff.hasDerivAt
  have heq : ↑(Real.pi / 6) * I * exp (↑(Real.pi * 4 / 6) * I) =
      (↑(H - Real.sqrt 3 / 2) : ℂ) * I :=
    ((uniqueDiffWithinAt_Iic (3 : ℝ)).eq_deriv _ hleft hd.hasDerivWithinAt).trans
      ((uniqueDiffWithinAt_Ici (3 : ℝ)).eq_deriv _ hright hd.hasDerivWithinAt).symm
  have hre := congr_arg Complex.re heq
  have hre_rhs : ((↑(H - Real.sqrt 3 / 2) : ℂ) * I).re = 0 := by simp [mul_re]
  rw [re_arc_deriv_eq, hre_rhs] at hre
  have hsin : Real.sin (Real.pi * 4 / 6) = Real.sqrt 3 / 2 := by
    rw [show Real.pi * 4 / 6 = Real.pi - Real.pi / 3 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [hsin] at hre
  nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)]

private lemma seg1_eventuallyEq_left_1 (H : ℝ) :
    fdBoundary_seg1_H H =ᶠ[𝓝[≤] 1] fdBoundary_H H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  exact ⟨Ioo 0 2 ∩ Iic 1, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin,
    fun s hs ↦ (fdBoundary_H_eq_seg1_H hs.2).symm⟩

private lemma arc_val_at_1 (H : ℝ) :
    (fun s ↦ exp ((↑Real.pi * (↑s + 1) / 6) * I)) 1 = fdBoundary_H H 1 := by
  dsimp only
  have harg : (↑Real.pi * ((1:ℂ) + 1) / 6) * I = ↑(Real.pi / 3 : ℝ) * I := by push_cast; ring
  rw [harg, exp_mul_I]
  simp only [fdBoundary_H, show (1:ℝ) ≤ 1 from le_rfl, ite_true]
  rw [← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring

private lemma arc_eventuallyEq_right_1 (H : ℝ) :
    (fun s ↦ exp ((↑Real.pi * (↑s + 1) / 6) * I)) =ᶠ[𝓝[≥] 1] fdBoundary_H H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨Ioo 0 2 ∩ Ici 1, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin, fun s hs ↦ ?_⟩
  rcases eq_or_lt_of_le (show (1:ℝ) ≤ s from hs.2) with rfl | hs1
  · exact arc_val_at_1 H
  · exact (fdBoundary_H_eq_arc_near hs1 (by linarith [hs.1.2])).symm.eq_of_nhds

lemma fdBoundary_H_not_differentiableAt_1 {H : ℝ} (_hH : Real.sqrt 3 / 2 < H) :
    ¬DifferentiableAt ℝ (fdBoundary_H H) 1 := by
  intro hdiff
  have hval_seg1 : fdBoundary_seg1_H H 1 = fdBoundary_H H 1 :=
    (fdBoundary_H_eq_seg1_H le_rfl).symm
  have hval_arc := arc_val_at_1 H
  have hleft : HasDerivWithinAt (fdBoundary_H H)
      (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) (Iic 1) 1 :=
    ((seg1_eventuallyEq_left_1 H).hasDerivWithinAt_iff hval_seg1).mp
      (hasDerivAt_fdBoundary_seg1_H H 1).hasDerivWithinAt
  have hright : HasDerivWithinAt (fdBoundary_H H)
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * 2 / 6) * I)) (Ici 1) 1 :=
    ((arc_eventuallyEq_right_1 H).hasDerivWithinAt_iff hval_arc).mp
      ((arc_hasDerivAt 1).hasDerivWithinAt.congr_deriv (by push_cast; ring_nf))
  have hd := hdiff.hasDerivAt
  have heq : -(↑(H - Real.sqrt 3 / 2) : ℂ) * I =
      ↑(Real.pi / 6) * I * exp (↑(Real.pi * 2 / 6) * I) :=
    ((uniqueDiffWithinAt_Iic (1 : ℝ)).eq_deriv _ hleft hd.hasDerivWithinAt).trans
      ((uniqueDiffWithinAt_Ici (1 : ℝ)).eq_deriv _ hright hd.hasDerivWithinAt).symm
  have hre := congr_arg Complex.re heq
  have hre_lhs : (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I).re = 0 := by simp [mul_re]
  rw [hre_lhs, re_arc_deriv_eq, show Real.pi * 2 / 6 = Real.pi / 3 by ring,
    Real.sin_pi_div_three] at hre
  nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)]

lemma fdBoundary_H_right_deriv_limit (H : ℝ) (hH : Real.sqrt 3 / 2 < H) (p : ℝ)
    (hp : p ∈ fdBoundaryFullPartition) (hp' : p < (5 : ℝ)) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv (fdBoundary_H H)) (𝓝[>] p) (𝓝 L) := by
  simp only [fdBoundaryFullPartition, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨-(↑H - ↑(Real.sqrt 3) / 2) * I, ?_, ?_⟩
    · rw [neg_mul]
      exact neg_ne_zero.mpr (seg_vertical_deriv_ne_zero hH)
    · exact tendsto_of_eventually_const_right (show (0 : ℝ) < 1 by norm_num)
        (fun s hs ↦ (fdBoundary_H_hasDerivAt_seg1' H s hs).deriv)
  · exact ⟨_, arc_limit_ne_zero 1, arc_tendsto_right 1 (by norm_num) (by norm_num)⟩
  · exact ⟨_, arc_limit_ne_zero 2, arc_tendsto_right 2 (by norm_num) (by norm_num)⟩
  · exact ⟨_, seg_vertical_deriv_ne_zero hH,
      tendsto_of_eventually_const_right (show (3 : ℝ) < 4 by norm_num)
        (fun s hs ↦ (fdBoundary_H_hasDerivAt_seg4' H s hs).deriv)⟩
  · exact ⟨1, one_ne_zero,
      tendsto_of_eventually_const_right (show (4 : ℝ) < 5 by norm_num)
        (fun s hs ↦ (fdBoundary_H_hasDerivAt_seg5' H s hs).deriv)⟩
  · linarith

private lemma fdBoundaryFullPartition_subset :
    ↑fdBoundaryFullPartition ⊆ Icc (0 : ℝ) 5 := by
  intro x hx
  simp only [fdBoundaryFullPartition, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff] at hx
  simp only [Icc, Set.mem_setOf_eq]
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> norm_num

private lemma fdBoundaryFullPartition_endpoints :
    (0 : ℝ) ∈ fdBoundaryFullPartition ∧ (5 : ℝ) ∈ fdBoundaryFullPartition :=
  ⟨by simp [fdBoundaryFullPartition], by simp [fdBoundaryFullPartition]⟩

/-- The H-parameterized boundary as a `PiecewiseC1Curve`. -/
noncomputable def fdBoundary_HCurve (H : ℝ) : PiecewiseC1Curve :=
  PiecewiseC1Curve.ofIccPartition (fdBoundary_H H) 0 5 (by norm_num)
    fdBoundaryFullPartition
    fdBoundaryFullPartition_subset
    fdBoundaryFullPartition_endpoints
    (fdBoundary_H_continuous H).continuousOn
    (by
      intro t _ htp
      have htP : t ∉ fdBoundary_H_partition := by
        simp only [fdBoundary_H_partition, fdBoundaryFullPartition, Finset.mem_insert,
          Finset.mem_singleton] at htp ⊢
        push Not at htp ⊢
        exact ⟨htp.2.1, htp.2.2.2.1, htp.2.2.2.2.1⟩
      exact fdBoundary_H_differentiableAt_off_partition H t htP)
    (fdBoundary_H_deriv_continuousAt_off_fullPartition H)

/-- The H-parameterized boundary as a `PiecewiseC1Immersion`.
Requires H > √3/2 for nonzero derivative. -/
noncomputable def fdBoundary_HImmersion (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    PiecewiseC1Immersion where
  toPiecewiseC1Curve := fdBoundary_HCurve H
  deriv_ne_zero := fdBoundary_H_deriv_ne_zero_off_fullPartition H hH
  left_deriv_limit := fdBoundary_H_left_deriv_limit H hH
  right_deriv_limit := fdBoundary_H_right_deriv_limit H hH

lemma fdBoundary_HCurve_closed (H : ℝ) :
    (fdBoundary_HCurve H).IsClosed :=
  fdBoundary_H_closed H

lemma fdBoundary_H_hasDerivAt_arc (H : ℝ) {t : ℝ} (h1 : 1 < t) (h3 : t < 3) :
    HasDerivAt (fdBoundary_H H)
      (exp ((↑Real.pi * (↑t + 1) / 6) * I) * (↑Real.pi / 6 * I)) t :=
  (arc_hasDerivAt t).congr_of_eventuallyEq
    (fdBoundary_H_eq_arc_near (H := H) h1 h3)

/-- On an open interval where `fdBoundary_H H` has constant derivative `c`, its derivative
function is continuous. -/
private lemma deriv_continuousOn_Ioo_const (H : ℝ) {a b : ℝ} (c : ℂ)
    (hc : ∀ s ∈ Ioo a b, HasDerivAt (fdBoundary_H H) c s) :
    ContinuousOn (deriv (fdBoundary_H H)) (Ioo a b) := fun t ht ↦ by
  have : deriv (fdBoundary_H H) =ᶠ[𝓝 t] fun _ ↦ c := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (hc s hs).deriv
  exact this.continuousAt.continuousWithinAt

lemma fdBoundary_H_deriv_continuousOn_Ioo_01 (H : ℝ) :
    ContinuousOn (deriv (fdBoundary_H H)) (Ioo 0 1) :=
  deriv_continuousOn_Ioo_const H _ fun s hs ↦ fdBoundary_H_hasDerivAt_seg1' H s hs

lemma fdBoundary_H_deriv_continuousOn_Ioo_13 (H : ℝ) :
    ContinuousOn (deriv (fdBoundary_H H)) (Ioo 1 3) := by
  intro t ht
  have hderiv_eq : deriv (fdBoundary_H H) =ᶠ[𝓝 t]
      fun s ↦ exp ((↑Real.pi * (↑s + 1) / 6) * I) * (↑Real.pi / 6 * I) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (Filter.EventuallyEq.deriv_eq
      (fdBoundary_H_eq_arc_near (H := H) hs.1 hs.2)).trans (arc_hasDerivAt s).deriv
  exact (continuousAt_congr hderiv_eq).mpr arc_deriv_continuous.continuousAt
    |>.continuousWithinAt

lemma fdBoundary_H_deriv_continuousOn_Ioo_34 (H : ℝ) :
    ContinuousOn (deriv (fdBoundary_H H)) (Ioo 3 4) :=
  deriv_continuousOn_Ioo_const H _ fun s hs ↦ fdBoundary_H_hasDerivAt_seg4' H s hs

lemma fdBoundary_H_deriv_continuousOn_Ioo_45 (H : ℝ) :
    ContinuousOn (deriv (fdBoundary_H H)) (Ioo 4 5) :=
  deriv_continuousOn_Ioo_const H _ fun s hs ↦ fdBoundary_H_hasDerivAt_seg5' H s hs

private lemma norm_cast_sub_eq {H : ℝ} (hH : Real.sqrt 3 / 2 < H) :
    ‖(↑H - ↑(Real.sqrt 3) / 2 : ℂ)‖ = H - Real.sqrt 3 / 2 := by
  have hcast : (↑H - ↑(Real.sqrt 3) / 2 : ℂ) = ↑(H - Real.sqrt 3 / 2) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by linarith)]

lemma fdBoundary_H_deriv_bound_ex {H : ℝ} (hH : Real.sqrt 3 / 2 < H) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ,
      t ∉ fdBoundary_H_partition → ‖deriv (fdBoundary_H H) t‖ ≤ M := by
  refine ⟨max (H - Real.sqrt 3 / 2) 1,
    lt_max_of_lt_right one_pos, fun t ht ↦ ?_⟩
  simp only [fdBoundary_H_partition, Finset.mem_insert,
    Finset.mem_singleton] at ht
  push Not at ht
  obtain ⟨h1, h3, h4⟩ := ht
  by_cases ht1 : t < 1
  · rw [show deriv (fdBoundary_H H) t = _ from (fdBoundary_H_hasDerivAt_seg1 H ht1).deriv,
      neg_mul, norm_neg, norm_mul, Complex.norm_I, mul_one,
      norm_cast_sub_eq hH]
    exact le_max_left _ _
  · push Not at ht1
    by_cases ht3 : t < 3
    · rw [show deriv (fdBoundary_H H) t = _ from (fdBoundary_H_hasDerivAt_arc H
          (lt_of_le_of_ne ht1 (Ne.symm h1)) ht3).deriv]
      simp only [norm_mul, Complex.norm_I, mul_one]
      have hexp : ‖exp ((↑Real.pi * (↑t + 1) / 6) * I)‖ = 1 := by
        rw [show (↑Real.pi * (↑t + 1) / 6 : ℂ) * I = ↑(Real.pi * (t + 1) / 6) * I by
          push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [hexp, one_mul]
      have hpi : ‖(↑Real.pi / 6 : ℂ)‖ = Real.pi / 6 := by
        rw [show (↑Real.pi / 6 : ℂ) = ↑(Real.pi / 6) by push_cast; ring,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [hpi]
      exact le_max_of_le_right (by linarith [Real.pi_le_four])
    · push Not at ht3
      by_cases ht4 : t < 4
      · rw [show deriv (fdBoundary_H H) t = _ from (fdBoundary_H_hasDerivAt_seg4 H
            (lt_of_le_of_ne ht3 (Ne.symm h3)) ht4).deriv,
          norm_mul, Complex.norm_I, mul_one,
          norm_cast_sub_eq hH]
        exact le_max_left _ _
      · push Not at ht4
        rw [show deriv (fdBoundary_H H) t = _ from (fdBoundary_H_hasDerivAt_seg5 H
            (lt_of_le_of_ne ht4 (Ne.symm h4))).deriv,
          norm_one]
        exact le_max_right _ _

lemma fdBoundary_H_deriv_continuousOn_off_partition (H : ℝ) :
    ContinuousOn (deriv (fdBoundary_H H)) (Icc 0 5 \ ↑fdBoundary_H_partition) := by
  intro t ht
  have ht_icc := ht.1
  have ht_part : t ∉ (fdBoundary_H_partition : Set ℝ) := ht.2
  simp only [fdBoundary_H_partition, Finset.coe_insert,
    Finset.coe_singleton, mem_insert_iff,
    mem_singleton_iff, not_or] at ht_part
  obtain ⟨h1, h3, h4⟩ := ht_part
  by_cases ht0 : t = 0
  · subst ht0
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.congr continuousAt_const
    filter_upwards [Iio_mem_nhds (show (0:ℝ) < 1 by norm_num)] with s hs
    exact (fdBoundary_H_hasDerivAt_seg1 H hs).deriv.symm
  by_cases ht5 : t = 5
  · subst ht5
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.congr continuousAt_const
    filter_upwards [Ioi_mem_nhds (show (4:ℝ) < 5 by norm_num)] with s hs
    exact (fdBoundary_H_hasDerivAt_seg5 H hs).deriv.symm
  have ht_ioo : t ∈ Ioo (0:ℝ) 5 :=
    ⟨lt_of_le_of_ne ht_icc.1 (Ne.symm ht0),
     lt_of_le_of_ne ht_icc.2 ht5⟩
  by_cases ht1 : t < 1
  · exact ((fdBoundary_H_deriv_continuousOn_Ioo_01 H).continuousAt
      (Ioo_mem_nhds ht_ioo.1 ht1)).continuousWithinAt
  · push Not at ht1
    by_cases ht3' : t < 3
    · exact ((fdBoundary_H_deriv_continuousOn_Ioo_13 H).continuousAt
        (Ioo_mem_nhds (lt_of_le_of_ne ht1 (fun h ↦ h1 h.symm))
          ht3')).continuousWithinAt
    · push Not at ht3'
      by_cases ht4' : t < 4
      · exact ((fdBoundary_H_deriv_continuousOn_Ioo_34 H).continuousAt
          (Ioo_mem_nhds (lt_of_le_of_ne ht3' (fun h ↦ h3 h.symm))
            ht4')).continuousWithinAt
      · push Not at ht4'
        exact ((fdBoundary_H_deriv_continuousOn_Ioo_45 H).continuousAt
          (Ioo_mem_nhds (lt_of_le_of_ne ht4' (fun h ↦ h4 h.symm))
            ht_ioo.2)).continuousWithinAt

end
