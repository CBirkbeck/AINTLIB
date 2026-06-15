/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDBoundary

/-!
# PiecewiseC1Path for the FD Boundary

This file constructs the `PiecewiseC1Path` for the fundamental domain boundary,
proving that `fdBoundaryFun H` is differentiable with continuous derivative on each
segment away from partition points.

## Main definitions

* `fdBoundaryPC1Path` — the FD boundary as a `PiecewiseC1Path`

## Main results

* `fdBoundaryPC1Path_eq` — the path agrees with `fdBoundaryFun` on `[0, 1]`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

private lemma fdBoundaryPath_extend_eq (H : ℝ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (fdBoundaryPath H).extend t = fdBoundaryFun H t :=
  Path.extend_apply _ ht

private lemma fdBoundaryPath_extend_eventuallyEq (H : ℝ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (fdBoundaryPath H).extend =ᶠ[𝓝 t] fdBoundaryFun H :=
  Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs =>
    fdBoundaryPath_extend_eq H s (Ioo_subset_Icc_self hs)

private def seg1Fun (H : ℝ) : ℝ → ℂ := fun t =>
  1/2 + (↑H - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I

private def seg2Fun : ℝ → ℂ := fun t =>
  exp ((↑Real.pi / 3 + (5 * ↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I)

private def seg3Fun : ℝ → ℂ := fun t =>
  exp ((↑Real.pi / 2 + (5 * ↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)

private def seg4Fun (H : ℝ) : ℝ → ℂ := fun t =>
  -1/2 + (↑(Real.sqrt 3) / 2 + (5 * ↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I

private def seg5Fun (H : ℝ) : ℝ → ℂ := fun t =>
  (5 * ↑t - 9/2) + ↑H * I

private lemma seg1Fun_contDiff (H : ℝ) : ContDiff ℝ ⊤ (seg1Fun H) :=
  contDiff_const.add
    ((contDiff_const.sub
      ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const)).mul
      contDiff_const)

private lemma seg2Fun_contDiff : ContDiff ℝ ⊤ seg2Fun :=
  Complex.contDiff_exp.comp
    ((contDiff_const.add
      (((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).mul
        contDiff_const)).mul contDiff_const)

private lemma seg3Fun_contDiff : ContDiff ℝ ⊤ seg3Fun :=
  Complex.contDiff_exp.comp
    ((contDiff_const.add
      (((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).mul
        contDiff_const)).mul contDiff_const)

private lemma seg4Fun_contDiff (H : ℝ) : ContDiff ℝ ⊤ (seg4Fun H) :=
  contDiff_const.add
    ((contDiff_const.add
      (((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).mul
        contDiff_const)).mul contDiff_const)

private lemma seg5Fun_contDiff (H : ℝ) : ContDiff ℝ ⊤ (seg5Fun H) :=
  ((contDiff_const.mul Complex.ofRealCLM.contDiff).sub contDiff_const).add contDiff_const

private lemma fdBoundaryFun_eventuallyEq_seg1 (H : ℝ) (t : ℝ)
    (ht1 : t < 1/5) :
    fdBoundaryFun H =ᶠ[𝓝 t] seg1Fun H :=
  Filter.eventually_of_mem (Iio_mem_nhds ht1) fun s (hs : s < 1/5) => by
    simp only [fdBoundaryFun, seg1Fun, if_pos hs.le]

private lemma fdBoundaryFun_eventuallyEq_seg2 (H : ℝ) (t : ℝ)
    (ht1 : 1/5 < t) (ht2 : t < 2/5) :
    fdBoundaryFun H =ᶠ[𝓝 t] seg2Fun :=
  Filter.eventually_of_mem
    (Filter.inter_mem (Ioi_mem_nhds ht1) (Iio_mem_nhds ht2))
    fun s ⟨hs1, hs2⟩ => by
      simp only [fdBoundaryFun, seg2Fun,
        show ¬s ≤ 1/5 from not_le.mpr hs1,
        show s ≤ 2/5 from le_of_lt hs2, ite_true, ite_false]

private lemma fdBoundaryFun_eventuallyEq_seg3 (H : ℝ) (t : ℝ)
    (ht2 : 2/5 < t) (ht3 : t < 3/5) :
    fdBoundaryFun H =ᶠ[𝓝 t] seg3Fun :=
  Filter.eventually_of_mem
    (Filter.inter_mem (Ioi_mem_nhds ht2) (Iio_mem_nhds ht3))
    fun s ⟨hs2, hs3⟩ => by
      simp only [fdBoundaryFun, seg3Fun,
        show ¬s ≤ 1/5 from not_le.mpr (lt_trans (by norm_num : (1:ℝ)/5 < 2/5) hs2),
        show ¬s ≤ 2/5 from not_le.mpr hs2,
        show s ≤ 3/5 from le_of_lt hs3, ite_true, ite_false]

private lemma fdBoundaryFun_eventuallyEq_seg4 (H : ℝ) (t : ℝ)
    (ht3 : 3/5 < t) (ht4 : t < 4/5) :
    fdBoundaryFun H =ᶠ[𝓝 t] seg4Fun H :=
  Filter.eventually_of_mem
    (Filter.inter_mem (Ioi_mem_nhds ht3) (Iio_mem_nhds ht4))
    fun s ⟨hs3, hs4⟩ => by
      simp only [fdBoundaryFun, seg4Fun,
        show ¬s ≤ 1/5 from not_le.mpr (lt_trans (by norm_num : (1:ℝ)/5 < 3/5) hs3),
        show ¬s ≤ 2/5 from not_le.mpr (lt_trans (by norm_num : (2:ℝ)/5 < 3/5) hs3),
        show ¬s ≤ 3/5 from not_le.mpr hs3,
        show s ≤ 4/5 from le_of_lt hs4, ite_true, ite_false]

private lemma fdBoundaryFun_eventuallyEq_seg5 (H : ℝ) (t : ℝ)
    (ht4 : 4/5 < t) :
    fdBoundaryFun H =ᶠ[𝓝 t] seg5Fun H :=
  Filter.eventually_of_mem (Ioi_mem_nhds ht4) fun s (hs4 : 4/5 < s) => by
    simp only [fdBoundaryFun, seg5Fun,
      show ¬s ≤ 1/5 from not_le.mpr (lt_trans (by norm_num : (1:ℝ)/5 < 4/5) hs4),
      show ¬s ≤ 2/5 from not_le.mpr (lt_trans (by norm_num : (2:ℝ)/5 < 4/5) hs4),
      show ¬s ≤ 3/5 from not_le.mpr (lt_trans (by norm_num : (3:ℝ)/5 < 4/5) hs4),
      show ¬s ≤ 4/5 from not_le.mpr hs4, ite_false]

private lemma fdBoundaryFun_differentiableAt_off (H : ℝ) (t : ℝ)
    (_ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ fdBoundaryPartition) :
    DifferentiableAt ℝ (fdBoundaryFun H) t := by
  simp only [fdBoundaryPartition, Finset.mem_insert, Finset.mem_singleton] at htp
  push Not at htp
  obtain ⟨ht1, ht2, ht3, ht4⟩ := htp
  have hT : (⊤ : WithTop ℕ∞) ≠ 0 := WithTop.top_ne_zero
  rcases lt_or_gt_of_ne ht1 with h1 | h1
  · exact ((seg1Fun_contDiff H).differentiable hT).differentiableAt.congr_of_eventuallyEq
      (fdBoundaryFun_eventuallyEq_seg1 H t h1)
  rcases lt_or_gt_of_ne ht2 with h2 | h2
  · exact (seg2Fun_contDiff.differentiable hT).differentiableAt.congr_of_eventuallyEq
      (fdBoundaryFun_eventuallyEq_seg2 H t h1 h2)
  rcases lt_or_gt_of_ne ht3 with h3 | h3
  · exact (seg3Fun_contDiff.differentiable hT).differentiableAt.congr_of_eventuallyEq
      (fdBoundaryFun_eventuallyEq_seg3 H t h2 h3)
  rcases lt_or_gt_of_ne ht4 with h4 | h4
  · exact ((seg4Fun_contDiff H).differentiable hT).differentiableAt.congr_of_eventuallyEq
      (fdBoundaryFun_eventuallyEq_seg4 H t h3 h4)
  exact ((seg5Fun_contDiff H).differentiable hT).differentiableAt.congr_of_eventuallyEq
    (fdBoundaryFun_eventuallyEq_seg5 H t h4)

private lemma fdBoundaryFun_deriv_continuousAt_off (H : ℝ) (t : ℝ)
    (_ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ fdBoundaryPartition) :
    ContinuousAt (deriv (fdBoundaryFun H)) t := by
  simp only [fdBoundaryPartition, Finset.mem_insert, Finset.mem_singleton] at htp
  push Not at htp
  obtain ⟨ht1, ht2, ht3, ht4⟩ := htp
  rcases lt_or_gt_of_ne ht1 with h1 | h1
  · exact (continuousAt_congr (fdBoundaryFun_eventuallyEq_seg1 H t h1).deriv).mpr
      ((seg1Fun_contDiff H).continuous_deriv le_top).continuousAt
  rcases lt_or_gt_of_ne ht2 with h2 | h2
  · exact (continuousAt_congr (fdBoundaryFun_eventuallyEq_seg2 H t h1 h2).deriv).mpr
      (seg2Fun_contDiff.continuous_deriv le_top).continuousAt
  rcases lt_or_gt_of_ne ht3 with h3 | h3
  · exact (continuousAt_congr (fdBoundaryFun_eventuallyEq_seg3 H t h2 h3).deriv).mpr
      (seg3Fun_contDiff.continuous_deriv le_top).continuousAt
  rcases lt_or_gt_of_ne ht4 with h4 | h4
  · exact (continuousAt_congr (fdBoundaryFun_eventuallyEq_seg4 H t h3 h4).deriv).mpr
      ((seg4Fun_contDiff H).continuous_deriv le_top).continuousAt
  exact (continuousAt_congr (fdBoundaryFun_eventuallyEq_seg5 H t h4).deriv).mpr
    ((seg5Fun_contDiff H).continuous_deriv le_top).continuousAt

private lemma fdBoundaryPath_differentiableAt_off (H : ℝ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ fdBoundaryPartition) :
    DifferentiableAt ℝ (fdBoundaryPath H).extend t :=
  (fdBoundaryFun_differentiableAt_off H t ht htp).congr_of_eventuallyEq
    (fdBoundaryPath_extend_eventuallyEq H t ht)

private lemma fdBoundaryPath_deriv_continuousAt_off (H : ℝ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ fdBoundaryPartition) :
    ContinuousAt (deriv (fdBoundaryPath H).extend) t :=
  (continuousAt_congr (fdBoundaryPath_extend_eventuallyEq H t ht).deriv).mpr
    (fdBoundaryFun_deriv_continuousAt_off H t ht htp)

/-- The fundamental domain boundary as a `PiecewiseC1Path`. -/
def fdBoundaryPC1Path (H : ℝ) (_hH : H > Real.sqrt 3 / 2) :
    PiecewiseC1Path (fdStart H) (fdStart H) where
  toFun := (fdBoundaryPath H).extend
  source := (fdBoundaryPath H).extend_zero
  target := (fdBoundaryPath H).extend_one
  continuous_toFun := (fdBoundaryPath H).continuous_extend.continuousOn
  toPath := fdBoundaryPath H
  toPath_extend_eq_toFun := fun _ _ => rfl
  partition := fdBoundaryPartition
  partition_subset := fdBoundaryPartition_subset_Ioo
  differentiable_off := fdBoundaryPath_differentiableAt_off H
  deriv_continuous_off := fdBoundaryPath_deriv_continuousAt_off H

/-- The `PiecewiseC1Path` agrees with `fdBoundaryFun` on `[0, 1]`. -/
theorem fdBoundaryPC1Path_eq (H : ℝ) (hH : H > Real.sqrt 3 / 2) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (fdBoundaryPC1Path H hH).toPath.extend t = fdBoundaryFun H t :=
  fdBoundaryPath_extend_eq H t ht

end
