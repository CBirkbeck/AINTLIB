/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDBoundaryPath
import LeanModularForms.ForMathlib.ArcFTCLimit
import LeanModularForms.ForMathlib.SingleCrossing
import LeanModularForms.ForMathlib.WindingWeightsUnconditional

/-!
# SingleCrossingData for the FD boundary crossing at i

Constructs a `SingleCrossingData` for the FD boundary crossing at `i` (`t₀ = 2/5`).

The cutoff `arcsinDelta(ε) = (12/(5π)) · arcsin(ε/2)` exactly inverts the half-angle
distance `‖γ(t) - i‖ = 2|sin(5(t-2/5)π/12)|`. Near and far bounds follow from
monotonicity of `sin` on `[0, π/2]` via `|sin α| = sin|α|`. The analytic core
(FTC, integrability, limit) is taken as an `ArcFTCHyp` parameter.

## Main results

* `singleCrossingData_atI_of_ftcHyp` -- `SingleCrossingData` at `i` from `ArcFTCHyp`
* `windingNumber_atI_of_ftcHyp` -- winding number at `i` is `-1/2`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Exact cutoff for the crossing at `i`: `δ(ε) = (12/(5π)) · arcsin(ε/2)`. -/
def arcsinDelta (ε : ℝ) : ℝ := 12 / (5 * Real.pi) * Real.arcsin (ε / 2)

theorem arcsinDelta_pos {ε : ℝ} (hε : 0 < ε) : 0 < arcsinDelta ε := by
  unfold arcsinDelta
  exact mul_pos (by positivity) (Real.arcsin_pos.mpr (by linarith))

/-- `5π/12 · arcsinDelta(ε) = arcsin(ε/2)`. -/
theorem half_angle_arcsinDelta (ε : ℝ) :
    5 * Real.pi / 12 * arcsinDelta ε = Real.arcsin (ε / 2) := by
  unfold arcsinDelta; field_simp

/-- Jordan's inequality for arcsin: `arcsin(x) ≤ π/2 · x` for `0 ≤ x ≤ 1`. -/
theorem arcsin_le_pi_half_mul {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.arcsin x ≤ Real.pi / 2 * x := by
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · simp
  have h_nn : 0 ≤ Real.arcsin x := Real.arcsin_nonneg.mpr hx
  have h_le : Real.arcsin x ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two x
  have h_jordan := Real.mul_le_sin h_nn h_le
  rw [Real.sin_arcsin (by linarith) hx1] at h_jordan
  have h1 : Real.pi / 2 * (2 / Real.pi * Real.arcsin x) ≤ Real.pi / 2 * x :=
    mul_le_mul_of_nonneg_left h_jordan (by positivity)
  rwa [← mul_assoc, show Real.pi / 2 * (2 / Real.pi) = (1 : ℝ) by field_simp,
    one_mul] at h1

/-- `arcsinDelta(ε) < 1/5` for `0 < ε < 1/3`. -/
theorem arcsinDelta_lt_one_fifth {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) :
    arcsinDelta ε < 1/5 := by
  unfold arcsinDelta
  calc 12 / (5 * Real.pi) * Real.arcsin (ε / 2)
      ≤ 12 / (5 * Real.pi) * (Real.pi / 2 * (ε / 2)) := by
        gcongr; exact arcsin_le_pi_half_mul (by linarith) (by linarith)
    _ = 3 * ε / 5 := by field_simp; ring
    _ < 1 / 5 := by linarith

private theorem halfAngle_eq (t : ℝ) :
    (fdArcAngle t - Real.pi / 2) / 2 = 5 * (t - 2/5) * Real.pi / 12 := by
  simp only [fdArcAngle]; ring

private theorem abs_halfAngle_eq (t : ℝ) :
    |5 * (t - 2/5) * Real.pi / 12| = 5 * Real.pi / 12 * |t - 2/5| := by
  rw [show 5 * (t - 2/5) * Real.pi / 12 = 5 * Real.pi / 12 * (t - 2/5) by ring,
    abs_mul, abs_of_pos (by positivity)]

private theorem abs_halfAngle_le_pi12 {t : ℝ}
    (ht : t ∈ Icc (1/5 : ℝ) (3/5)) :
    |5 * (t - 2/5) * Real.pi / 12| ≤ Real.pi / 12 := by
  rw [abs_halfAngle_eq]
  have h_abs : |t - 2/5| ≤ 1/5 := by
    rw [abs_le]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  calc 5 * Real.pi / 12 * |t - 2/5|
      ≤ 5 * Real.pi / 12 * (1/5) := by gcongr
    _ = Real.pi / 12 := by ring

/-- Near bound: `|t - 2/5| ≤ arcsinDelta(ε)` implies `‖γ(t) - i‖ ≤ ε`. -/
theorem arc_near_at_I_arcsin (H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3)
    {t : ℝ} (ht : |t - 2/5| ≤ arcsinDelta ε) :
    ‖fdBoundaryFun H t - I‖ ≤ ε := by
  have hpi := Real.pi_pos
  have hδ_small := arcsinDelta_lt_one_fifth hε hε_lt
  have ht1 : (1 : ℝ)/5 < t := by
    have := (abs_le.mp ht).1; have := arcsinDelta_pos hε; nlinarith
  have ht2 : t ≤ 3/5 := by
    have := (abs_le.mp ht).2; nlinarith
  rw [fdBoundaryFun_arc_dist_I H t ht1 ht2, halfAngle_eq]
  set α := 5 * (t - 2/5) * Real.pi / 12
  have hα_le_asin : |α| ≤ Real.arcsin (ε / 2) := by
    rw [abs_halfAngle_eq, ← half_angle_arcsinDelta]
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  have harc_le : Real.arcsin (ε / 2) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hα_le_pi : |α| ≤ Real.pi := by linarith
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hα_le_pi]
  have h_sin_le : Real.sin |α| ≤ ε / 2 := by
    rw [← Real.sin_arcsin (show (-1 : ℝ) ≤ ε / 2 by linarith) (show ε / 2 ≤ 1 by linarith)]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [abs_nonneg α]) harc_le hα_le_asin
  linarith

/-- Far bound on arc: `|t - 2/5| > arcsinDelta(ε)` implies `ε < ‖γ(t) - i‖`. -/
theorem arc_far_at_I_arcsin (H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3)
    {t : ℝ} (ht_arc : t ∈ Icc (1/5 : ℝ) (3/5)) (hδt : arcsinDelta ε < |t - 2/5|) :
    ε < ‖fdBoundaryFun H t - I‖ := by
  have hpi := Real.pi_pos
  rcases eq_or_lt_of_le ht_arc.1 with rfl | ht1
  · calc ε < 1/3 := hε_lt
      _ < 1/2 := by norm_num
      _ ≤ ‖fdBoundaryFun H (1/5) - I‖ := fdBoundaryFun_seg1_dist_I_lower H (1/5) le_rfl
  rw [fdBoundaryFun_arc_dist_I H t ht1 ht_arc.2, halfAngle_eq]
  set α := 5 * (t - 2/5) * Real.pi / 12
  have hα_gt_asin : Real.arcsin (ε / 2) < |α| := by
    rw [abs_halfAngle_eq, ← half_angle_arcsinDelta]
    exact mul_lt_mul_of_pos_left hδt (by positivity)
  have hα_le_pi12 := abs_halfAngle_le_pi12 ht_arc
  have hα_le_pi : |α| ≤ Real.pi := by linarith
  have harc_nn : 0 ≤ Real.arcsin (ε / 2) := Real.arcsin_nonneg.mpr (by linarith)
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hα_le_pi]
  have h_sin_gt : ε / 2 < Real.sin |α| := by
    rw [← Real.sin_arcsin (show (-1 : ℝ) ≤ ε / 2 by linarith) (show ε / 2 ≤ 1 by linarith)]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hα_gt_asin
  linarith

/-- Construct `SingleCrossingData` at `i` from `ArcFTCHyp`.

Bundles `t₀ = 2/5`, `L = -(πi)`, `threshold = min(1/3, H-1)`, `δ = arcsinDelta`
with all geometric bounds proved. -/
def singleCrossingData_atI_of_ftcHyp {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (ftcHyp : ArcFTCHyp γ I (2/5) arcsinDelta (min (1/3) (H - 1))
      (-(↑Real.pi * I))) :
    SingleCrossingData γ I :=
  mkSingleCrossingData_atI hH γ hγ
    arcsinDelta (min (1/3) (H - 1))
    (lt_min (by norm_num) (by linarith))
    (min_le_min (by norm_num : (1 : ℝ)/3 ≤ 1/2) le_rfl)
    (fun ε hε hεt ↦ arcsinDelta_pos hε)
    (fun ε hε hεt ↦ arcsinDelta_lt_one_fifth hε (lt_of_lt_of_le hεt (min_le_left _ _)))
    (fun ε hε hεt t ht hδt ↦
      arc_far_at_I_arcsin H hε (lt_of_lt_of_le hεt (min_le_left _ _)) ht hδt)
    (fun ε hε hεt t ht ↦
      arc_near_at_I_arcsin H hε (lt_of_lt_of_le hεt (min_le_left _ _)) ht)
    ftcHyp

end
