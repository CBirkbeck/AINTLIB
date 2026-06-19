/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.CrossingAtI
import LeanModularForms.ForMathlib.PVSplitting

/-!
# Asymmetric Crossing Data at rho and rho+1

Constructs `HasGeneralizedWindingNumber` for the corner crossings at the
elliptic points `rho` (t0 = 3/5) and `rho+1` (t0 = 1/5) on the FD boundary.

These are **asymmetric** crossings: the arc segment (unit circle) and the
vertical segment have different geometry. The arc side uses `arcsinDelta`
and the vertical side uses `vertDelta(H, eps) = eps / (5 * (H - sqrt(3)/2))`.

We bypass `SingleCrossingData` (which requires a symmetric delta) and instead
use `pv_tendsto_of_crossing_limit_asymmetric` from `PVSplitting.lean` to
directly construct `HasCauchyPV`, then derive `HasGeneralizedWindingNumber`.

## Main results

* `hasWindingNumber_atRho_of_cornerFtcHyp` -- winding number at rho is `-1/6`
* `hasWindingNumber_atRhoPlusOne_of_cornerFtcHyp` -- winding number at rho+1 is `-1/6`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Vertical delta: `delta(eps) = eps / (5 * (H - sqrt(3)/2))`. -/
def vertDelta (H : ℝ) (ε : ℝ) : ℝ := ε / (5 * (H - Real.sqrt 3 / 2))

theorem vertDelta_pos {H ε : ℝ} (hH : fdHeightValid H) (hε : 0 < ε) :
    0 < vertDelta H ε := by
  unfold vertDelta fdHeightValid at *
  have : 0 < H - Real.sqrt 3 / 2 := by linarith
  positivity

theorem vertDelta_lt_one_fifth {H ε : ℝ} (hH : fdHeightValid H)
    (hε_lt : ε < H - Real.sqrt 3 / 2) :
    vertDelta H ε < 1 / 5 := by
  unfold vertDelta fdHeightValid at *
  have hH' : 0 < H - Real.sqrt 3 / 2 := by linarith
  rw [div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 5)]
  linarith

private theorem vertDelta_mul_eq {H : ℝ} (hH : fdHeightValid H) (ε : ℝ) :
    5 * vertDelta H ε * (H - Real.sqrt 3 / 2) = ε := by
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  unfold vertDelta
  field_simp [ne_of_gt (show (0 : ℝ) < 5 * (H - Real.sqrt 3 / 2) from by positivity)]
  exact mul_div_cancel_right₀ _ (by nlinarith)

private theorem norm_ofReal_mul_I_eq (r : ℝ) (hr : 0 ≤ r) :
    ‖(↑r : ℂ) * I‖ = r := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hr]

private theorem two_sin_abs_le_of_le_arcsin {α ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3)
    (hα : |α| ≤ Real.arcsin (ε/2)) : 2 * Real.sin |α| ≤ ε := by
  have : Real.sin |α| ≤ ε / 2 := by
    rw [← Real.sin_arcsin (show (-1 : ℝ) ≤ ε / 2 by linarith) (show ε / 2 ≤ 1 by linarith)]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [abs_nonneg α, Real.pi_pos])
      (Real.arcsin_le_pi_div_two _) hα
  linarith

private theorem ε_lt_two_sin_abs {α ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3)
    (hα_pi2 : |α| ≤ Real.pi / 2) (hα : Real.arcsin (ε/2) < |α|) :
    ε < 2 * Real.sin |α| := by
  have : ε / 2 < Real.sin |α| := by
    rw [← Real.sin_arcsin (show (-1 : ℝ) ≤ ε / 2 by linarith) (show ε / 2 ≤ 1 by linarith)]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [Real.arcsin_nonneg.mpr (show (0 : ℝ) ≤ ε / 2 by linarith)]) hα_pi2 hα
  linarith

section RhoBounds

variable (H : ℝ)

/-- Near bound on arc for rho: `|t - 3/5| <= arcsinDelta(eps)` implies
`norm(gamma(t) - rho) <= eps`. -/
theorem arc_near_at_rho_arcsin {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3)
    {t : ℝ} (ht2 : t ≤ 3/5) (ht : |t - 3/5| ≤ arcsinDelta ε) :
    ‖fdBoundaryFun H t - ellipticPointRho‖ ≤ ε := by
  have ht1 : (1 : ℝ)/5 < t := by
    nlinarith [(abs_le.mp ht).1, arcsinDelta_lt_one_fifth hε hε_lt]
  rw [fdBoundaryFun_arc_dist_rho H t ht1 ht2,
    show (fdArcAngle t - 2 * Real.pi / 3) / 2 = 5 * (t - 3/5) * Real.pi / 12 from by
      simp only [fdArcAngle]; ring]
  set α := 5 * (t - 3/5) * Real.pi / 12
  have hα_le_asin : |α| ≤ Real.arcsin (ε / 2) := by
    rw [show α = 5 * Real.pi / 12 * (t - 3/5) from by ring, abs_mul,
      abs_of_pos (by positivity), ← half_angle_arcsinDelta]
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  have hα_le_pi : |α| ≤ Real.pi :=
    (hα_le_asin.trans (Real.arcsin_le_pi_div_two _)).trans (by linarith [Real.pi_pos])
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hα_le_pi]
  exact two_sin_abs_le_of_le_arcsin hε hε_lt hα_le_asin

/-- Far bound on arc for rho: `arcsinDelta(eps) < |t - 3/5|` implies `eps < norm`. -/
theorem arc_far_at_rho_arcsin {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3)
    {t : ℝ} (ht_arc : t ∈ Icc (1/5 : ℝ) (3/5))
    (hδt : arcsinDelta ε < |t - 3/5|) :
    ε < ‖fdBoundaryFun H t - ellipticPointRho‖ := by
  have ht3 : t < 3/5 := by
    by_contra h
    push Not at h
    have ht_eq : t = 3/5 := le_antisymm ht_arc.2 h
    subst ht_eq
    simp only [sub_self, abs_zero] at hδt
    linarith [arcsinDelta_pos hε]
  rcases eq_or_lt_of_le ht_arc.1 with rfl | ht1
  · calc ε < 1/3 := hε_lt
      _ ≤ 1 := by norm_num
      _ ≤ _ := fdBoundaryFun_seg1_dist_rho_lower H (1/5) (le_refl _)
  rw [fdBoundaryFun_arc_dist_rho H t ht1 (le_of_lt ht3),
    show (fdArcAngle t - 2 * Real.pi / 3) / 2 = 5 * (t - 3/5) * Real.pi / 12 from by
      simp only [fdArcAngle]; ring]
  set α := 5 * (t - 3/5) * Real.pi / 12
  have hα_abs : |α| = 5 * Real.pi / 12 * |t - 3/5| := by
    rw [show α = 5 * Real.pi / 12 * (t - 3/5) from by ring, abs_mul,
      abs_of_pos (by positivity)]
  have hα_gt_asin : Real.arcsin (ε / 2) < |α| := by
    rw [hα_abs, ← half_angle_arcsinDelta]
    exact mul_lt_mul_of_pos_left hδt (by positivity)
  have h_abs_bound : |t - 3/5| ≤ 2/5 :=
    abs_le.mpr ⟨by linarith [ht_arc.1], by linarith [ht_arc.2]⟩
  have hα_le_pi6 : |α| ≤ Real.pi / 6 := by rw [hα_abs]; nlinarith [Real.pi_pos]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [Real.pi_pos])]
  exact ε_lt_two_sin_abs hε hε_lt (by linarith [Real.pi_pos]) hα_gt_asin

/-- Distance from rho on segment 4 (left vertical). -/
theorem fdBoundaryFun_seg4_dist_rho (hH : fdHeightValid H) (t : ℝ)
    (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    ‖fdBoundaryFun H t - ellipticPointRho‖ =
      5 * (t - 3/5) * (H - Real.sqrt 3 / 2) := by
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    ht4, ite_true, ite_false,
    ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  have h_eq : (-1 : ℂ) / 2 +
      (↑(Real.sqrt 3) / 2 + (5 * ↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I -
      (-1 / 2 + ↑(Real.sqrt 3) / 2 * I) =
      ↑(5 * (t - 3/5) * (H - Real.sqrt 3 / 2)) * I := by push_cast; ring
  rw [h_eq, norm_ofReal_mul_I_eq _ (by nlinarith)]

/-- Near bound on vertical for rho. -/
theorem vert_near_at_rho (hH : fdHeightValid H)
    {ε : ℝ} {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5)
    (hδ : t - 3/5 ≤ vertDelta H ε) :
    ‖fdBoundaryFun H t - ellipticPointRho‖ ≤ ε := by
  rw [fdBoundaryFun_seg4_dist_rho H hH t ht3 ht4]
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  have h1 : 5 * (t - 3/5) * (H - Real.sqrt 3 / 2) ≤
      5 * vertDelta H ε * (H - Real.sqrt 3 / 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ (by norm_num)) hH'.le
  linarith [vertDelta_mul_eq hH ε]

/-- Far bound on vertical for rho. -/
theorem vert_far_at_rho (hH : fdHeightValid H)
    {ε : ℝ} {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5)
    (hδt : vertDelta H ε < t - 3/5) :
    ε < ‖fdBoundaryFun H t - ellipticPointRho‖ := by
  rw [fdBoundaryFun_seg4_dist_rho H hH t ht3 ht4]
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  linarith [vertDelta_mul_eq hH ε,
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hδt (by norm_num : (0:ℝ) < 5)) hH']

end RhoBounds

section RhoPlusOneBounds

variable (H : ℝ)

/-- Near bound on arc for rho+1. -/
theorem arc_near_at_rhoPlusOne_arcsin {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3)
    {t : ℝ} (ht1 : 1/5 ≤ t) (ht : |t - 1/5| ≤ arcsinDelta ε) :
    ‖fdBoundaryFun H t - ellipticPointRhoPlusOne‖ ≤ ε := by
  have ht2 : t ≤ 3/5 := by
    nlinarith [(abs_le.mp ht).2, arcsinDelta_lt_one_fifth hε hε_lt]
  rcases eq_or_lt_of_le ht1 with rfl | ht1'
  · rw [fdBoundaryFun_at_one_fifth, sub_self, norm_zero]
    linarith
  rw [fdBoundaryFun_arc_dist_rhoPlusOne H t ht1' ht2,
    show (fdArcAngle t - Real.pi / 3) / 2 = 5 * (t - 1/5) * Real.pi / 12 from by
      simp only [fdArcAngle]; ring]
  set α := 5 * (t - 1/5) * Real.pi / 12
  have hα_le_asin : |α| ≤ Real.arcsin (ε / 2) := by
    rw [show α = 5 * Real.pi / 12 * (t - 1/5) from by ring, abs_mul,
      abs_of_pos (by positivity), ← half_angle_arcsinDelta]
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  have hα_le_pi : |α| ≤ Real.pi :=
    (hα_le_asin.trans (Real.arcsin_le_pi_div_two _)).trans (by linarith [Real.pi_pos])
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hα_le_pi]
  exact two_sin_abs_le_of_le_arcsin hε hε_lt hα_le_asin

/-- Far bound on arc for rho+1. -/
theorem arc_far_at_rhoPlusOne_arcsin {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3)
    {t : ℝ} (ht_arc : t ∈ Icc (1/5 : ℝ) (3/5))
    (hδt : arcsinDelta ε < |t - 1/5|) :
    ε < ‖fdBoundaryFun H t - ellipticPointRhoPlusOne‖ := by
  have ht1 : 1/5 < t := by
    by_contra h
    push Not at h
    have ht_eq : t = 1/5 := le_antisymm h ht_arc.1
    subst ht_eq
    simp only [sub_self, abs_zero] at hδt
    linarith [arcsinDelta_pos hε]
  rw [fdBoundaryFun_arc_dist_rhoPlusOne H t ht1 ht_arc.2,
    show (fdArcAngle t - Real.pi / 3) / 2 = 5 * (t - 1/5) * Real.pi / 12 from by
      simp only [fdArcAngle]; ring]
  set α := 5 * (t - 1/5) * Real.pi / 12
  have hα_abs : |α| = 5 * Real.pi / 12 * |t - 1/5| := by
    rw [show α = 5 * Real.pi / 12 * (t - 1/5) from by ring, abs_mul,
      abs_of_pos (by positivity)]
  have hα_gt_asin : Real.arcsin (ε / 2) < |α| := by
    rw [hα_abs, ← half_angle_arcsinDelta]
    exact mul_lt_mul_of_pos_left hδt (by positivity)
  have h_abs_bound : |t - 1/5| ≤ 2/5 :=
    abs_le.mpr ⟨by linarith [ht_arc.1], by linarith [ht_arc.2]⟩
  have hα_le_pi6 : |α| ≤ Real.pi / 6 := by rw [hα_abs]; nlinarith [Real.pi_pos]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [Real.pi_pos])]
  exact ε_lt_two_sin_abs hε hε_lt (by linarith [Real.pi_pos]) hα_gt_asin

/-- Distance from rho+1 on segment 1 (right vertical). -/
theorem fdBoundaryFun_seg1_dist_rhoPlusOne (hH : fdHeightValid H) (t : ℝ)
    (_ht0 : 0 ≤ t) (ht1 : t < 1/5) :
    ‖fdBoundaryFun H t - ellipticPointRhoPlusOne‖ =
      5 * (1/5 - t) * (H - Real.sqrt 3 / 2) := by
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  simp only [fdBoundaryFun, show t ≤ 1/5 from by linarith, ite_true,
    ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  have h_eq : (1 : ℂ) / 2 +
      (↑H - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I -
      (1 / 2 + ↑(Real.sqrt 3) / 2 * I) =
      ↑(5 * (1/5 - t) * (H - Real.sqrt 3 / 2)) * I := by push_cast; ring
  rw [h_eq, norm_ofReal_mul_I_eq _ (by nlinarith)]

/-- Near bound on vertical for rho+1. -/
theorem vert_near_at_rhoPlusOne (hH : fdHeightValid H)
    {ε : ℝ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1/5)
    (hδ : 1/5 - t ≤ vertDelta H ε) :
    ‖fdBoundaryFun H t - ellipticPointRhoPlusOne‖ ≤ ε := by
  rw [fdBoundaryFun_seg1_dist_rhoPlusOne H hH t ht0 ht1]
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  have h1 : 5 * (1/5 - t) * (H - Real.sqrt 3 / 2) ≤
      5 * vertDelta H ε * (H - Real.sqrt 3 / 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ (by norm_num)) hH'.le
  linarith [vertDelta_mul_eq hH ε]

/-- Far bound on vertical for rho+1. -/
theorem vert_far_at_rhoPlusOne (hH : fdHeightValid H)
    {ε : ℝ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1/5)
    (hδt : vertDelta H ε < 1/5 - t) :
    ε < ‖fdBoundaryFun H t - ellipticPointRhoPlusOne‖ := by
  rw [fdBoundaryFun_seg1_dist_rhoPlusOne H hH t ht0 ht1]
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH; linarith
  linarith [vertDelta_mul_eq hH ε,
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hδt (by norm_num : (0:ℝ) < 5)) hH']

end RhoPlusOneBounds

/-- Analytic hypotheses for the asymmetric FTC telescope at a corner crossing. -/
structure CornerFTCHyp {x y : ℂ} (γ : PiecewiseC1Path x y) (z₀ : ℂ)
    (t₀ : ℝ) (δ_left δ_right : ℝ → ℝ) (threshold : ℝ) (L : ℂ) where
  /-- FTC expression for the far-segment integrals. -/
  E : ℝ → ℂ
  /-- The far-segment integrals equal `E(epsilon)`. -/
  h_ftc : ∀ ε, 0 < ε → ε < threshold →
    (∫ t in (0 : ℝ)..(t₀ - δ_left ε),
        (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t) +
    (∫ t in (t₀ + δ_right ε)..1,
        (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t) = E ε
  /-- Integrability on the left segment. -/
  hint_left : ∀ ε, 0 < ε → ε < threshold →
    IntervalIntegrable
      (fun t ↦ (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t)
      volume 0 (t₀ - δ_left ε)
  /-- Integrability on the right segment. -/
  hint_right : ∀ ε, 0 < ε → ε < threshold →
    IntervalIntegrable
      (fun t ↦ (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t)
      volume (t₀ + δ_right ε) 1
  /-- `E(epsilon) -> L` as `epsilon -> 0+`. -/
  h_limit : Tendsto E (𝓝[>] 0) (𝓝 L)

/-- Far bound on the left (arc) side of the rho crossing. -/
private theorem rho_far_left {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {ε : ℝ} (hε : 0 < ε) (hε_13 : ε < 1/3) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) (3/5 - arcsinDelta ε)) :
    ε < ‖γ.toPath.extend t - ellipticPointRho‖ := by
  have ht01 : t ∈ Icc (0 : ℝ) 1 :=
    ⟨ht.1, le_of_lt (by linarith [ht.2, arcsinDelta_pos hε])⟩
  rw [hγ t ht01]
  by_cases ht1 : t ≤ 1/5
  · calc ε < 1/3 := hε_13
      _ ≤ 1 := by norm_num
      _ ≤ _ := fdBoundaryFun_seg1_dist_rho_lower H t ht1
  · push Not at ht1
    have ht3 : t ≤ 3/5 := by linarith [ht.2, arcsinDelta_pos hε]
    exact arc_far_at_rho_arcsin H hε hε_13 ⟨le_of_lt ht1, ht3⟩ (by
      rw [show t - 3/5 = -(3/5 - t) from by ring, abs_neg,
        abs_of_pos (by linarith [ht.2, arcsinDelta_pos hε])]
      linarith [ht.2])

/-- Far bound on the right (vertical) side of the rho crossing. -/
private theorem rho_far_right {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {ε : ℝ} (hε : 0 < ε) (hε_H : ε < H - Real.sqrt 3 / 2) {t : ℝ}
    (ht : t ∈ Ioc (3/5 + vertDelta H ε) 1) :
    ε < ‖γ.toPath.extend t - ellipticPointRho‖ := by
  have hH_valid := fdHeightValid_of_one_lt H hH
  have ht01 : t ∈ Icc (0 : ℝ) 1 :=
    ⟨le_trans (by linarith [vertDelta_pos hH_valid hε]) (le_of_lt ht.1), ht.2⟩
  rw [hγ t ht01]
  by_cases ht4 : t ≤ 4/5
  · have ht3 : 3/5 < t := by linarith [ht.1, vertDelta_pos hH_valid hε]
    exact vert_far_at_rho H hH_valid ht3 ht4 (by linarith [ht.1])
  · push Not at ht4
    calc ε < H - Real.sqrt 3 / 2 := hε_H
      _ ≤ _ := fdBoundaryFun_seg5_dist_rho_lower H hH_valid t ht4

/-- Near bound at the rho crossing: arc side or vertical side. -/
private theorem rho_near {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {ε : ℝ} (hε : 0 < ε) (hε_13 : ε < 1/3)
    (hε_H : ε < H - Real.sqrt 3 / 2) {t : ℝ}
    (ht : t ∈ Icc (3/5 - arcsinDelta ε) (3/5 + vertDelta H ε)) :
    ‖γ.toPath.extend t - ellipticPointRho‖ ≤ ε := by
  have hH_valid := fdHeightValid_of_one_lt H hH
  have ht01 : t ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [ht.1, arcsinDelta_lt_one_fifth hε hε_13],
     by linarith [ht.2, vertDelta_lt_one_fifth hH_valid hε_H]⟩
  rw [hγ t ht01]
  by_cases ht35 : t ≤ 3/5
  · exact arc_near_at_rho_arcsin H hε hε_13 ht35 (by
      rw [show t - 3/5 = -(3/5 - t) from by ring, abs_neg,
        abs_of_nonneg (by linarith)]
      linarith [ht.1])
  · push Not at ht35
    have ht4 : t ≤ 4/5 := by linarith [ht.2, vertDelta_lt_one_fifth hH_valid hε_H]
    exact vert_near_at_rho H hH_valid ht35 ht4 (by linarith [ht.2])

/-- Far bound on the left (vertical) side of the rho+1 crossing. -/
private theorem rhoPlusOne_far_left {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {ε : ℝ} (hε : 0 < ε) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) (1/5 - vertDelta H ε)) :
    ε < ‖γ.toPath.extend t - ellipticPointRhoPlusOne‖ := by
  have hH_valid := fdHeightValid_of_one_lt H hH
  have ht01 : t ∈ Icc (0 : ℝ) 1 :=
    ⟨ht.1, le_of_lt (by linarith [ht.2, vertDelta_pos hH_valid hε])⟩
  rw [hγ t ht01]
  have ht1 : t < 1/5 := by linarith [ht.2, vertDelta_pos hH_valid hε]
  exact vert_far_at_rhoPlusOne H hH_valid ht.1 ht1 (by linarith [ht.2])

/-- Far bound on the right (arc) side of the rho+1 crossing. -/
private theorem rhoPlusOne_far_right {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {ε : ℝ} (hε : 0 < ε) (hε_13 : ε < 1/3)
    (hε_H : ε < H - Real.sqrt 3 / 2) {t : ℝ}
    (ht : t ∈ Ioc (1/5 + arcsinDelta ε) 1) :
    ε < ‖γ.toPath.extend t - ellipticPointRhoPlusOne‖ := by
  have ht01 : t ∈ Icc (0 : ℝ) 1 :=
    ⟨le_trans (by linarith [arcsinDelta_pos hε]) (le_of_lt ht.1), ht.2⟩
  rw [hγ t ht01]
  by_cases ht3 : t ≤ 3/5
  · have ht1 : 1/5 < t := by linarith [ht.1, arcsinDelta_pos hε]
    exact arc_far_at_rhoPlusOne_arcsin H hε hε_13 ⟨le_of_lt ht1, ht3⟩ (by
      rw [abs_of_pos (by linarith)]
      linarith [ht.1])
  · push Not at ht3
    by_cases ht4 : t ≤ 4/5
    · calc ε < 1/3 := hε_13
        _ ≤ 1 := by norm_num
        _ ≤ _ := fdBoundaryFun_seg4_dist_rhoPlusOne_lower H t ht3 ht4
    · push Not at ht4
      calc ε < H - Real.sqrt 3 / 2 := hε_H
        _ ≤ _ := fdBoundaryFun_seg5_dist_rhoPlusOne_lower H
          (fdHeightValid_of_one_lt H hH) t ht4

/-- Near bound at the rho+1 crossing: vertical side or arc side. -/
private theorem rhoPlusOne_near {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {ε : ℝ} (hε : 0 < ε) (hε_13 : ε < 1/3)
    (hε_H : ε < H - Real.sqrt 3 / 2) {t : ℝ}
    (ht : t ∈ Icc (1/5 - vertDelta H ε) (1/5 + arcsinDelta ε)) :
    ‖γ.toPath.extend t - ellipticPointRhoPlusOne‖ ≤ ε := by
  have hH_valid := fdHeightValid_of_one_lt H hH
  have ht01 : t ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [ht.1, vertDelta_lt_one_fifth hH_valid hε_H],
     by linarith [ht.2, arcsinDelta_lt_one_fifth hε hε_13]⟩
  rw [hγ t ht01]
  by_cases ht15 : 1/5 ≤ t
  · exact arc_near_at_rhoPlusOne_arcsin H hε hε_13 ht15 (by
      rw [abs_of_nonneg (by linarith)]
      linarith [ht.2])
  · push Not at ht15
    have ht0 : 0 ≤ t := by linarith [ht.1, vertDelta_lt_one_fifth hH_valid hε_H]
    exact vert_near_at_rhoPlusOne H hH_valid ht0 ht15 (by linarith [ht.1])

/-- The winding number at rho is `-1/6`, constructed via the asymmetric
crossing limit theorem. -/
theorem hasWindingNumber_atRho_of_cornerFtcHyp {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (ftcHyp : CornerFTCHyp γ ellipticPointRho (3/5)
      arcsinDelta (vertDelta H) (min (1/3) (H - Real.sqrt 3 / 2))
      (-(↑Real.pi / 3 * I))) :
    HasGeneralizedWindingNumber γ ellipticPointRho (-1/6) := by
  have hH_valid : fdHeightValid H := fdHeightValid_of_one_lt H hH
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH_valid; linarith
  have hthresh : 0 < min (1/3 : ℝ) (H - Real.sqrt 3 / 2) := lt_min (by norm_num) hH'
  have h_pv : HasCauchyPV (fun z ↦ (z - ellipticPointRho)⁻¹) γ ellipticPointRho
      (-(↑Real.pi / 3 * I)) := by
    simp only [HasCauchyPV]
    apply PVSplitting.pv_tendsto_of_crossing_limit_asymmetric
      (ht₀ := show (3/5 : ℝ) ∈ Ioo 0 1 from ⟨by norm_num, by norm_num⟩)
      (hthresh := hthresh)
      (δ_left := arcsinDelta) (δ_right := vertDelta H)
      (hδL_pos := fun ε hε _ ↦ arcsinDelta_pos hε)
      (hδR_pos := fun ε hε _ ↦ vertDelta_pos hH_valid hε)
      (hδL_small := fun ε hε hεt ↦ by
        linarith [arcsinDelta_lt_one_fifth hε (lt_of_lt_of_le hεt (min_le_left _ _))])
      (hδR_small := fun ε hε hεt ↦ by
        linarith [vertDelta_lt_one_fifth hH_valid
          (lt_of_lt_of_le hεt (min_le_right _ _))])
      (h_far_left := fun ε hε hεt t ht ↦
        rho_far_left γ hγ hε (lt_of_lt_of_le hεt (min_le_left _ _)) ht)
      (h_far_right := fun ε hε hεt t ht ↦
        rho_far_right hH γ hγ hε (lt_of_lt_of_le hεt (min_le_right _ _)) ht)
      (h_near := fun ε hε hεt t ht ↦
        rho_near hH γ hγ hε (lt_of_lt_of_le hεt (min_le_left _ _))
          (lt_of_lt_of_le hεt (min_le_right _ _)) ht)
      (h_ftc := ftcHyp.h_ftc)
      (hint_left := ftcHyp.hint_left)
      (hint_right := ftcHyp.hint_right)
      (h_limit := ftcHyp.h_limit)
  convert hasGeneralizedWindingNumber_of_hasCauchyPV h_pv using 1
  have hpi : (Real.pi : ℂ) ≠ 0 := mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- The winding number at rho+1 is `-1/6`, constructed via the asymmetric
crossing limit theorem. -/
theorem hasWindingNumber_atRhoPlusOne_of_cornerFtcHyp {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (ftcHyp : CornerFTCHyp γ ellipticPointRhoPlusOne (1/5)
      (vertDelta H) arcsinDelta (min (1/3) (H - Real.sqrt 3 / 2))
      (-(↑Real.pi / 3 * I))) :
    HasGeneralizedWindingNumber γ ellipticPointRhoPlusOne (-1/6) := by
  have hH_valid : fdHeightValid H := fdHeightValid_of_one_lt H hH
  have hH' : 0 < H - Real.sqrt 3 / 2 := by unfold fdHeightValid at hH_valid; linarith
  have hthresh : 0 < min (1/3 : ℝ) (H - Real.sqrt 3 / 2) := lt_min (by norm_num) hH'
  have h_pv : HasCauchyPV (fun z ↦ (z - ellipticPointRhoPlusOne)⁻¹) γ
      ellipticPointRhoPlusOne (-(↑Real.pi / 3 * I)) := by
    simp only [HasCauchyPV]
    apply PVSplitting.pv_tendsto_of_crossing_limit_asymmetric
      (ht₀ := show (1/5 : ℝ) ∈ Ioo 0 1 from ⟨by norm_num, by norm_num⟩)
      (hthresh := hthresh)
      (δ_left := vertDelta H) (δ_right := arcsinDelta)
      (hδL_pos := fun ε hε _ ↦ vertDelta_pos hH_valid hε)
      (hδR_pos := fun ε hε _ ↦ arcsinDelta_pos hε)
      (hδL_small := fun ε hε hεt ↦
        vertDelta_lt_one_fifth hH_valid (lt_of_lt_of_le hεt (min_le_right _ _)))
      (hδR_small := fun ε hε hεt ↦ by
        linarith [arcsinDelta_lt_one_fifth hε (lt_of_lt_of_le hεt (min_le_left _ _))])
      (h_far_left := fun ε hε _ t ht ↦ rhoPlusOne_far_left hH γ hγ hε ht)
      (h_far_right := fun ε hε hεt t ht ↦
        rhoPlusOne_far_right hH γ hγ hε (lt_of_lt_of_le hεt (min_le_left _ _))
          (lt_of_lt_of_le hεt (min_le_right _ _)) ht)
      (h_near := fun ε hε hεt t ht ↦
        rhoPlusOne_near hH γ hγ hε (lt_of_lt_of_le hεt (min_le_left _ _))
          (lt_of_lt_of_le hεt (min_le_right _ _)) ht)
      (h_ftc := ftcHyp.h_ftc)
      (hint_left := ftcHyp.hint_left)
      (hint_right := ftcHyp.hint_right)
      (h_limit := ftcHyp.h_limit)
  convert hasGeneralizedWindingNumber_of_hasCauchyPV h_pv using 1
  have hpi : (Real.pi : ℂ) ≠ 0 := mod_cast Real.pi_ne_zero
  field_simp
  ring

end
