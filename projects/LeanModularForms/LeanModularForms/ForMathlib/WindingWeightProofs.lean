/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDBoundary
import LeanModularForms.ForMathlib.SingleCrossing
import LeanModularForms.ForMathlib.SegmentFTC

/-!
# Winding Weight Proofs for the Valence Formula

This file provides the geometric infrastructure and assembly theorems for computing
the generalized winding numbers at the three elliptic/on-curve points of the
standard fundamental domain boundary: `i`, `rho`, and `rho+1`.

## Strategy

The computation of each winding weight follows the `SingleCrossingData` framework
from `SingleCrossing.lean`. For each crossing point, we need:

1. **Geometric facts** (proved here): arc angle parametrization, distance formulas,
   segment-wise lower bounds on distance from the crossing point.
2. **Analytic facts** (taken as hypotheses in the constructors): FTC telescoping,
   integrability, and the limit of the FTC expression.

The geometric facts are fully proved. The analytic facts (FTC + integrability + limit)
are the inputs to the constructor `mkSingleCrossingData_atI`.

## Main definitions

* `fdArcAngle` -- the arc angle function for segments 2-3
* `ArcFTCHyp` -- the analytic hypotheses (FTC + integrability + limit) for a crossing

## Main results

### Geometric lemmas
* `norm_exp_sub_exp` -- distance on the unit circle via sin half-angle
* `fdBoundaryFun_arc_eq_exp` -- arc segments equal `exp(i * fdArcAngle t)`
* `fdBoundaryFun_arc_dist_*` -- arc distance to each crossing point
* `fdBoundaryFun_seg*_dist_*_lower` -- distance lower bounds per segment

### Assembly
* `mkSingleCrossingData_atI` -- `SingleCrossingData` at `i` from geometric + analytic data

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- The arc angle function for the FD boundary segments 2-3. On `[1/5, 3/5]`,
the boundary traces `exp(i * fdArcAngle t)` along the unit circle from
angle `pi/3` (at `t = 1/5`) through `pi/2` (at `t = 2/5`) to `2pi/3` (at `t = 3/5`). -/
def fdArcAngle (t : ℝ) : ℝ := Real.pi / 3 + (5 * t - 1) * (Real.pi / 6)

theorem fdArcAngle_at_one_fifth : fdArcAngle (1/5) = Real.pi / 3 := by
  unfold fdArcAngle; ring

theorem fdArcAngle_at_three_fifths : fdArcAngle (3/5) = 2 * Real.pi / 3 := by
  unfold fdArcAngle; ring

@[fun_prop]
theorem fdArcAngle_continuous : Continuous fdArcAngle := by
  unfold fdArcAngle; fun_prop

private theorem cos_sin_sub_sq_eq_half_angle_sq (θ φ : ℝ) :
    (Real.cos θ - Real.cos φ) ^ 2 + (Real.sin θ - Real.sin φ) ^ 2 =
      (2 * |Real.sin ((θ - φ) / 2)|) ^ 2 := by
  have hcos_2 := (show 2 * ((θ - φ) / 2) = θ - φ by ring) ▸ Real.cos_two_mul ((θ - φ) / 2)
  rw [mul_pow, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ, Real.cos_sub θ φ,
    Real.sin_sq_add_cos_sq ((θ - φ) / 2), hcos_2]

/-- Distance between two points on the unit circle:
`norm(exp(i*theta) - exp(i*phi)) = 2|sin((theta-phi)/2)|`.

Proved by expanding to `cos + i*sin` form and using the half-angle identity. -/
theorem norm_exp_sub_exp (θ φ : ℝ) :
    ‖exp (↑θ * I) - exp (↑φ * I)‖ = 2 * |Real.sin ((θ - φ) / 2)| := by
  rw [exp_mul_I, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cos, ← ofReal_sin,
    show (↑(Real.cos θ) + ↑(Real.sin θ) * I) - (↑(Real.cos φ) + ↑(Real.sin φ) * I) =
      ↑(Real.cos θ - Real.cos φ) + ↑(Real.sin θ - Real.sin φ) * I by push_cast; ring,
    norm_add_mul_I, cos_sin_sub_sq_eq_half_angle_sq]
  exact Real.sqrt_sq (by positivity)

/-- On segments 2-3 (`t` in `(1/5, 3/5]`), the FD boundary is `exp(i * fdArcAngle t)`. -/
theorem fdBoundaryFun_arc_eq_exp (H : ℝ) (t : ℝ) (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    fdBoundaryFun H t = exp (↑(fdArcAngle t) * I) := by
  have hh : ¬ t ≤ 1/5 := by linarith
  rcases le_or_gt t (2/5) with ht | ht
  · simp only [fdBoundaryFun, fdArcAngle, hh, ht, ite_false, ite_true]
    congr 1; push_cast; ring
  · simp only [fdBoundaryFun, fdArcAngle, hh, ht2, show ¬t ≤ 2/5 by linarith,
      ite_false, ite_true]
    congr 1; push_cast; ring

/-- The arc distance to `I`:
`norm(fdBoundaryFun H t - I) = 2|sin((fdArcAngle t - pi/2)/2)|` for `t` in `(1/5, 3/5]`. -/
theorem fdBoundaryFun_arc_dist_I (H : ℝ) (t : ℝ) (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    ‖fdBoundaryFun H t - I‖ = 2 * |Real.sin ((fdArcAngle t - Real.pi / 2) / 2)| := by
  set θ := fdArcAngle t
  rw [fdBoundaryFun_arc_eq_exp H t ht1 ht2, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (↑(Real.cos θ) + ↑(Real.sin θ) * I : ℂ) - I =
        ↑(Real.cos θ - Real.cos (Real.pi / 2)) +
        ↑(Real.sin θ - Real.sin (Real.pi / 2)) * I by
      rw [Real.cos_pi_div_two, Real.sin_pi_div_two]; push_cast; ring,
    norm_add_mul_I, cos_sin_sub_sq_eq_half_angle_sq]
  exact Real.sqrt_sq (by positivity)

/-- The arc distance to `rho`:
`norm(fdBoundaryFun H t - rho) = 2|sin((fdArcAngle t - 2pi/3)/2)|` for `t` in `(1/5, 3/5]`. -/
theorem fdBoundaryFun_arc_dist_rho (H : ℝ) (t : ℝ) (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    ‖fdBoundaryFun H t - ellipticPointRho‖ =
      2 * |Real.sin ((fdArcAngle t - 2 * Real.pi / 3) / 2)| := by
  set θ := fdArcAngle t
  rw [fdBoundaryFun_arc_eq_exp H t ht1 ht2, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (↑(Real.cos θ) + ↑(Real.sin θ) * I : ℂ) - ellipticPointRho =
        ↑(Real.cos θ - Real.cos (2 * Real.pi / 3)) +
        ↑(Real.sin θ - Real.sin (2 * Real.pi / 3)) * I by
      simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
      rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
      push_cast; ring,
    norm_add_mul_I, cos_sin_sub_sq_eq_half_angle_sq]
  exact Real.sqrt_sq (by positivity)

/-- The arc distance to `rho+1`:
`norm(fdBoundaryFun H t - (rho+1)) = 2|sin((fdArcAngle t - pi/3)/2)|` for `t` in `(1/5, 3/5]`. -/
theorem fdBoundaryFun_arc_dist_rhoPlusOne (H : ℝ) (t : ℝ)
    (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    ‖fdBoundaryFun H t - ellipticPointRhoPlusOne‖ =
      2 * |Real.sin ((fdArcAngle t - Real.pi / 3) / 2)| := by
  set θ := fdArcAngle t
  rw [fdBoundaryFun_arc_eq_exp H t ht1 ht2, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (↑(Real.cos θ) + ↑(Real.sin θ) * I : ℂ) - ellipticPointRhoPlusOne =
        ↑(Real.cos θ - Real.cos (Real.pi / 3)) +
        ↑(Real.sin θ - Real.sin (Real.pi / 3)) * I by
      simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
      rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
      push_cast; ring,
    norm_add_mul_I, cos_sin_sub_sq_eq_half_angle_sq]
  exact Real.sqrt_sq (by positivity)

section DistanceBounds

variable (H : ℝ)

/-- On segment 1 (right vertical, `re = 1/2`), distance to `I` is at least `1/2`. -/
theorem fdBoundaryFun_seg1_dist_I_lower (t : ℝ) (ht : t ≤ 1/5) :
    (1 : ℝ) / 2 ≤ ‖fdBoundaryFun H t - I‖ := by
  have h1 : (fdBoundaryFun H t - I).re = 1/2 := by
    simp [fdBoundaryFun_seg1_re H t ht]
  simpa [h1, abs_of_pos] using Complex.abs_re_le_norm (fdBoundaryFun H t - I)

/-- On segment 4 (left vertical, `re = -1/2`), distance to `I` is at least `1/2`. -/
theorem fdBoundaryFun_seg4_dist_I_lower (t : ℝ) (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    (1 : ℝ) / 2 ≤ ‖fdBoundaryFun H t - I‖ := by
  have h1 : (fdBoundaryFun H t - I).re = -1/2 := by
    simp [fdBoundaryFun_seg4_re H t ht3 ht4]
  simpa [h1, show |(-1/2 : ℝ)| = 1/2 by norm_num] using
    Complex.abs_re_le_norm (fdBoundaryFun H t - I)

/-- On segment 5 (horizontal at height `H`), distance to `I` is at least `H - 1`. -/
theorem fdBoundaryFun_seg5_dist_I_lower (hH : 1 < H) (t : ℝ) (ht : 4/5 < t) :
    H - 1 ≤ ‖fdBoundaryFun H t - I‖ := by
  have h1 : (fdBoundaryFun H t - I).im = H - 1 := by
    simp [fdBoundaryFun_seg5_im H t ht]
  simpa [h1, abs_of_pos (by linarith : (0 : ℝ) < H - 1)] using
    Complex.abs_im_le_norm (fdBoundaryFun H t - I)

/-- On segment 1 (`re = 1/2`), distance to `rho` (`re = -1/2`) is at least 1. -/
theorem fdBoundaryFun_seg1_dist_rho_lower (t : ℝ) (ht : t ≤ 1/5) :
    (1 : ℝ) ≤ ‖fdBoundaryFun H t - ellipticPointRho‖ := by
  have h1 : (fdBoundaryFun H t - ellipticPointRho).re = 1 := by
    simp [ellipticPointRho, ellipticPointRho', fdBoundaryFun_seg1_re H t ht, sub_re]
    norm_num
  simpa [h1] using Complex.abs_re_le_norm (fdBoundaryFun H t - ellipticPointRho)

/-- On segment 5, distance to `rho` is at least `H - sqrt(3)/2`. -/
theorem fdBoundaryFun_seg5_dist_rho_lower (hH : fdHeightValid H) (t : ℝ) (ht : 4/5 < t) :
    H - Real.sqrt 3 / 2 ≤ ‖fdBoundaryFun H t - ellipticPointRho‖ := by
  have h1 : (fdBoundaryFun H t - ellipticPointRho).im = H - Real.sqrt 3 / 2 := by
    simp [ellipticPointRho, ellipticPointRho', fdBoundaryFun_seg5_im H t ht, sub_im]
  unfold fdHeightValid at hH
  simpa [h1, abs_of_pos (by linarith : (0 : ℝ) < H - Real.sqrt 3 / 2)] using
    Complex.abs_im_le_norm (fdBoundaryFun H t - ellipticPointRho)

/-- On segment 4 (`re = -1/2`), distance to `rho+1` (`re = 1/2`) is at least 1. -/
theorem fdBoundaryFun_seg4_dist_rhoPlusOne_lower (t : ℝ) (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    (1 : ℝ) ≤ ‖fdBoundaryFun H t - ellipticPointRhoPlusOne‖ := by
  have h1 : (fdBoundaryFun H t - ellipticPointRhoPlusOne).re = -1 := by
    simp [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
      fdBoundaryFun_seg4_re H t ht3 ht4, sub_re]
    norm_num
  simpa [h1, show |(-1 : ℝ)| = 1 by norm_num] using
    Complex.abs_re_le_norm (fdBoundaryFun H t - ellipticPointRhoPlusOne)

/-- On segment 5, distance to `rho+1` is at least `H - sqrt(3)/2`. -/
theorem fdBoundaryFun_seg5_dist_rhoPlusOne_lower (hH : fdHeightValid H) (t : ℝ)
    (ht : 4/5 < t) :
    H - Real.sqrt 3 / 2 ≤ ‖fdBoundaryFun H t - ellipticPointRhoPlusOne‖ := by
  have h1 : (fdBoundaryFun H t - ellipticPointRhoPlusOne).im = H - Real.sqrt 3 / 2 := by
    simp [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
      fdBoundaryFun_seg5_im H t ht, sub_im]
  unfold fdHeightValid at hH
  simpa [h1, abs_of_pos (by linarith : (0 : ℝ) < H - Real.sqrt 3 / 2)] using
    Complex.abs_im_le_norm (fdBoundaryFun H t - ellipticPointRhoPlusOne)

end DistanceBounds

/-- Analytic hypotheses for the FTC telescope at a crossing point.

Given a `PiecewiseC1Path` `gamma`, crossing point `z0`, crossing parameter `t0`,
cutoff `delta`, and target limit `L`, this bundles the integrability, FTC equality,
and limit convergence needed by `SingleCrossingData`. -/
structure ArcFTCHyp {x y : ℂ} (γ : PiecewiseC1Path x y) (z₀ : ℂ)
    (t₀ : ℝ) (δ : ℝ → ℝ) (threshold : ℝ) (L : ℂ) where
  /-- FTC expression for the far-segment integrals. -/
  E : ℝ → ℂ
  /-- The far-segment integrals equal `E(epsilon)`. -/
  h_ftc : ∀ ε, 0 < ε → ε < threshold →
    (∫ t in (0 : ℝ)..(t₀ - δ ε),
        (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t) +
    (∫ t in (t₀ + δ ε)..1,
        (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t) = E ε
  /-- Integrability on the left segment. -/
  hint_left : ∀ ε, 0 < ε → ε < threshold →
    IntervalIntegrable
      (fun t => (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t)
      volume 0 (t₀ - δ ε)
  /-- Integrability on the right segment. -/
  hint_right : ∀ ε, 0 < ε → ε < threshold →
    IntervalIntegrable
      (fun t => (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t)
      volume (t₀ + δ ε) 1
  /-- `E(epsilon) -> L` as `epsilon -> 0+`. -/
  h_limit : Tendsto E (𝓝[>] 0) (𝓝 L)

/-- Construct `SingleCrossingData` at `i` from geometric bounds and `ArcFTCHyp`.

The crossing occurs at `t0 = 2/5` in the middle of the arc. -/
def mkSingleCrossingData_atI {H : ℝ} (hH : 1 < H)
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (δ : ℝ → ℝ) (threshold : ℝ) (hthresh : 0 < threshold)
    (hthresh_le : threshold ≤ min (1/2) (H - 1))
    (hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε)
    (hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < 1/5)
    (h_arc_far : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Icc (1/5 : ℝ) (3/5), δ ε < |t - 2/5| → ε < ‖fdBoundaryFun H t - I‖)
    (h_arc_near : ∀ ε, 0 < ε → ε < threshold →
      ∀ t, |t - 2/5| ≤ δ ε → ‖fdBoundaryFun H t - I‖ ≤ ε)
    (ftcHyp : ArcFTCHyp γ I (2/5) δ threshold (-(↑Real.pi * I))) :
    SingleCrossingData γ I where
  L := -(↑Real.pi * I)
  t₀ := 2/5
  ht₀ := by constructor <;> norm_num
  δ := δ
  threshold := threshold
  hthresh := hthresh
  hδ_pos := hδ_pos
  hδ_small := fun ε hε hεt => by
    have hδ := hδ_small ε hε hεt
    simp only [show (1 : ℝ) - 2/5 = 3/5 by norm_num]
    exact lt_min (by linarith) (by linarith)
  h_far := fun ε hε hεt t ht hδt => by
    have hε_half : ε < 1/2 := hεt.trans_le (hthresh_le.trans (min_le_left _ _))
    have hε_Hm1 : ε < H - 1 := hεt.trans_le (hthresh_le.trans (min_le_right _ _))
    change ε < ‖γ.toPath.extend t - I‖
    rw [hγ t ht]
    by_cases ht1 : t ≤ 1/5
    · linarith [fdBoundaryFun_seg1_dist_I_lower H t ht1]
    · push Not at ht1
      by_cases ht2 : t ≤ 3/5
      · exact h_arc_far ε hε hεt t ⟨ht1.le, ht2⟩ hδt
      · push Not at ht2
        by_cases ht3 : t ≤ 4/5
        · linarith [fdBoundaryFun_seg4_dist_I_lower H t ht2 ht3]
        · push Not at ht3
          linarith [fdBoundaryFun_seg5_dist_I_lower H hH t ht3]
  h_near := fun ε hε hεt t hδt => by
    have ht01 : t ∈ Icc (0 : ℝ) 1 := by
      have hδ := hδ_small ε hε hεt
      rw [abs_le] at hδt
      exact ⟨by linarith, by linarith⟩
    change ‖γ.toPath.extend t - I‖ ≤ ε
    rw [hγ t ht01]
    exact h_arc_near ε hε hεt t hδt
  E := ftcHyp.E
  h_ftc := ftcHyp.h_ftc
  hint_left := ftcHyp.hint_left
  hint_right := ftcHyp.hint_right
  h_limit := ftcHyp.h_limit

end
