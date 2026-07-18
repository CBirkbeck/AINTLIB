/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.CauchyPrincipalValue

/-!
# Generalized Winding Number

This file defines the generalized winding number of a piecewise C¹ path around a point,
following the approach of Hungerbühler–Wasem. The definition uses the Cauchy principal value
integral, which allows the winding number to be defined even when the curve passes through
the point `z₀`.

## Main definitions

* `HasGeneralizedWindingNumber γ z₀ w` — the Tendsto-first predicate asserting that the CPV
  of `∮_γ (z - z₀)⁻¹ dz` exists and equals `2πi · w`.

* `generalizedWindingNumber γ z₀` — the generalized winding number, defined as
  `(2πi)⁻¹ · cauchyPV (fun z ↦ (z - z₀)⁻¹) γ z₀`. Returns junk when the CPV does not exist.

## Main results

* `HasGeneralizedWindingNumber.eq` — bridge: the predicate implies
  `generalizedWindingNumber γ z₀ = w`.

* `hasGeneralizedWindingNumber_of_avoids` — if `γ` avoids `z₀` (with positive minimum
  distance), the generalized winding number equals the classical contour integral formula.

* `generalizedWindingNumber_continuousAt_of_avoids` — the generalized winding number is
  continuous at any point off a Lipschitz piecewise C¹ curve.

## Design notes

The `HasGeneralizedWindingNumber` predicate wraps `HasCauchyPV` with the specific integrand
`(z - z₀)⁻¹`. This Tendsto-first design matches the pattern from `CauchyPrincipalValue.lean`:
downstream theorems state results using `HasGeneralizedWindingNumber`, and extract the value
via the bridge theorem when needed.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set Filter Topology MeasureTheory Complex
open scoped Interval

noncomputable section

variable {x y : ℂ}

/-- The generalized winding number of `γ` around `z₀` exists and equals `w`.

Defined as: the CPV of `∮_γ (z - z₀)⁻¹ dz` exists and equals `2πi · w`.
This is the **primary API predicate** for generalized winding numbers. -/
def HasGeneralizedWindingNumber (γ : PiecewiseC1Path x y) (z₀ : ℂ) (w : ℂ) : Prop :=
  HasCauchyPV (fun z ↦ (z - z₀)⁻¹) γ z₀ (2 * ↑Real.pi * I * w)

/-- The generalized winding number of `γ` around `z₀`, defined as
`(2πi)⁻¹ · PV ∮_γ (z - z₀)⁻¹ dz`. Returns junk when the CPV does not exist. -/
def generalizedWindingNumber (γ : PiecewiseC1Path x y) (z₀ : ℂ) : ℂ :=
  (2 * ↑Real.pi * I)⁻¹ * cauchyPV (fun z ↦ (z - z₀)⁻¹) γ z₀

/-- Bridge: if `HasGeneralizedWindingNumber γ z₀ w`, then `generalizedWindingNumber γ z₀ = w`. -/
theorem HasGeneralizedWindingNumber.eq {γ : PiecewiseC1Path x y} {z₀ w : ℂ}
    (h : HasGeneralizedWindingNumber γ z₀ w) : generalizedWindingNumber γ z₀ = w := by
  rw [generalizedWindingNumber, h.cauchyPV_eq, ← mul_assoc,
    inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]

/-- If `γ` avoids `z₀` (with positive minimum distance), the generalized winding number
equals the classical contour integral formula. -/
theorem hasGeneralizedWindingNumber_of_avoids {γ : PiecewiseC1Path x y} {z₀ : ℂ}
    (hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - z₀‖) :
    HasGeneralizedWindingNumber γ z₀
      ((2 * ↑Real.pi * I)⁻¹ * γ.contourIntegral (fun z ↦ (z - z₀)⁻¹)) := by
  rw [HasGeneralizedWindingNumber, mul_inv_cancel_left₀ Complex.two_pi_I_ne_zero]
  exact hasCauchyPV_of_avoids hδ

/-- If the CPV exists with some limit, then `HasGeneralizedWindingNumber` holds for the
corresponding winding number value. -/
theorem hasGeneralizedWindingNumber_of_hasCauchyPV {γ : PiecewiseC1Path x y} {z₀ L : ℂ}
    (h : HasCauchyPV (fun z ↦ (z - z₀)⁻¹) γ z₀ L) :
    HasGeneralizedWindingNumber γ z₀ ((2 * ↑Real.pi * I)⁻¹ * L) := by
  rw [HasGeneralizedWindingNumber, mul_inv_cancel_left₀ Complex.two_pi_I_ne_zero]
  exact h

/-- Helper: distance lower bound for points in a small ball around `w₀` (off the curve). -/
lemma ball_dist_to_curve_lb {γ : PiecewiseC1Path x y} {w₀ : ℂ}
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w₀) :
    ∃ ε > 0, ∀ w ∈ Metric.ball w₀ ε, ∀ t ∈ Icc (0 : ℝ) 1, ε ≤ ‖γ t - w‖ := by
  have h_compact : IsCompact (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image γ.toPath.continuous_extend
  have hδ_pos : 0 < Metric.infDist w₀ (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
    (h_compact.isClosed.notMem_iff_infDist_pos
        ⟨γ.toPath.extend 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩).mp
      fun ⟨t, ht, heq⟩ ↦ hoff t ht heq
  refine ⟨Metric.infDist w₀ (γ.toPath.extend '' Icc (0 : ℝ) 1) / 2, by linarith, ?_⟩
  intro w hw t ht
  have h1 : Metric.infDist w₀ (γ.toPath.extend '' Icc (0 : ℝ) 1) ≤ ‖γ t - w₀‖ := by
    rw [norm_sub_rev, ← Complex.dist_eq]
    exact Metric.infDist_le_dist_of_mem (mem_image_of_mem _ ht)
  have h2 : ‖w - w₀‖ < Metric.infDist w₀ (γ.toPath.extend '' Icc (0 : ℝ) 1) / 2 := by
    rw [← Complex.dist_eq]; exact Metric.mem_ball.mp hw
  have h3 : ‖γ t - w₀‖ ≤ ‖γ t - w‖ + ‖w - w₀‖ := by
    rw [show γ t - w₀ = (γ t - w) + (w - w₀) by ring]
    exact norm_add_le _ _
  linarith

/-- The generalized winding number is continuous at any point off a Lipschitz
piecewise C¹ curve. Uses parametric continuity of the contour integral
(`intervalIntegral.continuousAt_of_dominated_interval`) with the bound
`‖(γt - w)⁻¹ * γ'(t)‖ ≤ ε⁻¹ · K` for `w` in a ball around `w₀`. -/
theorem generalizedWindingNumber_continuousAt_of_avoids
    {γ : PiecewiseC1Path x y} {w₀ : ℂ}
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w₀)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    ContinuousAt (generalizedWindingNumber γ) w₀ := by
  obtain ⟨ε, hε_pos, h_dist_lb⟩ := ball_dist_to_curve_lb hoff
  set F : ℂ → ℝ → ℂ := fun w t ↦ (γ t - w)⁻¹ * deriv γ.toPath.extend t
  have h_integrand_meas : ∀ w ∈ Metric.ball w₀ ε,
      AEStronglyMeasurable (F w) (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    intro w hw
    rw [Set.uIoc_of_le (zero_le_one' ℝ)]
    have h_avoid : ∀ t ∈ Icc (0 : ℝ) 1, γ t - w ≠ 0 := fun t ht h ↦ by
      have := h_dist_lb w hw t ht
      rw [h, norm_zero] at this; linarith
    have h_cont_inv : ContinuousOn (fun t ↦ (γ t - w)⁻¹) (Icc (0 : ℝ) 1) :=
      (γ.toPath.continuous_extend.continuousOn.sub continuousOn_const).inv₀ h_avoid
    exact ((h_cont_inv.mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc).mul (stronglyMeasurable_deriv _).aestronglyMeasurable
  have h_eq_nbhd : (fun w ↦ generalizedWindingNumber γ w) =ᶠ[nhds w₀]
      fun w ↦ (2 * ↑Real.pi * I)⁻¹ * ∫ t in (0 : ℝ)..1, F w t := by
    filter_upwards [Metric.ball_mem_nhds w₀ hε_pos] with w hw
    have hγ_avoids : ∃ δ' > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ' ≤ ‖γ t - w‖ :=
      ⟨ε, hε_pos, h_dist_lb w hw⟩
    rw [(hasGeneralizedWindingNumber_of_avoids hγ_avoids).eq]
    simp only [PiecewiseC1Path.contourIntegral, F]
  refine (ContinuousAt.congr ?_ h_eq_nbhd.symm)
  refine ContinuousAt.mul continuousAt_const ?_
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ ↦ ε⁻¹ * K) ?_ ?_
    (intervalIntegrable_const (c := ε⁻¹ * K)) ?_
  · filter_upwards [Metric.ball_mem_nhds w₀ hε_pos] with w hw using h_integrand_meas w hw
  · filter_upwards [Metric.ball_mem_nhds w₀ hε_pos] with w hw
    filter_upwards with t ht
    rw [Set.uIoc_of_le (zero_le_one' ℝ)] at ht
    have ht_Icc : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    simp only [F, norm_mul, norm_inv]
    exact mul_le_mul
      (inv_anti₀ hε_pos (h_dist_lb w hw t ht_Icc))
      (norm_deriv_le_of_lipschitz hLip) (norm_nonneg _)
      (inv_nonneg.mpr hε_pos.le)
  · filter_upwards with t ht
    rw [Set.uIoc_of_le (zero_le_one' ℝ)] at ht
    have ht_Icc : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    have h_avoid : γ t - w₀ ≠ 0 := fun h ↦ by
      have := h_dist_lb w₀ (Metric.mem_ball_self hε_pos) t ht_Icc
      rw [h, norm_zero] at this; linarith
    exact ((continuous_const.sub continuous_id).continuousAt.inv₀ h_avoid).mul
      continuousAt_const

end
