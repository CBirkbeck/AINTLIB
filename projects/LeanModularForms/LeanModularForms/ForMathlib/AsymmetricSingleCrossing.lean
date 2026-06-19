/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.SingleCrossing

/-!
# Asymmetric single-crossing winding-number framework

Generalisation of `SingleCrossingData` allowing **independent left/right cutoffs**
`δ_left, δ_right : ℝ → ℝ`. This admits crossings where the chord-to-tangent
constants `‖L_-‖` and `‖L_+‖` differ — the symmetric `SingleCrossingData` was
unable to express such crossings (a single δ cannot simultaneously satisfy
`δ ≤ min(δ_R, δ_L)` for the near bound and `δ ≥ max(δ_R, δ_L)` for the far
bound when `δ_R ≠ δ_L`).

## Components

* `AsymmetricSingleCrossingData γ z₀` — bundled data with separate left/right
  cutoffs, near/far bounds, and an FTC-driven limit `E(ε) → L`.
* `AsymmetricSingleCrossingData.hasCauchyPV` — the CPV of `(z - z₀)⁻¹` along
  `γ` exists with limit `L`.
* `AsymmetricSingleCrossingData.hasWindingNumber`,
  `windingNumber_eq` — the `generalizedWindingNumber` equals `L / (2πi)`.
* `SingleCrossingData.toAsymmetric` — every symmetric crossing data lifts to
  an asymmetric one (taking `δ_left = δ_right = δ`). This makes the asymmetric
  framework backwards compatible: existing FD-curve constructors continue to
  work via this wrapper.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology
open scoped Interval

noncomputable section

variable {x y : ℂ}

/-- Data for computing the generalized winding number at a single crossing point,
**with independent left/right cutoffs**. The curve `γ` crosses `z₀` at exactly
one parameter `t₀ ∈ (0, 1)`; the left cutoff `δ_left ε` controls the
parameter-space radius on `[t₀ - δ_left ε, t₀]`, and the right cutoff
`δ_right ε` controls `[t₀, t₀ + δ_right ε]`. -/
structure AsymmetricSingleCrossingData (γ : PiecewiseC1Path x y) (z₀ : ℂ) where
  /-- Target PV limit value. -/
  L : ℂ
  /-- Unique crossing parameter in `(0, 1)`. -/
  t₀ : ℝ
  ht₀ : t₀ ∈ Ioo 0 1
  /-- Left cutoff function. -/
  δ_left : ℝ → ℝ
  /-- Right cutoff function. -/
  δ_right : ℝ → ℝ
  /-- Threshold below which all bounds hold. -/
  threshold : ℝ
  hthresh : 0 < threshold
  hδ_left_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_left ε
  hδ_right_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_right ε
  hδ_left_small : ∀ ε, 0 < ε → ε < threshold → δ_left ε < t₀
  hδ_right_small : ∀ ε, 0 < ε → ε < threshold → δ_right ε < 1 - t₀
  /-- Far bound on the left: outside `[t₀ - δ_left ε, t₀]`, γ is far from z₀. -/
  h_far_left : ∀ ε, 0 < ε → ε < threshold →
    ∀ t ∈ Icc (0 : ℝ) 1, t ≤ t₀ → δ_left ε < t₀ - t → ε < ‖γ.toPath.extend t - z₀‖
  /-- Far bound on the right. -/
  h_far_right : ∀ ε, 0 < ε → ε < threshold →
    ∀ t ∈ Icc (0 : ℝ) 1, t₀ ≤ t → δ_right ε < t - t₀ → ε < ‖γ.toPath.extend t - z₀‖
  /-- Near bound on the left. -/
  h_near_left : ∀ ε, 0 < ε → ε < threshold →
    ∀ t, t ≤ t₀ → t₀ - t ≤ δ_left ε → ‖γ.toPath.extend t - z₀‖ ≤ ε
  /-- Near bound on the right. -/
  h_near_right : ∀ ε, 0 < ε → ε < threshold →
    ∀ t, t₀ ≤ t → t - t₀ ≤ δ_right ε → ‖γ.toPath.extend t - z₀‖ ≤ ε
  /-- FTC expression. -/
  E : ℝ → ℂ
  /-- The far-segment integrals equal `E(ε)`. -/
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
  /-- `E(ε) → L` as `ε → 0⁺`. -/
  h_limit : Tendsto E (𝓝[>] 0) (𝓝 L)

namespace AsymmetricSingleCrossingData

variable {γ : PiecewiseC1Path x y} {z₀ : ℂ}

private theorem cpvIntegrand_zero_on_middle (D : AsymmetricSingleCrossingData γ z₀)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold)
    (h_mid_lt : D.t₀ - D.δ_left ε < D.t₀ + D.δ_right ε) :
    ∀ t ∈ Set.uIoc (D.t₀ - D.δ_left ε) (D.t₀ + D.δ_right ε),
      cpvIntegrand (fun z ↦ (z - z₀)⁻¹) γ.toPath.extend z₀ ε t = 0 := by
  intro t ht
  rw [Set.uIoc_of_le h_mid_lt.le] at ht
  simp only [cpvIntegrand]
  rw [if_neg (not_lt.mpr _)]
  by_cases h_t_le : t ≤ D.t₀
  · refine D.h_near_left ε hε_pos hε_lt t h_t_le ?_
    linarith [ht.1]
  · push Not at h_t_le
    refine D.h_near_right ε hε_pos hε_lt t h_t_le.le ?_
    linarith [ht.2]

private theorem cpvIntegrand_eq_full_left_ae (D : AsymmetricSingleCrossingData γ z₀)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold)
    (h_left_lt : (0 : ℝ) < D.t₀ - D.δ_left ε) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 (D.t₀ - D.δ_left ε) →
      cpvIntegrand (fun z ↦ (z - z₀)⁻¹) γ.toPath.extend z₀ ε t =
        (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t := by
  have h_sing : ({D.t₀ - D.δ_left ε} : Set ℝ)ᶜ ∈ ae volume :=
    compl_mem_ae_iff.mpr ((Set.finite_singleton _).measure_zero volume)
  filter_upwards [h_sing] with t ht_ne ht_mem
  rw [Set.uIoc_of_le h_left_lt.le] at ht_mem
  have ht_lt : t < D.t₀ - D.δ_left ε :=
    lt_of_le_of_ne ht_mem.2 (fun h ↦ ht_ne (Set.mem_singleton_iff.mpr h))
  have hδ_pos := D.hδ_left_pos ε hε_pos hε_lt
  simp only [cpvIntegrand]
  rw [if_pos]
  apply D.h_far_left ε hε_pos hε_lt t
  · exact ⟨ht_mem.1.le, le_of_lt (by linarith [D.ht₀.2])⟩
  · linarith
  · linarith

private theorem cpvIntegrand_eq_full_right_ae (D : AsymmetricSingleCrossingData γ z₀)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold)
    (h_right_lt : D.t₀ + D.δ_right ε < 1) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (D.t₀ + D.δ_right ε) 1 →
      cpvIntegrand (fun z ↦ (z - z₀)⁻¹) γ.toPath.extend z₀ ε t =
        (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t := by
  have h_sing : ({D.t₀ + D.δ_right ε} : Set ℝ)ᶜ ∈ ae volume :=
    compl_mem_ae_iff.mpr ((Set.finite_singleton _).measure_zero volume)
  filter_upwards [h_sing] with t ht_ne ht_mem
  rw [Set.uIoc_of_le h_right_lt.le] at ht_mem
  have hδ_pos := D.hδ_right_pos ε hε_pos hε_lt
  have ht_gt_t₀ : D.t₀ < t := by linarith [ht_mem.1]
  simp only [cpvIntegrand]
  rw [if_pos]
  apply D.h_far_right ε hε_pos hε_lt t
  · exact ⟨by linarith [D.ht₀.1], ht_mem.2⟩
  · linarith
  · linarith [ht_mem.1]

private theorem cutoff_integral_eq_E (D : AsymmetricSingleCrossingData γ z₀)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold) :
    ∫ t in (0 : ℝ)..1, cpvIntegrand (fun z ↦ (z - z₀)⁻¹) γ.toPath.extend z₀ ε t =
      D.E ε := by
  have hδL_pos := D.hδ_left_pos ε hε_pos hε_lt
  have hδR_pos := D.hδ_right_pos ε hε_pos hε_lt
  have hδL_small := D.hδ_left_small ε hε_pos hε_lt
  have hδR_small := D.hδ_right_small ε hε_pos hε_lt
  have h_left_lt : (0 : ℝ) < D.t₀ - D.δ_left ε := by linarith
  have h_mid_lt : D.t₀ - D.δ_left ε < D.t₀ + D.δ_right ε := by linarith
  have h_right_lt : D.t₀ + D.δ_right ε < 1 := by linarith
  set F := fun t ↦ cpvIntegrand (fun z ↦ (z - z₀)⁻¹) γ.toPath.extend z₀ ε t
  have hF_mid := D.cpvIntegrand_zero_on_middle hε_pos hε_lt h_mid_lt
  have hF_left := D.cpvIntegrand_eq_full_left_ae hε_pos hε_lt h_left_lt
  have hF_right := D.cpvIntegrand_eq_full_right_ae hε_pos hε_lt h_right_lt
  have hF_int_left : IntervalIntegrable F volume 0 (D.t₀ - D.δ_left ε) :=
    (D.hint_left ε hε_pos hε_lt).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).mpr
        (hF_left.mono (fun t ht hm ↦ (ht hm).symm)))
  have hF_int_mid : IntervalIntegrable F volume (D.t₀ - D.δ_left ε)
      (D.t₀ + D.δ_right ε) :=
    (IntervalIntegrable.zero (μ := volume)
      (a := D.t₀ - D.δ_left ε) (b := D.t₀ + D.δ_right ε)).congr
      (fun t ht ↦ (hF_mid t ht).symm)
  have hF_int_right : IntervalIntegrable F volume (D.t₀ + D.δ_right ε) 1 :=
    (D.hint_right ε hε_pos hε_lt).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).mpr
        (hF_right.mono (fun t ht hm ↦ (ht hm).symm)))
  rw [show ∫ t in (0 : ℝ)..1, F t =
      (∫ t in (0 : ℝ)..(D.t₀ - D.δ_left ε), F t) +
      (∫ t in (D.t₀ - D.δ_left ε)..(D.t₀ + D.δ_right ε), F t) +
      (∫ t in (D.t₀ + D.δ_right ε)..1, F t) by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hF_int_left.trans hF_int_mid) hF_int_right,
        ← intervalIntegral.integral_add_adjacent_intervals hF_int_left hF_int_mid],
    intervalIntegral.integral_zero_ae (ae_of_all _ hF_mid),
    intervalIntegral.integral_congr_ae hF_left,
    intervalIntegral.integral_congr_ae hF_right, add_zero]
  exact D.h_ftc ε hε_pos hε_lt

/-- The CPV of `(z - z₀)⁻¹` along `γ` exists and equals `D.L`. -/
theorem hasCauchyPV (D : AsymmetricSingleCrossingData γ z₀) :
    HasCauchyPV (fun z ↦ (z - z₀)⁻¹) γ z₀ D.L := by
  simp only [HasCauchyPV]
  have h_ev : (fun ε ↦ ∫ t in (0 : ℝ)..1,
      cpvIntegrand (fun z ↦ (z - z₀)⁻¹) γ.toPath.extend z₀ ε t)
      =ᶠ[𝓝[>] 0] D.E := by
    filter_upwards [Ioo_mem_nhdsGT D.hthresh] with ε hε
    exact D.cutoff_integral_eq_E hε.1 hε.2
  exact D.h_limit.congr' h_ev.symm

/-- The generalized winding number at `z₀` equals `L / (2πi)`. -/
theorem hasWindingNumber (D : AsymmetricSingleCrossingData γ z₀) :
    HasGeneralizedWindingNumber γ z₀ (D.L / (2 * ↑Real.pi * I)) := by
  rw [show D.L / (2 * ↑Real.pi * I) = (2 * ↑Real.pi * I)⁻¹ * D.L by ring]
  exact hasGeneralizedWindingNumber_of_hasCauchyPV D.hasCauchyPV
end AsymmetricSingleCrossingData

end
