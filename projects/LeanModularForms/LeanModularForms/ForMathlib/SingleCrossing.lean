/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.GeneralizedWindingNumber

/-!
# Single-Crossing Winding Number Framework

Unified framework for computing `generalizedWindingNumber γ z₀` when the
piecewise C1 curve `γ` crosses the point `z₀` at exactly one parameter value `t₀ ∈ (0, 1)`.

## Overview

The three edge/arc winding proofs (RightEdge, LeftEdge, UnitArc) share a
common 5-step structure:

1. Identify the unique crossing parameter `t₀`
2. Define a cutoff function `δ(ε)` that maps the norm threshold `ε` to a
   parameter-space interval radius around `t₀`
3. Prove far/near bounds: curve is ε-far from `z₀` outside `[t₀-δ, t₀+δ]`,
   and ε-close inside
4. Prove the FTC telescope: the far-segment integrals sum to some `E(ε)`
5. Prove `E(ε) → L` as `ε → 0⁺`, giving `gWN = L / (2πi)`

This file provides:
- `SingleCrossingData`: a structure bundling all geometric ingredients
- `SingleCrossingData.hasCauchyPV`: the CPV integral has limit `L`
- `SingleCrossingData.hasWindingNumber`: the generalized winding number is `L / (2πi)`
- `SingleCrossingData.windingNumber_neg_half`: specialized for `L = -πi` giving `-1/2`
- `SingleCrossingData.windingNumber_neg_sixth`: specialized for `L = -πi/3` giving `-1/6`

## Design

The key abstraction is that the PV integral splits into three pieces:
on `[0, t₀-δ]` and `[t₀+δ, 1]` the cutoff integrand equals the full integrand
(by the far bound), while on `[t₀-δ, t₀+δ]` it vanishes (by the near bound).
The sum of the two outer pieces equals `E(ε)`, which tends to `L`.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology
open scoped Interval

noncomputable section

variable {x y : ℂ}

/-- Data for computing the generalized winding number at a single crossing point.
The curve `γ` crosses `z₀` at exactly one parameter value `t₀ ∈ (0, 1)`. -/
structure SingleCrossingData (γ : PiecewiseC1Path x y) (z₀ : ℂ) where
  /-- Target PV limit value. -/
  L : ℂ
  /-- Unique crossing parameter in `(0, 1)`. -/
  t₀ : ℝ
  ht₀ : t₀ ∈ Ioo 0 1
  /-- Cutoff function: norm threshold `ε` maps to parameter radius. -/
  δ : ℝ → ℝ
  /-- Threshold below which all bounds hold. -/
  threshold : ℝ
  hthresh : 0 < threshold
  /-- `δ(ε)` is positive for valid `ε`. -/
  hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε
  /-- `δ(ε)` is small enough: stays within `(0, 1)` around `t₀`. -/
  hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min t₀ (1 - t₀)
  /-- Far bound: curve is ε-far from `z₀` outside the δ-window. -/
  h_far : ∀ ε, 0 < ε → ε < threshold →
    ∀ t ∈ Icc 0 1, δ ε < |t - t₀| → ε < ‖γ t - z₀‖
  /-- Near bound: curve is ε-close inside the δ-window. -/
  h_near : ∀ ε, 0 < ε → ε < threshold →
    ∀ t, |t - t₀| ≤ δ ε → ‖γ t - z₀‖ ≤ ε
  /-- FTC expression for the far-segment integrals. -/
  E : ℝ → ℂ
  /-- The far-segment integrals equal `E(ε)`. -/
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
  /-- `E(ε) → L` as `ε → 0⁺`. -/
  h_limit : Tendsto E (𝓝[>] 0) (𝓝 L)

namespace SingleCrossingData

variable {γ : PiecewiseC1Path x y} {z₀ : ℂ}

private theorem cpvIntegrand_zero_on_middle (D : SingleCrossingData γ z₀)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold)
    (h_mid_lt : D.t₀ - D.δ ε < D.t₀ + D.δ ε) :
    ∀ t ∈ Set.uIoc (D.t₀ - D.δ ε) (D.t₀ + D.δ ε),
      cpvIntegrand (fun z => (z - z₀)⁻¹) γ.toPath.extend z₀ ε t = 0 := by
  intro t ht
  rw [Set.uIoc_of_le h_mid_lt.le] at ht
  simp only [cpvIntegrand]
  rw [if_neg (not_lt.mpr _)]
  exact D.h_near ε hε_pos hε_lt t
    (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)

private theorem cpvIntegrand_eq_full_left_ae (D : SingleCrossingData γ z₀)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold)
    (h_left_lt : (0 : ℝ) < D.t₀ - D.δ ε) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 (D.t₀ - D.δ ε) →
      cpvIntegrand (fun z => (z - z₀)⁻¹) γ.toPath.extend z₀ ε t =
        (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t := by
  have h_sing : ({D.t₀ - D.δ ε} : Set ℝ)ᶜ ∈ ae volume :=
    compl_mem_ae_iff.mpr ((Set.finite_singleton _).measure_zero volume)
  filter_upwards [h_sing] with t ht_ne ht_mem
  rw [Set.uIoc_of_le h_left_lt.le] at ht_mem
  have ht_lt : t < D.t₀ - D.δ ε :=
    ht_mem.2.lt_of_ne (fun h => ht_ne (Set.mem_singleton_iff.mpr h))
  have hδ_pos := D.hδ_pos ε hε_pos hε_lt
  simp only [cpvIntegrand]
  rw [if_pos]
  apply D.h_far ε hε_pos hε_lt t
  · exact ⟨ht_mem.1.le, by linarith [D.ht₀.2]⟩
  · rw [abs_of_nonpos (by linarith)]; linarith

private theorem cpvIntegrand_eq_full_right_ae (D : SingleCrossingData γ z₀)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold)
    (h_right_lt : D.t₀ + D.δ ε < 1) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc (D.t₀ + D.δ ε) 1 →
      cpvIntegrand (fun z => (z - z₀)⁻¹) γ.toPath.extend z₀ ε t =
        (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t := by
  have h_sing : ({D.t₀ + D.δ ε} : Set ℝ)ᶜ ∈ ae volume :=
    compl_mem_ae_iff.mpr ((Set.finite_singleton _).measure_zero volume)
  filter_upwards [h_sing] with t ht_ne ht_mem
  rw [Set.uIoc_of_le h_right_lt.le] at ht_mem
  have hδ_pos := D.hδ_pos ε hε_pos hε_lt
  simp only [cpvIntegrand]
  rw [if_pos]
  apply D.h_far ε hε_pos hε_lt t
  · exact ⟨by linarith [D.ht₀.1, ht_mem.1], ht_mem.2⟩
  · rw [abs_of_pos (by linarith [ht_mem.1])]; linarith [ht_mem.1]

private theorem cutoff_integral_eq_E (D : SingleCrossingData γ z₀)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold) :
    ∫ t in (0 : ℝ)..1, cpvIntegrand (fun z => (z - z₀)⁻¹) γ.toPath.extend z₀ ε t =
      D.E ε := by
  have hδ_pos := D.hδ_pos ε hε_pos hε_lt
  have hδ_small := D.hδ_small ε hε_pos hε_lt
  have h_left_lt : (0 : ℝ) < D.t₀ - D.δ ε := by
    linarith [hδ_small.trans_le (min_le_left _ _)]
  have h_mid_lt : D.t₀ - D.δ ε < D.t₀ + D.δ ε := by linarith
  have h_right_lt : D.t₀ + D.δ ε < 1 := by
    linarith [hδ_small.trans_le (min_le_right _ _)]
  set F := fun t => cpvIntegrand (fun z => (z - z₀)⁻¹) γ.toPath.extend z₀ ε t
  have hF_mid := D.cpvIntegrand_zero_on_middle hε_pos hε_lt h_mid_lt
  have hF_left := D.cpvIntegrand_eq_full_left_ae hε_pos hε_lt h_left_lt
  have hF_right := D.cpvIntegrand_eq_full_right_ae hε_pos hε_lt h_right_lt
  have hF_int_left : IntervalIntegrable F volume 0 (D.t₀ - D.δ ε) :=
    (D.hint_left ε hε_pos hε_lt).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).mpr
        (hF_left.mono (fun _ ht hm => (ht hm).symm)))
  have hF_int_mid : IntervalIntegrable F volume (D.t₀ - D.δ ε) (D.t₀ + D.δ ε) :=
    (IntervalIntegrable.zero (μ := volume)
      (a := D.t₀ - D.δ ε) (b := D.t₀ + D.δ ε)).congr (fun t ht => (hF_mid t ht).symm)
  have hF_int_right : IntervalIntegrable F volume (D.t₀ + D.δ ε) 1 :=
    (D.hint_right ε hε_pos hε_lt).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).mpr
        (hF_right.mono (fun _ ht hm => (ht hm).symm)))
  rw [show ∫ t in (0 : ℝ)..1, F t =
      (∫ t in (0 : ℝ)..(D.t₀ - D.δ ε), F t) +
      (∫ t in (D.t₀ - D.δ ε)..(D.t₀ + D.δ ε), F t) +
      (∫ t in (D.t₀ + D.δ ε)..1, F t) by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hF_int_left.trans hF_int_mid) hF_int_right,
        ← intervalIntegral.integral_add_adjacent_intervals hF_int_left hF_int_mid],
    intervalIntegral.integral_zero_ae (ae_of_all _ hF_mid),
    intervalIntegral.integral_congr_ae hF_left,
    intervalIntegral.integral_congr_ae hF_right, add_zero]
  exact D.h_ftc ε hε_pos hε_lt

/-- The CPV of `(z - z₀)⁻¹` along `γ` exists and equals `D.L`.

The proof splits the cutoff integral into three pieces at `t₀ ± δ(ε)`:
- On `[0, t₀-δ]` and `[t₀+δ, 1]`: the cutoff is inactive (by `h_far`),
  so the integrand matches the full function.
- On `[t₀-δ, t₀+δ]`: the cutoff zeroes the integrand (by `h_near`).
The sum of the two outer pieces equals `E(ε)` (by `h_ftc`), which tends to `L`. -/
theorem hasCauchyPV (D : SingleCrossingData γ z₀) :
    HasCauchyPV (fun z => (z - z₀)⁻¹) γ z₀ D.L := by
  refine D.h_limit.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT D.hthresh] with ε hε
  exact (D.cutoff_integral_eq_E hε.1 hε.2).symm

/-- The generalized winding number at `z₀` equals `L / (2πi)`. -/
theorem hasWindingNumber (D : SingleCrossingData γ z₀) :
    HasGeneralizedWindingNumber γ z₀ (D.L / (2 * ↑Real.pi * I)) := by
  rw [div_eq_inv_mul]
  exact hasGeneralizedWindingNumber_of_hasCauchyPV D.hasCauchyPV

end SingleCrossingData

end
