/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.ClassicalCPV
import Mathlib

/-!
# PV Integral Splitting at Crossings

For a curve γ with a unique crossing of point s at parameter t₀, the PV cutoff
integral splits into left and right pieces — the near-crossing part vanishes.

The key observation: when ‖γ(t) - s‖ ≤ ε (i.e., t is near the crossing), the
cutoff integrand `if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0` is 0.
On the far segments, the cutoff condition is satisfied so the integrand equals
`(γ t - s)⁻¹ * deriv γ t` a.e.

## Main results

* `pv_split_at_crossing` — the PV cutoff integral equals the sum of left and
  right integrals of `(γ t - s)⁻¹ * deriv γ t`, where the middle part is zero.
-/

open Set MeasureTheory Complex Filter intervalIntegral

namespace ContourIntegral

/-- The PV cutoff integral splits at a crossing.

For ε, δ > 0 with δ < min(t₀ - a, b - t₀), if:
- the curve is far from s (norm > ε) outside the δ-window, and
- near to s (norm ≤ ε) inside the δ-window,

then the full cutoff integral equals the sum of the left and right integrals of
`(γ t - s)⁻¹ * deriv γ t`. The middle piece vanishes because the cutoff sets the
integrand to 0 whenever ‖γ t - s‖ ≤ ε. -/
theorem pv_split_at_crossing {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} {ε δ t₀ : ℝ}
    (_hab : a < b) (ht₀ : t₀ ∈ Ioo a b) (_hε : 0 < ε) (hδ : 0 < δ)
    (hδ_small : δ < min (t₀ - a) (b - t₀))
    (h_far : ∀ t ∈ Icc a b, δ < |t - t₀| → ε < ‖γ t - s‖)
    (h_near : ∀ t, |t - t₀| ≤ δ → ‖γ t - s‖ ≤ ε)
    (hint_left : IntervalIntegrable (fun t ↦ (γ t - s)⁻¹ * deriv γ t) volume a (t₀ - δ))
    (hint_right : IntervalIntegrable (fun t ↦ (γ t - s)⁻¹ * deriv γ t)
      volume (t₀ + δ) b) :
    (∫ t in a..b, if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0) =
      (∫ t in a..(t₀ - δ), (γ t - s)⁻¹ * deriv γ t) +
        (∫ t in (t₀ + δ)..b, (γ t - s)⁻¹ * deriv γ t) := by
  set F := fun t ↦ if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else (0 : ℂ)
  obtain ⟨ha_lt, hlt_b⟩ := ht₀
  have h_left_lt : a < t₀ - δ := by
    have := lt_of_lt_of_le hδ_small (min_le_left (t₀ - a) (b - t₀)); linarith
  have h_right_lt : t₀ + δ < b := by
    have := lt_of_lt_of_le hδ_small (min_le_right (t₀ - a) (b - t₀)); linarith
  have hF_mid : ∀ t ∈ uIoc (t₀ - δ) (t₀ + δ), F t = 0 := fun t ht ↦ by
    rw [uIoc_of_le (by linarith)] at ht
    exact if_neg (not_lt.mpr <| h_near _ <|
      abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have h_ne : ∀ x : ℝ, ({x} : Set ℝ)ᶜ ∈ ae volume := fun _ ↦
    compl_mem_ae_iff.mpr ((Set.finite_singleton _).measure_zero volume)
  have hF_left : ∀ᵐ t ∂volume, t ∈ uIoc a (t₀ - δ) →
      F t = (γ t - s)⁻¹ * deriv γ t := by
    filter_upwards [h_ne (t₀ - δ)] with t ht_ne ht
    rw [uIoc_of_le h_left_lt.le] at ht
    have ht_lt : t < t₀ - δ :=
      lt_of_le_of_ne ht.2 (fun h ↦ ht_ne (Set.mem_singleton_iff.mpr h))
    refine if_pos (h_far t ⟨ht.1.le, ht.2.trans (by linarith)⟩ ?_)
    rw [abs_of_nonpos (by linarith)]; linarith
  have hF_right : ∀ᵐ t ∂volume, t ∈ uIoc (t₀ + δ) b →
      F t = (γ t - s)⁻¹ * deriv γ t := by
    filter_upwards [h_ne (t₀ + δ)] with t _ ht
    rw [uIoc_of_le h_right_lt.le] at ht
    refine if_pos (h_far t ⟨by linarith [ht.1], ht.2⟩ ?_)
    rw [abs_of_nonneg (by linarith [ht.1])]
    linarith [ht.1]
  have hF_int_left : IntervalIntegrable F volume a (t₀ - δ) :=
    hint_left.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_left.mono (fun _ ht hm ↦ (ht hm).symm)))
  have hF_int_mid : IntervalIntegrable F volume (t₀ - δ) (t₀ + δ) :=
    (IntervalIntegrable.zero (μ := volume) (a := t₀ - δ) (b := t₀ + δ)).congr
      (fun t ht ↦ (hF_mid t ht).symm)
  have hF_int_right : IntervalIntegrable F volume (t₀ + δ) b :=
    hint_right.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_right.mono (fun _ ht hm ↦ (ht hm).symm)))
  rw [← integral_add_adjacent_intervals (hF_int_left.trans hF_int_mid) hF_int_right,
    ← integral_add_adjacent_intervals hF_int_left hF_int_mid,
    integral_zero_ae (ae_of_all _ hF_mid),
    integral_congr_ae hF_left, integral_congr_ae hF_right, add_zero]

end ContourIntegral
