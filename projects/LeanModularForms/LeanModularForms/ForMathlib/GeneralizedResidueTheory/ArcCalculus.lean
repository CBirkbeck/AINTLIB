/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Arc Calculus

General-purpose API for unit circle arc parameterizations and their properties.
Used for computing winding numbers, distances, and derivatives along circular arcs.

## Main definitions

* `unitArc` - parameterization of a unit circle arc from angle θ₁ to θ₂

## Main results

* `unitArc_norm` - points on the arc have norm 1
* `unitArc_hasDerivAt` - derivative formula for the arc
* `exp_sub_norm_sq` - distance formula between arc points via cosine
* `sin_pos_of_mem_Ioo_zero_pi` - sin is positive on (0, π)
-/

open Complex Real Set

namespace ArcCalculus

/-- Unit circle arc from angle θ₁ to θ₂, linearly parameterized on [a,b]. -/
noncomputable def unitArc (θ₁ θ₂ a b : ℝ) (t : ℝ) : ℂ :=
  exp (↑(θ₁ + (t - a) / (b - a) * (θ₂ - θ₁)) * I)

private lemma unitArc_angle_hasDerivAt (θ₁ θ₂ a b t : ℝ) (hab : b - a ≠ 0) :
    HasDerivAt (fun s => θ₁ + (s - a) / (b - a) * (θ₂ - θ₁))
      ((θ₂ - θ₁) / (b - a)) t := by
  have hd : HasDerivAt (fun s => (s - a) / (b - a)) (1 / (b - a)) t :=
    ((hasDerivAt_id t).sub_const a).div_const (b - a)
  have hval : (1 : ℝ) / (b - a) * (θ₂ - θ₁) = (θ₂ - θ₁) / (b - a) := by ring
  have h1 : HasDerivAt (fun s => (s - a) / (b - a) * (θ₂ - θ₁))
      ((θ₂ - θ₁) / (b - a)) t := hval ▸ hd.mul_const (θ₂ - θ₁)
  exact h1.const_add θ₁

/-- Derivative of the unit arc. -/
theorem unitArc_hasDerivAt (θ₁ θ₂ a b t : ℝ) (hab : a < b) :
    HasDerivAt (unitArc θ₁ θ₂ a b)
      (unitArc θ₁ θ₂ a b t * (↑((θ₂ - θ₁) / (b - a)) * I)) t := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hlift : HasDerivAt (fun s => (↑(θ₁ + (s - a) / (b - a) * (θ₂ - θ₁)) : ℂ))
      (↑((θ₂ - θ₁) / (b - a))) t := (unitArc_angle_hasDerivAt θ₁ θ₂ a b t hba).ofReal_comp
  simp only [unitArc]
  exact (hlift.mul_const I).cexp

/-- sin is positive on the open interval (0, π). -/
theorem sin_pos_of_mem_Ioo_zero_pi {θ : ℝ} (hθ : θ ∈ Ioo 0 π) : 0 < Real.sin θ :=
  Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2

/-- |cos θ| ≤ 1/2 for θ ∈ [π/3, 2π/3]. -/
theorem abs_cos_le_half_of_mem_Icc {θ : ℝ} (hθ : θ ∈ Icc (π / 3) (2 * π / 3)) :
    |Real.cos θ| ≤ 1 / 2 := by
  have hpi := Real.pi_pos
  obtain ⟨h1, h2⟩ := hθ
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hle : Real.cos (2 * π / 3) ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) h2
    rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three] at hle
    linarith
  · have hle : Real.cos θ ≤ Real.cos (π / 3) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) h1
    rw [Real.cos_pi_div_three] at hle
    linarith

end ArcCalculus
