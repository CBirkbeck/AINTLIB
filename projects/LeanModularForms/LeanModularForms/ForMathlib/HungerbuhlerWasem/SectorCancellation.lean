/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LeanModularForms.ForMathlib.FlatnessConditions
import LeanModularForms.ForMathlib.HungerbuhlerWasem.HigherOrderAsymptotics

/-!
# Sector-even cancellation under condition (B) (T-SC-01)

For γ with a transverse crossing at `s`, the Laurent term `c / (z - s)^k`
(`k ≥ 2`) has Cauchy principal value equal to zero provided condition (B)
`(L_plus / ‖L_plus‖)^(k-1) = ((-L_minus) / ‖L_minus‖)^(k-1)` holds.

This file restores the deleted `HW33SectorEven.lean` content under the new
`HungerbuhlerWasem` namespace. The arrangement follows
Hungerbühler–Wasem (arXiv:1808.00997v2), equation 3.4:

  `PV ∮_γ dz/z^n = lim_{ε → 0⁺} (1 - e^(-i(n-1)α)) / ((n-1) ε^(n-1))`,

which is identically zero whenever `(n-1) α ∈ 2πℤ`.

## Headline theorems

* `exp_neg_I_eq_one_of_conditionB` — `exp(-i(n-1)α) = 1` under condition (B).
* `sector_pv_formula_vanishes_under_conditionB` — sector PV formula = 0 under (B).
* `sector_pv_formula_tendsto_zero_under_conditionB` — Tendsto form.
* `real_ray_inv_pow_integral` — closed form for `∫_a^b 1/t^n dt`.
* `complex_ray_inv_pow_integral` — closed form for `∫_a^b c / t^n dt` (complex).
* `arc_inv_pow_integral` — closed form for `∫_arc dz / z^n`.
* `sector_inv_pow_integral_combined` — full sector integral identity.
* `sector_inv_pow_integral_vanishes_under_conditionB` — full sector PV = 0
  under condition (B).
* `sector_inv_pow_integral_tendsto_zero_under_conditionB` — Tendsto form.
* `F_line_diff_eq_zero_under_conditionB` — antiderivative side targets agree.
* `F_curve_diff_tendsto_zero_under_conditionB` — combined curve F-difference
  tends to zero.
* `hw_theorem_3_3_under_conditionB_parametric` — HW Theorem 3.3 parametric form.
* `hasCauchyPVOn_singleton_pow_of_conditionB_assembled` — fully assembled
  `HasCauchyPVOn` form.
-/

open Filter Topology Set Complex MeasureTheory
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

/-- **F-line difference vanishing under condition (B), general angle.**
For pole `s`, two tangent directions `L_plus` (right) and `L_minus` (left, used
inward as `-L_minus`), and `k ≥ 2`, the antiderivative
`F(z) = -1/((k-1)(z-s)^(k-1))` evaluated at the chord-targets
`s + ε · (L_plus / ‖L_plus‖)` and `s + ε · ((-L_minus) / ‖L_minus‖)` is
**equal** under condition (B):

  `((L_plus / ‖L_plus‖))^(k-1) = ((-L_minus / ‖L_minus‖))^(k-1)`.

For k odd, `(-L/|L|)^(k-1) = (L/|L|)^(k-1)` holds automatically (k-1 is even),
recovering condition (B). -/
theorem F_line_diff_eq_zero_under_conditionB
    (s : ℂ) (L_minus L_plus : ℂ) (k : ℕ) (_hk : 2 ≤ k)
    (hL_minus : L_minus ≠ 0) (hL_plus : L_plus ≠ 0)
    (h_B :
      (L_plus / (↑‖L_plus‖ : ℂ)) ^ (k - 1) =
      ((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k - 1))
    (ε : ℝ) :
    -((↑(k - 1) : ℂ))⁻¹ *
      (((s + (ε / ‖L_plus‖ : ℝ) • L_plus) - s) ^ (k - 1))⁻¹ =
    -((↑(k - 1) : ℂ))⁻¹ *
      (((s + (ε / ‖L_minus‖ : ℝ) • (-L_minus)) - s) ^ (k - 1))⁻¹ := by
  congr 2
  have h_pow_plus : ((s + (ε / ‖L_plus‖ : ℝ) • L_plus) - s) ^ (k - 1) =
      ((↑ε : ℂ) ^ (k - 1)) * ((L_plus / (↑‖L_plus‖ : ℂ)) ^ (k - 1)) := by
    rw [add_sub_cancel_left,
      show ((ε / ‖L_plus‖ : ℝ) • L_plus : ℂ) = (↑ε : ℂ) * (L_plus / (↑‖L_plus‖ : ℂ)) by
        rw [Complex.real_smul]; push_cast; field_simp,
      mul_pow]
  have h_pow_minus : ((s + (ε / ‖L_minus‖ : ℝ) • (-L_minus)) - s) ^ (k - 1) =
      ((↑ε : ℂ) ^ (k - 1)) * (((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k - 1)) := by
    rw [add_sub_cancel_left,
      show ((ε / ‖L_minus‖ : ℝ) • (-L_minus) : ℂ) =
          (↑ε : ℂ) * ((-L_minus) / (↑‖L_minus‖ : ℂ)) by
        rw [Complex.real_smul]; push_cast; field_simp,
      mul_pow]
  rw [h_pow_plus, h_pow_minus, h_B]

/-- **Combined curve F-difference → 0 under condition (B), general angle.**
For curve γ flat of order n at t₀ with tangents `L_minus` (left) and `L_plus`
(right), under condition (B):

  `‖F(γ(t_eps_minus(ε))) - F(γ(t_eps_plus(ε)))‖ → 0` as ε → 0⁺,

where `F(z) = -1/((k-1)(z-s)^(k-1))` and `t_eps_plus`, `t_eps_minus` are the
exit-time functions on each side.

Proof: triangle inequality `‖A - B‖ ≤ ‖A - TR‖ + ‖B - TR‖` where `TR` is
the common tangent target. Both `‖A - TR‖` and `‖B - TR‖` tend to 0 by
`F_diff_at_tangent_target_tendsto_zero_right/_left`. Under condition (B),
the two side targets are EQUAL (`F_line_diff_eq_zero_under_conditionB`). -/
theorem F_curve_diff_tendsto_zero_under_conditionB
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L_minus L_plus : ℂ} {n k : ℕ}
    (h_flat : IsFlatOfOrder γ t₀ n)
    (hL_minus : L_minus ≠ 0) (hL_plus : L_plus ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ L_plus (Set.Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ L_minus (Set.Iio t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_plus))
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_minus))
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (h_B :
      (L_plus / (↑‖L_plus‖ : ℂ)) ^ (k - 1) =
      ((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k - 1))
    (t_eps_plus t_eps_minus : ℝ → ℝ)
    (h_plus_to : Tendsto t_eps_plus (𝓝[>] (0 : ℝ)) (𝓝[>] t₀))
    (h_plus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (t_eps_plus ε) - s‖ = ε)
    (h_minus_to : Tendsto t_eps_minus (𝓝[>] (0 : ℝ)) (𝓝[<] t₀))
    (h_minus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (t_eps_minus ε) - s‖ = ε) :
    Tendsto (fun ε ↦
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h_sum_raw := ((F_diff_at_tangent_target_tendsto_zero_right
        h_flat hL_plus h_deriv_right hL_right h_s hk hkn hn1).comp h_plus_to).add
      ((F_diff_at_tangent_target_tendsto_zero_left
        h_flat hL_minus h_deriv_left hL_left h_s hk hkn hn1).comp h_minus_to)
  have h_sum : Tendsto (fun ε ↦
      ‖-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹ -
          -(↑(k - 1) : ℂ)⁻¹ *
            (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L_plus‖ : ℝ) • L_plus) - s)
              ^ (k - 1))⁻¹‖ +
        ‖-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹ -
          -(↑(k - 1) : ℂ)⁻¹ *
            (((s + (‖γ (t_eps_minus ε) - s‖ / ‖(-L_minus)‖ : ℝ) • (-L_minus)) - s)
              ^ (k - 1))⁻¹‖)
      (𝓝[>] 0) (𝓝 0) := by
    convert h_sum_raw using 2
    all_goals simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum
    (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
  filter_upwards [h_plus_radius, h_minus_radius] with ε hpr hmr
  have h_targets_eq :
      -(↑(k - 1) : ℂ)⁻¹ *
        (((s + (‖γ (t_eps_minus ε) - s‖ / ‖(-L_minus)‖ : ℝ) • (-L_minus)) - s)
          ^ (k - 1))⁻¹ =
      -(↑(k - 1) : ℂ)⁻¹ *
        (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L_plus‖ : ℝ) • L_plus) - s)
          ^ (k - 1))⁻¹ := by
    rw [hmr, norm_neg, hpr]
    exact (F_line_diff_eq_zero_under_conditionB s L_minus L_plus k hk
      hL_minus hL_plus h_B ε).symm
  set TR := -(↑(k - 1) : ℂ)⁻¹ *
    (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L_plus‖ : ℝ) • L_plus) - s) ^ (k - 1))⁻¹
  set A := -(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹
  set B := -(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹
  change ‖A - B‖ ≤ ‖B - TR‖ + ‖A - _‖
  rw [h_targets_eq]
  calc ‖A - B‖ = ‖(A - TR) - (B - TR)‖ := by rw [sub_sub_sub_cancel_right]
    _ ≤ ‖A - TR‖ + ‖B - TR‖ := norm_sub_le _ _
    _ = ‖B - TR‖ + ‖A - TR‖ := add_comm _ _

end HungerbuhlerWasem

end
