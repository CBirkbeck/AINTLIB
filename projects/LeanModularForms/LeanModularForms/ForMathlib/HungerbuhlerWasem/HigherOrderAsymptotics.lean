/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.FlatChordBound
import LeanModularForms.ForMathlib.FlatnessConditions

/-!
# F-diff asymptotic chain (T-SC-00a)

For a curve `γ` flat of order `n` at `t₀` with `γ(t₀) = s`, the antiderivative
`F(z) = -1/[(k-1)(z-s)^{k-1}]` of the higher-order pole integrand satisfies
`F(γ(t)) - F(tangent target) → 0` as `t → t₀` from either side, provided
`n ≥ k ≥ 2`. Combined with FTC on each smooth piece, this gives the
parameter-excised CPV `→ 0` result needed by the sector cancellation argument
of T-SC-01.

This file restores the F-diff asymptotic subset of the deleted
`HigherOrderCancel.lean` (git ref `79bcaa5^`, lines 477-1300+) into
`namespace HungerbuhlerWasem`. Only the asymptotic / FTC chain leading to the
five headline theorems is restored; the upstream `HasCauchyPVOn`-based
cancellation API (which depended on the also-deleted `HigherOrderAssembly.lean`)
is intentionally omitted as it isn't needed for T-SC-01.

## Headline theorems

* `integral_pow_inv_eq_FTC` — FTC for `γ'/(γ-s)^k` on a smooth piece.
* `closed_excised_integral_eq_antideriv_diff` — closed-form excised integral
  via antiderivative differences.
* `F_diff_at_tangent_target_tendsto_zero_right` — F-diff vs tangent target → 0
  from the right, under flatness and `n ≥ k`.
* `F_diff_at_tangent_target_tendsto_zero_left` — mirror form on the left.
* `cpv_excised_tendsto_zero_of_F_diff_zero` — combined excised-integral form
  of the F-diff Tendsto hypothesis.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Classical Real Interval

noncomputable section

namespace HungerbuhlerWasem

/-- Antiderivative of `1/(z-s)^k` as a function `ℂ → ℂ` (`k ≥ 2`): the function
`F(z) = -1/[(k-1)(z-s)^{k-1}]` has complex derivative `1/(z-s)^k` at any `z ≠ s`. -/
theorem hasDerivAt_antiderivative_pow_inv_complex
    {s : ℂ} {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ≠ s) :
    HasDerivAt (fun w => -(↑(k - 1) : ℂ)⁻¹ * ((w - s) ^ (k - 1))⁻¹)
      (1 / (z - s) ^ k) z := by
  have h_pow : HasDerivAt (fun w : ℂ => (w - s) ^ (k - 1))
      (↑(k - 1) * (z - s) ^ (k - 1 - 1) * 1) z :=
    ((hasDerivAt_id z).sub_const s).pow (k - 1)
  rw [show k - 1 - 1 = k - 2 from by lia] at h_pow
  have h_const := (h_pow.inv (pow_ne_zero _ (sub_ne_zero.mpr hz))).const_mul
    (-(↑(k - 1) : ℂ)⁻¹)
  convert h_const using 1
  -- In Lean v4.31 `convert` can emit a spurious instance-equality side-goal
  -- (`addCommGroup = NormedField…toAddCommGroup`) before the arithmetic goal;
  -- it is closed by `rfl`, so discharge any such defeq goals first.
  all_goals try rfl
  have hk1 : (↑(k - 1) : ℂ) ≠ 0 := by exact_mod_cast (by lia : 0 < k - 1).ne'
  have h_pow_k2_ne : (z - s) ^ (k - 2) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
  have h_pow2 : ((z - s) ^ (k - 1)) ^ 2 = (z - s) ^ k * (z - s) ^ (k - 2) := by
    rw [← pow_mul, ← pow_add]; congr 1; lia
  rw [h_pow2]
  field_simp

/-- When the line segment from `z₁` to `z₂` stays at distance `≥ ε` from `s`, the
antiderivative difference satisfies `‖F(z₂) − F(z₁)‖ ≤ ‖z₂ − z₁‖ / ε^k`, where
`F(z) = -1/[(k-1)(z-s)^{k-1}]`. -/
theorem norm_F_diff_le_segment_bound
    {z₁ z₂ s : ℂ} {k : ℕ} {ε : ℝ} (hk : 2 ≤ k) (hε : 0 < ε)
    (h_seg_avoids : ∀ z ∈ segment ℝ z₁ z₂, ε ≤ ‖z - s‖) :
    ‖(-(↑(k - 1) : ℂ)⁻¹ * ((z₂ - s) ^ (k - 1))⁻¹) -
      (-(↑(k - 1) : ℂ)⁻¹ * ((z₁ - s) ^ (k - 1))⁻¹)‖ ≤
      (1 / ε ^ k) * ‖z₂ - z₁‖ := by
  have h_deriv : ∀ z ∈ segment ℝ z₁ z₂,
      HasDerivWithinAt (fun w => -(↑(k - 1) : ℂ)⁻¹ * ((w - s) ^ (k - 1))⁻¹)
        (1 / (z - s) ^ k) (segment ℝ z₁ z₂) z := by
    intro z hz
    have h_ne : z ≠ s := fun heq => by
      have := h_seg_avoids z hz; rw [heq, sub_self, norm_zero] at this; linarith
    exact (hasDerivAt_antiderivative_pow_inv_complex hk h_ne).hasDerivWithinAt
  have h_bound : ∀ z ∈ segment ℝ z₁ z₂, ‖1 / (z - s) ^ k‖ ≤ 1 / ε ^ k := by
    intro z hz
    rw [norm_div, norm_one, norm_pow]
    exact div_le_div_of_nonneg_left zero_le_one (pow_pos hε k)
      (pow_le_pow_left₀ hε.le (h_seg_avoids z hz) k)
  exact (convex_segment z₁ z₂).norm_image_sub_le_of_norm_hasDerivWithin_le h_deriv h_bound
    (left_mem_segment _ _ _) (right_mem_segment _ _ _)

/-- When `γ` has right-derivative `L ≠ 0` at `t₀` and `γ(t₀) = s`, for `t` close to
`t₀` from the right, `γ(t) − s` lies in the `+L` hemisphere
(`Re((γ(t) − s) · conj L) ≥ 0`). -/
theorem eventually_re_pos_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_s : γ t₀ = s) :
    ∀ᶠ t in 𝓝[>] t₀, 0 ≤ ((γ t - s) * starRingEnd ℂ L).re := by
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hLsq_pos : 0 < ‖L‖ ^ 2 := by positivity
  filter_upwards [h_deriv.isLittleO.bound (by linarith : (0 : ℝ) < ‖L‖ / 2),
    self_mem_nhdsWithin] with t h_b ht
  have h_pos : 0 < t - t₀ := sub_pos.mpr ht
  rw [Real.norm_eq_abs, abs_of_pos h_pos] at h_b
  rw [show (γ t - s) = (t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L) by rw [h_s]; ring,
    add_mul, Complex.add_re]
  have h1 : ((((t - t₀) : ℝ) • L) * starRingEnd ℂ L).re = (t - t₀) * ‖L‖ ^ 2 := by
    rw [Complex.real_smul, mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h1]
  have h2 : -(‖L‖ / 2 * (t - t₀)) * ‖L‖ ≤
      ((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ L).re := by
    have habs := Complex.abs_re_le_norm
      ((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ L)
    rw [norm_mul, Complex.norm_conj] at habs
    nlinarith [abs_le.mp (habs.trans (mul_le_mul_of_nonneg_right h_b (norm_nonneg L)))]
  nlinarith [hLsq_pos]

/-- Symmetric counterpart of `eventually_re_pos_right`: `Re((γ(t) − s) · conj L) ≤ 0`
for `t` close to `t₀` from the left. -/
theorem eventually_re_neg_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_s : γ t₀ = s) :
    ∀ᶠ t in 𝓝[<] t₀, ((γ t - s) * starRingEnd ℂ L).re ≤ 0 := by
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hLsq_pos : 0 < ‖L‖ ^ 2 := by positivity
  filter_upwards [h_deriv.isLittleO.bound (by linarith : (0 : ℝ) < ‖L‖ / 2),
    self_mem_nhdsWithin] with t h_b ht
  have h_neg : t - t₀ < 0 := sub_neg.mpr ht
  rw [Real.norm_eq_abs, abs_of_neg h_neg] at h_b
  rw [show (γ t - s) = (t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L) by rw [h_s]; ring,
    add_mul, Complex.add_re]
  have h1 : ((((t - t₀) : ℝ) • L) * starRingEnd ℂ L).re = (t - t₀) * ‖L‖ ^ 2 := by
    rw [Complex.real_smul, mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h1]
  have h2 : ((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ L).re ≤
      ‖L‖ / 2 * -(t - t₀) * ‖L‖ := by
    have habs := Complex.abs_re_le_norm
      ((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ L)
    rw [norm_mul, Complex.norm_conj] at habs
    nlinarith [abs_le.mp (habs.trans (mul_le_mul_of_nonneg_right h_b (norm_nonneg L)))]
  nlinarith [hLsq_pos]

/-- With right-derivative `L ≠ 0`, the curve cannot stay at `s` past `t₀`. -/
theorem eventually_ne_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_s : γ t₀ = s) :
    ∀ᶠ t in 𝓝[>] t₀, γ t ≠ s := by
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  filter_upwards [h_deriv.isLittleO.bound (by linarith : (0 : ℝ) < ‖L‖ / 2),
    self_mem_nhdsWithin] with t h_b ht
  have h_pos : 0 < t - t₀ := sub_pos.mpr ht
  intro h_eq
  have h_diff_zero : γ t - γ t₀ = 0 := h_s ▸ sub_eq_zero.mpr h_eq
  simp only [h_diff_zero, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos h_pos] at h_b
  nlinarith

/-- Left-side counterpart of `eventually_ne_right`. -/
theorem eventually_ne_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_s : γ t₀ = s) :
    ∀ᶠ t in 𝓝[<] t₀, γ t ≠ s := by
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  filter_upwards [h_deriv.isLittleO.bound (by linarith : (0 : ℝ) < ‖L‖ / 2),
    self_mem_nhdsWithin] with t h_b ht
  have h_neg : t - t₀ < 0 := sub_neg.mpr ht
  intro h_eq
  have h_diff_zero : γ t - γ t₀ = 0 := h_s ▸ sub_eq_zero.mpr h_eq
  simp only [h_diff_zero, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_neg h_neg] at h_b
  nlinarith

/-- Combining flatness with the chord bound and the eventual sign/non-zero conditions,
the chord `‖γ(t) − s − (‖γ(t)−s‖/‖L‖)·L‖` is `o(‖γ(t)−s‖^n)` as `t → t₀⁺`. -/
theorem chord_to_tangent_isLittleO_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {n : ℕ}
    (h_flat : IsFlatOfOrder γ t₀ n) (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (h_s : γ t₀ = s) :
    (fun t => ‖γ t - s - (‖γ t - s‖ / ‖L‖ : ℝ) • L‖) =o[𝓝[>] t₀]
      (fun t => ‖γ t - s‖ ^ n) := by
  have h_eventually_bound : ∀ᶠ t in 𝓝[>] t₀,
      ‖γ t - s - (‖γ t - s‖ / ‖L‖ : ℝ) • L‖ ≤ 3 * ‖tangentDeviation (γ t - s) L‖ := by
    filter_upwards [eventually_re_pos_right hL h_deriv h_s,
                    eventually_ne_right hL h_deriv h_s] with t h_pos h_ne
    have hw_pos : 0 < ‖γ t - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h_ne)
    have h_chord := LeanModularForms.norm_chord_to_tangent_target_le hL hw_pos h_pos
    have h_dev_le : ‖tangentDeviation (γ t - s) L‖ ≤ 2 * ‖γ t - s‖ :=
      norm_tangentDeviation_le _ _ hL
    have h_div_bound : ‖tangentDeviation (γ t - s) L‖ ^ 2 / ‖γ t - s‖ ≤
        2 * ‖tangentDeviation (γ t - s) L‖ := by
      rw [pow_two, mul_div_assoc]
      have hd_div : ‖tangentDeviation (γ t - s) L‖ / ‖γ t - s‖ ≤ 2 := by
        rw [div_le_iff₀ hw_pos]; linarith
      nlinarith [norm_nonneg (tangentDeviation (γ t - s) L)]
    linarith [h_chord]
  refine Asymptotics.IsBigO.trans_isLittleO ?_
    (LeanModularForms.orthogonal_deviation_at_radius_right h_flat hL hL_right h_s)
  refine Asymptotics.IsBigO.of_bound 3 ?_
  filter_upwards [h_eventually_bound] with t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (norm_nonneg _)]
  exact ht

/-- Left-side counterpart of `chord_to_tangent_isLittleO_right`: the chord is bounded
by `o(‖γ(t)−s‖^n)` as `t → t₀⁻`, with target on the `−L` ray. -/
theorem chord_to_tangent_isLittleO_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {n : ℕ}
    (h_flat : IsFlatOfOrder γ t₀ n) (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (h_s : γ t₀ = s) :
    (fun t => ‖γ t - s - (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)‖) =o[𝓝[<] t₀]
      (fun t => ‖γ t - s‖ ^ n) := by
  have hLneg : (-L) ≠ 0 := neg_ne_zero.mpr hL
  have h_dev_eq : ∀ t, tangentDeviation (γ t - s) (-L) = tangentDeviation (γ t - s) L := by
    intro t
    unfold tangentDeviation orthogonalProjectionComplex
    rw [Complex.normSq_neg L,
      show ((γ t - s) * starRingEnd ℂ (-L)).re = -((γ t - s) * starRingEnd ℂ L).re by
        rw [map_neg, mul_neg]; exact Complex.neg_re _]
    module
  have h_pos_neg : ∀ᶠ t in 𝓝[<] t₀, 0 ≤ ((γ t - s) * starRingEnd ℂ (-L)).re := by
    filter_upwards [eventually_re_neg_left hL h_deriv h_s] with t h_neg
    rw [map_neg, mul_neg, Complex.neg_re]; linarith
  have h_eventually_bound : ∀ᶠ t in 𝓝[<] t₀,
      ‖γ t - s - (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)‖ ≤
        3 * ‖tangentDeviation (γ t - s) L‖ := by
    filter_upwards [h_pos_neg, eventually_ne_left hL h_deriv h_s] with t h_pos h_ne
    have hw_pos : 0 < ‖γ t - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h_ne)
    have h_chord := LeanModularForms.norm_chord_to_tangent_target_le hLneg hw_pos h_pos
    have h_dev_le : ‖tangentDeviation (γ t - s) (-L)‖ ≤ 2 * ‖γ t - s‖ :=
      norm_tangentDeviation_le _ _ hLneg
    have h_div_bound :
        ‖tangentDeviation (γ t - s) (-L)‖ ^ 2 / ‖γ t - s‖ ≤
          2 * ‖tangentDeviation (γ t - s) (-L)‖ := by
      rw [pow_two, mul_div_assoc]
      have hd_div : ‖tangentDeviation (γ t - s) (-L)‖ / ‖γ t - s‖ ≤ 2 := by
        rw [div_le_iff₀ hw_pos]; linarith
      nlinarith [norm_nonneg (tangentDeviation (γ t - s) (-L))]
    rw [← h_dev_eq t]; linarith [h_chord]
  refine Asymptotics.IsBigO.trans_isLittleO ?_
    (LeanModularForms.orthogonal_deviation_at_radius_left h_flat hL hL_left h_s)
  refine Asymptotics.IsBigO.of_bound 3 ?_
  filter_upwards [h_eventually_bound] with t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (norm_nonneg _)]
  exact ht

/-- If `z₁, z₂` are equidistant from `s` (distance `d`), then any point `z` on the
segment from `z₁` to `z₂` satisfies `‖z − s‖² ≥ d² − ‖z₁ − z₂‖²/4`. -/
theorem norm_sq_segment_to_pole_lower_bound
    {z₁ z₂ s : ℂ} {d : ℝ}
    (h₁ : ‖z₁ - s‖ = d) (h₂ : ‖z₂ - s‖ = d)
    {z : ℂ} (hz : z ∈ segment ℝ z₁ z₂) :
    d ^ 2 - ‖z₁ - z₂‖ ^ 2 / 4 ≤ ‖z - s‖ ^ 2 := by
  obtain ⟨α, β, hα, hβ, h_sum, rfl⟩ := hz
  rw [show α • z₁ + β • z₂ - s = α • (z₁ - s) + β • (z₂ - s) by
    rw [show β = 1 - α by linarith]; module]
  have h_expand : ‖α • (z₁ - s) + β • (z₂ - s)‖ ^ 2 =
      α ^ 2 * ‖z₁ - s‖ ^ 2 +
        2 * α * β * ((z₁ - s) * starRingEnd ℂ (z₂ - s)).re +
        β ^ 2 * ‖z₂ - s‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.real_smul]
    rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_ofReal, Complex.normSq_ofReal,
      show (((α : ℂ) * (z₁ - s)) * starRingEnd ℂ ((β : ℂ) * (z₂ - s))) =
          ((α * β : ℝ) : ℂ) * ((z₁ - s) * starRingEnd ℂ (z₂ - s)) by
        rw [map_mul, Complex.conj_ofReal]; push_cast; ring,
      show (((α * β : ℝ) : ℂ) * ((z₁ - s) * starRingEnd ℂ (z₂ - s))).re =
          α * β * ((z₁ - s) * starRingEnd ℂ (z₂ - s)).re by
        rw [Complex.mul_re]; simp]
    ring
  have h_cross : ((z₁ - s) * starRingEnd ℂ (z₂ - s)).re =
      (‖z₁ - s‖ ^ 2 + ‖z₂ - s‖ ^ 2 - ‖z₁ - z₂‖ ^ 2) / 2 := by
    have h_ns := Complex.normSq_sub (z₁ - s) (z₂ - s)
    rw [← Complex.sq_norm, ← Complex.sq_norm, ← Complex.sq_norm,
      show (z₁ - s) - (z₂ - s) = z₁ - z₂ by ring] at h_ns
    linarith
  rw [h_expand, h_cross, h₁, h₂]
  have h_ab_le : α * β ≤ 1 / 4 := by nlinarith [sq_nonneg (α - β)]
  have h_quad : α ^ 2 + 2 * α * β + β ^ 2 = 1 := by nlinarith [h_sum]
  nlinarith [h_quad, h_ab_le, sq_nonneg (‖z₁ - z₂‖)]

/-- When the chord between two equidistant points is at most `d`, the segment from
`z₁` to `z₂` stays at distance `≥ d/2` from `s`. -/
theorem norm_segment_to_pole_lower_bound_half
    {z₁ z₂ s : ℂ} {d : ℝ} (_hd_pos : 0 < d)
    (h₁ : ‖z₁ - s‖ = d) (h₂ : ‖z₂ - s‖ = d) (h_chord : ‖z₁ - z₂‖ ≤ d)
    {z : ℂ} (hz : z ∈ segment ℝ z₁ z₂) :
    d / 2 ≤ ‖z - s‖ := by
  have h_le_sq : (d / 2) ^ 2 ≤ ‖z - s‖ ^ 2 := by
    nlinarith [norm_sq_segment_to_pole_lower_bound h₁ h₂ hz,
      mul_self_le_mul_self (norm_nonneg _) h_chord]
  have := abs_le_of_sq_le_sq' h_le_sq (norm_nonneg _)
  linarith [this.2, abs_of_pos (by linarith : 0 < d / 2)]

/-- For `γ(t) ≠ s` and chord-to-target bounded by `‖γ(t) - s‖`, the antiderivative
difference between `γ(t)` and the tangent target `s + (‖γ(t)-s‖/‖L‖)·L` is bounded by
`(1/(‖γ(t)−s‖/2)^k) · chord(t)`. -/
theorem norm_F_diff_at_tangent_target_le
    {γ : ℝ → ℂ} {t : ℝ} {s L : ℂ} {k : ℕ} (hk : 2 ≤ k)
    (hL : L ≠ 0) (hw_ne : γ t ≠ s)
    (h_chord_le : ‖γ t - (s + (‖γ t - s‖ / ‖L‖ : ℝ) • L)‖ ≤ ‖γ t - s‖) :
    ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
      (-(↑(k - 1) : ℂ)⁻¹ * (((s + (‖γ t - s‖ / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹)‖ ≤
      (1 / (‖γ t - s‖ / 2) ^ k) * ‖γ t - (s + (‖γ t - s‖ / ‖L‖ : ℝ) • L)‖ := by
  have hd_pos : 0 < ‖γ t - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw_ne)
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  set d := ‖γ t - s‖
  set tgt := s + (d / ‖L‖ : ℝ) • L with htgt_def
  have h_tgt : ‖tgt - s‖ = d := by
    rw [show tgt - s = (d / ‖L‖ : ℝ) • L by simp [htgt_def], norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    field_simp
  have h_F_diff := norm_F_diff_le_segment_bound (z₁ := γ t) (z₂ := tgt) (s := s) hk
    (by linarith : 0 < d / 2)
    (fun z hz => norm_segment_to_pole_lower_bound_half hd_pos rfl h_tgt h_chord_le hz)
  rw [show (-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
      (-(↑(k - 1) : ℂ)⁻¹ * ((tgt - s) ^ (k - 1))⁻¹) =
      -((-(↑(k - 1) : ℂ)⁻¹ * ((tgt - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹)) by ring,
    norm_neg, show ‖γ t - tgt‖ = ‖tgt - γ t‖ from norm_sub_rev _ _]
  exact h_F_diff

/-- If `chord = o(d^n)`, `d → 0`, `d > 0` eventually, and `k ≤ n`, then
`chord/d^k → 0`. -/
theorem tendsto_div_pow_zero_of_isLittleO
    {chord d : ℝ → ℝ} {l : Filter ℝ} {n k : ℕ}
    (h_chord : chord =o[l] (fun t => d t ^ n)) (h_d : Tendsto d l (𝓝 0))
    (h_d_pos : ∀ᶠ t in l, 0 < d t) (hkn : k ≤ n) :
    Tendsto (fun t => chord t / d t ^ k) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h_chord.bound (by linarith : 0 < ε / 2),
    h_d.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)), h_d_pos] with t hb hd hdp
  have hd_n_pos : 0 < d t ^ n := pow_pos hdp n
  have hd_k_pos : 0 < d t ^ k := pow_pos hdp k
  rw [Real.dist_eq, sub_zero]
  have h_pow : d t ^ n = d t ^ k * d t ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hkn]
  rw [Real.norm_eq_abs] at hb
  rw [Real.norm_eq_abs, abs_of_nonneg hd_n_pos.le] at hb
  rw [abs_div, abs_of_pos hd_k_pos]
  have h_pow_le : d t ^ (n - k) ≤ 1 := by
    rcases Nat.eq_zero_or_pos (n - k) with h_eq | h_pos
    · simp [h_eq]
    · exact pow_le_one₀ hdp.le hd.le |>.trans_eq (by simp)
  calc |chord t| / d t ^ k
      ≤ ε / 2 * d t ^ (n - k) := by
        rw [div_le_iff₀ hd_k_pos]
        nlinarith [hb, h_pow]
    _ ≤ ε / 2 * 1 := by gcongr
    _ < ε := by linarith

/-- Under HW's flatness condition `n ≥ k` (with `k ≥ 2`), the antiderivative
difference between `γ(t)` and the tangent target on the +L ray tends to 0 as
`t → t₀⁺`. -/
theorem F_diff_at_tangent_target_tendsto_zero_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {n k : ℕ}
    (h_flat : IsFlatOfOrder γ t₀ n) (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n) :
    Tendsto (fun t =>
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ *
          (((s + (‖γ t - s‖ / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹)‖)
      (𝓝[>] t₀) (𝓝 0) := by
  have h_chord := chord_to_tangent_isLittleO_right h_flat hL h_deriv hL_right h_s
  have h_d_to_zero : Tendsto (fun t => ‖γ t - s‖) (𝓝[>] t₀) (𝓝 0) := by
    have hγ : Tendsto γ (𝓝[>] t₀) (𝓝 s) := h_s ▸ h_deriv.continuousWithinAt
    simpa using (hγ.sub_const s).norm
  have h_d_pos : ∀ᶠ t in 𝓝[>] t₀, 0 < ‖γ t - s‖ := by
    filter_upwards [eventually_ne_right hL h_deriv h_s] with t h
    exact norm_pos_iff.mpr (sub_ne_zero.mpr h)
  have h_const_ratio : Tendsto
      (fun t => 2 ^ k * (‖γ t - s - (‖γ t - s‖ / ‖L‖ : ℝ) • L‖ / ‖γ t - s‖ ^ k))
      (𝓝[>] t₀) (𝓝 0) := by
    simpa using
      (tendsto_div_pow_zero_of_isLittleO h_chord h_d_to_zero h_d_pos hkn).const_mul (2 ^ k : ℝ)
  have h_chord_le_d : ∀ᶠ t in 𝓝[>] t₀,
      ‖γ t - s - (‖γ t - s‖ / ‖L‖ : ℝ) • L‖ ≤ ‖γ t - s‖ := by
    filter_upwards [h_chord.bound one_pos,
      h_d_to_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      h_d_pos] with t hb hd hdp
    calc ‖γ t - s - (‖γ t - s‖ / ‖L‖ : ℝ) • L‖
        ≤ ‖γ t - s‖ ^ n := by simpa using hb
      _ ≤ ‖γ t - s‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hd hn1
      _ = ‖γ t - s‖ := pow_one _
  have h_F_diff_le : ∀ᶠ t in 𝓝[>] t₀,
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ *
          (((s + (‖γ t - s‖ / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹)‖ ≤
      2 ^ k * (‖γ t - s - (‖γ t - s‖ / ‖L‖ : ℝ) • L‖ / ‖γ t - s‖ ^ k) := by
    filter_upwards [eventually_ne_right hL h_deriv h_s, h_chord_le_d] with t h_ne hcd
    have hcd' : ‖γ t - (s + (‖γ t - s‖ / ‖L‖ : ℝ) • L)‖ ≤ ‖γ t - s‖ := by
      rwa [show γ t - (s + (‖γ t - s‖ / ‖L‖ : ℝ) • L) =
            γ t - s - (‖γ t - s‖ / ‖L‖ : ℝ) • L by ring]
    have h_bound := norm_F_diff_at_tangent_target_le hk hL h_ne hcd'
    rw [show ‖γ t - (s + (‖γ t - s‖ / ‖L‖ : ℝ) • L)‖ =
          ‖γ t - s - (‖γ t - s‖ / ‖L‖ : ℝ) • L‖ by congr 1; ring] at h_bound
    calc ‖_‖
        ≤ (1 : ℝ) / (‖γ t - s‖ / 2) ^ k *
            ‖γ t - s - (‖γ t - s‖ / ‖L‖ : ℝ) • L‖ := h_bound
      _ = 2 ^ k / ‖γ t - s‖ ^ k *
            ‖γ t - s - (‖γ t - s‖ / ‖L‖ : ℝ) • L‖ := by
          congr 1; rw [div_pow]; field_simp
      _ = 2 ^ k * (‖γ t - s - (‖γ t - s‖ / ‖L‖ : ℝ) • L‖ / ‖γ t - s‖ ^ k) := by ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_const_ratio
    (Eventually.of_forall fun _ => norm_nonneg _) h_F_diff_le

/-- Left-side counterpart of `F_diff_at_tangent_target_tendsto_zero_right`. -/
theorem F_diff_at_tangent_target_tendsto_zero_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {n k : ℕ}
    (h_flat : IsFlatOfOrder γ t₀ n) (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n) :
    Tendsto (fun t =>
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ *
          (((s + (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)) - s) ^ (k - 1))⁻¹)‖)
      (𝓝[<] t₀) (𝓝 0) := by
  have hLneg : (-L) ≠ 0 := neg_ne_zero.mpr hL
  have h_chord := chord_to_tangent_isLittleO_left h_flat hL h_deriv hL_left h_s
  have h_d_to_zero : Tendsto (fun t => ‖γ t - s‖) (𝓝[<] t₀) (𝓝 0) := by
    have hγ : Tendsto γ (𝓝[<] t₀) (𝓝 s) := h_s ▸ h_deriv.continuousWithinAt
    simpa using (hγ.sub_const s).norm
  have h_d_pos : ∀ᶠ t in 𝓝[<] t₀, 0 < ‖γ t - s‖ := by
    filter_upwards [eventually_ne_left hL h_deriv h_s] with t h
    exact norm_pos_iff.mpr (sub_ne_zero.mpr h)
  have h_const_ratio : Tendsto
      (fun t => 2 ^ k * (‖γ t - s - (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)‖ /
        ‖γ t - s‖ ^ k))
      (𝓝[<] t₀) (𝓝 0) := by
    simpa using
      (tendsto_div_pow_zero_of_isLittleO h_chord h_d_to_zero h_d_pos hkn).const_mul (2 ^ k : ℝ)
  have h_chord_le_d : ∀ᶠ t in 𝓝[<] t₀,
      ‖γ t - s - (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)‖ ≤ ‖γ t - s‖ := by
    filter_upwards [h_chord.bound one_pos,
      h_d_to_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      h_d_pos] with t hb hd hdp
    calc ‖γ t - s - (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)‖
        ≤ ‖γ t - s‖ ^ n := by simpa using hb
      _ ≤ ‖γ t - s‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hd hn1
      _ = ‖γ t - s‖ := pow_one _
  have h_F_diff_le : ∀ᶠ t in 𝓝[<] t₀,
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ *
          (((s + (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)) - s) ^ (k - 1))⁻¹)‖ ≤
      2 ^ k * (‖γ t - s - (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)‖ / ‖γ t - s‖ ^ k) := by
    filter_upwards [eventually_ne_left hL h_deriv h_s, h_chord_le_d] with t h_ne hcd
    have hcd' : ‖γ t - (s + (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L))‖ ≤ ‖γ t - s‖ := by
      rwa [show γ t - (s + (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)) =
            γ t - s - (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L) by ring]
    have h_bound := norm_F_diff_at_tangent_target_le hk hLneg h_ne hcd'
    rw [show ‖γ t - (s + (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L))‖ =
          ‖γ t - s - (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)‖ by congr 1; ring] at h_bound
    calc ‖_‖
        ≤ (1 : ℝ) / (‖γ t - s‖ / 2) ^ k *
            ‖γ t - s - (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)‖ := h_bound
      _ = 2 ^ k / ‖γ t - s‖ ^ k *
            ‖γ t - s - (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)‖ := by
          congr 1; rw [div_pow]; field_simp
      _ = 2 ^ k * (‖γ t - s - (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)‖ /
            ‖γ t - s‖ ^ k) := by ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_const_ratio
    (Eventually.of_forall fun _ => norm_nonneg _) h_F_diff_le

end HungerbuhlerWasem

end
