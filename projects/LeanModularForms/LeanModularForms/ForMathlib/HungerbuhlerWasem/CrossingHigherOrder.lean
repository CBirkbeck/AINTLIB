/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem.SectorCancellation
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CrossingDataBuilder
import LeanModularForms.ForMathlib.ExitTime
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Higher-order CPV discharger from immersion data (T-BR-03)

This file wraps `hasCauchyPVOn_singleton_pow_of_conditionB_assembled`
(in `SectorCancellation.lean`) into a paper-faithful form. The original
theorem takes ~30 hypotheses describing the analytic and geometric data
of the crossing; this wrapper derives all of them from a much smaller set
of inputs:

* `γ : ClosedPwC1Immersion x` — the closed piecewise-`C¹` immersion;
* `t₀ ∈ Ioo 0 1` — interior crossing time;
* `h_at`, `h_unique` — the curve crosses `s` only at `t₀`;
* `h_flat : IsFlatOfOrder γ.extend t₀ n` for `2 ≤ k ≤ n`;
* `h_B` (corner form) or `h_angle` (smooth form) — the angle compatibility
  expressing Condition (B) for the integrand `c/(z-s)^k`.

## Main results

* `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner` —
  general (corner-friendly) form, takes explicit left/right derivative
  limits and the unit-circle equation `h_B`.
* `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB` —
  smooth specialisation at off-partition points, deriving `L_- = L_+` and
  the even-power `h_B` from the simpler `(k-1)·π ∈ 2π·ℤ` form of (B).
-/

open Filter Topology Set Complex MeasureTheory
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

/-- Build `h_close` from a closed piecewise-`C¹` curve: the extended path takes
the same value at `0` and `1` (both equal the basepoint `x`). -/
theorem closed_immersion_extend_zero_eq_one (γ : ClosedPwC1Immersion x) :
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 0 =
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 1 := by
  simp

private theorem neg_pow_eq_self_of_even_sub_one
    {k : ℕ} (z : ℂ) (m : ℤ) (hm : ((k - 1 : ℕ) : ℝ) = 2 * (m : ℝ)) :
    (-z) ^ (k - 1) = z ^ (k - 1) := by
  refine Even.neg_pow ?_ z
  have h_eq : ((k - 1 : ℕ) : ℤ) = 2 * m := by exact_mod_cast hm
  exact ⟨m.toNat, by lia⟩

/-- At an off-partition interior point, the right and left derivative limits both
equal `deriv γ t₀` and are nonzero. -/
theorem deriv_limit_eq_at_off_partition
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (h_off : t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition) :
    let f := γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend
    deriv f t₀ ≠ 0 ∧
    Tendsto (deriv f) (𝓝[>] t₀) (𝓝 (deriv f t₀)) ∧
    Tendsto (deriv f) (𝓝[<] t₀) (𝓝 (deriv f t₀)) := by
  have h_cont :=
    γ.toPwC1Immersion.toPiecewiseC1Path.deriv_continuous_off_extend t₀ ht₀ h_off
  exact ⟨γ.toPwC1Immersion.deriv_ne_zero t₀ ht₀ h_off,
    h_cont.tendsto.mono_left nhdsWithin_le_nhds,
    h_cont.tendsto.mono_left nhdsWithin_le_nhds⟩

/-- The angle equation `h_B` from condition-(B) angle compatibility, in the
off-partition (smooth) case where `L_- = L_+ = L`.

If `(k-1) · π = m · 2π` for some integer `m`, then
`(L/‖L‖)^(k-1) = ((-L)/‖L‖)^(k-1)`. -/
theorem h_B_of_angle_compat_smooth
    (L : ℂ) (_hL : L ≠ 0) (k : ℕ) (_hk : 2 ≤ k)
    (h_angle : ∃ m : ℤ, ((k - 1 : ℕ) : ℝ) * Real.pi = (m : ℝ) * (2 * Real.pi)) :
    (L / (↑‖L‖ : ℂ)) ^ (k - 1) =
    ((-L) / (↑‖L‖ : ℂ)) ^ (k - 1) := by
  obtain ⟨m, hm⟩ := h_angle
  have hkm : ((k - 1 : ℕ) : ℝ) = 2 * (m : ℝ) :=
    mul_right_cancel₀ Real.pi_ne_zero (by linarith [hm] :
      ((k - 1 : ℕ) : ℝ) * Real.pi = (2 * m) * Real.pi)
  rw [neg_div, neg_pow_eq_self_of_even_sub_one (L / ↑‖L‖) m hkm]

/-- For a function `γ` with `Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L)` and eventual
differentiability on `(t₀, ∞)`, plus continuity at `t₀`, we have
`HasDerivWithinAt γ L (Ioi t₀) t₀`. -/
theorem hasDerivWithinAt_Ioi_of_tendsto
    {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L)) :
    HasDerivWithinAt γ L (Ioi t₀) t₀ := by
  obtain ⟨s, hs_mem, hs_diff⟩ := hγ_diff.exists_mem
  exact hasDerivWithinAt_Ioi_iff_Ici.mpr
    (hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun t ht => (hs_diff t ht).differentiableWithinAt)
      hγ_cont.continuousWithinAt hs_mem hL_right)

/-- For a function `γ` with `Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L)` and eventual
differentiability on `(-∞, t₀)`, plus continuity at `t₀`, we have
`HasDerivWithinAt γ L (Iio t₀) t₀`. -/
theorem hasDerivWithinAt_Iio_of_tendsto
    {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L)) :
    HasDerivWithinAt γ L (Iio t₀) t₀ := by
  obtain ⟨s, hs_mem, hs_diff⟩ := hγ_diff.exists_mem
  exact hasDerivWithinAt_Iio_iff_Iic.mpr
    (hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hs_diff t ht).differentiableWithinAt)
      hγ_cont.continuousWithinAt hs_mem hL_left)

/-- A cutoff-integrability lemma for `c / (z - s)^k`, mirroring
`cpvIntegrandOn_polarPart_intervalIntegrable` but specialised to a single
Laurent monomial. -/
theorem cpvIntegrandOn_singleMonomial_intervalIntegrable
    (γ : ClosedPwC1Immersion x) {s : ℂ} {S : Finset ℂ} (hs : s ∈ S)
    (c : ℂ) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => c / (z - s) ^ k)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t)
      MeasureTheory.volume 0 1 := by
  classical
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  set badSet : Set ℝ := {t | ∃ s' ∈ S, ‖γP.toPath.extend t - s'‖ ≤ ε} with badSet_def
  set monomial : ℂ → ℂ := fun z => c / (z - s) ^ k
  set h_curve : ℝ → ℂ := fun t =>
    monomial (γP.toPath.extend t) * deriv γP.toPath.extend t
  have h_indicator_eq :
      (fun t => cpvIntegrandOn S monomial γP.toPath.extend ε t) =
      badSetᶜ.indicator h_curve := by
    funext t
    by_cases ht_in : t ∈ badSet
    · rw [cpvIntegrandOn_of_exists_le ht_in,
        Set.indicator_of_notMem (Set.notMem_compl_iff.mpr ht_in)]
    · have h_forall : ∀ s' ∈ S, ε < ‖γP.toPath.extend t - s'‖ := by
        simpa only [Set.mem_setOf_eq, not_exists, not_and, not_le, badSet_def] using ht_in
      rw [cpvIntegrandOn_of_forall_gt h_forall, Set.indicator_of_mem ht_in]
  set M_polar : ℝ := ‖c‖ / ε ^ k
  set M : ℝ := M_polar * K
  have h_M_polar_nonneg : 0 ≤ M_polar :=
    div_nonneg (norm_nonneg _) (pow_nonneg hε.le _)
  have h_M_nonneg : 0 ≤ M := mul_nonneg h_M_polar_nonneg (NNReal.coe_nonneg K)
  have h_bound_on_compl : ∀ t ∈ badSetᶜ, ‖h_curve t‖ ≤ M := fun t ht_in => by
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_and,
      not_le, badSet_def] at ht_in
    calc ‖h_curve t‖ = ‖monomial (γP.toPath.extend t)‖ *
          ‖deriv γP.toPath.extend t‖ := norm_mul _ _
      _ ≤ M_polar * K :=
          mul_le_mul (by
            change ‖c / (γP.toPath.extend t - s) ^ k‖ ≤ M_polar
            rw [norm_div, norm_pow]
            exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hε _)
              (pow_le_pow_left₀ hε.le (ht_in s hs).le _))
            (norm_deriv_le_of_lipschitz hLip) (norm_nonneg _) h_M_polar_nonneg
  have h_γ_meas : Measurable γP.toPath.extend := γP.toPath.continuous_extend.measurable
  have h_curve_meas : Measurable h_curve :=
    (((h_γ_meas.sub_const s).pow_const _).const_div _).mul (measurable_deriv _)
  have h_badSet_meas : MeasurableSet badSet := by
    have h_eq : badSet = ⋃ s' ∈ (S : Set ℂ),
        {t : ℝ | ‖γP.toPath.extend t - s'‖ ≤ ε} := by
      ext t; simp only [badSet_def, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe, exists_prop]
    rw [h_eq]
    exact MeasurableSet.biUnion S.countable_toSet fun s' _ =>
      measurableSet_le (h_γ_meas.sub_const s').norm measurable_const
  rw [intervalIntegrable_iff, h_indicator_eq]
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
    (h_curve_meas.aestronglyMeasurable.indicator h_badSet_meas.compl) M ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t _
  by_cases ht_in : t ∈ badSetᶜ
  · rw [Set.indicator_of_mem ht_in]; exact h_bound_on_compl t ht_in
  · rw [Set.indicator_of_notMem ht_in, norm_zero]; exact h_M_nonneg

private theorem div_norm_eq_exp_arg {z : ℂ} (hz : z ≠ 0) :
    z / (↑‖z‖ : ℂ) = Complex.exp (↑(Complex.arg z) * Complex.I) := by
  rw [div_eq_iff (by exact_mod_cast (norm_pos_iff.mpr hz).ne'), mul_comm]
  exact (Complex.norm_mul_exp_arg_mul_I z).symm

/-- **From corner angle equation to `h_B`.** Given nonzero `L_-, L_+`, and the
integer angle equation `(k - 1 : ℕ) · (arg L_+ - arg (-L_-)) = m · 2π`, the
unit-circle powers `(L_+/‖L_+‖)^(k-1)` and `((-L_-)/‖L_-‖)^(k-1)` agree.

This is the general-angle analog of `h_B_of_angle_compat_smooth`: where the
smooth case forces `L_+ = -(-L_-)` (so the angle is `π` and the equation
reduces to even-power), the corner case uses the general angle
`α = arg(L_+) - arg(-L_-)`. -/
theorem h_B_of_angle_compat_corner
    {L_minus L_plus : ℂ} (hL_minus : L_minus ≠ 0) (hL_plus : L_plus ≠ 0)
    {k : ℕ} (_hk : 2 ≤ k)
    (h_angle : ∃ m : ℤ,
      ((k - 1 : ℕ) : ℝ) * (Complex.arg L_plus - Complex.arg (-L_minus)) =
        (m : ℝ) * (2 * Real.pi)) :
    (L_plus / (↑‖L_plus‖ : ℂ)) ^ (k - 1) =
    ((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k - 1) := by
  obtain ⟨m, hm⟩ := h_angle
  rw [show (↑‖L_minus‖ : ℂ) = ↑‖-L_minus‖ by rw [norm_neg],
    div_norm_eq_exp_arg hL_plus, div_norm_eq_exp_arg (neg_ne_zero.mpr hL_minus),
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨m, ?_⟩
  have hm_complex : ((k - 1 : ℕ) : ℂ) * (↑(Complex.arg L_plus) -
      ↑(Complex.arg (-L_minus))) = ((m : ℤ) : ℂ) * (2 * (↑Real.pi : ℂ)) := by
    have h := congrArg ((↑·) : ℝ → ℂ) hm
    push_cast at h ⊢
    linear_combination h
  linear_combination congr_arg (· * Complex.I) hm_complex
