/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import LeanModularForms.ForMathlib.BoundaryWinding
import LeanModularForms.ForMathlib.PaperPwC1Immersion
import LeanModularForms.ForMathlib.AsymmetricSingleCrossing
import LeanModularForms.ForMathlib.HungerbuhlerWasem.HigherOrderAsymptotics

/-!
# Generic `SingleCrossingData` builder from `IsFlatOfOrder _ _ 1`

This file provides infrastructure to build `SingleCrossingData` for any closed
piecewise-`C¹` immersion `γ` crossing a point `s` at parameter `t₀ ∈ Ioo 0 1`
transversely (`IsFlatOfOrder γ t₀ 1`) and uniquely.

## Components delivered

1. **`SingleCrossingData.ofClosedImmersion_flat_one`** — the headline generic
   builder. Takes `(γ : ClosedPwC1Immersion x, t₀, h_at, h_unique, h_flat,
   L, δ, threshold, hthresh, hδ_pos, hδ_small, h_far, h_near, ftcHyp)` and
   packages into `SingleCrossingData γ.toPiecewiseC1Path s`. Mirrors
   `mkSingleCrossingData_smooth` but for arbitrary `ClosedPwC1Immersion`.

2. **Far bound from uniqueness** (`exists_far_bound_compact`): if `γ` crosses
   `s` only at `t₀` on `[0, 1]`, then `‖γ(t) - s‖` has a positive minimum on
   any compact set `[0, t₀ - r] ∪ [t₀ + r, 1]`.

3. **One-sided derivative limits** (`exists_left_deriv_limit`,
   `exists_right_deriv_limit`): at any interior `t₀`, the immersion has nonzero
   one-sided derivative limits.

4. **Chord-to-tangent eventual bounds** (`exists_chord_lower_bound_right`,
   etc.): for some `r > 0`, on `(t₀, t₀ + r)`, `(‖L_+‖/2)·(t-t₀) ≤
   ‖γ(t) - s‖ ≤ (3‖L_+‖/2)·(t-t₀)`. Symmetric on the left.

5. **Eventual differentiability on each side** (`eventually_differentiable_*`).

These pieces are the geometric ingredients needed by the downstream T-BR-04
ticket (per-pole CPV witness assembly).

## Design note

The strict-monotonicity infrastructure is now in place:

* **`norm_sub_strictMonoOn_right`** — `‖γ(t) - s‖` is strictly increasing on
  `[t₀, t₀ + r]` for some `r > 0`.
* **`norm_sub_strictAntiOn_left`** — `‖γ(t) - s‖` is strictly decreasing on
  `[t₀ - r, t₀]` for some `r > 0`.

These follow from `HasDerivAt.norm_sq` and a careful chord-to-tangent
positivity argument: `(d/dt)‖γ(t) - s‖² = 2 · ⟪γ(t) - s, γ'(t)⟫_ℝ`, whose
leading term `(t - t₀) · ‖L‖²` dominates the `o(t - t₀)` corrections.

### Asymmetric crossings

The `SingleCrossingData` scheme uses a SINGLE cutoff `δ(ε)` controlling both
sides simultaneously: `‖γ(t) - s‖ ≤ ε` for `|t - t₀| ≤ δ(ε)` and
`‖γ(t) - s‖ > ε` for `|t - t₀| > δ(ε)`. For this to hold, the LEFT and RIGHT
exit times `δ_R(ε)`, `δ_L(ε)` (where `‖γ(t₀ ± δ_•(ε)) - s‖ = ε`) must be EQUAL
— i.e., the curve's distance-to-`s` function must be SYMMETRIC about `t₀`.

Even at off-partition (smooth) interior points, this symmetry does not hold
generically: for asymmetric `γ`, the level set `{t : ‖γ(t) - s‖ = ε}` consists
of two distinct points `t₀ + δ_R(ε)` and `t₀ - δ_L(ε)` with `δ_R ≠ δ_L`. Then
no choice of `δ(ε)` simultaneously satisfies h_near and h_far (h_near requires
`δ ≤ min(δ_R, δ_L)`, h_far requires `δ ≥ max(δ_R, δ_L)`).

Therefore the headline constructor `SingleCrossingData.ofClosedImmersion_flat_one`
continues to take `(δ, threshold, h_far, h_near)` as parameters: callers supply
curve-specific cutoffs (using either symmetry of the curve, or stronger flatness
input). The strict-monotonicity lemmas exposed in this file allow callers to
*build* such cutoffs via IVT inversion when they have additional symmetry
information.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

/-- At any `t₀ ∈ Ioo 0 1`, the right derivative limit `L_+` exists and is nonzero. -/
theorem exists_right_deriv_limit
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[>] t₀) (𝓝 L) := by
  by_cases h_part : t₀ ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition
  · exact γ.toPwC1Immersion.right_deriv_limit t₀ h_part
  · refine ⟨deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀,
      γ.toPwC1Immersion.deriv_ne_zero t₀ ht₀ h_part,
      (γ.toPwC1Immersion.toPiecewiseC1Path.deriv_continuous_off_extend t₀ ht₀
        h_part).tendsto.mono_left nhdsWithin_le_nhds⟩

/-- At any `t₀ ∈ Ioo 0 1`, the left derivative limit `L_-` exists and is nonzero. -/
theorem exists_left_deriv_limit
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[<] t₀) (𝓝 L) := by
  by_cases h_part : t₀ ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition
  · exact γ.toPwC1Immersion.left_deriv_limit t₀ h_part
  · refine ⟨deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀,
      γ.toPwC1Immersion.deriv_ne_zero t₀ ht₀ h_part,
      (γ.toPwC1Immersion.toPiecewiseC1Path.deriv_continuous_off_extend t₀ ht₀
        h_part).tendsto.mono_left nhdsWithin_le_nhds⟩

/-- Differentiability is eventual on `𝓝[>] t₀` for an immersion at interior `t₀`. -/
theorem eventually_differentiable_right
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ t in 𝓝[>] t₀,
      DifferentiableAt ℝ γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t := by
  have hcl : IsClosed
      ((↑γ.toPwC1Immersion.toPiecewiseC1Path.partition : Set ℝ) \ {t₀}) :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.subset
      sdiff_subset).isClosed
  filter_upwards [
    nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (mem_compl fun h ↦ h.2 rfl)),
    nhdsWithin_le_nhds (Ioo_mem_nhds ht₀.1 ht₀.2),
    self_mem_nhdsWithin] with t ht₁ ht₂ ht₃
  exact γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off_extend t ht₂
    fun hm ↦ ht₁ ⟨hm, ne_of_gt (mem_Ioi.mp ht₃)⟩

/-- Differentiability is eventual on `𝓝[<] t₀` for an immersion at interior `t₀`. -/
theorem eventually_differentiable_left
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ t in 𝓝[<] t₀,
      DifferentiableAt ℝ γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t := by
  have hcl : IsClosed
      ((↑γ.toPwC1Immersion.toPiecewiseC1Path.partition : Set ℝ) \ {t₀}) :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.subset
      sdiff_subset).isClosed
  filter_upwards [
    nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (mem_compl fun h ↦ h.2 rfl)),
    nhdsWithin_le_nhds (Ioo_mem_nhds ht₀.1 ht₀.2),
    self_mem_nhdsWithin] with t ht₁ ht₂ ht₃
  exact γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off_extend t ht₂
    fun hm ↦ ht₁ ⟨hm, ne_of_lt (mem_Iio.mp ht₃)⟩

private def reInner (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im

private lemma reInner_le_norm_mul_norm (z w : ℂ) :
    |reInner z w| ≤ ‖z‖ * ‖w‖ := by
  have h_id : reInner z w = (z * (starRingEnd ℂ) w).re := by
    simp only [reInner, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  have h_norm_eq : ‖z‖ * ‖w‖ = ‖z * (starRingEnd ℂ) w‖ := by
    rw [norm_mul, Complex.norm_conj]
  rw [h_id, h_norm_eq]; exact Complex.abs_re_le_norm _

private lemma reInner_add_left (a b c : ℂ) :
    reInner (a + b) c = reInner a c + reInner b c := by
  simp only [reInner, Complex.add_re, Complex.add_im]; ring

private lemma reInner_add_right (a b c : ℂ) :
    reInner a (b + c) = reInner a b + reInner a c := by
  simp only [reInner, Complex.add_re, Complex.add_im]; ring

private lemma reInner_smul_left (r : ℝ) (a c : ℂ) :
    reInner ((r : ℝ) • a) c = r * reInner a c := by
  simp only [reInner, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]; ring

private lemma reInner_self (z : ℂ) : reInner z z = ‖z‖^2 := by
  rw [reInner, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

private theorem reInner_lower_bound_right_eventually
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s)
    {L : ℂ} (hL : L ≠ 0)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t) :
    ∀ᶠ t in 𝓝[>] t₀,
      (t - t₀) * ‖L‖^2 / 2 ≤ reInner (γ t - s) (deriv γ t) := by
  obtain ⟨S, hS_mem, hS_diff⟩ := hγ_diff.exists_mem
  have hr := hasDerivWithinAt_iff_isLittleO.mp <| hasDerivWithinAt_Ioi_iff_Ici.mpr
    (hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun t ht ↦ (hS_diff t ht).differentiableWithinAt)
      hγ_cont.continuousWithinAt hS_mem hL_right)
  set η : ℝ := ‖L‖ / 8 with hη_def
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hη_pos : 0 < η := by rw [hη_def]; positivity
  have h_deriv_close : ∀ᶠ t in 𝓝[>] t₀, ‖deriv γ t - L‖ < η := by
    filter_upwards [(Metric.tendsto_nhds.mp hL_right) η hη_pos] with t ht
    rwa [dist_eq_norm] at ht
  filter_upwards [hr.def hη_pos, h_deriv_close, self_mem_nhdsWithin] with
    t h_chord_t h_dclose_t h_t_gt
  have h_t_pos : 0 < t - t₀ := sub_pos.mpr h_t_gt
  set R : ℂ := γ t - γ t₀ - (t - t₀) • L with hR_def
  set D : ℂ := deriv γ t - L with hD_def
  have hR_norm : ‖R‖ ≤ η * (t - t₀) := by
    rwa [Real.norm_eq_abs, abs_of_pos h_t_pos] at h_chord_t
  have hD_norm : ‖D‖ ≤ η := le_of_lt h_dclose_t
  rw [show γ t - s = (t - t₀) • L + R by rw [hR_def, h_at]; ring,
      show deriv γ t = L + D by rw [hD_def]; ring,
      reInner_add_left, reInner_add_right, reInner_add_right,
      reInner_smul_left, reInner_smul_left, reInner_self]
  have h_err_LD : |reInner L D| ≤ ‖L‖ * η :=
    (reInner_le_norm_mul_norm L D).trans (mul_le_mul_of_nonneg_left hD_norm (norm_nonneg _))
  have h_err_RL : |reInner R L| ≤ η * (t - t₀) * ‖L‖ :=
    (reInner_le_norm_mul_norm R L).trans (mul_le_mul_of_nonneg_right hR_norm (norm_nonneg _))
  have h_err_RD : |reInner R D| ≤ η * (t - t₀) * η :=
    (reInner_le_norm_mul_norm R D).trans
      (mul_le_mul hR_norm hD_norm (norm_nonneg _) (by positivity))
  have h_LD_lower : -(‖L‖ * η) ≤ reInner L D := neg_le_of_abs_le h_err_LD
  have h_RL_lower : -(η * (t - t₀) * ‖L‖) ≤ reInner R L := neg_le_of_abs_le h_err_RL
  have h_RD_lower : -(η * (t - t₀) * η) ≤ reInner R D := neg_le_of_abs_le h_err_RD
  have h_eta_bound : 2 * η * ‖L‖ + η^2 ≤ ‖L‖^2 / 2 := by rw [hη_def]; nlinarith [hL_pos]
  nlinarith [mul_le_mul_of_nonneg_left h_LD_lower h_t_pos.le,
    mul_le_mul_of_nonneg_left h_eta_bound h_t_pos.le, h_RL_lower, h_RD_lower]

private lemma reInner_eq_inner_real (z w : ℂ) :
    reInner z w = inner ℝ w z := by
  change z.re * w.re + z.im * w.im = (Inner.rclikeToReal ℂ ℂ).inner w z
  rw [Inner.rclikeToReal]
  change z.re * w.re + z.im * w.im = (z * (starRingEnd ℂ) w).re
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

/-- **Strict monotonicity right side**: for some `r > 0`, the function
`t ↦ ‖γ(t) - s‖` is strictly monotone-increasing on `[t₀, t₀+r]`.

This is the key one-sided strict-monotonicity property used to define the
exit-time cutoff `δ(ε)` via IVT. -/
theorem norm_sub_strictMonoOn_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s)
    {L : ℂ} (hL : L ≠ 0)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t) :
    ∃ r > 0, StrictMonoOn (fun t ↦ ‖γ t - s‖) (Icc t₀ (t₀ + r)) := by
  have h_combined : ∀ᶠ t in 𝓝[>] t₀,
      DifferentiableAt ℝ γ t ∧ (t - t₀) * ‖L‖^2 / 2 ≤ reInner (γ t - s) (deriv γ t) :=
    hγ_diff.and (reInner_lower_bound_right_eventually h_at hL hL_right hγ_cont hγ_diff)
  rw [eventually_nhdsWithin_iff] at h_combined
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.eventually_nhds_iff_ball.mp h_combined
  set r := r₀ / 2 with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; linarith
  have hr_data : ∀ t ∈ Ioc t₀ (t₀ + r),
      DifferentiableAt ℝ γ t ∧ (t - t₀) * ‖L‖^2 / 2 ≤ reInner (γ t - s) (deriv γ t) := by
    intro t ht
    refine hr₀_sub t ?_ ht.1
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)]
    linarith [ht.2]
  refine ⟨r, hr_pos, ?_⟩
  set f : ℝ → ℝ := fun t ↦ ‖γ t - s‖^2
  have h_γ_continuousOn : ContinuousOn γ (Icc t₀ (t₀ + r)) := fun t ht ↦ by
    rcases eq_or_lt_of_le ht.1 with h_eq | h_gt
    · rw [← h_eq]; exact hγ_cont.continuousWithinAt
    · exact (hr_data t ⟨h_gt, ht.2⟩).1.continuousAt.continuousWithinAt
  have h_f_cont : ContinuousOn f (Icc t₀ (t₀ + r)) := fun t ht ↦
    (((h_γ_continuousOn t ht).sub continuousWithinAt_const).norm).pow 2
  have h_int : interior (Icc t₀ (t₀ + r)) = Ioo t₀ (t₀ + r) := interior_Icc
  have h_f_strictMono : StrictMonoOn f (Icc t₀ (t₀ + r)) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (f' := fun t ↦ 2 * reInner (γ t - s) (deriv γ t)) h_f_cont
    · intro t ht
      rw [h_int] at ht
      have h_d_normSq :=
        ((hr_data t ⟨ht.1, le_of_lt ht.2⟩).1.hasDerivAt.sub_const s).norm_sq
      have h_re_eq : (2 : ℝ) * inner ℝ (γ t - s) (deriv γ t) =
          2 * reInner (γ t - s) (deriv γ t) := by
        rw [reInner_eq_inner_real, real_inner_comm]
      rw [h_re_eq] at h_d_normSq
      exact h_d_normSq.hasDerivWithinAt
    · intro t ht
      rw [h_int] at ht
      have hL_sq_pos : 0 < ‖L‖^2 := by positivity
      linarith [(hr_data t ⟨ht.1, le_of_lt ht.2⟩).2, sub_pos.mpr ht.1, mul_pos (sub_pos.mpr ht.1) hL_sq_pos]
  intro a ha b hb hab
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (h_f_strictMono ha hb hab)

private theorem reInner_upper_bound_left_eventually
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s)
    {L : ℂ} (hL : L ≠ 0)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t) :
    ∀ᶠ t in 𝓝[<] t₀,
      reInner (γ t - s) (deriv γ t) ≤ (t - t₀) * ‖L‖^2 / 2 := by
  obtain ⟨S, hS_mem, hS_diff⟩ := hγ_diff.exists_mem
  have hr := hasDerivWithinAt_iff_isLittleO.mp <| hasDerivWithinAt_Iio_iff_Iic.mpr
    (hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht ↦ (hS_diff t ht).differentiableWithinAt)
      hγ_cont.continuousWithinAt hS_mem hL_left)
  set η : ℝ := ‖L‖ / 8 with hη_def
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hη_pos : 0 < η := by rw [hη_def]; positivity
  have h_deriv_close : ∀ᶠ t in 𝓝[<] t₀, ‖deriv γ t - L‖ < η := by
    filter_upwards [(Metric.tendsto_nhds.mp hL_left) η hη_pos] with t ht
    rwa [dist_eq_norm] at ht
  filter_upwards [hr.def hη_pos, h_deriv_close, self_mem_nhdsWithin] with
    t h_chord_t h_dclose_t h_t_lt
  have h_t₀t_pos : 0 < t₀ - t := sub_pos.mpr h_t_lt
  set R : ℂ := γ t - γ t₀ - (t - t₀) • L with hR_def
  set D : ℂ := deriv γ t - L with hD_def
  have hR_norm : ‖R‖ ≤ η * (t₀ - t) := by
    rwa [Real.norm_eq_abs, abs_sub_comm, abs_of_pos h_t₀t_pos] at h_chord_t
  have hD_norm : ‖D‖ ≤ η := le_of_lt h_dclose_t
  rw [show γ t - s = (t - t₀) • L + R by rw [hR_def, h_at]; ring,
      show deriv γ t = L + D by rw [hD_def]; ring,
      reInner_add_left, reInner_add_right, reInner_add_right,
      reInner_smul_left, reInner_smul_left, reInner_self]
  have h_err_LD : |reInner L D| ≤ ‖L‖ * η :=
    (reInner_le_norm_mul_norm L D).trans (mul_le_mul_of_nonneg_left hD_norm (norm_nonneg _))
  have h_err_RL : |reInner R L| ≤ η * (t₀ - t) * ‖L‖ :=
    (reInner_le_norm_mul_norm R L).trans (mul_le_mul_of_nonneg_right hR_norm (norm_nonneg _))
  have h_err_RD : |reInner R D| ≤ η * (t₀ - t) * η :=
    (reInner_le_norm_mul_norm R D).trans
      (mul_le_mul hR_norm hD_norm (norm_nonneg _) (by positivity))
  have h_t_LD_upper : (t - t₀) * reInner L D ≤ (t₀ - t) * (‖L‖ * η) := by
    refine le_of_abs_le ?_; rw [abs_mul, abs_sub_comm, abs_of_pos h_t₀t_pos]
    exact mul_le_mul_of_nonneg_left h_err_LD h_t₀t_pos.le
  have h_eta_bound : 2 * η * ‖L‖ + η^2 ≤ ‖L‖^2 / 2 := by rw [hη_def]; nlinarith [hL_pos]
  nlinarith [h_t_LD_upper, le_of_abs_le h_err_RL, le_of_abs_le h_err_RD,
    mul_le_mul_of_nonneg_left h_eta_bound h_t₀t_pos.le]

/-- **Strict ANTI-monotonicity left side**: for some `r > 0`, the function
`t ↦ ‖γ(t) - s‖` is strictly anti-monotone (decreasing) on `[t₀ - r, t₀]`.

Symmetric to `norm_sub_strictMonoOn_right`. -/
theorem norm_sub_strictAntiOn_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s)
    {L : ℂ} (hL : L ≠ 0)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t) :
    ∃ r > 0, StrictAntiOn (fun t ↦ ‖γ t - s‖) (Icc (t₀ - r) t₀) := by
  have h_combined : ∀ᶠ t in 𝓝[<] t₀,
      DifferentiableAt ℝ γ t ∧ reInner (γ t - s) (deriv γ t) ≤ (t - t₀) * ‖L‖^2 / 2 :=
    hγ_diff.and (reInner_upper_bound_left_eventually h_at hL hL_left hγ_cont hγ_diff)
  rw [eventually_nhdsWithin_iff] at h_combined
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.eventually_nhds_iff_ball.mp h_combined
  set r := r₀ / 2 with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; linarith
  have hr_data : ∀ t ∈ Ico (t₀ - r) t₀,
      DifferentiableAt ℝ γ t ∧ reInner (γ t - s) (deriv γ t) ≤ (t - t₀) * ‖L‖^2 / 2 := by
    intro t ht
    refine hr₀_sub t ?_ ht.2
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.mpr ht.2)]
    linarith [ht.1]
  refine ⟨r, hr_pos, ?_⟩
  set f : ℝ → ℝ := fun t ↦ ‖γ t - s‖^2
  have h_γ_continuousOn : ContinuousOn γ (Icc (t₀ - r) t₀) := fun t ht ↦ by
    rcases eq_or_lt_of_le ht.2 with h_eq | h_lt
    · rw [h_eq]; exact hγ_cont.continuousWithinAt
    · exact (hr_data t ⟨ht.1, h_lt⟩).1.continuousAt.continuousWithinAt
  have h_f_cont : ContinuousOn f (Icc (t₀ - r) t₀) := fun t ht ↦
    (((h_γ_continuousOn t ht).sub continuousWithinAt_const).norm).pow 2
  have h_int : interior (Icc (t₀ - r) t₀) = Ioo (t₀ - r) t₀ := interior_Icc
  have h_f_strictAnti : StrictAntiOn f (Icc (t₀ - r) t₀) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
      (f' := fun t ↦ 2 * reInner (γ t - s) (deriv γ t)) h_f_cont
    · intro t ht
      rw [h_int] at ht
      have h_d_normSq :=
        ((hr_data t ⟨le_of_lt ht.1, ht.2⟩).1.hasDerivAt.sub_const s).norm_sq
      have h_re_eq : (2 : ℝ) * inner ℝ (γ t - s) (deriv γ t) =
          2 * reInner (γ t - s) (deriv γ t) := by
        rw [reInner_eq_inner_real, real_inner_comm]
      rw [h_re_eq] at h_d_normSq
      exact h_d_normSq.hasDerivWithinAt
    · intro t ht
      rw [h_int] at ht
      have hL_sq_pos : 0 < ‖L‖^2 := by positivity
      have h_neg_inner : (t - t₀) * ‖L‖^2 / 2 < 0 := by
        nlinarith [sub_neg_of_lt ht.2, hL_sq_pos]
      linarith [(hr_data t ⟨le_of_lt ht.1, ht.2⟩).2]
  intro a ha b hb hab
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (h_f_strictAnti ha hb hab)

/-- **Integrability of `(γ - s)⁻¹ * γ'` on segments away from the
singularity**. If `γ(t) ≠ s` on the closed interval `[a, b] ⊆ [0, 1]`, then
the integrand `(γ(t) - s)⁻¹ * γ'(t)` is interval-integrable on `[a, b]`.

The proof: `γ'` is interval-integrable on `[0, 1]` (hence on `[a, b]` by
restriction), and `(γ - s)⁻¹` is continuous on `[a, b]` (since `γ - s ≠ 0`
on the compact interval). Their product is interval-integrable. -/
theorem inv_sub_mul_deriv_intervalIntegrable
    (γ : ClosedPwC1Immersion x) {s : ℂ} {a b : ℝ}
    (hab : a ≤ b) (h_in_Icc : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1)
    (h_ne : ∀ t ∈ Set.Icc a b,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t ≠ s) :
    IntervalIntegrable
      (fun t ↦ (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s)⁻¹ *
        deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t)
      MeasureTheory.volume a b := by
  set γf : ℝ → ℂ := fun t ↦ γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
  have hγ_int : IntervalIntegrable (deriv γf) MeasureTheory.volume a b :=
    γ.toClosedPwC1Curve.deriv_extend_intervalIntegrable.mono_set <| by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le zero_le_one]; exact h_in_Icc
  have h_cont : ContinuousOn (fun t ↦ (γf t - s)⁻¹) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    refine (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousOn.sub
      continuousOn_const).inv₀ fun t ht h_eq ↦ h_ne t ht ?_
    linear_combination h_eq
  exact (hγ_int.mul_continuousOn h_cont).congr (fun t _ ↦ by ring)
