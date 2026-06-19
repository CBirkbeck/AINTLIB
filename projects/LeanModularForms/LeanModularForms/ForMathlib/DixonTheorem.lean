/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.DixonDiff
import Mathlib.Analysis.Complex.Liouville

/-!
# Dixon Theorem: the Dixon Function is Identically Zero

This file proves the Dixon theorem: for a null-homologous curve in an open set `U` with
`f` holomorphic on `U`, the Dixon function is identically zero. The proof combines:

1. Entireness of the Dixon function (from `DixonDiff.lean`)
2. A norm bound showing `dixonH2 f γ w → 0` as `‖w‖ → ∞`
3. An eventual agreement: `dixonFunction = dixonH2` for large `‖w‖`
4. Liouville's theorem: entire + tends to 0 at infinity → identically zero

## Main results

* `dixonH2_norm_le` -- norm bound: `‖dixonH2 f γ w‖ ≤ M_f · M_d / (‖w‖ - R)`
* `dixonH2_tendsto_zero` -- `dixonH2 f γ` tends to 0 along `cocompact ℂ`
* `dixonFunction_eq_zero_of_nullHomologous_convex_full` -- the Dixon function is zero
  for null-homologous curves in convex bounded open `U` (canonical statement)
* `dixonFunction_eq_zero_of_nullHomologous_open_full` -- same for general bounded open `U`
* `dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded` -- same for general open `U`
  with Lipschitz `γ` (no boundedness requirement on `U`)

## Proof strategy

The Dixon function `h` is defined piecewise: `h1` on `U`, `h2` off `U`.
By `dixonFunction_differentiable`, `h` is entire (the pieces match on the overlap).

To show `h → 0` at infinity, we use:
- For `w ∉ U`: `h(w) = h2(w)` by definition, and `‖h2(w)‖ ≤ M/(‖w‖ - R) → 0`.
- For `w ∈ U` with `n(γ,w) = 0`: the `h1/h2` identity gives `h1 = h2`.
- Eventually all points satisfy one of these (the winding number is 0 for large `‖w‖`).

Then `Differentiable.apply_eq_of_tendsto_cocompact` (Liouville) gives `h ≡ 0`.

The Cauchy integral formula follows: at `w ∈ U` off the curve, `0 = h1(w) = h2(w) - 2πi·n·f(w)`,
so `h2(w) = 2πi · n(γ,w) · f(w)`.

## References

* J. D. Dixon, *A brief proof of Cauchy's integral theorem*, 1971
* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set Filter Topology MeasureTheory
open scoped Classical Real Interval

noncomputable section

variable {x : ℂ}

/-! ## Norm bound for dixonH2 -/

/-- Cocompact membership: `{w : ℂ | R < ‖w‖}` belongs to the cocompact filter. -/
private lemma norm_gt_mem_cocompact (R : ℝ) :
    {w : ℂ | R < ‖w‖} ∈ Filter.cocompact ℂ :=
  Filter.mem_cocompact.mpr ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R,
    fun _ hw ↦ by simpa using hw⟩

/-- A function differentiable on an open set `U` is continuous on the image of a
null-homologous curve in `U`. -/
private lemma continuousOn_curveImage_of_nullHomologous
    {f : ℂ → ℂ} {U : Set ℂ} (hf : DifferentiableOn ℂ f U)
    {γ : PwC1Immersion x x} (h_null : IsNullHomologous γ U) :
    ContinuousOn f (γ.toPiecewiseC1Path.toPath.extend '' Icc (0 : ℝ) 1) :=
  hf.continuousOn.mono (fun _ ⟨t, ht, heq⟩ ↦ heq ▸ h_null.image_subset t ht)

/-- **Norm bound for `dixonH2`.**

When `‖w‖ > R ≥ sup_t ‖γ(t)‖`, the Cauchy-type integral satisfies
`‖dixonH2 f γ w‖ ≤ M_f · M_d / (‖w‖ - R)`, where `M_f` bounds `‖f ∘ γ‖` and `M_d`
bounds `‖γ'‖` on `[0, 1]`. -/
theorem dixonH2_norm_le {f : ℂ → ℂ} {γ : PiecewiseC1Path x x}
    {R M_f M_d : ℝ} (hM_f_nn : 0 ≤ M_f)
    (hR : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t‖ ≤ R)
    (hM_f : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ.toPath.extend t‖ ≤ M_d)
    {w : ℂ} (hw : R < ‖w‖) :
    ‖dixonH2 f γ w‖ ≤ M_f * M_d / (‖w‖ - R) := by
  simp only [dixonH2]
  have hpos : 0 < ‖w‖ - R := by linarith
  have h_ptwise : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖f (γ t) / (γ t - w) * deriv γ.toPath.extend t‖ ≤ M_f * M_d / (‖w‖ - R) := by
    intro t ht_ui
    have ht : t ∈ Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le (zero_le_one' ℝ)] at ht_ui
      exact Ioc_subset_Icc_self ht_ui
    rw [norm_mul, norm_div]
    have h_dist_lb : ‖w‖ - R ≤ ‖γ t - w‖ := by
      linarith [norm_sub_norm_le w (γ t), norm_sub_rev w (γ t), hR t ht]
    calc ‖f (γ t)‖ / ‖γ t - w‖ * ‖deriv γ.toPath.extend t‖
        ≤ M_f / (‖w‖ - R) * M_d := by gcongr; exacts [hM_f t ht, hM_d t ht]
      _ = M_f * M_d / (‖w‖ - R) := by ring
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const h_ptwise

/-! ## dixonH2 tends to zero at infinity -/

/-- **`dixonH2 f γ` tends to 0 along `cocompact ℂ`.**

For `‖w‖` large enough, `‖dixonH2 f γ w‖ ≤ M_f · M_d / (‖w‖ - R) → 0`. -/
theorem dixonH2_tendsto_zero {f : ℂ → ℂ} {γ : PiecewiseC1Path x x}
    {R M_f M_d : ℝ} (hM_f_nn : 0 ≤ M_f)
    (hR : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t‖ ≤ R)
    (hM_f : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ.toPath.extend t‖ ≤ M_d) :
    Tendsto (dixonH2 f γ) (Filter.cocompact ℂ) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  simp only [dist_zero_right]
  filter_upwards [norm_gt_mem_cocompact (max R (R + M_f * M_d / ε))] with
    w (hw : max R (R + M_f * M_d / ε) < ‖w‖)
  have hRw : R < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) hw
  calc ‖dixonH2 f γ w‖
      ≤ M_f * M_d / (‖w‖ - R) := dixonH2_norm_le hM_f_nn hR hM_f hM_d hRw
    _ < ε := by
        rw [div_lt_iff₀ (by linarith : 0 < ‖w‖ - R)]
        have h2 : M_f * M_d / ε < ‖w‖ - R := by
          linarith [lt_of_le_of_lt (le_max_right _ _) hw]
        rw [div_lt_iff₀ hε] at h2
        linarith [mul_comm ε (‖w‖ - R)]

/-! ## Dixon function tends to zero -/

/-- **The Dixon function tends to 0 along `cocompact ℂ`**, given that it eventually agrees
with `dixonH2` and `dixonH2` tends to 0.

The eventual agreement `dixonFunction = dixonH2` holds because:
- Off `U`: `dixonFunction = dixonH2` by definition.
- On `U` with winding number 0: the `h1/h2` identity gives `h1 = h2`. -/
theorem dixonFunction_tendsto_zero {f : ℂ → ℂ} {U : Set ℂ}
    {γ : PiecewiseC1Path x x}
    (h_evt : ∀ᶠ w in Filter.cocompact ℂ,
      dixonFunction f U γ w = dixonH2 f γ w)
    {R M_f M_d : ℝ} (hM_f_nn : 0 ≤ M_f)
    (hR : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t‖ ≤ R)
    (hM_f : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ.toPath.extend t‖ ≤ M_d) :
    Tendsto (dixonFunction f U γ) (Filter.cocompact ℂ) (nhds 0) :=
  (dixonH2_tendsto_zero hM_f_nn hR hM_f hM_d).congr' (Filter.EventuallyEq.symm h_evt)

/-! ## Dixon function is identically zero (Liouville) -/

/-- **The Dixon function is identically zero (Liouville's theorem).**

If the Dixon function is entire and tends to 0 at infinity, then it is identically zero.
This is a direct application of `Differentiable.apply_eq_of_tendsto_cocompact`. -/
private theorem dixonFunction_eq_zero {f : ℂ → ℂ} {U : Set ℂ}
    {γ : PiecewiseC1Path x x}
    (h_entire : Differentiable ℂ (dixonFunction f U γ))
    (h_tendsto : Tendsto (dixonFunction f U γ) (Filter.cocompact ℂ) (nhds 0)) :
    ∀ w, dixonFunction f U γ w = 0 :=
  fun w ↦ h_entire.apply_eq_of_tendsto_cocompact w h_tendsto

/-- **Assembled version**: the Dixon function is zero when given entireness, eventual
agreement with `h2`, and curve bounds. -/
private theorem dixonFunction_eq_zero_of_bounds {f : ℂ → ℂ} {U : Set ℂ}
    {γ : PiecewiseC1Path x x}
    (h_entire : Differentiable ℂ (dixonFunction f U γ))
    (h_evt : ∀ᶠ w in Filter.cocompact ℂ,
      dixonFunction f U γ w = dixonH2 f γ w)
    {R M_f M_d : ℝ} (hM_f_nn : 0 ≤ M_f)
    (hR : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t‖ ≤ R)
    (hM_f : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ.toPath.extend t‖ ≤ M_d) :
    ∀ w, dixonFunction f U γ w = 0 :=
  dixonFunction_eq_zero h_entire
    (dixonFunction_tendsto_zero h_evt hM_f_nn hR hM_f hM_d)

/-! ## Eventually h2 for null-homologous curves -/

/-- The Dixon function eventually agrees with `dixonH2` for null-homologous curves,
given that the winding number is eventually zero and the `h1 = h2 - 2πi·n·f(w)` identity
holds for off-curve points.

For `w ∉ U`: `dixonFunction = dixonH2` by definition.
For `w ∈ U` with `n(γ,w) = 0`: the identity gives `h1 = h2`. -/
theorem dixonFunction_eventually_eq_dixonH2 {f : ℂ → ℂ} {U : Set ℂ}
    (γ : PwC1Immersion x x)
    (h_identity : ∀ w, (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      dixonH1 f γ.toPiecewiseC1Path w =
        dixonH2 f γ.toPiecewiseC1Path w -
          2 * ↑Real.pi * I * generalizedWindingNumber γ.toPiecewiseC1Path w * f w)
    (h_winding_evt : ∀ᶠ w in Filter.cocompact ℂ,
      (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) ∧
        generalizedWindingNumber γ.toPiecewiseC1Path w = 0) :
    ∀ᶠ w in Filter.cocompact ℂ,
      dixonFunction f U γ.toPiecewiseC1Path w =
        dixonH2 f γ.toPiecewiseC1Path w := by
  filter_upwards [h_winding_evt] with w ⟨hoff, hwn⟩
  simp only [dixonFunction]
  split_ifs
  · simp [h_identity w hoff, hwn]
  · rfl

/-! ## Cauchy integral formula -/

/-- **Cauchy integral formula from pointwise Dixon-zero.** Requires only
`dixonFunction f U γ w = 0` at the specific point `w` (not globally). -/
private theorem cauchyIntegralFormula_nullHomologous_at {f : ℂ → ℂ} {U : Set ℂ}
    {γ : PiecewiseC1Path x x}
    {w : ℂ} (h_zero_at : dixonFunction f U γ w = 0)
    (hw : w ∈ U) (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w)
    (h_cauchy_int : IntervalIntegrable
      (fun t ↦ f (γ t) / (γ t - w) * deriv γ.toPath.extend t) volume 0 1)
    (h_base_int : IntervalIntegrable
      (fun t ↦ (γ t - w)⁻¹ * deriv γ.toPath.extend t) volume 0 1) :
    dixonH2 f γ w =
      2 * ↑Real.pi * I * generalizedWindingNumber γ w * f w := by
  rw [dixonFunction_eq_dixonH1 hw] at h_zero_at
  have h_identity := dixonH1_eq_dixonH2_sub_winding_f w hoff h_cauchy_int h_base_int
  rw [h_zero_at] at h_identity
  exact sub_eq_zero.mp h_identity.symm

/-! ## Cauchy's theorem for null-homologous curves: `∮_γ f = 0` -/

/-- **Pointwise version of Cauchy's theorem for null-homologous curves.**
Requires only `dixonFunction ((z-w₀)·f) U γ w₀ = 0` at the single point `w₀`,
rather than globally. This is strictly weaker: for a corrected remainder
`g_cor` that agrees with `f-pp` on `U\S`, the pointwise Dixon-zero at `w₀`
(where `w₀ ∉ S`) transfers directly.

The proof uses the classical trick: apply the Cauchy integral formula to
`g(z) := (z - w₀) · f(z)`. Since `g(w₀) = 0`, the formula gives
`dixonH2 g γ w₀ = 2πi · n(γ, w₀) · g(w₀) = 0`. But
`dixonH2 g γ w₀ = ∮_γ g(z)/(z - w₀) dz = ∮_γ f(z) dz` because γ avoids `w₀`. -/
theorem contourIntegral_eq_zero_of_nullHomologous_at
    {f : ℂ → ℂ} {U : Set ℂ} {γ : PiecewiseC1Path x x}
    (w₀ : ℂ) (hw₀_in_U : w₀ ∈ U)
    (hw₀_off : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w₀)
    (h_zero_at : dixonFunction (fun z ↦ (z - w₀) * f z) U γ w₀ = 0)
    (h_cauchy_int : IntervalIntegrable
      (fun t ↦ (γ t - w₀) * f (γ t) / (γ t - w₀) *
        deriv γ.toPath.extend t) volume 0 1)
    (h_base_int : IntervalIntegrable
      (fun t ↦ (γ t - w₀)⁻¹ * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f = 0 := by
  have h_cif := cauchyIntegralFormula_nullHomologous_at
    (f := fun z ↦ (z - w₀) * f z) h_zero_at
    hw₀_in_U hw₀_off h_cauchy_int h_base_int
  simp only [sub_self, zero_mul, mul_zero] at h_cif
  refine h_cif ▸ ?_
  simp only [dixonH2, PiecewiseC1Path.contourIntegral]
  refine intervalIntegral.integral_congr (fun t ht ↦ ?_)
  rw [Set.uIcc_of_le (zero_le_one' ℝ)] at ht
  rw [mul_div_cancel_left₀ _ (sub_ne_zero.mpr (hw₀_off t ht))]

/-- **B-5 aggregator: the Dixon function is zero for null-homologous curves.**

Bundles the Dixon machinery into a single theorem taking only the following oracle-
style hypotheses (to be discharged separately by tickets B-1, B-2, B-3 and integrability):

* `h1_diff` — `dixonH1 f γ` is differentiable on `U` (B-2)
* `h2_diff` — `dixonH2 f γ` is differentiable off the curve (B-3)
* `h_cauchy_int`, `h_base_int` — integrability for the `h1 = h2 - 2πi·n·f` identity
* `h_winding_evt` — winding is eventually 0 in `cocompact ℂ` (B-1 cocompact version)

Conclusion: `∀ w, dixonFunction f U γ w = 0`.

Downstream: `contourIntegral_eq_zero_of_nullHomologous` applied to the twisted function
`(z - w₀) · f` gives Cauchy's theorem. -/
private theorem dixonFunction_eq_zero_of_nullHomologous
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U)
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    (h1_diff : DifferentiableOn ℂ (dixonH1 f γ.toPiecewiseC1Path) U)
    (h2_diff : ∀ w, (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      DifferentiableAt ℂ (dixonH2 f γ.toPiecewiseC1Path) w)
    (h_cauchy_int : ∀ w, (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      IntervalIntegrable (fun t ↦ f (γ.toPiecewiseC1Path t) /
        (γ.toPiecewiseC1Path t - w) *
        deriv γ.toPiecewiseC1Path.toPath.extend t) volume 0 1)
    (h_base_int : ∀ w, (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      IntervalIntegrable (fun t ↦ (γ.toPiecewiseC1Path t - w)⁻¹ *
        deriv γ.toPiecewiseC1Path.toPath.extend t) volume 0 1)
    (h_winding_zero_near : ∀ w, w ∉ U →
      (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
        generalizedWindingNumber γ.toPiecewiseC1Path w' = 0)
    (h_winding_evt : ∀ᶠ w in Filter.cocompact ℂ,
      (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) ∧
        generalizedWindingNumber γ.toPiecewiseC1Path w = 0)
    {R M_f M_d : ℝ} (hM_f_nn : 0 ≤ M_f)
    (hR : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ.toPiecewiseC1Path t‖ ≤ R)
    (hM_f : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ.toPiecewiseC1Path t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖deriv γ.toPiecewiseC1Path.toPath.extend t‖ ≤ M_d) :
    ∀ w, dixonFunction f U γ.toPiecewiseC1Path w = 0 := by
  have h_id : ∀ w, (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      dixonH1 f γ.toPiecewiseC1Path w =
        dixonH2 f γ.toPiecewiseC1Path w -
          2 * ↑Real.pi * I * generalizedWindingNumber γ.toPiecewiseC1Path w * f w :=
    fun w hoff ↦ dixonH1_eq_dixonH2_sub_winding_f w hoff
      (h_cauchy_int w hoff) (h_base_int w hoff)
  exact dixonFunction_eq_zero_of_bounds
    (dixonFunction_differentiable hU hf γ h_null h1_diff h2_diff h_id
      h_winding_zero_near)
    (dixonFunction_eventually_eq_dixonH2 γ h_id h_winding_evt)
    hM_f_nn hR hM_f hM_d

/-! ### Unbounded U variants (TIGHT-12)

Parallel to the `_bounded` chain, but discharging the cocompact-winding-zero
hypothesis via `winding_eventually_zero_cocompact_of_lipschitz` (which uses
γ being Lipschitz, not U being bounded). This lifts the `hU_bounded`
restriction in Dixon-based theorems. -/

/-- **B-5 variant for unbounded U with Lipschitz γ**:
`dixonFunction_eq_zero_of_nullHomologous` specialized to the case where U
need not be bounded but γ is Lipschitz. The cocompact-winding-zero hypothesis
is discharged via `winding_eventually_zero_cocompact_of_lipschitz`. -/
private theorem dixonFunction_eq_zero_of_nullHomologous_unbounded
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U)
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    {K : NNReal} (hLip : LipschitzWith K γ.toPiecewiseC1Path.toPath.extend)
    (h1_diff : DifferentiableOn ℂ (dixonH1 f γ.toPiecewiseC1Path) U)
    (h2_diff : ∀ w, (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      DifferentiableAt ℂ (dixonH2 f γ.toPiecewiseC1Path) w)
    (h_cauchy_int : ∀ w, (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      IntervalIntegrable (fun t ↦ f (γ.toPiecewiseC1Path t) /
        (γ.toPiecewiseC1Path t - w) *
        deriv γ.toPiecewiseC1Path.toPath.extend t) volume 0 1)
    (h_base_int : ∀ w, (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      IntervalIntegrable (fun t ↦ (γ.toPiecewiseC1Path t - w)⁻¹ *
        deriv γ.toPiecewiseC1Path.toPath.extend t) volume 0 1)
    (h_winding_zero_near : ∀ w, w ∉ U →
      (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
        generalizedWindingNumber γ.toPiecewiseC1Path w' = 0)
    {R M_f M_d : ℝ} (hM_f_nn : 0 ≤ M_f)
    (hR : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ.toPiecewiseC1Path t‖ ≤ R)
    (hM_f : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ.toPiecewiseC1Path t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖deriv γ.toPiecewiseC1Path.toPath.extend t‖ ≤ M_d) :
    ∀ w, dixonFunction f U γ.toPiecewiseC1Path w = 0 :=
  dixonFunction_eq_zero_of_nullHomologous hU hf γ h_null h1_diff h2_diff
    h_cauchy_int h_base_int h_winding_zero_near
    (winding_eventually_zero_cocompact_of_lipschitz hLip)
    hM_f_nn hR hM_f hM_d

/-- Cauchy-type integrand `f(γ t)/(γ t - w) · γ'(t)` is interval-integrable on `[0,1]`
when `f ∘ γ` and `γ` are continuous and `γ` is Lipschitz with bound `K`. -/
private lemma cauchy_integrand_intervalIntegrable
    {f : ℂ → ℂ} {γ : PiecewiseC1Path x x} {K : NNReal}
    (hLip : LipschitzWith K γ.toPath.extend)
    (h_fγ_cont : ContinuousOn (fun t ↦ f (γ t)) (Icc (0 : ℝ) 1))
    (h_γ_cont : ContinuousOn (γ : ℝ → ℂ) (Icc (0 : ℝ) 1))
    {w : ℂ} (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    IntervalIntegrable
      (fun t ↦ f (γ t) / (γ t - w) * deriv γ.toPath.extend t) volume 0 1 := by
  have h_cont_inv : ContinuousOn (fun t ↦ (γ t - w)⁻¹) (Icc (0 : ℝ) 1) :=
    ContinuousOn.inv₀ (h_γ_cont.sub continuousOn_const)
      (fun t ht ↦ sub_ne_zero.mpr (hoff t ht))
  have h_cont_prod : ContinuousOn (fun t ↦ f (γ t) / (γ t - w)) (Icc (0 : ℝ) 1) := by
    simp_rw [div_eq_mul_inv]
    exact h_fγ_cont.mul h_cont_inv
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have h_meas : AEStronglyMeasurable
      (fun t ↦ f (γ t) / (γ t - w) * deriv γ.toPath.extend t)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((h_cont_prod.mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc).mul (stronglyMeasurable_deriv _).aestronglyMeasurable
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).bddAbove_image h_cont_prod.norm
  refine MeasureTheory.Integrable.of_bound h_meas (max C 0 * K) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht_Icc : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
  rw [norm_mul]
  exact mul_le_mul (le_max_of_le_left (hC ⟨t, ht_Icc, rfl⟩))
    (norm_deriv_le_of_lipschitz hLip) (norm_nonneg _)
    (le_max_of_le_left (le_trans (norm_nonneg _) (hC ⟨t, ht_Icc, rfl⟩)))

/-- Base integrand `(γ t - w)⁻¹ · γ'(t)` is interval-integrable on `[0,1]` when `γ` is
continuous and Lipschitz with bound `K`. -/
private lemma base_integrand_intervalIntegrable
    {γ : PiecewiseC1Path x x} {K : NNReal}
    (hLip : LipschitzWith K γ.toPath.extend)
    (h_γ_cont : ContinuousOn (γ : ℝ → ℂ) (Icc (0 : ℝ) 1))
    {w : ℂ} (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    IntervalIntegrable
      (fun t ↦ (γ t - w)⁻¹ * deriv γ.toPath.extend t) volume 0 1 := by
  have := cauchy_integrand_intervalIntegrable (f := fun _ ↦ 1) hLip
    continuousOn_const h_γ_cont hoff
  simpa [one_div] using this

/-- **B-5 autoH2 variant for unbounded U with Lipschitz γ.** -/
private theorem dixonFunction_eq_zero_of_nullHomologous_autoH2_unbounded
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U)
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    {K : NNReal} (hLip : LipschitzWith K γ.toPiecewiseC1Path.toPath.extend)
    (h1_diff : DifferentiableOn ℂ (dixonH1 f γ.toPiecewiseC1Path) U)
    (h_cauchy_int : ∀ w, (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      IntervalIntegrable (fun t ↦ f (γ.toPiecewiseC1Path t) /
        (γ.toPiecewiseC1Path t - w) *
        deriv γ.toPiecewiseC1Path.toPath.extend t) volume 0 1)
    (h_base_int : ∀ w, (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      IntervalIntegrable (fun t ↦ (γ.toPiecewiseC1Path t - w)⁻¹ *
        deriv γ.toPiecewiseC1Path.toPath.extend t) volume 0 1)
    (h_winding_zero_near : ∀ w, w ∉ U →
      (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
        generalizedWindingNumber γ.toPiecewiseC1Path w' = 0)
    {R M_f M_d : ℝ} (hM_f_nn : 0 ≤ M_f)
    (hR : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ.toPiecewiseC1Path t‖ ≤ R)
    (hM_f : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ.toPiecewiseC1Path t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖deriv γ.toPiecewiseC1Path.toPath.extend t‖ ≤ M_d) :
    ∀ w, dixonFunction f U γ.toPiecewiseC1Path w = 0 := by
  have hf_cont := continuousOn_curveImage_of_nullHomologous hf h_null
  have h2_diff : ∀ w, (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      DifferentiableAt ℂ (dixonH2 f γ.toPiecewiseC1Path) w :=
    fun _ hoff ↦ dixonH2_differentiableAt_of_regular hoff hf_cont hLip
  exact dixonFunction_eq_zero_of_nullHomologous_unbounded hU hf γ h_null hLip
    h1_diff h2_diff h_cauchy_int h_base_int h_winding_zero_near
    hM_f_nn hR hM_f hM_d

/-- **B-5 autoBounds variant for unbounded U with Lipschitz γ.** -/
private theorem dixonFunction_eq_zero_of_nullHomologous_autoBounds_unbounded
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U)
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    {K : NNReal} (hLip : LipschitzWith K γ.toPiecewiseC1Path.toPath.extend)
    (h1_diff : DifferentiableOn ℂ (dixonH1 f γ.toPiecewiseC1Path) U)
    (h_winding_zero_near : ∀ w, w ∉ U →
      (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
        generalizedWindingNumber γ.toPiecewiseC1Path w' = 0) :
    ∀ w, dixonFunction f U γ.toPiecewiseC1Path w = 0 := by
  have hf_cont := continuousOn_curveImage_of_nullHomologous hf h_null
  have h_fγ_cont : ContinuousOn
      (fun t ↦ f (γ.toPiecewiseC1Path t)) (Icc (0 : ℝ) 1) :=
    hf_cont.comp γ.toPiecewiseC1Path.toPath.continuous_extend.continuousOn
      (fun t ht ↦ ⟨t, ht, rfl⟩)
  have h_γ_cont : ContinuousOn (γ.toPiecewiseC1Path : ℝ → ℂ) (Icc (0 : ℝ) 1) :=
    γ.toPiecewiseC1Path.toPath.continuous_extend.continuousOn
  obtain ⟨R, hR_bd⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).bddAbove_image
    h_γ_cont.norm
  obtain ⟨M_f, hM_f_bd⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).bddAbove_image
    h_fγ_cont.norm
  have hR_curve : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ.toPiecewiseC1Path t‖ ≤ R :=
    fun t ht ↦ hR_bd ⟨t, ht, rfl⟩
  have hM_f_curve : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖f (γ.toPiecewiseC1Path t)‖ ≤ max M_f 0 :=
    fun t ht ↦ le_max_of_le_left (hM_f_bd ⟨t, ht, rfl⟩)
  have hM_f_nn : (0 : ℝ) ≤ max M_f 0 := le_max_right _ _
  have hM_d : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖deriv γ.toPiecewiseC1Path.toPath.extend t‖ ≤ K :=
    fun _ _ ↦ norm_deriv_le_of_lipschitz hLip
  exact dixonFunction_eq_zero_of_nullHomologous_autoH2_unbounded hU hf γ h_null
    hLip h1_diff
    (fun _ hoff ↦ cauchy_integrand_intervalIntegrable hLip h_fγ_cont h_γ_cont hoff)
    (fun _ hoff ↦ base_integrand_intervalIntegrable hLip h_γ_cont hoff)
    h_winding_zero_near hM_f_nn hR_curve hM_f_curve hM_d

/-- **B-5 fully closed for general open (possibly unbounded) U with Lipschitz γ.**
This is the unbounded analog of `dixonFunction_eq_zero_of_nullHomologous_open_full`. -/
theorem dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U)
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    {K : NNReal} (hLip : LipschitzWith K γ.toPiecewiseC1Path.toPath.extend)
    (h_winding_zero_near : ∀ w, w ∉ U →
      (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
        generalizedWindingNumber γ.toPiecewiseC1Path w' = 0) :
    ∀ w, dixonFunction f U γ.toPiecewiseC1Path w = 0 :=
  dixonFunction_eq_zero_of_nullHomologous_autoBounds_unbounded hU hf γ h_null
    hLip (dixonH1_differentiableOn_of_regular_open_full hU hf γ
      h_null.image_subset hLip) h_winding_zero_near

end
