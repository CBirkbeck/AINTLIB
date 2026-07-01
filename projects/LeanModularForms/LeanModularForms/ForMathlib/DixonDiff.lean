/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.DixonDef
import LeanModularForms.ForMathlib.DslopeIntegral
import LeanModularForms.ForMathlib.NullHomologous
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Dixon Function Differentiability

This file proves the Dixon h2 function is holomorphic off the curve, the h1 function is
holomorphic on U, and the full Dixon function is entire, using the parametric Leibniz rule
for differentiation under the integral sign.

## Main results

* `dixonH2_differentiableAt` -- h2 is holomorphic at every point off the curve image
* `dixonH1_differentiableOn` -- h1 is holomorphic on U
* `dixonFunction_differentiable` -- the Dixon function is entire

## References

* J. D. Dixon, *A brief proof of Cauchy's integral theorem*, 1971
-/

open Complex Set Filter Topology MeasureTheory
open scoped Classical Real Interval

noncomputable section

variable {x : ℂ}

private lemma curveImage_compact (γ : PiecewiseC1Path x x) :
    IsCompact (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
  isCompact_Icc.image γ.toPath.continuous_extend

private lemma curveImage_nonempty (γ : PiecewiseC1Path x x) :
    (γ.toPath.extend '' Icc (0 : ℝ) 1).Nonempty :=
  ⟨γ.toPath.extend 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩

private lemma curveImage_infDist_pos (γ : PiecewiseC1Path x x) (w : ℂ)
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    0 < Metric.infDist w (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
  ((curveImage_compact γ).isClosed.notMem_iff_infDist_pos (curveImage_nonempty γ)).mp
    fun ⟨t, ht, heq⟩ ↦ hoff t ht heq

private lemma ball_avoids_curve (γ : PiecewiseC1Path x x) (w : ℂ)
    {ε : ℝ} (hε : 0 < ε)
    (hε_le : 2 * ε ≤ Metric.infDist w (γ.toPath.extend '' Icc (0 : ℝ) 1)) :
    ∀ w' ∈ Metric.ball w ε, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w' := by
  intro w' hw' t ht heq
  have h1 := Metric.infDist_le_dist_of_mem (x := w)
    (show γ t ∈ γ.toPath.extend '' Icc (0 : ℝ) 1 from ⟨t, ht, rfl⟩)
  rw [heq] at h1
  linarith [Metric.mem_ball.mp hw', dist_comm w' w]

private lemma ball_dist_lower_bound (γ : PiecewiseC1Path x x) (w : ℂ)
    {ε : ℝ} (hε_le : 2 * ε ≤ Metric.infDist w (γ.toPath.extend '' Icc (0 : ℝ) 1)) :
    ∀ w' ∈ Metric.ball w ε, ∀ t ∈ Icc (0 : ℝ) 1, ε ≤ ‖γ t - w'‖ := by
  intro w' hw' t ht
  have h1 := Metric.infDist_le_dist_of_mem (x := w)
    (show γ t ∈ γ.toPath.extend '' Icc (0 : ℝ) 1 from ⟨t, ht, rfl⟩)
  rw [Complex.dist_eq] at h1
  have h2 := Metric.mem_ball.mp hw'
  rw [Complex.dist_eq] at h2
  have h5 := norm_sub_norm_le (γ t - w) (γ t - w')
  rw [show (γ t - w) - (γ t - w') = w' - w by ring] at h5
  linarith [norm_sub_rev w' w, norm_sub_rev w (γ t)]

private lemma h2_pointwise_hasDerivAt (fz c z w : ℂ) (hne : z - w ≠ 0) :
    HasDerivAt (fun w' ↦ fz * (z - w')⁻¹ * c)
      (fz * (z - w)⁻¹ ^ 2 * c) w := by
  have h_sub : HasDerivAt (fun w' ↦ z - w') (-1) w :=
    HasDerivAt.const_sub z (hasDerivAt_id w)
  have h_inv : HasDerivAt (fun w' ↦ (z - w')⁻¹) ((z - w)⁻¹ ^ 2) w := by
    have h := HasDerivAt.inv h_sub hne
    rw [show (- -1 / (z - w) ^ 2 : ℂ) = (z - w)⁻¹ ^ 2 by rw [inv_pow]; ring] at h
    exact h
  exact ((h_inv.const_mul fz).mul_const c).congr_deriv (by ring)

private lemma h2_integrand_norm_bound {f : ℂ → ℂ} {γ : PiecewiseC1Path x x}
    {M ε D : ℝ} (hM_nn : 0 ≤ M) (hε_pos : 0 < ε)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ t)‖ ≤ M)
    (hD : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ.toPath.extend t‖ ≤ D)
    (h_dist_lb : ∀ w' ∈ Metric.ball w ε,
      ∀ t ∈ Icc (0 : ℝ) 1, ε ≤ ‖γ t - w'‖)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) {w' : ℂ} (hw' : w' ∈ Metric.ball w ε) :
    ‖f (γ t) * (γ t - w')⁻¹ ^ 2 * deriv γ.toPath.extend t‖ ≤ M * ε⁻¹ ^ 2 * D := by
  have ht_Icc := Ioc_subset_Icc_self ht
  rw [norm_mul, norm_mul, norm_pow, norm_inv]
  exact mul_le_mul
    (mul_le_mul (hM t ht_Icc)
      (pow_le_pow_left₀ (by positivity)
        (inv_anti₀ hε_pos (h_dist_lb w' hw' t ht_Icc)) 2)
      (by positivity) hM_nn)
    (hD t ht_Icc) (by positivity) (mul_nonneg hM_nn (by positivity))

/-- A product `g · γ'` is a.e. strongly measurable on `Ι 0 1` whenever `g` is
continuous on `[0,1]`; the derivative factor is strongly measurable. -/
private lemma aestronglyMeasurable_mul_deriv {γ : PiecewiseC1Path x x} {g : ℝ → ℂ}
    (hg : ContinuousOn g (Icc (0 : ℝ) 1)) :
    AEStronglyMeasurable (fun t ↦ g t * deriv γ.toPath.extend t)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
  rw [Set.uIoc_of_le (zero_le_one' ℝ)]
  exact ((hg.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc).mul
    (stronglyMeasurable_deriv _).aestronglyMeasurable

/-- **h2 is holomorphic at every point off the curve.**

Uses the parametric Leibniz rule (differentiation under the integral sign).
The integrability, bounds, and measurability hypotheses are provided externally
since they depend on the curve's regularity structure. -/
theorem dixonH2_differentiableAt {f : ℂ → ℂ}
    {γ : PiecewiseC1Path x x} {w : ℂ}
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w)
    (h_int : IntervalIntegrable
      (fun t ↦ f (γ t) * (γ t - w)⁻¹ * deriv γ.toPath.extend t) volume 0 1)
    (h_fγ_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ t)‖ ≤ M)
    (h_deriv_bound : ∃ D : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ.toPath.extend t‖ ≤ D)
    (h_meas : ∀ w' ∈ Metric.ball w
        (Metric.infDist w (γ.toPath.extend '' Icc (0 : ℝ) 1) / 2),
      AEStronglyMeasurable
        (fun t ↦ f (γ t) * (γ t - w')⁻¹ * deriv γ.toPath.extend t)
        (volume.restrict (Set.uIoc 0 1)))
    (h_F'_meas : AEStronglyMeasurable
      (fun t ↦ f (γ t) * (γ t - w)⁻¹ ^ 2 * deriv γ.toPath.extend t)
      (volume.restrict (Set.uIoc 0 1))) :
    DifferentiableAt ℂ (dixonH2 f γ) w := by
  have hid_pos := curveImage_infDist_pos γ w hoff
  set ε := Metric.infDist w (γ.toPath.extend '' Icc (0 : ℝ) 1) / 2
  have hε_pos : 0 < ε := by positivity
  have h2ε : 2 * ε ≤ Metric.infDist w (γ.toPath.extend '' Icc (0 : ℝ) 1) := by
    simp only [ε]; linarith
  obtain ⟨M, hM_nn, hM⟩ := h_fγ_bound
  obtain ⟨D, hD⟩ := h_deriv_bound
  have h_ball_avoids := ball_avoids_curve γ w hε_pos h2ε
  have h_dist_lb := ball_dist_lower_bound γ w h2ε
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun w' t ↦ f (γ t) * (γ t - w')⁻¹ * deriv γ.toPath.extend t)
    (F' := fun w' t ↦ f (γ t) * (γ t - w')⁻¹ ^ 2 * deriv γ.toPath.extend t)
    (bound := fun _ ↦ M * ε⁻¹ ^ 2 * D)
    (Metric.ball_mem_nhds w hε_pos)
    (by
      filter_upwards [Metric.ball_mem_nhds w hε_pos] with w' hw'
      exact h_meas w' hw')
    h_int h_F'_meas
    (by filter_upwards with t ht w' hw'
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact h2_integrand_norm_bound hM_nn hε_pos hM hD h_dist_lb ht hw')
    (intervalIntegrable_const (c := M * ε⁻¹ ^ 2 * D))
    (by filter_upwards with t ht w' hw'
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact h2_pointwise_hasDerivAt (f (γ t)) (deriv γ.toPath.extend t) (γ t) w'
          (sub_ne_zero.mpr (h_ball_avoids w' hw' t (Ioc_subset_Icc_self ht))))).2.differentiableAt

private lemma dixonH2_integrand_stronglyMeasurable
    {f : ℂ → ℂ} {γ : PiecewiseC1Path x x} {w' : ℂ}
    (hf_cont : ContinuousOn f (γ.toPath.extend '' Icc (0 : ℝ) 1))
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w') :
    AEStronglyMeasurable
      (fun t ↦ f (γ t) * (γ t - w')⁻¹ * deriv γ.toPath.extend t)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
  aestronglyMeasurable_mul_deriv <|
    (hf_cont.comp γ.toPath.continuous_extend.continuousOn fun t ht ↦ ⟨t, ht, rfl⟩).mul
      (ContinuousOn.inv₀ (γ.toPath.continuous_extend.continuousOn.sub continuousOn_const)
        fun t ht ↦ sub_ne_zero.mpr (hoff t ht))

private lemma dixonH2_deriv_integrand_stronglyMeasurable
    {f : ℂ → ℂ} {γ : PiecewiseC1Path x x} {w : ℂ}
    (hf_cont : ContinuousOn f (γ.toPath.extend '' Icc (0 : ℝ) 1))
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    AEStronglyMeasurable
      (fun t ↦ f (γ t) * (γ t - w)⁻¹ ^ 2 * deriv γ.toPath.extend t)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
  aestronglyMeasurable_mul_deriv <|
    (hf_cont.comp γ.toPath.continuous_extend.continuousOn fun t ht ↦ ⟨t, ht, rfl⟩).mul
      ((ContinuousOn.inv₀ (γ.toPath.continuous_extend.continuousOn.sub continuousOn_const)
        fun t ht ↦ sub_ne_zero.mpr (hoff t ht)).pow 2)

/-- **B-3 bundle**: `dixonH2` is holomorphic at points off the curve, from simple
continuity + Lipschitz regularity hypotheses.

Discharges the six oracles of `dixonH2_differentiableAt`:
* `h_int`, `h_F'_meas`, `h_meas` — via strong measurability + bounds (finite volume)
* `h_fγ_bound` — from continuity of `f ∘ γ` on compact `Icc 0 1`
* `h_deriv_bound` — from `LipschitzWith K γ.extend` via `norm_deriv_le_of_lipschitz`. -/
theorem dixonH2_differentiableAt_of_regular {f : ℂ → ℂ}
    {γ : PiecewiseC1Path x x} {w : ℂ}
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w)
    (hf_cont : ContinuousOn f (γ.toPath.extend '' Icc (0 : ℝ) 1))
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    DifferentiableAt ℂ (dixonH2 f γ) w := by
  have hD : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ.toPath.extend t‖ ≤ K :=
    fun _ _ ↦ norm_deriv_le_of_lipschitz hLip
  have h_fγ_cont : ContinuousOn (fun t ↦ f (γ t)) (Icc (0 : ℝ) 1) :=
    hf_cont.comp γ.toPath.continuous_extend.continuousOn (fun t ht ↦ ⟨t, ht, rfl⟩)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).bddAbove_image h_fγ_cont.norm
  have hM_bd : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (γ t)‖ ≤ max M 0 :=
    fun t ht ↦ le_max_of_le_left (hM ⟨t, ht, rfl⟩)
  have hM₀_nn : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  have h_F'_meas := dixonH2_deriv_integrand_stronglyMeasurable hf_cont hoff
  set ε := Metric.infDist w (γ.toPath.extend '' Icc (0 : ℝ) 1) / 2
  have hε_pos : 0 < ε := by
    have := curveImage_infDist_pos γ w hoff; positivity
  have h2ε : 2 * ε ≤ Metric.infDist w (γ.toPath.extend '' Icc (0 : ℝ) 1) := by
    simp only [ε]; linarith
  have h_ball_avoids := ball_avoids_curve γ w hε_pos h2ε
  have h_meas : ∀ w' ∈ Metric.ball w ε,
      AEStronglyMeasurable (fun t ↦ f (γ t) * (γ t - w')⁻¹ *
        deriv γ.toPath.extend t) (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    fun w' hw' ↦ dixonH2_integrand_stronglyMeasurable hf_cont (h_ball_avoids w' hw')
  have h_ε_lb := ball_dist_lower_bound γ w h2ε w (Metric.mem_ball_self hε_pos)
  have h_int : IntervalIntegrable
      (fun t ↦ f (γ t) * (γ t - w)⁻¹ * deriv γ.toPath.extend t) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have h_meas_Ioc : AEStronglyMeasurable
        (fun t ↦ f (γ t) * (γ t - w)⁻¹ * deriv γ.toPath.extend t)
        (volume.restrict (Ioc (0 : ℝ) 1)) := by
      have := dixonH2_integrand_stronglyMeasurable hf_cont hoff
      rwa [Set.uIoc_of_le (zero_le_one' ℝ)] at this
    haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    refine MeasureTheory.Integrable.of_bound h_meas_Ioc (max M 0 * ε⁻¹ * K) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht_Icc : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    rw [norm_mul, norm_mul, norm_inv]
    exact mul_le_mul
      (mul_le_mul (hM_bd t ht_Icc) (inv_anti₀ hε_pos (h_ε_lb t ht_Icc))
        (by positivity) hM₀_nn)
      (hD t ht_Icc) (norm_nonneg _)
      (mul_nonneg hM₀_nn (inv_nonneg.mpr hε_pos.le))
  exact dixonH2_differentiableAt hoff h_int ⟨max M 0, hM₀_nn, hM_bd⟩ ⟨K, hD⟩
    h_meas h_F'_meas

private lemma dslope_comm (f : ℂ → ℂ) (a b : ℂ) : dslope f a b = dslope f b a := by
  by_cases h : b = a
  · rw [h]
  · rw [dslope_of_ne f h, dslope_of_ne f (Ne.symm h), slope_comm]

private lemma dslope_hasDerivAt_first_arg {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {c w : ℂ} (hc : c ∈ U) (hw : w ∈ U) :
    HasDerivAt (fun w' ↦ dslope f w' c) (deriv (dslope f c) w) w :=
  (((Complex.differentiableOn_dslope (hU.mem_nhds hc)).mpr hf w hw).differentiableAt
    (hU.mem_nhds hw)).hasDerivAt.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦ dslope_comm f _ _)

private lemma dslope_fixed_continuousOn {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {γ : PiecewiseC1Path x x} (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    {w : ℂ} (hw : w ∈ U) :
    ContinuousOn (fun t ↦ dslope f w (γ t)) (Icc (0 : ℝ) 1) :=
  ((Complex.differentiableOn_dslope (hU.mem_nhds hw)).mpr hf).continuousOn.comp
    γ.toPath.continuous_extend.continuousOn hγ

private lemma min3_ball_subsets (w₀ : ℂ) {ε_m ε_d δ_C : ℝ}
    (hε_m_pos : 0 < ε_m) (hε_d_pos : 0 < ε_d) (hδ_C_pos : 0 < δ_C) :
    let ε := min (min ε_m ε_d) δ_C / 2
    (0 < ε) ∧
    (Metric.ball w₀ ε ⊆ Metric.ball w₀ ε_m) ∧
    (Metric.ball w₀ ε ⊆ Metric.ball w₀ ε_d) ∧
    (Metric.ball w₀ ε ⊆ Metric.ball w₀ δ_C) := by
  refine ⟨by positivity,
    Metric.ball_subset_ball (by linarith [min_le_left (min ε_m ε_d) δ_C, min_le_left ε_m ε_d]),
    Metric.ball_subset_ball
      (by linarith [min_le_left (min ε_m ε_d) δ_C, min_le_right ε_m ε_d]),
    Metric.ball_subset_ball (by linarith [min_le_right (min ε_m ε_d) δ_C])⟩

private lemma dslope_deriv_product_bound
    {C D : ℝ} {γ : PiecewiseC1Path x x}
    (h_deriv_bd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Metric.ball w₀ δ_C,
      ‖deriv (dslope f (γ t)) w‖ ≤ C)
    (hD : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ.toPath.extend t‖ ≤ D)
    (hball_sub : Metric.ball w₀ ε ⊆ Metric.ball w₀ δ_C) :
    ∀ᵐ t, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ w ∈ Metric.ball w₀ ε,
      ‖deriv (dslope f (γ t)) w * deriv γ.toPath.extend t‖ ≤ C * D := by
  filter_upwards with t ht w hw
  rw [Set.uIoc_of_le zero_le_one] at ht
  have ht_Icc := Ioc_subset_Icc_self ht
  rw [norm_mul]
  exact mul_le_mul (h_deriv_bd t ht_Icc w (hball_sub hw)) (hD t ht_Icc)
    (norm_nonneg _) (le_trans (norm_nonneg _) (h_deriv_bd t ht_Icc w (hball_sub hw)))

/-- **h1 is holomorphic on U.**

Uses the parametric Leibniz rule with Cauchy estimates for the derivative of dslope. -/
theorem dixonH1_differentiableOn {f : ℂ → ℂ} {U : Set ℂ}
    (_hU : IsOpen U) (_hf : DifferentiableOn ℂ f U)
    (γ : PwC1Immersion x x) (_hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ∈ U)
    (h_int : ∀ w ∈ U, IntervalIntegrable
      (fun t ↦ dslope f w (γ.toPiecewiseC1Path t) *
        deriv γ.toPiecewiseC1Path.toPath.extend t) volume 0 1)
    (h_meas : ∀ w₀ ∈ U, ∃ ε > 0, ∀ w ∈ Metric.ball w₀ ε,
      AEStronglyMeasurable
        (fun t ↦ dslope f w (γ.toPiecewiseC1Path t) *
          deriv γ.toPiecewiseC1Path.toPath.extend t)
        (volume.restrict (Set.uIoc 0 1)))
    (h_deriv_bound : ∃ D : ℝ, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖deriv γ.toPiecewiseC1Path.toPath.extend t‖ ≤ D)
    (h_dslope_hasDerivAt : ∀ w₀ ∈ U, ∃ ε > 0,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Metric.ball w₀ ε,
        HasDerivAt (fun w' ↦ dslope f w' (γ.toPiecewiseC1Path t) *
          deriv γ.toPiecewiseC1Path.toPath.extend t)
          (deriv (dslope f (γ.toPiecewiseC1Path t)) w *
            deriv γ.toPiecewiseC1Path.toPath.extend t) w)
    (h_F'_meas : ∀ w₀ ∈ U, AEStronglyMeasurable
      (fun t ↦ deriv (dslope f (γ.toPiecewiseC1Path t)) w₀ *
        deriv γ.toPiecewiseC1Path.toPath.extend t) (volume.restrict (Set.uIoc 0 1)))
    (h_dslope_deriv_bound : ∀ w₀ ∈ U, ∃ C > 0, ∃ δ > 0,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Metric.ball w₀ δ,
        ‖deriv (dslope f (γ.toPiecewiseC1Path t)) w‖ ≤ C) :
    DifferentiableOn ℂ (dixonH1 f γ.toPiecewiseC1Path) U := by
  intro w₀ hw₀
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨D, hD⟩ := h_deriv_bound
  obtain ⟨ε_m, hε_m_pos, h_meas_ball⟩ := h_meas w₀ hw₀
  obtain ⟨ε_d, hε_d_pos, h_dslope_hda⟩ := h_dslope_hasDerivAt w₀ hw₀
  obtain ⟨C, hC_pos, δ_C, hδ_C_pos, h_deriv_bd⟩ := h_dslope_deriv_bound w₀ hw₀
  obtain ⟨hε_pos, hball_sub_εm, hball_sub_εd, hball_sub_δC⟩ :=
    min3_ball_subsets w₀ hε_m_pos hε_d_pos hδ_C_pos
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun w t ↦ dslope f w (γ.toPiecewiseC1Path t) *
      deriv γ.toPiecewiseC1Path.toPath.extend t)
    (F' := fun w t ↦ deriv (dslope f (γ.toPiecewiseC1Path t)) w *
      deriv γ.toPiecewiseC1Path.toPath.extend t)
    (bound := fun _ ↦ C * D) (Metric.ball_mem_nhds w₀ hε_pos)
    (by filter_upwards [Metric.ball_mem_nhds w₀ hε_pos] with w hw
        exact h_meas_ball w (hball_sub_εm hw))
    (h_int w₀ hw₀) (h_F'_meas w₀ hw₀)
    (dslope_deriv_product_bound h_deriv_bd hD hball_sub_δC)
    (intervalIntegrable_const (c := C * D))
    (by
      filter_upwards with t ht w hw
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact h_dslope_hda t (Ioc_subset_Icc_self ht) w (hball_sub_εd hw))).2.differentiableAt

private lemma dixonH1_integrand_stronglyMeasurable
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {γ : PiecewiseC1Path x x} (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    {w : ℂ} (hw : w ∈ U) :
    AEStronglyMeasurable
      (fun t ↦ dslope f w (γ t) * deriv γ.toPath.extend t)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
  aestronglyMeasurable_mul_deriv (dslope_fixed_continuousOn hU hf hγ hw)

/-- **B-2 partial bundle**: `dixonH1 f γ` is differentiable on `U` when
f is differentiable on open U, γ is a PwC1Immersion with image in U, and
γ.toPath.extend is Lipschitz, given two remaining oracle hypotheses on the
second-order structure of `dslope`:

* `h_F'_meas` — measurability of `t ↦ deriv (dslope f (γt)) w₀`
* `h_dslope_deriv_bound` — local uniform bound on `deriv (dslope f (γt)) w`.

Auto-discharges the other 5 oracles of `dixonH1_differentiableOn`:
* `h_int`, `h_meas` — via strong measurability + bounded + finite volume
* `_h_dslope_bound` — via continuity of dslope on compact γ.image
* `h_deriv_bound` — via `norm_deriv_le_of_lipschitz`
* `h_dslope_hasDerivAt` — via `dslope_hasDerivAt_first_arg`. -/
theorem dixonH1_differentiableOn_of_regular {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PwC1Immersion x x) (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ∈ U)
    {K : NNReal} (hLip : LipschitzWith K γ.toPiecewiseC1Path.toPath.extend)
    (h_F'_meas : ∀ w₀ ∈ U, AEStronglyMeasurable
      (fun t ↦ deriv (dslope f (γ.toPiecewiseC1Path t)) w₀ *
        deriv γ.toPiecewiseC1Path.toPath.extend t)
      (volume.restrict (Set.uIoc 0 1)))
    (h_dslope_deriv_bound : ∀ w₀ ∈ U, ∃ C > 0, ∃ δ > 0,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Metric.ball w₀ δ,
        ‖deriv (dslope f (γ.toPiecewiseC1Path t)) w‖ ≤ C) :
    DifferentiableOn ℂ (dixonH1 f γ.toPiecewiseC1Path) U := by
  have h_int : ∀ w ∈ U, IntervalIntegrable
      (fun t ↦ dslope f w (γ.toPiecewiseC1Path t) *
        deriv γ.toPiecewiseC1Path.toPath.extend t) volume 0 1 := by
    intro w hw
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have h_meas : AEStronglyMeasurable
        (fun t ↦ dslope f w (γ.toPiecewiseC1Path t) *
          deriv γ.toPiecewiseC1Path.toPath.extend t)
        (volume.restrict (Ioc (0 : ℝ) 1)) := by
      have := dixonH1_integrand_stronglyMeasurable hU hf hγ hw
      rwa [Set.uIoc_of_le (zero_le_one' ℝ)] at this
    haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).bddAbove_image
      (dslope_fixed_continuousOn hU hf hγ hw).norm
    refine MeasureTheory.Integrable.of_bound h_meas (max C 0 * K) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht_Icc : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    rw [norm_mul]
    refine mul_le_mul (le_max_of_le_left (hC ⟨t, ht_Icc, rfl⟩))
      (norm_deriv_le_of_lipschitz hLip) (norm_nonneg _)
      (le_max_of_le_left (le_trans (norm_nonneg _) (hC ⟨t, ht_Icc, rfl⟩)))
  have h_meas : ∀ w₀ ∈ U, ∃ ε > 0, ∀ w ∈ Metric.ball w₀ ε,
      AEStronglyMeasurable
        (fun t ↦ dslope f w (γ.toPiecewiseC1Path t) *
          deriv γ.toPiecewiseC1Path.toPath.extend t)
        (volume.restrict (Set.uIoc 0 1)) := by
    intro w₀ hw₀
    obtain ⟨ε, hε_pos, hball_sub⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
    exact ⟨ε, hε_pos, fun w hw ↦
      dixonH1_integrand_stronglyMeasurable hU hf hγ (hball_sub hw)⟩
  have h_dslope_hasDerivAt : ∀ w₀ ∈ U, ∃ ε > 0,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Metric.ball w₀ ε,
        HasDerivAt (fun w' ↦ dslope f w' (γ.toPiecewiseC1Path t) *
          deriv γ.toPiecewiseC1Path.toPath.extend t)
          (deriv (dslope f (γ.toPiecewiseC1Path t)) w *
            deriv γ.toPiecewiseC1Path.toPath.extend t) w := by
    intro w₀ hw₀
    obtain ⟨ε, hε_pos, hball_sub⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
    refine ⟨ε, hε_pos, fun t ht w hw ↦ ?_⟩
    exact (dslope_hasDerivAt_first_arg hU hf (hγ t ht) (hball_sub hw)).mul_const _
  exact dixonH1_differentiableOn hU hf γ hγ h_int h_meas
    ⟨K, fun _ _ ↦ norm_deriv_le_of_lipschitz hLip⟩ h_dslope_hasDerivAt h_F'_meas
    h_dslope_deriv_bound

/-- **B-2 bundle with D-1c auto-discharge for general open U** (no `Convex`):
auto-discharges `h_dslope_deriv_bound` via the non-convex
`Complex.deriv_dslope_bounded_on_compact_open`, leaving only `h_F'_meas` as
remaining oracle. -/
theorem dixonH1_differentiableOn_of_regular_open {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PwC1Immersion x x) (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ∈ U)
    {K : NNReal} (hLip : LipschitzWith K γ.toPiecewiseC1Path.toPath.extend)
    (h_F'_meas : ∀ w₀ ∈ U, AEStronglyMeasurable
      (fun t ↦ deriv (dslope f (γ.toPiecewiseC1Path t)) w₀ *
        deriv γ.toPiecewiseC1Path.toPath.extend t)
      (volume.restrict (Set.uIoc 0 1))) :
    DifferentiableOn ℂ (dixonH1 f γ.toPiecewiseC1Path) U := by
  have h_γ_compact : IsCompact (γ.toPiecewiseC1Path.toPath.extend '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image γ.toPiecewiseC1Path.toPath.continuous_extend
  have h_γ_sub : γ.toPiecewiseC1Path.toPath.extend '' Icc (0 : ℝ) 1 ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact hγ t ht
  have h_dslope_deriv_bound : ∀ w₀ ∈ U, ∃ C > 0, ∃ δ > 0,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Metric.ball w₀ δ,
        ‖deriv (dslope f (γ.toPiecewiseC1Path t)) w‖ ≤ C := by
    intro w₀ hw₀
    obtain ⟨C, hC_pos, δ, hδ_pos, h_bd⟩ :=
      Complex.deriv_dslope_bounded_on_compact_open hU hf h_γ_compact h_γ_sub hw₀
    exact ⟨C, hC_pos, δ, hδ_pos, fun t ht w hw ↦
      h_bd (γ.toPiecewiseC1Path t) ⟨t, ht, rfl⟩ w hw⟩
  exact dixonH1_differentiableOn_of_regular hU hf γ hγ hLip h_F'_meas h_dslope_deriv_bound

private lemma dslope_deriv_mul_extend_aestronglyMeasurable
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PwC1Immersion x x) (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ∈ U)
    {w₀ : ℂ} (hw₀ : w₀ ∈ U) :
    AEStronglyMeasurable
      (fun t ↦ deriv (dslope f (γ.toPiecewiseC1Path t)) w₀ *
        deriv γ.toPiecewiseC1Path.toPath.extend t)
      (volume.restrict (Set.uIoc 0 1)) := by
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
  set h_seq : ℕ → ℂ := fun n ↦ ((ρ / 2 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have h_seq_real_pos : ∀ n : ℕ, 0 < ρ / 2 / ((n : ℝ) + 1) := fun _ ↦ by positivity
  have h_seq_ne : ∀ n : ℕ, h_seq n ≠ 0 := fun n ↦ by
    simp only [h_seq, ne_eq, Complex.ofReal_eq_zero]; exact (h_seq_real_pos n).ne'
  have h_seq_norm_lt : ∀ n : ℕ, ‖h_seq n‖ < ρ := fun n ↦ by
    simp only [h_seq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (h_seq_real_pos n)]
    linarith [div_le_self (a := ρ / 2) (by linarith) (by linarith [Nat.cast_nonneg (α := ℝ) n] :
      (1 : ℝ) ≤ (n : ℝ) + 1)]
  have h_w_in_U : ∀ n : ℕ, w₀ + h_seq n ∈ U := fun n ↦ hρ_sub <| by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact h_seq_norm_lt n
  have h_seq_tendsto : Tendsto h_seq atTop (𝓝 0) := by
    have h_real : Tendsto (fun n : ℕ ↦ ρ / 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).inv_tendsto_atTop).const_mul
          (ρ / 2)
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from rfl]
    exact (Complex.continuous_ofReal.tendsto _).comp h_real
  set q : ℕ → ℝ → ℂ := fun n t ↦
    (dslope f (γ.toPiecewiseC1Path t) (w₀ + h_seq n) -
     dslope f (γ.toPiecewiseC1Path t) w₀) / h_seq n *
    deriv γ.toPiecewiseC1Path.toPath.extend t
  have h_γ_cont : Continuous (γ.toPiecewiseC1Path : ℝ → ℂ) :=
    γ.toPiecewiseC1Path.toPath.continuous_extend
  have h_q_aemeas : ∀ n : ℕ,
      AEStronglyMeasurable (q n) (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    intro n
    have h_factor1 : ContinuousOn
        (fun t : ℝ ↦
          (dslope f (γ.toPiecewiseC1Path t) (w₀ + h_seq n) -
           dslope f (γ.toPiecewiseC1Path t) w₀) / h_seq n)
        (Icc (0 : ℝ) 1) := by
      refine ContinuousOn.div_const ?_ _
      refine ContinuousOn.sub ?_ ?_
      · exact (Complex.continuousOn_dslope_first_arg_open hU hf
          (h_w_in_U n)).comp h_γ_cont.continuousOn hγ
      · exact (Complex.continuousOn_dslope_first_arg_open hU hf hw₀).comp
          h_γ_cont.continuousOn hγ
    have h_factor1_meas : AEStronglyMeasurable
        (fun t : ℝ ↦
          (dslope f (γ.toPiecewiseC1Path t) (w₀ + h_seq n) -
           dslope f (γ.toPiecewiseC1Path t) w₀) / h_seq n)
        (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
      rw [Set.uIoc_of_le (zero_le_one' ℝ)]
      exact (h_factor1.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    exact h_factor1_meas.mul (stronglyMeasurable_deriv _).aestronglyMeasurable
  refine aestronglyMeasurable_of_tendsto_ae atTop h_q_aemeas ?_
  have h_uIoc : Set.uIoc (0 : ℝ) 1 = Ioc 0 1 := Set.uIoc_of_le zero_le_one
  filter_upwards [ae_restrict_mem
    (h_uIoc ▸ measurableSet_Ioc : MeasurableSet (Set.uIoc (0 : ℝ) 1))] with t ht
  rw [h_uIoc] at ht
  have ht_Icc : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
  have h_diff : DifferentiableAt ℂ (dslope f (γ.toPiecewiseC1Path t)) w₀ :=
    ((Complex.differentiableOn_dslope (hU.mem_nhds (hγ t ht_Icc))).mpr
      hf w₀ hw₀).differentiableAt (hU.mem_nhds hw₀)
  have hy_within : Tendsto (fun n ↦ w₀ + h_seq n) atTop (𝓝[≠] w₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using h_seq_tendsto.const_add w₀,
      Eventually.of_forall fun n h ↦
        h_seq_ne n (add_left_cancel (a := w₀) (h.trans (add_zero w₀).symm))⟩
  have h_q_eq : ∀ n, q n t =
      (slope (dslope f (γ.toPiecewiseC1Path t)) w₀ (w₀ + h_seq n)) *
        deriv γ.toPiecewiseC1Path.toPath.extend t := fun n ↦ by
    simp only [q, slope_def_field]
    rw [show w₀ + h_seq n - w₀ = h_seq n by ring, div_eq_inv_mul,
      mul_comm (h_seq n)⁻¹]
  simp_rw [h_q_eq]
  exact (h_diff.hasDerivAt.tendsto_slope.comp hy_within).mul_const _

/-- **B-2 fully closed for general open U** (no `Convex` hypothesis): same conclusion
as `dixonH1_differentiableOn_of_regular_convex_full` but on any open `U`. -/
theorem dixonH1_differentiableOn_of_regular_open_full {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PwC1Immersion x x) (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ∈ U)
    {K : NNReal} (hLip : LipschitzWith K γ.toPiecewiseC1Path.toPath.extend) :
    DifferentiableOn ℂ (dixonH1 f γ.toPiecewiseC1Path) U :=
  dixonH1_differentiableOn_of_regular_open hU hf γ hγ hLip
    (fun _ ↦ dslope_deriv_mul_extend_aestronglyMeasurable hU hf γ hγ)

/-- **The Dixon function is entire.**

On `U`: equals `h1`, which is holomorphic.
Off `U`: equals `h2`, which is holomorphic. The curve lies in `U`, so
off `U` means off the curve.
Patching at `boundary(U)`: null-homologous gives winding number 0 near `boundary(U)`,
so `h1 = h2` by the fundamental identity. -/
theorem dixonFunction_differentiable {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (_hf : DifferentiableOn ℂ f U)
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    (h1_diff : DifferentiableOn ℂ (dixonH1 f γ.toPiecewiseC1Path) U)
    (h2_diff : ∀ w, (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      DifferentiableAt ℂ (dixonH2 f γ.toPiecewiseC1Path) w)
    (h_identity : ∀ w, (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      dixonH1 f γ.toPiecewiseC1Path w =
        dixonH2 f γ.toPiecewiseC1Path w -
          2 * ↑Real.pi * I * generalizedWindingNumber γ.toPiecewiseC1Path w * f w)
    (h_winding_zero_near : ∀ w, w ∉ U →
      (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) →
      ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
        generalizedWindingNumber γ.toPiecewiseC1Path w' = 0) :
    Differentiable ℂ (dixonFunction f U γ.toPiecewiseC1Path) := by
  intro w
  by_cases hw : w ∈ U
  · exact (h1_diff.differentiableAt (hU.mem_nhds hw)).congr_of_eventuallyEq
      (Filter.Eventually.mono (hU.mem_nhds hw) fun w' hw' ↦ dixonFunction_eq_dixonH1 hw')
  · have hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w :=
      fun t ht heq ↦ hw (heq ▸ h_null.image_subset t ht)
    obtain ⟨ε₁, hε₁_pos, hwn_zero⟩ := h_winding_zero_near w hw hoff
    have hid_pos := curveImage_infDist_pos γ.toPiecewiseC1Path w hoff
    set ε₂ := Metric.infDist w (γ.toPiecewiseC1Path.toPath.extend '' Icc (0 : ℝ) 1) / 2
    have hε₂_pos : 0 < ε₂ := by positivity
    set ε := min ε₁ ε₂
    have hε_pos : 0 < ε := lt_min hε₁_pos hε₂_pos
    have h_wn_zero : ∀ w' ∈ Metric.ball w ε,
        generalizedWindingNumber γ.toPiecewiseC1Path w' = 0 :=
      fun w' hw' ↦ hwn_zero w' (Metric.ball_subset_ball (min_le_left _ _) hw')
    have hoff' : ∀ w' ∈ Metric.ball w ε,
        ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w' :=
      ball_avoids_curve γ.toPiecewiseC1Path w (lt_min hε₁_pos hε₂_pos) (by
        simp only [ε, ε₂]
        nlinarith [min_le_right ε₁
          (Metric.infDist w (γ.toPiecewiseC1Path.toPath.extend '' Icc (0 : ℝ) 1) / 2)])
    have heq_near : ∀ᶠ w' in 𝓝 w,
        dixonFunction f U γ.toPiecewiseC1Path w' =
          dixonH2 f γ.toPiecewiseC1Path w' := by
      apply Filter.Eventually.mono (Metric.ball_mem_nhds w hε_pos)
      intro w' hw'
      simp only [dixonFunction]
      split_ifs with hw'U
      · rw [h_identity w' (hoff' w' hw'), h_wn_zero w' hw']; ring
      · rfl
    exact (h2_diff w hoff).congr_of_eventuallyEq heq_near

end
