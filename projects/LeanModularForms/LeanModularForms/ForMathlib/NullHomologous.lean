/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.GeneralizedWindingNumber
import LeanModularForms.ForMathlib.CurveUtilities
import LeanModularForms.ForMathlib.WindingArgDiff

/-!
# Null-Homologous Curves

A closed piecewise C^1 immersion is **null-homologous** in an open set `U` when its image
lies in `U` and its winding number around every point outside `U` is zero. This is the
topological condition required by the generalized residue theorem of Hungerbuhler-Wasem.

## Main definitions

* `IsNullHomologous` -- null-homologous closed piecewise C^1 immersion in an open set.
  Closedness is encoded by `PwC1Immersion x x` (same start and end point).

## Main results

* `isNullHomologous_of_convex` -- every closed piecewise C^1 immersion in a convex open
  set is null-homologous.
* `IsNullHomologous.mono` -- monotonicity: null-homologous in `U` implies null-homologous
  in any superset `V ⊇ U`.
* `IsNullHomologous.closed` -- extract that the underlying path is closed (trivial since
  `x = x`).

## Design notes

We use `PwC1Immersion x x` to encode closedness: since the start and end points
are the same, the path is automatically closed. The `winding_zero` field uses the value
`generalizedWindingNumber` (not the `HasGeneralizedWindingNumber` predicate) because
downstream applications need the actual numerical value `0`.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

noncomputable section

variable {x : ℂ}

/-- A closed piecewise C^1 immersion `gamma` is null-homologous in an open set `U` if:
1. Its image lies in `U`.
2. Its winding number around every point outside `U` is zero.

Closedness is encoded by the type: `PwC1Immersion x x` has the same start and
end point. -/
structure IsNullHomologous (γ : PwC1Immersion x x) (U : Set ℂ) : Prop where
  /-- The image of `gamma` lies in `U`. -/
  image_subset : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ∈ U
  /-- The generalized winding number around every point outside `U` is zero. -/
  winding_zero : ∀ z, z ∉ U →
    generalizedWindingNumber γ.toPiecewiseC1Path z = 0

/-! ### Basic properties -/

/-- Monotonicity: if `gamma` is null-homologous in `U` and `U ⊆ V`, then `gamma` is
null-homologous in `V`. -/
theorem IsNullHomologous.mono {γ : PwC1Immersion x x} {U V : Set ℂ}
    (h : IsNullHomologous γ U) (hUV : U ⊆ V) : IsNullHomologous γ V where
  image_subset t ht := hUV (h.image_subset t ht)
  winding_zero z hz := h.winding_zero z (fun hmem => hz (hUV hmem))

/-! ### Auxiliary lemmas -/

/-- If a piecewise C^1 path avoids a point, there is a positive distance lower bound. -/
theorem avoids_delta_bound (γ : PiecewiseC1Path x x) (z₀ : ℂ)
    (h_avoids : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ z₀) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - z₀‖ := by
  have h_compact : IsCompact (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image γ.toPath.continuous_extend
  have h_nonempty : (γ.toPath.extend '' Icc (0 : ℝ) 1).Nonempty :=
    ⟨γ.toPath.extend 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩
  have h_not_mem : z₀ ∉ γ.toPath.extend '' Icc (0 : ℝ) 1 :=
    fun ⟨t, ht, heq⟩ => h_avoids t ht heq
  have h_pos : 0 < Metric.infDist z₀ (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
    (h_compact.isClosed.notMem_iff_infDist_pos h_nonempty).mp h_not_mem
  exact ⟨_, h_pos, fun t ht => by
    calc Metric.infDist z₀ _ ≤ dist z₀ (γ.toPath.extend t) :=
          Metric.infDist_le_dist_of_mem (mem_image_of_mem _ ht)
      _ = ‖γ.toPath.extend t - z₀‖ := by rw [Complex.dist_eq, norm_sub_rev]⟩


/-! ### Lipschitz implies bounded image -/

/-- Lipschitz `γ.toPath.extend` on `[0, 1]` has norm bounded by
`‖γ(0)‖ + K`. -/
lemma lipschitzWith_norm_bound_on_Icc01
    {x : ℂ} {γ : PwC1Immersion x x} {K : NNReal}
    (hLip : LipschitzWith K γ.toPath.extend) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖γ.toPath.extend t‖ ≤ ‖γ.toPath.extend 0‖ + (K : ℝ) := by
  have hd : dist t 0 ≤ 1 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]; exact ht.2
  have h_norm_close : ‖γ.toPath.extend t - γ.toPath.extend 0‖ ≤ (K : ℝ) := by
    rw [← dist_eq_norm]
    calc dist (γ.toPath.extend t) (γ.toPath.extend 0)
        ≤ K * dist t 0 := hLip.dist_le_mul _ _
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hd (NNReal.coe_nonneg _)
      _ = (K : ℝ) := mul_one _
  calc ‖γ.toPath.extend t‖
      = ‖γ.toPath.extend 0 + (γ.toPath.extend t - γ.toPath.extend 0)‖ := by
        congr 1; ring
    _ ≤ ‖γ.toPath.extend 0‖ + ‖γ.toPath.extend t - γ.toPath.extend 0‖ :=
          norm_add_le _ _
    _ ≤ ‖γ.toPath.extend 0‖ + (K : ℝ) := by linarith

/-! ### Norm bound for `γ.contourIntegral (z-w)⁻¹` -/

/-- For γ contained in a ball of radius `R`, the contour integral of `1/(z-w)`
along γ is bounded by `M_d / (‖w‖ - R)` for `‖w‖ > R`, where `M_d` bounds γ's
derivative. Mirrors `dixonH2_norm_le` with `f = const 1`. -/
private lemma contourIntegral_inv_norm_le_of_far
    {x : ℂ} {γ : PiecewiseC1Path x x}
    {R M_d : ℝ}
    (hR : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ.toPath.extend t‖ ≤ R)
    (hM_d : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ.toPath.extend t‖ ≤ M_d)
    {w : ℂ} (hw : R < ‖w‖) :
    ‖γ.contourIntegral (fun z => (z - w)⁻¹)‖ ≤ M_d / (‖w‖ - R) := by
  have hpos : 0 < ‖w‖ - R := by linarith
  have h_dist_lb : ∀ t ∈ Icc (0 : ℝ) 1, ‖w‖ - R ≤ ‖γ.toPath.extend t - w‖ :=
    fun t ht => by
      have := norm_sub_norm_le w (γ.toPath.extend t)
      rw [norm_sub_rev] at this
      linarith [hR t ht]
  unfold PiecewiseC1Path.contourIntegral
  have h_ptwise : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖(γ.toPath.extend t - w)⁻¹ * deriv γ.toPath.extend t‖ ≤ M_d / (‖w‖ - R) := by
    intro t ht_ui
    have ht : t ∈ Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le (zero_le_one' ℝ)] at ht_ui
      exact Ioc_subset_Icc_self ht_ui
    rw [norm_mul, norm_inv]
    calc ‖γ.toPath.extend t - w‖⁻¹ * ‖deriv γ.toPath.extend t‖
        ≤ (‖w‖ - R)⁻¹ * M_d := mul_le_mul (inv_anti₀ hpos (h_dist_lb t ht))
          (hM_d t ht) (norm_nonneg _) (inv_pos.mpr hpos).le
      _ = M_d / (‖w‖ - R) := by rw [inv_mul_eq_div]
  simpa [PiecewiseC1Path.extendedPath] using
    intervalIntegral.norm_integral_le_of_norm_le_const h_ptwise

/-! ### Generalized winding number vanishes for `w` far from γ (Lipschitz form) -/

/-- **Generalized winding number vanishes for `w` far from γ.**

For a Lipschitz closed piecewise-`C¹` immersion `γ`, the generalized winding
number around `w` is `0` whenever `‖w‖` exceeds `‖γ(0)‖ + K + K/(2π)`. -/
theorem generalizedWindingNumber_eq_zero_of_far_lipschitz
    {x : ℂ} {γ : PwC1Immersion x x} {K : NNReal}
    (hLip : LipschitzWith K γ.toPath.extend) {w : ℂ}
    (hw : ‖γ.toPath.extend 0‖ + (K : ℝ) + (K : ℝ) / (2 * Real.pi) < ‖w‖) :
    generalizedWindingNumber γ.toPiecewiseC1Path w = 0 := by
  set R : ℝ := ‖γ.toPath.extend 0‖ + (K : ℝ) with hR_def
  have h_2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hR_w : R < ‖w‖ := by
    have : (0 : ℝ) ≤ (K : ℝ) / (2 * Real.pi) :=
      div_nonneg (NNReal.coe_nonneg _) h_2pi_pos.le
    linarith
  have hpos : 0 < ‖w‖ - R := by linarith
  have hR_bound : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ.toPath.extend t‖ ≤ R :=
    lipschitzWith_norm_bound_on_Icc01 hLip
  have h_dist_lb : ∀ t ∈ Icc (0 : ℝ) 1,
      (‖w‖ - R) ≤ ‖γ.toPath.extend t - w‖ := fun t ht => by
    have := norm_sub_norm_le w (γ.toPath.extend t)
    rw [norm_sub_rev] at this
    linarith [hR_bound t ht]
  have hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1,
      δ ≤ ‖γ.toPiecewiseC1Path t - w‖ := ⟨‖w‖ - R, hpos, h_dist_lb⟩
  obtain ⟨n, hn⟩ :=
    hasGeneralizedWindingNumber_integer_of_closed γ.toPiecewiseC1Path hδ
      (intervalIntegrable_div_lipschitz γ.toPiecewiseC1Path hpos h_dist_lb hLip)
  have h_eq_int : γ.toPiecewiseC1Path.contourIntegral (fun z => (z - w)⁻¹) =
      2 * ↑Real.pi * I * (n : ℂ) :=
    tendsto_nhds_unique (hasCauchyPV_of_avoids hδ) hn
  have h_norm_2piIn : ‖(2 : ℂ) * (↑Real.pi : ℂ) * I * (n : ℂ)‖ =
      2 * Real.pi * (|n| : ℝ) := by
    rw [show (2 : ℂ) * (↑Real.pi : ℂ) * I * (n : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) * (I * (n : ℂ)) from by push_cast; ring,
      norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos h_2pi_pos, Complex.norm_I, one_mul, Complex.norm_intCast]
  have hL : 2 * Real.pi * (|n| : ℝ) ≤ (K : ℝ) / (‖w‖ - R) := by
    rw [← h_norm_2piIn, ← h_eq_int]
    exact contourIntegral_inv_norm_le_of_far hR_bound
      (fun _ _ => norm_deriv_le_of_lipschitz hLip) hR_w
  have h_div_lt : (K : ℝ) / (‖w‖ - R) < 2 * Real.pi := by
    rw [div_lt_iff₀ hpos]
    have h_K_lt : (K : ℝ) / (2 * Real.pi) < ‖w‖ - R := by linarith
    rw [div_lt_iff₀ h_2pi_pos] at h_K_lt; nlinarith
  have h_n_abs_lt_1 : (|n| : ℝ) < 1 :=
    lt_of_mul_lt_mul_left (by simpa using hL.trans_lt h_div_lt) h_2pi_pos.le
  rw [hn.eq, show n = 0 from Int.abs_lt_one_iff.mp (mod_cast h_n_abs_lt_1), Int.cast_zero]

/-! ### Cocompact form: winding eventually zero from Lipschitz γ -/

/-- For a Lipschitz `PwC1Immersion`, the conjunction
"γ avoids w AND generalized winding γ w = 0" holds eventually in cocompact ℂ.
This is the **Lipschitz analog** of `winding_eventually_zero_cocompact_of_bounded`
(which used bounded U). Crucially, this version does **not** require U to be
bounded — it only uses γ being Lipschitz, which is automatic for
`ClosedPwC1Immersion`. -/
theorem winding_eventually_zero_cocompact_of_lipschitz
    {x : ℂ} {γ : PwC1Immersion x x} {K : NNReal}
    (hLip : LipschitzWith K γ.toPath.extend) :
    ∀ᶠ w in Filter.cocompact ℂ,
      (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) ∧
        generalizedWindingNumber γ.toPiecewiseC1Path w = 0 := by
  set R : ℝ := ‖γ.toPath.extend 0‖ + (K : ℝ) with hR_def
  set RR : ℝ := R + (K : ℝ) / (2 * Real.pi) with hRR_def
  have h_mem : {w : ℂ | RR < ‖w‖} ∈ Filter.cocompact ℂ := by
    rw [Filter.mem_cocompact]
    exact ⟨Metric.closedBall 0 RR, isCompact_closedBall 0 RR, fun w hw => by
      simpa [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hw⟩
  filter_upwards [h_mem] with w (hw : RR < ‖w‖)
  have h_2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_K_div_2pi_nn : (0 : ℝ) ≤ (K : ℝ) / (2 * Real.pi) :=
    div_nonneg (NNReal.coe_nonneg _) h_2pi_pos.le
  refine ⟨fun t ht heq => ?_,
    generalizedWindingNumber_eq_zero_of_far_lipschitz hLip hw⟩
  have hbd := lipschitzWith_norm_bound_on_Icc01 hLip t ht
  rw [show γ.toPath.extend t = w from heq] at hbd
  linarith

/-! ### Full B-1: locally constant near boundary points -/

/-- **B-1 (full form).** For a Lipschitz null-homologous closed immersion `γ` and
a point `w ∉ U` with `γ` avoiding `w`, the generalized winding number vanishes on
a whole neighborhood of `w`.

Combines W-4 (locally constant) with the null-homologous vanishing at `w`. Unlike
`winding_zero_nhds_of_not_mem_closure`, this works even when `w ∈ closure U \ U`
(e.g., a boundary point of `U`), at the cost of needing γ Lipschitz. -/
theorem IsNullHomologous.winding_zero_nhds_of_not_mem_of_closed
    {γ : PwC1Immersion x x} {U : Set ℂ} (h_null : IsNullHomologous γ U)
    {w : ℂ} (hw : w ∉ U)
    (h_avoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
      generalizedWindingNumber γ.toPiecewiseC1Path w' = 0 := by
  obtain ⟨ε, hε_pos, h_const⟩ :=
    Complex.generalizedWindingNumber_locally_const_of_closed
      γ.toPiecewiseC1Path h_avoid hLip
  exact ⟨ε, hε_pos, fun w' hw' => by rw [h_const w' hw', h_null.winding_zero w hw]⟩

/-! ### Convex domains -/

end
