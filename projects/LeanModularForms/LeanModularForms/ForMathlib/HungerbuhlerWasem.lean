/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.NullHomologous
import LeanModularForms.ForMathlib.DixonTheorem
import LeanModularForms.ForMathlib.PaperPwC1Immersion
import LeanModularForms.ForMathlib.SimplePoleIntegral
import LeanModularForms.ForMathlib.MultipointPV
import LeanModularForms.ForMathlib.PiecewiseContourIntegral
import LeanModularForms.ForMathlib.ResidueCircleIntegral
import LeanModularForms.ForMathlib.CurveMeasureZero
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue.MeasureHelpers

-- NOTE on imports / Central B:
-- The project currently maintains two parallel residue libraries with overlapping
-- root-namespace identifiers (e.g. both `LeanModularForms.ForMathlib.Residue` and
-- `LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue` define
-- `HasSimplePoleAt`; both `MultipointPV` files define `disjoint_balls_of_small_epsilon`).
-- This file commits to the legacy chain (`Residue`, `SimplePoleIntegral`,
-- `MultipointPV`, `MeromorphicCauchy`). Central theorem B
-- (`residueTheorem_simplePoles_convex`) and corollary 4
-- (`residueTheorem_simplePoles_convex_transverse`) wrap the existing
-- `generalizedResidueTheorem'` in `GeneralizedResidueTheory.Residue.GeneralizedTheoremBase`,
-- which uses the GRT chain.

/-!
# Hungerbühler–Wasem residue theorem

The generalized residue theorem of Hungerbühler and Wasem
(arXiv:1808.00997v2, Theorem 3.3): the Cauchy principal value of `∮f` along a
closed piecewise-`C¹` immersion `γ` null-homologous in an open domain `U`
equals `2πi · Σ winding(γ, s) · residue(f, s)` over the singular set `S ⊆ U`.

## Main results

* `HungerbuhlerWasem.PolarPartDecomposition` — the data of an explicit
  Laurent polar-part decomposition of a meromorphic function.
* `HungerbuhlerWasem.residueTheorem_avoidance` — central theorem A:
  decomposition-as-data form. γ avoids every pole.
* `HungerbuhlerWasem.residueTheorem_simplePoles_convex` — central theorem B:
  simple poles only on a convex domain. γ may cross poles, but two CPV
  oracles must be supplied.
* Four corollaries specializing one or the other central theorem:
  `residueTheorem_simplePoles_avoidance`, `residueTheorem_convex_avoidance`,
  `residueTheorem_simplePoles_convex_avoidance`,
  `residueTheorem_simplePoles_convex_transverse`.
* `HungerbuhlerWasem.residueTheorem_crossing` — unifying form (higher-order
  + crossings); lives in
  `LeanModularForms.ForMathlib.HungerbuhlerWasem.Crossing`.
-/

open Set Filter Topology Complex MeasureTheory
open scoped Interval

noncomputable section

namespace HungerbuhlerWasem

/-- A **polar-part decomposition** of a meromorphic function `f` on a domain
`U \ S`: for each pole `s ∈ S`, an explicit polar part `polarPart s z =
∑ k, a_{s,k} / (z - s)^(k+1)` such that `f` minus the total polar part extends
analytically to all of `U`.

This bundles the data the residue formula needs without requiring access to
mathlib's Laurent-extraction API. Each polar part is a finite Laurent
combination at its pole; the residue at `s` is the `k = 0` coefficient. -/
structure PolarPartDecomposition (f : ℂ → ℂ) (S : Finset ℂ) (U : Set ℂ) where
  /-- The polar part at each pole, viewed as a function of `z`. -/
  polarPart : ℂ → ℂ → ℂ
  /-- Order of the polar part at each pole. -/
  order : ℂ → ℕ
  /-- Laurent coefficients of the polar part at each pole. -/
  coeff : (s : ℂ) → Fin (order s) → ℂ
  /-- The polar part at `s` is the explicit Laurent sum
  `∑ k, coeff s k / (z - s)^(k+1)`. -/
  polarPart_eq : ∀ s ∈ S, ∀ z, z ≠ s →
    polarPart s z = ∑ k : Fin (order s), coeff s k / (z - s) ^ (k.val + 1)
  /-- The residue at `s ∈ S` equals the `k = 0` Laurent coefficient (for non-empty
  polar parts) or zero (for empty). -/
  residue_eq : ∀ s ∈ S,
    residue f s = if h : 0 < order s then coeff s ⟨0, h⟩ else 0
  /-- After subtracting the total polar part, `f` extends to a function
  differentiable on all of `U`. -/
  analyticRemainder : ℂ → ℂ
  analyticRemainder_diff : DifferentiableOn ℂ analyticRemainder U
  decomp : ∀ z ∈ U \ (↑S : Set ℂ),
    f z = analyticRemainder z + ∑ s ∈ S, polarPart s z

/-- For `k ≥ 2`, the function `c / (z - s)^k` has the single-valued antiderivative
`-c / ((k-1)(z-s)^(k-1))` on `ℂ \ {s}`. Hence its contour integral along any
closed piecewise-`C¹` path avoiding `s` vanishes. -/
theorem contourIntegral_higherOrder_eq_zero_of_avoids
    {x s : ℂ} (γ : PiecewiseC1Path x x)
    (h_avoids : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toPath.extend t ≠ s)
    {k : ℕ} (hk : 2 ≤ k) (c : ℂ)
    (h_int : IntervalIntegrable
      (fun t ↦ c / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t)
      volume 0 1) :
    γ.contourIntegral (fun z ↦ c / (z - s) ^ k) = 0 := by
  have hk_natcast : ((k - 1 : ℕ) : ℂ) ≠ 0 := by rw [Nat.cast_ne_zero]; omega
  set F : ℂ → ℂ := fun z ↦
    (-c / ((k - 1 : ℕ) : ℂ)) * (z - s) ^ (-((k - 1 : ℕ) : ℤ))
  have hF : ∀ z ∈ ({s} : Set ℂ)ᶜ, HasDerivAt F (c / (z - s) ^ k) z := by
    intro z hz
    have hz_sub : z - s ≠ 0 := sub_ne_zero.mpr hz
    have h_inner := (hasDerivAt_zpow (-((k - 1 : ℕ) : ℤ)) (z - s) (Or.inl hz_sub)).comp z
      ((hasDerivAt_id z).sub_const s)
    simp only [Function.comp_def, mul_one] at h_inner
    convert h_inner.const_mul (-c / ((k - 1 : ℕ) : ℂ)) using 1
    all_goals try rfl
    have hk_eq : -((k - 1 : ℕ) : ℤ) - 1 = -(k : ℤ) := by omega
    rw [hk_eq, zpow_neg, zpow_natCast]
    field_simp
    push_cast
    ring
  exact PiecewiseC1Path.contourIntegral_eq_zero_of_hasDerivAt_of_closed γ rfl
    h_avoids hF h_int

variable {x : ℂ}

/-- The derivative of a Lipschitz extended piecewise-`C¹` path is interval-integrable
on `[0, 1]`: derivatives of Lipschitz functions are bounded by the Lipschitz constant. -/
theorem deriv_intervalIntegrable_of_lipschitz (γP : PiecewiseC1Path x x) {K : NNReal}
    (hLip : LipschitzWith K γP.toPath.extend) :
    IntervalIntegrable (deriv γP.toPath.extend) MeasureTheory.volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
  refine MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
    (stronglyMeasurable_deriv _).aestronglyMeasurable
    (ae_restrict_of_ae (Filter.Eventually.of_forall
      (fun _ ↦ norm_deriv_le_of_lipschitz hLip)))

/-- The contour integral of the analytic remainder along a null-homologous
closed γ in U vanishes — even when γ passes through poles of f, because the
analytic remainder extends to all of U by construction of `PolarPartDecomposition`. -/
theorem analyticRemainder_contourIntegral_zero
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (decomp : PolarPartDecomposition f S U) :
    γ.toPwC1Immersion.toPiecewiseC1Path.contourIntegral
      decomp.analyticRemainder = 0 := by
  classical
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  obtain ⟨w₀, hw₀_in_U, hw₀_off⟩ :=
    ForMathlib.exists_mem_not_mem_path_image_of_isOpen γP hU_open hU_ne hLip
  obtain ⟨δ', hδ'_pos, hδ'_bound⟩ := avoids_delta_bound γP w₀ hw₀_off
  have h_deriv_int := deriv_intervalIntegrable_of_lipschitz γP hLip
  have h_dixon_G :
      dixonFunction (fun z ↦ (z - w₀) * decomp.analyticRemainder z) U γP w₀ = 0 :=
    dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded hU_open
      (fun z hz ↦ ((differentiableAt_id.sub_const w₀).differentiableWithinAt).mul
        (decomp.analyticRemainder_diff z hz))
      γ.toPwC1Immersion h_null hLip
      (fun w hw_notin h_avoid_local ↦
        h_null.winding_zero_nhds_of_not_mem_of_closed hw_notin h_avoid_local hLip) w₀
  have h_inv_cont : ContinuousOn (fun t ↦ (γP t - w₀)⁻¹) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (zero_le_one' ℝ)]
    refine ContinuousOn.inv₀
      (γP.toPath.continuous_extend.continuousOn.sub continuousOn_const) ?_
    intro t ht heq
    have := hδ'_bound t ht
    rw [heq, norm_zero] at this
    linarith
  have h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand decomp.analyticRemainder γP)
      MeasureTheory.volume 0 1 :=
    h_deriv_int.continuousOn_mul <| by
      rw [uIcc_of_le (zero_le_one' ℝ)]
      exact decomp.analyticRemainder_diff.continuousOn.comp
        γP.toPath.continuous_extend.continuousOn h_null.image_subset
  have h_cauchy_int : IntervalIntegrable
      (fun t ↦ (γP t - w₀) * decomp.analyticRemainder (γP t) / (γP t - w₀) *
        deriv γP.toPath.extend t) MeasureTheory.volume 0 1 := by
    refine h_rem_int.congr ?_
    intro t ht
    rw [uIoc_of_le (zero_le_one' ℝ)] at ht
    have h_ne : γP t - w₀ ≠ 0 :=
      sub_ne_zero.mpr (hw₀_off t (Ioc_subset_Icc_self ht))
    change PiecewiseC1Path.contourIntegrand decomp.analyticRemainder γP t =
      (γP t - w₀) * decomp.analyticRemainder (γP t) / (γP t - w₀) *
        deriv γP.toPath.extend t
    unfold PiecewiseC1Path.contourIntegrand
    rw [show (γP t - w₀) * decomp.analyticRemainder (γP t) / (γP t - w₀) =
      decomp.analyticRemainder (γP t) by field_simp]
  exact contourIntegral_eq_zero_of_nullHomologous_at w₀ hw₀_in_U hw₀_off h_dixon_G
    h_cauchy_int (h_deriv_int.continuousOn_mul h_inv_cont)

/-- The bad set `γ⁻¹(S) ∩ Icc 0 1` for a piecewise-`C¹` immersion `γ` and a
finite set `S` has Lebesgue measure zero. -/
theorem volume_preimage_finset_in_Icc01_zero
    (γ : ClosedPwC1Immersion x) (S : Finset ℂ) :
    volume {t ∈ Icc (0 : ℝ) 1 |
      γ.toPwC1Immersion.toPiecewiseC1Path t ∈ (↑S : Set ℂ)} = 0 := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  set P : Finset ℝ := insert 0 (insert 1 γP.partition)
  have h_in_Ioo : ∀ t ∈ Icc (0 : ℝ) 1, t ∉ P → t ∈ Ioo (0 : ℝ) 1 := by
    intro t ht htP
    have h0 : t ≠ 0 := fun h ↦ htP (h ▸ Finset.mem_insert_self _ _)
    have h1 : t ≠ 1 := fun h ↦ htP (h ▸
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    exact ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  have h_not_part : ∀ t ∈ Icc (0 : ℝ) 1, t ∉ P → t ∉ γP.partition := fun t _ htP h_part ↦
    htP (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h_part))
  exact preimage_finset_measure_zero_of_deriv_ne_zero S
    γP.toPath.continuous_extend.continuousOn
    (fun t ht htP ↦ γP.differentiable_off_extend t (h_in_Ioo t ht htP)
      (h_not_part t ht htP))
    (fun t ht htP ↦ γ.toPwC1Immersion.deriv_ne_zero t (h_in_Ioo t ht htP)
      (h_not_part t ht htP))

/-- For a function `g` differentiable on `U` and a closed piecewise-`C¹`
immersion `γ` with image in `U`, the contour integrand `g(γ(t)) · γ'(t)` is
interval-integrable on `[0, 1]`. -/
private theorem contourIntegrand_diff_intervalIntegrable
    (γ : ClosedPwC1Immersion x) {U : Set ℂ} {g : ℂ → ℂ}
    (h_diff : DifferentiableOn ℂ g U)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ∈ U) :
    IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand g
        γ.toPwC1Immersion.toPiecewiseC1Path) MeasureTheory.volume 0 1 := by
  obtain ⟨_, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  refine (deriv_intervalIntegrable_of_lipschitz γP hLip).continuousOn_mul ?_
  rw [uIcc_of_le (zero_le_one' ℝ)]
  exact h_diff.continuousOn.comp γP.toPath.continuous_extend.continuousOn hγ_in_U

/-- The "bad set" of times where γ comes within ε of some pole. -/
def cpv_badSet (γP : PiecewiseC1Path x x) (S : Finset ℂ) (ε : ℝ) :
    Set ℝ := {t : ℝ | ∃ s ∈ S, ‖γP.toPath.extend t - s‖ ≤ ε}

private theorem cpv_badSet_measurableSet (γP : PiecewiseC1Path x x) (S : Finset ℂ)
    (ε : ℝ) : MeasurableSet (cpv_badSet γP S ε) := by
  classical
  have h_eq : cpv_badSet γP S ε = ⋃ s ∈ S, {t : ℝ | ‖γP.toPath.extend t - s‖ ≤ ε} := by
    ext t; simp [cpv_badSet]
  rw [h_eq]
  exact (isClosed_biUnion_finset fun s _ ↦ isClosed_le
    ((γP.toPath.continuous_extend.sub continuous_const).norm) continuous_const).measurableSet

/-- Express `cpvIntegrandOn S g γ.extend ε` as an indicator of the contour
integrand on the complement of the bad set. -/
theorem cpvIntegrandOn_eq_indicator_compl
    (γP : PiecewiseC1Path x x) (S : Finset ℂ) (g : ℂ → ℂ) (ε : ℝ) (t : ℝ) :
    cpvIntegrandOn S g γP.toPath.extend ε t =
      (cpv_badSet γP S ε)ᶜ.indicator
        (PiecewiseC1Path.contourIntegrand g γP) t := by
  classical
  unfold cpvIntegrandOn cpv_badSet
  by_cases h : ∃ s ∈ S, ‖γP.toPath.extend t - s‖ ≤ ε
  · rw [if_pos h, Set.indicator_of_notMem (by simpa using h)]
  · rw [if_neg h, Set.indicator_of_mem (by simpa using h)]; rfl

/-- The cutoff integrand `cpvIntegrandOn S g γ.extend ε` is interval-integrable
on `[0, 1]` for any `ε`, when `g` is differentiable on `U` and γ has image in
`U`. The proof realizes the cutoff as an indicator of the (interval-integrable)
contour integrand on a measurable set. -/
theorem cpvIntegrandOn_diff_intervalIntegrable
    (γ : ClosedPwC1Immersion x) (S : Finset ℂ) {U : Set ℂ} {g : ℂ → ℂ}
    (h_diff : DifferentiableOn ℂ g U)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ∈ U) (ε : ℝ) :
    IntervalIntegrable
      (fun t ↦ cpvIntegrandOn S g
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t)
      MeasureTheory.volume 0 1 := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have h_full := contourIntegrand_diff_intervalIntegrable γ h_diff hγ_in_U
  rw [show (fun t ↦ cpvIntegrandOn S g γP.toPath.extend ε t) =
    (cpv_badSet γP S ε)ᶜ.indicator (PiecewiseC1Path.contourIntegrand g γP) from
    funext fun t ↦ cpvIntegrandOn_eq_indicator_compl γP S g ε t]
  rw [intervalIntegrable_iff] at h_full ⊢
  exact h_full.indicator (cpv_badSet_measurableSet γP S ε).compl

/-- Almost every `t ∈ Icc 0 1` satisfies `γ(t) ∉ S` — a consequence of the
immersion property (the bad set has measure zero). -/
private theorem cpv_ae_not_mem_S (γ : ClosedPwC1Immersion x) (S : Finset ℂ) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Icc (0 : ℝ) 1)),
      γ.toPwC1Immersion.toPiecewiseC1Path t ∉ (↑S : Set ℂ) := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (volume_preimage_finset_in_Icc01_zero γ S)
  intro t ht
  push Not at ht
  exact ht

/-- For a function `g` differentiable on `U` and γ ⊆ U, the cutoff integrands
converge pointwise a.e. on `Icc 0 1` to the contour integrand as `ε → 0⁺`. -/
theorem cpvIntegrandOn_tendsto_contourIntegrand_ae
    (γ : ClosedPwC1Immersion x) (S : Finset ℂ) (g : ℂ → ℂ) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Ι (0 : ℝ) 1)),
      Tendsto
        (fun ε ↦ cpvIntegrandOn S g
          γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t)
        (𝓝[>] 0)
        (𝓝 (PiecewiseC1Path.contourIntegrand g
          γ.toPwC1Immersion.toPiecewiseC1Path t)) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have h_ae := cpv_ae_not_mem_S γ S
  rw [Set.uIoc_of_le zero_le_one, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at h_ae
  filter_upwards [h_ae] with t h_not_mem ht
  have h_not_mem' : γP t ∉ (↑S : Set ℂ) := h_not_mem ⟨le_of_lt ht.1, ht.2⟩
  have h_far : ∀ s ∈ S, 0 < ‖γP.toPath.extend t - s‖ := fun s hs ↦
    norm_pos_iff.mpr <| sub_ne_zero.mpr <| fun heq ↦
      h_not_mem' (heq ▸ Finset.mem_coe.mpr hs : γP.toPath.extend t ∈ (↑S : Set ℂ))
  suffices h_lim_const :
      (fun ε ↦ cpvIntegrandOn S g γP.toPath.extend ε t) =ᶠ[𝓝[>] 0]
        (fun _ ↦ PiecewiseC1Path.contourIntegrand g γP t) from
    Tendsto.congr' h_lim_const.symm tendsto_const_nhds
  by_cases hS : S.Nonempty
  · obtain ⟨δ, hδ_mem, hδ_min⟩ := Finset.exists_min_image S
      (fun s ↦ ‖γP.toPath.extend t - s‖) hS
    filter_upwards [Ioo_mem_nhdsGT (h_far δ hδ_mem)] with ε hε
    rw [cpvIntegrandOn_of_forall_gt fun s hs ↦ lt_of_lt_of_le hε.2 (hδ_min s hs)]
    rfl
  · have h_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    filter_upwards [self_mem_nhdsWithin] with ε _
    subst h_empty
    rfl

/-- The Cauchy principal value of the analytic remainder along a null-homologous
closed piecewise-`C¹` immersion vanishes — even when `γ` may pass through poles
of `f`, because the analytic remainder extends to all of `U` by construction
of the polar-part decomposition.

This eliminates the `h_rem_cpv` oracle from `residueTheorem_crossing`. -/
theorem analyticRemainder_hasCauchyPVOn_zero
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (decomp : PolarPartDecomposition f S U) :
    HasCauchyPVOn S decomp.analyticRemainder
      γ.toPwC1Immersion.toPiecewiseC1Path 0 := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γP t ∈ U := h_null.image_subset
  have h_full := contourIntegrand_diff_intervalIntegrable γ
    decomp.analyticRemainder_diff hγ_in_U
  have h_meas : ∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun t ↦ cpvIntegrandOn S decomp.analyticRemainder
        γP.toPath.extend ε t)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (cpvIntegrandOn_diff_intervalIntegrable γ S
      decomp.analyticRemainder_diff hγ_in_U ε).aestronglyMeasurable_restrict_uIoc
  have h_bound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂MeasureTheory.volume,
      x ∈ Set.uIoc (0 : ℝ) 1 →
      ‖cpvIntegrandOn S decomp.analyticRemainder γP.toPath.extend ε x‖ ≤
        ‖PiecewiseC1Path.contourIntegrand decomp.analyticRemainder γP x‖ := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine MeasureTheory.ae_of_all _ fun t _ ↦ ?_
    rw [cpvIntegrandOn_eq_indicator_compl γP S decomp.analyticRemainder ε t]
    by_cases ht_in : t ∈ (cpv_badSet γP S ε)ᶜ
    · rw [Set.indicator_of_mem ht_in]
    · rw [Set.indicator_of_notMem ht_in, norm_zero]
      exact norm_nonneg _
  have h_pointwise : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      Tendsto (fun ε ↦ cpvIntegrandOn S decomp.analyticRemainder
          γP.toPath.extend ε x) (𝓝[>] 0)
        (𝓝 (PiecewiseC1Path.contourIntegrand decomp.analyticRemainder γP x)) := by
    have := cpvIntegrandOn_tendsto_contourIntegrand_ae γ S decomp.analyticRemainder
    rwa [MeasureTheory.ae_restrict_iff' measurableSet_uIoc] at this
  unfold HasCauchyPVOn
  rw [← analyticRemainder_contourIntegral_zero hU_open hU_ne hS_in_U γ h_null decomp]
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t ↦ ‖PiecewiseC1Path.contourIntegrand decomp.analyticRemainder γP t‖)
    h_meas h_bound h_full.norm h_pointwise

/-- Interval-integrability of the cutoff integrand of a polar part of the
decomposition. Eliminates the `h_polar_int` oracle from
`residueTheorem_crossing`. -/
theorem cpvIntegrandOn_polarPart_intervalIntegrable
    (γ : ClosedPwC1Immersion x) {U : Set ℂ} {S : Finset ℂ}
    (_hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ}
    (decomp : PolarPartDecomposition f S U) {s : ℂ} (hs : s ∈ S)
    (_h_null : IsNullHomologous γ.toPwC1Immersion U) {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable
      (fun t ↦ cpvIntegrandOn S (decomp.polarPart s)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t)
      MeasureTheory.volume 0 1 := by
  classical
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  set N : ℕ := decomp.order s
  set a : Fin N → ℂ := decomp.coeff s
  set laurentSum : ℂ → ℂ := fun z ↦ ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)
  set h_curve : ℝ → ℂ := fun t ↦
    laurentSum (γP.toPath.extend t) * deriv γP.toPath.extend t
  have h_far_of : ∀ t ∈ (cpv_badSet γP S ε)ᶜ, ∀ s' ∈ S,
      ε < ‖γP.toPath.extend t - s'‖ := fun t ht_in s' hs' ↦ by
    simp only [cpv_badSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_and,
      not_le] at ht_in
    exact ht_in s' hs'
  have h_indicator_eq' :
      (fun t ↦ cpvIntegrandOn S (decomp.polarPart s)
        γP.toPath.extend ε t) =
      (cpv_badSet γP S ε)ᶜ.indicator h_curve := by
    funext t
    rw [cpvIntegrandOn_eq_indicator_compl γP S (decomp.polarPart s) ε t]
    by_cases ht_in : t ∈ (cpv_badSet γP S ε)ᶜ
    · rw [Set.indicator_of_mem ht_in, Set.indicator_of_mem ht_in]
      have h_ne : γP.toPath.extend t ≠ s := fun heq ↦ by
        have := h_far_of t ht_in s hs
        rw [heq, sub_self, norm_zero] at this; linarith
      change decomp.polarPart s (γP.toPath.extend t) *
        deriv γP.toPath.extend t =
        laurentSum (γP.toPath.extend t) * deriv γP.toPath.extend t
      rw [decomp.polarPart_eq s hs (γP.toPath.extend t) h_ne]
    · rw [Set.indicator_of_notMem ht_in, Set.indicator_of_notMem ht_in]
  set M_polar : ℝ := ∑ k : Fin N, ‖a k‖ / ε ^ (k.val + 1)
  set M : ℝ := M_polar * K
  have h_M_polar_nonneg : 0 ≤ M_polar :=
    Finset.sum_nonneg (fun k _ ↦ div_nonneg (norm_nonneg _) (pow_nonneg hε.le _))
  have h_M_nonneg : 0 ≤ M := mul_nonneg h_M_polar_nonneg (NNReal.coe_nonneg K)
  have h_bound_on_compl : ∀ t ∈ (cpv_badSet γP S ε)ᶜ, ‖h_curve t‖ ≤ M := fun t ht_in ↦
    calc ‖h_curve t‖ = ‖laurentSum (γP.toPath.extend t)‖ *
          ‖deriv γP.toPath.extend t‖ := norm_mul _ _
      _ ≤ M_polar * K := mul_le_mul
          ((norm_sum_le _ _).trans <| Finset.sum_le_sum fun k _ ↦ by
            rw [norm_div, norm_pow]
            exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hε _)
              (pow_le_pow_left₀ hε.le (h_far_of t ht_in s hs).le _))
          (norm_deriv_le_of_lipschitz hLip) (norm_nonneg _) h_M_polar_nonneg
  have h_curve_meas : Measurable h_curve :=
    (Finset.measurable_sum (Finset.univ : Finset (Fin N)) fun k _ ↦
      Measurable.const_div ((γP.toPath.continuous_extend.measurable.sub_const s).pow_const _) _)
      |>.mul (measurable_deriv _)
  rw [intervalIntegrable_iff, h_indicator_eq']
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
    (h_curve_meas.aestronglyMeasurable.indicator (cpv_badSet_measurableSet γP S ε).compl) M ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t _
  by_cases ht_in : t ∈ (cpv_badSet γP S ε)ᶜ
  · rw [Set.indicator_of_mem ht_in]; exact h_bound_on_compl t ht_in
  · rw [Set.indicator_of_notMem ht_in, norm_zero]; exact h_M_nonneg


end HungerbuhlerWasem

end
