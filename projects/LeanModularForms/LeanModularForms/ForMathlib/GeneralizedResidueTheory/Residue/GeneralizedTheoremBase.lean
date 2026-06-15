/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue.MultipointPV
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue.MultipointPV.DominatedConvergence
import Mathlib.Analysis.Meromorphic.Order

/-!
# Generalized Residue Theorem -- Base Infrastructure

Multi-point PV existence, helper lemmas, and the core generalized residue theorem
for piecewise C1 immersions passing through poles. This file provides the
infrastructure used by both the convex and null-homologous versions.

## Main Results

* `cauchyPrincipalValueOn_singular_sum` -- multi-point PV exists when
  each singular term has PV
* `generalizedResidueTheorem'` -- CPV equals `2 pi i . Sigma winding . residue`
  (convex domain, with explicit PV hypothesis)
* `residueAt` -- residue via contour integral
* `generalizedResidueTheorem_higher_order_tendsto` -- higher-order Tendsto formulation
  (no convexity needed)
* Helper lemmas: `hasSimplePoleAt_sum_div_sub`, `differentiableOn_sum_div_sub`,
  `residueSimplePole_sum_div_sub`, `continuousAt_sum_remainder`

The convex-domain theorems `generalizedResidueTheorem`,
`generalizedResidueTheorem_higher_order`, and
`generalizedResidueTheorem_higher_order_simple` are in `GeneralizedTheorem.lean`,
where they are proved as corollaries of the null-homologous versions.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

private lemma cpv_crossing_null (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) :
    volume {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t ∈ (S0 : Set ℂ)} = 0 := by
  have h_eq : {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t ∈ (S0 : Set ℂ)} =
      ⋃ s ∈ (↑S0 : Set ℂ), {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t = s} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe]
    exact ⟨fun ⟨hin, hmem⟩ => ⟨γ.toFun t, hmem, hin, rfl⟩,
      fun ⟨_, hs, hin, heq⟩ => ⟨hin, heq ▸ hs⟩⟩
  rw [h_eq, measure_biUnion_null_iff S0.finite_toSet.countable]
  exact fun s _ => preimage_singleton_measure_zero_of_deriv_ne_zero
    (P := γ.partition) s γ.continuous_toFun γ.smooth_off_partition γ.deriv_ne_zero

private lemma finset_min_sep (S0 : Finset ℂ) (hS0_nonempty : S0.Nonempty) :
    ∃ δ > 0, ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖ := by
  by_cases h_card_one : S0.card = 1
  · refine ⟨1, one_pos, fun s hs s' hs' hne => ?_⟩
    obtain ⟨s₀, rfl⟩ := Finset.card_eq_one.mp h_card_one
    simp only [Finset.mem_singleton] at hs hs'
    exact (hne (hs.trans hs'.symm)).elim
  · have h_pos : ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → (0 : ℝ) < ‖s' - s‖ :=
      fun _ _ _ _ hne => norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
    have h_exists_pair : ∃ s ∈ S0, ∃ s' ∈ S0, s ≠ s' := by
      obtain ⟨s, hs⟩ := hS0_nonempty
      by_contra h_all_eq
      push Not at h_all_eq
      have h0 : 0 < S0.card := Finset.card_pos.mpr ⟨s, hs⟩
      have := Finset.card_le_card (fun x hx => Finset.mem_singleton.mpr (h_all_eq x hx s hs))
      simp only [Finset.card_singleton] at this
      omega
    obtain ⟨s₁, hs₁, s₂, hs₂, hne₁₂⟩ := h_exists_pair
    have h_finite : ((S0 ×ˢ S0).filter (fun p => p.1 ≠ p.2) |>.image
        (fun p => ‖p.2 - p.1‖)).Nonempty :=
      ⟨_, Finset.mem_image.mpr ⟨(s₁, s₂), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hs₁, hs₂⟩, hne₁₂⟩, rfl⟩⟩
    obtain ⟨δ, hδ_mem, hδ_min⟩ := Finset.exists_min_image _ id h_finite
    simp only [id] at hδ_min
    obtain ⟨⟨a, b⟩, hab_mem, hab_eq⟩ := Finset.mem_image.mp hδ_mem
    simp only [Finset.mem_filter, Finset.mem_product] at hab_mem
    refine ⟨δ, hab_eq ▸ h_pos a hab_mem.1.1 b hab_mem.1.2 hab_mem.2, fun s hs s' hs' hne =>
      hδ_min ‖s' - s‖ (Finset.mem_image.mpr ⟨(s, s'),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hs, hs'⟩, hne⟩, rfl⟩)⟩

/-- The Cauchy filter argument: if the sum of PV terms converges and the regular part
tends to its integral, then the full CPV filter is Cauchy (hence converges). -/
private lemma cpv_cauchy_of_sum_and_regular (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (hS0_nonempty : S0.Nonempty)
    (hPV_each : ∀ s ∈ S0, CauchyPrincipalValueExists'
      (fun z => residueSimplePole f s / (z - s)) γ.toFun γ.a γ.b s)
    (hg_reg_cont : ContinuousOn
      (fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s))
      (γ.toFun '' Icc γ.a γ.b)) :
    Cauchy (map (fun ε =>
      ∫ t in γ.a..γ.b, cpvIntegrandOn S0 f γ.toFun ε t) (𝓝[>] 0)) := by
  choose L_fn hL_fn using hPV_each
  set M := fun ε => ∫ t in γ.a..γ.b, cpvIntegrandOn S0 f γ.toFun ε t
  set S' := fun ε => ∑ s ∈ S0.attach, ∫ t in γ.a..γ.b,
    if ‖γ.toFun t - s.val‖ > ε then
      (residueSimplePole f s.val / (γ.toFun t - s.val)) * deriv γ.toFun t
    else 0
  set g_reg := fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s)
  have h_sum_tendsto : Tendsto S' (𝓝[>] 0) (𝓝 (∑ s ∈ S0.attach, L_fn s.val s.property)) :=
    tendsto_finsetSum _ fun ⟨s, hs⟩ _ => hL_fn s hs
  have h_A_tendsto : Tendsto (fun ε => M ε - S' ε) (𝓝[>] 0)
      (𝓝 (∫ t in γ.a..γ.b, g_reg (γ.toFun t) * deriv γ.toFun t)) :=
    multipointPV_diff_tendsto S0 f γ (cpv_crossing_null S0 γ) g_reg
      (fun _ _ => by simp only [g_reg]; ring) hg_reg_cont (finset_min_sep S0 hS0_nonempty)
  have h_M_tendsto :
      Tendsto M (𝓝[>] 0) (𝓝 ((∑ s ∈ S0.attach, L_fn s.val s.property) +
        ∫ t in γ.a..γ.b, g_reg (γ.toFun t) * deriv γ.toFun t)) := by
    have : M = fun ε => S' ε + (M ε - S' ε) := by ext; ring
    rw [this]; exact h_sum_tendsto.add h_A_tendsto
  exact h_M_tendsto.cauchy_map

/-- Multi-point PV exists when each singular term has PV. -/
lemma cauchyPrincipalValueOn_singular_sum (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (_hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hPV_each : ∀ s ∈ S0, CauchyPrincipalValueExists'
      (fun z => residueSimplePole f s / (z - s)) γ.toFun γ.a γ.b s)
    (hg_reg_cont : ContinuousOn
      (fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s))
      (γ.toFun '' Icc γ.a γ.b)) :
    CauchyPrincipalValueExistsOn S0 f γ.toFun γ.a γ.b := by
  by_cases hS0_empty : S0 = ∅
  · subst hS0_empty
    exact ⟨_, hasCauchyPVOn'_empty f γ.toFun γ.a γ.b⟩
  · exact CompleteSpace.complete (cpv_cauchy_of_sum_and_regular S0 f γ
      (Finset.nonempty_iff_ne_empty.mpr hS0_empty) hPV_each hg_reg_cont)

/-- The integral of a holomorphic function along a closed piecewise C¹ immersion
vanishes, via the fundamental theorem of calculus. -/
private lemma holomorphic_closed_integral_zero (U : Set ℂ) (hU : IsOpen U)
    (hU_convex : Convex ℝ U) (g : ℂ → ℂ) (hg_diff : DifferentiableOn ℂ g U)
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hg_cont_on_image : ContinuousOn g (γ.toFun '' Icc γ.a γ.b)) :
    ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0 := by
  obtain ⟨F, hF⟩ := holomorphic_convex_primitive hU_convex hU
    ⟨γ.toFun γ.a, hγ_in_U γ.a (left_mem_Icc.mpr γ.hab.le)⟩ hg_diff
  have h_Fγ_cont : ContinuousOn (F ∘ γ.toFun) (Icc γ.a γ.b) := fun t ht =>
    (hF (γ.toFun t) (hγ_in_U t ht)).continuousAt.continuousWithinAt.comp
      (γ.continuous_toFun t ht) (mapsTo_image γ.toFun _)
  have h_deriv' : ∀ t ∈ Ioo γ.a γ.b \ (↑γ.partition ∩ Ioo γ.a γ.b),
      HasDerivAt (F ∘ γ.toFun) (g (γ.toFun t) * deriv γ.toFun t) t := by
    intro t ⟨ht, hp⟩
    have ht' : t ∈ Icc γ.a γ.b := Ioo_subset_Icc_self ht
    exact (hF (γ.toFun t) (hγ_in_U t ht')).comp_of_eq t
      ((γ.smooth_off_partition t ht' (fun h => hp ⟨h, ht⟩)).hasDerivAt) rfl
  have h_int : IntervalIntegrable (fun t => g (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b :=
    IntervalIntegrable.continuousOn_mul
      (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve
        (piecewiseC1Immersion_deriv_bounded γ))
      (by rw [Set.uIcc_of_le γ.hab.le]
          exact hg_cont_on_image.comp γ.continuous_toFun (Set.mapsTo_image γ.toFun _))
  rw [integral_eq_of_hasDerivAt_off_countable_of_le (F ∘ γ.toFun) _ γ.hab.le
      (γ.partition.finite_toSet.inter_of_left _).countable h_Fγ_cont h_deriv' h_int,
    Function.comp_apply, Function.comp_apply,
    (hγ_closed : γ.toFun γ.a = γ.toFun γ.b), sub_self]

/-- The PV integral of `c/(z-s)` can be factored as `c` times the PV integral
of `1/(z-s)`. This is the integral equality used to extract the constant. -/
private lemma cpv_integral_factor_const (γ : PiecewiseC1Immersion) (s c : ℂ) :
    ∀ ε, (∫ t in γ.a..γ.b,
        if ‖γ.toFun t - s‖ > ε then (c / (γ.toFun t - s)) * deriv γ.toFun t else 0) =
      c * (∫ t in γ.a..γ.b,
        if ‖γ.toFun t - s‖ > ε then (γ.toFun t - s)⁻¹ * deriv γ.toFun t else 0) := by
  intro ε
  rw [← smul_eq_mul, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  split_ifs <;> simp [div_eq_mul_inv, mul_comm c, mul_assoc]

private lemma single_pole_pv_base_exists
    (γ : PiecewiseC1Immersion) (s : ℂ) (c : ℂ) (hc : c ≠ 0)
    (hPV : CauchyPrincipalValueExists' (fun z => c / (z - s)) γ.toFun γ.a γ.b s) :
    ∃ L', Tendsto (fun ε =>
      ∫ t in γ.a..γ.b,
        if ‖(fun t' => γ.toFun t' - s) t - 0‖ > ε
        then (·⁻¹) ((fun t' => γ.toFun t' - s) t) *
          deriv (fun t' => γ.toFun t' - s) t
        else 0)
      (𝓝[>] 0) (𝓝 L') := by
  obtain ⟨L, hL⟩ := hPV
  unfold HasCauchyPV' at hL
  refine ⟨L / c, ?_⟩
  have h_int_eq : ∀ ε,
      (∫ t in γ.a..γ.b,
        if ‖(fun t' => γ.toFun t' - s) t - 0‖ > ε
        then (·⁻¹) ((fun t' => γ.toFun t' - s) t) *
          deriv (fun t' => γ.toFun t' - s) t
        else 0) =
      (∫ t in γ.a..γ.b,
        if ‖γ.toFun t - s‖ > ε then (γ.toFun t - s)⁻¹ * deriv γ.toFun t else 0) :=
    fun _ => intervalIntegral.integral_congr fun _ _ => by simp [sub_zero, deriv_sub_const]
  simp only [h_int_eq]
  have hL' : Tendsto (fun ε => c * ∫ t in γ.a..γ.b,
      if ‖γ.toFun t - s‖ > ε then (γ.toFun t - s)⁻¹ * deriv γ.toFun t else 0)
      (𝓝[>] 0) (𝓝 L) := by
    convert hL using 1; ext ε; exact (cpv_integral_factor_const γ s c ε).symm
  convert hL'.const_mul c⁻¹ using 1
  · ext; simp [inv_mul_cancel_left₀ hc]
  · field_simp

/-- The CPV of `f` decomposes as the sum of individual CPVs for each pole term,
when the integral of the regular part vanishes. -/
private lemma cpv_eq_sum_single_pole_cpvs
    (S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hPV_singular : ∀ s ∈ S0,
      CauchyPrincipalValueExists' (fun z => residueSimplePole f s / (z - s))
        γ.toFun γ.a γ.b s)
    (hg_cont_on_image : ContinuousOn
      (fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s))
      (γ.toFun '' Icc γ.a γ.b))
    (hg_integral_zero :
      ∫ t in γ.a..γ.b,
        (fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s)) (γ.toFun t) *
          deriv γ.toFun t = 0) :
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      ∑ s ∈ S0, cauchyPrincipalValue'
        (fun z => residueSimplePole f s / (z - s)) γ.toFun γ.a γ.b s := by
  set g := fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s) with hg
  have hPV_each_tendsto :
      Tendsto (fun ε => ∑ s ∈ S0,
        ∫ t in γ.a..γ.b,
          if ‖γ.toFun t - s‖ > ε
          then (residueSimplePole f s / (γ.toFun t - s)) * deriv γ.toFun t
          else 0)
        (𝓝[>] 0)
        (𝓝 (∑ s ∈ S0,
          cauchyPrincipalValue' (fun z => residueSimplePole f s / (z - s))
            γ.toFun γ.a γ.b s)) := by
    refine tendsto_finsetSum _ fun s hs => ?_
    obtain ⟨Ls, hLs⟩ := hPV_singular s hs
    rw [show cauchyPrincipalValue' (fun z => residueSimplePole f s / (z - s))
      γ.toFun γ.a γ.b s = Ls from hLs.limUnder_eq]
    exact hLs
  have hS0_sep : ∃ δ' > 0, ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ' ≤ ‖s' - s‖ := by
    by_cases hS0_card : S0.card ≤ 1
    · exact ⟨1, one_pos, fun s hs s' hs' hne =>
        absurd (Finset.card_le_one_iff.mp hS0_card hs hs') hne⟩
    · push Not at hS0_card
      exact finset_min_sep S0 (Finset.card_pos.mp (by omega))
  exact multipointPV_eq_sum_of_integral_zero S0 f γ (cpv_crossing_null S0 γ) g
    (fun _ _ => by simp [hg]) hg_cont_on_image hS0_sep hg_integral_zero
    (cauchyPrincipalValueOn_singular_sum S0 f γ hSimplePoles hPV_singular hg_cont_on_image)
    hPV_each_tendsto

/-- CPV of each `c/(z-s)` equals `2πi · windingNumber · c`, then combine to get the
full residue sum formula. This is the crossing-case second half of the generalized
residue theorem. -/
private lemma generalizedResidueTheorem'_crossing_formula
    (S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hPV_singular : ∀ s ∈ S0,
      CauchyPrincipalValueExists' (fun z => residueSimplePole f s / (z - s))
        γ.toFun γ.a γ.b s)
    (hg_cont_on_image : ContinuousOn
      (fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s))
      (γ.toFun '' Icc γ.a γ.b))
    (hg_integral_zero :
      ∫ t in γ.a..γ.b,
        (fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s)) (γ.toFun t) *
          deriv γ.toFun t = 0) :
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      2 * Real.pi * I *
        ∑ s ∈ S0, generalizedWindingNumber' γ.toFun γ.a γ.b s *
          residueSimplePole f s := by
  have h_single_pole_formula : ∀ s ∈ S0,
      cauchyPrincipalValue' (fun z => residueSimplePole f s / (z - s))
        γ.toFun γ.a γ.b s =
      2 * Real.pi * I * generalizedWindingNumber' γ.toFun γ.a γ.b s *
        residueSimplePole f s := by
    intro s hs
    by_cases hc : residueSimplePole f s = 0
    · simp only [hc, zero_div, mul_zero]
      unfold cauchyPrincipalValue'
      simp only [zero_mul]
      refine limUnder_eventually_eq_const ?_
      filter_upwards with ε
      simp_rw [show ∀ t, (if ‖γ.toFun t - s‖ > ε then (0 : ℂ) else 0) = 0 from
        fun _ => by split_ifs <;> rfl]
      simp
    · exact pv_integral_simple_pole γ.toPiecewiseC1Curve s (residueSimplePole f s)
        (single_pole_pv_base_exists γ s (residueSimplePole f s) hc (hPV_singular s hs))
  rw [cpv_eq_sum_single_pole_cpvs S0 f γ hSimplePoles hPV_singular
      hg_cont_on_image hg_integral_zero,
    Finset.sum_congr rfl h_single_pole_formula, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Generalized residue theorem: CPV equals `2πi · Σ winding ·
residue` even when γ crosses poles. -/
theorem generalizedResidueTheorem'
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (_hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (_hS_closed : IsClosed S) (S0 : Finset ℂ)
    (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (_hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hf_ext : ∀ s ∈ S0,
      ContinuousAt (fun z => f z - residueSimplePole f s / (z - s)) s)
    (hPV_singular : ∀ s ∈ S0, CauchyPrincipalValueExists'
      (fun z => residueSimplePole f s / (z - s)) γ.toFun γ.a γ.b s) :
    CauchyPrincipalValueExistsOn S0 f γ.toFun γ.a γ.b ∧
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b = 2 * Real.pi * I *
        ∑ s ∈ S0, generalizedWindingNumber' γ.toFun γ.a γ.b s *
          residueSimplePole f s := by
  have hS0_in_U : ∀ s ∈ S0, s ∈ U := fun s hs => hS_in_U s (hS0_subset s hs)
  set g := fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s)
  have hg_diff : DifferentiableOn ℂ g U :=
    (simple_poles_decomposition U hU S0 hS0_in_U f hf hSimplePoles hf_ext).1
  have hg_cont_on_image : ContinuousOn g (γ.toFun '' Icc γ.a γ.b) :=
    hg_diff.continuousOn.mono fun _ ⟨t, ht, htz⟩ => htz ▸ hγ_in_U t ht
  refine ⟨?_, ?_⟩
  · by_cases h_avoids : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s
    · exact cauchyPrincipalValueExistsOn_avoids S0 f γ.toPiecewiseC1Curve h_avoids
    · exact cauchyPrincipalValueOn_singular_sum S0 f γ hSimplePoles hPV_singular
        hg_cont_on_image
  · by_cases h_avoids : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s
    · rw [cauchyPrincipalValueOn_avoids S0 f γ.toPiecewiseC1Curve h_avoids]
      exact integral_eq_sum_residues_of_avoids U hU hU_convex S0 hS0_in_U f hf
        γ.toPiecewiseC1Curve hγ_closed hγ_in_U h_avoids hSimplePoles hf_ext
        (piecewiseC1Immersion_deriv_bounded γ)
    · exact generalizedResidueTheorem'_crossing_formula S0 f γ hSimplePoles hPV_singular
        hg_cont_on_image
        (holomorphic_closed_integral_zero U hU hU_convex g hg_diff γ hγ_closed hγ_in_U
          hg_cont_on_image)

/-- If PV of f exists, then PV of c * f exists (scaling by constant). -/
lemma CauchyPrincipalValueExists'.const_mul
    {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} (c : ℂ)
    (h : CauchyPrincipalValueExists' f γ a b z₀) :
    CauchyPrincipalValueExists' (fun z => c * f z) γ a b z₀ :=
  let ⟨_, hL⟩ := h; ⟨_, hL.const_mul c⟩

end
