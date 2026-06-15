/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.PVInfrastructure.UniformStepBound
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue

/-!
# On-Curve Principal Value: General Infrastructure

General PV convergence machinery for piecewise C¹ curves: dyadic PV limits,
measurability of cutout integrands, arc angle injectivity, CPV avoidance
and concatenation lemmas. These results work for arbitrary curves and functions.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The principal value cutoff integral converges as `ε ↘ 0` for a `C²` curve with
non-vanishing derivative at an interior point `t₀`, using a dyadic Cauchy argument. -/
lemma pv_limit_via_dyadic {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ}
    (hat₀ : t₀ ∈ Set.Ioo a b) (hL : L ≠ 0)
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L)
    (hγ_cont_deriv : ContinuousOn (deriv γ) (Set.Icc a b))
    (hγ_meas : Measurable γ)
    (hγ_cont : ContinuousOn γ (Set.Icc a b))
    (h_inj : ∀ t ∈ Set.Icc a b, γ t = γ t₀ → t = t₀) :
    ∃ limit : ℂ, Tendsto (fun ε =>
      ∫ t in a..b, if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0)
      (𝓝[>] 0) (𝓝 limit) := by
  have hab : a < b := hat₀.1.trans hat₀.2
  obtain ⟨K, hK_pos, δ_P1, hδ_P1_pos, h_step_uniform⟩ :=
    pv_step_bound_ratio_two_uniform hab hat₀ hγ_C2 hγ_deriv hL
      hγ_meas hγ_cont_deriv hγ_cont h_inj
  let δ := δ_P1 / 2
  have hδ_pos : 0 < δ := by positivity
  have h_dyadic_lt : ∀ n : ℕ, δ / 2 ^ n < δ_P1 := fun n =>
    (div_le_self hδ_pos.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))).trans_lt
      (by simp only [δ]; linarith)
  let I : ℝ → ℂ := fun ε => ∫ t in a..b,
    if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0
  have h_step : ∀ n, ‖I (δ / 2 ^ (n + 1)) - I (δ / 2 ^ n)‖ ≤ K * δ / 2 ^ n := fun n => by
    have h_le : δ / 2 ^ (n + 1) ≤ δ / 2 ^ n :=
      div_le_div_of_nonneg_left hδ_pos.le (by positivity)
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ n))
    have h_ratio : δ / 2 ^ n ≤ 2 * (δ / 2 ^ (n + 1)) := by
      rw [pow_succ]; ring_nf; linarith
    calc ‖I (δ / 2 ^ (n + 1)) - I (δ / 2 ^ n)‖
        ≤ K * (δ / 2 ^ n) :=
          h_step_uniform (δ / 2 ^ n) (δ / 2 ^ (n + 1))
            (div_pos hδ_pos (by positivity)) h_le h_ratio (h_dyadic_lt n)
      _ = K * δ / 2 ^ n := by ring
  obtain ⟨limit_dyadic, h_limit_tendsto⟩ : ∃ L, Tendsto (fun n => I (δ / 2 ^ n)) atTop (𝓝 L) :=
    CompleteSpace.complete (cauchySeq_pv_dyadic hδ_pos hK_pos h_step)
  refine ⟨limit_dyadic, ?_⟩
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη_pos
  rw [Metric.tendsto_atTop] at h_limit_tendsto
  obtain ⟨N₁, hN₁⟩ := h_limit_tendsto (η / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, K * δ / 2 ^ N₂ < η / 4 := by
    have h_tendsto : Tendsto (fun n : ℕ => K * δ / 2 ^ n) atTop (𝓝 0) := by
      have h_tendsto_inv : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
        simp_rw [one_div]
        exact tendsto_inv_atTop_zero.comp
          (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
      simpa using (Tendsto.const_mul (K * δ) h_tendsto_inv).congr
        (fun n => show K * δ * (1 / (2 : ℝ) ^ n) = K * δ / 2 ^ n by ring)
    rw [Metric.tendsto_atTop] at h_tendsto
    obtain ⟨N₂, hN₂⟩ := h_tendsto (η / 4) (by linarith)
    refine ⟨N₂, ?_⟩
    have := hN₂ N₂ le_rfl
    rwa [Real.dist_eq, sub_zero,
      abs_of_pos (div_pos (mul_pos hK_pos hδ_pos) (by positivity))] at this
  let N := max N₁ N₂
  refine ⟨δ / 2 ^ N, div_pos hδ_pos (by positivity), fun ε hε_dist hε_pos => ?_⟩
  have hε_pos' : 0 < ε := hε_dist
  have hε_lt_dyadic : ε < δ / 2 ^ N := by
    rwa [Real.dist_eq, sub_zero, abs_of_pos hε_pos'] at hε_pos
  have h_first : dist (I ε) (I (δ / 2 ^ N)) ≤ 2 * K * δ / 2 ^ N := by
    rw [dist_eq_norm]
    have hε_le_δ : ε ≤ δ := hε_lt_dyadic.le.trans
      (div_le_self hδ_pos.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
    obtain ⟨M, hM_lower, hM_upper⟩ := exists_dyadic_bracket hδ_pos hε_pos' hε_le_δ
    have hM_ge_N : M ≥ N := by
      by_contra! h_lt
      have h_div_ge : δ / 2 ^ (M + 1) ≥ δ / 2 ^ N :=
        div_le_div_of_nonneg_left hδ_pos.le (by positivity)
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_lt)
      linarith
    have h_first_piece : ‖I ε - I (δ / 2 ^ M)‖ ≤ K * δ / 2 ^ M := by
      have h_ratio_M : δ / 2 ^ M ≤ 2 * ε := by
        have : δ / 2 ^ M = 2 * (δ / 2 ^ (M + 1)) := by rw [pow_succ]; ring
        linarith
      calc ‖I ε - I (δ / 2 ^ M)‖
          ≤ K * (δ / 2 ^ M) :=
            h_step_uniform (δ / 2 ^ M) ε hε_pos' hM_upper h_ratio_M (h_dyadic_lt M)
        _ = K * δ / 2 ^ M := by ring
    by_cases hMN : M = N
    · subst hMN
      calc ‖I ε - I (δ / 2 ^ N)‖
          ≤ K * δ / 2 ^ N := h_first_piece
        _ ≤ K * δ / 2 ^ N + K * δ / 2 ^ N := by
            linarith [show (0:ℝ) ≤ K * δ / 2 ^ N by positivity]
        _ = 2 * K * δ / 2 ^ N := by ring
    · have h_sum_bound : ‖I (δ / 2 ^ M) - I (δ / 2 ^ N)‖ ≤
          2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ M :=
        telescoping_sum_bound (I := fun n => I (δ / 2 ^ n)) hK_pos hδ_pos h_step N M
          (Nat.lt_of_le_of_ne hM_ge_N (Ne.symm hMN))
      calc ‖I ε - I (δ / 2 ^ N)‖
          ≤ ‖I ε - I (δ / 2 ^ M)‖ + ‖I (δ / 2 ^ M) - I (δ / 2 ^ N)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ K * δ / 2 ^ M + (2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ M) := by
            linarith [h_first_piece, h_sum_bound]
        _ = 2 * K * δ / 2 ^ N - K * δ / 2 ^ M := by ring
        _ ≤ 2 * K * δ / 2 ^ N := by
            linarith [show (0 : ℝ) ≤ K * δ / 2 ^ M by positivity]
  have h_Kδ_bound : K * δ / 2 ^ N < η / 4 :=
    (div_le_div_of_nonneg_left (mul_nonneg hK_pos.le hδ_pos.le) (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (le_max_right _ _))).trans_lt hN₂
  have h_first_small : 2 * K * δ / 2 ^ N < η / 2 := by
    rw [show 2 * K * δ / 2 ^ N = 2 * (K * δ / 2 ^ N) by ring,
        show (η : ℝ) / 2 = 2 * (η / 4) by ring]
    exact mul_lt_mul_of_pos_left h_Kδ_bound (by norm_num : (0 : ℝ) < 2)
  calc dist (I ε) limit_dyadic
      ≤ dist (I ε) (I (δ / 2 ^ N)) + dist (I (δ / 2 ^ N)) limit_dyadic :=
        dist_triangle _ _ _
    _ < η / 2 + η / 2 := by linarith [hN₁ N (le_max_left _ _)]
    _ = η := by ring

/-- The set where a complex-valued continuous-on function exceeds `ε` in norm,
intersected with the (measurable) domain, is measurable. -/
lemma measurableSet_norm_gt_of_continuousOn {f : ℝ → ℂ} {s : Set ℝ}
    (ε : ℝ) (hf : ContinuousOn f s) (hs : MeasurableSet s) :
    MeasurableSet ({t | ε < ‖f t‖} ∩ s) := by
  have h_norm_cont : ContinuousOn (fun t => ‖f t‖) s := hf.norm
  have h_open_sub : IsOpen ((s.restrict (fun t => ‖f t‖)) ⁻¹' Ioi ε) :=
    isOpen_Ioi.preimage h_norm_cont.restrict
  rw [isOpen_induced_iff] at h_open_sub
  obtain ⟨U, hU_open, hU_eq⟩ := h_open_sub
  have h_eq : {t | ε < ‖f t‖} ∩ s = U ∩ s := by
    ext x
    refine ⟨fun ⟨hx_far, hx_s⟩ => ⟨?_, hx_s⟩, fun ⟨hx_U, hx_s⟩ => ⟨?_, hx_s⟩⟩
    · have : (⟨x, hx_s⟩ : ↑s) ∈ Subtype.val ⁻¹' U := by rw [hU_eq]; exact hx_far
      exact this
    · have : (⟨x, hx_s⟩ : ↑s) ∈ (s.restrict fun t => ‖f t‖) ⁻¹' Ioi ε := by
        rw [← hU_eq]; exact hx_U
      exact this
  rw [h_eq]
  exact hU_open.measurableSet.inter hs

/-- Specialisation of `measurableSet_norm_gt_of_continuousOn` to closed intervals. -/
lemma measurableSet_norm_gt_Icc {f : ℝ → ℂ} {a b : ℝ}
    (ε : ℝ) (hf : ContinuousOn f (Icc a b)) :
    MeasurableSet ({t | ε < ‖f t‖} ∩ Icc a b) :=
  measurableSet_norm_gt_of_continuousOn ε hf isClosed_Icc.measurableSet

/-- AE strong measurability of the principal-value integrand on `[a, b]` for a piecewise
`C¹` curve, with derivative continuous off a finite exceptional set `P`. -/
theorem aEStronglyMeasurable_pv_integrand_piecewiseC1
    {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {ε : ℝ} {P : Finset ℝ}
    (hf : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ : ContinuousOn γ (Icc a b))
    (hγ'_off_P : ContinuousOn (deriv γ) ((Icc a b) \ P)) :
    AEStronglyMeasurable (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0)
      (volume.restrict (Icc a b)) := by
  let S := {t | ε < ‖γ t - z₀‖}
  have hS_meas : MeasurableSet (S ∩ Icc a b) :=
    measurableSet_norm_gt_Icc ε (hγ.sub continuousOn_const)
  have h_notBall : ∀ {s}, ε < ‖γ s - z₀‖ → γ s ∉ Metric.ball z₀ ε := fun hs => by
    simp only [Metric.mem_ball, not_lt, dist_eq_norm]; exact hs.le
  have h_cont : ContinuousOn (fun t => f (γ t) * deriv γ t)
      ((S ∩ Icc a b) \ P) := by
    intro t ⟨⟨ht_S, ht_Icc⟩, ht_nP⟩
    have hγt_in : γ t ∈ γ '' Icc a b \ Metric.ball z₀ ε :=
      ⟨mem_image_of_mem γ ht_Icc, h_notBall ht_S⟩
    have h_maps : MapsTo γ ((S ∩ Icc a b) \ P) (γ '' Icc a b \ Metric.ball z₀ ε) :=
      fun _ ⟨⟨hs_S, hs_Icc⟩, _⟩ => ⟨mem_image_of_mem γ hs_Icc, h_notBall hs_S⟩
    exact ((hf (γ t) hγt_in).comp
      ((hγ t ht_Icc).mono (diff_subset.trans inter_subset_right)) h_maps).mul
      ((hγ'_off_P t ⟨ht_Icc, ht_nP⟩).mono
        (fun x ⟨⟨_, hx_Icc⟩, hx_nP⟩ => ⟨hx_Icc, hx_nP⟩))
  have h_base_meas : AEStronglyMeasurable (fun t => f (γ t) * deriv γ t)
      (volume.restrict (S ∩ Icc a b)) := by
    have h_diff_meas : MeasurableSet ((S ∩ Icc a b) \ P) :=
      hS_meas.diff P.finite_toSet.measurableSet
    have hP_meas_zero : volume (↑P ∩ (S ∩ Icc a b)) = 0 :=
      (P.finite_toSet.inter_of_left _).measure_zero volume
    have hP_inter_meas : MeasurableSet (↑P ∩ (S ∩ Icc a b)) :=
      P.finite_toSet.measurableSet.inter hS_meas
    have h_disj : Disjoint ((S ∩ Icc a b) \ P) (↑P ∩ (S ∩ Icc a b)) :=
      disjoint_left.mpr fun _ ⟨_, hx_nP⟩ ⟨hx_P, _⟩ => hx_nP hx_P
    have h_eq : volume.restrict (S ∩ Icc a b) =
        volume.restrict ((S ∩ Icc a b) \ P) +
          volume.restrict (↑P ∩ (S ∩ Icc a b)) := by
      rw [← Measure.restrict_union h_disj hP_inter_meas]
      congr 1
      ext x; simp [mem_union, mem_diff, mem_inter_iff]; tauto
    rw [h_eq]
    apply AEStronglyMeasurable.add_measure (h_cont.aestronglyMeasurable (μ := volume) h_diff_meas)
    simp only [Measure.restrict_eq_zero.mpr hP_meas_zero]
    exact aestronglyMeasurable_zero_measure _
  have h_piecewise : AEStronglyMeasurable
      ((S ∩ Icc a b).piecewise (fun t => f (γ t) * deriv γ t) (fun _ => (0 : ℂ))) volume :=
    AEStronglyMeasurable.piecewise hS_meas h_base_meas aestronglyMeasurable_const
  have h_eq : (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0)
      =ᵐ[volume.restrict (Icc a b)]
      (S ∩ Icc a b).piecewise (fun t => f (γ t) * deriv γ t) (fun _ => 0) := by
    filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
    by_cases ht_S : t ∈ S
    · simp [piecewise, show t ∈ S ∩ Icc a b from ⟨ht_S, ht⟩, show ε < ‖γ t - z₀‖ from ht_S]
    · simp only [S, mem_setOf_eq, not_lt] at ht_S
      simp [piecewise, show ¬t ∈ S ∩ Icc a b from fun h => not_lt.mpr ht_S h.1,
        not_lt.mpr ht_S]
  exact (h_piecewise.mono_measure Measure.restrict_le_self).congr h_eq.symm

/-- If the principal-value cutoff integral for the shifted curve `γ - c` converges to `L`,
then the Cauchy principal value of `1 / (z - c)` along `γ` exists. -/
lemma cpv_exists_from_shifted_tendsto (γ : ℝ → ℂ) (a b : ℝ) (c : ℂ) (L : ℂ)
    (h : Tendsto (fun ε => ∫ t in a..b, if ‖γ t - c‖ > ε
      then (γ t - c)⁻¹ * deriv (fun s => γ s - c) t else 0) (𝓝[>] 0) (𝓝 L)) :
    CauchyPrincipalValueExists' (fun z => (z - c)⁻¹) γ a b c := by
  refine ⟨L, h.congr fun ε => intervalIntegral.integral_congr fun t _ => ?_⟩
  simp [deriv_sub_const]

/-- The map `t ↦ exp (π (1 + t) / 6 · i)` is injective on the open interval `(1, 3)`. -/
lemma arc_angle_injective {t t' : ℝ}
    (ht : t ∈ Set.Ioo (1:ℝ) 3) (ht' : t' ∈ Set.Ioo (1:ℝ) 3)
    (h_eq : Complex.exp (↑(Real.pi * (1 + t) / 6) * I) =
            Complex.exp (↑(Real.pi * (1 + t') / 6) * I)) :
    t = t' := by
  rw [Complex.exp_eq_exp_iff_exists_int] at h_eq
  obtain ⟨n, hn⟩ := h_eq
  have h_vals : Real.pi * (1 + t) / 6 - Real.pi * (1 + t') / 6 = 2 * Real.pi * ↑n := by
    have h2 : (↑(Real.pi * (1 + t) / 6 - Real.pi * (1 + t') / 6) : ℂ) * I =
        ↑(2 * Real.pi * ↑n) * I := by
      rw [show (↑(Real.pi * (1 + t) / 6 - Real.pi * (1 + t') / 6) : ℂ) * I =
            ↑(Real.pi * (1 + t) / 6) * I - ↑(Real.pi * (1 + t') / 6) * I by
          push_cast; ring, hn]
      push_cast
      ring
    exact_mod_cast Complex.ofReal_injective (mul_right_cancel₀ I_ne_zero h2)
  have h_diff_small : |Real.pi * (1 + t) / 6 - Real.pi * (1 + t') / 6| < Real.pi := by
    rw [abs_lt]
    constructor <;> nlinarith [Real.pi_pos, ht.1, ht.2, ht'.1, ht'.2]
  have hn0 : n = 0 := by
    by_contra h_ne
    have h1 : |(n : ℝ)| ≥ 1 := by exact_mod_cast Int.one_le_abs h_ne
    have h3 : |2 * Real.pi * (n : ℝ)| < Real.pi := by rwa [h_vals] at h_diff_small
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at h3
    nlinarith [Real.pi_pos]
  rw [hn0] at h_vals
  simp only [Int.cast_zero, mul_zero] at h_vals
  nlinarith [Real.pi_ne_zero, Real.pi_pos]

/-- CPV trivially exists when the curve avoids `z₀` on `[a, b]`. -/
lemma cpv_avoidance (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (h_cont : ContinuousOn γ (Set.Icc a b)) (hab : a ≤ b)
    (h_avoid : ∀ t ∈ Set.Icc a b, γ t ≠ z₀) :
    CauchyPrincipalValueExists' f γ a b z₀ :=
  cauchyPrincipalValueExists'_of_avoidance h_cont hab h_avoid

/-- CPV on adjacent intervals can be concatenated (when `a ≤ b ≤ c`). -/
lemma cpv_concat (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b c : ℝ) (z₀ : ℂ)
    (h_ab : CauchyPrincipalValueExists' f γ a b z₀)
    (h_bc : CauchyPrincipalValueExists' f γ b c z₀)
    (hab : a ≤ b) (hbc : b ≤ c)
    (h_int : ∀ ε > 0, IntervalIntegrable
        (fun t => if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0) volume a c) :
    CauchyPrincipalValueExists' f γ a c z₀ :=
  let ⟨_, hL₁⟩ := h_ab
  let ⟨_, hL₂⟩ := h_bc
  ⟨_, hL₁.concat hL₂ hab hbc h_int⟩

end
