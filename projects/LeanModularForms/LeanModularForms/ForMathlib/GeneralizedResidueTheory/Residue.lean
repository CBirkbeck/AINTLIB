/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.CauchyPrincipalValue
import LeanModularForms.ForMathlib.ClassicalCPV
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.CauchyPrimitive
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Homotopy.Invariance
import LeanModularForms.ForMathlib.Residue
import Mathlib.Topology.Order.ExtendFrom

/-!
# Residue Theory

Multi-point Cauchy principal values, simple pole residues, and the
generalized residue theorem for piecewise C¹ immersions.

## Main Definitions

* `HasCauchyPVOn'` — the **primary API predicate**: the multi-point CPV exists with
  value `L` (Tendsto-based, on a raw curve `γ : ℝ → ℂ` over `[a, b]`).
* `cauchyPrincipalValueOn` — multi-point CPV value (limUnder-based; secondary)
* `CauchyPrincipalValueExistsOn` — abbreviation `∃ L, HasCauchyPVOn' S f γ a b L`
* `HasCauchyPVOn'.cauchyPVOn_eq` — bridge: `HasCauchyPVOn' S f γ a b L → cauchyPrincipalValueOn S f γ a b = L`
* `residueSimplePole` — residue at a simple pole via limit
* `HasSimplePoleAt` (re-exported from `ForMathlib.Residue`) — simple pole decomposition

The multi-point PV integrand `cpvIntegrandOn` is imported from
`LeanModularForms.ForMathlib.CauchyPrincipalValue`.

## Main Results

* `integral_eq_sum_residues_of_avoids` — classical residue theorem
* `pv_integral_simple_pole` — PV of c/(z-s) = 2πi · winding · c
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- The multi-point Cauchy principal value exists with value `L`: the ε-truncated
integral along `γ` over `[a, b]` tends to `L` as `ε → 0⁺`. **Primary API predicate**
(Tendsto-based). -/
def HasCauchyPVOn'
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (a b : ℝ) (L : ℂ) : Prop :=
  Tendsto (fun ε => ∫ t in a..b, cpvIntegrandOn S f γ ε t) (𝓝[>] 0) (𝓝 L)

/-- The multi-point Cauchy principal value (limUnder-based; secondary).
Returns junk when the limit does not exist; use `HasCauchyPVOn'` for the predicate. -/
def cauchyPrincipalValueOn
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (a b : ℝ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    ∫ t in a..b,
      cpvIntegrandOn S f γ ε t

/-- Existence of the multi-point PV; abbreviation `∃ L, HasCauchyPVOn' S f γ a b L`. -/
def CauchyPrincipalValueExistsOn
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (a b : ℝ) : Prop :=
  ∃ L : ℂ, HasCauchyPVOn' S f γ a b L

/-- Bridge theorem: if `HasCauchyPVOn' S f γ a b L`, then `cauchyPrincipalValueOn S f γ a b = L`. -/
theorem HasCauchyPVOn'.cauchyPVOn_eq {S : Finset ℂ} {f : ℂ → ℂ} {γ : ℝ → ℂ}
    {a b : ℝ} {L : ℂ} (h : HasCauchyPVOn' S f γ a b L) :
    cauchyPrincipalValueOn S f γ a b = L :=
  h.limUnder_eq

/-- The limit in `HasCauchyPVOn'` is unique. -/
theorem HasCauchyPVOn'.unique {S : Finset ℂ} {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    {L₁ L₂ : ℂ} (h₁ : HasCauchyPVOn' S f γ a b L₁) (h₂ : HasCauchyPVOn' S f γ a b L₂) :
    L₁ = L₂ :=
  tendsto_nhds_unique h₁ h₂

/-- Residue of f at z₀ via the limit formula
`lim_{z → z₀} (z - z₀) · f(z)`. -/
def residueSimplePole (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[≠] z₀) fun z => (z - z₀) * f z

private lemma bounded_on_Ioo_of_continuousOn_with_limits
    {f : ℝ → ℂ} {a b : ℝ} (_hab : a < b) (hf_cont : ContinuousOn f (Ioo a b))
    (hf_left : ∃ L : ℂ, Tendsto f (𝓝[>] a) (𝓝 L))
    (hf_right : ∃ L : ℂ, Tendsto f (𝓝[<] b) (𝓝 L)) :
    ∃ M : ℝ, ∀ t ∈ Ioo a b, ‖f t‖ ≤ M := by
  obtain ⟨_, hLa⟩ := hf_left
  obtain ⟨_, hLb⟩ := hf_right
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_Icc_extendFrom_Ioo hf_cont hLa hLb)
  exact ⟨M, fun t ht => extendFrom_extends hf_cont t ht ▸
    hM t (Ioo_subset_Icc_self ht)⟩

private lemma deriv_bounded_on_consecutive_pair
    (γ : PiecewiseC1Immersion) {p q : ℝ}
    (hp : p ∈ γ.partition)
    (hq : q ∈ γ.partition)
    (hp_lt_q : p < q)
    (h_consec : ∀ r ∈ γ.partition, ¬(p < r ∧ r < q)) :
    ∃ M : ℝ, ∀ t ∈ Ioo p q,
      ‖deriv γ.toFun t‖ ≤ M := by
  have h_cont : ContinuousOn (deriv γ.toFun) (Ioo p q) := fun s hs =>
    (γ.toPiecewiseC1Curve.deriv_continuous_off_partition s
      ⟨lt_of_le_of_lt (γ.toPiecewiseC1Curve.partition_subset hp).1 hs.1,
       lt_of_lt_of_le hs.2 (γ.toPiecewiseC1Curve.partition_subset hq).2⟩
      (fun hs_P => h_consec s hs_P ⟨hs.1, hs.2⟩)).continuousWithinAt
  obtain ⟨L_left, _, hL_left⟩ := γ.right_deriv_limit p hp
    (lt_of_lt_of_le hp_lt_q (γ.toPiecewiseC1Curve.partition_subset hq).2)
  obtain ⟨L_right, _, hL_right⟩ := γ.left_deriv_limit q hq
    (lt_of_le_of_lt (γ.toPiecewiseC1Curve.partition_subset hp).1 hp_lt_q)
  exact bounded_on_Ioo_of_continuousOn_with_limits hp_lt_q
    h_cont ⟨L_left, hL_left⟩ ⟨L_right, hL_right⟩

private lemma off_partition_in_consecutive_pair
    (γ : PiecewiseC1Immersion) (t : ℝ)
    (ht : t ∈ Icc γ.a γ.b)
    (ht_nP : t ∉ (↑γ.partition : Set ℝ)) :
    ∃ p q, p ∈ γ.partition ∧ q ∈ γ.partition ∧
      p < q ∧ (∀ r ∈ γ.partition, ¬(p < r ∧ r < q)) ∧
      t ∈ Ioo p q := by
  have ha_in_P := γ.toPiecewiseC1Curve.endpoints_in_partition.1
  have hb_in_P := γ.toPiecewiseC1Curve.endpoints_in_partition.2
  have ht_Ioo : t ∈ Ioo γ.a γ.b :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm fun h => ht_nP (h ▸ ha_in_P)),
     lt_of_le_of_ne ht.2 fun h => ht_nP (h ▸ hb_in_P)⟩
  let P_left := γ.partition.filter (· < t)
  let P_right := γ.partition.filter (t < ·)
  have hL : P_left.Nonempty :=
    ⟨γ.a, Finset.mem_filter.mpr ⟨ha_in_P, ht_Ioo.1⟩⟩
  have hR : P_right.Nonempty :=
    ⟨γ.b, Finset.mem_filter.mpr ⟨hb_in_P, ht_Ioo.2⟩⟩
  have hp_lt_t := (Finset.mem_filter.mp
    (Finset.max'_mem P_left hL)).2
  have ht_lt_q := (Finset.mem_filter.mp
    (Finset.min'_mem P_right hR)).2
  refine ⟨P_left.max' hL, P_right.min' hR,
    Finset.filter_subset _ _ (Finset.max'_mem _ hL),
    Finset.filter_subset _ _ (Finset.min'_mem _ hR),
    lt_trans hp_lt_t ht_lt_q,
    fun r hr ⟨hr_gt, hr_lt⟩ => ?_,
    hp_lt_t, ht_lt_q⟩
  by_cases hrt : r < t
  · linarith [Finset.le_max' P_left r
      (Finset.mem_filter.mpr ⟨hr, hrt⟩)]
  · push Not at hrt
    by_cases htr : t < r
    · linarith [Finset.min'_le P_right r
        (Finset.mem_filter.mpr ⟨hr, htr⟩)]
    · exact ht_nP (le_antisymm (not_lt.mp htr) hrt ▸ hr)

/-- The derivative of a piecewise C¹ immersion is bounded on [a,b]. -/
lemma piecewiseC1Immersion_deriv_bounded
    (γ : PiecewiseC1Immersion) :
    ∃ M : ℝ, ∀ t ∈ Icc γ.a γ.b,
      ‖deriv γ.toFun t‖ ≤ M := by
  let P := γ.partition
  let M_part := P.sup'
    ⟨γ.a, γ.toPiecewiseC1Curve.endpoints_in_partition.1⟩
    (fun p => ‖deriv γ.toFun p‖)
  suffices h : ∃ M_off : ℝ, ∀ t ∈ Icc γ.a γ.b,
      t ∉ (↑P : Set ℝ) → ‖deriv γ.toFun t‖ ≤ M_off by
    obtain ⟨M_off, hM_off⟩ := h
    exact ⟨max M_part M_off, fun t ht => by
      by_cases ht_P : t ∈ (↑P : Set ℝ)
      · exact (Finset.le_sup'
          (fun p => ‖deriv γ.toFun p‖) ht_P).trans
          (le_max_left _ _)
      · exact (hM_off t ht ht_P).trans (le_max_right _ _)⟩
  classical
  let pairs := (P ×ˢ P).filter
    (fun (p, q) => p < q ∧ ∀ r ∈ P, ¬(p < r ∧ r < q))
  have h_aux : ∀ S : Finset (ℝ × ℝ), S ⊆ pairs →
      ∃ M : ℝ, ∀ pq ∈ S, ∀ t ∈ Ioo pq.1 pq.2,
        ‖deriv γ.toFun t‖ ≤ M := by
    intro S hS
    induction S using Finset.induction with
    | empty => exact ⟨0, fun pq hpq =>
        (Finset.notMem_empty pq hpq).elim⟩
    | insert pq S' _ ih =>
      obtain ⟨M_S', hM_S'⟩ := ih (Finset.insert_subset_iff.mp hS).2
      have hpq' := Finset.mem_filter.mp (Finset.insert_subset_iff.mp hS).1
      have hpq_prod := Finset.mem_product.mp hpq'.1
      obtain ⟨M_pq, hM_pq⟩ := deriv_bounded_on_consecutive_pair γ
        hpq_prod.1 hpq_prod.2 hpq'.2.1 hpq'.2.2
      exact ⟨max M_pq M_S', fun pq' hpq' t ht => by
        rcases Finset.mem_insert.mp hpq' with rfl | h
        · exact (hM_pq t ht).trans (le_max_left _ _)
        · exact (hM_S' pq' h t ht).trans (le_max_right _ _)⟩
  obtain ⟨M_off, hM_off⟩ := h_aux pairs (Finset.Subset.refl _)
  exact ⟨M_off, fun t ht ht_nP => by
    obtain ⟨p, q, hp, hq, hpq, hc, ht_in⟩ :=
      off_partition_in_consecutive_pair γ t ht ht_nP
    have hmem : (p, q) ∈ pairs := by
      simp only [Finset.mem_filter, Finset.mem_product, pairs]
      exact ⟨⟨hp, hq⟩, hpq, hc⟩
    exact hM_off (p, q) hmem t ht_in⟩

/-- The derivative of a piecewise C¹ curve is interval integrable when bounded. -/
lemma piecewiseC1_deriv_intervalIntegrable (γ : PiecewiseC1Curve)
    (h_bdd : ∃ M : ℝ, ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M) :
    IntervalIntegrable (deriv γ.toFun) MeasureTheory.volume γ.a γ.b := by
  obtain ⟨M, hM⟩ := h_bdd
  rw [intervalIntegrable_iff]
  refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ M ?_
  · simp only [Set.uIoc, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  · exact (aestronglyMeasurable_deriv γ.toFun _).restrict
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    exact .of_forall fun t ht => hM t <|
      Set.uIcc_of_le (le_of_lt γ.hab) ▸ uIoc_subset_uIcc ht

/-- A single singular term is interval integrable when γ avoids s. -/
lemma singular_term_intervalIntegrable
    (f : ℂ → ℂ) (s : ℂ)
    (γ : PiecewiseC1Curve)
    (hγ_avoids_s : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s)
    (hγ'_bdd : ∃ M : ℝ, ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M) :
    IntervalIntegrable
      (fun t => residueSimplePole f s / (γ.toFun t - s) * deriv γ.toFun t)
      MeasureTheory.volume γ.a γ.b :=
  (piecewiseC1_deriv_intervalIntegrable γ hγ'_bdd).continuousOn_mul <|
    Set.uIcc_of_le (le_of_lt γ.hab) ▸ continuousOn_const.div
      (γ.continuous_toFun.sub continuousOn_const)
      fun t ht => sub_ne_zero.mpr (hγ_avoids_s t ht)

/-- The singular sum is interval integrable when curve avoids all poles. -/
lemma singular_sum_intervalIntegrable
    (f : ℂ → ℂ) (S0 : Finset ℂ)
    (γ : PiecewiseC1Curve)
    (hγ_avoids : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s)
    (hγ'_bdd : ∃ M : ℝ, ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M) :
    IntervalIntegrable
      (fun t => ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s) * deriv γ.toFun t)
      MeasureTheory.volume γ.a γ.b := by
  induction S0 using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact intervalIntegrable_const
  | insert s S hs_nin ih =>
    simp only [Finset.sum_insert hs_nin]
    exact (singular_term_intervalIntegrable f s γ
      (fun t ht => hγ_avoids s (Finset.mem_insert_self s S) t ht) hγ'_bdd).add
      (ih fun s' hs' t ht => hγ_avoids s' (Finset.mem_insert_of_mem hs') t ht)

/-- For simple poles, the residue equals the Laurent coefficient. -/
theorem residue_simple_pole_eq_laurent
    (f : ℂ → ℂ) (z₀ : ℂ) (c : ℂ) (g : ℂ → ℂ)
    (hg : AnalyticAt ℂ g z₀)
    (hf : ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z) :
    residueSimplePole f z₀ = c := by
  unfold residueSimplePole
  have h_eq : (fun z => c + (z - z₀) * g z) =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) * f z := by
    filter_upwards [hf, self_mem_nhdsWithin] with z hz hz_ne
    rw [hz]
    field_simp [sub_ne_zero.mpr hz_ne]
  refine ((?_ : Tendsto _ _ _).congr' h_eq).limUnder_eq
  have h_sub : Tendsto (fun z => z - z₀) (𝓝[≠] z₀) (𝓝 0) :=
    ((sub_self z₀ ▸ tendsto_id.sub tendsto_const_nhds :
      Tendsto _ (𝓝 z₀) _)).mono_left nhdsWithin_le_nhds
  have h_prod : Tendsto (fun z => (z - z₀) * g z) (𝓝[≠] z₀) (𝓝 0) := by
    simpa using h_sub.mul (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simpa using tendsto_const_nhds.add h_prod

/-- The integral of a singular term equals the winding number times the coefficient. -/
lemma integral_singular_term_eq_winding_times_coeff
    (γ : PiecewiseC1Curve) (s c : ℂ)
    (h_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, c / (γ.toFun t - s) * deriv γ.toFun t =
      2 * Real.pi * I * generalizedWindingNumber' γ.toFun γ.a γ.b s * c := by
  have h_ne : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨two_ne_zero, by exact_mod_cast Real.pi_ne_zero⟩, Complex.I_ne_zero⟩
  have h_integral : ∫ t in γ.a..γ.b, (γ.toFun t - s)⁻¹ * deriv γ.toFun t =
      2 * Real.pi * I * generalizedWindingNumber' γ.toFun γ.a γ.b s := by
    rw [generalizedWindingNumber_eq_classical_away γ s h_avoids]
    field_simp [h_ne]
  calc ∫ t in γ.a..γ.b, c / (γ.toFun t - s) * deriv γ.toFun t
      = ∫ t in γ.a..γ.b, c * ((γ.toFun t - s)⁻¹ * deriv γ.toFun t) :=
        intervalIntegral.integral_congr fun t _ => by rw [div_eq_mul_inv]; ring
    _ = c * ∫ t in γ.a..γ.b, (γ.toFun t - s)⁻¹ * deriv γ.toFun t :=
        intervalIntegral.integral_smul c _
    _ = 2 * Real.pi * I * generalizedWindingNumber' γ.toFun γ.a γ.b s * c := by
        rw [h_integral]; ring

private lemma differentiableAt_singular_sum
    (f : ℂ → ℂ) (S0 : Finset ℂ) (w : ℂ)
    (hw_not_in_S0 : w ∉ (S0 : Set ℂ)) :
    DifferentiableAt ℂ (fun v => ∑ s ∈ S0, residueSimplePole f s / (v - s)) w := by
  have hh : DifferentiableAt ℂ (∑ s ∈ S0, fun v => residueSimplePole f s / (v - s)) w :=
    .sum fun s hs' => (differentiableAt_const _).div
      (differentiableAt_id.sub (differentiableAt_const s))
      (sub_ne_zero.mpr fun heq => hw_not_in_S0 (heq ▸ Finset.mem_coe.mpr hs'))
  convert hh using 1
  ext v
  simp only [Finset.sum_apply]

private lemma differentiableAt_g_off_poles
    (U : Set ℂ) (hU : IsOpen U) (S0 : Finset ℂ)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (w : ℂ) (hw_in_U : w ∈ U) (hw_not_in_S0 : w ∉ (S0 : Set ℂ)) :
    DifferentiableAt ℂ (fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s)) w :=
  have hw' : w ∈ U \ (S0 : Set ℂ) := ⟨hw_in_U, hw_not_in_S0⟩
  ((hf w hw').differentiableAt
    ((hU.sdiff S0.finite_toSet.isClosed).mem_nhds hw')).sub
    (differentiableAt_singular_sum f S0 w hw_not_in_S0)

private lemma continuousAt_g_at_pole
    (S0 : Finset ℂ) (f : ℂ → ℂ) (z : ℂ) (hs : z ∈ S0)
    (hf_ext : ContinuousAt (fun w => f w - residueSimplePole f z / (w - z)) z) :
    ContinuousAt (fun w => f w - ∑ s ∈ S0, residueSimplePole f s / (w - s)) z := by
  have h2 : ContinuousAt
      (fun w => ∑ s ∈ S0.filter (· ≠ z), residueSimplePole f s / (w - s)) z :=
    tendsto_finsetSum _ fun s hs' => by
      simp only [Finset.mem_filter] at hs'
      exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.mpr (Ne.symm hs'.2))).tendsto
  have hg_eq_at : ∀ w, f w - ∑ s ∈ S0, residueSimplePole f s / (w - s) =
      (f w - residueSimplePole f z / (w - z)) -
      ∑ s ∈ S0.filter (· ≠ z), residueSimplePole f s / (w - s) := fun w => by
    rw [show S0.filter (· ≠ z) = S0.erase z from Finset.filter_ne' _ _,
      ← Finset.add_sum_erase _ _ hs]; ring
  exact (funext hg_eq_at ▸ hf_ext.sub h2 : _)

private lemma diff_punctured_of_diff_off_poles
    (U : Set ℂ) (hU : IsOpen U) (S0 : Finset ℂ)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0)) (z : ℂ) (hz : z ∈ U) :
    ∀ᶠ w in 𝓝[≠] z,
      DifferentiableAt ℂ (fun v => f v - ∑ s ∈ S0, residueSimplePole f s / (v - s)) w := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  obtain ⟨ε₁, hε₁_pos, hε₁_subset⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  by_cases h_S0_singleton : (S0 : Set ℂ) ⊆ {z}
  · exact ⟨ε₁, hε₁_pos, fun w hw hw_ne => differentiableAt_g_off_poles U hU S0 f hf w
      (hε₁_subset hw) fun h => Set.mem_compl_singleton_iff.mp hw_ne
        (Set.mem_singleton_iff.mp (h_S0_singleton h))⟩
  · have h_ne : (S0.filter (· ≠ z)).Nonempty := by
      by_contra h_all
      refine h_S0_singleton fun x hx => Set.mem_singleton_iff.mpr <| by
        by_contra hxz
        exact h_all ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hx, hxz⟩⟩
    set δ := (S0.filter (· ≠ z)).inf' h_ne (fun s => ‖s - z‖)
    have hδ_pos : 0 < δ := (Finset.lt_inf'_iff h_ne).mpr fun s hs =>
      norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hs).2)
    refine ⟨min ε₁ δ, lt_min hε₁_pos hδ_pos, fun w hw hw_ne => ?_⟩
    refine differentiableAt_g_off_poles U hU S0 f hf w
      (hε₁_subset (lt_of_lt_of_le hw (min_le_left _ _))) fun hw_in_S0 => ?_
    rcases eq_or_ne w z with rfl | hw_eq
    · exact Set.mem_compl_singleton_iff.mp hw_ne rfl
    · linarith [Finset.inf'_le (fun s => ‖s - z‖) (show w ∈ S0.filter (· ≠ z) from
        Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hw_in_S0, hw_eq⟩),
        (dist_eq_norm w z ▸ show dist w z < δ from
          lt_of_lt_of_le hw (min_le_right _ _) : ‖w - z‖ < δ)]

lemma simple_poles_decomposition
    (U : Set ℂ) (hU : IsOpen U)
    (S0 : Finset ℂ) (_hS0_in_U : ∀ s ∈ S0, s ∈ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (_hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hf_ext : ∀ s ∈ S0, ContinuousAt (fun z => f z - residueSimplePole f s / (z - s)) s) :
    let g := fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s)
    DifferentiableOn ℂ g U ∧
    ∀ z ∈ U \ (S0 : Set ℂ), f z = (∑ s ∈ S0, residueSimplePole f s / (z - s)) + g z := by
  intro g
  refine ⟨fun z hz => ?_, fun z ⟨_, _⟩ => by ring⟩
  by_cases hz_S0 : z ∈ (S0 : Set ℂ)
  · have hs : z ∈ S0 := Finset.mem_coe.mp hz_S0
    exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (diff_punctured_of_diff_off_poles U hU S0 f hf z hz)
      (continuousAt_g_at_pole S0 f z hs (hf_ext z hs))).differentiableAt.differentiableWithinAt
  · exact (differentiableAt_g_off_poles U hU S0 f hf z hz hz_S0).differentiableWithinAt

private lemma holomorphic_closed_integral_zero
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (g : ℂ → ℂ) (hg_diff : DifferentiableOn ℂ g U)
    (γ : PiecewiseC1Curve) (hγ_closed : γ.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hγ'_bdd : ∃ M : ℝ, ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M) :
    ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0 := by
  obtain ⟨F, hF⟩ := holomorphic_convex_primitive hU_convex hU
    ⟨γ.toFun γ.a, hγ_in_U γ.a (left_mem_Icc.mpr (le_of_lt γ.hab))⟩ hg_diff
  have h_Fγ_cont : ContinuousOn (F ∘ γ.toFun) (Icc γ.a γ.b) := fun t ht =>
    (hF (γ.toFun t) (hγ_in_U t ht)).continuousAt.continuousWithinAt.comp
      (γ.continuous_toFun t ht) (mapsTo_image γ.toFun _)
  have h_deriv' : ∀ t ∈ Ioo γ.a γ.b \ (↑γ.partition ∩ Ioo γ.a γ.b),
      HasDerivAt (F ∘ γ.toFun) (g (γ.toFun t) * deriv γ.toFun t) t :=
    fun t ⟨ht, hp⟩ => (hF (γ.toFun t) (hγ_in_U t (Ioo_subset_Icc_self ht))).comp_of_eq t
      (γ.smooth_off_partition t (Ioo_subset_Icc_self ht) fun h => hp ⟨h, ht⟩).hasDerivAt rfl
  have h_int : IntervalIntegrable (fun t => g (γ.toFun t) * deriv γ.toFun t)
      MeasureTheory.volume γ.a γ.b :=
    (piecewiseC1_deriv_intervalIntegrable γ hγ'_bdd).continuousOn_mul
      (Set.uIcc_of_le (le_of_lt γ.hab) ▸
        hg_diff.continuousOn.comp γ.continuous_toFun hγ_in_U)
  rw [MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (F ∘ γ.toFun) _ (le_of_lt γ.hab) (γ.partition.finite_toSet.inter_of_left _).countable
    h_Fγ_cont h_deriv' h_int, Function.comp_apply, Function.comp_apply, hγ_closed, sub_self]

private lemma singular_sum_eq_winding_residues
    (f : ℂ → ℂ) (S0 : Finset ℂ)
    (γ : PiecewiseC1Curve)
    (hγ_avoids : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s)
    (hγ'_bdd : ∃ M : ℝ, ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M) :
    ∫ t in γ.a..γ.b,
      ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s) * deriv γ.toFun t =
    ∑ s ∈ S0, 2 * Real.pi * I *
      generalizedWindingNumber' γ.toFun γ.a γ.b s * residueSimplePole f s := by
  rw [intervalIntegral.integral_finsetSum (s := S0) fun s hs =>
    (piecewiseC1_deriv_intervalIntegrable γ hγ'_bdd).continuousOn_mul
      (Set.uIcc_of_le (le_of_lt γ.hab) ▸
        continuousOn_const.div (γ.continuous_toFun.sub continuousOn_const)
          fun t ht => sub_ne_zero.mpr (hγ_avoids s hs t ht))]
  exact Finset.sum_congr rfl fun s hs =>
    integral_singular_term_eq_winding_times_coeff γ s _ (hγ_avoids s hs)

/-- Classical residue theorem: when γ avoids all poles,
the contour integral equals `2πi · Σ winding · residue`. -/
theorem integral_eq_sum_residues_of_avoids
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (S0 : Finset ℂ) (hS0_in_U : ∀ s ∈ S0, s ∈ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Curve) (hγ_closed : γ.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hγ_avoids : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hf_ext : ∀ s ∈ S0, ContinuousAt
      (fun z => f z - residueSimplePole f s / (z - s)) s)
    (hγ'_bdd : ∃ M : ℝ, ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t =
      2 * Real.pi * I *
        ∑ s ∈ S0, generalizedWindingNumber' γ.toFun γ.a γ.b s *
            residueSimplePole f s := by
  set g := fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s)
  have ⟨hg_diff, hf_decomp⟩ :=
    simple_poles_decomposition U hU S0 hS0_in_U f hf hSimplePoles hf_ext
  have h_rewrite : ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t =
      ∫ t in γ.a..γ.b,
        ((∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s)) + g (γ.toFun t)) *
          deriv γ.toFun t := intervalIntegral.integral_congr fun t ht => by
    rw [Set.uIcc_of_le (le_of_lt γ.hab)] at ht
    rw [hf_decomp (γ.toFun t) ⟨hγ_in_U t ht, fun hs => by
      simp only [Finset.mem_coe] at hs
      exact hγ_avoids _ hs t ht rfl⟩]
  rw [h_rewrite]
  simp_rw [add_mul, Finset.sum_mul]
  rw [intervalIntegral.integral_add
      (singular_sum_intervalIntegrable f S0 γ hγ_avoids hγ'_bdd)
      ((piecewiseC1_deriv_intervalIntegrable γ hγ'_bdd).continuousOn_mul
        (Set.uIcc_of_le (le_of_lt γ.hab) ▸
          hg_diff.continuousOn.comp γ.continuous_toFun hγ_in_U)),
    holomorphic_closed_integral_zero U hU hU_convex g hg_diff γ hγ_closed hγ_in_U hγ'_bdd,
    singular_sum_eq_winding_residues f S0 γ hγ_avoids hγ'_bdd, add_zero, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- PV with empty singular set is just the ordinary contour integral. -/
lemma hasCauchyPVOn'_empty (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) :
    HasCauchyPVOn' ∅ f γ a b (∫ t in a..b, f (γ t) * deriv γ t) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε _
  exact intervalIntegral.integral_congr fun t _ =>
    (cpvIntegrandOn_of_forall_gt (by simp)).symm

/-- PV exists with value equal to the ordinary contour integral when the curve avoids
all singularities. -/
lemma hasCauchyPVOn'_avoids
    (S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Curve)
    (h_avoids : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    HasCauchyPVOn' S0 f γ.toFun γ.a γ.b
      (∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t) := by
  by_cases hS0_empty : S0 = ∅
  · subst hS0_empty; exact hasCauchyPVOn'_empty f γ.toFun γ.a γ.b
  have hS0_ne : S0.Nonempty := Finset.nonempty_of_ne_empty hS0_empty
  have h_cpt : IsCompact (γ.toFun '' Icc γ.a γ.b) :=
    isCompact_Icc.image_of_continuousOn γ.continuous_toFun
  have h_ne : (γ.toFun '' Icc γ.a γ.b).Nonempty :=
    ⟨γ.toFun γ.a, γ.a, left_mem_Icc.mpr (le_of_lt γ.hab), rfl⟩
  let δ_fun : ℂ → ℝ := fun s => Metric.infDist s (γ.toFun '' Icc γ.a γ.b)
  let δ := Finset.min' (S0.image δ_fun) (Finset.image_nonempty.mpr hS0_ne)
  have hδ_pos : 0 < δ := by
    obtain ⟨s, hs, hδ_eq⟩ := Finset.mem_image.mp
      (Finset.min'_mem (S0.image δ_fun) (Finset.image_nonempty.mpr hS0_ne))
    calc (0 : ℝ) < δ_fun s := (h_cpt.isClosed.notMem_iff_infDist_pos h_ne).mp
          fun ⟨t, ht, hts⟩ => h_avoids s hs t ht hts
      _ = δ := hδ_eq
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  rw [Filter.EventuallyEq, Filter.eventually_iff_exists_mem]
  refine ⟨Ioo 0 δ, Ioo_mem_nhdsGT hδ_pos, fun ε ⟨_, hε_lt_δ⟩ => ?_⟩
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le (le_of_lt γ.hab)] at ht
  exact (cpvIntegrandOn_of_forall_gt fun s hs =>
    calc ε < δ := hε_lt_δ
      _ ≤ Metric.infDist s (γ.toFun '' Icc γ.a γ.b) :=
        Finset.min'_le _ _ (Finset.mem_image_of_mem δ_fun hs)
      _ ≤ dist s (γ.toFun t) := Metric.infDist_le_dist_of_mem ⟨t, ht, rfl⟩
      _ = ‖γ.toFun t - s‖ := by rw [dist_eq_norm, norm_sub_rev]).symm

/-- PV exists when curve avoids all singularities. -/
lemma cauchyPrincipalValueExistsOn_avoids
    (S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Curve)
    (h_avoids : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    CauchyPrincipalValueExistsOn S0 f γ.toFun γ.a γ.b :=
  ⟨_, hasCauchyPVOn'_avoids S0 f γ h_avoids⟩

/-- PV value equals classical integral when avoiding. -/
lemma cauchyPrincipalValueOn_avoids
    (S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Curve)
    (h_avoids : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t :=
  (hasCauchyPVOn'_avoids S0 f γ h_avoids).cauchyPVOn_eq

/-- PV of 1/z equals 2πi times winding number. -/
theorem pv_integral_inverse
    (γ : PiecewiseC1Curve) (z₀ : ℂ) :
    cauchyPrincipalValue' (·⁻¹) (fun t => γ.toFun t - z₀) γ.a γ.b 0 =
      2 * Real.pi * I * generalizedWindingNumber' γ.toFun γ.a γ.b z₀ := by
  unfold generalizedWindingNumber'
  have h_ne : (2 * Real.pi * I : ℂ) ≠ 0 := by norm_num [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp [h_ne]

/-- Single-point PV formula for simple pole. -/
theorem pv_integral_simple_pole
    (γ : PiecewiseC1Curve) (z₀ c : ℂ)
    (hPV : ∃ L, Tendsto (fun ε => ∫ t in γ.a..γ.b,
      if ‖(fun s => γ.toFun s - z₀) t - 0‖ > ε
      then (·⁻¹) ((fun s => γ.toFun s - z₀) t) *
        deriv (fun s => γ.toFun s - z₀) t
      else 0) (𝓝[>] 0) (𝓝 L)) :
    cauchyPrincipalValue' (fun z => c / (z - z₀)) γ.toFun γ.a γ.b z₀ =
      2 * Real.pi * I * generalizedWindingNumber' γ.toFun γ.a γ.b z₀ * c := by
  rw [← pv_integral_inverse γ z₀]
  unfold cauchyPrincipalValue'
  have h_integral' : ∀ ε,
      (∫ t in γ.a..γ.b, if ‖γ.toFun t - z₀‖ > ε
        then (fun z => c / (z - z₀)) (γ.toFun t) * deriv γ.toFun t else 0) =
      (∫ t in γ.a..γ.b, if ‖(fun s => γ.toFun s - z₀) t - 0‖ > ε
        then (·⁻¹) ((fun s => γ.toFun s - z₀) t) *
          deriv (fun s => γ.toFun s - z₀) t else 0) * c := fun ε => by
    rw [show (∫ t in γ.a..γ.b, if ‖(fun s => γ.toFun s - z₀) t - 0‖ > ε
        then (·⁻¹) ((fun s => γ.toFun s - z₀) t) *
          deriv (fun s => γ.toFun s - z₀) t else 0) * c =
      ∫ t in γ.a..γ.b, (if ‖(fun s => γ.toFun s - z₀) t - 0‖ > ε
        then (·⁻¹) ((fun s => γ.toFun s - z₀) t) *
          deriv (fun s => γ.toFun s - z₀) t else 0) * c from
      (intervalIntegral.integral_mul_const c _).symm]
    exact intervalIntegral.integral_congr fun t _ => by
      simp only [sub_zero, deriv_sub_const]
      split_ifs <;> [rw [div_eq_mul_inv]; skip] <;> ring
  simp_rw [h_integral']
  obtain ⟨L, hL⟩ := hPV
  exact (hL.mul_const c).limUnder_eq ▸ (hL.limUnder_eq ▸ rfl)

end
