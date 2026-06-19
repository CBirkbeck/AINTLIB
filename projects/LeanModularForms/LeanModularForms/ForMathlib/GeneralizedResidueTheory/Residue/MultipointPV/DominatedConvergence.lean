/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue.MultipointPV

/-!
# Multi-point PV: Dominated Convergence

The dominated convergence machinery for decomposing multi-point principal
values into sums of single-point principal values. Contains the pointwise
a.e. limit, norm bounds, measurability, and the main convergence theorems.

## Main Results

* `dominated_convergence_multipoint_helper` — core DCT for multi-point PV
* `multipointPV_diff_tendsto` — difference integrand converges
* `multipointPV_eq_sum_of_integral_zero` — multi-point PV equals sum of
  single-point PVs when regular integral vanishes
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

private lemma continuousOn_deriv_off_partition (γ : PiecewiseC1Immersion) :
    ContinuousOn (deriv γ.toFun) (Icc γ.a γ.b \ γ.partition) := by
  intro t ⟨ht_Icc, ht_notP⟩
  by_cases ht_Ioo : t ∈ Ioo γ.a γ.b
  · exact (γ.toPiecewiseC1Curve.deriv_continuous_off_partition
        t ht_Ioo ht_notP).continuousWithinAt
  · have ht_endpoint : t = γ.a ∨ t = γ.b := by
      simp only [Set.mem_Ioo, not_and, not_lt] at ht_Ioo
      rcases ht_Icc.1.lt_or_eq with h | h
      · exact Or.inr (le_antisymm ht_Icc.2 (ht_Ioo h))
      · exact Or.inl h.symm
    rcases ht_endpoint with rfl | rfl
    · exact (ht_notP γ.toPiecewiseC1Curve.endpoints_in_partition.1).elim
    · exact (ht_notP γ.toPiecewiseC1Curve.endpoints_in_partition.2).elim

private lemma uIoc_subset_Icc_of_lt {a b : ℝ} (hab : a < b) : Set.uIoc a b ⊆ Icc a b :=
  Set.uIoc_of_le (le_of_lt hab) ▸ Set.Ioc_subset_Icc_self

private lemma γt_not_mem_S0_of_all_far {S0 : Finset ℂ} {γ : ℝ → ℂ} {t : ℝ} {ε : ℝ}
    (hε : 0 < ε) (hall : ∀ s ∈ S0, ε < ‖γ t - s‖) :
    γ t ∉ (S0 : Set ℂ) := fun h_in ↦ by
  have := hall (γ t) (Finset.mem_coe.mp h_in)
  simp only [sub_self, norm_zero] at this
  linarith

private lemma residue_sum_ifs_eq_mul_deriv {S0 : Finset ℂ} {f : ℂ → ℂ} {γ : ℝ → ℂ}
    {t : ℝ} {ε : ℝ} (hall : ∀ s ∈ S0, ε < ‖γ t - s‖) :
    ∑ s ∈ S0, (if ε < ‖γ t - s‖ then residueSimplePole f s / (γ t - s) * deriv γ t
      else 0) = (∑ s ∈ S0, residueSimplePole f s / (γ t - s)) * deriv γ t := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun s hs ↦ if_pos (hall s hs)

private lemma residueSimplePole_norm_bound (S0 : Finset ℂ) (f : ℂ → ℂ)
    (hS0_ne : S0.Nonempty) :
    ∃ Mc : ℝ, ∀ s ∈ S0, ‖residueSimplePole f s‖ ≤ Mc :=
  ⟨S0.sup' hS0_ne (fun s ↦ ‖residueSimplePole f s‖),
    fun _ hs ↦ Finset.le_sup' (fun s ↦ ‖residueSimplePole f s‖) hs⟩

private lemma dominated_convergence_empty_case (f g_reg : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hg_decomp : ∀ z, z ∉ (∅ : Finset ℂ) → f z = g_reg z + ∑ s ∈ (∅ : Finset ℂ),
      residueSimplePole f s / (z - s)) :
    let M := fun ε ↦ ∫ t in γ.a..γ.b,
      cpvIntegrandOn ∅ f γ.toFun ε t
    let S' := fun ε ↦ ∑ s ∈ (∅ : Finset ℂ).attach,
      ∫ t in γ.a..γ.b, if ‖γ.toFun t - s.val‖ > ε
        then (residueSimplePole f s.val / (γ.toFun t - s.val)) * deriv γ.toFun t else 0
    let A := fun ε ↦ M ε - S' ε
    let G := ∫ t in γ.a..γ.b, g_reg (γ.toFun t) * deriv γ.toFun t
    Tendsto A (𝓝[>] 0) (𝓝 G) := by
  intro M S' A G
  have hf_eq_g : ∀ z, f z = g_reg z := fun z ↦ by
    have h := hg_decomp z (Finset.notMem_empty z)
    simpa using h
  apply Filter.Tendsto.congr' (f₁ := fun _ ↦ G) _ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with ε _
  simp only [A, S', M, G, Finset.attach_empty, Finset.sum_empty, sub_zero]
  refine (intervalIntegral.integral_congr fun t _ ↦ ?_).symm
  simp only [cpvIntegrandOn, Finset.notMem_empty, false_and,
    exists_false, ↓reduceIte, hf_eq_g (γ.toFun t)]

private lemma pointwise_ae_limit_off_crossing (S0 : Finset ℂ) (f g_reg : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (hS0_ne : S0 ≠ ∅)
    (h_crossing_null : MeasureTheory.volume
      {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t ∈ (S0 : Set ℂ)} = 0)
    (hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s)) :
    let A_int : ℝ → ℝ → ℂ := fun ε t ↦
      cpvIntegrandOn S0 f γ.toFun ε t -
        ∑ s ∈ S0, if ‖γ.toFun t - s‖ > ε
          then (residueSimplePole f s / (γ.toFun t - s)) * deriv γ.toFun t else 0
    let f_lim : ℝ → ℂ := fun t ↦ g_reg (γ.toFun t) * deriv γ.toFun t
    ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b →
      Tendsto (fun ε ↦ A_int ε t) (𝓝[>] 0) (𝓝 (f_lim t)) := by
  intro A_int f_lim
  rw [ae_iff]
  apply le_antisymm _ bot_le
  calc volume {t | ¬(t ∈ Ι γ.a γ.b →
          Tendsto (fun ε ↦ A_int ε t) (𝓝[>] 0) (𝓝 (f_lim t)))}
      ≤ volume {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t ∈ (S0 : Set ℂ)} := by
        apply MeasureTheory.measure_mono
        intro t ht
        simp only [Set.mem_setOf_eq, Classical.not_imp] at ht
        obtain ⟨ht_in, ht_not_tendsto⟩ := ht
        refine ⟨(Set.uIcc_of_le γ.hab.le) ▸ Set.uIoc_subset_uIcc ht_in, ?_⟩
        by_contra ht_not_in_S0
        apply ht_not_tendsto
        let δ := S0.inf' (Finset.nonempty_iff_ne_empty.mpr hS0_ne) (fun s ↦ ‖γ.toFun t - s‖)
        have hδ_pos : 0 < δ := by
          simp only [δ, Finset.lt_inf'_iff, norm_pos_iff, sub_ne_zero]
          exact fun s hs heq ↦ ht_not_in_S0 (heq ▸ hs)
        apply Filter.Tendsto.congr' _ tendsto_const_nhds
        filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε ⟨_, hε_small⟩
        simp only [A_int, f_lim]
        have hall_far : ∀ s ∈ S0, ε < ‖γ.toFun t - s‖ :=
          fun s hs ↦ hε_small.trans_le (Finset.inf'_le _ hs)
        simp only [cpvIntegrandOn,
          if_neg (by push Not; exact hall_far : ¬ ∃ s ∈ S0, ‖γ.toFun t - s‖ ≤ ε),
          residue_sum_ifs_eq_mul_deriv hall_far, ← sub_mul]
        rw [show f (γ.toFun t) - ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s) =
          g_reg (γ.toFun t) by rw [hg_decomp (γ.toFun t) ht_not_in_S0]; ring]
    _ = 0 := h_crossing_null

private lemma norm_A_int_bound_all_far (S0 : Finset ℂ) (f g_reg : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (Mg Mγ' : ℝ)
    (hMg : ∀ z ∈ γ.toFun '' Icc γ.a γ.b, ‖g_reg z‖ ≤ Mg)
    (hMγ' : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Mγ')
    (hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s))
    {t ε : ℝ} (hε : 0 < ε) (ht : t ∈ Icc γ.a γ.b)
    (hall : ∀ s ∈ S0, ε < ‖γ.toFun t - s‖) (B : ℝ)
    (hB : max 0 Mg * max 0 Mγ' ≤ B) :
    ‖cpvIntegrandOn S0 f γ.toFun ε t -
      ∑ s ∈ S0, (if ‖γ.toFun t - s‖ > ε
        then residueSimplePole f s / (γ.toFun t - s) * deriv γ.toFun t else 0)‖ ≤ B := by
  simp only [cpvIntegrandOn]
  rw [if_neg (by push Not; exact hall), residue_sum_ifs_eq_mul_deriv hall, ← sub_mul,
    show f (γ.toFun t) - ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s) =
      g_reg (γ.toFun t) by
        rw [hg_decomp (γ.toFun t) (γt_not_mem_S0_of_all_far hε hall)]; ring]
  have h_g_bound : ‖g_reg (γ.toFun t)‖ ≤ Mg := hMg (γ.toFun t) ⟨t, ht, rfl⟩
  have h_γ'_bound : ‖deriv γ.toFun t‖ ≤ Mγ' := hMγ' t ht
  calc ‖g_reg (γ.toFun t) * deriv γ.toFun t‖
      ≤ ‖g_reg (γ.toFun t)‖ * ‖deriv γ.toFun t‖ := norm_mul_le _ _
    _ ≤ Mg * Mγ' :=
        mul_le_mul h_g_bound h_γ'_bound (norm_nonneg _) ((norm_nonneg _).trans h_g_bound)
    _ ≤ max 0 Mg * max 0 Mγ' :=
        mul_le_mul (le_max_right _ _) (le_max_right _ _)
          ((norm_nonneg _).trans h_γ'_bound) (le_max_left _ _)
    _ ≤ B := hB

private lemma residue_sum_norm_le_singular_bound {S0 : Finset ℂ} {f : ℂ → ℂ} {z : ℂ}
    {Mc δ ε : ℝ} (hδ_pos : 0 < δ)
    (hMc : ∀ s ∈ S0, ‖residueSimplePole f s‖ ≤ Mc)
    (hδ_sep : ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖)
    {s₀ : ℂ} (hs₀ : s₀ ∈ S0) (hs₀_near : ‖z - s₀‖ ≤ ε) :
    ∀ s ∈ S0, ‖if ‖z - s‖ > ε then residueSimplePole f s / (z - s) else 0‖ ≤
      2 * Mc / δ := by
  intro s hs
  by_cases h_inc : ‖z - s‖ > ε
  · simp only [h_inc, ↓reduceIte]
    have h_dist : δ / 2 ≤ ‖z - s‖ := by
      by_cases hs_eq : s = s₀
      · exact absurd (hs_eq ▸ h_inc) (not_lt.mpr hs₀_near)
      · have h_sep : δ ≤ ‖s - s₀‖ := norm_sub_rev s₀ s ▸ hδ_sep s hs s₀ hs₀ hs_eq
        have h_tri : ‖s - s₀‖ - ‖z - s₀‖ ≤ ‖z - s‖ :=
          calc ‖s - s₀‖ - ‖z - s₀‖
              ≤ ‖(s - s₀) - (z - s₀)‖ := norm_sub_norm_le _ _
            _ = ‖s - z‖ := by ring_nf
            _ = ‖z - s‖ := norm_sub_rev _ _
        by_cases hε_small' : ε ≤ δ / 2
        · linarith [h_tri]
        · linarith [h_inc]
    have hMc_nonneg : 0 ≤ Mc := (norm_nonneg _).trans (hMc s hs)
    calc ‖residueSimplePole f s / (z - s)‖
        = ‖residueSimplePole f s‖ / ‖z - s‖ := norm_div _ _
      _ ≤ Mc / ‖z - s‖ := div_le_div_of_nonneg_right (hMc s hs) (norm_nonneg _)
      _ ≤ Mc / (δ / 2) := div_le_div_of_nonneg_left hMc_nonneg (by linarith) h_dist
      _ = 2 * Mc / δ := by ring
  · simp only [h_inc, ↓reduceIte, norm_zero]
    have : 0 ≤ Mc := (norm_nonneg _).trans (hMc s₀ hs₀)
    positivity

private lemma norm_A_int_bound_some_near (S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (Mc Mγ' δ : ℝ) (hδ_pos : 0 < δ)
    (hMc : ∀ s ∈ S0, ‖residueSimplePole f s‖ ≤ Mc)
    (hMγ' : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Mγ')
    (hδ_sep : ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖)
    {t ε : ℝ} (ht : t ∈ Icc γ.a γ.b) {s₀ : ℂ} (hs₀ : s₀ ∈ S0) (hs₀_near : ‖γ.toFun t - s₀‖ ≤ ε)
    (B : ℝ) (hB : max 0 (2 * (S0.card : ℝ) * Mc / δ) * max 0 Mγ' ≤ B) :
    ‖cpvIntegrandOn S0 f γ.toFun ε t -
      ∑ s ∈ S0, (if ‖γ.toFun t - s‖ > ε
        then residueSimplePole f s / (γ.toFun t - s) * deriv γ.toFun t else 0)‖ ≤ B := by
  simp only [cpvIntegrandOn]
  rw [if_pos ⟨s₀, hs₀, hs₀_near⟩]
  simp only [zero_sub, norm_neg]
  have h_γ'_bound : ‖deriv γ.toFun t‖ ≤ Mγ' := hMγ' t ht
  have h_factor :
      ∑ s ∈ S0, (if ‖γ.toFun t - s‖ > ε
        then residueSimplePole f s / (γ.toFun t - s) * deriv γ.toFun t else 0) =
      (∑ s ∈ S0, if ‖γ.toFun t - s‖ > ε
        then residueSimplePole f s / (γ.toFun t - s) else 0) * deriv γ.toFun t := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    by_cases h : ‖γ.toFun t - s‖ > ε
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte, zero_mul]
  rw [h_factor]
  set singularBound := 2 * (S0.card : ℝ) * Mc / δ
  have hMc_nonneg : 0 ≤ Mc := (norm_nonneg _).trans (hMc s₀ hs₀)
  have h_sb_nonneg : 0 ≤ singularBound := by positivity
  have h_sum_bound : ‖∑ s ∈ S0, if ‖γ.toFun t - s‖ > ε
      then residueSimplePole f s / (γ.toFun t - s) else 0‖ ≤ singularBound :=
    calc ‖∑ s ∈ S0, if ‖γ.toFun t - s‖ > ε
            then residueSimplePole f s / (γ.toFun t - s) else 0‖
        ≤ ∑ s ∈ S0, ‖if ‖γ.toFun t - s‖ > ε
            then residueSimplePole f s / (γ.toFun t - s) else 0‖ := norm_sum_le _ _
      _ ≤ ∑ _s ∈ S0, (2 * Mc / δ) :=
          Finset.sum_le_sum (residue_sum_norm_le_singular_bound hδ_pos hMc hδ_sep hs₀ hs₀_near)
      _ = singularBound := by simp only [Finset.sum_const]; ring
  calc ‖(∑ s ∈ S0, if ‖γ.toFun t - s‖ > ε
          then residueSimplePole f s / (γ.toFun t - s) else 0) * deriv γ.toFun t‖
      ≤ singularBound * Mγ' :=
        (norm_mul_le _ _).trans (mul_le_mul h_sum_bound h_γ'_bound (norm_nonneg _) h_sb_nonneg)
    _ ≤ max 0 singularBound * max 0 Mγ' :=
        mul_le_mul (le_max_right _ _) (le_max_right _ _)
          ((norm_nonneg _).trans h_γ'_bound) (le_max_left _ _)
    _ ≤ B := hB

private lemma A_int_norm_bound (S0 : Finset ℂ) (f g_reg : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (Mg Mγ' Mc δ : ℝ) (hδ_pos : 0 < δ)
    (hMg : ∀ z ∈ γ.toFun '' Icc γ.a γ.b, ‖g_reg z‖ ≤ Mg)
    (hMγ' : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Mγ')
    (hMc : ∀ s ∈ S0, ‖residueSimplePole f s‖ ≤ Mc)
    (hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s))
    (hδ_sep : ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖) :
    let B := max 1 (max (max 0 Mg) (max 0 (2 * (S0.card : ℝ) * Mc / δ)) * max 0 Mγ')
    ∀ ε > 0, ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b →
      ‖cpvIntegrandOn S0 f γ.toFun ε t -
        ∑ s ∈ S0, (if ‖γ.toFun t - s‖ > ε
          then (residueSimplePole f s / (γ.toFun t - s)) * deriv γ.toFun t
          else 0)‖ ≤ B := by
  intro B ε hε
  refine ae_of_all _ fun t ht ↦ ?_
  have ht_Icc : t ∈ Icc γ.a γ.b := uIoc_subset_Icc_of_lt γ.hab ht
  by_cases hall : ∀ s ∈ S0, ε < ‖γ.toFun t - s‖
  · exact norm_A_int_bound_all_far S0 f g_reg γ Mg Mγ' hMg hMγ' hg_decomp hε ht_Icc hall B
      ((mul_le_mul_of_nonneg_right (le_max_left _ _) (le_max_left 0 Mγ')).trans
        (le_max_right _ _))
  · push Not at hall
    obtain ⟨s₀, hs₀, hs₀_near⟩ := hall
    exact norm_A_int_bound_some_near S0 f γ Mc Mγ' δ hδ_pos hMc hMγ' hδ_sep ht_Icc hs₀
      hs₀_near B ((mul_le_mul_of_nonneg_right (le_max_right _ _) (le_max_left 0 Mγ')).trans
        (le_max_right _ _))

private lemma A_int_aEStronglyMeasurable (S0 : Finset ℂ) (f g_reg : ℂ → ℂ)
    (γ : PiecewiseC1Immersion)
    (hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s))
    (hg_cont : ContinuousOn g_reg (γ.toFun '' Icc γ.a γ.b)) {ε : ℝ} (hε : 0 < ε) :
    AEStronglyMeasurable
      (fun t ↦ cpvIntegrandOn S0 f γ.toFun ε t -
        ∑ s ∈ S0, if ‖γ.toFun t - s‖ > ε
          then (residueSimplePole f s / (γ.toFun t - s)) * deriv γ.toFun t else 0)
      (volume.restrict (Ι γ.a γ.b)) := by
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  have hγ'_off_P := continuousOn_deriv_off_partition γ
  have h_eq_decomposed : ∀ t,
      cpvIntegrandOn S0 f γ.toFun ε t =
      (if ∃ s ∈ S0, ‖γ.toFun t - s‖ ≤ ε then 0
        else (g_reg (γ.toFun t) + ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s)) *
          deriv γ.toFun t) := fun t ↦ by
    simp only [cpvIntegrandOn]
    split_ifs with h_near
    · rfl
    · push Not at h_near
      rw [hg_decomp (γ.toFun t) (γt_not_mem_S0_of_all_far hε h_near)]
  have h_meas_pv : AEStronglyMeasurable (cpvIntegrandOn S0 f γ.toFun ε)
      (volume.restrict (Icc γ.a γ.b)) :=
    (aEStronglyMeasurable_pv_integrand_decomposed S0 (residueSimplePole f) hε hg_cont
      hγ_cont hγ'_off_P).congr (ae_of_all _ (fun t ↦ (h_eq_decomposed t).symm))
  exact (h_meas_pv.sub (aEStronglyMeasurable_pv_sum_residue S0 f γ.toFun ε hε γ.a γ.b hγ_cont
    hγ'_off_P)).mono_measure (Measure.restrict_mono (uIoc_subset_Icc_of_lt γ.hab) le_rfl)

private lemma pvIntegrand_intervalIntegrable_of_nonempty (S0 : Finset ℂ) (f g_reg : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (hS0_ne : S0 ≠ ∅)
    (hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s))
    (hg_cont : ContinuousOn g_reg (γ.toFun '' Icc γ.a γ.b)) {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable (cpvIntegrandOn S0 f γ.toFun ε)
      volume γ.a γ.b := by
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  have hγ'_off_P := continuousOn_deriv_off_partition γ
  obtain ⟨Mγ', hMγ'⟩ := piecewiseC1Immersion_deriv_bounded γ
  obtain ⟨Mg, hMg⟩ := continuousOn_image_bounded hγ_cont hg_cont
  have hS0_nonempty : S0.Nonempty := Finset.nonempty_of_ne_empty hS0_ne
  let res_bound := S0.sup' hS0_nonempty (fun s ↦ ‖residueSimplePole f s‖)
  have h_res_nonneg : 0 ≤ res_bound :=
    (norm_nonneg _).trans (Finset.le_sup' (fun s ↦ ‖residueSimplePole f s‖)
      hS0_nonempty.choose_spec)
  let Mb := (|Mg| + S0.card * res_bound / ε) * |Mγ'| + 1
  have h_bound : ∀ t ∈ Icc γ.a γ.b,
      ‖cpvIntegrandOn S0 f γ.toFun ε t‖ ≤ Mb := by
    intro t ht
    simp only [cpvIntegrandOn]
    split_ifs with h
    · simp only [Mb, norm_zero]; positivity
    · push Not at h
      rw [hg_decomp (γ.toFun t) (γt_not_mem_S0_of_all_far hε h)]
      calc ‖(g_reg (γ.toFun t) + ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s)) *
              deriv γ.toFun t‖
          = ‖g_reg (γ.toFun t) + ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s)‖ *
              ‖deriv γ.toFun t‖ := norm_mul _ _
        _ ≤ (|Mg| + S0.card * res_bound / ε) * |Mγ'| := by
            refine mul_le_mul ?_ ((hMγ' t ht).trans (le_abs_self _)) (norm_nonneg _) (by positivity)
            calc ‖g_reg (γ.toFun t) + ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s)‖
                ≤ ‖g_reg (γ.toFun t)‖ +
                    ‖∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s)‖ := norm_add_le _ _
              _ ≤ |Mg| + ∑ s ∈ S0, ‖residueSimplePole f s / (γ.toFun t - s)‖ := by
                  gcongr
                  · exact (hMg _ (Set.mem_image_of_mem _ ht)).trans (le_abs_self _)
                  · exact norm_sum_le _ _
              _ ≤ |Mg| + ∑ _s ∈ S0, res_bound / ε := by
                  gcongr with s hs
                  rw [norm_div]
                  calc ‖residueSimplePole f s‖ / ‖γ.toFun t - s‖
                      ≤ res_bound / ‖γ.toFun t - s‖ :=
                        div_le_div_of_nonneg_right
                          (Finset.le_sup' (fun s ↦ ‖residueSimplePole f s‖) hs) (norm_nonneg _)
                    _ ≤ res_bound / ε :=
                        div_le_div_of_nonneg_left h_res_nonneg hε (h s hs).le
              _ = |Mg| + S0.card * res_bound / ε := by simp only [Finset.sum_const]; ring
        _ ≤ Mb := by simp only [Mb]; linarith
  have h_eq_ae : (fun t ↦ cpvIntegrandOn S0 f γ.toFun ε t)
      =ᵐ[volume.restrict (Icc γ.a γ.b)]
      (fun t ↦ if ∃ s ∈ S0, ‖γ.toFun t - s‖ ≤ ε then (0 : ℂ)
        else (g_reg (γ.toFun t) + ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s)) *
          deriv γ.toFun t) := by
    filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t _
    simp only [cpvIntegrandOn]
    split_ifs with h_near
    · rfl
    · push Not at h_near
      rw [hg_decomp (γ.toFun t) (γt_not_mem_S0_of_all_far hε h_near)]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le γ.hab.le]
  exact (integrableOn_of_bounded_aeMeasurable Mb
    ((aEStronglyMeasurable_pv_integrand_decomposed S0 (residueSimplePole f) hε hg_cont
      hγ_cont hγ'_off_P).congr h_eq_ae.symm) h_bound).mono_set Ioc_subset_Icc_self

private lemma A_eq_integral_A_int (S0 : Finset ℂ) (f g_reg : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hS0_ne : S0 ≠ ∅)
    (hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s))
    (hg_cont : ContinuousOn g_reg (γ.toFun '' Icc γ.a γ.b)) :
    let A_int : ℝ → ℝ → ℂ := fun ε t ↦
      cpvIntegrandOn S0 f γ.toFun ε t -
        ∑ s ∈ S0, if ‖γ.toFun t - s‖ > ε
          then (residueSimplePole f s / (γ.toFun t - s)) * deriv γ.toFun t else 0
    let M := fun ε ↦ ∫ t in γ.a..γ.b, cpvIntegrandOn S0 f γ.toFun ε t
    let S' := fun ε ↦ ∑ s ∈ S0, ∫ t in γ.a..γ.b,
      if ‖γ.toFun t - s‖ > ε then (residueSimplePole f s / (γ.toFun t - s)) *
        deriv γ.toFun t else 0
    ∀ ε > 0, M ε - S' ε = ∫ t in γ.a..γ.b, A_int ε t := by
  intro A_int M S' ε hε
  simp only [A_int, M, S']
  let S_int_fun : ℂ → ℝ → ℂ := fun s t ↦
    if ‖γ.toFun t - s‖ > ε
    then (residueSimplePole f s / (γ.toFun t - s)) * deriv γ.toFun t else 0
  have hS_int : ∀ s ∈ S0, IntervalIntegrable (S_int_fun s) volume γ.a γ.b :=
    fun _ _ ↦ intervalIntegrable_residueTerm hε
  have hSum_int : IntervalIntegrable (fun t ↦ ∑ s ∈ S0, S_int_fun s t) volume γ.a γ.b := by
    simp only [← Finset.sum_apply]
    exact IntervalIntegrable.sum S0 hS_int
  rw [(intervalIntegral.integral_finsetSum hS_int).symm,
    ← intervalIntegral.integral_sub
      (pvIntegrand_intervalIntegrable_of_nonempty S0 f g_reg γ hS0_ne hg_decomp hg_cont hε)
      hSum_int]

/-- Core dominated convergence for multi-point PV decomposition. -/
lemma dominated_convergence_multipoint_helper (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (g_reg : ℂ → ℂ) (_h_crossing_null : MeasureTheory.volume
      {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t ∈ (S0 : Set ℂ)} = 0)
    (_hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s))
    (_hg_cont : ContinuousOn g_reg (γ.toFun '' Icc γ.a γ.b))
    (hS0_sep : ∃ δ > 0, ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖) :
    let M := fun ε ↦ ∫ t in γ.a..γ.b, cpvIntegrandOn S0 f γ.toFun ε t
    let S' := fun ε ↦ ∑ s ∈ S0.attach, ∫ t in γ.a..γ.b,
      if ‖γ.toFun t - s.val‖ > ε
      then (residueSimplePole f s.val / (γ.toFun t - s.val)) * deriv γ.toFun t else 0
    let A := fun ε ↦ M ε - S' ε
    let G := ∫ t in γ.a..γ.b, g_reg (γ.toFun t) * deriv γ.toFun t
    Tendsto A (𝓝[>] 0) (𝓝 G) := by
  intro M S' A G
  by_cases hS0_empty : S0 = ∅
  · subst hS0_empty
    exact dominated_convergence_empty_case f g_reg γ _hg_decomp
  · let A_int : ℝ → ℝ → ℂ := fun ε t ↦
      cpvIntegrandOn S0 f γ.toFun ε t -
        ∑ s ∈ S0, if ‖γ.toFun t - s‖ > ε
          then (residueSimplePole f s / (γ.toFun t - s)) * deriv γ.toFun t else 0
    have h_A_eq_int : ∀ ε > 0, A ε = ∫ t in γ.a..γ.b, A_int ε t := fun ε hε ↦ by
      simp only [A, M, S', A_int,
        Finset.sum_attach S0 (fun s ↦ ∫ t in γ.a..γ.b,
          if ‖γ.toFun t - s‖ > ε then residueSimplePole f s / (γ.toFun t - s) *
            deriv γ.toFun t else 0)]
      exact A_eq_integral_A_int S0 f g_reg γ hS0_empty _hg_decomp _hg_cont ε hε
    obtain ⟨Mg, hMg⟩ := continuousOn_image_bounded γ.toPiecewiseC1Curve.continuous_toFun _hg_cont
    obtain ⟨Mγ', hMγ'⟩ := piecewiseC1Immersion_deriv_bounded γ
    obtain ⟨Mc, hMc⟩ := residueSimplePole_norm_bound S0 f
      (Finset.nonempty_iff_ne_empty.mpr hS0_empty)
    obtain ⟨δ, hδ_pos, hδ_sep⟩ := hS0_sep
    refine Filter.Tendsto.congr' ?_ <| tendsto_integral_of_dominated'
      (fun ε hε ↦ A_int_aEStronglyMeasurable S0 f g_reg γ _hg_decomp _hg_cont hε)
      (A_int_norm_bound S0 f g_reg γ Mg Mγ' Mc δ hδ_pos hMg hMγ' hMc _hg_decomp hδ_sep)
      intervalIntegrable_const
      (pointwise_ae_limit_off_crossing S0 f g_reg γ hS0_empty _h_crossing_null _hg_decomp)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (h_A_eq_int ε hε).symm

/-- Difference integrand converges to regular part integral. -/
lemma multipointPV_diff_tendsto (S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (_h_crossing_null : MeasureTheory.volume
      {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t ∈ (S0 : Set ℂ)} = 0) (g_reg : ℂ → ℂ)
    (_hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s))
    (hg_cont : ContinuousOn g_reg (γ.toFun '' Icc γ.a γ.b))
    (hS0_sep : ∃ δ > 0, ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖) :
    let M := fun ε ↦ ∫ t in γ.a..γ.b, cpvIntegrandOn S0 f γ.toFun ε t
    let S' := fun ε ↦ ∑ s ∈ S0.attach, ∫ t in γ.a..γ.b,
      if ‖γ.toFun t - s.val‖ > ε
      then (residueSimplePole f s.val / (γ.toFun t - s.val)) * deriv γ.toFun t else 0
    let A := fun ε ↦ M ε - S' ε
    let G := ∫ t in γ.a..γ.b, g_reg (γ.toFun t) * deriv γ.toFun t
    Tendsto A (𝓝[>] 0) (𝓝 G) :=
  dominated_convergence_multipoint_helper S0 f γ g_reg _h_crossing_null _hg_decomp
    hg_cont hS0_sep

/-- Multi-point PV equals sum of single-point PVs when the regular part integral vanishes. -/
lemma multipointPV_eq_sum_of_integral_zero (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (_h_crossing_null : MeasureTheory.volume
      {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t ∈ (S0 : Set ℂ)} = 0) (_g_reg : ℂ → ℂ)
    (_hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = _g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s))
    (_hg_cont : ContinuousOn _g_reg (γ.toFun '' Icc γ.a γ.b))
    (_hS0_sep : ∃ δ > 0, ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖)
    (_hg_zero : ∫ t in γ.a..γ.b, _g_reg (γ.toFun t) * deriv γ.toFun t = 0)
    (_hPV_exists : CauchyPrincipalValueExistsOn S0 f γ.toFun γ.a γ.b)
    (_hPV_each_tendsto : Tendsto
      (fun ε ↦ ∑ s ∈ S0, ∫ t in γ.a..γ.b,
        if ‖γ.toFun t - s‖ > ε
        then (residueSimplePole f s / (γ.toFun t - s)) * deriv γ.toFun t else 0)
      (𝓝[>] 0)
      (𝓝 (∑ s ∈ S0, cauchyPrincipalValue'
        (fun z ↦ residueSimplePole f s / (z - s)) γ.toFun γ.a γ.b s))) :
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      ∑ s ∈ S0, cauchyPrincipalValue'
        (fun z ↦ residueSimplePole f s / (z - s)) γ.toFun γ.a γ.b s := by
  obtain ⟨L, hL⟩ := _hPV_exists
  have h_pv_eq_L : cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b = L := hL.limUnder_eq
  have h_A_tendsto := multipointPV_diff_tendsto S0 f γ _h_crossing_null _g_reg _hg_decomp
    _hg_cont _hS0_sep
  simp only [_hg_zero] at h_A_tendsto
  let S'_attach := fun ε ↦ ∑ s ∈ S0.attach, ∫ t in γ.a..γ.b,
    if ‖γ.toFun t - s.val‖ > ε
    then (residueSimplePole f s.val / (γ.toFun t - s.val)) * deriv γ.toFun t else 0
  let S' := fun ε ↦ ∑ s ∈ S0, ∫ t in γ.a..γ.b,
    if ‖γ.toFun t - s‖ > ε
    then (residueSimplePole f s / (γ.toFun t - s)) * deriv γ.toFun t else 0
  have h_S'_eq : S' = S'_attach := by
    ext ε
    simp only [S', S'_attach]
    rw [Finset.sum_attach S0 (fun s ↦ ∫ t in γ.a..γ.b,
      if ‖γ.toFun t - s‖ > ε
      then (residueSimplePole f s / (γ.toFun t - s)) * deriv γ.toFun t else 0)]
  have h_S'_tendsto : Tendsto S' (𝓝[>] 0) (𝓝 L) := by
    rw [h_S'_eq]
    have : Tendsto (fun ε ↦
        (∫ t in γ.a..γ.b, cpvIntegrandOn S0 f γ.toFun ε t) -
        ((∫ t in γ.a..γ.b, cpvIntegrandOn S0 f γ.toFun ε t) - S'_attach ε))
        (𝓝[>] 0) (𝓝 (L - 0)) := hL.sub h_A_tendsto
    simpa [sub_sub_cancel] using this
  rw [h_pv_eq_L, tendsto_nhds_unique h_S'_tendsto _hPV_each_tendsto]

end
