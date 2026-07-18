/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Auxiliary lemmas for dimension formulas

This file contains auxiliary material for proving
`SpherePacking/ModularForms/DimensionFormulas.lean:517` (`dim_gen_cong_levels`).

Strategy: reduce finite-dimensionality for a finite-index subgroup `Γ ≤ SL(2,ℤ)` to the level-one
case via the norm map `ModularForm.norm`, and use the `q`-expansion principle at `∞` to construct a
finite-dimensional embedding.
-/

namespace SpherePacking.ModularForms

open scoped Topology Real
open UpperHalfPlane Filter

noncomputable section

local notation "𝕢" => Function.Periodic.qParam

section Tendsto

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ} {F : Type*} [FunLike F ℍ ℂ]

/-- Values of a modular form tend to `valueAtInfty` along `atImInfty`. -/
public lemma modularForm_tendsto_valueAtInfty [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    Tendsto (fun τ : ℍ ↦ f τ) atImInfty (𝓝 (valueAtInfty f)) := by
  have hAn := ModularFormClass.analyticAt_cuspFunction_zero (f := f) hh hΓ
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have ht : Tendsto (fun τ : ℍ ↦ f τ) atImInfty (𝓝 (cuspFunction h f 0)) := by
    refine Filter.Tendsto.congr (fun τ ↦ ?_)
      ((hAn.continuousAt.tendsto).comp (UpperHalfPlane.qParam_tendsto_atImInfty hh))
    simpa using (SlashInvariantFormClass.eq_cuspFunction (f := f) (h := h) τ hΓ hh.ne')
  simpa [UpperHalfPlane.cuspFunction_apply_zero hh hAn hper] using ht

end Tendsto

section BigO

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ} {F : Type*} [FunLike F ℍ ℂ]

/-- If the first `N` `q`-coefficients vanish, then the cusp function is `O(‖q‖^N)` near `0`. -/
public lemma cuspFunction_isBigO_pow_of_qExpansion_coeff_eq_zero
    [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (N : ℕ)
    (hcoeff : ∀ n < N, (qExpansion h f).coeff n = 0) :
    cuspFunction h f =O[𝓝 (0 : ℂ)] (fun q : ℂ ↦ ‖q‖ ^ N) := by
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have hAn := ModularFormClass.analyticAt_cuspFunction_zero (f := f) hh hΓ
  have hhol := ModularFormClass.holo f
  have hbdd := ModularFormClass.bdd_at_infty f
  have hFPS : HasFPowerSeriesAt (cuspFunction h f)
      (qExpansionFormalMultilinearSeries (F := F) h f) 0 :=
    (hasFPowerSeries_cuspFunction (F := F) f hh hAn
      (fun τ ↦ hasSum_qExpansion hh hper hhol hbdd τ)).hasFPowerSeriesAt
  have hps : (qExpansionFormalMultilinearSeries (F := F) h f).partialSum N = 0 := by
    ext q
    exact Finset.sum_eq_zero fun n hn ↦ by
      simp [hcoeff n (by simpa [Finset.mem_range] using hn)]
  simpa [zero_add, hps] using hFPS.isBigO_sub_partialSum_pow N

private lemma norm_cuspFunction_div_pow_le_of_ball_bound
    [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (f : F) {C' δ : ℝ} {N n : ℕ} (hn : n < N) (hC' : 0 ≤ C')
    (hδ : Metric.ball (0 : ℂ) δ ⊆ {z | ‖cuspFunction h f z‖ ≤ C' * ‖z‖ ^ N})
    {R : ℝ} (hR0 : 0 < R) (hRltδ : R < δ) (hRlt1 : R < 1) {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) R) :
    ‖cuspFunction h f z / z ^ (n + 1)‖ ≤ C' := by
  have hzR : ‖z‖ = R := by simpa [mem_sphere_zero_iff_norm] using hz
  have hz_norm_ne : (‖z‖ : ℝ) ≠ 0 := by simpa [hzR] using hR0.ne'
  have hcz : ‖cuspFunction h f z‖ ≤ C' * ‖z‖ ^ N :=
    hδ (by simpa [Metric.mem_ball, dist_zero_right, hzR] using hRltδ)
  have hpow_le : ‖z‖ ^ N ≤ ‖z‖ ^ (n + 1) :=
    pow_le_pow_of_le_one (norm_nonneg _) (by simpa [hzR] using hRlt1.le)
      (Nat.succ_le_of_lt hn)
  calc
    ‖cuspFunction h f z / z ^ (n + 1)‖
        = ‖cuspFunction h f z‖ / ‖z‖ ^ (n + 1) := by simp only [norm_div, norm_pow]
    _ ≤ (C' * ‖z‖ ^ (n + 1)) / ‖z‖ ^ (n + 1) := by
      gcongr
      exact hcz.trans (by gcongr)
    _ = C' := by field_simp

private lemma norm_circleIntegral_cuspFunction_div_pow_le
    [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (f : F) {C' δ : ℝ} {N n : ℕ} (hn : n < N) (hC' : 0 ≤ C')
    (hδ : Metric.ball (0 : ℂ) δ ⊆ {z | ‖cuspFunction h f z‖ ≤ C' * ‖z‖ ^ N})
    {R : ℝ} (hR0 : 0 < R) (hRltδ : R < δ) (hRlt1 : R < 1) :
    ‖∮ (z : ℂ) in C(0, R), cuspFunction h f z / z ^ (n + 1)‖ ≤ 2 * π * R * C' :=
  circleIntegral.norm_integral_le_of_norm_le_const hR0.le fun _ hz ↦
    norm_cuspFunction_div_pow_le_of_ball_bound (f := f) hn hC' hδ hR0 hRltδ hRlt1 hz

/-- If `cuspFunction h f = O(‖q‖^N)` near `0`, then the `n`-th `q`-coefficient vanishes. -/
public lemma qExpansion_coeff_eq_zero_of_cuspFunction_isBigO_pow
    [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {N n : ℕ} (hn : n < N)
    (hO : cuspFunction h f =O[𝓝 (0 : ℂ)] (fun q : ℂ ↦ ‖q‖ ^ N)) :
    (qExpansion h f).coeff n = 0 := by
  rcases Asymptotics.isBigO_iff.1 hO with ⟨C, hC⟩
  set C' : ℝ := max C 1
  have hC'pos : 0 < C' :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hC' : ∀ᶠ q : ℂ in 𝓝 (0 : ℂ), ‖cuspFunction h f q‖ ≤ C' * ‖q‖ ^ N := by
    filter_upwards [hC] with q hq
    refine (by simpa using hq : ‖cuspFunction h f q‖ ≤ C * ‖q‖ ^ N).trans ?_
    gcongr
    exact le_max_left _ _
  rcases Metric.mem_nhds_iff.1 hC' with ⟨δ, hδ0, hδ⟩
  by_contra hne
  set ε : ℝ := ‖(qExpansion h f).coeff n‖ / 2
  have hε : 0 < ε := half_pos (norm_pos_iff.2 hne)
  set K : ℝ := ‖((2 * π * Complex.I : ℂ)⁻¹)‖ * (2 * π * C')
  have hKpos : 0 < K :=
    mul_pos (by simp [Real.pi_ne_zero]) (by positivity)
  set R : ℝ := min (δ / 2) (min (1 / 2) (ε / (2 * K)))
  have hR0 : 0 < R :=
    lt_min (by linarith) (lt_min (by norm_num) (div_pos hε (by positivity)))
  have hRltδ : R < δ := (min_le_left _ _).trans_lt (by linarith)
  have hRlt1 : R < 1 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by norm_num)
  have hRle : R ≤ ε / (2 * K) := (min_le_right _ _).trans (min_le_right _ _)
  have hbound_int :
      ‖∮ (z : ℂ) in C(0, R), cuspFunction h f z / z ^ (n + 1)‖ ≤ 2 * π * R * C' :=
    norm_circleIntegral_cuspFunction_div_pow_le (f := f) hn hC'pos.le hδ hR0 hRltδ hRlt1
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have hcoeff_le : ‖(qExpansion h f).coeff n‖ ≤ K * R := by
    rw [qExpansion_coeff_eq_circleIntegral (f := (f : ℍ → ℂ)) hh hper
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) n hR0 hRlt1]
    have := mul_le_mul_of_nonneg_left hbound_int (norm_nonneg ((2 * π * Complex.I : ℂ)⁻¹))
    simpa [norm_mul, K, mul_assoc, mul_left_comm, mul_comm] using this
  have hRlt : R < ε / K :=
    hRle.trans_lt (div_lt_div_of_pos_left hε hKpos (by nlinarith [hKpos]))
  have hKRlt : K * R < ε := by
    have h := mul_lt_mul_of_pos_left hRlt hKpos
    rwa [mul_div_cancel₀ _ hKpos.ne'] at h
  have : ‖(qExpansion h f).coeff n‖ < ‖(qExpansion h f).coeff n‖ / 2 := hcoeff_le.trans_lt hKRlt
  linarith [norm_nonneg ((qExpansion h f).coeff n)]

end BigO

end

end SpherePacking.ModularForms
