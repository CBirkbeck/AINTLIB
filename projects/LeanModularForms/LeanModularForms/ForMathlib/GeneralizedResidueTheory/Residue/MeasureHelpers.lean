/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ClassicalCPV

/-!
# Measure Theory Helpers for Residue Theory

Countability of isolated point sets and measure-zero results for
preimages of singletons under piecewise C¹ immersions.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

/-- A subset of `ℝ` consisting of points that are uniformly isolated within the set is
countable. -/
theorem Set.countable_setOf_isolated_points' {S : Set ℝ}
    (h : ∀ t ∈ S, ∃ ε > 0, ∀ s ∈ S, s ≠ t → |s - t| ≥ ε) : S.Countable := by
  classical
  by_cases hS : S = ∅
  · simp [hS]
  choose r hr_pos hr_sep using fun t : S ↦ h t.val t.prop
  let ball : S → Set ℝ := fun t ↦ Metric.ball t.val (r t / 2)
  have h_disj : Pairwise (Function.onFun Disjoint ball) := by
    intro ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ h_ne
    simp only [Function.onFun, Set.disjoint_iff, ball]
    intro x ⟨hx₁, hx₂⟩
    simp only [Metric.mem_ball, Real.dist_eq] at hx₁ hx₂
    have h_ne' : t₁ ≠ t₂ := fun heq ↦ h_ne (by simp [heq])
    rw [abs_sub_comm] at hx₁
    have h4 : r ⟨t₁, ht₁⟩ ≤ |t₁ - t₂| := by
      rw [abs_sub_comm]; exact hr_sep ⟨t₁, ht₁⟩ t₂ ht₂ (Ne.symm h_ne')
    have h5 : r ⟨t₂, ht₂⟩ ≤ |t₁ - t₂| := hr_sep ⟨t₂, ht₂⟩ t₁ ht₁ h_ne'
    linarith [hr_pos ⟨t₁, ht₁⟩, hr_pos ⟨t₂, ht₂⟩, abs_sub_le t₁ x t₂]
  have h_open : ∀ t : S, IsOpen (ball t) := fun _ ↦ Metric.isOpen_ball
  have h_nonempty : ∀ t : S, (ball t).Nonempty :=
    fun t ↦ ⟨t.val, Metric.mem_ball_self (by linarith [hr_pos t])⟩
  exact Set.countable_coe_iff.mp
    (Pairwise.countable_of_isOpen_disjoint h_disj h_open h_nonempty)

/-- Preimage of a singleton under a piecewise C¹ immersion has measure zero. -/
theorem preimage_singleton_measure_zero_of_deriv_ne_zero {γ : ℝ → ℂ} {a b : ℝ}
    {P : Finset ℝ} (z₀ : ℂ) (_hγ : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Icc a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ'_ne : ∀ t ∈ Icc a b, t ∉ P → deriv γ t ≠ 0) :
    volume ({t ∈ Icc a b | γ t = z₀}) = 0 := by
  let S := {t ∈ Icc a b | γ t = z₀}
  have h_isolated : ∀ t₀ ∈ S, t₀ ∉ P →
      ∃ ε > 0, ∀ t ∈ S, t ≠ t₀ → |t - t₀| ≥ ε := by
    intro t₀ ⟨ht₀_Icc, _⟩ ht₀_nP
    have h_ev := HasDerivAt.eventually_ne (hγ_diff t₀ ht₀_Icc ht₀_nP).hasDerivAt
      (hγ'_ne t₀ ht₀_Icc ht₀_nP) (c := z₀)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h_ev
    obtain ⟨ε, hε_pos, h_ball⟩ := h_ev
    refine ⟨ε, hε_pos, ?_⟩
    intro t ⟨_, ht_eq⟩ ht_ne
    by_contra! h_lt
    exact h_ball (by simpa [Real.dist_eq] using h_lt) (by simp [ht_ne]) ht_eq
  have h_countable : S.Countable := by
    rw [show S = (S ∩ ↑P) ∪ (S \ ↑P) from (Set.inter_union_diff S ↑P).symm]
    refine Set.Countable.union ?_ ?_
    · exact (P.finite_toSet.subset Set.inter_subset_right).countable
    have h_iso : ∀ t ∈ S \ ↑P, ∃ ε > 0, ∀ s ∈ S \ ↑P, s ≠ t → |s - t| ≥ ε := by
      intro t ⟨ht_S, ht_nP⟩
      obtain ⟨ε, hε_pos, h_sep⟩ := h_isolated t ht_S ht_nP
      exact ⟨ε, hε_pos, fun s ⟨hs_S, _⟩ hs_ne ↦ h_sep s hs_S hs_ne⟩
    exact Set.countable_setOf_isolated_points' h_iso
  exact h_countable.measure_zero _

/-- Preimage of a finite set of points under a piecewise C¹ immersion has measure
zero. Lifts `preimage_singleton_measure_zero_of_deriv_ne_zero` to a finset. -/
theorem preimage_finset_measure_zero_of_deriv_ne_zero {γ : ℝ → ℂ} {a b : ℝ}
    {P : Finset ℝ} (S : Finset ℂ) (hγ : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Icc a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ'_ne : ∀ t ∈ Icc a b, t ∉ P → deriv γ t ≠ 0) :
    volume ({t ∈ Icc a b | γ t ∈ (↑S : Set ℂ)}) = 0 := by
  classical
  have h_eq : {t ∈ Icc a b | γ t ∈ (↑S : Set ℂ)} =
      ⋃ s ∈ (↑S : Set ℂ), {t ∈ Icc a b | γ t = s} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe]
    exact ⟨fun ⟨ht_Icc, hmem⟩ ↦ ⟨γ t, hmem, ht_Icc, rfl⟩,
      fun ⟨_, hs, ht_Icc, hγt⟩ ↦ ⟨ht_Icc, hγt ▸ hs⟩⟩
  rw [h_eq, measure_biUnion_null_iff S.finite_toSet.countable]
  intro s _
  exact preimage_singleton_measure_zero_of_deriv_ne_zero s hγ hγ_diff hγ'_ne

end
