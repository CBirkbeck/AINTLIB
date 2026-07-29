/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.RingTheory.Noetherian.Basic
import ModularCurves.ForMathlib.CechSupportContraction
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCech

/-!
# Degree-one contraction of ordered support-restricted Cech cochains

This file gives the ordered degree-one specialization of the support contraction used in
[Stacks Project, Lemma 30.8.1 (Tag 01XT)](https://stacks.math.columbia.edu/tag/01XT).
For an index outside the required support, insertion into an ordered singleton contracts every
degree-one cocycle.
-/

open Set

namespace ModularCurves

noncomputable section

universe u v

variable (R : Type u) {ι : Type v} [CommRing R] [LinearOrder ι]

private def orderedCechSingleton (i : ι) :
    AlgebraicGeometry.Scheme.Modules.OrderedCechIndex ι 0 :=
  ⟨![i], by
    apply Fin.strictMono_iff_lt_succ.2
    intro k
    exact Fin.elim0 k⟩

private def orderedCechPair (i j : ι) (hij : i < j) :
    AlgebraicGeometry.Scheme.Modules.OrderedCechIndex ι 1 :=
  ⟨![i, j], by
    apply Fin.strictMono_iff_lt_succ.2
    intro k
    fin_cases k
    exact hij⟩

private def orderedCechTriple (i j k : ι) (hij : i < j) (hjk : j < k) :
    AlgebraicGeometry.Scheme.Modules.OrderedCechIndex ι 2 :=
  ⟨![i, j, k], by
    apply Fin.strictMono_iff_lt_succ.2
    intro l
    fin_cases l
    · exact hij
    · exact hjk⟩

@[simp]
private theorem orderedCechPair_delete_zero (i j : ι) (hij : i < j) :
    (orderedCechPair i j hij).delete 0 = orderedCechSingleton j := by
  apply Subtype.ext
  funext k
  fin_cases k
  rfl

@[simp]
private theorem orderedCechPair_delete_one (i j : ι) (hij : i < j) :
    (orderedCechPair i j hij).delete 1 = orderedCechSingleton i := by
  apply Subtype.ext
  funext k
  fin_cases k
  rfl

@[simp]
private theorem orderedCechTriple_delete_zero (i j k : ι)
    (hij : i < j) (hjk : j < k) :
    (orderedCechTriple i j k hij hjk).delete 0 = orderedCechPair j k hjk := by
  apply Subtype.ext
  funext l
  fin_cases l <;> rfl

@[simp]
private theorem orderedCechTriple_delete_one (i j k : ι)
    (hij : i < j) (hjk : j < k) :
    (orderedCechTriple i j k hij hjk).delete 1 =
      orderedCechPair i k (hij.trans hjk) := by
  apply Subtype.ext
  funext l
  fin_cases l <;> rfl

@[simp]
private theorem orderedCechTriple_delete_two (i j k : ι)
    (hij : i < j) (hjk : j < k) :
    (orderedCechTriple i j k hij hjk).delete 2 = orderedCechPair i j hij := by
  apply Subtype.ext
  funext l
  fin_cases l <;> rfl

/-- Ordered Cech cochains supported on tuples whose range contains `N`. -/
def OrderedCechSupportCochain (N : Set ι) (n : ℕ) :
    Submodule R
      (AlgebraicGeometry.Scheme.Modules.OrderedCechIndex ι n → R) where
  carrier := {s | ∀ a, ¬N ⊆ Set.range a.1 → s a = 0}
  zero_mem' := by
    intro a ha
    rfl
  add_mem' := by
    intro s t hs ht a ha
    simp [hs a ha, ht a ha]
  smul_mem' := by
    intro r s hs a ha
    simp [hs a ha]

/-- Ordered support-restricted Cech cochains on a finite index type form a finite module over a
Noetherian coefficient ring. -/
theorem OrderedCechSupportCochain.module_finite
    [IsNoetherianRing R] [Finite ι] (N : Set ι) (n : ℕ) :
    Module.Finite R (OrderedCechSupportCochain R N n) := by
  letI : Finite (AlgebraicGeometry.Scheme.Modules.OrderedCechIndex ι n) :=
    Subtype.finite
  letI : IsNoetherian R
      (AlgebraicGeometry.Scheme.Modules.OrderedCechIndex ι n → R) := inferInstance
  letI : IsNoetherian R (OrderedCechSupportCochain R N n) :=
    isNoetherian_of_submodule_of_noetherian R _ _ inferInstance
  infer_instance

private theorem orderedCechDelete_range_subset {n : ℕ}
    (a : AlgebraicGeometry.Scheme.Modules.OrderedCechIndex ι (n + 1))
    (k : Fin (n + 2)) :
    Set.range (a.delete k).1 ⊆ Set.range a.1 := by
  rintro x ⟨l, rfl⟩
  exact ⟨k.succAbove l, rfl⟩

/-- The alternating deletion differential on ordered support-restricted Cech cochains. -/
def orderedCechSupportDifferential (N : Set ι) (n : ℕ) :
    OrderedCechSupportCochain R N n →ₗ[R]
      OrderedCechSupportCochain R N (n + 1) where
  toFun s :=
    ⟨fun a => ∑ k : Fin (n + 2),
        (-1 : R) ^ (k : ℕ) * s.1 (a.delete k),
      fun a ha => by
        apply Finset.sum_eq_zero
        intro k hk
        have hdelete : ¬N ⊆ Set.range (a.delete k).1 :=
          fun hN => ha (Subset.trans hN (orderedCechDelete_range_subset a k))
        rw [s.2 _ hdelete, mul_zero]⟩
  map_add' s t := by
    apply Subtype.ext
    funext a
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_add]
  map_smul' r s := by
    apply Subtype.ext
    funext a
    simp only [Submodule.coe_smul_of_tower, Pi.smul_apply,
      RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ac_rfl

private theorem orderedCechPair_left_not_subset {N : Set ι} {i₀ : ι}
    (hi₀ : i₀ ∉ N)
    (a : AlgebraicGeometry.Scheme.Modules.OrderedCechIndex ι 0)
    (ha : ¬N ⊆ Set.range a.1) (h : i₀ < a.1 0) :
    ¬N ⊆ Set.range (orderedCechPair i₀ (a.1 0) h).1 := by
  intro hN
  apply ha
  intro x hx
  rcases hN hx with ⟨k, hk⟩
  fin_cases k
  · have hix : i₀ = x := by
      simpa [orderedCechPair] using hk
    subst x
    exact (hi₀ hx).elim
  · exact ⟨0, by simpa [orderedCechPair] using hk⟩

private theorem orderedCechPair_right_not_subset {N : Set ι} {i₀ : ι}
    (hi₀ : i₀ ∉ N)
    (a : AlgebraicGeometry.Scheme.Modules.OrderedCechIndex ι 0)
    (ha : ¬N ⊆ Set.range a.1) (h : a.1 0 < i₀) :
    ¬N ⊆ Set.range (orderedCechPair (a.1 0) i₀ h).1 := by
  intro hN
  apply ha
  intro x hx
  rcases hN hx with ⟨k, hk⟩
  fin_cases k
  · exact ⟨0, by simpa [orderedCechPair] using hk⟩
  · have hix : i₀ = x := by
      simpa [orderedCechPair] using hk
    subst x
    exact (hi₀ hx).elim

private def orderedCechSupportContractionOne (N : Set ι) (i₀ : ι)
    (hi₀ : i₀ ∉ N) :
    OrderedCechSupportCochain R N 1 →ₗ[R]
      OrderedCechSupportCochain R N 0 where
  toFun s :=
    ⟨fun a =>
        if h : i₀ < a.1 0 then s.1 (orderedCechPair i₀ (a.1 0) h)
        else if h : a.1 0 < i₀ then -s.1 (orderedCechPair (a.1 0) i₀ h)
        else 0,
      fun a ha => by
        dsimp
        split_ifs with hleft hright
        · exact s.2 _ (orderedCechPair_left_not_subset hi₀ a ha hleft)
        · rw [s.2 _ (orderedCechPair_right_not_subset hi₀ a ha hright), neg_zero]
        · rfl⟩
  map_add' s t := by
    apply Subtype.ext
    funext a
    simp only [Submodule.coe_add, Pi.add_apply]
    split_ifs <;> simp
    all_goals abel
  map_smul' r s := by
    apply Subtype.ext
    funext a
    simp only [Submodule.coe_smul_of_tower, Pi.smul_apply,
      RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp

private theorem orderedCechSupportContractionOne_apply_left {N : Set ι}
    {i₀ x : ι} (hi₀ : i₀ ∉ N) (h : i₀ < x)
    (s : OrderedCechSupportCochain R N 1) :
    (orderedCechSupportContractionOne R N i₀ hi₀ s).1
        (orderedCechSingleton x) =
      s.1 (orderedCechPair i₀ x h) := by
  simp [orderedCechSupportContractionOne, orderedCechSingleton, h]

private theorem orderedCechSupportContractionOne_apply_right {N : Set ι}
    {i₀ x : ι} (hi₀ : i₀ ∉ N) (h : x < i₀)
    (s : OrderedCechSupportCochain R N 1) :
    (orderedCechSupportContractionOne R N i₀ hi₀ s).1
        (orderedCechSingleton x) =
      -s.1 (orderedCechPair x i₀ h) := by
  simp [orderedCechSupportContractionOne, orderedCechSingleton, h,
    not_lt_of_ge h.le]

private theorem orderedCechSupportContractionOne_apply_self {N : Set ι}
    (i₀ : ι) (hi₀ : i₀ ∉ N)
    (s : OrderedCechSupportCochain R N 1) :
    (orderedCechSupportContractionOne R N i₀ hi₀ s).1
        (orderedCechSingleton i₀) = 0 := by
  simp [orderedCechSupportContractionOne, orderedCechSingleton]

private theorem orderedCechSupportDifferential_zero_apply_pair (N : Set ι)
    (t : OrderedCechSupportCochain R N 0)
    (i j : ι) (hij : i < j) :
    (orderedCechSupportDifferential R N 0 t).1
        (orderedCechPair i j hij) =
      t.1 (orderedCechSingleton j) - t.1 (orderedCechSingleton i) := by
  simp [orderedCechSupportDifferential, Fin.sum_univ_succ, sub_eq_add_neg]

/-- If `N` is nonempty and omits an index, the degree-zero ordered support differential is
injective. -/
theorem orderedCechSupportDifferential_zero_injective
    (N : Set ι) (hN : N.Nonempty) (i₀ : ι) (hi₀ : i₀ ∉ N) :
    Function.Injective (orderedCechSupportDifferential R N 0) := by
  intro s t hst
  have hzero : orderedCechSupportDifferential R N 0 (s - t) = 0 := by
    rw [map_sub, hst, sub_self]
  have hi₀_not_subset : ¬N ⊆ Set.range (orderedCechSingleton i₀).1 := by
    intro hsubset
    obtain ⟨i, hi⟩ := hN
    obtain ⟨k, hk⟩ := hsubset hi
    have hik : i = i₀ := by
      fin_cases k
      exact hk.symm
    exact hi₀ (hik ▸ hi)
  have hi₀_value : (s - t).1 (orderedCechSingleton i₀) = 0 :=
    (s - t).2 (orderedCechSingleton i₀) hi₀_not_subset
  have hsub : s - t = 0 := by
    apply Subtype.ext
    funext a
    change (s - t).1 a = 0
    by_cases ha : N ⊆ Set.range a.1
    · obtain ⟨i, hi⟩ := hN
      obtain ⟨k, hk⟩ := ha hi
      have hia : i = a.1 0 := by
        fin_cases k
        exact hk.symm
      have ha_mem : a.1 0 ∈ N := hia ▸ hi
      have hi₀_ne : i₀ ≠ a.1 0 := by
        intro h
        exact hi₀ (h.symm ▸ ha_mem)
      have ha_singleton : a = orderedCechSingleton (a.1 0) := by
        apply Subtype.ext
        funext k
        fin_cases k
        rfl
      rcases lt_or_gt_of_ne hi₀_ne with hi₀a | hai₀
      · have hp :
            (orderedCechSupportDifferential R N 0 (s - t)).1
                (orderedCechPair i₀ (a.1 0) hi₀a) = 0 := by
          rw [hzero]
          rfl
        rw [orderedCechSupportDifferential_zero_apply_pair, hi₀_value,
          sub_zero] at hp
        exact (congrArg (fun b => (s - t).1 b) ha_singleton).trans hp
      · have hp :
            (orderedCechSupportDifferential R N 0 (s - t)).1
                (orderedCechPair (a.1 0) i₀ hai₀) = 0 := by
          rw [hzero]
          rfl
        rw [orderedCechSupportDifferential_zero_apply_pair, hi₀_value,
          zero_sub] at hp
        have hp' : (s - t).1 (orderedCechSingleton (a.1 0)) = 0 :=
          neg_eq_zero.mp hp
        exact (congrArg (fun b => (s - t).1 b) ha_singleton).trans hp'
    · exact (s - t).2 a ha
  exact sub_eq_zero.mp hsub

/-- On a nontrivial index type, every nonempty support has injective degree-zero ordered support
differential. -/
theorem orderedCechSupportDifferential_zero_injective_of_nonempty
    [Nontrivial ι] (N : Set ι) (hN : N.Nonempty) :
    Function.Injective (orderedCechSupportDifferential R N 0) := by
  by_cases htop : N = Set.univ
  · intro s t _
    apply Subtype.ext
    funext a
    have hnot : ¬N ⊆ Set.range a.1 := by
      intro hsubset
      obtain ⟨i, hi⟩ := exists_ne (a.1 0)
      have hiN : i ∈ N := by
        rw [htop]
        exact Set.mem_univ i
      obtain ⟨k, hk⟩ := hsubset hiN
      fin_cases k
      exact hi hk.symm
    rw [s.2 a hnot, t.2 a hnot]
  · have hnot : ¬(Set.univ : Set ι) ⊆ N := by
      intro hsubset
      exact htop (Set.Subset.antisymm (Set.subset_univ N) hsubset)
    obtain ⟨i₀, _, hi₀⟩ := Set.not_subset.mp hnot
    exact orderedCechSupportDifferential_zero_injective R N hN i₀ hi₀

private theorem orderedCechSupport_cycle_triple (N : Set ι)
    (s : OrderedCechSupportCochain R N 1)
    (hs : orderedCechSupportDifferential R N 1 s = 0)
    (i j k : ι) (hij : i < j) (hjk : j < k) :
    s.1 (orderedCechPair j k hjk) -
        s.1 (orderedCechPair i k (hij.trans hjk)) +
      s.1 (orderedCechPair i j hij) = 0 := by
  have h := congrArg
    (fun t : OrderedCechSupportCochain R N 2 =>
      t.1 (orderedCechTriple i j k hij hjk)) hs
  simpa [orderedCechSupportDifferential, Fin.sum_univ_succ,
    sub_eq_add_neg, add_assoc] using h

private theorem orderedCechIndex_one_eq_pair
    (a : AlgebraicGeometry.Scheme.Modules.OrderedCechIndex ι 1) :
    a = orderedCechPair (a.1 0) (a.1 1) (a.2 (by decide)) := by
  apply Subtype.ext
  funext k
  fin_cases k <;> rfl

/-- If one index lies outside `N`, every ordered degree-one support cocycle is a boundary. -/
theorem exists_preimage_orderedCechSupportDifferential_zero
    (N : Set ι) (i₀ : ι) (hi₀ : i₀ ∉ N)
    (s : OrderedCechSupportCochain R N 1)
    (hs : orderedCechSupportDifferential R N 1 s = 0) :
    ∃ t : OrderedCechSupportCochain R N 0,
      orderedCechSupportDifferential R N 0 t = s := by
  refine ⟨orderedCechSupportContractionOne R N i₀ hi₀ s, ?_⟩
  apply Subtype.ext
  funext a
  rw [orderedCechIndex_one_eq_pair a]
  let i := a.1 0
  let j := a.1 1
  have hij : i < j := a.2 (by decide)
  rw [orderedCechSupportDifferential_zero_apply_pair]
  rcases lt_trichotomy i₀ i with h₀i | rfl | hi₀'
  · rw [orderedCechSupportContractionOne_apply_left R hi₀ (h₀i.trans hij),
      orderedCechSupportContractionOne_apply_left R hi₀ h₀i]
    have hcycle := orderedCechSupport_cycle_triple R N s hs i₀ i j h₀i hij
    linear_combination -hcycle
  · rw [orderedCechSupportContractionOne_apply_left R hi₀ hij,
      orderedCechSupportContractionOne_apply_self R i hi₀]
    simp [i, j]
  · rcases lt_trichotomy i₀ j with h₀j | rfl | hj₀
    · rw [orderedCechSupportContractionOne_apply_left R hi₀ h₀j,
        orderedCechSupportContractionOne_apply_right R hi₀ hi₀']
      have hcycle := orderedCechSupport_cycle_triple R N s hs i i₀ j hi₀' h₀j
      linear_combination hcycle
    · rw [orderedCechSupportContractionOne_apply_self R j hi₀,
        orderedCechSupportContractionOne_apply_right R hi₀ hi₀']
      simp [i, j]
    · rw [orderedCechSupportContractionOne_apply_right R hi₀ hj₀,
        orderedCechSupportContractionOne_apply_right R hi₀ hi₀']
      have hcycle := orderedCechSupport_cycle_triple R N s hs i j i₀ hij hj₀
      linear_combination -hcycle

end

end ModularCurves
