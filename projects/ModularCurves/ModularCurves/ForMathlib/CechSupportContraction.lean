/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Contraction of support-restricted Cech cochains

This file implements the combinatorial contraction in the proof of
[Stacks Project, Lemma 30.8.1 (Tag 01XT)](https://stacks.math.columbia.edu/tag/01XT).
A cochain is supported on tuples whose range contains a fixed set `N`. If `i₀ ∉ N`,
prepending `i₀` gives a contraction of the alternating deletion differential.
-/

open Set

namespace ModularCurves

noncomputable section

universe u v

variable (R : Type u) {ι : Type v} [CommRing R]

/-- Cochains supported on tuples whose range contains `N`. -/
def CechSupportCochain (N : Set ι) (n : ℕ) :
    Submodule R ((Fin (n + 1) → ι) → R) where
  carrier := {s | ∀ a, ¬N ⊆ Set.range a → s a = 0}
  zero_mem' := by
    intro a ha
    rfl
  add_mem' := by
    intro s t hs ht a ha
    simp [hs a ha, ht a ha]
  smul_mem' := by
    intro r s hs a ha
    simp [hs a ha]

private def cechSupportDelete {n : ℕ} (a : Fin (n + 2) → ι)
    (k : Fin (n + 2)) : Fin (n + 1) → ι :=
  a ∘ (SimplexCategory.δ k).toOrderHom

private theorem cechSupportDelete_range_subset {n : ℕ}
    (a : Fin (n + 2) → ι) (k : Fin (n + 2)) :
    Set.range (cechSupportDelete a k) ⊆ Set.range a := by
  rintro x ⟨l, rfl⟩
  exact ⟨(SimplexCategory.δ k).toOrderHom l, rfl⟩

/-- The alternating deletion differential on support-restricted Cech cochains. -/
def cechSupportDifferential (N : Set ι) (n : ℕ) :
    CechSupportCochain R N n →ₗ[R] CechSupportCochain R N (n + 1) where
  toFun s :=
    ⟨fun a => ∑ k : Fin (n + 2),
        (-1 : R) ^ (k : ℕ) * s.1 (cechSupportDelete a k),
      fun a ha => by
        apply Finset.sum_eq_zero
        intro k hk
        have hdelete : ¬N ⊆ Set.range (cechSupportDelete a k) :=
          fun hN => ha (Subset.trans hN (cechSupportDelete_range_subset a k))
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

private def cechSupportPrepend {n : ℕ} (i₀ : ι) (a : Fin (n + 1) → ι) :
    Fin (n + 2) → ι :=
  Fin.cases i₀ a

private theorem cechSupportPrepend_delete_zero {n : ℕ} (i₀ : ι)
    (a : Fin (n + 1) → ι) :
    cechSupportDelete (cechSupportPrepend i₀ a) 0 = a := by
  funext k
  rfl

private theorem cechSupportPrepend_delete_succ {n : ℕ} (i₀ : ι)
    (a : Fin (n + 2) → ι) (k : Fin (n + 2)) :
    cechSupportDelete (cechSupportPrepend i₀ a) k.succ =
      cechSupportPrepend i₀ (cechSupportDelete a k) := by
  funext l
  refine Fin.cases ?_ (fun m => ?_) l
  · rfl
  · simp [cechSupportDelete, cechSupportPrepend, SimplexCategory.δ,
      Function.comp_apply]

private theorem cechSupportPrepend_not_subset {N : Set ι} {i₀ : ι}
    (hi₀ : i₀ ∉ N) {n : ℕ} (a : Fin (n + 1) → ι)
    (ha : ¬N ⊆ Set.range a) :
    ¬N ⊆ Set.range (cechSupportPrepend i₀ a) := by
  intro hN
  apply ha
  intro x hx
  rcases hN hx with ⟨k, hk⟩
  induction k using Fin.cases with
  | zero =>
    have hix : i₀ = x := by
      simpa [cechSupportPrepend] using hk
    subst x
    exact (hi₀ hx).elim
  | succ l =>
    exact ⟨l, by simpa [cechSupportPrepend] using hk⟩

/-- Prepending an index outside `N` contracts the support-restricted Cech cochains. -/
def cechSupportContraction (N : Set ι) (i₀ : ι) (hi₀ : i₀ ∉ N) (n : ℕ) :
    CechSupportCochain R N (n + 1) →ₗ[R] CechSupportCochain R N n where
  toFun s :=
    ⟨fun a => s.1 (cechSupportPrepend i₀ a),
      fun a ha => s.2 _ (cechSupportPrepend_not_subset hi₀ a ha)⟩
  map_add' s t := by
    apply Subtype.ext
    rfl
  map_smul' r s := by
    apply Subtype.ext
    rfl

/-- The prepend contraction satisfies `dh + hd = 1`. -/
theorem cechSupportContraction_homotopy (N : Set ι) (i₀ : ι)
    (hi₀ : i₀ ∉ N) (n : ℕ) (s : CechSupportCochain R N (n + 1)) :
    cechSupportDifferential R N n (cechSupportContraction R N i₀ hi₀ n s) +
        cechSupportContraction R N i₀ hi₀ (n + 1)
          (cechSupportDifferential R N (n + 1) s) = s := by
  apply Subtype.ext
  funext a
  change
    (∑ k : Fin (n + 2), (-1 : R) ^ (k : ℕ) *
        s.1 (cechSupportPrepend i₀ (cechSupportDelete a k))) +
      ∑ k : Fin (n + 3), (-1 : R) ^ (k : ℕ) *
        s.1 (cechSupportDelete (cechSupportPrepend i₀ a) k) = s.1 a
  conv_lhs =>
    rhs
    rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ,
    mul_neg, mul_one, neg_mul,
    cechSupportPrepend_delete_zero, cechSupportPrepend_delete_succ]
  rw [Finset.sum_neg_distrib]
  abel

/-- Every positive-degree cycle in the support-restricted Cech complex is a boundary. -/
theorem exists_preimage_cechSupportDifferential (N : Set ι) (i₀ : ι)
    (hi₀ : i₀ ∉ N) (n : ℕ) (s : CechSupportCochain R N (n + 1))
    (hs : cechSupportDifferential R N (n + 1) s = 0) :
    ∃ t : CechSupportCochain R N n,
      cechSupportDifferential R N n t = s := by
  refine ⟨cechSupportContraction R N i₀ hi₀ n s, ?_⟩
  have h := cechSupportContraction_homotopy R N i₀ hi₀ n s
  rw [hs, map_zero, add_zero] at h
  exact h

end

end ModularCurves
