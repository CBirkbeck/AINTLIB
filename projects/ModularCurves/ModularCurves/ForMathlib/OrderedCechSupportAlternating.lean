/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Data.Fin.Tuple.Sort
import ModularCurves.ForMathlib.OrderedCechSupportContraction

/-!
# Alternating extension of ordered support-restricted Cech cochains

This file compares the native support-restricted Cech cochains with their ordered version.
Alternating extension from strictly increasing tuples is a section of restriction to those tuples.
-/

open Set

namespace ModularCurves

noncomputable section

universe u v

variable (R : Type u) {ι : Type v} [CommRing R] [LinearOrder ι]

/-- Restrict native support cochains to strictly increasing tuples. -/
def orderedCechSupportRestrict (N : Set ι) (n : ℕ) :
    CechSupportCochain R N n →ₗ[R] OrderedCechSupportCochain R N n where
  toFun s :=
    ⟨fun a => s.1 a.1, fun a ha => s.2 a.1 ha⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def orderedCechSupportPermutationExtend (N : Set ι) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    OrderedCechSupportCochain R N n →ₗ[R] CechSupportCochain R N n where
  toFun s :=
    ⟨fun a => if h : StrictMono (a ∘ σ) then s.1 ⟨a ∘ σ, h⟩ else 0,
      fun a ha => by
        change (if h : StrictMono (a ∘ σ) then s.1 ⟨a ∘ σ, h⟩ else 0) = 0
        split_ifs with h
        · apply s.2
          intro hN
          apply ha
          intro x hx
          obtain ⟨k, hk⟩ := hN hx
          exact ⟨σ k, hk⟩
        · rfl⟩
  map_add' s t := by
    apply Subtype.ext
    funext a
    change (if h : StrictMono (a ∘ σ) then (s + t).1 ⟨a ∘ σ, h⟩ else 0) =
      (if h : StrictMono (a ∘ σ) then s.1 ⟨a ∘ σ, h⟩ else 0) +
        if h : StrictMono (a ∘ σ) then t.1 ⟨a ∘ σ, h⟩ else 0
    split_ifs
    · rfl
    · simp
  map_smul' r s := by
    apply Subtype.ext
    funext a
    change (if h : StrictMono (a ∘ σ) then (r • s).1 ⟨a ∘ σ, h⟩ else 0) =
      r * if h : StrictMono (a ∘ σ) then s.1 ⟨a ∘ σ, h⟩ else 0
    split_ifs
    · rfl
    · simp

/-- Alternatingly extend ordered support cochains to all tuples. -/
noncomputable def orderedCechSupportAlternatingExtend (N : Set ι) (n : ℕ) :
    OrderedCechSupportCochain R N n →ₗ[R] CechSupportCochain R N n :=
  ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
    orderedCechSupportPermutationExtend R N n σ

/-- Restricting an alternating extension back to ordered tuples recovers the original cochain. -/
theorem orderedCechSupportAlternatingExtend_restrict (N : Set ι) (n : ℕ)
    (s : OrderedCechSupportCochain R N n) :
    orderedCechSupportRestrict R N n
        (orderedCechSupportAlternatingExtend R N n s) = s := by
  apply Subtype.ext
  funext a
  change ((∑ σ : Equiv.Perm (Fin (n + 1)),
    (Equiv.Perm.sign σ : ℤ) •
      orderedCechSupportPermutationExtend R N n σ) s).1 a.1 = s.1 a
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_apply, SetLike.val_smul_of_tower]
  change (∑ σ : Equiv.Perm (Fin (n + 1)),
    (Equiv.Perm.sign σ : ℤ) •
      (if h : StrictMono (a.1 ∘ σ) then s.1 ⟨a.1 ∘ σ, h⟩ else 0)) = s.1 a
  rw [Finset.sum_eq_single 1]
  · simp only [Equiv.Perm.sign_one, Units.val_one, one_zsmul]
    rw [dif_pos (by simpa using a.2)]
    apply congrArg s.1
    apply Subtype.ext
    rfl
  · intro σ _ hσ
    have hnot : ¬StrictMono (a.1 ∘ σ) := by
      intro h
      have hmono : Monotone σ := fun i j hij =>
        a.2.le_iff_le.mp (h.monotone hij)
      exact hσ ((Equiv.Perm.monotone_iff σ).mp hmono)
    simp [hnot]
  · simp

/-- Restriction to ordered tuples commutes with the alternating deletion differentials. -/
theorem orderedCechSupportRestrict_differential (N : Set ι) (n : ℕ)
    (s : CechSupportCochain R N n) :
    orderedCechSupportRestrict R N (n + 1)
        (cechSupportDifferential R N n s) =
      orderedCechSupportDifferential R N n
        (orderedCechSupportRestrict R N n s) := by
  apply Subtype.ext
  funext a
  rfl

end

end ModularCurves
