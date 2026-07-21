/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Data.Fin.Tuple.Sort
import ModularCurves.ForMathlib.OrderedCechSupportContraction
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechAlternating

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

private theorem orderedCechSupportAlternatingExtend_apply (N : Set ι) (n : ℕ)
    (s : OrderedCechSupportCochain R N n) (a : Fin (n + 1) → ι) :
    (orderedCechSupportAlternatingExtend R N n s).1 a =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        (Equiv.Perm.sign σ : ℤ) •
          if h : StrictMono (a ∘ σ) then s.1 ⟨a ∘ σ, h⟩ else 0 := by
  change ((∑ σ : Equiv.Perm (Fin (n + 1)),
    (Equiv.Perm.sign σ : ℤ) •
      orderedCechSupportPermutationExtend R N n σ) s).1 a = _
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_apply, SetLike.val_smul_of_tower]
  rfl

private theorem orderedCechSupportAlternatingExtend_permute (N : Set ι) (n : ℕ)
    (s : OrderedCechSupportCochain R N n) (a : Fin (n + 1) → ι)
    (τ : Equiv.Perm (Fin (n + 1))) :
    (orderedCechSupportAlternatingExtend R N n s).1 (a ∘ τ) =
      (Equiv.Perm.sign τ : ℤ) •
        (orderedCechSupportAlternatingExtend R N n s).1 a := by
  rw [orderedCechSupportAlternatingExtend_apply,
    orderedCechSupportAlternatingExtend_apply]
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  simp only [Equiv.coe_mulLeft, Equiv.Perm.sign_mul, smul_smul]
  rw [show (a ∘ τ) ∘ σ = a ∘ (τ * σ) by rfl]
  rw [Units.val_mul, ← mul_assoc, Int.units_coe_mul_self, one_mul]
  congr 1

private theorem orderedCechSupportAlternatingExtend_apply_of_not_injective
    (N : Set ι) (n : ℕ) (s : OrderedCechSupportCochain R N n)
    (a : Fin (n + 1) → ι) (ha : ¬Function.Injective a) :
    (orderedCechSupportAlternatingExtend R N n s).1 a = 0 := by
  rw [orderedCechSupportAlternatingExtend_apply]
  apply Finset.sum_eq_zero
  intro σ _
  have hmono : ¬StrictMono (a ∘ σ) := by
    intro h
    apply ha
    intro x y hxy
    apply σ.symm.injective
    apply h.injective
    simpa using hxy
  simp [hmono]

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

private theorem orderedCechSupportAlternatingExtend_apply_of_strictMono
    (N : Set ι) (n : ℕ) (s : OrderedCechSupportCochain R N n)
    (a : Fin (n + 1) → ι) (ha : StrictMono a) :
    (orderedCechSupportAlternatingExtend R N n s).1 a = s.1 ⟨a, ha⟩ := by
  have h := congrArg (fun t => t.1 ⟨a, ha⟩)
    (orderedCechSupportAlternatingExtend_restrict R N n s)
  exact h

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

private theorem cechSupportDifferential_alternatingExtend_permute
    (N : Set ι) (n : ℕ) (s : OrderedCechSupportCochain R N n)
    (a : Fin (n + 2) → ι) (τ : Equiv.Perm (Fin (n + 2))) :
    (cechSupportDifferential R N n
        (orderedCechSupportAlternatingExtend R N n s)).1 (a ∘ τ) =
      (Equiv.Perm.sign τ : ℤ) •
        (cechSupportDifferential R N n
          (orderedCechSupportAlternatingExtend R N n s)).1 a := by
  change (∑ r : Fin (n + 2), (-1 : R) ^ (r : ℕ) *
      (orderedCechSupportAlternatingExtend R N n s).1
        ((a ∘ τ) ∘ r.succAbove)) =
    (Equiv.Perm.sign τ : ℤ) •
      ∑ r : Fin (n + 2), (-1 : R) ^ (r : ℕ) *
        (orderedCechSupportAlternatingExtend R N n s).1
          (a ∘ r.succAbove)
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv τ _ _ fun r => ?_
  have hface :
      (a ∘ τ) ∘ r.succAbove =
        (a ∘ (τ r).succAbove) ∘
          AlgebraicGeometry.Scheme.Modules.cechPermDelete τ r := by
    funext x
    exact congrArg a
      (AlgebraicGeometry.Scheme.Modules.succAbove_cechPermDelete τ r x).symm
  rw [hface, orderedCechSupportAlternatingExtend_permute]
  simp only [zsmul_eq_mul]
  have hcoefficient :
      (-1 : R) ^ (r : ℕ) *
          (Equiv.Perm.sign
            (AlgebraicGeometry.Scheme.Modules.cechPermDelete τ r) : R) =
        (Equiv.Perm.sign τ : R) * (-1 : R) ^ (τ r : ℕ) := by
    have h := congrArg (Int.castRingHom R)
      (AlgebraicGeometry.Scheme.Modules.cechPermDelete_signed_coefficient τ r)
    simpa using h
  rw [← mul_assoc, ← mul_assoc, hcoefficient]

private theorem orderedCechSupportAlternatingExtend_face_pair_cancel
    (N : Set ι) (n : ℕ) (s : OrderedCechSupportCochain R N n)
    (a : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hal : a l = a k) (hkl : k ≠ l) :
    (-1 : R) ^ (k : ℕ) *
          (orderedCechSupportAlternatingExtend R N n s).1
            (a ∘ k.succAbove) +
        (-1 : R) ^ (l : ℕ) *
          (orderedCechSupportAlternatingExtend R N n s).1
            (a ∘ l.succAbove) = 0 := by
  let τ := AlgebraicGeometry.Scheme.Modules.cechDeleteSwapPerm k l
  have htuple :
      (a ∘ l.succAbove) ∘ τ = a ∘ k.succAbove :=
    AlgebraicGeometry.Scheme.Modules.comp_succAbove_cechDeleteSwapPerm_of_eq
      a k l hal.symm
  have hpair := orderedCechSupportAlternatingExtend_permute
    R N n s (a ∘ l.succAbove) τ
  rw [htuple] at hpair
  have hsign :
      (Equiv.Perm.sign τ : R) =
        -((-1 : R) ^ (k : ℕ) * (-1 : R) ^ (l : ℕ)) := by
    have h := congrArg (Int.castRingHom R)
      (AlgebraicGeometry.Scheme.Modules.cechDeleteSwapPerm_sign k l hkl)
    simpa [τ] using h
  have hk :
      (-1 : R) ^ (k : ℕ) * (-1 : R) ^ (k : ℕ) = 1 := by
    rw [← pow_add, (Even.add_self (k : ℕ)).neg_one_pow]
  rw [hpair, zsmul_eq_mul, hsign]
  rw [← mul_assoc, mul_neg, ← mul_assoc, hk, one_mul, neg_mul,
    neg_add_cancel]

private theorem cechSupportDifferential_alternatingExtend_apply_of_not_injective
    (N : Set ι) (n : ℕ) (s : OrderedCechSupportCochain R N n)
    (a : Fin (n + 2) → ι) (ha : ¬Function.Injective a) :
    (cechSupportDifferential R N n
        (orderedCechSupportAlternatingExtend R N n s)).1 a = 0 := by
  let F : Fin (n + 2) → R := fun k =>
    (-1 : R) ^ (k : ℕ) *
      (orderedCechSupportAlternatingExtend R N n s).1
        (a ∘ k.succAbove)
  change ∑ k, F k = 0
  by_cases hall : ∀ k : Fin (n + 2),
      ¬Function.Injective (a ∘ k.succAbove)
  · apply Finset.sum_eq_zero
    intro k _
    dsimp only [F]
    rw [orderedCechSupportAlternatingExtend_apply_of_not_injective
      R N n s (a ∘ k.succAbove) (hall k), mul_zero]
  · have hex : ∃ k : Fin (n + 2),
        Function.Injective (a ∘ k.succAbove) := by
      by_contra h
      apply hall
      intro k hk
      exact h ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hex
    obtain ⟨l, hlk, hal⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_partner_of_delete_injective
        a ha k hk
    have hkl : k ≠ l := hlk.symm
    have hother (m : Fin (n + 2)) (hmk : m ≠ k) (hml : m ≠ l) :
        F m = 0 := by
      have hm : ¬Function.Injective (a ∘ m.succAbove) :=
        AlgebraicGeometry.Scheme.Modules.delete_not_injective_of_ne
          a k l m hkl hmk.symm hml.symm hal
      dsimp only [F]
      rw [orderedCechSupportAlternatingExtend_apply_of_not_injective
        R N n s (a ∘ m.succAbove) hm, mul_zero]
    have hrem : ((Finset.univ.erase l).erase k).sum F = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hmk : m ≠ k := (Finset.mem_erase.mp hm).1
      have hml : m ≠ l :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1
      exact hother m hmk hml
    have hk_mem : k ∈ Finset.univ.erase l :=
      Finset.mem_erase.mpr ⟨hkl, Finset.mem_univ k⟩
    calc
      ∑ m, F m = (Finset.univ.erase l).sum F + F l :=
        (Finset.sum_erase_add Finset.univ F (Finset.mem_univ l)).symm
      _ = (((Finset.univ.erase l).erase k).sum F + F k) + F l := by
        rw [Finset.sum_erase_add (Finset.univ.erase l) F hk_mem]
      _ = F k + F l := by rw [hrem, zero_add]
      _ = 0 := by
        exact orderedCechSupportAlternatingExtend_face_pair_cancel
          R N n s a k l hal hkl

/-- Alternating extension commutes with the alternating deletion differentials. -/
theorem orderedCechSupportAlternatingExtend_differential
    (N : Set ι) (n : ℕ) (s : OrderedCechSupportCochain R N n) :
    cechSupportDifferential R N n
        (orderedCechSupportAlternatingExtend R N n s) =
      orderedCechSupportAlternatingExtend R N (n + 1)
        (orderedCechSupportDifferential R N n s) := by
  apply Subtype.ext
  funext a
  by_cases ha : Function.Injective a
  · let σ := Tuple.sort a
    let b := a ∘ σ
    let ε : ℤ := Equiv.Perm.sign σ
    have hb : StrictMono b :=
      (Tuple.monotone_sort a).strictMono_of_injective
        (ha.comp σ.injective)
    have hleft := cechSupportDifferential_alternatingExtend_permute
      R N n s a σ
    change
      (cechSupportDifferential R N n
          (orderedCechSupportAlternatingExtend R N n s)).1 b =
        ε •
          (cechSupportDifferential R N n
            (orderedCechSupportAlternatingExtend R N n s)).1 a at hleft
    have hright := orderedCechSupportAlternatingExtend_permute
      R N (n + 1) (orderedCechSupportDifferential R N n s) a σ
    change
      (orderedCechSupportAlternatingExtend R N (n + 1)
          (orderedCechSupportDifferential R N n s)).1 b =
        ε •
          (orderedCechSupportAlternatingExtend R N (n + 1)
            (orderedCechSupportDifferential R N n s)).1 a at hright
    have hd := orderedCechSupportRestrict_differential R N n
      (orderedCechSupportAlternatingExtend R N n s)
    rw [orderedCechSupportAlternatingExtend_restrict] at hd
    have hstrict :
        (cechSupportDifferential R N n
            (orderedCechSupportAlternatingExtend R N n s)).1 b =
          (orderedCechSupportAlternatingExtend R N (n + 1)
            (orderedCechSupportDifferential R N n s)).1 b := by
      rw [orderedCechSupportAlternatingExtend_apply_of_strictMono
        R N (n + 1) (orderedCechSupportDifferential R N n s) b hb]
      exact congrArg (fun t => t.1 ⟨b, hb⟩) hd
    have hε : ε * ε = 1 := by
      exact Int.units_coe_mul_self (Equiv.Perm.sign σ)
    calc
      (cechSupportDifferential R N n
          (orderedCechSupportAlternatingExtend R N n s)).1 a =
          ε • (ε •
            (cechSupportDifferential R N n
              (orderedCechSupportAlternatingExtend R N n s)).1 a) := by
            rw [smul_smul, hε, one_smul]
      _ = ε •
          (cechSupportDifferential R N n
            (orderedCechSupportAlternatingExtend R N n s)).1 b :=
        congrArg (ε • ·) hleft.symm
      _ = ε •
          (orderedCechSupportAlternatingExtend R N (n + 1)
            (orderedCechSupportDifferential R N n s)).1 b :=
        congrArg (ε • ·) hstrict
      _ = ε • (ε •
          (orderedCechSupportAlternatingExtend R N (n + 1)
            (orderedCechSupportDifferential R N n s)).1 a) :=
        congrArg (ε • ·) hright
      _ = (orderedCechSupportAlternatingExtend R N (n + 1)
          (orderedCechSupportDifferential R N n s)).1 a := by
        rw [smul_smul, hε, one_smul]
  · rw [cechSupportDifferential_alternatingExtend_apply_of_not_injective
      R N n s a ha]
    exact (orderedCechSupportAlternatingExtend_apply_of_not_injective
      R N (n + 1) (orderedCechSupportDifferential R N n s) a ha).symm

/-- Every positive-degree ordered support cocycle is a boundary. -/
theorem exists_preimage_orderedCechSupportDifferential
    (N : Set ι) (i₀ : ι) (hi₀ : i₀ ∉ N) (n : ℕ)
    (s : OrderedCechSupportCochain R N (n + 1))
    (hs : orderedCechSupportDifferential R N (n + 1) s = 0) :
    ∃ t : OrderedCechSupportCochain R N n,
      orderedCechSupportDifferential R N n t = s := by
  have hcycle :
      cechSupportDifferential R N (n + 1)
          (orderedCechSupportAlternatingExtend R N (n + 1) s) = 0 := by
    rw [orderedCechSupportAlternatingExtend_differential, hs, map_zero]
  obtain ⟨t, ht⟩ := exists_preimage_cechSupportDifferential
    R N i₀ hi₀ n (orderedCechSupportAlternatingExtend R N (n + 1) s) hcycle
  refine ⟨orderedCechSupportRestrict R N n t, ?_⟩
  rw [← orderedCechSupportRestrict_differential, ht,
    orderedCechSupportAlternatingExtend_restrict]

end

end ModularCurves
