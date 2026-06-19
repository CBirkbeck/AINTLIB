/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Index of Congruence Subgroups

Computes the index `[SL₂(ℤ) : Γ₀(pᵏ)] = pᵏ⁻¹(p + 1)` for prime `p` and `k ≥ 1`.

## Main results

* `Gamma0_prime_index` : `(Gamma0 p).index = p + 1` for prime `p`
* `Gamma0_relindex_step` : `(Gamma0 (p^(k+1))).relIndex (Gamma0 (p^k)) = p`
* `Gamma0_prime_power_index` : `(Gamma0 (p^k)).index = p^(k-1) * (p + 1)` for `k ≥ 1`

## References

* Shimura, Theorem 3.24
-/

open Matrix.SpecialLinearGroup Matrix ModularGroup CongruenceSubgroup

open scoped MatrixGroups

namespace HeckeRing.GL2

private lemma dvd_sub_val_mul (p : ℕ) (hp : Nat.Prime p) (a b : ℤ) (hb : (b : ZMod p) ≠ 0) :
    (p : ℤ) ∣ a - (((a : ZMod p) * (b : ZMod p)⁻¹).val : ℤ) * b := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hb, mul_one, sub_self]

private lemma SL2_entry_mul (A B : SL(2, ℤ)) (i j : Fin 2) :
    (A * B).1 i j = A.1 i 0 * B.1 0 j + A.1 i 1 * B.1 1 j := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private lemma TjS_inv_10 (j : ℤ) : ((T ^ j * S)⁻¹).1 1 0 = -1 := by
  simp [coe_T_zpow, coe_S, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two_of]

private lemma TjS_inv_11 (j : ℤ) : ((T ^ j * S)⁻¹).1 1 1 = j := by
  simp [coe_T_zpow, coe_S, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two_of]

private lemma TjS_00 (j : ℤ) : (T ^ j * S).1 0 0 = j := by
  simp [coe_T_zpow, coe_S]

private lemma TjS_10 (j : ℤ) : (T ^ j * S).1 1 0 = 1 := by
  simp [coe_S]

private lemma TjS_inv_mul_10 (j : ℤ) (σ : SL(2, ℤ)) :
    ((T ^ j * S)⁻¹ * σ).1 1 0 = j * σ.1 1 0 - σ.1 0 0 := by
  rw [SL2_entry_mul, TjS_inv_10, TjS_inv_11]
  ring

private lemma rep_diff_10 (i j : ℤ) :
    ((T ^ j * S)⁻¹ * (T ^ i * S)).1 1 0 = j - i := by
  rw [TjS_inv_mul_10, TjS_10, TjS_00]
  ring

section BaseCase

variable (p : ℕ) (hp : Nat.Prime p)
include hp

private def Gamma0Rep (j : Fin (p + 1)) : SL(2, ℤ) :=
  if j.val < p then T ^ (j.val : ℤ) * S else 1

private lemma Gamma0_prime_index_inj :
    Function.Injective (fun j : Fin (p + 1) ↦ QuotientGroup.mk (Gamma0Rep p j) :
      Fin (p + 1) → SL(2, ℤ) ⧸ (Gamma0 p)) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  intro ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ hf
  rw [QuotientGroup.eq, Gamma0_mem] at hf
  simp only [Gamma0Rep] at hf
  split_ifs at hf with h1 h2
  · rw [rep_diff_10, ZMod.intCast_zmod_eq_zero_iff_dvd] at hf
    have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hf (by lia)
    exact Fin.mk_eq_mk.mpr (by lia)
  · rw [mul_one, TjS_inv_10] at hf
    exact absurd hf (by norm_num)
  · rw [inv_one, one_mul, TjS_10] at hf
    exact absurd hf (by norm_num)
  · exact Fin.mk_eq_mk.mpr (by lia)

private lemma Gamma0_prime_index_surj :
    Function.Surjective (fun j : Fin (p + 1) ↦ QuotientGroup.mk (Gamma0Rep p j) :
      Fin (p + 1) → SL(2, ℤ) ⧸ (Gamma0 p)) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  intro x
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  by_cases h : ((σ.1 1 0 : ℤ) : ZMod p) = 0
  · refine ⟨⟨p, p.lt_succ_self⟩, ?_⟩
    rw [QuotientGroup.eq, Gamma0_mem]
    simpa [Gamma0Rep] using h
  · obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ZMod p, (p : ℤ) ∣ σ.1 0 0 - (j₀.val : ℤ) * σ.1 1 0 :=
      ⟨_, dvd_sub_val_mul p hp _ _ h⟩
    refine ⟨⟨j₀.val, Nat.lt_succ_of_lt (ZMod.val_lt j₀)⟩, ?_⟩
    rw [QuotientGroup.eq, Gamma0_mem]
    simp only [Gamma0Rep, ZMod.val_lt j₀, ite_true]
    rwa [TjS_inv_mul_10, ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_sub_comm]

/-- `[SL₂(ℤ) : Γ₀(p)] = p + 1` for prime `p`. -/
theorem Gamma0_prime_index : (Gamma0 p).index = p + 1 :=
  Nat.card_eq_of_equiv_fin (Equiv.ofBijective _
    ⟨Gamma0_prime_index_inj p hp, Gamma0_prime_index_surj p hp⟩).symm

end BaseCase

section InductiveStep

variable (p : ℕ)

private def lowerTriRep (k : ℕ) (c : Fin p) : SL(2, ℤ) :=
  ⟨!![1, 0; (c : ℤ) * (p : ℤ) ^ k, 1], by simp [det_fin_two_of]⟩

private lemma lowerTriRep_mem_Gamma0 (k : ℕ) (c : Fin p) :
    lowerTriRep p k c ∈ Gamma0 (p ^ k) := by
  rw [Gamma0_mem]
  simp [lowerTriRep, ← Nat.cast_pow, -Int.natCast_pow]

private lemma lowerTriRep_diff_entry (k : ℕ) (c₁ c₂ : Fin p) :
    ((lowerTriRep p k c₁)⁻¹ * lowerTriRep p k c₂).1 1 0 =
    ((c₂ : ℤ) - (c₁ : ℤ)) * (p : ℤ) ^ k := by
  simp [lowerTriRep, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two_of, sub_mul,
    neg_add_eq_sub]

private lemma lowerTriRep_inv_mul_10 (k : ℕ) (c : Fin p) (σ : SL(2, ℤ)) :
    ((lowerTriRep p k c)⁻¹ * σ).1 1 0 = σ.1 1 0 - (c : ℤ) * (p : ℤ) ^ k * σ.1 0 0 := by
  simp [SL2_entry_mul, lowerTriRep, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two_of,
    neg_add_eq_sub]

private def relindexRep (k : ℕ) (c : Fin p) : ↥(Gamma0 (p ^ k)) :=
  ⟨lowerTriRep p k c, lowerTriRep_mem_Gamma0 p k c⟩

private lemma relindexRep_coe (k : ℕ) (c : Fin p) :
    (relindexRep p k c : SL(2, ℤ)) = lowerTriRep p k c := rfl

variable (hp : Nat.Prime p)
include hp

private lemma Gamma0_relindex_step_inj (k : ℕ) :
    Function.Injective (fun c : Fin p ↦
      (QuotientGroup.mk (relindexRep p k c) :
        ↥(Gamma0 (p ^ k)) ⧸ (Gamma0 (p ^ (k + 1))).subgroupOf (Gamma0 (p ^ k)))) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  intro ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ hf
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Gamma0_mem] at hf
  simp only [InvMemClass.coe_inv, MulMemClass.coe_mul, relindexRep_coe] at hf
  rw [lowerTriRep_diff_entry p, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow, pow_succ,
    mul_comm ((↑c₂ : ℤ) - ↑c₁) ((p : ℤ) ^ k),
    mul_dvd_mul_iff_left (pow_ne_zero k (Int.natCast_ne_zero.mpr hp.ne_zero))] at hf
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hf (by lia)
  exact Fin.mk_eq_mk.mpr (by lia)

private lemma Gamma0_relindex_step_surj (k : ℕ) (hk : 0 < k) :
    Function.Surjective (fun c : Fin p ↦
      (QuotientGroup.mk (relindexRep p k c) :
        ↥(Gamma0 (p ^ k)) ⧸ (Gamma0 (p ^ (k + 1))).subgroupOf (Gamma0 (p ^ k)))) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  intro x
  obtain ⟨⟨σ, hσ_K⟩, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨q, hq⟩ : (↑(p ^ k) : ℤ) ∣ σ.1 1 0 := by
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← Gamma0_mem]
  push_cast at hq
  have h00_ne : ((σ.1 0 0 : ℤ) : ZMod p) ≠ 0 := by
    intro h_zero
    have h00_dvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h_zero
    have h10_dvd : (p : ℤ) ∣ σ.1 1 0 :=
      hq ▸ dvd_mul_of_dvd_left (dvd_pow_self _ hk.ne') q
    have hdet : σ.1 0 0 * σ.1 1 1 - σ.1 0 1 * σ.1 1 0 = 1 :=
      Matrix.det_fin_two σ.1 ▸ σ.2
    have h1_dvd : (p : ℤ) ∣ 1 :=
      hdet ▸ dvd_sub (dvd_mul_of_dvd_left h00_dvd _) (dvd_mul_of_dvd_right h10_dvd _)
    exact absurd (Int.le_of_dvd one_pos h1_dvd) (not_le.mpr (mod_cast hp.one_lt))
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ZMod p, (p : ℤ) ∣ q - (c₀.val : ℤ) * σ.1 0 0 :=
    ⟨_, dvd_sub_val_mul p hp q _ h00_ne⟩
  refine ⟨⟨c₀.val, ZMod.val_lt c₀⟩, ?_⟩
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [InvMemClass.coe_inv, MulMemClass.coe_mul, relindexRep_coe]
  rw [Gamma0_mem, lowerTriRep_inv_mul_10, hq, ZMod.intCast_zmod_eq_zero_iff_dvd, pow_succ]
  push_cast
  calc (p : ℤ) ^ k * (p : ℤ)
      ∣ (p : ℤ) ^ k * (q - ↑c₀.val * σ.1 0 0) := mul_dvd_mul_left _ hc₀
    _ = (p : ℤ) ^ k * q - ↑c₀.val * (p : ℤ) ^ k * σ.1 0 0 := by ring

/-- `[Γ₀(pᵏ) : Γ₀(p^{k+1})] = p` for `k ≥ 1`. -/
theorem Gamma0_relindex_step (k : ℕ) (hk : 0 < k) :
    (Gamma0 (p ^ (k + 1))).relIndex (Gamma0 (p ^ k)) = p :=
  Nat.card_eq_of_equiv_fin (Equiv.ofBijective _
    ⟨Gamma0_relindex_step_inj p hp k, Gamma0_relindex_step_surj p hp k hk⟩).symm

end InductiveStep

/-- `[SL₂(ℤ) : Γ₀(pᵏ)] = p^(k-1) * (p + 1)` for prime `p` and `k ≥ 1`. -/
theorem Gamma0_prime_power_index (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k) :
    (Gamma0 (p ^ k)).index = p ^ (k - 1) * (p + 1) := by
  induction k, hk using Nat.le_induction with
  | base => simpa using Gamma0_prime_index p hp
  | succ m hm ih =>
    have h_le : Gamma0 (p ^ (m + 1)) ≤ Gamma0 (p ^ m) := fun σ hσ ↦ by
      rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hσ ⊢
      exact (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p m.le_succ)).trans hσ
    rw [Nat.add_sub_cancel, ← Subgroup.relIndex_mul_index h_le,
      Gamma0_relindex_step p hp m hm, ih, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hm]

end HeckeRing.GL2
