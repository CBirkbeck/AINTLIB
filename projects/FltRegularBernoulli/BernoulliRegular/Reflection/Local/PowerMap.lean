module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import BernoulliRegular.Reflection.Local.RootsOfUnity

/-!
# The `p`-power map on local principal units

This file proves the REF-10c1 filtration estimate for the local principal-unit
filtration at `lambda`: for positive `n`, taking `p`-th powers sends `U_n` into
`U_{n+1}`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Reflection
namespace Local

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The rational prime `p` lies in the local maximal ideal above `p`. -/
theorem natCast_prime_mem_localCyclotomicMaximalIdeal :
    (p : localCyclotomicRing p K) ∈ localCyclotomicMaximalIdeal p K := by
  haveI : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) (p ^ (0 + 1)) := by
    simp
  have hp_global : (p : 𝓞 K) ∈ cyclotomicLambda p K := by
    simpa [cyclotomicLambda, zetaPrime] using
      (IsCyclotomicExtension.Rat.p_mem_span_zeta_sub_one p 0 hζ)
  rw [← localCyclotomicMaximalIdeal_eq_map p K]
  simpa using
    Ideal.mem_map_of_mem (algebraMap (𝓞 K) (localCyclotomicRing p K)) hp_global

/-- Globally, `p` lies in `lambda^(p-1)` in the prime cyclotomic field. -/
theorem natCast_prime_mem_cyclotomicLambda_pow_pred :
    (p : 𝓞 K) ∈ cyclotomicLambda p K ^ (p - 1) := by
  haveI : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) (p ^ (0 + 1)) := by
    simp
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hfin : Module.finrank ℚ K = p - 1 := by
    rw [IsCyclotomicExtension.finrank (K := ℚ) (L := K)
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos p)),
      Nat.totient_prime (Fact.out : Nat.Prime p)]
  have hp_span : (algebraMap ℤ (𝓞 K)) (p : ℤ) ∈
      Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span ({(p : ℤ)} : Set ℤ)) :=
    Ideal.mem_map_of_mem (algebraMap ℤ (𝓞 K))
      (Ideal.mem_span_singleton_self (p : ℤ))
  rw [IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow p 0 hζ] at hp_span
  simpa [cyclotomicLambda, zetaPrime, hfin] using hp_span

/-- Locally, `p` has `lambda`-adic order at least `p - 1`. -/
theorem natCast_prime_mem_localCyclotomicMaximalIdeal_pow_pred :
    (p : localCyclotomicRing p K) ∈ (localCyclotomicMaximalIdeal p K) ^ (p - 1) := by
  have hp_global := natCast_prime_mem_cyclotomicLambda_pow_pred (p := p) (K := K)
  rw [← localCyclotomicMaximalIdeal_eq_map p K]
  rw [← Ideal.map_pow]
  simpa using
    Ideal.mem_map_of_mem (algebraMap (𝓞 K) (localCyclotomicRing p K)) hp_global

/-- For positive filtration steps, the `p`-power map raises the filtration by one. -/
theorem pow_mem_principalUnitSubgroup_succ_of_pos {n : ℕ} (hn : 1 ≤ n)
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K n) :
    u ^ p ∈ principalUnitSubgroup p K (n + 1) := by
  rw [mem_principalUnitSubgroup_iff] at hu ⊢
  rw [Units.val_pow_eq_pow_val]
  let R := localCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  let x : R := (u : R) - 1
  have hx : x ∈ M ^ n := by
    simpa [x, M, R] using hu
  have hpM : (p : R) ∈ M := by
    simpa [R, M] using natCast_prime_mem_localCyclotomicMaximalIdeal (p := p) (K := K)
  have hu_eq : (u : R) = 1 + x := by
    dsimp [x]
    ring
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (R := R) (p := p)
    (Fact.out : Nat.Prime p) (1 : R) x
  have hpow_formula : (1 + x) ^ p - 1 = x ^ p + (p : R) * x * r := by
    rw [hr]
    ring
  rw [hu_eq, hpow_formula]
  apply Ideal.add_mem
  · have hxpow_raw : x ^ p ∈ (M ^ n) ^ p := Ideal.pow_mem_pow hx p
    have hxpow_np : x ^ p ∈ M ^ (n * p) := by
      simpa [pow_mul] using hxpow_raw
    have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    have hn_two : n + 1 ≤ n * 2 := by
      have h : n + 1 ≤ n + n := Nat.add_le_add_left hn n
      simpa [mul_two] using h
    exact Ideal.pow_le_pow_right (hn_two.trans (Nat.mul_le_mul_left n hp_two)) hxpow_np
  · have hpx : (p : R) * x ∈ M * M ^ n := Ideal.mul_mem_mul hpM hx
    have hpx_succ : (p : R) * x ∈ M ^ (n + 1) := by
      simpa [pow_succ'] using hpx
    simpa [mul_assoc] using Ideal.mul_mem_right r (M ^ (n + 1)) hpx_succ

/-- The subgroup of `p`-th powers of `U_n` lies in `U_{n+1}` for positive `n`. -/
theorem principalUnitPowerSubgroup_le_succ_of_pos {n : ℕ} (hn : 1 ≤ n) :
    principalUnitPowerSubgroup p K p n ≤ principalUnitSubgroup p K (n + 1) := by
  intro u hu
  rw [mem_principalUnitPowerSubgroup_iff] at hu
  rcases hu with ⟨v, hv, rfl⟩
  exact pow_mem_principalUnitSubgroup_succ_of_pos (p := p) (K := K) hn hv

/-- For `n >= 2`, the cyclotomic ramification estimate raises `U_n` by `p - 1`. -/
theorem pow_mem_principalUnitSubgroup_add_pred_of_two_le {n : ℕ} (hn : 2 ≤ n)
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K n) :
    u ^ p ∈ principalUnitSubgroup p K (n + (p - 1)) := by
  rw [mem_principalUnitSubgroup_iff] at hu ⊢
  rw [Units.val_pow_eq_pow_val]
  let R := localCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  let x : R := (u : R) - 1
  have hx : x ∈ M ^ n := by
    simpa [x, M, R] using hu
  have hpM : (p : R) ∈ M ^ (p - 1) := by
    simpa [R, M] using
      natCast_prime_mem_localCyclotomicMaximalIdeal_pow_pred (p := p) (K := K)
  have hu_eq : (u : R) = 1 + x := by
    dsimp [x]
    ring
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (R := R) (p := p)
    (Fact.out : Nat.Prime p) (1 : R) x
  have hpow_formula : (1 + x) ^ p - 1 = x ^ p + (p : R) * x * r := by
    rw [hr]
    ring
  rw [hu_eq, hpow_formula]
  apply Ideal.add_mem
  · have hxpow_raw : x ^ p ∈ (M ^ n) ^ p := Ideal.pow_mem_pow hx p
    have hxpow_np : x ^ p ∈ M ^ (n * p) := by
      simpa [pow_mul] using hxpow_raw
    have hp_one : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
    have hn_pos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
    have hnp : n + (p - 1) ≤ n * p := by
      have hmul : n * p = n + n * (p - 1) := by
        calc
          n * p = n * ((p - 1) + 1) := by rw [Nat.sub_add_cancel hp_one]
          _ = n * (p - 1) + n := by rw [Nat.mul_add, Nat.mul_one]
          _ = n + n * (p - 1) := by rw [Nat.add_comm]
      have hle : n + (p - 1) ≤ n + n * (p - 1) :=
        Nat.add_le_add_left (Nat.le_mul_of_pos_left (p - 1) hn_pos) n
      simpa [hmul] using hle
    exact Ideal.pow_le_pow_right hnp hxpow_np
  · have hxp : x * (p : R) ∈ M ^ n * M ^ (p - 1) := Ideal.mul_mem_mul hx hpM
    have hpx_step : (p : R) * x ∈ M ^ (n + (p - 1)) := by
      simpa [pow_add, mul_comm] using hxp
    simpa [mul_assoc] using Ideal.mul_mem_right r (M ^ (n + (p - 1))) hpx_step

/-- The subgroup of `p`-th powers of `U_n` lies in `U_{n+p-1}` for `n >= 2`. -/
theorem principalUnitPowerSubgroup_le_add_pred_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    principalUnitPowerSubgroup p K p n ≤ principalUnitSubgroup p K (n + (p - 1)) := by
  intro u hu
  rw [mem_principalUnitPowerSubgroup_iff] at hu
  rcases hu with ⟨v, hv, rfl⟩
  exact pow_mem_principalUnitSubgroup_add_pred_of_two_le (p := p) (K := K) hn hv

theorem pow_mem_principalUnitSubgroup_p_add_one_of_mem_two
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K 2) :
    u ^ p ∈ principalUnitSubgroup p K (p + 1) := by
  have hp_one : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
  have hidx : 2 + (p - 1) = p + 1 := by
    calc
      2 + (p - 1) = (p - 1) + 2 := Nat.add_comm _ _
      _ = (p - 1) + (1 + 1) := rfl
      _ = (p - 1 + 1) + 1 := by rw [← Nat.add_assoc]
      _ = p + 1 := by rw [Nat.sub_add_cancel hp_one]
  simpa [hidx] using
    pow_mem_principalUnitSubgroup_add_pred_of_two_le (p := p) (K := K)
      (n := 2) (by decide) hu

theorem principalUnitPowerSubgroup_two_le_p_add_one :
    principalUnitPowerSubgroup p K p 2 ≤ principalUnitSubgroup p K (p + 1) := by
  intro u hu
  rw [mem_principalUnitPowerSubgroup_iff] at hu
  rcases hu with ⟨v, hv, rfl⟩
  exact pow_mem_principalUnitSubgroup_p_add_one_of_mem_two (p := p) (K := K) hv

end CyclotomicSetup

end Local
end Reflection
end BernoulliRegular
