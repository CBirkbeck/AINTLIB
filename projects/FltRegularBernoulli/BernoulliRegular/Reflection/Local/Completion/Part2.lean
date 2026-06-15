module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian
public import BernoulliRegular.Reflection.Local.Graded
public import BernoulliRegular.Reflection.Local.Completion.Part1

/-!
# Completed local principal units

This file starts the REF-10d3b completed endpoint layer.  The localized ring
`Localization.AtPrime` is not complete, so the reverse `p`-power endpoint is
recorded in the adic completion at the cyclotomic maximal ideal.
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

/-- The completed cyclotomic root, viewed as an element of completed `U_1`. -/
noncomputable def completedLocalCyclotomicZetaPrincipalUnit :
    completedPrincipalUnitSubgroup p K 1 :=
  ⟨completedLocalCyclotomicZetaUnit p K,
    completedLocalCyclotomicZetaUnit_mem_completedPrincipalUnitSubgroup_one (p := p) (K := K)⟩

@[simp]
theorem completedLocalCyclotomicZetaPrincipalUnit_pow_eq_one :
    completedLocalCyclotomicZetaPrincipalUnit p K ^ p = 1 :=
  Subtype.ext (completedLocalCyclotomicZetaUnit_pow_eq_one p K)

theorem completedPrincipalUnitFirstGradedHom_zeta_ne_one :
    completedPrincipalUnitFirstGradedHom p K
      (completedLocalCyclotomicZetaPrincipalUnit p K) ≠ 1 := by
  intro h
  have hker : completedLocalCyclotomicZetaPrincipalUnit p K ∈
      (completedPrincipalUnitFirstGradedHom p K).ker := by
    rw [MonoidHom.mem_ker]
    exact h
  have hzeta_mem_two :
      completedLocalCyclotomicZetaUnit p K ∈ completedPrincipalUnitSubgroup p K 2 :=
    (mem_completedPrincipalUnitFirstGradedHom_ker (p := p) (K := K)).mp hker
  exact completedLocalCyclotomicZetaUnit_not_mem_completedPrincipalUnitSubgroup_two
    (p := p) (K := K) hzeta_mem_two

theorem completedPrincipalUnitFirstGradedHom_zeta_orderOf :
    orderOf (completedPrincipalUnitFirstGradedHom p K
      (completedLocalCyclotomicZetaPrincipalUnit p K)) = p :=
  orderOf_eq_prime
    (by
      rw [← map_pow]
      simp)
    (completedPrincipalUnitFirstGradedHom_zeta_ne_one (p := p) (K := K))

theorem completedPrincipalUnitFirstGradedHom_zeta_zpowers_eq_top :
    Subgroup.zpowers
      (completedPrincipalUnitFirstGradedHom p K
        (completedLocalCyclotomicZetaPrincipalUnit p K)) = ⊤ :=
  zpowers_eq_top_of_prime_card
    (completedCotangentMultiplicativeCard (p := p) (K := K))
    (completedPrincipalUnitFirstGradedHom_zeta_ne_one (p := p) (K := K))

/-- The completed endpoint subgroup `mu_p * completed U_2`. -/
noncomputable def completedLocalCyclotomicEndpointSubgroup :
    Subgroup (completedLocalCyclotomicUnitGroup p K) :=
  completedLocalCyclotomicMuP p K ⊔ completedPrincipalUnitSubgroup p K 2

theorem completedLocalCyclotomicMuP_le_endpointSubgroup :
    completedLocalCyclotomicMuP p K ≤ completedLocalCyclotomicEndpointSubgroup p K := by
  rw [completedLocalCyclotomicEndpointSubgroup]
  exact le_sup_left

theorem completedPrincipalUnitSubgroup_two_le_endpointSubgroup :
    completedPrincipalUnitSubgroup p K 2 ≤ completedLocalCyclotomicEndpointSubgroup p K := by
  rw [completedLocalCyclotomicEndpointSubgroup]
  exact le_sup_right

/-- The formal inclusion `mu_p * completed U_2 <= completed U_1`. -/
theorem completedLocalCyclotomicEndpointSubgroup_le_principalUnitSubgroup_one :
    completedLocalCyclotomicEndpointSubgroup p K ≤ completedPrincipalUnitSubgroup p K 1 := by
  rw [completedLocalCyclotomicEndpointSubgroup]
  exact sup_le
    (completedLocalCyclotomicMuP_le_completedPrincipalUnitSubgroup_one (p := p) (K := K))
    (completedPrincipalUnitSubgroup_mono (p := p) (K := K) (by decide : 1 ≤ 2))

theorem completedPrincipalUnitSubgroup_one_le_endpointSubgroup_of_zeta_zpowers_eq_top
    (htop : Subgroup.zpowers
      (completedPrincipalUnitFirstGradedHom p K
        (completedLocalCyclotomicZetaPrincipalUnit p K)) = ⊤) :
    completedPrincipalUnitSubgroup p K 1 ≤ completedLocalCyclotomicEndpointSubgroup p K := by
  intro u hu
  let U1 := completedPrincipalUnitSubgroup p K 1
  let z : U1 := completedLocalCyclotomicZetaPrincipalUnit p K
  let f := completedPrincipalUnitFirstGradedHom p K
  have htop' : Subgroup.zpowers (f z) = ⊤ := by
    simpa [f, z] using htop
  have hmem : f ⟨u, hu⟩ ∈ Subgroup.zpowers (f z) := by
    rw [htop']
    exact Subgroup.mem_top _
  rcases Subgroup.mem_zpowers_iff.mp hmem with ⟨k, hk⟩
  have hker : (z ^ k)⁻¹ * (⟨u, hu⟩ : U1) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    rw [map_mul, map_inv, map_zpow, hk, inv_mul_cancel]
  have hU2 : ((((z ^ k)⁻¹ * (⟨u, hu⟩ : U1)) : U1) :
      completedLocalCyclotomicUnitGroup p K) ∈ completedPrincipalUnitSubgroup p K 2 :=
    (mem_completedPrincipalUnitFirstGradedHom_ker (p := p) (K := K)).mp hker
  rw [completedLocalCyclotomicEndpointSubgroup, Subgroup.mem_sup]
  refine ⟨((z ^ k : U1) : completedLocalCyclotomicUnitGroup p K), ?_,
    ((((z ^ k)⁻¹ * (⟨u, hu⟩ : U1)) : U1) :
      completedLocalCyclotomicUnitGroup p K), hU2, ?_⟩
  · rw [completedLocalCyclotomicMuP]
    change ((completedLocalCyclotomicZetaUnit p K) ^ k) ∈
      Subgroup.zpowers (completedLocalCyclotomicZetaUnit p K)
    exact Subgroup.zpow_mem_zpowers _ _
  · change ((z ^ k : U1) : completedLocalCyclotomicUnitGroup p K) *
        ((((z ^ k)⁻¹ * (⟨u, hu⟩ : U1)) : U1) :
          completedLocalCyclotomicUnitGroup p K) = u
    simp

theorem completedPrincipalUnitSubgroup_one_eq_endpointSubgroup_of_zeta_zpowers_eq_top
    (htop : Subgroup.zpowers
      (completedPrincipalUnitFirstGradedHom p K
        (completedLocalCyclotomicZetaPrincipalUnit p K)) = ⊤) :
    completedPrincipalUnitSubgroup p K 1 = completedLocalCyclotomicEndpointSubgroup p K :=
  le_antisymm
    (completedPrincipalUnitSubgroup_one_le_endpointSubgroup_of_zeta_zpowers_eq_top
      (p := p) (K := K) htop)
    (completedLocalCyclotomicEndpointSubgroup_le_principalUnitSubgroup_one (p := p) (K := K))

theorem completedPrincipalUnitSubgroup_one_eq_endpointSubgroup :
    completedPrincipalUnitSubgroup p K 1 = completedLocalCyclotomicEndpointSubgroup p K :=
  completedPrincipalUnitSubgroup_one_eq_endpointSubgroup_of_zeta_zpowers_eq_top
    (p := p) (K := K)
    (completedPrincipalUnitFirstGradedHom_zeta_zpowers_eq_top (p := p) (K := K))

/-- For positive completed filtration steps, the `p`-power map raises the filtration by one. -/
theorem pow_mem_completedPrincipalUnitSubgroup_succ_of_pos {n : ℕ} (hn : 1 ≤ n)
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitSubgroup p K n) :
    u ^ p ∈ completedPrincipalUnitSubgroup p K (n + 1) := by
  rw [mem_completedPrincipalUnitSubgroup_iff] at hu ⊢
  rw [Units.val_pow_eq_pow_val]
  let R := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let x : R := (u : R) - 1
  have hx : x ∈ M ^ n := by
    simpa [x, M, R] using hu
  have hpM : (p : R) ∈ M := by
    simpa [R, M] using
      natCast_prime_mem_completedLocalCyclotomicMaximalIdeal (p := p) (K := K)
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

/-- Completed `p`-th powers of `U_n` lie in `U_{n+1}` for positive `n`. -/
theorem completedPrincipalUnitPowerSubgroup_le_succ_of_pos {n : ℕ} (hn : 1 ≤ n) :
    completedPrincipalUnitPowerSubgroup p K p n ≤
      completedPrincipalUnitSubgroup p K (n + 1) := by
  intro u hu
  rw [mem_completedPrincipalUnitPowerSubgroup_iff] at hu
  rcases hu with ⟨v, hv, rfl⟩
  exact pow_mem_completedPrincipalUnitSubgroup_succ_of_pos (p := p) (K := K) hn hv

/-- For `n >= 2`, exact ramification raises completed `U_n` by `p - 1`. -/
theorem pow_mem_completedPrincipalUnitSubgroup_add_pred_of_two_le {n : ℕ} (hn : 2 ≤ n)
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitSubgroup p K n) :
    u ^ p ∈ completedPrincipalUnitSubgroup p K (n + (p - 1)) := by
  rw [mem_completedPrincipalUnitSubgroup_iff] at hu ⊢
  rw [Units.val_pow_eq_pow_val]
  let R := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let x : R := (u : R) - 1
  have hx : x ∈ M ^ n := by
    simpa [x, M, R] using hu
  have hpM : (p : R) ∈ M ^ (p - 1) := by
    simpa [R, M] using
      natCast_prime_mem_completedLocalCyclotomicMaximalIdeal_pow_pred (p := p) (K := K)
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

/-- Completed `p`-th powers of `U_n` lie in `U_{n+p-1}` for `n >= 2`. -/
theorem completedPrincipalUnitPowerSubgroup_le_add_pred_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    completedPrincipalUnitPowerSubgroup p K p n ≤
      completedPrincipalUnitSubgroup p K (n + (p - 1)) := by
  intro u hu
  rw [mem_completedPrincipalUnitPowerSubgroup_iff] at hu
  rcases hu with ⟨v, hv, rfl⟩
  exact pow_mem_completedPrincipalUnitSubgroup_add_pred_of_two_le (p := p) (K := K) hn hv

theorem pow_mem_completedPrincipalUnitSubgroup_p_add_one_of_mem_two
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitSubgroup p K 2) :
    u ^ p ∈ completedPrincipalUnitSubgroup p K (p + 1) := by
  have hp_one : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
  have hidx : 2 + (p - 1) = p + 1 := by
    calc
      2 + (p - 1) = (p - 1) + 2 := Nat.add_comm _ _
      _ = (p - 1) + (1 + 1) := rfl
      _ = (p - 1 + 1) + 1 := by rw [← Nat.add_assoc]
      _ = p + 1 := by rw [Nat.sub_add_cancel hp_one]
  simpa [hidx] using
    pow_mem_completedPrincipalUnitSubgroup_add_pred_of_two_le (p := p) (K := K)
      (n := 2) (by decide) hu

theorem completedPrincipalUnitPowerSubgroup_two_le_p_add_one :
    completedPrincipalUnitPowerSubgroup p K p 2 ≤
      completedPrincipalUnitSubgroup p K (p + 1) := by
  intro u hu
  rw [mem_completedPrincipalUnitPowerSubgroup_iff] at hu
  rcases hu with ⟨v, hv, rfl⟩
  exact pow_mem_completedPrincipalUnitSubgroup_p_add_one_of_mem_two (p := p) (K := K) hv

/-- The subgroup of `p`-th powers of `mu_p * completed U_2`. -/
noncomputable def completedLocalCyclotomicEndpointPowerSubgroup :
    Subgroup (completedLocalCyclotomicUnitGroup p K) :=
  (completedLocalCyclotomicEndpointSubgroup p K).map (powMonoidHom p)

theorem completedLocalCyclotomicMuPPowerSubgroup_le_completedPrincipalUnitSubgroup_p_add_one :
    (completedLocalCyclotomicMuP p K).map (powMonoidHom p) ≤
      completedPrincipalUnitSubgroup p K (p + 1) := by
  intro u hu
  rw [Subgroup.mem_map] at hu
  rcases hu with ⟨v, hv, rfl⟩
  change v ^ p ∈ completedPrincipalUnitSubgroup p K (p + 1)
  rw [completedLocalCyclotomicMuP_pow_eq_one (p := p) (K := K) hv]
  exact one_mem_completedPrincipalUnitSubgroup (p := p) (K := K) (p + 1)

/-- The formal completed endpoint inclusion `(mu_p * completed U_2)^p <= completed U_{p+1}`. -/
theorem completedLocalCyclotomicEndpointPowerSubgroup_le_principalUnitSubgroup_p_add_one :
    completedLocalCyclotomicEndpointPowerSubgroup p K ≤
      completedPrincipalUnitSubgroup p K (p + 1) := by
  rw [completedLocalCyclotomicEndpointPowerSubgroup, completedLocalCyclotomicEndpointSubgroup,
    Subgroup.map_sup]
  exact sup_le
    (completedLocalCyclotomicMuPPowerSubgroup_le_completedPrincipalUnitSubgroup_p_add_one
      (p := p) (K := K))
    (by
      simpa [completedPrincipalUnitPowerSubgroup] using
        completedPrincipalUnitPowerSubgroup_two_le_p_add_one (p := p) (K := K))

theorem pow_mem_completedPrincipalUnitSubgroup_p_add_one_of_mem_completedEndpoint
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedLocalCyclotomicEndpointSubgroup p K) :
    u ^ p ∈ completedPrincipalUnitSubgroup p K (p + 1) :=
  completedLocalCyclotomicEndpointPowerSubgroup_le_principalUnitSubgroup_p_add_one
    (p := p) (K := K) ⟨u, hu, rfl⟩

theorem completedPrincipalUnitPowerSubgroup_one_le_p_add_one_of_endpoint_eq
    (h : completedPrincipalUnitSubgroup p K 1 =
      completedLocalCyclotomicEndpointSubgroup p K) :
    completedPrincipalUnitPowerSubgroup p K p 1 ≤
      completedPrincipalUnitSubgroup p K (p + 1) := by
  rw [completedPrincipalUnitPowerSubgroup, h]
  exact completedLocalCyclotomicEndpointPowerSubgroup_le_principalUnitSubgroup_p_add_one
    (p := p) (K := K)

theorem completedPrincipalUnitPowerSubgroup_one_le_p_add_one_of_zeta_zpowers_eq_top
    (htop : Subgroup.zpowers
      (completedPrincipalUnitFirstGradedHom p K
        (completedLocalCyclotomicZetaPrincipalUnit p K)) = ⊤) :
    completedPrincipalUnitPowerSubgroup p K p 1 ≤
      completedPrincipalUnitSubgroup p K (p + 1) :=
  completedPrincipalUnitPowerSubgroup_one_le_p_add_one_of_endpoint_eq
    (p := p) (K := K)
    (completedPrincipalUnitSubgroup_one_eq_endpointSubgroup_of_zeta_zpowers_eq_top
      (p := p) (K := K) htop)

theorem completedPrincipalUnitPowerSubgroup_one_le_p_add_one :
    completedPrincipalUnitPowerSubgroup p K p 1 ≤
      completedPrincipalUnitSubgroup p K (p + 1) :=
  completedPrincipalUnitPowerSubgroup_one_le_p_add_one_of_zeta_zpowers_eq_top
    (p := p) (K := K)
    (completedPrincipalUnitFirstGradedHom_zeta_zpowers_eq_top (p := p) (K := K))

theorem exists_completedPrincipalUnit_pow_prime_sub_one_add_mem_next
    {n : ℕ} (hn : 2 ≤ n) {x : completedLocalCyclotomicRing p K}
    (hx : x ∈ completedLocalCyclotomicMaximalIdeal p K ^ (n + (p - 1))) :
    ∃ w : completedLocalCyclotomicUnitGroup p K,
      w ∈ completedPrincipalUnitSubgroup p K n ∧
        ((w ^ p : completedLocalCyclotomicUnitGroup p K) :
            completedLocalCyclotomicRing p K) - (1 + x) ∈
          completedLocalCyclotomicMaximalIdeal p K ^ (n + (p - 1) + 1) := by
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let π : S := completedLocalCyclotomicUniformizer p K
  obtain ⟨y, hyM, hpy⟩ :=
    exists_natCast_prime_mul_eq_of_mem_completedLocalCyclotomicMaximalIdeal_pow_add_pred
      (p := p) (K := K) (n := n) hx
  obtain ⟨z, hz⟩ :=
    exists_uniformizer_pow_mul_eq_of_mem_completedLocalCyclotomicMaximalIdeal_pow
      (p := p) (K := K) (n := n) hyM
  have hn_ne : n ≠ 0 := by omega
  let w : completedLocalCyclotomicUnitGroup p K :=
    completedOneAddUnitOfMemMaximalIdealPow (p := p) (K := K) (n := n) hn_ne hyM
  have hw_coe : (w : S) = 1 + y := by
    simp [w]
  have hvu : π ∣ π ^ n := by
    refine ⟨π ^ (n - 1), ?_⟩
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hquv : (p : S) * π ^ n * π ∣ (π ^ n) ^ p :=
    natCast_prime_mul_uniformizer_pow_mul_uniformizer_dvd_uniformizer_pow_prime
      (p := p) (K := K) hn
  obtain ⟨b, hb⟩ := exists_one_add_mul_pow_prime_eq_of_dvd
    (R := S) (q := p) (u := π ^ n) (v := π)
    (Fact.out : Nat.Prime p) hvu hquv z
  have hpM : (p : S) ∈ M ^ (p - 1) := by
    simpa [S, M] using
      natCast_prime_mem_completedLocalCyclotomicMaximalIdeal_pow_pred (p := p) (K := K)
  have hπn : π ^ n ∈ M ^ n := by
    rw [completedLocalCyclotomicMaximalIdeal_pow_eq_span_uniformizer_pow (p := p) (K := K)]
    exact Ideal.mem_span_singleton_self (π ^ n)
  have hπ : π ∈ M := by
    change completedLocalCyclotomicUniformizer p K ∈ completedLocalCyclotomicMaximalIdeal p K
    rw [completedLocalCyclotomicMaximalIdeal_eq_span_uniformizer (p := p) (K := K)]
    exact Ideal.mem_span_singleton_self π
  have hprod : (p : S) * π ^ n * π ∈ M ^ (n + (p - 1) + 1) := by
    have hmul₁ : π ^ n * π ∈ M ^ n * M :=
      Ideal.mul_mem_mul hπn hπ
    have hmul₂ : (p : S) * (π ^ n * π) ∈ M ^ (p - 1) * (M ^ n * M) :=
      Ideal.mul_mem_mul hpM hmul₁
    have hIcomm : M ^ (p - 1) * (M ^ n * M) = (M ^ n * M) * M ^ (p - 1) := by
      rw [mul_comm]
    have hmul₃ : (p : S) * (π ^ n * π) ∈ (M ^ n * M) * M ^ (p - 1) := by
      rwa [hIcomm] at hmul₂
    have hIassoc : (M ^ n * M) * M ^ (p - 1) = M ^ n * (M * M ^ (p - 1)) := by
      rw [mul_assoc]
    have hmul₄ : (p : S) * (π ^ n * π) ∈ M ^ n * (M * M ^ (p - 1)) := by
      rwa [hIassoc] at hmul₃
    simpa [pow_add, mul_assoc, add_assoc, add_comm, add_left_comm] using hmul₄
  have hpxz : (p : S) * π ^ n * z = x := by
    rw [← hz] at hpy
    simpa [mul_assoc, S, π] using hpy
  refine ⟨w, ?_, ?_⟩
  · rw [mem_completedPrincipalUnitSubgroup_iff]
    simpa [hw_coe] using hyM
  · have hpow :
        ((w ^ p : completedLocalCyclotomicUnitGroup p K) : S) =
          1 + x + ((p : S) * π ^ n * π * b) := by
      rw [Units.val_pow_eq_pow_val, hw_coe, ← hz, hb, mul_add, hpxz]
      ring
    rw [hpow]
    have htail : (p : S) * π ^ n * π * b ∈ M ^ (n + (p - 1) + 1) :=
      Ideal.mul_mem_right b (M ^ (n + (p - 1) + 1)) hprod
    simpa using htail

private theorem mem_ideal_smul_top_iff_self {R : Type*} [CommRing R]
    (I : Ideal R) {x : R} :
    x ∈ I • (⊤ : Submodule R R) ↔ x ∈ I := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) ?_
    · simpa [smul_eq_mul] using I.mul_mem_right y hr
    · intro x y hx hy
      exact I.add_mem hx hy
  · intro hx
    have h : x • (1 : R) ∈ I • (⊤ : Submodule R R) :=
      Submodule.smul_mem_smul hx Submodule.mem_top
    simpa [smul_eq_mul] using h

private structure CompletedPthRootApprox
    (u : completedLocalCyclotomicUnitGroup p K) (n : ℕ) where
  val : completedLocalCyclotomicUnitGroup p K
  mem_two : val ∈ completedPrincipalUnitSubgroup p K 2
  err : ((val ^ p : completedLocalCyclotomicUnitGroup p K) :
      completedLocalCyclotomicRing p K) - (u : completedLocalCyclotomicRing p K) ∈
    completedLocalCyclotomicMaximalIdeal p K ^ (n + 2 + (p - 1))

private noncomputable def completedPthRootApproxZero
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitSubgroup p K (p + 1)) :
    CompletedPthRootApprox p K u 0 where
  val := 1
  mem_two := one_mem_completedPrincipalUnitSubgroup (p := p) (K := K) 2
  err := by
    let S := completedLocalCyclotomicRing p K
    let M := completedLocalCyclotomicMaximalIdeal p K
    rw [mem_completedPrincipalUnitSubgroup_iff] at hu
    have hp_one : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
    have hidx : 0 + 2 + (p - 1) = p + 1 := by omega
    rw [hidx]
    have hneg : -((u : S) - 1) ∈ M ^ (p + 1) := (M ^ (p + 1)).neg_mem hu
    simpa [S, sub_eq_add_neg, add_comm] using hneg

private noncomputable def completedPthRootApproxResidual
    {u : completedLocalCyclotomicUnitGroup p K} {n : ℕ}
    (A : CompletedPthRootApprox p K u n) :
    completedLocalCyclotomicRing p K :=
  (u : completedLocalCyclotomicRing p K) *
      (((A.val ^ p : completedLocalCyclotomicUnitGroup p K)⁻¹ :
        completedLocalCyclotomicUnitGroup p K) : completedLocalCyclotomicRing p K) - 1

private theorem completedPthRootApproxResidual_mem
    {u : completedLocalCyclotomicUnitGroup p K} {n : ℕ}
    (A : CompletedPthRootApprox p K u n) :
    completedPthRootApproxResidual (p := p) (K := K) A ∈
      completedLocalCyclotomicMaximalIdeal p K ^ (n + 2 + (p - 1)) := by
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let a : completedLocalCyclotomicUnitGroup p K := A.val ^ p
  have ha_inv : ((a : completedLocalCyclotomicUnitGroup p K) : S) *
      (((a : completedLocalCyclotomicUnitGroup p K)⁻¹ :
        completedLocalCyclotomicUnitGroup p K) : S) = 1 :=
    Units.mul_inv a
  have ha_inv_pow : ((A.val : S) ^ p) * (((A.val : completedLocalCyclotomicUnitGroup p K)⁻¹ :
      completedLocalCyclotomicUnitGroup p K) : S) ^ p = 1 := by
    simpa [S, a, Units.val_pow_eq_pow_val, Units.inv_pow_eq_pow_inv] using ha_inv
  have hmul : (((A.val ^ p : completedLocalCyclotomicUnitGroup p K) : S) -
        (u : S)) *
        ((((A.val ^ p : completedLocalCyclotomicUnitGroup p K)⁻¹ :
          completedLocalCyclotomicUnitGroup p K) : S)) ∈
      M ^ (n + 2 + (p - 1)) :=
    Ideal.mul_mem_right _ _ A.err
  have hneg := (M ^ (n + 2 + (p - 1))).neg_mem hmul
  have hres :
      completedPthRootApproxResidual (p := p) (K := K) A =
        -((((A.val ^ p : completedLocalCyclotomicUnitGroup p K) : S) - (u : S)) *
          ((((A.val ^ p : completedLocalCyclotomicUnitGroup p K)⁻¹ :
            completedLocalCyclotomicUnitGroup p K) : S))) := by
    simp only [completedPthRootApproxResidual, Units.val_pow_eq_pow_val,
      Units.inv_pow_eq_pow_inv] at ha_inv ⊢
    rw [sub_mul, ha_inv_pow]
    ring
  rw [hres]
  exact hneg

private noncomputable def completedPthRootCorrection
    {u : completedLocalCyclotomicUnitGroup p K} {n : ℕ}
    (A : CompletedPthRootApprox p K u n) :
    completedLocalCyclotomicUnitGroup p K :=
  Classical.choose
    (exists_completedPrincipalUnit_pow_prime_sub_one_add_mem_next (p := p) (K := K)
      (n := n + 2) (by omega : 2 ≤ n + 2)
      (completedPthRootApproxResidual_mem (p := p) (K := K) A))

private theorem completedPthRootCorrection_mem
    {u : completedLocalCyclotomicUnitGroup p K} {n : ℕ}
    (A : CompletedPthRootApprox p K u n) :
    completedPthRootCorrection (p := p) (K := K) A ∈
      completedPrincipalUnitSubgroup p K (n + 2) :=
  (Classical.choose_spec
    (exists_completedPrincipalUnit_pow_prime_sub_one_add_mem_next (p := p) (K := K)
      (n := n + 2) (by omega : 2 ≤ n + 2)
      (completedPthRootApproxResidual_mem (p := p) (K := K) A))).1

private theorem completedPthRootCorrection_err
    {u : completedLocalCyclotomicUnitGroup p K} {n : ℕ}
    (A : CompletedPthRootApprox p K u n) :
    (((completedPthRootCorrection (p := p) (K := K) A) ^ p :
        completedLocalCyclotomicUnitGroup p K) :
        completedLocalCyclotomicRing p K) -
      (1 + completedPthRootApproxResidual (p := p) (K := K) A) ∈
        completedLocalCyclotomicMaximalIdeal p K ^ ((n + 2) + (p - 1) + 1) :=
  (Classical.choose_spec
    (exists_completedPrincipalUnit_pow_prime_sub_one_add_mem_next (p := p) (K := K)
      (n := n + 2) (by omega : 2 ≤ n + 2)
      (completedPthRootApproxResidual_mem (p := p) (K := K) A))).2

private noncomputable def completedPthRootApproxStep
    {u : completedLocalCyclotomicUnitGroup p K} {n : ℕ}
    (A : CompletedPthRootApprox p K u n) :
    CompletedPthRootApprox p K u (n + 1) where
  val := A.val * completedPthRootCorrection (p := p) (K := K) A
  mem_two := by
    refine (completedPrincipalUnitSubgroup p K 2).mul_mem A.mem_two ?_
    exact completedPrincipalUnitSubgroup_mono (p := p) (K := K)
      (m := n + 2) (n := 2) (by omega)
      (completedPthRootCorrection_mem (p := p) (K := K) A)
  err := by
    let S := completedLocalCyclotomicRing p K
    let M := completedLocalCyclotomicMaximalIdeal p K
    let c := completedPthRootCorrection (p := p) (K := K) A
    let r := completedPthRootApproxResidual (p := p) (K := K) A
    let a : completedLocalCyclotomicUnitGroup p K := A.val ^ p
    have ha_inv : ((a : completedLocalCyclotomicUnitGroup p K) : S) *
        (((a : completedLocalCyclotomicUnitGroup p K)⁻¹ :
          completedLocalCyclotomicUnitGroup p K) : S) = 1 :=
      Units.mul_inv a
    have hr_eq : 1 + r = (u : S) *
        (((a : completedLocalCyclotomicUnitGroup p K)⁻¹ :
          completedLocalCyclotomicUnitGroup p K) : S) := by
      simp [r, completedPthRootApproxResidual, a]
    have ha_res : ((a : completedLocalCyclotomicUnitGroup p K) : S) * (1 + r) =
        (u : S) := by
      rw [hr_eq]
      calc
        ((a : completedLocalCyclotomicUnitGroup p K) : S) *
            ((u : S) * (((a : completedLocalCyclotomicUnitGroup p K)⁻¹ :
              completedLocalCyclotomicUnitGroup p K) : S)) =
          (u : S) * (((a : completedLocalCyclotomicUnitGroup p K) : S) *
            (((a : completedLocalCyclotomicUnitGroup p K)⁻¹ :
              completedLocalCyclotomicUnitGroup p K) : S)) := by ring
        _ = (u : S) := by rw [ha_inv, mul_one]
    have hcerr := completedPthRootCorrection_err (p := p) (K := K) A
    have hmul : ((a : completedLocalCyclotomicUnitGroup p K) : S) *
        (((c ^ p : completedLocalCyclotomicUnitGroup p K) : S) - (1 + r)) ∈
        M ^ ((n + 2) + (p - 1) + 1) :=
      Ideal.mul_mem_left _ _ hcerr
    have htarget :
        (((A.val * c) ^ p : completedLocalCyclotomicUnitGroup p K) : S) -
            (u : S) =
          ((a : completedLocalCyclotomicUnitGroup p K) : S) *
            (((c ^ p : completedLocalCyclotomicUnitGroup p K) : S) - (1 + r)) := by
      rw [mul_sub, ha_res]
      simp [a, c, mul_pow]
    have hidx : (n + 1) + 2 + (p - 1) = (n + 2) + (p - 1) + 1 := by omega
    rw [hidx, htarget]
    exact hmul

private noncomputable def completedPthRootApproxSeq
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitSubgroup p K (p + 1)) :
    (n : ℕ) → CompletedPthRootApprox p K u n
  | 0 => completedPthRootApproxZero (p := p) (K := K) hu
  | n + 1 => completedPthRootApproxStep (p := p) (K := K)
      (completedPthRootApproxSeq hu n)

private theorem completedPthRootApproxSeq_succ_sub_mem
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitSubgroup p K (p + 1)) (n : ℕ) :
    ((completedPthRootApproxSeq (p := p) (K := K) hu (n + 1)).val :
        completedLocalCyclotomicRing p K) -
      ((completedPthRootApproxSeq (p := p) (K := K) hu n).val :
        completedLocalCyclotomicRing p K) ∈
        completedLocalCyclotomicMaximalIdeal p K ^ (n + 2) := by
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let A := completedPthRootApproxSeq (p := p) (K := K) hu n
  let c := completedPthRootCorrection (p := p) (K := K) A
  have hc : (c : S) - 1 ∈ M ^ (n + 2) := by
    simpa [c, M] using completedPthRootCorrection_mem (p := p) (K := K) A
  have hmul : (A.val : S) * ((c : S) - 1) ∈ M ^ (n + 2) :=
    Ideal.mul_mem_left _ _ hc
  change ((completedPthRootApproxStep (p := p) (K := K) A).val : S) - (A.val : S) ∈
    M ^ (n + 2)
  convert hmul using 1
  simp [completedPthRootApproxStep, A, c]
  ring

private theorem completedPthRootApproxSeq_smodEq
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitSubgroup p K (p + 1)) :
    ∀ {m n : ℕ}, m ≤ n →
      ((completedPthRootApproxSeq (p := p) (K := K) hu m).val :
          completedLocalCyclotomicRing p K) ≡
        ((completedPthRootApproxSeq (p := p) (K := K) hu n).val :
          completedLocalCyclotomicRing p K)
        [SMOD (completedLocalCyclotomicMaximalIdeal p K ^ m •
          (⊤ : Submodule (completedLocalCyclotomicRing p K)
            (completedLocalCyclotomicRing p K)))] := by
  intro m n hmn
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst hm
      exact SModEq.rfl
  | succ n ih =>
      by_cases hmn' : m ≤ n
      · refine (ih hmn').trans ?_
        rw [SModEq.sub_mem]
        have hadj := completedPthRootApproxSeq_succ_sub_mem (p := p) (K := K) hu n
        have hmem : ((completedPthRootApproxSeq (p := p) (K := K) hu n).val :
              completedLocalCyclotomicRing p K) -
            ((completedPthRootApproxSeq (p := p) (K := K) hu (n + 1)).val :
              completedLocalCyclotomicRing p K) ∈
            completedLocalCyclotomicMaximalIdeal p K ^ m := by
          have hneg : -(((completedPthRootApproxSeq (p := p) (K := K) hu (n + 1)).val :
              completedLocalCyclotomicRing p K) -
            ((completedPthRootApproxSeq (p := p) (K := K) hu n).val :
              completedLocalCyclotomicRing p K)) ∈
            completedLocalCyclotomicMaximalIdeal p K ^ m :=
            Ideal.pow_le_pow_right (by omega : m ≤ n + 2)
              ((completedLocalCyclotomicMaximalIdeal p K ^ (n + 2)).neg_mem hadj)
          convert hneg using 1
          ring
        exact (mem_ideal_smul_top_iff_self
          (I := completedLocalCyclotomicMaximalIdeal p K ^ m)).mpr hmem
      · have hm : m = n + 1 := by omega
        subst hm
        exact SModEq.rfl

theorem exists_completed_pth_root_mem_two_of_mem_principalUnit_p_add_one
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitSubgroup p K (p + 1)) :
    ∃ v, v ∈ completedPrincipalUnitSubgroup p K 2 ∧ v ^ p = u := by
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let f : ℕ → S := fun n =>
    ((completedPthRootApproxSeq (p := p) (K := K) hu n).val : S)
  have hf : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD M ^ m • (⊤ : Submodule S S)] := by
    intro m n hmn
    exact completedPthRootApproxSeq_smodEq (p := p) (K := K) hu hmn
  have hpre : IsPrecomplete M S :=
    (completedLocalCyclotomic_isAdicComplete (p := p) (K := K)).toIsPrecomplete
  obtain ⟨L, hL⟩ := IsPrecomplete.prec
    (I := M) (M := S) (f := f) hpre hf
  have hL_two : L - 1 ∈ M ^ 2 := by
    have hseq := (completedPthRootApproxSeq (p := p) (K := K) hu 2).mem_two
    rw [mem_completedPrincipalUnitSubgroup_iff] at hseq
    have hconv := hL 2
    rw [SModEq.sub_mem] at hconv
    have hconvI : f 2 - L ∈ M ^ 2 :=
      (mem_ideal_smul_top_iff_self (I := M ^ 2)).mp hconv
    have hL_sub_seq : L - f 2 ∈ M ^ 2 := by
      have hneg := (M ^ 2).neg_mem hconvI
      convert hneg using 1
      ring
    have hsum : (L - f 2) + (f 2 - 1) ∈ M ^ 2 := Ideal.add_mem _ hL_sub_seq hseq
    convert hsum using 1
    ring
  let v : completedLocalCyclotomicUnitGroup p K :=
    completedOneAddUnitOfMemMaximalIdealPow (p := p) (K := K) (n := 2)
      (by decide) hL_two
  have hv_coe : (v : S) = L := by
    simp [v]
  have hv_mem : v ∈ completedPrincipalUnitSubgroup p K 2 := by
    rw [mem_completedPrincipalUnitSubgroup_iff]
    simpa [hv_coe] using hL_two
  have hroot_ring : ((v ^ p : completedLocalCyclotomicUnitGroup p K) : S) = (u : S) := by
    rw [IsHausdorff.eq_iff_smodEq (I := M)]
    intro n
    have hconv : f n ≡ L [SMOD M ^ n] := by
      rw [SModEq.sub_mem]
      have h := hL n
      rw [SModEq.sub_mem] at h
      exact (mem_ideal_smul_top_iff_self (I := M ^ n)).mp h
    have hpow : (f n) ^ p ≡ L ^ p [SMOD M ^ n] := SModEq.pow p hconv
    have herr := (completedPthRootApproxSeq (p := p) (K := K) hu n).err
    have hseq_root : (f n) ^ p ≡ (u : S) [SMOD M ^ n] := by
      rw [SModEq.sub_mem]
      exact Ideal.pow_le_pow_right (by omega : n ≤ n + 2 + (p - 1)) (by
        simpa [f, Units.val_pow_eq_pow_val] using herr)
    have hL_root : L ^ p ≡ (u : S) [SMOD M ^ n] := hpow.symm.trans hseq_root
    rw [SModEq.sub_mem]
    have hmem : L ^ p - (u : S) ∈ M ^ n := SModEq.sub_mem.mp hL_root
    have htarget : ((v ^ p : completedLocalCyclotomicUnitGroup p K) : S) - (u : S) ∈
        M ^ n := by
      convert hmem using 1
      simp [hv_coe, Units.val_pow_eq_pow_val]
    exact (mem_ideal_smul_top_iff_self (I := M ^ n)).mpr htarget
  exact ⟨v, hv_mem, Units.ext hroot_ring⟩

/-- The hard reverse endpoint statement in the completed local unit group. -/
def completedPrincipalUnitPowerEndpointReverse : Prop :=
  completedPrincipalUnitSubgroup p K (p + 1) ≤
    completedPrincipalUnitPowerSubgroup p K p 1

theorem completedPrincipalUnitPowerEndpointReverse_iff :
    completedPrincipalUnitPowerEndpointReverse p K ↔
      completedPrincipalUnitSubgroup p K (p + 1) ≤
        completedPrincipalUnitPowerSubgroup p K p 1 :=
  Iff.rfl

theorem exists_completed_pth_root_of_mem_principalUnit_p_add_one
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitSubgroup p K (p + 1)) :
    ∃ v, v ∈ completedPrincipalUnitSubgroup p K 1 ∧ v ^ p = u := by
  rcases exists_completed_pth_root_mem_two_of_mem_principalUnit_p_add_one
      (p := p) (K := K) hu with
    ⟨v, hv, hvp⟩
  exact ⟨v, completedPrincipalUnitSubgroup_mono (p := p) (K := K)
    (m := 2) (n := 1) (by decide) hv, hvp⟩

theorem completedPrincipalUnitPowerEndpointReverse_of_recursive :
    completedPrincipalUnitPowerEndpointReverse p K := by
  intro u hu
  rw [mem_completedPrincipalUnitPowerSubgroup_iff]
  exact exists_completed_pth_root_of_mem_principalUnit_p_add_one (p := p) (K := K) hu

theorem exists_completed_pth_root_of_endpoint_reverse
    (hreverse : completedPrincipalUnitPowerEndpointReverse p K)
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitSubgroup p K (p + 1)) :
    ∃ v, v ∈ completedPrincipalUnitSubgroup p K 1 ∧ v ^ p = u :=
  (mem_completedPrincipalUnitPowerSubgroup_iff (p := p) (K := K)).mp (hreverse hu)

theorem completedPrincipalUnitPowerSubgroup_one_eq_p_add_one_of_le
    (hupper : completedPrincipalUnitPowerSubgroup p K p 1 ≤
      completedPrincipalUnitSubgroup p K (p + 1))
    (hreverse : completedPrincipalUnitPowerEndpointReverse p K) :
    completedPrincipalUnitPowerSubgroup p K p 1 =
      completedPrincipalUnitSubgroup p K (p + 1) :=
  le_antisymm hupper ((completedPrincipalUnitPowerEndpointReverse_iff (p := p) (K := K)).mp
    hreverse)

theorem completedPrincipalUnitPowerSubgroup_one_eq_p_add_one_of_upper
    (hupper : completedPrincipalUnitPowerSubgroup p K p 1 ≤
      completedPrincipalUnitSubgroup p K (p + 1)) :
    completedPrincipalUnitPowerSubgroup p K p 1 =
      completedPrincipalUnitSubgroup p K (p + 1) :=
  completedPrincipalUnitPowerSubgroup_one_eq_p_add_one_of_le (p := p) (K := K) hupper
    (completedPrincipalUnitPowerEndpointReverse_of_recursive (p := p) (K := K))

theorem completedPrincipalUnitPowerSubgroup_one_eq_p_add_one_of_zeta_zpowers_eq_top
    (htop : Subgroup.zpowers
      (completedPrincipalUnitFirstGradedHom p K
        (completedLocalCyclotomicZetaPrincipalUnit p K)) = ⊤) :
    completedPrincipalUnitPowerSubgroup p K p 1 =
      completedPrincipalUnitSubgroup p K (p + 1) :=
  completedPrincipalUnitPowerSubgroup_one_eq_p_add_one_of_upper (p := p) (K := K)
    (completedPrincipalUnitPowerSubgroup_one_le_p_add_one_of_zeta_zpowers_eq_top
      (p := p) (K := K) htop)

theorem completedPrincipalUnitPowerSubgroup_one_eq_p_add_one :
    completedPrincipalUnitPowerSubgroup p K p 1 =
      completedPrincipalUnitSubgroup p K (p + 1) :=
  completedPrincipalUnitPowerSubgroup_one_eq_p_add_one_of_zeta_zpowers_eq_top
    (p := p) (K := K)
    (completedPrincipalUnitFirstGradedHom_zeta_zpowers_eq_top (p := p) (K := K))

end CyclotomicSetup

end Local
end Reflection
end BernoulliRegular
