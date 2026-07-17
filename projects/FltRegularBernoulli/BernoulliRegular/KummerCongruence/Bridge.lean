/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Characters
public import BernoulliRegular.KummerCongruence.Kummer

/-!
# Kummer congruences — Bridge (T012) and boundary (T013)

This module proves the two "bridge" congruences between classical and
generalized Bernoulli numbers:

- **T012** (`bernoulliGen_teichmuller_pow_sModEq_div`): for odd `n` with
  `(p − 1) ∤ (n + 1)`,
    `B_{1, ω^n} ≡ B_{n+1} / (n+1) (mod p)`.
  Combines the sharper Teichmüller congruence (Step 1, in
  `BernoulliRegular.Characters`) with Step 2 (power-sum mod `p²`) and
  T011 (Kummer's congruence).

- **T013** (boundary case): at `n = p − 2`, the RHS `B_{p−1}/(p−1)` has a
  `p` in its denominator (von Staudt–Clausen), so T012 does not apply
  directly. Instead,
    `B_{1, ω^{p−2}} ≡ bernoulli (p−1) (mod ℤ_[p])`
  (`bernoulliGen_teichmuller_inv_sub_bernoulli_mem_padicInt`), via T008
  and T010. We also record the Diekmann-page-51 boundary factor
  `2p · (−1/2) · B_{1, ω^{p−2}} = 1 + p · z`
  (`boundary_teichmuller_factor_eq_one_add_p_mul`).
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

private lemma teichmuller_pow_mul_val_sub_val_pow_mem_maximalIdeal_sq {p : ℕ} [hp : Fact p.Prime]
    (n : ℕ) (a : ZMod p) :
    (teichmuller p a) ^ n * (a.val : ℤ_[p]) - (a.val : ℤ_[p]) ^ (p * n + 1) ∈
      (IsLocalRing.maximalIdeal ℤ_[p]) ^ 2 := by
  have h_mul :=
    (SModEq.sub_mem.mpr (teichmuller_sub_pow_val_mem_pow_two (p := p) a)).pow n |>.mul
      (SModEq.refl (a.val : ℤ_[p]))
  rw [SModEq.sub_mem] at h_mul
  simpa only [← pow_mul, ← pow_succ] using h_mul

private lemma coe_sum_teichmuller_pow_mul_val {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
    (hn : n ≠ 0) :
    ((∑ a : ZMod p, (teichmuller p a) ^ n * (a.val : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) =
      ∑ a : ZMod p, ((teichmullerCharQp p) ^ n) a * (a.val : ℚ_[p]) := by
  rw [PadicInt.coe_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
  congr 1
  rw [teichmullerCharQp_pow_eq_ringHomComp (p := p) (n := n),
    MulChar.ringHomComp_apply, MulChar.pow_apply' _ hn,
    map_pow, teichmullerChar_apply]
  rfl

private lemma coe_sum_val_pow {p : ℕ} [hp : Fact p.Prime] (t : ℕ) :
    ((∑ a : ZMod p, (a.val : ℤ_[p]) ^ t : ℤ_[p]) : ℚ_[p]) =
      ∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t := by
  rw [PadicInt.coe_sum]
  simp_rw [PadicInt.coe_pow, PadicInt.coe_natCast]
  refine Finset.sum_nbij (fun a ↦ a.val) ?_ ?_ ?_ ?_
  · intro a _
    simp only [Finset.mem_range]
    exact ZMod.val_lt a
  · intro a _ b _ hab
    exact ZMod.val_injective _ hab
  · intro k hk
    simp only [Finset.coe_univ, Set.image_univ, Set.mem_range]
    simp only [Finset.mem_coe, Finset.mem_range] at hk
    exact ⟨(k : ZMod p), ZMod.val_natCast_of_lt hk⟩
  · intro a _
    rfl

private lemma bernoulliGen_mul_p_sub_sum_pow_mem {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : p ≠ 2) {n : ℕ} (hn_odd : Odd n) (hn_pos : 0 < n) :
    ∃ z : ℤ_[p],
      (p : ℚ_[p]) * BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
          (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ (p * n + 1)) =
        (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hn_not_dvd : ¬ (p - 1) ∣ n := by
    intro hdvd
    have hp_minus_one_even : 2 ∣ (p - 1) := by
      obtain ⟨k, _⟩ := hp.odd_of_ne_two hp_odd
      exact ⟨k, by omega⟩
    obtain ⟨l, hl⟩ := dvd_trans hp_minus_one_even hdvd
    obtain ⟨k, hk⟩ := hn_odd
    omega
  let S : ℤ_[p] := ∑ a : ZMod p, (teichmuller p a) ^ n * (a.val : ℤ_[p])
  let T : ℤ_[p] := ∑ a : ZMod p, (a.val : ℤ_[p]) ^ (p * n + 1)
  have hST_mem : S - T ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ 2 := by
    change (∑ a : ZMod p, (teichmuller p a) ^ n * (a.val : ℤ_[p])) -
        (∑ a : ZMod p, (a.val : ℤ_[p]) ^ (p * n + 1)) ∈ _
    rw [← Finset.sum_sub_distrib]
    exact Ideal.sum_mem _ fun a _ ↦
      teichmuller_pow_mul_val_sub_val_pow_mem_maximalIdeal_sq n a
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hST_mem
  obtain ⟨w, hw⟩ := hST_mem
  refine ⟨w, ?_⟩
  calc (p : ℚ_[p]) * BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
        (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ (p * n + 1))
      = (((S : ℤ_[p]) : ℚ_[p])) - ((T : ℤ_[p]) : ℚ_[p]) := by
        rw [show ((S : ℤ_[p]) : ℚ_[p]) =
              ∑ a : ZMod p, ((teichmullerCharQp p) ^ n) a * (a.val : ℚ_[p]) from
            coe_sum_teichmuller_pow_mul_val hn_pos.ne',
          show ((T : ℤ_[p]) : ℚ_[p]) =
              ∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ (p * n + 1) from
            coe_sum_val_pow (p * n + 1),
          natCast_mul_BernoulliGen_one_of_ne_one (R := ℚ_[p]) (N := p)
            (χ := (teichmullerCharQp p) ^ n)
            (teichmullerCharQp_pow_ne_one_of_not_dvd (p := p) hn_not_dvd)]
    _ = (((S - T : ℤ_[p]) : ℚ_[p])) := by rw [PadicInt.coe_sub]
    _ = (((p : ℤ_[p]) ^ 2 * w : ℤ_[p]) : ℚ_[p]) := by rw [hw]
    _ = (p : ℚ_[p]) ^ 2 * (w : ℚ_[p]) := by
      push_cast
      ring

private lemma sum_pow_t_sub_p_mul_bernoulli_mem {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : p ≠ 2) {n : ℕ} (hn_odd : Odd n) (hn_pos : 0 < n)
    (h_below_t : ∀ j, j ≤ p * n + 1 → ¬ (p : ℕ) ^ 3 ∣ (j + 1)) :
    ∃ z : ℤ_[p],
      (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ (p * n + 1)) -
          (p : ℚ_[p]) * ((bernoulli (p * n + 1) : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  refine sum_range_pow_sModEq_p_mul_bernoulli hp_odd ?_ ?_ ?_ ?_
  · exact Nat.succ_le_succ <|
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero hn_pos.ne')
  · exact ((hp.odd_of_ne_two hp_odd).mul hn_odd).add_one
  ·
    intro hdvd
    have h_eq : p * n + 1 + 1 = p * n + 2 := by omega
    rw [h_eq] at hdvd
    have hp2 : p ∣ 2 := by simpa using Nat.dvd_sub hdvd ⟨n, rfl⟩
    exact absurd (Nat.le_of_dvd (by omega) hp2) (by omega)
  ·
    intro j hj hj_two hj_even
    exact p_mul_bernoulli_mem_padicInt_restricted hp_odd hj_two hj_even
      fun j' hj' ↦ h_below_t j' (Nat.le_trans hj' hj.le)

private lemma bernoulli_sub_eq_mul_of_div_sub_eq_mul {p n t : ℕ} [Fact p.Prime]
    (ht_def : t = p * n + 1) (ht_pos : 0 < t) {b z : ℤ_[p]}
    (h : (((bernoulli t : ℚ) / t : ℚ) : ℚ_[p]) - (b : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p])) :
    ((bernoulli t : ℚ) : ℚ_[p]) - (b : ℚ_[p]) =
      (p : ℚ_[p]) * (((n : ℤ_[p]) * b + (t : ℤ_[p]) * z : ℤ_[p]) : ℚ_[p]) := by
  have htQ_ne : (t : ℚ_[p]) ≠ 0 := by exact_mod_cast ht_pos.ne'
  have h_BtOverT : (((bernoulli t : ℚ) / t : ℚ) : ℚ_[p]) =
      (b : ℚ_[p]) + (p : ℚ_[p]) * (z : ℚ_[p]) := by
    linear_combination h
  have h_Bt : ((bernoulli t : ℚ) : ℚ_[p]) = (t : ℚ_[p]) *
      (((bernoulli t : ℚ) / t : ℚ) : ℚ_[p]) := by
    push_cast
    field_simp
  rw [h_Bt, h_BtOverT]
  have ht_sub : (t : ℚ_[p]) = (p : ℚ_[p]) * (n : ℚ_[p]) + 1 := by
    rw [ht_def]
    push_cast
    rfl
  push_cast
  rw [ht_sub]
  ring

private lemma bernoulli_t_sub_div_mem {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : p ≠ 2) {n : ℕ} (hn_odd : Odd n)
    (h_pSubOne_not_dvd_nPlus : ¬ (p - 1) ∣ (n + 1))
    (hn_p_plus : ¬ (p : ℕ) ∣ (n + 1))
    (hn_p_plus_two : ¬ (p : ℕ) ∣ (n + 2))
    (hn_small : n + 1 < p - 1)
    (h_below_t : ∀ j, j ≤ p * n + 1 → ¬ (p : ℕ) ^ 3 ∣ (j + 1))
    (h_below_n1 : ∀ j, j ≤ n + 1 → ¬ (p : ℕ) ^ 3 ∣ (j + 1)) :
    ∃ z : ℤ_[p],
      (((bernoulli (p * n + 1) : ℚ) : ℚ_[p])) -
          (((bernoulli (n + 1) : ℚ) / (n + 1) : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  set t : ℕ := p * n + 1 with ht_def
  have ht_pos : 0 < t := by omega
  have hn1_pos : 0 < n + 1 := Nat.succ_pos n
  have h_mn_modEq : t ≡ (n + 1) [MOD (p - 1)] := by
    have h_eq : t = (n + 1) + (p - 1) * n := by
      simp only [ht_def]
      have hn_le : n ≤ p * n := Nat.le_mul_of_pos_left n (by omega)
      have hpn : (p - 1) * n = p * n - n := by rw [Nat.sub_mul, Nat.one_mul]
      omega
    unfold Nat.ModEq
    rw [h_eq, Nat.add_mul_mod_self_left]
  have ht_coprime : ¬ (p : ℕ) ∣ t := fun h ↦ by
    rw [(ht_def : t = p * n + 1)] at h
    exact absurd
      (Nat.le_of_dvd (by omega) ((Nat.dvd_add_right (show p ∣ p * n from ⟨n, rfl⟩)).mp h))
      (by omega)
  have ht_p_plus : ¬ (p : ℕ) ∣ (t + 1) := fun h ↦ by
    have h_eq_t1 : t + 1 = p * n + 2 := by omega
    rw [h_eq_t1] at h
    have hp2 : p ∣ 2 := by simpa using Nat.dvd_sub h ⟨n, rfl⟩
    exact absurd (Nat.le_of_dvd (by omega) hp2) (by omega)
  obtain ⟨z', hz'⟩ := bernoulli_div_sModEq_of_modEq hp_odd
    ht_pos hn1_pos ((hp.odd_of_ne_two hp_odd).mul hn_odd).add_one hn_odd.add_one
      h_pSubOne_not_dvd_nPlus h_mn_modEq
    ht_coprime hn_p_plus ht_p_plus hn_p_plus_two h_below_t h_below_n1
  obtain ⟨bn1, hbn1⟩ := bernoulli_mem_padicInt_of_lt_sub_one hp_odd (n + 1) hn_small
  have hn1_unit : IsUnit ((n + 1 : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hn1_pos (by omega))
  set n1Inv : ℤ_[p] := (hn1_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hn1Inv_mul : ((n + 1 : ℕ) : ℤ_[p]) * n1Inv = 1 := by
    change ((hn1_unit.unit * hn1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    rw [mul_inv_cancel]
    rfl
  have hn1Inv_mul_Qp : ((n + 1 : ℕ) : ℚ_[p]) * ((n1Inv : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p])) hn1Inv_mul
  set b : ℤ_[p] := bn1 * n1Inv with hb_def
  have hb : (((bernoulli (n + 1) : ℚ) / (n + 1 : ℕ) : ℚ) : ℚ_[p]) =
      ((b : ℤ_[p]) : ℚ_[p]) := by
    have h_div : (((bernoulli (n + 1) : ℚ) / (n + 1 : ℕ) : ℚ) : ℚ_[p]) =
        ((bernoulli (n + 1) : ℚ) : ℚ_[p]) / ((n + 1 : ℕ) : ℚ_[p]) := by
      push_cast
      rfl
    rw [h_div, hbn1, div_eq_mul_inv,
      inv_eq_of_mul_eq_one_right hn1Inv_mul_Qp]
    simp only [hb_def, PadicInt.coe_mul]
  rw [hb] at hz'
  refine ⟨(n : ℤ_[p]) * b + (t : ℤ_[p]) * z', ?_⟩
  have hb' : (((bernoulli (n + 1) : ℚ) / (↑n + 1) : ℚ) : ℚ_[p]) =
      (b : ℚ_[p]) := by
    rw [show ((((bernoulli (n + 1) : ℚ) / (↑n + 1) : ℚ)) : ℚ_[p]) =
        (((bernoulli (n + 1) : ℚ) / ↑(n + 1) : ℚ) : ℚ_[p]) from by
      push_cast
      ring_nf, hb]
  rw [hb']
  exact bernoulli_sub_eq_mul_of_div_sub_eq_mul ht_def ht_pos hz'

/-- **T012** (Diekmann Cor 34 / Erickson App. A.1.26).
For `n` odd with `n ≢ -1 (mod p-1)` (i.e. `(p-1) ∤ (n+1)`),
  `B_{1, ω^n} ≡ B_{n+1}/(n+1) (mod p)`
as elements of `ℚ_[p]` (both p-adic integers).

**Proof** (Erickson, elementary): let `t := p·n + 1`, which is even
(as `n` is odd and `p` is odd). Then:
1. `p · B_{1, ω^n} = ∑ ω(a)^n · (a.val) ≡ ∑ (a.val)^{p·n + 1} (mod p²)`
   by the sharper Teichmüller congruence
   `ω(a) ≡ (a.val)^p (mod p²)` (Step 1).
2. `∑ (a.val)^t ≡ p · B_t (mod p²)` by Step 2.
3. Combining, `p · B_{1, ω^n} ≡ p · B_t (mod p²)`, so
   `B_{1, ω^n} ≡ B_t (mod p)`.
4. `t ≡ n + 1 (mod p-1)` with `(p-1) ∤ (n+1)`, so Step 3 (T011) gives
   `B_t / t ≡ B_{n+1} / (n+1) (mod p)`.
5. `t ≡ 1 (mod p)`, so `B_t ≡ B_{n+1}/(n+1) (mod p)`.
6. Combining steps 3 and 5: `B_{1, ω^n} ≡ B_{n+1}/(n+1) (mod p)`. -/
theorem bernoulliGen_teichmuller_pow_sModEq_div
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {n : ℕ} (hn_odd : Odd n) (hn_pos : 0 < n)
    (h_pSubOne_not_dvd_nPlus : ¬ (p - 1) ∣ (n + 1))
    (hn_p_plus : ¬ (p : ℕ) ∣ (n + 1))
    (hn_p_plus_two : ¬ (p : ℕ) ∣ (n + 2))
    (hn_small : n + 1 < p - 1) :
    ∃ z : ℤ_[p],
      BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
          (((bernoulli (n + 1) : ℚ) / (n + 1) : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  set t : ℕ := p * n + 1 with ht_def
  have h_t_lt_p_sq : t + 1 < p ^ 2 := by
    obtain ⟨r, hr⟩ : ∃ r, p = r + 3 := ⟨p - 3, by omega⟩
    have ht_succ : t + 1 = p * n + 2 := by omega
    rw [ht_succ, hr, pow_two]
    nlinarith [(by omega : n ≤ r), Nat.zero_le r]
  have h_p_sq_lt_p_cube : p ^ 2 < p ^ 3 := by
    have h_p2_pos : 0 < p ^ 2 := by positivity
    simpa [pow_succ] using (Nat.mul_lt_mul_left h_p2_pos).mpr hp.one_lt
  have h_below_t : ∀ j, j ≤ t → ¬ (p : ℕ) ^ 3 ∣ (j + 1) := fun j hj hdvd ↦
    absurd (Nat.le_of_dvd (Nat.succ_pos j) hdvd) (by omega)
  have h_p_lt_p_sq : p < p ^ 2 := by nlinarith [hp.one_lt]
  have h_below_n1 : ∀ j, j ≤ n + 1 → ¬ (p : ℕ) ^ 3 ∣ (j + 1) := fun j hj hdvd ↦
    absurd (Nat.le_of_dvd (Nat.succ_pos j) hdvd) (by omega)
  obtain ⟨z₁, hz₁⟩ := bernoulliGen_mul_p_sub_sum_pow_mem hp_odd hn_odd hn_pos
  obtain ⟨z₂, hz₂⟩ := sum_pow_t_sub_p_mul_bernoulli_mem hp_odd hn_odd hn_pos h_below_t
  obtain ⟨z₃, hz₃⟩ := bernoulli_t_sub_div_mem hp_odd hn_odd
    h_pSubOne_not_dvd_nPlus hn_p_plus hn_p_plus_two hn_small h_below_t h_below_n1
  refine ⟨z₁ + z₂ + z₃, ?_⟩
  have h_bridge : BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
      ((bernoulli t : ℚ) : ℚ_[p]) = (p : ℚ_[p]) * ((z₁ : ℚ_[p]) + (z₂ : ℚ_[p])) :=
    (mul_right_inj' hpQ_ne).mp <| by linear_combination hz₁ + hz₂
  calc BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
        (((bernoulli (n + 1) : ℚ) / (n + 1) : ℚ) : ℚ_[p])
      = (BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
           ((bernoulli t : ℚ) : ℚ_[p])) +
        (((bernoulli t : ℚ) : ℚ_[p]) -
           (((bernoulli (n + 1) : ℚ) / (n + 1) : ℚ) : ℚ_[p])) := by ring
    _ = (p : ℚ_[p]) * ((z₁ : ℚ_[p]) + (z₂ : ℚ_[p])) +
        (p : ℚ_[p]) * (z₃ : ℚ_[p]) := by
      rw [h_bridge, hz₃]
    _ = (p : ℚ_[p]) * ((z₁ + z₂ + z₃ : ℤ_[p]) : ℚ_[p]) := by
      push_cast
      ring

/-- **Boundary Kummer congruence.** For an odd prime `p`, the
generalized Bernoulli number at the boundary character `ω^{p-2}`
and the classical `B_{p-1}` differ by a `p`-adic integer:

  `B_{1, ω^{p-2}} ≡ bernoulli (p-1) (mod ℤ_[p])`.

This is the Kummer-type congruence at the boundary case
`n ≡ -1 (mod p - 1)` not covered by T012. -/
theorem bernoulliGen_teichmuller_inv_sub_bernoulli_mem_padicInt
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2) :
    ∃ z : ℤ_[p],
      BernoulliGen ((teichmullerCharQp p) ^ (p - 2)) 1 -
        ((bernoulli (p - 1) : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
  obtain ⟨z₁, hz₁⟩ :=
    bernoulliGen_teichmuller_inverse_eq_p_sub_one_div_p_add_padicInt hp_odd
  obtain ⟨z₂, hz₂⟩ := bernoulli_pSubOne_add_inv_p_mem_padicInt hp_odd
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  refine ⟨1 + z₁ - z₂, ?_⟩
  rw [hz₁, eq_sub_of_add_eq hz₂]
  push_cast
  field_simp
  ring

/-- Diekmann page 51: the boundary factor in equation (32) is congruent to
`1` modulo `p`. More precisely,

`2p · (-1/2) · B_{1,ω^{p-2}} = 1 + pz`

for some `z ∈ ℤ_p`. This is the exceptional factor separated off in the proof
of Theorem 42. -/
theorem boundary_teichmuller_factor_eq_one_add_p_mul
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2) :
    ∃ z : ℤ_[p],
      (2 * p : ℚ_[p]) * (-(1 / 2 : ℚ_[p])) *
          BernoulliGen ((teichmullerCharQp p) ^ (p - 2)) 1 =
        1 + (p : ℚ_[p]) * (z : ℚ_[p]) := by
  obtain ⟨z₀, hz₀⟩ :=
    bernoulliGen_teichmuller_inverse_eq_p_sub_one_div_p_add_padicInt hp_odd
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have htwo_ne : (2 : ℚ_[p]) ≠ 0 := by norm_num
  refine ⟨-1 - z₀, ?_⟩
  rw [hz₀]
  push_cast
  field_simp [hpQ_ne, htwo_ne]
  ring

end BernoulliRegular
