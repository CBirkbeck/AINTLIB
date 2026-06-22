module

public import BernoulliRegular.KummerCongruence.Kummer
public import BernoulliRegular.Characters

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

/-! ### T012 — Bridge `B_{1, ω^n} ≡ B_{n+1}/(n+1) (mod p)` -/

/-- **Ingredient 1 of T012** (Step 1 + T006). With `t := p·n + 1`, the sharper
Teichmüller congruence `ω(a) ≡ (a.val)^p (mod p²)` gives, after summing over `ZMod p`
and lifting to `ℚ_[p]`,
  `p · B_{1, ω^n} - ∑_{k<p} k^t ≡ 0 (mod p²)`. -/
private lemma bernoulliGen_mul_p_sub_sum_pow_mem {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : p ≠ 2) {n : ℕ} (hn_odd : Odd n) (hn_pos : 0 < n) :
    ∃ z : ℤ_[p],
      (p : ℚ_[p]) * BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
          (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ (p * n + 1)) =
        (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  -- ω^n ≠ 1 for odd n (since p-1 even, (p-1) ∤ n).
  have hn_ne_zero : n ≠ 0 := hn_pos.ne'
  have hn_not_dvd : ¬ (p - 1) ∣ n := by
    intro hdvd
    have hp_minus_one_even : 2 ∣ (p - 1) := by
      obtain ⟨k, _⟩ := hp.odd_of_ne_two hp_odd
      exact ⟨k, by omega⟩
    have h2n : 2 ∣ n := dvd_trans hp_minus_one_even hdvd
    obtain ⟨k, hk⟩ := hn_odd
    rw [hk] at h2n
    omega
  have hωQ_ne_one : (teichmullerCharQp p) ^ n ≠ 1 :=
    teichmullerCharQp_pow_ne_one_of_not_dvd (p := p) hn_not_dvd
  -- T006 in ℚ_[p].
  have hT006 := natCast_mul_BernoulliGen_one_of_ne_one
    (R := ℚ_[p]) (N := p) (χ := (teichmullerCharQp p) ^ n) hωQ_ne_one
  -- Pointwise ℤ_[p] bound.
  have hterm_mem : ∀ a : ZMod p,
      (teichmuller p a) ^ n * (a.val : ℤ_[p]) - (a.val : ℤ_[p]) ^ (p * n + 1) ∈
      (IsLocalRing.maximalIdeal ℤ_[p]) ^ 2 := by
    intro a
    have h_mod : teichmuller p a ≡ (a.val : ℤ_[p]) ^ p
        [SMOD (IsLocalRing.maximalIdeal ℤ_[p]) ^ 2] :=
      SModEq.sub_mem.mpr (teichmuller_sub_pow_val_mem_pow_two (p := p) a)
    have h_pow := h_mod.pow n
    have h_mul := h_pow.mul (SModEq.refl (a.val : ℤ_[p]))
    rw [SModEq.sub_mem] at h_mul
    have h_simp : ((a.val : ℤ_[p]) ^ p) ^ n * (a.val : ℤ_[p]) =
        (a.val : ℤ_[p]) ^ (p * n + 1) := by
      rw [← pow_mul, ← pow_succ]
    rw [h_simp] at h_mul
    exact h_mul
  -- Sum the bounds: S - T ∈ (𝔪)².
  let S : ℤ_[p] := ∑ a : ZMod p, (teichmuller p a) ^ n * (a.val : ℤ_[p])
  let T : ℤ_[p] := ∑ a : ZMod p, (a.val : ℤ_[p]) ^ (p * n + 1)
  have hST_mem : S - T ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ 2 := by
    change (∑ a : ZMod p, (teichmuller p a) ^ n * (a.val : ℤ_[p])) -
        (∑ a : ZMod p, (a.val : ℤ_[p]) ^ (p * n + 1)) ∈ _
    rw [← Finset.sum_sub_distrib]
    exact Ideal.sum_mem _ fun a _ ↦ hterm_mem a
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hST_mem
  obtain ⟨w, hw⟩ := hST_mem
  refine ⟨w, ?_⟩
  -- Lift S to ℚ_[p] and match with p · B_{1, ωQ^n}.
  have hS_coe : ((S : ℤ_[p]) : ℚ_[p]) =
      ∑ a : ZMod p, ((teichmullerCharQp p) ^ n) a * (a.val : ℚ_[p]) := by
    change ((∑ a : ZMod p, (teichmuller p a) ^ n * (a.val : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) = _
    rw [PadicInt.coe_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
    congr 1
    rw [teichmullerCharQp_pow_eq_ringHomComp (p := p) (n := n),
      MulChar.ringHomComp_apply, MulChar.pow_apply' _ hn_ne_zero,
      map_pow, teichmullerChar_apply]
    rfl
  -- Lift T to ℚ_[p] and match with ∑ k^t.
  have hT_coe : ((T : ℤ_[p]) : ℚ_[p]) =
      ∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ (p * n + 1) := by
    change ((∑ a : ZMod p, (a.val : ℤ_[p]) ^ (p * n + 1) : ℤ_[p]) : ℚ_[p]) = _
    rw [PadicInt.coe_sum]
    simp_rw [show ∀ a : ZMod p,
        (((a.val : ℤ_[p]) ^ (p * n + 1) : ℤ_[p]) : ℚ_[p]) = ((a.val : ℚ_[p]) ^ (p * n + 1)) from
      fun a ↦ by rw [PadicInt.coe_pow, PadicInt.coe_natCast]]
    refine Finset.sum_nbij (fun a ↦ a.val) ?_ ?_ ?_ ?_
    · intro a _; simp only [Finset.mem_range]; exact ZMod.val_lt a
    · intros a _ b _ hab; exact ZMod.val_injective _ hab
    · intros k hk
      simp only [Finset.coe_univ, Set.image_univ, Set.mem_range]
      simp only [Finset.mem_coe, Finset.mem_range] at hk
      exact ⟨(k : ZMod p), ZMod.val_natCast_of_lt hk⟩
    · intros a _; rfl
  -- Combine.
  calc (p : ℚ_[p]) * BernoulliGen ((teichmullerCharQp p) ^ n) 1 -
        (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ (p * n + 1))
      = (((S : ℤ_[p]) : ℚ_[p])) - ((T : ℤ_[p]) : ℚ_[p]) := by
        rw [hS_coe, hT_coe, hT006]
    _ = (((S - T : ℤ_[p]) : ℚ_[p])) := by rw [PadicInt.coe_sub]
    _ = (((p : ℤ_[p]) ^ 2 * w : ℤ_[p]) : ℚ_[p]) := by rw [hw]
    _ = (p : ℚ_[p]) ^ 2 * (w : ℚ_[p]) := by push_cast; ring

/-- **Ingredient 2 of T012** (Step 2, power sums mod `p²`). With `t := p·n + 1`,
  `∑_{k<p} k^t - p · B_t ≡ 0 (mod p²)`,
the Faulhaber/von-Staudt–Clausen power-sum congruence. -/
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
  · -- 2 ≤ t
    have hpn : 1 ≤ p * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero hn_pos.ne')
    omega
  · exact ((hp.odd_of_ne_two hp_odd).mul hn_odd).add_one
  · -- ¬ p ∣ (t + 1)
    intro hdvd
    have h_pn : p ∣ p * n := ⟨n, rfl⟩
    have h_eq : p * n + 1 + 1 = p * n + 2 := by omega
    rw [h_eq] at hdvd
    have hp2 : p ∣ 2 := by simpa using Nat.dvd_sub hdvd h_pn
    exact absurd (Nat.le_of_dvd (by omega) hp2) (by omega)
  · -- IH for `p · B_j ∈ ℤ_[p]` at j < t (via the unified restricted theorem).
    intro j hj hj_two hj_even
    exact p_mul_bernoulli_mem_padicInt_restricted hp_odd hj_two hj_even
      (fun j' hj' ↦ h_below_t j' (Nat.le_trans hj' hj.le))

/-- **Ingredient 3 of T012** (T011 + `t ≡ 1 (mod p)` + integrality). With
`t := p·n + 1`, `t ≡ n+1 (mod p-1)` and `t ≡ 1 (mod p)`, so Kummer's congruence
(T011) plus the integrality of `B_{n+1}` (`n+1 < p-1`) gives
  `B_t - B_{n+1}/(n+1) ≡ 0 (mod p)`. -/
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
  have ht_pos : 0 < t := by simp [ht_def]
  have hn1_pos : 0 < n + 1 := Nat.succ_pos n
  have hn1_even : Even (n + 1) := hn_odd.add_one
  have hp_odd_pred : Odd p := hp.odd_of_ne_two hp_odd
  have ht_even : Even t := (hp_odd_pred.mul hn_odd).add_one
  -- `t ≡ n+1 [MOD (p-1)]`: `t = (n+1) + (p-1)·n`.
  have h_mn_modEq : t ≡ (n + 1) [MOD (p - 1)] := by
    have h_eq : t = (n + 1) + (p - 1) * n := by
      simp only [ht_def]
      have hn_le : n ≤ p * n := Nat.le_mul_of_pos_left n (by omega)
      have hpn : (p - 1) * n = p * n - n := by rw [Nat.sub_mul, Nat.one_mul]
      omega
    unfold Nat.ModEq; rw [h_eq, Nat.add_mul_mod_self_left]
  -- `p ∤ t` since `t = p·n + 1 ≡ 1 (mod p)` and `p ≥ 3`.
  have ht_coprime : ¬ (p : ℕ) ∣ t := fun h ↦ by
    have h_pn : p ∣ p * n := ⟨n, rfl⟩
    rw [(ht_def : t = p * n + 1)] at h
    exact absurd (Nat.le_of_dvd (by omega) ((Nat.dvd_add_right h_pn).mp h)) (by omega)
  -- `p ∤ (t + 1) = p·n + 2`: since `p ≥ 3`.
  have ht_p_plus : ¬ (p : ℕ) ∣ (t + 1) := fun h ↦ by
    have h_pn : p ∣ p * n := ⟨n, rfl⟩
    have h_eq_t1 : t + 1 = p * n + 2 := by simp [ht_def]
    rw [h_eq_t1] at h
    have hp2 : p ∣ 2 := by simpa using Nat.dvd_sub h h_pn
    exact absurd (Nat.le_of_dvd (by omega) hp2) (by omega)
  obtain ⟨z', hz'⟩ := bernoulli_div_sModEq_of_modEq hp_odd
    ht_pos hn1_pos ht_even hn1_even h_pSubOne_not_dvd_nPlus h_mn_modEq
    ht_coprime hn_p_plus ht_p_plus hn_p_plus_two h_below_t h_below_n1
  -- `B_{n+1} ∈ ℤ_[p]` directly (without Adams) since `n + 1 < p - 1`.
  obtain ⟨bn1, hbn1⟩ := bernoulli_mem_padicInt_of_lt_sub_one hp_odd (n + 1) hn_small
  -- `n + 1` is a `p`-unit since `n + 1 < p`.
  have hn1_unit : IsUnit ((n + 1 : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hn1_pos (by omega))
  set n1Inv : ℤ_[p] := (hn1_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hn1Inv_mul : ((n + 1 : ℕ) : ℤ_[p]) * n1Inv = 1 := by
    change ((hn1_unit.unit * hn1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
  have hn1Inv_mul_Qp : ((n + 1 : ℕ) : ℚ_[p]) * ((n1Inv : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p])) hn1Inv_mul
  -- `b := bn1 · n1Inv`, so `B_{n+1}/(n+1) = b` in ℚ_[p].
  set b : ℤ_[p] := bn1 * n1Inv with hb_def
  have hb : (((bernoulli (n + 1) : ℚ) / (n + 1 : ℕ) : ℚ) : ℚ_[p]) = ((b : ℤ_[p]) : ℚ_[p]) := by
    have h_div : (((bernoulli (n + 1) : ℚ) / (n + 1 : ℕ) : ℚ) : ℚ_[p]) =
        ((bernoulli (n + 1) : ℚ) : ℚ_[p]) / ((n + 1 : ℕ) : ℚ_[p]) := by push_cast; rfl
    rw [h_div, hbn1, div_eq_mul_inv,
      inv_eq_of_mul_eq_one_right hn1Inv_mul_Qp]
    simp only [hb_def, PadicInt.coe_mul]
  -- Candidate witness: n · b + t · z'.
  refine ⟨(n : ℤ_[p]) * b + (t : ℤ_[p]) * z', ?_⟩
  have htQ_ne : (t : ℚ_[p]) ≠ 0 := by exact_mod_cast ht_pos.ne'
  -- Rewrite hz' using hb to get B_t/t - b = p · z'.
  rw [hb] at hz'
  -- Derive B_t/t = b + p · z' in ℚ_[p].
  have h_BtOverT : (((bernoulli t : ℚ) / t : ℚ) : ℚ_[p]) =
      (b : ℚ_[p]) + (p : ℚ_[p]) * (z' : ℚ_[p]) := by
    linear_combination hz'
  -- B_t = t · (B_t/t).
  have h_Bt : ((bernoulli t : ℚ) : ℚ_[p]) = (t : ℚ_[p]) *
      (((bernoulli t : ℚ) / t : ℚ) : ℚ_[p]) := by
    push_cast; field_simp
  -- Combine:
  rw [h_Bt, h_BtOverT]
  have hb' : (((bernoulli (n + 1) : ℚ) / (↑n + 1) : ℚ) : ℚ_[p]) = (b : ℚ_[p]) := by
    rw [show ((((bernoulli (n + 1) : ℚ) / (↑n + 1) : ℚ)) : ℚ_[p]) =
        (((bernoulli (n + 1) : ℚ) / ↑(n + 1) : ℚ) : ℚ_[p]) from by push_cast; ring_nf, hb]
  rw [hb']
  have ht_sub : (t : ℚ_[p]) = (p : ℚ_[p]) * (n : ℚ_[p]) + 1 := by
    simp only [ht_def]; push_cast; ring
  push_cast; rw [ht_sub]; ring

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
  -- Auxiliary bounds: `t + 1 = p·n + 2 < p² < p³` (using `n + 1 < p - 1`), so
  -- `j + 1` is never divisible by `p³` for `j ≤ t` (resp. `j ≤ n + 1`).
  have h_t_lt_p_sq : t + 1 < p ^ 2 := by
    obtain ⟨r, hr⟩ : ∃ r, p = r + 3 := ⟨p - 3, by omega⟩
    rw [(by simp [ht_def] : t + 1 = p * n + 2), hr, pow_two]
    nlinarith [(by omega : n ≤ r), Nat.zero_le r]
  have h_p_sq_lt_p_cube : p ^ 2 < p ^ 3 := by
    have h_p2_pos : 0 < p ^ 2 := by positivity
    simpa [pow_succ] using (Nat.mul_lt_mul_left h_p2_pos).mpr hp.one_lt
  have h_below_t : ∀ j, j ≤ t → ¬ (p : ℕ) ^ 3 ∣ (j + 1) := fun j hj hdvd ↦
    absurd (Nat.le_of_dvd (Nat.succ_pos j) hdvd) (by omega)
  have h_p_lt_p_sq : p < p ^ 2 := by nlinarith [hp.one_lt]
  have h_below_n1 : ∀ j, j ≤ n + 1 → ¬ (p : ℕ) ^ 3 ∣ (j + 1) := fun j hj hdvd ↦
    absurd (Nat.le_of_dvd (Nat.succ_pos j) hdvd) (by omega)
  -- The three ingredients, each an independent `mod p^k` congruence.
  obtain ⟨z₁, hz₁⟩ := bernoulliGen_mul_p_sub_sum_pow_mem hp_odd hn_odd hn_pos
  obtain ⟨z₂, hz₂⟩ := sum_pow_t_sub_p_mul_bernoulli_mem hp_odd hn_odd hn_pos h_below_t
  obtain ⟨z₃, hz₃⟩ := bernoulli_t_sub_div_mem hp_odd hn_odd
    h_pSubOne_not_dvd_nPlus hn_p_plus hn_p_plus_two hn_small h_below_t h_below_n1
  /- **Combine**: from `hz₁` and `hz₂`, `p · (B_{1,ω^n} - B_t) ∈ p² · ℤ_[p]`,
     so dividing by `p`, `B_{1,ω^n} - B_t ∈ p · ℤ_[p]`. Adding `hz₃` gives
     `B_{1,ω^n} - B_{n+1}/(n+1) ∈ p · ℤ_[p]`. -/
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
    _ = (p : ℚ_[p]) * ((z₁ : ℚ_[p]) + (z₂ : ℚ_[p])) + (p : ℚ_[p]) * (z₃ : ℚ_[p]) := by
          rw [h_bridge, hz₃]
    _ = (p : ℚ_[p]) * ((z₁ + z₂ + z₃ : ℤ_[p]) : ℚ_[p]) := by push_cast; ring

/-! ### T013 — Boundary case `χ = ω^{p-2}`

At the boundary `n = p - 2`, the naive bridge
`B_{1, ω^n} ≡ B_{n+1} / (n+1) (mod p)` from T012 would require the
RHS `B_{p-1} / (p-1)` to be `p`-integral, but `B_{p-1}` has `p` in its
denominator by Von Staudt–Clausen (T010). Combining T008 and T010
directly, both `B_{1, ω^{p-2}}` and `bernoulli (p-1)` differ from
`-1/p` by a `p`-adic integer, so their **difference** is a `p`-adic
integer. -/

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
  obtain ⟨z₁, hz₁⟩ := bernoulliGen_teichmuller_inverse_eq_p_sub_one_div_p_add_padicInt hp_odd
  obtain ⟨z₂, hz₂⟩ := bernoulli_pSubOne_add_inv_p_mem_padicInt hp_odd
  -- From T008: `B_{1, ω^{p-2}} = (p-1)/p + z₁`.
  -- From T010: `bernoulli (p-1) + 1/p = z₂`.
  -- Subtracting: `B_{1, ω^{p-2}} - bernoulli (p-1) = (p-1)/p + 1/p + z₁ - z₂ = 1 + z₁ - z₂`.
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  refine ⟨1 + z₁ - z₂, ?_⟩
  rw [hz₁, eq_sub_of_add_eq hz₂]
  push_cast; field_simp; ring

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
  obtain ⟨z₀, hz₀⟩ := bernoulliGen_teichmuller_inverse_eq_p_sub_one_div_p_add_padicInt hp_odd
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have htwo_ne : (2 : ℚ_[p]) ≠ 0 := by norm_num
  refine ⟨-1 - z₀, ?_⟩
  rw [hz₀]
  push_cast; field_simp [hpQ_ne, htwo_ne]; ring


end BernoulliRegular
