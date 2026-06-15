import BernoulliRegular.IrregularPrimes.Basic
import BernoulliRegular.IrregularPrimes.BernoulliGrowth
import BernoulliRegular.IrregularPrimes.DivisorClosedBase
import BernoulliRegular.IrregularPrimes.KummerCongruenceFull
import BernoulliRegular.IrregularPrimes.RatNumerator
import BernoulliRegular.IrregularPrimes.VonStaudtConsequences
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Infinitude assembly infrastructure

This file contains the Carlitz infinitude assembly from the full Kummer
congruence for divided Bernoulli numbers.
-/

namespace BernoulliRegular

/-- The least nonnegative residue modulo `p - 1`.  In the final argument this
is positive because `(p - 1) ∤ m`. -/
def positiveResidueModSubOne (p m : ℕ) : ℕ :=
  m % (p - 1)

theorem positiveResidue_properties
    {p m : ℕ} (hp : p.Prime) (hp_odd : p ≠ 2)
    (hm_even : Even m) (hnot : ¬ (p - 1) ∣ m) :
    let m' := positiveResidueModSubOne p m
    0 < m' ∧ m' < p - 1 ∧ Even m' ∧ m ≡ m' [MOD p - 1] := by
  dsimp [positiveResidueModSubOne]
  have hpodd : Odd p := hp.odd_of_ne_two hp_odd
  have hp3 : 3 ≤ p := hp.odd_iff.mp hpodd
  have hp_sub_pos : 0 < p - 1 := by omega
  have hp_sub_even : Even (p - 1) := by
    rcases hpodd with ⟨k, hk⟩
    rw [hk]
    exact ⟨k, by omega⟩
  have hne_zero : m % (p - 1) ≠ 0 := fun hzero =>
    hnot (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  refine ⟨Nat.pos_of_ne_zero hne_zero, Nat.mod_lt _ hp_sub_pos,
    Even.mod_even hm_even hp_sub_even, ?_⟩
  exact (Nat.mod_modEq m (p - 1)).symm

theorem positiveResidue_in_irregular_range
    {p m' : ℕ} (hp : p.Prime) (hp_odd : p ≠ 2)
    (hm'_pos : 0 < m') (hm'_lt : m' < p - 1) (hm'_even : Even m') :
    1 ≤ m' / 2 ∧ 2 * (m' / 2) ≤ p - 3 := by
  have hpodd : Odd p := hp.odd_of_ne_two hp_odd
  have hp3 : 3 ≤ p := hp.odd_iff.mp hpodd
  constructor
  · by_contra hle
    have hm_eq : 2 * (m' / 2) = m' := Nat.two_mul_div_two_of_even hm'_even
    omega
  · have hm_eq : 2 * (m' / 2) = m' := Nat.two_mul_div_two_of_even hm'_even
    have hm_le : m' ≤ p - 3 := by
      rcases hm'_even with ⟨a, ha⟩
      rcases hpodd with ⟨b, hb⟩
      omega
    omega

/-- A numerator prime for the constructed Bernoulli quotient cannot divide the
constructed index. -/
theorem numerator_prime_not_dvd_constructed_m
    {S : Finset ℕ} {t p : ℕ} (hp : p.Prime)
    (hnum : (p : ℤ) ∣ (((bernoulli (irregularBase S * 2 ^ t) : ℚ) /
      ((irregularBase S * 2 ^ t : ℕ) : ℚ) : ℚ).num)) :
    ¬ p ∣ irregularBase S * 2 ^ t := by
  intro hpm
  have hm_pos : 0 < irregularBase S * 2 ^ t :=
    mul_pos (pos_irregularBase S) (pow_pos (by norm_num) t)
  have hm_even : Even (irregularBase S * 2 ^ t) :=
    (even_irregularBase S).mul_right _
  have hsub : p - 1 ∣ irregularBase S * 2 ^ t :=
    sub_one_dvd_m_of_prime_dvd_m hp hpm
  exact not_dvd_num_bernoulli_div_self_of_sub_one_dvd hp hm_pos hm_even hsub hnum

/-- A numerator prime for the constructed Bernoulli quotient is outside the
finite set used to construct the index. -/
theorem numerator_prime_not_mem_constructed_base
    {S : Finset ℕ} {t p : ℕ} (hp : p.Prime)
    (hnum : (p : ℤ) ∣ (((bernoulli (irregularBase S * 2 ^ t) : ℚ) /
      ((irregularBase S * 2 ^ t : ℕ) : ℚ) : ℚ).num)) :
    p ∉ S := by
  intro hpS
  have hm_pos : 0 < irregularBase S * 2 ^ t :=
    mul_pos (pos_irregularBase S) (pow_pos (by norm_num) t)
  have hm_even : Even (irregularBase S * 2 ^ t) :=
    (even_irregularBase S).mul_right _
  have hsub_base : p - 1 ∣ irregularBase S :=
    sub_one_dvd_irregularBase_of_mem hpS hp
  have hsub_m : p - 1 ∣ irregularBase S * 2 ^ t :=
    dvd_mul_of_dvd_left hsub_base _
  exact not_dvd_num_bernoulli_div_self_of_sub_one_dvd hp hm_pos hm_even hsub_m hnum

/-- Transport numerator divisibility across an already-proved Kummer
congruence between `B_m / m` and `B_m' / m'`. -/
theorem dvd_bernoulli_num_of_padic_congruent_residue
    {p m m' : ℕ} [Fact p.Prime] (hm'_pos : 0 < m')
    (hcong : ∃ z : ℤ_[p],
      (((bernoulli m : ℚ) / (m : ℕ) : ℚ) : ℚ_[p]) -
        (((bernoulli m' : ℚ) / (m' : ℕ) : ℚ) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p]))
    (hdiv : (p : ℤ) ∣ (((bernoulli m : ℚ) / (m : ℕ) : ℚ).num)) :
    (p : ℤ) ∣ (bernoulli m').num := by
  have hdiv_quot :
      (p : ℤ) ∣ (((bernoulli m' : ℚ) / (m' : ℕ) : ℚ).num) :=
    prime_dvd_num_of_padic_sub_eq_p_mul (p := p) (q := ((bernoulli m : ℚ) / (m : ℕ) : ℚ))
      (r := ((bernoulli m' : ℚ) / (m' : ℕ) : ℚ)) hdiv hcong
  exact dvd_num_of_dvd_div_nat_num (q := bernoulli m') hm'_pos hdiv_quot

/-- If `p` divides `B_m.num` and `m` is a p-adic unit, then `p` also divides
the reduced numerator of `B_m / m`. -/
theorem dvd_bernoulli_div_self_num_of_dvd_bernoulli_num
    {p m : ℕ} (hp : p.Prime) (_hm_pos : 0 < m)
    (hpm : ¬ p ∣ m)
    (hdiv : (p : ℤ) ∣ (bernoulli m).num) :
    (p : ℤ) ∣ (((bernoulli m : ℚ) / (m : ℕ) : ℚ).num) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, hb⟩ := padic_eq_p_mul_of_prime_dvd_num (p := p)
    (q := bernoulli m) hdiv
  have hm_unit : IsUnit ((m : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr hpm
  set mInv : ℤ_[p] := (hm_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hmInv_mul : ((m : ℕ) : ℤ_[p]) * mInv = 1 := by
    change ((hm_unit.unit * hm_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1
    simp
  have hmInv_mul_Qp :
      ((m : ℕ) : ℚ_[p]) * ((mInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hmInv_mul
  apply prime_dvd_num_of_padic_eq_p_mul (p := p)
    (q := ((bernoulli m : ℚ) / (m : ℕ) : ℚ))
  refine ⟨b * mInv, ?_⟩
  have hdiv_eq :
      (((bernoulli m : ℚ) / (m : ℕ) : ℚ) : ℚ_[p]) =
        ((bernoulli m : ℚ) : ℚ_[p]) / ((m : ℕ) : ℚ_[p]) := by
    push_cast
    rfl
  rw [hdiv_eq, hb, div_eq_mul_inv, inv_eq_of_mul_eq_one_right hmInv_mul_Qp]
  push_cast
  ring

/-- Carlitz divisor criterion from the full Kummer congruence. -/
theorem not_isRegularPrime_iff_exists_dvd_bernoulli_div_self_num
    {q : ℕ} (hq : q.Prime) (hq_odd : q ≠ 2) :
    (letI : Fact q.Prime := ⟨hq⟩; ¬ IsRegularPrime q) ↔
      ∃ m : ℕ, 0 < m ∧ Even m ∧
        (q : ℤ) ∣ (((bernoulli m : ℚ) / (m : ℕ) : ℚ).num) := by
  letI : Fact q.Prime := ⟨hq⟩
  constructor
  · intro hirr
    obtain ⟨k, hk_pos, hk_range, hdiv⟩ :=
      exists_bernoulli_num_dvd_of_not_isRegularPrime hq hq_odd hirr
    let m : ℕ := 2 * k
    have hm_pos : 0 < m := by
      dsimp [m]
      omega
    have hm_even : Even m := by
      dsimp [m]
      exact ⟨k, by omega⟩
    have hm_le : m ≤ q - 3 := by
      dsimp [m]
      exact hk_range
    have hq_not_dvd_m : ¬ q ∣ m := by
      intro hqm
      have hq_le_m : q ≤ m := Nat.le_of_dvd hm_pos hqm
      omega
    refine ⟨m, hm_pos, hm_even, ?_⟩
    exact dvd_bernoulli_div_self_num_of_dvd_bernoulli_num hq hm_pos
      hq_not_dvd_m (by dsimp [m]; exact hdiv)
  · rintro ⟨m, hm_pos, hm_even, hdiv⟩
    have hsub_not : ¬ (q - 1) ∣ m :=
      sub_one_not_dvd_of_dvd_num_bernoulli_div_self hq hm_pos hm_even hdiv
    let m' : ℕ := positiveResidueModSubOne q m
    obtain ⟨hm'_pos, hm'_lt, hm'_even, hmod⟩ :=
      positiveResidue_properties hq hq_odd hm_even hsub_not
    have hnot_m' : ¬ (q - 1) ∣ m' := by
      intro hdiv_m'
      have hle : q - 1 ≤ m' := Nat.le_of_dvd hm'_pos hdiv_m'
      omega
    have hcong :=
      bernoulli_div_sModEq_of_modEq_full (p := q) hq_odd hm_pos hm'_pos
        hm_even hm'_even hnot_m' hmod
    have hnum' : (q : ℤ) ∣ (bernoulli m').num :=
      dvd_bernoulli_num_of_padic_congruent_residue (p := q) (m := m) (m' := m')
        hm'_pos hcong hdiv
    have hrange := positiveResidue_in_irregular_range hq hq_odd hm'_pos hm'_lt hm'_even
    obtain ⟨hk_pos, hk_range⟩ := hrange
    have hm'_eq : 2 * (m' / 2) = m' := Nat.two_mul_div_two_of_even hm'_even
    have hnum_k : (q : ℤ) ∣ (bernoulli (2 * (m' / 2))).num := by
      rw [hm'_eq]
      exact hnum'
    exact not_isRegularPrime_of_bernoulli_num_dvd hq hq_odd
      ⟨m' / 2, hk_pos, hk_range, hnum_k⟩

/-- The growth and von Staudt steps produce a numerator prime for the constructed
index, already outside the finite candidate set. -/
theorem exists_numerator_prime_for_constructed_m (S : Finset ℕ) :
    ∃ t p : ℕ,
      p.Prime ∧
      (p : ℤ) ∣ (((bernoulli (irregularBase S * 2 ^ t) : ℚ) /
        ((irregularBase S * 2 ^ t : ℕ) : ℚ) : ℚ).num) ∧
      p ∉ S ∧ ¬ p ∣ irregularBase S * 2 ^ t ∧
      ¬ (p - 1) ∣ irregularBase S * 2 ^ t ∧
      p ≠ 2 := by
  obtain ⟨t, ht⟩ := exists_large_even_multiple_abs_bernoulli_div_self_gt_one
    (pos_irregularBase S) (even_irregularBase S)
  have ht' : 1 < |(((bernoulli (irregularBase S * 2 ^ t) : ℚ) /
        ((irregularBase S * 2 ^ t : ℕ) : ℚ) : ℚ) : ℝ)| := by
    simpa using ht
  obtain ⟨p, hp, hnum⟩ := exists_prime_dvd_num_of_one_lt_abs ht'
  have hp_not_mem : p ∉ S :=
    numerator_prime_not_mem_constructed_base (S := S) (t := t) hp hnum
  have hp_not_dvd_m : ¬ p ∣ irregularBase S * 2 ^ t :=
    numerator_prime_not_dvd_constructed_m (S := S) (t := t) hp hnum
  have hm_pos : 0 < irregularBase S * 2 ^ t :=
    mul_pos (pos_irregularBase S) (pow_pos (by norm_num) t)
  have hm_even : Even (irregularBase S * 2 ^ t) :=
    (even_irregularBase S).mul_right _
  have hsub_not : ¬ (p - 1) ∣ irregularBase S * 2 ^ t :=
    sub_one_not_dvd_of_dvd_num_bernoulli_div_self hp hm_pos hm_even hnum
  have hp_odd : p ≠ 2 := fun hp2 =>
    hsub_not (by simp [hp2])
  exact ⟨t, p, hp, hnum, hp_not_mem, hp_not_dvd_m, hsub_not, hp_odd⟩

/-- Carlitz-facing wrapper around the constructed large multiple.  It packages
the index as a single even positive `M` divisible by `q - 1` for every prime
`q` in the finite input set. -/
theorem exists_numerator_prime_for_carlitz_base (S : Finset ℕ) :
    ∃ M p : ℕ,
      p.Prime ∧ p ≠ 2 ∧ Even M ∧ 0 < M ∧
      (∀ q, q ∈ S → q.Prime → q - 1 ∣ M) ∧
      (p : ℤ) ∣ (((bernoulli M : ℚ) / (M : ℕ) : ℚ).num) ∧
      p ∉ S := by
  obtain ⟨t, p, hp, hnum, hp_not_mem, _hp_not_dvd_m, _hsub_not, hp_odd⟩ :=
    exists_numerator_prime_for_constructed_m S
  let M : ℕ := irregularBase S * 2 ^ t
  have hM_even : Even M := by
    dsimp [M]
    exact (even_irregularBase S).mul_right _
  have hM_pos : 0 < M := by
    dsimp [M]
    exact mul_pos (pos_irregularBase S) (pow_pos (by norm_num) t)
  have hdiv_base : ∀ q, q ∈ S → q.Prime → q - 1 ∣ M := by
    intro q hqS hq
    dsimp [M]
    exact dvd_mul_of_dvd_left (sub_one_dvd_irregularBase_of_mem hqS hq) _
  exact ⟨M, p, hp, hp_odd, hM_even, hM_pos, hdiv_base, by dsimp [M]; exact hnum,
    hp_not_mem⟩

/-- Carlitz finite-set contradiction. -/
theorem exists_not_isRegularPrime_not_mem_carlitz
    (S : Finset ℕ) :
    ∃ p : ℕ, ∃ hp : p.Prime,
      (letI : Fact p.Prime := ⟨hp⟩; ¬ IsRegularPrime p) ∧ p ∉ S := by
  obtain ⟨M, p, hp, hp_odd, hM_even, hM_pos, _hSdiv, hnum, hp_not_mem⟩ :=
    exists_numerator_prime_for_carlitz_base S
  letI : Fact p.Prime := ⟨hp⟩
  have hcrit :=
    (not_isRegularPrime_iff_exists_dvd_bernoulli_div_self_num hp hp_odd).mpr
      ⟨M, hM_pos, hM_even, hnum⟩
  exact ⟨p, hp, hcrit, hp_not_mem⟩

/-- Infinitely many primes are not regular, by the Carlitz route. -/
theorem infinite_not_isRegularPrime :
    Set.Infinite
      {p : ℕ | ∃ hp : p.Prime,
        letI : Fact p.Prime := ⟨hp⟩
        ¬ IsRegularPrime p} := by
  refine infinite_of_forall_finite_set_not_cover ?_
  intro S hcover
  obtain ⟨p, hp, hirr, hp_not_mem⟩ := exists_not_isRegularPrime_not_mem_carlitz S
  exact hp_not_mem (hcover p ⟨hp, hirr⟩)

end BernoulliRegular
