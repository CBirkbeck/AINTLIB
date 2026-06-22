import BernoulliRegular.IrregularPrimes.RatNumerator
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.NumberTheory.Bernoulli
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

/-!
# Consequences of von Staudt-Clausen

This file extracts the local numerator-exclusion statements needed in the
Diekmann/Jensen infinitude argument from mathlib's public
`Bernoulli.vonStaudt_clausen` theorem.
-/

namespace BernoulliRegular

/-- The finite correction-prime set appearing in von Staudt-Clausen for `B_n`. -/
def vonStaudtPrimesFor (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 2)).filter fun q ↦ q.Prime ∧ (q - 1) ∣ n

/-- Public even-index wrapper around mathlib's von Staudt-Clausen theorem. -/
theorem bernoulli_add_vonStaudtCorrection_mem_int {n : ℕ} (hn_even : Even n) :
    bernoulli n + ∑ q ∈ vonStaudtPrimesFor n, (1 : ℚ) / q ∈ Set.range Int.cast := by
  obtain ⟨k, hk⟩ := hn_even
  rw [hk]
  simpa [vonStaudtPrimesFor, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using Bernoulli.vonStaudt_clausen k

/-- The correction sum with the `p`-term removed has denominator prime to `p`. -/
theorem vonStaudtCorrection_rest_den_not_dvd {p n : ℕ} (hp : p.Prime) :
    ¬ p ∣ (∑ q ∈ (vonStaudtPrimesFor n).filter (fun q ↦ q ≠ p), (1 : ℚ) / q).den := by
  let F := (vonStaudtPrimesFor n).filter (fun q ↦ q ≠ p)
  have hprod_coprime : (∏ q ∈ F, ((1 : ℚ) / q).den).Coprime p := by
    refine Nat.Coprime.prod_left fun q hq ↦ ?_
    simp only [F, vonStaudtPrimesFor, Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨⟨_, hq_prime, _⟩, hne⟩ := hq
    rw [show ((1 : ℚ) / q).den = q by simp [hq_prime.ne_zero]]
    exact (Nat.coprime_primes hq_prime hp).mpr hne
  have hden_dvd :
      (∑ q ∈ F, (1 : ℚ) / q).den ∣ ∏ q ∈ F, ((1 : ℚ) / q).den :=
    Finset.Rat.den_sum_dvd_prod_den F fun q ↦ (1 : ℚ) / q
  have hden_coprime : (∑ q ∈ F, (1 : ℚ) / q).den.Coprime p :=
    Nat.Coprime.of_dvd_left hden_dvd hprod_coprime
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hden_coprime.symm

/-- Split the von Staudt correction sum into the `p`-term and the rest. -/
theorem vonStaudtCorrection_split {p n : ℕ} (hp : p.Prime) (hn_pos : 0 < n)
    (hdiv : p - 1 ∣ n) :
    ∑ q ∈ vonStaudtPrimesFor n, (1 : ℚ) / q =
      (1 : ℚ) / p + ∑ q ∈ (vonStaudtPrimesFor n).filter (fun q ↦ q ≠ p),
        (1 : ℚ) / q := by
  have hp_mem : p ∈ vonStaudtPrimesFor n := by
    rw [vonStaudtPrimesFor, Finset.mem_filter]
    refine ⟨?_, hp, hdiv⟩
    rw [Finset.mem_range]
    have hle : p - 1 ≤ n := Nat.le_of_dvd hn_pos hdiv
    omega
  rw [Finset.filter_ne']
  exact (Finset.add_sum_erase (vonStaudtPrimesFor n) (fun q ↦ (1 : ℚ) / q) hp_mem).symm

/-- If `p - 1 ∣ n`, the denominator of `B_n + 1/p` is prime to `p`. -/
theorem not_dvd_den_bernoulli_add_inv_of_sub_one_dvd
    {p n : ℕ} (hp : p.Prime) (hn_pos : 0 < n) (hn_even : Even n)
    (hdiv : p - 1 ∣ n) :
    ¬ p ∣ (bernoulli n + (1 : ℚ) / p).den := by
  obtain ⟨z, hz⟩ := bernoulli_add_vonStaudtCorrection_mem_int hn_even
  let R : ℚ := ∑ q ∈ (vonStaudtPrimesFor n).filter (fun q ↦ q ≠ p), (1 : ℚ) / q
  have hRden : ¬ p ∣ R.den := by
    dsimp [R]
    exact vonStaudtCorrection_rest_den_not_dvd (p := p) (n := n) hp
  have hsplit := vonStaudtCorrection_split (p := p) (n := n) hp hn_pos hdiv
  have hz' : (z : ℚ) = bernoulli n + ((1 : ℚ) / p + R) := by
    dsimp [R]
    rw [← hsplit]
    exact hz
  have hmain : bernoulli n + (1 : ℚ) / p = (z : ℚ) - R := by
    rw [hz']
    ring
  rw [hmain]
  have hden_dvd : ((z : ℚ) - R).den ∣ R.den := by
    simp
  intro hpden
  exact hRden (hpden.trans hden_dvd)

/-- A normalized expression for adding `1/p` to a rational. -/
theorem rat_add_inv_prime_eq_divInt {p : ℕ} (hp : p.Prime) (q : ℚ) :
    q + (1 : ℚ) / p = Rat.divInt (q.num * (p : ℤ) + q.den) (q.den * (p : ℤ)) := by
  rw [Rat.add_num_den]
  simp [Rat.divInt_eq_div, hp.ne_zero, hp.pos]

/-- If `p` divides the reduced numerator of `q`, then `q + 1/p` has denominator
divisible by `p`. -/
theorem dvd_den_add_inv_of_dvd_num {p : ℕ} (hp : p.Prime) {q : ℚ}
    (hdiv : (p : ℤ) ∣ q.num) :
    p ∣ (q + (1 : ℚ) / p).den := by
  by_contra hnot
  let r : ℚ := q + (1 : ℚ) / p
  let N : ℤ := q.num * (p : ℤ) + q.den
  let D : ℤ := (q.den : ℤ) * (p : ℤ)
  have hD_ne : D ≠ 0 := by
    dsimp [D]
    exact mul_ne_zero (Int.natCast_ne_zero.mpr (Rat.den_nz q))
      (Int.natCast_ne_zero.mpr hp.ne_zero)
  have hr_eq : r = Rat.divInt N D := by
    dsimp [r, N, D]
    exact rat_add_inv_prime_eq_divInt hp q
  obtain ⟨c, hN, hD⟩ := Rat.num_den_mk hD_ne hr_eq
  have hpD : (p : ℤ) ∣ D := by
    dsimp [D]
    exact dvd_mul_left _ _
  have hp_mul : (p : ℤ) ∣ c * (r.den : ℤ) := by
    rwa [hD] at hpD
  have hnot_int : ¬ (p : ℤ) ∣ (r.den : ℤ) := fun h ↦
    hnot (Int.natCast_dvd_natCast.mp h)
  have hpc : (p : ℤ) ∣ c := by
    rcases Int.Prime.dvd_mul' hp hp_mul with hpc | hprd
    · exact hpc
    · exact (hnot_int hprd).elim
  have hpN : (p : ℤ) ∣ N := by
    rw [hN]
    exact dvd_mul_of_dvd_left hpc _
  have hp_qnum_mul : (p : ℤ) ∣ q.num * (p : ℤ) :=
    dvd_mul_of_dvd_right (dvd_refl (p : ℤ)) q.num
  have hpden_int : (p : ℤ) ∣ (q.den : ℤ) := by
    have hsub : (p : ℤ) ∣ N - q.num * (p : ℤ) := Int.dvd_sub hpN hp_qnum_mul
    have hsub_eq : N - q.num * (p : ℤ) = (q.den : ℤ) := by
      dsimp [N]
      ring
    rwa [hsub_eq] at hsub
  have hpnum_nat : p ∣ q.num.natAbs := Int.natCast_dvd.mp hdiv
  have hpden_nat : p ∣ q.den := Int.natCast_dvd_natCast.mp hpden_int
  exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpnum_nat hpden_nat q.reduced

/-- Contrapositive form of `dvd_den_add_inv_of_dvd_num`. -/
theorem not_dvd_num_of_add_inv_den_not_dvd
    {p : ℕ} (hp : p.Prime) {q : ℚ}
    (hden_add : ¬ p ∣ (q + (1 : ℚ) / p).den) :
    ¬ (p : ℤ) ∣ q.num := fun hdiv ↦
  hden_add (dvd_den_add_inv_of_dvd_num hp hdiv)

/-- If `p - 1 ∣ n`, then `p` cannot divide the reduced numerator of `B_n`. -/
theorem not_dvd_num_bernoulli_of_sub_one_dvd
    {p n : ℕ} (hp : p.Prime) (hn_pos : 0 < n) (hn_even : Even n)
    (hdiv : p - 1 ∣ n) :
    ¬ (p : ℤ) ∣ (bernoulli n).num :=
  not_dvd_num_of_add_inv_den_not_dvd hp
    (not_dvd_den_bernoulli_add_inv_of_sub_one_dvd hp hn_pos hn_even hdiv)

/-- Even-index Bernoulli numerators are odd. -/
theorem odd_bernoulli_num_of_even
    {n : ℕ} (hn_two : 2 ≤ n) (hn_even : Even n) :
    Odd (bernoulli n).num := by
  rw [← Int.not_even_iff_odd, even_iff_two_dvd]
  exact not_dvd_num_bernoulli_of_sub_one_dvd
    (p := 2) Nat.prime_two (by omega) hn_even (by simp)

/-- If `p - 1 ∣ n`, then `p` cannot divide the reduced numerator of `B_n / n`. -/
theorem not_dvd_num_bernoulli_div_self_of_sub_one_dvd
    {p n : ℕ} (hp : p.Prime) (hn_pos : 0 < n) (hn_even : Even n)
    (hdiv : p - 1 ∣ n) :
    ¬ (p : ℤ) ∣ (((bernoulli n : ℚ) / n : ℚ).num) := fun hnum ↦
  not_dvd_num_bernoulli_of_sub_one_dvd hp hn_pos hn_even hdiv
    (dvd_num_of_dvd_div_nat_num (q := bernoulli n) hn_pos hnum)

/-- A numerator prime for `B_n / n` cannot satisfy `p - 1 ∣ n`. -/
theorem sub_one_not_dvd_of_dvd_num_bernoulli_div_self
    {p n : ℕ} (hp : p.Prime) (hn_pos : 0 < n) (hn_even : Even n)
    (hnum : (p : ℤ) ∣ (((bernoulli n : ℚ) / n : ℚ).num)) :
    ¬ (p - 1) ∣ n := fun hdiv ↦
  not_dvd_num_bernoulli_div_self_of_sub_one_dvd hp hn_pos hn_even hdiv hnum

/-- Even-index divided Bernoulli numerators are odd. -/
theorem odd_bernoulli_div_self_num_of_even
    {n : ℕ} (hn_pos : 0 < n) (hn_even : Even n) :
    Odd (((bernoulli n : ℚ) / (n : ℕ) : ℚ).num) := by
  rw [← Int.not_even_iff_odd, even_iff_two_dvd]
  exact not_dvd_num_bernoulli_div_self_of_sub_one_dvd
    (p := 2) Nat.prime_two hn_pos hn_even (by simp)

/-- For a prime correction term `1/q`, multiplying by `p` gives a
`p`-adic integer. -/
theorem p_mul_inv_nat_prime_mem_padicInt
    {p q : ℕ} [Fact p.Prime] (hq : q.Prime) :
    ∃ z : ℤ_[p], (((p : ℚ) * ((1 : ℚ) / q) : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
  by_cases hpq : p = q
  · subst q
    refine ⟨1, ?_⟩
    simp [(Fact.out : Nat.Prime p).ne_zero]
  · let r : ℚ := (p : ℚ) * ((1 : ℚ) / q)
    have hr_eq : r = Rat.divInt (p : ℤ) (q : ℤ) := by
      dsimp [r]
      rw [show (p : ℚ) * ((1 : ℚ) / q) = (p : ℚ) / q by ring]
      rw [Rat.divInt_eq_div]
      norm_num
    have hden_dvd_int : (r.den : ℤ) ∣ (q : ℤ) := by
      rw [hr_eq]
      exact Rat.den_dvd (p : ℤ) (q : ℤ)
    have hden_dvd_nat : r.den ∣ q := Int.natCast_dvd_natCast.mp hden_dvd_int
    have hden : ¬ p ∣ r.den := by
      intro hpd
      have hpq_dvd : p ∣ q := hpd.trans hden_dvd_nat
      exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) hq).mp hpq_dvd)
    refine ⟨⟨(r : ℚ_[p]), Padic.norm_rat_le_one hden⟩, rfl⟩

/-- The von Staudt correction sum becomes `p`-integral after multiplication
by `p`. -/
theorem p_mul_vonStaudtCorrection_mem_padicInt
    {p n : ℕ} [Fact p.Prime] :
    ∃ z : ℤ_[p],
      ((p : ℚ_[p]) * (((∑ q ∈ vonStaudtPrimesFor n, (1 : ℚ) / q) : ℚ) : ℚ_[p])) =
        (z : ℚ_[p]) := by
  classical
  let s := vonStaudtPrimesFor n
  have hterm : ∀ q ∈ s,
      ∃ z : ℤ_[p], (((p : ℚ) * ((1 : ℚ) / q) : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
    intro q hq
    dsimp [s] at hq
    rw [vonStaudtPrimesFor, Finset.mem_filter] at hq
    exact p_mul_inv_nat_prime_mem_padicInt hq.2.1
  choose z hz using hterm
  refine ⟨∑ x ∈ s.attach, z x.1 x.2, ?_⟩
  rw [PadicInt.coe_sum]
  dsimp [s]
  push_cast
  rw [← Finset.sum_attach]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have := hz x.1 x.2
  push_cast at this ⊢
  exact this

/-- Direct von Staudt-Clausen consequence: for every even index, `p * B_n`
is a `p`-adic integer. -/
theorem p_mul_bernoulli_mem_padicInt_vonStaudt
    {p n : ℕ} [Fact p.Prime] (hn_even : Even n) :
    ∃ z : ℤ_[p], (p : ℚ_[p]) * ((bernoulli n : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
  obtain ⟨T, hT⟩ := bernoulli_add_vonStaudtCorrection_mem_int hn_even
  obtain ⟨C, hC⟩ := p_mul_vonStaudtCorrection_mem_padicInt (p := p) (n := n)
  refine ⟨(p : ℤ_[p]) * T - C, ?_⟩
  have hTQ : ((bernoulli n + ∑ q ∈ vonStaudtPrimesFor n, (1 : ℚ) / q : ℚ) :
      ℚ_[p]) = (T : ℚ_[p]) := by
    exact_mod_cast hT.symm
  have hmain : (p : ℚ_[p]) * ((bernoulli n : ℚ) : ℚ_[p]) =
      (p : ℚ_[p]) * (T : ℚ_[p]) -
        (p : ℚ_[p]) * (((∑ q ∈ vonStaudtPrimesFor n, (1 : ℚ) / q) : ℚ) :
          ℚ_[p]) := by
    rw [← hTQ]
    push_cast
    ring
  rw [hmain, hC]
  push_cast
  ring

/-- If the `p`-term is absent from the von Staudt correction sum, then that
correction sum has denominator prime to `p`. -/
theorem vonStaudtCorrection_den_not_dvd_of_not_sub_one_dvd
    {p n : ℕ} (hp : p.Prime) (hnot : ¬ p - 1 ∣ n) :
    ¬ p ∣ (∑ q ∈ vonStaudtPrimesFor n, (1 : ℚ) / q).den := by
  have hfilter :
      (vonStaudtPrimesFor n).filter (fun q ↦ q ≠ p) = vonStaudtPrimesFor n := by
    apply Finset.filter_true_of_mem
    intro q hq
    rw [vonStaudtPrimesFor, Finset.mem_filter] at hq
    intro hqp
    subst q
    exact hnot hq.2.2
  simpa [hfilter] using
    vonStaudtCorrection_rest_den_not_dvd (p := p) (n := n) hp

/-- Direct von Staudt-Clausen generic case: if `(p - 1) ∤ n`, then `B_n`
is a `p`-adic integer. -/
theorem bernoulli_mem_padicInt_vonStaudt_of_not_sub_one_dvd
    {p n : ℕ} [Fact p.Prime] (hn_even : Even n) (hnot : ¬ p - 1 ∣ n) :
    ∃ z : ℤ_[p], ((bernoulli n : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
  let C : ℚ := ∑ q ∈ vonStaudtPrimesFor n, (1 : ℚ) / q
  have hCden : ¬ p ∣ C.den := by
    dsimp [C]
    exact vonStaudtCorrection_den_not_dvd_of_not_sub_one_dvd
      (p := p) (n := n) (Fact.out : Nat.Prime p) hnot
  let Cint : ℤ_[p] := ⟨(C : ℚ_[p]), Padic.norm_rat_le_one hCden⟩
  obtain ⟨T, hT⟩ := bernoulli_add_vonStaudtCorrection_mem_int hn_even
  refine ⟨T - Cint, ?_⟩
  have hTQ : ((bernoulli n + C : ℚ) : ℚ_[p]) = (T : ℚ_[p]) := by
    exact_mod_cast hT.symm
  dsimp [Cint]
  change ((bernoulli n : ℚ) : ℚ_[p]) = (T : ℚ_[p]) - (C : ℚ_[p])
  rw [← hTQ]
  push_cast
  ring

end BernoulliRegular
