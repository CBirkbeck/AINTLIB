import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

/-!
# Divisor-closed finite multipliers

For the Diekmann/Jensen argument we need an explicit even multiplier `C(S)`
such that every prime in a finite set `S` has `p - 1 ∣ C(S)`, and every prime
divisor of `C(S)` again has `q - 1 ∣ C(S)`.

The ticket board suggests an lcm over `q - 1`.  This file uses the stronger
factorial base `2 * M!`; it is larger but has the same formal role and gives
simpler closure proofs.
-/

open scoped Nat

namespace BernoulliRegular

/-- A finite bound used in the divisor-closed base. -/
def irregularBaseBound (S : Finset ℕ) : ℕ :=
  max 3 (S.sup id)

/-- The explicit even multiplier attached to a finite set of candidate primes. -/
def irregularBase (S : Finset ℕ) : ℕ :=
  2 * (irregularBaseBound S)!

theorem even_irregularBase (S : Finset ℕ) : Even (irregularBase S) := by
  unfold irregularBase
  exact even_two.mul_right _

theorem pos_irregularBase (S : Finset ℕ) : 0 < irregularBase S := by
  unfold irregularBase
  exact mul_pos (by norm_num) (Nat.factorial_pos _)

theorem sub_one_dvd_irregularBase_of_mem
    {S : Finset ℕ} {p : ℕ}
    (hpS : p ∈ S) (hp : p.Prime) :
    p - 1 ∣ irregularBase S := by
  have hp_le_sup : p ≤ S.sup id := Finset.le_sup (f := id) hpS
  have hp_le_bound : p ≤ irregularBaseBound S :=
    hp_le_sup.trans (le_max_right 3 (S.sup id))
  have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hle : p - 1 ≤ irregularBaseBound S :=
    (Nat.sub_le p 1).trans hp_le_bound
  have hdvd_fact : p - 1 ∣ (irregularBaseBound S)! :=
    Nat.dvd_factorial hpos hle
  simpa [irregularBase] using dvd_mul_of_dvd_right hdvd_fact 2

theorem sub_one_dvd_irregularBase_of_prime_dvd_irregularBase
    {S : Finset ℕ} {q : ℕ}
    (hq : q.Prime) (hqdvd : q ∣ irregularBase S) :
    q - 1 ∣ irregularBase S := by
  unfold irregularBase at hqdvd ⊢
  rcases hq.dvd_mul.mp hqdvd with hq_two | hq_fact
  · have hq_eq_two : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq_two
    simp [hq_eq_two]
  · have hq_le_bound : q ≤ irregularBaseBound S :=
      hq.dvd_factorial.mp hq_fact
    have hpos : 0 < q - 1 := Nat.sub_pos_of_lt hq.one_lt
    have hle : q - 1 ≤ irregularBaseBound S :=
      (Nat.sub_le q 1).trans hq_le_bound
    have hdvd_fact : q - 1 ∣ (irregularBaseBound S)! :=
      Nat.dvd_factorial hpos hle
    exact dvd_mul_of_dvd_right hdvd_fact 2

theorem sub_one_dvd_m_of_prime_dvd_m
    {S : Finset ℕ} {q t : ℕ}
    (hq : q.Prime) (hqdvd : q ∣ irregularBase S * 2 ^ t) :
    q - 1 ∣ irregularBase S * 2 ^ t := by
  rcases hq.dvd_mul.mp hqdvd with hq_base | hq_pow
  · exact dvd_mul_of_dvd_left
      (sub_one_dvd_irregularBase_of_prime_dvd_irregularBase hq hq_base) _
  · have hq_two_dvd : q ∣ 2 := hq.dvd_of_dvd_pow hq_pow
    have hq_eq_two : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq_two_dvd
    simp [hq_eq_two]

end BernoulliRegular
