import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# LeanBridge issue #54: bad primes

The bad primes of level `N` are exactly the prime factors of `N`.
-/

namespace XYin.Experiments.Issue54

/-- The finite set of primes dividing the level. -/
def badPrimes (N : ℕ) : Finset ℕ :=
  N.primeFactors

@[simp]
lemma mem_badPrimes {N p : ℕ} : p ∈ badPrimes N ↔ p.Prime ∧ p ∣ N ∧ N ≠ 0 := by
  simp [badPrimes]

lemma prime_mem_badPrimes_iff_dvd {N p : ℕ} (hp : p.Prime) (hN : N ≠ 0) :
    p ∈ badPrimes N ↔ p ∣ N := by
  simp [badPrimes, hp, hN]

lemma badPrimes_finite (N : ℕ) : {p | p ∈ badPrimes N}.Finite :=
  (badPrimes N).finite_toSet

example : badPrimes 11 = {11} := by
  ext p
  simp only [mem_badPrimes, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hdvd, _⟩
    exact (Nat.dvd_prime (by norm_num : Nat.Prime 11)).mp hdvd |>.resolve_left hp.ne_one
  · intro h
    subst h
    norm_num

example : badPrimes 12 = ({2, 3} : Finset ℕ) := by
  ext p
  simp only [mem_badPrimes, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hdvd, _⟩
    have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < p := hp.pos
    interval_cases p <;> norm_num [Nat.Prime] at *
  · rintro (rfl | rfl) <;> norm_num

end XYin.Experiments.Issue54
