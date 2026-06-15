import BernoulliRegular.BernoulliFast.Tactic
import BernoulliRegular.Main
import Mathlib.Data.Set.Finite.Basic

/-!
# Basic infrastructure for non-regular primes

This file contains the elementary bridge from Bernoulli numerator witnesses to
the existing `IsRegularPrime` predicate, plus finite-set scaffolding for the
infinitude argument.
-/

namespace BernoulliRegular

/-- A Bernoulli numerator witness in Kummer's range proves that `p` is not
regular. -/
theorem not_isRegularPrime_of_bernoulli_num_dvd
    {p : ℕ} (hp : p.Prime) (hp_odd : p ≠ 2)
    (h : ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧
      (p : ℤ) ∣ (bernoulli (2 * k)).num) :
    letI : Fact p.Prime := ⟨hp⟩
    ¬ IsRegularPrime p := by
  letI : Fact p.Prime := ⟨hp⟩
  intro hreg
  rcases h with ⟨k, hk_pos, hk_range, hdiv⟩
  exact ((KummerCriterion (p := p) hp_odd).mp hreg k hk_pos hk_range) hdiv

/-- Conversely, non-regularity gives a Bernoulli numerator witness in Kummer's
range. -/
theorem exists_bernoulli_num_dvd_of_not_isRegularPrime
    {p : ℕ} (hp : p.Prime) (hp_odd : p ≠ 2)
    (hirr : letI : Fact p.Prime := ⟨hp⟩; ¬ IsRegularPrime p) :
    ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧
      (p : ℤ) ∣ (bernoulli (2 * k)).num := by
  letI : Fact p.Prime := ⟨hp⟩
  by_contra h
  exact hirr <| (KummerCriterion (p := p) hp_odd).mpr <| by
    intro k hk_pos hk_range hdiv
    exact h ⟨k, hk_pos, hk_range, hdiv⟩

/-- A concrete sanity check: the Bernoulli witness `37 ∣ B_32` implies that
`37` is not regular. -/
theorem not_isRegularPrime_thirtyseven_via_bernoulli :
    letI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
    ¬ IsRegularPrime 37 :=
  not_isRegularPrime_of_bernoulli_num_dvd
    (p := 37) (by norm_num) (by norm_num)
    ⟨16, by norm_num, by norm_num, by
      bernoulli_decide
      exact ⟨-208360028141, by norm_num⟩⟩

/-- To prove a predicate infinite, it is enough to show that no finite set
covers it. -/
theorem infinite_of_forall_finite_set_not_cover
    {P : ℕ → Prop}
    (h : ∀ S : Finset ℕ, (∀ p, P p → p ∈ S) → False) :
    Set.Infinite {p : ℕ | P p} := by
  intro hfinite
  exact h hfinite.toFinset fun p hp => hfinite.mem_toFinset.mpr hp

/-- Finite non-regular primes can be represented by a finite covering set of
natural numbers. -/
theorem finite_not_isRegularPrime_set_iff_bounded_by_finset :
    Set.Finite
      {p : ℕ | ∃ hp : p.Prime,
        letI : Fact p.Prime := ⟨hp⟩
        ¬ IsRegularPrime p} ↔
      ∃ S : Finset ℕ,
        ∀ p : ℕ, (∃ hp : p.Prime,
          letI : Fact p.Prime := ⟨hp⟩
          ¬ IsRegularPrime p) → p ∈ S := by
  constructor
  · intro hfinite
    exact ⟨hfinite.toFinset, fun p hp => hfinite.mem_toFinset.mpr hp⟩
  · rintro ⟨S, hS⟩
    exact S.finite_toSet.subset fun p hp => hS p hp

end BernoulliRegular
