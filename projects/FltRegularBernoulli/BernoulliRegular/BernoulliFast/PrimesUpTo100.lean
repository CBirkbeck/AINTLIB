import BernoulliRegular.BernoulliFast.ValuesUpTo100
import BernoulliRegular.Main

/-!
# Regularity of primes below 100

This file records the regularity status of each prime below `100`.

Regular primes below `100`:
`2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 43, 47, 53, 61, 71, 73, 79,
83, 89, 97`.

Irregular primes below `100`:
`37, 59, 67`.

The computational Bernoulli steps are discharged by `norm_num` using the
`@[simp]` values from `BernoulliRegular.BernoulliFast.ValuesUpTo100`.
-/

namespace BernoulliRegular

private theorem regular_of_bernoulli_values
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hB : ∀ k, 1 ≤ k → 2 * k ≤ p - 3 →
      ¬ (p : ℤ) ∣ (bernoulli (2 * k)).num) :
    IsRegularPrime p :=
  (kummer_criterion (p := p) hp_odd).mpr hB

private theorem not_regular_of_dvd_bernoulli_value
    {p k : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hk : 1 ≤ k) (hk_range : 2 * k ≤ p - 3)
    (hdiv : (p : ℤ) ∣ (bernoulli (2 * k)).num) :
    ¬ IsRegularPrime p := fun hreg ↦
  ((kummer_criterion (p := p) hp_odd).mp hreg k hk hk_range) hdiv

macro "regular_prime_by_values" p:num upper:num : tactic => `(tactic|
  (haveI : Fact (Nat.Prime $p) := ⟨by norm_num⟩
   exact regular_of_bernoulli_values (p := $p) (by norm_num) (by
     intro k hk hk_range
     have hk_upper : k ≤ $upper := by omega
     interval_cases k <;> norm_num)))

macro "irregular_prime_by_value" p:num k:num : tactic => `(tactic|
  (haveI : Fact (Nat.Prime $p) := ⟨by norm_num⟩
   exact not_regular_of_dvd_bernoulli_value (p := $p) (k := $k)
     (by norm_num) (by norm_num) (by norm_num) (by norm_num)))

theorem isRegularPrime_two_lt100 : IsRegularPrime 2 :=
  isRegularPrime_two

theorem isRegularPrime_three_lt100 :
    letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    IsRegularPrime 3 :=
  isRegularPrime_three

theorem isRegularPrime_five_lt100 :
    letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    IsRegularPrime 5 := by
  regular_prime_by_values 5 1

theorem isRegularPrime_seven_lt100 :
    letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    IsRegularPrime 7 := by
  regular_prime_by_values 7 2

theorem isRegularPrime_eleven_lt100 :
    letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    IsRegularPrime 11 := by
  regular_prime_by_values 11 4

theorem isRegularPrime_thirteen_lt100 :
    letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    IsRegularPrime 13 := by
  regular_prime_by_values 13 5

theorem isRegularPrime_seventeen_lt100 :
    letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    IsRegularPrime 17 := by
  regular_prime_by_values 17 7

theorem isRegularPrime_nineteen_lt100 :
    letI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    IsRegularPrime 19 := by
  regular_prime_by_values 19 8

theorem isRegularPrime_twentythree_lt100 :
    letI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    IsRegularPrime 23 := by
  regular_prime_by_values 23 10

theorem isRegularPrime_twentynine_lt100 :
    letI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
    IsRegularPrime 29 := by
  regular_prime_by_values 29 13

theorem isRegularPrime_thirtyone_lt100 :
    letI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    IsRegularPrime 31 := by
  regular_prime_by_values 31 14

theorem not_isRegularPrime_thirtyseven :
    letI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
    ¬ IsRegularPrime 37 := by
  irregular_prime_by_value 37 16

theorem isRegularPrime_fortyone_lt100 :
    letI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
    IsRegularPrime 41 := by
  regular_prime_by_values 41 19

theorem isRegularPrime_fortythree_lt100 :
    letI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
    IsRegularPrime 43 := by
  regular_prime_by_values 43 20

theorem isRegularPrime_fortyseven_lt100 :
    letI : Fact (Nat.Prime 47) := ⟨by norm_num⟩
    IsRegularPrime 47 := by
  regular_prime_by_values 47 22

theorem isRegularPrime_fiftythree_lt100 :
    letI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    IsRegularPrime 53 := by
  regular_prime_by_values 53 25

theorem not_isRegularPrime_fiftynine_lt100 :
    letI : Fact (Nat.Prime 59) := ⟨by norm_num⟩
    ¬ IsRegularPrime 59 := by
  irregular_prime_by_value 59 22

theorem isRegularPrime_sixtyone_lt100 :
    letI : Fact (Nat.Prime 61) := ⟨by norm_num⟩
    IsRegularPrime 61 := by
  regular_prime_by_values 61 29

theorem not_isRegularPrime_sixtyseven_lt100 :
    letI : Fact (Nat.Prime 67) := ⟨by norm_num⟩
    ¬ IsRegularPrime 67 := by
  irregular_prime_by_value 67 29

theorem isRegularPrime_seventyone_lt100 :
    letI : Fact (Nat.Prime 71) := ⟨by norm_num⟩
    IsRegularPrime 71 := by
  regular_prime_by_values 71 34

theorem isRegularPrime_seventythree_lt100 :
    letI : Fact (Nat.Prime 73) := ⟨by norm_num⟩
    IsRegularPrime 73 := by
  regular_prime_by_values 73 35

theorem isRegularPrime_seventynine_lt100 :
    letI : Fact (Nat.Prime 79) := ⟨by norm_num⟩
    IsRegularPrime 79 := by
  regular_prime_by_values 79 38

theorem isRegularPrime_eightythree_lt100 :
    letI : Fact (Nat.Prime 83) := ⟨by norm_num⟩
    IsRegularPrime 83 := by
  regular_prime_by_values 83 40

theorem isRegularPrime_eightynine_lt100 :
    letI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
    IsRegularPrime 89 := by
  regular_prime_by_values 89 43

theorem isRegularPrime_ninetyseven_lt100 :
    letI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
    IsRegularPrime 97 := by
  regular_prime_by_values 97 47

/-- Every prime below `100` except the three irregular primes `37`, `59`,
and `67` is regular. -/
theorem isRegularPrime_of_prime_lt100_of_ne_irregular
    {n : ℕ} (hn_prime : n.Prime) (hn_two : 2 < n) (hn_lt100 : n < 100)
    (hn37 : n ≠ 37) (hn59 : n ≠ 59) (hn67 : n ≠ 67) :
    letI : Fact n.Prime := ⟨hn_prime⟩
    IsRegularPrime n := by
  haveI : Fact n.Prime := ⟨hn_prime⟩
  interval_cases n <;> first
    | (exfalso; norm_num at hn_prime; done)
    | exact False.elim (hn37 rfl)
    | exact False.elim (hn59 rfl)
    | exact False.elim (hn67 rfl)
    | simpa using isRegularPrime_three_lt100
    | simpa using isRegularPrime_five_lt100
    | simpa using isRegularPrime_seven_lt100
    | simpa using isRegularPrime_eleven_lt100
    | simpa using isRegularPrime_thirteen_lt100
    | simpa using isRegularPrime_seventeen_lt100
    | simpa using isRegularPrime_nineteen_lt100
    | simpa using isRegularPrime_twentythree_lt100
    | simpa using isRegularPrime_twentynine_lt100
    | simpa using isRegularPrime_thirtyone_lt100
    | simpa using isRegularPrime_fortyone_lt100
    | simpa using isRegularPrime_fortythree_lt100
    | simpa using isRegularPrime_fortyseven_lt100
    | simpa using isRegularPrime_fiftythree_lt100
    | simpa using isRegularPrime_sixtyone_lt100
    | simpa using isRegularPrime_seventyone_lt100
    | simpa using isRegularPrime_seventythree_lt100
    | simpa using isRegularPrime_seventynine_lt100
    | simpa using isRegularPrime_eightythree_lt100
    | simpa using isRegularPrime_eightynine_lt100
    | simpa using isRegularPrime_ninetyseven_lt100

end BernoulliRegular
