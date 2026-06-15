import BernoulliRegular.BernoulliFast.PrimesUpTo100
import FltRegular.FltRegular
import Mathlib.NumberTheory.FLT.Four

/-!
# FLT for regular prime exponents up to 100

This file exposes one readable endpoint: every exponent `n ≤ 100`, with
`2 < n` and `n ∉ {37, 59, 67, 74}`, satisfies Fermat's Last Theorem.

The three primes `37`, `59`, and `67` are the irregular primes below `100`.
The composite exponent `74 = 2 * 37` is also excluded because reducing FLT for
`74` by divisor monotonicity would require the currently excluded exponent
`37`; the exponent `2` itself is false.
-/

namespace BernoulliRegular

/-- Fermat's Last Theorem for every prime exponent below `100` except the
three irregular primes below `100`: `37`, `59`, and `67`. -/
theorem fermatLastTheoremFor_prime_lt100_of_ne_irregular
    (n : ℕ) (hn_prime : n.Prime) (hn_two : 2 < n) (hn_lt100 : n < 100)
    (hn37 : n ≠ 37) (hn59 : n ≠ 59) (hn67 : n ≠ 67) :
    FermatLastTheoremFor n := by
  haveI : Fact n.Prime := ⟨hn_prime⟩
  exact flt_regular
    (isRegularPrime_of_prime_lt100_of_ne_irregular
      hn_prime hn_two hn_lt100 hn37 hn59 hn67)
    (by omega)

private theorem fermatLastTheoremFor_of_isRegularPrime_dvd
    {p n : ℕ} (hp_prime : p.Prime)
    (hp_reg : letI : Fact p.Prime := ⟨hp_prime⟩; IsRegularPrime p)
    (hp_odd : p ≠ 2) (hdvd : p ∣ n) :
    FermatLastTheoremFor n := by
  letI : Fact p.Prime := ⟨hp_prime⟩
  exact FermatLastTheoremFor.mono hdvd (flt_regular hp_reg hp_odd)

/-- Fermat's Last Theorem for every exponent up to `100` except `2`, the
three irregular primes below `100`, and `74 = 2 * 37`. -/
theorem fermatLastTheoremFor_le100_of_ne_irregular
    (n : ℕ) (hn_two : 2 < n) (hn_le100 : n ≤ 100)
    (hn37 : n ≠ 37) (hn59 : n ≠ 59) (hn67 : n ≠ 67) (hn74 : n ≠ 74) :
    FermatLastTheoremFor n := by
  by_cases h3 : 3 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 3) (by norm_num) isRegularPrime_three_lt100 (by norm_num) h3
  by_cases h4 : 4 ∣ n
  · exact FermatLastTheoremFor.mono h4 fermatLastTheoremFour
  by_cases h5 : 5 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 5) (by norm_num) isRegularPrime_five_lt100 (by norm_num) h5
  by_cases h7 : 7 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 7) (by norm_num) isRegularPrime_seven_lt100 (by norm_num) h7
  by_cases h11 : 11 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 11) (by norm_num) isRegularPrime_eleven_lt100 (by norm_num) h11
  by_cases h13 : 13 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 13) (by norm_num) isRegularPrime_thirteen_lt100 (by norm_num) h13
  by_cases h17 : 17 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 17) (by norm_num) isRegularPrime_seventeen_lt100 (by norm_num) h17
  by_cases h19 : 19 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 19) (by norm_num) isRegularPrime_nineteen_lt100 (by norm_num) h19
  by_cases h23 : 23 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 23) (by norm_num) isRegularPrime_twentythree_lt100 (by norm_num) h23
  by_cases h29 : 29 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 29) (by norm_num) isRegularPrime_twentynine_lt100 (by norm_num) h29
  by_cases h31 : 31 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 31) (by norm_num) isRegularPrime_thirtyone_lt100 (by norm_num) h31
  by_cases h41 : 41 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 41) (by norm_num) isRegularPrime_fortyone_lt100 (by norm_num) h41
  by_cases h43 : 43 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 43) (by norm_num) isRegularPrime_fortythree_lt100 (by norm_num) h43
  by_cases h47 : 47 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 47) (by norm_num) isRegularPrime_fortyseven_lt100 (by norm_num) h47
  by_cases h53 : 53 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 53) (by norm_num) isRegularPrime_fiftythree_lt100 (by norm_num) h53
  by_cases h61 : 61 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 61) (by norm_num) isRegularPrime_sixtyone_lt100 (by norm_num) h61
  by_cases h71 : 71 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 71) (by norm_num) isRegularPrime_seventyone_lt100 (by norm_num) h71
  by_cases h73 : 73 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 73) (by norm_num) isRegularPrime_seventythree_lt100 (by norm_num) h73
  by_cases h79 : 79 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 79) (by norm_num) isRegularPrime_seventynine_lt100 (by norm_num) h79
  by_cases h83 : 83 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 83) (by norm_num) isRegularPrime_eightythree_lt100 (by norm_num) h83
  by_cases h89 : 89 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 89) (by norm_num) isRegularPrime_eightynine_lt100 (by norm_num) h89
  by_cases h97 : 97 ∣ n
  · exact fermatLastTheoremFor_of_isRegularPrime_dvd
      (p := 97) (by norm_num) isRegularPrime_ninetyseven_lt100 (by norm_num) h97
  exfalso
  interval_cases n <;> omega

end BernoulliRegular
