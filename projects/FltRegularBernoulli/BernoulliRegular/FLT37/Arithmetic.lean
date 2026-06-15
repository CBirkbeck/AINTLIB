import BernoulliRegular.BernoulliFast.Tactic

/-!
# Arithmetic non-divisibility lemmas for `p = 37` (ticket FLT37a)

This module contains the concrete numerical input to the Vandiver-III route
for FLT at `p = 37`: for every odd `k ∈ {1, 3, 5, 7, 9, 11, 13, 15, 17}`,
the prime `37` does **not** divide the numerator of `B_{2k}`.

Combined with the existing `thirtyseven_dvd_bernoulli_thirtytwo_num` (witness
for the even index `k = 16`),
this establishes the parity hypothesis of Vandiver Theorem III for `ℓ = 37`:
the only Bernoulli index `2k ∈ [2, 34]` with `37 ∣ num(B_{2k})` is `k = 16`,
which is even.

All proofs reduce to the `bernoulli_decide` tactic on concrete numerator
values cached by `BernoulliRegular.BernoulliFast`.
-/

namespace BernoulliRegular

namespace FLT37

private lemma not_dvd_bernoulli_two_num : ¬ (37 : ℤ) ∣ (bernoulli 2).num := by
  bernoulli_decide

private lemma not_dvd_bernoulli_six_num : ¬ (37 : ℤ) ∣ (bernoulli 6).num := by
  bernoulli_decide

private lemma not_dvd_bernoulli_ten_num : ¬ (37 : ℤ) ∣ (bernoulli 10).num := by
  bernoulli_decide

private lemma not_dvd_bernoulli_fourteen_num : ¬ (37 : ℤ) ∣ (bernoulli 14).num := by
  bernoulli_decide

private lemma not_dvd_bernoulli_eighteen_num : ¬ (37 : ℤ) ∣ (bernoulli 18).num := by
  bernoulli_decide

private lemma not_dvd_bernoulli_twentytwo_num : ¬ (37 : ℤ) ∣ (bernoulli 22).num := by
  bernoulli_decide

private lemma not_dvd_bernoulli_twentysix_num : ¬ (37 : ℤ) ∣ (bernoulli 26).num := by
  bernoulli_decide

private lemma not_dvd_bernoulli_thirty_num : ¬ (37 : ℤ) ∣ (bernoulli 30).num := by
  bernoulli_decide

private lemma not_dvd_bernoulli_thirtyfour_num : ¬ (37 : ℤ) ∣ (bernoulli 34).num := by
  bernoulli_decide

/-- For every odd `k ∈ {1, 3, 5, 7, 9, 11, 13, 15, 17}`, the prime `37` does
not divide the numerator of `B_{2k}`. -/
theorem not_dvd_bernoulli_num_of_odd_index_thirtyseven
    {k : ℕ} (hk_pos : 1 ≤ k) (hk_le : k ≤ 17) (hk_odd : Odd k) :
    ¬ (37 : ℤ) ∣ (bernoulli (2 * k)).num := by
  interval_cases k
  · exact not_dvd_bernoulli_two_num
  · exact absurd hk_odd (by decide)
  · exact not_dvd_bernoulli_six_num
  · exact absurd hk_odd (by decide)
  · exact not_dvd_bernoulli_ten_num
  · exact absurd hk_odd (by decide)
  · exact not_dvd_bernoulli_fourteen_num
  · exact absurd hk_odd (by decide)
  · exact not_dvd_bernoulli_eighteen_num
  · exact absurd hk_odd (by decide)
  · exact not_dvd_bernoulli_twentytwo_num
  · exact absurd hk_odd (by decide)
  · exact not_dvd_bernoulli_twentysix_num
  · exact absurd hk_odd (by decide)
  · exact not_dvd_bernoulli_thirty_num
  · exact absurd hk_odd (by decide)
  · exact not_dvd_bernoulli_thirtyfour_num

/-- The arithmetic parity hypothesis of Vandiver Theorem III for `ℓ = 37`:
every Bernoulli index `2k ∈ [2, 34]` for which `37 ∣ num(B_{2k})` has even
`k`. The only such `k` is `k = 16` (witness:
`BernoulliRegular.thirtyseven_dvd_bernoulli_thirtytwo_num`). -/
theorem irregular_index_even_thirtyseven :
    ∀ k, 1 ≤ k → 2 * k ≤ 37 - 3 →
      (37 : ℤ) ∣ (bernoulli (2 * k)).num → Even k := by
  intro k hk_pos hk_le hdvd
  rcases Nat.even_or_odd k with hk_even | hk_odd
  · exact hk_even
  · exact absurd hdvd
      (not_dvd_bernoulli_num_of_odd_index_thirtyseven hk_pos (by omega) hk_odd)

end FLT37

end BernoulliRegular
