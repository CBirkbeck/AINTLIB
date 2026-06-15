import Mathlib.NumberTheory.Bernoulli

/-!
# Rational zeta values at non-positive integers

RJW (arXiv:2309.15692) §4 interpolates the values `ζ(−k)`. As rational numbers these
are `ζ(−k) = (−1)^k B_{k+1}/(k+1)` (RJW TeX line 1455, with mathlib's `bernoulli`
convention `B₁ = −1/2`); the whole p-adic chain of §4 only ever uses this rational
value, cast into `ℚ_p`. The identification with the complex `riemannZeta (−k)` is the
bridge `zetaNeg_eq_riemannZeta` in `ZetaValuesComplex.lean` (kept separate so the main
chain does not import complex analysis).
-/

/-- The rational number `ζ(−k) = (−1)^k B_{k+1}/(k+1)` (RJW TeX line 1455; mathlib's
`bernoulli` convention). For the identification with the complex zeta function see
`zetaNeg_eq_riemannZeta`. -/
def zetaNeg (k : ℕ) : ℚ :=
  (-1) ^ k * bernoulli (k + 1) / (k + 1)

@[simp]
lemma zetaNeg_zero : zetaNeg 0 = -(1 / 2) := by
  norm_num [zetaNeg, bernoulli_one]

/-- The trivial zeros: `ζ(−k) = 0` for even `k ≥ 2` (odd Bernoulli numbers vanish). -/
lemma zetaNeg_eq_zero_of_even {k : ℕ} (hk : k ≠ 0) (h : Even k) : zetaNeg k = 0 := by
  rw [zetaNeg, bernoulli_eq_zero_of_odd h.add_one (by omega), mul_zero, zero_div]

/-- Sign removal in the Kubota–Leopoldt interpolation (RJW TeX line 1596: "we may
remove the `(−1)^k` as `ζ(1−k) ≠ 0` if and only if `k` is even"): for `k > 0`,
`(−1)^k (1−q^{k−1}) ζ(1−k) = (1−q^{k−1}) ζ(1−k)` — at `k = 1` the factor
`1−q⁰` vanishes, at even `k` the sign is `+1`, and at odd `k ≥ 3` the zeta value vanishes. -/
lemma neg_one_pow_mul_one_sub_pow_mul_zetaNeg (q : ℚ) {k : ℕ} (hk : 0 < k) :
    (-1) ^ k * ((1 - q ^ (k - 1)) * zetaNeg (k - 1))
      = (1 - q ^ (k - 1)) * zetaNeg (k - 1) := by
  obtain rfl | hk1 := eq_or_ne k 1
  · simp
  · rcases Nat.even_or_odd k with he | ho
    · rw [he.neg_one_pow, one_mul]
    · rw [zetaNeg_eq_zero_of_even (by omega) (Nat.Odd.sub_odd ho odd_one)]
      ring
