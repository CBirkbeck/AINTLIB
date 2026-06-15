# Completed Tickets - Infinitely Many Irregular Primes

Archived from `tickets.md` after completion.

### [IRR-00] Bridge Bernoulli witnesses to `¬ IsRegularPrime`

- Status: done
- Claimer: Riccardo
- Started: 2026-05-22
- Completed: 2026-05-22
- Result: Added `BernoulliRegular/IrregularPrimes/Basic.lean` with
  `not_isRegularPrime_of_bernoulli_num_dvd`,
  `exists_bernoulli_num_dvd_of_not_isRegularPrime`, and the concrete
  `not_isRegularPrime_thirtyseven_via_bernoulli` sanity check.
- Files:
  - `BernoulliRegular/IrregularPrimes/Basic.lean`
  - `BernoulliRegular/IrregularPrimes.lean`

Goal:

Add small bridge lemmas that use `BernoulliRegular.KummerCriterion` without
introducing a new irregular-prime predicate.

Suggested declarations:

```lean
theorem not_isRegularPrime_of_bernoulli_num_dvd
    {p : Nat} (hp : p.Prime) (hp_odd : p ≠ 2) :
    (∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧
      (p : Int) ∣ (bernoulli (2 * k)).num) →
      letI : Fact p.Prime := ⟨hp⟩
      ¬ IsRegularPrime p

theorem exists_bernoulli_num_dvd_of_not_isRegularPrime
    {p : Nat} (hp : p.Prime) (hp_odd : p ≠ 2)
    (hirr : letI : Fact p.Prime := ⟨hp⟩; ¬ IsRegularPrime p) :
    ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧
      (p : Int) ∣ (bernoulli (2 * k)).num
```

Implementation notes:

- The first theorem is just the contrapositive of
  `BernoulliRegular.KummerCriterion`.
- The second theorem extracts the `∃ k` witness from the negated universal
  in `KummerCriterion`.
- Keep theorem statements independent of global typeclass arguments where
  possible; introduce `letI : Fact p.Prime := ⟨hp⟩` locally.
- Prove a small seed theorem from existing computations if useful:

```lean
theorem not_isRegularPrime_thirtyseven_via_bernoulli :
    letI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
    ¬ IsRegularPrime 37
```

This is not mathematically needed if the final proof handles the empty finite
set, but it is useful as a sanity check.

Done criteria:

- The witness-to-regularity bridge builds.
- No new theorem is proved from a bundled irregularity hypothesis.

### [IRR-01] Finite-set and infinitude scaffolding

- Status: done
- Claimer: Riccardo
- Started: 2026-05-22
- Completed: 2026-05-22
- Result: Added finite-cover scaffolding in
  `BernoulliRegular/IrregularPrimes/Basic.lean`, including
  `infinite_of_forall_finite_set_not_cover` and
  `finite_not_isRegularPrime_set_iff_bounded_by_finset`.
- Files:
  - `BernoulliRegular/IrregularPrimes/Basic.lean`

Goal:

Set up the exact finite-set contradiction form used by the final proof.

Suggested declarations:

```lean
theorem infinite_of_forall_finite_set_exists_outside
    {P : Nat → Prop}
    (h : ∀ S : Finset Nat, (∀ p, P p → p ∈ S) → False) :
    Set.Infinite {p : Nat | P p}

theorem finite_irregular_set_iff_bounded_by_finset :
    Set.Finite
      {p : Nat | ∃ hp : p.Prime,
        letI : Fact p.Prime := ⟨hp⟩
        ¬ IsRegularPrime p} ↔
      ∃ S : Finset Nat,
        ∀ p, (∃ hp : p.Prime,
          letI : Fact p.Prime := ⟨hp⟩
          ¬ IsRegularPrime p) → p ∈ S
```

Implementation notes:

- Mathlib already has many `Set.Finite` and `Set.Infinite` tools; prefer using
  them rather than proving a custom theorem if a suitable lemma exists.
- The final contradiction should be parameterized by a finite set `S` satisfying
  `∀ p, (∃ hp : p.Prime, letI : Fact p.Prime := ⟨hp⟩; ¬ IsRegularPrime p) → p ∈ S`.
- Do not require `S` to contain only irregular primes.  Allowing extra primes
  makes the divisor-closed base construction easier.

Done criteria:

- The final theorem can be reduced to proving:

```lean
∀ S : Finset Nat,
  (∀ p, (∃ hp : p.Prime,
    letI : Fact p.Prime := ⟨hp⟩
    ¬ IsRegularPrime p) → p ∈ S) → False
```

### [IRR-02] Rational numerator and prime-divisor lemmas

- Status: done
- Claimer: Riccardo
- Started: 2026-05-22
- Completed: 2026-05-22
- Result: Added `BernoulliRegular/IrregularPrimes/RatNumerator.lean`
  with `exists_prime_dvd_num_of_one_lt_abs`,
  `dvd_num_of_dvd_div_nat_num`,
  `dvd_bernoulli_num_of_dvd_bernoulli_div_num`, and public `ℤ_[p]` /
  `ℚ_[p]` congruence helpers
  `padic_eq_p_mul_of_prime_dvd_num`,
  `prime_dvd_num_of_padic_eq_p_mul`, and
  `prime_dvd_num_of_padic_sub_eq_p_mul`.  The original `pIntegral` sketch was
  replaced because mathlib's `pIntegral` abbreviation is private.
- Files:
  - `BernoulliRegular/IrregularPrimes/RatNumerator.lean`

Goal:

Formalize the rational-number bookkeeping used to pass from
`|B_m / m| > 1` to a prime divisor of the numerator, and from p-adic
congruences back to `Rat.num`.

Suggested declarations:

```lean
theorem exists_prime_dvd_num_of_one_lt_abs
    {q : Rat} (hq : 1 < |(q : Real)|) :
    ∃ p : Nat, p.Prime ∧ (p : Int) ∣ q.num

theorem prime_not_dvd_num_of_neg_valuation
    {p : Nat} (hp : p.Prime) {q : Rat}
    (hval : Rat.padicValuation p q < 0) :
    ¬ (p : Int) ∣ q.num

theorem prime_dvd_num_of_padic_eq_p_mul
    {p : Nat} [Fact p.Prime] {q : Rat}
    (hzero : ∃ z : ℤ_[p], (q : ℚ_[p]) = (p : ℚ_[p]) * (z : ℚ_[p])) :
    (p : Int) ∣ q.num

theorem padic_eq_p_mul_of_prime_dvd_num
    {p : Nat} [Fact p.Prime] {q : Rat}
    (hdiv : (p : Int) ∣ q.num) :
    ∃ z : ℤ_[p], (q : ℚ_[p]) = (p : ℚ_[p]) * (z : ℚ_[p])

theorem prime_dvd_num_of_padic_sub_eq_p_mul
    {p : Nat} [Fact p.Prime] {q r : Rat}
    (hdiv : (p : Int) ∣ q.num)
    (hcong : ∃ z : ℤ_[p],
      (q : ℚ_[p]) - (r : ℚ_[p]) = (p : ℚ_[p]) * (z : ℚ_[p])) :
    (p : Int) ∣ r.num

theorem dvd_bernoulli_num_of_dvd_bernoulli_div_num
    {p n : Nat} (hp : p.Prime) (hn_pos : 0 < n)
    (hpn : ¬ p ∣ n)
    (hden : ¬ p ∣ (bernoulli n).den)
    (hdiv : (p : Int) ∣ (((bernoulli n : Rat) / n).num)) :
    (p : Int) ∣ (bernoulli n).num
```

Implementation notes:

- `Int.exists_prime_and_dvd` is likely enough once `q.num.natAbs ≠ 1` is
  extracted from `1 < |q|`.
- Keep signs out of the divisibility API by using `Int.natAbs`.
- Prefer `Rat.padicValuation` for denominator/numerator statements when it
  gives a shorter proof than direct `Rat.num_den` arithmetic.
- For `B_m / m`, remember that `Rat.num` is the reduced numerator of the
  quotient, not `(bernoulli m).num`.

Done criteria:

- The final proof can obtain a prime `p` with
  `(p : Int) ∣ (((bernoulli m : Rat) / m).num)` from `1 < |B_m / m|`.
- The final proof can convert divisibility of the reduced numerator of
  `B_m' / m'` into divisibility of `(bernoulli m').num`.

### [IRR-03] Bernoulli growth along even multiples

- Status: done
- Claimer: Riccardo
- Started: 2026-05-22
- Completed: 2026-05-22
- Result: Added `BernoulliRegular/IrregularPrimes/BernoulliGrowth.lean`.
  The proof uses `Mathlib.NumberTheory.ZetaValues.hasSum_zeta_nat` to derive
  a lower bound for `|B_{2k}|`, proves factorial-over-exponential divergence
  via `FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop`, and provides
  both `tendsto_abs_bernoulli_div_self_even` and
  `exists_large_even_multiple_abs_bernoulli_div_self_gt_one`.
- Files:
  - `BernoulliRegular/IrregularPrimes/BernoulliGrowth.lean`

Goal:

Prove Diekmann's growth input:

```lean
theorem tendsto_abs_bernoulli_div_self_even :
    Tendsto
      (fun n : Nat => |(((bernoulli (2 * n) : Rat) / (2 * n) : Rat) : Real)|)
      atTop atTop
```

and the arithmetic-progression corollary needed for the final proof:

```lean
theorem exists_large_even_multiple_abs_bernoulli_div_self_gt_one
    {C : Nat} (hC_pos : 0 < C) (hC_even : Even C) :
    ∃ t : Nat,
      1 < |(((bernoulli (C * 2 ^ t) : Rat) / (C * 2 ^ t) : Rat) : Real)|
```

Implementation strategy:

1. Use `Mathlib.NumberTheory.ZetaValues.hasSum_zeta_nat`.
2. Extract the absolute-value formula for `B_{2k}`:

   ```text
   |B_{2k}| =
     2 * (2k)! / (2π)^(2k) * ζ(2k)
   ```

   or a one-sided lower bound sufficient for divergence.

3. Use positivity of the zeta sum:

   ```text
   ζ(2k) = ∑' n ≥ 1, 1 / n^(2k) ≥ 1
   ```

   The `n = 1` term is `1`, and all terms are nonnegative.

4. Reduce growth to factorial-over-exponential:

   ```text
   |B_{2k}| / (2k)
     ≥ (2k - 1)! / (2π)^(2k)    -- up to a harmless factor of 2
   ```

5. Prove the right-hand side tends to `∞`.  A ratio argument is probably the
   least painful:

   ```text
   a_k = (2k - 1)! / (2π)^(2k)
   a_{k+1} / a_k = (2k)(2k + 1) / (2π)^2
   ```

   Once this ratio is eventually `≥ 2`, `a_k` dominates a geometric sequence.

6. Compose with `k_t = C * 2^t / 2` for even `C`.  Since `C * 2^t → ∞`, the
   subsequence still tends to `∞`.

Risk:

- This is the largest analytic dependency in the route.  If the direct zeta
  extraction is too heavy, split it:
  - `IRR-03a`: exact zeta/Bernoulli absolute formula;
  - `IRR-03b`: positivity lower bound for zeta;
  - `IRR-03c`: factorial-over-exponential divergence;
  - `IRR-03d`: even-multiple corollary.

Done criteria:

- Given any positive even `C`, produce an even `m = C * 2^t` with
  `1 < |B_m / m|`.

### [IRR-04] Von Staudt-Clausen consequences for numerator exclusion

- Status: done
- Claimer: Riccardo
- Started: 2026-05-22
- Completed: 2026-05-22
- Result: Added `BernoulliRegular/IrregularPrimes/VonStaudtConsequences.lean`
  with a public even-index wrapper for `Bernoulli.vonStaudt_clausen`, the
  correction-sum split, denominator exclusion for `B_n + 1/p`, and the
  numerator exclusions
  `not_dvd_num_bernoulli_of_sub_one_dvd`,
  `not_dvd_num_bernoulli_div_self_of_sub_one_dvd`, and
  `sub_one_not_dvd_of_dvd_num_bernoulli_div_self`.  Also added the constructed
  index exclusion lemmas
  `numerator_prime_not_dvd_constructed_m` and
  `numerator_prime_not_mem_constructed_base` in `Infinitude.lean`.
- Files:
  - `BernoulliRegular/IrregularPrimes/VonStaudtConsequences.lean`
  - `BernoulliRegular/IrregularPrimes/Infinitude.lean`

Goal:

Derive exactly the local consequences of von Staudt-Clausen used in Theorem
47.

Suggested declarations:

```lean
theorem bernoulli_vpadic_eq_neg_one_of_sub_one_dvd
    {p n : Nat} (hp : p.Prime) (hn_pos : 0 < n) (hn_even : Even n)
    (hdiv : p - 1 ∣ n) :
    Rat.padicValuation p (bernoulli n) = -1

theorem not_dvd_num_bernoulli_of_sub_one_dvd
    {p n : Nat} (hp : p.Prime) (hn_pos : 0 < n) (hn_even : Even n)
    (hdiv : p - 1 ∣ n) :
    ¬ (p : Int) ∣ (bernoulli n).num

theorem not_dvd_num_bernoulli_div_self_of_sub_one_dvd
    {p n : Nat} (hp : p.Prime) (hn_pos : 0 < n) (hn_even : Even n)
    (hdiv : p - 1 ∣ n) :
    ¬ (p : Int) ∣ (((bernoulli n : Rat) / n).num)
```

Implementation notes:

- Source theorem: `Bernoulli.vonStaudt_clausen`.
- It is enough to prove the p-adic local statement:

  ```text
  B_n + 1/p ∈ ℤ_[p]  when p - 1 | n
  ```

  because the remaining correction-sum terms have denominators prime to `p`.
- The quotient statement `B_n / n` is stronger when `p ∣ n`: its valuation is
  even more negative.  This is exactly why the divisor-closed base construction
  works.
- Also prove the generic case:

  ```lean
theorem sub_one_not_dvd_of_dvd_num_bernoulli_div_self
      {p n : Nat} ... :
      (p : Int) ∣ (((bernoulli n : Rat) / n).num) → ¬ (p - 1) ∣ n
  ```

Done criteria:

- The final proof can exclude:
  - every old irregular prime `p_i`, because `p_i - 1 ∣ m`;
  - every prime divisor of the constructed `m`, because `q - 1 ∣ m`;
  - the boundary case `(p - 1) ∣ m` for the newly found numerator prime.

### [IRR-05] Divisor-closed multiplier

- Status: done
- Claimer: Riccardo
- Started: 2026-05-22
- Completed: 2026-05-22
- Result: Added `BernoulliRegular/IrregularPrimes/DivisorClosedBase.lean`.
  The implementation uses the stronger factorial base
  `irregularBase S = 2 * (max 3 (S.sup id))!`, proving the requested
  evenness, positivity, membership, and divisor-closure lemmas.
- Files:
  - `BernoulliRegular/IrregularPrimes/DivisorClosedBase.lean`

Goal:

Build the formal replacement for Diekmann's informal choice of `N`.

Suggested definitions:

```lean
def primeSubOneLcmUpTo (M : Nat) : Nat :=
  (Finset.range (M + 1)).lcm
    (fun q => if q.Prime then q - 1 else 1)

def irregularBase (S : Finset Nat) : Nat :=
  2 * primeSubOneLcmUpTo (max 3 (S.sup id))
```

Suggested declarations:

```lean
theorem even_irregularBase (S : Finset Nat) : Even (irregularBase S)

theorem pos_irregularBase (S : Finset Nat) : 0 < irregularBase S

theorem sub_one_dvd_irregularBase_of_mem
    {S : Finset Nat} {p : Nat}
    (hpS : p ∈ S) (hp : p.Prime) :
    p - 1 ∣ irregularBase S

theorem sub_one_dvd_irregularBase_of_prime_dvd_irregularBase
    {S : Finset Nat} {q : Nat}
    (hq : q.Prime) (hqdvd : q ∣ irregularBase S) :
    q - 1 ∣ irregularBase S

theorem sub_one_dvd_m_of_prime_dvd_m
    {S : Finset Nat} {q t : Nat}
    (hq : q.Prime) (hqdvd : q ∣ irregularBase S * 2 ^ t) :
    q - 1 ∣ irregularBase S * 2 ^ t
```

Implementation notes:

- The lcm over all primes up to the finite bound is intentionally stronger
  than the minimal recursive closure.  It is simpler in Lean.
- If a prime `q` divides `irregularBase S`, then either `q = 2`, or `q`
  divides `r - 1` for some prime `r ≤ max 3 (S.sup id)`, hence `q < r`
  and `q ≤ max 3 (S.sup id)`.  Therefore `q - 1` appears in the lcm.
- For the final `m = irregularBase S * 2^t`, a prime divisor is either `2` or
  a divisor of `irregularBase S`, so the same closure property holds.

Done criteria:

- The final proof has a reusable lemma:

```lean
theorem numerator_prime_not_dvd_constructed_m
    {S : Finset Nat} {t p : Nat}
    (hp : p.Prime)
    (hnum : (p : Int) ∣ (((bernoulli (irregularBase S * 2 ^ t) : Rat) /
      (irregularBase S * 2 ^ t)).num)) :
    ¬ p ∣ irregularBase S * 2 ^ t
```

proved by combining divisor closure with `IRR-04`.

### [IRR-07] Positive residue reduction

- Status: done
- Claimer: Riccardo
- Started: 2026-05-22
- Completed: 2026-05-22
- Result: Added `positiveResidueModSubOne`,
  `positiveResidue_properties`, and
  `positiveResidue_in_irregular_range` in
  `BernoulliRegular/IrregularPrimes/Infinitude.lean`.
- Files:
  - `BernoulliRegular/IrregularPrimes/Infinitude.lean`

Goal:

Given a numerator prime `p` for `B_m / m`, produce the Diekmann residue
`m'`.

Suggested declarations:

```lean
def positiveResidueModSubOne (p m : Nat) : Nat := m % (p - 1)

theorem positiveResidue_properties
    {p m : Nat} (hp : p.Prime) (hp_odd : p ≠ 2)
    (hm_even : Even m) (hnot : ¬ (p - 1) ∣ m) :
    let m' := positiveResidueModSubOne p m
    0 < m' ∧ m' < p - 1 ∧ Even m' ∧ m ≡ m' [MOD p - 1]

theorem positiveResidue_in_irregular_range
    {p m m' : Nat} ... :
    1 ≤ m' / 2 ∧ 2 * (m' / 2) ≤ p - 3
```

Implementation notes:

- Since `p` is odd, `p - 1` is even.  If `m` is even and
  `m ≡ m' [MOD p - 1]`, then `m'` is even.
- `m' < p - 1` and `m' > 0` imply `m' ≤ p - 2`.  Evenness and oddness of `p`
  sharpen this to `m' ≤ p - 3`.
- The final KummerCriterion witness wants an index `k` with `2 * k = m'`.

Done criteria:

- The final proof can pass from `m` to an even `m'` in the exact Bernoulli
  range for `p`.
