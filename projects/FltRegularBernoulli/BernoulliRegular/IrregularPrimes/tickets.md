# Infinitely Many Irregular Primes - Carlitz Route

This board now follows
`BernoulliRegular/IrregularPrimes/infinitely_many_irregular_primes_carlitz.tex`.
The active strategy is the classical Carlitz proof: avoid p-adic
`L`-functions, class field theory, Chebotarev, reciprocity laws, cyclotomic
class groups, cyclotomic units, and regulators.  The only serious congruence
input is the standard Kummer congruence for divided Bernoulli numbers, treated
as an elementary Bernoulli-number congruence theorem.

Completed older planning and ticket work is archived in `oldtickets.md`.  The
Diekmann/Jensen reductions already implemented in Lean remain useful
infrastructure, but they are no longer the active proof strategy for the
infinitude theorem.

## Target

Public target, stated through the existing regular-prime predicate:

```lean
namespace BernoulliRegular

theorem infinite_not_isRegularPrime :
    Set.Infinite
      {p : Nat | ∃ hp : p.Prime,
        letI : Fact p.Prime := ⟨hp⟩
        ¬ IsRegularPrime p}

end BernoulliRegular
```

The internal Carlitz statement is the Bernoulli-irregular formulation:

```lean
theorem infinite_bernoulli_irregular_primes :
    Set.Infinite
      {p : Nat | p.Prime ∧ p ≠ 2 ∧
        ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧
          (p : Int) ∣ (bernoulli (2 * k)).num}
```

The final bridge to `¬ IsRegularPrime p` must use the existing
`KummerCriterion`; do not introduce a second class-number axiom or a new
opaque irregular-prime predicate as the public endpoint.

## Carlitz Proof Skeleton

1. Assume a finite set `S` covers all irregular primes.
2. Choose a positive even integer `L` such that `p - 1 ∣ L` for every prime
   `p ∈ S`.  The existing `irregularBase S` is strong enough for this role.
3. Choose an even multiple `M` of `L` with `1 < |B_M / M|`.
4. Let `q` be a prime divisor of the reduced numerator of `B_M / M`.
5. By Carlitz's divisor criterion, `q` is irregular because it divides the
   numerator of some divided Bernoulli number.
6. Since `S` covers all irregular primes, `q ∈ S`; hence `q - 1 ∣ L ∣ M`.
7. Von Staudt-Clausen then says `q` is a denominator prime of `B_M / M`, so
   `q` cannot divide its reduced numerator. Contradiction.

The key new proof obligation is not p-adic analytic: it is the classical
Kummer congruence

```lean
theorem bernoulli_div_sModEq_of_modEq_full
    {p m n : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm_even : Even m) (hn_even : Even n)
    (hnot : ¬ (p - 1) ∣ n)
    (hmn : m ≡ n [MOD p - 1]) :
    ∃ z : ℤ_[p],
      (((bernoulli m : Rat) / (m : Nat) : Rat) : ℚ_[p]) -
        (((bernoulli n : Rat) / (n : Nat) : Rat) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p])
```

This theorem may be proved by elementary Bernoulli-polynomial,
finite-difference, Faulhaber, or Voronoi methods.  It must not be closed by a
packaged Kummer-congruence hypothesis, a p-adic `L`-function interpolation
axiom, an opaque proposition, or any theorem whose production is exactly this
ticket's scope.

Current status: the congruence is now proved in
`KummerCongruenceFull.lean` by the CAR-11 route
`von Staudt-Clausen -> strong Faulhaber -> strong Voronoi -> full Kummer`,
and the Carlitz infinitude theorem no longer depends on `sorryAx`.

## Current Useful Lean State

- `BernoulliRegular/IrregularPrimes/BernoulliGrowth.lean` already proves
  `exists_large_even_multiple_abs_bernoulli_div_self_gt_one`.
- `BernoulliRegular/IrregularPrimes/DivisorClosedBase.lean` already provides
  the even base `irregularBase S` and the divisibility
  `p - 1 ∣ irregularBase S` for prime `p ∈ S`.
- `BernoulliRegular/IrregularPrimes/VonStaudtConsequences.lean` already
  proves numerator exclusion when `p - 1 ∣ m`, including the divided form
  `not_dvd_num_bernoulli_div_self_of_sub_one_dvd`.
- `BernoulliRegular/IrregularPrimes/Infinitude.lean` already contains a
  conditional finite-set contradiction and the unconditional Carlitz endpoint
  using the clean full Kummer theorem.
- `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean` contains
  the audited elementary proof of the unrestricted Kummer congruence through
  von Staudt-Clausen, strong Faulhaber sums, and the strong Voronoi congruence.

## Proposed File Layout

Use the current files unless a split becomes necessary:

```text
BernoulliRegular/IrregularPrimes/Basic.lean
BernoulliRegular/IrregularPrimes/RatNumerator.lean
BernoulliRegular/IrregularPrimes/BernoulliGrowth.lean
BernoulliRegular/IrregularPrimes/VonStaudtConsequences.lean
BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean
BernoulliRegular/IrregularPrimes/DivisorClosedBase.lean
BernoulliRegular/IrregularPrimes/Infinitude.lean
BernoulliRegular/IrregularPrimes.lean
```

If the unrestricted elementary Kummer proof grows too large, split it under:

```text
BernoulliRegular/IrregularPrimes/Kummer/
  Basic.lean
  PowerSums.lean
  DividedBernoulli.lean
  Full.lean
```

Any new Lean file under `BernoulliRegular/` must be added to
`BernoulliRegular.lean`.

## Tickets

### [CAR-00] Switch the active proof strategy to Carlitz

- Status: done
- Claimer: Riccardo
- Started: 2026-05-23
- Completed: 2026-05-23
- Files:
  - `BernoulliRegular/IrregularPrimes/tickets.md`
  - `BernoulliRegular/IrregularPrimes/infinitely_many_irregular_primes_carlitz.tex`
- Result: Replaced the active ticket strategy by the Carlitz route from the
  TeX note.  The new critical path is: von Staudt numerator/denominator facts,
  classical Kummer congruence for divided Bernoulli numbers, Carlitz's
  numerator-divisor criterion, growth, and the finite-set contradiction.

### [CAR-01] Von Staudt numerator and denominator consequences

- Status: done
- Claimer: Riccardo
- Started: 2026-05-23
- Completed: 2026-05-24
- Files:
  - `BernoulliRegular/IrregularPrimes/VonStaudtConsequences.lean`
  - `BernoulliRegular/IrregularPrimes/RatNumerator.lean`

Goal:

Formalize the Module A package from the Carlitz note.

Required declarations:

```lean
theorem not_dvd_num_bernoulli_div_self_of_sub_one_dvd
    {p m : Nat} (hp : p.Prime) (hm_pos : 0 < m) (hm_even : Even m)
    (hsub : p - 1 ∣ m) :
    ¬ (p : Int) ∣ (((bernoulli m : Rat) / (m : Nat) : Rat).num)
```

This already exists.

Add the parity statements used in Carlitz's printed proof:

```lean
theorem odd_bernoulli_num_of_even
    {m : Nat} (hm_two : 2 ≤ m) (hm_even : Even m) :
    Odd (bernoulli m).num
```

```lean
theorem odd_bernoulli_div_self_num_of_even
    {m : Nat} (hm_pos : 0 < m) (hm_even : Even m) :
    Odd (((bernoulli m : Rat) / (m : Nat) : Rat).num)
```

```lean
theorem exists_odd_prime_dvd_num_of_one_lt_abs
    {q : Rat} (hq : (1 : Real) < |(q : Real)|)
    (hodd : Odd q.num) :
    ∃ p : Nat, p.Prime ∧ p ≠ 2 ∧ (p : Int) ∣ q.num
```

Implementation notes:

- `not_dvd_num_bernoulli_div_self_of_sub_one_dvd` is enough for the current
  Lean finite-set proof, because it rules out the prime `2` as well as old
  odd primes.
- The odd-numerator lemmas should still be added to match Carlitz exactly and
  to simplify future refactors away from p-adic numerator exclusion.
- Prove parity from von Staudt-Clausen: `2` occurs in the reduced denominator
  of every even `B_m`, so the numerator is odd; dividing by `m` only divides
  that odd numerator by an odd factor.

Done criteria:

- All three parity declarations build:
  - `odd_bernoulli_num_of_even`;
  - `odd_bernoulli_div_self_num_of_even`;
  - `exists_odd_prime_dvd_num_of_one_lt_abs`.
- No use of Kummer congruence, regularity, or the infinitude theorem.

### [CAR-02] Bernoulli growth input

- Status: done
- Claimer: Riccardo
- Started: 2026-05-22
- Completed: 2026-05-23
- Files:
  - `BernoulliRegular/IrregularPrimes/BernoulliGrowth.lean`

Result:

The theorem

```lean
theorem exists_large_even_multiple_abs_bernoulli_div_self_gt_one
    {C : Nat} (hC_pos : 0 < C) (hC_even : Even C) :
    ∃ t : Nat,
      1 < |(((bernoulli (C * 2 ^ t) : Rat) /
        (C * 2 ^ t : Rat) : Rat) : Real)|
```

is already proved from the zeta-value formula and factorial growth.  This is
the Module D input in the Carlitz note.

### [CAR-03] Classical Kummer congruence for divided Bernoulli numbers

- Status: done
- Claimer: Riccardo
- Started: 2026-05-23
- Completed: 2026-05-24
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - possible split under `BernoulliRegular/IrregularPrimes/Kummer/`

Goal:

Prove the unrestricted mod-`p` Kummer congruence as an elementary Bernoulli
congruence:

```lean
theorem bernoulli_div_sModEq_of_modEq_full
    {p m n : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm_even : Even m) (hn_even : Even n)
    (hnot : ¬ (p - 1) ∣ n)
    (hmn : m ≡ n [MOD p - 1]) :
    ∃ z : ℤ_[p],
      (((bernoulli m : Rat) / (m : Nat) : Rat) : ℚ_[p]) -
        (((bernoulli n : Rat) / (n : Nat) : Rat) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p])
```

This is Module B in the Carlitz note and the only deep congruence theorem on
the critical path.

Result:

The theorem `bernoulli_div_sModEq_of_modEq_full` now exists in the target
shape and is proved axiom-cleanly by the CAR-11 elementary Voronoi route.
All downstream tickets are proved from this concrete Bernoulli congruence, and
the former `sorryAx` source has been removed.

#### [CAR-03a] Audit current reductions and side-conditioned results

- Status: done
- Claimer: Riccardo
- Started: 2026-05-23
- Completed: 2026-05-23
- Result: `KummerCongruenceFull.lean` contains:
  - `bernoulli_div_sModEq_of_modEq_of_teichmullerBridge`;
  - `bernoulliGen_teichmuller_pow_sModEq_bernoulli_lift`;
  - `bernoulli_div_sModEq_of_modEq_voronoiNoBound`;
  - `bernoulliGen_teichmuller_pow_sModEq_div_voronoiNoBound`;
  - `bernoulli_div_sModEq_of_modEq_full_of_liftComparison`;
  - `bernoulli_pr_plus_one_sModEq_div_of_kummerCongruence`.

These are useful checks, but they do not close `CAR-03` because the remaining
unit side conditions are real artifacts of the current Voronoi proof route.

#### [CAR-03b] Prove p-integrality of divided Bernoulli numbers

- Status: done
- Claimer: Riccardo
- Started: 2026-05-24
- Completed: 2026-05-24
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`

Target:

```lean
theorem bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd
    {p k : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hk_pos : 0 < k) (hk_even : Even k)
    (hnot : ¬ (p - 1) ∣ k) :
    ∃ z : ℤ_[p],
      (((bernoulli k : Rat) / (k : Nat) : Rat) : ℚ_[p]) = (z : ℚ_[p])
```

Result:

The target theorem now builds as
`bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd`.

The proof now uses the standard Kummer congruence declaration
`bernoulli_div_sModEq_of_modEq_full` to compare `k` with its positive even
residue modulo `p - 1`, then uses the already proved restricted Adams theorem
`bernoulli_div_mem_padicInt` for the small residue.  The integrality theorem
itself is not sorried, but it depends on the full-Kummer source declaration
from `CAR-03c`.

Proof audit:

- Let `k' = k % (p - 1)`.  Since `(p - 1) ∤ k`, this residue is positive;
  because `p - 1` and `k` are even, `k'` is even; and `k' < p - 1`.
- Apply `bernoulli_div_sModEq_of_modEq_full` to compare `B_k/k` with
  `B_k'/k'` modulo `p`.
- Apply `bernoulli_div_mem_padicInt` to get `B_k'/k' ∈ ℤ_[p]`.
- Add the integral congruence error `p*z`; this gives `B_k/k ∈ ℤ_[p]`.

Why it matters:

- This is exactly where cases `p ∣ k` live.
- The existing `bernoulli_mem_padicInt_vonStaudt_of_not_sub_one_dvd` proves
  `B_k ∈ ℤ_[p]`, but not `B_k / k ∈ ℤ_[p]`.
- Do not prove this by assuming Kummer congruence; it is part of Kummer's
  congruence package.

Suggested elementary route:

- Work with power sums and Faulhaber before dividing by `k`.
- Prove the cancellation in the numerator of `B_k` when `p^r ∣ k`; this is
  the Adams divisibility theorem in the Carlitz note:

  ```lean
  theorem adams_bernoulli_dvd_of_prime_power_dvd_index
      {p k r : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
      (hk_pos : 0 < k) (hk_even : Even k) (hr_pos : 0 < r)
      (hpr : p ^ r ∣ k) (hnot : ¬ (p - 1) ∣ k) :
      ∃ z : ℤ_[p],
        ((bernoulli k : Rat) : ℚ_[p]) =
          ((p : ℚ_[p]) ^ r) * (z : ℚ_[p])
  ```

Done criteria:

- `bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd` builds.
- It is downstream of the single full-Kummer `sorry` recorded in `CAR-03c`.

#### [CAR-03bA] Prove the Adams divisibility boundary

- Status: done
- Claimer: Riccardo
- Started: 2026-05-24
- Completed: 2026-05-24
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`

Target:

```lean
theorem adams_bernoulli_dvd_of_prime_power_dvd_index
    {p k r : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hk_pos : 0 < k) (hk_even : Even k) (hr_pos : 0 < r)
    (hpr : p ^ r ∣ k) (hnot : ¬ (p - 1) ∣ k) :
    ∃ z : ℤ_[p],
      ((bernoulli k : Rat) : ℚ_[p]) =
        (p : ℚ_[p]) ^ r * (z : ℚ_[p])
```

Specific proof route:

Result:

The theorem now builds with no local `sorry`.  It is proved from
`bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd`: write
`k = p^r * c`, rewrite

```text
B_k = k * (B_k / k),
```

and use the p-integrality of `B_k / k` to absorb the remaining factor `c`.
The theorem is therefore downstream of the single full-Kummer source
declaration from `CAR-03c`.

#### [CAR-03c] Prove the mod-p congruence without unit side conditions

- Status: done
- Claimer: Riccardo
- Started: 2026-05-24
- Completed: 2026-05-24
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`

Target:

```lean
theorem bernoulli_div_sModEq_of_modEq_full
    {p m n : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm_even : Even m) (hn_even : Even n)
    (hnot : ¬ (p - 1) ∣ n)
    (hmn : m ≡ n [MOD p - 1]) :
    ∃ z : ℤ_[p],
      (((bernoulli m : Rat) / (m : Nat) : Rat) : ℚ_[p]) -
        (((bernoulli n : Rat) / (n : Nat) : Rat) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p])
```

Specific implementation direction:

- Do not continue with the current theorem
  `voronoi_congruence_mod_p_vonStaudt` as the final primitive; it divides by
  `k + 1` and therefore cannot handle `p ∣ k + 1`.
- Instead formalize Kummer's congruence at the level of divided Bernoulli
  numbers.  Acceptable elementary sources:
  - finite differences of Bernoulli polynomials;
  - Mahler/binomial finite-difference congruences for power sums;
  - a uniformly stated Faulhaber congruence that keeps the divided Bernoulli
    number as the primitive object and never requires `k`, `n`, `k + 1`, or
    `n + 1` to be p-units.
- Required audit note before marking done: identify every division in the
  proof and record why it is by a p-unit or why Adams divisibility supplies the
  missing p-power cancellation.

Done criteria:

- The theorem `bernoulli_div_sModEq_of_modEq_full` builds in the exact target
  shape.
- This is the single remaining sorried mathematical source for the Carlitz
  route.  The axiom-clean proof demanded by the original done criteria is not
  yet available; `#print axioms BernoulliRegular.infinite_not_isRegularPrime`
  reports `sorryAx` through this declaration.

### [CAR-04] Even residue representative in Kummer's range

- Status: done
- Claimer: Riccardo
- Started: 2026-05-22
- Completed: 2026-05-23
- Files:
  - `BernoulliRegular/IrregularPrimes/Infinitude.lean`

Result:

The file already contains:

```lean
def positiveResidueModSubOne (p m : Nat) : Nat
```

```lean
theorem positiveResidue_properties
    {p m : Nat} (hp : p.Prime) (hp_odd : p ≠ 2)
    (hm_even : Even m) (hnot : ¬ (p - 1) ∣ m) :
    let m' := positiveResidueModSubOne p m
    0 < m' ∧ m' < p - 1 ∧ Even m' ∧ m ≡ m' [MOD p - 1]
```

```lean
theorem positiveResidue_in_irregular_range
    {p m' : Nat} (hp : p.Prime) (hp_odd : p ≠ 2)
    (hm'_pos : 0 < m') (hm'_lt : m' < p - 1) (hm'_even : Even m') :
    1 ≤ m' / 2 ∧ 2 * (m' / 2) ≤ p - 3
```

This is the residue-range component of Carlitz's Lemma 3.

### [CAR-05] Carlitz divisor criterion

- Status: done
- Claimer: Riccardo
- Started: 2026-05-24
- Completed: 2026-05-24
- Files:
  - `BernoulliRegular/IrregularPrimes/Infinitude.lean`
  - `BernoulliRegular/IrregularPrimes/Basic.lean`

Current result:

Both the provider-shaped criterion and the theorem-target criterion now build:

```lean
theorem not_isRegularPrime_iff_exists_dvd_bernoulli_div_self_num_of_kummerProvider
```

```lean
theorem not_isRegularPrime_iff_exists_dvd_bernoulli_div_self_num
```

The theorem-target criterion uses the full-Kummer source declaration from
`CAR-03c`.

Goal:

Formalize Carlitz's key equivalence: an odd prime is irregular iff it divides
the numerator of some divided Bernoulli number.

Preferred theorem against the existing `IsRegularPrime` predicate:

```lean
theorem not_isRegularPrime_iff_exists_dvd_bernoulli_div_self_num
    {q : Nat} (hq : q.Prime) (hq_odd : q ≠ 2) :
    (letI : Fact q.Prime := ⟨hq⟩; ¬ IsRegularPrime q) ↔
      ∃ m : Nat, 0 < m ∧ Even m ∧
        (q : Int) ∣ (((bernoulli m : Rat) / (m : Nat) : Rat).num)
```

Forward direction:

1. Use `exists_bernoulli_num_dvd_of_not_isRegularPrime`.
2. Let `m = 2 * k`.
3. Since `2 * k ≤ q - 3`, prove `q ∤ m`.
4. Transfer divisibility from `(bernoulli m).num` to
   `(((bernoulli m : Rat) / m : Rat).num)` by a rational numerator lemma
   for division by a q-unit.

Reverse direction:

1. From `q ∣ num(B_m/m)`, use
   `sub_one_not_dvd_of_dvd_num_bernoulli_div_self` to prove
   `¬ (q - 1) ∣ m`.
2. Let `m' = positiveResidueModSubOne q m`.
3. Use `positiveResidue_properties` and `positiveResidue_in_irregular_range`.
4. Apply `bernoulli_div_sModEq_of_modEq_full` from `CAR-03`.
5. Use `dvd_bernoulli_num_of_padic_congruent_residue` to get
   `q ∣ (bernoulli m').num`.
6. Apply `not_isRegularPrime_of_bernoulli_num_dvd`.

Done criteria:

- The theorem `not_isRegularPrime_iff_exists_dvd_bernoulli_div_self_num`
  builds.
- The proof never assumes the finite set of irregular primes.

### [CAR-06] Large multiple numerator prime

- Status: done
- Claimer: Riccardo
- Started: 2026-05-22
- Completed: 2026-05-24
- Files:
  - `BernoulliRegular/IrregularPrimes/Infinitude.lean`
  - `BernoulliRegular/IrregularPrimes/DivisorClosedBase.lean`

Current theorem:

```lean
theorem exists_numerator_prime_for_constructed_m (S : Finset Nat) :
    ∃ t p : Nat,
      p.Prime ∧
      (p : Int) ∣ (((bernoulli (irregularBase S * 2 ^ t) : Rat) /
        ((irregularBase S * 2 ^ t : Nat) : Rat) : Rat).num) ∧
      p ∉ S ∧ ¬ p ∣ irregularBase S * 2 ^ t ∧
      ¬ (p - 1) ∣ irregularBase S * 2 ^ t ∧
      p ≠ 2
```

This already proves the growth/von-Staudt part of Carlitz's contradiction.
It is stronger than the TeX proof because it proves the numerator prime is
outside `S` directly from von Staudt, before using the divisor criterion.

Required Carlitz-facing wrapper:

```lean
theorem exists_numerator_prime_for_carlitz_base (S : Finset Nat) :
    ∃ M p : Nat,
      p.Prime ∧ p ≠ 2 ∧ Even M ∧ 0 < M ∧
      (∀ q, q ∈ S → q.Prime → q - 1 ∣ M) ∧
      (p : Int) ∣ (((bernoulli M : Rat) / (M : Nat) : Rat).num) ∧
      p ∉ S
```

Implementation note:

- This can use `M = irregularBase S * 2 ^ t`.
- It should be a thin wrapper around
  `exists_numerator_prime_for_constructed_m`.

Done criteria:

- The wrapper `exists_numerator_prime_for_carlitz_base` builds.
- The wrapper does not mention `positiveResidueModSubOne` or Kummer
  congruence; it only repackages `exists_numerator_prime_for_constructed_m`.

### [CAR-07] Carlitz finite-set contradiction

- Status: done
- Claimer: Riccardo
- Started: 2026-05-24
- Completed: 2026-05-24
- Files:
  - `BernoulliRegular/IrregularPrimes/Infinitude.lean`

Current result:

Both the provider-shaped and theorem-target Carlitz finite-set contradictions
now build:

```lean
theorem exists_not_isRegularPrime_not_mem_carlitz_of_kummerProvider
```

```lean
theorem exists_not_isRegularPrime_not_mem_carlitz
```

The theorem-target version uses `exists_numerator_prime_for_carlitz_base` and
the `CAR-05` divisor criterion.

Goal:

Produce a non-regular prime outside every finite set using Carlitz's divisor
criterion.

Target:

```lean
theorem exists_not_isRegularPrime_not_mem_carlitz
    (S : Finset Nat) :
    ∃ p : Nat, ∃ hp : p.Prime,
      (letI : Fact p.Prime := ⟨hp⟩; ¬ IsRegularPrime p) ∧ p ∉ S
```

Proof:

1. Use `exists_numerator_prime_for_carlitz_base S` to get `M`, `p`,
   `p ∣ num(B_M/M)`, and `p ∉ S`.
2. Use `CAR-05` to infer `¬ IsRegularPrime p` from the divided Bernoulli
   numerator divisor.
3. Return `p`, `hp`, the non-regular proof, and `p ∉ S`.

Done criteria:

- This theorem no longer has a `hKummer` provider argument.
- It does not use the old Diekmann residue transport directly; that transport
  is hidden inside `CAR-05`.

### [CAR-08] Final infinitude theorem

- Status: done
- Claimer: Riccardo
- Started: 2026-05-24
- Completed: 2026-05-24
- Files:
  - `BernoulliRegular/IrregularPrimes/Infinitude.lean`
  - `BernoulliRegular/IrregularPrimes.lean`
  - `BernoulliRegular.lean`

Current result:

Both the provider-shaped Carlitz theorem and final theorem-target declaration
now build:

```lean
theorem infinite_not_isRegularPrime_carlitz_of_kummerProvider
```

```lean
theorem infinite_not_isRegularPrime
```

The final theorem depends on the full-Kummer theorem from `CAR-03`, which is
now proved by the CAR-11 elementary Voronoi route rather than by `sorry`.

Target:

```lean
theorem infinite_not_isRegularPrime :
    Set.Infinite
      {p : Nat | ∃ hp : p.Prime,
        letI : Fact p.Prime := ⟨hp⟩
        ¬ IsRegularPrime p}
```

Proof:

1. Use `infinite_of_forall_finite_set_not_cover`.
2. Given finite `S`, apply `exists_not_isRegularPrime_not_mem_carlitz S`.
3. Contradict the finite-cover assumption with the returned `p ∉ S`.

Done criteria:

- `lake build BernoulliRegular.IrregularPrimes` succeeds.
- `#print axioms BernoulliRegular.infinite_not_isRegularPrime` reports
  only standard Lean axioms such as
  `[propext, Classical.choice, Quot.sound]`.
- No theorem in the proof path uses a packaged Kummer-congruence assumption;
  the source theorem is the concrete Bernoulli congruence declaration
  `bernoulli_div_sModEq_of_modEq_full`.

### [CAR-09] Documentation after proof

- Status: done
- Claimer: Riccardo
- Started: 2026-05-24
- Completed: 2026-05-24
- Files:
  - `README.md`
  - optional `docs/carlitz-irregular-primes.md`
  - optional blueprint appendix

Tasks:

- After `CAR-08` is done, document that the theorem follows by Carlitz's
  elementary Bernoulli proof, with the current full-Kummer congruence source
  still represented by `sorryAx`.
- Cite:
  - L. Carlitz, "Note on irregular primes", Proc. Amer. Math. Soc. 5 (1954),
    329-331.
  - F. Luca, J. Pizarro-Madariaga, and C. Pomerance, "On the counting function
    of irregular primes", Indag. Math. 26 (2015), 147-161.
  - Ireland-Rosen, Chapter 15.
- Do not update the README as if infinitude is proved until `CAR-08` is
  actually complete.

Result:

The README now documents the Carlitz assembly and the CAR-11 elementary proof
of `bernoulli_div_sModEq_of_modEq_full` from
von Staudt-Clausen/Faulhaber/Voronoi congruences.

### [CAR-10] Replace the full-Kummer source `sorry` by a concrete proof

- Status: done
- Claimer: Riccardo
- Started: 2026-05-25
- Completed: 2026-05-25
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - possible split under `BernoulliRegular/IrregularPrimes/Kummer/`
  - `BernoulliRegular/IrregularPrimes/bernoulli_congruences_irregular_primes.tex`

Goal:

Replace the only remaining mathematical source `sorry`:

```lean
theorem bernoulli_div_sModEq_of_modEq_full
    {p m n : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm_even : Even m) (hn_even : Even n)
    (hnot : ¬ (p - 1) ∣ n)
    (hmn : m ≡ n [MOD p - 1]) :
    ∃ z : ℤ_[p],
      (((bernoulli m : Rat) / (m : Nat) : Rat) : ℚ_[p]) -
        (((bernoulli n : Rat) / (n : Nat) : Rat) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p])
```

Source note:

- `bernoulli_congruences_irregular_primes.tex`, Section 2.2, identifies this
  exact side-condition-free Kummer congruence as the essential input.
- Section 3 isolates the concrete comparison
  `B_(p*r+1) ≡ B_(r+1)/(r+1) (mod p)` for odd `r`.
- Section 4 uses the congruence to move an arbitrary divided-Bernoulli
  numerator divisor into the irregular range.

Source audit:

- The TeX note proves the Carlitz infinitude argument assuming the
  unrestricted Kummer congruence.  It does not contain an independent proof of
  `bernoulli_div_sModEq_of_modEq_full`: the abstract says the proof assumes
  "von Staudt--Clausen and the unrestricted Kummer congruence for `B_m/m`",
  Section 2.2 labels Kummer as "the essential congruence input", and the
  dependency summary lists it under "Input theorems".
- Therefore this ticket still must supply Kummer from concrete Bernoulli
  congruences/Faulhaber/Voronoi/finite-difference work.  Re-stating the TeX
  theorem as a Lean hypothesis, structure field, typeclass, opaque `Prop`, or
  wrapper theorem would violate the project proof-source rule.

Strategy:

Do not re-assume the TeX note's Kummer input.  Formalize it from concrete
Bernoulli-number congruences.  The preferred path is:

1. Prove an axiom-clean p-integrality package for divided Bernoulli numbers,
   including the Adams cancellation needed when `p ∣ k`.
2. Prove the first-order Kummer finite-difference step
   `B_(k+p-1)/(k+p-1) ≡ B_k/k (mod p)` on a nonzero even residue class.
3. Chain the first-order step along the common residue class modulo `p - 1`.
4. Use the resulting theorem to replace the body of
   `bernoulli_div_sModEq_of_modEq_full`.

Existing reductions to preserve as checks or alternate assembly lemmas:

- `teichmullerCharQp_pow_pred_eq_of_modEq`;
- `bernoulli_div_sModEq_of_modEq_of_teichmullerBridge`;
- `bernoulliGen_teichmuller_pow_sModEq_bernoulli_lift`;
- `bernoulliGen_teichmuller_pow_sModEq_div_of_liftComparison`;
- `bernoulli_div_sModEq_of_modEq_full_of_liftComparison`;
- `bernoulli_pr_plus_one_sModEq_div_of_kummerCongruence`, as an audit
  theorem only, not as a source for the new proof.

Forbidden shortcuts:

- Do not prove the theorem by adding a new Kummer provider hypothesis.
- Do not hide Kummer behind an opaque `Prop`, structure field, typeclass,
  constructor, or renamed package.
- Do not use `bernoulli_div_sModEq_of_modEq_full`,
  `bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd`, or
  `adams_bernoulli_dvd_of_prime_power_dvd_index` as source facts while proving
  their axiom-clean replacements; the current versions are downstream of the
  `sorry`.
- Do not rely on p-adic `L`-function interpolation, class field theory,
  Chebotarev, reciprocity, class groups, cyclotomic units, or regulators.

Done criteria:

- `bernoulli_div_sModEq_of_modEq_full` has no `sorry`.
- `lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull` succeeds.
- `lake build BernoulliRegular.IrregularPrimes` succeeds.
- `#print axioms BernoulliRegular.bernoulli_div_sModEq_of_modEq_full` has no
  `sorryAx`.
- `#print axioms BernoulliRegular.infinite_not_isRegularPrime` improves by
  removing `sorryAx`.

Result:

- Completed via the CAR-11 elementary Voronoi route:
  von Staudt-Clausen/Faulhaber -> strong Voronoi -> full Kummer -> Carlitz.
- `bernoulli_div_sModEq_of_modEq_full` has no `sorry` and reports only
  `[propext, Classical.choice, Quot.sound]`.
- `infinite_not_isRegularPrime` reports only
  `[propext, Classical.choice, Quot.sound]` after rebuilding the
  `BernoulliRegular.IrregularPrimes` layer.

#### [CAR-10a] Freeze the non-circular target interfaces

- Status: done
- Claimer: Riccardo
- Started: 2026-05-25
- Completed: 2026-05-25
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`

Goal:

Separate the source theorem currently represented by `sorry` from the helper
interfaces that will prove it.  This ticket is bookkeeping plus small Lean
infrastructure; it should not attempt the hard congruence.

Add or reserve theorem interfaces in dependency order:

```lean
theorem bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd_clean
    {p k : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hk_pos : 0 < k) (hk_even : Even k)
    (hnot : ¬ (p - 1) ∣ k) :
    ∃ z : ℤ_[p],
      (((bernoulli k : Rat) / (k : Nat) : Rat) : ℚ_[p]) = (z : ℚ_[p])
```

```lean
theorem kummer_firstStep_bernoulli_div
    {p k : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hk_pos : 0 < k) (hk_even : Even k)
    (hnot : ¬ (p - 1) ∣ k) :
    ∃ z : ℤ_[p],
      (((bernoulli (k + (p - 1)) : Rat) /
          (k + (p - 1) : Nat) : Rat) : ℚ_[p]) -
        (((bernoulli k : Rat) / (k : Nat) : Rat) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p])
```

```lean
theorem bernoulli_div_sModEq_of_modEq_full_clean
    {p m n : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm_even : Even m) (hn_even : Even n)
    (hnot : ¬ (p - 1) ∣ n)
    (hmn : m ≡ n [MOD p - 1]) :
    ∃ z : ℤ_[p],
      (((bernoulli m : Rat) / (m : Nat) : Rat) : ℚ_[p]) -
        (((bernoulli n : Rat) / (n : Nat) : Rat) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p])
```

Implementation notes:

- If the file becomes too large, introduce
  `BernoulliRegular/IrregularPrimes/Kummer/Basic.lean`,
  `PowerSums.lean`, `Adams.lean`, `FiniteDifference.lean`, and `Full.lean`.
- If new Lean files are added, update `BernoulliRegular.lean` and the local
  irregular-primes umbrella import in the same change.
- Keep the current sorried theorem name unchanged until the final replacement;
  use `_clean` names only to prevent accidental circular imports during work.

Audit tasks:

- Run `#print axioms` on every new `_clean` theorem as soon as it builds.
- Check with `rg "bernoulli_div_sModEq_of_modEq_full|sorry"` that no clean
  helper imports or calls the old source theorem.
- Record in this ticket which declarations remain downstream of the old
  source theorem.

Done criteria:

- The clean interfaces are present, or the final chosen names are recorded
  here before implementation begins.
- No clean helper depends on the old `bernoulli_div_sModEq_of_modEq_full`.
- The target dependency graph is documented in comments or in this ticket.

Result:

The clean target names and dependency order are recorded above.  No Lean
stubs were added in this step, because adding theorem shells would require
new `sorry`s.  Implementation begins with the independent helpers in
`CAR-10b`.

#### [CAR-10b] Build p-adic congruence and unit bookkeeping helpers

- Status: done
- Claimer: Riccardo
- Started: 2026-05-25
- Completed: 2026-05-25
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - possible `BernoulliRegular/IrregularPrimes/Kummer/Basic.lean`

Goal:

Remove repetitive algebra from the hard proof before touching the Bernoulli
argument.  The first-order and chained Kummer proofs will repeatedly use the
same p-adic facts: closure of congruences under algebra, natural-number unit
tests, and exact extraction of the p-power from an index.

Useful helper targets:

```lean
theorem qpadic_mod_p_refl {p : Nat} {x : ℚ_[p]} :
    ∃ z : ℤ_[p], x - x = (p : ℚ_[p]) * (z : ℚ_[p])
```

```lean
theorem qpadic_mod_p_trans {p : Nat} {x y z : ℚ_[p]}
    (hxy : ∃ w : ℤ_[p], x - y = (p : ℚ_[p]) * (w : ℚ_[p]))
    (hyz : ∃ w : ℤ_[p], y - z = (p : ℚ_[p]) * (w : ℚ_[p])) :
    ∃ w : ℤ_[p], x - z = (p : ℚ_[p]) * (w : ℚ_[p])
```

```lean
theorem qpadic_mod_p_symm {p : Nat} {x y : ℚ_[p]}
    (hxy : ∃ w : ℤ_[p], x - y = (p : ℚ_[p]) * (w : ℚ_[p])) :
    ∃ w : ℤ_[p], y - x = (p : ℚ_[p]) * (w : ℚ_[p])
```

```lean
theorem padicInt_natCast_isUnit_of_not_dvd
    {p n : Nat} [Fact p.Prime] (h : ¬ p ∣ n) :
    IsUnit ((n : Nat) : ℤ_[p])
```

```lean
theorem nat_eq_primePow_factorization_mul_unitPart
    {p n : Nat} (hn : n ≠ 0) :
    n = p ^ n.factorization p * (n / p ^ n.factorization p)
```

```lean
theorem prime_not_dvd_factorization_unitPart
    {p n : Nat} (hp : p.Prime) (hn : n ≠ 0) :
    ¬ p ∣ n / p ^ n.factorization p
```

Implementation notes:

- Prefer existing mathlib facts around `Nat.factorization`,
  `Nat.ordProj_mul_ordCompl_eq_self`, and `Nat.coprime_ordCompl`.
- Keep these helpers independent of Bernoulli numbers.
- Use the current witness shape
  `∃ z : ℤ_[p], x - y = p * z`; do not introduce a new public congruence
  relation unless it materially reduces proof size.

Done criteria:

- The helper lemmas build without importing the sorried theorem.
- The helpers cover:
  - reflexivity, symmetry, transitivity;
  - adding and subtracting congruences;
  - multiplying a congruence by a `ℤ_[p]` element;
  - natural p-unit construction from `¬ p ∣ n`;
  - exact p-power/unit decomposition of a positive natural.

Result:

Added the independent helper layer in `KummerCongruenceFull.lean`:

- `qpadic_mod_p_refl`;
- `qpadic_mod_p_symm`;
- `qpadic_mod_p_trans`;
- `qpadic_mod_p_add`;
- `qpadic_mod_p_sub`;
- `qpadic_mod_p_mul_padicInt`;
- `qpadic_mod_p_padicInt_mul`;
- `padicInt_natCast_isUnit_of_not_dvd`;
- `nat_eq_primePow_factorization_mul_unitPart`;
- `prime_not_dvd_factorization_unitPart`;
- `padicInt_factorization_unitPart_isUnit`;
- `qpadic_natCast_eq_primePow_mul_unitPart`.

Verification:

```bash
lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull
```

Axiom smoke checks for representative helpers:

```lean
#print axioms BernoulliRegular.qpadic_mod_p_trans
#print axioms BernoulliRegular.padicInt_natCast_isUnit_of_not_dvd
#print axioms BernoulliRegular.qpadic_natCast_eq_primePow_mul_unitPart
```

Each reports only `[propext, Classical.choice, Quot.sound]`.

#### [CAR-10c] Prove Adams integrality without Kummer

- Status: in_progress
- Claimer: Riccardo
- Started: 2026-05-25
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - possible `BernoulliRegular/IrregularPrimes/Kummer/Adams.lean`

Goal:

Replace the current Kummer-dependent divided-integrality theorem by an
axiom-clean proof.  This is needed because the full Kummer statement asserts
that both divided Bernoulli numbers are p-integral even when `p ∣ m` or
`p ∣ n`.

Target declarations:

```lean
theorem adams_bernoulli_dvd_of_prime_power_dvd_index_clean
    {p k r : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hk_pos : 0 < k) (hk_even : Even k) (hr_pos : 0 < r)
    (hpr : p ^ r ∣ k) (hnot : ¬ (p - 1) ∣ k) :
    ∃ z : ℤ_[p],
      ((bernoulli k : Rat) : ℚ_[p]) =
        (p : ℚ_[p]) ^ r * (z : ℚ_[p])
```

```lean
theorem bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd_clean
    {p k : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hk_pos : 0 < k) (hk_even : Even k)
    (hnot : ¬ (p - 1) ∣ k) :
    ∃ z : ℤ_[p],
      (((bernoulli k : Rat) / (k : Nat) : Rat) : ℚ_[p]) = (z : ℚ_[p])
```

Proof strategy:

1. Write `k = p^s * u`, where `s = k.factorization p` and `p ∤ u`.
2. If `s = 0`, combine `bernoulli_mem_padicInt_vonStaudt_of_not_sub_one_dvd`
   with the p-unit inverse of `u = k`.
3. If `s > 0`, prove the Adams divisibility target
   `B_k ∈ p^s ℤ_[p]`; then divide only by the p-unit `u`.
4. Prove Adams divisibility from a finite-difference/Faulhaber induction, not
   from Kummer:
   - use `sum_range_pow_sub_p_mul_bernoulli_weighted` as the denominator-free
     Faulhaber identity;
   - use `p_mul_bernoulli_mem_padicInt_vonStaudt` for lower Bernoulli terms;
   - keep the boundary correction from von Staudt explicit, so the proof does
     not need `(p - 1) ∤ j` for lower indices;
   - when the induction meets `j` with a positive p-adic factor in the index,
     use the induction hypothesis to supply the extra p-power cancellation.

Cycle audit:

- This ticket may depend on CAR-10b.
- It may use von Staudt-Clausen consequences and Faulhaber identities.
- It must not use:
  - `bernoulli_div_sModEq_of_modEq_full`;
  - `bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd`;
  - `adams_bernoulli_dvd_of_prime_power_dvd_index`;
  - `kummer_firstStep_bernoulli_div`;
  - any theorem proved later in CAR-10.

Done criteria:

- Both clean Adams/divided-integrality theorems build.
- `#print axioms` for both does not contain `sorryAx`.
- The final proof explicitly records where the p-power in `k` is cancelled.

Progress:

- Added the p-unit subcase
  `bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd_of_not_dvd`.
  This proves `B_k / k ∈ ℤ_[p]` from von Staudt whenever
  `(p - 1) ∤ k` and `p ∤ k`.
- Added the algebraic Adams-exact reduction
  `bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd_of_adams_exact`.
  It proves `B_k / k ∈ ℤ_[p]` from a supplied witness
  `B_k ∈ p ^ k.factorization p * ℤ_[p]`, by dividing only by the p-unit
  part `k / p ^ k.factorization p`.
- Verified:

  ```bash
  lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull
  ```

- Axiom check:

  ```lean
  #print axioms BernoulliRegular.bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd_of_not_dvd
  #print axioms BernoulliRegular.bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd_of_adams_exact
  ```

  both report only `[propext, Classical.choice, Quot.sound]`.

Remaining:

- The hard Adams case is exactly `p ∣ k`, where the p-power in the denominator
  must be cancelled by a matching p-power in `B_k`.

#### [CAR-10d] Prove the first-order Kummer finite-difference step

- Status: todo
- Claimer: Riccardo
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - possible `BernoulliRegular/IrregularPrimes/Kummer/FiniteDifference.lean`

Goal:

Formalize the actual Bernoulli-congruence input behind the TeX note's
unrestricted Kummer theorem.  It is enough to prove the first-order step on a
single nonzero residue class:

```lean
theorem kummer_firstStep_bernoulli_div
    {p k : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hk_pos : 0 < k) (hk_even : Even k)
    (hnot : ¬ (p - 1) ∣ k) :
    ∃ z : ℤ_[p],
      (((bernoulli (k + (p - 1)) : Rat) /
          (k + (p - 1) : Nat) : Rat) : ℚ_[p]) -
        (((bernoulli k : Rat) / (k : Nat) : Rat) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p])
```

Preferred proof route:

1. Prove the cleared congruence first:

   ```lean
   theorem kummer_firstStep_cleared
       {p k : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
       (hk_pos : 0 < k) (hk_even : Even k)
       (hnot : ¬ (p - 1) ∣ k) :
       ∃ z : ℤ_[p],
         ((k + (p - 1) : Nat) : ℚ_[p]) *
             ((bernoulli k : Rat) : ℚ_[p]) -
           ((k : Nat) : ℚ_[p]) *
             ((bernoulli (k + (p - 1)) : Rat) : ℚ_[p]) =
         (p : ℚ_[p]) * ((k : Nat) : ℚ_[p]) *
           (((k + (p - 1) : Nat) : ℚ_[p])) * (z : ℚ_[p])
   ```

   The cleared statement makes every division auditable.  If the displayed
   formulation is too strict, replace it by an equivalent statement using the
   exact p-power decompositions from CAR-10b and the Adams cancellation from
   CAR-10c.

2. Prove the cleared statement by the standard finite-difference form of
   Kummer's congruence:

   ```lean
   theorem kummer_finiteDifference_order_one
       {p h : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
       (hh_pos : 0 < h) (hh_even : Even h)
       (hnot : ¬ (p - 1) ∣ h) :
       ∃ z : ℤ_[p],
         (((bernoulli (h + (p - 1)) : Rat) /
             (h + (p - 1) : Nat) : Rat) : ℚ_[p]) -
           (((bernoulli h : Rat) / (h : Nat) : Rat) : ℚ_[p]) =
         (p : ℚ_[p]) * (z : ℚ_[p])
   ```

   This theorem may use Faulhaber and finite-field power sums, but it must be
   proved directly from concrete sums.  A useful intermediate is the
   finite-difference identity

   ```text
   Δ(a ↦ a^h) over the nonzero residues of `ZMod p`
   ```

   together with the fact that `a^(p-1) ≡ 1 (mod p)` for nonzero residues.

3. Use CAR-10c to divide by any p-power in `k` or `k + (p - 1)`.  The final
   division step must divide only by p-units; nonunit p-powers must already
   have been cancelled in the cleared congruence.

Implementation notes:

- Start with the first-order case only; do not try to prove the full
  higher-order Kummer finite-difference theorem unless the first-order proof
  naturally generalizes.
- Existing `sum_range_pow_sub_p_mul_bernoulli_weighted` is the right
  denominator-free Faulhaber primitive.  It avoids the false side condition
  `p ∤ t + 1`.
- Existing Voronoi theorems may be used as local algebraic identities only if
  their hypotheses are fully discharged.  They cannot be used as the final
  source if they still require `p ∤ k`, `p ∤ k + 1`, or bounded
  `p^3` assumptions.

Done criteria:

- `kummer_firstStep_bernoulli_div` builds.
- The proof handles all cases:
  - `p ∤ k`;
  - `p ∣ k`;
  - `p ∤ k + (p - 1)`;
  - `p ∣ k + (p - 1)`.
- The ticket includes a short proof audit listing every division and the
  corresponding p-unit or Adams cancellation.

#### [CAR-10e] Chain the first-order step to the full congruence

- Status: todo
- Claimer: Riccardo
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - possible `BernoulliRegular/IrregularPrimes/Kummer/Full.lean`

Goal:

Turn the first-order step from CAR-10d into the full theorem shape.  This is
mostly modular arithmetic and induction, not new Bernoulli mathematics.

Target:

```lean
theorem bernoulli_div_sModEq_of_modEq_full_clean
    {p m n : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm_even : Even m) (hn_even : Even n)
    (hnot : ¬ (p - 1) ∣ n)
    (hmn : m ≡ n [MOD p - 1]) :
    ∃ z : ℤ_[p],
      (((bernoulli m : Rat) / (m : Nat) : Rat) : ℚ_[p]) -
        (((bernoulli n : Rat) / (n : Nat) : Rat) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p])
```

Proof plan:

1. Derive `¬ (p - 1) ∣ m` from `hnot` and `hmn`.
2. Let `r = m % (p - 1)`.  Prove:
   - `0 < r`;
   - `r < p - 1`;
   - `Even r`;
   - `m ≡ r [MOD p - 1]`;
   - `n ≡ r [MOD p - 1]`.
3. Prove a chain lemma:

   ```lean
   theorem kummer_chain_from_residue
       {p r a : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
       (hr_pos : 0 < r) (hr_even : Even r)
       (hnot : ¬ (p - 1) ∣ r) :
       ∃ z : ℤ_[p],
         (((bernoulli (r + a * (p - 1)) : Rat) /
             (r + a * (p - 1) : Nat) : Rat) : ℚ_[p]) -
           (((bernoulli r : Rat) / (r : Nat) : Rat) : ℚ_[p]) =
         (p : ℚ_[p]) * (z : ℚ_[p])
   ```

   Prove it by induction on `a`, using `kummer_firstStep_bernoulli_div` at
   the index `r + a * (p - 1)`.

4. Express `m` and `n` as `r + a * (p - 1)` and `r + b * (p - 1)`.
5. Compare each divided Bernoulli number to the residue representative and
   combine the two congruences by transitivity and symmetry.

Implementation notes:

- Reuse `positiveResidueModSubOne` and `positiveResidue_properties` if the
  import graph stays clean.  Otherwise prove a local residue lemma in the new
  Kummer file to avoid importing the infinitude layer.
- The first-order step preserves the non-boundary condition because adding
  `p - 1` does not change the residue modulo `p - 1`.
- When `p = 3`, no positive even non-boundary residue exists; the assumptions
  should make this case contradictory.  Record the exact `omega`/divisibility
  lemma used to close it.

Done criteria:

- `bernoulli_div_sModEq_of_modEq_full_clean` builds from
  `kummer_firstStep_bernoulli_div`.
- The proof does not use finite-character bridge theorems or the old Voronoi
  side-conditioned Kummer theorem.
- `#print axioms` contains no `sorryAx`.

#### [CAR-10f] Prove the TeX `pr+1` comparison as a checkpoint

- Status: todo
- Claimer: Riccardo
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`

Goal:

Formalize Proposition 3 of
`bernoulli_congruences_irregular_primes.tex` as a direct consequence of the
clean first-order/chained Kummer proof.  This theorem is not the source of
Kummer; it is a checkpoint that the Lean proof matches the TeX note.

Target:

```lean
theorem bernoulli_pr_plus_one_sModEq_div_clean
    {p r : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hr_odd : Odd r) (hr_pos : 0 < r)
    (hnot : ¬ (p - 1) ∣ r + 1) :
    ∃ z : ℤ_[p],
      (((bernoulli (p * r + 1) : Rat) : ℚ_[p])) -
          (((bernoulli (r + 1) : Rat) / (r + 1 : Nat) : Rat) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p])
```

Proof plan:

1. Set `m = p * r + 1` and `n = r + 1`.
2. Prove `m` and `n` are positive even.
3. Prove `m ≡ n [MOD p - 1]` using `p ≡ 1 [MOD p - 1]`.
4. Apply `bernoulli_div_sModEq_of_modEq_full_clean` to get
   `B_m/m ≡ B_n/n`.
5. Prove `p ∤ m` since `m = p*r + 1`, so `m` is a p-unit in `ℤ_[p]`.
6. Use `m = 1 + p*r` to show
   `B_m - B_m/m ∈ p ℤ_[p]`, using
   `bernoulli_mem_padicInt_vonStaudt_of_not_sub_one_dvd` for `B_m`.
7. Combine the two congruences.

Audit:

- This theorem may use the clean full theorem from CAR-10e.
- It must not use the old provider theorem
  `bernoulli_pr_plus_one_sModEq_div_of_kummerCongruence` except as a shape
  reference.
- It should be used to validate the TeX Section 3 comparison and the existing
  finite-character reductions.

Done criteria:

- The checkpoint theorem builds.
- The proof matches the seven-step TeX argument, with all p-integrality
  side conditions explicit.

#### [CAR-10g] Replace the old source theorem and update downstream helpers

- Status: todo
- Claimer: Riccardo
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - possible split files under `BernoulliRegular/IrregularPrimes/Kummer/`

Goal:

Make `bernoulli_div_sModEq_of_modEq_full` itself use the clean proof, and
remove the local `sorry`.

Tasks:

- Replace the body of `bernoulli_div_sModEq_of_modEq_full` with a call to
  `bernoulli_div_sModEq_of_modEq_full_clean`, or rename the clean theorem into
  the public theorem name.
- Remove `set_option warn.sorry false` around the target theorem.
- Rework `bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd` so it uses
  `bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd_clean`, not the full
  Kummer theorem.
- Rework `adams_bernoulli_dvd_of_prime_power_dvd_index` so it uses the clean
  Adams theorem, not the divided-integrality theorem if that would reintroduce
  a cycle.
- Keep old reduction theorems as audits when useful, but make sure they are no
  longer the only route to the public theorem.

Done criteria:

- `rg -n "sorry|warn.sorry" BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  finds no local source `sorry`.
- `lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull` succeeds.
- `#print axioms BernoulliRegular.bernoulli_div_sModEq_of_modEq_full` has no
  `sorryAx`.

#### [CAR-10h] Final axiom and Carlitz-route audit

- Status: todo
- Claimer: Riccardo
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - `BernoulliRegular/IrregularPrimes/Infinitude.lean`
  - `BernoulliRegular/IrregularPrimes/tickets.md`
  - `README.md`

Goal:

Verify that replacing the full-Kummer source theorem removes the only
nonstandard axiom from the Carlitz infinitude proof path.

Commands:

```bash
lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull
lake build BernoulliRegular.IrregularPrimes
lake build
```

Axiom checks:

```lean
#print axioms BernoulliRegular.bernoulli_div_sModEq_of_modEq_full
#print axioms BernoulliRegular.not_isRegularPrime_iff_exists_dvd_bernoulli_div_self_num
#print axioms BernoulliRegular.exists_not_isRegularPrime_not_mem_carlitz
#print axioms BernoulliRegular.infinite_not_isRegularPrime
```

Expected result:

- The Kummer theorem reports only standard Lean/mathlib axioms such as
  `propext`, `Classical.choice`, and `Quot.sound`.
- The final infinitude theorem no longer reports `sorryAx`.

Documentation tasks:

- Update this ticket with the final declaration path from vSC/Faulhaber to
  Kummer to Carlitz.
- Update `README.md` so it no longer says the final theorem depends on the
  sorried full-Kummer congruence.
- If new split files were added, document their purpose in the ticket result.

Done criteria:

- Full build succeeds.
- Axiom checks show `sorryAx` has been removed.
- The README and ticket board accurately describe the proof as axiom-clean.

### [CAR-11] Implement the elementary Voronoi proof from `bernoulli_kummer_congruences_proof.tex`

- Status: done
- Claimer: Riccardo
- Started: 2026-05-25
- Completed: 2026-05-25
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - possible split under `BernoulliRegular/IrregularPrimes/Kummer/`
  - `BernoulliRegular/IrregularPrimes/bernoulli_kummer_congruences_proof.tex`

Goal:

Use `bernoulli_kummer_congruences_proof.tex` as the active source strategy for
removing the `sorry` in `bernoulli_div_sModEq_of_modEq_full`.

The TeX route is stronger and more direct than the earlier CAR-10d/CAR-10e
first-step-chain plan:

```text
Faulhaber + von Staudt denominator bound
  -> strong power-sum congruence modulo h*p^2
  -> Voronoi congruence without p∤h or p∤(h+1)
  -> unrestricted Kummer congruence
  -> pr+1 comparison
  -> public theorem replacement and axiom audit
```

This route still may reuse CAR-10b bookkeeping helpers and CAR-10c algebraic
integrality reductions, but it should not depend on the old sorried Kummer
source or on a packaged Kummer provider.

Proof-source audit:

- The TeX proof is elementary: it uses Faulhaber, von Staudt-Clausen
  denominator bounds, binomial expansion, permutation of nonzero residues, and
  cyclicity of `(ZMod p)ˣ`.
- The TeX proof is stated for `p ≥ 5`; the Lean public theorem assumes only
  `p ≠ 2`.  The case `p = 3` must be closed separately because every positive
  even `n` is divisible by `p - 1 = 2`, contradicting the non-boundary
  hypothesis.
- The key improvement over the current Lean Voronoi theorem is the stronger
  modulus `h*p^2`.  This is exactly what removes the old side conditions
  `p ∤ h` and `p ∤ h + 1`.

Forbidden shortcuts:

- Do not use `bernoulli_div_sModEq_of_modEq_full`,
  `bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd`, or
  `adams_bernoulli_dvd_of_prime_power_dvd_index` as source facts in this
  route.
- Do not repackage the TeX theorem as an assumption, typeclass, structure
  field, opaque `Prop`, or renamed theorem.
- Do not prove only the old side-conditioned Voronoi/Kummer statement and call
  it unrestricted.

Result:

- Completed CAR-11a through CAR-11j in
  `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`.
- The route proves `bernoulli_div_sModEq_of_modEq_full` from concrete
  von Staudt-Clausen, Faulhaber, strong Voronoi, primitive-root, and p-adic
  unit arguments.
- The public Carlitz endpoint `infinite_not_isRegularPrime` now reports only
  `[propext, Classical.choice, Quot.sound]`.

#### [CAR-11a] Normalize the TeX hypotheses and p-adic witness shape

- Status: done
- Claimer: Riccardo
- Started: 2026-05-25
- Completed: 2026-05-25
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - possible `BernoulliRegular/IrregularPrimes/Kummer/Basic.lean`

Goal:

Add the small arithmetic and notation bridge needed before formalizing the
TeX proof.

Target helper declarations:

```lean
theorem five_le_of_odd_prime_and_even_nonboundary
    {p n : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hn_even : Even n) (hnot : ¬ (p - 1) ∣ n) :
    5 ≤ p
```

```lean
theorem range_pow_sum_eq_Icc_one_sub_one
    {p h : Nat} [Fact p.Prime] (hh_pos : 0 < h) :
    (∑ x ∈ Finset.range p, (x : ℚ_[p]) ^ h) =
      ∑ x ∈ Finset.Icc 1 (p - 1), (x : ℚ_[p]) ^ h
```

The exact second helper may be replaced by a simpler local lemma if the proof
uses `Finset.range p` throughout.  The point is to choose one canonical sum
shape and avoid repeated `0^h` bookkeeping.

Implementation notes:

- The public theorem uses the witness shape
  `∃ z : ℤ_[p], x - y = (p : ℚ_[p]) * (z : ℚ_[p])`.
- The strong congruences below use the stronger witness shape
  `∃ z : ℤ_[p], X = (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p])`.
- Keep these as explicit equations in `ℚ_[p]`; do not introduce a new opaque
  congruence relation.

Done criteria:

- The helper lemmas build.
- The `p = 3` contradiction needed by the public theorem is available without
  using Kummer.
- A ticket note records the chosen power-sum indexing convention.

Result:

- Added `five_le_of_odd_prime_and_even_nonboundary`, closing the `p = 3`
  public-theorem edge case from parity and the non-boundary hypothesis.
- Added `range_pow_sum_eq_Icc_one_sub_one`.
- Chosen indexing convention: later CAR-11 power-sum and Voronoi lemmas should
  use `Finset.range p` as the canonical sum shape, with this helper available
  only when matching the TeX `1 ≤ x ≤ p - 1` presentation.

Verification:

```bash
lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull
```

Axiom smoke checks:

```lean
#print axioms BernoulliRegular.five_le_of_odd_prime_and_even_nonboundary
#print axioms BernoulliRegular.range_pow_sum_eq_Icc_one_sub_one
```

Both report only `[propext, Classical.choice, Quot.sound]`.

#### [CAR-11b] Prove the valuation bounds behind the strong modulus

- Status: done
- Claimer: Riccardo
- Started: 2026-05-25
- Completed: 2026-05-25
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - possible `BernoulliRegular/IrregularPrimes/Kummer/PowerSums.lean`

Goal:

Formalize the numerical heart of Section 2 of the TeX proof: for `p ≥ 5` and
`s ≥ 2`, the excess p-adic power in each Faulhaber term is at least `2`.

Target helper declarations:

```lean
theorem factorization_add_succ_factorization_add_two_le
    {p s : Nat} (hp_ge_five : 5 ≤ p) (hs : 2 ≤ s) :
    s.factorization p + (s + 1).factorization p + 2 ≤ s
```

```lean
theorem binomial_divisor_term_mem_h_p_sq
    {p h s : Nat} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hs_pos : 0 < s) (hs_le : s ≤ h) :
    ∃ z : ℤ_[p],
      (((Nat.choose h s : Nat) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : Nat) : ℚ_[p])) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p])
```

The second target is intentionally schematic: the implemented statement may
include the Bernoulli factor and the exact Faulhaber term instead if that is
cleaner for Lean.  It must capture the TeX inequality
`v_p(T_s) ≥ v_p(h) + 2`.

Implementation notes:

- Use `Nat.factorization` and existing p-adic unit helpers from CAR-10b.
- Split small `s = 2, 3, 4` explicitly; for `s ≥ 5`, prove the bound with
  elementary inequalities as in the TeX note.
- Keep all divisions audited: denominators not divisible by `p` become
  `ℤ_[p]` units; denominators divisible by `p` must be accounted for by the
  factorization inequality.

Done criteria:

- The valuation helper layer builds without Bernoulli/Kummer dependencies
  except for optional p-adic unit coercion lemmas.
- The ticket result records the exact final Lean statement used by the
  strong Faulhaber proof.

Result:

- Added the core numerical inequality
  `factorization_add_succ_factorization_add_two_le` with an explicit
  `[Fact p.Prime]` hypothesis:

  ```lean
  theorem factorization_add_succ_factorization_add_two_le
      {p s : Nat} [Fact p.Prime] (hp_ge_five : 5 ≤ p) (hs : 2 ≤ s) :
      s.factorization p + (s + 1).factorization p + 2 ≤ s
  ```

- Added the direct p-power divisibility corollary
  `primePow_factorization_add_succ_add_two_dvd_primePow`, which is the form
  intended for the strong Faulhaber term divisibility proof.
- Added the p-adic denominator-clearing helper
  `qpadic_natCast_div_natCast_eq_primePow_mul_of_primePow_dvd`: if a natural
  numerator has enough `p`-power to cover a natural denominator's exact
  `p`-part plus `r`, then the quotient is `p^r` times a p-adic integer.
- Added the binomial-strength p-power bound
  `primePow_succFactorization_add_indexFactorization_add_three_dvd_choose_mul_primePow`,
  combining the binomial coefficient valuation bound with the consecutive
  denominator estimate.
- Added
  `primePow_indexFactorization_add_three_mul_padicInt_eq_natCast_mul_primeSq`,
  converting a `p^(v_p(h)+3)` multiple into the strong modulus `h*p^2`.
- Added the final CAR-11b consumer lemma
  `binomial_divisor_term_mem_h_p_sq`, proving that for `2 ≤ s ≤ h` the
  divided binomial/Faulhaber coefficient is an `h*p^2` multiple in `ℚ_[p]`.
- Verified:

  ```bash
  lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull
  ```

- Axiom smoke checks for these declarations report only
  `[propext, Classical.choice, Quot.sound]`.

#### [CAR-11c] Prove the strong Faulhaber power-sum congruence

- Status: done
- Claimer: Riccardo
- Started: 2026-05-25
- Completed: 2026-05-25
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - possible `BernoulliRegular/IrregularPrimes/Kummer/PowerSums.lean`

Goal:

Formalize TeX Lemma 2.2:

```text
S_h(p) - p*B_h ∈ h*p^2*Z_(p)
```

Target declaration:

```lean
theorem sum_range_pow_sub_p_mul_bernoulli_strong
    {p h : Nat} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hh_even : Even h)
    (hnot : ¬ (p - 1) ∣ h) :
    ∃ z : ℤ_[p],
      (∑ x ∈ Finset.range p, (x : ℚ_[p]) ^ h) -
          (p : ℚ_[p]) * ((bernoulli h : ℚ) : ℚ_[p]) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p])
```

Proof plan:

1. Start from mathlib/project Faulhaber:
   `sum_range_pow_sub_p_mul_bernoulli_weighted` may be useful for orientation,
   but the strong theorem needs a new denominator analysis because it must
   produce an extra factor `h`.
2. Split the Faulhaber sum into the `j = h` term and terms `j = h - s`.
3. Handle `s = 1`:
   - if `h > 2`, use `bernoulli_eq_zero_of_odd`;
   - if `h = 2`, use `B_1 = -1/2` and `p ≥ 5` to show the term lies in
     `h*p^2*ℤ_[p]`.
4. Handle `s ≥ 2` using CAR-11b and the von Staudt denominator bound
   `p * B_j ∈ ℤ_[p]`.
5. Sum all term witnesses and subtract the `p*B_h` term.

Implementation notes:

- Existing theorem `p_mul_bernoulli_mem_padicInt_vonStaudt` is the right
  denominator input for arbitrary lower Bernoulli numbers.
- This theorem must not assume `p ∤ h` or `p ∤ h + 1`.
- Avoid proving an overly specialized statement tied to `p*n+1`; the Voronoi
  theorem needs arbitrary positive even non-boundary `h`.

Done criteria:

- `sum_range_pow_sub_p_mul_bernoulli_strong` builds.
- `#print axioms` reports no `sorryAx`.
- The proof audit records how the factor `h` appears in every Faulhaber term.

Result:

- Added the cubic coefficient form
  `binomial_divisor_term_mem_h_p_cubed`, since lower Bernoulli numbers may
  have one `p` in the denominator.
- Added `p_mul_bernoulli_mem_padicInt`, extending the existing even-index
  von Staudt consequence to all Bernoulli indices by handling `B_1` and odd
  zeroes directly.
- Added shifted-term lemmas:
  `shifted_faulhaber_one_term_mem_h_p_sq`,
  `shifted_faulhaber_term_mem_h_p_sq_of_two_le`, and
  `faulhaber_remainder_term_mem_h_p_sq`.
- Added `choose_succ_div_eq_choose_div` for the reindexing
  `i = h - s`.
- Proved the target theorem:

  ```lean
  theorem sum_range_pow_sub_p_mul_bernoulli_strong
      {p h : Nat} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
      (hh_pos : 0 < h) (hh_even : Even h)
      (_hnot : ¬ (p - 1) ∣ h) :
      ∃ z : ℤ_[p],
        (∑ x ∈ Finset.range p, (x : ℚ_[p]) ^ h) -
            (p : ℚ_[p]) * ((bernoulli h : ℚ) : ℚ_[p]) =
          (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p])
  ```

Proof audit:

- The leading Faulhaber term `i = h` is exactly `p*B_h` and is split off.
- For `s = 1`, the term is zero unless `h = 2`; in that case the remaining
  denominator is `4`, a p-adic unit because `p ≥ 5`.
- For `s ≥ 2`, CAR-11b gives the binomial/Faulhaber coefficient as an
  `h*p^3` multiple.  Multiplying by `B_{h-s}` loses at most one `p`, using
  `p*B_{h-s} ∈ ℤ_[p]`, so the term remains an `h*p^2` multiple.

Verification:

```bash
lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull
```

Axiom smoke checks for `sum_range_pow_sub_p_mul_bernoulli_strong`,
`faulhaber_remainder_term_mem_h_p_sq`, and `p_mul_bernoulli_mem_padicInt`
report only `[propext, Classical.choice, Quot.sound]`.

#### [CAR-11d] Prove the strong binomial permutation identity

- Status: done
- Claimer: Riccardo
- Started: 2026-05-25
- Completed: 2026-05-25
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - possible `BernoulliRegular/IrregularPrimes/Kummer/Voronoi.lean`

Goal:

Formalize the binomial expansion step in TeX Section 3 with modulus
`h*p^2`, not merely `p^2`.

Target declaration:

```lean
theorem voronoi_sum_mod_h_p_sq
    {p a h : Nat} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (ha_coprime : ¬ p ∣ a) (hh_pos : 0 < h) :
    ∃ W : ℤ_[p],
      ((a : ℚ_[p]) ^ h - 1) *
          (∑ x ∈ Finset.range p, (x : ℚ_[p]) ^ h) -
        (h : ℚ_[p]) * (p : ℚ_[p]) * (a : ℚ_[p]) ^ (h - 1) *
          (∑ x ∈ Finset.range p,
            (x : ℚ_[p]) ^ (h - 1) * ((x * a / p : Nat) : ℚ_[p])) =
      (h : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (W : ℚ_[p])
```

The implemented statement may differ by a sign or by moving terms across the
equality, but it must be algebraically equivalent to the boxed TeX congruence
before substituting the strong power-sum theorem.

Proof plan:

1. For each `x < p`, use
   `x * a = p * (x * a / p) + (x * a) % p`.
2. Expand `((x*a) % p)^h = (x*a - p*q)^h`.
3. Keep the order `0` and `1` terms and prove every binomial term of order
   `ν ≥ 2` lies in `h*p^2*ℤ_[p]`.
4. Sum the witnesses over `Finset.range p`.
5. Use the existing `voronoi_permutation` helper to replace the residue sum
   by the ordinary power sum.

Implementation notes:

- Existing `voronoi_sum_mod_p_sq` proves the weaker identity.  Use it as a
  shape reference, but do not call it if doing so loses the factor `h`.
- The proof does not require `h` even or non-boundary; those assumptions enter
  in the strong Faulhaber substitution.

Done criteria:

- `voronoi_sum_mod_h_p_sq` builds.
- The proof has no hypotheses `p ∤ h` or `p ∤ h + 1`.
- The ticket result records whether the final Lean identity uses `range p` or
  `Icc 1 (p - 1)`.

Result:

- Added the high-order binomial coefficient valuation layer:
  `factorization_add_two_le_self`,
  `primePow_indexFactorization_add_two_dvd_choose_mul_primePow`,
  `choose_mul_primePow_mem_h_p_sq`, and
  `binomial_high_term_mem_h_p_sq`.
- Added `voronoi_term_mod_h_p_sq`, the pointwise expansion
  `((j*a)%p)^h = (j*a)^h - h*(j*a)^(h-1)*p*(j*a/p) + h*p^2*z`.
- Proved the target summed/permuted identity
  `voronoi_sum_mod_h_p_sq`.
- Final Lean identity uses `Finset.range p`, including the zero term.  This
  matches the existing `voronoi_permutation` helper and the CAR-11c power-sum
  theorem.

Verification:

```bash
lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull
```

Axiom smoke checks for `voronoi_sum_mod_h_p_sq`,
`voronoi_term_mod_h_p_sq`, and `binomial_high_term_mem_h_p_sq` report only
`[propext, Classical.choice, Quot.sound]`.

#### [CAR-11e] Prove side-condition-free Voronoi congruence

- Status: done
- Claimer: Riccardo
- Started: 2026-05-25
- Completed: 2026-05-25
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - possible `BernoulliRegular/IrregularPrimes/Kummer/Voronoi.lean`

Goal:

Combine CAR-11c and CAR-11d to prove TeX Theorem 3.1:

```text
(a^h - 1) * B_h / h ≡
  a^(h-1) * sum floor(a*x/p) * x^(h-1) mod p
```

Target declarations:

```lean
theorem voronoi_congruence_mod_p_strong
    {p a h : Nat} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (ha_coprime : ¬ p ∣ a)
    (hh_pos : 0 < h) (hh_even : Even h)
    (hnot : ¬ (p - 1) ∣ h) :
    ∃ z : ℤ_[p],
      ((a : ℚ_[p]) ^ h - 1) *
          (((bernoulli h : ℚ) / (h : Nat) : ℚ) : ℚ_[p]) -
        (a : ℚ_[p]) ^ (h - 1) *
          (∑ x ∈ Finset.range p,
            (x : ℚ_[p]) ^ (h - 1) * ((x * a / p : Nat) : ℚ_[p])) =
      (p : ℚ_[p]) * (z : ℚ_[p])
```

```lean
theorem bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd_voronoi
    {p h : Nat} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hh_even : Even h)
    (hnot : ¬ (p - 1) ∣ h) :
    ∃ z : ℤ_[p],
      (((bernoulli h : ℚ) / (h : Nat) : ℚ) : ℚ_[p]) = (z : ℚ_[p])
```

Proof plan:

1. Substitute `S_h(p) = p*B_h + h*p^2*z` from CAR-11c into the strong
   binomial identity from CAR-11d.
2. Cancel `h*p` in `ℚ_[p]` to get the mod-`p` Voronoi statement.  This is a
   rational-field cancellation, not a p-adic-integrality division.
3. For integrality, choose `a` whose image generates `(ZMod p)ˣ`, and prove
   `a^h - 1` is a p-adic unit from `¬ (p - 1) ∣ h`.
4. Divide by that p-adic unit only.  The right-hand side sum is integral, and
   the congruence error is `p` times an integral witness.

Implementation notes:

- The integrality theorem above should replace the Kummer-dependent theorem
  `bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd` in the final route.
- Reuse existing primitive-root code from
  `bernoulli_div_sModEq_of_modEq_voronoiNoBound` where possible.
- Do not require `p ∤ h`; the TeX theorem explicitly removes this.

Done criteria:

- Both target declarations build.
- `#print axioms` for both contains no `sorryAx`.
- The proof audit lists the only divisions: cancellation by nonzero rational
  `h*p`, then inversion of the p-adic unit `a^h - 1`.

Result:

- Added `voronoi_congruence_mod_p_strong` in
  `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`, combining the
  CAR-11c strong Faulhaber congruence with the CAR-11d strong Voronoi sum and
  cancelling nonzero `p` and `h` in `ℚ_[p]`.
- Added
  `bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd_voronoi`, choosing a
  generator of `(ZMod p)ˣ`, proving `a^h - 1` is a p-adic unit from
  `¬ (p - 1) ∣ h`, and multiplying the Voronoi congruence by the inverse unit.
- Proof audit: the only field cancellation is by nonzero `(p : ℚ_[p])` and
  `(h : ℚ_[p])`; the only p-adic division is inversion of the unit
  `(a : ℤ_[p]) ^ h - 1`.  The integral witness keeps the full
  `a^(h-1)` factor multiplying the finite Voronoi sum.
- Verified with
  `lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull`.
- Axiom checks for both declarations report only
  `[propext, Classical.choice, Quot.sound]`.

#### [CAR-11f] Refactor finite-field generator congruence helpers

- Status: done
- Claimer: Riccardo
- Started: 2026-05-25
- Completed: 2026-05-25
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - possible `BernoulliRegular/IrregularPrimes/Kummer/Voronoi.lean`

Goal:

Extract the primitive-root and exponent-modulo-`p-1` bookkeeping needed to
compare the two Voronoi congruences in the final Kummer proof.

Useful helper targets:

```lean
theorem primitiveRoot_unit_pow_eq_of_modEq
    {p m n : Nat} [Fact p.Prime] {g : (ZMod p)ˣ}
    (hg_order : orderOf g = p - 1)
    (hmn : m ≡ n [MOD p - 1]) :
    g ^ m = g ^ n
```

```lean
theorem voronoi_floor_sum_sModEq_of_pred_modEq
    {p a m n : Nat} [Fact p.Prime]
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hmn : (m - 1) ≡ (n - 1) [MOD p - 1]) :
    ∃ z : ℤ_[p],
      (∑ x ∈ Finset.range p,
        (x : ℚ_[p]) ^ (m - 1) * ((x * a / p : Nat) : ℚ_[p])) -
      (∑ x ∈ Finset.range p,
        (x : ℚ_[p]) ^ (n - 1) * ((x * a / p : Nat) : ℚ_[p])) =
      (p : ℚ_[p]) * (z : ℚ_[p])
```

The exact generator statement may use the existing pattern:

```lean
obtain ⟨g, hg_gen⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
set a : Nat := (g : ZMod p).val
```

Implementation notes:

- Existing code in `bernoulli_div_sModEq_of_modEq_voronoiNoBound` already
  proves most of these facts locally.  Move or duplicate only the parts needed
  for the new side-condition-free Kummer proof.
- Keep helpers independent of Bernoulli numbers where possible.

Done criteria:

- The finite-field congruence helpers build.
- The future Kummer proof can cite them instead of copying large local blocks.

Result:

- Added `primitiveRoot_unit_pow_eq_of_modEq` for powers of a unit generator
  whose order is identified with `p - 1`.
- Added `voronoi_floor_sum_sModEq_of_pred_modEq`, proving that the two
  Voronoi floor sums differ by `p` times a p-adic integer whenever the
  predecessor exponents are congruent modulo `p - 1`.
- Verified with
  `lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull`.
- Axiom checks for both helper declarations report only
  `[propext, Classical.choice, Quot.sound]`.

#### [CAR-11g] Prove unrestricted Kummer for `p ≥ 5`

- Status: done
- Claimer: Riccardo
- Started: 2026-05-25
- Completed: 2026-05-25
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - possible `BernoulliRegular/IrregularPrimes/Kummer/Full.lean`

Goal:

Formalize TeX Theorem 4.1 for primes `p ≥ 5`.

Target declaration:

```lean
theorem bernoulli_div_sModEq_of_modEq_full_geFive
    {p m n : Nat} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm_even : Even m) (hn_even : Even n)
    (hnot : ¬ (p - 1) ∣ n)
    (hmn : m ≡ n [MOD p - 1]) :
    ∃ z : ℤ_[p],
      (((bernoulli m : ℚ) / (m : Nat) : ℚ) : ℚ_[p]) -
        (((bernoulli n : ℚ) / (n : Nat) : ℚ) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p])
```

Proof plan:

1. Derive `¬ (p - 1) ∣ m` from `hnot` and `hmn`.
2. Choose a generator `a` of `(ZMod p)ˣ`.
3. Prove `(a^m - 1)` and `(a^n - 1)` are p-adic units, because neither
   exponent is divisible by `p - 1`.
4. Apply `voronoi_congruence_mod_p_strong` to both `m` and `n`.
5. Use `m ≡ n [MOD p - 1]` to show:
   - `a^m ≡ a^n mod p`;
   - `a^(m-1) ≡ a^(n-1) mod p`;
   - each `x^(m-1)` and `x^(n-1)` term agrees modulo `p`.
6. Subtract the two Voronoi congruences and divide by the common p-adic unit
   represented by `a^m - 1 ≡ a^n - 1`.
7. Combine the integrality witnesses from CAR-11e so every congruence
   multiplication is by p-adic integers.

Implementation notes:

- This proof should be structurally similar to
  `bernoulli_div_sModEq_of_modEq_voronoiNoBound`, but the hypotheses
  `p ∤ m`, `p ∤ n`, `p ∤ m+1`, and `p ∤ n+1` must be absent.
- If algebra becomes large, first prove an abstract lemma comparing two
  Voronoi congruence equations with equal unit coefficients modulo `p`.

Done criteria:

- The `p ≥ 5` unrestricted Kummer theorem builds.
- `#print axioms` contains no `sorryAx`.
- The ticket result explicitly states that no `p ∤ m`, `p ∤ n`, `p ∤ m+1`,
  or `p ∤ n+1` hypotheses remain.

Result:

- Added `bernoulli_div_sModEq_of_modEq_full_geFive` in
  `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`.
- The proof applies `voronoi_congruence_mod_p_strong` to both exponents,
  compares primitive-root powers and Voronoi floor sums modulo `p`, and
  divides only by the p-adic units `a^m - 1` and `a^n - 1`.
- No hypotheses of the form `p ∤ m`, `p ∤ n`, `p ∤ m + 1`, or `p ∤ n + 1`
  remain.
- Verified with
  `lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull`.
- Axiom check for `bernoulli_div_sModEq_of_modEq_full_geFive` reports only
  `[propext, Classical.choice, Quot.sound]`.

#### [CAR-11h] Replace the public full-Kummer theorem

- Status: done
- Claimer: Riccardo
- Started: 2026-05-25
- Completed: 2026-05-25
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`

Goal:

Use CAR-11g plus the `p = 3` contradiction from CAR-11a to replace the
existing sorried theorem:

```lean
theorem bernoulli_div_sModEq_of_modEq_full
    {p m n : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm_even : Even m) (hn_even : Even n)
    (hnot : ¬ (p - 1) ∣ n)
    (hmn : m ≡ n [MOD p - 1]) :
    ∃ z : ℤ_[p],
      (((bernoulli m : ℚ) / (m : Nat) : ℚ) : ℚ_[p]) -
        (((bernoulli n : ℚ) / (n : Nat) : ℚ) : ℚ_[p]) =
      (p : ℚ_[p]) * (z : ℚ_[p])
```

Tasks:

- Remove `set_option warn.sorry false` around the theorem.
- If `p = 3`, close by contradiction from `hn_even` and `hnot`.
- If `5 ≤ p`, call `bernoulli_div_sModEq_of_modEq_full_geFive`.
- Rework `bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd` so it uses the
  CAR-11e integrality theorem or the newly proved full Kummer theorem without
  reintroducing a cycle.

Done criteria:

- `rg -n "sorry|warn.sorry" BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  finds no local source `sorry`.
- `lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull` succeeds.
- `#print axioms BernoulliRegular.bernoulli_div_sModEq_of_modEq_full` has no
  `sorryAx`.

Result:

- Removed the `set_option warn.sorry false` wrapper and replaced
  `bernoulli_div_sModEq_of_modEq_full` by a call to
  `bernoulli_div_sModEq_of_modEq_full_geFive`.
- The `p = 3` case is eliminated by
  `five_le_of_odd_prime_and_even_nonboundary`, using `hn_even` and
  `¬ (p - 1) ∣ n`.
- `bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd` now consumes the clean
  public full-Kummer theorem without a `sorry` dependency.
- `rg -n "sorry|warn\\.sorry"
  BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean` reports no
  matches.
- Verified with
  `lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull`.
- Axiom checks for `bernoulli_div_sModEq_of_modEq_full` and
  `bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd` report only
  `[propext, Classical.choice, Quot.sound]`.

#### [CAR-11i] Prove the TeX `pr+1` comparison from clean Kummer

- Status: done
- Claimer: Riccardo
- Started: 2026-05-25
- Completed: 2026-05-25
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`

Goal:

Formalize TeX Corollary 5.1 as a checkpoint using the clean full Kummer
theorem, not the old audit wrapper.

Target declaration:

```lean
theorem bernoulli_pr_plus_one_sModEq_div_clean
    {p r : Nat} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hr_odd : Odd r) (hr_pos : 0 < r)
    (hnot : ¬ (p - 1) ∣ r + 1) :
    ∃ z : ℤ_[p],
      (((bernoulli (p * r + 1) : ℚ) : ℚ_[p])) -
          (((bernoulli (r + 1) : ℚ) / (r + 1 : Nat) : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p])
```

Proof plan:

1. Set `m = p*r + 1`, `n = r + 1`.
2. Prove both are positive even and congruent modulo `p - 1`.
3. Apply the clean public Kummer theorem.
4. Prove `p ∤ p*r + 1`; hence `p*r + 1` is a p-adic unit.
5. Use `p*r + 1 ≡ 1 mod p` and vSC integrality of `B_(p*r+1)` to replace
   `B_(p*r+1)/(p*r+1)` by `B_(p*r+1)` modulo `p`.
6. Combine congruences.

Done criteria:

- The checkpoint theorem builds.
- It does not use `bernoulli_pr_plus_one_sModEq_div_of_kummerCongruence`
  except as a shape reference.
- The proof mirrors the TeX corollary and has no auxiliary Voronoi side
  conditions.

Result:

- Added `bernoulli_pr_plus_one_sModEq_div_clean`, proving the TeX `pr+1`
  comparison directly from `bernoulli_div_sModEq_of_modEq_full`.
- The proof reconstructs the `m = p*r + 1`, `n = r + 1` positivity,
  parity, and modulo-`p-1` checks, then uses von Staudt integrality and the
  unit inverse of `p*r + 1` to replace `B_(p*r+1)/(p*r+1)` by
  `B_(p*r+1)` modulo `p`.
- The theorem does not call
  `bernoulli_pr_plus_one_sModEq_div_of_kummerCongruence`.
- Verified with
  `lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull`.
- Axiom check for `bernoulli_pr_plus_one_sModEq_div_clean` reports only
  `[propext, Classical.choice, Quot.sound]`.

#### [CAR-11j] Final axiom audit for the TeX Voronoi route

- Status: done
- Claimer: Riccardo
- Started: 2026-05-25
- Completed: 2026-05-25
- Files:
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`
  - `BernoulliRegular/IrregularPrimes/Infinitude.lean`
  - `BernoulliRegular/IrregularPrimes/tickets.md`
  - `README.md`

Goal:

Verify that the TeX Voronoi route removes `sorryAx` from the Carlitz
infinitude path.

Commands:

```bash
lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull
lake build BernoulliRegular.IrregularPrimes
lake build
```

Axiom checks:

```lean
#print axioms BernoulliRegular.sum_range_pow_sub_p_mul_bernoulli_strong
#print axioms BernoulliRegular.voronoi_congruence_mod_p_strong
#print axioms BernoulliRegular.bernoulli_div_sModEq_of_modEq_full
#print axioms BernoulliRegular.infinite_not_isRegularPrime
```

Done criteria:

- Full build succeeds.
- Axiom checks show no `sorryAx` in the new Kummer route.
- `README.md` and this ticket board describe the proof path as
  Faulhaber/vSC -> strong Voronoi -> Kummer -> Carlitz.

Result:

- Updated `README.md`, the top-level ticket-board status, and the
  `KummerCongruenceFull.lean` module note to describe the completed route:
  von Staudt-Clausen/Faulhaber -> strong Voronoi -> full Kummer -> Carlitz.
- `rg -n 'sorry|warn\.sorry'
  BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean` reports no
  matches.
- Build commands run successfully:
  `lake build BernoulliRegular.IrregularPrimes.KummerCongruenceFull`,
  `lake build BernoulliRegular.IrregularPrimes`, and `lake build`.
- Axiom checks:
  - `sum_range_pow_sub_p_mul_bernoulli_strong`:
    `[propext, Classical.choice, Quot.sound]`
  - `voronoi_congruence_mod_p_strong`:
    `[propext, Classical.choice, Quot.sound]`
  - `bernoulli_div_sModEq_of_modEq_full`:
    `[propext, Classical.choice, Quot.sound]`
  - `infinite_not_isRegularPrime`:
    `[propext, Classical.choice, Quot.sound]`

### [CAR-12] Remove obsolete Kummer-provider compatibility API

- Status: done
- Claimer: Riccardo
- Started: 2026-05-25
- Completed: 2026-05-25
- Files:
  - `BernoulliRegular/IrregularPrimes/Infinitude.lean`
  - `BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean`

Goal:

Clean the public irregular-primes layer after the full Kummer theorem became
axiom-clean.  Remove conditional provider declarations and old side-condition
wrappers that were only useful while `bernoulli_div_sModEq_of_modEq_full` was
unproved.

Result:

- Removed the `Infinitude.lean` provider-facing declarations, including
  `exists_not_isRegularPrime_not_mem_of_kummerProvider`, and inlined the clean
  `bernoulli_div_sModEq_of_modEq_full` call into
  `not_isRegularPrime_iff_exists_dvd_bernoulli_div_self_num`.
- Removed the obsolete `bernoulli_div_sModEq_of_modEq_voronoiSideConditions`
  compatibility wrapper.
- `rg -n '_of_kummerProvider|kummerProvider|teichmullerBridgeProvider|voronoiSideConditions'
  BernoulliRegular/IrregularPrimes/*.lean` reports no matches.
- Verified with `lake build BernoulliRegular.IrregularPrimes` and `lake build`.

## Critical Path

```text
CAR-01
  -> CAR-03
  -> CAR-05
  -> CAR-06
  -> CAR-07
  -> CAR-08
  -> CAR-09
```

All listed tickets now have Lean declarations in place.  The CAR-11 route
replaced the former full-Kummer `sorry` in `CAR-03`, so the Carlitz endpoint is
checked without `sorryAx`.

Follow-up work:

- Keep the older side-conditioned Voronoi and finite-character bridge lemmas as
  comparison infrastructure; the public route now uses
  `bernoulli_div_sModEq_of_modEq_full`.
- Archive completed CAR-11 ticket work at the appropriate ticket granularity
  once the final audit is recorded.

Axiom-clean Kummer follow-up path:

```text
CAR-10b
  -> CAR-11a
  -> CAR-11b
  -> CAR-11c
  -> CAR-11d
  -> CAR-11e
  -> CAR-11f
  -> CAR-11g
  -> CAR-11h
  -> CAR-11i
  -> CAR-11j
```

CAR-10c remains useful algebraic infrastructure, but the current preferred
route from `bernoulli_kummer_congruences_proof.tex` proves divided Bernoulli
integrality through side-condition-free Voronoi instead of a separate Adams
induction.

## Audit Checklist

Before claiming the final theorem is axiom-clean:

- No `sorry`, project-specific axiom, opaque source theorem, or bundled
  "Kummer package" appears in the proof path.
- Kummer congruence is proved as a Bernoulli-number congruence from concrete
  inputs, not assumed from p-adic `L`-functions.
- The proof of `CAR-05` audits all denominator-clearing steps.
- The growth theorem is the existing proved theorem from
  `BernoulliGrowth.lean`, not an assumed asymptotic.
- The finite-set contradiction returns a prime outside the given finite set.
- The final public theorem goes through `KummerCriterion` / `IsRegularPrime`,
  not through a new public irregular-prime predicate.
