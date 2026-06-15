import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# B-C1.0 (part 1) — the Iwasawa `p`-adic logarithm `log_p`

This file defines the **`p`-adic logarithm** `padicLog : ℚ_[p] → ℚ_[p]` as the
Iwasawa power series

  `log_p x = ∑_{n ≥ 1} (-1)^{n+1} (x - 1)^n / n`,

a genuine `tsum`.  On the disk of convergence (`‖x - 1‖ < 1`, i.e. on principal
units `x ≡ 1 mod p`) this is the standard `p`-adic logarithm used by Washington
in §5.4 / §8.4 for FLT for regular and irregular primes; outside that disk the
`tsum` of a non-summable family is `0` by mathlib convention, which matches the
extension `log_p p = 0` once one passes to `ℚ_[p]ˣ` (not needed here).

The target ring is the **concrete** `ℚ_[p]` (not an abstract `adicCompletion`):
this side-steps the `adicCompletionIntegers` ring-transport whnf wall documented
for the `samePrimeFiniteLog` route.

## Main definitions / results (this file)

* `padicLog : ℚ_[p] → ℚ_[p]` — the Iwasawa `log_p` power series.
* `padicLog_one : padicLog 1 = 0` — every term of the series vanishes at `x = 1`
  (proved).
* `padicLog_summand`, `padicLog_eq_tsum` — unfolding API.

The **multiplicativity** `log_p (x y) = log_p x + log_p y` and the
**integrality** `log_p (1 + p z) ∈ ℤ_[p]` are the deep analytic inputs; they are
isolated as named `Prop`s in `Theorem518.lean` (B-C1.1) — they are NOT asserted
here.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §5.1, §5.4.
* Iwasawa, *Lectures on `p`-adic `L`-functions*, §1–2.
-/

namespace BernoulliRegular.FLT37.PadicL

variable {p : ℕ} [hp : Fact p.Prime]

/-- The `n`-th summand of the Iwasawa `p`-adic logarithm series:
`(-1)^{n+1} (x - 1)^n / n`, with the `n = 0` term set to `0` (the series starts
at `n = 1`). -/
noncomputable def padicLogSummand (x : ℚ_[p]) (n : ℕ) : ℚ_[p] :=
  if n = 0 then 0 else (-1) ^ (n + 1) * (x - 1) ^ n / (n : ℚ_[p])

/-- The **`p`-adic logarithm** `log_p x = ∑_{n ≥ 1} (-1)^{n+1} (x-1)^n / n`,
defined as a `tsum` over all `n : ℕ` (the `n = 0` term being `0`). -/
noncomputable def padicLog (x : ℚ_[p]) : ℚ_[p] :=
  ∑' n : ℕ, padicLogSummand x n

theorem padicLog_eq_tsum (x : ℚ_[p]) :
    padicLog x = ∑' n : ℕ, padicLogSummand x n := rfl

@[simp]
theorem padicLogSummand_zero (x : ℚ_[p]) : padicLogSummand x 0 = 0 := by
  simp [padicLogSummand]

theorem padicLogSummand_of_ne_zero (x : ℚ_[p]) {n : ℕ} (hn : n ≠ 0) :
    padicLogSummand x n = (-1) ^ (n + 1) * (x - 1) ^ n / (n : ℚ_[p]) := by
  simp [padicLogSummand, hn]

/-- At `x = 1`, every summand vanishes (because `(1 - 1)^n = 0` for `n ≥ 1`),
so `log_p 1 = 0`. -/
@[simp]
theorem padicLog_one : padicLog (1 : ℚ_[p]) = 0 := by
  have h : ∀ n : ℕ, padicLogSummand (1 : ℚ_[p]) n = 0 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [padicLogSummand_of_ne_zero _ hn]
      simp [sub_self, zero_pow hn]
  rw [padicLog, show padicLogSummand (1 : ℚ_[p]) = (fun _ => 0) from funext h]
  simp

end BernoulliRegular.FLT37.PadicL
