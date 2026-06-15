/-
Copyright (c) 2026 Bernoulli-Regular project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernoulli-Regular project contributors
-/
import Mathlib.NumberTheory.Bernoulli

/-!
# Fast computable Bernoulli numbers

This module defines a fully computable version of the Bernoulli sequence
`bernoulliCompute : ℕ → ℚ` that agrees with Mathlib's noncomputable
`bernoulli` and evaluates efficiently once unfolded by `norm_num`.

## Key design choices

* **No `Nat.choose`:** The standard Pascal-triangle recursion for `Nat.choose`
  is exponential in the kernel (no memoisation).  Instead, binomial
  coefficients are computed *incrementally in `ℚ`* via the identity
  `C(m, k+1) = C(m, k) · (m − k) / (k + 1)`, giving O(1) per coefficient.

* **Sequential list traversal:** `binomSum` pattern-matches on the list
  head, so the kernel never needs random access into an `Array` or `List`.

* **Memoisation via `let`:** `bernoulliList n` calls `bernoulliList (n−1)`
  once; the result is shared through a `let` binding, so total work is
  O(n²) rational operations.

## Main declarations

* `BernoulliRegular.BernoulliFast.binomSum` — O(n) computation of
  `∑_{k<|bs|} C(m,k) · bs[k]` with incremental binom coefficients.
* `BernoulliRegular.BernoulliFast.bernoulliList` — `[B₀, …, Bₙ]`
  computed iteratively from the recurrence.
* `BernoulliRegular.BernoulliFast.bernoulliCompute` — `Bₙ` extracted
  from the list.
-/

set_option linter.unusedVariables false

namespace BernoulliRegular.BernoulliFast

open Finset

/-! ### Incremental binomial-coefficient summation -/

/-- Inner loop for `binomSum`.

`binomSum.loop m bs k c acc` computes
  `acc + ∑_{j=0}^{|bs|−1} C(m, k+j) · bs[j]`
where `c = ↑C(m, k)` is the running binomial coefficient maintained
incrementally in `ℚ`. -/
def binomSum.loop (m : ℕ) : List ℚ → ℕ → ℚ → ℚ → ℚ
  | [], _, _, acc => acc
  | b :: rest, k, c, acc =>
    binomSum.loop m rest (k + 1)
      (c * ((m : ℚ) - k) / ((k : ℚ) + 1))
      (acc + c * b)

/-- `binomSum bs m = ∑_{k<|bs|} C(m,k) · bs[k]`.

Computed in O(|bs|) rational operations without calling `Nat.choose`.
The binomial coefficient `C(m, k)` is tracked as a running `ℚ` value
updated via `C(m, k+1) = C(m,k) · (m−k)/(k+1)`. -/
def binomSum (bs : List ℚ) (m : ℕ) : ℚ :=
  binomSum.loop m bs 0 1 0

/-! ### Iterative Bernoulli table -/

/-- `bernoulliList n` returns the list `[B₀, B₁, …, Bₙ]`.

Uses the recurrence derived from `sum_bernoulli`:
  `(n+2) · B_{n+1} + ∑_{k≤n} C(n+2, k) · Bₖ = 0`
so that
  `B_{n+1} = − (∑_{k≤n} C(n+2,k) · Bₖ) / (n+2)`. -/
def bernoulliList : ℕ → List ℚ
  | 0 => [(1 : ℚ)]
  | n + 1 =>
    let prev := bernoulliList n
    let s := binomSum prev (n + 2)
    prev ++ [- s / ((n : ℚ) + 2)]

/-- Fast computable Bernoulli number `Bₙ`.

Extracts the last element of `bernoulliList n = [B₀, …, Bₙ]`. -/
def bernoulliCompute (n : ℕ) : ℚ :=
  (bernoulliList n).getLast!

end BernoulliRegular.BernoulliFast
