import BernoulliRegular.FLT37.PadicL.LpValue

/-!
# B-C1.2 — Proposition 6.13 at `f = 1`: `v_p(τ(ω^{-i})) = i/(p-1)`

This file isolates the **Gauss-sum valuation** input to Proposition 8.12, namely
Washington Proposition 6.13 in the conductor-`1` case (the cyclotomic field
`ℚ(ζ_p)`, where the only relevant prime is the totally-ramified prime
`𝔓 = (1 - ζ_p)` above `p`, with `𝔓^{p-1} = (p)`).

For `f = 1` the base-`p` digit-sum collapses to `s(i) = i` (Washington p. 97, one
sentence), so Stickelberger's theorem gives the integral valuation

  `v_𝔓(τ(ω^{-i})) = i`,

and, after normalising the valuation so that `v_p(p) = 1` (i.e. dividing the
`𝔓`-adic valuation by the ramification index `e = p - 1`),

  `v_p(τ(ω^{-i})) = i / (p - 1)`.

The integral digit-sum identity `v_𝔓(τ) = i` is the genuine Stickelberger content
(no mathlib support; see `GaussSumK.lean`'s `StickelbergerDigitSumValuation` for
the auxiliary-prime analogue).  It is carried here as the named `Prop`
`GaussSumValuationCaseF1` (B-C1.2), **not** an axiom.  The arithmetic conversion
`i ↦ i/(p-1)` and the `p = 37, i = 32` numeric value `32/36 = 8/9` are proved
unconditionally.

## Main definitions / results

* `gaussSumNormalizedValuation p i : ℚ := i / (p - 1)` — the normalised value
  (the right-hand `i/(p-1)` term of Prop 8.12).
* `gaussSumNormalizedValuation_thirtytwo`: `= 8/9` for `p = 37, i = 32` (proved).
* `GaussSumValuationCaseF1`: the named Stickelberger residual
  `(p - 1) · v_p(τ) = i` (equivalently `v_p(τ) = i/(p-1)`), a `Prop`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83,
  Prop 6.13, Lemmas 6.11–6.12 (pp. 87–97).
-/

namespace BernoulliRegular.FLT37.PadicL

/-- The **normalised Gauss-sum valuation** `v_p(τ(ω^{-i})) = i/(p-1)` as a
rational number (with `v_p(p) = 1`).  This is the left-hand term `i/(p-1)` of the
Prop 8.12 valuation formula. -/
def gaussSumNormalizedValuation (p i : ℕ) : ℚ := (i : ℚ) / ((p : ℚ) - 1)

theorem gaussSumNormalizedValuation_def (p i : ℕ) :
    gaussSumNormalizedValuation p i = (i : ℚ) / ((p : ℚ) - 1) := rfl

/-- For `p = 37, i = 32`: `v₃₇(τ(ω^{-32})) = 32/36 = 8/9`. -/
theorem gaussSumNormalizedValuation_thirtytwo :
    gaussSumNormalizedValuation 37 32 = 8 / 9 := by
  rw [gaussSumNormalizedValuation_def]; norm_num

/-- **B-C1.2 = Washington Proposition 6.13 at `f = 1`** — the named Stickelberger
residual.

For a prime `p`, given a `ℚ`-valued (`v_p(p) = 1`-normalised) valuation `v` on the
ring of integers of `ℚ_p(ζ_p)` and a realisation `τ : ℕ → (that ring)` of the
Gauss sums `τ(ω^{-i})`, the valuation of `τ(ω^{-i})` is `i/(p-1)` for the relevant
even indices `2 ≤ i ≤ p - 3`.

Stated abstractly as the identity `v (τ i) = gaussSumNormalizedValuation p i`
for a carried valuation function `v`.  Its content is the Stickelberger digit-sum
`s(i) = i` (the `f = 1` collapse), an analytic/arithmetic input with no mathlib
support; this is a `Prop`, **not** an axiom. -/
def GaussSumValuationCaseF1 (p : ℕ) {E : Type*} (v : E → ℚ) (τ : ℕ → E) : Prop :=
  ∀ i, 2 ≤ i → i ≤ p - 3 → Even i → v (τ i) = gaussSumNormalizedValuation p i

end BernoulliRegular.FLT37.PadicL
