import BernoulliRegular.FLT37.PadicL.PadicLog
import BernoulliRegular.FLT37.PadicL.LpValue

/-!
# B-C1.1 — Washington Theorem 5.18 (Case I, `f = p`): the analytic heart

This file isolates, **as a named `Prop` (not an axiom, not a `sorry`)**, the deep
analytic input behind Proposition 8.12: Washington's Theorem 5.18 in the case of
the cyclotomic field `ℚ(ζ_p)` (conductor `f = p`).

Washington's formula (GTM 83, p. 63), specialised to `f = p` where the Euler
factor `1 - χ(p)/p = 1` (because `χ = ω^{-i}` is ramified at `p`, so `χ(p) = 0`):

  `L_p(1, ω^i) = - (τ(ω^{-i}) / p) · ∑_{a=1}^{p-1} ω^{-i}(a) · log_p(1 - ζ_p^a)`.

Together with Prop 6.13 (`v_p(τ(ω^{-i})) = i/(p-1)`, file `GaussSumValuation.lean`)
and the micro-facts of `ValuationExactness.lean`, this is what the Prop 8.12
assembly (`Prop812.lean`) consumes.

## The residual and its sub-leaf structure

`Theorem518CaseI p` is the statement that a Kubota–Leopoldt package `L` together
with a `p`-adic logarithm `log_p` and a Gauss sum `τ`/root of unity `ζ` satisfy
the Thm 5.18 identity above.  Its proof (Washington pp. 63–66, ~3.5 pages,
Case I only — Case II `f ≠ p` is not needed for `ℚ(ζ_p)`) decomposes into:

* **4a** `log φ(X)` multinomial-integrality expansion (the formal power series of
  `log_p` of the cyclotomic polynomial factor);
* **4b** Lemma 5.19: `∑_{j} (-1)^j C(i, j) j^m = 0` for `i > m`;
* **4c** the Bernoulli generating function identity;
* **4d** the `L_p` limit `L_p(1, ω^k) = lim_n L_p(1 - k p^n, ω^k)`;
* **4e** the Gauss-sum collapse `∑_a ω^{-k}(a) ζ^{aj} = ω^k(j) τ(ω^{-k})`.

The cited reduction `valuation_eq_bernoulliFactor` carried by `PadicLFunction`
(the Iwasawa congruence `v_p(L_p(1, ω^i)) = v_p(B_i / i)`) is the *valuation*
consequence of this identity together with Prop 6.13; constructing an actual
`PadicLFunction p` (equivalently, proving `Theorem518CaseI` and feeding it into
the limit) is the named open analytic content.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83,
  Thm 5.18 (pp. 63–66), Lemma 5.19, Cor 5.13.
-/

namespace BernoulliRegular.FLT37.PadicL

/-- **Washington Theorem 5.18, Case I (`f = p`)** — the named analytic residual.

For a prime `p`, a Kubota–Leopoldt package `L : PadicLFunction p`, the Iwasawa
`p`-adic logarithm `padicLog`, and Gauss-sum / root-of-unity data realised in
`ℚ_[p]` (here packaged abstractly as `τ : ℕ → ℚ_[p]` and a finite-sum functional
`logSum : ℕ → ℚ_[p]` with `logSum i = ∑_{a=1}^{p-1} ω^{-i}(a) log_p(1 - ζ^a)`),
the `L`-value at `s = 1` is given by Washington's formula

  `L i = -(τ i / p) · logSum i`   for the relevant even indices `2 ≤ i ≤ p - 3`.

This is a `Prop` (a hypothesis to be discharged by the §5.4 analytic argument),
**not** an axiom. -/
def Theorem518CaseI (p : ℕ) [Fact p.Prime]
    (L : PadicLFunction p) (τ : ℕ → ℚ_[p]) (logSum : ℕ → ℚ_[p]) : Prop :=
  ∀ i, 2 ≤ i → i ≤ p - 3 → Even i →
    L.Lp i = -(τ i / (p : ℚ_[p])) * logSum i

end BernoulliRegular.FLT37.PadicL
