import BernoulliRegular.FLT37.PadicL.ValuationExactness
import BernoulliRegular.FLT37.PadicL.PadicLog
import BernoulliRegular.FLT37.PadicL.LpValue
import BernoulliRegular.FLT37.PadicL.GaussSumValuation
import BernoulliRegular.FLT37.PadicL.GaussSumValuationF1
import BernoulliRegular.FLT37.PadicL.Theorem518
import BernoulliRegular.FLT37.PadicL.Prop812

/-!
# The `p`-adic `L`-function layer for Washington Proposition 8.12 (FLT for `p = 37`)

This umbrella gathers the `p`-adic `L`-function / `p`-adic-logarithm development
behind Washington **Proposition 8.12** (the deep Case-II / Assumption-II content
of FLT for the irregular prime `p = 37`: Cor 8.23 → Thm 8.22 → Prop 8.12).

The repo's pre-existing logarithm infrastructure is **archimedean** (Sinnott
regulator, `LogEmbedding`, `LDerivative`) or the graded **λ-adic** `completedLog`
(the dead first-order mod-`37²` route).  This layer is the genuinely new
**`p`-adic** development (Washington §§5.4, 6.3, 8.4), built over the concrete
`p`-adic numbers `ℚ_[p]` / `ℤ_[p]` (side-stepping the `adicCompletionIntegers`
ring-transport whnf wall).

## Decomposition (from `decomposition-descent-mechanisms.md` §B-C1)

* **B-C1.0** — API: `padicLog` (Iwasawa `log_p`), `bernoulliFactorQp`, the
  `PadicLFunction` Kubota–Leopoldt package. **Built** (`PadicLog`, `LpValue`).
* **B-C1.2** — Prop 6.13 at `f = 1`: `v_p(τ(ω^{-i})) = i/(p-1)`. Named residual
  `GaussSumValuationCaseF1` + proved `p = 37, i = 32` arithmetic.
* **B-C1.3** — exactness `x ≡ y mod p^N ∧ v_p(y) < N ⟹ v_p(x) = v_p(y)`; unit
  valuations. **Proved** (`ValuationExactness`).
* **B-C1.1** — Thm 5.18 Case I (`f = p`):
  `L_p(1,ω^i) = -τ(ω^{-i})/p · Σ ω^{-i}(a) log_p(1-ζ^a)`. Named residual
  `Theorem518CaseI` + sub-leaf structure.
* **B-C1.4** — Prop 8.12 assembly:
  `v_p(log_p E_i^{(N)}) = i/(p-1) + v_p(L_p(1,ω^i))`. **Proved** (`Prop812`,
  conditional on the data).

## Key unconditional result

The genuine first-order arithmetic content of `M = 1`, namely
`v₃₇(L_p(1, ω³²)) = 1` (read off as `v₃₇(B₃₂/32) = 1` from the proven `37 ∥ B₃₂`),
is **proved unconditionally** (`valuation_bernoulliFactorQp_thirtytwo`,
`PadicLFunction.valuation_thirtytwo`).  Feeding it through the assembly gives
`v₃₇(log_p E_{32}^{(N)}) = 8/9 + 1 = 17/9` (`Prop812Data.prop812_thirtytwo`).
The `Prop812Data` bundle is shown **non-vacuous** (`ofPadicLFunction`).

## The smallest true analytic residual

After this layer, the open analytic content of Prop 8.12 is precisely:

* **`Theorem518CaseI`** (Washington Thm 5.18, Case `f = p`, ≈3.5 pp.) — the
  formula `L_p(1, ω^i) = -τ(ω^{-i})/p · Σ_a ω^{-i}(a) log_p(1 - ζ^a)`, with the
  five sub-leaves (log-`φ` multinomial expansion, Lemma 5.19, the Bernoulli
  generating function, the `L_p` limit, the Gauss-sum collapse);
* **`GaussSumValuationCaseF1`** (Washington Prop 6.13 at `f = 1`) — the
  Stickelberger digit-sum collapse `s(i) = i`, giving `v_p(τ(ω^{-i})) = i/(p-1)`.
  **Substantially discharged** in `GaussSumValuationF1.lean`: over the abstract
  `f = 1` DVR setup `StickelbergerF1Setup` (modelling `ℤ_p[ζ_p]`), the genuine
  Gauss sum `g i = Σ_a (ω a)^{-i} (1+π)^a` is built, the base-`π` expansion and
  the full valuation reduction are proved, the **leading non-degeneracy
  `c_i ∉ 𝔓` is PROVED** (the `𝔽_p` character sum `Σ_a a^{-i} C(a,i) = -(i!)⁻¹`,
  via `sum_eval_eq_zero_of_natDegree_lt` + the inversion substitution), the
  normalisation `i ↦ i/(p-1)` is proved, and `GaussSumValuationCaseF1` for the
  concrete `(O, v_p, g)` is reduced to the **single** remaining leaf
  `GaussSumHigherCongruence` (the Gross–Koblitz higher-order vanishing
  `c i j ∈ 𝔓^{i+1-j}` for `j < i`) by
  `gaussSumValuationCaseF1_of_higherCongruence`;
* the **construction of an inhabitant of `PadicLFunction p`** (equivalently, the
  Iwasawa-limit definition of `L_p` together with `Theorem518CaseI`), carrying the
  congruence `v_p(L_p(1, ω^i)) = v_p(B_i / i)`.

These are stated as named `def … : Prop` / `structure` inputs (never `sorry`,
never `axiom`); everything downstream of them — the valuation read-off and the
`p = 37` numerics — is proved with the standard axioms `propext`,
`Classical.choice`, `Quot.sound`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83,
  Thm 5.11, Cor 5.13, Thm 5.18, Prop 6.13, Prop 8.12, Cor 8.23.
* Iwasawa, *Lectures on `p`-adic `L`-functions*.
-/
