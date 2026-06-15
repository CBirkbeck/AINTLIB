module

public import BernoulliRegular.HMinus.KplusLocalCharacters
public import BernoulliRegular.HMinus.KplusPrimeArithmetic
public import BernoulliRegular.HMinus.KplusEulerProduct
public import BernoulliRegular.HMinus.ClassNumberFormula
public import BernoulliRegular.HMinus.LValueReduction
public import BernoulliRegular.HMinus.PadicCorollaries

/-!
# Relative class number formula (umbrella)

This file re-exports the L4/T023 submodules covering the closed form for the
relative class number `h⁻` of a prime cyclotomic field in terms of odd
Bernoulli data. The legacy import path
`BernoulliRegular.HMinus.KplusLocalResidue` remains available as a
compatibility umbrella over the two split local files below.

- `BernoulliRegular.HMinus.KplusLocalCharacters`: the even-character local
  factor algebra over `K⁺`, including `localResidueDegreePlus`,
  `localPrimeCountPlus`, the cardinality identities, and the unramified
  even-character Euler factor formula.
- `BernoulliRegular.HMinus.KplusPrimeArithmetic`: the prime-ideal arithmetic
  package over `K⁺`, including the contraction fibers, the
  complex-conjugation fixed-prime criterion, and the inertia-degree formula.
- `BernoulliRegular.HMinus.KplusEulerProduct`: the global `K⁺`
  Euler-product / residue bridge, culminating in
  `dedekindZeta_eq_riemannZeta_mul_evenLProduct_of_one_lt_re` and
  `complex_maximalRealSubfield_residue_eq_evenLProduct_one`.
- `BernoulliRegular.HMinus.ClassNumberFormula`: analytic class-number
  formula for `K` and `K⁺`, plus the prime-conductor specialization
  (`h_formula`, `hPlus_formula`, `hMinus_formula_via_residues`,
  `h_formula_cyclotomic`).
- `BernoulliRegular.HMinus.LValueReduction`: umbrella over the split
  `Factors`, `LValues`, `Assembly`, `GaussGoal`, `GaussPairing`,
  `GaussProduct`, `Final`, and `Teichmuller` submodules, culminating in
  the proved formulas `hMinus_formula` and `hMinus_formula_teichmuller`.
- `BernoulliRegular.HMinus.PadicCorollaries`: page-51 congruence
  corollaries `hMinus_formula_teichmuller_mod_p` and
  `hMinus_formula_bernoulli_mod_p` for `h⁻ mod p`.
-/
