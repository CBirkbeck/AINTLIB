module

public import BernoulliRegular.HMinus.LValueReduction.Factors
public import BernoulliRegular.HMinus.LValueReduction.LValues
public import BernoulliRegular.HMinus.LValueReduction.Assembly
public import BernoulliRegular.HMinus.LValueReduction.GaussGoal
public import BernoulliRegular.HMinus.LValueReduction.GaussPairing
public import BernoulliRegular.HMinus.LValueReduction.GaussProduct
public import BernoulliRegular.HMinus.LValueReduction.Final
public import BernoulliRegular.HMinus.LValueReduction.Teichmuller

/-!
# Reduction of `h⁻` to the odd-Bernoulli product (T023a / T023b skeleton)

This umbrella re-exports the split `hMinus` reduction chain:

* `Factors`: the complex class-number coefficients.
* `LValues`: odd/even `L(1, χ)` evaluations and supporting odd-character
  Gauss lemmas.
* `Assembly`: the generic residue / `hPlus` / Gauss assembly statements.
* `GaussGoal`, `GaussPairing`, `GaussProduct`: the `T023d` raw odd
  Gauss-product proof package.
* `Final`: Diekmann Theorem 43 in cyclotomic form.
* `Teichmuller`: the odd-Teichmüller reindexing specialization used
  downstream in the `p`-adic corollaries.
-/
