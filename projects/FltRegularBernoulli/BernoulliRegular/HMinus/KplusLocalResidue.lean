module

public import BernoulliRegular.HMinus.KplusLocalCharacters
public import BernoulliRegular.HMinus.KplusPrimeArithmetic

/-!
# `K⁺` local residue data (umbrella)

Compatibility umbrella preserving the historical import path for the local
`K⁺` package. The former monolithic module is now split into:

- `BernoulliRegular.HMinus.KplusLocalCharacters`: the even-character local
  factor algebra, including `localResidueDegreePlus`,
  `localPrimeCountPlus`, the cardinality identities, and the unramified
  character-side Euler factor theorem.
- `BernoulliRegular.HMinus.KplusPrimeArithmetic`: the arithmetic prime package
  over `K⁺`, including the contraction fibers, the complex-conjugation fixed
  prime criterion, and the inertia-degree formula above `ℓ ≠ p`.
-/
