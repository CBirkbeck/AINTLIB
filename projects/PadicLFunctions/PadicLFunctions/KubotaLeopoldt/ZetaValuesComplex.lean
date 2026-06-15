import PadicLFunctions.KubotaLeopoldt.ZetaValues
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# The complex bridge for `zetaNeg`

Identifies the rational value `zetaNeg k` with the complex Riemann zeta function at
`−k` (mathlib's `riemannZeta_neg_nat_eq_bernoulli`). Quarantined in its own file so
that the p-adic development does not import complex analysis.
-/

open Complex

/-- `zetaNeg k` really is `ζ(−k)`: the bridge to the complex Riemann zeta function.

Source: RJW TeX line 1455 (`ζ(−k) = (−1)^k B_{k+1}/(k+1)`); mathlib's
`riemannZeta_neg_nat_eq_bernoulli`. -/
theorem zetaNeg_eq_riemannZeta (k : ℕ) :
    ((zetaNeg k : ℚ) : ℂ) = riemannZeta (-(k : ℂ)) := by
  rw [riemannZeta_neg_nat_eq_bernoulli, zetaNeg]
  push_cast
  ring
