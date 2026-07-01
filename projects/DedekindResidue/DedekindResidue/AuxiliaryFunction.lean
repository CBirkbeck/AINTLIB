module

public import Mathlib

/-!
# The auxiliary test function of Belabas–Friedman

Real, `sorry`-free definitions of the auxiliary functions from Belabas–Friedman,
*Computing the residue of the Dedekind zeta function* (arXiv:1305.0035):

* `gAux s` — the function `g_s(t) = exp(-h|t|)/|t|`, `h = s - 1/2` (eq. 6);
* `auxF s X` — the test function `F_{s,X}` (eqs. 11–12).

The Fourier transform of `auxF` (Lemma 2, eq. 8) is stated and proved later.
-/

namespace DedekindResidue

@[expose] public section

open scoped Real

/-- `g_s(t) = exp(-h|t|)/|t|` with `h = s - 1/2` — Belabas–Friedman eq. (6).
(Junk value `0` at `t = 0`.) -/
noncomputable def gAux (s : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(s - 1 / 2) * Complex.ofReal |t|) / Complex.ofReal |t|

/-- The auxiliary test function `F_{s,X}` — Belabas–Friedman eqs. (11)–(12):
`F(t) = 1` for `|t| ≤ log X`, and `F(t) = (log X / |t|)·exp(-h(|t| - log X))`
(with `h = s - 1/2`, `T = log X`) for `|t| > log X`. -/
noncomputable def auxF (s : ℂ) (X t : ℝ) : ℂ :=
  if |t| ≤ Real.log X then 1
  else Complex.ofReal (Real.log X / |t|) *
    Complex.exp (-(s - 1 / 2) * Complex.ofReal (|t| - Real.log X))

end

end DedekindResidue
