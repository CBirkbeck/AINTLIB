module

public import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Dedekind residue — effective bound (Belabas–Friedman)

Root of the `DedekindResidue` development: an effective, GRH-conditional bound on the
residue `κ_K = Res_{s=1} ζ_K(s)` of the Dedekind zeta function of a number field `K`,
following Belabas–Friedman, *Computing the residue of the Dedekind zeta function*
(arXiv:1305.0035, 2013).

The motivation is the **analytic class number formula**
`κ_K = 2^{r₁} (2π)^{r₂} h_K R_K / (w_K √|d_K|)` (already available in mathlib as
`NumberField.dedekindZeta_residue`): a certified approximation of `κ_K` yields a certified
value of `h_K R_K`, the input to Buchmann's class-group / regulator algorithm.

This module is the initial scaffold. The mathematical content is developed bottom-up
across `CompletedZeta/`, `ExplicitFormula/`, and the top-level estimate files; the full
decomposition is tracked in the blueprint and the project's dev tickets.

Design discipline: the generalized Riemann hypothesis is the **only** assumption, threaded
as an explicit hypothesis (never an `axiom`); every result is `sorry`-free and axiom-clean
(`#print axioms` = `propext`, `Classical.choice`, `Quot.sound`).
-/

namespace DedekindResidue

end DedekindResidue
