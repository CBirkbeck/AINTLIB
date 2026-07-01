module

public import DedekindResidue.CompletedZeta.FunctionalEquation

/-!
# The Generalized Riemann Hypothesis for `ζ_K`

The project's **sole assumption**, stated (mirroring mathlib's `RiemannHypothesis`)
against the completed Dedekind zeta `Λ_K`, whose zeros are exactly the nontrivial zeros
of `ζ_K`. It is always threaded as a hypothesis argument — **never an `axiom`** — so that
every result stays axiom-clean.
-/

namespace DedekindResidue

@[expose] public section

/-- GRH for the Dedekind zeta function of `K`: every zero of the completed zeta `Λ_K`
lies on the critical line `Re s = 1/2` (equivalently, in Belabas–Friedman's notation,
every `γ_ρ ∈ ℝ`). -/
def GeneralizedRiemannHypothesis (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ s : ℂ, completedDedekindZeta K s = 0 → s.re = 1 / 2

end

end DedekindResidue
