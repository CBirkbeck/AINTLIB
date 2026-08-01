/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetNoetherianVertices
import «Adic spaces».Presheaf
import «Adic spaces».NoetherianTateModules
import Mathlib.RingTheory.Flat.Basic

/-!
# Comparator challenge: Nonarchimedean Scottish Book Problems 24 and 28

The two Scottish Book answers obtained from the finite-jet algebra, stated with `sorry`
proofs, for verification by [leanprover/comparator](https://github.com/leanprover/comparator)
against `ScottishBookSolution.lean`.

Both statements are given **over an arbitrary finite-jet base** (`IsFJPBase`), which is what
the library proves: a complete ultrametric nonarchimedean field with a pseudouniformizer, no
discreteness. So they cover `ℚ_p` and `ℂ_p` as well as `F((t))`.

## Trust boundary

Like `Challenge.lean`, this module imports only the **definition layer**. The witness element
`Q²` and the chart datum `(W; ϖ)` both live in the *proving* layer (`FJP.FiniteJetChart`,
`FJP.FiniteJetScottishBook`), so rather than importing them the challenge **quantifies both
existentially**. That keeps those modules out of the closure, so these statements are
independent restatements rather than echoes of the proofs being judged.

The existential form is also the faithful one: Problem 28 asks whether there *exist* a pair
and an element with these properties, so the certificate should fix what was claimed without
naming how it was built.

Excluded from the default build: the `«Adic spaces»` `lean_lib` declares no `globs`, so only
its root module is a build target and nothing imports this file.
-/

open FiniteJet ValuationSpectrum

universe u

variable (F : Type u) [NormedField F] [IsUltrametricDist F] [CompleteSpace F]
  [IsFJPBase F]

/-- **Scottish Book Problem 28 (affirmative)**: there is a rational datum on
`Spa(𝓐, 𝓐°)` cutting out a nonempty subset with a nonzero chart, on which the
non-zero-divisor `Q²` — multiplication by which is a strict inclusion with closed image —
restricts to zero. -/
theorem sb_28_strict_inclusion_dies_on_rational_subset :
    ∃ (f : JetA F) (D : RationalLocData (JetA F)),
      D.IsRational ∧
      (rationalOpen D.T D.s).Nonempty ∧
      Nontrivial (presheafValue D) ∧
      Function.Injective (fun a : JetA F => f * a) ∧
      IsStrictMap (fun a : JetA F => f * a) ∧
      IsClosed (Set.range fun a : JetA F => f * a) ∧
      D.canonicalMap f = 0 := sorry

/-- **Scottish Book Problem 24 (negative)**: the completed rational localization of a Tate
pair need not be flat. -/
theorem sb_24_rational_localization_not_flat :
    ∃ D : RationalLocData (JetA F),
      ¬ @Module.Flat (JetA F) (presheafValue D) _ _
        (RingHom.toModule D.canonicalMap) := sorry
