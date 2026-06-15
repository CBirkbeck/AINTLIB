module

public import BernoulliRegular.Reflection.WeakSplitting.PoleOrder
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Final weak-splitting lemma assembly (REF-21e)

The weak-splitting lemma in its `Module.finrank K L = 1` form is exactly
`finrank_eq_one_of_global_identity` (REF-21d). This file provides the
final wrap-up: under the global identity hypothesis,
`Module.finrank K L = 1`, hence the algebra map `K → L` is bijective and
`L` is "the same" as `K`.

For our reflection application (Kummer extension `L = K(η^{1/p})` over
the cyclotomic `K = ℚ(ζ_p)`), `[L : K] = 1` means `η ∈ K^{×p}`. That
specialised conclusion is consumed by REF-22 (Proposition 5.2 in the
`kummer_reflection.tex` draft) as the contradiction with the construction
of `η`.

## Main results

* `BernoulliRegular.WeakSplitting.weakSplittingLemma`:
  the final wrap-up — under the global identity hypothesis (REF-21c2c)
  and the simple-pole hypotheses on both sides (REF-21a), the field
  extension has degree one.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace WeakSplitting

open NumberField Ideal Filter Topology

variable (L K : Type*) [Field L] [NumberField L] [Field K] [NumberField K] [Algebra K L]

/--
**The weak-splitting lemma** in its abstract `Module.finrank K L = 1`
form. If the global Kummer comparison identity (REF-21c2c) holds for the
unfolded forms `ζ_L · ∏(1 - N(Q)^{-s})` and `(ζ_K · ∏(1 - N(P)^{-s}))^[L:K]`
on `Re(s) > 1`, then `[L : K] = 1`.

This is exactly `finrank_eq_one_of_global_identity` (REF-21d), reframed
as the final API. The mathematical content is the pole-order argument
of REF-21d. The "all but finitely many primes split completely" version
of the weak-splitting lemma reduces to this via the chain of REF-21a (pole
preservation), REF-21c2 (global identity), and REF-21d (pole-order
assembly).
-/
theorem weakSplittingLemma
    (F_L : Finset (Ideal (𝓞 L))) (S : Finset (Ideal (𝓞 K)))
    (hF_L : ∀ Q ∈ F_L, Q.IsPrime ∧ Q ≠ ⊥)
    (hS : ∀ P ∈ S, P.IsPrime ∧ P ≠ ⊥)
    (h_global : ∀ s : ℝ, 1 < s →
      dedekindZeta L (s : ℂ) * ∏ Q ∈ F_L, ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-(s : ℂ))) =
        (dedekindZeta K (s : ℂ) * ∏ P ∈ S,
          ((1 : ℂ) - (Ideal.absNorm P : ℂ) ^ (-(s : ℂ)))) ^ Module.finrank K L)
    [Module.Finite K L] [Module.Free K L] (h_finrank_pos : 0 < Module.finrank K L) :
    Module.finrank K L = 1 :=
  finrank_eq_one_of_global_identity L K F_L S hF_L hS h_global h_finrank_pos

end WeakSplitting

end BernoulliRegular
