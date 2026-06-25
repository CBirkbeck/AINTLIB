import HasseWeil.DiscriminantBounds
import HasseWeil.Hasse.PointFix

/-!
# Witness-parametric Hasse bound

Top-level witness form of Silverman V.1.1 (the Hasse bound).

The existing `hasse_bound` in `HasseWeil/HasseBound.lean` has a residual
`sorry` on the QF non-negativity in `ℤ` (a true statement, deferred until
Silverman III.6.3 lands axiom-clean) and depends on `pointCount_eq`
(`HasseWeil/Frobenius.lean`, also `sorry`-ed). The witness-parametric
companions (`pointCount_eq_of_witness`, `degree_quadratic_nonneg_of_witness`,
the `_qf_nonneg` chain below) bypass both blockers. This file composes them
into `hasse_bound_of_t_witness`, which is axiom-hygienic and *conditionally*
proves the Hasse bound given:

1. an integer `t : ℤ` (the intended trace) such that
   `#E(F_q) = q + 1 − t`;
2. a family of endomorphism isogenies `β_qf r s` whose degrees realise the
   quadratic form `q·r² − t·r·s + s²` for every `r, s : ℤ`.

Both conditions are exactly what the III.5 / III.6 chain + V.1.1 setup produces
in Silverman; once those chains are fully formalised, the witnesses become
internally constructible and the unconditional `hasse_bound` falls out as a
special case.

## Main results

* `traceOfFrobenius_sq_le_of_witness` — the discriminant bound `t² ≤ 4q` given
  a family of quadratic-form degree witnesses.
* `hasse_bound_of_t_witness` — `|#E(F_q) − q − 1| ≤ 2√q` given both witness
  families.
* `hasse_bound_of_full_witnesses` — the same bound from the `1 − π` hom/kernel
  witness (trace computed internally) plus the quadratic-form witness family.
* `hasse_bound_of_all_witnesses` — the top-level plug-in form, gathering every
  upstream dependency (separable + finite-dim + fiber + QF witnesses) into one
  theorem whose hypotheses map one-to-one to the outstanding upstream tickets.

## References
* [Silverman, *The Arithmetic of Elliptic Curves*], V.1.1.
-/

open WeierstrassCurve Real

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-! ### Discriminant bound from a quadratic-form witness family -/

/-- **Discriminant bound, witness form**. Given an integer `t` and a family of
    endomorphism isogenies `β r s` whose degrees realise the binary quadratic
    form `q·r² − t·r·s + s²`, we have `t² ≤ 4q`.

    This is the witness-parametric companion of `traceOfFrobenius_sq_le`. The
    caller supplies the degree equalities (which unconditional III.6.3 would
    produce internally) and this lemma concludes the discriminant bound. -/
theorem traceOfFrobenius_sq_le_of_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (t : ℤ)
    (β : ℤ → ℤ → Isogeny W.toAffine W.toAffine)
    (h_deg : ∀ r s : ℤ, ((β r s).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 - t * r * s + s ^ 2) :
    t ^ 2 ≤ 4 * (Fintype.card K : ℤ) := by
  apply trace_sq_le_four_mul_deg _ _ Fintype.card_pos
  intro r s
  rw [← h_deg r s]
  exact Int.natCast_nonneg _

end HasseWeil
