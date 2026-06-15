/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Verschiebung.IsDual
import HasseWeil.AdditionPullback.Frobenius
import HasseWeil.DegreeQuadraticForm

/-!
# Sum-trace identity for Frobenius + Verschiebung (Silverman III.6.2(b))

`degree_quadratic_genuine_addIsog` (and the III.6.3 polarisation chain
that consumes it) requires `h_sum_trace : α + α_dual = [tr α]` at the
`toAddMonoidHom` level. For the Hasse-critical case `α = π` (Frobenius),
`α_dual = V` (Verschiebung), Silverman III.6.2(b) gives this via the
bilinear pairing argument; the substantive ingredient is
`(1 − π) ∘ (1 − V) = [deg(1 − π)]` (the bilinear form's diagonal value
on `(1, −π)`).

This file ships:

* `sum_trace_frobenius_witness` — Frobenius+Verschiebung specialisation
  of `trace_identity_of_dual_chain` (in `DegreeQuadraticForm.lean`).
  Witness-parametric on the Session-3 inclusion (axiom-clean for `q=2`
  char `2` from `Verschiebung.QthRoots`) and on the
  `IsDualOf one_sub_V (isogOneSub_negFrobenius)` substantive content.
  Worker D consumes this as `h_sum_trace` for the
  `degree_quadratic_genuine_addIsog` instance with `α = π`, supplying
  the III.6.2(b) bilinear identity from Worker C's eventual dual chain.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.6.2(b)
  (bilinearity of the degree pairing).
* Silverman, *The Arithmetic of Elliptic Curves*, III.6.3 (degree
  quadratic form).
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

/-- **Sum-trace identity for Frobenius + Verschiebung** (Silverman
III.6.2(b), Hasse case): given the Session-3 inclusion `Im([q]*) ⊆ Im(π*)`
(which makes `verschiebungIsog_of_witness` a genuine isogeny dual to
Frobenius), an auxiliary `1 − V` isogeny with the standard hom-form, and
the substantive III.6.2(b) ingredient `IsDualOf (1 − V) (1 − π)`,
conclude

  `π + V = [tr π]`

at the `toAddMonoidHom` level, where `tr π = isogTrace π (1 − π) =
1 + q − deg(1 − π)`. Worker D consumes this as `h_sum_trace` for the
`degree_quadratic_genuine_addIsog` instance with `α = π`.

The Frobenius half of the dual chain comes from
`verschiebungIsog_of_witness_isDualOf_frobenius` (Worker C, Session 5).
The `(1 − π) ∘ (1 − V) = [deg(1 − π)]` ingredient is the substantive
III.6.2(b) input — it's the one piece that doesn't reduce to the existing
chain and needs to be supplied separately (or proved from universal
dual-additivity in a future closure). -/
theorem sum_trace_frobenius_witness
    (hq : 2 ≤ Fintype.card K)
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (one_sub_V : Isogeny W.toAffine W.toAffine)
    (h_one_sub_V_hom : one_sub_V.toAddMonoidHom =
        AddMonoidHom.id _ -
          (verschiebungIsog_of_witness W h_subset).toAddMonoidHom)
    (h_one_sub_isDual : IsDualOf W.toAffine
        one_sub_V (isogOneSub_negFrobenius W hq)) :
    (frobeniusIsog W).toAddMonoidHom +
        (verschiebungIsog_of_witness W h_subset).toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W)
          (isogOneSub_negFrobenius W hq))).toAddMonoidHom := by
  -- Extract the IsDualOf V π from Worker C's Session 5 output.
  have h_V_dual : IsDualOf W.toAffine
      (verschiebungIsog_of_witness W h_subset) (frobeniusIsog W) :=
    verschiebungIsog_of_witness_isDualOf_frobenius W h_subset
  -- Apply the witness-parametric trace identity.
  refine trace_identity_of_dual_chain (frobeniusIsog W)
    (verschiebungIsog_of_witness W h_subset)
    (isogOneSub_negFrobenius W hq) one_sub_V ?_ ?_ h_one_sub_V_hom ?_
  · -- h_dual_comp_right: π(V(P)) = π.degree • P. From IsDualOf's second conjunct.
    intro P
    have h := h_V_dual.2
    -- h : π.comp V = mulByInt π.degree
    have h_hom : ((frobeniusIsog W).comp
        (verschiebungIsog_of_witness W h_subset)).toAddMonoidHom =
        (mulByInt W.toAffine ((frobeniusIsog W).degree : ℤ)).toAddMonoidHom :=
      congrArg Isogeny.toAddMonoidHom h
    have h_app := DFunLike.congr_fun h_hom P
    rw [Isogeny.comp_apply] at h_app
    rw [h_app, mulByInt_apply]
  · -- h_one_sub_α_hom: (1-π).toAddMonoidHom = id - π.toAddMonoidHom
    exact isogOneSub_negFrobenius_toAddMonoidHom W hq
  · -- h_one_sub_one_sub_dual: (1-π)((1-V)(P)) = (1-π).degree • P
    intro P
    have h := h_one_sub_isDual.2
    have h_hom : ((isogOneSub_negFrobenius W hq).comp one_sub_V).toAddMonoidHom =
        (mulByInt W.toAffine
          ((isogOneSub_negFrobenius W hq).degree : ℤ)).toAddMonoidHom :=
      congrArg Isogeny.toAddMonoidHom h
    have h_app := DFunLike.congr_fun h_hom P
    rw [Isogeny.comp_apply] at h_app
    rw [h_app, mulByInt_apply]

/-- **Dual-composition for Frobenius + Verschiebung** (`h_dual_comp` form):
`V(π(P)) = q • P` for every `P : E.Point`. Discharges Worker D's
`h_dual_comp` hypothesis in `degree_quadratic_genuine_addIsog` for the
`α = π` instance. Direct from `verschiebungIsog_of_witness_isDualOf_frobenius`'s
first conjunct + `frobeniusIsog_degree`. -/
theorem dual_comp_frobenius_witness
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (P : W.toAffine.Point) :
    (verschiebungIsog_of_witness W h_subset).toAddMonoidHom
        ((frobeniusIsog W).toAddMonoidHom P) =
      ((frobeniusIsog W).degree : ℤ) • P := by
  have h := (verschiebungIsog_of_witness_isDualOf_frobenius W h_subset).1
  -- h : V.comp π = mulByInt π.degree
  have h_hom : ((verschiebungIsog_of_witness W h_subset).comp
      (frobeniusIsog W)).toAddMonoidHom =
      (mulByInt W.toAffine ((frobeniusIsog W).degree : ℤ)).toAddMonoidHom :=
    congrArg Isogeny.toAddMonoidHom h
  have h_app := DFunLike.congr_fun h_hom P
  rw [Isogeny.comp_apply] at h_app
  rw [h_app, mulByInt_apply]

end HasseWeil
