import «Adic spaces».Presheaf
import «Adic spaces».HuberRings
import «Adic spaces».FJP.FiniteJetScottishBook
import «Adic spaces».FJP.FJPBaseLaurent

/-!
# Nonarchimedean Scottish Book — Problem 28

**Proposer:** Kiran Kedlaya
**Date:** 11 October 2017

## Problem Statement

Do there exist (A, A+) with A Tate/perfectoid and an element f where multiplication by f
is a strict inclusion on A but f restricts to zero on some rational subspace?

## Status

**Answered affirmatively in the Tate case** by the [FJP] finite-jet algebra
(`ScottishBook.problem28`). The perfectoid case remains open — the witness `𝓐` is a
complete uniform *nonnoetherian* Tate domain, not a perfectoid ring.

## The witness

Take `𝓐` the finite-jet ("pinching") algebra over the complete discretely valued field
`K = F((t))`, for an arbitrary field `F`, with `𝓐⁺ = 𝓐°`, the element `f = Q²`, and the
rational subset `U = R(W/ϖ) = {x : |W(x)| ≤ |ϖ(x)| ≠ 0}`. Then:

* the restricted Gauss norm on `𝓐` is multiplicative and `‖Q²‖ = 1`, so
  `‖Q²a − Q²b‖ = ‖a − b‖` — multiplication by `Q²` is an **isometry**, hence injective,
  open onto its image, and (as `𝓐` is complete) with closed image `Q²𝓐`. No
  nonarchimedean open mapping theorem is needed;
* `ρ(Q²) = 0` in `𝒪_X(U) = 𝓐⟨W/ϖ⟩` ([FJP] (3.3): `Q² = ϖⁿXⁿ(W^{−n}Q²)` for every `n`,
  so `Q²` lies in every `ϖⁿ𝓐₀[X]` and dies in the separated completion).

The vanishing is purely a *completion* phenomenon: `ϖ` is already a unit of the Tate ring
`𝓐`, so the algebraic localization `Localization.Away ϖ` is `𝓐` itself, in which
`Q² ≠ 0`. This is why the statement below is phrased with the structure-presheaf value
`presheafValue D` and its canonical map `D.canonicalMap`, not with
`algebraMap A (Localization.Away D.s)`: over the algebraic localization the statement is
satisfiable only degenerately (by a nilpotent `s`, for which `R(T/s)` is empty).

For the same reason the statement records that the rational subset is **nonempty** and
that its chart is a **nonzero** ring, closing the empty-chart loophole.

## Definitions

- **Strict morphism**: a continuous map that is open onto its image (`IsStrictMap`); for
  a strict *inclusion* one additionally asks that the image be closed.
- **Rational subspace restriction**: the image of `f` under the canonical map
  `D.canonicalMap : A →+* presheafValue D` into the completed rational localization
  `A⟨T/s⟩ = 𝒪_X(R(T/s))`.

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problem 28
* Wedhorn, *Adic Spaces*, §6 (Huber/Tate rings), §8.1 (rational localizations)
* [FJP] §3 (Proposition 3.1, Corollary 3.2)
-/

open ValuationSpectrum

namespace ScottishBook

universe u

/-- **A faithful Problem-28 witness**: an element `f` of a Tate ring `A` and a rational
localization datum `D` such that

* `D` is a genuine rational datum cutting out a nonempty subset of `Spa(A, A⁺)` whose
  chart `𝒪_X(R(T/s))` is a nonzero ring (no degenerate loopholes);
* multiplication by `f` is a **strict inclusion**: injective, continuous, open onto its
  image, and with closed image;
* `f` restricts to `0` on that rational subset. -/
def IsProblem28Witness {A : Type u} [CommRing A] [TopologicalSpace A]
    [PlusSubring A] [IsHuberRing A]
    (f : A) (D : RationalLocData A) : Prop :=
  D.IsRational ∧
  (rationalOpen D.T D.s).Nonempty ∧
  Nontrivial (presheafValue D) ∧
  Function.Injective (f * ·) ∧
  Continuous (f * ·) ∧
  IsStrictMap (f * ·) ∧
  IsClosed (Set.range (f * ·)) ∧
  D.canonicalMap f = 0

/-- **The finite-jet algebra is a Problem-28 witness** (with `f = Q²` and the chart datum
`(W; ϖ)`) — the concrete form of `problem28` below. -/
theorem finiteJet_isProblem28Witness (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [FiniteJet.IsFJPBase K] :
    IsProblem28Witness (FiniteJet.scottishWitness K) (FiniteJet.chartDatum K) :=
  FiniteJet.finiteJet_problem28 K

/-- **Scottish Book Problem 28 — affirmative answer (Tate case).**

*There is a Tate Huber pair `(A, A⁺)` with an element `f : A` such that multiplication by
`f` is a strict inclusion — injective, open onto its image, with closed image `fA` — yet
`f` restricts to `0` on a nonempty rational subspace of `Spa(A, A⁺)` with nonzero chart.*

Stated over an arbitrary base: for **every** field `F` (in every universe) the [FJP]
finite-jet algebra over the Laurent series field `K = F((t))` is a witness, with `f = Q²`
and the rational datum `(W; ϖ)`. No hypothesis on `F` — any characteristic, any
cardinality. The equal-characteristic shape `K = F((t))` of the base is the one genuine
restriction, and it is inherited from the finite-jet construction itself
(`FJP/FiniteJetRings.lean`), not from this statement; mixed characteristic (e.g. `ℚ_p`)
would need that construction redone over an abstract complete DVR.

The perfectoid case of the problem is **not** settled by this example. -/
theorem problem28 (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [FiniteJet.IsFJPBase K] :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : PlusSubring A) (_ : IsHuberRing A) (_ : IsTateRing A) (f : A)
      (D : RationalLocData A),
      IsProblem28Witness f D :=
  ⟨FiniteJet.JetA K, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, _, _, finiteJet_isProblem28Witness K⟩

/-- The classical [FJP] base is an instance: `K = F((t))` for any field `F`. Recorded so the
abstract statement above is visibly non-vacuous. -/
theorem problem28_laurentSeries (F : Type u) [Field F] :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : PlusSubring A) (_ : IsHuberRing A) (_ : IsTateRing A) (f : A)
      (D : RationalLocData A),
      IsProblem28Witness f D :=
  problem28 (LaurentSeries F)

end ScottishBook
