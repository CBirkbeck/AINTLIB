module

public import BernoulliRegular.Reflection.RankInequality

/-!
# Kummer-to-unit-quotient inclusion: atomic refinement

This file refines the honest bridge `KummerToUnitQuotientInclusion`
(see `BernoulliRegular.Reflection.RankInequality`) into smaller,
mathematically-meaningful atomic predicates.

## Mathematical content

The Hilbert `p`-class field `L = H_p(K)` over `K = ℚ(ζ_p)` has Galois
group `Gal(L/K) ≃ A/A^p`, the `p`-quotient of the class group.  Kummer
theory presents `L = K(C^{1/p})` for some subgroup `C ⊂ Kˣ/(Kˣ)^p`.

The key mathematical fact is:

> `L/K` is **unramified** ⟺ every class in `C` is represented by a unit
> in `(𝓞_K)ˣ`, modulo `p`-th powers.

In other words, the inclusion `(𝓞_K)ˣ ↪ Kˣ` induces a surjection
`(𝓞_K)ˣ / ((𝓞_K)ˣ)^p ↠ C` (and the lifted map `C → (𝓞_K)ˣ / ((𝓞_K)ˣ)^p`
is an injection that, in the standard formulation, gives the embedding
of the Kummer subgroup into the unit-quotient).

At the `Δ = (ZMod p)ˣ`-character level, this gives, for every character
`χ`, an injective group homomorphism

  `R.kummerComponent χ  →  S.components.component χ`

between the matched per-character pieces.  Cardinality monotonicity then
yields the inequality recorded by `KummerToUnitQuotientInclusion`.

## Refinement strategy

We refine the existing `KummerToUnitQuotientInclusion` bridge into:

* `KummerToUnitQuotientPerCharacterEmbedding` — a single atomic predicate
  recording, for one character, the existence of an injective group hom
  `R.kummerComponent χ → S.components.component χ`.  This is the
  honest mathematical content arising from the unramifiedness of the
  Hilbert Kummer extension at the χ-eigenspace level.

* `KummerToUnitQuotientEmbeddingData` — the χ-indexed family of these
  per-character embeddings, packaged as a single bundle.

* `kummerToUnitQuotientInclusion_of_embeddingData` — the construction
  showing how this richer per-character embedding data implies the
  cardinality form `KummerToUnitQuotientInclusion`.

## What this buys

* The cardinality form `KummerToUnitQuotientInclusion` is now a
  consequence of the **mathematically substantive** per-character
  injection data.
* The per-character embedding is the honest interface that the future
  unramifiedness construction (from component-extension data / `ComponentUnramifiedCyclic
  DegreePExtension`) must supply.  Constructing it is now cleanly
  isolated as a single atomic Lean obligation per character.
* Downstream callers can consume either the cardinality bound directly
  (matching the existing `T042b` shape) or the richer per-character
  embedding.

## References

* Washington, *Introduction to Cyclotomic Fields*, §10.2-10.3
  (unramifiedness ⇔ unit representation in Kummer theory).
* Diekmann, *FLT for regular primes*, §6.
* Borevich-Shafarevich, §4.9.
-/

@[expose] public section

universe u v

noncomputable section

open NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

section KummerToUnitQuotient

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
variable {P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)}

/-- **Per-character embedding data for one Δ-character `χ`.**

This is the atomic mathematical content of the inclusion
`KummerToUnitQuotientInclusion`, restricted to a single character.

It carries an injective group homomorphism from the Kummer-side
`χ`-component into the unit-quotient `χ`-component carrier.  The honest
mathematical input is exactly such a map, which arises from
unramifiedness of the Hilbert Kummer extension `L = K(C^{1/p})/K`:
unramifiedness forces every class in `C` to be represented mod `p`-th
powers by a unit of `𝓞_K`, and the resulting unit class lies in the
matching χ-eigenspace by Δ-equivariance.

The downstream cardinality bound used by `T042b` is a direct corollary
(see `KummerToUnitQuotientPerCharacterEmbedding.kummer_card_le_unit_card`).
-/
structure KummerToUnitQuotientPerCharacterEmbedding
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    (R : KummerPairingRawComparison (p := p) (K := K) N T)
    (S : CyclotomicUnitModPStructure (p := p) K)
    (χ : MulChar (ZMod p)ˣ ℚ) where
  /-- The honest group homomorphism encoding the Kummer-to-unit-quotient
  embedding at the `χ`-eigenspace level. -/
  toFun : R.kummerComponent χ →* (S.components.component χ).Carrier
  /-- The map is injective — the substantive mathematical content
  (separation: a Kummer class represented by a `p`-th power of a unit
  is a `p`-th power in `K`, when `K = ℚ(ζ_p)`). -/
  injective : Function.Injective toFun

namespace KummerToUnitQuotientPerCharacterEmbedding

variable {p K}
variable {N : NondegenerateKummerPairing (p := p) (K := K) P}
variable {T : KummerPairingTwistData (p := p) (K := K) N}
variable {R : KummerPairingRawComparison (p := p) (K := K) N T}
variable {S : CyclotomicUnitModPStructure (p := p) K}

/-- **Cardinality corollary at one character.**

Given an injective per-character embedding into the unit quotient, the
Kummer-side `χ`-component has cardinality bounded by the unit-quotient
`χ`-component.

The unit-quotient component carrier is finite — its cardinality is
`p ^ (torsion + N · free)` by `CyclotomicUnitQuotientComponent.natCard_eq_pow`.
We use `Nat.card_le_card_of_injective`, supplying the finiteness of the
target via `Nat.finite_of_card_ne_zero` from positivity of the prime power. -/
theorem kummer_card_le_unit_card
    {χ : MulChar (ZMod p)ˣ ℚ}
    (E : KummerToUnitQuotientPerCharacterEmbedding (p := p) (K := K) R S χ) :
    Nat.card (R.kummerComponent χ : Type _) ≤
      Nat.card (S.components.component χ).Carrier := by
  -- The target is finite: its cardinality is a power of p, hence positive,
  -- hence nonzero, so `Nat.finite_of_card_ne_zero` produces the instance.
  have hcard :
      Nat.card (S.components.component χ).Carrier =
        p ^ (S.components.torsionContribution χ +
              1 * S.components.freeContribution χ) := by
    -- `S : CyclotomicUnitModPStructure (p := p) K = CyclotomicUnitQuotientStructure
    -- (p := p) (N := 1) K`, so the structure cardinality lemma applies with `N = 1`.
    exact CyclotomicUnitQuotientStructure.component_natCard_eq_pow
      (p := p) (N := 1) (K := K) S χ
  have hpos : 0 < Nat.card (S.components.component χ).Carrier := by
    rw [hcard]
    exact Nat.pos_of_ne_zero
      (pow_ne_zero _ (Nat.Prime.ne_zero Fact.out))
  haveI : Finite (S.components.component χ).Carrier := by
    apply Nat.finite_of_card_ne_zero hpos.ne'
  exact Nat.card_le_card_of_injective E.toFun E.injective

end KummerToUnitQuotientPerCharacterEmbedding

/-- **Per-character embedding data, χ-indexed bundle.**

A χ-indexed family of `KummerToUnitQuotientPerCharacterEmbedding`
witnesses, packaged as a single bundle ready to be supplied by the
downstream construction (from component-extension data unramifiedness).

This is strictly stronger than the cardinality bridge
`KummerToUnitQuotientInclusion`: the per-character embeddings are
honest group homomorphisms, not just a numerical inequality.  Building
a cardinality-only bridge from this data is immediate via
`toInclusion`.
-/
structure KummerToUnitQuotientEmbeddingData
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    (R : KummerPairingRawComparison (p := p) (K := K) N T)
    (S : CyclotomicUnitModPStructure (p := p) K) where
  /-- The per-character embedding data, one for every Δ-character. -/
  embedding : ∀ χ : MulChar (ZMod p)ˣ ℚ,
    KummerToUnitQuotientPerCharacterEmbedding (p := p) (K := K) R S χ

namespace KummerToUnitQuotientEmbeddingData

variable {p K}
variable {N : NondegenerateKummerPairing (p := p) (K := K) P}
variable {T : KummerPairingTwistData (p := p) (K := K) N}
variable {R : KummerPairingRawComparison (p := p) (K := K) N T}
variable {S : CyclotomicUnitModPStructure (p := p) K}

/-- The cardinality bound at every character, extracted from the
per-character embedding data. -/
theorem kummer_card_le_unit_card
    (D : KummerToUnitQuotientEmbeddingData (p := p) (K := K) R S)
    (χ : MulChar (ZMod p)ˣ ℚ) :
    Nat.card (R.kummerComponent χ : Type _) ≤
      Nat.card (S.components.component χ).Carrier :=
  KummerToUnitQuotientPerCharacterEmbedding.kummer_card_le_unit_card
    (p := p) (K := K) (R := R) (S := S) (D.embedding χ)

/-- **Refinement bridge: per-character embedding data implies the
cardinality-only inclusion.**

This shows that the existing `KummerToUnitQuotientInclusion` bridge,
which `T042b` consumes, is a strict consequence of supplying honest
per-character group injections.  In particular, any future construction
of `KummerToUnitQuotientEmbeddingData` from component-extension data / unramifiedness
automatically discharges `KummerToUnitQuotientInclusion` and hence
`T042b`. -/
def toInclusion
    (D : KummerToUnitQuotientEmbeddingData (p := p) (K := K) R S) :
    KummerToUnitQuotientInclusion (p := p) (K := K) R S where
  kummer_card_le_unit_card χ := D.kummer_card_le_unit_card χ

end KummerToUnitQuotientEmbeddingData

/-- **Top-level constructor**: given per-character embedding data,
produce the `KummerToUnitQuotientInclusion` bridge.

This is the named entry point that downstream files can use to build
the bridge from the substantive mathematical content. -/
def kummerToUnitQuotientInclusion_of_embeddingData
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    {R : KummerPairingRawComparison (p := p) (K := K) N T}
    {S : CyclotomicUnitModPStructure (p := p) K}
    (D : KummerToUnitQuotientEmbeddingData (p := p) (K := K) R S) :
    KummerToUnitQuotientInclusion (p := p) (K := K) R S :=
  D.toInclusion

end KummerToUnitQuotient

end BernoulliRegular

end
