module

public import Mathlib.NumberTheory.NumberField.CMField
public import BernoulliRegular.Reflection.KummerToUnitQuotient
public import BernoulliRegular.HilbertClassField

/-!
# Kummer-to-unit-quotient: component-extension unit lifts

This file refines the per-character embedding bridge
`KummerToUnitQuotientPerCharacterEmbedding` (introduced in
`BernoulliRegular.Reflection.KummerToUnitQuotient`) into smaller, mathematically
meaningful atomic predicates that decompose the Kummer-theoretic construction
into independent obligations.

The full construction the project ultimately needs is:

> Given component-refined unramified cyclic degree-`p` extension data, for
> each Δ-character `χ`, build an injective group homomorphism from the
> `χ`-component of the Kummer subgroup `C ⊂ Kˣ/(Kˣ)^p` into the `χ`-component
> of the unit quotient `(𝓞_K)ˣ/((𝓞_K)ˣ)^p`.

Mathematically, this proceeds in several steps:

1. **Kummer presentation.** For each non-trivial χ-component of the class group
   carrying an unramified cyclic degree-`p` extension `E/K`, Kummer
   theory presents `E = K(γ_χ^{1/p})` for some `γ_χ ∈ Kˣ`, since `K` contains
   `ζ_p` and `[E : K] = p` is cyclic.

2. **Unit lift from unramifiedness.** Because `E/K` is unramified, the Kummer
   class of `γ_χ` has a representative in `(𝓞_K)ˣ` modulo `p`-th powers
   (Washington, §10.2; the standard "unramified ⟺ unit Kummer generator"
   characterisation).

3. **χ-eigenspace alignment.** The class of the unit lift lives in the matching
   χ-eigenspace of the unit quotient, by Δ-equivariance of the Kummer
   correspondence and Artin reciprocity.

4. **Injectivity.** If two Kummer classes have the same unit lift modulo
   `p`-th powers, they are equal in `Kˣ/(Kˣ)^p`, since the inclusion
   `(𝓞_K)ˣ ↪ Kˣ` descends to an injection on the relevant component.

The atomic refinement here introduces:

* `KummerCharacterUnitLift` — the substantive per-character predicate: a group
  homomorphism `R.kummerComponent χ →* (S.components.component χ).Carrier`
  together with its injectivity.

* `KummerCharacterUnitLiftFamily` — the χ-indexed family of these lifts.

* `KummerCharacterUnitLift.toPerCharacterEmbedding` — structural reduction
  to the existing `KummerToUnitQuotientPerCharacterEmbedding`.

* `KummerCharacterUnitLiftFamily.toEmbeddingData` — the family-level reduction
  to the full `KummerToUnitQuotientEmbeddingData`.

* `KummerCharacterUnitLift.ofKummerComponentSubsingleton` — the **trivial-case
  atomic constructor**: whenever the Kummer-side χ-component is itself a
  subsingleton (e.g. χ = 1 or any χ on a class-group component that vanishes),
  the per-character embedding is automatic via the trivial homomorphism, with
  injectivity from `Function.injective_of_subsingleton`.

* `KummerCharacterUnitLiftFamily.ofPointwise` — assemble a family from the
  per-character data.

* `KummerCharacterUnitLiftFamily.ofPartition` — **partition constructor**:
  build a family by choosing, per character, between the trivial-case
  constructor and a supplied non-trivial-case constructor. This isolates
  the only non-trivial obligation as the non-trivial-case input, while
  handling the trivial case uniformly.

## Decomposition into atomic obligations

After this file, the remaining mathematical work to feed component-extension
data into the reflection chain factors as one atomic Lean predicate per non-trivial
character:

* `KummerCharacterNonTrivialUnitLift` — a `KummerCharacterUnitLift`
  obligation specifically for characters where the Kummer-side χ-component
  is non-trivial. This corresponds to the component-extension Kummer-theoretic
  construction.

The trivial χ obligations are handled automatically by
`ofKummerComponentSubsingleton`.

## References

* Washington, *Introduction to Cyclotomic Fields*, §10.2-10.3.
* Diekmann, *FLT for regular primes*, §6.
* Borevich-Shafarevich, §4.9.
-/

@[expose] public section

universe u v

noncomputable section

open NumberField

namespace BernoulliRegular


section KummerCharacterUnitLift

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
variable {P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)}

/-- **Atomic per-character lift predicate.**

This is the substantive mathematical content of the per-character bridge
`KummerToUnitQuotientPerCharacterEmbedding`, refactored as an isolated
predicate-level structure that can be supplied independently for each
character.

It carries exactly the data that the per-character embedding needs:

* a group homomorphism `lift : R.kummerComponent χ →* (S.components.component χ).Carrier`,
  representing the Kummer-class to unit-class lift, and
* injectivity of `lift`, which is the separation property arising from
  the inclusion `(𝓞_K)ˣ ↪ Kˣ` modulo `p`-th powers in the χ-eigenspace.

Equipping every χ with such a lift yields the full
`KummerToUnitQuotientEmbeddingData` package via the family-level reduction
below. -/
structure KummerCharacterUnitLift
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    (R : KummerPairingRawComparison (p := p) (K := K) N T)
    (S : CyclotomicUnitModPStructure (p := p) K)
    (χ : MulChar (ZMod p)ˣ ℚ) where
  /-- The per-character lift homomorphism. -/
  lift : R.kummerComponent χ →* (S.components.component χ).Carrier
  /-- The lift is injective — the substantive separation content. -/
  lift_injective : Function.Injective lift

namespace KummerCharacterUnitLift

variable {p K}
variable {N : NondegenerateKummerPairing (p := p) (K := K) P}
variable {T : KummerPairingTwistData (p := p) (K := K) N}
variable {R : KummerPairingRawComparison (p := p) (K := K) N T}
variable {S : CyclotomicUnitModPStructure (p := p) K}

/-- **Structural reduction**: a `KummerCharacterUnitLift` is exactly the data
needed to populate a `KummerToUnitQuotientPerCharacterEmbedding`. -/
def toPerCharacterEmbedding {χ : MulChar (ZMod p)ˣ ℚ}
    (L : KummerCharacterUnitLift (p := p) (K := K) R S χ) :
    KummerToUnitQuotientPerCharacterEmbedding (p := p) (K := K) R S χ where
  toFun := L.lift
  injective := L.lift_injective

/-- **Trivial-case constructor**: when the Kummer-side χ-component is itself
a subsingleton, the per-character lift is automatic via the trivial
homomorphism.

Mathematical content: this captures the mathematically vacuous case where
the Kummer subgroup has no nontrivial χ-eigenvectors. The non-vacuous cases
are exactly those where the component-extension input produces an unramified
cyclic degree-`p` extension realising the χ-component of the class group. -/
def ofKummerComponentSubsingleton {χ : MulChar (ZMod p)ˣ ℚ}
    [Subsingleton (R.kummerComponent χ : Type _)] :
    KummerCharacterUnitLift (p := p) (K := K) R S χ where
  lift := 1
  lift_injective := Function.injective_of_subsingleton _

/-- The cardinality bound at one character, extracted from a per-character
lift. This is the same as the bound from the per-character embedding. -/
theorem kummer_card_le_unit_card {χ : MulChar (ZMod p)ˣ ℚ}
    (L : KummerCharacterUnitLift (p := p) (K := K) R S χ) :
    Nat.card (R.kummerComponent χ : Type _) ≤
      Nat.card (S.components.component χ).Carrier :=
  KummerToUnitQuotientPerCharacterEmbedding.kummer_card_le_unit_card
    (p := p) (K := K) (R := R) (S := S) L.toPerCharacterEmbedding

end KummerCharacterUnitLift

/-- **Trivial-case atomic constructor at the per-character embedding level.**

Whenever the Kummer-side χ-component is a subsingleton, the per-character
embedding is automatic via the trivial homomorphism, and injectivity holds
vacuously. -/
def kummerToUnitQuotientPerCharacterEmbedding_of_kummerComponent_subsingleton
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    {R : KummerPairingRawComparison (p := p) (K := K) N T}
    {S : CyclotomicUnitModPStructure (p := p) K}
    {χ : MulChar (ZMod p)ˣ ℚ}
    [Subsingleton (R.kummerComponent χ : Type _)] :
    KummerToUnitQuotientPerCharacterEmbedding (p := p) (K := K) R S χ :=
  (KummerCharacterUnitLift.ofKummerComponentSubsingleton
    (p := p) (K := K) (R := R) (S := S) (χ := χ)).toPerCharacterEmbedding

/-- **χ-indexed family of per-character lifts.**

Bundling a `KummerCharacterUnitLift` for every Δ-character produces the data
needed to build the full `KummerToUnitQuotientEmbeddingData` and hence the
`KummerToUnitQuotientInclusion` consumed by `T042b`.

In the actual component-extension construction, the family decomposes into:

* the trivial character `χ = 1`, where the Kummer-side component is
  trivial (handled by `KummerCharacterUnitLift.ofKummerComponentSubsingleton`);

* non-trivial χ on which the class-group χ-component vanishes — again
  trivial Kummer-side component;

* non-trivial χ with non-trivial class-group χ-component, where component-extension
  `ComponentUnramifiedCyclicDegreePExtension` provides the unramified
  cyclic degree-`p` extension whose Kummer presentation supplies the
  generator. -/
structure KummerCharacterUnitLiftFamily
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    (R : KummerPairingRawComparison (p := p) (K := K) N T)
    (S : CyclotomicUnitModPStructure (p := p) K) where
  /-- A per-character unit lift for every Δ-character. -/
  lift : ∀ χ : MulChar (ZMod p)ˣ ℚ,
    KummerCharacterUnitLift (p := p) (K := K) R S χ

namespace KummerCharacterUnitLiftFamily

variable {p K}
variable {N : NondegenerateKummerPairing (p := p) (K := K) P}
variable {T : KummerPairingTwistData (p := p) (K := K) N}
variable {R : KummerPairingRawComparison (p := p) (K := K) N T}
variable {S : CyclotomicUnitModPStructure (p := p) K}

/-- **Family-level structural reduction**: a `KummerCharacterUnitLiftFamily`
constructs the full `KummerToUnitQuotientEmbeddingData`. -/
def toEmbeddingData
    (F : KummerCharacterUnitLiftFamily (p := p) (K := K) R S) :
    KummerToUnitQuotientEmbeddingData (p := p) (K := K) R S where
  embedding χ := (F.lift χ).toPerCharacterEmbedding

/-- The cardinality bound at every character, extracted from the family. -/
theorem kummer_card_le_unit_card
    (F : KummerCharacterUnitLiftFamily (p := p) (K := K) R S)
    (χ : MulChar (ZMod p)ˣ ℚ) :
    Nat.card (R.kummerComponent χ : Type _) ≤
      Nat.card (S.components.component χ).Carrier :=
  KummerToUnitQuotientEmbeddingData.kummer_card_le_unit_card
    (p := p) (K := K) (R := R) (S := S) F.toEmbeddingData χ

/-- **Top-level reduction**: a `KummerCharacterUnitLiftFamily` produces the
`KummerToUnitQuotientInclusion` bridge consumed by `T042b`. -/
def toInclusion
    (F : KummerCharacterUnitLiftFamily (p := p) (K := K) R S) :
    KummerToUnitQuotientInclusion (p := p) (K := K) R S :=
  F.toEmbeddingData.toInclusion

/-- **Pointwise constructor**: assemble a family from per-character data. -/
def ofPointwise
    (lift : ∀ χ : MulChar (ZMod p)ˣ ℚ,
      KummerCharacterUnitLift (p := p) (K := K) R S χ) :
    KummerCharacterUnitLiftFamily (p := p) (K := K) R S where
  lift := lift

/-- **Partition constructor**: build a family by checking, per character,
whether the Kummer-side component is a subsingleton; in that case use the
trivial-case constructor, otherwise use the supplied non-trivial-case input.

This isolates the only non-trivial obligation (`nonTrivialLift`) as the
input that the component-extension Kummer-theoretic construction must supply,
handling the trivial character and any other vanishing-Kummer-side cases
uniformly.

The `ifPos`/`ifNeg` choice uses `Classical.dec`, so this is a noncomputable
constructor. -/
noncomputable def ofPartition
    (nonTrivialLift : ∀ χ : MulChar (ZMod p)ˣ ℚ,
      ¬ Subsingleton (R.kummerComponent χ : Type _) →
      KummerCharacterUnitLift (p := p) (K := K) R S χ) :
    KummerCharacterUnitLiftFamily (p := p) (K := K) R S where
  lift χ := by
    classical
    by_cases h : Subsingleton (R.kummerComponent χ : Type _)
    · exact KummerCharacterUnitLift.ofKummerComponentSubsingleton
        (p := p) (K := K) (R := R) (S := S) (χ := χ)
    · exact nonTrivialLift χ h

/-- **Trivial-character family constructor**: when *every* Kummer-side
χ-component is a subsingleton, the family is built entirely from the
trivial-case constructor — no non-trivial-case input required.

This handles the (degenerate but mathematically possible) case where the
class group of `K` is trivial mod `p`, so the Kummer subgroup `C` is itself
trivial. In particular, this is the regular-prime case as far as the
Kummer-side reflection chain is concerned, after the component-extension input
produces no nontrivial extensions. -/
noncomputable def ofAllTrivial
    (h : ∀ χ : MulChar (ZMod p)ˣ ℚ, Subsingleton (R.kummerComponent χ : Type _)) :
    KummerCharacterUnitLiftFamily (p := p) (K := K) R S :=
  ofPartition (R := R) (S := S) (fun χ habs =>
    absurd (h χ) habs)

end KummerCharacterUnitLiftFamily

/-- **Top-level constructor**: produce the `KummerToUnitQuotientEmbeddingData`
package from a per-character lift family. -/
def kummerToUnitQuotientEmbeddingData_of_unitLiftFamily
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    {R : KummerPairingRawComparison (p := p) (K := K) N T}
    {S : CyclotomicUnitModPStructure (p := p) K}
    (F : KummerCharacterUnitLiftFamily (p := p) (K := K) R S) :
    KummerToUnitQuotientEmbeddingData (p := p) (K := K) R S :=
  F.toEmbeddingData

/-- **Composite top-level constructor**: from a per-character lift family,
produce the cardinality-only inclusion `KummerToUnitQuotientInclusion` that
`T042b` consumes. This compresses the two-step chain
`F → KummerToUnitQuotientEmbeddingData → KummerToUnitQuotientInclusion`. -/
def kummerToUnitQuotientInclusion_of_unitLiftFamily
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    {R : KummerPairingRawComparison (p := p) (K := K) N T}
    {S : CyclotomicUnitModPStructure (p := p) K}
    (F : KummerCharacterUnitLiftFamily (p := p) (K := K) R S) :
    KummerToUnitQuotientInclusion (p := p) (K := K) R S :=
  F.toInclusion

/-! ### component-extension atomic obligation: per-character unit lift for non-trivial χ

The remaining work is to construct a `KummerCharacterUnitLift` for every
character on which the Kummer-side component is non-trivial.

The atomic predicate `KummerCharacterNonTrivialUnitLift` records exactly
this — when the Kummer-side χ-component is non-trivial, there exists a
per-character lift. Its mathematical content is:

* (Kummer presentation) the χ-component of `R.kummerComponent χ` is
  generated by the Kummer class of some `γ_χ ∈ Kˣ` selected from component-extension
  unramified cyclic degree-`p` extension `E_χ = K(γ_χ^{1/p})`;
* (Unit lift) `γ_χ` has a representative `u_χ ∈ (𝓞_K)ˣ` modulo `p`-th
  powers, by unramifiedness of `E_χ/K` (Washington §10.2);
* (χ-eigenspace match) the Kummer class of `γ_χ` and the unit class of
  `u_χ` lie in matching χ-eigenspaces, by Δ-equivariance;
* (Injectivity) the resulting embedding is injective by the separation
  property.

Once the project formalises a `Nonempty (ComponentUnramifiedCyclicDegreePExtension χ C) →
KummerCharacterUnitLift R S χ` constructor for every non-trivial component
`C`, the partition constructor above produces the full family in one
step. -/

/-- **component-extension atomic obligation** at one character: when the Kummer-side
χ-component is non-trivial, there exists a per-character unit lift.

This is the focused, irreducible mathematical obligation that the
Kummer-theoretic refinement of component-extension must discharge. The trivial-case
counterpart is handled by `KummerCharacterUnitLift.ofKummerComponentSubsingleton`,
so the partition constructor `KummerCharacterUnitLiftFamily.ofPartition`
needs only this obligation per non-trivial χ. -/
def KummerCharacterNonTrivialUnitLift
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    (R : KummerPairingRawComparison (p := p) (K := K) N T)
    (S : CyclotomicUnitModPStructure (p := p) K)
    (χ : MulChar (ZMod p)ˣ ℚ) : Prop :=
  ¬ Subsingleton (R.kummerComponent χ : Type _) →
    Nonempty (KummerCharacterUnitLift (p := p) (K := K) R S χ)

/-- **component-extension atomic obligation** at every character: the per-character unit
lift exists for every non-trivial Kummer-side χ-component.

This is the single per-family input that, together with the automatic
trivial-case handler, suffices to build the full
`KummerToUnitQuotientEmbeddingData`. -/
def KummerNonTrivialUnitLiftData
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    (R : KummerPairingRawComparison (p := p) (K := K) N T)
    (S : CyclotomicUnitModPStructure (p := p) K) : Prop :=
  ∀ χ : MulChar (ZMod p)ˣ ℚ,
    KummerCharacterNonTrivialUnitLift (p := p) (K := K) R S χ

/-- **From component-extension atomic obligation to the full embedding data.**

Given a `KummerNonTrivialUnitLiftData` witness — the per-character lift on
every non-trivial Kummer-side χ-component — assemble the full
`KummerToUnitQuotientEmbeddingData` by combining with the automatic
trivial-case handler. -/
noncomputable def kummerToUnitQuotientEmbeddingData_of_nonTrivialUnitLiftData
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    {R : KummerPairingRawComparison (p := p) (K := K) N T}
    {S : CyclotomicUnitModPStructure (p := p) K}
    (D : KummerNonTrivialUnitLiftData (p := p) (K := K) R S) :
    KummerToUnitQuotientEmbeddingData (p := p) (K := K) R S :=
  KummerCharacterUnitLiftFamily.toEmbeddingData
    (KummerCharacterUnitLiftFamily.ofPartition (R := R) (S := S)
      (fun χ hχ => Classical.choice (D χ hχ)))

/-- **From component-extension atomic obligation to the cardinality inclusion.**

Composes `kummerToUnitQuotientEmbeddingData_of_nonTrivialUnitLiftData` with
the cardinality reduction. -/
noncomputable def kummerToUnitQuotientInclusion_of_nonTrivialUnitLiftData
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    {R : KummerPairingRawComparison (p := p) (K := K) N T}
    {S : CyclotomicUnitModPStructure (p := p) K}
    (D : KummerNonTrivialUnitLiftData (p := p) (K := K) R S) :
    KummerToUnitQuotientInclusion (p := p) (K := K) R S :=
  (kummerToUnitQuotientEmbeddingData_of_nonTrivialUnitLiftData
    (p := p) (K := K) (R := R) (S := S) D).toInclusion

/-! ### Explicit component-extension contract

The following Prop bundles the natural input from component-extension data: a per-character,
per-component-extension construction of the unit lift. The intended use is:

* The downstream Kummer-theory work supplies, for every `χ` and every
  `ComponentUnramifiedCyclicDegreePExtension` over the matching χ-component,
  a per-character `KummerCharacterUnitLift`.

* A separate "global hypothesis hookup" then chooses, per non-trivial
  Kummer-side χ-component, a class-group component and an component extension and
  applies this constructor.

The Prop is intentionally per-`(χ, C)` rather than per-`χ`: the actual
Kummer-theoretic refinement reads the component extension data directly (degree,
Galois group, unramifiedness, character matching) and produces the lift.
-/

/-- **Per-component obligation feeding the per-character lift.**

For each Δ-character `χ` and each Sylow-p class-group component `C` whose
component extension is supplied, there exists a `KummerCharacterUnitLift R S χ`.

This is the substantive Kummer-theoretic obligation: turn an component-extension
`ComponentUnramifiedCyclicDegreePExtension` into a per-character unit lift
via the Kummer presentation, unit-generator extraction, χ-eigenspace
matching, and injectivity. -/
def KummerCharacterUnitLift.OfComponentExtensions
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    (R : KummerPairingRawComparison (p := p) (K := K) N T)
    (S : CyclotomicUnitModPStructure (p := p) K) : Prop :=
  ∀ (χ : MulChar (ZMod p)ˣ ℚ)
    (C : CyclotomicFieldClassGroupPSylowComponent (p := p) K),
    C.character = χ →
    Nonempty (ComponentUnramifiedCyclicDegreePExtension.{u, v} (p := p) K χ C) →
    Nonempty (KummerCharacterUnitLift (p := p) (K := K) R S χ)

end KummerCharacterUnitLift

end BernoulliRegular

end
