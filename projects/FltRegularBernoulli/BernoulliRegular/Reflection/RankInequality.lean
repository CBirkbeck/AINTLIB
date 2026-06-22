module

public import BernoulliRegular.Reflection.Comparison
public import BernoulliRegular.UnitQuotient.Vanishing

/-!
# Reflection — rank inequality with vanishing inserted (T042b)

The reflection rank inequality in the form consumed by `T044`: combining the
raw Kummer-pairing comparison (`T042a`) with the `E/E^p` odd-component
vanishing (`T041`), the Galois-side component on the pairing left is
cardinality-bounded by the matching unit-quotient component, and the latter
is trivial for odd non-distinguished characters.

The exact bridge between the abstract Kummer subgroup `P.PairingRight` and
the unit-quotient component from `T041` is deferred to a small honest
interface (`KummerToUnitQuotientInclusion`) so the reflection step does
not depend on a particular concrete embedding of `C ⊂ Kˣ/(Kˣ)^p` into
`(𝒪_K)ˣ/((𝒪_K)ˣ)^p` arising from unramifiedness of the Hilbert `p`-class
field.

## Main definitions

* `KummerToUnitQuotientInclusion`: honest bridge recording, per character,
  that the Kummer-side component sits inside the matching unit-quotient
  component via a cardinality inclusion.

## Main results

* `reflection_gal_card_le`: transport theorem — cardinality upper bound on
  the twist-dual Kummer-side component gives the same bound on the
  Galois-side.
* `reflection_gal_card_le_one_of_oddVanishing`: **T042b** proper — combines
  T042a, T041, and the bridge to conclude that the Galois-side component
  for any character whose twist dual is odd and non-distinguished has
  cardinality at most one.

## References

* Washington, *Introduction to Cyclotomic Fields*, §10.3.
* Diekmann, *FLT for regular primes*, §6.
-/

@[expose] public section

universe u v

noncomputable section

open NumberField

namespace BernoulliRegular

section RankInequality

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
variable {P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)}

/-- Honest bridge recording the inclusion of the Kummer-subgroup component
into the unit-quotient component for each character.

This bridge will be instantiated once the project formalises the
unramifiedness constraint `C ⊂ (𝒪_K)ˣ/((𝒪_K)ˣ)^p` coming from the
Hilbert-class-field presentation. Until then, reflection consumes this
bridge as the exact interface between the Kummer-pairing side and the
unit-quotient side. -/
structure KummerToUnitQuotientInclusion
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    (R : KummerPairingRawComparison (p := p) (K := K) N T)
    (S : CyclotomicUnitModPStructure (p := p) K) where
  /-- Cardinality bound: for each Δ-character, the Kummer-side component's
  cardinality is bounded by the matching unit-quotient component's
  cardinality. -/
  kummer_card_le_unit_card : ∀ χ : MulChar (ZMod p)ˣ ℚ,
    Nat.card (R.kummerComponent χ : Type _) ≤
      Nat.card (S.components.component χ).Carrier

/-- Cardinality transport: from an upper bound on the twist-dual Kummer-side
component, derive the corresponding bound on the Galois side. -/
theorem reflection_gal_card_le
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    (R : KummerPairingRawComparison (p := p) (K := K) N T)
    (χ : MulChar (ZMod p)ˣ ℚ) {n : ℕ}
    (hle : Nat.card (R.kummerComponent (characterTwistDual p χ) : Type _) ≤ n) :
    Nat.card (R.galComponent χ : Type _) ≤ n := by
  rwa [R.card_gal_eq_card_kummer_dual_apply χ]

/-- **T042b**: the reflection rank inequality with vanishing inserted.

For any Δ-character `χ` whose twist dual `χ⁻¹` is odd and distinct from
the distinguished `T041` character (classically `ω`, the Teichmüller-tagging
character), the Galois-side `χ`-component has cardinality at most one.

This is the exact shape consumed by `T044a` (convert the reflection
inequality into a nontrivial minus component). -/
theorem reflection_gal_card_le_one_of_oddVanishing
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    (R : KummerPairingRawComparison (p := p) (K := K) N T)
    {S : CyclotomicUnitModPStructure (p := p) K}
    (V : CyclotomicUnitModPOddVanishing (p := p) K S)
    (Br : KummerToUnitQuotientInclusion (p := p) (K := K) R S)
    {χ : MulChar (ZMod p)ˣ ℚ}
    (hχ_odd_dual : IsOddDeltaCharacter (p := p) (characterTwistDual p χ))
    (hχ_ne_dual : characterTwistDual p χ ≠ V.distinguishedCharacter) :
    Nat.card (R.galComponent χ : Type _) ≤ 1 := by
  have hunit_one :
      Nat.card (S.components.component (characterTwistDual p χ)).Carrier = 1 :=
    V.component_natCard_eq_one hχ_odd_dual hχ_ne_dual
  have hkummer_le :
      Nat.card (R.kummerComponent (characterTwistDual p χ) : Type _) ≤ 1 := by
    have := Br.kummer_card_le_unit_card (characterTwistDual p χ)
    rwa [hunit_one] at this
  exact reflection_gal_card_le (p := p) (K := K) R χ hkummer_le

end RankInequality

end BernoulliRegular

end
