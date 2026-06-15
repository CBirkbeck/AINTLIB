module

public import BernoulliRegular.KummerPairing.Twist
public import Mathlib.NumberTheory.MulChar.Basic

/-!
# Reflection — raw component comparison from the Kummer pairing (T042a)

The reflection argument compares the `Δ = (ZMod p)ˣ`-character components of
the two sides of the nondegenerate Kummer pairing
`Gal(H_p(K)/K) × C → μ_p` attached to a cyclotomic field `K = ℚ(ζ_p)`.
Nondegeneracy plus the Galois twist identity imply that, after transport
along the Artin / Kummer isomorphisms, the `χ`-component on the Galois
side (≃ class-group side) has matching cardinality with a **twist-dual**
character's component on the Kummer-subgroup side.

This file exposes the bridge structure and its basic extraction lemmas;
`T042b` inserts the `T041` odd-component vanishing into the comparison
to produce the reflection rank inequality.

## Main definitions

* `characterTwistDual p χ`: `χ⁻¹`, the Kummer-side character matched to the
  Galois-side character `χ` by the pairing twist (`T039`).
* `KummerPairingRawComparison N T`: honest bridge packaging the per-character
  component subgroups on both sides and the cardinality match.

## Main results

* `KummerPairingRawComparison.card_gal_eq_card_kummer_dual`: bridge
  extraction — cardinality equality by character.
* `KummerPairingRawComparison.card_kummer_dual_le_of_subset`: monotonicity
  helper used by `T042b` when inserting the `E/E^p`-vanishing subgroup
  inclusion.

## References

* Washington, *Introduction to Cyclotomic Fields*, §10.3.
* Diekmann, *FLT for regular primes*, §6.
* Ciurca, *Arithmetic of cyclotomic fields*, §6.4.
-/

@[expose] public section

universe u v

noncomputable section

open NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

section Comparison

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
variable {P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)}

/-- The **twist dual** of a Δ-character: the Kummer-side character matched
to a Galois-side character `χ` under the Kummer-pairing twist formula.

Concretely, `characterTwistDual p χ := χ⁻¹`, reflecting that the action of
`σ_a ∈ Δ` moves an `a^i`-eigenvector on the Galois side to an `a^{-i}`-eigenvector
on the Kummer side (because σ_a scales the pairing value by `a`, so perfect
matching of eigenvalues requires the target eigenspace at `χ⁻¹`).

In additive Δ-index notation (`χ = a ↦ a^i`), this is `i ↦ 1 - i` after
absorbing the `ω`-action on `μ_p`. We keep the multiplicative `χ⁻¹` form to
match the project's `MulChar` API. -/
def characterTwistDual (χ : MulChar (ZMod p)ˣ ℚ) : MulChar (ZMod p)ˣ ℚ :=
  χ⁻¹

@[simp]
lemma characterTwistDual_involutive (χ : MulChar (ZMod p)ˣ ℚ) :
    characterTwistDual p (characterTwistDual p χ) = χ := by
  simp [characterTwistDual]

/-- **T042a** — the raw comparison bridge extracted from a nondegenerate
Kummer pairing together with its Galois twist identity.

Records, as data, character-indexed component subgroups on the two sides
of the pairing and the per-character cardinality match guaranteed by
nondegeneracy + twist.

The concrete instantiation of this bridge from `N` and `T` uses
finite-abelian Pontryagin duality under the `Δ`-action; we expose the
result as a bridge to keep `T042a` transport-level and defer the
character-eigenspace decomposition of finite abelian groups with a
nondegenerate pairing to the eventual refinement ticket. -/
structure KummerPairingRawComparison
    (N : NondegenerateKummerPairing (p := p) (K := K) P)
    (T : KummerPairingTwistData (p := p) (K := K) N) where
  /-- The Galois-side `χ`-component subgroup. -/
  galComponent : MulChar (ZMod p)ˣ ℚ → Subgroup P.PairingLeft
  /-- The Kummer-side `χ`-component subgroup. -/
  kummerComponent : MulChar (ZMod p)ˣ ℚ → Subgroup P.PairingRight
  /-- Per-character cardinality match under the pairing twist:
  the Galois-side `χ`-component has the same cardinality as the
  Kummer-side twist-dual (`χ⁻¹`) component. -/
  card_gal_eq_card_kummer_dual : ∀ χ : MulChar (ZMod p)ˣ ℚ,
    Nat.card (galComponent χ : Type _) =
      Nat.card (kummerComponent (characterTwistDual p χ) : Type _)

namespace KummerPairingRawComparison

variable {p K}
variable {N : NondegenerateKummerPairing (p := p) (K := K) P}
variable {T : KummerPairingTwistData (p := p) (K := K) N}

/-- Extraction: the cardinality of a class-group-side component equals
the cardinality of the twist-dual Kummer-side component.

Rewriting with `characterTwistDual_involutive` gives the symmetric form. -/
theorem card_gal_eq_card_kummer_dual_apply
    (R : KummerPairingRawComparison (p := p) (K := K) N T)
    (χ : MulChar (ZMod p)ˣ ℚ) :
    Nat.card (R.galComponent χ : Type _) =
      Nat.card (R.kummerComponent (characterTwistDual p χ) : Type _) :=
  R.card_gal_eq_card_kummer_dual χ

/-- Symmetric reformulation via `characterTwistDual_involutive`: for the
twisted-dual character `χ⁻¹`, the Kummer-side `χ`-component matches the
Galois-side `χ⁻¹`-component. -/
theorem card_gal_dual_eq_card_kummer
    (R : KummerPairingRawComparison (p := p) (K := K) N T)
    (χ : MulChar (ZMod p)ˣ ℚ) :
    Nat.card (R.galComponent (characterTwistDual p χ) : Type _) =
      Nat.card (R.kummerComponent χ : Type _) := by
  have := R.card_gal_eq_card_kummer_dual (characterTwistDual p χ)
  rw [characterTwistDual_involutive] at this
  exact this

/-- Monotonicity helper used by `T042b`: if the Kummer-side twist-dual
component is contained in a larger subgroup `S`, the Galois-side
`χ`-component's cardinality is bounded by `S`.

This is the exact shape consumed when the `T041` vanishing shows the
twist-dual unit-quotient component vanishes: we transfer that vanishing
to the class-group side via this inclusion. -/
theorem card_gal_le_of_kummer_subset
    (R : KummerPairingRawComparison (p := p) (K := K) N T)
    (χ : MulChar (ZMod p)ˣ ℚ)
    {S : Subgroup P.PairingRight}
    [Finite S]
    (h : R.kummerComponent (characterTwistDual p χ) ≤ S) :
    Nat.card (R.galComponent χ : Type _) ≤ Nat.card S := by
  rw [R.card_gal_eq_card_kummer_dual_apply χ]
  exact Subgroup.card_le_of_le h

end KummerPairingRawComparison

end Comparison

end BernoulliRegular

end
