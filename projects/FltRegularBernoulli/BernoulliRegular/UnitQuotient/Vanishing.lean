/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Characters
public import BernoulliRegular.UnitQuotient.Structure

/-!
# Vanishing of odd unit-quotient components

For the cyclotomic field `K = ℚ(ζ_p)`, Dirichlet's unit theorem and Kronecker's theorem
imply that every odd `Δ = (ZMod p)ˣ`-character component of `E / E^p`, except the
torsion component tagged by `ω`, is trivial.

This file packages that conclusion as a certificate on a
`CyclotomicUnitModPStructure` and provides the extraction lemmas used by the reflection
rank inequality. It does not construct the certificate from the unit theorem.

## Main definitions

* `CyclotomicUnitModPOddVanishing S`: a certificate that every odd character of `Δ`,
  other than a distinguished torsion character, has trivial component in `S`.

## Main results

* `CyclotomicUnitModPOddVanishing.component_eq_bot`: an odd nondistinguished component
  has trivial carrier.
* `CyclotomicUnitModPOddVanishing.component_natCard_eq_one`: an odd nondistinguished
  component has cardinality one.

## References

* Washington, *Introduction to Cyclotomic Fields*, §8.
* Diekmann, *FLT for regular primes*, §6.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K]

/-- A certificate that the odd part of the mod-`p` cyclotomic unit quotient is supported
only at one distinguished torsion character. -/
structure CyclotomicUnitModPOddVanishing
    (S : CyclotomicUnitModPStructure (p := p) K) where
  /-- The odd character tagging the torsion subgroup component
  (classically `ω`, the Teichmüller character mod `p`). -/
  distinguishedCharacter : MulChar (CyclotomicUnitDelta p) ℚ
  /-- The distinguished character is odd. -/
  distinguishedOdd : IsOddUnitCharacter (p := p) distinguishedCharacter
  /-- Every other odd character has trivial component. -/
  vanishing : ∀ χ : MulChar (CyclotomicUnitDelta p) ℚ,
    IsOddUnitCharacter (p := p) χ →
    χ ≠ distinguishedCharacter →
    (S.components.component χ).carrier = ⊥

namespace CyclotomicUnitModPOddVanishing

variable {p K}
variable {S : CyclotomicUnitModPStructure (p := p) K}

omit [NumberField K] in
/-- An odd component distinct from the distinguished one has trivial carrier. -/
theorem component_eq_bot (V : CyclotomicUnitModPOddVanishing (p := p) K S)
    {χ : MulChar (CyclotomicUnitDelta p) ℚ}
    (hχ_odd : IsOddUnitCharacter (p := p) χ)
    (hχ_ne : χ ≠ V.distinguishedCharacter) :
    (S.components.component χ).carrier = ⊥ :=
  V.vanishing χ hχ_odd hχ_ne

omit [NumberField K] in
/-- An odd component distinct from the distinguished one has cardinality one. -/
theorem component_natCard_eq_one
    (V : CyclotomicUnitModPOddVanishing (p := p) K S)
    {χ : MulChar (CyclotomicUnitDelta p) ℚ}
    (hχ_odd : IsOddUnitCharacter (p := p) χ)
    (hχ_ne : χ ≠ V.distinguishedCharacter) :
    Nat.card (S.components.component χ).Carrier = 1 := by
  rw [CyclotomicUnitQuotientComponent.Carrier, V.component_eq_bot hχ_odd hχ_ne]
  exact Subgroup.card_bot

end CyclotomicUnitModPOddVanishing

end BernoulliRegular

end
