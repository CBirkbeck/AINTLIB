module

public import BernoulliRegular.UnitQuotient.Structure

/-!
# Vanishing of odd unit-quotient components

For the cyclotomic field `K = ℚ(ζ_p)`, the Dirichlet-unit theorem plus
Kronecker's theorem on roots of unity force the `Δ = (ZMod p)ˣ`-character
decomposition of `E / E^p` to concentrate in the `ω`-eigenspace (the
"Teichmüller index `j = 1`") on the odd side: every odd character other
than the one tagging the torsion subgroup has trivial component.

The component decomposition is treated as data (see
`CyclotomicUnitQuotientComponentStructure`), so the vanishing is recorded here as a
**predicate** on a given `CyclotomicUnitModPStructure` — a certificate to be supplied —
together with the extraction lemmas downstream callers consume. Deriving that certificate
from the Dirichlet unit theorem and the cyclotomic-unit module structure is not done here.

## Main definitions

* `CyclotomicUnitModPOddVanishing S`: a predicate recording that every
  odd character `χ` of `Δ`, other than a distinguished "torsion-tagging"
  odd character, has trivial `χ`-component in `S`.

## Main results

* `CyclotomicUnitModPOddVanishing.component_eq_bot`: extraction lemma —
  from a vanishing certificate and an odd `χ ≠ distinguishedCharacter`,
  the component carrier is the trivial subgroup.
* `CyclotomicUnitModPOddVanishing.component_natCard_eq_one`: the same
  vanishing phrased at the cardinality level, directly usable by the
  reflection rank inequality.

## References

* Washington, *Introduction to Cyclotomic Fields*, §8.
* Diekmann, *FLT for regular primes*, §6.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

set_option linter.unusedSectionVars false

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K]

/-- A character `χ : Δ → ℚ` is *odd* when `χ(-1) = -1`. This matches the
classical notion that `ε_χ` acts by `-1` on the complex-conjugation
involution. Duplicates the convention `IsOddUnitCharacter` used in the
Stickelberger layer, but avoids importing it to keep `UnitQuotient` light. -/
def IsOddDeltaCharacter (χ : MulChar (CyclotomicUnitDelta p) ℚ) : Prop :=
  χ (-1 : (ZMod p)ˣ) = -1

/-- The vanishing predicate for the mod-`p` cyclotomic unit quotient.

Records that the `Δ`-component decomposition of `E/E^p` encoded by `S`
concentrates its odd side at a single distinguished character: every other
odd character has trivial component.

`distinguishedCharacter` is the odd character tagging the torsion
contribution (classically `ω`, the Teichmüller mod `p`). The predicate
`vanishing` then asserts `(S.components.component χ).carrier = ⊥` for every
odd `χ` different from it. -/
structure CyclotomicUnitModPOddVanishing
    (S : CyclotomicUnitModPStructure (p := p) K) where
  /-- The odd character tagging the torsion subgroup component
  (classically `ω`, the Teichmüller character mod `p`). -/
  distinguishedCharacter : MulChar (CyclotomicUnitDelta p) ℚ
  /-- The distinguished character is odd. -/
  distinguishedOdd : IsOddDeltaCharacter (p := p) distinguishedCharacter
  /-- Every other odd character has trivial component. -/
  vanishing : ∀ χ : MulChar (CyclotomicUnitDelta p) ℚ,
    IsOddDeltaCharacter (p := p) χ →
    χ ≠ distinguishedCharacter →
    (S.components.component χ).carrier = ⊥

namespace CyclotomicUnitModPOddVanishing

variable {p K}
variable {S : CyclotomicUnitModPStructure (p := p) K}

/-- **Carrier form**: for a vanishing certificate and an odd character other than the
distinguished one, the component carrier is the trivial subgroup. -/
theorem component_eq_bot (V : CyclotomicUnitModPOddVanishing (p := p) K S)
    {χ : MulChar (CyclotomicUnitDelta p) ℚ}
    (hχ_odd : IsOddDeltaCharacter (p := p) χ)
    (hχ_ne : χ ≠ V.distinguishedCharacter) :
    (S.components.component χ).carrier = ⊥ :=
  V.vanishing χ hχ_odd hχ_ne

/-- **Cardinality form**: the trivial component has cardinality one. This is the shape
the reflection rank inequality consumes. -/
theorem component_natCard_eq_one
    (V : CyclotomicUnitModPOddVanishing (p := p) K S)
    {χ : MulChar (CyclotomicUnitDelta p) ℚ}
    (hχ_odd : IsOddDeltaCharacter (p := p) χ)
    (hχ_ne : χ ≠ V.distinguishedCharacter) :
    Nat.card (S.components.component χ).Carrier = 1 := by
  simp [CyclotomicUnitQuotientComponent.Carrier, V.component_eq_bot hχ_odd hχ_ne]

end CyclotomicUnitModPOddVanishing

end BernoulliRegular

end
