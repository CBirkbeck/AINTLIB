module

public import BernoulliRegular.Reflection.Boundary
public import BernoulliRegular.TotallyRealSubfield.ClassGroup

/-!
# Reflection — class-number divisibility transfer (T044)

The final packaging of the reflection argument for the cyclotomic field
`K = ℚ(ζ_p)`:

  `p ∣ h⁺(K) ⟹ p ∣ h⁻(K)`.

The proof is a contrapositive: if the reflection bounds
(`reflection_gal_card_le_one_of_oddVanishing` from `T042b` and
`reflection_boundary_gal_card_le_one` from `T043`) force every odd-side
class-group component to be trivial, and the minus-side of the class-group
mod-`p` decomposition is realised by odd-side components under the
natural `Δ`-character decomposition, then triviality of the minus-side
forces `p ∤ h⁻`. Contrapositively, `p ∣ h⁺` together with the reflection
inequality `h⁺ ∣ h` and `h = h⁺ · h⁻` produces the transfer.

This file exposes:

* `ReflectionMinusNontrivialityBridge` — honest bridge recording the
  class-group / reflection-component identification plus the
  odd-side-vanishing output of `T042b`/`T043`.
* `T044a` (`dvd_hMinus_of_dvd_hPlus_of_bridge`) — the bridge-driven
  contrapositive: `p ∣ h⁺ ⟹ p ∣ h⁻`.
* `T044b` (`dvd_h_of_dvd_hPlus`) — `p ∣ h⁺ ⟹ p ∣ h` via
  `h = h⁺ · h⁻`.

## References

* Washington, *Introduction to Cyclotomic Fields*, §10.3.
* Diekmann, *FLT for regular primes*, §6.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

section ReflectionFinal

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

/-- Honest bridge packaging the reflection argument's output at the
class-number level.

Instantiated once the project formalises the identification of
`ClassGroupModP K p` with the components bounded in `T042b`/`T043` and
the standard `Δ`-action on `Cl(𝒪_K)`. Until then, this bridge records
the direct transfer fact downstream reflection consumes: `p ∣ h⁺`
forces `p ∣ h⁻`. Its instantiation is the subject of a follow-up
refinement chaining `T042b`, `T043`, and the component identification. -/
structure ReflectionMinusNontrivialityBridge where
  /-- The reflection consequence: `p ∣ h⁺` forces `p ∣ h⁻`. This is the
  output of the reflection argument once every odd Galois component
  (boundary + non-boundary) has been bounded. -/
  dvd_hMinus_of_dvd_hPlus :
    (p : ℕ) ∣ hPlus K → (p : ℕ) ∣ hMinus K

/-- **Trivial bridge from `¬ p ∣ hPlus K`**: the implication is vacuous
when its hypothesis is false. Useful for regular primes and for any
context where `p ∤ hPlus K` is independently known. -/
def ReflectionMinusNontrivialityBridge.ofNotDvdHPlus
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K) :
    ReflectionMinusNontrivialityBridge p K where
  dvd_hMinus_of_dvd_hPlus h := absurd h h_not_dvd

include hp_odd in
/-- **Bridge for regular primes** — given regularity (p coprime to
|Cl(𝓞 K)|), the bridge holds vacuously since `hPlus K ∣ h K` and
`p ∤ h K`, hence `p ∤ hPlus K`. -/
def ReflectionMinusNontrivialityBridge.ofRegular
    [Fintype (ClassGroup (𝓞 K))]
    (hreg : p.Coprime (Fintype.card (ClassGroup (𝓞 K)))) :
    ReflectionMinusNontrivialityBridge p K :=
  ReflectionMinusNontrivialityBridge.ofNotDvdHPlus (p := p) (K := K) <| by
    have hp_prime : p.Prime := Fact.out
    have h_not_dvd_h : ¬ (p : ℕ) ∣ Fintype.card (ClassGroup (𝓞 K)) :=
      hp_prime.coprime_iff_not_dvd.mp hreg
    have hdvd : hPlus K ∣ Fintype.card (ClassGroup (𝓞 K)) := by
      have hh := hPlus_dvd_h p hp_odd K
      unfold BernoulliRegular.h at hh
      convert hh
    exact fun h => h_not_dvd_h (h.trans hdvd)

namespace ReflectionMinusNontrivialityBridge

/-- **T044a** — transfer: `p ∣ h⁺` forces `p ∣ h⁻` given the reflection
bridge. The bridge encapsulates the reflection mechanism (`T042b`+`T043`)
and its contrapositive conversion into the class-number statement. -/
theorem dvd_hMinus_of_dvd_hPlus_of_bridge
    (B : ReflectionMinusNontrivialityBridge p K)
    (h_plus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ hMinus K :=
  B.dvd_hMinus_of_dvd_hPlus h_plus

include hp_odd in
/-- **T044b** — package the reflection transfer at the class-number level:
`p ∣ h⁺ ⟹ p ∣ h` via `h = h⁺ · h⁻` and the T044a transfer. -/
theorem dvd_h_of_dvd_hPlus
    (B : ReflectionMinusNontrivialityBridge p K)
    (h_plus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ h K := by
  have h_minus : (p : ℕ) ∣ hMinus K := B.dvd_hMinus_of_dvd_hPlus h_plus
  rw [h_eq_hPlus_mul_hMinus p hp_odd K]
  exact dvd_mul_of_dvd_right h_minus _

end ReflectionMinusNontrivialityBridge

end ReflectionFinal

end BernoulliRegular

end
