module

public import BernoulliRegular.Reflection.ComponentReflection.Basic
public import BernoulliRegular.Reflection.Final

/-!
# Spiegelungssatz structural reduction (REF-25 + REF-26)

This file packages the **structural** reduction from
`ComponentReflectionData p` (the abstract per-component reflection
principle) plus a class-group identification of `hPlus`/`hMinus` with
even/odd components, into the
`ReflectionMinusNontrivialityBridge p K` consumed by `T044a`/`T044b`.

The reduction isolates the **substantive content** — the class-group
identification (`even_componentNontrivial_of_dvd_hPlus` and
`dvd_hMinus_of_odd_componentNontrivial`) — from the **purely structural**
Spiegelungssatz composition, which is just `exists_odd_nontrivial_of_nontrivial`
plus modus ponens.

## Structure

`SpiegelungssatzData p K` packages:

* a `ComponentReflectionData p` carrying the per-component reflection
  principle `componentNontrivial i → componentNontrivial (p - i)`;
* the translation `(p ∣ hPlus K) → ∃ valid even i, componentNontrivial i`,
  which identifies `hPlus K`'s `p`-divisibility with the existence of a
  nontrivial even-character component (the plus-side of the class group);
* the translation `(∃ valid odd j, componentNontrivial j) → (p ∣ hMinus K)`,
  which identifies the existence of a nontrivial odd-character component
  with `hMinus K`'s `p`-divisibility (the minus-side of the class group).

`reflectionMinusNontrivialityBridge_of_spiegelungssatzData` then composes
these three pieces via `ComponentReflectionData.exists_odd_nontrivial_of_nontrivial`
to produce the final bridge `(p ∣ hPlus K) → (p ∣ hMinus K)`.

## Use case

Once the project formalises (a) the `Δ`-character idempotent decomposition
of `Cl(𝓞 K)/p` and (b) the per-component reflection principle (REF-25 +
REF-25a), the `SpiegelungssatzData` instance follows directly. The
present reduction is a one-line structural composition, so the
substantive remaining work is exactly the construction of the data
fields — *not* the bridge composition itself.

This file therefore eliminates the Spiegelungssatz **composition** as an
open obligation: the bridge is mechanically derivable from the
component-level data.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

universe u

variable (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
variable (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

/-- **Spiegelungssatz data bundle** for the cyclotomic class-number transfer.

Bundles the abstract `ComponentReflectionData p` together with the two
class-group identifications that translate `hPlus` and `hMinus`
divisibility to the existence of nontrivial even / odd components. -/
structure SpiegelungssatzData where
  /-- The abstract per-component reflection data. -/
  reflection : ComponentReflectionData p
  /-- Class-group identification: `p ∣ hPlus K` exhibits a nontrivial
  even-character (plus-side) component at some valid index `i`. -/
  even_componentNontrivial_of_dvd_hPlus :
    (p : ℕ) ∣ hPlus K →
      ∃ i : ℕ, IsReflectionComponentIndex p i ∧ Even i ∧
        reflection.componentNontrivial i
  /-- Class-group identification: a nontrivial odd-character (minus-side)
  component at some valid index `j` exhibits `p ∣ hMinus K`. -/
  dvd_hMinus_of_odd_componentNontrivial :
    (∃ j : ℕ, IsReflectionComponentIndex p j ∧ Odd j ∧
        reflection.componentNontrivial j) →
      (p : ℕ) ∣ hMinus K

namespace SpiegelungssatzData

variable {p hp_odd K}

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- **Bridge from the bundled data.** Composes the three fields of
`SpiegelungssatzData` via `ComponentReflectionData.exists_odd_nontrivial_of_nontrivial`
to produce the `(p ∣ hPlus K) → (p ∣ hMinus K)` implication. -/
theorem dvd_hMinus_of_dvd_hPlus
    (hp_odd : Odd p) (S : SpiegelungssatzData p K)
    (h_plus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ hMinus K := by
  obtain ⟨i, hi_index, _hi_even, h_componentI⟩ :=
    S.even_componentNontrivial_of_dvd_hPlus h_plus
  obtain ⟨j, hj_index, hj_odd, h_componentJ⟩ :=
    S.reflection.exists_odd_nontrivial_of_nontrivial hp_odd hi_index h_componentI
  exact S.dvd_hMinus_of_odd_componentNontrivial ⟨j, hj_index, hj_odd, h_componentJ⟩

end SpiegelungssatzData

/-- **`ReflectionMinusNontrivialityBridge` from `SpiegelungssatzData`.**

The structural reduction: bundle the Spiegelungssatz data, get the
bridge for free. The substantive content is concentrated in the
`SpiegelungssatzData` fields; this constructor is purely structural. -/
def reflectionMinusNontrivialityBridge_of_spiegelungssatzData
    (hp_odd_nat : Odd p) (S : SpiegelungssatzData p K) :
    ReflectionMinusNontrivialityBridge p K where
  dvd_hMinus_of_dvd_hPlus := S.dvd_hMinus_of_dvd_hPlus hp_odd_nat

/-- **`T044b` consumed via the structural reduction.**

`p ∣ hPlus K → p ∣ h K`, packaged through the `SpiegelungssatzData`
reduction. This makes the dependency on the Spiegelungssatz inputs
explicit at the consumer level. -/
theorem dvd_h_of_dvd_hPlus_via_spiegelungssatzData
    (hp_odd_nat : Odd p) (hp_ne_two : p ≠ 2) (S : SpiegelungssatzData p K)
    (h_plus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ h K :=
  ReflectionMinusNontrivialityBridge.dvd_h_of_dvd_hPlus
    p hp_ne_two K
    (reflectionMinusNontrivialityBridge_of_spiegelungssatzData
      (p := p) (K := K) hp_odd_nat S)
    h_plus

end BernoulliRegular

end
