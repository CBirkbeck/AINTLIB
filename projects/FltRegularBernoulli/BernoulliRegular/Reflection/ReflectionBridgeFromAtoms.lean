module

public import BernoulliRegular.Reflection.ComponentReflection.SpiegelungssatzReduction
public import BernoulliRegular.Reflection.ComponentReflection.EigenspaceReflection

/-!
# Reflection bridge from atomic data (top-level structural composer)

This file packages the **complete structural composition** that derives
`ReflectionMinusNontrivialityBridge p K` from the atomic data:

  * `SpiegelungssatzData p K` — bundles per-component reflection data
    + class-group identifications (`hPlus`/`hMinus` ↔ even/odd
    components),

producing the bridge `(p ∣ hPlus K) → (p ∣ hMinus K)` consumed by
`T044a`/`T044b`.

This composition is **purely structural** — the substantive content is
contained in the atomic input data (in particular, the
`ComponentReflectionData` reflection step and the class-group
identifications). The substantive content can in turn be assembled
from the eigenspace argument (`EigenspaceProjectionData` from
`EigenspaceReflection.lean`), the universal REF-19 hypothesis
(`Ref19UniversalHypothesis` from `PhiClassFunction.lean`), and
class-field-theoretic identifications.

## Composition map

```
  Ref19UniversalHypothesis η  -- REF-20 well-definedness
  + ClassGroup → ZMod p map  -- REF-23 / REF-24
  + EigenspaceProjectionData -- REF-25 (substantive eigenspace step)
  ────────────────────────────────────
  ⟹ ComponentReflectionData p

  + class-group component identifications (hPlus / hMinus)
  ────────────────────────────────────
  ⟹ SpiegelungssatzData p K

  + (purely structural composition)
  ────────────────────────────────────
  ⟹ ReflectionMinusNontrivialityBridge p K  (T044a / T044b ready)
```

## File scope

This file does not introduce new substantive reasoning — it composes
the existing structural pieces. The substantive open content remaining
is *inside* `SpiegelungssatzData`'s fields, not in the composition.

For consumers that already hold a `SpiegelungssatzData` (e.g. via the
class-field-theoretic refinement of component-extension `componentExtension_nonempty`),
this file's `reflectionMinusNontrivialityBridge_of_spiegelungssatzData`
gives the bridge in one step.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

universe u

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

/-- **End-to-end reduction**: produce a `ReflectionMinusNontrivialityBridge p K`
from a `SpiegelungssatzData p K`. Direct re-export of
`reflectionMinusNontrivialityBridge_of_spiegelungssatzData` from
`SpiegelungssatzReduction.lean`, presented at the top level of the
reflection bridge stack. -/
def ReflectionMinusNontrivialityBridge.ofSpiegelungssatzData
    (hp_odd : Odd p) (S : SpiegelungssatzData p K) :
    ReflectionMinusNontrivialityBridge p K :=
  reflectionMinusNontrivialityBridge_of_spiegelungssatzData
    (p := p) (K := K) hp_odd S

/-- **Top-level T044b consumer from `SpiegelungssatzData`.**
Direct application: `(p ∣ hPlus K) → (p ∣ h K)` via the bridge derived
from a `SpiegelungssatzData` instance. -/
theorem dvd_h_of_dvd_hPlus_of_spiegelungssatzData
    (hp_odd_nat : Odd p) (hp_ne_two : p ≠ 2) (S : SpiegelungssatzData p K)
    (h_plus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ h K :=
  ReflectionMinusNontrivialityBridge.dvd_h_of_dvd_hPlus
    p hp_ne_two K
    (ReflectionMinusNontrivialityBridge.ofSpiegelungssatzData
      (p := p) (K := K) hp_odd_nat S)
    h_plus

/-- **Component nontriviality from the SpiegelungssatzData reflection.**
Wrapper exposing the per-component reflection: if some valid component is
nontrivial, an odd component is also nontrivial.  This is the structural
content of the reflection step underlying `dvd_hMinus_of_dvd_hPlus`. -/
theorem SpiegelungssatzData.exists_odd_componentNontrivial_of_componentNontrivial
    {p K} {_ : Fact p.Prime} {_ : Field K} {_ : NumberField K}
    {_ : IsCyclotomicExtension {p} ℚ K} {_ : IsCMField K}
    (hp_odd : Odd p) (S : SpiegelungssatzData p K)
    {i : ℕ} (hi : IsReflectionComponentIndex p i)
    (h_nontrivial : S.reflection.componentNontrivial i) :
    ∃ j : ℕ, IsReflectionComponentIndex p j ∧ Odd j ∧
      S.reflection.componentNontrivial j :=
  S.reflection.exists_odd_nontrivial_of_nontrivial hp_odd hi h_nontrivial

end BernoulliRegular

end
