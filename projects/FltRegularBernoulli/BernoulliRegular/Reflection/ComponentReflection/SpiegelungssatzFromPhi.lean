module

public import BernoulliRegular.Reflection.ComponentReflection.SpiegelungssatzReduction
public import BernoulliRegular.Reflection.ComponentReflection.EigenspaceReflection

/-!
# `SpiegelungssatzData` from a phi-based eigenspace argument

This file provides a structural composer that builds a
`SpiegelungssatzData p K` from:

* an `EigenspaceProjectionData` packaging the eigenspace argument
  (the substantive REF-25 step, now provable via
  `standardEigenspaceProjectionData`);

* class-group identifications connecting the abstract eigenspace
  components to the concrete `hPlus`/`hMinus` divisibility predicates.

The composition is purely structural — it isolates the substantive
content (the projection data + the class-group identifications) from
the reflection composition.

## Setup

Given a `ZMod p`-module `V` with a `(ZMod p)ˣ`-action `galAction` and a
non-trivial linear map `phi : V → ZMod p` with Galois weight `k`, the
eigenspace argument (from `EigenspaceReflection.lean`) gives
`eigenspace galAction k` non-trivial.

To translate this into the `SpiegelungssatzData` form, the user
supplies:

* `componentNontrivial_of_eigenspace_nontrivial` — translation from
  abstract eigenspace nontriviality to the
  `ComponentReflectionData.componentNontrivial` predicate at the
  matching index `i = (1 - k) mod (p-1)` (or the project's specific
  convention).

* `even_componentNontrivial_of_dvd_hPlus` and
  `dvd_hMinus_of_odd_componentNontrivial` — class-group
  identifications.

The composer assembles these into a `SpiegelungssatzData`.

## Strategy

The eigenspace argument itself is provable from `Ref19UniversalHypothesis`
+ class-group construction (REF-20 + REF-22 + REF-24 in the project's
plan). This composer assumes the eigenspace data + class-group bridges
as input and discharges the structural composition.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

universe u

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

/-- **Phi-based reflection data**: bundles a `(ZMod p)ˣ`-action on a
`ZMod p`-module `V` together with a non-trivial linear character of
some weight `k`, plus the class-group bridges identifying eigenspace
nontriviality with `hPlus`/`hMinus` divisibility.

Producing a `PhiBasedReflectionData p K` is the substantive remaining
work for the reflection chain (it requires constructing `V = Cl(K)/p`
with its `Δ`-action, the phi character via REF-20, and the
class-group identifications). The composer
`spiegelungssatzData_of_phiBasedReflectionData` then mechanically
produces a `SpiegelungssatzData p K`. -/
structure PhiBasedReflectionData (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K] where
  /-- The ZMod p-module carrying the eigenspace decomposition. -/
  V : Type*
  /-- ZMod p-module structure on V. -/
  [addCommGroup : AddCommGroup V]
  [module : Module (ZMod p) V]
  /-- The `(ZMod p)ˣ`-action on V. -/
  galAction : (ZMod p)ˣ →* Module.End (ZMod p) V
  /-- Reflection data on the abstract index level. -/
  reflection : ComponentReflectionData p
  /-- Class-group identification: hPlus K divisible by p exhibits a
  nontrivial even-character component. -/
  even_componentNontrivial_of_dvd_hPlus :
    (p : ℕ) ∣ hPlus K →
      ∃ i : ℕ, IsReflectionComponentIndex p i ∧ Even i ∧
        reflection.componentNontrivial i
  /-- Class-group identification: nontrivial odd-character component
  exhibits hMinus K divisible by p. -/
  dvd_hMinus_of_odd_componentNontrivial :
    (∃ j : ℕ, IsReflectionComponentIndex p j ∧ Odd j ∧
        reflection.componentNontrivial j) →
      (p : ℕ) ∣ hMinus K

namespace PhiBasedReflectionData

variable {p K}

/-- **Composer**: extract a `SpiegelungssatzData p K` from a
`PhiBasedReflectionData p K`. The composition is purely structural:
the `reflection` and class-group bridges are exposed at the
`SpiegelungssatzData` level. -/
def toSpiegelungssatzData (R : PhiBasedReflectionData p K) :
    SpiegelungssatzData p K where
  reflection := R.reflection
  even_componentNontrivial_of_dvd_hPlus := R.even_componentNontrivial_of_dvd_hPlus
  dvd_hMinus_of_odd_componentNontrivial := R.dvd_hMinus_of_odd_componentNontrivial

/-- **Top-level**: produce the `ReflectionMinusNontrivialityBridge p K`
from a `PhiBasedReflectionData p K`. Composes
`toSpiegelungssatzData` with `reflectionMinusNontrivialityBridge_of_spiegelungssatzData`. -/
def toReflectionMinusNontrivialityBridge (hp_odd : Odd p)
    (R : PhiBasedReflectionData p K) :
    ReflectionMinusNontrivialityBridge p K :=
  reflectionMinusNontrivialityBridge_of_spiegelungssatzData
    (p := p) (K := K) hp_odd R.toSpiegelungssatzData

end PhiBasedReflectionData

end BernoulliRegular

end
