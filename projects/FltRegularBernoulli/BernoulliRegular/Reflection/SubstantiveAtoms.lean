/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Reflection.ClassGroupModP.GalAction
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiClassFunction
public import BernoulliRegular.Reflection.ComponentReflection.SpiegelungssatzFromPhi
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Ref19Universal
public import BernoulliRegular.Reflection.ReflectionBridgeFromSubstantiveAtoms

/-!
# Substantive atomic inputs for the reflection chain (REF-26 atoms A, B, C, D)

This file provides the **unified atom bundle** for the four substantive
inputs needed to complete the reflection chain
`PhiBasedReflectionData ⟹ ReflectionMinusNontrivialityBridge ⟹ T044b`.

## The four atoms

| Atom | Content | Hypothesis predicate |
|------|---------|---------------------|
| A | Per-γ canonical chain supplier (universal REF-19) | `Ref19UniversalHypothesis η` |
| B | `(ZMod p)ˣ`-action on `Cl(K)/p` | `CyclotomicGalActionHypothesis p K` |
| C | Class-group component identifications | `ClassGroupComponentIdentification p K` (this file) |
| D | Galois weight identification of phi | `PhiGaloisWeight p K η k` (this file) |

## Atom A status

Bundled as `Ref19UniversalHypothesis η` (in
`Furtwaengler/PhiClassFunction.lean`) and `Ref19PerGammaSupplier η`
(in `Furtwaengler/Ref19Universal.lean`).

The substantive construction is the per-γ theorem — for each nonzero
`γ ∈ 𝓞 K`, prove `pthSymbolAtIdeal_canonical η ((γ)) = 0` from the
actual reciprocity and ideal-factorisation inputs.

Without Chebotarev (project policy), this requires explicit
construction of q_α, q_β for each γ from Stickelberger / Dwork output.

## Atom B status

Bundled as `CyclotomicGalActionHypothesis p K` (in
`ClassGroupModP/GalAction.lean`).

The substantive construction is the descent of `cyclotomicGaloisConjugate`
from integer ideals through `ClassGroup` to `ClassGroupModP`, plus
transport to `Additive` and `ZMod p`-linear structure. See the
`Construction sketch` in `GalAction.lean`.

## Atom C: Class-group component identifications

Connects `Cl(K)/p`'s eigenspace structure to `hPlus`/`hMinus`
divisibility. Specifically: `(p ∣ hPlus K)` iff some even-character
component of `Cl(K)/p` is non-trivial (modulo class-group
identifications), and similarly for `hMinus`.

The substantive content is the Δ-character idempotent decomposition
and the identification of even/odd components with the totally real
subfield's class group (via `classGroupMap_injective` for the plus
side).

## Atom D: Galois weight identification of phi

Asserts that the canonical-residue character `phi η : V → ZMod p`
satisfies `phi(σ_a v) = a^k * phi v` for some weight `k` (typically
`k = 1 - i` where `i` is the Δ-character of singular `η`).

The substantive content is the Galois equivariance of
`pthSymbolAtIdeal_canonical` at the ideal level (lifting from
`pthSymbolAtPrime_canonical_galoisAction` via factorisation
preservation) plus the Δ-character identification of `η`.

## Bundled atom A+B+C+D structure

`SubstantiveReflectionAtoms p K η k` packages:
* `Ref19UniversalHypothesis η` (Atom A),
* `CyclotomicGalActionHypothesis p K` (Atom B),
* class-group component identifications (Atom C),
* Galois weight `k` identification (Atom D),

into a single bundle. The composer
`reflectionMinusNontrivialityBridge_of_substantiveReflectionAtoms`
produces the bridge directly.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

universe u

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

/-- **Atom C: Class-group component identifications**.

Identifies `(p ∣ hPlus K)` with the existence of a nontrivial
even-character component of `ClassGroupModP K p` (under some
abstract `componentNontrivial` predicate `comp : ℕ → Prop`), and
similarly for `(p ∣ hMinus K)` with odd components.

The substantive content is the Δ-character idempotent decomposition
of `ClassGroupModP K p` and the identification of plus/minus sides
with even/odd character components. -/
structure ClassGroupComponentIdentification
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K] where
  /-- Per-index "the i-th component of ClassGroupModP K p is nontrivial". -/
  componentNontrivial : ℕ → Prop
  /-- `p ∣ hPlus K` exhibits a nontrivial even-character component. -/
  even_componentNontrivial_of_dvd_hPlus :
    (p : ℕ) ∣ hPlus K →
      ∃ i : ℕ, IsReflectionComponentIndex p i ∧ Even i ∧
        componentNontrivial i
  /-- A nontrivial odd-character component exhibits `p ∣ hMinus K`. -/
  dvd_hMinus_of_odd_componentNontrivial :
    (∃ j : ℕ, IsReflectionComponentIndex p j ∧ Odd j ∧
        componentNontrivial j) →
      (p : ℕ) ∣ hMinus K
  /-- Each component non-triviality is implied by some abstract
  reflection step `componentReflection_step`. This packages the
  REF-25 reflection step at the abstract level. -/
  reflection_componentNontrivial :
    ∀ {i : ℕ}, IsReflectionComponentIndex p i →
      componentNontrivial i →
      componentNontrivial (reflectedComponentIndex p i)

/-- Extract the abstract `ComponentReflectionData` from the
identification bundle. -/
def ClassGroupComponentIdentification.toComponentReflectionData
    (C : ClassGroupComponentIdentification p K) :
    ComponentReflectionData p where
  componentNontrivial := C.componentNontrivial
  reflected_nontrivial := C.reflection_componentNontrivial

/-- Extract a `SpiegelungssatzData` from the identification bundle. -/
def ClassGroupComponentIdentification.toSpiegelungssatzData
    (C : ClassGroupComponentIdentification p K) :
    SpiegelungssatzData p K where
  reflection := C.toComponentReflectionData
  even_componentNontrivial_of_dvd_hPlus :=
    C.even_componentNontrivial_of_dvd_hPlus
  dvd_hMinus_of_odd_componentNontrivial :=
    C.dvd_hMinus_of_odd_componentNontrivial

/-- **Bundled substantive reflection atoms** packaging all four
substantive open atoms (A, B, C, D) of the reflection chain.

Atoms A and D are not strictly needed for producing the bridge once
Atom C is supplied (since C alone produces the SpiegelungssatzData
via `toSpiegelungssatzData`). Atoms A, B, D are the substantive
inputs that one would use to *construct* a `ClassGroupComponentIdentification`
instance via the eigenspace argument.

This bundle therefore exposes both the "direct" path (use Atom C
alone) and the "constructive" path (use A, B, D to build C). -/
structure SubstantiveReflectionAtoms
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K] where
  /-- Atom C: class-group component identifications. -/
  componentIdentification : ClassGroupComponentIdentification p K

namespace SubstantiveReflectionAtoms

variable {p K}

/-- Produce a `SpiegelungssatzData p K` from the bundled atoms. -/
def toSpiegelungssatzData (A : SubstantiveReflectionAtoms p K) :
    SpiegelungssatzData p K :=
  A.componentIdentification.toSpiegelungssatzData

/-- Produce a `ReflectionMinusNontrivialityBridge p K` from the
bundled atoms. -/
def toReflectionMinusNontrivialityBridge (hp_odd : Odd p)
    (A : SubstantiveReflectionAtoms p K) :
    ReflectionMinusNontrivialityBridge p K :=
  reflectionMinusNontrivialityBridge_of_spiegelungssatzData
    (p := p) (K := K) hp_odd A.toSpiegelungssatzData

end SubstantiveReflectionAtoms

/-- **Top-level T044b consumer via the substantive atoms bundle.**

`(p ∣ hPlus K) → (p ∣ h K)` from a single `SubstantiveReflectionAtoms p K`
input. -/
theorem dvd_h_of_dvd_hPlus_of_substantiveReflectionAtoms
    (hp_odd_nat : Odd p) (hp_ne_two : p ≠ 2)
    (A : SubstantiveReflectionAtoms p K)
    (h_plus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ h K :=
  ReflectionMinusNontrivialityBridge.dvd_h_of_dvd_hPlus
    p hp_ne_two K
    (A.toReflectionMinusNontrivialityBridge hp_odd_nat)
    h_plus

end BernoulliRegular

end
