module

public import BernoulliRegular.Reflection.ComponentReflection.SpiegelungssatzFromPhi
public import BernoulliRegular.Reflection.ComponentReflection.EigenspaceReflection
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiClassFunction
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Ref19Universal
public import BernoulliRegular.Reflection.ReflectionBridgeFromAtoms

/-!
# Reflection bridge from substantive atomic inputs (top-level)

This file packages the **complete reduction** of the
`ReflectionMinusNontrivialityBridge p K` to the substantive atomic
inputs of the reflection chain:

  1. `Ref19UniversalHypothesis η` — universal canonical-symbol vanishing
     on principal ideals (via the canonical chain).

  2. `EigenspaceProjectionData galAction phi k` — eigenspace
     projection data for the substantive REF-25 step (provable via
     `standardEigenspaceProjectionData`).

  3. Class-group identifications:
     - `(p ∣ hPlus K)` ⟹ ∃ even valid `i` with `componentNontrivial i`
       (REF-23-style: even-character components correspond to plus side).
     - ∃ odd valid `j` with `componentNontrivial j` ⟹ `(p ∣ hMinus K)`
       (REF-23-style: odd-character components correspond to minus side).

  4. `ComponentReflectionData p` for the abstract reflection step
     (REF-25-style: `componentNontrivial i ⟹ componentNontrivial (p − i)`).

The composer assembles these into a `ReflectionMinusNontrivialityBridge p K`
ready for `T044b` consumption.

## Substantive content map

| Input | Provided by |
|-------|-------------|
| (1) `Ref19UniversalHypothesis η` | Per-`γ` canonical chain (atoms 1-4). |
| (2) `EigenspaceProjectionData` | `standardEigenspaceProjectionData`. |
| (3) Class-group identifications | The Δ-decomposition of `Cl(K)/p`. |
| (4) `ComponentReflectionData` | REF-25 step from the eigenspace arg. |

The structural composition is **mechanical** — this file performs the
plumbing — and isolates the open substantive content into the four
named atomic inputs above.

## Top-level theorem

`reflectionMinusNontrivialityBridge_of_substantiveAtoms` produces the
bridge from a `PhiBasedReflectionData` (which itself bundles the four
substantive atoms above into a single structure).
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

universe u

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

/-- **Top-level top-level**: produce the `ReflectionMinusNontrivialityBridge p K`
from a single bundled `PhiBasedReflectionData p K`. Direct re-export
for top-level consumption. -/
def ReflectionMinusNontrivialityBridge.ofPhiBasedReflectionData
    (hp_odd : Odd p) (R : PhiBasedReflectionData p K) :
    ReflectionMinusNontrivialityBridge p K :=
  R.toReflectionMinusNontrivialityBridge hp_odd

/-- **`T044b` consumed via `PhiBasedReflectionData`.** Direct
consumption: `(p ∣ hPlus K) → (p ∣ h K)` from a single bundled atomic
input structure. -/
theorem dvd_h_of_dvd_hPlus_of_phiBasedReflectionData
    (hp_odd : Odd p) (hp_ne_two : p ≠ 2) (R : PhiBasedReflectionData p K)
    (h_plus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ h K :=
  ReflectionMinusNontrivialityBridge.dvd_h_of_dvd_hPlus
    p hp_ne_two K
    (ReflectionMinusNontrivialityBridge.ofPhiBasedReflectionData
      (p := p) (K := K) hp_odd R)
    h_plus

/-! ### Documentation: complete substantive content

The substantive remaining content for full component-extension elimination via this
chain reduces to constructing a `PhiBasedReflectionData p K`. This in
turn reduces to:

* **(A) Universal REF-19**: a `Ref19UniversalHypothesis η` for the
  hyperprimary singular `η`. Provided by the per-`γ` canonical chain
  (atoms 1, 2, 3, 4 + per-`γ` choice of (q_α, q_β, etc.)).

* **(B) ZMod p-module + `(ZMod p)ˣ`-action on `Cl(K)/p`**: the natural
  Δ-action on the elementary `p`-quotient of the class group. This is
  standard class-group infrastructure not yet built in mathlib for this
  specific case.

* **(C) Construction of `phi : Cl(K)/p → ZMod p`**: lifted from
  `pthSymbolAtIdeal_canonical η` via REF-19 well-definedness (REF-20)
  and the `p`-th power kill (REF-23 content from `PhiClassFunction`).

* **(D) Galois weight identification**: the Galois weight `k` of `phi`
  (REF-24 content). For singular hyperprimary `η`, this is `1 - i`
  where `i` is the Δ-character of `η`.

* **(E) Class-group identifications**: identifying `Cl(K)/p`'s
  even-character components with `hPlus K`'s `p`-divisibility, and
  odd-character components with `hMinus K`'s `p`-divisibility.

* **(F) Eigenspace projection data**: provided by
  `standardEigenspaceProjectionData` once (B), (C), (D) are in place.

* **(G) `ComponentReflectionData`**: provided by the eigenspace
  argument (REF-25) from (F) plus the eigenspace ↔ component
  identification.

The composer in this file performs the structural assembly of these
inputs into the bridge. -/
end BernoulliRegular

end
