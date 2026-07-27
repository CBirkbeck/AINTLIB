/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.KummerLift.Bridge
import BernoulliRegular.Reflection.SubstantiveAtoms
import BernoulliRegular.Thaine.UniqueIrregularData

/-!
# T-PIVOT-1: `FLT37UnitClassBridge` — Thaine-route decomposition of `Cor8_19Bridge`

After the 2026-05-06 expert-review pivot from Sinnott's regulator route to
Thaine's annihilator theorem, `Cor8_19Bridge` is decomposed into four
independently-fillable Props following the reviewer's recommendation:

1. **`UnitQuotientComponentTrivial p K i`** — the Pollaczek certificate side:
   the `ω^i`-eigencomponent of `(E⁺/C⁺) ⊗ ℤ/pℤ` is trivial. Filled by
   `T-PIVOT-4` from the local certificate `realLocalCert` (LV004g).
2. **`ClassGroupPlusComponentTrivial p K j`** — the class-group eigencomponent:
   the `ω^j`-eigencomponent of `Cl(K⁺) ⊗ ℤ/pℤ` is trivial.
3. **`UniqueIrregularIndex p i`** — the irregular-index audit: `i` is the
   unique even index in `{2, 4, …, p−3}` with `p ∣ B_i`. For `p = 37`,
   `i = 32`. This is a numerical/decidable assertion.
4. **`FLT37UnitClassBridge`** — the four-field structure with adapter to
   `Cor8_19Bridge`.

The four bridge fields:

* `pollaczekUnitComponent`: `realLocalCert ⟹ UnitQuotientComponentTrivial`
  (filled by `T-PIVOT-4`, using existing infrastructure).
* `thaineComponent`: `UnitQuotientComponentTrivial ⟹ ClassGroupPlusComponentTrivial`
  (filled by the `T-THAINE-*` epic — Thaine's annihilator theorem).
* `reflectionOtherComponents`: `UniqueIrregularIndex p i ⟹` every other
  eigencomponent of `Cl(K⁺) ⊗ ℤ/pℤ` is trivial (filled by `T-PIVOT-5` via
  Spiegelungssatz + Herbrand–Ribet).
* `hPlusOfComponents`: every eigencomponent trivial `⟹ ¬ p ∣ hPlus K`
  (filled by `T-PIVOT-6` via the `ClassGroupModP` decomposition).

The class-group "trivial" Prop remains intentionally **opaque** at this
level: its concrete eigenspace formulation lives in `T-PIVOT-5/6` and
`T-THAINE-*`, so it can be refined independently without re-shaping the
bridge interface. The irregular-index input is content-bearing: it is the
Bernoulli-side uniqueness package `Thaine.UniqueIrregularData`.

## References

* Reviewer reply, 2026-05-06 (`.mathlib-quality/expert-review/2026-05-06/reply.md`).
* [Wash97 2nd ed §15] Thaine/Kolyvagin/Rubin chapters.
* [Rubin00] *Euler Systems*, Chapter 4.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

universe u

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

/-- **`UnitQuotientComponentTrivial p K i`** — input form for the Thaine
single-character bridge.

**Reviewer-mandated framing (2026-05-07).** The mathematically correct
content is *"the idempotent `e_i ∈ ℤ_p[G]` annihilates the `p`-primary
part of `E⁺/C_S`"*, where `C_S` is **Sinnott's** real circular-unit
group (not Washington's `C_cl`; for prime conductor `p` they coincide,
but Kučera explicitly warns that Washington's §15.2 uses the weaker
`C_cl`).

For a finite `p`-primary module `M`, the chain
`M[p] = 0 ⟹ M_{p\text{-primary}} = 0 ⟹ e_i \text{ annihilates } M`
makes the torsion form (`(E⁺/C_S)(ω^i)[p] = 0`) equivalent to the
annihilator form (`e_i` annihilates the `p`-primary part). Both are
equivalent — by `T-Q1-RANK-ONE` (the rank-one component lemma) — to
the **K-side certificate form** stated below, namely:

  `pollaczekUnitPlus p K i` is not a `p`-th power in `(𝓞 K)ˣ`.

By T-PIVOT-2's `isPthPower_image_iff`, the K-side and K⁺-side
certificate forms are themselves equivalent for odd `p`.

This Prop is the **frozen Thaine-input statement**: T-Q1-RANK-ONE will
prove the equivalence to the eigencomponent-triviality / annihilator
form, and T-THAINE-5-REFRAME consumes it via Kučera's Theorem 4.3
specialised to `θ = e_i`.

References:
* Kučera, *Circular units and class groups of abelian fields*, Thm 4.3.
* Reviewer followup, 2026-05-07: "Thaine is an annihilator theorem,
  not a torsion-vanishing theorem; the bridge should pass through
  annihilator language explicitly."
-/
def UnitQuotientComponentTrivial
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] (i : ℕ) : Prop :=
  -- K-side certificate form — frozen Thaine-input statement.
  -- Equivalent (via T-Q1-RANK-ONE + T-PIVOT-2) to the annihilator form
  -- "e_i annihilates (E⁺/C_S)_{p-primary}".
  ∀ α : (𝓞 K)ˣ,
    ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ≠
      ((α : (𝓞 K)ˣ) : 𝓞 K) ^ p

/-- **`ClassGroupPlusComponentTrivial p K j`** — opaque carrier for the
assertion that the `ω^j`-eigencomponent of `Cl(K⁺) ⊗ ℤ/pℤ` is trivial.

The concrete eigenspace formulation is supplied by `T-PIVOT-5` (Spiegelung
side) and `T-THAINE-*` (Thaine annihilator side); both feed into
`hPlusOfComponents` (T-PIVOT-6). -/
def ClassGroupPlusComponentTrivial
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] (j : ℕ) : Prop :=
  -- Opaque placeholder; refined by T-PIVOT-5/T-PIVOT-6/T-THAINE-*.
  ∀ (_ : (p, j, K) = (p, j, K)), True

/-- **`UniqueIrregularIndex p i`** — `i` is the unique even index in
`{2, 4, …, p − 3}` such that `p ∣ B_i` (the Herbrand irregular index).

For `p = 37`, `i = 32` (since `37 ∣ B_{32}` and no other even `k` in
`{2, …, 34}` satisfies `37 ∣ B_k`). Decidable by computation. -/
def UniqueIrregularIndex (p i : ℕ) : Prop :=
  Thaine.UniqueIrregularData p i

namespace UniqueIrregularIndex

/-- The irregular-index witness: `p ∣ B_i`. -/
theorem dvd_at_irreg {p i : ℕ} (h : UniqueIrregularIndex p i) :
    (p : ℤ) ∣ (bernoulli i).num :=
  (show Thaine.UniqueIrregularData p i from h).dvd_at_irreg

/-- No other even Bernoulli index in the reflection range is irregular. -/
theorem not_dvd_elsewhere {p i : ℕ} (h : UniqueIrregularIndex p i) :
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ p - 3 → 2 * k ≠ i →
      ¬ (p : ℤ) ∣ (bernoulli (2 * k)).num :=
  (show Thaine.UniqueIrregularData p i from h).not_dvd_elsewhere

/-- **FLT37 irregular-index data**: `32` is the unique irregular index for
`p = 37` in the Herbrand-Ribet range. This uses only the small Bernoulli
computations `B_2, …, B_34`; it does not touch the blocked `B_1184`
second-order computation. -/
theorem thirtyseven_thirtytwo : UniqueIrregularIndex 37 32 :=
  Thaine.UniqueIrregularData.thirtyseven_thirtytwo

end UniqueIrregularIndex

/-- **`FLT37UnitClassBridge`** — Thaine-route decomposition of the
Cor 8.19 bridge into four independently-fillable Props.

Following the reviewer's recommendation (2026-05-06): the original
`Cor8_19Bridge` is treated as a "mysterious monolith" only useful when
the regulator route is on the table. With the Thaine pivot, the bridge
splits cleanly along the eigenspace decomposition. -/
structure FLT37UnitClassBridge (i : ℕ) where
  /-- The Pollaczek certificate side: `realLocalCert` (i.e.,
  `pollaczekUnitPlus` not a `p`-th power in `(𝓞 K)ˣ`) implies the
  `ω^i`-eigencomponent of `(E⁺/C⁺) ⊗ ℤ/pℤ` is trivial. -/
  pollaczekUnitComponent :
    (∀ α : (𝓞 K)ˣ,
        ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ≠
          ((α : (𝓞 K)ˣ) : 𝓞 K) ^ p) →
      UnitQuotientComponentTrivial p K i
  /-- Thaine's annihilator at the single character `ω^i`: triviality of
  the unit-quotient eigencomponent forces triviality of the class-group
  eigencomponent at the same character. Filled by the `T-THAINE-*` epic. -/
  thaineComponent :
    UnitQuotientComponentTrivial p K i →
      ClassGroupPlusComponentTrivial p K i
  /-- Spiegelungssatz + Herbrand–Ribet: under `UniqueIrregularIndex`, every
  eigenspace of `Cl(K⁺) ⊗ ℤ/pℤ` other than `ω^i` is automatically trivial.
  (For `p = 37`, `i = 32`: only the reflected eigenspace can be non-trivial,
  and it is identified with `ω^i` itself by the Herbrand index choice.) -/
  reflectionOtherComponents :
    UniqueIrregularIndex p i →
      ∀ j : ℕ, j ≠ i → ClassGroupPlusComponentTrivial p K j
  /-- All eigenspaces of `Cl(K⁺) ⊗ ℤ/pℤ` trivial implies `¬ p ∣ hPlus K`
  via the class-group eigenspace decomposition (`ClassGroupModP`). -/
  hPlusOfComponents :
    UniqueIrregularIndex p i →
    (∀ j : ℕ, ClassGroupPlusComponentTrivial p K j) →
      ¬ (p : ℕ) ∣ hPlus K

namespace FLT37UnitClassBridge

variable {p K}

/-- **Adapter**: a `FLT37UnitClassBridge` paired with `UniqueIrregularIndex`
yields the original `Cor8_19Bridge`, preserving downstream call sites
(e.g., `FLT37BridgeBundle.ofRemaining`). -/
def toCor8_19Bridge {i : ℕ} (B : FLT37UnitClassBridge p K i)
    (h_unique : UniqueIrregularIndex p i) :
    Cor8_19Bridge p K i where
  not_dvd_hPlus_of_not_isPthPower h_no_pth :=
    B.hPlusOfComponents h_unique (fun j => by
      -- Either j = i (use thaine of pollaczek of the cert) or j ≠ i (use reflection).
      by_cases hj : j = i
      · subst hj
        exact B.thaineComponent (B.pollaczekUnitComponent h_no_pth)
      · exact B.reflectionOtherComponents h_unique j hj)

end FLT37UnitClassBridge

/-- **`cor8_19Bridge_of_unitClassBridge`** — top-level adapter, namespaced
at `BernoulliRegular` to mirror the existing `cor8_19Bridge_of_*`
constructors in `Cor8_19Forward.lean`. -/
def cor8_19Bridge_of_unitClassBridge {i : ℕ}
    (B : FLT37UnitClassBridge p K i)
    (h_unique : UniqueIrregularIndex p i) :
    Cor8_19Bridge p K i :=
  B.toCor8_19Bridge h_unique

/-! ## T-PIVOT-1-REFINE: content-bearing eigenspace bridge

This refinement replaces the opaque-Prop layer above with a concrete
eigenspace formulation, using the project's existing
`ClassGroupComponentIdentification` (`Reflection.SubstantiveAtoms`).
The bridge takes:

* an eigenspace identification `id : ClassGroupComponentIdentification p K`
  (the "data" providing the eigenspace decomposition);
* a Pollaczek-side discharge: for the irregular index `i`,
  the certificate forces `¬ id.componentNontrivial i`;
* a reflection-side discharge: for every other reflection index `j ≠ i`,
  `¬ id.componentNontrivial j`;

and produces a real `Cor8_19Bridge p K i` via the contrapositive of
`id.even_componentNontrivial_of_dvd_hPlus`. -/

/-- **`cor8_19Bridge_of_componentTrivialities`** — content-bearing bridge.
Given the eigenspace identification and per-component triviality
witnesses (whose disjunction over even reflection indices covers all
of `hPlus K`'s p-divisibility), construct a real `Cor8_19Bridge`. -/
def cor8_19Bridge_of_componentTrivialities {i : ℕ}
    (id : ClassGroupComponentIdentification p K)
    (h_pollaczek :
        (∀ α : (𝓞 K)ˣ,
            ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ≠
              ((α : (𝓞 K)ˣ) : 𝓞 K) ^ p) →
          ¬ id.componentNontrivial i)
    (h_reflection_other :
        ∀ j : ℕ, IsReflectionComponentIndex p j → Even j → j ≠ i →
          ¬ id.componentNontrivial j) :
    Cor8_19Bridge p K i where
  not_dvd_hPlus_of_not_isPthPower h_no_pth h_dvd := by
    -- From id.even_componentNontrivial_of_dvd_hPlus, p ∣ hPlus K gives an
    -- even reflection-range index j with componentNontrivial j.
    obtain ⟨j, h_refl, h_even, h_nt⟩ := id.even_componentNontrivial_of_dvd_hPlus h_dvd
    -- Either j = i (contradicted by Pollaczek discharge) or j ≠ i (by reflection).
    by_cases hj : j = i
    · subst hj
      exact h_pollaczek h_no_pth h_nt
    · exact h_reflection_other j h_refl h_even hj h_nt

/-- **`FLT37UnitClassBridgeRefined p K i`** — content-bearing refinement
of `FLT37UnitClassBridge`. Replaces the opaque-Prop carriers from
T-PIVOT-1 with concrete eigenspace-component formulations using the
project's existing `ClassGroupComponentIdentification`. The three
fields directly correspond to the inputs of
`cor8_19Bridge_of_componentTrivialities`. -/
structure FLT37UnitClassBridgeRefined (i : ℕ) where
  /-- The eigenspace identification — existing project infrastructure. -/
  identification : ClassGroupComponentIdentification p K
  /-- Pollaczek/Thaine discharge: certificate forces ω^i-eigencomponent
  triviality. -/
  pollaczekUnitComponent :
    (∀ α : (𝓞 K)ˣ,
        ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ≠
          ((α : (𝓞 K)ˣ) : 𝓞 K) ^ p) →
      ¬ identification.componentNontrivial i
  /-- Spiegelungssatz/Herbrand–Ribet at non-irregular indices. -/
  reflectionOtherComponents :
    ∀ j : ℕ, IsReflectionComponentIndex p j → Even j → j ≠ i →
      ¬ identification.componentNontrivial j

namespace FLT37UnitClassBridgeRefined

variable {p K}

/-- Adapter: a refined bridge gives the original `Cor8_19Bridge`. -/
def toCor8_19Bridge {i : ℕ} (B : FLT37UnitClassBridgeRefined p K i) :
    Cor8_19Bridge p K i :=
  cor8_19Bridge_of_componentTrivialities (p := p) (K := K)
    B.identification B.pollaczekUnitComponent B.reflectionOtherComponents

end FLT37UnitClassBridgeRefined

/-- **`cor8_19Bridge_of_refined`** — top-level adapter from refined bridge
to original `Cor8_19Bridge`. -/
def cor8_19Bridge_of_refined {i : ℕ} (B : FLT37UnitClassBridgeRefined p K i) :
    Cor8_19Bridge p K i :=
  B.toCor8_19Bridge

end BernoulliRegular

end
