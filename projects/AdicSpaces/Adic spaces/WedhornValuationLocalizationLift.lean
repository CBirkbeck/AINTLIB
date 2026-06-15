/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornLocalizationPlus
import «Adic spaces».WedhornLocalizationContinuity

/-!
# Wedhorn 8.34(ii) valuation lift to localization

The single biggest missing Lean lemma identified in
`WedhornC1StrongSupplierCore.lean` toward the full Wedhorn 8.34(ii)
core supplier: lift a Spa point `v ∈ Spa(A, A⁺)` with `¬ v.vle s 0`
(i.e., `v(s) ≠ 0`) to a point `w ∈ Spa(A_loc, A_loc⁺_image)` on the
localization, with `comap (algebraMap A A_loc) w = v`.

## Existing infrastructure (audit)

The **algebraic lift** is already implemented in
`Adic spaces/ValuationSpectrum.lean:234`:

* `localizationLift S B v hS : Spv B` — given a submonoid
  `S ≤ v.supp.primeCompl` of any localization target `B`, lift `v` to
  `Spv B` via `Valuation.extendToLocalization`.
* `comap_localizationLift` — the comap-of-lift identity.

What is **missing**:

* The specialisation to `S := Submonoid.powers s` (for
  `Localization.Away s`), with the `S ≤ v.supp.primeCompl` derivation
  from `¬ v.vle s 0`.
* The plus-subring bound on `localizationAwayPlusSubring` (image of
  `A⁺`) — this is purely algebraic.
* The **continuity** of the lift `w` w.r.t. `locTopology P T s hopen`
  — the genuinely missing technical content.

## What this file provides

1. `valuationLocalizationLift_powers_subset_primeCompl` — derives
   `Submonoid.powers s ≤ v.supp.primeCompl` from `¬ v.vle s 0` (the
   precondition for invoking `localizationLift` on
   `Localization.Away s`).

2. `valuationLocalizationLift_algebraic` — the algebraic lift
   conclusion: comap-of-lift identity plus the plus-subring bound.
   Avoids the topological structure on `Localization.Away s`, so it
   compiles unconditionally.

3. `valuationLocalizationLift_via_continuity` — full Spa membership
   conditional on the continuity hypothesis. Combines the algebraic
   lift with a continuity-of-lift hypothesis (the precise remaining
   residual).

## Documented remaining residual

The single remaining Lean lemma needed to upgrade
`valuationLocalizationLift_via_continuity` to a fully unconditional
theorem:

```
theorem isContinuous_localizationLift_locTopology
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    {v : Spv A} (hv : v ∈ Cont A) (hvs : ¬ v.vle s 0)
    (hS : Submonoid.powers s ≤ v.supp.primeCompl) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    (localizationLift (Submonoid.powers s) (Localization.Away s) v hS).IsContinuous
```

This is a technical valuation-continuity lemma: the extended valuation
`w = v.extendToLocalization` is continuous w.r.t. `locTopology` because
`locTopology` is the coarsest ring topology on `Localization.Away s`
making `algebraMap` continuous, and `w ∘ algebraMap = v` (continuous by
`hv`). The proof requires reaching into the value-group order topology
and showing the basic neighborhoods of 0 in `locTopology` (`locNhd P T
s n`) are mapped into appropriate value-group neighborhoods.

## Notes

* No root import; leaf-level file.
* No edits to `ValuationSpectrum.lean` (the underlying `localizationLift`
  lives there) or any committed bridge file.
* No Lane B / Cor 8.32 / Jacobson / T001 / faithful-flatness /
  final-acyclicity content. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **`Submonoid.powers s` avoids `v.supp` iff `v(s) ≠ 0`**.

Precondition for invoking `localizationLift` on
`Localization.Away s` from the Spa-side hypothesis `¬ v.vle s 0`.

**Proof**: by induction on the power exponent. `s^0 = 1 ∉ supp` (always
true). `s^(n+1) ∉ supp` from `s ∉ supp` (by `hvs`) using primality of
`v.supp`. -/
lemma valuationLocalizationLift_powers_subset_primeCompl
    {v : Spv A} {s : A} (hvs : ¬ v.vle s 0) :
    Submonoid.powers s ≤ v.supp.primeCompl := by
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  -- s ∉ v.supp from hvs.
  have hs_notin : s ∉ v.supp := by
    rw [mem_supp_iff]; exact hvs
  -- s^n ∉ v.supp by primality (closed under non-supp).
  intro hxs
  exact hs_notin
    ((inferInstance : v.supp.IsPrime).mem_of_pow_mem n hxs)

omit [IsTopologicalRing A] in
/-- **Algebraic lift conclusion**: comap-of-lift identity plus the
plus-subring bound.

Given `v ∈ Spa A A⁺` and `¬ v.vle s 0`, the lift `w :=
localizationLift (Submonoid.powers s) (Localization.Away s) v _`
satisfies:

* `comap (algebraMap A _) w = v` — the lift is a section of the comap.
* For every `a ∈ A⁺`, `w.vle (algebraMap a) 1` — the plus-subring bound
  on `Subring.map (algebraMap) A⁺` (the canonical
  `localizationAwayPlusSubring`).

**Avoids the topological structure on `Localization.Away s`**, so this
compiles independent of `locTopology` / `hopen` data. The Spa
membership requires the continuity residual; see
`valuationLocalizationLift_via_continuity` below for the full
conditional theorem. -/
theorem valuationLocalizationLift_algebraic
    (s : A) {v : Spv A} (hv : v ∈ Spa A A⁺) (hvs : ¬ v.vle s 0) :
    let hS := valuationLocalizationLift_powers_subset_primeCompl hvs
    let w := localizationLift (Submonoid.powers s) (Localization.Away s) v hS
    comap (algebraMap A (Localization.Away s)) w = v ∧
    ∀ a : A, a ∈ A⁺ → w.vle (algebraMap A (Localization.Away s) a) 1 := by
  refine ⟨?_, ?_⟩
  · -- comap-of-lift identity, directly from `comap_localizationLift`.
    exact comap_localizationLift _ _ v _
  · -- Plus-subring bound: w.vle (algebraMap a) 1 ↔ v.vle a 1 (via comap).
    intro a ha
    have hv_a : v.vle a 1 := hv.2 a ha
    have h_comap := comap_localizationLift (Submonoid.powers s)
      (Localization.Away s) v
      (valuationLocalizationLift_powers_subset_primeCompl hvs)
    -- Rewrite the goal `w.vle (algebraMap a) 1` to `v.vle a 1` via map_one, comap_vle,
    -- and the comap-of-lift identity.
    rw [show (1 : Localization.Away s) = algebraMap A (Localization.Away s) 1 from
          (map_one _).symm,
        ← comap_vle (algebraMap A (Localization.Away s))
          (localizationLift (Submonoid.powers s) (Localization.Away s) v
            (valuationLocalizationLift_powers_subset_primeCompl hvs)) a 1,
        h_comap]
    exact hv_a

/-- **Conditional full Spa-membership lift**: under the continuity
hypothesis on the lifted valuation, the lift `w` lies in
`Spa(Localization.Away s, (Localization.Away s)⁺_image)` with the
canonical `localizationAwayPlusSubring` choice.

This is the manager's target signature `valuationLocalizationLift`,
modulo the continuity hypothesis `h_cont` (the precise remaining
residual identified in the file's docblock).

**Plug-in path**: once
`isContinuous_localizationLift_locTopology` (documented in trailing
docblock) lands, `h_cont` discharges automatically and the conditional
becomes unconditional. -/
theorem valuationLocalizationLift_via_continuity
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    {v : Spv A} (hv : v ∈ Spa A A⁺) (hvs : ¬ v.vle s 0)
    (h_cont :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      (localizationLift (Submonoid.powers s) (Localization.Away s) v
        (valuationLocalizationLift_powers_subset_primeCompl hvs)).IsContinuous) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    ∃ w : Spv (Localization.Away s),
      w ∈ @Spa (Localization.Away s) _ (locTopology P T s hopen)
        (localizationAwayPlusSubring s).toSubring ∧
      comap (algebraMap A (Localization.Away s)) w = v := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  obtain ⟨h_comap, h_plus⟩ := valuationLocalizationLift_algebraic s hv hvs
  refine ⟨localizationLift (Submonoid.powers s) (Localization.Away s) v
    (valuationLocalizationLift_powers_subset_primeCompl hvs), ?_, h_comap⟩
  refine ⟨h_cont, fun f hf => ?_⟩
  -- f ∈ (localizationAwayPlusSubring s).toSubring = Subring.map (algebraMap) A⁺.
  obtain ⟨a, ha, rfl⟩ := Subring.mem_map.mp hf
  exact h_plus a ha

end ValuationSpectrum
