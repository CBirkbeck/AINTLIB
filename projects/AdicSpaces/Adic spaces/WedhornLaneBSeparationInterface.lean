/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornPart2LaneAInternalizedConsumer
import «Adic spaces».GeometricReduction

/-!
# Wedhorn 8.34(ii) — Lane B per-E separation interface (T068)

T066 (commit `8d9bf5e`) lands the Part-2 consumer with Lane A
internalized, leaving only `lane_B_supplier` and the standard
geometric / caller inputs at the consumer boundary. This file lands
the **Lane B per-E separation interface**: a reusable bridge
producing the `lane_B_supplier` shape consumed by T066 from the
canonical cover-level separation supplier (the universal-over-rational-
coverings nonempty-cover separation theorem already documented in
`TateAcyclicityFinalAssembly.lean`).

## What this file provides

* `laneB_supplier_via_perE_separation_interface` — generic interface.
  From a `nonempty-cover separation supplier` (universal over rational
  coverings, requiring `C'.covers.Nonempty`) plus a per-E local-cover
  nonemptiness witness, produce the `lane_B_supplier` shape consumed
  by `tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA`.

* `laneB_supplier_via_perE_separation_interface_allow_empty` — the
  allow-empty variant matching the relaxed Lane B shape consumed by
  `tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_allow_empty`.
  Uses `RationalCovering.per_E_local_covering_nonempty_of_rationalOpen_nonempty`
  (`GeometricReduction.lean`) to derive per-E local-cover nonemptiness
  from `(rationalOpen E.1.T E.1.s).Nonempty`.

* `laneB_supplier_via_prime_extension_closed` — concrete variant
  using the Wedhorn Corollary 8.32 prime-extension-closed route via
  `RationalCovering.nonempty_separation_supplier_via_prime_extension_closed`
  in `TateAcyclicityFinalAssembly.lean`. Narrows the Lane B residual
  to the four named Cor 8.32 hypotheses (`hloc_noeth`,
  `hAplus_le_A₀`, `hcanonicalMap_cont`, `h_closed_nonOpen`) on the
  ambient rational-covering family.

* `laneB_supplier_via_prime_extension_closed_allow_empty` — concrete
  + allow-empty variant. Single named blocker = the four Cor 8.32
  hypotheses; per-E nonemptiness derived structurally from cover-piece
  nonemptiness.

## Lane B shape consumed by T066

```
∀ (S' : StandardCover A)
  (hS'_per_E : refines_cover_per_E C S'.elts)
  (_hS'_contain : refines_contain C S'.elts),
  ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
  (∀ (D : RationalLocData A)
     (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
    restrictionMap E.1 D
        ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
      restrictionMap E.1 D
        ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
    a = b
```

This is per-E local-covering separation: at each `E ∈ C.covers` and
each standard refinement `S'`, the product restriction
`presheafValue E.1 → ∏ presheafValue D.1` over
`(C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers` is
injective.

## Reduction to Cor 8.32 prime-extension-closed hypotheses

Wedhorn Corollary 8.32-style cover-level injectivity
(`productRestriction_injective_tate_via_prime_extension_closed` in
`Cor832.lean`) is the canonical source of the per-E separation. Its
universal-over-rational-coverings packaging
`RationalCovering.nonempty_separation_supplier_via_prime_extension_closed`
already takes the four-hypothesis bundle:

* `hloc_noeth` — locSubring noetherianity per cover.
* `hAplus_le_A₀` — `A⁺ ⊆ P.A₀` per cover.
* `hcanonicalMap_cont` — canonicalMap continuity per cover.
* `h_closed_nonOpen` — closedness of non-open primes' images per cover.

This file's `laneB_supplier_via_prime_extension_closed` packages those
four hypotheses straight into the `lane_B_supplier` shape, leaving
the per-E local-cover nonemptiness as the only remaining geometric
input — and that is structural (`per_E_local_covering_nonempty_of_rationalOpen_nonempty`
discharges it from `(rationalOpen E.1.T E.1.s).Nonempty`).

## Notes

* No root import; leaf-level.
* Imports T066's `WedhornPart2LaneAInternalizedConsumer` (transitively
  brings in T063's bridge, the C1SupplierStrong_local insertDenom
  lift, and the strong base-Spa bridge) and `GeometricReduction`
  (for `per_E_local_covering_nonempty_of_rationalOpen_nonempty`).
* Both deliverables are **structural** lifts; no new mathematical
  content over the Cor 8.32 prime-extension-closed route already
  documented in `TateAcyclicityFinalAssembly.lean`.
* No edits to T031–T067 accepted leaves, root imports, or final
  theorem signatures.
* No revival of T001 / Jacobson / bivariate-overlap / Zavyalov /
  global-universal-Spa / σ-power-decay / M-power-decay routes; only
  the established Wedhorn Cor 8.32 / per-E separation route.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A] [DecidableEq A]

/-- **Generic Lane B per-E separation interface** (T068 main
deliverable, full form).

From a nonempty-cover separation supplier (universal over rational
coverings, requiring `C'.covers.Nonempty`) plus a per-`(S', E)`
local-cover nonemptiness witness, produce the `lane_B_supplier` shape
consumed by `tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA`.

Mirrors the `lane_B_supplier` construction in
`RationalCovering.tateAcyclicity_end_to_end_via_primary_laneA_of_nonempty_separation`
(`TateAcyclicityFinalAssembly.lean:1502`): apply the separation
supplier at each per-E local covering with the supplied nonemptiness
witness. Reusable across all consumer wrappers that need the full-form
`lane_B_supplier` shape. -/
theorem laneB_supplier_via_perE_separation_interface
    (C : RationalCovering A) (f₀ : A)
    (separation_supplier : ∀ C' : RationalCovering A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (per_E_nonempty : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts)
      (E : { E // E ∈ C.covers }),
      (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers.Nonempty) :
    ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b := by
  intro S' hS'_per_E hS'_contain E a b hlocal
  exact separation_supplier (C.per_E_local_covering S'.elts f₀ E hS'_per_E)
    (per_E_nonempty S' hS'_per_E hS'_contain E) a b hlocal

/-- **Allow-empty Lane B per-E separation interface** (T068
allow-empty form).

Matches the relaxed `lane_B_supplier` shape consumed by
`tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_allow_empty`:
the supplier is only required for cover pieces `E` with
`(rationalOpen E.1.T E.1.s).Nonempty`. Per-E local-cover nonemptiness
is derived structurally via
`RationalCovering.per_E_local_covering_nonempty_of_rationalOpen_nonempty`
(`GeometricReduction.lean`), so the caller no longer supplies an
explicit per-E nonemptiness witness. -/
theorem laneB_supplier_via_perE_separation_interface_allow_empty
    (C : RationalCovering A) (f₀ : A)
    (separation_supplier : ∀ C' : RationalCovering A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b) :
    ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }),
      (rationalOpen E.1.T E.1.s).Nonempty →
      ∀ a b : presheafValue E.1,
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b := by
  intro S' hS'_per_E _hS'_contain E hE_nonempty a b hlocal
  exact separation_supplier (C.per_E_local_covering S'.elts f₀ E hS'_per_E)
    (C.per_E_local_covering_nonempty_of_rationalOpen_nonempty
      S'.elts f₀ E hS'_per_E hE_nonempty)
    a b hlocal

/-- **Concrete Lane B interface via Cor 8.32 prime-extension-closed
route** (T068 concrete deliverable, full form).

Composes
`RationalCovering.nonempty_separation_supplier_via_prime_extension_closed`
with `laneB_supplier_via_perE_separation_interface` to produce the
full-form `lane_B_supplier` directly from the four named Cor 8.32
hypotheses. The per-E nonemptiness witness `per_E_nonempty` is left
explicit. -/
theorem laneB_supplier_via_prime_extension_closed
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (f₀ : A)
    (hloc_noeth : ∀ C' : RationalCovering A,
      IsNoetherianRing (locSubring C'.base.P C'.base.T C'.base.s))
    (hAplus_le_A₀ : ∀ C' : RationalCovering A,
      (A⁺ : Set A) ⊆ C'.base.P.A₀)
    (hcanonicalMap_cont : ∀ C' : RationalCovering A,
      Continuous C'.base.canonicalMap)
    (h_closed_nonOpen : ∀ C' : RationalCovering A,
      ∀ (p : Ideal A), p.IsPrime → C'.base.s ∉ p →
        ¬IsOpen (p : Set A) →
        @IsClosed _ C'.base.topology
          ((Ideal.map (algebraMap A (Localization.Away C'.base.s)) p :
              Ideal (Localization.Away C'.base.s)) :
            Set (Localization.Away C'.base.s)))
    (per_E_nonempty : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts)
      (E : { E // E ∈ C.covers }),
      (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers.Nonempty) :
    ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b :=
  laneB_supplier_via_perE_separation_interface C f₀
    (RationalCovering.nonempty_separation_supplier_via_prime_extension_closed
      P hloc_noeth hAplus_le_A₀ hcanonicalMap_cont h_closed_nonOpen)
    per_E_nonempty

/-- **Concrete Lane B interface via Cor 8.32 prime-extension-closed
route, allow-empty form** (T068 concrete deliverable, allow-empty
form).

Composes
`RationalCovering.nonempty_separation_supplier_via_prime_extension_closed`
with `laneB_supplier_via_perE_separation_interface_allow_empty` to
produce the relaxed `lane_B_supplier` directly from the four named
Cor 8.32 hypotheses. Per-E local-cover nonemptiness derives
structurally from `(rationalOpen E.1.T E.1.s).Nonempty`. -/
theorem laneB_supplier_via_prime_extension_closed_allow_empty
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (f₀ : A)
    (hloc_noeth : ∀ C' : RationalCovering A,
      IsNoetherianRing (locSubring C'.base.P C'.base.T C'.base.s))
    (hAplus_le_A₀ : ∀ C' : RationalCovering A,
      (A⁺ : Set A) ⊆ C'.base.P.A₀)
    (hcanonicalMap_cont : ∀ C' : RationalCovering A,
      Continuous C'.base.canonicalMap)
    (h_closed_nonOpen : ∀ C' : RationalCovering A,
      ∀ (p : Ideal A), p.IsPrime → C'.base.s ∉ p →
        ¬IsOpen (p : Set A) →
        @IsClosed _ C'.base.topology
          ((Ideal.map (algebraMap A (Localization.Away C'.base.s)) p :
              Ideal (Localization.Away C'.base.s)) :
            Set (Localization.Away C'.base.s))) :
    ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }),
      (rationalOpen E.1.T E.1.s).Nonempty →
      ∀ a b : presheafValue E.1,
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b :=
  laneB_supplier_via_perE_separation_interface_allow_empty C f₀
    (RationalCovering.nonempty_separation_supplier_via_prime_extension_closed
      P hloc_noeth hAplus_le_A₀ hcanonicalMap_cont h_closed_nonOpen)

end ValuationSpectrum
