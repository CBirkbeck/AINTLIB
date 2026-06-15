/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornPart2LaneAInternalizedConsumer
import «Adic spaces».WedhornLaneBSeparationInterface

/-!
# Wedhorn 8.34(ii) — Part 2 consumer with Lane A and Lane B integrated (T071)

T066 (commit `8d9bf5e`) lands the Part-2 consumer with Lane A
internalized via `PrimaryLaneAInputs C f₀`, leaving only the abstract
`lane_B_supplier` and the standard geometric / caller residuals.
T068 (commit `123998a`) lands the Lane B per-E separation interface
producing the `lane_B_supplier` shape from either a universal nonempty-
cover separation supplier or the concrete Cor 8.32 prime-extension-
closed hypothesis bundle.

This file lands the **integration** of these two layers: theorem-level
wrappers that remove the abstract `lane_B_supplier` argument from the
Part-2 consumer boundary by routing through T068's interface. The
result is a Part-2 consumer whose remaining residuals are explicit
named intermediate inputs (C1 supplier, separation supplier, geometric
hypotheses, caller's compatible section family), not abstract Lane B.

## What this file provides

* `tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_separation`
  — generic full-form integration. Composes T066's main consumer with
  T068's `laneB_supplier_via_perE_separation_interface`. Inputs:
  T066's standard inputs minus `lane_B_supplier`, replaced by
  (i) a universal nonempty-cover separation supplier, and (ii) a
  per-`(S', E)` local-cover nonemptiness witness.

* `tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_separation_allow_empty`
  — generic allow-empty integration. Composes T066's allow-empty
  variant with T068's
  `laneB_supplier_via_perE_separation_interface_allow_empty`. The
  per-E nonemptiness witness is structurally derived from
  `(rationalOpen E.1.T E.1.s).Nonempty`, removed from the consumer
  inputs entirely.

* `tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_prime_extension_closed`
  — concrete full-form integration. Routes Lane B through the Wedhorn
  Cor 8.32 prime-extension-closed bundle (`hloc_noeth`,
  `hAplus_le_A₀`, `hcanonicalMap_cont`, `h_closed_nonOpen` — all
  universal over rational coverings). Inherits `sorryAx` transitively
  from the upstream Cor 8.32 chain documented in
  `TateAcyclicityFinalAssembly.lean`.

* `..._laneA_laneB_via_prime_extension_closed_allow_empty` — concrete
  allow-empty integration. Combines the concrete Cor 8.32 route with
  the allow-empty per-E nonemptiness derivation.

## Residuals at this layer

After T071, the Part-2 consumer's named residuals are:

| Input | Source / status |
|-------|------|
| `C1SupplierStrong_local C` | T061's per-call Lemma 8.33 reach |
| `h_base_eq_Spa` | geometric Wedhorn cover-of-Spa hypothesis |
| `h_covers_nonempty` | mild insertDenom-lift hypothesis |
| `hLaneA : PrimaryLaneAInputs C f₀` | landed Lane A package |
| separation_supplier / Cor 8.32 bundle | universal nonempty-cover separation |
| `(fC, hC_compat)` | caller's compatible section data |

In the full-form variants, a per-E local-cover nonemptiness witness
is also required; in the allow-empty variants, this is structurally
discharged from cover-piece `(rationalOpen E.1.T E.1.s).Nonempty`.

**No abstract `lane_B_supplier` remains.** Stage-2 strengthening,
`h_outside_rescue`, `h_nonzero_cover_supplier`, and Lane A are all
internally absorbed.

## Important: this does not change the final tate acyclicity theorem

The cor 8.32, nonempty-cover separation, C1 supplier, base-Spa,
geometric, and caller compatibility inputs are documented here as
**intermediate supplier-boundary inputs** for the consumer wrappers
in this file; they are NOT changes to
`ValuationSpectrum.tateAcyclicity` (which retains its existing
signature). T071 only integrates two existing supplier interfaces; it
does not add hypotheses to the final root theorem.

## Notes

* No root import; leaf-level.
* Imports T066's `WedhornPart2LaneAInternalizedConsumer` and T068's
  `WedhornLaneBSeparationInterface`.
* No edits to T031–T070 accepted leaves, root imports, or final
  theorem signatures.
* No revival of T001 / Jacobson / bivariate-overlap / Zavyalov /
  global-universal-Spa / σ-power-decay / M-power-decay routes; only
  mechanical composition of two accepted bridges.
* The deliverable matches T071 acceptance: at least one wrapper
  composes T066 with T068 so the Part-2 boundary no longer takes a
  raw `lane_B_supplier`; remaining residuals are named intermediate
  inputs.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A] [DecidableEq A]

/-- **Generic Lane-A + Lane-B integrated Part-2 consumer**, full form
(T071 main deliverable).

Identical caller signature to T066's
`tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA` modulo
replacement of the abstract `lane_B_supplier` with a universal
nonempty-cover separation supplier plus a per-`(S', E)` local-cover
nonemptiness witness — the inputs consumed by T068's
`laneB_supplier_via_perE_separation_interface`. Composes T066's main
consumer with T068's generic interface mechanically. -/
theorem tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_separation
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_C1_strong : C1SupplierStrong_local C)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
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
      (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers.Nonempty)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA P hA₀_le hAplus_le_A₀
    π hI hπ_tn hπ_unit hArch C hne h_base_eq_Spa h_covers_nonempty
    h_C1_strong f₀ fC hC_compat
    (laneB_supplier_via_perE_separation_interface C f₀
      separation_supplier per_E_nonempty)
    hLaneA

/-- **Generic Lane-A + Lane-B integrated Part-2 consumer**, allow-empty
variant.

Identical caller signature to T066's
`tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_allow_empty`
modulo replacement of the abstract `lane_B_supplier` with the universal
nonempty-cover separation supplier alone — the per-E local-cover
nonemptiness witness is structurally derived via
`per_E_local_covering_nonempty_of_rationalOpen_nonempty` from
`(rationalOpen E.1.T E.1.s).Nonempty`, embedded in the relaxed Lane B
shape. -/
theorem tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_separation_allow_empty
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_C1_strong : C1SupplierStrong_local C)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (separation_supplier : ∀ C' : RationalCovering A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_allow_empty P hA₀_le
    hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C hne h_base_eq_Spa
    h_covers_nonempty h_C1_strong f₀ fC hC_compat
    (laneB_supplier_via_perE_separation_interface_allow_empty C f₀
      separation_supplier)
    hLaneA

/-- **Concrete Lane-A + Lane-B integrated Part-2 consumer via Cor 8.32
prime-extension-closed**, full form (T071 concrete deliverable).

Routes Lane B through the four named Cor 8.32 prime-extension-closed
hypotheses. Identical caller signature to T066's main consumer modulo
replacement of `lane_B_supplier` with the four universal-over-rational-
coverings hypotheses (`hloc_noeth`, `hAplus_le_A₀_perCovers`,
`hcanonicalMap_cont`, `h_closed_nonOpen`) plus a per-`(S', E)`
local-cover nonemptiness witness. **Inherits `sorryAx` transitively**
from the upstream Cor 8.32 chain (`productRestriction_injective_tate_via_prime_extension_closed`),
consistent with `TateAcyclicityFinalAssembly`'s documented status. -/
theorem tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_prime_extension_closed
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺) [IsNoetherianRing P.A₀]
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_C1_strong : C1SupplierStrong_local C)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hloc_noeth : ∀ C' : RationalCovering A,
      IsNoetherianRing (locSubring C'.base.P C'.base.T C'.base.s))
    (hAplus_le_A₀_perCovers : ∀ C' : RationalCovering A,
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
      (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers.Nonempty)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA P hA₀_le hAplus_le_A₀
    π hI hπ_tn hπ_unit hArch C hne h_base_eq_Spa h_covers_nonempty
    h_C1_strong f₀ fC hC_compat
    (laneB_supplier_via_prime_extension_closed P C f₀ hloc_noeth
      hAplus_le_A₀_perCovers hcanonicalMap_cont h_closed_nonOpen per_E_nonempty)
    hLaneA

set_option linter.style.longLine false in
/-- **Concrete Lane-A + Lane-B integrated Part-2 consumer via Cor 8.32
prime-extension-closed**, allow-empty variant.

Identical caller signature to the full-form concrete consumer modulo
the relaxed Lane B shape: per-E nonemptiness is structurally derived
from `(rationalOpen E.1.T E.1.s).Nonempty` rather than supplied
explicitly. **Inherits `sorryAx` transitively** from the upstream
Cor 8.32 chain. -/
theorem tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_prime_extension_closed_allow_empty
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺) [IsNoetherianRing P.A₀]
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_C1_strong : C1SupplierStrong_local C)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hloc_noeth : ∀ C' : RationalCovering A,
      IsNoetherianRing (locSubring C'.base.P C'.base.T C'.base.s))
    (hAplus_le_A₀_perCovers : ∀ C' : RationalCovering A,
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
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_allow_empty P hA₀_le
    hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C hne h_base_eq_Spa
    h_covers_nonempty h_C1_strong f₀ fC hC_compat
    (laneB_supplier_via_prime_extension_closed_allow_empty P C f₀
      hloc_noeth hAplus_le_A₀_perCovers hcanonicalMap_cont h_closed_nonOpen)
    hLaneA

/-! ### T194: Single-`t` structural-data sibling wrappers

These mirror the four T071 wrappers above, replacing the abstract
residual `h_C1_strong : C1SupplierStrong_local C` with the explicit
single-`t` σ/N structural per-call provider consumed by T191/T192/T193.
The composition uses T193's
`tateAcyclicity_Part2_via_single_t_structural_data_laneA`/`_allow_empty`
in place of T066. All other inputs (Lane B separation supplier, Cor 8.32
prime-extension-closed bundle, per-E nonemptiness, geometric/caller
hypotheses, `hLaneA`) are preserved exactly. -/

/-- **T194 generic Lane-A + Lane-B integrated Part-2 consumer**, full
form, from honest single-`t` structural-data provider.

Sibling of `tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_separation`
(T071) with the abstract residual `h_C1_strong : C1SupplierStrong_local
C` replaced by the explicit single-`t` σ/N structural per-call provider
`h_struct` consumed by T191/T192/T193. Composes T193's
`tateAcyclicity_Part2_via_single_t_structural_data_laneA` with T068's
`laneB_supplier_via_perE_separation_interface` mechanically. -/
theorem tateAcyclicity_Part2_via_single_t_structural_data_laneA_laneB_via_separation
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_struct :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ (σ : A) (N : ℕ),
          C.base.s = D.s * (σ * t * D.s ^ N) ∧
          (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
          v.vle (σ * t * D.s ^ N) C.base.s)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
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
      (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers.Nonempty)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_single_t_structural_data_laneA P hA₀_le hAplus_le_A₀
    π hI hπ_tn hπ_unit hArch C hne h_base_eq_Spa h_covers_nonempty
    h_struct f₀ fC hC_compat
    (laneB_supplier_via_perE_separation_interface C f₀
      separation_supplier per_E_nonempty)
    hLaneA

/-- **T194 generic Lane-A + Lane-B integrated Part-2 consumer**,
allow-empty variant, from honest single-`t` structural-data provider.

Sibling of
`tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_separation_allow_empty`
(T071 allow-empty) with `h_C1_strong` replaced by the single-`t` σ/N
structural per-call provider `h_struct`. Per-E nonemptiness witness is
structurally derived via the allow-empty interface. -/
theorem tateAcyclicity_Part2_via_single_t_structural_data_laneA_laneB_via_separation_allow_empty
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_struct :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ (σ : A) (N : ℕ),
          C.base.s = D.s * (σ * t * D.s ^ N) ∧
          (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
          v.vle (σ * t * D.s ^ N) C.base.s)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (separation_supplier : ∀ C' : RationalCovering A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_single_t_structural_data_laneA_allow_empty P hA₀_le
    hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C hne h_base_eq_Spa
    h_covers_nonempty h_struct f₀ fC hC_compat
    (laneB_supplier_via_perE_separation_interface_allow_empty C f₀
      separation_supplier)
    hLaneA

set_option linter.style.longLine false in
/-- **T194 concrete Lane-A + Lane-B integrated Part-2 consumer via Cor 8.32
prime-extension-closed**, full form, from honest single-`t` structural-
data provider.

Sibling of
`tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_prime_extension_closed`
(T071 concrete) with `h_C1_strong` replaced by the single-`t` σ/N
structural per-call provider `h_struct`. Routes Lane B through the four
named Cor 8.32 prime-extension-closed hypotheses; preserves the same
caller boundary modulo the C1-side residual replacement.

**Inherits `sorryAx` transitively** from the upstream Cor 8.32 chain
(`productRestriction_injective_tate_via_prime_extension_closed`),
consistent with the existing T071 concrete deliverable's documented
status. -/
theorem tateAcyclicity_Part2_via_single_t_structural_data_laneA_laneB_via_prime_extension_closed
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺) [IsNoetherianRing P.A₀]
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_struct :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ (σ : A) (N : ℕ),
          C.base.s = D.s * (σ * t * D.s ^ N) ∧
          (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
          v.vle (σ * t * D.s ^ N) C.base.s)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hloc_noeth : ∀ C' : RationalCovering A,
      IsNoetherianRing (locSubring C'.base.P C'.base.T C'.base.s))
    (hAplus_le_A₀_perCovers : ∀ C' : RationalCovering A,
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
      (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers.Nonempty)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_single_t_structural_data_laneA P hA₀_le hAplus_le_A₀
    π hI hπ_tn hπ_unit hArch C hne h_base_eq_Spa h_covers_nonempty
    h_struct f₀ fC hC_compat
    (laneB_supplier_via_prime_extension_closed P C f₀ hloc_noeth
      hAplus_le_A₀_perCovers hcanonicalMap_cont h_closed_nonOpen per_E_nonempty)
    hLaneA

set_option linter.style.longLine false in
/-- **T194 concrete Lane-A + Lane-B integrated Part-2 consumer via Cor 8.32
prime-extension-closed**, allow-empty variant, from honest single-`t`
structural-data provider.

Sibling of
`tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_prime_extension_closed_allow_empty`
(T071 concrete allow-empty) with `h_C1_strong` replaced by the
single-`t` σ/N structural per-call provider `h_struct`. Per-E
nonemptiness is structurally derived from
`(rationalOpen E.1.T E.1.s).Nonempty`. **Inherits `sorryAx` transitively**
from the upstream Cor 8.32 chain. -/
theorem tateAcyclicity_Part2_via_single_t_structural_data_laneA_laneB_via_prime_extension_closed_allow_empty
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺) [IsNoetherianRing P.A₀]
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_struct :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ (σ : A) (N : ℕ),
          C.base.s = D.s * (σ * t * D.s ^ N) ∧
          (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
          v.vle (σ * t * D.s ^ N) C.base.s)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hloc_noeth : ∀ C' : RationalCovering A,
      IsNoetherianRing (locSubring C'.base.P C'.base.T C'.base.s))
    (hAplus_le_A₀_perCovers : ∀ C' : RationalCovering A,
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
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_single_t_structural_data_laneA_allow_empty P hA₀_le
    hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C hne h_base_eq_Spa
    h_covers_nonempty h_struct f₀ fC hC_compat
    (laneB_supplier_via_prime_extension_closed_allow_empty P C f₀
      hloc_noeth hAplus_le_A₀_perCovers hcanonicalMap_cont h_closed_nonOpen)
    hLaneA

end ValuationSpectrum
