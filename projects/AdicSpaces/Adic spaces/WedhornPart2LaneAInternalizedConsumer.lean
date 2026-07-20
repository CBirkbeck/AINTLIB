/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornTateAcyclicityPart2C1Consumer
import «Adic spaces».TateAcyclicityFinalAssembly
import «Adic spaces».Wedhorn834SupplierAssembly

/-!
# Wedhorn 8.34(ii) — Part 2 consumer with Lane A internalized (T066)

T063 (commit `204983f`) lands the Part-2 consumer
`tateAcyclicity_Part2_via_C1SupplierStrong_local`, which composes
`C1SupplierStrong_local C` with the existing strong base-Spa bridge
chain to produce Part 2 of Wedhorn Theorem 8.28(b) tate acyclicity —
but it still asks the caller for both `lane_A_supplier` and
`lane_B_supplier` as abstract universal hypotheses.

This file lands the **Lane-A-internalized** variant: the Lane A
supplier is discharged internally via the existing primary-Lane-A
infrastructure (`RationalCoveringData.lane_A_supplier_via_primary` and the
`PrimaryLaneAInputs C f₀` packaging in
`TateAcyclicityFinalAssembly.lean`), leaving only Lane B and the
unavoidable geometric / caller inputs at the consumer boundary.

## What this file provides

* `tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA` — the main
  consumer. Identical caller signature to T063's
  `tateAcyclicity_Part2_via_C1SupplierStrong_local` modulo replacement
  of the abstract `lane_A_supplier` with `hLaneA : PrimaryLaneAInputs
  C f₀`. Output: the gluing existential
  `∃ x : presheafValue C.base, ∀ E ∈ C.covers,
    restrictionMap C.base E _ x = fC E` from compatible cover-level
  sections — exactly Part 2 of `tateAcyclicity`.

* `tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_allow_empty`
  — empty-piece-tolerant variant matching
  `RationalCoveringData.part2_via_primary_laneA_allow_empty`. Lane B is
  only requested for cover pieces with nonempty rational open;
  empty-base and empty-piece branches are handled structurally.

## Composition pipeline

```
C1SupplierStrong_local C
  │
  │ (C1SupplierStrong_local_insertDenom_lift, T058 lift, mod h_covers_nonempty)
  ▼
C1SupplierStrong_local C.insertDenom
  │
  │ (hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa,
  │  Stage-2 + outside-rescue absorbed under h_base_eq_Spa)
  ▼
hZavyalov_per_E
  │
  │ (RationalCoveringData.tateAcyclicity_Part2_end_to_end_via_primary_laneA,
  │  Lane A internalized via PrimaryLaneAInputs)
  ▼
∃ x ∈ presheafValue C.base, ∀ E ∈ C.covers,
   restrictionMap C.base E _ x = fC E         [Part 2 of tateAcyclicity]
```

## Residuals at this layer

| Input | Source / status |
|-------|------|
| `C1SupplierStrong_local C` | T061's per-call Lemma 8.33 bridge |
| `h_base_eq_Spa` | Wedhorn cover-of-Spa hypothesis (geometric) |
| `h_covers_nonempty` | mild insertDenom-lift hypothesis |
| `hLaneA : PrimaryLaneAInputs C f₀` | landed Lane A package |
| `lane_B_supplier` | abstract Lane B (only remaining named blocker) |
| `(fC, hC_compat)` | caller's compatible section data |

Stage-2 strengthening, `h_outside_rescue`,
`h_nonzero_cover_supplier`, and Lane A are all internally absorbed.
The only remaining blocker is **Lane B** (per-E separation, Wedhorn
Cor 8.32 / `productRestriction_injective_tate_via_prime_extension_closed`
route).

## Notes

* No root import; leaf-level.
* Imports T063's `WedhornTateAcyclicityPart2C1Consumer` (transitively
  brings in the strong base-Spa bridge, the C1SupplierStrong_local
  insertDenom lift, and the C1 supplier predicate) and
  `TateAcyclicityFinalAssembly` (provides
  `tateAcyclicity_Part2_end_to_end_via_primary_laneA` and the
  `PrimaryLaneAInputs C f₀` structure).
* No edits to T031–T065 accepted leaves, root imports, or final
  theorem signatures.
* No revival of T001 / Lane-B / Jacobson / bivariate-overlap /
  Zavyalov / global-universal-Spa / σ-power-decay / M-power-decay
  routes.
* Mechanical composition of three accepted strong bridges with
  `tateAcyclicity_Part2_end_to_end_via_primary_laneA` /
  `part2_via_primary_laneA_allow_empty`.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A] [DecidableEq A]

/-- **Lane-A-internalized Part 2 consumer of `C1SupplierStrong_local C`**
(T066 main deliverable).

Identical caller signature to T063's
`tateAcyclicity_Part2_via_C1SupplierStrong_local` modulo replacement
of the abstract `lane_A_supplier` with `hLaneA : PrimaryLaneAInputs C
f₀`. Composes:

1. `C1SupplierStrong_local_insertDenom_lift` — lifts
   `C1SupplierStrong_local C` to the normalized cover under
   `h_covers_nonempty`.
2. `hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa`
   — discharges Stage-2 strengthening and outside rescue internally
   under `h_base_eq_Spa`, producing `hZavyalov_per_E`.
3. `RationalCoveringData.tateAcyclicity_Part2_end_to_end_via_primary_laneA`
   — final Part-2 assembly with Lane A discharged via `hLaneA` and
   only the Lane B supplier abstract.

**Output:** the gluing existential `∃ x : presheafValue C.base,
∀ E ∈ C.covers, restrictionMap C.base E _ x = fC E` (Part 2 of
`tateAcyclicity`).

**Remaining residuals:** `C1SupplierStrong_local C`, `h_base_eq_Spa`,
`h_covers_nonempty`, `hLaneA`, `lane_B_supplier`, and the caller's
`(fC, hC_compat)`. Lane A is no longer abstract at this layer. -/
theorem tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
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
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  -- Step 1: lift the strong supplier to the normalized cover.
  have h_C1_strong_insertDenom : C1SupplierStrong_local C.insertDenom :=
    C1SupplierStrong_local_insertDenom_lift C h_covers_nonempty h_C1_strong
  -- Step 2: produce hZavyalov_per_E via the strong base-Spa bridge.
  have hZavyalov_per_E :
      rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S :=
    hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa
      P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C h_base_eq_Spa
      h_C1_strong_insertDenom
  -- Step 3: invoke the Lane-A-internalized Part 2 assembly.
  exact RationalCoveringData.tateAcyclicity_Part2_end_to_end_via_primary_laneA
    (A := A) (C := C) (f₀ := f₀) hne hZavyalov_per_E fC hC_compat
    lane_B_supplier hLaneA

/-- **Empty-piece-tolerant variant** of
`tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA` (T066
allow-empty variant).

The Lane B supplier is only requested for cover pieces whose rational
open is nonempty; empty-base and empty-piece branches are handled
structurally by `part2_via_primary_laneA_allow_empty`. Identical
caller signature to T066's main consumer modulo the relaxed Lane B
shape. -/
theorem tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_allow_empty
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
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
    (lane_B_supplier : ∀ (S' : StandardCover A)
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
        a = b)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  have h_C1_strong_insertDenom : C1SupplierStrong_local C.insertDenom :=
    C1SupplierStrong_local_insertDenom_lift C h_covers_nonempty h_C1_strong
  have hZavyalov_per_E :
      rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S :=
    hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa
      P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C h_base_eq_Spa
      h_C1_strong_insertDenom
  exact RationalCoveringData.part2_via_primary_laneA_allow_empty
    (A := A) (C := C) (f₀ := f₀) hne hZavyalov_per_E fC hC_compat
    lane_B_supplier hLaneA

/-- **Lane-A-internalized Part 2 consumer from honest single-`t`
structural-data provider** (T193 main deliverable).

Sibling of `tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA`
(T066) with the abstract residual `h_C1_strong : C1SupplierStrong_local
C` replaced by the **explicit single-`t` σ/N structural per-call
provider** `h_struct` consumed by T191 / T192. The provider supplies,
for each `D ∈ C.covers`, `v ∈ rationalOpen D.T D.s`, and `t ∈ D.T`
with `v.vle t D.s ∧ ¬ v.vle D.s 0`, an explicit `(σ : A) (N : ℕ)` with:

* the base-side factorization `C.base.s = D.s * (σ * t * D.s ^ N)`,
* test-family integrality `∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)`,
* and the `f`-membership `v.vle (σ * t * D.s ^ N) C.base.s`.

These are the honest Wedhorn 8.34(ii) σ/N data delivered by T188's
`rationalOpen_subset_via_single_t_sigma_N_data` and T185's power-cleared
`f`-construction lane.

Composition pipeline:

1. T192 (`hZavyalov_per_E_via_single_t_structural_data_of_base_eq_Spa`)
   → `hZavyalov_per_E` shape directly from `h_struct` under
   `h_covers_nonempty` and `h_base_eq_Spa`.
2. `RationalCoveringData.tateAcyclicity_Part2_end_to_end_via_primary_laneA`
   → the gluing existential `∃ x : presheafValue C.base, ∀ E ∈ C.covers,
   restrictionMap C.base E _ x = fC E` (Part 2 of `tateAcyclicity`)
   with Lane A discharged via `hLaneA : PrimaryLaneAInputs C f₀` and
   only the Lane B supplier abstract.

**Output:** identical to T066's main consumer.

**Remaining residuals:** `h_struct` (T192-style σ/N provider),
`h_base_eq_Spa`, `h_covers_nonempty`, `hLaneA`, `lane_B_supplier`, and
the caller's `(fC, hC_compat)`. Lane A is internally absorbed; the
unnormalized `C1SupplierStrong_local C` residual has been replaced by
the strictly-stronger explicit single-`t` structural provider. -/
theorem tateAcyclicity_Part2_via_single_t_structural_data_laneA
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
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
    (lane_B_supplier : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (D : RationalLocData A)
         (hD : D ∈ (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers),
        restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) a =
          restrictionMap E.1 D
            ((C.per_E_local_covering S'.elts f₀ E hS'_per_E).hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  -- Build hZavyalov_per_E directly from h_struct via T192.
  have hZavyalov_per_E :
      rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S :=
    hZavyalov_per_E_via_single_t_structural_data_of_base_eq_Spa
      P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C h_base_eq_Spa
      h_covers_nonempty h_struct
  -- Invoke the Lane-A-internalized Part 2 assembly.
  exact RationalCoveringData.tateAcyclicity_Part2_end_to_end_via_primary_laneA
    (A := A) (C := C) (f₀ := f₀) hne hZavyalov_per_E fC hC_compat
    lane_B_supplier hLaneA

/-- **Empty-piece-tolerant variant** of
`tateAcyclicity_Part2_via_single_t_structural_data_laneA` (T193
allow-empty variant).

The Lane B supplier is only requested for cover pieces whose rational
open is nonempty; empty-base and empty-piece branches are handled
structurally by `part2_via_primary_laneA_allow_empty`. Identical
caller signature to T193's main consumer modulo the relaxed Lane B
shape. -/
theorem tateAcyclicity_Part2_via_single_t_structural_data_laneA_allow_empty
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
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
    (lane_B_supplier : ∀ (S' : StandardCover A)
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
        a = b)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  have hZavyalov_per_E :
      rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S :=
    hZavyalov_per_E_via_single_t_structural_data_of_base_eq_Spa
      P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C h_base_eq_Spa
      h_covers_nonempty h_struct
  exact RationalCoveringData.part2_via_primary_laneA_allow_empty
    (A := A) (C := C) (f₀ := f₀) hne hZavyalov_per_E fC hC_compat
    lane_B_supplier hLaneA

end ValuationSpectrum
