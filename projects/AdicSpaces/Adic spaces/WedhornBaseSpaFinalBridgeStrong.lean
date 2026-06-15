/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornNormalizedC1AssemblyStrong
import «Adic spaces».WedhornBaseSpaFinalBridge

/-!
# Wedhorn Base-Spa Final Bridge (Strong Variant)

Strong analogue of
`WedhornBaseSpaFinalBridge.hZavyalov_per_E_via_normalized_C1_supplier_of_base_eq_Spa`:
consumes Primary's
`WedhornNormalizedC1AssemblyStrong.exists_per_D_finset_via_normalized_C1Strong_supplier`
(commit `46624f7`) to remove the abstract `h_nonzero_cover_supplier`
hypothesis from the base-Spa specialised bridge.

The result has only **one** abstract Stage-2 obligation remaining,
modulo the standard Tate pseudouniformizer pack and the geometric
hypothesis `h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺`:

* `h_C1_strong : C1SupplierStrong_local C.insertDenom` — strong C1
  supplier on the normalized cover (Tertiary's territory; will be
  discharged by the strong analogue of
  `exists_single_f_refinement_at_t_via_dominating_unit` once committed).

## What this file provides

* `hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa` —
  the composed bridge: takes only `h_base_eq_Spa` and `h_C1_strong`,
  produces the per-E refinement existence directly. Theorem-level
  composition of the strong normalized assembly with the Stage-2 span
  extractor, base-Spa outside rescue, and `hZavyalov_per_E_of_per_D_construction`.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness content.
* Does not edit Primary's `WedhornNormalizedC1AssemblyStrong.lean`,
  Tertiary's localization-plus work, `WedhornBaseSpaFinalBridge.lean`,
  `WedhornOutsideRescue.lean`, `WedhornFinalAssemblyBridge.lean`,
  `WedhornStage2SpanExtractor.lean`, `WedhornNormalizedC1Assembly.lean`,
  `WedhornC1Assembly.lean`, `WedhornCompactExtraction.lean`,
  `WedhornCoverNormalization.lean`, `StandardCover.lean`, root imports,
  or `WedhornC1AssemblyStrong.lean`.

## Status of the three Stage-2 obligations from
`WedhornFinalAssemblyBridge`

| Obligation                | Status here |
|---------------------------|-------------|
| `h_C1` (regular)          | upgraded to `h_C1_strong` (single hypothesis) |
| `h_nonzero_cover_supplier`| **discharged** internally via Primary's strong wrapper |
| `h_outside_rescue`        | **discharged** internally via `h_base_eq_Spa` |
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A] [DecidableEq A]

/-- **Strong base-Spa final bridge**.

Composes Primary's
`exists_per_D_finset_via_normalized_C1Strong_supplier` (which packages
both `h_in_D` and the strengthened `h_cover_D_nonzero`) with
`span_top_via_strengthened_cover_and_outside_rescue` (Stage-2 span
extractor), `outside_rescue_pointwise_of_base_eq_Spa` (vacuous outside
rescue under `h_base_eq_Spa`), and
`hZavyalov_per_E_of_per_D_construction` (per-E refinement supplier).

Modulo the standard Tate pseudouniformizer pack and the directional
inclusions `(P.A₀ ≤ A⁺)` / `(A⁺ ⊆ P.A₀)`, the per-E refinement
existence is discharged from exactly:

* `h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺`
  — geometric Wedhorn cover-of-Spa hypothesis (automatic for
  `base.T := {1}, base.s := 1`).
* `h_C1_strong : C1SupplierStrong_local C.insertDenom`
  — strong C1 supplier on the normalized cover.

This is the cleanest assembly state currently achievable: a single
strong-supplier hypothesis under the standard Wedhorn setup. -/
theorem hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa
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
    (C : RationalCovering A)
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_C1_strong : C1SupplierStrong_local C.insertDenom) :
    rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S := by
  obtain ⟨mk_S_D, h_in_D, h_cover_D_nonzero⟩ :=
    exists_per_D_finset_via_normalized_C1Strong_supplier P hA₀_le π hI
      hπ_tn hπ_unit hArch C h_C1_strong
  have h_cover_D : ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s := by
    intro D hD v hv
    obtain ⟨f, hf, hv_f, _⟩ := h_cover_D_nonzero D hD v hv
    exact ⟨f, hf, hv_f⟩
  have h_span : Ideal.span ((C.covers.biUnion mk_S_D : Finset A) : Set A) = ⊤ :=
    span_top_via_strengthened_cover_and_outside_rescue P hAplus_le_A₀ C mk_S_D
      h_cover_D_nonzero
      (outside_rescue_pointwise_of_base_eq_Spa C h_base_eq_Spa mk_S_D)
  exact hZavyalov_per_E_of_per_D_construction C mk_S_D h_in_D h_cover_D h_span

end ValuationSpectrum
