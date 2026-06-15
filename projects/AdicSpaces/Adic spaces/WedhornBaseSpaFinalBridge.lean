/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornFinalAssemblyBridge
import «Adic spaces».WedhornOutsideRescue

/-!
# Wedhorn Base-Spa Final Bridge

Specialises
`WedhornFinalAssemblyBridge.hZavyalov_per_E_via_normalized_C1_supplier_explicit_stage2`
to the **standard Wedhorn cover-of-Spa setup** by discharging the
`h_outside_rescue` parameter via
`WedhornOutsideRescue.outside_rescue_of_base_eq_Spa`.

The result has only two abstract Stage-2 obligations remaining:

1. `h_C1 : C1Supplier_local C.insertDenom` — abstract C1 supplier on
   the normalized cover (Tertiary's territory).
2. `h_nonzero_cover_supplier` — third-clause `¬ v.vle f 0` strengthening
   of `h_cover_D` (Primary's strengthened compactness extraction
   territory).

The third obligation `h_outside_rescue` is replaced by the standard
geometric hypothesis `h_base_eq_Spa : rationalOpen C.base.T C.base.s =
Spa A A⁺`, which holds automatically in Wedhorn's standard setup
(`base.T := {1}, base.s := 1`; cf.
`Presheaf.rationalOpen_singleton_one`).

## What this file provides

* `hZavyalov_per_E_via_normalized_C1_supplier_of_base_eq_Spa` — the
  composed bridge described above. Theorem-level wrapper, not local
  patching.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness content.
* Does not edit `WedhornFinalAssemblyBridge`, `WedhornOutsideRescue`,
  `WedhornNormalizedC1Assembly`, `WedhornStage2SpanExtractor`,
  `WedhornC1Assembly`, `WedhornCompactExtraction`,
  `WedhornCoverNormalization`, `StandardCover`, root imports, or
  Primary/Tertiary work.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A] [DecidableEq A]

/-- **Base-Spa final bridge** — composes
`WedhornFinalAssemblyBridge.hZavyalov_per_E_via_normalized_C1_supplier_explicit_stage2`
with `WedhornOutsideRescue.outside_rescue_of_base_eq_Spa`.

Under the standard Wedhorn cover-of-Spa hypothesis `h_base_eq_Spa :
rationalOpen C.base.T C.base.s = Spa A A⁺`, the abstract
`h_outside_rescue` parameter of the final assembly bridge is discharged
vacuously, leaving only the normalized C1 supplier and the strong
nonzero per-D supplier as Stage-2 obligations. -/
theorem hZavyalov_per_E_via_normalized_C1_supplier_of_base_eq_Spa
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
    (h_C1 : C1Supplier_local C.insertDenom)
    (h_nonzero_cover_supplier : ∀ mk_S_D : RationalLocData A → Finset A,
      (∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) →
      (∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
        ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s) →
      ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
        ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
          ¬ v.vle f 0) :
    rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S :=
  hZavyalov_per_E_via_normalized_C1_supplier_explicit_stage2 P hA₀_le
    hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C h_C1 h_nonzero_cover_supplier
    (outside_rescue_of_base_eq_Spa C h_base_eq_Spa)

end ValuationSpectrum
