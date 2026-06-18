/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornC1StrongSupplierBridge
import «Adic spaces».WedhornBaseSpaFinalBridgeStrong
import «Adic spaces».TateAcyclicityFinalAssembly

/-!
# Wedhorn 8.34(ii) — Part 2 consumer of `C1SupplierStrong_local C` (T063)

T061 (commit `dfcbeb3`) lands the leaf-level final-closure bridge
producing `C1SupplierStrong_local C` from per-call Wedhorn 8.33
multi-piece collapse data. This file lands the **downstream consumer
closure**: composes `C1SupplierStrong_local C` with the existing
end-to-end Part-2 assembly chain to produce the cover-level Part 2 of
Wedhorn Theorem 8.28(b) tate acyclicity directly.

## What this file provides

* `tateAcyclicity_Part2_via_C1SupplierStrong_local` — top-level
  consumer theorem composing `C1SupplierStrong_local C` with:
  1. `C1SupplierStrong_local_insertDenom_lift` (lift to the
     normalized cover under `h_covers_nonempty`).
  2. `hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa`
     (Stage-2 + outside-rescue absorbed under `h_base_eq_Spa`).
  3. `RationalCovering.tateAcyclicity_Part2_end_to_end_via_primary`
     (final Part-2 assembly with abstract Lane A / Lane B).

  Output: the gluing clause `∃ x : presheafValue C.base, ∀ E ∈ C.covers,
  restrictionMap C.base E _ x = fC E` from compatible cover-level
  sections — exactly Part 2 of `tateAcyclicity` (Wedhorn 8.28(b)).

## The single theorem-level residual

After this consumer bridge, the **only theorem-level mathematical
residual** to close Part 2 is `C1SupplierStrong_local C` itself —
which T061 already reduces to per-call Wedhorn Lemma 8.33 multi-piece
cover-acyclicity collapse data via
`C1SupplierStrong_local_via_lemma833_per_call_assembly`. The other
inputs to this bridge are:

* **Standard Tate / pseudouniformizer hypotheses** — the canonical
  `IsTateRing / IsNoetherianRing / T2Space / NonarchimedeanRing /
  IsHuberRing / HasLocLiftPowerBounded` typeclasses plus a chosen
  pseudouniformizer pack `(P, π, hI, hπ_tn, hπ_unit, hArch)`.
* **Plus-subring directional inclusions** — `hA₀_le : P.A₀ ≤ A⁺` and
  `hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀`.
* **`h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺`** —
  the Wedhorn cover-of-Spa hypothesis (automatic for `base.T := {1},
  base.s := 1`). Discharges `h_outside_rescue` via
  `outside_rescue_pointwise_of_base_eq_Spa`.
* **`h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty`** — the mild
  insertDenom-lift hypothesis (cover pieces with `D.T = ∅` are basic
  opens at `D.s`, an unusual degenerate case).
* **Lane A / Lane B suppliers** — universal Laurent-overlap gluing
  and per-E separation. Both are existing named blockers documented
  in `TateAcyclicityFinalAssembly.lean`'s docstring; they remain
  external residuals at this layer.
* **Compatible cover-section family `(fC, hC_compat)`** — the
  caller's input data for Part 2 (the compatible sections to glue).

## Closure status

This file's main theorem reduces tate acyclicity Part 2 to:

| Input | Source |
|-------|--------|
| `C1SupplierStrong_local C` | T061's per-call Lemma 8.33 bridge |
| `h_base_eq_Spa` | Wedhorn cover-of-Spa hypothesis (geometric input) |
| `h_covers_nonempty` | mild insertDenom-lift hypothesis (geometric input) |
| `lane_A_supplier` | universal Laurent-overlap gluing (existing blocker) |
| `lane_B_supplier` | universal per-E separation (existing blocker) |
| `(fC, hC_compat)` | caller's compatible section data |

Everything else (Stage-2 strengthening, `h_outside_rescue`,
`h_nonzero_cover_supplier`, normalization wrapping) is internally
absorbed by the existing strong-bridge chain. The deliverable matches
the T063 acceptance criterion: the strongest compiling bridge from
`C1SupplierStrong_local` into the existing tate acyclicity Part-2
assembly.

## Notes

* No root import; leaf-level.
* Imports `WedhornC1StrongSupplierBridge` (insertDenom-lift),
  `WedhornBaseSpaFinalBridgeStrong` (Stage-2-absorbed strong bridge),
  and `TateAcyclicityFinalAssembly` (final Part-2 assembly).
* No edits to T031–T062 accepted leaves, root imports, or final
  theorem signatures.
* No revival of T001/Lane-B/Jacobson/bivariate/Zavyalov/global
  universal-Spa-bound/σ-power-decay/M-power-decay detours; only the
  named final-assembly residuals remain.
* The deliverable substantively composes three accepted bridges; the
  proof is mechanical composition of theorem applications.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A] [DecidableEq A]

/-- **Top-level Part-2 consumer of `C1SupplierStrong_local C`** (T063 main
deliverable).

Composes T061's strong-supplier route with the existing end-to-end
Part-2 assembly chain to produce Part 2 of Wedhorn Theorem 8.28(b)
tate acyclicity from `C1SupplierStrong_local C` plus the standard
Wedhorn data and the documented final-assembly residuals.

**Composition pipeline:**

1. `C1SupplierStrong_local_insertDenom_lift` — lifts
   `C1SupplierStrong_local C` to `C1SupplierStrong_local C.insertDenom`
   under `h_covers_nonempty`.
2. `hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa`
   — discharges Stage-2 strengthening and outside rescue internally
   under `h_base_eq_Spa`, producing `hZavyalov_per_E`.
3. `RationalCovering.tateAcyclicity_Part2_end_to_end_via_primary` —
   final Part-2 assembly with abstract Lane A / Lane B suppliers and
   the caller's compatible section family.

**Output:** the gluing existential `∃ x : presheafValue C.base,
∀ E ∈ C.covers, restrictionMap C.base E _ x = fC E` from compatible
cover-level sections.

**Residuals:** five inputs at this layer — `C1SupplierStrong_local C`
(T061's reach), `h_base_eq_Spa` and `h_covers_nonempty` (geometric
inputs on the cover), `lane_A_supplier` and `lane_B_supplier`
(existing named blockers from `TateAcyclicityFinalAssembly`), and the
caller's `(fC, hC_compat)`. -/
theorem tateAcyclicity_Part2_via_C1SupplierStrong_local
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
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_C1_strong : C1SupplierStrong_local C)
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (lane_A_supplier : ∀ (S' : StandardCover A)
      (_hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts),
      ∀ (fV : ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.refinedVCovers S'.elts f₀ })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ C.refinedVCovers S'.elts f₀ },
        restrictionMap C.base D.1
          (C.refinedVCovers_subset_base S'.elts f₀ D.1 D.2) x = fV D)
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
        a = b) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  -- Compose the three accepted bridges: lift `C1SupplierStrong_local C` to the
  -- normalized cover, produce `hZavyalov_per_E` via the strong base-Spa bridge,
  -- then feed the final Part-2 assembly with abstract Lane A / Lane B.
  RationalCovering.tateAcyclicity_Part2_end_to_end_via_primary C hne
    (hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa
      P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C h_base_eq_Spa
      (C1SupplierStrong_local_insertDenom_lift C h_covers_nonempty h_C1_strong))
    f₀ fC hC_compat lane_A_supplier lane_B_supplier

end ValuationSpectrum
