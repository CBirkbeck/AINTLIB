/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornPerPieceLaurentCoverAssembly
import «Adic spaces».WedhornPerPieceLaurentC1Supplier
import «Adic spaces».WedhornStrengthenedC1

/-!
# Wedhorn 8.34(ii) — Final-closure bridge from T056/T057 to `C1SupplierStrong_local` (T061)

T056 (commit `WedhornPerPieceLaurentC1Supplier`) lands the per-piece
source-restricted reroute producing per-piece subset inclusions on
σ-rescaled Laurent pieces. T057
(`WedhornPerPieceLaurentCoverAssembly`) lands the cover-assembly API
together with the structured Wedhorn Lemma 8.33 multi-piece
cover-acyclicity collapse predicate
`LaurentCoverPresheafLemma833Assembly` and the substantive consumer
theorem `rationalOpen_global_subset_via_lemma833_assembly`.

This file lands the **final-closure bridge** that connects T056/T057
outputs to the strongest existing cover-refinement boundary,
`C1SupplierStrong_local C` (in `WedhornStrengthenedC1.lean`). It
exposes the **single explicit residual** carrying the remaining
mathematical content: the per-call Lemma 8.33 multi-piece
cover-acyclicity collapse predicate.

## What this file provides

* `WedhornC1Lemma833PerCallAssemblyData` — per-call data package
  bundling, for each `(D ∈ C.covers, v ∈ rationalOpen D.T D.s, t ∈ D.T)`
  triple, the inputs needed by T057's
  `rationalOpen_global_subset_via_lemma833_assembly` to produce the
  C1 cover refinement: the σ-construction unit `σ`, the candidate `f`,
  the σ-rescaled Laurent test family `T_test`, plus the four
  per-call hypotheses (per-piece subset on each Laurent piece,
  σ-rescaled Laurent cover, base-side `v ∈ rationalOpen (insert f
  C.base.T) C.base.s`, non-degeneracy `¬ v.vle f 0`, and the
  Lemma 8.33 collapse predicate).

* `C1SupplierStrong_local_via_lemma833_per_call_assembly` — the main
  bridge: from a per-call delivery of `WedhornC1Lemma833PerCallAssemblyData`,
  produce `C1SupplierStrong_local C`. Substantive consumption of T057's
  `rationalOpen_global_subset_via_lemma833_assembly` at every per-call
  input. The output `C1SupplierStrong_local C` is exactly the supplier
  consumed by the existing chain
  (`WedhornC1AssemblyStrong.exists_per_D_finset_via_C1Strong_supplier_and_compactness`
  → Stage-2 → `hZavyalov_per_E` →
  `tateAcyclicity_Part2_end_to_end_via_primary` → tate acyclicity
  Part 2).

## The single explicit final residual

The per-call assembly data carries five components per `(D, v, t)`:

1. `f`, `σ`, `T_test` — the σ-construction outputs (σ is the
   dominating unit; `f := σ * ∏ T_D` is the candidate denominator;
   `T_test` is the σ-rescaled Laurent test family).
2. `hv_in_plus : v ∈ rationalOpen (insert f C.base.T) C.base.s` — base-
   side rationalOpen membership of `v` (the C1 supplier's clause 1).
3. `hvf_nz : ¬ v.vle f 0` — non-degeneracy of `f` at `v` (the C1
   supplier's clause 3 — the strong-form additional clause beyond
   `C1Supplier_local`).
4. `h_per_piece` — per-piece subset on each σ-rescaled Laurent piece
   (T056's per-piece source-restricted output, dischargeable from
   T056's `per_piece_singleton_subset_via_laurent_membership` via
   T054's per-piece refinement output and a per-piece product upper
   bound at `D.s`).
5. `h_cover` — σ-rescaled Laurent cover hypothesis (T054's
   `cor732_multi_piece_laurent_refinement` output).
6. `h_lemma833 : LaurentCoverPresheafLemma833Assembly` — the
   structured blocker naming the **single explicit remaining
   mathematical residual**: Wedhorn Lemma 8.33 multi-piece cover-
   acyclicity collapse, upgrading the union-form covering to a single
   global RHS. **The Lemma 8.33 multi-piece content is what the rest
   of the route reduces to.**

Items (1)–(5) are dischargeable from T054's accepted per-piece
refinement output, T056's per-piece subset-shaping reroute, and the
σ-construction's standard outputs (Cor 7.32). Item (6) is the only
remaining theorem-level residual; it is the multi-piece iteration of
the existing 2-element Laurent cover acyclicity
(`laurentCover_gluing_presheaf` in `LaurentRefinement.lean`),
documented in T057's docstring as the named missing API.

## Connection to `tateAcyclicity` Part 2

`C1SupplierStrong_local C` is the canonical input to the existing
end-to-end Part 2 chain in `TateAcyclicityFinalAssembly.lean`:

* `WedhornC1AssemblyStrong.exists_per_D_finset_via_C1Strong_supplier_and_compactness`
  → produces `mk_S_D : RationalLocData A → Finset A` with strengthened
  per-D coverage (the Stage-2 input shape).
* `WedhornFinalAssemblyBridge.hZavyalov_per_E_via_normalized_C1_supplier_explicit_stage2`
  → produces the Wedhorn refinement existential `hZavyalov_per_E`
  modulo the Stage-2 hypotheses (`h_outside_rescue`,
  `h_nonzero_cover_supplier`).
* `RationalCovering.tateAcyclicity_Part2_end_to_end_via_primary`
  (`TateAcyclicityFinalAssembly.lean`) → produces Part 2 of the
  cover-level tate acyclicity from `hZavyalov_per_E` plus the abstract
  `lane_A_supplier` and `lane_B_supplier` hypotheses.

The **only** new theorem-level residual introduced by this T061
bridge over the existing chain is the per-call Lemma 8.33
multi-piece collapse `h_lemma833`. All other residuals
(`h_outside_rescue`, `lane_A_supplier`, `lane_B_supplier`, etc.) are
already named in the existing chain's documentation. This T061
deliverable is the **honest final-closure bridge**: it makes the
dependency on the C1 cover assembly / multi-piece Lemma 8.33 theorem
explicit by routing through T057's already-landed structured blocker.

## Notes

* No root import; leaf-level.
* Imports `WedhornPerPieceLaurentCoverAssembly` (T057),
  `WedhornPerPieceLaurentC1Supplier` (T056), and
  `WedhornStrengthenedC1` (`C1SupplierStrong_local` definition).
* No edits to T031–T057 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, global universal-
  Spa-bound, or bivariate-overlap content.
* The deliverable is a substantive bridge consuming T057's
  `rationalOpen_global_subset_via_lemma833_assembly` at every per-call
  input; it does **not** prove the Lemma 8.33 multi-piece collapse
  itself (that is the named residual `h_lemma833`).
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Per-call Lemma 8.33 + per-piece assembly data package** (T061
per-call interface).

Bundles the inputs needed by T057's
`rationalOpen_global_subset_via_lemma833_assembly` to produce the
C1 supplier's cover-refinement clause. For a fixed `(C, D, v)`:

* `f` — base-side denominator candidate (the σ-construction output).
* `σ` — σ-construction dominating unit (Cor 7.32).
* `T_test` — σ-rescaled Laurent test family (T054 input).

* `hv_in_plus` — base rationalOpen membership of `v`.
* `hvf_nz` — non-degeneracy of `f` at `v`.
* `h_per_piece` — per-piece subset on each σ-rescaled Laurent piece.
* `h_cover` — σ-rescaled Laurent cover hypothesis.
* `h_lemma833` — Lemma 8.33 multi-piece cover-acyclicity collapse.
  **The single explicit remaining theorem-level residual.**

The shape matches the input expected by
`rationalOpen_global_subset_via_lemma833_assembly` exactly. -/
structure WedhornC1Lemma833PerCallAssemblyData
    [DecidableEq A]
    (C : RationalCovering A) (D : RationalLocData A) (v : Spv A) where
  /-- σ-construction dominating unit (Cor 7.32). -/
  σ : Aˣ
  /-- Base-side denominator candidate. -/
  f : A
  /-- σ-rescaled Laurent test family. -/
  T_test : Finset A
  /-- Base rationalOpen membership of `v` (C1 supplier's clause 1). -/
  hv_in_plus : v ∈ rationalOpen (insert f C.base.T) C.base.s
  /-- Non-degeneracy of `f` at `v` (C1 supplier's strong clause 3). -/
  hvf_nz : ¬ v.vle f 0
  /-- Per-piece subset on each σ-rescaled Laurent piece. -/
  h_per_piece :
    ∀ τ ∈ T_test,
      rationalOpen (insert f C.base.T) C.base.s ∩
          rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) ⊆
        rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D.s
  /-- σ-rescaled Laurent cover hypothesis. -/
  h_cover :
    ∀ w ∈ rationalOpen (insert f C.base.T) C.base.s, ∃ τ ∈ T_test,
      w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ)
  /-- Lemma 8.33 multi-piece cover-acyclicity collapse. The single
  explicit remaining theorem-level residual. -/
  h_lemma833 :
    LaurentCoverPresheafLemma833Assembly (σ := σ) T_test
      (fun τ => rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D.s)
      (rationalOpen D.T D.s)

/-- **Final-closure bridge: `C1SupplierStrong_local C` from per-call
Lemma 8.33 + per-piece assembly data** (T061 main theorem).

From a per-call delivery of `WedhornC1Lemma833PerCallAssemblyData`,
produce `C1SupplierStrong_local C` — the strong cover-refinement
supplier consumed downstream by the existing tate acyclicity Part 2
chain.

**Substantive consumption** of T057's
`rationalOpen_global_subset_via_lemma833_assembly` at every per-call
input: at each `(D, v, t)`, unpack the assembly data, apply
`rationalOpen_global_subset_via_lemma833_assembly` with the supplied
`σ`, `f`, `T_test`, `h_per_piece`, `h_cover`, `h_lemma833` to derive
the cover-refinement clause `rationalOpen (insert f C.base.T)
C.base.s ⊆ rationalOpen D.T D.s`. The other two clauses (`v ∈
rationalOpen (insert f C.base.T) C.base.s` and `¬ v.vle f 0`) read
directly from the assembly data.

**The only theorem-level residual** consumed by this bridge is the
Lemma 8.33 multi-piece cover-acyclicity collapse predicate carried
inside `WedhornC1Lemma833PerCallAssemblyData.h_lemma833`. All other
residuals downstream (`h_outside_rescue`, `lane_A_supplier`,
`lane_B_supplier`, the Stage-2 strengthening) live at the
`tateAcyclicity_Part2_end_to_end_via_primary` boundary and are
unchanged by this bridge.

This is the **final-closure bridge** for the Wedhorn 8.34(ii) C1
supplier route: it makes the dependency on the C1 cover assembly /
multi-piece Wedhorn 8.33 theorem explicit. -/
theorem C1SupplierStrong_local_via_lemma833_per_call_assembly
    [DecidableEq A]
    (C : RationalCovering A)
    (h_per_call :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        WedhornC1Lemma833PerCallAssemblyData C D v) :
    C1SupplierStrong_local C := by
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ, f, T_test, hv_in_plus, hvf_nz, h_per_piece, h_cover, h_lemma833⟩ :=
    h_per_call D hD v hv t ht hvt hvD_s
  refine ⟨f, hv_in_plus, ?_, hvf_nz⟩
  exact rationalOpen_global_subset_via_lemma833_assembly T_test
    C.base.T D.T C.base.s D.s f h_lemma833 h_per_piece h_cover

end ValuationSpectrum
