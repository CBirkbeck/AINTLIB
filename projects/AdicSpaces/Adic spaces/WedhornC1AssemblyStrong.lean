/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornStrengthenedC1
import «Adic spaces».WedhornStrengthenedCompactExtraction

/-!
# Wedhorn Strong C1 Assembly: total `mk_S_D` with nonzero-coverage clause

Strengthened analogue of
`WedhornC1Assembly.exists_per_D_finset_via_C1_supplier_and_compactness`
(commit `7500a6a`): from `C1SupplierStrong_local C`
(`WedhornStrengthenedC1.lean`, commit `2214684`) plus the Wedhorn
7.30(3) normalization `D.s ∈ D.T` for each `D ∈ C.covers`, produce a
total function `mk_S_D : RationalLocData A → Finset A` whose per-D
coverage clause carries the third clause `¬ v.vle f 0` (i.e.,
`v(f) ≠ 0`) consumed by
`WedhornStage2SpanExtractor.span_top_via_strengthened_cover_and_outside_rescue`
(commit `63c8ecd`).

## Composition layers

* `WedhornStrengthenedC1.exists_single_f_refining_point_in_D_via_C1SupplierStrong`
  — strong supplier + `D.s ∈ D.T` → strengthened pointwise C1.
* `WedhornStrengthenedCompactExtraction.mk_S_D_of_C1Strong_and_compactness`
  — strengthened pointwise C1 → per-D Finset with strengthened coverage.
* This file — aggregation of the per-D Finsets into a total
  `mk_S_D : RationalLocData A → Finset A` (defaulting to `∅` on cover
  pieces outside `C.covers`).

## What this file provides

* `exists_per_D_finset_via_C1Strong_supplier_and_compactness` — total
  `mk_S_D` with both containment and strengthened coverage. Sorry-free,
  axiom-clean.

## Notes

* No root import: leaf-level, not in `Adic spaces.lean`.
* No edits to `WedhornStrengthenedC1.lean`,
  `WedhornStrengthenedCompactExtraction.lean`,
  `WedhornCompactExtraction.lean` (Secondary), or
  `WedhornStandardCoverRefinement.lean` (Tertiary).
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson /
  T001 / faithful-flatness content.
* `mk_S_D` is built by `Classical.dec` dispatch on `D ∈ C.covers`
  (no project-level `DecidableEq` for `RationalLocData A`); on
  out-of-cover inputs `mk_S_D D = ∅`. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Strong C1 assembly: total `mk_S_D` with strengthened coverage**.

Strengthened analogue of
`WedhornC1Assembly.exists_per_D_finset_via_C1_supplier_and_compactness`:
the per-D coverage clause additionally carries `¬ v.vle f 0`
(i.e., `v(f) ≠ 0`).

For each `D ∈ C.covers`, the strong supplier `C1SupplierStrong_local`
plus the normalization `D.s ∈ D.T` produces a strengthened pointwise C1
witness on every `v ∈ rationalOpen D.T D.s`
(via `exists_single_f_refining_point_in_D_via_C1SupplierStrong`).
The strengthened compact-extraction wrapper
(`mk_S_D_of_C1Strong_and_compactness`) then extracts a finite
`S_D : Finset A` whose plus-piece-coverage carries the third clause.

Aggregating these per-D Finsets via `Classical.dec` dispatch on
`D ∈ C.covers` (defaulting to `∅` on out-of-cover pieces) produces the
total `mk_S_D : RationalLocData A → Finset A`. The output shape exactly
matches the input expected by
`WedhornStage2SpanExtractor.span_top_via_strengthened_cover_and_outside_rescue`
(at the `h_cover_D_nonzero` argument). -/
theorem exists_per_D_finset_via_C1Strong_supplier_and_compactness
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A)
    (h_C1_strong : C1SupplierStrong_local C)
    (h_normalized : ∀ D ∈ C.covers, D.s ∈ D.T) :
    ∃ mk_S_D : RationalLocData A → Finset A,
      (∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) ∧
      (∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
        ∃ f ∈ mk_S_D D,
          v ∈ rationalOpen (insert f C.base.T) C.base.s ∧ ¬ v.vle f 0) := by
  classical
  -- Step 1: per-D strengthened pointwise C1 via the strong-supplier bridge.
  have hC1_pointwise_strong : ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ v ∈ rationalOpen D.T D.s, ∃ f : A,
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s ∧
        ¬ v.vle f 0 := by
    intro D hD v hv
    exact exists_single_f_refining_point_in_D_via_C1SupplierStrong C h_C1_strong D hD
      (h_normalized D hD) v hv
  -- Step 2: per-D Finset with strengthened coverage via compactness.
  have hPerD : ∀ (D : RationalLocData A), D ∈ C.covers →
      ∃ S : Finset A,
        (∀ f ∈ S,
          rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) ∧
        (∀ v ∈ rationalOpen D.T D.s,
          ∃ f ∈ S,
            v ∈ rationalOpen (insert f C.base.T) C.base.s ∧ ¬ v.vle f 0) := by
    intro D hD
    exact mk_S_D_of_C1Strong_and_compactness P hA₀_le π hI hπ_tn hπ_unit hArch C D
      (hC1_pointwise_strong D hD)
  -- Step 3: aggregate per-D Finsets into a total function via Classical.dec.
  let mk_S_D : RationalLocData A → Finset A := fun D =>
    if hD : D ∈ C.covers then Classical.choose (hPerD D hD) else ∅
  refine ⟨mk_S_D, ?_, ?_⟩
  · -- containment per D, per f.
    intro D hD f hf
    have h_unfold : mk_S_D D = Classical.choose (hPerD D hD) := by
      simp [mk_S_D, hD]
    rw [h_unfold] at hf
    exact (Classical.choose_spec (hPerD D hD)).1 f hf
  · -- strengthened coverage per D, per v.
    intro D hD v hv
    have h_unfold : mk_S_D D = Classical.choose (hPerD D hD) := by
      simp [mk_S_D, hD]
    rw [h_unfold]
    exact (Classical.choose_spec (hPerD D hD)).2 v hv

end ValuationSpectrum
