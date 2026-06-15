/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornNormalizedC1Assembly
import «Adic spaces».WedhornStage2SpanExtractor

/-!
# Wedhorn Final Assembly Bridge: explicit Stage-2 hypotheses

Composes
`WedhornNormalizedC1Assembly.hZavyalov_per_E_via_normalized_C1_supplier_with_h_span`
with
`WedhornStage2SpanExtractor.span_top_via_strengthened_cover_and_outside_rescue`
to replace the abstract `h_span_extractor` parameter by the two explicit
Stage-2 hypotheses (`h_cover_D_nonzero` and `h_outside_rescue`).

The result is the **clean final assembly interface**: the Wedhorn
per-E refinement existence is dischargeable from exactly three
hypotheses (modulo the Tate pseudouniformizer pack and the
`A⁺`/`P.A₀` directional inclusions):

1. `h_C1 : C1Supplier_local C.insertDenom` — the abstract C1 supplier on
   the normalized cover; will be discharged by Tertiary's
   `exists_single_f_refinement_at_t_via_dominating_unit` once committed
   (`WedhornStandardCoverRefinement.lean:91`).
2. `h_nonzero_cover_supplier` — the strengthening of `h_cover_D` to
   `h_cover_D_nonzero` (third-clause `¬ v.vle f 0` audited in
   `WedhornStrengthenedC1.lean`); will be discharged by Primary's
   strengthened compactness extraction once committed.
3. `h_outside_rescue` — the explicit outside-base no-common-zero
   witness, parameterized over the `mk_S_D` family produced internally
   by the normalized wrapper.

This file does **not** prove (2) or (3); both are kept abstract,
parameterized over the wrapper's internal `mk_S_D`. The compactness
extraction is **not duplicated**; this bridge only consumes the
existing chain.

## What this file provides

* `hZavyalov_per_E_via_normalized_C1_supplier_explicit_stage2` — the
  bridge composition described above. Sorry-free, axiom-clean.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness content.
* Does not edit `WedhornNormalizedC1Assembly`,
  `WedhornStage2SpanExtractor`, `WedhornStrengthenedC1`,
  `WedhornC1Assembly`, `WedhornCompactExtraction`,
  `WedhornCoverNormalization`, `StandardCover`, or root imports.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A] [DecidableEq A]

/-- **Wedhorn final assembly bridge with explicit Stage-2 hypotheses**.

Replaces the abstract `h_span_extractor` parameter of
`WedhornNormalizedC1Assembly.hZavyalov_per_E_via_normalized_C1_supplier_with_h_span`
with the two explicit Stage-2 hypotheses
`WedhornStage2SpanExtractor.span_top_via_strengthened_cover_and_outside_rescue`
consumes:

* `h_nonzero_cover_supplier` — strengthens any `h_cover_D` into
  `h_cover_D_nonzero` (additionally `¬ v.vle f 0`). Parameterized over
  `mk_S_D` so it works with the wrapper's internally-produced family.
  Once Primary's strengthened compactness extraction lands, this
  parameter is dischargeable from a strengthened C1 supplier on
  `C.insertDenom` and the existing chain.

* `h_outside_rescue` — the explicit outside-base no-common-zero witness,
  also parameterized over `mk_S_D`. This piece does **not** follow from
  the C1 chain because `RationalCovering.hcover` only covers
  `rationalOpen C.base.T C.base.s`, not all of `Spa A A⁺`; it must be
  supplied externally (geometric content). -/
theorem hZavyalov_per_E_via_normalized_C1_supplier_explicit_stage2
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
    (h_C1 : C1Supplier_local C.insertDenom)
    (h_nonzero_cover_supplier : ∀ mk_S_D : RationalLocData A → Finset A,
      (∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) →
      (∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
        ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s) →
      ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
        ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
          ¬ v.vle f 0)
    (h_outside_rescue : ∀ mk_S_D : RationalLocData A → Finset A,
      (∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) →
      ∀ v ∈ Spa A A⁺, v ∉ rationalOpen C.base.T C.base.s →
        ∃ f ∈ C.covers.biUnion mk_S_D, ¬ v.vle f 0) :
    rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S := by
  refine hZavyalov_per_E_via_normalized_C1_supplier_with_h_span P hA₀_le π hI
    hπ_tn hπ_unit hArch C h_C1 ?_
  intro mk_S_D h_in_D h_cover_D
  exact span_top_via_strengthened_cover_and_outside_rescue P hAplus_le_A₀ C mk_S_D
    (h_nonzero_cover_supplier mk_S_D h_in_D h_cover_D)
    (h_outside_rescue mk_S_D h_in_D)

end ValuationSpectrum
