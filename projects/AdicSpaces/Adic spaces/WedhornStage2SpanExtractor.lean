/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».StandardCover

/-!
# Wedhorn Stage-2 Span Extractor: small bridge + precise residual obligation

`hZavyalov_per_E_via_C1_supplier_and_compactness_with_h_span` (in
`WedhornC1Assembly.lean`, commit `7500a6a`) takes an explicit
`h_span_extractor` hypothesis as the residual Stage-2 obligation. This
file lands the **smallest local bridge** that reduces that obligation
to two more granular hypotheses derivable (potentially) from a
strengthened C1 supplier:

* a **strengthened per-D cover** clause: each plus-piece-at-`f` covering
  `v` additionally satisfies `¬ v.vle f 0` (i.e., `v(f) ≠ 0`);
* an **outside-base rescue** clause: every Spa point outside
  `rationalOpen C.base.T C.base.s` is non-zero on some `f` in the
  combined family.

Given both, `Prop 7.14` (`spanTop_iff_noCommonZero_spa`) closes the
ideal-theoretic span-top conclusion.

## What this file provides

* `span_top_via_strengthened_cover_and_outside_rescue` — the small
  bridge above. Sorry-free, axiom-clean.

## What this file does NOT provide / records as residual

* The **outside-base rescue** must be supplied by the caller; it cannot
  be derived from the `h_in_D` / `h_cover_D` data Theorem A produces
  because `RationalCovering.hcover` only covers `rationalOpen C.base.T
  C.base.s`, not all of `Spa A A⁺`.
* The **strengthened per-D cover** (with `¬ v.vle f 0` clause) is the
  third-clause strengthening of Tertiary's
  `exists_single_f_refinement_at_t_via_dominating_unit` signature
  recorded in the assembly-audit dependency plan; it is not currently
  exposed by Tertiary's target signature at
  `WedhornStandardCoverRefinement.lean:91`.

## Notes

* No root import: leaf-level, not in `Adic spaces.lean`.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson /
  T001 / faithful-flatness content.
* No edits to `StandardCover.lean`,
  `StandardCoverConditionalBridge.lean`, `WedhornCompactExtraction.lean`,
  `WedhornStandardCoverRefinement.lean`, or `WedhornC1Assembly.lean`.
* Imports only `StandardCover` (for `Spa`, `rationalOpen`,
  `RationalCovering`, `spanTop_iff_noCommonZero_spa`). -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Stage-2 span extractor — small bridge**.

For a fixed `mk_S_D : RationalLocData A → Finset A`, the union family
`C.covers.biUnion mk_S_D` generates the unit ideal in `A` if (and
trivially only if, by `Prop 7.14`) it has no common zero on
`Spa(A, A⁺)`. The "no common zero" check decomposes by case-splitting
on `v ∈ rationalOpen C.base.T C.base.s`:

* **Inside the base** (`v ∈ R(C.base.T, C.base.s)`): `C.hcover` provides
  `D ∈ C.covers` with `v ∈ rationalOpen D.T D.s`; the strengthened
  cover `h_cover_D_nonzero` then gives `f ∈ mk_S_D D` with `v(f) ≠ 0`.
* **Outside the base** (`v ∉ R(C.base.T, C.base.s)`): the explicit
  `h_outside_rescue` hypothesis supplies the witness directly.

The two hypotheses together close the no-common-zero check on all of
`Spa A A⁺`, and `spanTop_iff_noCommonZero_spa` lifts that to the
ideal-theoretic span-top conclusion. -/
theorem span_top_via_strengthened_cover_and_outside_rescue
    [DecidableEq A] (P : PairOfDefinition A)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (C : RationalCovering A)
    (mk_S_D : RationalLocData A → Finset A)
    (h_cover_D_nonzero : ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ f ∈ mk_S_D D,
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧ ¬ v.vle f 0)
    (h_outside_rescue : ∀ v ∈ Spa A A⁺,
      v ∉ rationalOpen C.base.T C.base.s →
        ∃ f ∈ C.covers.biUnion mk_S_D, ¬ v.vle f 0) :
    Ideal.span ((C.covers.biUnion mk_S_D : Finset A) : Set A) = ⊤ := by
  -- Reduce span-top to no-common-zero on Spa via Prop 7.14.
  refine (spanTop_iff_noCommonZero_spa P hAplus_le_A₀ _).mpr ?_
  intro v hv_spa
  -- Case-split on `v ∈ rationalOpen C.base.T C.base.s`.
  by_cases hv_base : v ∈ rationalOpen C.base.T C.base.s
  · -- Inside the base: use C.hcover + strengthened cover.
    obtain ⟨D, hD_mem, hv_D⟩ := C.hcover v hv_base
    obtain ⟨f, hf_mem, _hv_plus, hvf_ne⟩ :=
      h_cover_D_nonzero D hD_mem v hv_D
    refine ⟨f, ?_, hvf_ne⟩
    exact Finset.mem_biUnion.mpr ⟨D, hD_mem, hf_mem⟩
  · -- Outside the base: use the explicit rescue hypothesis.
    exact h_outside_rescue v hv_spa hv_base

end ValuationSpectrum
