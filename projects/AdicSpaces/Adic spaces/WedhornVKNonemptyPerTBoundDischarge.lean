/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornCoverPieceStructuralDataDischarge

/-!
# Wedhorn 8.34(ii) — V_K-nonempty per-`t` bound max-element reduction (T046)

T045 (commit `53c86cd`) accepted the V_K branch decomposition discharge
of `WedhornCoverPieceStructuralData`, isolating the V_K-nonempty
per-`t` bound supply (`h_VK_per_t_le_s_D`) as the single named
non-tautological residual: at every `w ∈ Spa(Loc s, ⁺)` satisfying
f-membership AND σ-strict-domination by some `τ ∈ localizedTestFamily`
AND with V_K-nonempty witness `∃ t_0 ∈ T_D.image, σ-strict-dom`,
supply the per-`t'` upper bound `∀ t ∈ T_D.image, w.vle t (algMap s_D)`.

Per T034's docstring analysis (`WedhornAlphaTDComparisonSupplier.lean`),
the per-`t'` bound is **not** derivable from σ-strict-domination,
V_K-nonempty witness, Laurent-piece membership, or f-membership alone.
The genuine remaining mathematical residual is the **max-element
comparison** `w.vle τ_max (algMap s_D)` for `τ_max` a max of
`T_D.image` at `w`. This is the localized counterpart of the base
rational-open inclusion `v ∈ rationalOpen T_D s_D ⇒ v(t) ≤ v(s_D)`
restricted to the V_K-nonempty cover plus-piece — the explicit
Wedhorn 7.45 / 8.34(ii) α_T_D-branch ratio comparison.

This file lands the **max-element reduction** of T045's residual:
combines T034's `Spv.exists_max_vle_of_nonempty` with T033's
`alpha_T_D_per_t_bound_via_intermediate` to reduce T045's universal
per-`t'` supply to the single max-element comparison under the same
source restrictions (f-membership + σ-strict-dom + V_K-nonempty).

The reduction is non-tautological in structure: the per-`t'` bound
quantifies over all of `T_D.image`, while the max-element bound is
a single comparison at a distinguished element. The reduction
composes T034's max extraction (giving `τ_max ∈ T_D.image` with
maxness automatic from `w.vle_total`) with T033's intermediate-`τ`
arithmetic (per-`t'` bound from `τ ≤ algMap s_D` AND max-ness).

## What this file provides

* `h_VK_per_t_le_s_D_via_max_element_residual` — the main reduction:
  T045's V_K-nonempty per-`t'` supply follows from a V_K-nonempty
  max-element comparison residual. The V_K-nonempty witness gives
  nonempty `T_D.image`, T034's lemma extracts the max element
  `τ_max`, and T033's intermediate-τ arithmetic + transitivity
  through max-ness produces the per-`t'` bound.

* `WedhornCoverPieceStructuralData_via_max_element_residual_VK` —
  one-step composition with T045's structural data discharge.
  Produces `WedhornCoverPieceStructuralData` directly from the
  max-element residual, bypassing the intermediate per-`t'` supply.

* `C1SupplierStrong_local_via_max_element_residual_VK` — top-level
  C1 supplier wrapper composing this file's max-element reduction
  with T045's structural-data discharge and T044's Cov+ lift bridge.
  Produces `C1SupplierStrong_local C` from per-call delivery of
  σ-construction components plus the V_K-nonempty max-element
  comparison residual.

## Why max-element is closer to Wedhorn 7.45 ratio arithmetic

T045's per-`t'` bound supply is a **universal-quantified** statement
over `T_D.image`. The max-element bound is a **single comparison**
at a distinguished element of `T_D.image`. Wedhorn 7.45 and 8.34(ii)
prove the cover-refinement inclusion via explicit ratio
manipulations on a single intermediate element (e.g., the maximum,
or the σ-strict-dom witness). The max-element formulation matches
this single-comparison structure directly — it is the cleanest
isolation of the Wedhorn α_T_D-branch ratio bound.

The reduction is documented in the T034 / T035 lineage as the
natural Wedhorn-content target: T034's docstring labels the
max-element comparison as "the genuine remaining T021 residual"
and "the precise localized counterpart of the base rational-open
inclusion".

## Notes

* No root import; leaf-level.
* Imports only `WedhornCoverPieceStructuralDataDischarge` (T045,
  commit `53c86cd`), which transitively brings in T034's
  `Spv.exists_max_vle_of_nonempty`, T033's
  `alpha_T_D_per_t_bound_via_intermediate`, T031's V_K decomposition,
  and the σ-construction algebraic data API.
* No edits to T031–T045 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* Source-restriction is preserved: max-element residual is still
  conditioned on f-membership AND σ-strict-dom AND V_K-nonempty.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [PlusSubring A] in
/-- **Max-element reduction of T045's V_K-nonempty per-`t'` bound
residual** (T046 main reduction).

From a max-element comparison residual at every `w ∈ Spa(Loc s, ⁺)`
satisfying f-membership, σ-strict-dom by some `τ ∈ localizedTestFamily`,
AND with V_K-nonempty witness, derive T045's universal per-`t'` upper
bound supply.

**Proof**: take `w` and the source-restricted hypotheses. The
V_K-nonempty witness `(t_0, ...)` gives nonempty `T_D.image (algMap)`
(the witness `t_0` itself). Apply
`Spv.exists_max_vle_of_nonempty` (T034) to extract a max element
`τ_max ∈ T_D.image (algMap)` with `∀ t' ∈ T_D.image, w.vle t' τ_max`.
Apply the max-element residual to obtain
`w.vle τ_max (algMap s_D)`. For each `t ∈ T_D.image`, max-ness gives
`w.vle t τ_max`, and transitivity closes via `vle_trans` to give
`w.vle t (algMap s_D)`. -/
theorem h_VK_per_t_le_s_D_via_max_element_residual
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_max_element_residual :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∃ t_0 ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle (σ_loc : Localization.Away s) t_0 ∧
              ¬ w.vle t_0 (σ_loc : Localization.Away s)) →
          ∀ τ_max ∈ T_D.image (algebraMap A (Localization.Away s)),
            (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
                w.vle t' τ_max) →
            w.vle τ_max (algebraMap A (Localization.Away s) s_D)) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      ∀ τ ∈ localizedTestFamily s T_D s_D,
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
        (∃ t_0 ∈ T_D.image (algebraMap A (Localization.Away s)),
            w.vle (σ_loc : Localization.Away s) t_0 ∧
            ¬ w.vle t_0 (σ_loc : Localization.Away s)) →
        ∀ t ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t (algebraMap A (Localization.Away s) s_D) := by
  intro w hw_spa hw_f τ hτ hστ hVK
  -- V_K witness gives nonempty `T_D.image (algMap)`; extract max element via T034.
  obtain ⟨τ_max, hτ_max_mem, hτ_max_max⟩ :=
    Spv.exists_max_vle_of_nonempty w (hVK.imp fun _ h => h.1)
  -- Apply max-element residual, then T033's intermediate-τ arithmetic with τ := τ_max.
  exact alpha_T_D_per_t_bound_via_intermediate T_D s_D w τ_max
    (h_max_element_residual w hw_spa hw_f τ hτ hστ hVK τ_max
      hτ_max_mem hτ_max_max) hτ_max_max

omit [PlusSubring A] in
/-- **Structural data discharge via max-element residual under V_K-
nonempty source restriction** (T046 composed deliverable).

One-step composition: produces `WedhornCoverPieceStructuralData` from
the max-element comparison residual via T046's reduction +
T045's V_K branch decomposition discharge. The V_∅ branch is
auto-dispatched by T045 (transitivity in α_s_D, vacuous in α_T_D);
the V_K-nonempty branch reduces to the max-element residual via
T046's max extraction and intermediate-τ arithmetic. -/
theorem WedhornCoverPieceStructuralData_via_max_element_residual_VK
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_max_element_residual :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∃ t_0 ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle (σ_loc : Localization.Away s) t_0 ∧
              ¬ w.vle t_0 (σ_loc : Localization.Away s)) →
          ∀ τ_max ∈ T_D.image (algebraMap A (Localization.Away s)),
            (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
                w.vle t' τ_max) →
            w.vle τ_max (algebraMap A (Localization.Away s) s_D)) :
    WedhornCoverPieceStructuralData P T s hopen T_D s_D σ_loc :=
  WedhornCoverPieceStructuralData_via_VK_nonempty_residual P T s hopen
    T_D s_D σ_loc
    (h_VK_per_t_le_s_D_via_max_element_residual P T s hopen T_D s_D σ_loc
      h_max_element_residual)

/-- **Top-level: `C1SupplierStrong_local C` via max-element residual**
(T046 final deliverable).

Caller theorem producing `C1SupplierStrong_local C` from a per-call
delivery of σ-construction components plus the V_K-nonempty
max-element comparison residual. Composes T046's reduction with
T045's structural-data discharge and T044's Cov+ lift bridge.

**The single named non-tautological residual** is
`h_max_element_residual` — the max-element comparison
`w.vle τ_max (algMap s_D)` at LHS-satisfying `w` (in particular,
restricted to the V_K-nonempty branch). This is the cleanest
single-comparison form of the Wedhorn 8.34(ii) α_T_D-branch
cover-refinement deduction at the C1 layer. -/
theorem C1SupplierStrong_local_via_max_element_residual_VK
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (C : RationalCovering A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (h_per_call_components :
      letI : TopologicalSpace (Localization.Away C.base.s) :=
        locTopology P C.base.T C.base.s hopen_base
      letI : PlusSubring (Localization.Away C.base.s) :=
        localizationLocSubringPlusSubring P C.base.T C.base.s
      letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (σ_loc : (Localization.Away C.base.s)ˣ) (f : A),
        algebraMap A (Localization.Away C.base.s) f =
          (σ_loc : Localization.Away C.base.s) *
            (∏ t ∈ D.T.image
                (algebraMap A (Localization.Away C.base.s)), t) ∧
        (∀ w ∈ Spa (Localization.Away C.base.s)
              (Localization.Away C.base.s)⁺,
          ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
            w.vle (σ_loc : Localization.Away C.base.s) τ ∧
              ¬ w.vle τ (σ_loc : Localization.Away C.base.s)) ∧
        (∀ w ∈ Spa (Localization.Away C.base.s)
              (Localization.Away C.base.s)⁺,
          w.vle ((σ_loc : Localization.Away C.base.s) *
              (∏ t ∈ D.T.image
                  (algebraMap A (Localization.Away C.base.s)), t))
            (algebraMap A (Localization.Away C.base.s) C.base.s) →
          ∀ τ ∈ localizedTestFamily C.base.s D.T D.s,
            w.vle (σ_loc : Localization.Away C.base.s) τ ∧
              ¬ w.vle τ (σ_loc : Localization.Away C.base.s) →
            (∃ t_0 ∈ D.T.image
                (algebraMap A (Localization.Away C.base.s)),
                w.vle (σ_loc : Localization.Away C.base.s) t_0 ∧
                ¬ w.vle t_0 (σ_loc : Localization.Away C.base.s)) →
            ∀ τ_max ∈ D.T.image
                (algebraMap A (Localization.Away C.base.s)),
              (∀ t' ∈ D.T.image
                  (algebraMap A (Localization.Away C.base.s)),
                  w.vle t' τ_max) →
              w.vle τ_max
                (algebraMap A (Localization.Away C.base.s) D.s)) ∧
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0) :
    C1SupplierStrong_local C := by
  refine C1SupplierStrong_local_via_VK_nonempty_residual P hA₀_le C hopen_base ?_
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_loc, f, h_alg, h_dom, h_max_residual, hv_in_plus, hvf_nz⟩ :=
    h_per_call_components D hD v hv t ht hvt hvD_s
  exact ⟨σ_loc, f, h_alg, h_dom,
    h_VK_per_t_le_s_D_via_max_element_residual P C.base.T C.base.s
      hopen_base D.T D.s σ_loc h_max_residual, hv_in_plus, hvf_nz⟩

end ValuationSpectrum
