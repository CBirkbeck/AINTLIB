/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornCovPlusLiftPerTBoundDischarge

/-!
# Wedhorn 8.34(ii) — Source-restricted structural data discharge (T045)

T044 (commit `5cdf55b`) accepted the source-restricted Cov+ lift bridge
`C1SupplierStrong_local_via_cov_plus_piece_lift_via_structural_data`,
isolating the remaining honest mathematical residual as T037's
`WedhornCoverPieceStructuralData` itself.

This file lands the **V_K branch decomposition discharge** of T037's
structural data Prop: combining T031's
`laurent_VK_branch_decomposition_at` (the per-`w` exhaustive split
into V_∅ and V_K-nonempty branches) with the T037 source-restricted
σ-strict-domination + f-membership premises gives:

* **V_∅ + α_s_D branch**: dischargeable automatically by transitivity
  through the σ-strict-dom hypothesis. ✓
* **V_∅ + α_T_D branch**: vacuous (V_∅ + σ-strict-dom by τ ∈ T_D.image
  contradict directly). ✓
* **V_K-nonempty branch**: the genuine remaining residual, narrowing
  T037's structural-data residual to the V_K-nonempty subset of
  `Spa(Loc s, ⁺)`.

The non-vanishing conclusion `¬ w.vle (algebraMap s_D) 0` is fully
auto-dispatched in all branches via `not_vle_zero_of_strict_dominator`
(α_s_D case) and transitivity through the per-`t'` bound at `t' = τ`
(α_T_D case).

## What this file provides

* `WedhornCoverPieceStructuralData_via_VK_nonempty_residual` — the
  main bridge: structural data follows from a single named residual,
  the V_K-nonempty per-`t'` upper-bound supply (per-`w` with
  f-membership AND σ-strict-dom AND V_K-nonempty witness, supply
  per-`t'` upper bound at `algebraMap s_D`). The residual is
  strictly closer to Wedhorn 8.34(ii) / 7.45 cover-refinement
  arithmetic than T037's per-`t'` supply: it carries the V_K-nonempty
  witness (a σ-strict-dom by some `t_0 ∈ T_D.image`) explicitly,
  matching the α_T_D-branch context where Wedhorn's ratio
  manipulations apply.

* `C1SupplierStrong_local_via_VK_nonempty_residual` — top-level C1
  supplier wrapper composing the V_K-nonempty residual discharge
  with T044's `C1SupplierStrong_local_via_cov_plus_piece_lift_via_structural_data`.
  Produces `C1SupplierStrong_local C` from per-call delivery of
  σ-construction components plus the V_K-nonempty per-`t'` residual.

## Why this is closer to Wedhorn 7.45 / 8.34(ii) than T037

T037's residual `h_per_t_le_s_D_at_w` is purely the per-`t'` upper
bound at LHS-satisfying `w`, with no decomposition by branch. T045's
residual narrows the supply to V_K-nonempty `w` only — the V_∅ branch
is fully dispatched mechanically. This matches Wedhorn 7.45's
α_T_D-branch arithmetic, where `T_D.image` necessarily contains an
element σ-strictly dominating `σ_loc` (the V_K-nonempty witness).

The vacuous α_T_D + V_∅ case captures the structural fact: σ-strict-
dom by `τ ∈ T_D.image` AND `τ ≤ σ_loc` (V_∅) are inconsistent. This
is automatic logic, not Wedhorn-specific.

## The named V_K-nonempty residual

```
∀ w ∈ Spa(Loc s, ⁺),
  w.vle (σ_loc * ∏ T_D.image (algMap)) (algMap s) →   -- f-membership
  ∀ τ ∈ localizedTestFamily,
  w.vle σ_loc τ ∧ ¬ w.vle τ σ_loc →                   -- σ-strict-dom
  (∃ t_0 ∈ T_D.image (algMap),
     w.vle σ_loc t_0 ∧ ¬ w.vle t_0 σ_loc) →           -- V_K-nonempty
    ∀ t ∈ T_D.image (algMap), w.vle t (algMap s_D)    -- per-t' bound
```

**Mathematical content**: at every `w` in the cover plus-piece (LHS
rationalOpen via comap) AND in the V_K-nonempty branch, the
rational-subset condition `w ∈ rationalOpen (T_D.image) (algMap s_D)`
holds. This is the substantive content of Wedhorn 7.45's
α_T_D-branch refinement deduction: when `T_D.image` contains an
element σ-strictly dominating `σ_loc`, the f-membership premise
forces all `T_D.image` elements to be bounded by `algebraMap s_D`.

The residual is genuinely non-tautological — it requires the
α_T_D-branch ratio arithmetic from Wedhorn 7.45 / 8.34(ii) — and is
the cleanest statement of the remaining mathematical content at the
T037 → C1 supplier interface.

## Notes

* No root import; leaf-level.
* Imports only `WedhornCovPlusLiftPerTBoundDischarge` (T044, commit
  `5cdf55b`), which transitively brings in T031's
  `laurent_VK_branch_decomposition_at`, T037's
  `WedhornCoverPieceStructuralData`, T035's source-restriction
  analysis, and the `localizedTestFamily` API.
* No edits to T031–T044 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* The source-restriction is preserved at every layer: the `w`
  hypotheses include f-membership AND σ-strict-domination AND
  V_K-nonempty witness; no global universal-over-`Spa(Loc s, ⁺)`
  per-`w` upper-bound is reintroduced.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [PlusSubring A] in
/-- **V_K branch decomposition discharge of `WedhornCoverPieceStructuralData`**
(T045 main bridge).

Splits T037's source-restricted structural data Prop along T031's
exhaustive V_∅ vs V_K-nonempty decomposition at every `w`, dispatching
the V_∅ branch automatically and reducing to the V_K-nonempty
per-`t'` upper-bound residual.

**V_∅ + α_s_D branch (auto-dispatch)**: V_∅ at `w` gives
`∀ t' ∈ T_D.image, w.vle t' σ_loc`; σ-strict-dom by `τ = algMap s_D`
gives `w.vle σ_loc (algMap s_D)`. Transitivity yields
`∀ t' ∈ T_D.image, w.vle t' (algMap s_D)`. Non-vanishing of
`algMap s_D` follows from σ-strict-dom directly via
`not_vle_zero_of_strict_dominator`.

**V_∅ + α_T_D branch (vacuous)**: V_∅ at `w` gives `w.vle τ σ_loc`
for `τ ∈ T_D.image`; σ-strict-dom by `τ` gives `¬ w.vle τ σ_loc`.
Direct contradiction.

**V_K-nonempty branch (residual)**: at `w` with V_K-nonempty witness
(some `t_0 ∈ T_D.image` σ-strictly dominating `σ_loc`), supply the
per-`t'` upper bound at `algMap s_D`. Non-vanishing is then
auto-derived in α_s_D case via σ-strict-dom and in α_T_D case via
transitivity through the per-`t'` bound at `t' = τ`.

## Hypotheses

* `h_VK_per_t_le_s_D` — V_K-nonempty per-`t'` residual: at every
  `w ∈ Spa(Loc s, ⁺)` satisfying f-membership, σ-strict-dom by some
  `τ ∈ localizedTestFamily`, AND with V_K-nonempty witness, every
  `t ∈ T_D.image (algMap)` is bounded above by `algMap s_D` at `w`.
  This is the **single named non-tautological residual** of the
  bridge.

## Conclusion

`WedhornCoverPieceStructuralData P T s hopen T_D s_D σ_loc`. -/
theorem WedhornCoverPieceStructuralData_via_VK_nonempty_residual
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_VK_per_t_le_s_D :
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
            w.vle t (algebraMap A (Localization.Away s) s_D)) :
    WedhornCoverPieceStructuralData P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro τ hτ w hw_spa hw_f hστ
  rcases laurent_VK_branch_decomposition_at T_D σ_loc w with
    h_V_empty | h_VK_nonempty
  · -- V_∅ branch.
    rw [mem_localizedTestFamily_iff] at hτ
    rcases hτ with rfl | hτ_in_T_D
    · -- α_s_D + V_∅: per-`t'` by transitivity through σ_loc.
      refine ⟨fun t ht ↦ w.vle_trans (h_V_empty t ht) hστ.1, ?_⟩
      exact not_vle_zero_of_strict_dominator hστ.2
    · -- α_T_D + V_∅: vacuous (σ-strict-dom by τ ∈ T_D.image vs V_∅ at τ).
      exact absurd (h_V_empty τ hτ_in_T_D) hστ.2
  · -- V_K-nonempty branch: apply the residual supply.
    have h_per_t :
        ∀ t ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t (algebraMap A (Localization.Away s) s_D) :=
      h_VK_per_t_le_s_D w hw_spa hw_f τ hτ hστ h_VK_nonempty
    refine ⟨h_per_t, ?_⟩
    rw [mem_localizedTestFamily_iff] at hτ
    rcases hτ with rfl | hτ_in_T_D
    · exact not_vle_zero_of_strict_dominator hστ.2
    · intro h_s_D_zero
      exact not_vle_zero_of_strict_dominator hστ.2
        (w.vle_trans (h_per_t τ hτ_in_T_D) h_s_D_zero)

/-- **Top-level: `C1SupplierStrong_local C` via V_K-nonempty residual**
(T045 final deliverable).

Caller theorem producing `C1SupplierStrong_local C` from a per-call
delivery of σ-construction components plus the V_K-nonempty per-`t'`
upper-bound residual. Composes
`WedhornCoverPieceStructuralData_via_VK_nonempty_residual` with T044's
`C1SupplierStrong_local_via_cov_plus_piece_lift_via_structural_data`.

**Per-call inputs**: σ_loc, f, h_alg (Cor 7.32 algebraic identity),
hσ_loc_dom (Cor 7.32 σ-strict-dom over `localizedTestFamily`),
h_VK_per_t_le_s_D (V_K-nonempty per-`t'` residual), hv_in_plus
(rationalOpen membership of `v`), hvf_nz (f-non-degeneracy of `v`).

**The single named non-tautological residual** is
`h_VK_per_t_le_s_D` — the V_K-nonempty per-`t'` upper-bound supply.
This is the cleanest narrowing of the Wedhorn 8.34(ii) cover-
refinement deduction at the C1 layer: the V_∅ branch is
mechanically dispatched, leaving the α_T_D-branch ratio arithmetic
(σ-strict-dom by some `t_0 ∈ T_D.image` AND f-membership →
per-`t'` bound at `algMap s_D`) as the sole remaining input. -/
theorem C1SupplierStrong_local_via_VK_nonempty_residual
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
            ∀ t ∈ D.T.image
                (algebraMap A (Localization.Away C.base.s)),
              w.vle t
                (algebraMap A (Localization.Away C.base.s) D.s)) ∧
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0) :
    C1SupplierStrong_local C := by
  letI : TopologicalSpace (Localization.Away C.base.s) :=
    locTopology P C.base.T C.base.s hopen_base
  letI : PlusSubring (Localization.Away C.base.s) :=
    localizationLocSubringPlusSubring P C.base.T C.base.s
  letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
  refine C1SupplierStrong_local_via_cov_plus_piece_lift_via_structural_data
    P hA₀_le C hopen_base ?_
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_loc, f, h_alg, h_dom, h_VK_per_t, hv_in_plus, hvf_nz⟩ :=
    h_per_call_components D hD v hv t ht hvt hvD_s
  refine ⟨σ_loc, f, h_alg, h_dom, ?_, hv_in_plus, hvf_nz⟩
  exact WedhornCoverPieceStructuralData_via_VK_nonempty_residual
    P C.base.T C.base.s hopen_base D.T D.s σ_loc h_VK_per_t

end ValuationSpectrum
