/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornVKNonemptyPerTBoundDischarge

/-!
# Wedhorn 8.34(ii) — V_K-nonempty max-element comparison reduction (T047)

T046 (commit `1cd55d0`) accepted the max-element bridge
`h_VK_per_t_le_s_D_via_max_element_residual` and isolated the
remaining honest theorem-level residual: `h_max_element_residual` —
the V_K-nonempty α_T_D-branch ratio comparison
`w.vle τ_max (algMap s_D)` for `τ_max` a max of `T_D.image` at `w`.

Per T034 / T035's documented analysis, the universal-over-Spa
formulation of this residual is **mathematically false in general**:
T035's counter-example (`A = ℚ_p`, `T_D = {1}`, `s_D = p`,
`σ_loc = p^N`) satisfies σ-strict-domination, V_K-nonempty witness,
f-membership, and max-ness, yet `v_p.vle 1 p` fails. T035 identifies
the **natural source** as the base rational-subset condition
`v ∈ rationalOpen T_D s_D` on `Spa(A, A⁺)`, lifted to the localized
side via `comap`.

This file lands the **base rational-subset reduction** of T046's
max-element residual: T046's localized max-element comparison
follows from the comap-image base rational-subset condition
`comap (algebraMap A (Loc s)) w ∈ rationalOpen T_D s_D` on
`Spa(A, A⁺)`. The reduction is a clean application of `comap_vle`
through `Finset.mem_image` to identify `τ_max` with `algMap t` for
some `t ∈ T_D` and translate the base-side per-`t` bound back to
the localized side.

The new residual is **closer to Wedhorn 7.45 / 8.34(ii) ratio /
refinement arithmetic** than T046's because:

1. It is stated at the **base side** `Spa(A, A⁺)` — the natural
   setting of Wedhorn 7.45's cover-refinement statement.
2. It is a **single rational-open membership** — Wedhorn 7.45's
   primary object — rather than a max-element per-`t` comparison.
3. T035's docstring explicitly identifies it as "the natural source"
   for the per-`t' ` upper bound: `v ∈ rationalOpen T_D s_D` directly
   gives `∀ t ∈ T_D, v.vle t s_D`.

## What this file provides

* `h_max_element_residual_via_base_rational_subset_comap` — the
  main reduction: T046's V_K-nonempty max-element residual follows
  from the base rational-subset condition at the comap-lifted point
  `comap w ∈ rationalOpen T_D s_D` on `Spa(A, A⁺)`. Discharges via
  `comap_vle` + `Finset.mem_image`. Both σ-strict-dom, V_K-nonempty
  witness, and max-ness premises are unused in the reduction (the
  base rational-open subsumes them entirely): the new residual
  matches the mathematically natural Wedhorn 7.45 source.

* `WedhornCoverPieceStructuralData_via_base_rational_subset_comap` —
  one-step composition with T046's bridge and T045's discharge.
  Produces `WedhornCoverPieceStructuralData` directly from the base
  rational-subset comap residual.

* `C1SupplierStrong_local_via_base_rational_subset_comap` — top-level
  C1 supplier wrapper: composes this file's base-rational-subset
  reduction with T046, T045, T044's chain to produce
  `C1SupplierStrong_local C` from per-call delivery of σ-construction
  components plus the V_K-nonempty base-rational-subset comap
  residual.

## Why the base rational-subset comap residual is the natural Wedhorn
7.45 / 8.34(ii) reduction

Wedhorn 7.45's cover-refinement statement
`R(insert f T_base, s) ⊆ R(T_D, s_D)` on `Spa(A, A⁺)` lifts to a
statement about `comap`-images of localized Spa-points: at every
`w ∈ Spa(Loc s, ⁺)` arising as a comap-lift of a base point in
`R(insert f T_base, s)`, `comap w ∈ R(T_D, s_D)` holds. T047's
reduction asks for this **comap-image rational-subset condition**
explicitly under the σ-construction + V_K-nonempty premises. In
the actual Wedhorn 8.34(ii) cover-refinement context, the
σ-construction's σ_loc and the LHS rationalOpen conditions on `w`
ensure the comap-lift relation; combining with Wedhorn 7.45's base
inclusion discharges the comap-image residual at LHS-satisfying w.

The full discharge of the comap-image residual remains a Wedhorn 7.45
content — proving the base inclusion `R(insert f T_base, s) ⊆
R(T_D, s_D)` and verifying LHS-satisfaction at the relevant w —
which is the **next theorem-sized residual** beyond T047. Per T035's
analysis, this is the genuine Wedhorn 8.34(ii) cover-refinement
deduction; T047's reduction reformulates the residual in the natural
base-side / rational-open vocabulary, exposing the Wedhorn 7.45
content directly.

## Notes

* No root import; leaf-level.
* Imports only `WedhornVKNonemptyPerTBoundDischarge` (T046, commit
  `1cd55d0`), which transitively brings in T034's
  `Spv.exists_max_vle_of_nonempty`, T033's intermediate-`τ`
  arithmetic, T031's V_K decomposition, and the `comap_vle` /
  `rationalOpen` / `localizedTestFamily` API.
* No edits to T031–T046 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* Source-restriction is preserved: the new residual is conditioned
  on f-membership AND σ-strict-dom AND V_K-nonempty witness; no
  global universal-over-Spa per-`t'` upper bound is reintroduced.
* The σ-strict-dom and V_K-nonempty premises pass through unchanged
  to the new residual; the max-ness premise is dispatched internally
  via `Finset.mem_image`.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Base rational-subset comap reduction of T046's max-element
residual** (T047 main reduction).

From the base rational-subset condition at the comap-lifted point —
`comap (algebraMap A (Loc s)) w ∈ rationalOpen T_D s_D` on
`Spa(A, A⁺)` at every `w ∈ Spa(Loc s, ⁺)` satisfying f-membership +
σ-strict-dom + V_K-nonempty witness — derive T046's V_K-nonempty
max-element comparison residual.

**Proof**: take `w` with σ-construction + V_K witness + max-element
input. Apply the base rational-subset residual at `w` to obtain
`comap w ∈ rationalOpen T_D s_D` on `Spa(A, A⁺)`. Unfold `rationalOpen`:
`∀ t ∈ T_D, comap w.vle t s_D`. Since `τ_max ∈ T_D.image (algMap)`,
extract `t ∈ T_D` with `algMap t = τ_max` via `Finset.mem_image`.
Apply the per-`t` bound at this `t`, then translate via `comap_vle`
to get `w.vle τ_max (algMap s_D)`.

The base rational-subset comap residual is **closer to Wedhorn 7.45**
than T046's max-element comparison: it is stated at the base side,
matches Wedhorn 7.45's natural rational-open vocabulary, and is
identified by T035 as the natural source for the per-`t'` upper
bound. -/
theorem h_max_element_residual_via_base_rational_subset_comap
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_base_rational_subset_comap :
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
          comap (algebraMap A (Localization.Away s)) w ∈
            rationalOpen T_D s_D) :
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
          w.vle τ_max (algebraMap A (Localization.Away s) s_D) := by
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f τ hτ hστ hVK τ_max hτ_max_mem _h_max
  -- Extract `t ∈ T_D` with `algMap t = τ_max`.
  obtain ⟨t, ht_mem, hτ_max_eq⟩ := Finset.mem_image.mp hτ_max_mem
  -- Apply the base per-`t` bound (from the comap rational-subset residual),
  -- then translate via `comap_vle`.
  rw [← hτ_max_eq, ← comap_vle]
  exact (h_base_rational_subset_comap w hw_spa hw_f τ hτ hστ hVK).2.1 t ht_mem

/-- **Structural data discharge via base rational-subset comap
residual** (T047 composed deliverable).

One-step composition: produces `WedhornCoverPieceStructuralData` from
the base rational-subset comap residual via T047's reduction +
T046's max-element bridge + T045's V_K branch decomposition discharge.
Bypasses the intermediate max-element and per-`t'` supplies entirely,
exposing the base rational-subset comap as the single natural
Wedhorn 7.45 residual. -/
theorem WedhornCoverPieceStructuralData_via_base_rational_subset_comap
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_base_rational_subset_comap :
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
          comap (algebraMap A (Localization.Away s)) w ∈
            rationalOpen T_D s_D) :
    WedhornCoverPieceStructuralData P T s hopen T_D s_D σ_loc :=
  WedhornCoverPieceStructuralData_via_max_element_residual_VK P T s hopen
    T_D s_D σ_loc
    (h_max_element_residual_via_base_rational_subset_comap P T s hopen
      T_D s_D σ_loc h_base_rational_subset_comap)

/-- **Top-level: `C1SupplierStrong_local C` via base rational-subset
comap residual** (T047 final deliverable).

Caller theorem producing `C1SupplierStrong_local C` from per-call
delivery of σ-construction components plus the V_K-nonempty
base rational-subset comap residual. Composes T047's reduction with
T046's max-element bridge, T045's V_K branch decomposition, and
T044's Cov+ lift bridge.

**The single named non-tautological residual** is
`h_base_rational_subset_comap` — at every `w ∈ Spa(Loc s, ⁺)`
satisfying f-membership + σ-strict-dom + V_K-nonempty, the
comap-image of `w` lies in the base rational-open
`rationalOpen T_D s_D` on `Spa(A, A⁺)`. This is Wedhorn 7.45's
natural cover-refinement statement, lifted via `comap` to the
σ-construction + V_K context. T035's docstring identifies this as
"the natural source" for the per-`t'` upper bound. -/
theorem C1SupplierStrong_local_via_base_rational_subset_comap
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
            comap (algebraMap A (Localization.Away C.base.s)) w ∈
              rationalOpen D.T D.s) ∧
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0) :
    C1SupplierStrong_local C := by
  refine C1SupplierStrong_local_via_max_element_residual_VK P hA₀_le C hopen_base ?_
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_loc, f, h_alg, h_dom, h_base_residual, hv_in_plus, hvf_nz⟩ :=
    h_per_call_components D hD v hv t ht hvt hvD_s
  exact ⟨σ_loc, f, h_alg, h_dom,
    h_max_element_residual_via_base_rational_subset_comap
      P C.base.T C.base.s hopen_base D.T D.s σ_loc h_base_residual,
    hv_in_plus, hvf_nz⟩

end ValuationSpectrum
