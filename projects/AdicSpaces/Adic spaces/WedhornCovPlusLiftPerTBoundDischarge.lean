/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornC1ComapLiftRestrictedSupplier

/-!
# Wedhorn 8.34(ii) — Source-restricted Cov+ lift per-`t` bound discharge (T044)

T043 (commit `08388d4`) accepted the source-restricted predicate
`WedhornCoverPieceCovPlusPieceLiftPerTBound`, replacing the false
universal-over-`Spa(Loc s, ⁺)` per-`w` per-`t` upper-bound supplier
of T039–T042 with a predicate quantified only over `w` satisfying
the LHS rationalOpen conditions for `(insert f T_base, s)` (the
cover plus-piece). At LHS-violating `w`, the predicate is vacuously
trivial, sidestepping T035's counter-example.

This file lands the **honest source-restricted discharge** of T043's
predicate: from the standard Cor 7.32 σ-construction data — the
denominator-clearing identity `algebraMap f = σ_loc * ∏ T_D.image
algebraMap`, the σ-strict-domination supplier over
`localizedTestFamily s T_D s_D`, and T037's source-restricted
`WedhornCoverPieceStructuralData` (the per-`w`-with-f-membership-and-
σ-strict-dom Prop matching the structural data shape consumed by
`rationalOpen_subset_base_via_local_Cor732_chain`) — we deduce
T043's predicate.

## Forward bridge (this file's main theorem)

`WedhornCoverPieceCovPlusPieceLiftPerTBound_via_structural_data`:
the predicate follows from T037's `WedhornCoverPieceStructuralData`
plus `h_alg` (Cor 7.32 algebraic identity) plus `hσ_loc_dom` (Cor 7.32
σ-strict-dom over `localizedTestFamily`). The discharge is a clean
composition:

1. The LHS rationalOpen condition at `c = f` (which is in
   `insert f T_base` by `Finset.mem_insert_self`) gives `w.vle
   (algebraMap f) (algebraMap s)`.
2. By `h_alg`, this is the f-membership premise of structural data.
3. `hσ_loc_dom` at `w` gives some `τ ∈ localizedTestFamily` with
   σ-strict-dom.
4. Apply structural data at `(τ, w)`: per-`t'` upper bound at
   `algebraMap s_D` AND non-vanishing of `algebraMap s_D`.
5. Translate `T_D.image (algebraMap)` back to `T_D` via
   `Finset.mem_image`.

## Top-level deliverable

`C1SupplierStrong_local_via_cov_plus_piece_lift_via_structural_data`:
caller theorem producing `C1SupplierStrong_local C` from a per-call
delivery of σ-construction components (σ_loc, f, h_alg, hσ_loc_dom,
structural data, plus rationalOpen membership and f-non-degeneracy of
v). Composes this file's forward bridge with T043's
`C1SupplierStrong_local_via_cov_plus_piece_lift_supplier`.

## Why this is the natural σ-construction discharge

T037's `WedhornCoverPieceStructuralData` was designed precisely as
the source-restricted Prop matching the per-`w`-with-f-membership-
and-σ-strict-dom shape required by Wedhorn 7.45's α_T_D-branch
cover-refinement deduction. T043's predicate is the comap-lift form
of the cover refinement at the source plus-piece, and the natural
bridge between them is the σ-construction's algebraic identity +
σ-strict-dom data.

## Remaining mathematical content

The structural data Prop `WedhornCoverPieceStructuralData` is itself
the "honest σ-construction residual": at every `w ∈ Spa(Loc s, ⁺)`
satisfying f-membership AND σ-strict-domination, the per-`t'` upper
bound at `algebraMap s_D` plus s_D non-vanishing must hold. This is
mathematically TRUE under the Wedhorn 7.45 cover refinement and
matches T036/T037's source-restricted shape with explicit per-`w`
premises. Honest discharge of `WedhornCoverPieceStructuralData` is
the genuine substance of Wedhorn 8.34(ii) Step 2; this file does not
attempt that — it composes it cleanly into T043's predicate.

## Notes

* No root import; leaf-level.
* Imports only `WedhornC1ComapLiftRestrictedSupplier` (T043, commit
  `08388d4`), which transitively brings in T037's
  `WedhornCoverPieceStructuralData`,
  `rationalOpen_subset_base_via_cover_piece_structural_data`, and
  the `localizedTestFamily` API via the T031–T037 chain.
* No edits to T027–T043 accepted files, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No global universal-over-`Spa` per-`w` upper-bound resurrection:
  this file's discharge is source-restricted at every layer.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [PlusSubring A] in
/-- **Forward bridge: T043's source-restricted predicate from T037's
structural data + σ-construction algebraic data** (T044 main bridge).

From:
* `σ_loc : (Localization.Away s)ˣ` — the σ-unit of Cor 7.32.
* `h_alg : algebraMap f = σ_loc * ∏ T_D.image (algebraMap)` —
  the canonical denominator-cleared algebraic identity.
* `hσ_loc_dom : ∀ w ∈ Spa(Loc s, ⁺), ∃ τ ∈ localizedTestFamily,
  σ-strict-dom` — the Cor 7.32 σ-strict-domination output.
* `h_struct : WedhornCoverPieceStructuralData` — T037's
  source-restricted structural Prop (per-(τ, w) with f-membership
  and σ-strict-dom premises → per-`t'` upper bound + s_D
  non-vanishing).

Conclude `WedhornCoverPieceCovPlusPieceLiftPerTBound P T s hopen
T_base T_D s_D f` (T043's source-restricted predicate).

**Proof**: take `w ∈ Spa(Loc s, locSubring)` satisfying the LHS
rationalOpen conditions for `(insert f T_base, s)`. The condition at
`c = f` (which is in `insert f T_base` by `Finset.mem_insert_self`)
gives `w.vle (algebraMap f) (algebraMap s)`. Substituting `h_alg`
yields the f-membership premise of `h_struct`. Extract a σ-strict-dom
witness `τ` from `hσ_loc_dom w`. Apply `h_struct` at `(τ, w)`. The
conclusion translates from `T_D.image (algebraMap)` back to `T_D`
via `Finset.mem_image`. -/
theorem WedhornCoverPieceCovPlusPieceLiftPerTBound_via_structural_data
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_base T_D : Finset A) (s_D : A) (f : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_alg :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) f =
        (σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_struct :
      WedhornCoverPieceStructuralData P T s hopen T_D s_D σ_loc) :
    WedhornCoverPieceCovPlusPieceLiftPerTBound P T s hopen
      T_base T_D s_D f := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_LHS _hw_s_ne
  -- LHS condition at c = f gives `w.vle (algebraMap f) (algebraMap s)`.
  have hwf : w.vle (algebraMap A (Localization.Away s) f)
      (algebraMap A (Localization.Away s) s) :=
    hw_LHS f (Finset.mem_insert_self f T_base)
  -- Substitute h_alg to get the f-membership premise of structural data.
  have hw_f_membership :
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) := by
    rw [← h_alg]; exact hwf
  -- Extract σ-strict-dom witness via hσ_loc_dom.
  obtain ⟨τ, hτ_mem, hστ⟩ := hσ_loc_dom w hw_spa
  -- Apply structural data at (τ, w).
  obtain ⟨h_per_t', h_s_D_ne⟩ :=
    h_struct τ hτ_mem w hw_spa hw_f_membership hστ
  -- Translate per-t' on T_D.image back to per-t on T_D.
  refine ⟨fun t ht => ?_, h_s_D_ne⟩
  exact h_per_t' (algebraMap A (Localization.Away s) t)
    (Finset.mem_image.mpr ⟨t, ht, rfl⟩)

/-- **Per-call composition: `WedhornC1PerCallSupplyCovPlusPieceLift`
via structural data** (T044 composed deliverable).

Produces T043's per-call supply predicate from the natural
σ-construction inputs at one per-call site:

* `f, σ_loc, h_alg` — Cor 7.32 algebraic identity.
* `hσ_loc_dom` — Cor 7.32 σ-strict-dom over `localizedTestFamily
  C.base.s D.T D.s`.
* `h_struct` — T037's source-restricted structural data Prop at
  `(C.base.T, C.base.s, D.T, D.s, σ_loc)`.
* `hv_in_plus, hvf_nz` — the standard rationalOpen-membership and
  f-non-degeneracy of `v` from `C1SupplierStrong_local`'s output
  shape.

Composes
`WedhornCoverPieceCovPlusPieceLiftPerTBound_via_structural_data`
with T043's per-call supply unfolding. -/
theorem WedhornC1PerCallSupplyCovPlusPieceLift_via_structural_data
    [DecidableEq A]
    (P : PairOfDefinition A) (C : RationalCovering A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) (v : Spv A) :
    letI : TopologicalSpace (Localization.Away C.base.s) :=
      locTopology P C.base.T C.base.s hopen_base
    letI : PlusSubring (Localization.Away C.base.s) :=
      localizationLocSubringPlusSubring P C.base.T C.base.s
    letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
    ∀ (σ_loc : (Localization.Away C.base.s)ˣ) (f : A)
      (_h_alg : algebraMap A (Localization.Away C.base.s) f =
        (σ_loc : Localization.Away C.base.s) *
          (∏ t ∈ D.T.image
              (algebraMap A (Localization.Away C.base.s)), t))
      (_hσ_loc_dom :
        ∀ w ∈ Spa (Localization.Away C.base.s)
            (Localization.Away C.base.s)⁺,
          ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
            w.vle (σ_loc : Localization.Away C.base.s) τ ∧
              ¬ w.vle τ (σ_loc : Localization.Away C.base.s))
      (_h_struct : WedhornCoverPieceStructuralData P C.base.T
        C.base.s hopen_base D.T D.s σ_loc)
      (_hv_in_plus : v ∈ rationalOpen (insert f C.base.T) C.base.s)
      (_hvf_nz : ¬ v.vle f 0),
      WedhornC1PerCallSupplyCovPlusPieceLift P C hopen_base D v := by
  letI : TopologicalSpace (Localization.Away C.base.s) :=
    locTopology P C.base.T C.base.s hopen_base
  letI : PlusSubring (Localization.Away C.base.s) :=
    localizationLocSubringPlusSubring P C.base.T C.base.s
  letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
  intro σ_loc f h_alg hσ_loc_dom h_struct hv_in_plus hvf_nz
  refine ⟨f, ?_, hv_in_plus, hvf_nz⟩
  exact WedhornCoverPieceCovPlusPieceLiftPerTBound_via_structural_data
    P C.base.T C.base.s hopen_base C.base.T D.T D.s f σ_loc h_alg
    hσ_loc_dom h_struct

/-- **Top-level: `C1SupplierStrong_local C` via structural data**
(T044 final deliverable).

Caller theorem producing `C1SupplierStrong_local C` from a per-call
delivery of the natural σ-construction components: σ_loc, f, h_alg,
hσ_loc_dom, h_struct (T037 structural data), hv_in_plus, hvf_nz.

Composes
`WedhornC1PerCallSupplyCovPlusPieceLift_via_structural_data` with
T043's `C1SupplierStrong_local_via_cov_plus_piece_lift_supplier`.

This is the strongest compiling theorem-level discharge of T043's
source-restricted predicate from explicit σ-construction
hypotheses. The remaining honest mathematical content is
`WedhornCoverPieceStructuralData` itself (T037's source-restricted
Prop); discharging that Prop is the genuine residual of Wedhorn
8.34(ii) Step 2 at the C1 layer. -/
theorem C1SupplierStrong_local_via_cov_plus_piece_lift_via_structural_data
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
        WedhornCoverPieceStructuralData P C.base.T C.base.s
          hopen_base D.T D.s σ_loc ∧
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0) :
    C1SupplierStrong_local C := by
  letI : TopologicalSpace (Localization.Away C.base.s) :=
    locTopology P C.base.T C.base.s hopen_base
  letI : PlusSubring (Localization.Away C.base.s) :=
    localizationLocSubringPlusSubring P C.base.T C.base.s
  letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
  refine C1SupplierStrong_local_via_cov_plus_piece_lift_supplier
    P hA₀_le C hopen_base ?_
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_loc, f, h_alg, h_dom, h_struct, hv_in_plus, hvf_nz⟩ :=
    h_per_call_components D hD v hv t ht hvt hvD_s
  exact WedhornC1PerCallSupplyCovPlusPieceLift_via_structural_data
    P C hopen_base D v σ_loc f h_alg h_dom h_struct hv_in_plus hvf_nz

end ValuationSpectrum
