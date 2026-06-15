/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LaurentOverlap
import «Adic spaces».TopologyComparison

/-!
# Bivariate continuity of `example638Bivariate_evalHom` / `_forwardHom`

This module proves the **bivariate analog** of
`tateEvalPresheafHom_continuous_canonical` (TopologyComparison.lean:2430) for
the overlap-shaped Wedhorn Example 6.39 setup, then derives the
quotient-lift continuity for `example638Bivariate_forwardHom`.

For a complete strongly noetherian Tate ring `B`, a pair of definition
`P : PairOfDefinition B` with `IsNoetherianRing P.A₀`, and an element
`b ∈ B`, the bivariate evaluation hom
`example638Bivariate_evalHom B P b : TateAlgebra₂ B →+* presheafValue
(overlapDatum B P b)` is continuous for the canonical bivariate Tate
topology on `TateAlgebra₂ B`. The proof structurally mirrors the
univariate `tateEvalPresheafHom_continuous_canonical`:

* `V ∈ nhds 0` contains an open subgroup `W` (presheafValue is nonarch).
* The bivariate power range `{canonicalMap(b)^(n 0) · invS^(n 1)}` is
  bounded — product of two bounded power families
  (`canonicalMap_b_isPowerBounded_in_overlap` and
  `invS_isPowerBounded_in_overlap`).
* Standard nhds-of-0 boundedness gives `U ∈ nhds 0` with bivRange · U ⊆ W.
* `canonicalMap` is continuous, so for some `N`, image `P.I^N ⊆ canonicalMap⁻¹(U)`.
* For `h ∈ tateAlgNhd₂ P_B N`, all bivariate coefficients lie in image
  `P.I^N`, so each `evalTerm₂` lies in W.
* Partial sums of `evalTerm₂` stay in `W` (subgroup); they tend to
  `example638Bivariate_evalHom h` (summable); `W` is closed (open
  subgroup) — so the tsum lies in `W ⊆ V`.

The quotient consequence is then derived via
`QuotientRing.isOpenQuotientMap_mk.isQuotientMap.continuous_iff`, using
that `example638Bivariate_forwardHom = Ideal.Quotient.lift _
(example638Bivariate_evalHom B P b) _`.

## Main results

* `tateEvalPresheafHom_bivariate_continuous_canonical` — direct
  continuity of `example638Bivariate_evalHom` for the canonical
  bivariate Tate topology, no hypothesis-discharge required.
* `example638Bivariate_forwardHom_continuous_canonical` — quotient-lift
  consequence: the forward hom factored through
  `bivariateOverlapIdeal b` is continuous for the bivariate overlap
  quotient topology.

These eliminate the `hcont_forward_overlap` residual hypothesis
previously required in `LaneAReverseRoundTrip.lean`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition 6.18,
  Example 6.39.
-/

namespace ValuationSpectrum

open Filter Topology UniformSpace TateAlgebra

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- **Bivariate canonical-topology continuity of `example638Bivariate_evalHom`
(Wedhorn Prop 6.18 bivariate analog).**

Under the natural strongly-noetherian Tate setup on `B`, the bivariate
evaluation hom `example638Bivariate_evalHom B P b : TateAlgebra₂ B →+*
presheafValue (overlapDatum B P b)` (sending `X ↦ canonicalMap b` and
`Y ↦ invS`) is continuous for the canonical bivariate Tate topology
`instTopologicalSpaceTateAlgebra₂` on `TateAlgebra₂ B` (no
hypothesis-discharge required).

This is the bivariate analog of `tateEvalPresheafHom_continuous_canonical`
(TopologyComparison.lean:2430). The proof structurally mirrors the
univariate, using `(hb_canon.mul hb_invS).subset` to derive bivariate
boundedness, the bivariate basis `tateAlgBasis'₂.hasBasis_nhds_zero`,
the bivariate coefficient lemma `tateAlgNhd₂_coeff_mem`, and the
bivariate summable machinery `evalTerm₂_summable` over `Fin 2 →₀ ℕ`. -/
theorem tateEvalPresheafHom_bivariate_continuous_canonical
    (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [PlusSubring B] [IsHuberRing B] [HasLocLiftPowerBounded B]
    [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    @Continuous _ _ instTopologicalSpaceTateAlgebra₂
      (inferInstance : TopologicalSpace (presheafValue (overlapDatum B P b)))
      (example638Bivariate_evalHom B P b) := by
  set hb_canon := canonicalMap_b_isPowerBounded_in_overlap B P b
  set hb_invS := invS_isPowerBounded_in_overlap B P b
  set D := overlapDatum B P b
  set f_canon := D.canonicalMap b
  set f_invS := invS D
  letI τ : TopologicalSpace ↥(TateAlgebra₂ B) := instTopologicalSpaceTateAlgebra₂
  -- Reduce to continuity at 0.
  apply continuous_of_continuousAt_zero (example638Bivariate_evalHom B P b).toAddMonoidHom
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro V hV
  -- Step 1: extract open additive subgroup W ⊆ V (presheafValue D is nonarch).
  obtain ⟨W, hWV⟩ := NonarchimedeanRing.is_nonarchimedean V hV
  have hW_open : IsOpen (W : Set (presheafValue D)) := W.isOpen
  have hW_closed : IsClosed (W : Set (presheafValue D)) :=
    AddSubgroup.isClosed_of_isOpen W.toAddSubgroup hW_open
  have hW_nhds : (W : Set (presheafValue D)) ∈ @nhds (presheafValue D) _ 0 :=
    hW_open.mem_nhds W.toAddSubgroup.zero_mem
  -- Step 2: bivariate range bounded; get U ∈ nhds 0 with bivRange · U ⊆ W.
  have hbiv_bdd : TopologicalRing.IsBounded
      (Set.range (fun n : Fin 2 →₀ ℕ => f_canon ^ (n 0) * f_invS ^ (n 1))) :=
    (hb_canon.mul hb_invS).subset (by
      rintro _ ⟨n, rfl⟩
      exact Set.mul_mem_mul ⟨n 0, rfl⟩ ⟨n 1, rfl⟩)
  obtain ⟨U, hU, hUW⟩ := hbiv_bdd (W : Set (presheafValue D)) hW_nhds
  -- Step 3: continuity of canonicalMap at 0.
  have hcmU : D.canonicalMap ⁻¹' U ∈ @nhds B _ 0 :=
    (canonicalMap_continuous D).continuousAt.preimage_mem_nhds
      (by rw [map_zero]; exact hU)
  -- Step 4: Extract N with image(P_B.I^N) ⊆ canonicalMap⁻¹(U).
  let P_B := (IsTateRing.principalPair B).toPairOfDefinition
  obtain ⟨N, -, hN⟩ := P_B.hasBasis_nhds_zero.mem_iff.mp hcmU
  -- Bivariate canonical basis at 0.
  have hbasis : ((@nhds _ τ (0 : ↥(TateAlgebra₂ B))).HasBasis
      (fun _ : ℕ => True) fun n =>
        (TateAlgebra.tateAlgNhd₂ P_B n : Set ↥(TateAlgebra₂ B))) :=
    TateAlgebra.tateAlgBasis'₂.hasBasis_nhds_zero
  apply hbasis.mem_iff.mpr
  refine ⟨N, trivial, fun h hh => ?_⟩
  change example638Bivariate_evalHom B P b h ∈ V
  refine hWV ?_
  -- Each bivariate evalTerm₂ lies in W.
  have hterm_mem : ∀ n : Fin 2 →₀ ℕ,
      TateAlgebraWedhorn.evalTerm₂ D.canonicalMap f_canon f_invS h n ∈
        (W : Set (presheafValue D)) := by
    intro n
    -- evalTerm₂ = canonicalMap(coeff_n h) * (f_canon^(n 0) * f_invS^(n 1)).
    change D.canonicalMap (MvPowerSeries.coeff n h.val) *
      (f_canon ^ (n 0) * f_invS ^ (n 1)) ∈ (W : Set (presheafValue D))
    rw [mul_comm]
    apply hUW
    refine ⟨f_canon ^ (n 0) * f_invS ^ (n 1), ⟨n, rfl⟩,
      D.canonicalMap (MvPowerSeries.coeff n h.val), ?_, rfl⟩
    apply hN
    -- coeff_n h ∈ image P_B.I^N via tateAlgNhd₂_coeff_mem.
    obtain ⟨b', hbI, hbeq⟩ := TateAlgebra.tateAlgNhd₂_coeff_mem P_B N hh n
    rw [← hbeq]
    exact ⟨b', hbI, rfl⟩
  -- evalTerm₂ is summable; HasSum gives the tsum equals our hom value.
  have hsum : Summable
      (TateAlgebraWedhorn.evalTerm₂ D.canonicalMap f_canon f_invS h) :=
    TateAlgebraWedhorn.evalTerm₂_summable D.canonicalMap
      (canonicalMap_continuous D) f_canon f_invS hb_canon hb_invS h
  have hhs : HasSum (TateAlgebraWedhorn.evalTerm₂ D.canonicalMap f_canon f_invS h)
      (example638Bivariate_evalHom B P b h) := by
    change HasSum _ (∑' n, TateAlgebraWedhorn.evalTerm₂ D.canonicalMap f_canon f_invS h n)
    exact hsum.hasSum
  -- W is closed; HasSum is Tendsto on Finset(Fin 2 →₀ ℕ); each partial sum is in W.
  refine hW_closed.mem_of_tendsto hhs ?_
  refine Filter.Eventually.of_forall fun s => ?_
  exact W.toAddSubgroup.sum_mem (fun k _ => hterm_mem k)

/-- **Bivariate canonical-topology continuity of `example638Bivariate_forwardHom`
(Wedhorn Prop 6.18 + Example 6.39 quotient-lift).**

Descends from `tateEvalPresheafHom_bivariate_continuous_canonical` via the
ring-quotient map `mk : TateAlgebra₂ B →+* TateAlgebra₂ B ⧸
bivariateOverlapIdeal b`, which is an open quotient map (topological ring
quotient). The canonical quotient topology
`quotientBivariateOverlapIdealTopology b` is the coinduced topology via
`mk`, so `IsQuotientMap.continuous_iff` transports continuity.

This eliminates the `hcont_forward_overlap` hypothesis previously required
by `example638Bivariate_equiv` (Wedhorn Example 6.39 / Step A) and by
`laneA_τ_preBiv` (LaneAReverseRoundTrip.lean). -/
theorem example638Bivariate_forwardHom_continuous_canonical
    (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [PlusSubring B] [IsHuberRing B] [HasLocLiftPowerBounded B]
    [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    @Continuous _ _
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (inferInstance : TopologicalSpace (presheafValue (overlapDatum B P b)))
      (example638Bivariate_forwardHom B P b) := by
  letI τ : TopologicalSpace ↥(TateAlgebra₂ B) := instTopologicalSpaceTateAlgebra₂
  letI τQ : TopologicalSpace (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology b
  haveI hTR : IsTopologicalRing ↥(TateAlgebra₂ B) := instIsTopologicalRingTateAlgebra₂
  have hmk_qm : Topology.IsQuotientMap
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b) :
        ↥(TateAlgebra₂ B) → ↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    (@QuotientRing.isOpenQuotientMap_mk ↥(TateAlgebra₂ B) τ
      (inferInstanceAs (CommRing ↥(TateAlgebra₂ B)))
      (TateAlgebra.bivariateOverlapIdeal b) hTR).isQuotientMap
  refine hmk_qm.continuous_iff.mpr ?_
  change Continuous (example638Bivariate_evalHom B P b)
  exact tateEvalPresheafHom_bivariate_continuous_canonical B P b

end ValuationSpectrum
