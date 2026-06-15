# Review brief — Tate acyclicity / IsSheafy (round 16: architecture APPROVED, final refinements)

*Prepared 2026-05-15 for ChatGPT Pro (continuing series, follow-up to round 15). Self-contained: no repo access required.*

*The round-15 reviewer APPROVED the architecture as structurally sound — first positive assessment in the series. Two small Lean-facing refinements were requested: (1) make `RatioNodeData.cover` a derived def for definitional `cover.base = D` and `cover.covers = {plus, minus}`; (2) update I.1 to cascade to a realized ratio tree output. Both applied in round-16.*

---

## 1. What changed since round 15

| Object | Round-15 issue | Round-16 fix |
|---|---|---|
| `RatioNodeData.cover` as field with propositional equalities | Cast-heavy in NODE induction | Replaced with derived `RatioNodeData.cover : RationalCovering A` defined from `D`, `plus`, `minus`. The `cover.base = D` and `cover.covers = {plus, minus}` are now DEFINITIONAL. The `hsubset` and `hcover` proofs are constructed from the new data fields `plus_subset`, `minus_subset`, `cover_proof`. |
| I.1's signature | Still outputting bare `LaurentTree A` | Added new `exists_wedhorn_ratio_laurent_refinement_tree_realized` outputting `∃ (t : RatioLaurentTree A) (ρ : RatioTreeRealization t C.base), ρ.Refines C ∧ ρ.allSplitsInducing`. Kept legacy `exists_wedhorn_laurent_refinement_tree` for backward compat. |

## 2. Updated `RatioNodeData` (final structure)

**Lean.**
```lean
structure RatioNodeData (D : RationalLocData A) (f g : A) where
  plus : RationalLocData A
  minus : RationalLocData A
  plus_subset : rationalOpen plus.T plus.s ⊆ rationalOpen D.T D.s
  minus_subset : rationalOpen minus.T minus.s ⊆ rationalOpen D.T D.s
  cover_proof : ∀ v ∈ rationalOpen D.T D.s,
    v ∈ rationalOpen plus.T plus.s ∨ v ∈ rationalOpen minus.T minus.s
  plus_open_eq :
    rationalOpen plus.T plus.s =
      {v ∈ rationalOpen D.T D.s | v.vle f g}
  minus_open_eq :
    rationalOpen minus.T minus.s =
      {v ∈ rationalOpen D.T D.s | v.vle g f}

noncomputable def RatioNodeData.cover
    (data : RatioNodeData D f g) : RationalCovering A :=
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  { base := D
    covers := {data.plus, data.minus}
    hsubset := <built from data.plus_subset + data.minus_subset>
    hcover := <built from data.cover_proof> }
```

Both `data.cover.base` and `data.cover.covers` are now definitional (no `Eq.mp` / cast machinery needed downstream).

## 3. I.1 cascade

**New realized-output theorem (round-16):**
```lean
theorem exists_wedhorn_ratio_laurent_refinement_tree_realized
    [project standing hypotheses on A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) :
    ∃ (t : RatioLaurentTree A) (ρ : RatioTreeRealization t C.base),
      ρ.Refines C ∧ ρ.allSplitsInducing
```

The legacy `exists_wedhorn_laurent_refinement_tree` is kept for backward compat with `isSheafyComplete`. The downstream `productRestrictionSub_isInducing_of_wedhorn_tree_existence` in `EmbeddingTopo.lean` should be refactored to consume the realized ratio tree (per round-12 reviewer NODE-step refactor recommendation).

## 4. Full lemma chain (architecturally approved)

```
W1: exists_standard_cover_refining
  → standard cover S refining C

W2: exists_first_stage_laurent_tree_unit_generated
  → s : Aˣ, outer LaurentTree A t_outer with allSplitsInducing C.base
  → per-leaf restricted_standard_cover_generated_by_units(L, C, S, s, I_units)

W3: unitGeneratedCover_has_relative_ratioLaurentRefinement (per outer leaf L)
  → relative tree inner_rel : LaurentTree (presheafValue L)
  → IsRatioLaurentTreeFrom L C I_units h_unit_base inner_rel
  → inner_rel.Refines L_rel unitCover ∧ inner_rel.allSplitsInducing L_rel
  → where unitCover = IsUnitGeneratedCoverFrom witness, L_rel canonical

W3-transport: relative_laurent_tree_to_absolute
  → (inner_abs : RatioLaurentTree A) (ρ : RatioTreeRealization inner_abs L)
  → ρ.allSplitsInducing ∧ ρ.Refines C
  ⮕ Per ratio node `nodeRatio g h`, constructs a RatioNodeData L g h
    via the transport theorem: relative split at u_g · u_h⁻¹ over O(L)
    ↔ absolute R(L) ∩ {v(g) ≤ v(h)} (via plus_open_eq).

Bridge lemmas:
  - isUnit_relativeUnitGenerator_from_W2_unit: W2's unit → W3's u_f unit.
  - isUnit_base_s_in_presheafValue_of_subset: L ⊆ C.base → 
    IsUnit (L.canonicalMap C.base.s).

I.1 cascade: exists_wedhorn_ratio_laurent_refinement_tree_realized
  → compose W1 → W2 → W3 → W3-transport per outer leaf
  → graft outer Laurent tree with per-leaf realized ratio sub-trees
  → output the realized RatioLaurentTree A
```

## 5. Sorry inventory at round-16

| Sorry | Description | Status |
|---|---|---|
| W1 | Standard cover existence | open |
| `isUnit_relativeUnitGenerator_from_W2_unit` | Bridge lemma | open |
| `isUnit_base_s_in_presheafValue_of_subset` | Derived unit hypothesis | open |
| W2 | First-stage Laurent tree | open |
| W3 | Relative ratio Laurent refinement | open |
| W3-transport | Relative-to-absolute transport (realized) | open |
| Legacy I.1 (LaurentTree A output) | Backward compat for `isSheafyComplete` | open |
| New I.1 realized cascade | Composition of W1–W3-transport | open |
| V.1 | Stacks 00MA | external Mathlib gap |

## 6. Questions

**Q1.** Is the round-16 architecture now finalized as the proof target? With the derived `RatioNodeData.cover` and the realized I.1 cascade, are there any remaining structural concerns?

**Q2.** Is the `RatioNodeData.cover` derivation correct? Built from `data.plus_subset`, `data.minus_subset`, `data.cover_proof` to produce `hsubset` and `hcover` for the `RationalCovering A`. Specifically: `covers = {data.plus, data.minus}` uses `Classical.decEq` for the Finset.

**Q3.** Is keeping both `exists_wedhorn_laurent_refinement_tree` (legacy) and `exists_wedhorn_ratio_laurent_refinement_tree_realized` (new) a reasonable transitional state? Or should we delete the legacy one and immediately refactor `isSheafyComplete` to use the new one?

**Q4.** Are there any other refinements you'd recommend before proof work begins on the 8 open lemmas?

## 7. Document metadata

- Project name: Tate acyclicity / IsSheafy (round 16 of the series)
- Brief generated: 2026-05-15
- Length: ~5 pages
- Build status: `lake build` clean; 9 sorries (W1, bridge1, bridge2, W2, W3, W3-transport, legacy I.1, new I.1-realized, V.1).
- **Reviewer status**: round-15 APPROVED architecture; round-16 applies the two requested refinements.
