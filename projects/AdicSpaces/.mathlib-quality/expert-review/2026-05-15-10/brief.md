# Review brief — Tate acyclicity / IsSheafy (round 15: RatioTreeRealization)

*Prepared 2026-05-15 for ChatGPT Pro (continuing series, follow-up to round 14). Self-contained: no repo access required.*

*Compact follow-up to round 14. Reviewer found that independent existential `RatioNodeData` choices in `Refines` vs `allSplitsInducing` broke coherence. Round-15 fix: (1) added `cover_covers : cover.covers = {plus, minus}` field to `RatioNodeData` for exact-2-cover shape; (2) introduced indexed inductive `RatioTreeRealization t D` assigning coherent `RatioNodeData` to every `nodeRatio` so child subtrees see FIXED sub-bases; (3) `Refines` and `allSplitsInducing` are now defined on the realization, recursing coherently.*

---

## 1. What changed since round 14

| Object | Round-14 issue | Round-15 fix |
|---|---|---|
| `RatioNodeData` | Missing exact-2-cover shape | Added `cover_covers : cover.covers = {plus, minus}` field. |
| `Refines`/`allSplitsInducing` independent existentials | Coherence broken — same subtree could be interpreted over different sub-bases | Introduced `RatioTreeRealization t D` indexed inductive: a tree decorated with coherent `RatioNodeData` choices at every `nodeRatio`. Predicates now defined on the realization (NOT the bare tree). |
| W3-transport output | `∃ (t : RatioLaurentTree A), t.allSplitsInducing ∧ t.Refines` | `∃ (t : RatioLaurentTree A) (ρ : RatioTreeRealization t L), ρ.allSplitsInducing ∧ ρ.Refines C` |

## 2. Updated `RatioNodeData` (math + Lean)

**Round-15 addition**: exact 2-cover shape clause.

**Lean.**
```lean
structure RatioNodeData (D : RationalLocData A) (f g : A) where
  plus : RationalLocData A
  minus : RationalLocData A
  cover : RationalCovering A
  cover_base : cover.base = D
  cover_covers : cover.covers =
    letI : DecidableEq (RationalLocData A) := Classical.decEq _
    ({plus, minus} : Finset (RationalLocData A))
  plus_open_eq :
    rationalOpen plus.T plus.s =
      {v ∈ rationalOpen D.T D.s | v.vle f g}
  minus_open_eq :
    rationalOpen minus.T minus.s =
      {v ∈ rationalOpen D.T D.s | v.vle g f}
```

## 3. New `RatioTreeRealization` (math + Lean)

**Mathematical content.** *A `RatioTreeRealization t D` is the data needed to interpret the ratio-Laurent tree `t` at root `D` coherently. At each `nodeRatio f g`, it carries a specific `RatioNodeData D f g` (= the validity package); child realizations recurse on the fixed sub-bases `data.plus` and `data.minus`.*

**Lean.**
```lean
inductive RatioTreeRealization :
    RatioLaurentTree A → RationalLocData A → Type _
  | leaf (D : RationalLocData A) :
      RatioTreeRealization .leaf D
  | nodeLaurent {L R : RatioLaurentTree A}
      (D : RationalLocData A) (f : A)
      (ρL : RatioTreeRealization L (laurentPlusDatum D f))
      (ρR : RatioTreeRealization R (laurentMinusDatum D f)) :
      RatioTreeRealization (.nodeLaurent f L R) D
  | nodeRatio {L R : RatioLaurentTree A}
      (D : RationalLocData A) (f g : A)
      (data : RatioNodeData D f g)
      (ρL : RatioTreeRealization L data.plus)
      (ρR : RatioTreeRealization R data.minus) :
      RatioTreeRealization (.nodeRatio f g L R) D
```

The crucial coherence: in the `nodeRatio` constructor, the child realizations `ρL : RatioTreeRealization L data.plus` and `ρR : RatioTreeRealization R data.minus` ARE PARAMETERIZED BY the chosen `data`'s plus/minus. So the same `data` fixes the recursion.

## 4. Updated predicates (math + Lean)

### 4.1 `RatioTreeRealization.Refines`

```lean
def RatioTreeRealization.Refines : {t : RatioLaurentTree A} →
    {D : RationalLocData A} → RatioTreeRealization t D →
    RationalCovering A → Prop
  | _, _, .leaf D, C => ∃ E ∈ C.covers, rationalOpen D.T D.s ⊆ rationalOpen E.T E.s
  | _, _, .nodeLaurent _ _ ρL ρR, C => ρL.Refines C ∧ ρR.Refines C
  | _, _, .nodeRatio _ _ _ _ ρL ρR, C => ρL.Refines C ∧ ρR.Refines C
```

### 4.2 `RatioTreeRealization.allSplitsInducing`

```lean
def RatioTreeRealization.allSplitsInducing : {t : RatioLaurentTree A} →
    {D : RationalLocData A} → RatioTreeRealization t D → Prop
  | _, _, .leaf _ => True
  | _, _, .nodeLaurent D f ρL ρR =>
      Topology.IsInducing (productRestrictionSub A (laurentCovering D f)) ∧
      ρL.allSplitsInducing ∧ ρR.allSplitsInducing
  | _, _, .nodeRatio _ _ _ data ρL ρR =>
      Topology.IsInducing (productRestrictionSub A data.cover) ∧
      ρL.allSplitsInducing ∧ ρR.allSplitsInducing
```

Both predicates recurse on the SAME `ρL`/`ρR` (sharing whatever realization data was chosen). No independent existentials.

## 5. Updated W3-transport output

```lean
∃ (inner_abs : RatioLaurentTree A)
  (ρ : RatioTreeRealization inner_abs L),
  ρ.allSplitsInducing ∧ ρ.Refines C
```

The proof now needs to construct both the tree AND the realization (= the coherent choice of `RatioNodeData` at every `nodeRatio`).

## 6. Questions

**Q1.** Is `RatioTreeRealization` correctly designed as an indexed inductive? Specifically:
- `leaf D` provides a realization for a leaf at base `D`.
- `nodeLaurent D f ρL ρR` recurses with fixed sub-bases `laurentPlusDatum D f` and `laurentMinusDatum D f`.
- `nodeRatio D f g data ρL ρR` carries the `RatioNodeData` and recurses with fixed sub-bases `data.plus` and `data.minus`.

Is this the right indexed-inductive shape, or should it be a non-indexed structure with more bookkeeping?

**Q2.** Is the `cover_covers` field in `RatioNodeData` correctly formulated? It uses `Classical.decEq` for the Finset equality. Should it use a different formulation (e.g., `cover.covers ⊆ {plus, minus}` plus the two membership clauses)?

**Q3.** With the realization in place, **is the round-15 architecture now finally correct as a proof target**? Specifically: W3-transport outputs `∃ (inner_abs, ρ), ρ.Refines C ∧ ρ.allSplitsInducing`. Can the proof now construct the realization by recursing on `inner_rel`'s `IsRatioLaurentTreeFrom` structure + the relative-to-absolute transport theorem (which produces a `RatioNodeData L g h` instance for each ratio split `u_g · u_h⁻¹`)?

**Q4.** I.1's signature still outputs `LaurentTree A`. Should it now switch to `∃ (t : RatioLaurentTree A) (ρ : RatioTreeRealization t C.base), ρ.Refines C ∧ ρ.allSplitsInducing`? This is the cascade from the round-12 reviewer recommendation that I held back pending coherence verification.

## 7. Document metadata

- Project name: Tate acyclicity / IsSheafy (round 15 of the series)
- Brief generated: 2026-05-15
- Length: ~4 pages
- Build status: `lake build` clean; 8 sorries (W1, bridge1, bridge2, W2, W3, W3-transport, I.1 body, V.1).
