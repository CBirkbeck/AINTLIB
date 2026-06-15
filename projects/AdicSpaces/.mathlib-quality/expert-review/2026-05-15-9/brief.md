# Review brief — Tate acyclicity / IsSheafy (round 14: RatioNodeData validity package)

*Prepared 2026-05-15 for ChatGPT Pro (continuing series, follow-up to round 13). Self-contained: no repo access required.*

*Compact follow-up to round 13. Reviewer found that the unconditional `ratioPlusDatumDC`/`ratioMinusDatumDC`/`ratioCoveringDC` definitions weren't valid for arbitrary `f, g` — they need a nonvanishing/unit hypothesis that's true in Wedhorn's case but not in general. Round-14 fix: removed the unconditional definitions and introduced a `RatioNodeData D f g` structure as a **validity package** carrying the plus/minus pieces, the 2-cover, and the rational-open semantic equalities as proof fields.*

---

## 1. What changed since round 13

| Object | Round-13 issue | Round-14 fix |
|---|---|---|
| `ratioPlusDatumDC` / `ratioMinusDatumDC` / `ratioCoveringDC` | Unconditional definitions with sorry'd hopen/hsubset/hcover; not valid for arbitrary `f, g` | **Removed**. Replaced by the `RatioNodeData D f g` structure (a validity package). |
| `RatioLaurentTree.Refines` nodeRatio case | Used unconditional `ratioPlusDatumDC`/`ratioMinusDatumDC` | Existentially quantifies over `RatioNodeData D f g`. |
| `RatioLaurentTree.allSplitsInducing` nodeRatio case | Used unconditional `ratioCoveringDC` | Existentially quantifies over the SAME `RatioNodeData` package (coherent recursion). |

## 2. The `RatioNodeData` validity package (math + Lean)

**Mathematical content.** *A `RatioNodeData D f g` is the data needed to interpret a ratio split at `(f, g)` over base `D`. It carries: the plus piece (rational locality data whose rational open is `R(D) ∩ {v(f) ≤ v(g)}`), the minus piece (rational open `R(D) ∩ {v(g) ≤ v(f)}`), the 2-cover packaging these as a `RationalCovering A` with `D` as base, and the semantic equalities pinning down the plus/minus rational opens.*

**Lean.**
```lean
structure RatioNodeData (D : RationalLocData A) (f g : A) where
  plus : RationalLocData A
  minus : RationalLocData A
  cover : RationalCovering A
  cover_base : cover.base = D
  cover_plus_mem : plus ∈ cover.covers
  cover_minus_mem : minus ∈ cover.covers
  plus_open_eq :
    rationalOpen plus.T plus.s =
      {v ∈ rationalOpen D.T D.s | v.vle f g}
  minus_open_eq :
    rationalOpen minus.T minus.s =
      {v ∈ rationalOpen D.T D.s | v.vle g f}
```

Note: `RatioNodeData D f g` is constructible only when valid (e.g., when `f, g` correspond to units in `𝒪(D)` via the relative-to-absolute transport). The structure exposes the data and proof obligations together.

## 3. Updated `RatioLaurentTree A` predicates

### 3.1 `RatioLaurentTree.Refines` (round-14)

```lean
def RatioLaurentTree.Refines :
    RatioLaurentTree A → RationalLocData A → RationalCovering A → Prop
  | .leaf, D₀, C => ∃ E ∈ C.covers, rationalOpen D₀.T D₀.s ⊆ rationalOpen E.T E.s
  | .nodeLaurent f L R, D₀, C =>
      L.Refines (laurentPlusDatum D₀ f) C ∧ R.Refines (laurentMinusDatum D₀ f) C
  | .nodeRatio f g L R, D₀, C =>
      ∃ data : RatioNodeData D₀ f g,
        L.Refines data.plus C ∧ R.Refines data.minus C
```

### 3.2 `RatioLaurentTree.allSplitsInducing` (round-14)

```lean
def RatioLaurentTree.allSplitsInducing :
    RatioLaurentTree A → RationalLocData A → Prop
  | .leaf, _ => True
  | .nodeLaurent f L R, D₀ =>
      L.allSplitsInducing (laurentPlusDatum D₀ f) ∧
      R.allSplitsInducing (laurentMinusDatum D₀ f) ∧
      Topology.IsInducing (productRestrictionSub A (laurentCovering D₀ f))
  | .nodeRatio f g L R, D₀ =>
      ∃ data : RatioNodeData D₀ f g,
        L.allSplitsInducing data.plus ∧
        R.allSplitsInducing data.minus ∧
        Topology.IsInducing (productRestrictionSub A data.cover)
```

The existential quantification over `RatioNodeData D₀ f g` makes the validity a proof obligation at the consumer (W3-transport's proof must construct the instance).

## 4. Coherence note

Both `Refines` and `allSplitsInducing` quantify over `RatioNodeData D₀ f g` existentially. The reviewer noted that for the recursion to be coherent, the SAME package should be used for plus/minus sub-bases and the 2-cover at each node. With the structure approach:

- The package's `plus_open_eq` and `minus_open_eq` fields uniquely determine the plus/minus rational opens (up to RationalLocData representation).
- The package's `cover` carries both pieces explicitly via `cover_plus_mem` and `cover_minus_mem`.

So at a single node, choosing one `data : RatioNodeData D₀ f g` determines all the sub-bases used by both predicates. Coherence is maintained.

## 5. What remains pending

- **W3-transport**: still output `RatioLaurentTree A` (no longer `LaurentTree A`). The proof now needs to construct `RatioNodeData D f g` instances for each ratio node. This construction is the relative-to-absolute transport theorem the reviewer asked for.
- **I.1**: signature still outputs `LaurentTree A` (not yet switched to `RatioLaurentTree A`). Held pending reviewer confirmation of round-14.

## 6. Questions

**Q1.** Is the `RatioNodeData D f g` structure correctly designed? It carries:
- `plus`, `minus` as `RationalLocData A`,
- `cover` as `RationalCovering A` with explicit `cover_base`, `cover_plus_mem`, `cover_minus_mem`,
- `plus_open_eq`, `minus_open_eq` as rational-open semantic equalities.

Should it also carry a `cover.covers = {plus, minus}` clause (currently we have the two `_mem` clauses, but not the full equality)? Or a coverage clause `rationalOpen plus ∪ rationalOpen minus = rationalOpen D`?

**Q2.** Are the `RatioLaurentTree.Refines` and `RatioLaurentTree.allSplitsInducing` round-14 definitions correct? Specifically, the existential quantification over `RatioNodeData D f g` at `nodeRatio` — does this give the coherent recursion the reviewer requested?

**Q3.** The construction of `RatioNodeData D f g` is the responsibility of W3-transport's proof. The reviewer mentioned the "key transport theorem": relative Laurent split at `u_g · u_h⁻¹` ↔ absolute `R(L) ∩ {v(g) ≤ v(h)}`. Should this theorem be stated separately and consumed by W3-transport, or be embedded in W3-transport's proof?

**Q4.** **Is the round-14 architecture now finally correct as a proof target?** With `RatioNodeData` as the validity package, the `nodeRatio` semantics is decoupled from unconditional hopen proofs that don't hold in general.

## 7. Document metadata

- Project name: Tate acyclicity / IsSheafy (round 14 of the series)
- Brief generated: 2026-05-15
- Length: ~4 pages
- Build status: `lake build` clean; 8 sorries (W1, bridge1, bridge2, W2, W3, W3-transport, I.1 body, V.1) — *down from 12 in round 13 (the 4 unconditional hopen/hsubset/hcover sorries are now proof obligations in `RatioNodeData`)*.
