# Review brief — Tate acyclicity / IsSheafy (round 12: W3-transport switched to RatioLaurentTree A)

*Prepared 2026-05-15 for ChatGPT Pro (continuing series, follow-up to round 11). Self-contained: no repo access required.*

*Compact follow-up to round 11. Reviewer found that W3-transport's codomain `LaurentTree A` was mathematically wrong — ratio splits `v(g) ≤ v(h)` aren't ordinary Laurent splits relative to a current denominator. Reviewer offered three paths; **user chose Option 1**: use the project's existing pair-labelled `RatioLaurentTree A` (with constructors `leaf`, `nodeLaurent f`, `nodeRatio f g`). Round-12 fixes: added the missing `Refines` and `allSplitsInducing` predicates for `RatioLaurentTree A`, and switched W3-transport's output type.*

---

## 1. What changed since round 11

| Object | Round-11 issue | Round-12 fix |
|---|---|---|
| W3-transport's codomain | `LaurentTree A` — wrong, because ratio splits don't fit | Switched to `RatioLaurentTree A` (existing project type, pair-labelled, with `nodeRatio f g` constructor). |
| `RatioLaurentTree.Refines` | Not defined | Added recursive definition; `nodeRatio` case uses existential unit witnesses + project's `ratioPlusDatum`/`ratioMinusDatum`. |
| `RatioLaurentTree.allSplitsInducing` | Not defined | Added recursive definition; `nodeLaurent` uses `laurentCovering`, `nodeRatio` uses project's `ratioCovering` (also from I.3 era). |
| `isUnit_base_s_in_presheafValue_of_subset` | Bare set inclusion concern | Docstring revised to note that rational-containment/restriction-map data is preferred; signature kept for now pending audit of available restriction-map API. |

## 2. The new `RatioLaurentTree A` predicates (math + Lean)

### 2.1 `RatioLaurentTree.Refines`

**Mathematical content.** *A `RatioLaurentTree A` refines `C` at base `D₀` if every leaf is contained in some `C`-piece. Recursive: at `leaf` we require existence of `E ∈ C.covers` with `R(D₀) ⊆ R(E)`. At `nodeLaurent f`, both sub-trees refine `C` at the plus/minus laurent sub-bases. At `nodeRatio f g`, existential unit witnesses `f_inv, g_inv ∈ A₀` (with `f·f_inv = 1`, `g·g_inv = 1`) let us construct the ratio sub-bases via `ratioPlusDatum`/`ratioMinusDatum`, and both sub-trees refine `C` at those sub-bases.*

**Lean.**
```lean
def RatioLaurentTree.Refines :
    RatioLaurentTree A → RationalLocData A → RationalCovering A → Prop
  | .leaf, D₀, C => ∃ E ∈ C.covers, rationalOpen D₀.T D₀.s ⊆ rationalOpen E.T E.s
  | .nodeLaurent f L R, D₀, C =>
      L.Refines (laurentPlusDatum D₀ f) C ∧ R.Refines (laurentMinusDatum D₀ f) C
  | .nodeRatio f g L R, D₀, C =>
      ∃ (f_inv g_inv : A)
        (hf : f * f_inv = 1) (hg : g * g_inv = 1)
        (hf_inv : f_inv ∈ D₀.P.A₀) (hg_inv : g_inv ∈ D₀.P.A₀),
        L.Refines (ratioPlusDatum D₀ f g g_inv hg hg_inv) C ∧
        R.Refines (ratioMinusDatum D₀ f g f_inv hf hf_inv) C
```

### 2.2 `RatioLaurentTree.allSplitsInducing`

**Mathematical content.** *At every internal node, the diagonal 2-cover is inducing. At `nodeLaurent f`, this is the standard Laurent 2-cover (`laurentCovering`). At `nodeRatio f g`, this is the ratio 2-cover (`ratioCovering`, project-side). Recursive sub-trees also satisfy `allSplitsInducing`.*

**Lean.**
```lean
def RatioLaurentTree.allSplitsInducing :
    RatioLaurentTree A → RationalLocData A → Prop
  | .leaf, _ => True
  | .nodeLaurent f L R, D₀ =>
      L.allSplitsInducing (laurentPlusDatum D₀ f) ∧
      R.allSplitsInducing (laurentMinusDatum D₀ f) ∧
      Topology.IsInducing (productRestrictionSub A (laurentCovering D₀ f))
  | .nodeRatio f g L R, D₀ =>
      ∃ (f_inv g_inv : A)
        (hf : f * f_inv = 1) (hg : g * g_inv = 1)
        (hf_inv : f_inv ∈ D₀.P.A₀) (hg_inv : g_inv ∈ D₀.P.A₀),
        L.allSplitsInducing (ratioPlusDatum D₀ f g g_inv hg hg_inv) ∧
        R.allSplitsInducing (ratioMinusDatum D₀ f g f_inv hf hf_inv) ∧
        Topology.IsInducing
          (productRestrictionSub A (ratioCovering D₀ f g f_inv g_inv hf hf_inv hg hg_inv))
```

## 3. Updated W3-transport (round-12)

```lean
theorem relative_laurent_tree_to_absolute
    [project standing hypotheses on A]
    ... [all previous params: P, C, S, hS_contain, s, L, hL_subset, I_units,
        h_unit_generated, locSubring noeth, typeclasses on presheafValue L,
        h_unit_base, L_rel, h_L_rel_canonical, unitCover, h_unitCover,
        inner_rel, h_refines_rel, h_split_rel, h_ratio_tree] :
    -- Round-12: output type is RatioLaurentTree A (pair-labelled),
    -- with the new `Refines` and `allSplitsInducing` predicates.
    ∃ inner_abs : RatioLaurentTree A,
      inner_abs.allSplitsInducing L ∧
      inner_abs.Refines L C
```

## 4. Cascading consequence for I.1

Since W3-transport now outputs `RatioLaurentTree A` (not `LaurentTree A`), I.1's overall output type for the per-leaf inner trees changes too. This means:

- I.1's overall output type — currently `∃ t : LaurentTree A, ...` — may need to switch to `∃ t : RatioLaurentTree A, ...` after the graft.
- Downstream consumers (`isSheafyComplete` via `productRestrictionSub_isInducing_of_wedhorn_tree_existence`) expect `LaurentTree A`. Either they need updating, OR there's a separate "ratio-tree induction theorem" analogous to `productRestrictionSub_isInducing_via_tree`.

For now I.1's signature is unchanged (still `LaurentTree A`). The mismatch is documented in I.1's docstring as part of the round-12 pending refactor.

## 5. Questions

**Q1.** Is `RatioLaurentTree.Refines` correctly stated? Specifically, the `nodeRatio` case existentially quantifies the unit witnesses (`f_inv, g_inv ∈ A₀`); using these, `ratioPlusDatum`/`ratioMinusDatum` build the sub-bases. Is this the right Lean formulation, or should the unit witnesses be carried IN the tree (e.g., as additional fields of `nodeRatio`)?

**Q2.** Is `RatioLaurentTree.allSplitsInducing` correctly stated? The `nodeRatio` case asserts `IsInducing` for the `ratioCovering` 2-cover. Is the `ratioCovering`-as-2-cover the right object, or should it be something else (e.g., a different diagonal-restriction interpretation)?

**Q3.** With W3-transport now outputting `RatioLaurentTree A`, the cascade to I.1's signature is: I.1 should output `∃ t : RatioLaurentTree A, t.Refines C.base C ∧ t.allSplitsInducing C.base`. Does this make sense, or should there be a *ratio-graft* operation joining outer `LaurentTree A` with per-leaf `RatioLaurentTree A` inner trees?

**Q4.** Is the round-12 architecture now finally correct as a proof target for W1, W2, W3, W3-transport? After the `RatioLaurentTree A` switch, are there any remaining structural mismatches?

## 6. Document metadata

- Project name: Tate acyclicity / IsSheafy (round 12 of the series)
- Brief generated: 2026-05-15 (same day as rounds 6–11)
- Length: ~4 pages
- Build status: `lake build` clean; 8 sorries (W1, W2, W3, W3-transport, bridge1, bridge2, I.1 body, V.1).
- Round-11 reply integrated; this brief asks whether the `RatioLaurentTree A` switch + new predicates are correctly captured.
