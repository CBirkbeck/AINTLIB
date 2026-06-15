# Review brief — Tate acyclicity / IsSheafy (round 11: IsRatioLaurentTreeFrom + bridge lemmas)

*Prepared 2026-05-15 for ChatGPT Pro (continuing series, follow-up to round 10). Self-contained: no repo access required.*

*Compact follow-up to round 10. The reviewer offered two paths (Option A: predicate; Option B: fold into one theorem) — user chose **Option A** (preserve relative-labels architecture). Round-11 fixes: added `IsRatioLaurentTreeFrom` predicate constraining inner_rel's labels to canonical ratios, added the W2↔W3 unit bridge lemma, and added the lemma deriving `h_unit_base` from `L ⊆ C.base`.*

---

## 1. What changed since round 10

| Object | Round-10 issue | Round-11 fix |
|---|---|---|
| W3-transport too strong | Arbitrary `inner_rel` need not have transportable labels | New predicate `IsRatioLaurentTreeFrom L C I_units h_unit_base inner_rel`: every split label is `u_g · u_h⁻¹` for some g, h ∈ I_units. W3 now also outputs this; W3-transport requires it. |
| W2's unit ≠ W3's unit | W2 proves `IsUnit (L.canonicalMap (s⁻¹·f))`; W3 needs `IsUnit (relativeUnitGenerator L C f) = IsUnit (f/C.base.s)` | New bridge lemma `isUnit_relativeUnitGenerator_from_W2_unit` |
| `h_unit_base` undischarged | I.1's composition couldn't provide `IsUnit (L.canonicalMap C.base.s)` automatically | New lemma `isUnit_base_s_in_presheafValue_of_subset` derives it from `L ⊆ C.base` |

## 2. New predicate and lemmas (math + Lean)

### 2.1 `IsRatioLaurentTreeFrom` — canonical ratio tree

**Mathematical content.** *A relative Laurent tree `inner_rel` is the canonical ratio-Laurent tree from `I_units` if every internal split label is `u_g · u_h⁻¹` for some `g, h ∈ I_units`, where each `u_f = relativeUnitGenerator L C f`. The leaf case is trivially satisfied (no labels).*

**Lean.**
```lean
def IsRatioLaurentTreeFrom
    (L : RationalLocData A) (C : RationalCovering A)
    (I_units : Finset A)
    [typeclasses on presheafValue L]
    (h_unit_base : IsUnit (L.canonicalMap C.base.s)) :
    LaurentTree (presheafValue L) → Prop
  | .leaf => True
  | .node label l r =>
    (∃ g ∈ I_units, ∃ h ∈ I_units,
      ∃ h_unit_uh : IsUnit (relativeUnitGenerator L C h h_unit_base),
        label = relativeUnitGenerator L C g h_unit_base *
          ((h_unit_uh.unit⁻¹ : (presheafValue L)ˣ) : presheafValue L)) ∧
    IsRatioLaurentTreeFrom L C I_units h_unit_base l ∧
    IsRatioLaurentTreeFrom L C I_units h_unit_base r
```

### 2.2 Bridge lemma — `isUnit_relativeUnitGenerator_from_W2_unit`

**Mathematical content.** *From W2's `IsUnit (L.canonicalMap (s⁻¹·f))`, derive W3's `IsUnit (relativeUnitGenerator L C f h_unit_base) = IsUnit (f/C.base.s)`. The bridge: $f / C.\mathrm{base}.s = (s^{-1} f) \cdot (s / C.\mathrm{base}.s)$, where the right factor is a product of units (`s : Aˣ` so `L.canonicalMap s` is a unit; `h_unit_base` gives `L.canonicalMap C.base.s` a unit).*

**Lean.**
```lean
theorem isUnit_relativeUnitGenerator_from_W2_unit
    (L : RationalLocData A) (C : RationalCovering A) (f : A)
    [typeclasses on presheafValue L]
    (s : Aˣ)
    (h_unit_base : IsUnit (L.canonicalMap C.base.s))
    (_h_unit_W2 : IsUnit (L.canonicalMap (((s⁻¹ : Aˣ) : A) * f))) :
    IsUnit (relativeUnitGenerator L C f h_unit_base)
```

### 2.3 Derived hypothesis — `isUnit_base_s_in_presheafValue_of_subset`

**Mathematical content.** *From `rationalOpen L.T L.s ⊆ rationalOpen C.base.T C.base.s`, derive `IsUnit (L.canonicalMap C.base.s)`. By definition of rational open, `C.base.s` is nonzero on every Spa point of `rationalOpen C.base`. The inclusion transfers this nonzeroness to all Spa points of `rationalOpen L`, which via the project's adic-Spa correspondence implies `L.canonicalMap C.base.s` is a unit in `presheafValue L`.*

**Lean.**
```lean
theorem isUnit_base_s_in_presheafValue_of_subset
    (L : RationalLocData A) (C : RationalCovering A)
    [typeclasses on presheafValue L]
    (_hL_subset : rationalOpen L.T L.s ⊆ rationalOpen C.base.T C.base.s) :
    IsUnit (L.canonicalMap C.base.s)
```

## 3. Updated W3 and W3-transport

### 3.1 W3 (round-11)

Output now has THREE conjuncts:
- `inner_rel.Refines L_rel unitCover`
- `inner_rel.allSplitsInducing L_rel`
- `IsRatioLaurentTreeFrom L C I_units h_unit_base inner_rel` ← NEW

### 3.2 W3-transport (round-11)

Takes an additional input:
- `_h_ratio_tree : IsRatioLaurentTreeFrom L C I_units h_unit_base inner_rel`

This ensures the tree's labels are A-originating ratios, which is what makes the descent to `LaurentTree A` actually possible.

## 4. The final architecture (round-11)

```
W1: standard cover S refining C
  ↓
W2: outer Laurent tree + restricted_standard_cover_generated_by_units
  ↓ [bridge: isUnit_relativeUnitGenerator_from_W2_unit + isUnit_base_s_in_presheafValue_of_subset]
  ↓
W3 (relative): inner_rel : LaurentTree (presheafValue L) with
  Refines L_rel unitCover ∧ allSplitsInducing L_rel ∧
  IsRatioLaurentTreeFrom L C I_units h_unit_base inner_rel
  ↓
W3-transport: inner_abs : LaurentTree A with
  allSplitsInducing L ∧ Refines L C
  (uses the IsRatioLaurentTreeFrom constraint to denominator-clear labels)
  ↓
Graft (per outer leaf L via Refines_graftAt + allSplitsInducing_graftAt)
  ↓
[Pending] NODE-step refactor of productRestrictionSub_isInducing_via_tree
  removes need for allNodesDisjoint
  ↓
I.1: ∃ t : LaurentTree A, Refines C.base C ∧ allSplitsInducing C.base
  (and then IsSheafy)
```

## 5. Questions

**Q1.** Is `IsRatioLaurentTreeFrom` correctly stated? Recursive definition: at each `node label l r`, require `∃ g h ∈ I_units, ∃ unit witness for u_h, label = u_g · u_h⁻¹`, and recursively for sub-trees. Does this capture "every label is a canonical ratio" precisely, or should we add an additional structural constraint (e.g., the relationship between the labels and the unitCover's pieces)?

**Q2.** Is the bridge lemma `isUnit_relativeUnitGenerator_from_W2_unit` correctly stated? The math is $f/C.\mathrm{base}.s = (s^{-1}f) \cdot (s/C.\mathrm{base}.s)$. The Lean statement takes `IsUnit (L.canonicalMap (s⁻¹·f))` + `s : Aˣ` + `h_unit_base : IsUnit (L.canonicalMap C.base.s)` and outputs `IsUnit (relativeUnitGenerator L C f h_unit_base)`. Is anything missing?

**Q3.** Is `isUnit_base_s_in_presheafValue_of_subset` provable as stated? The proof would use the adic-Spa correspondence: rational-open nonzeroness ⇒ algebraic unit in completion. Should we add a hypothesis like `[CompatiblePlusSubring A]` or other regularity assumptions?

**Q4.** **Is the round-11 architecture now finally correct as a proof target?** With the predicate, the bridge lemmas, and the explicit constraint on transportable labels, the W1 → W2 → W3 (with `IsRatioLaurentTreeFrom`) → W3-transport → graft chain should be sound. Any remaining structural issues?

## 6. Document metadata

- Project name: Tate acyclicity / IsSheafy (round 11 of the series)
- Brief generated: 2026-05-15 (same day as rounds 6–10)
- Length: ~5 pages
- Build status: `lake build` clean; 8 sorries (W1, bridge lemma 1, bridge lemma 2, W2, W3, W3-transport, I.1 body, V.1)
- Round-10 reply integrated; this brief asks whether round-10's transportability + bridge requirements are correctly captured.
