# Review brief — Tate acyclicity / IsSheafy (round 13: denominator-cleared ratio data)

*Prepared 2026-05-15 for ChatGPT Pro (continuing series, follow-up to round 12). Self-contained: no repo access required.*

*Compact follow-up to round 12. Reviewer found that `nodeRatio` was using global inverses `f_inv, g_inv ∈ A₀` — mathematically wrong, because Wedhorn's ratio units live in `𝒪(D)` not in `A`. Round-13 fix: deterministic **denominator-cleared** rational data — `ratioPlusDatumDC`/`ratioMinusDatumDC`/`ratioCoveringDC` — which represent the ratio sub-pieces without requiring global inverses. The predicates `RatioLaurentTree.Refines` and `.allSplitsInducing` now use these.*

---

## 1. What changed since round 12

| Object | Round-12 issue | Round-13 fix |
|---|---|---|
| `nodeRatio` in `Refines` | Required global inverses `f_inv, g_inv ∈ A₀` (mathematically wrong) | Replaced with deterministic `ratioPlusDatumDC D f g` and `ratioMinusDatumDC D f g`. No global inverses. |
| `nodeRatio` in `allSplitsInducing` | Same issue + uses project's `ratioCovering` (which needs global inverses) | Uses new `ratioCoveringDC D f g` (no global inverses). |
| Denominator-cleared rational data | Didn't exist | New definitions; hopen/hsubset/hcover proofs sorry'd (substantive but localized). |

## 2. New denominator-cleared ratio data (math + Lean)

### 2.1 `ratioPlusDatumDC D f g`

**Mathematical content.** *The rational locality datum representing $R(D.T/D.s) \cap \{v : v(f) \le v(g)\}$, constructed via denominator clearing without requiring global inverses for `f` or `g`. The denominator is `D.s · g` and the numerators include `D.s · f` (giving `v(f) ≤ v(g)` after canceling `D.s`) plus `t · g` for each `t ∈ D.T` (giving `v(t) ≤ v(D.s)` after canceling `g`).*

**Lean.**
```lean
noncomputable def ratioPlusDatumDC
    (D : RationalLocData A) (f g : A) : RationalLocData A where
  P := D.P
  T := insert (D.s * f) (D.T.image (fun t => t * g))
  s := D.s * g
  hopen := by sorry  -- round-13 hopen proof
```

### 2.2 `ratioMinusDatumDC D f g`

**Mathematical content.** *Symmetric: represents $R(D.T/D.s) \cap \{v : v(g) \le v(f)\}$.*

**Lean.**
```lean
noncomputable def ratioMinusDatumDC
    (D : RationalLocData A) (f g : A) : RationalLocData A where
  P := D.P
  T := insert (D.s * g) (D.T.image (fun t => t * f))
  s := D.s * f
  hopen := by sorry
```

### 2.3 `ratioCoveringDC D f g`

**Mathematical content.** *The 2-cover of `D` by `ratioPlusDatumDC` and `ratioMinusDatumDC`. Covers `D` by valuation trichotomy on `v(f)` vs `v(g)`.*

**Lean.**
```lean
noncomputable def ratioCoveringDC
    (D : RationalLocData A) (f g : A) : RationalCovering A :=
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  { base := D
    covers := {ratioPlusDatumDC D f g, ratioMinusDatumDC D f g}
    hsubset := by sorry
    hcover := by sorry }
```

## 3. Updated `RatioLaurentTree A` predicates

### 3.1 `RatioLaurentTree.Refines` (round-13)

```lean
def RatioLaurentTree.Refines :
    RatioLaurentTree A → RationalLocData A → RationalCovering A → Prop
  | .leaf, D₀, C => ∃ E ∈ C.covers, rationalOpen D₀.T D₀.s ⊆ rationalOpen E.T E.s
  | .nodeLaurent f L R, D₀, C =>
      L.Refines (laurentPlusDatum D₀ f) C ∧ R.Refines (laurentMinusDatum D₀ f) C
  | .nodeRatio f g L R, D₀, C =>
      L.Refines (ratioPlusDatumDC D₀ f g) C ∧
      R.Refines (ratioMinusDatumDC D₀ f g) C
```

Deterministic — no existential unit witnesses; the sub-bases are uniquely determined by `f, g, D₀`.

### 3.2 `RatioLaurentTree.allSplitsInducing` (round-13)

```lean
def RatioLaurentTree.allSplitsInducing :
    RatioLaurentTree A → RationalLocData A → Prop
  | .leaf, _ => True
  | .nodeLaurent f L R, D₀ =>
      L.allSplitsInducing (laurentPlusDatum D₀ f) ∧
      R.allSplitsInducing (laurentMinusDatum D₀ f) ∧
      Topology.IsInducing (productRestrictionSub A (laurentCovering D₀ f))
  | .nodeRatio f g L R, D₀ =>
      L.allSplitsInducing (ratioPlusDatumDC D₀ f g) ∧
      R.allSplitsInducing (ratioMinusDatumDC D₀ f g) ∧
      Topology.IsInducing (productRestrictionSub A (ratioCoveringDC D₀ f g))
```

## 4. Status of I.1's signature

I.1's output is currently `∃ t : LaurentTree A, ...` but the reviewer suggested it should be `RatioLaurentTree A` (with the outer first-stage tree embedded via `nodeLaurent`). This cascade hasn't been applied yet — held back pending reviewer confirmation that the round-13 `nodeRatio` semantics is finally right.

## 5. Questions

**Q1.** Are the round-13 denominator-cleared formulas correct?
- `ratioPlusDatumDC`: `T = insert (D.s * f) (D.T.image (·*g))`, `s = D.s * g`. Rational open = `R(D.T/D.s) ∩ {v(f) ≤ v(g)}`?
- `ratioMinusDatumDC`: symmetric.

If correct, the `hopen` proofs are non-trivial but localized lemmas. Is there a structural concern (e.g., the T might be missing necessary generators for `hopen` to hold)?

**Q2.** Is `ratioCoveringDC D f g` (the 2-cover by plus/minus DC pieces) the right 2-cover for `nodeRatio`'s `allSplitsInducing` clause? Specifically, do you expect the diagonal `productRestrictionSub A (ratioCoveringDC D f g)` to be inducing under the standing hypotheses, or are additional inducing-conditions needed?

**Q3.** Does the round-13 architecture correctly capture Wedhorn's ratio split as a deterministic A-level rational subset operation? The key transport claim — relative `R({u_g · u_h⁻¹}/1)` in `𝒪(L)` corresponds to absolute `ratioPlusDatumDC L g h` (rational open `R(L.T/L.s) ∩ {v(g) ≤ v(h)}`) — should now be cleanly stateable as a separate theorem during W3-transport's proof.

**Q4.** **Is the round-13 architecture now finally correct as a proof target?** Should I also switch I.1's signature to output `RatioLaurentTree A` (with outer Laurent embedded via `nodeLaurent`), or should that be a separate step?

## 6. Document metadata

- Project name: Tate acyclicity / IsSheafy (round 13 of the series)
- Brief generated: 2026-05-15
- Length: ~4 pages
- Build status: `lake build` clean; sorries: W1, bridge1, bridge2, ratioPlusDatumDC's hopen, ratioMinusDatumDC's hopen, ratioCoveringDC's hsubset, ratioCoveringDC's hcover, W2, W3, W3-transport, I.1 body, V.1.
