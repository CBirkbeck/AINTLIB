# Inventory: ./HasseWeil/Pic0/RouteCAdditivity.lean

**File**: `HasseWeil/Pic0/RouteCAdditivity.lean`
**Lines**: 1–259
**Imports**: `HasseWeil.Pic0.PicDual`, `HasseWeil.AdditionPullback.Frobenius`
**Namespace**: `HasseWeil.Pic0.RouteCAdditivity`

**Summary**: This file provides a reduction chain for Silverman III.6.2(c) / III.8 (dual additivity for the Frobenius family `rπ − s`). It ships 6 theorems establishing the equivalence `htrace_dual ⟺ hpicval` and the abstract dual-additivity engine that reduces the III.8 trace relation to the single additivity residual `picDual α = picDual α₁ + picDual α₂`. No `sorry`, no `set_option maxHeartbeats`, no instances, no defs.

---

## Declarations

### `theorem smul_sub_add_smul_sub_eq`

- **Type**: `{π V : E.Point →+ E.Point} (r s t : ℤ) → (hsum : π + V = (mulByInt E t).toAddMonoidHom) → (r • π - s • AddMonoidHom.id _) + (r • V - s • AddMonoidHom.id _) = (mulByInt E (r * t - 2 * s)).toAddMonoidHom`
- **What**: Re-exports the candidate trace half: for abstract point endomorphisms `π, V` with `π + V = [t]`, the identity `(r·π − s·id) + (r·V − s·id) = [r·t − 2s]` holds purely by point-group algebra.
- **How**: One-line delegation to `HasseWeil.Isogeny.smul_sub_add_smul_sub_eq_mulByInt` from `PicDual.lean`.
- **Hypotheses**: Elliptic curve `E` over a field `F` with `DecidableEq`; abstract `AddMonoidHom` endomorphisms `π, V` satisfying the Frobenius trace relation.
- **Uses from project**: `HasseWeil.Isogeny.smul_sub_add_smul_sub_eq_mulByInt`
- **Used by**: `htrace_dual_of_picDual_eq` (line 161), `htrace_dual_iff_picDual_eq_rV_sub_s` (via `htrace_dual_of_picDual_eq`)
- **Visibility**: public
- **Lines**: 119–124; proof length: 1 line
- **Notes**: Pure re-export / renaming wrapper.

---

### `theorem picDual_eq_of_htrace_dual`

- **Type**: Given `α : Isogeny E E` with `CoordHom ch`, injectivity of `ch.toAlgHom`, finiteness; abstract `π, V : E.Point →+ E.Point`; integers `r s t`; hypotheses `hbeta : α.toAddMonoidHom = r • π - s • id`, `hsum : π + V = [t]`, `htrace_dual : α + α̂ = [r·t − 2s]`; concludes `α.picDual ch hinj hfin = r • V - s • id`
- **What**: Proves the forward direction of the equivalence: the Silverman III.8 trace relation for `α` of `rπ − s` shape implies the III.6.2(c) dual value `α̂ = r·V − s·id`.
- **How**: Delegates to `HasseWeil.Isogeny.picDual_eq_smul_sub_of_sum_trace` from `PicDual.lean`, which subtracts `α` from both sides and left-cancels using the candidate trace half.
- **Hypotheses**: Isogeny `α : Isogeny E E` with `CoordHom`, injectivity, finiteness; `rπ − s` shape; Frobenius trace relation; III.8 trace hypothesis.
- **Uses from project**: `HasseWeil.Isogeny.picDual_eq_smul_sub_of_sum_trace`
- **Used by**: `htrace_dual_iff_picDual_eq_rV_sub_s` (line 179)
- **Visibility**: public
- **Lines**: 133–142; proof length: 1 line
- **Notes**: Pure re-export wrapper for the ⟹ direction of the equivalence.

---

### `theorem htrace_dual_of_picDual_eq`

- **Type**: Given `α : Isogeny E E` with `CoordHom ch`, injectivity, finiteness; abstract `π, V`; integers `r s t`; `hbeta`, `hsum`, `hpicval : α.picDual ch hinj hfin = r • V - s • id`; concludes `α.toAddMonoidHom + α.picDual ch hinj hfin = (mulByInt E (r * t - 2 * s)).toAddMonoidHom`
- **What**: Proves the reverse direction: if the dual value is `α̂ = r·V − s·id`, then the III.8 trace relation holds.
- **How**: Rewrites `α.toAddMonoidHom` via `hbeta` and `α.picDual` via `hpicval`, then applies `smul_sub_add_smul_sub_eq` (the candidate half).
- **Hypotheses**: Isogeny with `CoordHom`, injectivity, finiteness; `rπ − s` shape; Frobenius trace relation; picDual value hypothesis.
- **Uses from project**: `smul_sub_add_smul_sub_eq` (local)
- **Used by**: `htrace_dual_iff_picDual_eq_rV_sub_s` (line 180), `htrace_dual_of_picDual_additive` (line 235)
- **Visibility**: public
- **Lines**: 151–161; proof length: 2 lines
- **Notes**: The key ⟸ direction; used twice within the file.

---

### `theorem htrace_dual_iff_picDual_eq_rV_sub_s`

- **Type**: Given `α : Isogeny E E` with `CoordHom ch`, injectivity, finiteness; abstract `π, V`; integers `r s t`; `hbeta`, `hsum`; produces `(α + α̂ = [r·t − 2s]) ↔ (α̂ = r·V − s·id)`
- **What**: Packages both directions as an `Iff`: the III.8 trace relation is equivalent to the III.6.2(c) dual value, for `α` of `rπ − s` shape with Frobenius trace relation. This is the algebraic backbone of Route-C Part (B) v3 — no degree, no uniqueness, no circularity with `deg(rπ − s) = N`.
- **How**: Packages `picDual_eq_of_htrace_dual` (⟹) and `htrace_dual_of_picDual_eq` (⟸) into an anonymous constructor `⟨..., ...⟩`.
- **Hypotheses**: Isogeny with `CoordHom`, injectivity, finiteness; `rπ − s` shape; Frobenius trace relation.
- **Uses from project**: `picDual_eq_of_htrace_dual` (local), `htrace_dual_of_picDual_eq` (local)
- **Used by**: unused in file (exported to consumers in other files)
- **Visibility**: public
- **Lines**: 170–180; proof length: 2 lines
- **Notes**: None of the long-proof or sorry flags apply. Unused within this file itself.

---

### `theorem htrace_dual_of_picDual_additive`

- **Type**: Given `α α₁ α₂ : Isogeny E E` each with `CoordHom`, injectivity, finiteness; abstract `π, V`; integers `r s t`; hypotheses `hbeta`, `hsum`, `hdual₁ : α₁.picDual = r • V`, `hdual₂ : α₂.picDual = -(s • id)`, `hadd : α.picDual = α₁.picDual + α₂.picDual`; concludes `α + α̂ = [r·t − 2s]`
- **What**: The abstract dual-additivity engine: given the single III.6.2(c) additivity hypothesis `hadd` and the two per-summand seeds `hdual₁`, `hdual₂`, derives the Silverman III.8 trace relation for `α`. This converts the III.8 residual into the cleanest possible form — pure pointwise additivity of `picDual`.
- **How**: Combines `hadd` with `hdual₁` and `hdual₂` (rewriting via `sub_eq_add_neg`) to obtain `hpicval : α.picDual = r • V - s • id`; then calls `htrace_dual_of_picDual_eq` to lift this to the III.8 trace relation.
- **Hypotheses**: Three isogenies with `CoordHom`, injectivity, finiteness; `rπ − s` shape for `α`; Frobenius trace; two per-summand seeds; the III.6.2(c) additivity residual.
- **Uses from project**: `htrace_dual_of_picDual_eq` (local)
- **Used by**: unused in file (exported; used in `RouteCTheoremOfSquare.lean` and `RouteCTheoremOfSquareDiv.lean`)
- **Visibility**: public
- **Lines**: 214–235; proof length: 5 lines
- **Notes**: The key public API export — the central engine. Proof is short but high-level impact.

---

### `theorem picDual_eq_rV_sub_s_of_additive`

- **Type**: Given `α α₁ α₂ : Isogeny E E` each with `CoordHom`, injectivity, finiteness; abstract `V`; integers `r s`; hypotheses `hdual₁ : α₁.picDual = r • V`, `hdual₂ : α₂.picDual = -(s • id)`, `hadd : α.picDual = α₁.picDual + α₂.picDual`; concludes `α.picDual = r • V - s • id`
- **What**: Variant of the dual-additivity engine delivering the III.6.2(c) dual value directly (rather than the III.8 trace), without needing `hbeta` or `hsum`. Useful when the caller wants the dual value rather than the trace relation.
- **How**: Rewrites `hadd` via `hdual₁` and `hdual₂`, then uses `sub_eq_add_neg` — a single `rw` step.
- **Hypotheses**: Three isogenies with `CoordHom`, injectivity, finiteness; two per-summand seeds; III.6.2(c) additivity residual.
- **Uses from project**: (none — pure point-group algebra via `rw`)
- **Used by**: unused in file (exported; used in `RouteCTheoremOfSquare.lean`)
- **Visibility**: public
- **Lines**: 243–257; proof length: 1 line
- **Notes**: Strictly weaker statement than `htrace_dual_of_picDual_additive` (gives value not trace); the two are equivalent by Phase 1. Unused within this file.

---

## Internal call graph (within file)

```
smul_sub_add_smul_sub_eq  ←  htrace_dual_of_picDual_eq
htrace_dual_of_picDual_eq  ←  htrace_dual_iff_picDual_eq_rV_sub_s
picDual_eq_of_htrace_dual  ←  htrace_dual_iff_picDual_eq_rV_sub_s
htrace_dual_of_picDual_eq  ←  htrace_dual_of_picDual_additive
```

## Key API (used by 2+ declarations in this file)

- `htrace_dual_of_picDual_eq` — used by `htrace_dual_iff_picDual_eq_rV_sub_s` and `htrace_dual_of_picDual_additive` (2 callers within file)
- `smul_sub_add_smul_sub_eq` — used by `htrace_dual_of_picDual_eq` (1 direct caller in file, but transitively by all)

## Declarations unused within this file (candidates for external API)

- `htrace_dual_iff_picDual_eq_rV_sub_s` — exported; used by `RouteCTheoremOfSquare.lean` (indirectly)
- `htrace_dual_of_picDual_additive` — exported; used by `RouteCTheoremOfSquare.lean` and `RouteCTheoremOfSquareDiv.lean`
- `picDual_eq_rV_sub_s_of_additive` — exported; used by `RouteCTheoremOfSquare.lean`
- `smul_sub_add_smul_sub_eq`, `picDual_eq_of_htrace_dual` — used only internally
