> **⛔ PARKED 2026-05-26 — fallback only.** The QF witness is committed to Route 1 (Pic⁰ /
> restricted dual additivity); see `expert-review/2026-05-26/integration.md` and
> `tickets/QF-PIC0-ROUTE.md`. The reviewer judged the explicit-coordinate route the wrong
> primary path (genuine, not tactical, obstructions). Retained for possible local-computation
> reuse only. Do not pursue as the primary QF route.

# `/develop --decompose` — Wall B y-side double-Vieta match (DRY-RUN GATE)

**Date**: 2026-05-25T22:45Z
**Target**: `genuine_dual_comp_pullback_y_gen_eq_mulByInt_y_decomp` at `HasseWeil/Hasse/L6Witnesses.lean:665-682` (and the x-side companion at line 645-662).

## Statement (verbatim from skeleton)

```lean
theorem genuine_dual_comp_pullback_y_gen_eq_mulByInt_y_decomp
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (V : Isogeny W.toAffine W.toAffine)
    (hV : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (β_dual : Isogeny W.toAffine W.toAffine)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _)) :
    (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK)).pullback (y_gen W) =
      mulByInt_y W
        ((Fintype.card K : ℤ) * r ^ 2 -
          isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)
```

(x-side analog at line 645 has the same shape with `y_gen` → `x_gen` and `mulByInt_y` → `mulByInt_x`.)

## Plain-English content (Silverman III.6.3 double-Vieta match)

Given:
- The genuine isogeny `β = rπ - s` (constructed via the π-side genuine chain in `genuineIsogSmulSub`, axiom-clean).
- A V dual to π satisfying `V·π = [q]`.
- The trace identity `π + V = [tr]`.
- A dual β-isogeny `β_dual = rV - s` at the toAddMonoidHom level.

Conclude: `(β_dual ∘ β).pullback x_gen = mulByInt_x W (qr² - tr·rs + s²)` (= the quadratic form value).

**This is the "double-Vieta match" — the multiplication β_dual · β equals [N] at the FULL Isogeny level (not just toAddMonoidHom), where N = qr² - tr·rs + s².**

## Decomposition tree

### Top-level: Wall B (x-side and y-side together)

**Composition**:
1. **β · β_dual = [N]** at AddMonoidHom level — from `h_sum_trace` + `h_beta_dual_hom` via algebra: (rπ-s)(rV-s) = r²(πV) - rs(π+V) + s² = r²q - rs·tr + s² = N.
2. **Pullback equality on x_gen** — `(β_dual ∘ β).pullback x_gen = mulByInt_x W N` (extracts the x-coord match).
3. **Pullback equality on y_gen** — `(β_dual ∘ β).pullback y_gen = mulByInt_y W N` (extracts the y-coord match).

The (2)+(3) are the explicit statements of Wall B's two halves.

### Sub-leaf W-B.1: AddMonoidHom-level β · β_dual = [N]

**Statement**: `(β_dual.comp β).toAddMonoidHom = mulByInt W.toAffine N .toAddMonoidHom`.

**Proof**:
- (β_dual ∘ β).toAddMonoidHom = β_dual.toAddMonoidHom ∘ β.toAddMonoidHom (`Isogeny.comp_toAddMonoidHom`)
- = (rV-s) ∘ (rπ-s) by `h_beta_dual_hom` and `genuineIsogSmulSub_toAddMonoidHom`
- Expand: (rV-s)(rπ-s) = r²Vπ - rs(V+π) + s² (algebra)
- = r²[q] - rs·[tr] + s² by `hV.1` (V·π = [deg π] = [q]) and `h_sum_trace`
- = [r²q - rs·tr + s²] = [N]
- Both sides as toAddMonoidHom = mulByInt N.toAddMonoidHom

**Required substrate**:
- `Isogeny.comp_toAddMonoidHom` — SHIPPED
- `genuineIsogSmulSub_toAddMonoidHom` — SHIPPED
- `hV.1` (V·π hom equality) — given
- AddMonoidHom algebra (commutativity of End(E), distributivity) — SHIPPED mathlib

**Attacks attempted**:
1. **Counterexample search**: search for cases where rV-s and rπ-s don't compose to [N] — none; this is Silverman III.6.3 algebra.
2. **Edge case**: r = 1, s = 0 → (V)(π) = [q]; matches.
3. **Discharge**: AddMonoidHom-level algebra is shipped. ✓

**Verdict**: ✓ DISPATCHABLE — pure AddMonoidHom algebra. ~30-50 LOC.

### Sub-leaf W-B.2: Pullback equality from AddMonoidHom equality (THE WALL)

**Statement**: given `α.toAddMonoidHom = β.toAddMonoidHom`, conclude `α.pullback (x_gen W) = β.pullback (x_gen W)`.

**This is the substantive substrate** — this is FALSE in general. Two Isogenies with the same toAddMonoidHom can have DIFFERENT pullbacks (this is the placeholder vs. genuine distinction).

**The actual fact we need**: for SPECIFIC α = β_dual ∘ β and β = mulByInt N, the pullbacks AGREE on x_gen (not just have the same value, but agree as elements of K(E)).

**Discharge route per docstring**: via `addIsog_pullback_eq_mulByInt_tr_pullback_of_xy_witnesses` (`OpenLemmaPrimitives.lean:1447`) — takes x and y identities AS INPUTS and concludes the AlgHom equality. So Wall B at this level reduces to:

**W-B.2a**: `addPullback_x_pair (frobeniusIsog W) V = mulByInt_x W tr` — the (π, V) sum at x.

**W-B.2b**: `addPullback_y_pair (frobeniusIsog W) V = mulByInt_y W tr` — the (π, V) sum at y.

These two facts ARE the substantive Wall B content (`addPullback_x_pair (π, V) = (mulByInt tr).pullback x_gen` and y-side analog).

**Required substrate**:
- `addPullback_x_pair_eq_mulByInt_x_of_sum_witness`: addPullback_x_pair α β = mulByInt_x (α+β as integer) IF the sum is a mulByInt. NOT shipped.
- Similar for y. NOT shipped.
- For (α, β) = (π, V) with α+β = [tr]: ad-hoc analysis using `π.pullback x_gen = x^q` + `V.pullback x_gen` analysis.

This is GENUINE SILVERMAN III.6.3 SUBSTRATE — the explicit formula for adding two isogenies' x-coordinates. ~200-400 LOC.

**Attacks attempted**:
1. **Counterexample**: in general, addPullback_x_pair ≠ (sum).pullback x_gen unless the sum is a specific isogeny like mulByInt. The substrate IS valid for the specific (π, V) case under the trace hypothesis.
2. **Edge case**: r = 1, s = 0 — gives just (π + V).pullback x = mulByInt_x tr. Still needs substrate.
3. **Discharge**: requires Silverman III.6.3 explicit formula. NOT shipped.
4. **Source-drift**: Silverman III.6.3 proves addition of isogenies at pullback level. Lean version matches.

**Verdict**: REJECTED for current infrastructure — needs ~200-400 LOC Silverman III.6.3 substrate.

### Sub-leaf W-B.3: Composition x-side

**Statement**: `(β_dual.comp β).pullback (x_gen W) = mulByInt_x W N`.

**Composition**: from W-B.2a (the (π, V) x-side) + composition rules: (β_dual ∘ β).pullback x_gen = β.pullback (β_dual.pullback x_gen) = ... → reduces to a chain involving (π, V) sum at x scaled by (r, s).

**Substrate**: ~100-200 LOC additional chain analysis once W-B.2a ships.

**Verdict**: ⏳ DISPATCHABLE PENDING W-B.2a.

### Sub-leaf W-B.4: Composition y-side

**Statement**: `(β_dual.comp β).pullback (y_gen W) = mulByInt_y W N`.

**Composition**: same as W-B.3 but for y. Uses `addPullback_y_pair` analog + composition.

**Substrate**: ~100-200 LOC additional.

**Verdict**: ⏳ DISPATCHABLE PENDING W-B.2b.

## Prior-B2 log consultation

`Read .mathlib-quality/b2_log.jsonl`:
- 5 entries: IV.4.3-P, traceOfFrobenius_sq_le, T-PFA-2, AUDIT-2a-E.6, AUDIT-D.2-pointCount_eq.
- **No match by name** for `genuine_dual_comp_pullback_{x,y}_gen_eq_mulByInt_{x,y}_decomp`.
- **No match by shape** — Wall B is about pullback equality from hom equality, no prior B2.
- Verdict: clean of prior B2 history.

## Categorized inputs (Attack 9 DRY-RUN GATE)

| # | Component | Status |
|---|-----------|--------|
| 1 | `Isogeny.comp_toAddMonoidHom` | **SHIPPED** ✓ |
| 2 | `genuineIsogSmulSub_toAddMonoidHom` | **SHIPPED** ✓ |
| 3 | AddMonoidHom-level algebra (V·π = [q], V+π = [tr]) | **SHIPPED** (given via h_sum_trace, hV.1) |
| 4 | `addIsog_pullback_eq_mulByInt_tr_pullback_of_xy_witnesses` (closer) | **SHIPPED axiom-clean** ✓ |
| 5 | **W-B.2a**: addPullback_x_pair (π, V) = mulByInt_x tr | **REJECTED** — needs Silverman III.6.3 explicit formula (~200-400 LOC) |
| 6 | **W-B.2b**: addPullback_y_pair (π, V) = mulByInt_y tr | **REJECTED** — same substrate |
| 7 | Composition chain (scalar mult of pullbacks) | **SHIPPED** (existing infra at SilvermanIV14, AdditionPullback) |

## Verdict

**REJECTED** — Wall B genuinely needs the W-B.2a/2b substrate, which is the Silverman III.6.3 explicit addition formula at the pullback level. This is ~200-400 LOC of new substrate.

**The user's memory note explicitly says**: "GAP-QF-DEGQF Wall B (Isogeny-level dual pullback, 'double-Vieta match'): IsDualOf β_dual β needs the PULLBACK equality (dual-additivity lemmas give only AddMonoidHom)."

This matches my decomposition: the AddMonoidHom-level β·β_dual = [N] is straightforward (W-B.1, ~50 LOC). The PULLBACK-level equality requires explicit (π, V) addition formula at coordinate level (W-B.2a/2b, substantial substrate).

**Alternative routes**:
- **W4-A (abstract dual-composition)**: instead of computing the (π, V) sum explicitly, use the dual-composition theorem `α̂ ∘ α = [deg α]` (Silverman III.6.1a) + dual additivity (III.6.2c). This bypasses W-B.2a/2b but requires its own substrate (III.6.2(c) additivity of dual).
- **W4-B (Weil pairing)**: use the determinant formula. Needs Weil pairing infrastructure.

Both alternatives are themselves substantive substrate.

**Sources**:
- Silverman III.6.3 (positive-definite QF on End(E))
- Silverman III.4 (addition formula explicit)

## Confidence gate

1. ✓ Sub-leaves identified (4 sub-leaves, 2 REJECTED for substrate, 2 DISPATCHABLE pending).
2. ⏳ Skeleton compiles (sorries at 662, 682).
3. ✓ Verbatim source quotes.
4. ✓ Attack categories: 5 per leaf, REJECTs caught at attack 5 (discharge).
5. ✓ Prior-B2 log: clean.
6. ✓ Structure mirrors Silverman III.6.3.

## Next step

Wall B is REJECTED for direct discharge — needs Silverman III.6.3 explicit formula substrate (~200-400 LOC). Alternative: use W4-A or W4-B routes (each with their own substrate cost).

Per /develop --decompose protocol: STOP. User decision on substrate development direction (Wall B direct vs W4-A dual-composition vs W4-B Weil pairing).
