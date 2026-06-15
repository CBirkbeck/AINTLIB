# Inventory: ./HasseWeil/Valuation.lean

**File purpose**: Proves that the local ring of a Weierstrass elliptic curve at a nonsingular affine point is a discrete valuation ring (DVR), following Silverman I.1.7, II.1.1.

**Imports**: `HasseWeil.Isogeny`, `Mathlib.RingTheory.DiscreteValuationRing.TFAE`, `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Mathlib.Algebra.Polynomial.Div`

**Total declarations**: 11 (2 private, 9 public)

---

## Private / local declarations

### `private theorem eval_poly_deriv_eq_polynomialX_eval`
- **Type**: `(W : Affine F) (y₀ : F) : (W.polynomial.eval (C y₀)).derivative = W.polynomialX.eval (C y₀)`
- **What**: The derivative of the Weierstrass polynomial W(X, y₀) with respect to X equals the partial derivative ∂W/∂X evaluated at y₀; i.e., inner eval commutes with X-derivative.
- **How**: Fully unfolds `Affine.polynomial` and `Affine.polynomialX` and closes by `ring_nf`/`simp`.
- **Hypotheses**: None beyond the field and the curve.
- **Uses from project**: `Affine.polynomial`, `Affine.polynomialX` (definitions from mathlib WeierstrassCurve)
- **Used by**: `quot_evalEval_eq_polynomialY`, `mk_C_g_not_mem`, `localRing_isDVR`
- **Visibility**: private
- **Lines**: 27–34, proof ~7 lines
- **Notes**: None.

---

### `private theorem mem_of_mul_unit`
- **Type**: `[CommRing R] {I : Ideal R} {a b : R} (hmul : a * b ∈ I) (hb : IsUnit b) : a ∈ I`
- **What**: If `a * b ∈ I` and `b` is a unit, then `a ∈ I`; cancellation of units in ideals.
- **How**: Destructs the unit `b = u`, uses `I.mul_mem_right u⁻¹` and `mul_assoc`.
- **Hypotheses**: Commutative ring, `b` is a unit.
- **Uses from project**: None.
- **Used by**: `localRing_isDVR`
- **Visibility**: private
- **Lines**: 226–228, proof 2 lines
- **Notes**: Likely provable by a short mathlib lemma (e.g., `Ideal.mem_of_mul_unit` or similar); suspected mild duplication.

---

### `private theorem map_mem_span_sing`
- **Type**: `(f : R →+* S) {a x : R} (hmem : x ∈ span ({a} : Set R)) : f x ∈ span ({f a} : Set S)`
- **What**: Ring homomorphisms preserve membership in principal (singleton-generated) ideals.
- **How**: Rewrites via `mem_span_singleton`, extracts the scalar `c`, and maps through `f` using `map_mul`.
- **Hypotheses**: None beyond the ring hom.
- **Uses from project**: None.
- **Used by**: `localRing_isDVR`
- **Visibility**: private
- **Lines**: 230–233, proof 3 lines
- **Notes**: Standard mathlib-style lemma; may duplicate `Ideal.map_span` reasoning.

---

## Public declarations

### `noncomputable def pointIdeal`
- **Type**: `(x : F) (y : F) : Ideal W.CoordinateRing`
- **What**: The ideal of the coordinate ring of `W` corresponding to the affine point `(x, y)`, defined as `XYIdeal W x (C y)`.
- **How**: Direct alias for `Affine.CoordinateRing.XYIdeal`.
- **Hypotheses**: None.
- **Uses from project**: `Affine.CoordinateRing.XYIdeal` (mathlib)
- **Used by**: `pointIdeal_isMaximal`, `localRing_isDVR`
- **Visibility**: public
- **Lines**: 40–41
- **Notes**: Thin wrapper; no separate proof body.

---

### `theorem pointIdeal_isMaximal`
- **Type**: `{x y : F} (h : W.Nonsingular x y) : (pointIdeal W x y).IsMaximal`
- **What**: The point ideal at a nonsingular point is a maximal ideal; equivalently the residue field is `F`.
- **How**: Uses `Ideal.Quotient.maximal_of_isField` together with `Affine.CoordinateRing.quotientXYIdealEquiv` (which shows the quotient is isomorphic to `F`) transported via `RingEquiv.isField`.
- **Hypotheses**: `(x, y)` is a nonsingular point on `W`.
- **Uses from project**: `pointIdeal`, `Affine.CoordinateRing.quotientXYIdealEquiv` (mathlib)
- **Used by**: `localRing_isDVR`
- **Visibility**: public
- **Lines**: 43–46, proof 2 lines
- **Notes**: None.

---

### `theorem yclass_mul_quot_in_xclass_span`
- **Type**: `{x₀ y₀ : F} (h : W.Equation x₀ y₀) : YClass W (C y₀) * mk W (W.polynomial /ₘ (Y - C (C y₀))) ∈ span {XClass W x₀}`
- **What**: The product `YClass · Q ∈ ⟨XClass⟩` where `Q = W.polynomial /ₘ (Y − C y₀)` is the Y-quotient; a key algebraic fact used to show `YClass` is in the span of `XClass` modulo a unit.
- **How**: Uses `modByMonic_X_sub_C_eq_C_eval` and `modByMonic_add_div` to get the polynomial identity `W = (Y−y₀)·Q + C(W.eval y₀)`, maps it to the coordinate ring, then factors `mk(C(W.eval y₀))` as `XClass · mk(C g)` using `dvd_iff_isRoot`.
- **Hypotheses**: `(x₀, y₀)` lies on `W` (i.e., `W.Equation x₀ y₀`).
- **Uses from project**: `Affine.CoordinateRing.XClass`, `Affine.CoordinateRing.YClass`, `Affine.CoordinateRing.mk`
- **Used by**: `localRing_isDVR`
- **Visibility**: public
- **Lines**: 51–71, proof ~20 lines
- **Notes**: `set_option maxHeartbeats 800000` at line 51 — comment says "Type class synthesis in CoordinateRing is expensive." Proof is ~20 lines, below 30-line threshold.

---

### `theorem quot_evalEval_eq_polynomialY`
- **Type**: `{x₀ y₀ : F} (h : W.Equation x₀ y₀) : evalEval x₀ y₀ (W.polynomial /ₘ (Y - C (C y₀))) = evalEval x₀ y₀ W.polynomialY`
- **What**: The Y-quotient `Q` evaluates to `polynomialY(x₀, y₀)` at the point; the key identity identifying the quotient's evaluation as the partial Y-derivative.
- **How**: Takes the derivative of the division identity `W = (Y−y₀)·Q + C(W.eval y₀)`, uses `eval_poly_deriv_eq_polynomialX_eval` (but for the Y-derivative via `Affine.polynomial.derivative = polynomialY`), then evaluates at `(x₀, y₀)` noting `(Y−y₀)` vanishes.
- **Hypotheses**: `(x₀, y₀)` lies on `W`.
- **Uses from project**: `Affine.polynomialY` (mathlib); indirectly calls `eval_poly_deriv_eq_polynomialX_eval` logic (not that private lemma directly, but the same `polynomial.derivative = polynomialY` fact).
- **Used by**: `mk_quot_not_mem`
- **Visibility**: public
- **Lines**: 75–97, proof ~22 lines
- **Notes**: `set_option maxHeartbeats 800000` at line 75 — NO separate comment (the earlier comment at line 50 about CoordinateRing synthesis is for the block, but the option is repeated here without inline comment). Proof is ~22 lines.

---

### `theorem mk_quot_not_mem`
- **Type**: `{x₀ y₀ : F} (h : W.Equation x₀ y₀) (hY : W.polynomialY.evalEval x₀ y₀ ≠ 0) : mk W (W.polynomial /ₘ (Y - C (C y₀))) ∉ XYIdeal W x₀ (C y₀)`
- **What**: `mk(Q)` is not in the point ideal when the partial Y-derivative is nonzero at `(x₀, y₀)`; implies `mk(Q)` maps to a unit in the localization.
- **How**: Shows `XYIdeal ≤ ker(evalEval)` by checking that both generators `XClass` and `YClass` vanish under `evalEval`, then derives `evalEval(mk(Q)) = polynomialY(x₀, y₀) ≠ 0` via `quot_evalEval_eq_polynomialY`, yielding a contradiction.
- **Hypotheses**: `(x₀, y₀)` lies on `W`; `polynomialY.evalEval x₀ y₀ ≠ 0`.
- **Uses from project**: `quot_evalEval_eq_polynomialY`, `AdjoinRoot.evalEval_mk`, `Affine.CoordinateRing.XYIdeal`, `Affine.CoordinateRing.XClass`, `Affine.CoordinateRing.YClass`
- **Used by**: `localRing_isDVR`
- **Visibility**: public
- **Lines**: 101–126, proof ~25 lines
- **Notes**: None.

---

### `theorem xclass_mul_C_g_in_yclass_span`
- **Type**: `{x₀ y₀ : F} (h : W.Equation x₀ y₀) : XClass W x₀ * mk W (C (W.polynomial.eval (C y₀) /ₘ (X - C x₀))) ∈ span {YClass W (C y₀)}`
- **What**: The X-side analog of `yclass_mul_quot_in_xclass_span`: `XClass · mk(C g) ∈ ⟨YClass⟩` where `g = W(X, y₀) /ₘ (X − x₀)` is the inner X-quotient.
- **How**: Uses the inner X-factorization `W(X,y₀) = (X−x₀)·g` (from `modByMonic_X_sub_C_eq_C_eval` and `h`), combines with the Y-division identity to get `mk(C(X−x₀))·mk(Cg) = −(YClass·mk(Q))`, which lies in `span{YClass}`.
- **Hypotheses**: `(x₀, y₀)` lies on `W`.
- **Uses from project**: `Affine.CoordinateRing.XClass`, `Affine.CoordinateRing.YClass`, `Affine.CoordinateRing.mk`
- **Used by**: `localRing_isDVR` (the polynomialX-nonzero branch inlines equivalent logic rather than calling this; the standalone version is defined for reuse/symmetry but the main proof inlines)
- **Visibility**: public
- **Lines**: 140–175, proof ~35 lines
- **Notes**: `set_option maxHeartbeats 800000` at line 140 — NO inline comment (header comment at line 128 explains the X/Y symmetry). **Proof is >30 lines (~35 lines)**. The `localRing_isDVR` proof inlines essentially the same calculation in its X-branch rather than calling this lemma — suspected dead code within the file (unused in file).

---

### `theorem mk_C_g_not_mem`
- **Type**: `{x₀ y₀ : F} (h : W.Equation x₀ y₀) (hX : W.polynomialX.evalEval x₀ y₀ ≠ 0) : mk W (C (W.polynomial.eval (C y₀) /ₘ (X - C x₀))) ∉ XYIdeal W x₀ (C y₀)`
- **What**: The X-side analog of `mk_quot_not_mem`: `mk(C g)` is not in the point ideal when the partial X-derivative is nonzero.
- **How**: Same strategy as `mk_quot_not_mem`: shows `XYIdeal ≤ ker(evalEval)`, evaluates `mk(Cg)` via derivative computation (`eval_poly_deriv_eq_polynomialX_eval`), and derives a contradiction from `hX`.
- **Hypotheses**: `(x₀, y₀)` lies on `W`; `polynomialX.evalEval x₀ y₀ ≠ 0`.
- **Uses from project**: `eval_poly_deriv_eq_polynomialX_eval`, `AdjoinRoot.evalEval_mk`, `Affine.CoordinateRing.XYIdeal`, `Affine.CoordinateRing.XClass`, `Affine.CoordinateRing.YClass`
- **Used by**: `localRing_isDVR` (the X-branch inlines essentially the same argument — this standalone lemma appears unused within the file)
- **Visibility**: public
- **Lines**: 177–222, proof ~45 lines
- **Notes**: `set_option maxHeartbeats 800000` at line 177 — NO inline comment. **Proof is >30 lines (~45 lines)**. The `localRing_isDVR` X-branch inlines substantially the same proof — `mk_C_g_not_mem` appears to be unused within this file (dead code candidate within file; may be used by other files or kept for clarity/symmetry with the Y-side).

---

### `theorem localRing_isDVR`
- **Type**: `{x₀ y₀ : F} (h : W.Nonsingular x₀ y₀) : IsDiscreteValuationRing (Localization.AtPrime (pointIdeal W x₀ y₀))`
- **What**: The main result: the local ring of the Weierstrass curve at a nonsingular affine point is a DVR. Equivalently, the maximal ideal of the localization is principal and nonzero.
- **How**: Splits on the two branches of `Nonsingular` (polynomialX ≠ 0 or polynomialY ≠ 0). In each branch: (1) shows the maximal ideal equals a principal ideal `span{f(XClass)}` or `span{f(YClass)}` by showing the other generator is in that span modulo a unit (using `yclass_mul_quot_in_xclass_span`/`mk_quot_not_mem` for the Y-branch; analogous inline logic for X-branch); (2) uses `IsLocalization.map_units` to recognize the quotient element as a unit; (3) applies `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain` (the DVR TFAE from `Mathlib.RingTheory.DiscreteValuationRing.TFAE`) to pass from `IsPrincipalIdealRing` to `IsDiscreteValuationRing`; (4) shows the maximal ideal is nonzero via injectivity of localization and `XClass_ne_zero`.
- **Hypotheses**: `(x₀, y₀)` is a nonsingular point on `W` over a field `F`.
- **Uses from project**: `pointIdeal`, `pointIdeal_isMaximal`, `yclass_mul_quot_in_xclass_span`, `mk_quot_not_mem`, `mem_of_mul_unit`, `map_mem_span_sing`, `eval_poly_deriv_eq_polynomialX_eval`; from mathlib: `Affine.CoordinateRing.XClass_ne_zero`, `IsLocalization.map_units`, `Localization.AtPrime.map_eq_maximalIdeal`, `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`
- **Used by**: Nothing within this file (leaf theorem); presumably used by downstream DVR/valuation files.
- **Visibility**: public
- **Lines**: 235–375, proof ~140 lines
- **Notes**: `set_option maxHeartbeats 3200000` at line 235 — NO inline comment explaining the high heartbeat budget (4× the other theorems). **Proof is far >30 lines (~140 lines).** The X-branch (lines 246–343) inlines the full logic of `xclass_mul_C_g_in_yclass_span` and `mk_C_g_not_mem` rather than calling those lemmas — making those two public lemmas appear unused within this file. The two branches are structurally symmetric but not formally deduplicated.

---

## Summary statistics

| Kind | Count |
|------|-------|
| `noncomputable def` | 1 |
| `theorem` (public) | 8 |
| `theorem` (private) | 2 |
| **Total** | **11** |

## `set_option maxHeartbeats` occurrences

| Line | Value | Comment |
|------|-------|---------|
| 51 | 800000 | "Type class synthesis in CoordinateRing is expensive." |
| 75 | 800000 | (no inline comment; preceding section comment mentions expense) |
| 140 | 800000 | (no inline comment; block header explains X/Y symmetry) |
| 177 | 800000 | (no inline comment) |
| 235 | 3200000 | (no inline comment) |

## Long proofs (>30 lines)

| Name | Lines |
|------|-------|
| `xclass_mul_C_g_in_yclass_span` | ~35 |
| `mk_C_g_not_mem` | ~45 |
| `localRing_isDVR` | ~140 |

## Unused within file (dead-code candidates)

- `xclass_mul_C_g_in_yclass_span` — the X-branch of `localRing_isDVR` inlines equivalent logic
- `mk_C_g_not_mem` — the X-branch of `localRing_isDVR` inlines equivalent logic
- `pointIdeal` — used only by `pointIdeal_isMaximal` and `localRing_isDVR`

## Key API (used by 3+ declarations in this file)

- `eval_poly_deriv_eq_polynomialX_eval` (private) — used by `quot_evalEval_eq_polynomialY` (indirectly via the same calculation), `mk_C_g_not_mem`, `localRing_isDVR`
- `pointIdeal` — used by `pointIdeal_isMaximal`, `localRing_isDVR`

## Notes

The file constructs the DVR property via the TFAE characterization from mathlib (`tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`). The X-branch of `localRing_isDVR` duplicates the proofs of `xclass_mul_C_g_in_yclass_span` and `mk_C_g_not_mem` inline, making those two public lemmas dead code within the file (they exist for symmetric exposition). There is no `sorry` in the file.
