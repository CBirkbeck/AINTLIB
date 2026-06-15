# Inventory: ./HasseWeil/Curves/AlgebraicNonNegOrd.lean

**File path:** `HasseWeil/Curves/AlgebraicNonNegOrd.lean`
**Namespace:** `HasseWeil.Curves.SmoothPlaneCurve`
**Imports:** `HasseWeil.Curves.Divisors`, `Mathlib.RingTheory.Valuation.Integral`

**Summary:** 127 lines, 3 declarations (2 theorems + 1 theorem used as a helper), no sorries, no `set_option maxHeartbeats`. Proves the algebraic-Liouville inequality (Silverman II.1): algebraic elements over `F` have nonneg order at every smooth point, and its contrapositive transcendence criterion.

---

## Declaration Inventory

---

### `theorem pointValuation_algebraMap_F_le_one`

- **Type**: `(P : C.SmoothPoint) (c : F) : C.pointValuation P (algebraMap F C.FunctionField c) ≤ 1`
- **What**: Every element of the constant field `F` (lifted to the function field `F(C)` via the algebra map) lies in the valuation ring at every smooth point `P`, i.e., has `pointValuation P (c) ≤ 1`.
- **How**: Rewrites the `F → F(C)` algebra map as the composition `F → C.CoordinateRing → F(C)` using `IsScalarTower.algebraMap_apply`, then invokes the project's `pointValuation_algebraMap_le_one` (in `Infinity.lean`) which handles the `CoordinateRing → FunctionField` step.
- **Hypotheses**: `C : SmoothPlaneCurve F`, `F` a field, `P` a smooth point.
- **Uses from project**: `C.pointValuation_algebraMap_le_one` (from `HasseWeil/Curves/Infinity.lean`)
- **Used by**: `ord_P_nonneg_of_isAlgebraic` (this file); heavily used by callers in `SamePlace.lean`, `TranslateLocalRing.lean`, `TranslateValuation.lean`, `TranslationOrd.lean`, `MulByIntSamePlace.lean`, `OneSubAffineResidues.lean`, `PencilComapWitnesses.lean`, `L6Witnesses.lean` (other files).
- **Visibility**: public
- **Lines**: 49–55, proof length 5 lines
- **Notes**: Thin wrapper / scalar-tower adapter for `pointValuation_algebraMap_le_one`. Widely used across the project (key API node).

---

### `theorem ord_P_nonneg_of_isAlgebraic`

- **Type**: `(P : C.SmoothPoint) {f : C.FunctionField} (h_alg : IsAlgebraic F f) : (0 : WithTop ℤ) ≤ C.ord_P P f`
- **What**: The algebraic-Liouville inequality: every element of `F(C)` that is algebraic over the constant field `F` has nonnegative order `ord_P P f ≥ 0` at every smooth point `P` of the curve. This is the discrete analogue of Liouville's theorem at finite places.
- **How**: Constructs a ring hom `φ : F →+* (pointValuation P).integer` using `pointValuation_algebraMap_F_le_one` (constants land in the valuation ring), lifts the monic minimal polynomial of `f` over `F` to a polynomial over the valuation ring, concludes `f` is integral over the valuation ring, then applies Mathlib's `Valuation.integer.integers.isIntegral_iff_v_le_one` to get `pointValuation P f ≤ 1`, and finally converts that inequality to `0 ≤ ord_P P f` by unfolding the `WithTop ℤ`-valued `ord_P` definition and reasoning about `WithZero.unzero` / `Multiplicative.toAdd` monotonicity with `omega`.
- **Hypotheses**: `C : SmoothPlaneCurve F`, `F` a field, `P` a smooth point, `f` algebraic over `F`.
- **Uses from project**: `pointValuation_algebraMap_F_le_one` (this file); `C.ord_P` and `ord_P_zero` (from `HasseWeil/Curves/Valuation.lean`).
- **Used by**: `transcendental_of_neg_ord_P` (this file).
- **Visibility**: public
- **Lines**: 68–112, proof length 44 lines
- **Notes**: **Proof longer than 30 lines (44 lines).** No sorry. The proof is self-contained but somewhat low-level: it manually unfolds the `WithTop ℤ` encoding of `ord_P` and uses `WithZero.coe_le_coe`, `WithZero.coe_unzero`, and `omega` to convert `pointValuation ≤ 1` to `0 ≤ ord_P`. A cleaner approach might factor out a project lemma `ord_P_nonneg_iff_pointValuation_le_one`. Silverman II.1 reference is accurate.

---

### `theorem transcendental_of_neg_ord_P`

- **Type**: `{P : C.SmoothPoint} {f : C.FunctionField} (h_neg : C.ord_P P f < 0) : Transcendental F f`
- **What**: The transcendence-from-pole criterion: if `f ∈ F(C)` has strictly negative order at any single smooth point `P`, then `f` is transcendental over `F`. This is the contrapositive of the algebraic-Liouville inequality.
- **How**: Direct contrapositive: assumes `f` is algebraic and derives a contradiction with `h_neg` via `ord_P_nonneg_of_isAlgebraic` and `not_le.mpr`.
- **Hypotheses**: `C : SmoothPlaneCurve F`, `F` a field, `P` a smooth point, `f` with negative order at `P`.
- **Uses from project**: `ord_P_nonneg_of_isAlgebraic` (this file).
- **Used by**: Used in `TranslationOrd.lean` (lines 1892 and 3008) as the transcendence engine for coordinate functions with negative order.
- **Visibility**: public
- **Lines**: 117–122, proof length 4 lines
- **Notes**: Minimal one-liner contrapositive; serves as the public API entry point used by downstream files.
