# Inventory: ./HasseWeil/OrdAtInftyBridge.lean

**File purpose**: Bridge from the project's `WeierstrassCurve`/`x_gen`/`y_gen` framework to the `SmoothPlaneCurve`-indexed `ordAtInfty` infrastructure in `HasseWeil/Curves/Infinity.lean`. Re-exports `ordAtInfty` facts for the generators and division-polynomial function-field elements `Φ_ff`, `ΨSq_ff`, and `mulByInt_x`.

**Imports**: `HasseWeil.MulByIntPullback`, `HasseWeil.Curves.Infinity`

**Total declarations**: 19 (18 public + 1 private)

---

## Declarations

### `noncomputable def W_smooth`
- **Type**: `W_smooth (W : WeierstrassCurve F) [W.toAffine.IsElliptic] : SmoothPlaneCurve F`
- **What**: Wraps `W.toAffine` as a `SmoothPlaneCurve F` so that the `ordAtInfty` machinery from `Curves/Infinity.lean` (which is indexed by `SmoothPlaneCurve`) can be applied.
- **How**: Constructor `⟨W.toAffine⟩`; definitionally trivial one-liner.
- **Hypotheses**: `W : WeierstrassCurve F`, `W.toAffine.IsElliptic`.
- **Uses from project**: none directly; just `SmoothPlaneCurve` from `Curves/Infinity.lean`.
- **Used by**: virtually every declaration in this file uses `W_smooth W`.
- **Visibility**: public
- **Lines**: 49–50, proof length 1 (term-mode constructor)
- **Notes**: None.

---

### `@[simp] theorem W_smooth_toAffine`
- **Type**: `(W_smooth W).toAffine = W.toAffine`
- **What**: `rfl` simp lemma: the `toAffine` field of the wrapper is definitionally equal to `W.toAffine`.
- **How**: `rfl`.
- **Hypotheses**: standard curve variable context.
- **Uses from project**: `W_smooth`.
- **Used by**: unused within this file (exported for callers).
- **Visibility**: public, `@[simp]`
- **Lines**: 52–52, proof length 1

---

### `@[simp] theorem W_smooth_functionField`
- **Type**: `(W_smooth W).FunctionField = KE`
- **What**: `rfl` simp lemma: the function field of the wrapper equals `W.toAffine.FunctionField`.
- **How**: `rfl`.
- **Hypotheses**: standard curve variable context.
- **Uses from project**: `W_smooth`.
- **Used by**: used implicitly by `show` casts in `ordAtInfty_Φ_ff`, `ordAtInfty_ΨSq_ff`, `ordAtInfty_mulByInt_x_neg`, `exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two`.
- **Visibility**: public, `@[simp]`
- **Lines**: 56–57, proof length 1

---

### `theorem coordX_W_smooth_eq_x_gen`
- **Type**: `(W_smooth W).coordX = x_gen W`
- **What**: Identifies the `coordX` of the `SmoothPlaneCurve` wrapper with `x_gen W` in the function field; both are the image of `Polynomial.X` under `algebraMap (Polynomial F) KE`.
- **How**: Uses `IsScalarTower.algebraMap_apply` to reduce to `rfl` via the scalar tower `F[X] → CoordinateRing → FunctionField`.
- **Hypotheses**: standard curve variable context.
- **Uses from project**: `W_smooth`, `x_gen`.
- **Used by**: `ordAtInfty_x_gen`, `x_gen_ne_zero`, `ordAtInfty_x_gen_pow`.
- **Visibility**: public
- **Lines**: 61–66, proof length 5

---

### `theorem ordAtInfty_x_gen`
- **Type**: `(W_smooth W).ordAtInfty (x_gen W) = ((-2 : ℤ) : WithTop ℤ)`
- **What**: Proves that the order at infinity of the generic x-coordinate is −2, as in Silverman II.1/IV.1.
- **How**: Rewrites via `coordX_W_smooth_eq_x_gen`, then applies `SmoothPlaneCurve.ordAtInfty_coordX` from `Curves/Infinity.lean`.
- **Hypotheses**: standard curve variable context.
- **Uses from project**: `coordX_W_smooth_eq_x_gen`, `W_smooth`.
- **Used by**: `ordAtInfty_x_gen_pow`.
- **Visibility**: public
- **Lines**: 69–72, proof length 3

---

### `theorem coordY_W_smooth_eq_y_gen`
- **Type**: `(W_smooth W).coordY = y_gen W`
- **What**: Identifies the `coordY` of the wrapper with `y_gen W`; both are the image of `AdjoinRoot.root W.polynomial` in `KE`.
- **How**: Unfolds `SmoothPlaneCurve.coordY` and `y_gen`, then rewrites with `Affine.CoordinateRing.basis_one` which identifies `basis 1 = AdjoinRoot.mk _ X = AdjoinRoot.root _`.
- **Hypotheses**: standard curve variable context.
- **Uses from project**: `W_smooth`, `y_gen`, `Affine.CoordinateRing.basis_one`.
- **Used by**: `ordAtInfty_y_gen`, `y_gen_ne_zero`, `ordAtInfty_y_gen_pow`.
- **Visibility**: public
- **Lines**: 78–81, proof length 3

---

### `theorem ordAtInfty_y_gen`
- **Type**: `(W_smooth W).ordAtInfty (y_gen W) = ((-3 : ℤ) : WithTop ℤ)`
- **What**: Proves that the order at infinity of the generic y-coordinate is −3, as in Silverman II.1/IV.1.
- **How**: Rewrites via `coordY_W_smooth_eq_y_gen`, then applies `SmoothPlaneCurve.ordAtInfty_coordY`.
- **Hypotheses**: standard curve variable context.
- **Uses from project**: `coordY_W_smooth_eq_y_gen`, `W_smooth`.
- **Used by**: `ordAtInfty_y_gen_pow`.
- **Visibility**: public
- **Lines**: 84–87, proof length 3

---

### `theorem ordAtInfty_algebraMap_F_nonzero`
- **Type**: `{c : F} → (hc : c ≠ 0) → (W_smooth W).ordAtInfty (algebraMap F KE c) = 0`
- **What**: Constants from the base field have order 0 at infinity.
- **How**: Direct delegation to `SmoothPlaneCurve.ordAtInfty_algebraMap_F_nonzero` applied to `W_smooth W`.
- **Hypotheses**: `c : F`, `c ≠ 0`.
- **Uses from project**: `W_smooth`.
- **Used by**: unused within this file (exported for callers).
- **Visibility**: public
- **Lines**: 91–93, proof length 1

---

### `theorem x_gen_ne_zero`
- **Type**: `x_gen W ≠ 0`
- **What**: The generic x-coordinate is nonzero in the function field.
- **How**: Rewrites via `coordX_W_smooth_eq_x_gen` then applies `SmoothPlaneCurve.coordX_ne_zero`.
- **Hypotheses**: standard curve variable context.
- **Uses from project**: `coordX_W_smooth_eq_x_gen`, `W_smooth`.
- **Used by**: `ordAtInfty_x_gen_pow`.
- **Visibility**: public
- **Lines**: 98–99, proof length 2

---

### `theorem y_gen_ne_zero`
- **Type**: `y_gen W ≠ 0`
- **What**: The generic y-coordinate is nonzero in the function field.
- **How**: Rewrites via `coordY_W_smooth_eq_y_gen` then applies `SmoothPlaneCurve.coordY_ne_zero`.
- **Hypotheses**: standard curve variable context.
- **Uses from project**: `coordY_W_smooth_eq_y_gen`, `W_smooth`.
- **Used by**: `ordAtInfty_y_gen_pow`.
- **Visibility**: public
- **Lines**: 102–103, proof length 2

---

### `theorem ordAtInfty_x_gen_pow`
- **Type**: `(n : ℕ) → (W_smooth W).ordAtInfty (x_gen W ^ n) = n • ((-2 : ℤ) : WithTop ℤ)`
- **What**: The order at infinity of `x_gen^n` is `n·(−2)`.
- **How**: Applies `SmoothPlaneCurve.ordAtInfty_pow` to `x_gen_ne_zero`, then rewrites with `ordAtInfty_x_gen`.
- **Hypotheses**: standard curve variable context, `n : ℕ`.
- **Uses from project**: `W_smooth`, `x_gen_ne_zero`, `ordAtInfty_x_gen`.
- **Used by**: unused within this file (exported for callers).
- **Visibility**: public
- **Lines**: 106–111, proof length 5

---

### `theorem ordAtInfty_y_gen_pow`
- **Type**: `(n : ℕ) → (W_smooth W).ordAtInfty (y_gen W ^ n) = n • ((-3 : ℤ) : WithTop ℤ)`
- **What**: The order at infinity of `y_gen^n` is `n·(−3)`.
- **How**: Applies `SmoothPlaneCurve.ordAtInfty_pow` to `y_gen_ne_zero`, then rewrites with `ordAtInfty_y_gen`.
- **Hypotheses**: standard curve variable context, `n : ℕ`.
- **Uses from project**: `W_smooth`, `y_gen_ne_zero`, `ordAtInfty_y_gen`.
- **Used by**: unused within this file (exported for callers).
- **Visibility**: public
- **Lines**: 114–119, proof length 5

---

### `theorem Φ_ff_eq_algebraMap_polynomial`
- **Type**: `(n : ℤ) → Φ_ff W n = algebraMap (Polynomial F) KE (W.Φ n)`
- **What**: Identifies `Φ_ff W n` (defined via a two-step algebraMap) with the direct `algebraMap (Polynomial F) KE (W.Φ n)` via the scalar tower `F[X] → CoordinateRing → FunctionField`.
- **How**: Single application of `IsScalarTower.algebraMap_apply` (symmetrically).
- **Hypotheses**: standard curve variable context, `n : ℤ`.
- **Uses from project**: `Φ_ff` (from MulByIntPullback).
- **Used by**: `ordAtInfty_Φ_ff`, `Φ_ff_ne_zero`, `ordAtInfty_mulByInt_x`, `ordAtInfty_mulByInt_x_neg`, `exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two`.
- **Visibility**: public
- **Lines**: 131–134, proof length 2

---

### `theorem ΨSq_ff_eq_algebraMap_polynomial`
- **Type**: `(n : ℤ) → ΨSq_ff W n = algebraMap (Polynomial F) KE (W.ΨSq n)`
- **What**: Identifies `ΨSq_ff W n` with the direct `algebraMap (Polynomial F) KE (W.ΨSq n)` via the same scalar tower.
- **How**: Single application of `IsScalarTower.algebraMap_apply` (symmetrically).
- **Hypotheses**: standard curve variable context, `n : ℤ`.
- **Uses from project**: `ΨSq_ff` (from MulByIntPullback).
- **Used by**: `ordAtInfty_ΨSq_ff`, `ordAtInfty_mulByInt_x_neg`, `exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two`.
- **Visibility**: public
- **Lines**: 138–141, proof length 2

---

### `theorem ordAtInfty_Φ_ff`
- **Type**: `(n : ℤ) → (W_smooth W).ordAtInfty (Φ_ff W n) = ((-2 * (n.natAbs : ℤ) ^ 2 : ℤ) : WithTop ℤ)`
- **What**: Computes the order at infinity of the n-th division polynomial numerator element `Φ_ff W n` as `−2·natAbs(n)²`.
- **How**: Uses `Φ_ff_eq_algebraMap_polynomial` to reduce to the polynomial setting, applies `SmoothPlaneCurve.ordAtInfty_algebraMap_polynomial_of_ne_zero` with `W.Φ_ne_zero`, then `W.natDegree_Φ n`, and simplifies the cast arithmetic with `push_cast; ring_nf`.
- **Hypotheses**: standard curve variable context, `n : ℤ`.
- **Uses from project**: `W_smooth`, `Φ_ff_eq_algebraMap_polynomial`, `Φ_ff` (from MulByIntPullback); `W.Φ_ne_zero`, `W.natDegree_Φ` (from mathlib/WeierstrassCurve).
- **Used by**: `ordAtInfty_mulByInt_x`, `ordAtInfty_mulByInt_x_neg`, `exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two`.
- **Visibility**: public
- **Lines**: 149–158, proof length 9

---

### `theorem ordAtInfty_ΨSq_ff`
- **Type**: `(n : ℤ) → (hnF : (n : F) ≠ 0) → (W_smooth W).ordAtInfty (ΨSq_ff W n) = ((-2 * ((n.natAbs : ℤ) ^ 2 - 1) : ℤ) : WithTop ℤ)`
- **What**: Computes the order at infinity of `ΨSq_ff W n` (the squared n-th division polynomial element) as `−2·(natAbs(n)² − 1)`, under the separability hypothesis `(n : F) ≠ 0`.
- **How**: Uses `ΨSq_ff_eq_algebraMap_polynomial`, `SmoothPlaneCurve.ordAtInfty_algebraMap_polynomial_of_ne_zero`, `W.ΨSq_ne_zero hnF`, and `W.natDegree_ΨSq hnF`; handles the cast of `Nat.sub` via `h_pos` (showing `1 ≤ natAbs^2`) and `Nat.cast_sub`.
- **Hypotheses**: `(n : F) ≠ 0` (separability); standard curve variable context.
- **Uses from project**: `W_smooth`, `ΨSq_ff_eq_algebraMap_polynomial`, `ΨSq_ff` (from MulByIntPullback).
- **Used by**: `ordAtInfty_mulByInt_x`.
- **Visibility**: public
- **Lines**: 161–178, proof length 17

---

### `private theorem algebraMap_polynomial_KE_injective`
- **Type**: `Function.Injective (algebraMap (Polynomial F) W.toAffine.FunctionField)`
- **What**: The composition of scalar tower algebraMaps `F[X] → CoordinateRing → FunctionField` is injective.
- **How**: Composes `IsFractionRing.injective` (injectivity of CoordinateRing → FunctionField) with `Affine.CoordinateRing.algebraMap_poly_injective`.
- **Hypotheses**: standard curve variable context.
- **Uses from project**: `Affine.CoordinateRing.algebraMap_poly_injective` (from mathlib via WeierstrassCurve).
- **Used by**: `Φ_ff_ne_zero`.
- **Visibility**: private
- **Lines**: 183–188, proof length 5

---

### `theorem Φ_ff_ne_zero`
- **Type**: `(n : ℤ) → Φ_ff W n ≠ 0`
- **What**: `Φ_ff W n` is nonzero for any `n : ℤ`.
- **How**: Rewrites via `Φ_ff_eq_algebraMap_polynomial`, then deduces contradiction from `algebraMap_polynomial_KE_injective` and `W.Φ_ne_zero`.
- **Hypotheses**: standard curve variable context; `omit [DecidableEq F]` annotation (the proof uses `classical` instead).
- **Uses from project**: `Φ_ff_eq_algebraMap_polynomial`, `algebraMap_polynomial_KE_injective`, `W.Φ_ne_zero`.
- **Used by**: `mulByInt_x_ne_zero`, `ordAtInfty_mulByInt_x`, `ordAtInfty_mulByInt_x_neg`, `exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two`.
- **Visibility**: public
- **Lines**: 192–197, proof length 5

---

### `theorem mulByInt_x_ne_zero`
- **Type**: `(n : ℤ) → (hn : n ≠ 0) → mulByInt_x W n ≠ 0`
- **What**: The x-coordinate of the `n`-multiplication map is nonzero in the function field, for `n ≠ 0`.
- **How**: Unfolds `mulByInt_x` as `Φ_ff / ΨSq_ff` and applies `div_ne_zero` using `Φ_ff_ne_zero` and `ΨSq_ff_ne_zero` (from MulByIntPullback).
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `Φ_ff_ne_zero`, `ΨSq_ff_ne_zero` (from MulByIntPullback), `mulByInt_x` (from MulByIntPullback).
- **Used by**: unused within this file (exported for callers).
- **Visibility**: public
- **Lines**: 201–203, proof length 3

---

### `theorem ordAtInfty_mulByInt_x`
- **Type**: `(n : ℤ) → (hn : n ≠ 0) → (hnF : (n : F) ≠ 0) → (W_smooth W).ordAtInfty (mulByInt_x W n) = ((-2 : ℤ) : WithTop ℤ)`
- **What**: The order at infinity of `mulByInt_x W n` is exactly −2, under the separability hypothesis `(n : F) ≠ 0`.
- **How**: Unfolds `mulByInt_x = Φ_ff / ΨSq_ff`, uses `ordAtInfty_mul` + `ordAtInfty_inv` to split order of quotient, then applies `ordAtInfty_Φ_ff` and `ordAtInfty_ΨSq_ff`; arithmetic on `WithTop ℤ` is handled by a nested `congr 1; ring` after explicit `push_cast; rfl` lemmas for each cast step.
- **Hypotheses**: `n ≠ 0`, `(n : F) ≠ 0`.
- **Uses from project**: `W_smooth`, `Φ_ff_ne_zero`, `ΨSq_ff_ne_zero` (MulByIntPullback), `ordAtInfty_Φ_ff`, `ordAtInfty_ΨSq_ff`, `mulByInt_x` (MulByIntPullback).
- **Used by**: unused within this file (exported for callers).
- **Visibility**: public
- **Lines**: 209–233, proof length 24
- **Notes**: The `WithTop ℤ` arithmetic requires manual push_cast/rfl lemma cascades; slightly verbose but no sorry.

---

### `theorem ordAtInfty_mulByInt_x_neg`
- **Type**: `(n : ℤ) → (hn : n ≠ 0) → (W_smooth W).ordAtInfty (mulByInt_x W n) < 0`
- **What**: Unconditional weaker bound: `mulByInt_x W n` has a strictly negative order at infinity for any `n ≠ 0`, without requiring `(n : F) ≠ 0` (covers the inseparable case).
- **How**: Rewrites to `Φ_ff * (ΨSq_ff)⁻¹`, uses `ordAtInfty_mul`/`ordAtInfty_inv`, applies the unconditional polynomial-ord lemma `ordAtInfty_algebraMap_polynomial_of_ne_zero` for `ΨSq_ff` (via `ΨSq_poly_ne_zero`), and deduces strict negativity from `W.natDegree_ΨSq_le` + `Int.natAbs_pos`. Strict comparison is transported to `WithTop ℤ` via `exact_mod_cast h_int`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `W_smooth`, `Φ_ff_ne_zero`, `ΨSq_ff_ne_zero` (MulByIntPullback), `ΨSq_poly_ne_zero` (MulByIntPullback), `ordAtInfty_Φ_ff`, `ΨSq_ff_eq_algebraMap_polynomial`, `mulByInt_x` (MulByIntPullback); `W.natDegree_ΨSq_le` (mathlib).
- **Used by**: `exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two` (docstring reference).
- **Visibility**: public
- **Lines**: 249–284, proof length 35
- **Notes**: Proof is 35 lines — exceeds 30-line threshold. Handles the inseparable regime not covered by `ordAtInfty_mulByInt_x`.

---

### `theorem exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two`
- **Type**: `(n : ℤ) → (hn : n ≠ 0) → ∃ M : ℤ, (W_smooth W).ordAtInfty (mulByInt_x W n) = ((M : ℤ) : WithTop ℤ) ∧ M ≤ -2 ∧ Even M`
- **What**: Sharpens the unconditional bound: `ord_∞(mulByInt_x W n)` equals some explicit even integer `M ≤ −2`, with `M = −2·(natAbs(n)² − natDegree(ΨSq n))`, valid without `(n : F) ≠ 0`.
- **How**: Provides the witness `M = -2 * (natAbs^2 - natDegree (ΨSq n))`; for the value equality uses the same `ordAtInfty_mul / ordAtInfty_inv / ordAtInfty_Φ_ff` chain plus `push_cast; rfl` arithmetic; for `M ≤ -2` uses `W.natDegree_ΨSq_le` + `nlinarith`; evenness is `⟨-(natAbs^2 - natDegree ΨSq), by ring⟩`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `W_smooth`, `Φ_ff_ne_zero`, `ΨSq_ff_ne_zero` (MulByIntPullback), `ΨSq_poly_ne_zero` (MulByIntPullback), `ordAtInfty_Φ_ff`, `ΨSq_ff_eq_algebraMap_polynomial`, `mulByInt_x` (MulByIntPullback); `W.natDegree_ΨSq_le` (mathlib).
- **Used by**: unused within this file (exported for callers — intended for the pencil `r·π − s` inseparable regime).
- **Visibility**: public
- **Lines**: 297–331, proof length 34
- **Notes**: Proof is 34 lines — exceeds 30-line threshold. This is the main new lemma motivating the file's extension; docstring explains the pencil-scaling application.

---

## Cross-reference summary

**Key API (used by 3+ others in this file)**:
- `W_smooth` — used by all 18 public declarations.
- `Φ_ff_ne_zero` — used by `mulByInt_x_ne_zero`, `ordAtInfty_mulByInt_x`, `ordAtInfty_mulByInt_x_neg`, `exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two`.
- `ordAtInfty_Φ_ff` — used by `ordAtInfty_mulByInt_x`, `ordAtInfty_mulByInt_x_neg`, `exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two`.
- `Φ_ff_eq_algebraMap_polynomial` — used by `ordAtInfty_Φ_ff`, `Φ_ff_ne_zero`, `ordAtInfty_mulByInt_x`, `ordAtInfty_mulByInt_x_neg`, `exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two`.
- `ΨSq_ff_eq_algebraMap_polynomial` — used by `ordAtInfty_ΨSq_ff`, `ordAtInfty_mulByInt_x_neg`, `exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two`.

**Declarations unused within this file** (dead code for other files):
- `W_smooth_toAffine`
- `W_smooth_functionField`
- `ordAtInfty_algebraMap_F_nonzero`
- `ordAtInfty_x_gen_pow`
- `ordAtInfty_y_gen_pow`
- `mulByInt_x_ne_zero`
- `ordAtInfty_mulByInt_x`
- `exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two`

**Sorries**: none.

**`set_option maxHeartbeats`**: none in file.

**Long proofs (>30 lines)**:
- `ordAtInfty_mulByInt_x_neg`: 35 lines (L249–284).
- `exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two`: 34 lines (L297–331).
