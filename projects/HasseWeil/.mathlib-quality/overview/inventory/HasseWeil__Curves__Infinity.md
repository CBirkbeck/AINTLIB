# Inventory: ./HasseWeil/Curves/Infinity.lean

**Total lines**: 1762  
**Total declarations**: 97 (4 `noncomputable def`, 1 `noncomputable instance`, 76 `theorem`, 16 `private theorem`/`private noncomputable def`)  
**Sorries**: none  
**set_option**: 1 (`set_option synthInstance.maxHeartbeats 80000` at L1529)

## Overview

This file defines and develops the theory of the **order at infinity** `ordAtInfty : F(C) → WithTop ℤ` on the function field of a smooth plane (Weierstrass) curve. The order is defined algebraically via `- intDegree(N(f))` where `N` is the algebra norm `F(C)/F(x)`. The file proves the classical values `ord_∞(x) = -2`, `ord_∞(y) = -3`, the non-archimedean inequality, and uses these to prove algebraic Liouville and Bezout-finiteness theorems. It also packages `ordAtInfty` as a multiplicative `Valuation` object and develops the `maximalIdealAt` ↔ evaluation bridge.

---

### `noncomputable def normAsRatFunc`
- **Type**: `(f : C.FunctionField) → RatFunc F`
- **What**: Packages the algebra norm `N : F(C) → FractionRing(F[X])` as a `RatFunc F` by applying `RatFunc.ofFractionRing` to `C.fieldNorm f`.
- **How**: Single application of `RatFunc.ofFractionRing` to `C.fieldNorm`.
- **Hypotheses**: C is a `SmoothPlaneCurve F`.
- **Uses from project**: `C.fieldNorm`
- **Used by**: `normAsRatFunc_zero`, `normAsRatFunc_one`, `normAsRatFunc_mul`, `normAsRatFunc_eq_zero_iff`, `ordAtInfty`, `normAsRatFunc_neg_one`, `normAsRatFunc_inv`, `ordAtInfty_algebraMap_fracPolyX_of_ne_zero`, `ordAtInfty_coordX`, `ordAtInfty_coordY`, `ordAtInftyVal`
- **Visibility**: public
- **Lines**: 57–59 (definition, 3 lines)
- **Notes**: Key packaging abstraction for downstream ord computations.

---

### `@[simp] theorem normAsRatFunc_zero`
- **Type**: `C.normAsRatFunc 0 = 0`
- **What**: The norm of zero is zero, as a `RatFunc`.
- **How**: `simp` with `RatFunc.ofFractionRing_zero`.
- **Hypotheses**: none beyond the curve.
- **Uses from project**: `normAsRatFunc`
- **Used by**: `normAsRatFunc_eq_zero_iff`
- **Visibility**: public
- **Lines**: 60–62 (2 lines)

---

### `@[simp] theorem normAsRatFunc_one`
- **Type**: `C.normAsRatFunc 1 = 1`
- **What**: The norm of 1 is 1.
- **How**: `simp` with `RatFunc.ofFractionRing_one`.
- **Hypotheses**: none.
- **Uses from project**: `normAsRatFunc`
- **Used by**: `normAsRatFunc_inv`, `ordAtInfty_one`, `ordAtInfty_algebraMap_F_nonzero`
- **Visibility**: public
- **Lines**: 63–65 (2 lines)

---

### `theorem normAsRatFunc_mul`
- **Type**: `C.normAsRatFunc (f * g) = C.normAsRatFunc f * C.normAsRatFunc g`
- **What**: Multiplicativity of `normAsRatFunc`.
- **How**: `simp` with `RatFunc.ofFractionRing_mul`.
- **Hypotheses**: none (works for all f, g).
- **Uses from project**: `normAsRatFunc`
- **Used by**: `ordAtInfty_mul`, `normAsRatFunc_inv`
- **Visibility**: public
- **Lines**: 66–69 (3 lines)

---

### `theorem normAsRatFunc_eq_zero_iff`
- **Type**: `C.normAsRatFunc f = 0 ↔ f = 0`
- **What**: The norm (as RatFunc) is zero if and only if f is zero.
- **How**: Uses `RatFunc.ofFractionRing` injectivity and `C.fieldNorm_eq_zero_iff`.
- **Hypotheses**: none.
- **Uses from project**: `normAsRatFunc`, `C.fieldNorm_eq_zero_iff`
- **Used by**: `ordAtInfty_mul`, `ordAtInfty_algebraMap_fracPolyX_of_ne_zero`
- **Visibility**: public
- **Lines**: 70–76 (6 lines)

---

### `noncomputable def ordAtInfty`
- **Type**: `(f : C.FunctionField) → WithTop ℤ`
- **What**: The order of a function at the point at infinity: `⊤` for `f = 0`, and `- intDegree(N(f))` for nonzero `f`. The sign convention makes poles negative and zeros positive.
- **How**: Conditional definition using `if f = 0`.
- **Hypotheses**: none.
- **Uses from project**: `normAsRatFunc`
- **Used by**: Essentially all subsequent theorems in the file.
- **Visibility**: public
- **Lines**: 81–84 (4 lines)
- **Notes**: Central definition of the entire file.

---

### `@[simp] theorem ordAtInfty_zero`
- **Type**: `C.ordAtInfty 0 = ⊤`
- **What**: Order at infinity of zero is `⊤`.
- **How**: `if_pos rfl`.
- **Uses from project**: `ordAtInfty`
- **Used by**: `ordAtInfty_eq_top_iff`, `ordAtInfty_neg`, `ordAtInfty_basis_eq_min`, `ordAtInfty_algebraMap_fracPolyX_add_ge_min`, others
- **Visibility**: public
- **Lines**: 85 (1 line)

---

### `theorem ordAtInfty_eq_top_iff`
- **Type**: `C.ordAtInfty f = ⊤ ↔ f = 0`
- **What**: Order at infinity is `⊤` if and only if `f = 0`.
- **How**: Case split on the `if` in `ordAtInfty`.
- **Uses from project**: `ordAtInfty`
- **Used by**: `ordAtInftyValuation_surjective` (indirectly via `ordAtInfty_coordY`)
- **Visibility**: public
- **Lines**: 87–93 (6 lines)

---

### `theorem ordAtInfty_of_ne`
- **Type**: `(hf : f ≠ 0) → C.ordAtInfty f = (- RatFunc.intDegree (C.normAsRatFunc f) : ℤ)`
- **What**: For nonzero `f`, `ordAtInfty f` equals `-intDegree(N(f))` cast to `WithTop ℤ`.
- **How**: `if_neg hf`.
- **Uses from project**: `ordAtInfty`, `normAsRatFunc`
- **Used by**: `ordAtInfty_mul`, `ordAtInfty_one`, `ordAtInfty_neg`, `ordAtInfty_pow`, `ordAtInfty_inv`, `ordAtInfty_algebraMap_fracPolyX_of_ne_zero`, `ordAtInfty_algebraMap_coordinateRing`, `ordAtInftyVal_eq_exp_neg_ordAtInfty`, and many more (used 16 times)
- **Visibility**: public
- **Lines**: 94–97 (3 lines)
- **Notes**: Key API lemma; used 16 times in this file alone.

---

### `theorem ordAtInfty_mul`
- **Type**: `(hf : f ≠ 0) (hg : g ≠ 0) → C.ordAtInfty (f * g) = C.ordAtInfty f + C.ordAtInfty g`
- **What**: Multiplicativity of `ordAtInfty`: `ord(f·g) = ord(f) + ord(g)` for nonzero f, g.
- **How**: Uses `normAsRatFunc_mul`, `RatFunc.intDegree_mul`, and the nonzero conditions from `normAsRatFunc_eq_zero_iff`.
- **Hypotheses**: `f ≠ 0`, `g ≠ 0`.
- **Uses from project**: `ordAtInfty_of_ne`, `normAsRatFunc_mul`, `normAsRatFunc_eq_zero_iff`
- **Used by**: `ordAtInfty_one`, `ordAtInfty_neg`, `ordAtInfty_pow`, `ordAtInfty_inv`, `ordAtInfty_div_eq_mul_inv`, `ordAtInfty_algebraMap_fracPolyX_of_ne_zero`, `ordAtInfty_basis_eq_min`, `ordAtInftyVal_mul`, and others (6 uses)
- **Visibility**: public
- **Lines**: 100–108 (8 lines)

---

### `@[simp] theorem ordAtInfty_one`
- **Type**: `C.ordAtInfty (1 : C.FunctionField) = 0`
- **What**: Order at infinity of 1 is 0.
- **How**: Uses `ordAtInfty_of_ne` + `normAsRatFunc_one` + `RatFunc.intDegree_one`.
- **Uses from project**: `ordAtInfty_of_ne`, `normAsRatFunc_one`
- **Used by**: `ordAtInfty_pow`, `ordAtInftyVal_one`
- **Visibility**: public
- **Lines**: 110–112 (3 lines)

---

### `theorem normAsRatFunc_neg_one`
- **Type**: `C.normAsRatFunc (-1 : C.FunctionField) = 1`
- **What**: The norm of `-1` (as a constant from the base field) is `1`, since `N(-1) = (-1)^2 = 1`.
- **How**: Lifts `-1` via `algebraMap` and uses `C.fieldNorm_algebraMap` + `neg_one_sq`.
- **Uses from project**: `normAsRatFunc`, `C.fieldNorm_algebraMap`
- **Used by**: `ordAtInfty_neg_one`
- **Visibility**: public
- **Lines**: 126–130 (5 lines)

---

### `@[simp] theorem ordAtInfty_neg_one`
- **Type**: `C.ordAtInfty (-1 : C.FunctionField) = 0`
- **What**: Order at infinity of `-1` is 0.
- **How**: Uses `ordAtInfty_of_ne` + `normAsRatFunc_neg_one` + `RatFunc.intDegree_one`.
- **Uses from project**: `normAsRatFunc_neg_one`, `ordAtInfty_of_ne`
- **Used by**: `ordAtInfty_neg`
- **Visibility**: public
- **Lines**: 133–136 (4 lines)

---

### `@[simp] theorem ordAtInfty_neg`
- **Type**: `C.ordAtInfty (-f) = C.ordAtInfty f`
- **What**: Order at infinity is negation-invariant.
- **How**: Factors `-f = (-1) * f` and uses `ordAtInfty_mul` + `ordAtInfty_neg_one`.
- **Uses from project**: `ordAtInfty_mul`, `ordAtInfty_neg_one`
- **Used by**: `ordAtInfty_sub_ge_min`, `ordAtInfty_sub_eq_of_lt`, `ordAtInfty_add_eq_of_lt` (via h_step)
- **Visibility**: public
- **Lines**: 139–146 (7 lines)

---

### `theorem ordAtInfty_pow`
- **Type**: `(hf : f ≠ 0) (n : ℕ) → C.ordAtInfty (f ^ n) = n • C.ordAtInfty f`
- **What**: `ord(f^n) = n • ord(f)` for nonzero `f`.
- **How**: Induction on `n`, using `ordAtInfty_mul` for the successor case.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `ordAtInfty_one`, `ordAtInfty_mul`
- **Used by**: `ordAtInfty_pow_of_ord_eq`
- **Visibility**: public
- **Lines**: 148–154 (6 lines)

---

### `theorem normAsRatFunc_inv`
- **Type**: `(hf : f ≠ 0) → C.normAsRatFunc (f⁻¹) = (C.normAsRatFunc f)⁻¹`
- **What**: The norm of an inverse is the inverse of the norm.
- **How**: Shows `normAsRatFunc(f⁻¹) * normAsRatFunc(f) = 1` via `normAsRatFunc_mul` and `normAsRatFunc_one`, then uses `eq_inv_of_mul_eq_one_left`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `normAsRatFunc_mul`, `normAsRatFunc_one`
- **Used by**: `ordAtInfty_inv`
- **Visibility**: public
- **Lines**: 158–162 (5 lines)

---

### `theorem ordAtInfty_inv`
- **Type**: `(f : C.FunctionField) → C.ordAtInfty (f⁻¹) = -C.ordAtInfty f`
- **What**: `ord(f⁻¹) = -ord(f)` (with `ord 0⁻¹ = -⊤ = ⊤` handled via `simp`).
- **How**: Case split on `f = 0` vs `f ≠ 0`; uses `normAsRatFunc_inv` + `RatFunc.intDegree_inv`.
- **Uses from project**: `ordAtInfty_of_ne`, `normAsRatFunc_inv`
- **Used by**: `ordAtInfty_div_eq_mul_inv`, `ordAtInfty_basis_eq_min`, `ordAtInfty_div_of_ord_eq`, `ordAtInftyValuation_surjective`
- **Visibility**: public
- **Lines**: 165–173 (9 lines)

---

### `theorem ordAtInfty_div_eq_mul_inv`
- **Type**: `(hf : f ≠ 0) (hg : g ≠ 0) → C.ordAtInfty (f / g) = C.ordAtInfty f + C.ordAtInfty (g⁻¹)`
- **What**: `ord(f/g) = ord(f) + ord(g⁻¹)` — the additive form of division (no `WithTop` subtraction).
- **How**: Rewrites `f/g = f * g⁻¹` then applies `ordAtInfty_mul`.
- **Uses from project**: `ordAtInfty_mul`
- **Used by**: `ordAtInftyValuation_surjective`, `ordAtInfty_div_of_ord_eq`
- **Visibility**: public
- **Lines**: 179–182 (4 lines)

---

### `private theorem ofFractionRing_sq`
- **Type**: `RatFunc.ofFractionRing (r ^ 2) = (RatFunc.ofFractionRing r : RatFunc F) ^ 2`
- **What**: Commutativity of `ofFractionRing` with squaring.
- **How**: `sq`, `RatFunc.ofFractionRing_mul`.
- **Uses from project**: none
- **Used by**: `ordAtInfty_algebraMap_fracPolyX_of_ne_zero`, `ordAtInfty_coordX`
- **Visibility**: private
- **Lines**: 184–186 (3 lines)

---

### `theorem ordAtInfty_algebraMap_fracPolyX_of_ne_zero`
- **Type**: For nonzero `r ∈ FractionRing F[X]`, `C.ordAtInfty (algebraMap ... r) = (-2 * intDegree(ofFractionRing r) : ℤ)`
- **What**: The order at infinity of a function-field element coming from `F(X)` is twice the `F(X)`-order at infinity (with a sign): `ord_∞(r) = -2 · intDeg r`. The factor 2 reflects ramification index 2.
- **How**: Uses `fieldNorm_algebraMap` (norm of algebraMap element = element squared) and `ofFractionRing_sq`, then `RatFunc.intDegree_mul`.
- **Hypotheses**: `r ≠ 0`.
- **Uses from project**: `ordAtInfty_of_ne`, `normAsRatFunc`, `C.fieldNorm_algebraMap`, `normAsRatFunc_eq_zero_iff`, `ofFractionRing_sq`
- **Used by**: `ordAtInfty_algebraMap_polynomial_of_ne_zero`, `ordAtInfty_coordX`, `ordAtInfty_basis_fracPolyX_of_both_ne_zero`, `ordAtInfty_basis_eq_min`, `ordAtInfty_algebraMap_fracPolyX_add_ge_min`, `ordAtInfty_exists_const_sub_pos_of_fracPolyX_nonneg` (10 uses total)
- **Visibility**: public
- **Lines**: 194–212 (19 lines)
- **Notes**: Key API lemma; used 10 times in this file.

---

### `theorem ordAtInfty_algebraMap_polynomial_of_ne_zero`
- **Type**: For nonzero `p : Polynomial F`, `C.ordAtInfty (algebraMap (Polynomial F) C.FunctionField p) = (-2 * p.natDegree : ℤ)`
- **What**: Order at infinity of a polynomial (via the scalar tower through `FractionRing`) is `-2·natDegree(p)`.
- **How**: Applies `IsScalarTower.algebraMap_apply` to factor through `FractionRing`, then uses `ordAtInfty_algebraMap_fracPolyX_of_ne_zero` + `RatFunc.intDegree_polynomial`.
- **Hypotheses**: `p ≠ 0`.
- **Uses from project**: `ordAtInfty_algebraMap_fracPolyX_of_ne_zero`
- **Used by**: `ordAtInfty_basis_fracPolyX_of_both_ne_zero` (via h_ord_d)
- **Visibility**: public
- **Lines**: 217–232 (16 lines)

---

### `theorem natDegree_norm_smul_basis_of_both_ne_zero`
- **Type**: For nonzero `p, q : Polynomial F`, `(norm (p·1 + q·Y)).natDegree = max(2·natDeg p, 2·natDeg q + 3)`
- **What**: Computes the natDegree of the algebra norm of a basis element `p·1 + q·Y` in `F[C]`: it equals `max(2·deg p, 2·deg q + 3)`.
- **How**: Invokes mathlib's `WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis` and converts from `degree`/`WithBot ℕ` to `natDegree`/`ℕ` via `WithBot.coe_max` + `natDegree_eq_of_degree_eq_some`.
- **Hypotheses**: `p ≠ 0`, `q ≠ 0`.
- **Uses from project**: none (uses mathlib `degree_norm_smul_basis`)
- **Used by**: `ordAtInfty_smul_basis_coordinateRing_of_both_ne_zero`, `ordAtInfty_basis_fracPolyX_of_both_ne_zero`, `q_eq_zero_of_norm_natDeg_zero`
- **Visibility**: public
- **Lines**: 238–267 (30 lines)
- **Notes**: Proof is exactly 30 lines; bridges mathlib's `degree` to `natDegree` in `WithBot`/`ℕ`.

---

### `noncomputable instance coordinateRing_free_over_polynomialX`
- **Type**: `Module.Free (Polynomial F) C.CoordinateRing`
- **What**: The coordinate ring `F[C]` is a free module over `F[X]`, using the basis `{1, Y}`.
- **How**: `Module.Free.of_basis` applied to mathlib's `CoordinateRing.basis`.
- **Hypotheses**: none beyond the curve.
- **Uses from project**: none (uses mathlib basis)
- **Used by**: (supports typeclass resolution for `Algebra.norm` in several proofs)
- **Visibility**: public
- **Lines**: 270–272 (3 lines)

---

### `theorem ordAtInfty_coordX`
- **Type**: `C.ordAtInfty C.coordX = ((-2 : ℤ) : WithTop ℤ)`
- **What**: The coordinate function `x` has order `-2` at infinity (Silverman IV.1).
- **How**: Lifts `coordX` through `FractionRing(F[X])` via `IsScalarTower`, then uses `fieldNorm_algebraMap` (norm = square) + `intDegree_mul` + `intDegree_polynomial` with `natDegree_X = 1`.
- **Uses from project**: `ordAtInfty_of_ne`, `normAsRatFunc`, `C.fieldNorm_algebraMap`, `C.coordX_ne_zero`, `ofFractionRing_sq`, `C.coordX`
- **Used by**: `ordAtInftyValuation_surjective`
- **Visibility**: public
- **Lines**: 276–291 (16 lines)

---

### `private noncomputable def weierstrassCubic`
- **Type**: `Polynomial F` — the polynomial `X³ + a₂X² + a₄X + a₆`
- **What**: The monic cubic from the Weierstrass equation's right-hand side.
- **How**: Direct polynomial expression.
- **Uses from project**: none
- **Used by**: `weierstrassCubic_natDegree`, `weierstrassCubic_ne_zero`, `algebraNorm_coordY_eq`, `ordAtInfty_coordY`
- **Visibility**: private
- **Lines**: 296–298 (3 lines)

---

### `private theorem weierstrassCubic_natDegree`
- **Type**: `C.weierstrassCubic.natDegree = 3`
- **What**: The Weierstrass cubic has degree 3.
- **How**: `compute_degree!`.
- **Uses from project**: `weierstrassCubic`
- **Used by**: `weierstrassCubic_ne_zero`, `ordAtInfty_coordY`
- **Visibility**: private
- **Lines**: 300–302 (3 lines)

---

### `private theorem weierstrassCubic_ne_zero`
- **Type**: `C.weierstrassCubic ≠ 0`
- **What**: The Weierstrass cubic is nonzero.
- **How**: Contradiction via `weierstrassCubic_natDegree` and `Polynomial.natDegree_zero`.
- **Uses from project**: `weierstrassCubic`, `weierstrassCubic_natDegree`
- **Used by**: `algebraNorm_coordY_eq`
- **Visibility**: private
- **Lines**: 304–308 (5 lines)

---

### `private theorem algebraNorm_coordY_eq`
- **Type**: `Algebra.norm (Polynomial F) (CoordinateRing.basis C.toAffine 1) = -C.weierstrassCubic`
- **What**: The algebra norm (over F[X]) of the basis element `Y` (= `basis 1`) equals minus the Weierstrass cubic.
- **How**: Invokes mathlib's `norm_smul_basis` with `p = 0, q = 1` and rearranges with `ring`.
- **Uses from project**: `weierstrassCubic`
- **Used by**: `ordAtInfty_coordY`
- **Visibility**: private
- **Lines**: 313–323 (11 lines)

---

### `theorem ordAtInfty_coordY`
- **Type**: `C.ordAtInfty C.coordY = ((-3 : ℤ) : WithTop ℤ)`
- **What**: The coordinate function `y` has order `-3` at infinity (Silverman IV.1).
- **How**: Uses `Algebra.norm_localization` to reduce to `CoordinateRing`, `algebraNorm_coordY_eq`, and `weierstrassCubic_natDegree`.
- **Uses from project**: `ordAtInfty_of_ne`, `normAsRatFunc`, `C.fieldNorm`, `algebraNorm_coordY_eq`, `weierstrassCubic_natDegree`, `C.coordY_ne_zero`
- **Used by**: `ordAtInfty_coordYInFunctionField`
- **Visibility**: public
- **Lines**: 327–334 (8 lines)

---

### `theorem ordAtInfty_algebraMap_coordinateRing`
- **Type**: For nonzero `u : C.CoordinateRing`, `C.ordAtInfty (algebraMap ... u) = (-(Algebra.norm (Polynomial F) u).natDegree : ℤ)`
- **What**: Order at infinity of a coordinate-ring element is minus the natDegree of its norm.
- **How**: Uses `fieldNorm` factored through `Algebra.norm_localization` + `RatFunc.intDegree_polynomial`.
- **Hypotheses**: `u ≠ 0`.
- **Uses from project**: `ordAtInfty_of_ne`, `normAsRatFunc`, `C.fieldNorm`
- **Used by**: `ordAtInfty_algebraMap_F_nonzero`, `ordAtInfty_smul_basis_coordinateRing_of_both_ne_zero`, `natDegree_zero_of_ordAtInfty_nonneg`
- **Visibility**: public
- **Lines**: 343–352 (10 lines)

---

### `theorem ordAtInfty_algebraMap_F_nonzero`
- **Type**: For nonzero `c : F`, `C.ordAtInfty (algebraMap F C.FunctionField c) = 0`
- **What**: Constants have order 0 at infinity.
- **How**: Lifts through scalar towers to apply `ordAtInfty_algebraMap_coordinateRing`, then computes `Algebra.norm (F[X]) (C c) = (C c)^2` via `Algebra.norm_algebraMap_of_basis` with the `{1,Y}` basis; `natDegree((C c)^2) = 0`.
- **Hypotheses**: `c ≠ 0`.
- **Uses from project**: `ordAtInfty_algebraMap_coordinateRing`
- **Used by**: (not called within this file — used externally)
- **Visibility**: public
- **Lines**: 360–388 (29 lines)

---

### `theorem ordAtInfty_smul_basis_coordinateRing_of_both_ne_zero`
- **Type**: For nonzero `p, q : Polynomial F`, `C.ordAtInfty (algebraMap (p·1 + q·Y)) = (-(max(2·natDeg p, 2·natDeg q+3) : ℕ) : ℤ)`
- **What**: Order at infinity of a coordinate-ring basis element `p·1 + q·Y` is minus the max of the two degree expressions.
- **How**: Combines `natDegree_norm_smul_basis_of_both_ne_zero` with `ordAtInfty_algebraMap_coordinateRing`.
- **Hypotheses**: `p ≠ 0`, `q ≠ 0`.
- **Uses from project**: `natDegree_norm_smul_basis_of_both_ne_zero`, `ordAtInfty_algebraMap_coordinateRing`
- **Used by**: `ordAtInfty_basis_polynomial_of_both_ne_zero`, `ordAtInfty_basis_fracPolyX_of_both_ne_zero`
- **Visibility**: public
- **Lines**: 398–418 (21 lines)

---

### `theorem algebraMap_smul_basis_eq`
- **Type**: `algebraMap C.CoordinateRing C.FunctionField (p·1 + q·mk Y) = algebraMap F[X] K(C) p + algebraMap F[X] K(C) q * C.coordYInFunctionField`
- **What**: Bridges the smul-basis form (in `C.CoordinateRing`) with the additive form (in `C.FunctionField`).
- **How**: Rewrites `smul_def`, `map_add`, `map_mul`, and `IsScalarTower.algebraMap_apply`.
- **Uses from project**: `C.coordYInFunctionField`
- **Used by**: `ordAtInfty_basis_polynomial_of_both_ne_zero`, `ordAtInfty_basis_fracPolyX_of_both_ne_zero` (4 uses total)
- **Visibility**: public
- **Lines**: 424–442 (19 lines)

---

### `theorem ordAtInfty_basis_polynomial_of_both_ne_zero`
- **Type**: For nonzero `p, q : Polynomial F`, `C.ordAtInfty (algebraMap p + algebraMap q * coordY) = (-(max(2·natDeg p, 2·natDeg q+3) : ℕ) : ℤ)`
- **What**: Additive form of the basis-decomposition ord formula.
- **How**: Rewrites via `algebraMap_smul_basis_eq` then applies `ordAtInfty_smul_basis_coordinateRing_of_both_ne_zero`.
- **Hypotheses**: `p ≠ 0`, `q ≠ 0`.
- **Uses from project**: `algebraMap_smul_basis_eq`, `ordAtInfty_smul_basis_coordinateRing_of_both_ne_zero`
- **Used by**: (not called within this file — used externally)
- **Visibility**: public
- **Lines**: 451–458 (8 lines)

---

### `private theorem intDegree_ofFractionRing_eq_of_surj`
- **Type**: Under `r * algebraMap d = algebraMap p`, `(ofFractionRing r).intDegree = natDegree p - natDegree d`
- **What**: Computes `intDegree(r)` from a presentation `r = p/d` via an `IsLocalization.surj` witness. The `intDegree`-vs-polynomial-degree bridge.
- **How**: Explicitly writes `r = (algebraMap p) * (algebraMap d)⁻¹`, uses `intDegree_mul`, `intDegree_inv`, `intDegree_polynomial` twice, then `ring`.
- **Hypotheses**: `p ≠ 0`, `d ≠ 0`, and the surjectivity relation `r * algebraMap d = algebraMap p`.
- **Uses from project**: none
- **Used by**: `ordAtInfty_basis_fracPolyX_of_both_ne_zero` (called twice)
- **Visibility**: private
- **Lines**: 464–501 (38 lines)
- **Notes**: Long proof (38 lines); boilerplate for FractionRing presentation arithmetic.

---

### `theorem ordAtInfty_basis_fracPolyX_of_both_ne_zero`
- **Type**: For nonzero `r₁, r₂ : FractionRing F[X]`, `C.ordAtInfty (algebraMap r₁ + algebraMap r₂ * coordY) = min(-2·intDeg r₁, -2·intDeg r₂ - 3)`
- **What**: The order at infinity of `r₁ + r₂·y` (with `F(X)` coefficients) is the minimum of the two component orders — the non-archimedean formula at the `K`-coefficient level. Parity ensures the minimum is always achieved.
- **How**: Localises via `IsLocalization.surj` to get polynomial representatives, reduces to the polynomial basis formula `ordAtInfty_smul_basis_coordinateRing_of_both_ne_zero`, and uses `intDegree_ofFractionRing_eq_of_surj` twice for an arithmetic rearrangement closing via `WithTop.add_left_cancel`.
- **Hypotheses**: `r₁ ≠ 0`, `r₂ ≠ 0`.
- **Uses from project**: `ordAtInfty_smul_basis_coordinateRing_of_both_ne_zero`, `natDegree_norm_smul_basis_of_both_ne_zero`, `algebraMap_smul_basis_eq`, `ordAtInfty_algebraMap_polynomial_of_ne_zero`, `ordAtInfty_mul`, `intDegree_ofFractionRing_eq_of_surj`
- **Used by**: `ordAtInfty_basis_eq_min`
- **Visibility**: public
- **Lines**: 510–661 (152 lines)
- **Notes**: Longest proof in file (152 lines). The main non-archimedean computation at FractionRing-coefficient level.

---

### `theorem coordY_eq_coordYInFunctionField`
- **Type**: `C.coordY = C.coordYInFunctionField`
- **What**: Identifies `coordY` (from `CoordinateRing`) with `coordYInFunctionField` (from the function field).
- **How**: `unfold` + `congr 1` + `CoordinateRing.basis_one`.
- **Uses from project**: `C.coordY`, `C.coordYInFunctionField`
- **Used by**: `coordYInFunctionField_ne_zero`, `ordAtInfty_coordYInFunctionField`
- **Visibility**: public
- **Lines**: 666–669 (4 lines)

---

### `theorem coordYInFunctionField_ne_zero`
- **Type**: `C.coordYInFunctionField ≠ 0`
- **What**: `coordYInFunctionField` is nonzero.
- **How**: Uses `coordY_eq_coordYInFunctionField` + `C.coordY_ne_zero`.
- **Uses from project**: `coordY_eq_coordYInFunctionField`, `C.coordY_ne_zero`
- **Used by**: `ordAtInfty_basis_eq_min`
- **Visibility**: public
- **Lines**: 672–673 (2 lines)

---

### `@[simp] theorem ordAtInfty_coordYInFunctionField`
- **Type**: `C.ordAtInfty C.coordYInFunctionField = ((-3 : ℤ) : WithTop ℤ)`
- **What**: `ord_∞(y) = -3` for `coordYInFunctionField`.
- **How**: Renames via `coordY_eq_coordYInFunctionField` and applies `ordAtInfty_coordY`.
- **Uses from project**: `coordY_eq_coordYInFunctionField`, `ordAtInfty_coordY`
- **Used by**: `ordAtInfty_basis_eq_min`, `ordAtInfty_add_ge_min`
- **Visibility**: public
- **Lines**: 676–678 (3 lines)

---

### `theorem ordAtInfty_basis_eq_min`
- **Type**: `C.ordAtInfty (algebraMap r₁ + algebraMap r₂ * coordY) = min (ordAtInfty(algebraMap r₁)) (ordAtInfty(algebraMap r₂) + ordAtInfty(coordY))`
- **What**: Unified basis decomposition for `ordAtInfty` handling zero coefficients via case splits. The non-archimedean min formula for the full F(X)-coefficient basis.
- **How**: Four cases (r₁=0, r₂=0, both, neither); the "both nonzero" case uses `ordAtInfty_basis_fracPolyX_of_both_ne_zero` + arithmetic to convert `min` expressions. `WithTop.coe_add` for the cast.
- **Hypotheses**: none (handles all cases).
- **Uses from project**: `ordAtInfty_mul`, `ordAtInfty_zero`, `coordYInFunctionField_ne_zero`, `ordAtInfty_coordYInFunctionField`, `ordAtInfty_basis_fracPolyX_of_both_ne_zero`, `ordAtInfty_algebraMap_fracPolyX_of_ne_zero`
- **Used by**: `ordAtInfty_add_ge_min` (5 times total)
- **Visibility**: public
- **Lines**: 684–726 (43 lines)
- **Notes**: Long proof (43 lines); key "min" formula for non-archimedean inequality.

---

### `theorem ordAtInfty_algebraMap_fracPolyX_add_ge_min`
- **Type**: `min(ord(algebraMap p), ord(algebraMap q)) ≤ ord(algebraMap(p+q))`
- **What**: Non-archimedean inequality for F(X)-level elements lifted to F(C): the min of the orders is at most the order of the sum.
- **How**: Case splits on p, q, p+q being zero. For the all-nonzero case, uses `RatFunc.intDegree_add_le` from mathlib and arithmetic on the `-2·intDegree` formula.
- **Hypotheses**: none (handles zeros).
- **Uses from project**: `ordAtInfty_algebraMap_fracPolyX_of_ne_zero`, `ordAtInfty_zero`
- **Used by**: `ordAtInfty_add_ge_min` (called for both α and β components)
- **Visibility**: public
- **Lines**: 734–795 (62 lines)
- **Notes**: Long proof (62 lines); bridges F(X) non-archimedean inequality to F(C).

---

### `theorem ordAtInfty_add_ge_min`
- **Type**: `min(C.ordAtInfty f, C.ordAtInfty g) ≤ C.ordAtInfty (f + g)`
- **What**: Non-archimedean inequality for `ordAtInfty` on `F(C)`: `min(ord f, ord g) ≤ ord(f+g)`.
- **How**: Decomposes `f, g, f+g` via `exists_decomp` into basis form, applies `ordAtInfty_basis_eq_min` for each, and combines the F(X)-level non-archimedean from `ordAtInfty_algebraMap_fracPolyX_add_ge_min` via lattice manipulations.
- **Hypotheses**: none.
- **Uses from project**: `C.exists_decomp`, `ordAtInfty_basis_eq_min`, `ordAtInfty_algebraMap_fracPolyX_add_ge_min`, `ordAtInfty_coordYInFunctionField`
- **Used by**: `ordAtInfty_sub_ge_min`, `ordAtInfty_add_eq_of_lt`, `ordAtInftyVal_add_le_max`
- **Visibility**: public
- **Lines**: 803–875 (73 lines)
- **Notes**: Long proof (73 lines); the main non-archimedean inequality for F(C).

---

### `theorem ordAtInfty_sub_ge_min`
- **Type**: `min(C.ordAtInfty f, C.ordAtInfty g) ≤ C.ordAtInfty (f - g)`
- **What**: Non-archimedean inequality for subtraction.
- **How**: Rewrites `f - g = f + (-g)` and uses `ordAtInfty_neg` + `ordAtInfty_add_ge_min`.
- **Uses from project**: `ordAtInfty_neg`, `ordAtInfty_add_ge_min`
- **Used by**: `ordAtInfty_sub_eq_of_lt`
- **Visibility**: public
- **Lines**: 878–881 (4 lines)

---

### `theorem ordAtInfty_add_eq_of_lt`
- **Type**: `(h : C.ordAtInfty f < C.ordAtInfty g) → C.ordAtInfty (f + g) = C.ordAtInfty f`
- **What**: Strict non-archimedean: when `ord f < ord g`, the dominant term wins and `ord(f+g) = ord f`.
- **How**: Lower bound `ord(f+g) ≥ ord f` from `ordAtInfty_add_ge_min`; upper bound from re-applying the inequality to `(f+g) + (-g) = f`, concluding by contradiction or antisymmetry.
- **Hypotheses**: `C.ordAtInfty f < C.ordAtInfty g`.
- **Uses from project**: `ordAtInfty_add_ge_min`, `ordAtInfty_neg`
- **Used by**: `ordAtInfty_sub_eq_of_lt`
- **Visibility**: public
- **Lines**: 890–903 (14 lines)

---

### `theorem ordAtInfty_sub_eq_of_lt`
- **Type**: `(h : C.ordAtInfty f < C.ordAtInfty g) → C.ordAtInfty (f - g) = C.ordAtInfty f`
- **What**: Strict non-archimedean for subtraction.
- **How**: Rewrites via `sub_eq_add_neg`, applies `ordAtInfty_neg` + `ordAtInfty_add_eq_of_lt`.
- **Uses from project**: `ordAtInfty_neg`, `ordAtInfty_add_eq_of_lt`
- **Used by**: (not called within this file)
- **Visibility**: public
- **Lines**: 906–911 (6 lines)

---

### `private theorem intDegree_algebraMap_div_algebraMap`
- **Type**: For nonzero `a, b : Polynomial F`, `(algebraMap a / algebraMap b).intDegree = natDegree a - natDegree b`
- **What**: The `intDegree` of a rational function presented as `p/q` (in `RatFunc F`) is `natDegree p - natDegree q`.
- **How**: Rewrites `div = mul * inv`, uses `intDegree_mul`, `intDegree_inv`, `intDegree_polynomial` twice, then `ring`.
- **Uses from project**: none
- **Used by**: `ratFunc_exists_C_sub_intDegree_neg`
- **Visibility**: private
- **Lines**: 924–935 (12 lines)

---

### `private theorem ratFunc_exists_C_sub_intDegree_neg`
- **Type**: If `r.intDegree ≤ 0`, then `∃ lam : F, r - C lam = 0 ∨ (r - C lam).intDegree < 0`
- **What**: The "value at ∞" of a rational function with `intDegree ≤ 0`: there exists a constant `lam` (ratio of leading coefficients) such that `r - C lam` is zero or has strictly negative `intDegree`. This is the residue at the place at infinity of `ℙ¹_F`.
- **How**: Uses `RatFunc.num`, `RatFunc.denom`, splits on `natDeg(num) < natDeg(den)` vs `=`; in the equal case takes `lam = leadingCoeff(num)/leadingCoeff(den)` and shows cancellation of leading terms via `Polynomial.degree_sub_lt`.
- **Hypotheses**: `r.intDegree ≤ 0`.
- **Uses from project**: `intDegree_algebraMap_div_algebraMap`
- **Used by**: `ordAtInfty_exists_const_sub_pos_of_fracPolyX_nonneg`
- **Visibility**: private
- **Lines**: 943–993 (51 lines)
- **Notes**: Long proof (51 lines).

---

### `theorem ordAtInfty_exists_const_sub_pos_of_fracPolyX_nonneg`
- **Type**: If `0 ≤ C.ordAtInfty (algebraMap r₀)` then `∃ lam : F, 0 < C.ordAtInfty (algebraMap r₀ - algebraMap_F lam)`
- **What**: For a regular-at-∞ element `r₀ ∈ F(X)` (viewed in F(C)), there exists a constant `lam` such that subtracting it gives strictly positive order at infinity.
- **How**: Converts `0 ≤ ordAtInfty` to `intDegree ≤ 0` using `ordAtInfty_algebraMap_fracPolyX_of_ne_zero`, applies `ratFunc_exists_C_sub_intDegree_neg`, then converts the negative `intDegree` back via `ordAtInfty_algebraMap_fracPolyX_of_ne_zero`.
- **Hypotheses**: `0 ≤ C.ordAtInfty (algebraMap ... r₀)`.
- **Uses from project**: `ordAtInfty_algebraMap_fracPolyX_of_ne_zero`, `ordAtInfty_zero`, `ratFunc_exists_C_sub_intDegree_neg`
- **Used by**: (not called within this file — used externally)
- **Visibility**: public
- **Lines**: 1001–1060 (60 lines)
- **Notes**: Long proof (60 lines).

---

### `noncomputable def ordAtInftyVal`
- **Type**: `(f : C.FunctionField) → WithZero (Multiplicative ℤ)`
- **What**: The multiplicative value `exp(-ordAtInfty f)` at infinity: `0 ↦ 0`, and for nonzero `f`, `WithZero.exp(intDegree(N(f)))`.
- **How**: Conditional on `f = 0`.
- **Uses from project**: `normAsRatFunc`
- **Used by**: `ordAtInftyVal_eq_exp_neg_ordAtInfty`, `ordAtInftyVal_zero`, `ordAtInftyVal_ne_zero`, `ordAtInftyVal_one`, `ordAtInftyVal_mul`, `ordAtInftyVal_add_le_max`, `ordAtInftyValuation`
- **Visibility**: public
- **Lines**: 1075–1077 (3 lines)

---

### `theorem ordAtInftyVal_eq_exp_neg_ordAtInfty`
- **Type**: `(hf : f ≠ 0) (hn : C.ordAtInfty f = n) → C.ordAtInftyVal f = WithZero.exp (-n)`
- **What**: Bridge lemma: for nonzero `f` with known ord value `n`, the multiplicative val is `exp(-n)`.
- **How**: Uses `ordAtInfty_of_ne` to identify `n = -intDegree(N(f))`, then `neg_neg`.
- **Hypotheses**: `f ≠ 0`, `C.ordAtInfty f = n`.
- **Uses from project**: `ordAtInftyVal`, `ordAtInfty_of_ne`
- **Used by**: `ordAtInftyVal_one`, `ordAtInftyVal_mul`, `ordAtInftyVal_add_le_max`, `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`, `ordAtInftyValuation_le_one_iff_ordAtInfty_nonneg`, `ordAtInftyValuation_surjective` (8 uses)
- **Visibility**: public
- **Lines**: 1078–1086 (9 lines)
- **Notes**: Key bridge; used 8 times in this file.

---

### `@[simp] theorem ordAtInftyVal_zero`
- **Type**: `C.ordAtInftyVal 0 = 0`
- **What**: Multiplicative val of 0 is 0.
- **How**: `if_pos rfl`.
- **Uses from project**: `ordAtInftyVal`
- **Used by**: `ordAtInftyVal_add_le_max`, `ordAtInftyValuation`
- **Visibility**: public
- **Lines**: 1088 (1 line)

---

### `theorem ordAtInftyVal_ne_zero`
- **Type**: `(hf : f ≠ 0) → C.ordAtInftyVal f ≠ 0`
- **What**: For nonzero `f`, the multiplicative val is nonzero.
- **How**: Direct from `if_neg hf` + `WithZero.exp_ne_zero`.
- **Uses from project**: `ordAtInftyVal`
- **Used by**: `ordAtInftyValuation_ne_zero`
- **Visibility**: public
- **Lines**: 1090–1092 (3 lines)

---

### `@[simp] theorem ordAtInftyVal_one`
- **Type**: `C.ordAtInftyVal (1 : C.FunctionField) = 1`
- **What**: Multiplicative val of 1 is 1.
- **How**: `ordAtInftyVal_eq_exp_neg_ordAtInfty` with `ordAtInfty_one`, then `WithZero.exp_zero`.
- **Uses from project**: `ordAtInftyVal_eq_exp_neg_ordAtInfty`, `ordAtInfty_one`
- **Used by**: `ordAtInftyValuation`
- **Visibility**: public
- **Lines**: 1094–1096 (3 lines)

---

### `theorem ordAtInftyVal_mul`
- **Type**: `C.ordAtInftyVal (f * g) = C.ordAtInftyVal f * C.ordAtInftyVal g`
- **What**: Multiplicativity of `ordAtInftyVal`.
- **How**: Case splits on `f = 0` or `g = 0`; for both nonzero, uses `ordAtInftyVal_eq_exp_neg_ordAtInfty` with `ordAtInfty_mul`, then `neg_add` + `WithZero.exp_add`.
- **Uses from project**: `ordAtInftyVal_eq_exp_neg_ordAtInfty`, `ordAtInfty_of_ne`, `ordAtInfty_mul`
- **Used by**: `ordAtInftyValuation`
- **Visibility**: public
- **Lines**: 1098–1113 (16 lines)

---

### `theorem ordAtInftyVal_add_le_max`
- **Type**: `C.ordAtInftyVal (f + g) ≤ max (C.ordAtInftyVal f) (C.ordAtInftyVal g)`
- **What**: Ultrametric property of the multiplicative val: val(f+g) ≤ max(val f, val g).
- **How**: Converts to `WithZero.exp` form, applies `ordAtInfty_add_ge_min` (min of ords ≤ ord of sum), then translates to `exp` order comparison via `le_max_iff` and `WithZero.exp_le_exp`.
- **Uses from project**: `ordAtInftyVal_zero`, `ordAtInftyVal_eq_exp_neg_ordAtInfty`, `ordAtInfty_of_ne`, `ordAtInfty_add_ge_min`
- **Used by**: `ordAtInftyValuation`
- **Visibility**: public
- **Lines**: 1115–1145 (31 lines)
- **Notes**: Proof is 31 lines (just over threshold).

---

### `noncomputable def ordAtInftyValuation`
- **Type**: `Valuation C.FunctionField (WithZero (Multiplicative ℤ))`
- **What**: Packages `ordAtInftyVal` as a `Valuation` using the multiplicative structure proven above.
- **How**: Structure fields `toFun := ordAtInftyVal`, `map_zero' := ordAtInftyVal_zero`, etc.
- **Uses from project**: `ordAtInftyVal`, `ordAtInftyVal_zero`, `ordAtInftyVal_one`, `ordAtInftyVal_mul`, `ordAtInftyVal_add_le_max`
- **Used by**: `ordAtInftyValuation_apply`, `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`, `ordAtInftyValuation_surjective`, `ordAtInftyValuation_ne_zero`, `ordAtInftyValuation_le_one_iff_ordAtInfty_nonneg`, `ordAtInftyValuation_le_one_of_ordAtInfty_nonneg`
- **Visibility**: public
- **Lines**: 1149–1155 (7 lines)

---

### `@[simp] theorem ordAtInftyValuation_apply`
- **Type**: `C.ordAtInftyValuation f = C.ordAtInftyVal f`
- **What**: Unfolds the `Valuation` apply.
- **How**: `rfl`.
- **Uses from project**: `ordAtInftyValuation`, `ordAtInftyVal`
- **Used by**: `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`, `ordAtInftyValuation_ne_zero`, `ordAtInftyValuation_le_one_iff_ordAtInfty_nonneg`, `ordAtInftyValuation_le_one_of_ordAtInfty_nonneg`
- **Visibility**: public
- **Lines**: 1157–1158 (2 lines)

---

### `theorem ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`
- **Type**: For nonzero `f` with `C.ordAtInfty f = n`, `C.ordAtInftyValuation f = WithZero.exp (-n)`
- **What**: Bridge for the `Valuation`-packaged version.
- **How**: `ordAtInftyValuation_apply` + `ordAtInftyVal_eq_exp_neg_ordAtInfty`.
- **Uses from project**: `ordAtInftyValuation_apply`, `ordAtInftyVal_eq_exp_neg_ordAtInfty`
- **Used by**: `ordAtInftyValuation_surjective`, `ordAtInftyValuation_le_one_iff_ordAtInfty_nonneg`
- **Visibility**: public
- **Lines**: 1162–1165 (4 lines)

---

### `theorem ordAtInftyValuation_surjective`
- **Type**: `Function.Surjective C.ordAtInftyValuation`
- **What**: The valuation at infinity is surjective onto `ℤᵐ⁰`. The uniformizer is `t := coordY / coordX` which has order `-1`, so every integer power of exp(1) is achieved.
- **How**: Uses `ordAtInfty_div_eq_mul_inv` + `ordAtInfty_inv` + `ordAtInfty_coordX` + `ordAtInfty_coordY` to compute `ordAtInfty t = -1`; then `map_zpow₀`, `WithZero.exp_zsmul`, `WithZero.exp_log`.
- **Uses from project**: `ordAtInfty_div_eq_mul_inv`, `ordAtInfty_inv`, `ordAtInfty_coordX`, `ordAtInfty_coordY`, `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`, `ordAtInftyValuation`
- **Used by**: (not called within this file)
- **Visibility**: public
- **Lines**: 1170–1194 (25 lines)

---

### `theorem ordAtInftyValuation_ne_zero`
- **Type**: `(hf : f ≠ 0) → C.ordAtInftyValuation f ≠ 0`
- **What**: For nonzero `f`, the valuation is nonzero.
- **How**: `ordAtInftyValuation_apply` + `ordAtInftyVal_ne_zero`.
- **Uses from project**: `ordAtInftyVal_ne_zero`
- **Used by**: (not called within this file)
- **Visibility**: public
- **Lines**: 1196–1197 (2 lines)

---

### `theorem ordAtInftyValuation_le_one_iff_ordAtInfty_nonneg`
- **Type**: `(hf : f ≠ 0) → C.ordAtInftyValuation f ≤ 1 ↔ 0 ≤ C.ordAtInfty f`
- **What**: Integrality bridge: the valuation is ≤ 1 iff the order at infinity is ≥ 0 (no pole at ∞).
- **How**: Reduces both sides to `exp(-n) ≤ exp(0)` via `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`, then `WithZero.exp_le_exp` and cast comparison.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`, `ordAtInfty_of_ne`
- **Used by**: `ordAtInftyValuation_le_one_of_ordAtInfty_nonneg`
- **Visibility**: public
- **Lines**: 1202–1211 (10 lines)

---

### `theorem ordAtInftyValuation_le_one_of_ordAtInfty_nonneg`
- **Type**: `(hf : f ≠ 0) (h : 0 ≤ C.ordAtInfty f) → C.ordAtInftyValuation f ≤ 1`
- **What**: One direction of the integrality bridge.
- **How**: Direct from `ordAtInftyValuation_le_one_iff_ordAtInfty_nonneg`.
- **Uses from project**: `ordAtInftyValuation_le_one_iff_ordAtInfty_nonneg`
- **Used by**: (not called within this file)
- **Visibility**: public
- **Lines**: 1213–1216 (4 lines)

---

### `theorem ordAtInfty_div_of_ord_eq`
- **Type**: Given `ord a = m`, `ord b = n`, `b ≠ 0`, then `ord(a/b) = m - n`
- **What**: Closed-form ord of a quotient given known integer ord values.
- **How**: Uses `ordAtInfty_div_eq_mul_inv`, `ordAtInfty_inv`, and `WithTop.coe_add` for arithmetic.
- **Hypotheses**: `b ≠ 0`, `ord a = m`, `ord b = n`.
- **Uses from project**: `ordAtInfty_div_eq_mul_inv`, `ordAtInfty_inv`, `ordAtInfty_zero`
- **Used by**: (not called within this file)
- **Visibility**: public
- **Lines**: 1222–1236 (15 lines)

---

### `theorem ordAtInfty_pow_of_ord_eq`
- **Type**: Given `hf : f ≠ 0`, `ord f = m`, then `ord(f^n) = n * m`
- **What**: Closed-form ord of a power given the known integer ord value.
- **How**: Uses `ordAtInfty_pow` + induction on `n` with `succ_nsmul` and `WithTop.coe_add`.
- **Hypotheses**: `f ≠ 0`, `ord f = m`.
- **Uses from project**: `ordAtInfty_pow`
- **Used by**: (not called within this file)
- **Visibility**: public
- **Lines**: 1240–1251 (12 lines)

---

### `private theorem natDegree_zero_of_ordAtInfty_nonneg`
- **Type**: If `0 ≤ C.ordAtInfty (algebraMap u)` and `u ≠ 0`, then `(Algebra.norm u).natDegree = 0`
- **What**: Bridge: nonneg order at infinity for a coordinate-ring element forces norm degree zero.
- **How**: Applies `ordAtInfty_algebraMap_coordinateRing` and uses WithTop integer comparison.
- **Uses from project**: `ordAtInfty_algebraMap_coordinateRing`
- **Used by**: `coordinateRing_const_of_ordAtInfty_nonneg`
- **Visibility**: private
- **Lines**: 1255–1266 (12 lines)

---

### `private theorem q_eq_zero_of_norm_natDeg_zero`
- **Type**: If `norm(p·1 + q·Y) ≠ 0` and `natDegree(norm(p·1 + q·Y)) = 0`, then `q = 0`
- **What**: The q-coefficient vanishes when the norm has degree 0: parity argument from `degree_norm_smul_basis`.
- **How**: Uses `degree_norm_smul_basis` + contradiction from `2·natDeg q + 3 ≤ 0` via `omega`.
- **Uses from project**: (uses mathlib's `WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis`)
- **Used by**: `coordinateRing_const_of_ordAtInfty_nonneg`
- **Visibility**: private
- **Lines**: 1268–1294 (27 lines)

---

### `theorem coordinateRing_const_of_ordAtInfty_nonneg`
- **Type**: If `0 ≤ C.ordAtInfty (algebraMap u)`, then `∃ c : F, u = algebraMap F C.CoordinateRing c`
- **What**: Algebraic Liouville for the coordinate ring: an element with nonneg ord at infinity is constant.
- **How**: Uses `natDegree_zero_of_ordAtInfty_nonneg`, then `q_eq_zero_of_norm_natDeg_zero` to force `q = 0`, then from `p·1` having degree 0 concludes `p` is a constant polynomial.
- **Uses from project**: `natDegree_zero_of_ordAtInfty_nonneg`, `q_eq_zero_of_norm_natDeg_zero`
- **Used by**: `const_of_no_poles_of_coordinateRing`, `const_of_no_poles_of_valuation_of_ordAtInfty`, `const_of_isIntegral_polynomialX_of_ordAtInfty` (2 internal uses via `const_of_no_poles_of_coordinateRing`)
- **Visibility**: public
- **Lines**: 1299–1330 (32 lines)
- **Notes**: Long proof (32 lines).

---

### `private noncomputable def fiberQuadratic`
- **Type**: `(a : F) → Polynomial F` — the quadratic `Y² + (a₁a+a₃)Y - (a³+a₂a²+a₄a+a₆)`
- **What**: The polynomial in `Y` obtained by specializing the Weierstrass equation at `X = a`. Roots correspond to `y`-coordinates of smooth points above `x = a`.
- **How**: Direct polynomial expression.
- **Uses from project**: none
- **Used by**: `fiberQuadratic_natDegree`, `fiberQuadratic_ne_zero`, `fiberQuadratic_isRoot_of_smoothPoint`, `smoothPoint_x_preimage_finite`
- **Visibility**: private
- **Lines**: 1335–1338 (4 lines)

---

### `private theorem fiberQuadratic_natDegree`
- **Type**: `(C.fiberQuadratic a).natDegree = 2`
- **What**: The fiber quadratic has degree 2.
- **How**: `compute_degree!`.
- **Uses from project**: `fiberQuadratic`
- **Used by**: `fiberQuadratic_ne_zero`, `smoothPoint_x_preimage_finite`
- **Visibility**: private
- **Lines**: 1340–1342 (3 lines)

---

### `private theorem fiberQuadratic_ne_zero`
- **Type**: `C.fiberQuadratic a ≠ 0`
- **What**: The fiber quadratic is nonzero.
- **How**: Contradiction via `fiberQuadratic_natDegree`.
- **Uses from project**: `fiberQuadratic`, `fiberQuadratic_natDegree`
- **Used by**: `smoothPoint_x_preimage_finite`
- **Visibility**: private
- **Lines**: 1344–1348 (5 lines)

---

### `private theorem fiberQuadratic_isRoot_of_smoothPoint`
- **Type**: If `P.x = a`, then `(C.fiberQuadratic a).IsRoot P.y`
- **What**: The y-coordinate of a smooth point above `x = a` is a root of the fiber quadratic.
- **How**: Uses `P.nonsingular.1` (the Weierstrass equation), `equation_iff'`, `Polynomial.IsRoot`, and `linear_combination`.
- **Uses from project**: `fiberQuadratic`
- **Used by**: `smoothPoint_x_preimage_finite`
- **Visibility**: private
- **Lines**: 1350–1357 (8 lines)

---

### `theorem smoothPoint_x_preimage_finite`
- **Type**: `{P : C.SmoothPoint | P.x = a}.Finite`
- **What**: The x-projection has finite fibers: at most finitely many smooth points have the same x-coordinate (at most 2, being roots of the fiber quadratic).
- **How**: `Set.Finite.of_injOn`: injects via `P.y` into the finite root set of `fiberQuadratic a`, using `Polynomial.finite_setOf_isRoot` and `SmoothPoint.ext`.
- **Uses from project**: `fiberQuadratic`, `fiberQuadratic_ne_zero`, `fiberQuadratic_isRoot_of_smoothPoint`
- **Used by**: `smoothPoint_x_preimage_finite_of_set`
- **Visibility**: public
- **Lines**: 1364–1371 (8 lines)

---

### `theorem smoothPoint_x_preimage_finite_of_set`
- **Type**: `(hs : s.Finite) → {P : C.SmoothPoint | P.x ∈ s}.Finite`
- **What**: Preimage of a finite set of `x`-values is finite.
- **How**: Rewrites the set as `⋃ a ∈ s, {P | P.x = a}` and uses `Set.Finite.biUnion` with `smoothPoint_x_preimage_finite`.
- **Hypotheses**: `s.Finite`.
- **Uses from project**: `smoothPoint_x_preimage_finite`
- **Used by**: `finite_setOf_mem_maximalIdealAt`
- **Visibility**: public
- **Lines**: 1377–1382 (6 lines)

---

### `private noncomputable def coordEval`
- **Type**: `(P : C.SmoothPoint) → C.CoordinateRing →+* F`
- **What**: The evaluation ring hom at a smooth point `P`, extending `eval P.x : F[X] → F` along the adjoined root `Y ↦ P.y`. This is the "value at P" on the coordinate ring.
- **How**: `AdjoinRoot.lift (evalRingHom P.x) P.y` using `P.nonsingular.1` for the root condition.
- **Uses from project**: none (uses mathlib `AdjoinRoot.lift`)
- **Used by**: `coordEval_mk`, `coordEval_smul_basis`, `XClass_mem_ker_coordEval`, `YClass_mem_ker_coordEval`, `maximalIdealAt_le_ker_coordEval`, `ker_coordEval_ne_top`, `ker_coordEval_eq`
- **Visibility**: private
- **Lines**: 1389–1392 (4 lines)

---

### `private theorem coordEval_mk`
- **Type**: `C.coordEval P (mk g) = g.evalEval P.x P.y`
- **What**: The evaluation of a `CoordinateRing.mk g` under `coordEval P` equals double-evaluation.
- **How**: `AdjoinRoot.lift_mk` + `Polynomial.eval₂_evalRingHom`.
- **Uses from project**: `coordEval`
- **Used by**: `coordEval_smul_basis`, `XClass_mem_ker_coordEval`, `YClass_mem_ker_coordEval`
- **Visibility**: private
- **Lines**: 1394–1401 (8 lines)

---

### `private theorem coordEval_smul_basis`
- **Type**: `C.coordEval P (p·1 + q·mk Y) = eval P.x p + eval P.x q * P.y`
- **What**: Evaluates a basis element `p·1 + q·Y` at `P` using `coordEval`.
- **How**: Rewrites using `Algebra.smul_def` + `coordEval_mk` + `Polynomial.evalEval_*`.
- **Uses from project**: `coordEval`, `coordEval_mk`
- **Used by**: `maximalIdealAt_le_ker_coordEval` (via `XClass`/`YClass`), `mem_maximalIdealAt_iff_eval_zero`
- **Visibility**: private
- **Lines**: 1403–1416 (14 lines)

---

### `private theorem XClass_mem_ker_coordEval`
- **Type**: `CoordinateRing.XClass C.toAffine P.x ∈ RingHom.ker (C.coordEval P)`
- **What**: The element `x - P.x` (XClass) is in the kernel of `coordEval P`.
- **How**: `coordEval_mk` + `evalEval_C` simp.
- **Uses from project**: `coordEval`, `coordEval_mk`
- **Used by**: `maximalIdealAt_le_ker_coordEval`
- **Visibility**: private
- **Lines**: 1418–1423 (6 lines)

---

### `private theorem YClass_mem_ker_coordEval`
- **Type**: `CoordinateRing.YClass C.toAffine (C P.y) ∈ RingHom.ker (C.coordEval P)`
- **What**: The element `y - P.y` (YClass) is in the kernel of `coordEval P`.
- **How**: `coordEval_mk` + `evalEval_*` simp.
- **Uses from project**: `coordEval`, `coordEval_mk`
- **Used by**: `maximalIdealAt_le_ker_coordEval`
- **Visibility**: private
- **Lines**: 1425–1430 (6 lines)

---

### `private theorem maximalIdealAt_le_ker_coordEval`
- **Type**: `C.maximalIdealAt P ≤ RingHom.ker (C.coordEval P)`
- **What**: The maximal ideal at P is contained in the kernel of the evaluation.
- **How**: Shows the generators `XClass` and `YClass` are in the kernel via `XClass_mem_ker_coordEval` and `YClass_mem_ker_coordEval`.
- **Uses from project**: `coordEval`, `C.maximalIdealAt`, `XClass_mem_ker_coordEval`, `YClass_mem_ker_coordEval`
- **Used by**: `ker_coordEval_eq`
- **Visibility**: private
- **Lines**: 1432–1439 (8 lines)

---

### `private theorem ker_coordEval_ne_top`
- **Type**: `RingHom.ker (C.coordEval P) ≠ ⊤`
- **What**: The kernel of `coordEval P` is proper (since `evalRingHom` sends 1 to 1 ≠ 0).
- **How**: `Ideal.eq_top_iff_one`, `map_one`, `one_ne_zero`.
- **Uses from project**: `coordEval`
- **Used by**: `ker_coordEval_eq`
- **Visibility**: private
- **Lines**: 1441–1444 (4 lines)

---

### `private theorem ker_coordEval_eq`
- **Type**: `RingHom.ker (C.coordEval P) = C.maximalIdealAt P`
- **What**: The kernel of `coordEval P` equals the maximal ideal at P.
- **How**: Uses `maximalIdealAt_isMaximal` and `eq_of_le` (maximality forces the reverse inclusion).
- **Uses from project**: `C.maximalIdealAt_isMaximal`, `ker_coordEval_ne_top`, `maximalIdealAt_le_ker_coordEval`, `C.maximalIdealAt`
- **Used by**: `mem_maximalIdealAt_iff_eval_zero`
- **Visibility**: private
- **Lines**: 1446–1449 (4 lines)

---

### `theorem mem_maximalIdealAt_iff_eval_zero`
- **Type**: `(p·1 + q·mk Y) ∈ C.maximalIdealAt P ↔ eval P.x p + eval P.x q * P.y = 0`
- **What**: Scheme-theoretic membership characterization: an element vanishes in the maximal ideal at P if and only if it evaluates to 0 at P. The D-004 missing bridge.
- **How**: `ker_coordEval_eq P` + `RingHom.mem_ker` + `coordEval_smul_basis`.
- **Uses from project**: `ker_coordEval_eq`, `coordEval_smul_basis`, `C.maximalIdealAt`
- **Used by**: `finite_setOf_mem_maximalIdealAt`
- **Visibility**: public
- **Lines**: 1455–1461 (7 lines)

---

### `theorem norm_eval_at_x_of_zero_at_smoothPoint`
- **Type**: If `eval P.x p + eval P.x q * P.y = 0`, then `(norm(p·1+q·Y)).eval P.x = 0`
- **What**: Bezout counting algebraic identity: vanishing at P implies the norm polynomial has P.x as a root. The core computation behind finiteness of zeros.
- **How**: Uses the Weierstrass equation `P.nonsingular.1`, expands `norm_smul_basis`, and closes with `linear_combination`.
- **Uses from project**: none (uses mathlib `norm_smul_basis`)
- **Used by**: `finite_setOf_mem_maximalIdealAt`
- **Visibility**: public
- **Lines**: 1471–1483 (13 lines)

---

### `theorem pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`
- **Type**: `C.pointValuation P (algebraMap u) < 1 ↔ u ∈ C.maximalIdealAt P`
- **What**: Valuation < 1 at P iff the coordinate-ring element is in the maximal ideal at P.
- **How**: Uses `Localization.AtPrime.comap_maximalIdeal` and `HeightOneSpectrum.valuation_lt_one_iff_mem`.
- **Uses from project**: `C.pointValuation`, `C.maximalIdealAt`, `C.localRingAt`
- **Used by**: `ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt`
- **Visibility**: public
- **Lines**: 1491–1502 (12 lines)

---

### `theorem pointValuation_algebraMap_le_one`
- **Type**: `C.pointValuation P (algebraMap u) ≤ 1`
- **What**: The valuation of a coordinate-ring element is always ≤ 1 (no pole at affine points).
- **How**: Direct from `IsDedekindDomain.HeightOneSpectrum.valuation_le_one`.
- **Uses from project**: `C.pointValuation`, `C.localRingAt`
- **Used by**: `ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt`
- **Visibility**: public
- **Lines**: 1506–1512 (7 lines)

---

### `theorem pointValuation_algebraMap_localRingAt_le_one`
- **Type**: `C.pointValuation P (algebraMap (C.localRingAt P) C.FunctionField x) ≤ 1`
- **What**: Step (B'') easy direction: every local-ring element has valuation ≤ 1 at P.
- **How**: Direct from `IsDedekindDomain.HeightOneSpectrum.valuation_le_one` at the DVR level.
- **Uses from project**: `C.pointValuation`, `C.localRingAt`
- **Used by**: `mem_localRingAt_image_iff_pointValuation_le_one`
- **Visibility**: public
- **Lines**: 1519–1524 (6 lines)

---

### `theorem mem_localRingAt_image_of_pointValuation_le_one`
- **Type**: `(hf : C.pointValuation P f ≤ 1) → ∃ x : C.localRingAt P, algebraMap _ _ x = f`
- **What**: Step (B'') hard direction: if the valuation at P is ≤ 1, then f comes from the local ring.
- **How**: Uses `IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer` to write `f = n/d`; then `IsLocalRing.notMem_maximalIdeal.mp d.prop` gives `d` is a unit; so `f = n * d⁻¹` lives in the local ring.
- **Hypotheses**: `C.pointValuation P f ≤ 1`.
- **Uses from project**: `C.pointValuation`, `C.localRingAt`
- **Used by**: `mem_localRingAt_image_iff_pointValuation_le_one`
- **Visibility**: public
- **Lines**: 1540–1564 (25 lines; preceded by `set_option synthInstance.maxHeartbeats 80000`)
- **Notes**: `set_option synthInstance.maxHeartbeats 80000` at L1529. Comment explains FaithfulSMul synthesis is slow on cold caches.

---

### `theorem mem_localRingAt_image_iff_pointValuation_le_one`
- **Type**: `(∃ x : C.localRingAt P, algebraMap _ _ x = f) ↔ C.pointValuation P f ≤ 1`
- **What**: Biconditional characterization of the local-ring image as the v-adic integer subring.
- **How**: Combines the two directions.
- **Uses from project**: `pointValuation_algebraMap_localRingAt_le_one`, `mem_localRingAt_image_of_pointValuation_le_one`
- **Used by**: (not called within this file — used externally)
- **Visibility**: public
- **Lines**: 1571–1577 (7 lines)

---

### `theorem ord_P_eq_zero_iff_pointValuation_eq_one`
- **Type**: `(hf : f ≠ 0) → C.ord_P P f = 0 ↔ C.pointValuation P f = 1`
- **What**: `ord_P = 0` iff the point valuation equals 1 (multiplicative language: not in the maximal ideal).
- **How**: Unfolds `ord_P` via `WithZero.unzero` and converts `(unzero hv).toAdd = 0` to `unzero hv = 1`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `C.ord_P`, `C.pointValuation`
- **Used by**: `ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt`
- **Visibility**: public
- **Lines**: 1580–1596 (17 lines)

---

### `theorem ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt`
- **Type**: `(hu : u ≠ 0) → C.ord_P P (algebraMap u) ≠ 0 ↔ u ∈ C.maximalIdealAt P`
- **What**: Main bridge for Bezout counting: `ord_P ≠ 0` iff the element is in the maximal ideal at P.
- **How**: Uses `pointValuation_algebraMap_le_one` + `pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt` + `ord_P_eq_zero_iff_pointValuation_eq_one`.
- **Hypotheses**: `u ≠ 0`.
- **Uses from project**: `C.ord_P`, `pointValuation_algebraMap_le_one`, `pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`, `ord_P_eq_zero_iff_pointValuation_eq_one`
- **Used by**: `finite_setOf_ord_P_nonzero_of_coordinateRing`
- **Visibility**: public
- **Lines**: 1600–1616 (17 lines)

---

### `theorem finite_setOf_mem_maximalIdealAt`
- **Type**: `(hu : u ≠ 0) → {P : C.SmoothPoint | u ∈ C.maximalIdealAt P}.Finite`
- **What**: Bezout counting for F[C]: a nonzero coordinate-ring element vanishes at only finitely many smooth points (Silverman II.1.2).
- **How**: Decomposes `u = p·1 + q·Y` via `exists_smul_basis_eq`, maps points to roots of `Algebra.norm u` via `norm_eval_at_x_of_zero_at_smoothPoint` + `mem_maximalIdealAt_iff_eval_zero`, and uses `Polynomial.finite_setOf_isRoot` + `smoothPoint_x_preimage_finite_of_set`.
- **Hypotheses**: `u ≠ 0`.
- **Uses from project**: `mem_maximalIdealAt_iff_eval_zero`, `norm_eval_at_x_of_zero_at_smoothPoint`, `smoothPoint_x_preimage_finite_of_set`
- **Used by**: `finite_setOf_ord_P_nonzero_of_coordinateRing`
- **Visibility**: public
- **Lines**: 1626–1639 (14 lines)

---

### `theorem finite_setOf_ord_P_nonzero_of_coordinateRing`
- **Type**: `(hu : u ≠ 0) → {P : C.SmoothPoint | C.ord_P P (algebraMap u) ≠ 0}.Finite`
- **What**: D-004 for coordinate-ring elements: finite set of points where ord_P ≠ 0.
- **How**: Rewrites the set via `ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt` then applies `finite_setOf_mem_maximalIdealAt`.
- **Hypotheses**: `u ≠ 0`.
- **Uses from project**: `ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt`, `finite_setOf_mem_maximalIdealAt`
- **Used by**: `finite_setOf_ord_P_nonzero`
- **Visibility**: public
- **Lines**: 1643–1653 (11 lines)

---

### `theorem finite_setOf_ord_P_nonzero`
- **Type**: `(hf : f ≠ 0) → {P : C.SmoothPoint | C.ord_P P f ≠ 0}.Finite`
- **What**: Silverman II.1.2: any nonzero function on C has zeros and poles at only finitely many smooth points.
- **How**: Writes `f = u/v` via `IsFractionRing.div_surjective`, shows `ord_P f ≠ 0` forces `ord_P(algebraMap u) ≠ 0` or `ord_P(algebraMap v) ≠ 0` using `ord_P_mul`, and takes the union of two finite sets.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `finite_setOf_ord_P_nonzero_of_coordinateRing`, `C.ord_P_mul`, `C.ord_P`
- **Used by**: `finite_zeros_poles`
- **Visibility**: public
- **Lines**: 1666–1692 (27 lines)

---

### `theorem finite_zeros_poles`
- **Type**: `(hf : f ≠ 0) → {P : C.SmoothPoint | C.ord_P P f ≠ 0}.Finite`
- **What**: Alias of `finite_setOf_ord_P_nonzero` with the ticket-statement name.
- **How**: Direct call to `finite_setOf_ord_P_nonzero`.
- **Uses from project**: `finite_setOf_ord_P_nonzero`
- **Used by**: (not called within this file)
- **Visibility**: public
- **Lines**: 1699–1701 (3 lines)

---

### `theorem const_of_no_poles_of_coordinateRing`
- **Type**: Given `h_coord : ∃ u, algebraMap u = f` and `h_inf : 0 ≤ ordAtInfty f`, then `∃ c : F, f = algebraMap c`
- **What**: Algebraic Liouville, coordinate-ring form: if f comes from the coordinate ring and has nonneg ord at infinity, then f is constant.
- **How**: Obtains `u` with `algebraMap u = f`, applies `coordinateRing_const_of_ordAtInfty_nonneg`.
- **Uses from project**: `coordinateRing_const_of_ordAtInfty_nonneg`, `C.ordAtInfty`
- **Used by**: `const_of_no_poles_of_valuation_of_ordAtInfty`, `const_of_isIntegral_polynomialX_of_ordAtInfty`
- **Visibility**: public
- **Lines**: 1718–1728 (11 lines)

---

### `theorem const_of_no_poles_of_valuation_of_ordAtInfty`
- **Type**: `[IsIntegrallyClosed C.CoordinateRing]` + `(h_primes : ∀ v, v.valuation f ≤ 1)` + `h_inf` → `∃ c, f = algebraMap c`
- **What**: IC-006 (Silverman II.1.2, Part 2, prime-indexed): if f has nonneg valuation at every prime and at infinity, then f is constant.
- **How**: Uses `C.mem_coordinateRing_of_valuation_le_one` then `const_of_no_poles_of_coordinateRing`.
- **Hypotheses**: `IsIntegrallyClosed C.CoordinateRing`, valuation ≤ 1 at all primes, nonneg ord at infinity.
- **Uses from project**: `const_of_no_poles_of_coordinateRing`, `C.mem_coordinateRing_of_valuation_le_one`
- **Used by**: (not called within this file)
- **Visibility**: public
- **Lines**: 1737–1744 (8 lines)

---

### `theorem const_of_isIntegral_polynomialX_of_ordAtInfty`
- **Type**: `[IsIntegrallyClosed C.CoordinateRing]` + `h_int : IsIntegral (Polynomial F) f` + `h_inf` → `∃ c, f = algebraMap c`
- **What**: IC-006 integrality form: if f is integral over F[X] and has nonneg ord at infinity, then f is constant.
- **How**: `C.mem_coordinateRing_of_isIntegral_polynomialX` then `const_of_no_poles_of_coordinateRing`.
- **Hypotheses**: `IsIntegrallyClosed C.CoordinateRing`, `IsIntegral (Polynomial F) f`, nonneg ord at infinity.
- **Uses from project**: `const_of_no_poles_of_coordinateRing`, `C.mem_coordinateRing_of_isIntegral_polynomialX`
- **Used by**: (not called within this file)
- **Visibility**: public
- **Lines**: 1751–1757 (7 lines)

---

## Summary Statistics

- **Total declarations**: 97
- **noncomputable def**: 4 (`normAsRatFunc`, `ordAtInfty`, `ordAtInftyVal`, `ordAtInftyValuation`)  
- **noncomputable instance**: 1 (`coordinateRing_free_over_polynomialX`)
- **private noncomputable def**: 2 (`weierstrassCubic`, `fiberQuadratic`, `coordEval`)
- **private theorem**: 13 (`ofFractionRing_sq`, `weierstrassCubic_natDegree`, `weierstrassCubic_ne_zero`, `algebraNorm_coordY_eq`, `intDegree_ofFractionRing_eq_of_surj`, `intDegree_algebraMap_div_algebraMap`, `ratFunc_exists_C_sub_intDegree_neg`, `natDegree_zero_of_ordAtInfty_nonneg`, `q_eq_zero_of_norm_natDeg_zero`, `fiberQuadratic_natDegree`, `fiberQuadratic_ne_zero`, `fiberQuadratic_isRoot_of_smoothPoint`, `coordEval_mk`, `coordEval_smul_basis`, `XClass_mem_ker_coordEval`, `YClass_mem_ker_coordEval`, `maximalIdealAt_le_ker_coordEval`, `ker_coordEval_ne_top`, `ker_coordEval_eq`)
- **Sorries**: none
- **set_option maxHeartbeats**: 1 occurrence (`set_option synthInstance.maxHeartbeats 80000` at L1529, before `mem_localRingAt_image_of_pointValuation_le_one`, with justifying comment about FaithfulSMul synthesis)

## Key API

- `ordAtInfty_of_ne` — used 16 times
- `ordAtInfty_algebraMap_fracPolyX_of_ne_zero` — used 10 times  
- `ordAtInftyVal_eq_exp_neg_ordAtInfty` — used 8 times
- `ordAtInfty_mul` — used 9 times
- `ordAtInfty_add_ge_min` — used 6 times
- `ordAtInfty_basis_eq_min` — used 5 times
- `ordAtInfty_algebraMap_coordinateRing` — used 5 times
- `const_of_no_poles_of_coordinateRing` — used 5 times

## Long Proofs (>30 lines)

| Name | Lines |
|------|-------|
| `ordAtInfty_basis_fracPolyX_of_both_ne_zero` | 152 |
| `ordAtInfty_add_ge_min` | 73 |
| `ordAtInfty_algebraMap_fracPolyX_add_ge_min` | 62 |
| `ordAtInfty_exists_const_sub_pos_of_fracPolyX_nonneg` | 60 |
| `ordAtInfty_basis_eq_min` | 43 |
| `intDegree_ofFractionRing_eq_of_surj` | 38 |
| `ratFunc_exists_C_sub_intDegree_neg` | 51 |
| `coordinateRing_const_of_ordAtInfty_nonneg` | 32 |
| `ordAtInftyVal_add_le_max` | 31 |
| `natDegree_norm_smul_basis_of_both_ne_zero` | 30 |
