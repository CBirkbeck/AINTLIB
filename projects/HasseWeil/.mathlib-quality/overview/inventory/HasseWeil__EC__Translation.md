# Inventory: ./HasseWeil/EC/Translation.lean

**File**: `HasseWeil/EC/Translation.lean`
**Total lines**: 428
**Import**: `HasseWeil.AdditionPullback`
**Purpose**: Constructs the translation-by-a-base-field-point algebra automorphism τ_k : K(E) →ₐ[F] K(E), paralleling the `addPullbackAlgHom` construction in `AdditionPullback.lean`. Also develops ord-at-infinity computations for the translated coordinates.

---

## Declarations

### `noncomputable def translateSlope_xy`
- **Type**: `(xk yk : F) : KE`
- **What**: The slope of the line through the generic point `(x_gen, y_gen)` and the base-field constant point `(xk, yk)`, computed via the Weierstrass `slope` function with the second coordinates lifted to `K(E)` via `algebraMap`.
- **How**: Pure definitional: applies `(W_KE W).toAffine.slope (x_gen W) (algebraMap F KE xk) (y_gen W) (algebraMap F KE yk)`.
- **Hypotheses**: None beyond the ambient elliptic curve `W`.
- **Uses from project**: `W_KE` (MulByIntPullback), `x_gen` (MulByIntPullback), `y_gen` (MulByIntPullback).
- **Used by**: `translateX_xy`, `translateY_xy`, `translateX_xy_eq_addX`, `translateY_xy_eq_addY`, `translateSlope_xy_eq`, `ord_translateSlope_xy`.
- **Visibility**: public
- **Lines**: 61–63, proof length: 3 lines (definitional body)
- **Notes**: None.

---

### `noncomputable def translateX_xy`
- **Type**: `(xk yk : F) : KE`
- **What**: The x-coordinate of the sum `P_gen + (xk, yk)` on the base-changed curve, using the group-law `addX` formula.
- **How**: Applies `(W_KE W).toAffine.addX (x_gen W) (algebraMap F KE xk) (translateSlope_xy W xk yk)`.
- **Hypotheses**: None beyond the ambient elliptic curve.
- **Uses from project**: `W_KE`, `x_gen`, `translateSlope_xy`.
- **Used by**: `translateX_xy_eq_addX`, `translate_equation`, `translateBaseHom`, `translateCoordAlgHom_injective_of_baseHom_inj`, `translateX_xy_ne_const_of_pole`, `translateBaseHom_injective_of_transcendental`.
- **Visibility**: public
- **Lines**: 66–68, 3 lines
- **Notes**: None.

---

### `noncomputable def translateY_xy`
- **Type**: `(xk yk : F) : KE`
- **What**: The y-coordinate of `P_gen + (xk, yk)`, using the group-law `addY` formula with the generic point `y_gen` as the base y-value.
- **How**: Applies `(W_KE W).toAffine.addY (x_gen W) (algebraMap F KE xk) (y_gen W) (translateSlope_xy W xk yk)`.
- **Hypotheses**: None beyond the ambient elliptic curve.
- **Uses from project**: `W_KE`, `x_gen`, `y_gen`, `translateSlope_xy`.
- **Used by**: `translateY_xy_eq_addY`, `translate_equation`, `translate_poly_eval₂_zero`, `translateCoordRingHom`, `translateCoordAlgHom`, `translateCoordAlgHom_injective_of_baseHom_inj`.
- **Visibility**: public
- **Lines**: 71–73, 3 lines
- **Notes**: None.

---

### `@[simp] theorem translateX_xy_eq_addX`
- **Type**: `(xk yk : F) : translateX_xy W xk yk = (W_KE W).toAffine.addX (x_gen W) (algebraMap F KE xk) (translateSlope_xy W xk yk)`
- **What**: Definitional unfolding of `translateX_xy` — confirms it literally is the `addX` formula. Pure `rfl`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `translateX_xy`, `W_KE`, `x_gen`, `translateSlope_xy`.
- **Used by**: External callers (e.g., `TranslationEvaluation.lean`).
- **Visibility**: public (simp lemma)
- **Lines**: 83–86, 1 line
- **Notes**: None.

---

### `@[simp] theorem translateY_xy_eq_addY`
- **Type**: `(xk yk : F) : translateY_xy W xk yk = (W_KE W).toAffine.addY (x_gen W) (algebraMap F KE xk) (y_gen W) (translateSlope_xy W xk yk)`
- **What**: Definitional unfolding of `translateY_xy` — confirms it is the `addY` formula. Pure `rfl`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `translateY_xy`, `W_KE`, `x_gen`, `y_gen`, `translateSlope_xy`.
- **Used by**: External callers (e.g., `TranslationEvaluation.lean`).
- **Visibility**: public (simp lemma)
- **Lines**: 91–94, 1 line
- **Notes**: None.

---

### `abbrev TranslateNonInverse`
- **Type**: `(xk yk : F) : Prop := ¬(x_gen W = algebraMap F KE xk ∧ y_gen W = (W_KE W).toAffine.negY (algebraMap F KE xk) (algebraMap F KE yk))`
- **What**: The non-inverse hypothesis asserting that `(xk, yk)` is not the additive inverse of the generic point — needed to apply the non-degenerate form of the addition law.
- **How**: Pure abbreviation.
- **Hypotheses**: None (a Prop-valued abbreviation).
- **Uses from project**: `x_gen`, `y_gen`, `W_KE`.
- **Used by**: `translate_equation`, `translate_poly_eval₂_zero`, `translateCoordRingHom`, `translateCoordAlgHom`, `translateCoordAlgHom_injective_of_baseHom_inj`, `translateAlgHom`.
- **Visibility**: public
- **Lines**: 99–101, 3 lines
- **Notes**: None.

---

### `theorem translate_constant_equation`
- **Type**: `(xk yk : F) (h_eq : W.toAffine.Equation xk yk) : (W_KE W).toAffine.Equation (algebraMap F KE xk) (algebraMap F KE yk)`
- **What**: Lifts the equation condition `(xk, yk) ∈ W(F)` to the K(E)-base-changed curve, showing the base-field constants satisfy the Weierstrass equation over K(E).
- **How**: Applies `Affine.Equation.map (algebraMap F KE)` to transport the equation, then rewrites the curve identity `W.toAffine.map (algebraMap F KE) = (W_KE W).toAffine` by `rfl`.
- **Hypotheses**: `(xk, yk)` satisfies the Weierstrass equation over F.
- **Uses from project**: `W_KE`.
- **Used by**: `translate_equation`; also used externally in `MulByIntUnramified.lean` and `TranslationOrd.lean`.
- **Visibility**: public
- **Lines**: 106–111, 6 lines
- **Notes**: None.

---

### `theorem translate_equation`
- **Type**: `(xk yk : F) (h_eq : W.toAffine.Equation xk yk) (hxy : TranslateNonInverse W xk yk) : (W_KE W).toAffine.Equation (translateX_xy W xk yk) (translateY_xy W xk yk)`
- **What**: Proves that the translated coordinates `(translateX_xy, translateY_xy)` satisfy the Weierstrass equation, i.e., the addition formula stays on the curve.
- **How**: Direct application of `Affine.equation_add` to `generic_equation W` and `translate_constant_equation`.
- **Hypotheses**: `(xk, yk)` on the curve; non-inverse hypothesis `hxy`.
- **Uses from project**: `translateX_xy`, `translateY_xy`, `translate_constant_equation`, `W_KE`, `generic_equation` (MulByIntPullback).
- **Used by**: `translate_poly_eval₂_zero`.
- **Visibility**: public
- **Lines**: 116–120, 5 lines
- **Notes**: None.

---

### `noncomputable def translateBaseHom`
- **Type**: `(xk yk : F) : Polynomial F →+* KE`
- **What**: The ring hom `F[X] →+* K(E)` that evaluates a polynomial at `translateX_xy W xk yk` (with base-field coefficients sent via `algebraMap`). This is the intermediate building block for `AdjoinRoot.lift`.
- **How**: `Polynomial.eval₂RingHom (algebraMap F KE) (translateX_xy W xk yk)`.
- **Hypotheses**: None.
- **Uses from project**: `translateX_xy`.
- **Used by**: `translate_poly_eval₂_zero`, `translateCoordRingHom`, `translateCoordAlgHom`, `translateCoordAlgHom_injective_of_baseHom_inj`, `translateAlgHom`, `translateBaseHom_injective_of_transcendental`.
- **Visibility**: public
- **Lines**: 125–126, 2 lines
- **Notes**: None.

---

### `theorem translate_poly_eval₂_zero`
- **Type**: `(xk yk : F) (h_eq : W.toAffine.Equation xk yk) (hxy : TranslateNonInverse W xk yk) : W.toAffine.polynomial.eval₂ (translateBaseHom W xk yk) (translateY_xy W xk yk) = 0`
- **What**: The Weierstrass polynomial vanishes when evaluated at the translated coordinates via the base hom — the key compatibility condition for `AdjoinRoot.lift`.
- **How**: Rewrites via `Polynomial.eval₂_eval₂RingHom_apply` and `Affine.map_polynomial`, then applies `translate_equation`.
- **Hypotheses**: Equation and non-inverse conditions.
- **Uses from project**: `translateBaseHom`, `translateY_xy`, `translate_equation`.
- **Used by**: `translateCoordRingHom`; also used externally in `TranslationOrd.lean`.
- **Visibility**: public
- **Lines**: 129–134, 6 lines
- **Notes**: None.

---

### `noncomputable def translateCoordRingHom`
- **Type**: `(xk yk : F) (h_eq : W.toAffine.Equation xk yk) (hxy : TranslateNonInverse W xk yk) : W.toAffine.CoordinateRing →+* KE`
- **What**: The ring homomorphism `CoordinateRing → K(E)` sending the coordinate generators to the translation outputs, constructed via `AdjoinRoot.lift`.
- **How**: `AdjoinRoot.lift (translateBaseHom W xk yk) (translateY_xy W xk yk) (translate_poly_eval₂_zero ...)`.
- **Hypotheses**: Equation and non-inverse conditions.
- **Uses from project**: `translateBaseHom`, `translateY_xy`, `translate_poly_eval₂_zero`.
- **Used by**: `translateCoordAlgHom`, `translateCoordAlgHom_injective_of_baseHom_inj`.
- **Visibility**: public
- **Lines**: 140–145, 6 lines
- **Notes**: None.

---

### `noncomputable def translateCoordAlgHom`
- **Type**: `(xk yk : F) (h_eq : W.toAffine.Equation xk yk) (hxy : TranslateNonInverse W xk yk) : W.toAffine.CoordinateRing →ₐ[F] KE`
- **What**: Packages `translateCoordRingHom` as an F-algebra homomorphism by verifying the `commutes'` condition (that the map commutes with the structure maps from F).
- **How**: Sets `toRingHom := translateCoordRingHom`; proves `commutes'` by unfolding to `AdjoinRoot.lift_mk` and `Polynomial.eval₂_C` + `simp`.
- **Hypotheses**: Equation and non-inverse conditions.
- **Uses from project**: `translateCoordRingHom`, `translateBaseHom`, `translateY_xy`.
- **Used by**: `translateCoordAlgHom_injective_of_baseHom_inj`, `translateAlgHom`.
- **Visibility**: public
- **Lines**: 148–163, 16 lines
- **Notes**: None.

---

### `theorem translateCoordAlgHom_injective_of_baseHom_inj`
- **Type**: `(xk yk : F) (h_eq : W.toAffine.Equation xk yk) (hxy : TranslateNonInverse W xk yk) (hxinj : Function.Injective (translateBaseHom W xk yk)) : Function.Injective (translateCoordAlgHom W xk yk h_eq hxy)`
- **What**: Given that `translateBaseHom` is injective (i.e., `translateX_xy` is transcendental over F), the full coordinate-ring algebra hom is also injective. This is the translation analog of `addCoordAlgHom_injective_of_baseHom_inj` from `AdditionPullback.lean`.
- **How**: Reduces to `translateCoordRingHom` injectivity. Uses the `CoordinateRing` basis decomposition via `Affine.CoordinateRing.exists_smul_basis_eq`; the key argument is that any element `r = p·1 + q·Y` maps to `baseHom(p) + baseHom(q)·translateY_xy`, and non-vanishing of the image forces `q = 0` via `Affine.CoordinateRing.degree_norm_smul_basis` giving a degree contradiction when `q ≠ 0`.
- **Hypotheses**: Equation condition, `TranslateNonInverse`, and `Function.Injective (translateBaseHom W xk yk)`.
- **Uses from project**: `translateCoordRingHom`, `translateBaseHom`, `translateY_xy`, `translateCoordAlgHom`.
- **Used by**: `translateAlgHom`.
- **Visibility**: public
- **Lines**: 180–255, **76 lines**
- **Notes**: Proof > 30 lines. The argument is a direct transposition of the analogous lemma in `AdditionPullback.lean` (explicitly noted in the docstring). Relies on `Affine.CoordinateRing.exists_smul_basis_eq`, `Affine.CoordinateRing.coe_norm_smul_basis`, and `Affine.CoordinateRing.degree_norm_smul_basis` from mathlib.

---

### `noncomputable def translateAlgHom`
- **Type**: `(xk yk : F) (h_eq : W.toAffine.Equation xk yk) (hxy : TranslateNonInverse W xk yk) (hxinj : Function.Injective (translateBaseHom W xk yk)) : KE →ₐ[F] KE`
- **What**: The translation algebra endomorphism of K(E), lifted from `translateCoordAlgHom` to the full function field via `IsFractionRing.liftAlgHom`. This is the main output of the file.
- **How**: `IsFractionRing.liftAlgHom (translateCoordAlgHom_injective_of_baseHom_inj ...)`.
- **Hypotheses**: Equation condition, non-inverse, and base-hom injectivity.
- **Uses from project**: `translateCoordAlgHom_injective_of_baseHom_inj`, `translateCoordAlgHom`.
- **Used by**: Heavily used externally in `TranslationOrd.lean` (as `translateAlgHom_of_nonTorsion`, `translateAlgHom_of_2tor`).
- **Visibility**: public
- **Lines**: 265–271, 7 lines
- **Notes**: Witness-parametric design (requires caller to supply injectivity). External files construct the unconditional variants by supplying `translateBaseHom_injective_of_transcendental`.

---

### `theorem translateX_xy_ne_const_of_pole`
- **Type**: `(xk yk : F) (c : F) (h_pole : (W_smooth W).ordAtInfty (translateX_xy W xk yk) < 0) (hc : translateX_xy W xk yk = algebraMap F KE c) : False`
- **What**: If `translateX_xy` has a pole at infinity and equals a base-field constant `c`, then a contradiction follows — constants are either zero (giving `ordAtInfty = ⊤`) or nonzero (giving `ordAtInfty = 0`), both contradicting the pole hypothesis.
- **How**: Case split on `c = 0` vs `c ≠ 0`: uses `(W_smooth W).ordAtInfty_zero` and `ordAtInfty_algebraMap_F_nonzero`.
- **Hypotheses**: Pole hypothesis `ordAtInfty < 0` and equality to a constant.
- **Uses from project**: `W_smooth` (OrdAtInftyBridge), `translateX_xy`, `ordAtInfty_algebraMap_F_nonzero` (OrdAtInftyBridge).
- **Used by**: Unused in file; used conceptually as a building block documented in `translateBaseHom_injective_of_transcendental`'s docstring.
- **Visibility**: public
- **Lines**: 291–305, 15 lines
- **Notes**: Has `set_option linter.unusedSectionVars false` (no justifying comment). Marked as unused within this file.

---

### `theorem translateBaseHom_injective_of_transcendental`
- **Type**: `(xk yk : F) (h_trans : Transcendental F (translateX_xy W xk yk)) : Function.Injective (translateBaseHom W xk yk)`
- **What**: If `translateX_xy` is transcendental over F, then `translateBaseHom` (evaluation at `translateX_xy`) is injective as a ring hom `F[X] →+* K(E)`.
- **How**: Rewrites `translateBaseHom = (Polynomial.aeval (translateX_xy W xk yk)).toRingHom` then applies `transcendental_iff_injective.mp`.
- **Hypotheses**: Transcendence of `translateX_xy` over F.
- **Uses from project**: `translateBaseHom`, `translateX_xy`.
- **Used by**: Unused in file; used externally in `TranslationOrd.lean` (for both the non-2-torsion and 2-torsion `translateAlgHom` constructions).
- **Visibility**: public
- **Lines**: 332–347, 16 lines
- **Notes**: Has `set_option linter.unusedSectionVars false` (no justifying comment). Key bridge lemma used heavily externally even though not referenced in this file itself.

---

### `theorem ord_x_gen_sub_const`
- **Type**: `(xk : F) : (W_smooth W).ordAtInfty (x_gen W - algebraMap F KE xk) = ((-2 : ℤ) : WithTop ℤ)`
- **What**: The order at infinity of `x_gen - algebraMap xk` is −2 for any base-field constant `xk`. When `xk = 0` this is just `ord(x_gen) = -2`; otherwise `ord(x_gen) = -2 < 0 = ord(algebraMap xk)` so the ultrametric inequality gives the dominant order.
- **How**: Case split on `xk = 0` (uses `ordAtInfty_x_gen`) and `xk ≠ 0` (uses `ordAtInfty_x_gen`, `ordAtInfty_algebraMap_F_nonzero`, and `(W_smooth W).ordAtInfty_sub_eq_of_lt`).
- **Hypotheses**: None beyond ambient curve.
- **Uses from project**: `W_smooth`, `x_gen`, `ordAtInfty_x_gen` (OrdAtInftyBridge), `ordAtInfty_algebraMap_F_nonzero` (OrdAtInftyBridge).
- **Used by**: `ord_translateSlope_xy`.
- **Visibility**: public
- **Lines**: 361–379, 19 lines
- **Notes**: None.

---

### `theorem x_gen_sub_const_ne_zero`
- **Type**: `(xk : F) : x_gen W - algebraMap F KE xk ≠ 0`
- **What**: The difference `x_gen - algebraMap xk` is nonzero in K(E), since if it were zero then `x_gen` would equal a constant, contradicting its transcendence over F.
- **How**: Assumes equality, constructs an algebraic witness `Polynomial.X - Polynomial.C xk` for `x_gen`, then applies `x_gen_transcendental W`.
- **Hypotheses**: None beyond ambient curve.
- **Uses from project**: `x_gen`, `x_gen_transcendental` (MulByIntPullback).
- **Used by**: `translateSlope_xy_eq`, `ord_translateSlope_xy` (via `x_gen_sub_const_ne_zero`). Also used extensively in `TranslationOrd.lean`, `TranslateValuation.lean`, and `MulByIntUnramified.lean`.
- **Visibility**: public
- **Lines**: 383–390, 8 lines
- **Notes**: One of the most widely used lemmas from this file across the project.

---

### `theorem translateSlope_xy_eq`
- **Type**: `(xk yk : F) : translateSlope_xy W xk yk = (y_gen W - algebraMap F KE yk) / (x_gen W - algebraMap F KE xk)`
- **What**: Simplifies `translateSlope_xy` from its definition in terms of the Weierstrass `slope` function to the explicit secant-slope fraction `(y_gen - yk) / (x_gen - xk)`, using the `slope_of_X_ne` lemma from mathlib (which applies when the two x-coordinates differ).
- **How**: Unfolds `translateSlope_xy`, applies `WeierstrassCurve.Affine.slope_of_X_ne` using `x_gen_sub_const_ne_zero` to provide the non-equality of x-coords.
- **Hypotheses**: None (uses `x_gen_sub_const_ne_zero` which has no extra hypotheses).
- **Uses from project**: `translateSlope_xy`, `y_gen`, `x_gen`, `x_gen_sub_const_ne_zero`.
- **Used by**: `ord_translateSlope_xy`. Also used externally in `TranslateValuation.lean` and `TranslationOrd.lean`.
- **Visibility**: public
- **Lines**: 393–400, 8 lines
- **Notes**: Uses `classical` to handle the `DecidableEq` needed for `slope_of_X_ne`.

---

### `theorem ord_y_gen_sub_const`
- **Type**: `(yk : F) : (W_smooth W).ordAtInfty (y_gen W - algebraMap F KE yk) = ((-3 : ℤ) : WithTop ℤ)`
- **What**: The order at infinity of `y_gen - algebraMap yk` is −3 for any base-field constant `yk`. Analogous to `ord_x_gen_sub_const` for the y-generator.
- **How**: Case split on `yk = 0` (uses `ordAtInfty_y_gen`) and `yk ≠ 0` (uses `ordAtInfty_y_gen`, `ordAtInfty_algebraMap_F_nonzero`, and `(W_smooth W).ordAtInfty_sub_eq_of_lt`).
- **Hypotheses**: None beyond ambient curve.
- **Uses from project**: `W_smooth`, `y_gen`, `ordAtInfty_y_gen` (OrdAtInftyBridge), `ordAtInfty_algebraMap_F_nonzero` (OrdAtInftyBridge).
- **Used by**: `ord_translateSlope_xy`.
- **Visibility**: public
- **Lines**: 403–417, 15 lines
- **Notes**: Direct y-analog of `ord_x_gen_sub_const`.

---

### `theorem ord_translateSlope_xy`
- **Type**: `(xk yk : F) : (W_smooth W).ordAtInfty (translateSlope_xy W xk yk) = ((-1 : ℤ) : WithTop ℤ)`
- **What**: The order at infinity of the translation slope is −1, i.e., `ord((y_gen - yk) / (x_gen - xk)) = ord(numerator) - ord(denominator) = -3 - (-2) = -1`.
- **How**: Rewrites using `translateSlope_xy_eq`, then applies `(W_smooth W).ordAtInfty_div_of_ord_eq` with `x_gen_sub_const_ne_zero`, `ord_y_gen_sub_const`, and `ord_x_gen_sub_const`.
- **Hypotheses**: None beyond ambient curve.
- **Uses from project**: `translateSlope_xy`, `translateSlope_xy_eq`, `W_smooth`, `x_gen_sub_const_ne_zero`, `ord_y_gen_sub_const`, `ord_x_gen_sub_const`.
- **Used by**: Unused in file; exported for use in files developing the ord-at-infinity computation for `translateX_xy`.
- **Visibility**: public
- **Lines**: 421–426, 6 lines
- **Notes**: Unused within this file; likely consumed by `TranslateOrdInfty.lean` or `TranslationOrd.lean`.

---

## Summary

- **Total declarations**: 20 (3 `noncomputable def`, 4 `noncomputable def` with proofs, 1 `abbrev`, 12 `theorem`)
- **Defs**: 8 (`translateSlope_xy`, `translateX_xy`, `translateY_xy`, `translateBaseHom`, `translateCoordRingHom`, `translateCoordAlgHom`, `translateAlgHom`, `TranslateNonInverse` as abbrev)
- **Lemmas/theorems**: 12
- **Instances**: 0
- **Sorries**: 0
- **`set_option maxHeartbeats`**: 0 (only `set_option linter.unusedSectionVars false`)
- **Long proofs** (> 30 lines): `translateCoordAlgHom_injective_of_baseHom_inj` (76 lines)
- **Key API** (used by 3+ others in file): `translateSlope_xy` (used by `translateX_xy`, `translateY_xy`, `translateX_xy_eq_addX`, `translateY_xy_eq_addY`, `translateSlope_xy_eq`, `ord_translateSlope_xy`); `x_gen_sub_const_ne_zero` (used by `translateSlope_xy_eq`, `ord_translateSlope_xy`; also widely used externally).
- **Unused in file**: `translateX_xy_ne_const_of_pole`, `translateBaseHom_injective_of_transcendental`, `ord_translateSlope_xy` (not referenced in this file's bodies, but used externally).
