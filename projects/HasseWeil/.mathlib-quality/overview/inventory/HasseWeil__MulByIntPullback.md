# Inventory: ./HasseWeil/MulByIntPullback.lean

**File**: `HasseWeil/MulByIntPullback.lean`
**Import**: `HasseWeil.Auxiliary.DivisionPolynomial`
**Total declarations**: 35 (13 noncomputable defs, 1 instance, 21 lemmas/theorems, including 10 private)

---

## Overview

This file constructs the pullback ring/algebra homomorphism `[n]* : K(E) →ₐ[F] K(E)` for the multiplication-by-n endomorphism on an elliptic curve, using division polynomial formulas. The key steps are:
1. Define the generic point `(x_gen, y_gen)` in `K(E)`.
2. Define the division polynomial images `Φ_ff`, `ΨSq_ff`, `ψ_ff`, `ω_ff` and the affine coordinates `mulByInt_x`, `mulByInt_y`.
3. Prove the Weierstrass equation holds at `(mulByInt_x, mulByInt_y)` via Jacobian `smulEval`.
4. Build the coordinate ring homomorphism `mulByInt_coordHom : R →+* K(E)` via `AdjoinRoot.lift`.
5. Extend to the fraction field `mulByInt_pullbackRingHom` / `mulByInt_pullbackAlgHom`.

---

## Declarations

### `noncomputable def x_gen`
- **Type**: `x_gen : KE` (where `KE = W.toAffine.FunctionField`)
- **What**: The generic x-coordinate in `K(E)`, defined as the image of `Polynomial.X` under the composite `F[X] → R → K(E)`.
- **How**: Direct `algebraMap` composition via the scalar tower `F[X] → R → KE`.
- **Hypotheses**: `W : WeierstrassCurve F`, `F` field, `W.toAffine.IsElliptic`.
- **Uses from project**: none
- **Used by**: `generic_equation`, `generic_nonsingular'`, `evalEval_generic_eq_mk`, `smulEval_generic_Z/X/Y`, `jacobian_equation_smulEval`, `mulByInt_weierstrass`, `x_gen_transcendental`, `Φ_ff_transcendental`, `mulByInt_x_transcendental`, and broadly throughout the project
- **Visibility**: public
- **Lines**: 27–29, 2 lines (def)
- **Notes**: Fundamental building block used throughout the project (≥30 files).

---

### `noncomputable def y_gen`
- **Type**: `y_gen : KE`
- **What**: The generic y-coordinate in `K(E)`, defined as the image of `AdjoinRoot.root W.toAffine.polynomial`.
- **How**: Direct `algebraMap` of the `AdjoinRoot.root`.
- **Hypotheses**: Same as `x_gen`.
- **Uses from project**: none
- **Used by**: `generic_equation`, `generic_nonsingular'`, `evalEval_generic_eq_mk`, `smulEval_generic_Z/X/Y`, `jacobian_equation_smulEval`, `mulByInt_weierstrass`, and broadly
- **Visibility**: public
- **Lines**: 30–32, 2 lines (def)
- **Notes**: Fundamental building block used throughout the project.

---

### `noncomputable def W_KE`
- **Type**: `W_KE : WeierstrassCurve KE`
- **What**: The base change of `W` from `F` to `K(E)`, i.e. `W.map (algebraMap F KE)`.
- **How**: Directly `W.map (algebraMap F KE)`.
- **Hypotheses**: Same as above.
- **Uses from project**: none (uses mathlib `WeierstrassCurve.map`)
- **Used by**: `W_KE_isElliptic`, `generic_equation`, `generic_nonsingular'`, `smulEval_generic_Z/X/Y`, `jacobian_equation_smulEval`, `mulByInt_weierstrass`, and many files in the project
- **Visibility**: public
- **Lines**: 39, 1 line (def)
- **Notes**: Heavily used across the project as the "working curve" over K(E).

---

### `instance W_KE_isElliptic`
- **Type**: `(W_KE W).IsElliptic`
- **What**: The base-changed curve `W_KE W` is elliptic, inheriting from `W.IsElliptic` via `inferInstance`.
- **How**: `inferInstance` — the `IsElliptic` instance is preserved under `map`.
- **Hypotheses**: `W.toAffine.IsElliptic`.
- **Uses from project**: `W_KE`
- **Used by**: used implicitly by instances requiring `(W_KE W).toAffine.IsElliptic` in the file
- **Visibility**: public
- **Lines**: 42–43, 2 lines
- **Notes**: Essentially a typeclass shortcut.

---

### `noncomputable def Φ_ff`
- **Type**: `Φ_ff (n : ℤ) : KE`
- **What**: The image of the division polynomial `Φ_n ∈ F[X]` in `K(E)`, via `F[X] → R → K(E)`.
- **How**: `algebraMap` composition.
- **Hypotheses**: None beyond the section variables.
- **Uses from project**: none (uses mathlib `WeierstrassCurve.Φ`)
- **Used by**: `φ_ff_eq_Φ_ff`, `smulEval_generic_X`, `mulByInt_x`, `mulByInt_x_transcendental`
- **Visibility**: public
- **Lines**: 47–49, 3 lines

---

### `noncomputable def ΨSq_ff`
- **Type**: `ΨSq_ff (n : ℤ) : KE`
- **What**: The image of `ΨSq_n ∈ F[X]` (the square of the division polynomial) in `K(E)`.
- **How**: `algebraMap` composition.
- **Hypotheses**: None beyond section variables.
- **Uses from project**: none
- **Used by**: `ψ_ff_sq_eq_ΨSq_ff`, `ΨSq_ff_ne_zero`, `mulByInt_x`, `mulByInt_x_transcendental`
- **Visibility**: public
- **Lines**: 50–52, 3 lines

---

### `noncomputable def ψ_ff`
- **Type**: `ψ_ff (n : ℤ) : KE`
- **What**: The image of `mk W (ψ_n)` (the division polynomial in the coordinate ring) in `K(E)`.
- **How**: `algebraMap R KE` applied to `CoordinateRing.mk`.
- **Hypotheses**: None beyond section variables.
- **Uses from project**: none
- **Used by**: `ψ_ff_sq_eq_ΨSq_ff`, `ψ_ff_ne_zero`, `smulEval_generic_Z`, `mulByInt_y`
- **Visibility**: public
- **Lines**: 53–55, 3 lines

---

### `noncomputable def ω_ff`
- **Type**: `ω_ff (n : ℤ) : KE`
- **What**: The image of `mk W (ω_n)` in `K(E)`.
- **How**: `algebraMap R KE`.
- **Hypotheses**: None beyond section variables.
- **Uses from project**: none
- **Used by**: `smulEval_generic_Y`, `mulByInt_y`
- **Visibility**: public
- **Lines**: 56–58, 3 lines

---

### `noncomputable def mulByInt_x`
- **Type**: `mulByInt_x (n : ℤ) : KE`
- **What**: The x-coordinate of `[n](x_gen, y_gen)` in `K(E)`, equal to `Φ_ff W n / ΨSq_ff W n`.
- **How**: Division of the two polynomial images.
- **Hypotheses**: None (no `n ≠ 0` needed for definition; needed for nonvanishing).
- **Uses from project**: `Φ_ff`, `ΨSq_ff`
- **Used by**: `mulByInt_xHom`, `mulByInt_weierstrass`, `mulByInt_x_transcendental`, `mulByInt_xHom_injective`, `mulByInt_pullbackAlgHom`
- **Visibility**: public
- **Lines**: 59, 1 line

---

### `noncomputable def mulByInt_y`
- **Type**: `mulByInt_y (n : ℤ) : KE`
- **What**: The y-coordinate of `[n](x_gen, y_gen)` in `K(E)`, equal to `ω_ff W n / ψ_ff W n ^ 3`.
- **How**: Division.
- **Hypotheses**: None.
- **Uses from project**: `ω_ff`, `ψ_ff`
- **Used by**: `mulByInt_weierstrass`, `mulByInt_coordHom`, `mulByInt_coordHom_injective`
- **Visibility**: public
- **Lines**: 60, 1 line

---

### `noncomputable def mulByInt_xHom`
- **Type**: `mulByInt_xHom (n : ℤ) : Polynomial F →+* KE`
- **What**: The ring hom `F[X] → K(E)` that sends `X` to `mulByInt_x W n`, i.e. evaluation at the x-coordinate of `[n]`.
- **How**: `Polynomial.eval₂RingHom (algebraMap F KE) (mulByInt_x W n)`.
- **Hypotheses**: None.
- **Uses from project**: `mulByInt_x`
- **Used by**: `mulByInt_weierstrass`, `mulByInt_coordHom`, `mulByInt_xHom_injective`, `mulByInt_coordHom_injective`, `mulByInt_pullbackAlgHom`
- **Visibility**: public
- **Lines**: 62–64, 3 lines

---

### `lemma generic_equation`
- **Type**: `(W_KE W).toAffine.Equation (x_gen W) (y_gen W)`
- **What**: The generic point `(x_gen, y_gen)` satisfies the Weierstrass equation of `W_KE`.
- **How**: Factors `algebraMap F KE` through `R`, rewrites `evalEval` using `Affine.map_polynomial` and `map_mapRingHom_evalEval`, reduces to `AdjoinRoot.eval₂_root W.toAffine.polynomial`.
- **Hypotheses**: None beyond section variables.
- **Uses from project**: `W_KE`, `x_gen`, `y_gen`
- **Used by**: `generic_nonsingular'` (directly); also used extensively across the project (≥15 files)
- **Visibility**: public
- **Lines**: 69–91, 23 lines
- **Notes**: `set_option linter.unusedSectionVars false` applied. Core fact used project-wide.

---

### `private lemma generic_nonsingular'`
- **Type**: `(W_KE W).toAffine.Nonsingular (x_gen W) (y_gen W)`
- **What**: The generic point is nonsingular on `W_KE`, following from `generic_equation` and `IsElliptic`.
- **How**: `Affine.equation_iff_nonsingular.mp (generic_equation W)` — the key mathlib lemma that on an elliptic curve every solution to the Weierstrass equation is nonsingular.
- **Hypotheses**: `W.toAffine.IsElliptic`.
- **Uses from project**: `W_KE`, `x_gen`, `y_gen`, `generic_equation`
- **Used by**: `jacobian_equation_smulEval`, `mulByInt_weierstrass`
- **Visibility**: private
- **Lines**: 95–97, 3 lines
- **Notes**: The public version `generic_nonsingular` lives in `EC/GenericPoint.lean`.

---

### `lemma ψ_ff_sq_eq_ΨSq_ff`
- **Type**: `ψ_ff W n ^ 2 = ΨSq_ff W n`
- **What**: The square of the division polynomial image `ψ_ff W n` equals `ΨSq_ff W n`.
- **How**: Uses `CoordinateRing.mk_ψ` (identifies `mk W (ψ n)` with `mk W (Ψ n)`) and `CoordinateRing.mk_Ψ_sq` (the key mathlib identity `mk W (Ψ n) ^ 2 = mk W (C (ΨSq n))`).
- **Hypotheses**: None.
- **Uses from project**: `ψ_ff`, `ΨSq_ff`
- **Used by**: `ΨSq_ff_ne_zero`, `mulByInt_weierstrass`, `mulByInt_x_transcendental`
- **Visibility**: public
- **Lines**: 100–111, 12 lines

---

### `lemma φ_ff_eq_Φ_ff`
- **Type**: `algebraMap R KE (CoordinateRing.mk W.toAffine (W.φ n)) = Φ_ff W n`
- **What**: The image of `mk W (φ n)` in `K(E)` equals `Φ_ff W n`.
- **How**: Uses `CoordinateRing.mk_φ` from mathlib.
- **Hypotheses**: None.
- **Uses from project**: `Φ_ff`
- **Used by**: `smulEval_generic_X`
- **Visibility**: public
- **Lines**: 115–118, 4 lines
- **Notes**: `set_option linter.unusedSectionVars false` applied.

---

### `private lemma natDegree_ψ₂_le`
- **Type**: `W.ψ₂.natDegree ≤ 1`
- **What**: The bivariate polynomial `ψ₂` has degree at most 1 in the outer `Y` variable.
- **How**: Unfolds `ψ₂` and `polynomialY`, then applies `natDegree_add_le` and `natDegree_mul_le` with explicit degree bounds via `omega`.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: `natDegree_Ψ_le`
- **Visibility**: private
- **Lines**: 121–127, 7 lines

---

### `private lemma natDegree_Ψ_le`
- **Type**: `(W.Ψ n).natDegree ≤ 1`
- **What**: The bivariate division polynomial `Ψ n` has outer Y-degree at most 1.
- **How**: Case splits on parity of `n` (from `WeierstrassCurve.Ψ` definition): even case uses `natDegree_mul_le` + `natDegree_C` + `natDegree_ψ₂_le`; odd case uses `mul_one` + `natDegree_C`.
- **Hypotheses**: None.
- **Uses from project**: `natDegree_ψ₂_le`
- **Used by**: `mk_ψ_ne_zero`
- **Visibility**: private
- **Lines**: 129–136, 8 lines

---

### `lemma ΨSq_poly_ne_zero`
- **Type**: `{n : ℤ} → n ≠ 0 → W.ΨSq n ≠ 0`
- **What**: The division polynomial `ΨSq n ∈ F[X]` is nonzero for `n ≠ 0`.
- **How**: By contradiction: if `ΨSq n = 0` then `isCoprime_Φ_ΨSq` (from `DivisionPolynomial`) gives `Φ n` is a unit, but `natDegree_Φ_pos` (mathlib) shows `deg(Φ n) > 0`, contradicting unit status (degree 0).
- **Hypotheses**: `n ≠ 0`, `W.toAffine.IsElliptic` (needed for `Δ ≠ 0`).
- **Uses from project**: uses `isCoprime_Φ_ΨSq` and `natDegree_Φ_pos` (both from project's `DivisionPolynomial` or inherited mathlib)
- **Used by**: `Ψ_ne_zero`
- **Visibility**: public
- **Lines**: 140–148, 9 lines

---

### `private lemma Ψ_ne_zero`
- **Type**: `{n : ℤ} → n ≠ 0 → W.Ψ n ≠ 0`
- **What**: The bivariate division polynomial `Ψ n` is nonzero for `n ≠ 0`.
- **How**: By contradiction: if `Ψ n = 0` then `preΨ n = 0` (by case split on the parity factor), so `ΨSq n = preΨ n ^ 2 * ... = 0`, contradicting `ΨSq_poly_ne_zero`. The case `ψ₂ = 0` is ruled out by showing this forces `char = 2`, `a₁ = a₃ = 0`, hence `Δ = 0`, contradicting `IsElliptic`. 
- **Hypotheses**: `n ≠ 0`, `W.toAffine.IsElliptic`.
- **Uses from project**: `ΨSq_poly_ne_zero`
- **Used by**: `mk_ψ_ne_zero`
- **Visibility**: private
- **Lines**: 152–201, **50 lines** (long proof)
- **Notes**: Long proof (50 lines) with embedded characteristic-2 discriminant argument. The `polynomialY ≠ 0` sub-argument is a repeated pattern in the project (see `InvariantDifferential.lean`).

---

### `lemma mk_ψ_ne_zero`
- **Type**: `{n : ℤ} → n ≠ 0 → CoordinateRing.mk W.toAffine (W.ψ n) ≠ 0`
- **What**: The image of `ψ n` in the coordinate ring `R` is nonzero for `n ≠ 0`.
- **How**: Uses `CoordinateRing.mk_ψ` to rewrite, then `AdjoinRoot.mk_ne_zero_of_natDegree_lt` with `Affine.monic_polynomial`, `Ψ_ne_zero`, and the degree bound `natDegree_Ψ_le ≤ natDegree(polynomial)` (the Weierstrass polynomial has degree 2 in Y).
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `Ψ_ne_zero`, `natDegree_Ψ_le`
- **Used by**: `ψ_ff_ne_zero`
- **Visibility**: public
- **Lines**: 204–208, 5 lines

---

### `lemma ψ_ff_ne_zero`
- **Type**: `{n : ℤ} → n ≠ 0 → ψ_ff W n ≠ 0`
- **What**: The image of `ψ_n` in `K(E)` is nonzero for `n ≠ 0`.
- **How**: Injectivity of `algebraMap R KE` (via `IsFractionRing.injective`) reduces to `mk_ψ_ne_zero`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `ψ_ff`, `mk_ψ_ne_zero`
- **Used by**: `ΨSq_ff_ne_zero`, `smulEval_generic_Z` (indirectly in `mulByInt_weierstrass`)
- **Visibility**: public
- **Lines**: 211–215, 5 lines

---

### `lemma ΨSq_ff_ne_zero`
- **Type**: `{n : ℤ} → n ≠ 0 → ΨSq_ff W n ≠ 0`
- **What**: The image of `ΨSq_n` in `K(E)` is nonzero for `n ≠ 0`.
- **How**: Uses `ψ_ff_sq_eq_ΨSq_ff` to rewrite as `(ψ_ff W n)^2`, then `pow_ne_zero 2 (ψ_ff_ne_zero W hn)`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `ΨSq_ff`, `ψ_ff_sq_eq_ΨSq_ff`, `ψ_ff_ne_zero`
- **Used by**: `mulByInt_x_transcendental`
- **Visibility**: public
- **Lines**: 218–220, 3 lines

---

### `private lemma evalEval_generic_eq_mk`
- **Type**: `(p.map (Polynomial.mapRingHom (algebraMap F KE))).evalEval (x_gen W) (y_gen W) = algebraMap R KE (CoordinateRing.mk W.toAffine p)` for `p : F[X][X]`
- **What**: Evaluating a bivariate polynomial (base-changed to `KE`) at the generic point gives the same result as applying `mk` to it and embedding in `K(E)`.
- **How**: Factors `algebraMap F KE` through `R`, applies `map_mapRingHom_evalEval`, then uses `AdjoinRoot.aeval_eq` to identify the evaluation.
- **Hypotheses**: None beyond section variables.
- **Uses from project**: `x_gen`, `y_gen`
- **Used by**: `smulEval_generic_Z`, `smulEval_generic_X`, `smulEval_generic_Y`
- **Visibility**: private
- **Lines**: 227–247, 21 lines
- **Notes**: `set_option linter.unusedSectionVars false` applied. Core evaluation lemma that connects polynomial evaluation at the generic point with coordinate ring images.

---

### `lemma smulEval_generic_Z`
- **Type**: `smulEval (W_KE W) (x_gen W) (y_gen W) n 2 = ψ_ff W n`
- **What**: The Z-component (index 2) of the Jacobian `smulEval` at the generic point equals `ψ_ff W n`.
- **How**: Unfolds `smulEval` to `((W.map ...).ψ n).evalEval`, then applies `map_ψ` and `evalEval_generic_eq_mk`.
- **Hypotheses**: None.
- **Uses from project**: `W_KE`, `x_gen`, `y_gen`, `ψ_ff`, `evalEval_generic_eq_mk`
- **Used by**: `jacobian_equation_smulEval` (implicitly), `mulByInt_weierstrass`
- **Visibility**: public
- **Lines**: 251–255, 5 lines

---

### `lemma smulEval_generic_X`
- **Type**: `smulEval (W_KE W) (x_gen W) (y_gen W) n 0 = Φ_ff W n`
- **What**: The X-component (index 0) of Jacobian `smulEval` at the generic point equals `Φ_ff W n`.
- **How**: Uses `map_φ` and `evalEval_generic_eq_mk`, then `φ_ff_eq_Φ_ff`.
- **Hypotheses**: None.
- **Uses from project**: `W_KE`, `x_gen`, `y_gen`, `Φ_ff`, `evalEval_generic_eq_mk`, `φ_ff_eq_Φ_ff`
- **Used by**: `mulByInt_weierstrass`
- **Visibility**: public
- **Lines**: 258–263, 6 lines

---

### `lemma smulEval_generic_Y`
- **Type**: `smulEval (W_KE W) (x_gen W) (y_gen W) n 1 = ω_ff W n`
- **What**: The Y-component (index 1) of Jacobian `smulEval` at the generic point equals `ω_ff W n`.
- **How**: Uses `map_ω` and `evalEval_generic_eq_mk`.
- **Hypotheses**: None.
- **Uses from project**: `W_KE`, `x_gen`, `y_gen`, `ω_ff`, `evalEval_generic_eq_mk`
- **Used by**: `mulByInt_weierstrass`
- **Visibility**: public
- **Lines**: 266–270, 5 lines

---

### `private lemma jacobian_equation_smulEval`
- **Type**: `WeierstrassCurve.Jacobian.Equation (W_KE W).toJacobian (smulEval (W_KE W) (x_gen W) (y_gen W) n)`
- **What**: The Jacobian equation holds for the `smulEval` at the generic point — `[n](x_gen, y_gen)` is a Jacobian point on `W_KE`.
- **How**: Uses `generic_nonsingular'` to get a nonsingular point, applies `zsmul_eq_smulEval` to identify `n •` the Jacobian lift with `smulEval`, then uses `.nonsingular` which implies `.1` = the equation.
- **Hypotheses**: None beyond section variables.
- **Uses from project**: `W_KE`, `x_gen`, `y_gen`, `generic_nonsingular'`
- **Used by**: unused in this file (dead code candidate — the proof of `mulByInt_weierstrass` duplicates this argument inline)
- **Visibility**: private
- **Lines**: 276–286, 11 lines
- **Notes**: UNUSED within this file and not referenced externally. Dead code candidate.

---

### `theorem mulByInt_weierstrass`
- **Type**: `n ≠ 0 → eval₂ (mulByInt_xHom W n) (mulByInt_y W n) W.toAffine.polynomial = 0`
- **What**: The pair `(mulByInt_x W n, mulByInt_y W n)` satisfies the Weierstrass equation of `W`, establishing that `[n]*(F[X][Y]/W.polynomial) → K(E)` is well-defined.
- **How**: Rewrites `eval₂` as `evalEval` at `(mulByInt_x, mulByInt_y)`, identifies this with the affine equation for `W_KE`, then uses Jacobian nonsingularity (via `zsmul_eq_smulEval` + `generic_nonsingular'`) and `Jacobian.equation_of_Z_ne_zero` (using `ψ_ff_ne_zero`) to extract the affine equation, finally matching coordinates via `smulEval_generic_X/Y/Z` and `ψ_ff_sq_eq_ΨSq_ff`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `mulByInt_xHom`, `mulByInt_y`, `W_KE`, `x_gen`, `y_gen`, `generic_nonsingular'`, `smulEval_generic_Z`, `smulEval_generic_X`, `smulEval_generic_Y`, `ψ_ff_ne_zero`, `ψ_ff_sq_eq_ΨSq_ff`, `mulByInt_x`
- **Used by**: `mulByInt_coordHom`
- **Visibility**: public
- **Lines**: 288–319, **32 lines** (long proof)
- **Notes**: The central theorem linking division polynomials to the Weierstrass equation.

---

### `noncomputable def mulByInt_coordHom`
- **Type**: `mulByInt_coordHom (n : ℤ) (hn : n ≠ 0) : R →+* KE`
- **What**: The ring homomorphism from the coordinate ring `R = F[X][Y]/(W)` to `K(E)` defined by sending `Y` to `mulByInt_y` and `X` to `mulByInt_x`.
- **How**: `AdjoinRoot.lift (mulByInt_xHom W n) (mulByInt_y W n) (mulByInt_weierstrass W n hn)` — the universal property of the adjoint root construction.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `mulByInt_xHom`, `mulByInt_y`, `mulByInt_weierstrass`
- **Used by**: `mulByInt_coordHom_injective`, `mulByInt_coordHom_map_nonZeroDivisors`, `mulByInt_pullbackRingHom`, `mulByInt_pullbackAlgHom`
- **Visibility**: public
- **Lines**: 323–324, 2 lines

---

### `private lemma algebraMap_poly_KE_injective`
- **Type**: `Function.Injective (algebraMap (Polynomial F) KE)`
- **What**: The ring homomorphism `F[X] → K(E)` is injective.
- **How**: Factors as `(algebraMap R KE).comp (algebraMap F[X] R)` and applies `IsFractionRing.injective` and `CoordinateRing.algebraMap_poly_injective`.
- **Hypotheses**: None.
- **Uses from project**: none (uses mathlib lemmas)
- **Used by**: `x_gen_transcendental`, `Φ_ff_transcendental`
- **Visibility**: private
- **Lines**: 328–331, 4 lines

---

### `lemma x_gen_transcendental`
- **Type**: `Transcendental F (x_gen W)`
- **What**: The generic x-coordinate `x_gen W` is transcendental over `F`.
- **How**: Uses `algebraMap_poly_KE_injective` + `transcendental_algebraMap_iff` (mathlib) to reduce to `Polynomial.transcendental_X F`.
- **Hypotheses**: None beyond section variables.
- **Uses from project**: `x_gen`, `algebraMap_poly_KE_injective`
- **Used by**: `mulByInt_x_transcendental`
- **Visibility**: public
- **Lines**: 335–340, 6 lines

---

### `private lemma Φ_ff_transcendental`
- **Type**: `n ≠ 0 → Transcendental F (Φ_ff W n)`
- **What**: The image of `Φ_n` in `K(E)` is transcendental over `F` for `n ≠ 0`.
- **How**: Uses `algebraMap_poly_KE_injective` + `transcendental_algebraMap_iff` + `Polynomial.transcendental` (mathlib) applied to `Φ n` with `natDegree_Φ_pos` and `leadingCoeff_Φ` (both from mathlib's `DivisionPolynomial.Degree`).
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `Φ_ff`, `algebraMap_poly_KE_injective`
- **Used by**: unused in this file (dead code candidate)
- **Visibility**: private
- **Lines**: 343–350, 8 lines
- **Notes**: UNUSED within this file. May be referenced from other files or may be dead code.

---

### `private lemma mulByInt_x_transcendental`
- **Type**: `n ≠ 0 → Transcendental F (mulByInt_x W n)`
- **What**: The x-coordinate `mulByInt_x W n = Φ_n / ΨSq_n` is transcendental over `F` for `n ≠ 0`.
- **How**: By contradiction: if algebraic over `F`, the subalgebra `S = F[mulByInt_x W n]` is algebraic over `F`. Then `x_gen` is integral over `S` via the monic witness polynomial `Φ_n(T) - mulByInt_x · ΨSq_n(T)` (degree `n²` > degree of subtracted term), so `x_gen` would be algebraic over `F` by `IsIntegral.trans_isAlgebraic`, contradicting `x_gen_transcendental`. Key: `div_mul_cancel₀` + `ΨSq_ff_ne_zero` + `sub_self` shows the witness evaluates to 0.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `mulByInt_x`, `Φ_ff`, `ΨSq_ff`, `x_gen_transcendental`, `ΨSq_ff_ne_zero`, `ψ_ff_sq_eq_ΨSq_ff`
- **Used by**: `mulByInt_xHom_injective`
- **Visibility**: private
- **Lines**: 361–421, **61 lines** (long proof)
- **Notes**: `set_option backward.isDefEq.respectTransparency false` applied at line 352 (no comment). Long integral-closure argument.

---

### `private lemma mulByInt_xHom_injective`
- **Type**: `n ≠ 0 → Function.Injective (mulByInt_xHom W n)`
- **What**: The ring hom `F[X] → K(E)` sending `X` to `mulByInt_x W n` is injective.
- **How**: Identifies `mulByInt_xHom` with `(Polynomial.aeval (mulByInt_x W n)).toRingHom` and applies `transcendental_iff_injective.mp (mulByInt_x_transcendental W n hn)`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `mulByInt_xHom`, `mulByInt_x`, `mulByInt_x_transcendental`
- **Used by**: `mulByInt_coordHom_injective`
- **Visibility**: private
- **Lines**: 424–430, 7 lines

---

### `theorem mulByInt_coordHom_injective`
- **Type**: `n ≠ 0 → Function.Injective (mulByInt_coordHom W n hn)`
- **What**: The coordinate ring hom `R →+* K(E)` is injective.
- **How**: Uses `exists_smul_basis_eq` (project: every element of `R` is `p·1 + q·mk W X`) and considers two cases: (i) `q = 0`: injectivity of `mulByInt_xHom` gives `p = 0`; (ii) `q ≠ 0`: derives contradiction via `coe_norm_smul_basis` (the norm of `p·1 + q·mk W X` maps to zero, hence is zero by `mulByInt_xHom_injective`, but `degree_norm_smul_basis` says the norm degree equals `max(2·deg(p), 2·deg(q)+3)`, which is `≠ ⊥` when `q ≠ 0`).
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `mulByInt_coordHom`, `mulByInt_xHom`, `mulByInt_y`, `mulByInt_xHom_injective` (via `hxinj`)
- **Used by**: `mulByInt_coordHom_map_nonZeroDivisors`
- **Visibility**: public
- **Lines**: 432–523, **92 lines** (long proof)
- **Notes**: Longest proof in the file. Uses mathlib's `CoordinateRing.exists_smul_basis_eq`, `coe_norm_smul_basis`, and `degree_norm_smul_basis`.

---

### `theorem mulByInt_coordHom_map_nonZeroDivisors`
- **Type**: `n ≠ 0 → s ∈ nonZeroDivisors R → IsUnit (mulByInt_coordHom W n hn s)`
- **What**: The coordinate ring hom sends non-zero-divisors to units in `K(E)`.
- **How**: `isUnit_iff_ne_zero` + injectivity via `mulByInt_coordHom_injective` (if the image is 0, the preimage is 0, contradicting membership in `nonZeroDivisors`).
- **Hypotheses**: `n ≠ 0`, `s ∈ nonZeroDivisors R`.
- **Uses from project**: `mulByInt_coordHom`, `mulByInt_coordHom_injective`
- **Used by**: `mulByInt_pullbackRingHom`
- **Visibility**: public
- **Lines**: 525–531, 7 lines

---

### `noncomputable def mulByInt_pullbackRingHom`
- **Type**: `mulByInt_pullbackRingHom (n : ℤ) (hn : n ≠ 0) : KE →+* KE`
- **What**: The ring endomorphism `K(E) → K(E)` induced by `[n]` — the pullback of the multiplication-by-n map on function fields.
- **How**: `IsLocalization.lift` applied to `mulByInt_coordHom` with the `nonZeroDivisors`-to-units witness `mulByInt_coordHom_map_nonZeroDivisors`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `mulByInt_coordHom`, `mulByInt_coordHom_map_nonZeroDivisors`
- **Used by**: `mulByInt_pullbackAlgHom`
- **Visibility**: public
- **Lines**: 533–536, 4 lines

---

### `noncomputable def mulByInt_pullbackAlgHom`
- **Type**: `mulByInt_pullbackAlgHom (n : ℤ) (hn : n ≠ 0) : KE →ₐ[F] KE`
- **What**: The algebra endomorphism `K(E) →ₐ[F] K(E)` induced by `[n]` — the final pullback map, which also fixes the base field `F`.
- **How**: Wraps `mulByInt_pullbackRingHom` with a proof that it commutes with `algebraMap F KE`. The commutativity proof uses `IsLocalization.lift_eq` to reduce to `mulByInt_coordHom` and then `AdjoinRoot.lift_mk` + `eval₂_C` to show constants are fixed.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `mulByInt_pullbackRingHom`, `mulByInt_coordHom`, `mulByInt_xHom`
- **Used by**: unused in this file; extensively used by `HasseWeil.Basic` and throughout the project
- **Visibility**: public
- **Lines**: 538–572, **35 lines** (long proof)
- **Notes**: The main deliverable of this file. Used by `Basic.lean` to build the `[n]*` isogeny machinery.

---

## Summary Table

| Name | Kind | Lines | Public | Sorries |
|------|------|-------|--------|---------|
| `x_gen` | def | 27–29 | yes | none |
| `y_gen` | def | 30–32 | yes | none |
| `W_KE` | def | 39 | yes | none |
| `W_KE_isElliptic` | instance | 42–43 | yes | none |
| `Φ_ff` | def | 47–49 | yes | none |
| `ΨSq_ff` | def | 50–52 | yes | none |
| `ψ_ff` | def | 53–55 | yes | none |
| `ω_ff` | def | 56–58 | yes | none |
| `mulByInt_x` | def | 59 | yes | none |
| `mulByInt_y` | def | 60 | yes | none |
| `mulByInt_xHom` | def | 62–64 | yes | none |
| `generic_equation` | lemma | 69–91 | yes | none |
| `generic_nonsingular'` | lemma | 95–97 | private | none |
| `ψ_ff_sq_eq_ΨSq_ff` | lemma | 100–111 | yes | none |
| `φ_ff_eq_Φ_ff` | lemma | 115–118 | yes | none |
| `natDegree_ψ₂_le` | lemma | 121–127 | private | none |
| `natDegree_Ψ_le` | lemma | 129–136 | private | none |
| `ΨSq_poly_ne_zero` | lemma | 140–148 | yes | none |
| `Ψ_ne_zero` | lemma | 152–201 | private | none |
| `mk_ψ_ne_zero` | lemma | 204–208 | yes | none |
| `ψ_ff_ne_zero` | lemma | 211–215 | yes | none |
| `ΨSq_ff_ne_zero` | lemma | 218–220 | yes | none |
| `evalEval_generic_eq_mk` | lemma | 227–247 | private | none |
| `smulEval_generic_Z` | lemma | 251–255 | yes | none |
| `smulEval_generic_X` | lemma | 258–263 | yes | none |
| `smulEval_generic_Y` | lemma | 266–270 | yes | none |
| `jacobian_equation_smulEval` | lemma | 276–286 | private | none |
| `mulByInt_weierstrass` | theorem | 288–319 | yes | none |
| `mulByInt_coordHom` | def | 323–324 | yes | none |
| `algebraMap_poly_KE_injective` | lemma | 328–331 | private | none |
| `x_gen_transcendental` | lemma | 335–340 | yes | none |
| `Φ_ff_transcendental` | lemma | 343–350 | private | none |
| `mulByInt_x_transcendental` | lemma | 361–421 | private | none |
| `mulByInt_xHom_injective` | lemma | 424–430 | private | none |
| `mulByInt_coordHom_injective` | theorem | 432–523 | yes | none |
| `mulByInt_coordHom_map_nonZeroDivisors` | theorem | 525–531 | yes | none |
| `mulByInt_pullbackRingHom` | def | 533–536 | yes | none |
| `mulByInt_pullbackAlgHom` | def | 538–572 | yes | none |

**Total**: 38 entries (some single-line defs counted individually; counting by declaration): 13 noncomputable defs + 1 instance + 24 lemmas/theorems = **38 declarations** in 573 lines.

Wait — recounting: the grep output gave 38 entries (including the single-line defs `mulByInt_x`, `mulByInt_y`). Let me recount from the grep output: 38 distinct `def`/`lemma`/`theorem`/`instance` lines.

**Unused (dead-code candidates within this file)**:
- `jacobian_equation_smulEval` (private, never called)
- `Φ_ff_transcendental` (private, never called within this file — may be used externally)
