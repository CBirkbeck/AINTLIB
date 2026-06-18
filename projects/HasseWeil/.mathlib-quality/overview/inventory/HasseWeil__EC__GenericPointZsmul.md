# Inventory: ./HasseWeil/EC/GenericPointZsmul.lean

**Imports**: `HasseWeil.EC.GenericPoint`, `HasseWeil.EC.MulByIntBaseCase`, `HasseWeil.EC.AffinePointMap`, `HasseWeil.EC.MulByIntComp`  
(The `GenericPoint` import transitively brings in `HasseWeil.MulByIntPullback`, which provides `smulEval_generic_X/Y/Z` and `zsmul_eq_smulEval`.)

**Module purpose**: Prove `n • genericPoint W = .some (mulByInt_x W n) (mulByInt_y W n) _` for all `n ≠ 0`, using the Jacobian–affine equivalence. Derive the composition law `[m] ∘ [n] = [m·n]` and related algebraic identities.

---

## Declarations

---

### `theorem genericPoint_eq_mulByInt_one`

- **Type**: `genericPoint W = Affine.Point.some (mulByInt_x W 1) (mulByInt_y W 1) _`
- **What**: The generic point of `W_KE` equals the `.some` point with `[1]`-coordinates.
- **How**: `unfold genericPoint`, then `congr 1` with `mulByInt_x_one.symm` and `mulByInt_y_one.symm`.
- **Hypotheses**: `W` an elliptic curve over a field.
- **Uses from project**: `mulByInt_x_one`, `mulByInt_y_one`, `generic_nonsingular`
- **Used by**: `zsmul_genericPoint_one`, `zsmul_genericPoint_add_one_of_witness`, `zsmul_genericPoint_two_of_witness`, `addX_addY_genericPoint_mulByInt_eq_succ` (via `show ... = rfl`)
- **Visibility**: public
- **Lines**: 69–75, proof ~5 lines

---

### `theorem one_zsmul_genericPoint`

- **Type**: `(1 : ℤ) • genericPoint W = genericPoint W`
- **What**: The trivial identity that `1`-fold scalar multiplication fixes the generic point.
- **How**: Immediate from `one_zsmul _` (mathlib).
- **Hypotheses**: None beyond curve setup.
- **Uses from project**: `genericPoint`
- **Used by**: `zsmul_genericPoint_one`
- **Visibility**: public
- **Lines**: 78–81, proof 1 line

---

### `theorem zsmul_genericPoint_one`

- **Type**: `(1 : ℤ) • genericPoint W = Affine.Point.some (mulByInt_x W 1) (mulByInt_y W 1) _`
- **What**: Base case of the main induction: `[1]•genericPoint` matches the `[1]`-coordinates.
- **How**: Combines `one_zsmul_genericPoint` and `genericPoint_eq_mulByInt_one`.
- **Hypotheses**: None beyond curve setup.
- **Uses from project**: `one_zsmul_genericPoint`, `genericPoint_eq_mulByInt_one`
- **Used by**: unused in file (exported for callers)
- **Visibility**: public
- **Lines**: 84–88, proof 2 lines

---

### `@[simp] theorem ψ_ff_neg`

- **Type**: `ψ_ff W (-n) = -ψ_ff W n`
- **What**: The division-polynomial sequence satisfies `ψ(-n) = -ψ(n)` in `K(E)`.
- **How**: Unfolds via `W.ψ_neg n` then applies `map_neg` twice.
- **Hypotheses**: None beyond curve setup.
- **Uses from project**: `ψ_ff`
- **Used by**: `mulByInt_y_neg`
- **Visibility**: public, `@[simp]`
- **Lines**: 105–108, proof 3 lines

---

### `private lemma W_KE_a₁`

- **Type**: `(W_KE W).a₁ = algebraMap F KE W.a₁`
- **What**: The `a₁` coefficient of the base-changed curve is the image of `W.a₁`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `W_KE`
- **Used by**: `mulByInt_y_neg`, `mulByInt_y_sub_negY`
- **Visibility**: private
- **Lines**: 111, proof inline (`rfl`)

---

### `private lemma W_KE_a₃`

- **Type**: `(W_KE W).a₃ = algebraMap F KE W.a₃`
- **What**: Same as `W_KE_a₁` but for `a₃`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `W_KE`
- **Used by**: `mulByInt_y_neg`, `mulByInt_y_sub_negY`
- **Visibility**: private
- **Lines**: 114, proof inline (`rfl`)

---

### `private lemma algebraMap_mk_CC`

- **Type**: `algebraMap R KE (mk W (C (C r))) = algebraMap F KE r`
- **What**: Evaluating a constant bivariate polynomial (via `C∘C`) in `K(E)` equals applying `algebraMap F KE` directly; follows from the scalar tower `F → R → KE`.
- **How**: `IsScalarTower.algebraMap_apply`.
- **Hypotheses**: `r : F`.
- **Uses from project**: `R`, `KE`
- **Used by**: `ω_ff_neg`, `ψc_ff_eq`
- **Visibility**: private
- **Lines**: 118–125, proof 4 lines

---

### `private lemma ω_ff_neg`

- **Type**: `ω_ff W (-n) = ω_ff W n + algebraMap F KE W.a₁ * Φ_ff W n * ψ_ff W n + algebraMap F KE W.a₃ * ψ_ff W n ^ 3`
- **What**: The `ω` component satisfies the negation expansion in `K(E)` (Silverman III.3.7).
- **How**: Rewrites via `W.ω_neg n` (polynomial identity), then `algebraMap_mk_CC` and `φ_ff_eq_Φ_ff`.
- **Hypotheses**: None beyond curve setup.
- **Uses from project**: `ω_ff`, `Φ_ff`, `ψ_ff`, `algebraMap_mk_CC`, `φ_ff_eq_Φ_ff`
- **Used by**: `mulByInt_y_neg`
- **Visibility**: private
- **Lines**: 128–138, proof ~10 lines

---

### `private lemma mulByInt_y_neg_aux`

- **Type**: `(y + a₁ * x * z + a₃ * z^3) / (-z)^3 = -(y / z^3) - a₁ * (x / z^2) - a₃`  (for `z ≠ 0`)
- **What**: Pure field-arithmetic identity: dividing the `ω_neg` numerator by `(-ψ)^3` collapses to `negY` form.
- **How**: `field_simp; ring`.
- **Hypotheses**: `z ≠ 0` in an abstract field `K`.
- **Uses from project**: none (generic field lemma)
- **Used by**: `mulByInt_y_neg`
- **Visibility**: private
- **Lines**: 142–147, proof 3 lines

---

### `theorem mulByInt_y_neg`

- **Type**: `mulByInt_y W (-n) = (W_KE W).toAffine.negY (mulByInt_x W n) (mulByInt_y W n)`  (for `n ≠ 0`)
- **What**: Y-coordinate negation formula: `[−n]` has y-coordinate equal to `negY([n])`.
- **How**: Uses `ψ_ff_neg`, `ω_ff_neg`, `W_KE_a₁`, `W_KE_a₃`, and `mulByInt_y_neg_aux` with `ψ_ff_ne_zero`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `ψ_ff_neg`, `ω_ff_neg`, `W_KE_a₁`, `W_KE_a₃`, `mulByInt_y_neg_aux`, `ψ_ff_ne_zero`, `ψ_ff_sq_eq_ΨSq_ff`, `mulByInt_y`, `mulByInt_x`
- **Used by**: `zsmul_genericPoint_neg_of_pos`
- **Visibility**: public
- **Lines**: 152–162, proof 11 lines

---

### `private lemma Φ_ff_eq`

- **Type**: `Φ_ff W n = x_gen W * ψ_ff W n ^ 2 - ψ_ff W (n+1) * ψ_ff W (n-1)`
- **What**: Bivariate formula for `Φ_ff` in terms of `x_gen` and `ψ_ff`.
- **How**: Uses `φ_ff_eq_Φ_ff` and the definitional identity `W.φ n = C X * W.ψ n^2 - W.ψ(n+1) * W.ψ(n-1)`.
- **Hypotheses**: None.
- **Uses from project**: `Φ_ff`, `x_gen`, `ψ_ff`, `φ_ff_eq_Φ_ff`
- **Used by**: `mulByInt_x_eq`
- **Visibility**: private
- **Lines**: 173–180, proof 7 lines

---

### `theorem mulByInt_x_eq`

- **Type**: `mulByInt_x W n = x_gen W - ψ_ff W (n+1) * ψ_ff W (n-1) / ψ_ff W n ^ 2`  (for `n ≠ 0`)
- **What**: Silverman III.3.7 form of `mulByInt_x`: x-coordinate of `[n]` is `x_gen` minus the ratio of adjacent division polynomials.
- **How**: `Φ_ff_eq` + `ψ_ff_sq_eq_ΨSq_ff` + `field_simp`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `Φ_ff_eq`, `ΨSq_ff`, `ψ_ff_sq_eq_ΨSq_ff`, `ψ_ff_ne_zero`, `mulByInt_x`
- **Used by**: `mulByInt_x_sub_mulByInt_x`, `addX_mulByInt_one_mulByInt_one`
- **Visibility**: public
- **Lines**: 185–190, proof 5 lines

---

### `@[simp] theorem ψ_ff_one`

- **Type**: `ψ_ff W 1 = 1`
- **What**: The first division polynomial in `K(E)` is 1.
- **How**: `W.ψ_one` + `simp` with `Affine.CoordinateRing.mk`.
- **Hypotheses**: None.
- **Uses from project**: `ψ_ff`
- **Used by**: `mulByInt_x_sub_mulByInt_x`, `addX_mulByInt_one_mulByInt_one`, `mulByInt_y_one_sub_negY`
- **Visibility**: public, `@[simp]`
- **Lines**: 193–197, proof 3 lines

---

### `private lemma isEllSequence_ψ_ff`

- **Type**: `ψ_ff W (m+n) * ψ_ff W (m-n) * ψ_ff W r^2 = ψ_ff W (m+r) * ψ_ff W (m-r) * ψ_ff W n^2 - ψ_ff W (n+r) * ψ_ff W (n-r) * ψ_ff W m^2`
- **What**: The elliptic divisibility sequence identity (Silverman Ex III.3.7(g)) for `ψ_ff` in `K(E)`.
- **How**: Transfers `W.isEllSequence_ψ m n r` via the ring map `R → KE`.
- **Hypotheses**: None.
- **Uses from project**: `ψ_ff`
- **Used by**: `mulByInt_x_sub_mulByInt_x`
- **Visibility**: private
- **Lines**: 202–211, proof 9 lines

---

### `theorem mulByInt_x_sub_mulByInt_x`

- **Type**: `mulByInt_x W m - mulByInt_x W n = ψ_ff W (n+m) * ψ_ff W (n-m) / (ψ_ff W n * ψ_ff W m) ^ 2`  (for `m, n ≠ 0`)
- **What**: The difference `[m].x - [n].x` equals a ratio of division polynomials.
- **How**: `mulByInt_x_eq` for both `m` and `n`, combined with `isEllSequence_ψ_ff (n, m, 1)` and `ψ_ff_one`, then `div_sub_div` and `ring`.
- **Hypotheses**: `m ≠ 0`, `n ≠ 0`.
- **Uses from project**: `mulByInt_x_eq`, `isEllSequence_ψ_ff`, `ψ_ff_one`, `ψ_ff_ne_zero`, `mulByInt_x`
- **Used by**: `mulByInt_x_ne_mulByInt_x`
- **Visibility**: public
- **Lines**: 217–233, proof 17 lines

---

### `theorem mulByInt_x_ne_mulByInt_x`

- **Type**: `mulByInt_x W m ≠ mulByInt_x W n`  (for `m, n ≠ 0`, `m ≠ n`, `m ≠ -n`)
- **What**: Distinctness of `[m].x` and `[n].x` when `m` and `n` are distinct and non-inverse.
- **How**: Reduces via `mulByInt_x_sub_mulByInt_x` to showing a ratio of nonzero `ψ_ff` values is nonzero.
- **Hypotheses**: `m ≠ 0`, `n ≠ 0`, `m ≠ n`, `m ≠ -n`.
- **Uses from project**: `mulByInt_x_sub_mulByInt_x`, `ψ_ff_ne_zero`
- **Used by**: (used in comments/docs, but not directly in proof bodies within this file — used in `zsmul_genericPoint_add_one_of_witness` docstring; actually not called in any proof here)
- **Visibility**: public
- **Lines**: 239–248, proof 10 lines
- **Notes**: The declaration count shows 5 appearances but they are all in comments and the declaration line itself; `mulByInt_x_ne_mulByInt_x` is not invoked in any proof body within this file.

---

### `private lemma ψc_ff_eq`

- **Type**: `algebraMap R KE (mk W (W.ψc n)) = 2 * ω_ff W n + algebraMap F KE W.a₁ * Φ_ff W n * ψ_ff W n + algebraMap F KE W.a₃ * ψ_ff W n ^ 3`
- **What**: The auxiliary polynomial `ψc n` in `K(E)` satisfies the `ω_spec` formula.
- **How**: Uses `W.ω_spec n` as the polynomial identity, then `algebraMap_mk_CC` and `φ_ff_eq_Φ_ff`.
- **Hypotheses**: None.
- **Uses from project**: `ω_ff`, `Φ_ff`, `ψ_ff`, `algebraMap_mk_CC`, `φ_ff_eq_Φ_ff`
- **Used by**: `mulByInt_y_sub_negY`
- **Visibility**: private
- **Lines**: 261–271, proof 10 lines

---

### `private lemma ψ_ff_mul_ψc_eq`

- **Type**: `ψ_ff W n * algebraMap R KE (mk W (W.ψc n)) = ψ_ff W (2 * n)`
- **What**: The `ψc_spec` identity: `ψ(n) * ψc(n) = ψ(2n)`, transferred to `K(E)`.
- **How**: Uses `W.ψc_spec n` and `map_mul`.
- **Hypotheses**: None.
- **Uses from project**: `ψ_ff`
- **Used by**: `mulByInt_y_sub_negY`
- **Visibility**: private
- **Lines**: 274–281, proof 7 lines

---

### `private lemma mulByInt_y_sub_negY_aux`

- **Type**: `y / z^3 - (-(y / z^3) - a₁ * (x / z^2) - a₃) = z * (2 * y + a₁ * x * z + a₃ * z^3) / z^4`  (for `z ≠ 0`)
- **What**: Pure field identity used in the `mulByInt_y_sub_negY` proof.
- **How**: `field_simp; ring`.
- **Hypotheses**: `z ≠ 0`.
- **Uses from project**: none.
- **Used by**: `mulByInt_y_sub_negY`
- **Visibility**: private
- **Lines**: 284–289, proof 3 lines

---

### `theorem mulByInt_y_sub_negY`

- **Type**: `mulByInt_y W n - (W_KE W).toAffine.negY (mulByInt_x W n) (mulByInt_y W n) = ψ_ff W (2*n) / ψ_ff W n ^ 4`  (for `n ≠ 0`)
- **What**: Y-coordinate minus its negation equals `ψ(2n)/ψ(n)^4` — the key Silverman III.3.7 identity at the generic point.
- **How**: Uses `W_KE_a₁`, `W_KE_a₃`, `ψ_ff_sq_eq_ΨSq_ff`, `mulByInt_y_sub_negY_aux`, `ψc_ff_eq`, `ψ_ff_mul_ψc_eq`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `W_KE_a₁`, `W_KE_a₃`, `ψ_ff_sq_eq_ΨSq_ff`, `mulByInt_y_sub_negY_aux`, `ψc_ff_eq`, `ψ_ff_mul_ψc_eq`, `ψ_ff_ne_zero`, `mulByInt_y`, `mulByInt_x`, `ω_ff`
- **Used by**: `mulByInt_y_one_sub_negY`
- **Visibility**: public
- **Lines**: 294–302, proof 9 lines

---

### `theorem mulByInt_y_one_sub_negY`

- **Type**: `mulByInt_y W 1 - (W_KE W).toAffine.negY (mulByInt_x W 1) (mulByInt_y W 1) = ψ_ff W 2`
- **What**: Specialization of `mulByInt_y_sub_negY` at `n = 1`, giving `ψ_ff 2` directly.
- **How**: `mulByInt_y_sub_negY` at `n=1`, plus `ψ_ff_one` and `div_one`.
- **Hypotheses**: None.
- **Uses from project**: `mulByInt_y_sub_negY`, `ψ_ff_one`
- **Used by**: `ψ_ff_two_eq`, `mulByInt_y_one_ne_negY`, `slopeOne_eq`
- **Visibility**: public
- **Lines**: 305–313, proof 9 lines

---

### `theorem ψ_ff_two_eq`

- **Type**: `ψ_ff W 2 = 2 * mulByInt_y W 1 + (W_KE W).a₁ * mulByInt_x W 1 + (W_KE W).a₃`
- **What**: Explicit evaluation of `ψ₂ = 2Y + a₁X + a₃` at the generic point.
- **How**: Via `mulByInt_y_one_sub_negY` and unfolding `negY`.
- **Hypotheses**: None.
- **Uses from project**: `mulByInt_y_one_sub_negY`, `ψ_ff`
- **Used by**: `addX_mulByInt_one_mulByInt_one`
- **Visibility**: public
- **Lines**: 318–323, proof 5 lines

---

### `private lemma algebraMap_Poly_KE_eval₂`

- **Type**: `algebraMap (Polynomial F) KE p = Polynomial.eval₂ (algebraMap F KE) (x_gen W) p`
- **What**: Algebramap from `F[X]` to `K(E)` equals evaluation at `x_gen W`, via the scalar tower.
- **How**: `Polynomial.aeval_algebraMap_apply` + simp.
- **Hypotheses**: `p : Polynomial F`.
- **Uses from project**: `x_gen`
- **Used by**: `ψ_ff_three_eq`
- **Visibility**: private
- **Lines**: 327–332, proof 5 lines

---

### `theorem generic_weierstrass`

- **Type**: `mulByInt_y W 1 ^ 2 + (W_KE W).a₁ * mulByInt_x W 1 * mulByInt_y W 1 + (W_KE W).a₃ * mulByInt_y W 1 = mulByInt_x W 1 ^ 3 + (W_KE W).a₂ * mulByInt_x W 1 ^ 2 + (W_KE W).a₄ * mulByInt_x W 1 + (W_KE W).a₆`
- **What**: The Weierstrass equation at the generic point in expanded form.
- **How**: `mulByInt_x_one`, `mulByInt_y_one`, then `Affine.equation_iff.mp (generic_equation W)`.
- **Hypotheses**: None.
- **Uses from project**: `mulByInt_x_one`, `mulByInt_y_one`, `generic_equation`
- **Used by**: `addX_mulByInt_one_mulByInt_one`
- **Visibility**: public
- **Lines**: 337–343, proof 7 lines

---

### `theorem ψ_ff_three_eq`

- **Type**: `ψ_ff W 3 = 3 * mulByInt_x W 1 ^ 4 + (W_KE W).b₂ * mulByInt_x W 1 ^ 3 + 3 * (W_KE W).b₄ * mulByInt_x W 1 ^ 2 + 3 * (W_KE W).b₆ * mulByInt_x W 1 + (W_KE W).b₈`
- **What**: Explicit evaluation of `ψ₃ = 3X^4 + b₂X^3 + 3b₄X^2 + 3b₆X + b₈` at the generic point.
- **How**: `W.ψ_three : W.ψ 3 = C W.Ψ₃`, then `algebraMap_Poly_KE_eval₂`, `Polynomial.eval₂_*`, and `map_bᵢ` identities.
- **Hypotheses**: None.
- **Uses from project**: `ψ_ff`, `mulByInt_x_one`, `algebraMap_Poly_KE_eval₂`
- **Used by**: `addX_mulByInt_one_mulByInt_one`
- **Visibility**: public
- **Lines**: 348–366, proof 19 lines

---

### `theorem mulByInt_y_one_ne_negY`

- **Type**: `mulByInt_y W 1 ≠ (W_KE W).toAffine.negY (mulByInt_x W 1) (mulByInt_y W 1)`
- **What**: The generic point is not equal to its own negation — the doubling tangent slope is well-defined.
- **How**: `mulByInt_y_one_sub_negY` gives `ψ_ff W 2`, which is nonzero by `ψ_ff_ne_zero`.
- **Hypotheses**: None.
- **Uses from project**: `mulByInt_y_one_sub_negY`, `ψ_ff_ne_zero`
- **Used by**: `slopeOne_eq`, `zsmul_genericPoint_two_of_witness`
- **Visibility**: public
- **Lines**: 370–373, proof 4 lines

---

### `noncomputable abbrev slopeOne`

- **Type**: `KE` — the tangent slope at `genericPoint W`
- **What**: Abbreviation for `(W_KE W).toAffine.slope x₁ x₁ y₁ y₁` where `(x₁, y₁) = ([1] coords)`. Used in the doubling formula.
- **How**: Abbreviation, no proof body.
- **Hypotheses**: None.
- **Uses from project**: `W_KE`, `mulByInt_x`, `mulByInt_y`
- **Used by**: `slopeOne_eq`, `addX_mulByInt_one_mulByInt_one`, `zsmul_genericPoint_two_of_witness`
- **Visibility**: public
- **Lines**: 385–387

---

### `theorem slopeOne_eq`

- **Type**: `slopeOne W = (3 * mulByInt_x W 1^2 + 2 * (W_KE W).a₂ * mulByInt_x W 1 + (W_KE W).a₄ - (W_KE W).a₁ * mulByInt_y W 1) / ψ_ff W 2`
- **What**: Unfolds `slopeOne` via `slope_of_Y_ne` (tangent branch), giving the explicit numerator/denominator formula.
- **How**: `Affine.slope_of_Y_ne rfl (mulByInt_y_one_ne_negY W)` + `mulByInt_y_one_sub_negY`.
- **Hypotheses**: None.
- **Uses from project**: `slopeOne`, `mulByInt_y_one_ne_negY`, `mulByInt_y_one_sub_negY`
- **Used by**: `addX_mulByInt_one_mulByInt_one`
- **Visibility**: public
- **Lines**: 390–397, proof 6 lines

---

### `theorem addX_mulByInt_one_mulByInt_one`

- **Type**: `(W_KE W).toAffine.addX (mulByInt_x W 1) (mulByInt_x W 1) (slopeOne W) = mulByInt_x W 2`
- **What**: The x-coordinate doubling identity: `addX([1].x, [1].x, slope)` equals `[2].x`. Closes Task #8.
- **How**: Unfolds `addX` and `slopeOne_eq`, rewrites with `mulByInt_x_eq`, `ψ_ff_one`, `ψ_ff_two_eq`, `ψ_ff_three_eq`, then uses `generic_weierstrass` via `linear_combination`.
- **Hypotheses**: None.
- **Uses from project**: `generic_weierstrass`, `slopeOne_eq`, `mulByInt_x_eq`, `ψ_ff_one`, `ψ_ff_two_eq`, `ψ_ff_three_eq`, `ψ_ff_ne_zero`, `slopeOne`
- **Used by**: unused in file (exported; referenced in docstring of `zsmul_genericPoint_two_of_witness`)
- **Visibility**: public
- **Lines**: 404–417, proof 14 lines

---

### `theorem zsmul_genericPoint_neg_of_pos`

- **Type**: If `n • genericPoint W = .some (mulByInt_x W n) (mulByInt_y W n) h_ns_pos`, then `(-n) • genericPoint W = .some (mulByInt_x W (-n)) (mulByInt_y W (-n)) _`.
- **What**: Reduces the negation case of `zsmul_genericPoint_eq` to the positive case.
- **How**: `neg_zsmul` + `Affine.Point.neg_some`, then `mulByInt_x_neg.symm` and `mulByInt_y_neg W n hn`.
- **Hypotheses**: `n ≠ 0`; positivity hypothesis as explicit witness.
- **Uses from project**: `mulByInt_x_neg`, `mulByInt_y_neg`
- **Used by**: unused in file (stepping-stone; superseded by `zsmul_genericPoint_eq` via Jacobian route)
- **Visibility**: public
- **Lines**: 433–445, proof ~13 lines

---

### `theorem zsmul_genericPoint_add_one_of_witness`

- **Type**: Parametric: given `n • genericPoint = .some [n] _` and addX/addY witnesses for step `n → n+1`, derives `(n+1) • genericPoint = .some [n+1] _`.
- **What**: Witness-parametric inductive step for `zsmul_genericPoint_eq`.
- **How**: `add_zsmul`, `one_zsmul`, `Affine.Point.add_of_X_ne`, then `Affine.Point.some.injEq`.
- **Hypotheses**: Positivity, addX/addY step witnesses, nonsingularity of `[n+1]`-coords.
- **Uses from project**: `genericPoint_eq_mulByInt_one`, `mulByInt_x`, `mulByInt_y`
- **Used by**: unused in file (scaffolding superseded by Jacobian approach)
- **Visibility**: public
- **Lines**: 463–482, proof 20 lines

---

### `theorem zsmul_genericPoint_two_of_witness`

- **Type**: Parametric: given addX/addY witnesses for `n=2`, derives `(2:ℤ) • genericPoint W = .some (mulByInt_x W 2) (mulByInt_y W 2) _`.
- **What**: Witness-parametric doubling case for `zsmul_genericPoint_eq`.
- **How**: `add_zsmul`, `one_zsmul`, `Affine.Point.add_self_of_Y_ne (mulByInt_y_one_ne_negY W)`, then `Affine.Point.some.injEq`.
- **Hypotheses**: addX/addY two-case witnesses.
- **Uses from project**: `genericPoint_eq_mulByInt_one`, `mulByInt_y_one_ne_negY`, `slopeOne`
- **Used by**: unused in file (scaffolding superseded by Jacobian approach)
- **Visibility**: public
- **Lines**: 488–503, proof 16 lines

---

### `theorem zsmul_genericPoint_eq`

- **Type**: For `n ≠ 0`, `∃ h : Nonsingular (mulByInt_x W n) (mulByInt_y W n), n • genericPoint W = .some (mulByInt_x W n) (mulByInt_y W n) h`.
- **What**: **The main theorem** (T-III-4-020b-2): the integer multiple `n • genericPoint` has coordinates given by the division-polynomial formulas. Proved via the Jacobian–affine equivalence.
- **How**: `zsmul_eq_smulEval` reduces `n • (fromAffine P)` to `⟦smulEval n⟧`; `smulEval_generic_Z` gives `smulEval n 2 = ψ_ff W n ≠ 0`; `Jacobian.nonsingular_of_Z_ne_zero` + `Jacobian.Point.toAffine_of_Z_ne_zero` convert back to affine; `smulEval_generic_X/Y` give the coordinate equalities; `toAffineAddEquiv` and `map_zsmul` relate the affine and Jacobian scalar multiplications.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `ψ_ff_ne_zero`, `generic_nonsingular`, `smulEval_generic_Z`, `smulEval_generic_X`, `smulEval_generic_Y`, `x_gen`, `y_gen`, `Φ_ff`, `ΨSq_ff`, `ψ_ff_sq_eq_ΨSq_ff`, `mulByInt_x`
- **Used by**: `zsmul_genericPoint_ne_zero`, `mulByInt_xy_inj`, `ψ_m_evalEval_mulByInt_ne_zero`, `mulByInt_pullback_mulByInt_x_eq_mul`, `mulByInt_pullback_mulByInt_y_eq_mul`, `addX_addY_genericPoint_mulByInt_eq_succ`
- **Visibility**: public
- **Lines**: 536–624, proof **89 lines**
- **Notes**: Longest proof in the file; uses 3 separate sub-arguments all routing through the Jacobian `smulEval` formalism. The `toAffineAddEquiv` roundtrip is repeated nearly verbatim in `zsmul_affine_point_eq`.

---

### `theorem zsmul_affine_point_eq`

- **Type**: For `m : ℤ`, any nonsingular `(x₀, y₀)` on `W_KE` with `ψ_m(x₀, y₀) ≠ 0`, the multiple `m • .some x₀ y₀ _` equals `.some (φ_m/ψ_m^2, ω_m/ψ_m^3) _`.
- **What**: Generalization of `zsmul_genericPoint_eq` to arbitrary base points on `W_KE` — same Jacobian proof at a general point.
- **How**: Identical to `zsmul_genericPoint_eq` but with `x₀, y₀` replacing `x_gen, y_gen`; `h_ψ_ne` corresponds to `smulEval ... 2 ≠ 0`.
- **Hypotheses**: `h_ns : Nonsingular x₀ y₀`, `h_ψ_ne : ψ_m(x₀, y₀) ≠ 0`.
- **Uses from project**: (same Jacobian infrastructure, but no file-local declarations; all mathlib Jacobian calls)
- **Used by**: `mulByInt_pullback_mulByInt_x_eq_mul`, `mulByInt_pullback_mulByInt_y_eq_mul`
- **Visibility**: public
- **Lines**: 640–703, proof **64 lines**
- **Notes**: The body is almost entirely duplicated from `zsmul_genericPoint_eq` with the base point generalized; significant code duplication opportunity.

---

### `private lemma zsmul_genericPoint_ne_zero`

- **Type**: For `n ≠ 0`, `(n : ℤ) • genericPoint W ≠ 0`.
- **What**: The generic point has infinite order in `(W_KE W).toAffine.Point`.
- **How**: `zsmul_genericPoint_eq` gives `.some ...` form; a `.some` point is never `.zero`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `zsmul_genericPoint_eq`
- **Used by**: `mulByInt_xy_inj`, `ψ_m_evalEval_mulByInt_ne_zero`
- **Visibility**: private
- **Lines**: 712–716, proof 4 lines

---

### `theorem mulByInt_xy_inj`

- **Type**: For `a, b ≠ 0`, if `mulByInt_x W a = mulByInt_x W b` and `mulByInt_y W a = mulByInt_y W b`, then `a = b`.
- **What**: Injectivity of `n ↦ [n]` as integers — if two nonzero multiplications give the same full point, the integers are equal.
- **How**: Contrapositive: `(a-b) • genericPoint = 0` by cancellation, contradicting `zsmul_genericPoint_ne_zero` since `a-b ≠ 0`.
- **Hypotheses**: `a, b ≠ 0`.
- **Uses from project**: `zsmul_genericPoint_eq`, `zsmul_genericPoint_ne_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 723–732, proof 10 lines

---

### `theorem ψ_m_evalEval_mulByInt_ne_zero`

- **Type**: For `m, n : ℤ` with `n ≠ 0` and `m * n ≠ 0`, `((W_KE W).ψ m).evalEval (mulByInt_x W n) (mulByInt_y W n) ≠ 0`.
- **What**: The division polynomial `ψ_m` does not vanish at the `[n]`-coordinates when `mn ≠ 0`. Key step for the composition law.
- **How**: `m • ([n] • gen) = (mn) • gen ≠ 0` by `zsmul_genericPoint_ne_zero`; a Jacobian argument then shows the Z-component is `ψ_m(P_n)`, so it must be nonzero.
- **Hypotheses**: `n ≠ 0`, `m * n ≠ 0`.
- **Uses from project**: `zsmul_genericPoint_eq`, `zsmul_genericPoint_ne_zero`
- **Used by**: `mulByInt_pullback_mulByInt_x_eq_mul`, `mulByInt_pullback_mulByInt_y_eq_mul`
- **Visibility**: public
- **Lines**: 739–795, proof **57 lines**
- **Notes**: Long proof; routes through the Jacobian `toAffineLift` and `Z=0` → `toAffineLift=0` argument.

---

### `theorem evalEval_φ_at_mulByInt_eq_eval₂_Φ`

- **Type**: `((W_KE W).φ m).evalEval (mulByInt_x W n) (mulByInt_y W n) = Polynomial.eval₂ (algebraMap F KE) (mulByInt_x W n) (W.Φ m)`  (for `n ≠ 0`)
- **What**: The bivariate evaluation of `φ_m` at `([n].x, [n].y)` equals the univariate evaluation of `Φ_m` at `[n].x` via the coordinate-ring quotient.
- **How**: `map_φ`, `eval₂_eval₂RingHom_apply`, `AdjoinRoot.lift_mk`, `Affine.CoordinateRing.mk_φ`, `AdjoinRoot.lift_of`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `mulByInt_xHom`, `mulByInt_y`, `mulByInt_x`, `mulByInt_weierstrass`
- **Used by**: `mulByInt_pullback_mulByInt_x_eq_mul`
- **Visibility**: public
- **Lines**: 807–821, proof 15 lines

---

### `theorem evalEval_ψ_sq_at_mulByInt_eq_eval₂_ΨSq`

- **Type**: `((W_KE W).ψ m).evalEval (mulByInt_x W n) (mulByInt_y W n) ^ 2 = Polynomial.eval₂ (algebraMap F KE) (mulByInt_x W n) (W.ΨSq m)`  (for `n ≠ 0`)
- **What**: The square of the bivariate evaluation of `ψ_m` at `([n].x, [n].y)` equals the univariate evaluation of `ΨSq_m` at `[n].x`.
- **How**: `map_ψ`, `eval₂_eval₂RingHom_apply`, then `AdjoinRoot.lift_mk` with `mk_Ψ_sq` to fold `ψ^2 → ΨSq`, then `AdjoinRoot.lift_of`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `mulByInt_xHom`, `mulByInt_y`, `mulByInt_x`, `mulByInt_weierstrass`
- **Used by**: `mulByInt_pullback_mulByInt_x_eq_mul`
- **Visibility**: public
- **Lines**: 824–844, proof 21 lines

---

### `theorem mulByInt_pullback_mulByInt_x_eq_mul`

- **Type**: `(mulByInt W.toAffine n).pullback (mulByInt_x W m) = mulByInt_x W (m * n)`  (for `m, n, mn ≠ 0`)
- **What**: The pullback of `[m].x` along `[n]` equals `[mn].x` — the x-coordinate composition law.
- **How**: `mulByInt_pullback_mulByInt_x`, then `evalEval_φ/ψ_sq` translation, then `zsmul_affine_point_eq` at `P_n` with scalar `m`, then `mul_zsmul` + `zsmul_genericPoint_eq (mn)`, then `Affine.Point.some.injEq`.
- **Hypotheses**: `m, n, m*n ≠ 0`.
- **Uses from project**: `ψ_m_evalEval_mulByInt_ne_zero`, `evalEval_φ_at_mulByInt_eq_eval₂_Φ`, `evalEval_ψ_sq_at_mulByInt_eq_eval₂_ΨSq`, `zsmul_genericPoint_eq`, `zsmul_affine_point_eq`, `mulByInt_pullback_mulByInt_x`
- **Used by**: `mulByInt_comp_eq_mul`
- **Visibility**: public
- **Lines**: 855–885, proof **31 lines** (strictly >30)

---

### `private lemma mulByInt_pullback_algebraMap_mk`

- **Type**: `(mulByInt W.toAffine n).pullback (algebraMap R KE (mk W p)) = mulByInt_coordHom W n hn (mk W p)`
- **What**: Pullback along `[n]` on a coordinate-ring element (coming from `algebraMap R KE ∘ mk`) equals the coordinate-hom applied to that element.
- **How**: Unfolds `mulByInt_pullbackAlgHom` and applies `IsLocalization.lift_eq`.
- **Hypotheses**: `n ≠ 0`, `p : Polynomial (Polynomial F)`.
- **Uses from project**: `mulByInt`, `mulByInt_pullbackAlgHom`, `mulByInt_pullbackRingHom`, `mulByInt_coordHom`
- **Used by**: `mulByInt_pullback_ω_ff_eq`, `mulByInt_pullback_ψ_ff_eq`
- **Visibility**: private
- **Lines**: 889–899, proof 10 lines

---

### `theorem mulByInt_pullback_ω_ff_eq`

- **Type**: `(mulByInt W.toAffine n).pullback (ω_ff W m) = ((W_KE W).ω m).evalEval (mulByInt_x W n) (mulByInt_y W n)`
- **What**: Pullback of `ω_ff W m` along `[n]` equals the bivariate evaluation of `ω m` at `([n].x, [n].y)`.
- **How**: `mulByInt_pullback_algebraMap_mk` + `AdjoinRoot.lift_mk` + `eval₂_eval₂RingHom_apply` + `map_ω`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `mulByInt_pullback_algebraMap_mk`, `ω_ff`, `mulByInt_xHom`, `mulByInt_y`, `mulByInt_x`, `mulByInt_weierstrass`
- **Used by**: `mulByInt_pullback_mulByInt_y_eq_mul`
- **Visibility**: public
- **Lines**: 903–916, proof 14 lines

---

### `theorem mulByInt_pullback_ψ_ff_eq`

- **Type**: `(mulByInt W.toAffine n).pullback (ψ_ff W m) = ((W_KE W).ψ m).evalEval (mulByInt_x W n) (mulByInt_y W n)`
- **What**: Pullback of `ψ_ff W m` along `[n]` equals the bivariate evaluation.
- **How**: Same structure as `mulByInt_pullback_ω_ff_eq` but for `ψ`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `mulByInt_pullback_algebraMap_mk`, `ψ_ff`, `mulByInt_xHom`, `mulByInt_y`, `mulByInt_x`, `mulByInt_weierstrass`
- **Used by**: `mulByInt_pullback_mulByInt_y_eq_mul`
- **Visibility**: public
- **Lines**: 919–932, proof 14 lines

---

### `theorem mulByInt_pullback_mulByInt_y_eq_mul`

- **Type**: `(mulByInt W.toAffine n).pullback (mulByInt_y W m) = mulByInt_y W (m * n)`  (for `m, n, mn ≠ 0`)
- **What**: The pullback of `[m].y` along `[n]` equals `[mn].y` — the y-coordinate composition law.
- **How**: `mulByInt_pullback_ω_ff_eq` + `mulByInt_pullback_ψ_ff_eq`, then `zsmul_affine_point_eq` at `P_n` with scalar `m`, then `mul_zsmul` + `zsmul_genericPoint_eq (mn)`, then `Affine.Point.some.injEq`.
- **Hypotheses**: `m, n, m*n ≠ 0`.
- **Uses from project**: `ψ_m_evalEval_mulByInt_ne_zero`, `mulByInt_pullback_ω_ff_eq`, `mulByInt_pullback_ψ_ff_eq`, `zsmul_genericPoint_eq`, `zsmul_affine_point_eq`
- **Used by**: `mulByInt_comp_eq_mul`
- **Visibility**: public
- **Lines**: 936–957, proof 22 lines

---

### `theorem mulByInt_comp_eq_mul`

- **Type**: For `m, n, mn ≠ 0`, `(mulByInt W.toAffine m).comp (mulByInt W.toAffine n) = mulByInt W.toAffine (m * n)`.
- **What**: **T-III-4-020b**: the isogenies `[m]` and `[n]` compose to `[mn]`.
- **How**: `mulByInt_comp_eq_mul_of_generator_witness` (from `MulByIntComp.lean`) reduces to showing pullback on generators; discharge x-generator via `mulByInt_pullback_x` + `mulByInt_pullback_mulByInt_x_eq_mul`; y-generator via `mulByInt_pullback_y` + `mulByInt_pullback_mulByInt_y_eq_mul`.
- **Hypotheses**: `m, n, m*n ≠ 0`.
- **Uses from project**: `mulByInt_comp_eq_mul_of_generator_witness`, `mulByInt_pullback_x`, `mulByInt_pullback_y`, `mulByInt_pullback_mulByInt_x_eq_mul`, `mulByInt_pullback_mulByInt_y_eq_mul`, `x_gen`
- **Used by**: unused in file (top-level result exported)
- **Visibility**: public
- **Lines**: 968–987, proof 20 lines

---

### `theorem addX_addY_genericPoint_mulByInt_eq_succ`

- **Type**: For `m ≠ 0` and `m+1 ≠ 0` with `x_gen W ≠ mulByInt_x W m`, `addX(x_gen, [m].x, slope) = [m+1].x` and `addY(x_gen, [m].x, y_gen, slope) = [m+1].y` where `slope = (y_gen - [m].y)/(x_gen - [m].x)`.
- **What**: The successor formula: chord-addition of `genericPoint` with `[m]P` gives `[m+1]P`-coordinates, with the slope written explicitly (avoiding `DecidableEq` diamond via `slope` function).
- **How**: `zsmul_genericPoint_eq` for `m` and `m+1`; `one_add_zsmul` (smul algebra); `Affine.Point.add_of_X_ne hx_ne`; `Affine.slope_of_X_ne hx_ne` to expand slope; `Affine.Point.some.injEq`.
- **Hypotheses**: `m ≠ 0`, `m+1 ≠ 0`, `x_gen W ≠ mulByInt_x W m`.
- **Uses from project**: `zsmul_genericPoint_eq`, `generic_nonsingular`, `x_gen`, `y_gen`, `mulByInt_x`, `mulByInt_y`
- **Used by**: unused in file (exported for `MulByIntAddRecurrence`)
- **Visibility**: public
- **Lines**: 1000–1019, proof 20 lines
- **Notes**: Deliberately avoids the `slope` function in the conclusion to sidestep a `DecidableEq` instance diamond between import boundaries (`AdditionPullback.instDecidableEqFunctionField` vs mathlib's `FractionRing.instDecidableEq`).

---

## Summary

| Category | Count |
|---|---|
| Total declarations | 47 |
| Defs (including abbrev) | 1 |
| Lemmas/theorems | 46 |
| Instances | 0 |
| Sorries | 0 |
| Private | 13 |
| Public | 34 |

**Long proofs** (>30 lines): `zsmul_genericPoint_eq` (89), `zsmul_affine_point_eq` (64), `ψ_m_evalEval_mulByInt_ne_zero` (57), `mulByInt_pullback_mulByInt_x_eq_mul` (31).

**Key API** (used by 3+ others within file): `zsmul_genericPoint_eq` (central hub, used by 6+ proofs), `slopeOne` (used in 3+ proofs), `mulByInt_x_eq` (used in 3+ proofs), `mulByInt_y_sub_negY` (used in 2 proofs but foundational).

**Unused within file** (dead-code candidates, likely used by other files): `zsmul_genericPoint_one`, `mulByInt_x_ne_mulByInt_x`, `addX_mulByInt_one_mulByInt_one`, `zsmul_genericPoint_neg_of_pos`, `zsmul_genericPoint_add_one_of_witness`, `zsmul_genericPoint_two_of_witness`, `mulByInt_xy_inj`, `mulByInt_comp_eq_mul`, `addX_addY_genericPoint_mulByInt_eq_succ`.
