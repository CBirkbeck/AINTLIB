# Inventory: ./HasseWeil/EvenFunctions.lean

**File**: `HasseWeil/EvenFunctions.lean`
**Module summary**: Defines and studies the negation involution on the coordinate ring of a Weierstrass curve (sending Y to `negPolynomial`), proving it is involutive and that its fixed points are exactly elements of F[X] (functions depending only on x). Formalises Silverman III.2.3.1. No sorries, no `set_option maxHeartbeats`. All declarations unused by other files in the project.

---

## Section `NegInvolution` (general commutative ring R)

---

### `lemma eval₂_polynomial_negPolynomial`

- **Type**: `W.polynomial.eval₂ (C : R[X] →+* R[X][Y]) W.negPolynomial = W.polynomial`
- **What**: The polynomial identity that results from evaluating W's Weierstrass polynomial at `negPolynomial` in place of Y yields the same polynomial back. This is the algebraic check that `negPolynomial` is another root of the defining equation.
- **How**: Pure `simp` expanding `eval₂` through `polynomial` and `negPolynomial`, closed by `ring`.
- **Hypotheses**: R a commutative ring, W a Weierstrass affine curve.
- **Uses from project**: none (pure mathlib polynomial API)
- **Used by**: `negInvolution_aux` (private, this file)
- **Visibility**: public
- **Lines**: 44–48, proof 3 lines
- **Notes**: none

---

### `private lemma negInvolution_aux`

- **Type**: `W.polynomial.eval₂ (AdjoinRoot.of W.polynomial) (AdjoinRoot.mk W.polynomial W.negPolynomial) = 0`
- **What**: The auxiliary well-definedness condition for `AdjoinRoot.lift`: evaluating `W.polynomial` in the coordinate ring via `mk negPolynomial` for Y gives 0, as required by the universal property.
- **How**: Rewrites `AdjoinRoot.of` as `(AdjoinRoot.mk).comp C`, applies `hom_eval₂` to factor the evaluation, uses `eval₂_polynomial_negPolynomial` to reduce to `W.polynomial`, then applies `AdjoinRoot.mk_self`.
- **Hypotheses**: R a commutative ring.
- **Uses from project**: `eval₂_polynomial_negPolynomial`
- **Used by**: `negInvolution` (def), `negInvolution_root`, `negInvolution_of`
- **Visibility**: private
- **Lines**: 50–56, proof 5 lines
- **Notes**: none

---

### `noncomputable def negInvolution`

- **Type**: `W.negInvolution : W.CoordinateRing →+* W.CoordinateRing`
- **What**: The negation involution ring homomorphism on the coordinate ring, defined via the universal property of `AdjoinRoot`, sending Y to `mk negPolynomial` and fixing coefficients from R[X].
- **How**: Uses `AdjoinRoot.lift` with the witness `negInvolution_aux`.
- **Hypotheses**: R a commutative ring.
- **Uses from project**: `negInvolution_aux`
- **Used by**: `negInvolution_root`, `negInvolution_of`, `negInvolution_mk_C`, `negInvolution_mk_Y`, `negInvolution_mk_negPolynomial`, `negInvolution_involutive`, `negInvolution_smul`, `negInvolution_smul_basis`, `negInvolution_eq_iff`
- **Visibility**: public
- **Lines**: 60–62, noncomputable def
- **Notes**: Key API declaration. Used by 8 other declarations in this file.

---

### `lemma negInvolution_root`

- **Type**: `W.negInvolution (AdjoinRoot.root W.polynomial) = AdjoinRoot.mk W.polynomial W.negPolynomial`
- **What**: The negation involution sends the canonical root (class of Y) to the class of `negPolynomial`.
- **How**: Directly `AdjoinRoot.lift_root` applied to `negInvolution_aux`.
- **Hypotheses**: R a commutative ring.
- **Uses from project**: `negInvolution_aux`, `negInvolution`
- **Used by**: `negInvolution_mk_Y`, `negInvolution_mk_negPolynomial`
- **Visibility**: public (`@[simp]`)
- **Lines**: 65–68, proof 1 line
- **Notes**: none

---

### `lemma negInvolution_of`

- **Type**: `W.negInvolution (AdjoinRoot.of W.polynomial p) = AdjoinRoot.of W.polynomial p` for `p : R[X]`
- **What**: The negation involution fixes the image of any polynomial `p : R[X]` under `AdjoinRoot.of`.
- **How**: Directly `AdjoinRoot.lift_of` applied to `negInvolution_aux`.
- **Hypotheses**: R a commutative ring.
- **Uses from project**: `negInvolution_aux`, `negInvolution`
- **Used by**: `negInvolution_mk_C`, `negInvolution_mk_negPolynomial`, `negInvolution_smul`
- **Visibility**: public (`@[simp]`)
- **Lines**: 71–74, proof 1 line
- **Notes**: none

---

### `lemma negInvolution_mk_C`

- **Type**: `W.negInvolution (AdjoinRoot.mk W.polynomial (C p)) = AdjoinRoot.mk W.polynomial (C p)` for `p : R[X]`
- **What**: The involution fixes constants (images of polynomials via `C`).
- **How**: Immediate from `negInvolution_of` (since `AdjoinRoot.mk ... (C p) = AdjoinRoot.of ... p`).
- **Hypotheses**: R a commutative ring.
- **Uses from project**: `negInvolution_of`
- **Used by**: `negInvolution_smul_basis` (indirectly via simp)
- **Visibility**: public (`@[simp]`)
- **Lines**: 77–80, proof 1 line
- **Notes**: none

---

### `lemma negInvolution_mk_Y`

- **Type**: `W.negInvolution (CoordinateRing.mk W Y) = CoordinateRing.mk W W.negPolynomial`
- **What**: The involution sends the class of Y (the coordinate function) to the class of `negPolynomial`.
- **How**: Changes `CoordinateRing.mk W Y` to `AdjoinRoot.root W.polynomial` by definitional equality, then applies `negInvolution_root`.
- **Hypotheses**: R a commutative ring.
- **Uses from project**: `negInvolution_root`, `negInvolution`
- **Used by**: `negInvolution_smul_basis`
- **Visibility**: public (`@[simp]`)
- **Lines**: 83–88, proof 3 lines
- **Notes**: none

---

### `lemma negInvolution_mk_negPolynomial`

- **Type**: `W.negInvolution (AdjoinRoot.mk W.polynomial W.negPolynomial) = AdjoinRoot.root W.polynomial`
- **What**: Applying the involution to `mk negPolynomial` returns the canonical root `mk Y`; this is the second half of involutivity.
- **How**: Rewrites `mk negPolynomial` as `-root - of(C a₁ · X + C a₃)` using `negPolynomial`'s definition, then applies `negInvolution_root` and `negInvolution_of` and closes by `ring`.
- **Hypotheses**: R a commutative ring.
- **Uses from project**: `negInvolution_root`, `negInvolution_of`, `negInvolution`
- **Used by**: `negInvolution_involutive`
- **Visibility**: public
- **Lines**: 91–100, proof 10 lines
- **Notes**: Proof requires explicit decomposition of `negPolynomial` to make the arithmetic visible.

---

### `lemma negInvolution_involutive`

- **Type**: `Function.Involutive W.negInvolution`
- **What**: The negation involution composed with itself is the identity ring homomorphism, i.e., it squares to the identity.
- **How**: Shows `W.negInvolution.comp W.negInvolution = RingHom.id _` using `AdjoinRoot.ringHom_ext` on two generators: on constants (by `simp` using `negInvolution_of`) and on the root (using `negInvolution_mk_negPolynomial`). Then applies `RingHom.congr_fun`.
- **Hypotheses**: R a commutative ring.
- **Uses from project**: `negInvolution_mk_negPolynomial`, `negInvolution`, `negInvolution_of`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 103–111, proof 8 lines
- **Notes**: none

---

### `lemma negInvolution_smul`

- **Type**: `W.negInvolution (p • f) = p • W.negInvolution f` for `p : R[X]`, `f : W.CoordinateRing`
- **What**: The negation involution commutes with the R[X]-module scalar multiplication on the coordinate ring.
- **How**: Uses `CoordinateRing.smul` to unfold to ring multiplication, then `map_mul` + `negInvolution_mk_C` (which fixes C-scalars).
- **Hypotheses**: R a commutative ring.
- **Uses from project**: `negInvolution_mk_C`, `negInvolution`
- **Used by**: `negInvolution_smul_basis`, `negInvolution_eq_iff`
- **Visibility**: public
- **Lines**: 114–116, proof 2 lines
- **Notes**: none

---

## Section `FixedPoints` (field F, char ≠ 2)

---

### `private lemma smul_basis_eq_of_eq`

- **Type**: For `p₁ q₁ p₂ q₂ : F[X]`, if `p₁ • 1 + q₁ • mk Y = p₂ • 1 + q₂ • mk Y` in `W.CoordinateRing`, then `p₁ = p₂ ∧ q₁ = q₂`.
- **What**: Linear independence of the basis `{1, mk Y}` in the coordinate ring over F[X]: two representations as `p • 1 + q • mk Y` must have equal coefficients.
- **How**: Subtracts to get `(p₁ - p₂) • 1 + (q₁ - q₂) • mk Y = 0`, then applies mathlib's `CoordinateRing.smul_basis_eq_zero` to extract `p₁ - p₂ = 0` and `q₁ - q₂ = 0`.
- **Hypotheses**: F a field (required for `smul_basis_eq_zero` in mathlib), W a Weierstrass curve over F.
- **Uses from project**: none (uses mathlib `CoordinateRing.smul_basis_eq_zero`)
- **Used by**: `negInvolution_eq_iff`
- **Visibility**: private
- **Lines**: 126–141, proof 14 lines
- **Notes**: none

---

### `lemma negInvolution_smul_basis`

- **Type**: `W.negInvolution (p • 1 + q • mk Y) = (p - q * (C W.a₁ * X + C W.a₃)) • 1 + (-q) • mk Y`
- **What**: Explicit formula for the negation involution acting on a general element written in the `{1, mk Y}` basis: it negates the Y-coefficient and adjusts the constant part by the `a₁x + a₃` term.
- **How**: Applies `map_add`, `negInvolution_smul` (twice), `map_one`, `negInvolution_mk_Y`, then expands `negPolynomial` and closes by `ring` + `simp`.
- **Hypotheses**: F a field (context of section), W a Weierstrass curve over F.
- **Uses from project**: `negInvolution_smul`, `negInvolution_mk_Y`
- **Used by**: `negInvolution_eq_iff`
- **Visibility**: public
- **Lines**: 146–152, proof 6 lines
- **Notes**: none

---

### `lemma negInvolution_eq_iff`

- **Type**: `[NeZero (2 : F)] → ∀ f : W.CoordinateRing, W.negInvolution f = f ↔ ∃ p : F[X], f = p • 1`
- **What**: The fixed points of the negation involution in the coordinate ring are exactly the elements lying in the image of F[X] (functions of x alone), i.e., the "even functions" of Silverman III.2.3.1.
- **How**: The forward direction decomposes `f = p • 1 + q • mk Y` via mathlib's `CoordinateRing.exists_smul_basis_eq`, applies `negInvolution_smul_basis` to get the fixed-point equation, uses `smul_basis_eq_of_eq` to read off the Y-coefficient condition `(-q) = q`, deduces `2q = 0` entrywise, and concludes `q = 0` using `NeZero (2 : F)`. The backward direction is immediate from `negInvolution_smul` + `map_one`.
- **Hypotheses**: F a field with `char ≠ 2` (encoded as `NeZero (2 : F)`), W a Weierstrass curve over F.
- **Uses from project**: `negInvolution_smul_basis`, `smul_basis_eq_of_eq`, `negInvolution_smul`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 156–175, proof 19 lines
- **Notes**: Main theorem of the file. The char ≠ 2 hypothesis is genuinely necessary (the result fails in char 2). Uses mathlib `CoordinateRing.exists_smul_basis_eq` from `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`.

---

## Summary table

| Name | Kind | Lines | Sorry | Proof length |
|---|---|---|---|---|
| `eval₂_polynomial_negPolynomial` | lemma | 44–48 | no | 3 |
| `negInvolution_aux` | private lemma | 50–56 | no | 5 |
| `negInvolution` | noncomputable def | 60–62 | n/a | — |
| `negInvolution_root` | lemma | 65–68 | no | 1 |
| `negInvolution_of` | lemma | 71–74 | no | 1 |
| `negInvolution_mk_C` | lemma | 77–80 | no | 1 |
| `negInvolution_mk_Y` | lemma | 83–88 | no | 3 |
| `negInvolution_mk_negPolynomial` | lemma | 91–100 | no | 10 |
| `negInvolution_involutive` | lemma | 103–111 | no | 8 |
| `negInvolution_smul` | lemma | 114–116 | no | 2 |
| `smul_basis_eq_of_eq` | private lemma | 126–141 | no | 14 |
| `negInvolution_smul_basis` | lemma | 146–152 | no | 6 |
| `negInvolution_eq_iff` | lemma | 156–175 | no | 19 |

**Total**: 13 declarations (1 noncomputable def, 12 lemmas; 2 private)
**Sorries**: none
**`set_option maxHeartbeats`**: none
**Proofs > 30 lines**: none
**Key API** (used by 3+): `negInvolution` (used by 8+ others in file)
**Unused** (no callers in this file or project): `eval₂_polynomial_negPolynomial` is used only via `negInvolution_aux`; `negInvolution_involutive` and `negInvolution_eq_iff` are not called anywhere else in this file or in any other project file (confirmed by grep).
