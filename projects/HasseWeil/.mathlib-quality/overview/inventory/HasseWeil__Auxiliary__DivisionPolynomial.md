# Inventory: ./HasseWeil/Auxiliary/DivisionPolynomial.lean

**File**: `HasseWeil/Auxiliary/DivisionPolynomial.lean`
**Total lines**: 861
**Description**: Extends mathlib's division polynomial development with the ω-family (Y-coordinate in Jacobian multiplication), the complement ψc, the invariant polynomial, and the key theorem `zsmul_eq_smulEval` expressing `[n]P` in division polynomial Jacobian coordinates. Also proves coprimality of Φ_n and ΨSq_n (Sutherland Lemma 6.8) and the degree formula for multiplication-by-n.

---

## Section: Invariant polynomial and ψc/ω family (lines 64–155)

### `def invar`
- **Type**: `W : WeierstrassCurve R → R[X]`
- **What**: The polynomial `6X² + b₂X + b₄`, the "invariant" polynomial appearing in division polynomial recurrences.
- **How**: Direct definition; no proof required.
- **Hypotheses**: `CommRing R`
- **Uses from project**: none
- **Used by**: `preΨ₄_add_Ψ₂Sq_sq`, `preΨ₄_add_ψ₂_pow_four`, `ω_spec` (via `invar`)
- **Visibility**: public
- **Lines**: 67 (definition, 1 line)
- **Notes**: none

### `def ψc`
- **Type**: `W : WeierstrassCurve R → ℤ → R[X][Y]`
- **What**: The complement of ψ(n) in ψ(2n), defined as `complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)`, so that `ψ(n) * ψc(n) = ψ(2n)`.
- **How**: Direct alias for `complEDS₂` from `EllipticDivisibilitySequence`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `EllipticDivisibilitySequence.complEDS₂`
- **Used by**: `ψc_spec`, `ω_spec`, `two_mul_ω`, `smulY_sub_negY`, `polyEval_cusp_ψc`
- **Visibility**: public
- **Lines**: 72 (definition, 1 line)
- **Notes**: none

### `lemma isEllSequence_ψ`
- **Type**: `IsEllSequence W.ψ`
- **What**: The family ψ(n) of division polynomials is an elliptic sequence (satisfies the net identity).
- **How**: Directly from `IsEllSequence.normEDS`, since ψ is defined as `normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: none (mathlib `IsEllSequence.normEDS`)
- **Used by**: `addZ_smulPoly`
- **Visibility**: public
- **Lines**: 74 (1 line)
- **Notes**: none

### `lemma C_Ψ₃_eq`
- **Type**: `C W.Ψ₃ = (3 * C X + CC W.a₂) * C W.Ψ₂Sq - polynomialX W ^ 2 + CC W.a₁ * W.ψ₂ * polynomialX W - CC W.a₁ ^ 2 * polynomial W`
- **What**: Expresses the third division polynomial Ψ₃ in terms of the fundamental Weierstrass curve polynomials and ψ₂.
- **How**: `simp_rw` unfolding Ψ₃, Ψ₂Sq, ψ₂, etc., then `C_simp` and `ring`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: none
- **Used by**: `addX_smul_one_smul_one`
- **Visibility**: public
- **Lines**: 76–79 (3 lines)
- **Notes**: none

### `lemma preΨ₄_add_Ψ₂Sq_sq`
- **Type**: `W.preΨ₄ + W.Ψ₂Sq ^ 2 = W.invar * W.Ψ₃`
- **What**: An algebraic identity relating preΨ₄ and Ψ₂Sq to the invariant and Ψ₃, used in the ω_spec proof.
- **How**: `rw` to unfold, then `linear_combination` using `W.b_relation` (the Weierstrass curve Brill-Noether/b relation) times X².
- **Hypotheses**: `CommRing R`
- **Uses from project**: `invar`
- **Used by**: `preΨ₄_add_ψ₂_pow_four`
- **Visibility**: public
- **Lines**: 81–83 (3 lines)
- **Notes**: none

### `lemma preΨ₄_add_ψ₂_pow_four`
- **Type**: `C W.preΨ₄ + W.ψ₂ ^ 4 = C (W.invar * W.Ψ₃) + 8 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq)`
- **What**: A bivariate polynomial identity needed in the proof of `ω_spec`.
- **How**: `simp_rw` using `ψ₂_sq` and `add_sq`, then applies `preΨ₄_add_Ψ₂Sq_sq`; finishes with `C_simp` and `ring`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `preΨ₄_add_Ψ₂Sq_sq`, `invar`
- **Used by**: `ω_spec`
- **Visibility**: public
- **Lines**: 85–88 (4 lines)
- **Notes**: none

### `lemma φ_mul_ψ`
- **Type**: `W.φ n * W.ψ n = C X * W.ψ n ^ 3 - EllSequence.invarDenom W.ψ 1 n`
- **What**: An identity decomposing the product φ(n)·ψ(n) in terms of ψ(n)³ and an elliptic-sequence "invarDenom" term.
- **How**: Unfolds `φ` and `EllSequence.invarDenom` and closes by `ring`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: none
- **Used by**: `ω_spec`
- **Visibility**: public
- **Lines**: 90–92 (3 lines)
- **Notes**: none

### `protected def ω`
- **Type**: `(n : ℤ) → R[X][Y]`
- **What**: The ω-family of bivariate division polynomials, whose evaluation at (x,y) gives the Y-coordinate (in Jacobian coordinates) of n·(x,y).
- **How**: Defined explicitly using `redInvarDenom`, `complEDSAux₂`, and `negPolynomial` from the elliptic divisibility sequence infrastructure.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `EllipticDivisibilitySequence` infrastructure (`redInvarDenom`, `complEDSAux₂`), `ψc`, polynomial map operators
- **Used by**: `ω_spec`, `ω_zero`, `ω_one`, `map_ω`, `ω_neg`, `ω_neg_eq_neg_negY`, `smulY`, `addY_smul_one_smul_one`, `smulY_neg`, `dblZ_smulPoly`
- **Visibility**: public (protected)
- **Lines**: 96–100 (5 lines)
- **Notes**: none

### `lemma ω_spec`
- **Type**: `2 * W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = W.ψc n`
- **What**: The fundamental identity relating ω(n) to ψc(n): `2ω(n) = ψc(n) - a₁φ(n)ψ(n) - a₃ψ(n)³`. This is the Y-doubling formula in division polynomial form.
- **How**: Uses `complEDS₂_eq_redInvarNum_sub`, `redInvar_normEDS`, `preΨ₄_add_ψ₂_pow_four`, `φ_mul_ψ`, `invarDenom_normEDS_eq_redInvarDenom_mul`, then unfolds ω definition and closes by `C_simp; ring`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `ψc`, `ω`, `preΨ₄_add_ψ₂_pow_four`, `φ_mul_ψ`, `invar`
- **Used by**: `two_mul_ω`, `smulY_sub_negY`, `polyEval_cusp_ω`, `dblZ_smulPoly`
- **Visibility**: public
- **Lines**: 104–110 (7 lines)
- **Notes**: none

### `lemma two_mul_ω`
- **Type**: `2 * W.ω n = W.ψc n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3`
- **What**: Rearrangement of `ω_spec` solving for `2ω(n)`.
- **How**: Follows from `ω_spec` by `abel`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `ω_spec`
- **Used by**: `universal_ω_neg`, `polyEval_cusp_ω`
- **Visibility**: public
- **Lines**: 112–114 (3 lines)
- **Notes**: none

### `lemma ψc_spec`
- **Type**: `W.ψ n * W.ψc n = W.ψ (2 * n)`
- **What**: The complementary factorisation: ψ(n) times its complement equals ψ(2n).
- **How**: Direct application of `normEDS_mul_complEDS₂` from the EDS library.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `ψc`
- **Used by**: `smulY_sub_negY`, `dblZ_smulPoly`
- **Visibility**: public
- **Lines**: 116–117 (2 lines)
- **Notes**: none

### `@[simp] lemma ω_zero`
- **Type**: `W.ω 0 = 1`
- **What**: Base case: ω(0) equals the constant polynomial 1.
- **How**: `simp` using `redInvarDenom_zero`, `complEDSAux₂_zero`, `ψ_zero`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `ω`
- **Used by**: unused in file (used externally by `MulByIntBaseCase.lean`)
- **Visibility**: public
- **Lines**: 119–120 (2 lines)
- **Notes**: none

### `@[simp] lemma ω_one`
- **Type**: `W.ω 1 = Y`
- **What**: Base case: ω(1) equals the polynomial Y (the Y-coordinate polynomial).
- **How**: Unfolds ω, applies `redInvarDenom_one`, `complEDSAux₂_one`, `ψ_one`, then `C_simp; ring`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `ω`
- **Used by**: unused in this file (used externally by `MulByIntBaseCase.lean`)
- **Visibility**: public
- **Lines**: 122–127 (6 lines)
- **Notes**: not referenced within this file

### `@[simp] lemma ψc_neg`
- **Type**: `W.ψc (-n) = W.ψc n`
- **What**: ψc is an even function: ψc(-n) = ψc(n).
- **How**: `simp [ψc]` unfolding to `complEDS₂` which is even.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `ψc`
- **Used by**: `universal_ω_neg`
- **Visibility**: public
- **Lines**: 128 (1 line)
- **Notes**: none

---

## Section: Maps across ring homomorphisms (lines 134–155)

### `@[simp] lemma map_ω`
- **Type**: `(W.map f).ω n = (W.ω n).map (mapRingHom f)`
- **What**: ω commutes with base change along a ring homomorphism f : R →+* S.
- **How**: `simp_rw` using `map_redInvarDenom`, `map_complEDSAux₂`, and the various `Affine.map_*` and `map_ψ` lemmas.
- **Hypotheses**: `CommRing R`, `CommRing S`, `f : R →+* S`
- **Uses from project**: `ω`
- **Used by**: `ω_neg`, `evalEval_ω`
- **Visibility**: public
- **Lines**: 141–144 (4 lines)
- **Notes**: none

### `private lemma universal_ω_neg`
- **Type**: `(letI W := Universal.curve; W.ω (-n) = W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3)`
- **What**: The negation formula ω(-n) = ω(n) + a₁φ(n)ψ(n) + a₃ψ(n)³, proved first on the universal curve (where 2 is a non-zero-divisor).
- **How**: Multiplies both sides by 2 (a non-zero-divisor on the universal curve via `Universal.Poly.two_ne_zero`), uses `two_mul_ω`, `ψc_neg`, `ψ_neg`, `φ_neg`, and closes by `ring`.
- **Hypotheses**: (implicit: on Universal.curve)
- **Uses from project**: `ω`, `two_mul_ω`, `ψc_neg`
- **Used by**: `ω_neg`
- **Visibility**: private
- **Lines**: 146–150 (5 lines)
- **Notes**: none

### `lemma ω_neg`
- **Type**: `W.ω (-n) = W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3`
- **What**: For any Weierstrass curve, ω(-n) = ω(n) + a₁φ(n)ψ(n) + a₃ψ(n)³. The negation formula for the ω-family.
- **How**: Transfers `universal_ω_neg` to an arbitrary curve via `W.map_specialize` (the universal curve specialization trick), `map_ω`, `map_φ`, `map_ψ`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `universal_ω_neg`, `map_ω`
- **Used by**: `smulY_neg`, `ω_neg_eq_neg_negY`
- **Visibility**: public
- **Lines**: 152–153 (2 lines)
- **Notes**: none

---

## Section: evalEval lemmas and cusp specializations (lines 168–211)

### `lemma evalEval_ψ₂`
- **Type**: `W.ψ₂.evalEval x y = polyEval W x y curve.ψ₂`
- **What**: ψ₂ evalEval at (x,y) equals the polyEval of the universal ψ₂ specialized to W.
- **How**: `simp_rw [polyEval_apply, ← map_ψ₂, map_specialize]`
- **Hypotheses**: `CommRing R`, `x y : R`
- **Uses from project**: none
- **Used by**: `polyEval_cusp_ψ`, `polyEval_cusp_ψc`
- **Visibility**: public
- **Lines**: 169–171 (3 lines)
- **Notes**: none

### `lemma evalEval_Ψ₃`
- **Type**: `(C W.Ψ₃).evalEval x y = polyEval W x y (C curve.Ψ₃)`
- **What**: Evaluating the constant polynomial C(Ψ₃) via evalEval matches polyEval on the universal Ψ₃.
- **How**: `simp_rw [polyEval_apply, map_C, ← map_Ψ₃, map_specialize]`
- **Hypotheses**: `CommRing R`, `x y : R`
- **Uses from project**: none
- **Used by**: `polyEval_cusp_ψ`, `polyEval_cusp_ψc`
- **Visibility**: public
- **Lines**: 172–173 (2 lines)
- **Notes**: none

### `lemma evalEval_preΨ₄`
- **Type**: `(C W.preΨ₄).evalEval x y = polyEval W x y (C curve.preΨ₄)`
- **What**: Evaluating the constant polynomial C(preΨ₄) via evalEval matches polyEval on the universal preΨ₄.
- **How**: `simp_rw [polyEval_apply, map_C, ← map_preΨ₄, map_specialize]`
- **Hypotheses**: `CommRing R`, `x y : R`
- **Uses from project**: none
- **Used by**: `polyEval_cusp_ψ`, `polyEval_cusp_ψc`
- **Visibility**: public
- **Lines**: 175–177 (3 lines)
- **Notes**: none

### `lemma evalEval_ψ`
- **Type**: `(W.ψ n).evalEval x y = polyEval W x y (curve.ψ n)`
- **What**: evalEval of ψ(n) matches polyEval of universal ψ(n).
- **How**: `simp_rw [polyEval_apply, ← map_ψ, map_specialize]`
- **Hypotheses**: `CommRing R`, `x y : R`, `n : ℤ`
- **Uses from project**: none
- **Used by**: unused within this file (potentially used externally)
- **Visibility**: public
- **Lines**: 180–181 (2 lines)
- **Notes**: not referenced within this file

### `lemma evalEval_φ`
- **Type**: `(W.φ n).evalEval x y = polyEval W x y (curve.φ n)`
- **What**: evalEval of φ(n) matches polyEval of universal φ(n).
- **How**: `simp_rw [polyEval_apply, ← map_φ, map_specialize]`
- **Hypotheses**: `CommRing R`, `x y : R`, `n : ℤ`
- **Uses from project**: none
- **Used by**: unused within this file (potentially used externally)
- **Visibility**: public
- **Lines**: 183–184 (2 lines)
- **Notes**: not referenced within this file

### `lemma evalEval_ω`
- **Type**: `(W.ω n).evalEval x y = polyEval W x y (curve.ω n)`
- **What**: evalEval of ω(n) matches polyEval of universal ω(n).
- **How**: `simp_rw [polyEval_apply, ← map_ω, map_specialize]`
- **Hypotheses**: `CommRing R`, `x y : R`, `n : ℤ`
- **Uses from project**: `map_ω`
- **Used by**: unused within this file (potentially used externally)
- **Visibility**: public
- **Lines**: 186–187 (2 lines)
- **Notes**: not referenced within this file

### `lemma cusp_ψ₂`
- **Type**: `cusp.ψ₂ = 2 * Y`
- **What**: On the cusp curve Y² = X³ (the `cusp` universal test curve), ψ₂ equals 2Y.
- **How**: `simp [cusp, ψ₂, Affine.polynomialY, C_ofNat]`
- **Hypotheses**: none (cusp is a specific curve over ℤ)
- **Uses from project**: none
- **Used by**: `polyEval_cusp_ψ`, `polyEval_cusp_ψc`
- **Visibility**: public
- **Lines**: 191 (1 line)
- **Notes**: none

### `lemma cusp_Ψ₃`
- **Type**: `cusp.Ψ₃ = 3 * X ^ 4`
- **What**: On the cusp curve, Ψ₃ equals 3X⁴.
- **How**: `simp [cusp, Ψ₃, b₂, b₄, b₆, b₈]`
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: `polyEval_cusp_ψ`, `polyEval_cusp_ψc`
- **Visibility**: public
- **Lines**: 192 (1 line)
- **Notes**: none

### `lemma cusp_preΨ₄`
- **Type**: `cusp.preΨ₄ = 2 * X ^ 6`
- **What**: On the cusp curve, preΨ₄ equals 2X⁶.
- **How**: `simp [cusp, preΨ₄, b₂, b₄, b₆, b₈]`
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: `polyEval_cusp_ψ`, `polyEval_cusp_ψc`
- **Visibility**: public
- **Lines**: 193 (1 line)
- **Notes**: none

### `lemma polyEval_cusp_ψ`
- **Type**: `polyEval cusp 1 1 (curve.ψ n) = n`
- **What**: On the cusp at (1,1), the universal ψ(n) evaluates to the integer n.
- **How**: Unfolds ψ as normEDS, applies evalEval lemmas for ψ₂/Ψ₃/preΨ₄ and cusp values, uses `normEDS_two_three_two` from the EDS library.
- **Hypotheses**: none
- **Uses from project**: `evalEval_ψ₂`, `evalEval_Ψ₃`, `evalEval_preΨ₄`, `cusp_ψ₂`, `cusp_Ψ₃`, `cusp_preΨ₄`
- **Used by**: `ψᵤ_ne_zero`, `polyEval_cusp_φ` (indirectly), `polyEval_cusp_ω` (indirectly)
- **Visibility**: public
- **Lines**: 195–198 (4 lines)
- **Notes**: none

### `lemma polyEval_cusp_φ`
- **Type**: `polyEval cusp 1 1 (curve.φ n) = 1`
- **What**: On the cusp at (1,1), the universal φ(n) evaluates to 1.
- **How**: Unfolds φ using `map_sub`, `map_mul`, `map_pow`, applies `polyEval_cusp_ψ`, then simplifies `eval₂_C`/`eval₂_X` and closes by `ring`.
- **Hypotheses**: none
- **Uses from project**: `polyEval_cusp_ψ`
- **Used by**: `polyToField_φ_ne_zero`
- **Visibility**: public
- **Lines**: 200–202 (3 lines)
- **Notes**: none

### `lemma polyEval_cusp_ψc`
- **Type**: `polyEval cusp 1 1 (curve.ψc n) = 2`
- **What**: On the cusp at (1,1), the universal ψc(n) evaluates to 2.
- **How**: Unfolds ψc using `map_complEDS₂`, applies `evalEval_ψ₂/Ψ₃/preΨ₄` and cusp values, uses `complEDS₂_two_three_two`.
- **Hypotheses**: none
- **Uses from project**: `ψc`, `evalEval_ψ₂`, `evalEval_Ψ₃`, `evalEval_preΨ₄`, `cusp_ψ₂`, `cusp_Ψ₃`, `cusp_preΨ₄`
- **Used by**: `polyEval_cusp_ω`
- **Visibility**: public
- **Lines**: 204–206 (3 lines)
- **Notes**: none

### `lemma polyEval_cusp_ω`
- **Type**: `polyEval cusp 1 1 (curve.ω n) = 1`
- **What**: On the cusp at (1,1), the universal ω(n) evaluates to 1.
- **How**: Uses `two_mul_ω` (applied via `congr`), `polyEval_cusp_ψc`, and specializes the cusp/Universal.curve structure.
- **Hypotheses**: none
- **Uses from project**: `two_mul_ω`, `polyEval_cusp_ψc`
- **Used by**: unused within this file
- **Visibility**: public
- **Lines**: 208–211 (4 lines)
- **Notes**: not referenced within this file

---

## Section: Universal field setup and ψᵤ (lines 214–242)

### `abbrev ψᵤ`
- **Type**: `(n : ℤ) → Universal.Field`
- **What**: The ψ family as elements of the universal function field: `polyToField (curve.ψ n)`.
- **How**: Direct abbreviation.
- **Hypotheses**: none
- **Uses from project**: none (uses `Universal` infrastructure)
- **Used by**: `ψᵤ_eq_normEDS`, `isEllSequence_ψᵤ`, `net_ψᵤ`, `ψᵤ_ne_zero`, `polyToField_ψ₂Sq`, `smulX`, `smulY`, `smulX_eq`, ..., and most lemmas in the Affine/Jacobian sections
- **Visibility**: public
- **Lines**: 214 (1 line)
- **Notes**: key API — used by 20+ declarations in this file

### `lemma ψᵤ_eq_normEDS`
- **Type**: `ψᵤ = normEDS (polyToField curve.ψ₂) (polyToField <| C curve.Ψ₃) (polyToField <| C curve.preΨ₄)`
- **What**: Identifies ψᵤ with the normEDS elliptic divisibility sequence in the universal field.
- **How**: `ext; rw [← map_normEDS]; rfl`
- **Hypotheses**: none
- **Uses from project**: `ψᵤ`
- **Used by**: `isEllSequence_ψᵤ`, `net_ψᵤ`
- **Visibility**: public
- **Lines**: 216–219 (4 lines)
- **Notes**: none

### `lemma isEllSequence_ψᵤ`
- **Type**: `IsEllSequence ψᵤ`
- **What**: ψᵤ is an elliptic divisibility sequence in the universal field.
- **How**: `rw [ψᵤ_eq_normEDS]; exact IsEllSequence.normEDS _ _ _`
- **Hypotheses**: none
- **Uses from project**: `ψᵤ_eq_normEDS`
- **Used by**: `smulX_sub_smulX`
- **Visibility**: public
- **Lines**: 221–222 (2 lines)
- **Notes**: none

### `lemma net_ψᵤ`
- **Type**: `EllSequence.net ψᵤ p q r s = 0`
- **What**: The net identity of ψᵤ vanishes (a consequence of being an elliptic sequence).
- **How**: `rw [ψᵤ_eq_normEDS]; apply net_normEDS`
- **Hypotheses**: `p q r s : ℤ`
- **Uses from project**: `ψᵤ_eq_normEDS`
- **Used by**: `smulY_add_sub_negY`
- **Visibility**: public
- **Lines**: 224–225 (2 lines)
- **Notes**: none

### `lemma ψᵤ_ne_zero`
- **Type**: `n ≠ 0 → ψᵤ n ≠ 0`
- **What**: For n ≠ 0, the universal division polynomial ψ(n) is nonzero in the function field.
- **How**: By contradiction: injects into the fraction field, specializes to the cusp via `ringEval cusp_equation_one_one`, uses `polyEval_cusp_ψ` to get ψ(n) evaluated to n, which is nonzero.
- **Hypotheses**: `n ≠ 0`
- **Uses from project**: `ψᵤ`, `polyEval_cusp_ψ`
- **Used by**: `smulX_eq`, `smulX_ne_zero`, `smulX_sub_smulX`, `smulY_sub_negY`, `smulY_one_ne_negY`, `slopeOne_eq_neg_div`, `addX_smul_one_smul_one`, `addY_smul_one_smul_one`, `smulY_neg`, `smulX_add`, `smulY_add_sub_negY`, `zsmul_point_eq_smulField`, `dblXYZ_smulField`, `addXYZ_smulField`, and others
- **Visibility**: public
- **Lines**: 227–231 (5 lines)
- **Notes**: KEY API — used by 20+ other declarations in this file

### `lemma polyToField_φ_ne_zero`
- **Type**: `polyToField (curve.φ n) ≠ 0`
- **What**: The universal φ(n) is nonzero in the function field.
- **How**: Contradiction via `IsFractionRing.injective`, specializing to the cusp using `polyEval_cusp_φ` which gives value 1.
- **Hypotheses**: none (implicit: n : ℤ from section variable)
- **Uses from project**: `polyEval_cusp_φ`
- **Used by**: `smulX_ne_zero`
- **Visibility**: public
- **Lines**: 233–237 (5 lines)
- **Notes**: none

### `lemma polyToField_ψ₂Sq`
- **Type**: `polyToField (C curve.Ψ₂Sq) = ψᵤ 2 ^ 2`
- **What**: The universal Ψ₂Sq in the field equals ψᵤ(2)².
- **How**: `rw [← map_pow, ψ_two, ψ₂_sq, map_add, map_mul, polyToField_polynomial, mul_zero, add_zero]`
- **Hypotheses**: none
- **Uses from project**: `ψᵤ`
- **Used by**: `addX_smul_one_smul_one`
- **Visibility**: public
- **Lines**: 239–240 (2 lines)
- **Notes**: none

---

## Section: Affine namespace — smulX, smulY and their properties (lines 242–470)

### `instance : AddGroup (curve⟮Universal.Field⟯)`
- **Type**: `AddGroup (curve⟮Universal.Field⟯)`
- **What**: Supplies the AddGroup instance for the rational points of the universal curve over Universal.Field.
- **How**: `inferInstance`
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: `zsmul_point_eq_smulX_smulY`
- **Visibility**: public (local instance via `open`)
- **Lines**: 420 (1 line)
- **Notes**: `attribute [local instance] Classical.propDecidable` is also set at line 244

### `def smulX`
- **Type**: `(n : ℤ) → Universal.Field`
- **What**: The X-coordinate of `n • (X, Y)` on the universal curve, defined as `φ(n) / ψ(n)²` in the function field.
- **How**: Direct definition.
- **Hypotheses**: none
- **Uses from project**: `ψᵤ`
- **Used by**: `smulX_zero`, `smulX_one`, `smulX_eq`, `smulX_neg`, `smulX_ne_zero`, `smulX_sub_smulX`, `smulX_two`, `smulX_sub_sub_smulX_add`, `smulX_ne_smulX`, `smulY_sub_negY`, `smulY_one_sub_negY`, `slopeOne`, `addX_smul_one_smul_one`, `smulY_neg`, `smulX_add`, `smulY_add_sub_negY`, `zsmul_point_eq_smulX_smulY`
- **Visibility**: public
- **Lines**: 248 (1 line)
- **Notes**: KEY API — referenced 60+ times in this file

### `def smulY`
- **Type**: `(n : ℤ) → Universal.Field`
- **What**: The Y-coordinate of `n • (X, Y)` on the universal curve, defined as `ω(n) / ψ(n)³`.
- **How**: Direct definition.
- **Hypotheses**: none
- **Uses from project**: `ψᵤ`, `ω`
- **Used by**: `smulY_zero`, `smulY_one`, `smulY_sub_negY`, `smulY_one_sub_negY`, `smulY_one_ne_negY`, `slopeOne`, `addX_smul_one_smul_one`, `addY_smul_one_smul_one`, `smulY_neg`, `smulX_add`, `smulY_add_sub_negY`, `zsmul_point_eq_smulX_smulY`
- **Visibility**: public
- **Lines**: 251 (1 line)
- **Notes**: KEY API — referenced 35+ times in this file

### `@[simp] lemma smulX_zero`
- **Type**: `smulX 0 = 0`
- **What**: X-coordinate of 0·(X,Y) is 0.
- **How**: `simp [smulX, ψᵤ]` using ψ(0) = 0, φ(0) = 0.
- **Hypotheses**: none
- **Uses from project**: `smulX`, `ψᵤ`
- **Used by**: `smulX_ne_smulX`
- **Visibility**: public
- **Lines**: 254 (1 line)
- **Notes**: none

### `@[simp] lemma smulY_zero`
- **Type**: `smulY 0 = 0`
- **What**: Y-coordinate of 0·(X,Y) is 0.
- **How**: `simp [smulY, ψᵤ]`
- **Hypotheses**: none
- **Uses from project**: `smulY`, `ψᵤ`
- **Used by**: unused within this file
- **Visibility**: public
- **Lines**: 255 (1 line)
- **Notes**: not referenced within this file

### `@[simp] lemma smulX_one`
- **Type**: `smulX 1 = polyToField (C X)`
- **What**: X-coordinate of 1·(X,Y) is the X generator.
- **How**: `simp [smulX, ψᵤ]` using ψ(1) = 1, φ(1) = X.
- **Hypotheses**: none
- **Uses from project**: `smulX`, `ψᵤ`
- **Used by**: `smulX_eq`, `smulX_two`, `addX_smul_one_smul_one`, `addY_smul_one_smul_one`, `smulY_one_ne_negY` (via `smulY_one_sub_negY`), `slopeOne_eq_neg_div`, `zsmul_point_eq_smulX_smulY`
- **Visibility**: public
- **Lines**: 256 (1 line)
- **Notes**: none

### `@[simp] lemma smulY_one`
- **Type**: `smulY 1 = polyToField Y`
- **What**: Y-coordinate of 1·(X,Y) is the Y generator.
- **How**: `simp [smulY, ψᵤ]` using ω(1) = Y, ψ(1) = 1.
- **Hypotheses**: none
- **Uses from project**: `smulY`, `ψᵤ`
- **Used by**: `smulY_one_sub_negY`, `slopeOne_eq_neg_div`, `addX_smul_one_smul_one`, `addY_smul_one_smul_one`, `zsmul_point_eq_smulX_smulY`
- **Visibility**: public
- **Lines**: 257 (1 line)
- **Notes**: none

### `lemma smulX_eq`
- **Type**: `n ≠ 0 → smulX n = smulX 1 - ψᵤ (n+1) * ψᵤ (n-1) / (ψᵤ n) ^ 2`
- **What**: Alternative formula for smulX n using adjacent division polynomials. The recurrence X-coordinate formula.
- **How**: Reformulates the division polynomial definition of φ(n) using `div_eq_iff` and algebraic manipulations.
- **Hypotheses**: `n ≠ 0`
- **Uses from project**: `smulX`, `smulX_one`, `ψᵤ`, `ψᵤ_ne_zero`
- **Used by**: `smulX_sub_smulX`, `smulX_two`, `smulX_ne_smulX` (indirectly)
- **Visibility**: public
- **Lines**: 259–264 (6 lines)
- **Notes**: none

### `lemma smulX_neg`
- **Type**: `smulX (-n) = smulX n`
- **What**: smulX is an even function (X-coordinates of n·P and (-n)·P coincide).
- **How**: `simp_rw [smulX, φ_neg, ψᵤ, ψ_neg, ← map_pow, neg_sq]`
- **Hypotheses**: none
- **Uses from project**: `smulX`, `ψᵤ`
- **Used by**: `zsmul_point_eq_smulX_smulY` (via neg case)
- **Visibility**: public
- **Lines**: 266–267 (2 lines)
- **Notes**: none

### `lemma smulX_ne_zero`
- **Type**: `n ≠ 0 → smulX n ≠ 0`
- **What**: For n ≠ 0, the X-coordinate smulX n is nonzero.
- **How**: `div_ne_zero polyToField_φ_ne_zero (pow_ne_zero _ <| ψᵤ_ne_zero h0)`
- **Hypotheses**: `n ≠ 0`
- **Uses from project**: `smulX`, `polyToField_φ_ne_zero`, `ψᵤ_ne_zero`
- **Used by**: `smulX_ne_smulX`
- **Visibility**: public
- **Lines**: 269–270 (2 lines)
- **Notes**: none

### `lemma smulX_sub_smulX`
- **Type**: `m ≠ 0 → n ≠ 0 → smulX m - smulX n = (ψᵤ (n+m) * ψᵤ (n-m)) / (ψᵤ n * ψᵤ m)^2`
- **What**: The difference of X-coordinates expressed via products of division polynomials. This is the key "addition formula" identity in division polynomial form.
- **How**: Uses `smulX_eq` twice, algebraic simplification, and `isEllSequence_ψᵤ` for the net identity.
- **Hypotheses**: `m ≠ 0`, `n ≠ 0`
- **Uses from project**: `smulX_eq`, `isEllSequence_ψᵤ`, `ψᵤ_ne_zero`
- **Used by**: `smulX_sub_sub_smulX_add`, `smulX_ne_smulX`, `smulX_add`, `smulY_add_sub_negY`
- **Visibility**: public
- **Lines**: 272–280 (9 lines)
- **Notes**: none

### `lemma smulX_two`
- **Type**: `smulX 2 = smulX 1 - ψᵤ 3 / (ψᵤ 2)^2`
- **What**: The X-coordinate doubling formula: smulX 2 = X - ψ₃/ψ₂².
- **How**: `simp [smulX_eq two_ne_zero, ψᵤ]`
- **Hypotheses**: none
- **Uses from project**: `smulX_eq`, `ψᵤ`
- **Used by**: `addX_smul_one_smul_one`, `addY_smul_one_smul_one`
- **Visibility**: public
- **Lines**: 282–283 (2 lines)
- **Notes**: none

### `lemma smulX_sub_sub_smulX_add`
- **Type**: `n+m ≠ 0 → n-m ≠ 0 → smulX (n-m) - smulX (n+m) = (ψᵤ (2*n) * ψᵤ (2*m)) / (ψᵤ (n+m) * ψᵤ (n-m))^2`
- **What**: A refined difference-of-X-coordinates identity with "symmetric" indices, used in the addition formula.
- **How**: `rw [smulX_sub_smulX sub_ne add_ne]` and index rewriting.
- **Hypotheses**: `n+m ≠ 0`, `n-m ≠ 0`
- **Uses from project**: `smulX_sub_smulX`
- **Used by**: `smulX_add`
- **Visibility**: public
- **Lines**: 285–288 (4 lines)
- **Notes**: none

### `lemma smulX_ne_smulX`
- **Type**: `m ≠ n → m ≠ -n → smulX m ≠ smulX n`
- **What**: If m ≠ ±n then smulX m ≠ smulX n (injectivity of X-coordinates modulo negation).
- **How**: Case analysis on m=0/n=0, then uses `smulX_sub_smulX` and `ψᵤ_ne_zero` to conclude the difference is nonzero.
- **Hypotheses**: `m ≠ n`, `m ≠ -n`
- **Uses from project**: `smulX_zero`, `smulX_ne_zero`, `smulX_sub_smulX`, `ψᵤ_ne_zero`
- **Used by**: `zsmul_point_eq_smulX_smulY`
- **Visibility**: public
- **Lines**: 290–299 (10 lines)
- **Notes**: none

### `private lemma smulY_sub_negY_aux`
- **Type**: `z ≠ 0 → y/z^3 - (-(y/z^3) - a₁*(x/z^2) - a₃) = z*(2*y + a₁*x*z + a₃*z^3)/z^4`
- **What**: An abstract field identity (no curve structure) used to simplify the smulY_sub_negY computation.
- **How**: `field_simp; ring`
- **Hypotheses**: `z ≠ 0`, in any field F
- **Uses from project**: none
- **Used by**: `smulY_sub_negY`
- **Visibility**: private
- **Lines**: 301–304 (4 lines)
- **Notes**: none

### `lemma smulY_sub_negY`
- **Type**: `n ≠ 0 → smulY n - negY (smulX n) (smulY n) = ψᵤ (2*n) / (ψᵤ n)^4`
- **What**: The difference between smulY(n) and its negation on the curve equals ψ(2n)/ψ(n)⁴. This is the key identity linking the Y-difference to the doubling division polynomial.
- **How**: `simp_rw` unfolding negY, smulX, smulY; uses `ψc_spec` and `ω_spec` to rewrite; applies `smulY_sub_negY_aux`.
- **Hypotheses**: `n ≠ 0`
- **Uses from project**: `smulX`, `smulY`, `ψᵤ`, `ψᵤ_ne_zero`, `ψc_spec`, `ω_spec`
- **Used by**: `smulY_one_sub_negY`, `smulX_add`, `smulY_add_sub_negY`
- **Visibility**: public
- **Lines**: 306–310 (5 lines)
- **Notes**: none

### `lemma smulY_one_sub_negY`
- **Type**: `smulY 1 - negY (smulX 1) (smulY 1) = ψᵤ 2`
- **What**: At n=1, the Y-difference formula specializes to just ψ₂.
- **How**: `rw [smulY_sub_negY one_ne_zero]` then simplifies using ψ(1)=1.
- **Hypotheses**: none
- **Uses from project**: `smulY_sub_negY`, `ψᵤ`
- **Used by**: `smulY_one_ne_negY`, `slopeOne_eq_neg_div`
- **Visibility**: public
- **Lines**: 312–314 (3 lines)
- **Notes**: none

### `lemma smulY_one_ne_negY`
- **Type**: `smulY 1 ≠ negY (smulX 1) (smulY 1)`
- **What**: The Y-coordinate of the generic point is not equal to its negation (equivalently, the generic point is not 2-torsion).
- **How**: `rw [← sub_ne_zero, smulY_one_sub_negY]; exact ψᵤ_ne_zero two_ne_zero`
- **Hypotheses**: none
- **Uses from project**: `smulY_one_sub_negY`, `ψᵤ_ne_zero`
- **Used by**: `slopeOne_eq_neg_div`, `addX_smul_one_smul_one`, `addY_smul_one_smul_one`, `zsmul_point_eq_smulX_smulY`
- **Visibility**: public
- **Lines**: 316–317 (2 lines)
- **Notes**: none

### `def slopeOne`
- **Type**: `Universal.Field`
- **What**: The slope of the tangent line at the generic point (smulX 1, smulY 1) on the universal curve, used in the doubling step.
- **How**: Direct definition as `Affine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)`.
- **Hypotheses**: none
- **Uses from project**: `smulX`, `smulY`
- **Used by**: `slopeOne_eq_neg_div`, `addX_smul_one_smul_one`, `addY_smul_one_smul_one`
- **Visibility**: public
- **Lines**: 320–321 (2 lines)
- **Notes**: none

### `lemma slopeOne_eq_neg_div`
- **Type**: `slopeOne = -polyToField curve.polynomialX / ψᵤ 2`
- **What**: The tangent slope at the generic point equals -polynomialX / ψ₂.
- **How**: Uses `Affine.slope_of_Y_ne rfl smulY_one_ne_negY`, applies `smulY_one_sub_negY`, unfolds coefficient maps; closes with `field_simp; norm_num`.
- **Hypotheses**: none
- **Uses from project**: `slopeOne`, `smulY_one_ne_negY`, `smulY_one_sub_negY`, `smulX_one`, `smulY_one`, `ψᵤ`, `ψᵤ_ne_zero`
- **Used by**: `addX_smul_one_smul_one`, `addY_smul_one_smul_one`
- **Visibility**: public
- **Lines**: 323–329 (7 lines)
- **Notes**: none

### `private lemma addX_smul_one_smul_one_aux`
- **Type**: `h0 : dy ≠ 0 → (-dx/dy)^2 + a₁*(-dx/dy) - a₂ - x - x - x = (dx^2 - a₁*dx*dy - (3*x+a₂)*dy^2)/dy^2`
- **What**: A pure field identity isolating the addX doubling formula's numerator.
- **How**: `field_simp; ring`
- **Hypotheses**: `dy ≠ 0`, in any field F
- **Uses from project**: none
- **Used by**: unused in file (helper for `addX_smul_one_smul_one` which uses `addX_smul_ring_identity` instead)
- **Visibility**: private
- **Lines**: 331–334 (4 lines)
- **Notes**: not referenced within this file; possibly leftover from a proof draft

### `private lemma addX_smul_ring_identity`
- **Type**: pure ring identity about X', ψ, a₁, a₂, cx
- **What**: An abstract ring identity used as the final step in `addX_smul_one_smul_one`.
- **How**: `ring`
- **Hypotheses**: in any field F
- **Uses from project**: none
- **Used by**: `addX_smul_one_smul_one`
- **Visibility**: private
- **Lines**: 336–338 (3 lines)
- **Notes**: none

### `lemma addX_smul_one_smul_one`
- **Type**: `Affine.addX (smulX 1) (smulX 1) slopeOne = smulX 2`
- **What**: Doubling the generic point's X-coordinate via the slope formula gives smulX 2.
- **How**: Uses `slopeOne_eq_neg_div`, `smulX_two`, `smulX_one`, `C_Ψ₃_eq`, `polyToField_ψ₂Sq`; closes with `field_simp` and `addX_smul_ring_identity`.
- **Hypotheses**: none
- **Uses from project**: `slopeOne_eq_neg_div`, `smulX_two`, `smulX_one`, `C_Ψ₃_eq`, `polyToField_ψ₂Sq`, `ψᵤ_ne_zero`, `ψᵤ`
- **Used by**: `addY_smul_one_smul_one`, `zsmul_point_eq_smulX_smulY`
- **Visibility**: public
- **Lines**: 340–348 (9 lines)
- **Notes**: none

### `private lemma addY_smul_one_smul_one_aux`
- **Type**: field identity relating the Y-addition formula components
- **What**: An abstract field identity isolating the addY doubling step.
- **How**: `field_simp; ring`
- **Hypotheses**: `dy ≠ 0`, in any field F
- **Uses from project**: none
- **Used by**: `addY_smul_one_smul_one`
- **Visibility**: private
- **Lines**: 350–353 (4 lines)
- **Notes**: none

### `lemma addY_smul_one_smul_one`
- **Type**: `Affine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2`
- **What**: Doubling the generic point's Y-coordinate via the slope formula gives smulY 2.
- **How**: Unfolds ω and smulY at n=2, uses `redInvarDenom_two`, `complEDSAux₂_two`, `addX_smul_one_smul_one`, `slopeOne_eq_neg_div`, EllSequence machinery, `smulX_one`, `smulY_one`, then `addY_smul_one_smul_one_aux`.
- **Hypotheses**: none
- **Uses from project**: `smulY`, `ω`, `slopeOne_eq_neg_div`, `addX_smul_one_smul_one`, `smulX_two`, `smulX_one`, `smulY_one`, `ψᵤ_ne_zero`, `ψᵤ`
- **Used by**: `zsmul_point_eq_smulX_smulY`
- **Visibility**: public
- **Lines**: 356–363 (8 lines)
- **Notes**: none

### `private lemma smulY_neg_aux`
- **Type**: `hz : z ≠ 0 → (y + a₁*x*z + a₃*z^3)/(-z)^3 = -(y/z^3) - a₁*(x/z^2) - a₃`
- **What**: A field identity for the negation of Jacobian Y-coordinates.
- **How**: `rw [neg_pow]; field_simp; ring`
- **Hypotheses**: `z ≠ 0`, in any field F
- **Uses from project**: none
- **Used by**: `smulY_neg`
- **Visibility**: private
- **Lines**: 365–367 (3 lines)
- **Notes**: none

### `lemma smulY_neg`
- **Type**: `n ≠ 0 → smulY (-n) = negY (smulX n) (smulY n)`
- **What**: The Y-coordinate of (-n)·P is the negation of n·P's Y-coordinate.
- **How**: `simp only` unfolding negY, smulX, smulY, applies `ψ_neg`, `ω_neg`; uses `smulY_neg_aux`.
- **Hypotheses**: `n ≠ 0`
- **Uses from project**: `smulX`, `smulY`, `ω_neg`, `ψᵤ`, `ψᵤ_ne_zero`
- **Used by**: `zsmul_point_eq_smulX_smulY`
- **Visibility**: public
- **Lines**: 369–372 (4 lines)
- **Notes**: none

### `private lemma smulX_add_aux`
- **Type**: abstract field identity for smulX_add
- **What**: Field algebra identity: n₂/n^4 * (m₂/m^4) / (a*s/(n*m)^2)^2 = n₂*m₂/(a*s)^2.
- **How**: `field_simp`
- **Hypotheses**: `m,n,a,s ≠ 0`, in any field F
- **Uses from project**: none
- **Used by**: `smulX_add`
- **Visibility**: private
- **Lines**: 374–377 (4 lines)
- **Notes**: none

### `lemma smulX_add`
- **Type**: `m ≠ 0 → n ≠ 0 → n+m ≠ 0 → n-m ≠ 0 → smulX (n+m) = smulX (n-m) - (smulY n - negY (smulX n) (smulY n)) * (smulY m - negY (smulX m) (smulY m)) / (smulX m - smulX n)^2`
- **What**: The addition formula for X-coordinates of scalar multiples: smulX(n+m) in terms of smulX(n-m) and the Y-differences at n,m.
- **How**: Uses `smulY_sub_negY`, `smulX_sub_smulX`, `smulX_add_aux`, `smulX_sub_sub_smulX_add` in a calc chain.
- **Hypotheses**: `m ≠ 0`, `n ≠ 0`, `n+m ≠ 0`, `n-m ≠ 0`
- **Uses from project**: `smulX`, `smulY`, `smulY_sub_negY`, `smulX_sub_smulX`, `smulX_add_aux`, `smulX_sub_sub_smulX_add`, `ψᵤ_ne_zero`
- **Used by**: `zsmul_point_eq_smulX_smulY`
- **Visibility**: public
- **Lines**: 379–394 (16 lines)
- **Notes**: none

### `private lemma smulY_add_sub_negY_aux`
- **Type**: abstract field identity for smulY_add_sub_negY
- **What**: A field identity expressing the Y-difference at (n+m) in terms of Y-differences and X-differences at n, m, and (n+m).
- **How**: `field_simp`
- **Hypotheses**: `m,n,a,s ≠ 0`, in any field F
- **Uses from project**: none
- **Used by**: `smulY_add_sub_negY`
- **Visibility**: private
- **Lines**: 396–401 (6 lines)
- **Notes**: none

### `lemma smulY_add_sub_negY`
- **Type**: `m ≠ 0 → n ≠ 0 → n+m ≠ 0 → n-m ≠ 0 → smulY(n+m) - negY(smulX(n+m))(smulY(n+m)) = (... formula ...)`
- **What**: The Y-difference at (n+m) expressed via Y-differences and X-differences at n, m. A key step in showing smulY_add satisfies the addition law.
- **How**: Uses `smulY_sub_negY`, `smulX_sub_smulX`, `smulY_add_sub_negY_aux`, `net_ψᵤ` (via `EllSequence.net_add_sub_iff`) for the final linear combination.
- **Hypotheses**: `m ≠ 0`, `n ≠ 0`, `n+m ≠ 0`, `n-m ≠ 0`
- **Uses from project**: `smulY_sub_negY`, `smulX_sub_smulX`, `smulY_add_sub_negY_aux`, `net_ψᵤ`, `ψᵤ_ne_zero`
- **Used by**: `zsmul_point_eq_smulX_smulY`
- **Visibility**: public
- **Lines**: 403–415 (13 lines)
- **Notes**: none

### `theorem zsmul_point_eq_smulX_smulY`
- **Type**: `n ≠ 0 → ∃ h : Nonsingular _ (smulX n) (smulY n), n • Affine.point = .some _ _ h`
- **What**: For n ≠ 0, the n-th scalar multiple of the universal affine point has coordinates (smulX n, smulY n). The main inductive identification of scalar multiplication with division polynomials.
- **How**: Strong induction on n (via `Int.negInduction` and `Nat.strong_induction_on`). Base case n=1 uses the equation/nonsingularity of the point. The doubling step uses `addX_smul_one_smul_one` and `addY_smul_one_smul_one`. The addition step uses `smulX_add`, `smulY_add_sub_negY`, `smulX_ne_smulX` for the X-inequality, and `smulY_neg` for the negation case.
- **Hypotheses**: `n ≠ 0`
- **Uses from project**: `smulX`, `smulY`, `smulX_one`, `smulY_one`, `smulX_neg`, `smulY_neg`, `smulY_one_ne_negY`, `smulX_ne_smulX`, `addX_smul_one_smul_one`, `addY_smul_one_smul_one`, `smulX_add`, `smulY_add_sub_negY`
- **Used by**: `zsmul_point_ne_zero` (Affine), `zsmul_point_eq_smulField`
- **Visibility**: public
- **Lines**: 423–464 (41 lines)
- **Notes**: Proof >30 lines. Strong induction with separate doubling and addition cases.

### `lemma zsmul_point_ne_zero` (Affine)
- **Type**: `n ≠ 0 → n • Affine.point ≠ 0`
- **What**: For n ≠ 0, n times the universal affine point is not zero.
- **How**: Applies `zsmul_point_eq_smulX_smulY` to get some-form, then `exact fun h => nomatch h`.
- **Hypotheses**: `n ≠ 0`
- **Uses from project**: `zsmul_point_eq_smulX_smulY`
- **Used by**: `zsmul_point_ne_zero` (Jacobian)
- **Visibility**: public
- **Lines**: 465–469 (5 lines)
- **Notes**: none

---

## Section: Jacobian namespace (lines 475–630)

### `lemma zsmul_point_ne_zero` (Jacobian)
- **Type**: `n ≠ 0 → n • Jacobian.point ≠ 0`
- **What**: For n ≠ 0, n times the universal Jacobian point is not zero.
- **How**: Reduces to the Affine case via `Point.toAffineAddEquiv`.
- **Hypotheses**: `n ≠ 0`
- **Uses from project**: `Affine.zsmul_point_ne_zero`
- **Used by**: `zsmul_point_ne`
- **Visibility**: public
- **Lines**: 479–485 (7 lines)
- **Notes**: none

### `lemma point_point`
- **Type**: `Jacobian.point.point = ⟦![polyToField (C X), polyToField Y, 1]⟧`
- **What**: The Jacobian point's underlying projective representative.
- **How**: `rfl`
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 487 (1 line)
- **Notes**: not referenced within this file

### `abbrev smulPoly`
- **Type**: `(n : ℤ) → Fin 3 → Poly`
- **What**: The triple (φ(n), ω(n), ψ(n)) of universal polynomials encoding the Jacobian coordinates of n·P.
- **How**: Direct definition as `![curve.φ n, curve.ω n, curve.ψ n]`.
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: `smulRing`, `smulField`, `zsmul_point_eq_smulField`, `ω_neg_eq_neg_negY`, `smulPoly_neg`, `dblZ_smulPoly`, `addZ_smulPoly`, `addXYZ_smulField`
- **Visibility**: public
- **Lines**: 490 (1 line)
- **Notes**: none

### `abbrev smulRing`
- **Type**: `(n : ℤ) → Fin 3 → Universal.Ring`
- **What**: The smulPoly triple mapped into the coordinate ring (quotient by the curve equation).
- **How**: `AdjoinRoot.mk _ ∘ smulPoly n`
- **Hypotheses**: none
- **Uses from project**: `smulPoly`
- **Used by**: `algebraMap_comp_smulRing`, `smulRing_neg`, `dblXYZ_smulRing`, `addXYZ_smulRing`, `addXYZ_smulRing₁`, `ringEval_comp_smulRing`
- **Visibility**: public
- **Lines**: 492 (1 line)
- **Notes**: none

### `abbrev smulField`
- **Type**: `(n : ℤ) → Fin 3 → Universal.Field`
- **What**: The smulPoly triple mapped into the universal function field.
- **How**: `polyToField ∘ smulPoly n`
- **Hypotheses**: none
- **Uses from project**: `smulPoly`
- **Used by**: `algebraMap_comp_smulRing`, `zsmul_point_eq_smulField`, `smulField_neg`, `smulField_zero`, `dblXYZ_smulField`, `addXYZ_smulField`, `addXYZ_smulField₁`
- **Visibility**: public
- **Lines**: 494 (1 line)
- **Notes**: none

### `lemma algebraMap_comp_smulRing`
- **Type**: `algebraMap _ _ ∘ smulRing n = smulField n`
- **What**: The algebraMap from Universal.Ring to Universal.Field commutes with smulRing/smulField.
- **How**: `ext i; fin_cases i <;> rfl`
- **Hypotheses**: none
- **Uses from project**: `smulRing`, `smulField`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 496–497 (2 lines)
- **Notes**: not referenced within this file

### `theorem zsmul_point_eq_smulField`
- **Type**: `(n • Jacobian.point).point = ⟦smulField n⟧`
- **What**: The Jacobian coordinates of n times the universal point equal the smulField triple. The Jacobian version of the scalar multiplication formula.
- **How**: Case n=0 by direct computation. For n≠0, uses `Affine.zsmul_point_eq_smulX_smulY`, converts via `toAffineAddEquiv`, then applies `Quotient.sound` with a unit scalar giving the Jacobian scaling.
- **Hypotheses**: none (n : ℤ from context)
- **Uses from project**: `smulField`, `smulPoly`, `Affine.zsmul_point_eq_smulX_smulY`, `ψᵤ_ne_zero`, `ψᵤ`, `Affine.smulX`, `Affine.smulY`
- **Used by**: `nonsingular_smulField`, `two_zsmul_point_eq_dblXYZ`, `add_point_of_ne_eq_addXYZ`, `zsmul_point_ne`, `dblXYZ_smulField`, `addXYZ_smulField`
- **Visibility**: public
- **Lines**: 500–511 (12 lines)
- **Notes**: none

### `private lemma ω_neg_eq_neg_negY`
- **Type**: `curve.ω (-n) = -negY curvePoly (smulPoly n)`
- **What**: Connects ω(-n) to the Jacobian negation of smulPoly n.
- **How**: Unfolds smulPoly, negY, and applies `ω_neg` with algebraic simplification.
- **Hypotheses**: none
- **Uses from project**: `smulPoly`, `ω_neg`
- **Used by**: `smulPoly_neg`
- **Visibility**: private
- **Lines**: 513–517 (5 lines)
- **Notes**: none

### `lemma smulPoly_neg`
- **Type**: `smulPoly (-n) = (-1 : Poly) • neg curvePoly (smulPoly n)`
- **What**: Negation of the index in smulPoly corresponds to the Jacobian negation map (up to scalar -1).
- **How**: `simp [smulPoly, ω_neg_eq_neg_negY, neg, smul_fin3, Odd.neg_pow]`
- **Hypotheses**: none
- **Uses from project**: `smulPoly`, `ω_neg_eq_neg_negY`
- **Used by**: `smulRing_neg`, `smulField_neg`
- **Visibility**: public
- **Lines**: 519–520 (2 lines)
- **Notes**: none

### `lemma smulRing_neg`
- **Type**: `smulRing (-n) = (-1 : Universal.Ring) • neg curveRing (smulRing n)`
- **What**: smulRing negation formula: smulRing(-n) is the Jacobian negation of smulRing(n) scaled by -1.
- **How**: `simp_rw` using `smulPoly_neg`, `map_neg`, `map_one`.
- **Hypotheses**: none
- **Uses from project**: `smulRing`, `smulPoly_neg`
- **Used by**: `zsmul_eq_smulEval` (via `ringEval_comp_smulRing`)
- **Visibility**: public
- **Lines**: 522–524 (3 lines)
- **Notes**: none

### `private lemma dblZ_smulPoly`
- **Type**: `dblZ curvePoly (smulPoly n) = curve.ψ (2*n)`
- **What**: The Jacobian doubling Z-formula applied to smulPoly gives ψ(2n).
- **How**: Unfolds dblZ, smulPoly; uses `ψc_spec` and `ω_spec`.
- **Hypotheses**: none
- **Uses from project**: `smulPoly`, `ψc_spec`, `ω_spec`
- **Used by**: `dblXYZ_smulField`
- **Visibility**: private
- **Lines**: 526–531 (6 lines)
- **Notes**: none

### `private lemma nonsingular_smulField`
- **Type**: `Nonsingular curveField (smulField n)`
- **What**: smulField(n) is a nonsingular point on the base-changed universal curve.
- **How**: Uses `zsmul_point_eq_smulField` to identify with a point and extracts its nonsingularity.
- **Hypotheses**: none
- **Uses from project**: `smulField`, `zsmul_point_eq_smulField`
- **Used by**: `addXYZ_smulField`
- **Visibility**: private
- **Lines**: 533–535 (3 lines)
- **Notes**: none

### `private lemma two_zsmul_point_eq_dblXYZ`
- **Type**: `P.point = ⟦v⟧ → ((2:ℤ) • P).point = ⟦dblXYZ curveField v⟧`
- **What**: Doubling a Jacobian point corresponds to dblXYZ in Jacobian projective coordinates.
- **How**: `rw [two_zsmul, Point.add_point, hv, addMap_eq, add_self]`
- **Hypotheses**: P, v given
- **Uses from project**: none
- **Used by**: `dblXYZ_smulField`
- **Visibility**: private
- **Lines**: 537–540 (4 lines)
- **Notes**: none

### `private lemma add_point_of_ne_eq_addXYZ`
- **Type**: `P.point = ⟦v⟧ → Q.point = ⟦w⟧ → P ≠ Q → (P+Q).point = ⟦addXYZ curveField v w⟧`
- **What**: Addition of two distinct Jacobian points corresponds to addXYZ.
- **How**: `rw [Point.add_point, hv, hw, addMap_eq, add_of_not_equiv]`; injectivity via `Point.ext_iff`.
- **Hypotheses**: P ≠ Q
- **Uses from project**: none
- **Used by**: `addXYZ_smulField`
- **Visibility**: private
- **Lines**: 542–546 (5 lines)
- **Notes**: none

### `private lemma zsmul_point_ne`
- **Type**: `m ≠ n → m • Jacobian.point ≠ n • Jacobian.point`
- **What**: Distinct multiples of the universal Jacobian point are distinct.
- **How**: Subtracts and uses `zsmul_point_ne_zero`.
- **Hypotheses**: `m ≠ n`
- **Uses from project**: `zsmul_point_ne_zero` (Jacobian)
- **Used by**: `addXYZ_smulField`
- **Visibility**: private
- **Lines**: 548–551 (4 lines)
- **Notes**: none

### `lemma dblXYZ_smulField`
- **Type**: `dblXYZ curveField (smulField n) = smulField (2*n)`
- **What**: The Jacobian doubling formula applied to smulField(n) gives smulField(2n).
- **How**: For n=0, direct simp. For n≠0, uses `equiv_iff_eq_of_Z_eq` (reducing to Z-coordinate and point equality), `dblZ_smulPoly`, `two_zsmul_point_eq_dblXYZ`, `zsmul_point_eq_smulField`.
- **Hypotheses**: none
- **Uses from project**: `smulField`, `smulPoly`, `ψᵤ_ne_zero`, `dblZ_smulPoly`, `zsmul_point_eq_smulField`, `two_zsmul_point_eq_dblXYZ`
- **Used by**: `dblXYZ_smulRing`
- **Visibility**: public
- **Lines**: 554–565 (12 lines)
- **Notes**: `set_option maxRecDepth 2048` at line 553 with NO justifying comment

### `lemma dblXYZ_smulRing`
- **Type**: `dblXYZ curveRing (smulRing n) = smulRing (2*n)`
- **What**: The Jacobian doubling formula at the ring level.
- **How**: `IsFractionRing.injective` reduces to the field case `dblXYZ_smulField` via `map_dblXYZ`.
- **Hypotheses**: none
- **Uses from project**: `smulRing`, `dblXYZ_smulField`
- **Used by**: `dblXYZ_smulEval`
- **Visibility**: public
- **Lines**: 567–569 (3 lines)
- **Notes**: none

### `private lemma addZ_smulPoly`
- **Type**: `addZ (smulPoly m) (smulPoly n) = curve.ψ (n+m) * curve.ψ (n-m)`
- **What**: The Jacobian addition Z-formula for smulPoly gives ψ(n+m)·ψ(n-m).
- **How**: Uses `isEllSequence_ψ` (the net identity for ψ) in the form of `isEllSequence_ψ n m 1`.
- **Hypotheses**: none
- **Uses from project**: `smulPoly`, `isEllSequence_ψ`
- **Used by**: `addXYZ_smulField`
- **Visibility**: private
- **Lines**: 571–575 (5 lines)
- **Notes**: none

### `private lemma smulField_neg`
- **Type**: `smulField (-n) = (-1 : Universal.Field) • neg curveField (smulField n)`
- **What**: smulField negation formula at the field level.
- **How**: Uses `smulPoly_neg`, `map_neg`, `map_one`.
- **Hypotheses**: none
- **Uses from project**: `smulField`, `smulPoly_neg`
- **Used by**: `addXYZ_smulField`
- **Visibility**: private
- **Lines**: 577–579 (3 lines)
- **Notes**: none

### `private lemma smulField_zero`
- **Type**: `smulField 0 = ![1, 1, 0]`
- **What**: smulField(0) is the Jacobian "infinity" point representative.
- **How**: `simp [smulField, smulPoly, comp_fin3]`
- **Hypotheses**: none
- **Uses from project**: `smulField`, `smulPoly`
- **Used by**: `addXYZ_smulField`
- **Visibility**: private
- **Lines**: 581–582 (2 lines)
- **Notes**: none

### `lemma addXYZ_smulField`
- **Type**: `addXYZ curveField (smulField m) (smulField n) = polyToField (curve.ψ (n-m)) • smulField (n+m)`
- **What**: The Jacobian addition formula: addXYZ at smulField(m), smulField(n) gives ψ(n-m) · smulField(n+m).
- **How**: Three cases: m=n (degenerate via Z=0), n=-m (negation case), generic (uses `add_point_of_ne_eq_addXYZ`, `zsmul_point_eq_smulField`, `addZ_smulPoly`, `smul_eq`, `zsmul_point_ne`).
- **Hypotheses**: none
- **Uses from project**: `smulField`, `ψᵤ_ne_zero`, `nonsingular_smulField`, `smulField_neg`, `smulField_zero`, `dblZ_smulPoly`, `add_point_of_ne_eq_addXYZ`, `zsmul_point_eq_smulField`, `zsmul_point_ne`, `addZ_smulPoly`
- **Used by**: `addXYZ_smulRing`
- **Visibility**: public
- **Lines**: 584–608 (24 lines)
- **Notes**: none

### `lemma addXYZ_smulRing`
- **Type**: `addXYZ curveRing (smulRing m) (smulRing n) = AdjoinRoot.mk curve.polynomial (curve.ψ (n-m)) • smulRing (n+m)`
- **What**: The Jacobian addition formula at the ring level.
- **How**: `IsFractionRing.injective` reduces to `addXYZ_smulField`.
- **Hypotheses**: none
- **Uses from project**: `smulRing`, `addXYZ_smulField`
- **Used by**: `addXYZ_smulRing₁`
- **Visibility**: public
- **Lines**: 609–613 (5 lines)
- **Notes**: none

### `lemma addXYZ_smulField₁`
- **Type**: `addXYZ curveField (smulField n) (smulField (n+1)) = smulField (2*n+1)`
- **What**: The Jacobian addition formula at consecutive indices: smulField(n) + smulField(n+1) = smulField(2n+1).
- **How**: Specializes `addXYZ_smulField` with m=n, n=n+1; ψ(n+1-n)=ψ(1)=1 simplifies.
- **Hypotheses**: none
- **Uses from project**: `smulField`, `addXYZ_smulField`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 615–621 (7 lines)
- **Notes**: not referenced within this file; referenced only by `addXYZ_smulRing₁`

### `lemma addXYZ_smulRing₁`
- **Type**: `addXYZ curveRing (smulRing n) (smulRing (n+1)) = smulRing (2*n+1)`
- **What**: The Jacobian addition formula at consecutive indices at the ring level.
- **How**: `rw [addXYZ_smulRing, ...]` then specializes; ψ(1)=1 simplifies.
- **Hypotheses**: none
- **Uses from project**: `smulRing`, `addXYZ_smulRing`
- **Used by**: `addXYZ_smulEval₁`
- **Visibility**: public
- **Lines**: 623–629 (7 lines)
- **Notes**: none

---

## Section: smulEval and zsmul_eq_smulEval (lines 633–717)

### `abbrev smulEval`
- **Type**: `(n : ℤ) → Fin 3 → R`
- **What**: The evaluation of the division polynomial triple (φ(n), ω(n), ψ(n)) at a point (x,y) on the curve; equals the Jacobian coordinates of n·(x,y).
- **How**: `evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]`
- **Hypotheses**: `CommRing R`, `x y : R`
- **Uses from project**: none
- **Used by**: `ringEval_comp_smulRing`, `ringEval_ψ`, `dblXYZ_smulEval`, `addXYZ_smulEval`, `addXYZ_smulEval₁`, `zsmul_eq_smulEval`, `isCoprime_Φ_ΨSq`
- **Visibility**: public
- **Lines**: 636 (1 line)
- **Notes**: KEY API — main exported definition used externally by MulByIntPullback, MulByIntUnramified, GenericPointZsmul

### `lemma ringEval_comp_smulRing`
- **Type**: `ringEval eqn ∘ smulRing n = smulEval W x y n`
- **What**: The `ringEval` map (specializing the universal ring to W at (x,y)) composed with smulRing equals smulEval.
- **How**: Rewrites via `smulEval`, `map_specialize`, pulls apart via `polyEval`, and applies `ringEval_comp_mk`.
- **Hypotheses**: `eqn : W.toAffine.Equation x y`
- **Uses from project**: `smulEval`, `smulRing`
- **Used by**: `ringEval_ψ`, `dblXYZ_smulEval`, `addXYZ_smulEval`, `addXYZ_smulEval₁`, `zsmul_eq_smulEval`
- **Visibility**: public
- **Lines**: 642–647 (6 lines)
- **Notes**: none

### `lemma ringEval_ψ`
- **Type**: `ringEval eqn (AdjoinRoot.mk _ <| curve.ψ n) = evalEval x y (W.ψ n)`
- **What**: Evaluating ψ(n) in the universal ring at a curve point (x,y) gives evalEval.
- **How**: Follows from `ringEval_comp_smulRing` at index 2.
- **Hypotheses**: `eqn : W.toAffine.Equation x y`
- **Uses from project**: `smulEval`, `ringEval_comp_smulRing`
- **Used by**: `addXYZ_smulEval`
- **Visibility**: public
- **Lines**: 649–651 (3 lines)
- **Notes**: none

### `lemma dblXYZ_smulEval`
- **Type**: `dblXYZ W (smulEval W x y n) = smulEval W x y (2*n)` (requires `eqn`)
- **What**: The Jacobian doubling formula in concrete evaluation form.
- **How**: `simp_rw` using `ringEval_comp_smulRing`, `dblXYZ_smulRing`, `map_dblXYZ`, `curveRing_map_ringEval`.
- **Hypotheses**: `eqn : W.toAffine.Equation x y`
- **Uses from project**: `smulEval`, `ringEval_comp_smulRing`, `dblXYZ_smulRing`
- **Used by**: `zsmul_eq_smulEval`
- **Visibility**: public
- **Lines**: 654–656 (3 lines)
- **Notes**: none

### `lemma addXYZ_smulEval`
- **Type**: `addXYZ W (smulEval W x y m) (smulEval W x y n) = evalEval x y (W.ψ (n-m)) • smulEval W x y (n+m)` (requires `eqn`)
- **What**: The Jacobian addition formula in concrete evaluation form.
- **How**: `simp_rw` using `ringEval_comp_smulRing`, `ringEval_ψ`, then `addXYZ_smulRing`, `map_addXYZ`, `curveRing_map_ringEval`.
- **Hypotheses**: `eqn : W.toAffine.Equation x y`
- **Uses from project**: `smulEval`, `ringEval_comp_smulRing`, `ringEval_ψ`, `addXYZ_smulRing`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 659–664 (6 lines)
- **Notes**: not referenced within this file (likely used externally)

### `lemma addXYZ_smulEval₁`
- **Type**: `addXYZ W (smulEval W x y n) (smulEval W x y (n+1)) = smulEval W x y (2*n+1)` (requires `eqn`)
- **What**: The Jacobian addition formula at consecutive indices in concrete form.
- **How**: `simp_rw` using `ringEval_comp_smulRing`, `addXYZ_smulRing₁`, `map_addXYZ`, `curveRing_map_ringEval`.
- **Hypotheses**: `eqn : W.toAffine.Equation x y`
- **Uses from project**: `smulEval`, `ringEval_comp_smulRing`, `addXYZ_smulRing₁`
- **Used by**: `zsmul_eq_smulEval`
- **Visibility**: public
- **Lines**: 667–670 (4 lines)
- **Notes**: none

### `theorem zsmul_eq_smulEval`
- **Type**: `h : Affine.Nonsingular W x y → ∀ n : ℤ, (n • Point.fromAffine (Affine.Point.some _ _ h)).point = ⟦smulEval W x y n⟧`
- **What**: The main theorem: for any nonsingular affine point (x,y) on a Weierstrass curve W over a field F, the Jacobian coordinates of n·P equal smulEval W x y n. Expresses scalar multiplication entirely in division polynomial coordinates.
- **How**: `Int.negInduction` then `Nat.strong_induction_on`. Even n=2m: uses `dblXYZ_smulEval`. Odd n=2m+1: uses `addXYZ_smulEval₁`. Negative: `smulRing_neg` via `ringEval_comp_smulRing`.
- **Hypotheses**: `h : Affine.Nonsingular W x y`, field F
- **Uses from project**: `smulEval`, `ringEval_comp_smulRing`, `smulRing_neg`, `dblXYZ_smulEval`, `addXYZ_smulEval₁`
- **Used by**: `isCoprime_Φ_ΨSq` (in this file); used externally by MulByIntPullback, MulByIntUnramified, GenericPointZsmul
- **Visibility**: public
- **Lines**: 678–714 (37 lines)
- **Notes**: Proof >30 lines. KEY API — main export of this file

---

## Section: Coprimality (lines 720–839)

### `lemma evalEval_eq_of_mk_eq`
- **Type**: `heq : W.toAffine.Equation x y → Affine.CoordinateRing.mk W p = Affine.CoordinateRing.mk W q → p.evalEval x y = q.evalEval x y`
- **What**: Evaluation factors through the coordinate ring: if two polynomials are equal in CoordinateRing, their evaluations at any curve point agree.
- **How**: `AdjoinRoot.mk_eq_mk` gives a product relation; uses `evalEval_mul` and `mul_eq_zero_of_left` with the equation hypothesis.
- **Hypotheses**: `CommRing R`, `heq : W.toAffine.Equation x y`
- **Uses from project**: none
- **Used by**: `evalEval_ψ_sq`, `evalEval_φ_eq_Φ`
- **Visibility**: public
- **Lines**: 729–737 (9 lines)
- **Notes**: none

### `lemma evalEval_ψ_sq`
- **Type**: `heq : W.toAffine.Equation x y → (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x`
- **What**: The square of ψ(n) evaluated at any curve point equals ΨSq_n(x) (the univariate division polynomial squared).
- **How**: Uses `CoordinateRing.mk_ψ` and `mk_Ψ_sq` to equate the squares in the coordinate ring, then applies `evalEval_eq_of_mk_eq`.
- **Hypotheses**: `CommRing R`, `heq : W.toAffine.Equation x y`
- **Uses from project**: `evalEval_eq_of_mk_eq`
- **Used by**: `isCoprime_Φ_ΨSq`
- **Visibility**: public
- **Lines**: 740–746 (7 lines)
- **Notes**: none

### `lemma evalEval_φ_eq_Φ`
- **Type**: `heq : W.toAffine.Equation x y → (W.φ n).evalEval x y = (W.Φ n).eval x`
- **What**: φ(n) evaluated at any curve point equals Φ_n(x) (the univariate x-coordinate division polynomial).
- **How**: Uses `CoordinateRing.mk_φ` and `evalEval_eq_of_mk_eq`.
- **Hypotheses**: `CommRing R`, `heq : W.toAffine.Equation x y`
- **Uses from project**: `evalEval_eq_of_mk_eq`
- **Used by**: `isCoprime_Φ_ΨSq`
- **Visibility**: public
- **Lines**: 749–752 (4 lines)
- **Notes**: none

### `lemma exists_point_on_curve`
- **Type**: `[IsAlgClosed F] → (a : F) → ∃ b : F, W.toAffine.Equation a b`
- **What**: Over an algebraically closed field, every x-value lifts to a point on the curve.
- **How**: Reduces to finding a root of a quadratic Y² + (a₁x+a₃)Y - (x³+...) = 0. Uses `IsAlgClosed.exists_root` after computing `natDegree = 2`.
- **Hypotheses**: `Field F`, `IsAlgClosed F`
- **Uses from project**: none
- **Used by**: `isCoprime_Φ_ΨSq`
- **Visibility**: public
- **Lines**: 757–779 (23 lines)
- **Notes**: none

### `theorem isCoprime_Φ_ΨSq`
- **Type**: `W.Δ ≠ 0 → n ≠ 0 → IsCoprime (W.Φ n) (W.ΨSq n)`
- **What**: The division polynomials Φ_n and ΨSq_n are coprime for a nonsingular curve (Sutherland Lemma 6.8). This is the key tool for the degree formula.
- **How**: Reduces to the algebraic closure via `Polynomial.isCoprime_map` and `Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed`. For any common root a: lifts to a nonsingular point (a,b) via `exists_point_on_curve` and `equation_iff_nonsingular_of_Δ_ne_zero`; from ΨSq_n(a)=0 derives ψ_n(a,b)=0 via `evalEval_ψ_sq`; from Φ_n(a)=0 derives φ_n(a,b)=0 via `evalEval_φ_eq_Φ`; then `zsmul_eq_smulEval` + `Jacobian.X_ne_zero_of_Z_eq_zero` gives a contradiction.
- **Hypotheses**: `Field F`, `W.Δ ≠ 0`, `n ≠ 0`
- **Uses from project**: `smulEval`, `evalEval_ψ_sq`, `evalEval_φ_eq_Φ`, `exists_point_on_curve`, `zsmul_eq_smulEval`
- **Used by**: `degree_mulByN_eq_sq`; used externally by Basic.lean, MulByIntPullback, MulByIntUnramified
- **Visibility**: public
- **Lines**: 794–838 (44 lines)
- **Notes**: Proof >30 lines. KEY external API.

---

## Section: Degree of multiplication-by-n (lines 841–861)

### `theorem degree_mulByN_eq_sq`
- **Type**: `[Nontrivial F] → max (W.Φ n).natDegree (W.ΨSq n).natDegree = n.natAbs ^ 2`
- **What**: The degree of the rational map [n] on x-coordinates is n² (Sutherland Theorem 6.9).
- **How**: Uses `W.natDegree_Φ n` (=n²) and `W.natDegree_ΨSq_le n` (≤n²-1) from mathlib; then `max_eq_left` since ΨSq degree ≤ n²-1 < n².
- **Hypotheses**: `Field F`, `Nontrivial F`
- **Uses from project**: none (uses mathlib `natDegree_Φ`, `natDegree_ΨSq_le`)
- **Used by**: unused in this file; used externally by Basic.lean
- **Visibility**: public
- **Lines**: 853–857 (5 lines)
- **Notes**: Curiously does not use `isCoprime_Φ_ΨSq` — the coprimality is not needed for the pure degree formula (just degree bounds from mathlib).

---

## Summary Statistics

- **Total declarations**: 99 (approximately; includes 5 abbrevs, 6 defs, 1 instance, 5 theorems, 83 lemmas with ~18 private)
- **Sorries**: none
- **set_option**: `set_option maxRecDepth 2048` at line 553 (for `dblXYZ_smulField`), no justifying comment present
- **Proofs >30 lines**: `zsmul_point_eq_smulX_smulY` (41), `isCoprime_Φ_ΨSq` (44+), `zsmul_eq_smulEval` (37)
- **Unused in file**: `evalEval_ψ`, `evalEval_φ`, `evalEval_ω`, `polyEval_cusp_ω`, `smulY_zero`, `addX_smul_one_smul_one_aux`, `point_point`, `algebraMap_comp_smulRing`, `addXYZ_smulField₁`, `addXYZ_smulEval`, `ω_one` (some used externally)
- **Key API** (used 3+ times internally or externally): `ψᵤ_ne_zero`, `smulX`, `smulY`, `smulEval`, `ψᵤ`, `smulField`, `zsmul_eq_smulEval`, `isCoprime_Φ_ΨSq`, `ψc_spec`, `ω_spec`
