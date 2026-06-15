# Inventory: ./HasseWeil/Auxiliary/Universal.lean

File: `HasseWeil/Auxiliary/Universal.lean`
Ported from: `LutzNagell/Universal.lean`
Author: Junyan Xu

This file builds the universal Weierstrass curve machinery needed for division polynomial
proofs: injectivity of `algebraMap` into the coordinate ring, a universal polynomial ring in
5+2 variables, the universal pointed elliptic curve, the specialization maps, and the cusp
curve used to prove nonvanishing of division polynomials.

---

## Section: `WeierstrassCurve.Affine.CoordinateRing`

### `lemma algebraMap_poly_injective`
- **Type**: `Function.Injective (algebraMap R[X] W'.CoordinateRing)`
- **What**: The canonical ring map from `R[X]` (polynomials in the x-variable) to the coordinate ring `W'.CoordinateRing = R[X][Y]/⟨Weierstrass polynomial⟩` is injective.
- **How**: Uses `smul_basis_eq_zero` (the basis representation of the coordinate ring over `R[X]`) to reduce injectivity to `smul_basis_eq_zero`: if `algebraMap p = 0` then `p * 1 = 0` in the quotient, which via the basis forces `p = 0`.
- **Hypotheses**: `R` commutative ring, `W'` affine Weierstrass curve over `R`.
- **Uses from project**: none (uses mathlib `smul_basis_eq_zero`)
- **Used by**: `algebraMap_injective'` (within file); heavily used in project files `Basic.lean`, `OrdAtInftyBridge.lean`, `OmegaPullbackCoeff.lean`, `FrobeniusIsogeny.lean`, `BridgeMulByInt.lean`, `MulByIntPullback.lean`, `EC/MulByIntUnramified.lean`, `EC/WronskianGeneral.lean`, `Verschiebung/QthRoots.lean`, `Verschiebung/Genuine.lean`, `Curves/FiniteOverKx.lean`
- **Visibility**: public
- **Lines**: 48–51, proof 4 lines
- **Notes**: Has `set_option backward.isDefEq.respectTransparency false` immediately preceding (line 47), with no justifying comment. This option prevents transparency blowup when synthesizing instances involving `CoordinateRing`.

### `lemma algebraMap_injective'`
- **Type**: `Function.Injective (algebraMap R W'.CoordinateRing)`
- **What**: The canonical ring map from the base ring `R` into the coordinate ring is injective.
- **How**: Composed from `algebraMap_poly_injective` (the `R[X]` case) and `C_injective` (the constant polynomial embedding `R → R[X]`).
- **Hypotheses**: `R` commutative ring, `W'` affine Weierstrass curve over `R`.
- **Uses from project**: `algebraMap_poly_injective`
- **Used by**: `algebraMap_field_injective` (within file)
- **Visibility**: public
- **Lines**: 53–54, proof 1 line

---

## Section: `WeierstrassCurve.Affine.Point`

### `lemma some_eq_some_iff`
- **Type**: `some x₁ y₁ h₁ = some x₂ y₂ h₂ ↔ x₁ = x₂ ∧ y₁ = y₂`
- **What**: Equality of two nonsingular affine points `(x₁,y₁)` and `(x₂,y₂)` on a Weierstrass curve is equivalent to equality of their coordinates.
- **How**: Both directions by pattern matching on the point equality (`rintro (_ | _)` and `rintro ⟨rfl, rfl⟩`); straightforward `rfl`.
- **Hypotheses**: `h₁ : W'.Nonsingular x₁ y₁`, `h₂ : W'.Nonsingular x₂ y₂`.
- **Uses from project**: none
- **Used by**: used externally in `Auxiliary/DivisionPolynomial.lean`; unused within this file
- **Visibility**: public
- **Lines**: 62–64, proof 2 lines

---

## Section: `WeierstrassCurve.Universal`

### `inductive Coeff`
- **Type**: `Type` with constructors `A₁ A₂ A₃ A₄ A₆ : Coeff`
- **What**: A five-element type indexing the five Weierstrass coefficients; used as the index set for `MvPolynomial Coeff ℤ`, the universal coefficient ring.
- **How**: Plain inductive definition, no proof.
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: `curve`, `specialize`, `Poly`, `Ring`, `Field`, `polyEval`, `ringEval` (all within file); used in `DivisionPolynomial.lean` via `Universal.Poly`, `Universal.Ring`, etc.
- **Visibility**: public (in `WeierstrassCurve` namespace)
- **Lines**: 76, definition only

### `def curve`
- **Type**: `Affine (MvPolynomial Coeff ℤ)`
- **What**: The universal Weierstrass curve over `ℤ[A₁,A₂,A₃,A₄,A₆]`, with `aᵢ` coefficients being the corresponding free polynomial variables.
- **How**: Structure literal setting each `aᵢ` field to `MvPolynomial.X Aᵢ`.
- **Hypotheses**: none
- **Uses from project**: `Coeff` (within file)
- **Used by**: `Δ_curve_ne_zero`, `Poly`, `Ring`, `Field`, `polyToField_polynomial`, `algebraMap_field_injective`, `pointedCurve`, `equation_point`, `Affine.point`, `Jacobian.point`, `curvePoly`, `curveRing`, `curveField`, `map_specialize`, `ringEval`; used externally throughout project
- **Visibility**: public
- **Lines**: 87–88, definition only

### `lemma Δ_curve_ne_zero`
- **Type**: `curve.Δ ≠ 0`
- **What**: The discriminant of the universal Weierstrass curve is nonzero in `MvPolynomial Coeff ℤ`.
- **How**: Applies a specific evaluation `MvPolynomial.eval (Coeff.rec 0 0 0 0 1)` (setting `A₆=1`, all others to 0) to reduce to a concrete integer inequality `0 ≠ 0` which `simp` closes.
- **Hypotheses**: none
- **Uses from project**: `curve` (within file)
- **Used by**: `pointedCurve.IsElliptic` instance (within file)
- **Visibility**: public
- **Lines**: 90–93, proof 4 lines

### `abbrev Poly`
- **Type**: `Type := (MvPolynomial Coeff ℤ)[X][Y]`
- **What**: The universal polynomial ring `ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]` as a bivariate polynomial ring over the universal coefficient ring.
- **How**: Type alias.
- **Uses from project**: `Coeff`, `curve`
- **Used by**: `Poly.two_ne_zero`, `polyToField`, `polyEval`, `curvePoly`; used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 97

### `protected abbrev Ring`
- **Type**: `Type := curve.CoordinateRing`
- **What**: The universal ring `ℤ[A₁,…,A₆,X,Y]/⟨Weierstrass polynomial⟩` for pointed Weierstrass curves.
- **Uses from project**: `curve`
- **Used by**: `Field`, `polyToField`, `algebraMap_ring_eq_comp`, `curveRing`, `Field.two_ne_zero`, `curveRing_map_ringEval`; used externally
- **Visibility**: protected public
- **Lines**: 99

### `protected abbrev Field`
- **Type**: `Type := FractionRing Universal.Ring`
- **What**: The universal field for pointed Weierstrass curves: the field of fractions of the universal ring.
- **Uses from project**: `Ring`
- **Used by**: `polyToField`, `algebraMap_field_eq_comp`, `algebraMap_field_injective`, `pointedCurve`, `equation_point`, `Affine.point`, `Jacobian.point`, `curveField`, `Field.two_ne_zero`; used externally
- **Visibility**: protected public
- **Lines**: 102

### `instance : CommRing Poly`
- **Type**: `CommRing Poly`
- **What**: Provides the `CommRing` instance for `Poly = (MvPolynomial Coeff ℤ)[X][Y]`; the comment `why is this not automatic` notes it should be inferred but isn't.
- **How**: `Polynomial.commRing` directly.
- **Hypotheses**: none
- **Uses from project**: `Poly`
- **Used by**: downstream uses of ring operations on `Poly`; unused explicitly within file (purely instance)
- **Visibility**: public (anonymous instance)
- **Lines**: 104, 1 line

### `lemma Poly.two_ne_zero`
- **Type**: `(2 : Poly) ≠ 0`
- **What**: The element 2 is nonzero in the universal polynomial ring `Poly`.
- **How**: Propagates the fact `two_ne_zero' (α := ℤ)` through `MvPolynomial.C_injective` and two applications of `Polynomial.C_ne_zero`.
- **Hypotheses**: none
- **Uses from project**: `Poly`
- **Used by**: unused within this file; used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 106–108, proof 3 lines

### `def polyToField`
- **Type**: `Poly →+* Universal.Field`
- **What**: The canonical ring homomorphism from the universal polynomial ring `Poly` to the universal field `Field`, sending `P` to its image in the fraction ring of the coordinate ring.
- **How**: Defined as composition of `AdjoinRoot.mk` (the quotient map `Poly → Ring`) and `algebraMap Ring Field` (the fraction-ring embedding).
- **Uses from project**: `Poly`, `Field`, `Ring`
- **Used by**: `polyToField_apply`, `algebraMap_field_eq_comp`, `polyToField_polynomial`, `equation_point`, `Affine.point`, `pointedCurve_a₁`–`_a₆`; used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 111, definition only

### `lemma polyToField_apply`
- **Type**: `polyToField p = algebraMap Universal.Ring _ (AdjoinRoot.mk _ p)`
- **What**: Unfolds the definition of `polyToField` to show it factors as `algebraMap ∘ AdjoinRoot.mk`.
- **How**: `rfl`.
- **Uses from project**: `polyToField`, `Ring`, `Field`
- **Used by**: `polyToField_polynomial`, `equation_point`; used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 113–114, proof is `rfl`

### `lemma algebraMap_field_eq_comp`
- **Type**: `algebraMap (MvPolynomial Coeff ℤ) Universal.Field = polyToField.comp (algebraMap _ _)`
- **What**: The `algebraMap` from the coefficient ring to the universal field equals `polyToField` composed with the `algebraMap` from the coefficient ring to `Poly`.
- **How**: `rfl`.
- **Uses from project**: `Poly`, `Field`, `polyToField`
- **Used by**: `equation_point` (within file)
- **Visibility**: public
- **Lines**: 116–117, proof is `rfl`

### `lemma algebraMap_ring_eq_comp`
- **Type**: `algebraMap (MvPolynomial Coeff ℤ) Universal.Ring = (AdjoinRoot.mk _).comp (algebraMap _ _)`
- **What**: The `algebraMap` from the coefficient ring to the universal ring equals `AdjoinRoot.mk` composed with the natural map from the coefficient ring to `Poly`.
- **How**: `rfl`.
- **Uses from project**: `Ring`, `Poly`
- **Used by**: `ringEval_comp_eq_specialize` (within file)
- **Visibility**: public
- **Lines**: 119–121, proof is `rfl`

### `@[simp] lemma polyToField_polynomial`
- **Type**: `polyToField curve.polynomial = 0`
- **What**: The image of the Weierstrass polynomial under `polyToField` is zero (since it is the defining relation of the coordinate ring).
- **How**: `AdjoinRoot.mk_self` (the quotient of the defining polynomial is 0) and `map_zero`.
- **Uses from project**: `polyToField`, `polyToField_apply`, `curve`
- **Used by**: `equation_point` (within file)
- **Visibility**: public (simp lemma)
- **Lines**: 123–124, proof 2 lines

### `lemma algebraMap_field_injective`
- **Type**: `Function.Injective (algebraMap (MvPolynomial Coeff ℤ) Universal.Field)`
- **What**: The `algebraMap` from the universal coefficient ring `MvPolynomial Coeff ℤ` into the universal field is injective.
- **How**: Composes `IsFractionRing.injective` (injectivity of fraction-ring embedding) with `algebraMap_injective'` (injectivity of `R → CoordinateRing` from this file).
- **Uses from project**: `algebraMap_injective'`, `Field`, `Ring`, `curve`
- **Used by**: `pointedCurve.IsElliptic` instance (within file); used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 126–129, proof 4 lines

### `abbrev pointedCurve`
- **Type**: `WeierstrassCurve Universal.Field`
- **What**: The universal pointed Weierstrass curve obtained by base-changing `curve` to the universal field.
- **Uses from project**: `curve`, `Field`
- **Used by**: `pointedCurve.IsElliptic`, `equation_point`, `Affine.point`, `pointedCurve_a₁`–`_a₆`, `curveField_eq`; used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 133

### `instance : pointedCurve.IsElliptic`
- **Type**: `pointedCurve.IsElliptic`
- **What**: The universal pointed curve is an elliptic curve (its discriminant is a unit in `Universal.Field`).
- **How**: Uses `map_Δ` to transport the discriminant, then `algebraMap_field_injective` to conclude it is nonzero (via `Δ_curve_ne_zero`), hence a unit in the field.
- **Hypotheses**: none (uses `Δ_curve_ne_zero` and `algebraMap_field_injective`)
- **Uses from project**: `pointedCurve`, `algebraMap_field_injective`, `Δ_curve_ne_zero`, `Field`
- **Used by**: `Affine.point` (implicitly, via equation membership); used externally
- **Visibility**: public (anonymous instance)
- **Lines**: 135–138, proof 4 lines

### `lemma equation_point`
- **Type**: `pointedCurve.toAffine.Equation (polyToField (C X)) (polyToField Y)`
- **What**: The point `(X, Y)` (the canonical generators of `Poly`) maps to a point on the universal curve in `Universal.Field`.
- **How**: Rewrites the equation using `Affine.map_polynomial` and computes that the composite ring hom `evalEvalRingHom ∘ mapRingHom ∘ mapRingHom = polyToField` by an `ext` argument; then applies `polyToField_polynomial`.
- **Uses from project**: `pointedCurve`, `polyToField`, `algebraMap_field_eq_comp`, `polyToField_polynomial`
- **Used by**: `Affine.point` (within file); used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 141–150, proof 10 lines

### `def Affine.point`
- **Type**: `curve⟮Universal.Field⟯` (a point of type `WeierstrassCurve.Affine.Point (curve.baseChange Universal.Field) = pointedCurve.toAffine.Point`)
- **What**: The distinguished affine point `(X, Y)` on the universal curve over `Universal.Field`.
- **How**: Constructed via `.mk equation_point`.
- **Uses from project**: `equation_point`, `curve`, `Field`
- **Used by**: `Jacobian.point` (within file); used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 154–155, definition only

### `def Jacobian.point`
- **Type**: `Jacobian.Point (curve.baseChange Universal.Field)`
- **What**: The distinguished Jacobian projective point on the universal curve, obtained from the affine point via `Jacobian.Point.fromAffine`.
- **How**: `Jacobian.Point.fromAffine Affine.point`.
- **Uses from project**: `Affine.point`, `curve`, `Field`
- **Used by**: unused within this file; used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 158–159, definition only

### `@[simp] lemma pointedCurve_a₁`
- **Type**: `pointedCurve.a₁ = polyToField (CC curve.a₁)`
- **What**: The first Weierstrass coefficient of `pointedCurve` equals the image of the corresponding universal coefficient under `polyToField`.
- **How**: `rfl`.
- **Uses from project**: `pointedCurve`, `polyToField`, `curve`
- **Used by**: `equation_point` (indirectly); used externally in `DivisionPolynomial.lean`
- **Visibility**: public (simp lemma)
- **Lines**: 163, proof is `rfl`

### `@[simp] lemma pointedCurve_a₂`
- **Type**: `pointedCurve.a₂ = polyToField (CC curve.a₂)`
- **What/How**: Analogous to `pointedCurve_a₁` for `a₂`.
- **Uses from project**: `pointedCurve`, `polyToField`, `curve`
- **Used by**: used externally in `DivisionPolynomial.lean`
- **Visibility**: public (simp lemma)
- **Lines**: 164, proof is `rfl`

### `@[simp] lemma pointedCurve_a₃`
- **Type**: `pointedCurve.a₃ = polyToField (CC curve.a₃)`
- **What/How**: Analogous for `a₃`.
- **Uses from project**: `pointedCurve`, `polyToField`, `curve`
- **Used by**: used externally in `DivisionPolynomial.lean`
- **Visibility**: public (simp lemma)
- **Lines**: 165, proof is `rfl`

### `@[simp] lemma pointedCurve_a₄`
- **Type**: `pointedCurve.a₄ = polyToField (CC curve.a₄)`
- **What/How**: Analogous for `a₄`.
- **Uses from project**: `pointedCurve`, `polyToField`, `curve`
- **Used by**: used externally in `DivisionPolynomial.lean`
- **Visibility**: public (simp lemma)
- **Lines**: 166, proof is `rfl`

### `@[simp] lemma pointedCurve_a₆`
- **Type**: `pointedCurve.a₆ = polyToField (CC curve.a₆)`
- **What/How**: Analogous for `a₆`.
- **Uses from project**: `pointedCurve`, `polyToField`, `curve`
- **Used by**: used externally in `DivisionPolynomial.lean`
- **Visibility**: public (simp lemma)
- **Lines**: 167, proof is `rfl`

### `abbrev curvePoly`
- **Type**: `WeierstrassCurve Poly`
- **What**: The universal Weierstrass curve base-changed to the polynomial ring `Poly`.
- **Uses from project**: `curve`, `Poly`
- **Used by**: unused within this file; potentially used externally
- **Visibility**: public
- **Lines**: 170

### `abbrev curveRing`
- **Type**: `WeierstrassCurve Universal.Ring`
- **What**: The universal Weierstrass curve base-changed to the universal ring.
- **Uses from project**: `curve`, `Ring`
- **Used by**: `curveRing_map_ringEval` (within file); used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 173

### `abbrev curveField`
- **Type**: `WeierstrassCurve Universal.Field`
- **What**: The universal Weierstrass curve base-changed to the universal field; equals `pointedCurve` by `curveField_eq`.
- **Uses from project**: `curve`, `Field`
- **Used by**: `curveField_eq` (within file)
- **Visibility**: public
- **Lines**: 176

### `lemma curveField_eq`
- **Type**: `curveField = pointedCurve`
- **What**: The two ways to define the universal curve over the universal field (`curveField` and `pointedCurve`) are definitionally equal.
- **How**: `rfl`.
- **Uses from project**: `curveField`, `pointedCurve`
- **Used by**: unused within this file (and not referenced externally in the files checked)
- **Visibility**: public
- **Lines**: 178, proof is `rfl`

---

## Section: `WeierstrassCurve` (outside Universal namespace)

### `def cusp`
- **Type**: `Affine ℤ`
- **What**: The cusp curve `Y² = X³` over ℤ, defined by setting all five Weierstrass coefficients to zero.
- **How**: Structure literal with all `aᵢ = 0`.
- **Uses from project**: none
- **Used by**: `cusp_equation_one_one`, `Field.two_ne_zero` (within file); used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 183, definition only

### `lemma cusp_equation_one_one`
- **Type**: `cusp.Equation 1 1`
- **What**: The point `(1, 1)` lies on the cusp curve: `1² - 1³ = 0`.
- **How**: `simp` with `Affine.Equation`, `Affine.polynomial`, `cusp`, `Polynomial.evalEval`.
- **Uses from project**: `cusp`
- **Used by**: `Field.two_ne_zero` (within file); used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 185–186, proof 2 lines

### `def specialize`
- **Type**: `MvPolynomial Coeff ℤ →+* R`
- **What**: The specialization ring homomorphism from the universal coefficient ring `ℤ[A₁,…,A₆]` to any commutative ring `R`, sending each `Aᵢ` to the corresponding Weierstrass coefficient of `W`.
- **How**: `MvPolynomial.aeval` applied to the function `Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆`.
- **Hypotheses**: `W : WeierstrassCurve R`, `R` commutative ring.
- **Uses from project**: `Coeff`
- **Used by**: `map_specialize`, `polyEval`, `ringEval`, `polyEval_comp_eq_specialize`, `ringEval_comp_eq_specialize`; used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 193–194, definition only

### `lemma map_specialize`
- **Type**: `Universal.curve.map W.specialize = W`
- **What**: Mapping the universal Weierstrass curve along the specialization homomorphism recovers the original curve `W`.
- **How**: `simp [specialize, curve, map]`.
- **Uses from project**: `curve`, `specialize`
- **Used by**: `ringEval` (within file proof obligation), `curveRing_map_ringEval`; used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 197, proof 1 line

### `def polyEval`
- **Type**: `Poly →+* R`
- **What**: Given an affine point `(x, y)` over `R`, the evaluation ring homomorphism from `Poly = ℤ[A₁,…,A₆,X,Y]` to `R` that sends each `Aᵢ` to the corresponding coefficient of `W` and `X,Y` to `x,y`.
- **How**: `eval₂RingHom (eval₂RingHom W.specialize x) y` — iterated evaluation at `x` then `y`.
- **Hypotheses**: `W : WeierstrassCurve R`, `x y : R`.
- **Uses from project**: `specialize`, `Poly`
- **Used by**: `polyEval_apply`, `ringEval`, `ringEval_mk`, `ringEval_comp_mk`, `polyEval_comp_eq_specialize`, `ringEval_comp_eq_specialize`; used extensively externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 206, definition only

### `lemma polyEval_apply`
- **Type**: `polyEval W x y p = (p.map (mapRingHom W.specialize)).evalEval x y`
- **What**: Computes `polyEval` explicitly: apply `specialize` to all the coefficient variables, then evaluate at `x` and `y`.
- **How**: `eval₂_eval₂RingHom_apply`.
- **Uses from project**: `polyEval`, `specialize`
- **Used by**: `ringEval` (within proof); used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 209–211, proof 1 line

### `def ringEval`
- **Type**: `Universal.Ring →+* R`
- **What**: Given a point `(x,y)` on the curve `W`, the ring homomorphism from the universal ring `Ring = Poly/⟨Weierstrass polynomial⟩` to `R` that specializes `Aᵢ` to `W.aᵢ` and `X,Y` to `x,y`.
- **How**: `AdjoinRoot.lift` applied to `polyEval W x y` at `y`; the well-definedness proof uses `polyEval_apply`, `map_specialize`, and the hypothesis `eqn : Affine.Equation W x y`.
- **Hypotheses**: `eqn : Affine.Equation W x y` (the point `(x,y)` lies on `W`).
- **Uses from project**: `polyEval`, `polyEval_apply`, `map_specialize`, `Ring`
- **Used by**: `ringEval_mk`, `ringEval_comp_mk`, `ringEval_comp_eq_specialize`, `Field.two_ne_zero`, `curveRing_map_ringEval`; used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 218–221, with inline proof of well-definedness (~4 lines)

### `lemma ringEval_mk`
- **Type**: `ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p`
- **What**: The value of `ringEval` on a coset representative `AdjoinRoot.mk p` equals `polyEval` applied to `p`.
- **How**: `AdjoinRoot.lift_mk`.
- **Uses from project**: `ringEval`, `polyEval`
- **Used by**: `ringEval_comp_mk` (within file); used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 223–224, proof 1 line

### `lemma ringEval_comp_mk`
- **Type**: `(ringEval eqn).comp (AdjoinRoot.mk _) = polyEval W x y`
- **What**: The composition of `ringEval eqn` with `AdjoinRoot.mk` equals `polyEval W x y` as ring homomorphisms.
- **How**: `RingHom.ext (ringEval_mk eqn)`.
- **Uses from project**: `ringEval`, `polyEval`, `ringEval_mk`
- **Used by**: `ringEval_comp_eq_specialize` (within file); used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 226–227, proof 1 line

### `lemma polyEval_comp_eq_specialize`
- **Type**: `(polyEval W x y).comp (algebraMap _ _) = W.specialize`
- **What**: Composing `polyEval` with the `algebraMap` from the coefficient ring into `Poly` recovers the specialization homomorphism.
- **How**: `ext <;> simp [polyEval]`.
- **Uses from project**: `polyEval`, `specialize`
- **Used by**: `ringEval_comp_eq_specialize` (within file)
- **Visibility**: public
- **Lines**: 229–230, proof 1 line

### `lemma ringEval_comp_eq_specialize`
- **Type**: `(ringEval eqn).comp (algebraMap _ _) = W.specialize`
- **What**: Composing `ringEval eqn` with the `algebraMap` from the coefficient ring into `Ring` recovers the specialization homomorphism.
- **How**: Rewrites using `algebraMap_ring_eq_comp`, then applies `ringEval_comp_mk` and `polyEval_comp_eq_specialize`.
- **Uses from project**: `ringEval`, `specialize`, `algebraMap_ring_eq_comp`, `ringEval_comp_mk`, `polyEval_comp_eq_specialize`
- **Used by**: `curveRing_map_ringEval` (within file)
- **Visibility**: public
- **Lines**: 232–233, proof 2 lines

### `protected lemma Field.two_ne_zero`
- **Type**: `(2 : Universal.Field) ≠ 0`
- **What**: The element 2 is nonzero in the universal field `Field`.
- **How**: Lifts to `Universal.Ring` via `IsFractionRing.injective`, then applies `ringEval cusp_equation_one_one` to specialize to the cusp curve, reducing to a concrete integer computation where `2 ≠ 0`.
- **Uses from project**: `Field`, `Ring`, `ringEval`, `cusp_equation_one_one`
- **Used by**: unused within this file; used externally in `DivisionPolynomial.lean`
- **Visibility**: protected public
- **Lines**: 235–238, proof 4 lines

### `lemma curveRing_map_ringEval`
- **Type**: `curveRing.map (ringEval eqn) = W`
- **What**: Mapping the universal curve over `Ring` along `ringEval eqn` recovers the original Weierstrass curve `W`.
- **How**: Uses `map_map` to decompose as `curve.map (algebraMap ∘ ringEval eqn)`, then `ringEval_comp_eq_specialize` to identify the composition with `specialize`, and finally `map_specialize`.
- **Uses from project**: `curveRing`, `ringEval`, `ringEval_comp_eq_specialize`, `map_specialize`
- **Used by**: unused within this file; used externally in `DivisionPolynomial.lean`
- **Visibility**: public
- **Lines**: 240–242, proof 3 lines

---

## Summary statistics

| Category | Count |
|---|---|
| Total declarations | 38 |
| `def` / `noncomputable def` | 8 |
| `lemma` / `theorem` | 21 |
| `instance` | 2 |
| `abbrev` | 7 |
| `inductive` | 1 |
| Sorries | 0 |
| `set_option maxHeartbeats` | 0 |
| Other `set_option` | 1 (line 47: `backward.isDefEq.respectTransparency false`) |
| Proofs > 30 lines | 0 |
