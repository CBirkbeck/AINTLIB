# Inventory: LutzNagell/Universal.lean

Source: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/LutzNagell/Universal.lean`

File purpose: provides mathlib-missing lemmas (coordinate-ring `algebraMap` injectivity, affine point equality) and constructs the **universal Weierstrass curve** over `ℤ[A₁,A₂,A₃,A₄,A₆]` and the **universal pointed elliptic curve** over the fraction field of `ℤ[A₁,…,A₆,X,Y]/⟨P⟩`. Also sets up specialization homomorphisms and the cusp curve `Y²=X³` used to prove non-vanishing of universal division polynomials.

---

### lemma algebraMap_poly_injective
- Type: `Function.Injective (algebraMap R[X] W'.CoordinateRing)`
- What: The structure map from the univariate polynomial ring `R[X]` into the coordinate ring of an affine Weierstrass curve `W'` is injective.
- How: Uses `injective_iff_map_eq_zero`; given `p` mapping to `0`, applies `smul_basis_eq_zero` (mathlib) with `q := 0` to deduce `p = 0`, after rewriting `Algebra.smul_def`, `mul_one`, `zero_smul`, `add_zero`.
- Hypotheses: `R` a commutative ring; `W'` an affine Weierstrass curve over `R`.
- Uses from project: []
- Used by: `algebraMap_injective'`
- Visibility: public
- Lines: 44-48 (proof ~4 lines)
- Notes: `set_option backward.isDefEq.respectTransparency false in` set on this lemma.

### lemma algebraMap_injective'
- Type: `Function.Injective (algebraMap R W'.CoordinateRing)`
- What: The structure map from the base ring `R` directly into the coordinate ring of `W'` is injective.
- How: Composes `algebraMap_poly_injective` with `C_injective` (injectivity of the constant-polynomial embedding `R → R[X]`).
- Hypotheses: `R` a commutative ring; `W'` an affine Weierstrass curve over `R`.
- Uses from project: [`algebraMap_poly_injective`]
- Used by: `algebraMap_field_injective` (referenced cross-section as `Affine.CoordinateRing.algebraMap_injective'`)
- Visibility: public
- Lines: 50-51 (proof 1 line)
- Notes: none

### lemma some_eq_some_iff
- Type: `some x₁ y₁ h₁ = some x₂ y₂ h₂ ↔ x₁ = x₂ ∧ y₁ = y₂`
- What: Two nonsingular affine points `some x y h` are equal iff their coordinates coincide.
- How: Forward direction destructs the point equality (`rintro (_ | _)`) to get `trivial`; backward substitutes `rfl, rfl`.
- Hypotheses: `h₁ : W'.Nonsingular x₁ y₁`, `h₂ : W'.Nonsingular x₂ y₂` (nonsingularity witnesses).
- Uses from project: []
- Used by: unused in file
- Visibility: public
- Lines: 59-61 (proof 1 line)
- Notes: none

### inductive Coeff
- Type: `inductive Coeff : Type | A₁ | A₂ | A₃ | A₄ | A₆`
- What: A five-element index type naming the Weierstrass coefficients `a₁, a₂, a₃, a₄, a₆`; serves as the variable index set for the universal polynomial ring.
- How: Plain inductive enumeration with five constructors.
- Hypotheses: none.
- Uses from project: []
- Used by: `curve`, `Δ_curve_ne_zero`, `Poly`, `specialize` (via `Coeff.rec`), and all decls building on the universal ring.
- Visibility: public
- Lines: 71-73 (no proof)
- Notes: none

### def curve
- Type: `curve : Affine (MvPolynomial Coeff ℤ)`
- What: The universal affine Weierstrass curve whose coefficients are the five generators `X A₁,…,X A₆` of the polynomial ring `MvPolynomial Coeff ℤ`.
- How: Direct structure literal setting each `aᵢ` to the corresponding `MvPolynomial.X` generator.
- Hypotheses: none.
- Uses from project: [`Coeff`]
- Used by: `Δ_curve_ne_zero`, `Universal.Ring`, `polyToField_polynomial`, `algebraMap_field_injective`, `pointedCurve`, `equation_point`, `pointedCurve_a₁…a₆`, `curvePoly`, `curveRing`, `curveField`, `map_specialize`, `curveRing_map_ringEval`, etc. (heavily used)
- Visibility: public
- Lines: 80-85 (no proof)
- Notes: none

### lemma Δ_curve_ne_zero
- Type: `curve.Δ ≠ 0`
- What: The discriminant of the universal curve is a nonzero element of `MvPolynomial Coeff ℤ`.
- How: Unfolds `Δ, b₂, b₄, b₆, b₈, curve`, then specializes via `MvPolynomial.eval (Coeff.rec 0 0 0 0 1)` (sending `A₆ ↦ 1`, others `↦ 0`, i.e. the curve `Y²=X³+1`) and discharges with `simp`, since the discriminant evaluates to a nonzero integer.
- Hypotheses: none.
- Uses from project: [`curve`]
- Used by: `IsElliptic` instance (line 135)
- Visibility: public
- Lines: 87-90 (proof ~4 lines)
- Notes: none

### abbrev Poly
- Type: `Poly : Type := (MvPolynomial Coeff ℤ)[X][Y]`
- What: The seven-variable polynomial ring `ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]`, i.e. the bivariate polynomial ring over the universal coefficient ring.
- How: Abbreviation (iterated `Polynomial`).
- Hypotheses: none.
- Uses from project: [`Coeff`]
- Used by: `CommRing Poly` instance, `Poly.two_ne_zero`, `polyToField`, `polyEval`, `polyEval_apply`, `ringEval_mk`, `ringEval_comp_mk`, `curvePoly`
- Visibility: public
- Lines: 94 (no proof)
- Notes: none

### abbrev Universal.Ring
- Type: `protected abbrev Ring : Type := curve.CoordinateRing`
- What: The universal ring for pointed Weierstrass curves, namely the coordinate ring `ℤ[A₁,…,A₆,X,Y]/⟨P⟩` of the universal curve.
- How: Abbreviation for `curve.CoordinateRing`.
- Hypotheses: none.
- Uses from project: [`curve`]
- Used by: `Universal.Field`, `polyToField`, `polyToField_apply`, `algebraMap_ring_eq_comp`, `algebraMap_field_injective`, `curveRing`, `Field.two_ne_zero`, `ringEval` (range), etc.
- Visibility: public (protected)
- Lines: 96 (no proof)
- Notes: none

### abbrev Universal.Field
- Type: `protected abbrev Field : Type := FractionRing Universal.Ring`
- What: The universal field for pointed Weierstrass curves: the fraction field of the universal ring.
- How: Abbreviation for `FractionRing Universal.Ring`.
- Hypotheses: none.
- Uses from project: [`Universal.Ring`]
- Used by: `polyToField`, `algebraMap_field_eq_comp`, `algebraMap_field_injective`, `pointedCurve`, `IsElliptic` instance, `equation_point`, `curveField`, `Field.two_ne_zero`
- Visibility: public (protected)
- Lines: 97-99 (no proof)
- Notes: none

### instance : CommRing Poly
- Type: `instance : CommRing Poly := Polynomial.commRing`
- What: Supplies the commutative-ring instance on `Poly` explicitly.
- How: Provides `Polynomial.commRing` directly (the inline comment notes it is surprisingly not inferred automatically).
- Hypotheses: none.
- Uses from project: [`Poly`]
- Used by: unused in file (typeclass instance, used implicitly)
- Visibility: public (instance)
- Lines: 101 (no proof)
- Notes: inline comment `/- why is this not automatic ... -/`.

### lemma Poly.two_ne_zero
- Type: `(2 : Poly) ≠ 0`
- What: The element `2` is nonzero in the seven-variable polynomial ring `Poly`.
- How: Pushes nonvanishing down through the two `Polynomial.C` layers via `Polynomial.C_ne_zero` (twice) and `MvPolynomial.C_injective`, reducing to `2 ≠ 0` in `ℤ` (`two_ne_zero'`).
- Hypotheses: none.
- Uses from project: [`Poly`]
- Used by: unused in file
- Visibility: public
- Lines: 103-105 (proof ~3 lines)
- Notes: none

### def polyToField
- Type: `polyToField : Poly →+* Universal.Field`
- What: The canonical ring homomorphism from the seven-variable polynomial ring to the universal field, factoring through the quotient `Poly → Universal.Ring` and then the fraction-field embedding.
- How: Composes `algebraMap Universal.Ring _` with `AdjoinRoot.mk _` (the quotient map by the Weierstrass polynomial).
- Hypotheses: none.
- Uses from project: [`Poly`, `Universal.Field`, `Universal.Ring`]
- Used by: `polyToField_apply`, `algebraMap_field_eq_comp`, `polyToField_polynomial`, `equation_point`, `pointedCurve_a₁…a₆`, `Affine.point` (via `equation_point`)
- Visibility: public
- Lines: 107-108 (no proof)
- Notes: none

### lemma polyToField_apply
- Type: `polyToField p = algebraMap Universal.Ring _ (AdjoinRoot.mk _ p)`
- What: Unfolds the definition of `polyToField` applied to an element `p`.
- How: Definitional `rfl`.
- Hypotheses: `p : Poly`.
- Uses from project: [`polyToField`, `Universal.Ring`]
- Used by: `polyToField_polynomial`
- Visibility: public
- Lines: 110-111 (proof: rfl)
- Notes: none

### lemma algebraMap_field_eq_comp
- Type: `algebraMap (MvPolynomial Coeff ℤ) Universal.Field = polyToField.comp (algebraMap _ _)`
- What: The structure map from the coefficient ring into the universal field equals `polyToField` precomposed with the coefficient-ring inclusion into `Poly`.
- How: Definitional `rfl`.
- Hypotheses: none.
- Uses from project: [`Coeff`, `Universal.Field`, `polyToField`]
- Used by: `algebraMap_field_injective`, `equation_point`
- Visibility: public
- Lines: 113-114 (proof: rfl)
- Notes: none

### lemma algebraMap_ring_eq_comp
- Type: `algebraMap (MvPolynomial Coeff ℤ) Universal.Ring = (AdjoinRoot.mk _).comp (algebraMap _ _)`
- What: The structure map from the coefficient ring into the universal ring equals the quotient map `AdjoinRoot.mk` precomposed with the inclusion into `Poly`.
- How: Definitional `rfl`.
- Hypotheses: none.
- Uses from project: [`Coeff`, `Universal.Ring`]
- Used by: `ringEval_comp_eq_specialize`
- Visibility: public
- Lines: 116-118 (proof: rfl)
- Notes: none

### lemma polyToField_polynomial
- Type: `polyToField curve.polynomial = 0`
- What: The Weierstrass polynomial of the universal curve maps to `0` in the universal field (the defining relation holds).
- How: Rewrites with `polyToField_apply`, then `AdjoinRoot.mk_self` (the relation is killed by the quotient) and `map_zero`.
- Hypotheses: none.
- Uses from project: [`polyToField`, `curve`, `polyToField_apply`]
- Used by: `equation_point`
- Visibility: public (`@[simp]`)
- Lines: 120-121 (proof ~1 line)
- Notes: none

### lemma algebraMap_field_injective
- Type: `Function.Injective (algebraMap (MvPolynomial Coeff ℤ) Universal.Field)`
- What: The structure map from the coefficient ring `ℤ[A₁,…,A₆]` into the universal field is injective.
- How: Composes `IsFractionRing.injective Universal.Ring Universal.Field` with the coordinate-ring injectivity `Affine.CoordinateRing.algebraMap_injective'` (for `W' := curve`).
- Hypotheses: none.
- Uses from project: [`Coeff`, `Universal.Field`, `Universal.Ring`, `algebraMap_injective'`, `curve`]
- Used by: `IsElliptic` instance (line 135)
- Visibility: public
- Lines: 123-126 (proof ~3 lines)
- Notes: none

### abbrev pointedCurve
- Type: `pointedCurve : WeierstrassCurve Universal.Field := baseChange curve Universal.Field`
- What: The universal pointed Weierstrass curve, obtained by base-changing the universal curve to the universal field.
- How: Abbreviation `baseChange curve Universal.Field`.
- Hypotheses: none.
- Uses from project: [`curve`, `Universal.Field`]
- Used by: `IsElliptic` instance, `equation_point`, `pointedCurve_a₁…a₆`, `curveField_eq`
- Visibility: public
- Lines: 128-130 (no proof)
- Notes: none

### instance : pointedCurve.IsElliptic
- Type: `instance : pointedCurve.IsElliptic`
- What: The universal pointed curve is an elliptic curve over the universal field (its discriminant is a unit).
- How: Rewrites the discriminant via `map_Δ curve (algebraMap _ Universal.Field)`, then shows it is nonzero by `map_ne_zero_iff` using `algebraMap_field_injective` and `Δ_curve_ne_zero`, hence a unit (`.isUnit`); since `Field` is a field, nonzero ⇒ unit.
- Hypotheses: none.
- Uses from project: [`pointedCurve`, `curve`, `Universal.Field`, `algebraMap_field_injective`, `Δ_curve_ne_zero`]
- Used by: unused in file (typeclass instance)
- Visibility: public (instance)
- Lines: 132-135 (proof ~3 lines)
- Notes: none

### lemma equation_point
- Type: `pointedCurve.toAffine.Equation (polyToField (C X)) (polyToField Y)`
- What: The image of the distinguished point `(X, Y)` under `polyToField` satisfies the affine Weierstrass equation of the universal pointed curve.
- How: Unfolds the goal to `evalEval … (polynomial) = 0`; builds the key ring-hom identity `h` that `evalEvalRingHom (…) ∘ mapRingHom(mapRingHom(algebraMap)) = polyToField` (proved by `ext`/`simp` using `algebraMap_field_eq_comp`), promotes it to all polynomials `p` via `congr($h p)`, then rewrites with `Affine.map_polynomial` and `polyToField_polynomial` to conclude `= 0`.
- Hypotheses: none.
- Uses from project: [`pointedCurve`, `polyToField`, `algebraMap_field_eq_comp`, `Universal.Field`, `polyToField_polynomial`, `curve` (implicit via pointedCurve)]
- Used by: `Affine.point`
- Visibility: public
- Lines: 137-147 (proof ~10 lines)
- Notes: none

### def Affine.point
- Type: `Affine.point : (curve.baseChange Universal.Field).toAffine.Point`
- What: The distinguished affine point `(X, Y)` on the universal pointed curve.
- How: Constructs the point via `.mk equation_point` (the affine-point constructor from the equation witness).
- Hypotheses: none.
- Uses from project: [`curve`, `Universal.Field`, `equation_point`]
- Used by: `Jacobian.point`
- Visibility: public
- Lines: 149-152 (no proof)
- Notes: none

### def Jacobian.point
- Type: `Jacobian.point : Jacobian.Point (curve.baseChange Universal.Field)`
- What: The distinguished point on the universal curve in Jacobian coordinates.
- How: `Jacobian.Point.fromAffine` applied to `Affine.point`.
- Hypotheses: none.
- Uses from project: [`curve`, `Universal.Field`, `Affine.point`]
- Used by: unused in file
- Visibility: public
- Lines: 154-156 (no proof)
- Notes: none

### lemma pointedCurve_a₁
- Type: `pointedCurve.a₁ = polyToField (CC curve.a₁)`
- What: Identifies the `a₁`-coefficient of the universal pointed curve as the image of the universal `a₁` under `polyToField ∘ CC`.
- How: Definitional `rfl`.
- Hypotheses: none.
- Uses from project: [`pointedCurve`, `polyToField`, `curve`]
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 160 (proof: rfl)
- Notes: none

### lemma pointedCurve_a₂
- Type: `pointedCurve.a₂ = polyToField (CC curve.a₂)`
- What: Identifies the `a₂`-coefficient of the universal pointed curve via `polyToField ∘ CC`.
- How: Definitional `rfl`.
- Hypotheses: none.
- Uses from project: [`pointedCurve`, `polyToField`, `curve`]
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 161 (proof: rfl)
- Notes: none

### lemma pointedCurve_a₃
- Type: `pointedCurve.a₃ = polyToField (CC curve.a₃)`
- What: Identifies the `a₃`-coefficient of the universal pointed curve via `polyToField ∘ CC`.
- How: Definitional `rfl`.
- Hypotheses: none.
- Uses from project: [`pointedCurve`, `polyToField`, `curve`]
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 162 (proof: rfl)
- Notes: none

### lemma pointedCurve_a₄
- Type: `pointedCurve.a₄ = polyToField (CC curve.a₄)`
- What: Identifies the `a₄`-coefficient of the universal pointed curve via `polyToField ∘ CC`.
- How: Definitional `rfl`.
- Hypotheses: none.
- Uses from project: [`pointedCurve`, `polyToField`, `curve`]
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 163 (proof: rfl)
- Notes: none

### lemma pointedCurve_a₆
- Type: `pointedCurve.a₆ = polyToField (CC curve.a₆)`
- What: Identifies the `a₆`-coefficient of the universal pointed curve via `polyToField ∘ CC`.
- How: Definitional `rfl`.
- Hypotheses: none.
- Uses from project: [`pointedCurve`, `polyToField`, `curve`]
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 164 (proof: rfl)
- Notes: none

### abbrev curvePoly
- Type: `curvePoly : WeierstrassCurve Poly := curve.baseChange Poly`
- What: The base change of the universal curve from `ℤ[A₁,…,A₆]` up to `Poly = ℤ[A₁,…,A₆,X,Y]`.
- How: Abbreviation `curve.baseChange Poly`.
- Hypotheses: none.
- Uses from project: [`curve`, `Poly`]
- Used by: unused in file
- Visibility: public
- Lines: 166-167 (no proof)
- Notes: none

### abbrev curveRing
- Type: `curveRing : WeierstrassCurve Universal.Ring := curve.baseChange Universal.Ring`
- What: The base change of the universal curve to the universal ring `ℤ[A₁,…,A₆,X,Y]/⟨P⟩`.
- How: Abbreviation `curve.baseChange Universal.Ring`.
- Hypotheses: none.
- Uses from project: [`curve`, `Universal.Ring`]
- Used by: `curveRing_map_ringEval`
- Visibility: public
- Lines: 168-170 (no proof)
- Notes: none

### abbrev curveField
- Type: `curveField : WeierstrassCurve Universal.Field := curve.baseChange Universal.Field`
- What: The base change of the universal curve to the universal field `Frac(ℤ[A₁,…,A₆,X,Y]/⟨P⟩)`.
- How: Abbreviation `curve.baseChange Universal.Field`.
- Hypotheses: none.
- Uses from project: [`curve`, `Universal.Field`]
- Used by: `curveField_eq`
- Visibility: public
- Lines: 171-173 (no proof)
- Notes: none

### lemma curveField_eq
- Type: `curveField = pointedCurve`
- What: The base-changed curve `curveField` is definitionally the same as `pointedCurve`.
- How: Definitional `rfl`.
- Hypotheses: none.
- Uses from project: [`curveField`, `pointedCurve`]
- Used by: unused in file
- Visibility: public
- Lines: 175 (proof: rfl)
- Notes: none

### def cusp
- Type: `cusp : Affine ℤ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }`
- What: The cuspidal Weierstrass curve `Y² = X³` over `ℤ` (all coefficients zero).
- How: Structure literal with all `aᵢ = 0`.
- Hypotheses: none.
- Uses from project: []
- Used by: `cusp_equation_one_one`
- Visibility: public
- Lines: 179-180 (no proof)
- Notes: none

### lemma cusp_equation_one_one
- Type: `cusp.Equation 1 1`
- What: The point `(1, 1)` lies on the cusp curve `Y² = X³` (since `1 = 1`).
- How: `simp` unfolding `Affine.Equation`, `Affine.polynomial`, `cusp`, `Polynomial.evalEval`.
- Hypotheses: none.
- Uses from project: [`cusp`]
- Used by: `Field.two_ne_zero` (via `ringEval cusp_equation_one_one`)
- Visibility: public
- Lines: 182-183 (proof ~1 line)
- Notes: none

### def specialize
- Type: `specialize : MvPolynomial Coeff ℤ →+* R`
- What: The specialization homomorphism sending each universal coefficient variable `Aᵢ` to the actual coefficient `W.aᵢ` of a given Weierstrass curve `W` over `R`.
- How: `(MvPolynomial.aeval <| Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom` — evaluation of the multivariate polynomial at the curve's coefficients.
- Hypotheses: `R` a commutative ring; `W : WeierstrassCurve R`.
- Uses from project: [`Coeff`]
- Used by: `map_specialize`, `polyEval`, `polyEval_apply`, `ringEval`, `polyEval_comp_eq_specialize`, `ringEval_comp_eq_specialize`
- Visibility: public
- Lines: 188-191 (no proof)
- Notes: none

### lemma map_specialize
- Type: `Universal.curve.map W.specialize = W`
- What: Mapping the universal curve along the specialization homomorphism `W.specialize` recovers the original curve `W`; i.e. every Weierstrass curve is a specialization of the universal one.
- How: `simp [specialize, curve, map]` — unfolds the definitions; each universal generator `X Aᵢ` evaluates back to `W.aᵢ`.
- Hypotheses: `W : WeierstrassCurve R`.
- Uses from project: [`curve`, `specialize`]
- Used by: `ringEval` (in its defining proof), `curveRing_map_ringEval`
- Visibility: public
- Lines: 193-194 (proof ~1 line)
- Notes: none

### def polyEval
- Type: `polyEval : Poly →+* R`
- What: The evaluation homomorphism `ℤ[A₁,…,A₆,X,Y] → R` induced by a curve `W` and a chosen affine point `(x, y)`: specialize the coefficients via `W.specialize` and evaluate `X ↦ x`, `Y ↦ y`.
- How: `eval₂RingHom (eval₂RingHom W.specialize x) y` — nested two-variable evaluation built on `specialize`.
- Hypotheses: `W : WeierstrassCurve R`; `x y : R`.
- Uses from project: [`Poly`, `specialize`]
- Used by: `polyEval_apply`, `ringEval_mk`, `ringEval_comp_mk`, `polyEval_comp_eq_specialize`
- Visibility: public
- Lines: 200-203 (no proof)
- Notes: none

### lemma polyEval_apply
- Type: `polyEval W x y p = (p.map <| mapRingHom W.specialize).evalEval x y`
- What: Expresses `polyEval` on `p` as: map the coefficients of `p` along `W.specialize`, then evaluate the resulting bivariate polynomial at `(x, y)`.
- How: `eval₂_eval₂RingHom_apply` (mathlib lemma equating nested `eval₂RingHom` with map-then-`evalEval`).
- Hypotheses: `W : WeierstrassCurve R`; `x y : R`; `p : Poly`.
- Uses from project: [`polyEval`, `specialize`, `Poly` (implicit)]
- Used by: unused in file
- Visibility: public
- Lines: 205-208 (proof ~1 line)
- Notes: none

### def ringEval
- Type: `ringEval : Universal.Ring →+* R`
- What: Given a point `(x, y)` actually **on** a curve `W` (witnessed by the equation `eqn`), the induced specialization homomorphism from the universal ring `ℤ[A₁,…,A₆,X,Y]/⟨P⟩` to `R`.
- How: `AdjoinRoot.lift (eval₂RingHom W.specialize x) y …`; the side condition (the lift respects the relation `P`) is discharged by rewriting `coe_eval₂RingHom`, `eval₂RingHom_eval₂RingHom`, `coe_mapRingHom`, then `Affine.map_polynomial` and `map_specialize`, reducing to the hypothesis `eqn` that `(x,y)` satisfies `W`'s equation.
- Hypotheses: `{W x y}` implicit; `eqn : Affine.Equation W x y` (the point lies on `W`).
- Uses from project: [`Universal.Ring`, `specialize`, `map_specialize`]
- Used by: `ringEval_mk`, `ringEval_comp_mk`, `ringEval_comp_eq_specialize`, `Field.two_ne_zero`, `curveRing_map_ringEval`
- Visibility: public
- Lines: 212-218 (proof ~3 lines side condition)
- Notes: none

### lemma ringEval_mk
- Type: `ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p`
- What: `ringEval` composed with the quotient map `AdjoinRoot.mk` agrees with `polyEval` on representatives.
- How: `AdjoinRoot.lift_mk` (the computation rule for `AdjoinRoot.lift` on `mk`).
- Hypotheses: `eqn : Affine.Equation W x y`; `p : Poly`.
- Uses from project: [`ringEval`, `polyEval`, `Poly` (implicit)]
- Used by: `ringEval_comp_mk`
- Visibility: public
- Lines: 220-221 (proof ~1 line)
- Notes: none

### lemma ringEval_comp_mk
- Type: `(ringEval eqn).comp (AdjoinRoot.mk _) = polyEval W x y`
- What: The composite `ringEval ∘ AdjoinRoot.mk` equals `polyEval` as ring homomorphisms (the previous lemma upgraded to an equality of maps).
- How: `RingHom.ext (ringEval_mk eqn)` — extensionality plus the pointwise lemma.
- Hypotheses: `eqn : Affine.Equation W x y`.
- Uses from project: [`ringEval`, `polyEval`, `ringEval_mk`]
- Used by: `ringEval_comp_eq_specialize`
- Visibility: public
- Lines: 223-224 (proof ~1 line)
- Notes: none

### lemma polyEval_comp_eq_specialize
- Type: `(polyEval W x y).comp (algebraMap _ _) = W.specialize`
- What: Restricting `polyEval` to the coefficient subring `ℤ[A₁,…,A₆]` recovers `W.specialize`.
- How: `ext <;> simp [polyEval]` — extensionality on generators, then unfold.
- Hypotheses: `W : WeierstrassCurve R`; `x y : R`.
- Uses from project: [`polyEval`, `specialize`]
- Used by: `ringEval_comp_eq_specialize`
- Visibility: public
- Lines: 226-227 (proof ~1 line)
- Notes: none

### lemma ringEval_comp_eq_specialize
- Type: `(ringEval eqn).comp (algebraMap _ _) = W.specialize`
- What: Restricting `ringEval` to the coefficient subring `ℤ[A₁,…,A₆]` recovers `W.specialize`.
- How: Rewrites `algebraMap_ring_eq_comp`, reassociates (`← RingHom.comp_assoc`), then applies `ringEval_comp_mk` and `polyEval_comp_eq_specialize`.
- Hypotheses: `eqn : Affine.Equation W x y`.
- Uses from project: [`ringEval`, `specialize`, `algebraMap_ring_eq_comp`, `ringEval_comp_mk`, `polyEval_comp_eq_specialize`]
- Used by: `curveRing_map_ringEval`
- Visibility: public
- Lines: 229-230 (proof ~1 line)
- Notes: none

### lemma Field.two_ne_zero
- Type: `protected lemma Field.two_ne_zero : (2 : Universal.Field) ≠ 0`
- What: The element `2` is nonzero in the universal field.
- How: Reduces to `2 ≠ 0` in `Universal.Ring` via `map_ofNat`/`map_ne_zero_iff` with `IsFractionRing.injective`; then specializes to the cusp curve at `(1,1)` using `ringEval cusp_equation_one_one`, where `2 = 0` would force `2 = 0` in `ℤ` (contradiction via `map_ofNat`, `map_zero`, `cases h`).
- Hypotheses: none.
- Uses from project: [`Universal.Field`, `Universal.Ring`, `ringEval`, `cusp_equation_one_one`]
- Used by: unused in file
- Visibility: public (protected)
- Lines: 232-235 (proof ~3 lines)
- Notes: none

### lemma curveRing_map_ringEval
- Type: `curveRing.map (ringEval eqn) = W`
- What: Mapping the universal-ring curve `curveRing` along `ringEval eqn` recovers the original curve `W`.
- How: Uses `map_map curve (algebraMap _ _) (ringEval eqn)` (composition of maps) together with rewrites `ringEval_comp_eq_specialize eqn` and `map_specialize W` (via `▸`).
- Hypotheses: `eqn : Affine.Equation W x y`.
- Uses from project: [`curveRing`, `ringEval`, `curve`, `ringEval_comp_eq_specialize`, `map_specialize`]
- Used by: unused in file
- Visibility: public
- Lines: 237-239 (proof ~3 lines)
- Notes: none

---

## File Summary

- **Total declarations: 39** — defs: 6 (`curve`, `polyToField`, `Affine.point`, `Jacobian.point`, `cusp`, `specialize`, `polyEval`, `ringEval` = **8 defs** counting `polyEval`/`ringEval`; *defs* = 8); lemmas+theorems: 27; instances: 2; inductive: 1; abbrevs: 7. (Breakdown: 1 inductive `Coeff`; 8 defs; 7 abbrevs `Poly`, `Universal.Ring`, `Universal.Field`, `pointedCurve`, `curvePoly`, `curveRing`, `curveField`; 2 instances `CommRing Poly`, `pointedCurve.IsElliptic`; 27 lemmas.)

  Recount for clarity — defs (8): `curve`, `polyToField`, `Affine.point`, `Jacobian.point`, `cusp`, `specialize`, `polyEval`, `ringEval`. Lemmas/theorems (21): `algebraMap_poly_injective`, `algebraMap_injective'`, `some_eq_some_iff`, `Δ_curve_ne_zero`, `Poly.two_ne_zero`, `polyToField_apply`, `algebraMap_field_eq_comp`, `algebraMap_ring_eq_comp`, `polyToField_polynomial`, `algebraMap_field_injective`, `equation_point`, `pointedCurve_a₁`..`a₆` (5), `curveField_eq`, `cusp_equation_one_one`, `map_specialize`, `polyEval_apply`, `ringEval_mk`, `ringEval_comp_mk`, `polyEval_comp_eq_specialize`, `ringEval_comp_eq_specialize`, `Field.two_ne_zero`, `curveRing_map_ringEval`. Abbrevs (7) + inductive (1) + instances (2). **Total entries documented: 39.**

- **Key API (used by ≥3 in-file):**
  - `curve` — foundational; used by ~15 decls.
  - `polyToField` — used by `polyToField_apply`, `algebraMap_field_eq_comp`, `polyToField_polynomial`, `equation_point`, `pointedCurve_a₁..a₆`.
  - `Universal.Field` — used by `polyToField`, `algebraMap_field_*`, `pointedCurve`, `IsElliptic`, `equation_point`, `curveField`, `Field.two_ne_zero`.
  - `Universal.Ring` — used by `Universal.Field`, `polyToField`, `algebraMap_ring_eq_comp`, `algebraMap_field_injective`, `curveRing`, `Field.two_ne_zero`, `ringEval`.
  - `specialize` — used by `map_specialize`, `polyEval`, `ringEval`, `polyEval_apply`, `polyEval_comp_eq_specialize`, `ringEval_comp_eq_specialize`.
  - `pointedCurve` — used by `IsElliptic`, `equation_point`, `pointedCurve_a₁..a₆`, `curveField_eq`.
  - `ringEval` — used by `ringEval_mk`, `ringEval_comp_mk`, `ringEval_comp_eq_specialize`, `Field.two_ne_zero`, `curveRing_map_ringEval`.
  - `Coeff` — index type, used pervasively (`curve`, `Poly`, `specialize`, `algebraMap_*`).

- **Unused decls (in this file; likely consumed by sibling files in the project):** `some_eq_some_iff`, `CommRing Poly` instance, `Poly.two_ne_zero`, `algebraMap_field_eq_comp` (used once → not unused), `pointedCurve_a₁..a₆` (5 simp lemmas), `Jacobian.point`, `curvePoly`, `curveField_eq`, `polyEval_apply`, `Field.two_ne_zero`, `curveRing_map_ringEval`, `IsElliptic` instance (implicit use). These are public API exported for downstream division-polynomial / ZSMul development.

- **Decls with `sorry`: none.**

- **Decls with `set_option`: 1** — `algebraMap_poly_injective` (`set_option backward.isDefEq.respectTransparency false in`).

- **Proofs > 50 lines (OVER-50): none (count 0).**

- **Proofs 30–50 lines long(30-50): none (count 0).**

- **Longest proof:** `equation_point` (~10 lines, lines 137–147). All other proofs are ≤ ~4 lines; the bulk of the file is definitions, abbreviations, and one-line `rfl`/`simp` lemmas.
