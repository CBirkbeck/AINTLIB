# Inventory: ./HasseWeil/Curves/Miller.lean

**File summary**: 2200 lines. Proves Miller's relation (Silverman III.3.5) — the chord/tangent divisor identity `(P)+(Q)−(P+Q)−(O)` is principal — and upgrades it to the unconditional `MillerHypothesis W`, `DivZeroReduce W`, `AFInputs W`, and `Pic⁰(E) ≅ E` isomorphism (`picZeroIsoE`). Then provides IsogenyBaseChange §5 wrappers (Frobenius/Verschiebung on Pic⁰). No sorries. No `set_option maxHeartbeats`.

---

## Namespace `HasseWeil.Curves` (degenerate Miller cases)

### `theorem miller_of_zero_left`
- **Type**: `∀ Q : W.Point, ProjIsPrincipal ⟨W⟩ ((0) + (Q) − (0+Q) − (O))`
- **What**: The Miller divisor at `(0, Q)` is zero (principal), since `0+Q=Q` and `0.toProj=∞`, so the divisor cancels.
- **How**: Rewrites `zero_add Q` and `0.toProjectiveSmoothPoint = ∞`, then `abel` reduces to zero; finishes with `projIsPrincipal_zero`.
- **Hypotheses**: None (omits IsElliptic).
- **Uses from project**: `SmoothPlaneCurve.projIsPrincipal_zero`
- **Used by**: `miller_hypothesis_holds`
- **Visibility**: public
- **Lines**: 62–81, proof ~14 lines

---

### `theorem miller_of_zero_right`
- **Type**: `∀ P : W.Point, ProjIsPrincipal ⟨W⟩ ((P) + (0) − (P+0) − (O))`
- **What**: The Miller divisor at `(P, 0)` is zero (principal), same argument as left-zero.
- **How**: Rewrites `add_zero P`, `0.toProjectiveSmoothPoint = ∞`, then `abel` + `projIsPrincipal_zero`.
- **Hypotheses**: None (omits IsElliptic).
- **Uses from project**: `SmoothPlaneCurve.projIsPrincipal_zero`
- **Used by**: `miller_hypothesis_holds`
- **Visibility**: public
- **Lines**: 86–105, proof ~14 lines

---

### `theorem miller_divisor_at_neg_eq_vertical`
- **Type**: `(P)+(−P)−(P+(−P))−(O) = (P)+(−P)−2·(O)` as a `ProjectiveDivisor` equality.
- **What**: Pure algebraic rearrangement: since `P+(−P)=0` and `0.toProj=∞`, the Miller divisor at `(P,−P)` equals the vertical-line divisor.
- **How**: Rewrites `add_neg_cancel P` and unfolds `2·single ∞ 1 = single ∞ 1 + single ∞ 1`, then `abel`.
- **Hypotheses**: None (omits IsElliptic).
- **Uses from project**: none
- **Used by**: `miller_of_neg_of_vertical_principal`
- **Visibility**: public
- **Lines**: 122–143, proof ~16 lines

---

### `theorem miller_of_neg_of_vertical_principal`
- **Type**: If `(P)+(−P)−2·(O)` is principal, then the Miller divisor at `(P,−P)` is principal.
- **What**: Reduces the `(P,−P)` Miller case to `h_vert` (the vertical-line principal hypothesis) via `miller_divisor_at_neg_eq_vertical`.
- **How**: One `rw [miller_divisor_at_neg_eq_vertical]` then `exact h_vert`.
- **Hypotheses**: Hypothesis `h_vert : ProjIsPrincipal ⟨W⟩ ((P)+(−P)−2·(O))`.
- **Uses from project**: `miller_divisor_at_neg_eq_vertical`
- **Used by**: `miller_at_neg_of_some`
- **Visibility**: public
- **Lines**: 149–162, proof 3 lines

---

## Namespace `HasseWeil.Curves.SmoothPlaneCurve` — vertical-line scaffolding

### `theorem coordX_sub_const_eq_algebraMap_XClass`
- **Type**: `C.coordX − algebraMap F C.FunctionField a = algebraMap C.CoordinateRing C.FunctionField (XClass C.toAffine a)`
- **What**: Identifies the function-field element `X−a` with the image of `XClass a` from the coordinate ring. Bridge between the function-field coordX and the ring-theoretic XClass.
- **How**: Uses `IsScalarTower.algebraMap_apply` twice to move scalars through the tower, then `map_sub`, `congr 1`, and `Polynomial.C_sub`.
- **Hypotheses**: Field `F`, smooth plane curve `C`.
- **Uses from project**: none (pure mathlib/scalar-tower)
- **Used by**: `coordX_sub_const_ne_zero`, `divisorOf_coordX_sub_const_apply`
- **Visibility**: public
- **Lines**: 177–205, proof ~29 lines

---

### `theorem coordX_sub_const_ne_zero`
- **Type**: `C.coordX − algebraMap F C.FunctionField a ≠ 0`
- **What**: The function `X−a` is nonzero in `K(C)`, since `XClass a ≠ 0` in the coordinate ring and the algebra map is injective.
- **How**: Rewrites via `coordX_sub_const_eq_algebraMap_XClass`, then applies `XClass_ne_zero` and injectivity of `IsFractionRing`.
- **Hypotheses**: Field `F`, smooth plane curve `C`.
- **Uses from project**: `coordX_sub_const_eq_algebraMap_XClass`
- **Used by**: `vertical_line_principal`, `miller_at_addSmoothPoint_principal`
- **Visibility**: public
- **Lines**: 209–214, proof 5 lines

---

### `theorem ordAtInfty_coordX_sub_const`
- **Type**: `C.ordAtInfty (C.coordX − algebraMap F C.FunctionField a) = (−2 : ℤ)`
- **What**: The order at infinity of the vertical line function `X−a` is −2 (double pole at ∞ on a Weierstrass curve).
- **How**: Expresses as `algebraMap (Polynomial F) K(C) (X − C a)`, then applies `ordAtInfty_algebraMap_polynomial_of_ne_zero` with `natDegree (X−Ca) = 1`, giving `−2·1 = −2`.
- **Hypotheses**: Field `F`, smooth plane curve `C`.
- **Uses from project**: `ordAtInfty_algebraMap_polynomial_of_ne_zero` (via imports), `coordX`
- **Used by**: `projectiveDivisorOf_coordX_sub_const`
- **Visibility**: public
- **Lines**: 220–236, proof ~18 lines

---

### `theorem divisorOf_coordX_sub_const_apply`
- **Type**: Under `[IsIntegrallyClosed C.CoordinateRing]`, `C.divisorOf (C.coordX − a) P = count(maximalIdealAt P, span{XClass a})`
- **What**: Gives the coefficient of `P` in the affine divisor of `X−a` as the Dedekind-domain count of `maximalIdealAt P` in `span{XClass a}`.
- **How**: Applies `coordX_sub_const_eq_algebraMap_XClass` and then `divisorOf_algebraMap_apply_eq_count`.
- **Hypotheses**: `IsIntegrallyClosed C.CoordinateRing`.
- **Uses from project**: `coordX_sub_const_eq_algebraMap_XClass`, `divisorOf_algebraMap_apply_eq_count`
- **Used by**: `divisorOf_coordX_sub_const_apply_eq_zero_of_x_ne`, `divisorOf_coordX_sub_const_apply_eq_finsupp`
- **Visibility**: public
- **Lines**: 243–254, proof ~12 lines

---

### `theorem divisorOf_coordX_sub_const_apply_eq_zero_of_x_ne`
- **Type**: Under `[IsIntegrallyClosed C.CoordinateRing]`, if `Q.x ≠ a` then `C.divisorOf (C.coordX − a) Q = 0`
- **What**: The vertical line `X−a` has zero order at any smooth point `Q` not lying over `x=a`.
- **How**: Uses `divisorOf_coordX_sub_const_apply`; proves `XClass a ∉ maximalIdealAt Q` via the membership criterion (`mem_maximalIdealAt_iff_eval_zero`) and `Q.x ≠ a`, then applies `Associates.count_eq_zero_of_ne` / nonmembership implies count 0.
- **Hypotheses**: `IsIntegrallyClosed C.CoordinateRing`, `Q.x ≠ a`.
- **Uses from project**: `divisorOf_coordX_sub_const_apply`, `maximalIdealAt_ne_bot`, `maximalIdealAt_isMaximal`, `mem_maximalIdealAt_iff_eval_zero`
- **Used by**: (not called within this file; exposed for downstream)
- **Visibility**: public
- **Lines**: 260–312, proof ~53 lines
- **Notes**: Proof > 30 lines.

---

### `noncomputable def SmoothPoint.neg`
- **Type**: `{C : SmoothPlaneCurve F} → C.SmoothPoint → C.SmoothPoint`; with `x := P.x`, `y := C.toAffine.negY P.x P.y`.
- **What**: Smooth-point negation: same x-coordinate, y replaced by `negY`. Uses `Affine.nonsingular_neg` to verify the result is nonsingular.
- **How**: Definitional construction using `nonsingular_neg`.
- **Hypotheses**: `[Field F]`.
- **Uses from project**: none (wraps mathlib's `nonsingular_neg`)
- **Used by**: `SmoothPoint.neg_x`, `SmoothPoint.neg_y`, `SmoothPoint.neg_neg`, `maximalIdealAt_neg`, `span_XClass_eq_maximalIdealAt_neg_mul`, `smoothPoint_x_eq_iff_self_or_neg`, `divisorOf_coordX_sub_const_apply_eq_finsupp`, `divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp`, etc.
- **Visibility**: public (`_root_` qualified)
- **Lines**: 319–324, def body ~6 lines

---

### `@[simp] theorem SmoothPoint.neg_x`
- **Type**: `P.neg.x = P.x`
- **What**: x-coordinate of the negated smooth point equals the original x.
- **How**: `rfl`.
- **Hypotheses**: none
- **Uses from project**: `SmoothPoint.neg`
- **Used by**: `smoothPoint_x_eq_iff_self_or_neg`, etc.
- **Visibility**: public
- **Lines**: 326–327

---

### `@[simp] theorem SmoothPoint.neg_y`
- **Type**: `P.neg.y = C.toAffine.negY P.x P.y`
- **What**: y-coordinate of the negated smooth point is `negY`.
- **How**: `rfl`.
- **Hypotheses**: none
- **Uses from project**: `SmoothPoint.neg`
- **Used by**: `SmoothPoint.neg_neg`, `smoothPoint_x_eq_iff_self_or_neg`
- **Visibility**: public
- **Lines**: 329–330

---

### `@[simp] theorem SmoothPoint.neg_neg`
- **Type**: `P.neg.neg = P`
- **What**: Negation is an involution on smooth points.
- **How**: `ext` then `rfl` for x; `negY_negY` for y.
- **Hypotheses**: none
- **Uses from project**: `SmoothPoint.neg`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 332–336

---

### `theorem maximalIdealAt_neg`
- **Type**: `C.maximalIdealAt P.neg = XYIdeal C.toAffine P.x (Polynomial.C (C.toAffine.negY P.x P.y))`
- **What**: The maximal ideal at the negated smooth point matches mathlib's `XYIdeal` of the negated y-coordinate. Definitional.
- **How**: `rfl`.
- **Hypotheses**: none
- **Uses from project**: `SmoothPoint.neg`
- **Used by**: `span_XClass_eq_maximalIdealAt_neg_mul`
- **Visibility**: public
- **Lines**: 340–343

---

### `theorem span_XClass_eq_maximalIdealAt_neg_mul`
- **Type**: `span {XClass P.x} = maximalIdealAt P.neg * maximalIdealAt P`
- **What**: The vertical-line ideal `⟨X − P.x⟩` factors as the product of the maximal ideals at `P` and `−P`. Wraps mathlib's `XYIdeal_neg_mul`.
- **How**: Rewrites `maximalIdealAt_neg`, unfolds `maximalIdealAt`, applies `XYIdeal_neg_mul`.
- **Hypotheses**: P nonsingular.
- **Uses from project**: `maximalIdealAt_neg`, `maximalIdealAt`
- **Used by**: `divisorOf_coordX_sub_const_apply_eq_finsupp`
- **Visibility**: public
- **Lines**: 348–354

---

### `theorem count_maximalIdealAt_self`
- **Type**: Under `[IsIntegrallyClosed C.CoordinateRing]`, `count(maximalIdealAt P, maximalIdealAt P) = 1`
- **What**: The maximal ideal at P counts once in its own factorisation.
- **How**: Builds the HeightOneSpectrum `vP` from `maximalIdealAt P` and applies `Associates.count_self`.
- **Hypotheses**: `IsIntegrallyClosed C.CoordinateRing`.
- **Uses from project**: `maximalIdealAt_isMaximal`, `maximalIdealAt_ne_bot`
- **Used by**: `divisorOf_coordX_sub_const_apply_eq_finsupp`, `count_maximalIdealAt_eq_single`
- **Visibility**: public
- **Lines**: 359–365

---

### `theorem count_maximalIdealAt_eq_zero_of_ne`
- **Type**: Under `[IsIntegrallyClosed C.CoordinateRing]`, if `Q ≠ P` then `count(maximalIdealAt Q, maximalIdealAt P) = 0`
- **What**: Distinct smooth points have disjoint maximal ideals in the count sense.
- **How**: Builds HeightOneSpectra `vQ, vP`; shows `mk vQ.asIdeal ≠ mk vP.asIdeal` from `maximalIdealAt_injective`; applies `Associates.count_eq_zero_of_ne`.
- **Hypotheses**: `IsIntegrallyClosed C.CoordinateRing`, `Q ≠ P`.
- **Uses from project**: `maximalIdealAt_isMaximal`, `maximalIdealAt_ne_bot`, `maximalIdealAt_injective`
- **Used by**: `divisorOf_coordX_sub_const_apply_eq_finsupp`, `count_maximalIdealAt_eq_single`
- **Visibility**: public
- **Lines**: 371–387

---

### `theorem smoothPoint_x_eq_iff_self_or_neg`
- **Type**: If `Q.x = P.x` then `Q = P ∨ Q = P.neg`
- **What**: Fibre dichotomy: points with the same x-coordinate are either equal or negations (follows from the two roots of the Weierstrass equation in y at fixed x).
- **How**: Uses `WeierstrassCurve.Affine.Y_eq_of_X_eq` (mathlib) to get two cases for y, constructs equality in each via `SmoothPoint.ext`.
- **Hypotheses**: `Q.x = P.x`.
- **Uses from project**: `SmoothPoint.neg`, `SmoothPoint.neg_y`
- **Used by**: `divisorOf_coordX_sub_const_apply_eq_finsupp`
- **Visibility**: public
- **Lines**: 392–403

---

### `theorem divisorOf_coordX_sub_const_apply_eq_finsupp`
- **Type**: Under `[IsAlgClosed F] [NeZero 2] [NeZero 3] [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing]`, `C.divisorOf (C.coordX − P.x) Q = (single P 1 + single P.neg 1) Q`
- **What**: Pointwise identity: the affine divisor of the vertical line `X − P.x` at any smooth point Q equals the sum of Dirac masses at P and P.neg.
- **How**: Expands via `divisorOf_coordX_sub_const_apply` and `span_XClass_eq_maximalIdealAt_neg_mul`; applies `Associates.count_mul`; computes diagonal counts via `count_maximalIdealAt_self` and cross counts via `count_maximalIdealAt_eq_zero_of_ne`; finishes with `split_ifs` + `ring`.
- **Hypotheses**: `IsAlgClosed F`, `NeZero 2`, `NeZero 3`, `IsElliptic`, `IsIntegrallyClosed C.CoordinateRing`.
- **Uses from project**: `divisorOf_coordX_sub_const_apply`, `span_XClass_eq_maximalIdealAt_neg_mul`, `count_maximalIdealAt_self`, `count_maximalIdealAt_eq_zero_of_ne`, `maximalIdealAt_isMaximal`, `maximalIdealAt_ne_bot`
- **Used by**: `divisorOf_coordX_sub_const`, `divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp`
- **Visibility**: public
- **Lines**: 413–463, proof ~55 lines
- **Notes**: Proof > 30 lines.

---

### `theorem divisorOf_coordX_sub_const`
- **Type**: Under same hypotheses, `C.divisorOf (C.coordX − P.x) = single P 1 + single P.neg 1`
- **What**: Global Finsupp identity for the affine divisor of `X − P.x`.
- **How**: `Finsupp.ext` from `divisorOf_coordX_sub_const_apply_eq_finsupp`.
- **Hypotheses**: Same as above.
- **Uses from project**: `divisorOf_coordX_sub_const_apply_eq_finsupp`
- **Used by**: `projectiveDivisorOf_coordX_sub_const`
- **Visibility**: public
- **Lines**: 468–474

---

### `theorem projectiveDivisorOf_coordX_sub_const`
- **Type**: Under same hypotheses, `C.projectiveDivisorOf (C.coordX − P.x) = single (affine P) 1 + single (affine P.neg) 1 − 2·single ∞ 1`
- **What**: Full projective divisor of the vertical line: `(P) + (P.neg) − 2·(∞)`.
- **How**: Unfolds `projectiveDivisorOf`; uses `divisorOf_coordX_sub_const` and `ordAtInfty_coordX_sub_const`; maps Finsupp.single through `Divisor.toProjective` via `Finsupp.mapDomain_single`; finishes with `abel`.
- **Hypotheses**: Same as above.
- **Uses from project**: `divisorOf_coordX_sub_const`, `ordAtInfty_coordX_sub_const`, `Divisor.toProjective_add`
- **Used by**: `vertical_line_principal`, `miller_at_addSmoothPoint_principal`
- **Visibility**: public
- **Lines**: 479–519, proof ~41 lines
- **Notes**: Proof > 30 lines.

---

### `theorem vertical_line_principal`
- **Type**: Under same hypotheses, `ProjIsPrincipal C ((affine P) + (affine P.neg) − 2·(∞))`
- **What**: The divisor `(P) + (P.neg) − 2·(∞)` is principal, witnessed by `coordX − P.x`.
- **How**: Constructs the witness triple `⟨coordX − P.x, coordX_sub_const_ne_zero, projectiveDivisorOf_coordX_sub_const⟩`.
- **Hypotheses**: Same as above.
- **Uses from project**: `coordX_sub_const_ne_zero`, `projectiveDivisorOf_coordX_sub_const`
- **Used by**: `miller_at_neg_of_some`, `miller_at_some_some_degen`, `projectiveDivisorSum_vertical_line_of_principal`
- **Visibility**: public
- **Lines**: 526–537

---

## Chord-line scaffolding

### `theorem coordY_sub_algMap_linePolynomial_eq_algMap_YClass`
- **Type**: `C.coordY − algebraMap (Polynomial F) K(C) (linePolynomial x y slope) = algebraMap C.CoordinateRing K(C) (YClass C.toAffine (linePolynomial x y slope))`
- **What**: Identifies the function-field element `Y − ℓ(X)` with the image of `YClass(linePoly)` from the coordinate ring.
- **How**: Expresses `coordY` via `basis_one`, expresses `algMap linePoly` via the scalar tower, applies `map_sub` and unfolds `YClass`.
- **Hypotheses**: `[Field F]`, `SmoothPlaneCurve C`.
- **Uses from project**: `coordY`, `coordYInFunctionField`, `CoordinateRing.basis_one`
- **Used by**: `coordY_sub_algMap_linePolynomial_ne_zero`, `divisorOf_coordY_sub_algMap_linePolynomial_apply`
- **Visibility**: public
- **Lines**: 551–585, proof ~35 lines
- **Notes**: Proof > 30 lines.

---

### `theorem coordY_sub_algMap_linePolynomial_ne_zero`
- **Type**: `C.coordY − algebraMap (Polynomial F) K(C) (linePolynomial x y slope) ≠ 0`
- **What**: The chord/tangent line function is nonzero in `K(C)`.
- **How**: Uses `coordY_sub_algMap_linePolynomial_eq_algMap_YClass` then `YClass_ne_zero` and injectivity.
- **Hypotheses**: `[Field F]`.
- **Uses from project**: `coordY_sub_algMap_linePolynomial_eq_algMap_YClass`
- **Used by**: `miller_at_addSmoothPoint_principal`, `projectiveDivisorSum_chord_line`
- **Visibility**: public
- **Lines**: 589–596

---

### `theorem ordAtInfty_coordY_sub_algMap_linePolynomial`
- **Type**: `C.ordAtInfty (C.coordY − algMap linePoly) = (−3 : ℤ)`
- **What**: The chord/tangent line has a triple pole at infinity (Y has weight 3, the polynomial term has weight ≤ 2).
- **How**: Writes the function as `algMap(−linePoly) + algMap(1) · coordYInFunctionField`; applies `ordAtInfty_basis_polynomial_of_both_ne_zero`; bounds `natDegree(linePoly) ≤ 1` by hand (Polynomial.natDegree_add_le + natDegree_C + natDegree_X_sub_C); computes `max(2·natDeg, 3) = 3`. Handles the degenerate `linePoly = 0` case separately via `ordAtInfty_coordYInFunctionField`.
- **Hypotheses**: `[Field F]`.
- **Uses from project**: `coordY_eq_coordYInFunctionField`, `ordAtInfty_basis_polynomial_of_both_ne_zero`, `ordAtInfty_coordYInFunctionField`
- **Used by**: `projectiveDivisorOf_coordY_sub_algMap_linePolynomial`
- **Visibility**: public
- **Lines**: 601–667, proof ~67 lines
- **Notes**: Proof > 30 lines.

---

### `theorem span_XClass_mul_maximalIdealAt_mul_eq`
- **Type**: `span{XClass(addX)} * (maximalIdealAt SP * maximalIdealAt SQ) = span{YClass(linePoly)} * XYIdeal(addX, addY)` in C.CoordinateRing
- **What**: Structural ideal identity: the product of the vertical-at-sum ideal with the two input ideals equals the chord-line ideal times the sum-point ideal. Wraps mathlib's `XYIdeal_mul_XYIdeal`.
- **How**: Unfolds `maximalIdealAt` and identifies `span{XClass} = XIdeal`, `span{YClass} = YIdeal`, then calls `XYIdeal_mul_XYIdeal`.
- **Hypotheses**: `[DecidableEq F]`, `hxy : ¬(SP.x = SQ.x ∧ SP.y = negY SQ.x SQ.y)`.
- **Uses from project**: `maximalIdealAt`
- **Used by**: `span_XClass_addSmoothPoint_mul_eq`
- **Visibility**: public
- **Lines**: 674–710, proof ~37 lines
- **Notes**: Proof > 30 lines.

---

### `noncomputable def addSmoothPoint`
- **Type**: `C.SmoothPoint → C.SmoothPoint → (non-deg hyp) → C.SmoothPoint`; adds two smooth points using the Weierstrass addition formulae.
- **What**: Constructs the smooth point `SP + SQ` with coordinates `(addX, addY)` and verifies nonsingularity via `nonsingular_add`.
- **How**: Direct construction, `nonsingular` field from `WeierstrassCurve.Affine.nonsingular_add`.
- **Hypotheses**: `[DecidableEq F]`, `hxy` (non-degenerate).
- **Uses from project**: none (wraps mathlib's nonsingular_add)
- **Used by**: `addSmoothPoint_x`, `addSmoothPoint_y`, `span_XClass_addSmoothPoint_mul_eq`, `count_YClass_linePolynomial_eq`, `divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp`, `divisorOf_coordY_sub_algMap_linePolynomial`, `projectiveDivisorOf_coordY_sub_algMap_linePolynomial`, `miller_at_addSmoothPoint_principal`, `WeierstrassCurve.Affine.Point.add_some_some_toProjectiveSmoothPoint`, `projectiveDivisorSum_chord_line`
- **Visibility**: public
- **Lines**: 716–724

---

### `@[simp] theorem addSmoothPoint_x`
- **Type**: `(C.addSmoothPoint SP SQ hxy).x = C.toAffine.addX SP.x SQ.x (slope SP.x SQ.x SP.y SQ.y)`
- **What**: x-coordinate of the sum smooth point.
- **How**: `rfl`.
- **Uses from project**: `addSmoothPoint`
- **Used by**: `span_XClass_addSmoothPoint_mul_eq`
- **Visibility**: public
- **Lines**: 726–730

---

### `@[simp] theorem addSmoothPoint_y`
- **Type**: `(C.addSmoothPoint SP SQ hxy).y = C.toAffine.addY SP.x SQ.x SP.y (slope ...)`
- **What**: y-coordinate of the sum smooth point.
- **How**: `rfl`.
- **Uses from project**: `addSmoothPoint`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 732–736

---

### `theorem span_XClass_addSmoothPoint_mul_eq`
- **Type**: `span{XClass(addSmoothPoint).x} * (maximalIdealAt SP * maximalIdealAt SQ) = span{YClass(linePoly)} * maximalIdealAt(addSmoothPoint)`
- **What**: Same structural ideal identity as `span_XClass_mul_maximalIdealAt_mul_eq` but stated in smooth-point terms (SmoothPoint SR replaces raw coordinates).
- **How**: Unfolds `maximalIdealAt(addSmoothPoint)` to `XYIdeal`, then applies `span_XClass_mul_maximalIdealAt_mul_eq`.
- **Hypotheses**: `[DecidableEq F]`, `hxy`.
- **Uses from project**: `span_XClass_mul_maximalIdealAt_mul_eq`, `addSmoothPoint`, `maximalIdealAt`
- **Used by**: `count_YClass_linePolynomial_eq`
- **Visibility**: public
- **Lines**: 742–761

---

### `theorem divisorOf_coordY_sub_algMap_linePolynomial_apply`
- **Type**: Under `[IsIntegrallyClosed C.CoordinateRing]`, `C.divisorOf (C.coordY − algMap linePoly) Q' = count(maximalIdealAt Q', span{YClass linePoly})`
- **What**: Gives the coefficient of Q' in the affine divisor of the chord line as the Dedekind count at the YClass ideal.
- **How**: Uses `coordY_sub_algMap_linePolynomial_eq_algMap_YClass` and `divisorOf_algebraMap_apply_eq_count`.
- **Hypotheses**: `IsIntegrallyClosed C.CoordinateRing`, `[DecidableEq F]`.
- **Uses from project**: `coordY_sub_algMap_linePolynomial_eq_algMap_YClass`, `divisorOf_algebraMap_apply_eq_count`
- **Used by**: `divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp`
- **Visibility**: public
- **Lines**: 768–782

---

### `theorem count_YClass_linePolynomial_eq`
- **Type**: Under `[IsAlgClosed F] [NeZero 2] [NeZero 3] [IsElliptic] [IsIntegrallyClosed C.CoordinateRing]`, a ℤ equality: `count(YClass linePoly, Q') + count(M_SR, Q') = count(XClass SR.x, Q') + count(M_SP, Q') + count(M_SQ, Q')`
- **What**: The structural count equation at any Q': the chord YClass count plus the sum-point count equals the vertical XClass count plus the two input point counts. Follows from `span_XClass_addSmoothPoint_mul_eq` via `Associates.count_mul`.
- **How**: Reduces to ℕ via `push_cast`; lifts `span_XClass_addSmoothPoint_mul_eq` to Associates; applies `Associates.count_mul` twice on each side; then `linarith`.
- **Hypotheses**: `IsAlgClosed F`, `NeZero 2`, `NeZero 3`, `IsElliptic`, `IsIntegrallyClosed C.CoordinateRing`, `hxy`.
- **Uses from project**: `span_XClass_addSmoothPoint_mul_eq`, `addSmoothPoint`, `maximalIdealAt_isMaximal`, `maximalIdealAt_ne_bot`
- **Used by**: `divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp`
- **Visibility**: public
- **Lines**: 791–920, proof ~130 lines
- **Notes**: Proof > 30 lines (130 lines). Substantial boilerplate with repeated Associates / mk_mul_mk manipulations.

---

### `theorem count_maximalIdealAt_eq_single`
- **Type**: Under `[IsIntegrallyClosed C.CoordinateRing]`, `count(maximalIdealAt Q', maximalIdealAt X) : ℤ = (single X 1) Q'`
- **What**: The Dedekind count equals the Finsupp.single evaluation: 1 if X=Q', 0 otherwise.
- **How**: `by_cases h : X = Q'`; in the positive case applies `count_maximalIdealAt_self`; in the negative case `count_maximalIdealAt_eq_zero_of_ne`.
- **Hypotheses**: `IsIntegrallyClosed C.CoordinateRing`.
- **Uses from project**: `count_maximalIdealAt_self`, `count_maximalIdealAt_eq_zero_of_ne`
- **Used by**: `divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp`
- **Visibility**: public
- **Lines**: 925–936

---

### `theorem divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp`
- **Type**: Under full hypotheses, `C.divisorOf (C.coordY − algMap linePoly) Q' = (single SP 1 + single SQ 1 + single SR.neg 1) Q'`
- **What**: Pointwise chord-line divisor identity: the affine divisor of `Y − ℓ(X)` at Q' equals the sum of Dirac masses at SP, SQ, and the negation of the sum-point SR.
- **How**: Uses `divisorOf_coordY_sub_algMap_linePolynomial_apply`, then `count_YClass_linePolynomial_eq` to expand the count; substitutes `count(XClass SR.x)` via `divisorOf_coordX_sub_const_apply_eq_finsupp`; substitutes each maximalIdealAt count via `count_maximalIdealAt_eq_single`; finishes with `linarith`.
- **Hypotheses**: Full hypothesis cone (IsAlgClosed, NeZero 2/3, IsElliptic, IsIntegrallyClosed).
- **Uses from project**: `divisorOf_coordY_sub_algMap_linePolynomial_apply`, `count_YClass_linePolynomial_eq`, `divisorOf_coordX_sub_const_apply_eq_finsupp`, `count_maximalIdealAt_eq_single`, `addSmoothPoint`
- **Used by**: `divisorOf_coordY_sub_algMap_linePolynomial`
- **Visibility**: public
- **Lines**: 943–981, proof ~39 lines
- **Notes**: Proof > 30 lines.

---

### `theorem divisorOf_coordY_sub_algMap_linePolynomial`
- **Type**: Under full hypotheses, `C.divisorOf (C.coordY − algMap linePoly) = single SP 1 + single SQ 1 + single SR.neg 1`
- **What**: Global Finsupp identity for the affine divisor of the chord line.
- **How**: `Finsupp.ext` from `divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp`.
- **Hypotheses**: Full cone.
- **Uses from project**: `divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp`
- **Used by**: `projectiveDivisorOf_coordY_sub_algMap_linePolynomial`, `projectiveDivisorSum_chord_line`
- **Visibility**: public
- **Lines**: 987–999

---

### `theorem projectiveDivisorOf_coordY_sub_algMap_linePolynomial`
- **Type**: Under full hypotheses, `C.projectiveDivisorOf (C.coordY − algMap linePoly) = single (affine SP) 1 + single (affine SQ) 1 + single (affine SR.neg) 1 − 3·single ∞ 1`
- **What**: Full projective divisor of the chord/tangent line: three affine points minus a triple pole at ∞.
- **How**: Unfolds `projectiveDivisorOf`; applies `divisorOf_coordY_sub_algMap_linePolynomial` and `ordAtInfty_coordY_sub_algMap_linePolynomial`; lifts each Finsupp.single through `Divisor.toProjective` via `Finsupp.mapDomain_single`; finishes with `abel`.
- **Hypotheses**: Full cone.
- **Uses from project**: `divisorOf_coordY_sub_algMap_linePolynomial`, `ordAtInfty_coordY_sub_algMap_linePolynomial`, `Divisor.toProjective_add`
- **Used by**: `miller_at_addSmoothPoint_principal`, `projectiveDivisorSum_chord_line`
- **Visibility**: public
- **Lines**: 1003–1052, proof ~50 lines
- **Notes**: Proof > 30 lines.

---

### `theorem miller_at_addSmoothPoint_principal`
- **Type**: Under full hypotheses and `hxy`, `ProjIsPrincipal C ((affine SP) + (affine SQ) − (affine SR) − (∞))` where `SR = addSmoothPoint SP SQ hxy`
- **What**: The Miller divisor at non-degenerate `(SP, SQ)` is principal, witnessed by `f/g` where `f = coordY − linePoly` and `g = coordX − SR.x`.
- **How**: Sets `f` and `g`; constructs the witness `f * g⁻¹`; rewrites the projective divisor of the quotient using `projectiveDivisorOf_mul`, `projectiveDivisorOf_inv`, and the known divisors of `f` and `g`; the resulting Finsupp identity follows from `ring` pointwise.
- **Hypotheses**: Full cone, `hxy`.
- **Uses from project**: `coordY_sub_algMap_linePolynomial_ne_zero`, `coordX_sub_const_ne_zero`, `projectiveDivisorOf_coordY_sub_algMap_linePolynomial`, `projectiveDivisorOf_coordX_sub_const`, `projectiveDivisorOf_mul`, `projectiveDivisorOf_inv`, `addSmoothPoint`
- **Used by**: `miller_at_some_some_nondegen`
- **Visibility**: public
- **Lines**: 1058–1104, proof ~47 lines
- **Notes**: Proof > 30 lines. Central geometric construction.

---

## Namespace `HasseWeil.Curves` — Miller at `(P, −P)` for concrete Points

### `theorem WeierstrassCurve.Affine.Point.neg_some_toProjectiveSmoothPoint`
- **Type**: `(−(Point.some x y h)).toProjectiveSmoothPoint = ProjectiveSmoothPoint.affine (⟨x, y, h⟩ : C.SmoothPoint).neg`
- **What**: The projective smooth point of a negated `.some` point equals the affine projective point of the smooth-point negation.
- **How**: `rfl` (definitional).
- **Hypotheses**: `W.Nonsingular x y` (omits IsElliptic and DecidableEq).
- **Uses from project**: `SmoothPoint.neg`
- **Used by**: `miller_at_neg_of_some`
- **Visibility**: public (`_root_` qualified)
- **Lines**: 1118–1123

---

### `theorem miller_at_neg_of_some`
- **Type**: Under `[IsAlgClosed F] [NeZero 2] [NeZero 3] [IsIntegrallyClosed]` and `W.Nonsingular x y`, `ProjIsPrincipal (⟨W⟩) ((Point.some x y).toProj + (−Point.some x y).toProj − (P+(−P)).toProj − ∞)`
- **What**: Miller at `(P, −P)` for a concrete `.some` point: principal via vertical-line.
- **How**: Applies `miller_of_neg_of_vertical_principal`; identifies projective forms; applies `vertical_line_principal`.
- **Hypotheses**: `IsAlgClosed F`, `NeZero 2/3`, `IsIntegrallyClosed`.
- **Uses from project**: `miller_of_neg_of_vertical_principal`, `WeierstrassCurve.Affine.Point.neg_some_toProjectiveSmoothPoint`, `vertical_line_principal`
- **Used by**: `miller_hypothesis_holds` (indirectly via `miller_at_some_some_degen`)
- **Visibility**: public
- **Lines**: 1128–1152, proof ~25 lines

---

### `theorem WeierstrassCurve.Affine.Point.add_some_some_toProjectiveSmoothPoint`
- **Type**: `(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂).toProjectiveSmoothPoint = affine (C.addSmoothPoint ⟨x₁,y₁,h₁⟩ ⟨x₂,y₂,h₂⟩ hxy)`
- **What**: The projective form of the sum of two `.some` points equals the affine projective form of `addSmoothPoint`. Bridge between the Point-level addition and the SmoothPoint-level `addSmoothPoint`.
- **How**: `rw [WeierstrassCurve.Affine.Point.add_some hxy]; rfl`.
- **Hypotheses**: `hxy` (non-degenerate).
- **Uses from project**: `addSmoothPoint`
- **Used by**: `miller_at_some_some_nondegen`
- **Visibility**: public (`_root_` qualified)
- **Lines**: 1159–1169

---

### `theorem miller_at_some_some_nondegen`
- **Type**: Under full cone and `hxy`, `ProjIsPrincipal (⟨W⟩) ((Point.some x₁ y₁ h₁).toProj + (Point.some x₂ y₂ h₂).toProj − (P+Q).toProj − ∞)`
- **What**: Miller at non-degenerate `(some x₁ y₁, some x₂ y₂)`: principal via the chord-line witness.
- **How**: Rewrites the projective forms via `add_some_some_toProjectiveSmoothPoint`; then applies `miller_at_addSmoothPoint_principal`.
- **Hypotheses**: Full cone, `hxy`.
- **Uses from project**: `WeierstrassCurve.Affine.Point.add_some_some_toProjectiveSmoothPoint`, `miller_at_addSmoothPoint_principal`
- **Used by**: `miller_hypothesis_holds`
- **Visibility**: public
- **Lines**: 1175–1199, proof ~24 lines

---

### `theorem miller_at_some_some_degen`
- **Type**: Under full cone and `hxy : x₁=x₂ ∧ y₁=W.negY x₂ y₂`, `ProjIsPrincipal (⟨W⟩) ((Point.some x₁ y₁).toProj + (Point.some x₂ y₂).toProj − (P+Q).toProj − ∞)`
- **What**: Miller at degenerate `(some, some)` case where `P+Q=0`: principal via vertical-line.
- **How**: Rewrites `P+Q=0` (via `add_of_Y_eq`), identifies `Q.toProj = affine(SP.neg)`, rewrites projective forms, then uses `vertical_line_principal`; closes the Finsupp equality via `convert h_vert` + `abel`.
- **Hypotheses**: Full cone, `hxy` (degenerate: Q = −P).
- **Uses from project**: `vertical_line_principal`, `SmoothPoint.neg`, `SmoothPoint.ext`
- **Used by**: `miller_hypothesis_holds`
- **Visibility**: public
- **Lines**: 1204–1258, proof ~55 lines
- **Notes**: Proof > 30 lines.

---

### `theorem miller_hypothesis_holds`
- **Type**: Under full cone, `MillerHypothesis W`
- **What**: The Miller relation holds unconditionally for all P, Q: by cases on whether P, Q are zero or `.some`, dispatching to the four lemmas.
- **How**: `cases P, cases Q`, then `by_cases hxy`; dispatches to `miller_of_zero_left`, `miller_of_zero_right`, `miller_at_some_some_degen`, `miller_at_some_some_nondegen`.
- **Hypotheses**: Full cone.
- **Uses from project**: `miller_of_zero_left`, `miller_of_zero_right`, `miller_at_some_some_degen`, `miller_at_some_some_nondegen`
- **Used by**: `general_kappa_reduce`, `afInputs_unconditional`, `AddHomProperty_of_pushforward_principal`
- **Visibility**: public
- **Lines**: 1271–1292, proof ~22 lines

---

### `theorem general_kappa_reduce`
- **Type**: Under full cone, for any `D : ProjectiveDivisor C`, `D ~ kappaDivisor W (projectiveDivisorSum W D) + (deg D) • single ∞ 1`
- **What**: Every projective divisor is linearly equivalent to a kappa-divisor shifted by `deg(D)·∞`. Proved by Finsupp induction.
- **How**: Induction on `D` using `Finsupp.induction`: base is trivial; step uses `single_minus_inf_eq_kappaDivisor`, `kappaDivisor_zsmul_linEquiv_of_miller`, `kappaDivisor_add_linEquiv_of_miller` (with `miller_hypothesis_holds` passed as `h_miller`), and `projPrincipalSubgroup.neg_mem` + `.add_mem`.
- **Hypotheses**: Full cone.
- **Uses from project**: `miller_hypothesis_holds`, `projectiveDivisorSum_zero`, `projectiveDivisorSum_add`, `projectiveDivisorSum_single`, `kappaDivisor_zero`, `kappaDivisor_add_linEquiv_of_miller`, `kappaDivisor_zsmul_linEquiv_of_miller`, `single_minus_inf_eq_kappaDivisor`, `ProjectiveDivisor.degree_zero`, `ProjectiveDivisor.degree_add`
- **Used by**: `divZeroReduce_holds`
- **Visibility**: public
- **Lines**: 1306–1460, proof ~155 lines
- **Notes**: Proof > 30 lines (155 lines). Core inductive proof of the universal kappa-reduction.

---

### `theorem divZeroReduce_holds`
- **Type**: Under full cone, `DivZeroReduce W`
- **What**: Every degree-zero divisor is linearly equivalent to `kappaDivisor W (σ D)`. Corollary of `general_kappa_reduce` when `deg D = 0`.
- **How**: Calls `general_kappa_reduce`; the `deg D · ∞` term vanishes since `deg D = 0`.
- **Hypotheses**: Full cone.
- **Uses from project**: `general_kappa_reduce`, `ProjectiveDivisor.mem_degZero`
- **Used by**: `afInputs_unconditional`, `AddHomProperty_of_pushforward_principal`, `exists_kappa_form`
- **Visibility**: public
- **Lines**: 1466–1477

---

### `noncomputable def afInputs_unconditional`
- **Type**: Under `[IsAlgClosed F] [NeZero 2] [NeZero 3] [IsDedekindDomain C.CoordinateRing] [IsIntegrallyClosed C.CoordinateRing]`, `AFInputs W`
- **What**: Bundles Miller + DivZeroReduce + NoFinitePolesBridge into the `AFInputs` record unconditionally.
- **How**: Fills the three fields with `miller_hypothesis_holds`, `divZeroReduce_holds`, `noFinitePolesBridge_unconditional`.
- **Hypotheses**: Full cone plus IsDedekindDomain.
- **Uses from project**: `miller_hypothesis_holds`, `divZeroReduce_holds`, `noFinitePolesBridge_unconditional`
- **Used by**: `picZeroIsoE`, `projectiveDivisorSum_eq_zero_of_principal`
- **Visibility**: public
- **Lines**: 1491–1498

---

### `noncomputable def picZeroIsoE`
- **Type**: Under full cone plus IsDedekindDomain + IsIntegrallyClosed, `PicProj₀ (⟨W⟩ : SmoothPlaneCurve F) ≃+ W.Point`
- **What**: The canonical Pic⁰(E) ≅ E isomorphism (Silverman III.3.4), constructed unconditionally by discharging `picZeroIsoE_of_AFInputs` against `afInputs_unconditional`.
- **How**: One-liner: `picZeroIsoE_of_AFInputs (afInputs_unconditional W)`.
- **Hypotheses**: Full cone plus IsDedekindDomain + IsIntegrallyClosed.
- **Uses from project**: `afInputs_unconditional`, `picZeroIsoE_of_AFInputs`
- **Used by**: `picZeroIsoE_baseChange`, `picZeroIsoE_symm_apply`, `picZeroIsoE_picZeroOfPoint`, `picZeroOfPoint_sigmaBar`, `picZeroOfPoint_injective`, `picZeroEquiv`, `picZeroPushforward`, `picZeroPullback`, `dualViaPicZero`, `dualViaPicZero_comp_property`, various Isogeny wrappers
- **Visibility**: public
- **Lines**: 1508–1513
- **Notes**: keyApi — used by 10+ other declarations in this file.

---

### `noncomputable def picZeroIsoE_baseChange`
- **Type**: Under full cone on `L` (algebraically closed), `PicProj₀ (⟨W.baseChange L⟩) ≃+ (W.baseChange L).Point`
- **What**: Applies `picZeroIsoE` to the base change of `W` to an algebraically closed field `L`.
- **How**: `picZeroIsoE (W.baseChange L)`.
- **Hypotheses**: `[Field L] [Algebra F L] [IsAlgClosed L] [NeZero 2] [NeZero 3] [(W.baseChange L).IsElliptic] [IsDedekindDomain] [IsIntegrallyClosed]`.
- **Uses from project**: `picZeroIsoE`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1520–1528

---

### `@[simp] theorem picZeroIsoE_symm_apply`
- **Type**: `(picZeroIsoE W).symm P = picZeroOfPoint W P`
- **What**: The inverse of the Pic⁰ isomorphism is the κ map.
- **How**: `rfl`.
- **Hypotheses**: Full cone.
- **Uses from project**: `picZeroIsoE`
- **Used by**: `picZeroIsoE_picZeroOfPoint`, `picZeroOfPoint_sigmaBar`, `picZeroOfPoint_injective`, `picZeroPushforward_picZeroOfPoint`, `dualViaPicZero_comp_property`
- **Visibility**: public
- **Lines**: 1533–1538

---

### `@[simp] theorem picZeroIsoE_picZeroOfPoint`
- **Type**: `picZeroIsoE W (picZeroOfPoint W P) = P`
- **What**: The forward direction of the Pic⁰ isomorphism inverts the κ map.
- **How**: `rw [← picZeroIsoE_symm_apply, (picZeroIsoE W).apply_symm_apply]`.
- **Hypotheses**: Full cone.
- **Uses from project**: `picZeroIsoE`, `picZeroIsoE_symm_apply`
- **Used by**: `sigmaBar_picZeroOfPoint`
- **Visibility**: public
- **Lines**: 1542–1548

---

### `theorem projectiveDivisorSum_eq_zero_of_principal`
- **Type**: Under full cone, if `D ∈ projPrincipalSubgroup`, then `projectiveDivisorSum W D = 0`
- **What**: The σ map vanishes on principal divisors.
- **How**: Applies `(afInputs_unconditional W).h_van` with `principal_mem_degZero`.
- **Hypotheses**: Full cone, `D` principal.
- **Uses from project**: `afInputs_unconditional`, `SmoothPlaneCurve.principal_mem_degZero`
- **Used by**: `projectiveDivisorSum_chord_line`, `projectiveDivisorSum_vertical_line_of_principal`
- **Visibility**: public
- **Lines**: 1561–1571

---

### `theorem sigmaBar_picZeroOfPoint`
- **Type**: `picZeroIsoE W (picZeroOfPoint W P) = P` (alias)
- **What**: Right inverse: σ̄ ∘ κ = id at the Pic⁰ level.
- **How**: `picZeroIsoE_picZeroOfPoint W P`.
- **Uses from project**: `picZeroIsoE_picZeroOfPoint`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1576–1582

---

### `theorem picZeroOfPoint_sigmaBar`
- **Type**: `picZeroOfPoint W (picZeroIsoE W D) = D`
- **What**: Left inverse: κ ∘ σ̄ = id at the Pic⁰ level.
- **How**: `rw [← picZeroIsoE_symm_apply, (picZeroIsoE W).symm_apply_apply]`.
- **Uses from project**: `picZeroIsoE`, `picZeroIsoE_symm_apply`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1587–1593

---

### `theorem exists_kappa_form`
- **Type**: Under cone (no IsDedekindDomain needed), for `D : ProjectiveDivisor.degZero C`, `∃ P, D.val ~ kappaDivisor W P`
- **What**: Every degree-zero divisor class is represented by some `(P) − (O)`.
- **How**: Witness: `projectiveDivisorSum W D.val`; uses `divZeroReduce_holds W D`.
- **Uses from project**: `divZeroReduce_holds`, `projectiveDivisorSum`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1602–1609

---

### `theorem picZeroOfPoint_injective`
- **Type**: Under full cone, `Function.Injective (picZeroOfPoint W)`
- **What**: The κ map is injective.
- **How**: Uses `picZeroIsoE_symm_apply` to identify `picZeroOfPoint = (picZeroIsoE W).symm`, which is injective as an equiv.
- **Uses from project**: `picZeroIsoE`, `picZeroIsoE_symm_apply`
- **Used by**: `kappaDivisor_inj`
- **Visibility**: public
- **Lines**: 1614–1624

---

### `noncomputable abbrev picZeroEquiv`
- **Type**: `PicProj₀ (⟨W⟩) ≃+ W.Point` (alias for `picZeroIsoE W`)
- **What**: Naming-convention alias for `picZeroIsoE`.
- **Uses from project**: `picZeroIsoE`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1629–1634

---

### `theorem AddHomProperty_of_pushforward_principal`
- **Type**: Under full cone on both W₁, W₂, if `φ : Isogeny W₁ W₂` has `CoordHom cd` and `h_pres` (pushforward-principal hypothesis), then `φ.AddHomProperty cd`
- **What**: Reduces the additive-hom property of an isogeny to just the pushforward-principal hypothesis, since Miller/DivZeroReduce now discharge unconditionally.
- **How**: Calls `AddHomProperty_of_miller_divZeroReduce` with `miller_hypothesis_holds` and `divZeroReduce_holds` for both curves.
- **Uses from project**: `miller_hypothesis_holds`, `divZeroReduce_holds`, `AddHomProperty_of_miller_divZeroReduce`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1647–1665

---

### `theorem kappaDivisor_inj`
- **Type**: Under full cone, if `kappaDivisor W P ~ kappaDivisor W Q` then `P = Q`
- **What**: Injectivity of the κ divisor map: if `(P)−(O) ∼ (Q)−(O)` then `P = Q`.
- **How**: Lifts the linear equivalence to equality in Pic⁰ via `Quot.sound` + `QuotientAddGroup.leftRel_apply`; applies `projPrincipalSubgroup.neg_mem`; concludes with `picZeroOfPoint_injective`.
- **Uses from project**: `picZeroOfPoint_injective`, `picZeroOfPoint`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1672–1698, proof ~27 lines

---

## Namespace `HasseWeil.Isogeny` — §5 wrappers

### `noncomputable def picZeroPushforward`
- **Type**: `HasseWeil.Isogeny W W → PicProj₀ C →+ PicProj₀ C`
- **What**: Instantiates `isogPicPushforward` at the canonical `picZeroIsoE`.
- **Uses from project**: `HasseWeil.Curves.picZeroIsoE`, `isogPicPushforward`
- **Used by**: `picZeroPushforward_picZeroOfPoint`, `picZeroPullback_comp_pushforward`, `dualViaPicZero`, `dualViaPicZero_comp_property`, `frobeniusPicPushforward_charP_prime`, `frobeniusPicPushforward_charP_pow`
- **Visibility**: public
- **Lines**: 1722–1727

---

### `noncomputable def picZeroPullback`
- **Type**: `(α_dual : HasseWeil.Isogeny W W) → PicProj₀ C →+ PicProj₀ C`
- **What**: Instantiates `isogPicPullback` at the canonical `picZeroIsoE`.
- **Uses from project**: `HasseWeil.Curves.picZeroIsoE`, `isogPicPullback`
- **Used by**: `picZeroPullback_comp_pushforward`, `dualViaPicZero`, `dualViaPicZero_comp_property`, `verschiebungPicPullback_charP_prime`, `verschiebungPicPullback_charP_pow`
- **Visibility**: public
- **Lines**: 1732–1737

---

### `theorem picZeroPushforward_picZeroOfPoint`
- **Type**: `picZeroPushforward α (picZeroOfPoint W P) = picZeroOfPoint W (α.toAddMonoidHom P)`
- **What**: Pushforward compat: the iso-conjugate pushforward commutes with the κ map.
- **How**: `isogPicPushforward_compat` + rewrites via `picZeroIsoE_symm_apply`.
- **Uses from project**: `picZeroPushforward`, `picZeroIsoE_symm_apply`, `isogPicPushforward_compat`
- **Used by**: `dualViaPicZero_comp_property`, `frobeniusPicPushforward_charP_prime_picZeroOfPoint`, `frobeniusPicPushforward_charP_pow_picZeroOfPoint`
- **Visibility**: public
- **Lines**: 1742–1750

---

### `theorem picZeroPullback_comp_pushforward`
- **Type**: `(picZeroPullback α_dual).comp (picZeroPushforward α) = (AddMonoidHom.id _).comp (α.degree • AddMonoidHom.id _)`
- **What**: Verschiebung ∘ Frobenius = [deg] on Pic⁰, given the point-level dual identity.
- **How**: `isogPicPullback_comp_pushforward` at the canonical iso.
- **Uses from project**: `picZeroPushforward`, `picZeroPullback`, `isogPicPullback_comp_pushforward`, `picZeroIsoE`
- **Used by**: `verschiebungPicPullback_comp_frobeniusPicPushforward`, `verschiebungPicPullback_comp_frobeniusPicPushforward_charP_pow`
- **Visibility**: public
- **Lines**: 1756–1763

---

### `noncomputable def dualViaPicZero`
- **Type**: `(α α_dual : HasseWeil.Isogeny W W) → HasseWeil.Isogeny W W`
- **What**: Constructs the Silverman III.6.1(b) dual isogeny via the canonical Pic⁰ iso: `α̂ = κ ∘ α_pullback ∘ κ.symm`.
- **How**: `dualOfPicZeroPullback` at the canonical `picZeroIsoE`.
- **Uses from project**: `dualOfPicZeroPullback`, `picZeroIsoE`, `picZeroPushforward`, `picZeroPullback`
- **Used by**: `dualViaPicZero_comp_property`, `frobeniusDualViaPicZero_charP_prime`, `frobeniusDualViaPicZero_charP_pow`
- **Visibility**: public
- **Lines**: 1771–1775

---

### `theorem dualViaPicZero_comp_property`
- **Type**: Given `h_dual : α_dual ∘ α = [deg α]` at the point level, `(dualViaPicZero α α_dual).toAddMonoidHom (α.toAddMonoidHom P) = (α.degree : ℤ) • P`
- **What**: The Pic⁰-constructed dual satisfies the dual functional equation.
- **How**: `h_dual_comp_from_picZeroPullback_witness` at the canonical iso; supplies `picZeroPushforward_picZeroOfPoint` and `picZeroPullback_comp_pushforward`.
- **Uses from project**: `dualViaPicZero`, `picZeroIsoE`, `picZeroPushforward`, `picZeroPullback`, `picZeroPushforward_picZeroOfPoint`, `picZeroPullback_comp_pushforward`, `picZeroIsoE_symm_apply`, `h_dual_comp_from_picZeroPullback_witness`
- **Used by**: `frobeniusDualViaPicZero_charP_prime_comp_property`, `frobeniusDualViaPicZero_charP_pow_comp_property`
- **Visibility**: public
- **Lines**: 1782–1795

---

### `noncomputable def frobeniusPicPushforward_charP_prime`
- **Type**: Pic⁰ →+ Pic⁰ for E over `F_p` base-changed to algebraically closed L.
- **What**: Instantiates `picZeroPushforward` at `frobeniusIsog_baseChange_charP_prime`.
- **Uses from project**: `picZeroPushforward`, `frobeniusIsog_baseChange_charP_prime`
- **Used by**: `verschiebungPicPullback_comp_frobeniusPicPushforward`, `frobeniusPicPushforward_charP_prime_picZeroOfPoint`
- **Visibility**: public
- **Lines**: 1808–1825

---

### `theorem frobeniusPicPushforward_charP_prime_picZeroOfPoint`
- **Type**: `frobeniusPicPushforward_charP_prime ... (picZeroOfPoint W P) = picZeroOfPoint W (frobenius.toAddMonoidHom P)`
- **What**: Pushforward compat for Frobenius on Pic⁰ (F_p case).
- **How**: `picZeroPushforward_picZeroOfPoint`.
- **Uses from project**: `frobeniusPicPushforward_charP_prime`, `picZeroPushforward_picZeroOfPoint`, `frobeniusIsog_baseChange_charP_prime`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1831–1850

---

### `noncomputable def verschiebungPicPullback_charP_prime`
- **Type**: Pic⁰ →+ Pic⁰ for E over `F_p` base-changed to L, witness-parametric on dual.
- **What**: Instantiates `picZeroPullback` at the given `α_dual` (Verschiebung candidate).
- **Uses from project**: `picZeroPullback`
- **Used by**: `verschiebungPicPullback_comp_frobeniusPicPushforward`
- **Visibility**: public
- **Lines**: 1857–1875

---

### `theorem verschiebungPicPullback_comp_frobeniusPicPushforward`
- **Type**: Given `h_dual`, `(verschiebungPicPullback α_dual).comp (frobeniusPicPushforward) = [deg frobenius] • id`
- **What**: Verschiebung ∘ Frobenius = [deg] on Pic⁰ (F_p case).
- **How**: `picZeroPullback_comp_pushforward`.
- **Uses from project**: `verschiebungPicPullback_charP_prime`, `frobeniusPicPushforward_charP_prime`, `picZeroPullback_comp_pushforward`, `frobeniusIsog_baseChange_charP_prime`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1883–1908

---

### `noncomputable def frobeniusDualViaPicZero_charP_prime`
- **Type**: `HasseWeil.Isogeny ... → HasseWeil.Isogeny ...` (dual of Frobenius, F_p case)
- **What**: Silverman III.6.1(b) dual of Frobenius for E over F_p.
- **How**: `dualViaPicZero` at Frobenius and `α_dual`.
- **Uses from project**: `dualViaPicZero`, `frobeniusIsog_baseChange_charP_prime`
- **Used by**: `frobeniusDualViaPicZero_charP_prime_comp_property`
- **Visibility**: public
- **Lines**: 1914–1931

---

### `theorem frobeniusDualViaPicZero_charP_prime_comp_property`
- **Type**: Given `h_dual`, `frobeniusDualViaPicZero.toAddMonoidHom (frobenius.toAddMonoidHom P) = (deg frobenius : ℤ) • P`
- **What**: Dual functional equation for the Pic⁰-constructed Frobenius dual (F_p case).
- **How**: `dualViaPicZero_comp_property`.
- **Uses from project**: `frobeniusDualViaPicZero_charP_prime`, `dualViaPicZero_comp_property`, `frobeniusIsog_baseChange_charP_prime`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1937–1960

---

### `noncomputable def frobeniusPicPushforward_charP_pow`
- **Type**: Pic⁰ →+ Pic⁰ for E over `F_{p^r}` base-changed to L.
- **What**: Instantiates `picZeroPushforward` at `frobeniusIsog_baseChange_charP_pow`.
- **Uses from project**: `picZeroPushforward`, `frobeniusIsog_baseChange_charP_pow`
- **Used by**: `frobeniusPicPushforward_charP_pow_picZeroOfPoint`, `verschiebungPicPullback_comp_frobeniusPicPushforward_charP_pow`
- **Visibility**: public
- **Lines**: 1971–1988

---

### `theorem frobeniusPicPushforward_charP_pow_picZeroOfPoint`
- **Type**: `frobeniusPicPushforward_charP_pow ... (picZeroOfPoint W P) = picZeroOfPoint W (frobenius.toAddMonoidHom P)` (F_{p^r} case)
- **How**: `picZeroPushforward_picZeroOfPoint`.
- **Uses from project**: `frobeniusPicPushforward_charP_pow`, `picZeroPushforward_picZeroOfPoint`, `frobeniusIsog_baseChange_charP_pow`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1993–2012

---

### `noncomputable def verschiebungPicPullback_charP_pow`
- **Type**: Pic⁰ →+ Pic⁰ for E over `F_{p^r}` base-changed to L, witness-parametric on dual.
- **Uses from project**: `picZeroPullback`
- **Used by**: `verschiebungPicPullback_comp_frobeniusPicPushforward_charP_pow`
- **Visibility**: public
- **Lines**: 2016–2034

---

### `theorem verschiebungPicPullback_comp_frobeniusPicPushforward_charP_pow`
- **Type**: Verschiebung ∘ Frobenius = [deg] on Pic⁰ (F_{p^r} case).
- **How**: `picZeroPullback_comp_pushforward`.
- **Uses from project**: `verschiebungPicPullback_charP_pow`, `frobeniusPicPushforward_charP_pow`, `picZeroPullback_comp_pushforward`, `frobeniusIsog_baseChange_charP_pow`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 2039–2064

---

### `noncomputable def frobeniusDualViaPicZero_charP_pow`
- **Type**: Dual isogeny of Frobenius via Pic⁰ (F_{p^r} case).
- **How**: `dualViaPicZero` at Frobenius and `α_dual`.
- **Uses from project**: `dualViaPicZero`, `frobeniusIsog_baseChange_charP_pow`
- **Used by**: `frobeniusDualViaPicZero_charP_pow_comp_property`
- **Visibility**: public
- **Lines**: 2068–2085

---

### `theorem frobeniusDualViaPicZero_charP_pow_comp_property`
- **Type**: Dual functional equation for the Pic⁰-constructed Frobenius dual (F_{p^r} case).
- **How**: `dualViaPicZero_comp_property`.
- **Uses from project**: `frobeniusDualViaPicZero_charP_pow`, `dualViaPicZero_comp_property`, `frobeniusIsog_baseChange_charP_pow`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 2088–2111

---

## Namespace `HasseWeil.Curves.SmoothPlaneCurve` — explicit σ-vanishing corollaries

### `theorem projectiveDivisorSum_chord_line`
- **Type**: Under full cone, `projectiveDivisorSum C.toAffine ((affine SP) + (affine SQ) + (affine SR.neg) − 3·∞) = 0`
- **What**: σ vanishes on the chord-line divisor.
- **How**: Rewrites via `projectiveDivisorOf_coordY_sub_algMap_linePolynomial`; applies `projectiveDivisorSum_eq_zero_of_principal` using the chord-line principal witness.
- **Uses from project**: `projectiveDivisorOf_coordY_sub_algMap_linePolynomial`, `projectiveDivisorSum_eq_zero_of_principal`, `coordY_sub_algMap_linePolynomial_ne_zero`, `addSmoothPoint`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 2133–2147

---

### `theorem projectiveDivisorSum_vertical_line_of_principal`
- **Type**: Under full cone, `projectiveDivisorSum C.toAffine ((affine P) + (affine P.neg) − 2·∞) = 0`
- **What**: σ vanishes on the vertical-line divisor.
- **How**: `projectiveDivisorSum_eq_zero_of_principal` applied to `vertical_line_principal P`.
- **Uses from project**: `projectiveDivisorSum_eq_zero_of_principal`, `vertical_line_principal`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 2152–2162

---

### `theorem pointValuation_algebraMap_eq_intValuation`
- **Type**: Under `[IsDedekindDomain C.CoordinateRing] [IsIntegrallyClosed C.CoordinateRing]`, `C.pointValuation P (algebraMap C.CoordinateRing K(C) u) = (smoothPointToHeightOne C.toAffine P).intValuation u`
- **What**: The project's `pointValuation` matches mathlib's `intValuation` for the corresponding height-one prime (T-PIC-C-003a closure).
- **How**: Case splits on `u = 0`; for nonzero `u` uses `pointValuation_algebraMap_eq_exp_count` and `IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg`, verifying the two formulas agree.
- **Uses from project**: `pointValuation_algebraMap_eq_exp_count`, `smoothPointToHeightOne`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 2189–2198
