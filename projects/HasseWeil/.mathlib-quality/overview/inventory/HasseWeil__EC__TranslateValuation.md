# Inventory: ./HasseWeil/EC/TranslateValuation.lean

## File overview

2698 lines. Proves that the K-algebra automorphism `τ_k = translateAlgEquivOfPoint W k` (translation by a smooth affine point `k`) carries `localRingAt(P+k)` onto `localRingAt(P)` and intertwines the maximal ideals — in particular `pointValuation P ∘ τ_k = pointValuation (P+k)` as valuations on K(E). The proof proceeds in four numbered items: (1) generator-vanishing, (2) polynomial-induction lift to CoordinateRing, (3) maxIdeal compatibility, (4) ord-equality lifted to all of K(E). No sorries. No instances except the trivial `W_smooth_toAffine_isElliptic`. Final export: `isTranslateValuationCompatible_all`.

Imports: `HasseWeil.EC.TranslateLocalRing`, `HasseWeil.Curves.NormValuation`, `HasseWeil.Curves.IntegralClosure`, `HasseWeil.Ramification`.

---

### `theorem XClass_notMem_maximalIdealAt`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk : F) (h_x : P.x ≠ xk) → Affine.CoordinateRing.XClass W.toAffine xk ∉ (W_smooth W).maximalIdealAt P`
- **What**: For a smooth point P with P.x ≠ xk, the coordinate-ring class `X - xk` is not in the maximal ideal at P (i.e., it evaluates to a nonzero residue at P).
- **How**: Uses `ker_evalAt` to identify `maximalIdealAt P = ker(evalAt P)`, then `evalAt P (XClass xk) = P.x - xk ≠ 0` via `Polynomial.evalEval_*` simp lemmas.
- **Hypotheses**: Smooth elliptic curve W over a field F; P a smooth point; P.x ≠ xk.
- **Uses from project**: `W_smooth W`, `ker_evalAt` (SmoothPlaneCurve), `SmoothPlaneCurve.evalAt_mk`
- **Used by**: `pointValuation_x_gen_sub_const_eq_one_of_X_ne` (×2 indirect via `pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`)
- **Visibility**: public
- **Lines**: 66–92, proof ~26 lines
- **Notes**: Count 3 references.

---

### `theorem pointValuation_x_gen_sub_const_eq_one_of_X_ne`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk : F) (h_x : P.x ≠ xk) → (W_smooth W).pointValuation P (x_gen W - algebraMap F KE xk) = 1`
- **What**: For P.x ≠ xk, the function field element `x_gen − xk` has valuation exactly 1 at P (is a unit in the local ring at P).
- **How**: Rewrites via `x_gen_sub_const_eq_algebraMap_XClass`, shows ≤1 via `pointValuation_algebraMap_le_one`, then ¬<1 via `XClass_notMem_maximalIdealAt` + `pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`; concludes by `le_antisymm`.
- **Hypotheses**: P smooth, P.x ≠ xk.
- **Uses from project**: `x_gen_sub_const_eq_algebraMap_XClass`, `XClass_notMem_maximalIdealAt`, `SmoothPlaneCurve.pointValuation_algebraMap_le_one`, `SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`
- **Used by**: `pointValuation_x_gen_sub_const_inv_eq_one_of_X_ne`, `pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_X_ne`, `pointValuation_A_eq_one_of_doubling` (≥3 uses)
- **Visibility**: public
- **Lines**: 97–116, proof ~19 lines

---

### `theorem pointValuation_x_gen_sub_const_inv_eq_one_of_X_ne`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk : F) (h_x : P.x ≠ xk) → (W_smooth W).pointValuation P (x_gen W - algebraMap F KE xk)⁻¹ = 1`
- **What**: In the chord case P.x ≠ xk, the inverse `(x_gen − xk)⁻¹` also has valuation 1 at P.
- **How**: From `pointValuation_x_gen_sub_const_eq_one_of_X_ne` and `map_inv₀`.
- **Hypotheses**: P smooth, P.x ≠ xk.
- **Uses from project**: `x_gen_sub_const_ne_zero`, `pointValuation_x_gen_sub_const_eq_one_of_X_ne`
- **Used by**: `pointValuation_translateSlope_xy_le_one_of_X_ne`
- **Visibility**: public
- **Lines**: 122–130, proof ~8 lines

---

### `theorem pointValuation_translateSlope_xy_le_one_of_X_ne`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_x : P.x ≠ xk) → (W_smooth W).pointValuation P (translateSlope_xy W xk yk) ≤ 1`
- **What**: In the chord case, the translate slope (y_gen − yk)/(x_gen − xk) has valuation ≤ 1 at P.
- **How**: Unfolds `translateSlope_xy` to the chord form via `Affine.slope_of_X_ne`, then applies `pointValuation_algebraMap_le_one` for numerator and `pointValuation_x_gen_sub_const_inv_eq_one_of_X_ne` for the denominator inverse, combined with `pointValuation_mul_le_one`.
- **Hypotheses**: P smooth, P.x ≠ xk.
- **Uses from project**: `translateSlope_xy`, `x_gen_sub_const_ne_zero`, `y_gen_sub_const_eq_algebraMap_YClass`, `pointValuation_x_gen_sub_const_inv_eq_one_of_X_ne`, `pointValuation_mul_le_one`
- **Used by**: `pointValuation_chord_numerator_lt_one_of_X_ne`, `pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_X_ne`, `pointValuation_translateX_xy_sub_alg_addX_lt_one_of_X_ne`, `pointValuation_translateY_xy_sub_alg_addY_lt_one_of_X_ne` (≥4 uses)
- **Visibility**: public
- **Lines**: 136–154, proof ~18 lines

---

### `theorem pointValuation_chord_numerator_lt_one_of_X_ne`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_x : P.x ≠ xk) → (W_smooth W).pointValuation P ((y_gen W - alg yk) * alg(P.x - xk) - alg(P.y - yk) * (x_gen W - alg xk)) < 1`
- **What**: The numerator that controls slope evaluation in the chord case is strictly less than 1 in the valuation at P — this encodes "the slope evaluates correctly at P".
- **How**: Algebraic rearrangement by `ring`/`push_cast`, then ultra-strong triangle inequality for the two-term sum via `map_sub`, each term bounded using `pointValuation_algebraMap_F_le_one` (constant factor) and `YClass_mem_maximalIdealAt`/`XClass_mem_maximalIdealAt` (generator factors < 1), combined via `pointValuation_mul_lt_one_of_le_and_lt`.
- **Hypotheses**: P smooth, P.x ≠ xk.
- **Uses from project**: `y_gen_sub_const_eq_algebraMap_YClass`, `x_gen_sub_const_eq_algebraMap_XClass`, `YClass_mem_maximalIdealAt`, `XClass_mem_maximalIdealAt`, `pointValuation_mul_lt_one_of_le_and_lt`, `SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`
- **Used by**: `pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_X_ne`
- **Visibility**: public
- **Lines**: 161–221, proof ~60 lines
- **Notes**: Proof >30 lines.

---

### `theorem pointValuation_algebraMap_F_eq_one_of_ne_zero`
- **Type**: `(P : (W_smooth W).SmoothPoint) {c : F} (hc : c ≠ 0) → (W_smooth W).pointValuation P (algebraMap F KE c) = 1`
- **What**: A nonzero scalar from the base field has valuation exactly 1 at any smooth point (units of the DVR).
- **How**: Uses `ord_P_algebraMap_F_of_ne_zero` to get `ord_P = 0`, then unfolds `ord_P` and uses `WithZero.unzero`/`Multiplicative.toAdd` to read off `pV = 1`. The nonzero case is handled by case-split on `pV = 0`.
- **Hypotheses**: c ≠ 0 in F.
- **Uses from project**: `SmoothPlaneCurve.ord_P_algebraMap_F_of_ne_zero`, `SmoothPlaneCurve.pointValuation_eq_zero_iff`
- **Used by**: `pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_X_ne`, `pointValuation_A_eq_one_of_doubling`, `pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_doubling`, `pointValuation_translateAlgEquivOfPoint_algebraMap_eq_one_of_notMem`, `pointValuation_translateAlgEquivOfPoint_algebraMap_eq_one_of_notMem` (≥5 uses)
- **Visibility**: public
- **Lines**: 226–248, proof ~22 lines

---

### `theorem pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_X_ne`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_x : P.x ≠ xk) → (W_smooth W).pointValuation P (translateSlope_xy W xk yk - algebraMap F KE (W.toAffine.slope P.x xk P.y yk)) < 1`
- **What**: In the chord case, the difference between the K(E)-slope `translateSlope_xy` and the F-slope `W.slope P.x xk P.y yk` is in the maximal ideal at P (vanishes at P to first order).
- **How**: Clears denominators to reduce to the chord numerator (pV < 1 by `pointValuation_chord_numerator_lt_one_of_X_ne`), then computes the denominator has pV = 1 using `pointValuation_x_gen_sub_const_eq_one_of_X_ne` and `pointValuation_algebraMap_F_eq_one_of_ne_zero` via `Valuation.map_mul`; the quotient is therefore < 1.
- **Hypotheses**: P smooth, P.x ≠ xk.
- **Uses from project**: `x_gen_sub_const_ne_zero`, `translateSlope_xy`, `pointValuation_chord_numerator_lt_one_of_X_ne`, `pointValuation_x_gen_sub_const_eq_one_of_X_ne`, `pointValuation_algebraMap_F_eq_one_of_ne_zero`
- **Used by**: `pointValuation_translateX_xy_sub_alg_addX_lt_one_of_X_ne`, `pointValuation_translateY_xy_sub_alg_addY_lt_one_of_X_ne` (and indirectly more)
- **Visibility**: public
- **Lines**: 254–336, proof ~82 lines
- **Notes**: Proof >30 lines.

---

### `theorem pointValuation_translateX_xy_sub_alg_addX_lt_one_of_X_ne`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_x : P.x ≠ xk) → (W_smooth W).pointValuation P (translateX_xy W xk yk - algebraMap F KE (W.toAffine.addX P.x xk (W.toAffine.slope P.x xk P.y yk))) < 1`
- **What**: In the chord case, the difference between the K(E) addX formula and the F addX at the chord slope vanishes at P — the geometric content that `τ_k(x_gen)` evaluates to `(P+k).x` at P in the chord case.
- **How**: Algebraic factorization of the addX-difference as `(slope_K - alg slope_F)(slope_K + alg slope_F + a₁) - (x_gen - alg P.x)`, both terms pV < 1 (first uses `pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_X_ne` + `pointValuation_translateSlope_xy_le_one_of_X_ne`, second uses `XClass_mem_maximalIdealAt`); combined via strong triangle.
- **Hypotheses**: P smooth, P.x ≠ xk.
- **Uses from project**: `translateX_xy`, `Affine.map_addX`, `pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_X_ne`, `pointValuation_translateSlope_xy_le_one_of_X_ne`, `XClass_mem_maximalIdealAt`, `x_gen_sub_const_eq_algebraMap_XClass`, `pointValuation_mul_lt_one_of_le_and_lt`, `pointValuation_add_le_one`
- **Used by**: `pointValuation_translateY_xy_sub_alg_addY_lt_one_of_X_ne` (sub-goal), `isTranslateXY_evaluatesAt_some` (chord x branch)
- **Visibility**: public
- **Lines**: 344–435, proof ~91 lines
- **Notes**: Proof >30 lines.

---

### `theorem addY_eq_unfolded_neg_negAddY`
- **Type**: `{R : Type*} [CommRing R] (W' : WeierstrassCurve R) (x₁ x₂ y₁ ℓ : R) → W'.toAffine.addY x₁ x₂ y₁ ℓ = -(ℓ * (W'.toAffine.addX x₁ x₂ ℓ - x₁) + y₁) - W'.a₁ * W'.toAffine.addX x₁ x₂ ℓ - W'.a₃`
- **What**: Algebraic identity unfolding `addY` in terms of `addX`, `negY`, and `negAddY` — expresses the y-coordinate of the group law result in a form amenable to linear arithmetic.
- **How**: Unfolds `negY`, `negAddY` and closes by `ring`.
- **Hypotheses**: CommRing R.
- **Uses from project**: none (pure algebra identity on WeierstrassCurve)
- **Used by**: `pointValuation_translateY_xy_sub_alg_addY_lt_one_of_X_ne` (×2), `pointValuation_translateY_xy_sub_alg_addY_lt_one_of_doubling` (×2), `pointValuation_translateY_xy_le_one_of_isSome` (×1), `pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome` (via the above) — total ≥8 references
- **Visibility**: public
- **Lines**: 441–449, proof ~8 lines
- **Notes**: Most-used helper in this file.

---

### `theorem pointValuation_translateY_xy_sub_alg_addY_lt_one_of_X_ne`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_x : P.x ≠ xk) → (W_smooth W).pointValuation P (translateY_xy W xk yk - algebraMap F KE (W.toAffine.addY P.x xk P.y (W.toAffine.slope P.x xk P.y yk))) < 1`
- **What**: In the chord case, `τ_k(y_gen)` evaluates to `(P+k).y` at P — the y-coordinate evaluation counterpart of the x lemma.
- **How**: Unfolds `translateY_xy` via `addY_eq_unfolded_neg_negAddY` for both sides, `Affine.map_addY`/`map_addX`, then factors the difference into 4 terms (T1–T4) each pV < 1, assembled by iterated triangle inequality. T1 calls `pointValuation_translateX_xy_sub_alg_addX_lt_one_of_X_ne`; T2–T4 call previously established slope and generator bounds.
- **Hypotheses**: P smooth, P.x ≠ xk.
- **Uses from project**: `translateY_xy`, `addY_eq_unfolded_neg_negAddY`, `Affine.map_addY`, `Affine.map_addX`, `pointValuation_translateSlope_xy_le_one_of_X_ne`, `pointValuation_translateX_xy_sub_alg_addX_lt_one_of_X_ne`, `pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_X_ne`, `XClass_mem_maximalIdealAt`, `YClass_mem_maximalIdealAt`, `pointValuation_mul_lt_one_of_le_and_lt`
- **Used by**: `isTranslateXY_evaluatesAt_some` (chord y branch)
- **Visibility**: public
- **Lines**: 456–584, proof ~128 lines
- **Notes**: `set_option maxHeartbeats 1600000` — NO-COMMENT. Proof >30 lines.

---

### `theorem weierstrass_factorization`
- **Type**: `(xk yk : F) (h_eq : W.toAffine.Equation xk yk) → (y_gen W - alg yk) * A = (x_gen W - alg xk) * B` where A, B are explicit polynomial expressions in K(E)
- **What**: In K(E), the Weierstrass curve identity at the generic point and at (xk, yk) factor the difference `W(x_gen,y_gen) - W(xk,yk) = 0` into `(y_gen - yk)·A = (x_gen - xk)·B`. This is the key ingredient for tangent/doubling slope evaluation.
- **How**: Applies `generic_equation W` and the hypothesis `h_eq`, rewrites both via `Affine.equation_iff'`, then pushes `algebraMap` through with explicit `congrArg (algebraMap F KE) h_eq` and closes with `linear_combination h_gen - h_eq_alg`.
- **Hypotheses**: (xk, yk) on the Weierstrass curve W.
- **Uses from project**: `generic_equation`, `W_KE`, `x_gen`, `y_gen`
- **Used by**: `pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_doubling` (×2 via h_factor)
- **Visibility**: public
- **Lines**: 603–666, proof ~63 lines
- **Notes**: Proof >30 lines.

---

### `theorem pointValuation_A_eq_one_of_doubling`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_eq_x : P.x = xk) (h_eq_y : P.y = yk) (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) → (W_smooth W).pointValuation P (y_gen W + alg yk + (W_KE W).a₁ * x_gen W + (W_KE W).a₃) = 1`
- **What**: In the tangent/doubling case (P = (xk,yk), non-2-torsion), the factor A = y_gen + yk + a₁·x_gen + a₃ has valuation exactly 1 at P. A evaluates to `yk - negY xk yk ≠ 0` at P.
- **How**: Shows pV(A) ≤ 1 by bounding each monomial. Then shows pV(A - alg(yk - negY xk yk)) < 1 via the maximal ideal membership of generator differences; uses strong triangle `Valuation.map_add_eq_of_lt_right` to conclude pV(A) = 1.
- **Hypotheses**: P = (xk,yk) on W, yk ≠ negY xk yk.
- **Uses from project**: `pointValuation_y_gen_le_one`, `pointValuation_x_gen_le_one`, `YClass_mem_maximalIdealAt`, `XClass_mem_maximalIdealAt`, `y_gen_sub_const_eq_algebraMap_YClass`, `x_gen_sub_const_eq_algebraMap_XClass`, `pointValuation_mul_lt_one_of_le_and_lt`, `pointValuation_add_le_one`, `pointValuation_mul_le_one`, `pointValuation_algebraMap_F_eq_one_of_ne_zero`
- **Used by**: `pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_doubling`
- **Visibility**: public
- **Lines**: 678–783, proof ~105 lines
- **Notes**: Proof >30 lines.

---

### `theorem pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_doubling`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_eq_x : P.x = xk) (h_eq_y : P.y = yk) (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) → (W_smooth W).pointValuation P (translateSlope_xy W xk yk - algebraMap F KE (W.toAffine.slope P.x xk P.y yk)) < 1`
- **What**: In the tangent case, the K(E) slope `translateSlope_xy` and the F tangent slope differ by something in the maximal ideal at P — the tangent counterpart of the chord slope lemma.
- **How**: Uses `weierstrass_factorization` to write `translateSlope_xy * A_K = B_K`, so `translateSlope_xy - alg slope_F = (B_K - A_K * alg slope_F) / A_K`. Since `pV(A_K) = 1` (by `pointValuation_A_eq_one_of_doubling`) and `pV(B_K - A_K * alg slope_F) < 1` (via `h_B_minus_AS` factorization + x/y-gen vanishing), the quotient is < 1. Uses `translateSlope_xy_eq` and `field_simp`.
- **Hypotheses**: P = (xk,yk), non-2-torsion.
- **Uses from project**: `weierstrass_factorization`, `pointValuation_A_eq_one_of_doubling`, `translateSlope_xy_eq`, `x_gen_sub_const_ne_zero`, `XClass_mem_maximalIdealAt`, `YClass_mem_maximalIdealAt`, `pointValuation_mul_lt_one_of_le_and_lt`, `pointValuation_add_le_one`
- **Used by**: `pointValuation_translateSlope_xy_le_one_of_doubling`, `pointValuation_translateX_xy_sub_alg_addX_lt_one_of_doubling`, `pointValuation_translateY_xy_sub_alg_addY_lt_one_of_doubling` (≥4 uses)
- **Visibility**: public
- **Lines**: 793–947, proof ~154 lines
- **Notes**: `set_option maxHeartbeats 1600000` — NO-COMMENT. Proof >30 lines.

---

### `theorem pointValuation_translateSlope_xy_le_one_of_doubling`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_eq_x : P.x = xk) (h_eq_y : P.y = yk) (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) → (W_smooth W).pointValuation P (translateSlope_xy W xk yk) ≤ 1`
- **What**: In the tangent case, the K(E) slope has valuation ≤ 1 at P.
- **How**: Writes `slope_K = (slope_K - alg slope_F) + alg slope_F`, applies `pointValuation_add_le_one` with `le_of_lt` from `pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_doubling` and `pointValuation_algebraMap_F_le_one`.
- **Hypotheses**: P = (xk,yk), non-2-torsion.
- **Uses from project**: `pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_doubling`, `pointValuation_add_le_one`
- **Used by**: `pointValuation_translateX_xy_sub_alg_addX_lt_one_of_doubling`, `pointValuation_translateY_xy_sub_alg_addY_lt_one_of_doubling` (≥3 uses, also via `le_one_of_isSome`)
- **Visibility**: public
- **Lines**: 952–966, proof ~14 lines

---

### `theorem pointValuation_translateX_xy_sub_alg_addX_lt_one_of_doubling`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_eq_x : P.x = xk) (h_eq_y : P.y = yk) (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) → (W_smooth W).pointValuation P (translateX_xy W xk yk - algebraMap F KE (W.toAffine.addX P.x xk (W.toAffine.slope P.x xk P.y yk))) < 1`
- **What**: Tangent analogue of the chord x-evaluation: τ_k(x_gen) evaluates to (P+k).x at P in the doubling/tangent case.
- **How**: Same algebraic factorization of the addX-difference as the chord case; uses `pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_doubling` for the slope-difference factor and `pointValuation_translateSlope_xy_le_one_of_doubling` for bounds.
- **Hypotheses**: P = (xk,yk), non-2-torsion.
- **Uses from project**: `translateX_xy`, `Affine.map_addX`, `pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_doubling`, `pointValuation_translateSlope_xy_le_one_of_doubling`, `XClass_mem_maximalIdealAt`, `x_gen_sub_const_eq_algebraMap_XClass`, `pointValuation_mul_lt_one_of_le_and_lt`, `pointValuation_add_le_one`
- **Used by**: `pointValuation_translateY_xy_sub_alg_addY_lt_one_of_doubling`, `isTranslateXY_evaluatesAt_some` (tangent x branch)
- **Visibility**: public
- **Lines**: 972–1042, proof ~70 lines
- **Notes**: Proof >30 lines.

---

### `theorem pointValuation_translateY_xy_sub_alg_addY_lt_one_of_doubling`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_eq_x : P.x = xk) (h_eq_y : P.y = yk) (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) → (W_smooth W).pointValuation P (translateY_xy W xk yk - algebraMap F KE (W.toAffine.addY P.x xk P.y (W.toAffine.slope P.x xk P.y yk))) < 1`
- **What**: Tangent analogue of the chord y-evaluation: τ_k(y_gen) evaluates to (P+k).y at P in the doubling/tangent case.
- **How**: Parallel to the chord y-case: `addY_eq_unfolded_neg_negAddY`, then 4-term factored difference each < 1, calling `pointValuation_translateX_xy_sub_alg_addX_lt_one_of_doubling` for T1.
- **Hypotheses**: P = (xk,yk), non-2-torsion.
- **Uses from project**: `translateY_xy`, `addY_eq_unfolded_neg_negAddY`, `Affine.map_addY`, `Affine.map_addX`, `pointValuation_translateSlope_xy_le_one_of_doubling`, `pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_doubling`, `pointValuation_translateX_xy_sub_alg_addX_lt_one_of_doubling`, `YClass_mem_maximalIdealAt`, `XClass_mem_maximalIdealAt`, `pointValuation_mul_lt_one_of_le_and_lt`
- **Used by**: `isTranslateXY_evaluatesAt_some` (tangent y branch)
- **Visibility**: public
- **Lines**: 1049–1173, proof ~124 lines
- **Notes**: `set_option maxHeartbeats 1600000` — NO-COMMENT. Proof >30 lines.

---

### `theorem translateAlgEquivOfPoint_apply_x_gen`
- **Type**: `(xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) → translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns) (x_gen W) = translateX_xy W xk yk`
- **What**: `τ_k` acts on the x-generator as `translateX_xy`, regardless of whether k is 2-torsion or not.
- **How**: Case split on `yk = W.toAffine.negY xk yk`: 2-torsion case uses `translateAlgEquivOfPoint_some_2tor` and `translateAlgHom_of_2tor_apply_x_gen`; non-torsion case uses `translateAlgEquivOfPoint_some_nonTor` and `translateAlgHom_apply_x_gen`.
- **Hypotheses**: k = some xk yk nonsingular.
- **Uses from project**: `translateAlgEquivOfPoint_some_2tor`, `translateAlgHom_of_2tor_apply_x_gen`, `translateAlgEquivOfPoint_some_nonTor`, `translateAlgHom_apply_x_gen`
- **Used by**: `isTranslateXY_evaluatesAt_some`, `pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome` (≥3 uses)
- **Visibility**: public
- **Lines**: 1196–1206, proof ~10 lines

---

### `theorem translateAlgEquivOfPoint_apply_y_gen`
- **Type**: `(xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) → translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns) (y_gen W) = translateY_xy W xk yk`
- **What**: `τ_k` acts on the y-generator as `translateY_xy`, regardless of 2-torsion.
- **How**: Same case split as `translateAlgEquivOfPoint_apply_x_gen` but for y.
- **Hypotheses**: k nonsingular affine.
- **Uses from project**: `translateAlgEquivOfPoint_some_2tor`, `translateAlgHom_of_2tor_apply_y_gen`, `translateAlgEquivOfPoint_some_nonTor`, `translateAlgHom_apply_y_gen`
- **Used by**: `isTranslateXY_evaluatesAt_some`, `pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome` (≥3 uses)
- **Visibility**: public
- **Lines**: 1210–1220, proof ~10 lines

---

### `instance W_smooth_toAffine_isElliptic`
- **Type**: `(W_smooth W).toAffine.IsElliptic`
- **What**: Trivial instance: `W_smooth W` has the same elliptic-curve typeclass as W itself.
- **How**: `inferInstanceAs W.toAffine.IsElliptic`.
- **Hypotheses**: W.toAffine.IsElliptic.
- **Uses from project**: `W_smooth`
- **Used by**: Present to resolve typeclass inference for subsequent declarations in file.
- **Visibility**: public
- **Lines**: 1222–1223, proof 1 line

---

### `theorem isTranslateXY_evaluatesAt_some`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) (h : (P.toAffinePoint + (Affine.Point.some xk yk h_ns)).IsSome) → IsTranslateXY_evaluatesAt W P (Affine.Point.some xk yk h_ns) h`
- **What**: The predicate `IsTranslateXY_evaluatesAt` (saying τ_k maps generators to the correct values at P) holds for any nonzero k with finite sum. Unifies chord and tangent cases via case-split on P.x = xk.
- **How**: IsSome forces non-cancellation; then case-split on `P.x = xk`. Tangent branch derives `P.y = yk` from `Y_eq_of_Y_ne`. Each sub-goal dispatches to the appropriate chord/tangent x/y evaluation lemma.
- **Hypotheses**: (P + k).IsSome.
- **Uses from project**: `Affine.Point.add_of_Y_eq`, `Affine.Point.zero_not_isSome`, `Affine.Point.add_some`, `SmoothPoint.translate_of_finite_x`, `SmoothPoint.translate_of_finite_y`, `translateAlgEquivOfPoint_apply_x_gen`, `translateAlgEquivOfPoint_apply_y_gen`, `pointValuation_translateX_xy_sub_alg_addX_lt_one_of_X_ne`, `pointValuation_translateX_xy_sub_alg_addX_lt_one_of_doubling`, `pointValuation_translateY_xy_sub_alg_addY_lt_one_of_X_ne`, `pointValuation_translateY_xy_sub_alg_addY_lt_one_of_doubling`, `Affine.Y_eq_of_Y_ne`
- **Used by**: `isTranslateMaxIdealCompatible_on_CoordinateRing_some` (×1), `pointValuation_translateSlope_xy_le_one_of_isSome` (×0 direct), `pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome` (×0 direct) — referenced ≥3 times in aggregate
- **Visibility**: public
- **Lines**: 1227–1300, proof ~73 lines
- **Notes**: Proof >30 lines.

---

### `theorem pointValuation_translateSlope_xy_le_one_of_isSome`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : ...) (h : (P.toAffinePoint + some xk yk h_ns).IsSome) → (W_smooth W).pointValuation P (translateSlope_xy W xk yk) ≤ 1`
- **What**: Unified slope bound — for any finite translate, the K(E) slope has valuation ≤ 1 at P.
- **How**: Case-split on P.x = xk: tangent case derives non-2-torsion and applies `pointValuation_translateSlope_xy_le_one_of_doubling`; chord case applies `pointValuation_translateSlope_xy_le_one_of_X_ne`.
- **Hypotheses**: (P + k).IsSome.
- **Uses from project**: `Affine.Point.add_of_Y_eq`, `Affine.Point.zero_not_isSome`, `Affine.Y_eq_of_Y_ne`, `pointValuation_translateSlope_xy_le_one_of_doubling`, `pointValuation_translateSlope_xy_le_one_of_X_ne`
- **Used by**: `pointValuation_translateX_xy_le_one_of_isSome`, `pointValuation_translateY_xy_le_one_of_isSome`, `pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome` (≥3 uses)
- **Visibility**: public
- **Lines**: 1310–1337, proof ~27 lines

---

### `theorem pointValuation_translateX_xy_le_one_of_isSome`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : ...) (h : (...).IsSome) → (W_smooth W).pointValuation P (translateX_xy W xk yk) ≤ 1`
- **What**: `pV(translateX_xy) ≤ 1` at P when (P + k).IsSome. Used as a bound for polynomial induction.
- **How**: Unfolds `translateX_xy`, then builds up ≤ 1 for each monomial using `pointValuation_translateSlope_xy_le_one_of_isSome` and standard arithmetic bounds (`pointValuation_pow_le_one`, `pointValuation_mul_le_one`, `pointValuation_add_le_one`, `pointValuation_sub_le_one`).
- **Hypotheses**: (P + k).IsSome.
- **Uses from project**: `translateX_xy`, `pointValuation_translateSlope_xy_le_one_of_isSome`, `pointValuation_x_gen_le_one`, `pointValuation_pow_le_one`, `pointValuation_mul_le_one`, `pointValuation_add_le_one`, `pointValuation_sub_le_one`
- **Used by**: `pointValuation_translateY_xy_le_one_of_isSome`, `pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome` (×2 calls, total ≥4)
- **Visibility**: public
- **Lines**: 1341–1369, proof ~28 lines

---

### `theorem pointValuation_translateY_xy_le_one_of_isSome`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : ...) (h : (...).IsSome) → (W_smooth W).pointValuation P (translateY_xy W xk yk) ≤ 1`
- **What**: `pV(translateY_xy) ≤ 1` at P when (P + k).IsSome. Companion to the X version.
- **How**: Rewrites `translateY_xy` via `addY_eq_unfolded_neg_negAddY`, then bounds each term using `pointValuation_translateSlope_xy_le_one_of_isSome`, `pointValuation_translateX_xy_le_one_of_isSome`, `pointValuation_neg_le_one`, and F-constant bounds.
- **Hypotheses**: (P + k).IsSome.
- **Uses from project**: `translateY_xy`, `addY_eq_unfolded_neg_negAddY`, `pointValuation_translateSlope_xy_le_one_of_isSome`, `pointValuation_translateX_xy_le_one_of_isSome`, `pointValuation_y_gen_le_one`, `pointValuation_neg_le_one`, `pointValuation_mul_le_one`, `pointValuation_sub_le_one`, `pointValuation_add_le_one`
- **Used by**: `pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome`
- **Visibility**: public
- **Lines**: 1373–1408, proof ~35 lines
- **Notes**: Proof >30 lines (barely).

---

### `theorem pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : ...) (h : (...).IsSome) (r : (W_smooth W).CoordinateRing) → (W_smooth W).pointValuation P (translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns) (algebraMap (W_smooth W).CoordinateRing KE r)) ≤ 1`
- **What**: Item 2 — polynomial-induction lift: for any CoordinateRing element r, `τ_k(algMap r)` has valuation ≤ 1 at P. This extends the generator bounds to all polynomial expressions.
- **How**: Induction via `AdjoinRoot.induction_on` then `Polynomial.induction_on'`: the `add` case uses `pointValuation_add_le_one` with IH; the `monomial` case reduces to `τ_k(algMap(of(C c))) = alg c` (fixed by `AlgEquiv.commutes`) and `τ_k(algMap(root^n)) = translateX_xy^n` (via `h_tau_x`) with `pointValuation_pow_le_one`. Outer `n` powers of y-gen use `pointValuation_translateY_xy_le_one_of_isSome`.
- **Hypotheses**: (P + k).IsSome.
- **Uses from project**: `translateAlgEquivOfPoint_apply_x_gen`, `translateAlgEquivOfPoint_apply_y_gen`, `pointValuation_translateX_xy_le_one_of_isSome`, `pointValuation_translateY_xy_le_one_of_isSome`, `pointValuation_add_le_one`, `pointValuation_mul_le_one`, `pointValuation_pow_le_one`
- **Used by**: `isTranslateMaxIdealCompatible_on_CoordinateRing_some`, `pointValuation_translateAlgEquivOfPoint_algebraMap_eq_one_of_notMem`, `ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_pow_mem`, `ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_ne_zero`, `ord_P_translateAlgEquivOfPoint_algebraMap_le_of_ne_zero` (≥6 uses)
- **Visibility**: public
- **Lines**: 1422–1616, proof ~194 lines
- **Notes**: `set_option maxHeartbeats 800000` — NO-COMMENT. Proof >30 lines. Very long due to manual `show ... from ...` rewrites needed to make `map_mul`/`map_pow` typecheck through CoordinateRing/FunctionField inference.

---

### `theorem isTranslateMaxIdealCompatible_on_CoordinateRing_some`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : ...) (h : (...).IsSome) → IsTranslateMaxIdealCompatible_on_CoordinateRing W P (Affine.Point.some xk yk h_ns) h`
- **What**: Item 3 — for any CoordinateRing element r in maxIdealAt(P+k), the image `τ_k(algMap r)` has valuation < 1 at P.
- **How**: Decomposes r = a·XClass + b·YClass via `Ideal.mem_span_pair`; applies `τ_k` using `map_add`/`map_mul`/`AlgEquiv.commutes`; bounds each summand as `pV ≤ 1 · pV < 1` via Item 2 (`pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome`) and Item 1 (`isTranslateXY_evaluatesAt_some`); combines via strong triangle.
- **Hypotheses**: (P + k).IsSome.
- **Uses from project**: `isTranslateXY_evaluatesAt_some`, `pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome`, `x_gen_sub_const_eq_algebraMap_XClass`, `y_gen_sub_const_eq_algebraMap_YClass`, `pointValuation_mul_lt_one_of_le_and_lt`, `Ideal.mem_span_pair`
- **Used by**: `pointValuation_translateAlgEquivOfPoint_algebraMap_eq_one_of_notMem`, `ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_pow_mem` (×1 direct each; ≥3 total)
- **Visibility**: public
- **Lines**: 1630–1797, proof ~167 lines
- **Notes**: Proof >30 lines.

---

### `theorem pointValuation_translateAlgEquivOfPoint_algebraMap_eq_one_of_notMem`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : ...) (h : (...).IsSome) (r : (W_smooth W).CoordinateRing) (h_notMem : r ∉ (W_smooth W).maximalIdealAt (P.translate_of_finite ...)) → (W_smooth W).pointValuation P (translateAlgEquivOfPoint W ... (algMap r)) = 1`
- **What**: Item 4 part 1 — if CoordinateRing element r is outside the maximal ideal at P+k, then `τ_k(algMap r)` has valuation exactly 1 at P.
- **How**: Decomposes r = r' + alg c where c = evalAt(P+k) r ≠ 0 and r' ∈ maxIdealAt(P+k); then `pV(τ_k(algMap r')) < 1` (Item 3) while `pV(alg c) = 1` (by `pointValuation_algebraMap_F_eq_one_of_ne_zero`); strong triangle `Valuation.map_add_eq_of_lt_right` gives the result.
- **Hypotheses**: r ∉ maxIdealAt(P+k).
- **Uses from project**: `isTranslateMaxIdealCompatible_on_CoordinateRing_some`, `pointValuation_algebraMap_F_eq_one_of_ne_zero`, `ker_evalAt`, `evalAt_algebraMap`
- **Used by**: `ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_ne_zero` (×1), `ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_pow_mem` is used by step 1 (×1), and more (≥3 uses)
- **Visibility**: public
- **Lines**: 1815–1910, proof ~95 lines
- **Notes**: Proof >30 lines.

---

### `theorem zero_le_ord_P_of_pointValuation_le_one`
- **Type**: `{f : (W_smooth W).FunctionField} (P : (W_smooth W).SmoothPoint) (hf : (W_smooth W).pointValuation P f ≤ 1) → (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P f`
- **What**: If pV(f) ≤ 1 at P, then ord_P(f) ≥ 0 — the bridge from the valuation bound to the integer-order bound.
- **How**: Case-splits on pV < 1 vs pV = 1: if < 1, applies `one_le_ord_P_iff_pointValuation_lt_one` to get ord ≥ 1 ≥ 0; if = 1, directly unfolds `ord_P` to show `-(unzero hv).toAdd = 0` and the unzero equals 1.
- **Hypotheses**: f has pointValuation ≤ 1.
- **Uses from project**: `SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one`, `SmoothPlaneCurve.ord_P_eq_top_iff`, `SmoothPlaneCurve.ord_P_zero`
- **Used by**: `ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_pow_mem` (base case, ×1, ≥3 total)
- **Visibility**: public
- **Lines**: 1920–1979, proof ~59 lines
- **Notes**: Proof >30 lines.

---

### `theorem ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_pow_mem`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : ...) (h : (...).IsSome) (n : ℕ) (r : (W_smooth W).CoordinateRing) (h_mem : r ∈ (maxIdealAt(P+k))^n) → (n : WithTop ℤ) ≤ (W_smooth W).ord_P P (τ_k (algMap r))`
- **What**: Item 4 part 2 step 1 — if r ∈ maxIdealAt(P+k)^n, then ord_P P (τ_k(algMap r)) ≥ n. The ord-transport inequality in one direction.
- **How**: Induction via `Submodule.pow_induction_on_left'`: base uses Item 2 + `zero_le_ord_P_of_pointValuation_le_one`; add case uses `ord_P_add_le` + min-le; mem_mul case uses Item 3 + `one_le_ord_P_iff_pointValuation_lt_one` for ord(τ(m)) ≥ 1, then `ord_P_mul` and IH.
- **Hypotheses**: r ∈ maxIdealAt(P+k)^n.
- **Uses from project**: `zero_le_ord_P_of_pointValuation_le_one`, `isTranslateMaxIdealCompatible_on_CoordinateRing_some`, `pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome`, `SmoothPlaneCurve.ord_P_add_le`, `SmoothPlaneCurve.ord_P_mul`, `SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one`
- **Used by**: `ord_P_translateAlgEquivOfPoint_algebraMap_le_of_ne_zero`, `ord_P_translateAlgEquivOfPoint_neg_algebraMap_ge_of_pow_mem` (≥3 uses)
- **Visibility**: public
- **Lines**: 1989–2056, proof ~67 lines
- **Notes**: `set_option maxHeartbeats 1600000` — NO-COMMENT. Proof >30 lines.

---

### `theorem ord_P_translateAlgEquivOfPoint_neg_algebraMap_ge_of_pow_mem`
- **Type**: `(P : (W_smooth W).SmoothPoint) ... (n : ℕ) (s : (W_smooth W).CoordinateRing) (h_mem : s ∈ (maxIdealAt P)^n) → (n : WithTop ℤ) ≤ (W_smooth W).ord_P (P+k) (τ_{-k}(algMap s))`
- **What**: Step 1 applied at (P+k, -k): if s ∈ maxIdealAt(P)^n, then ord_{P+k}(τ_{-k}(algMap s)) ≥ n. Used for the reverse inequality.
- **How**: Reduces to step 1 (`ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_pow_mem`) by showing that `(P+k) + (-k) = P` (via `add_assoc` and `add_neg_cancel`), hence (P+k) + (-k) is finite and equals P, so the hypothesis translates correctly.
- **Hypotheses**: s ∈ maxIdealAt(P)^n.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_pow_mem`, `Affine.negY_negY`, `Affine.nonsingular_neg`, `Affine.Point.add_of_Y_eq`, `Affine.Point.some_isSome`, `SmoothPoint.translate_of_finite_toAffinePoint`, `SmoothPoint.ext`, `SmoothPoint.translate_of_finite_x`, `SmoothPoint.translate_of_finite_y`
- **Used by**: `ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_ne_zero`
- **Visibility**: public
- **Lines**: 2068–2139, proof ~71 lines
- **Notes**: Proof >30 lines.

---

### `private theorem mem_pow_maxIdealAt_of_le_ord_P_algebraMap`
- **Type**: `(P : (W_smooth W).SmoothPoint) {r : (W_smooth W).CoordinateRing} (hr : r ≠ 0) {n : ℕ} (h_le : (n : WithTop ℤ) ≤ ord_P P (algMap r)) → r ∈ (maxIdealAt P)^n`
- **What**: Bridge: if ord_P ≥ n for a nonzero CoordinateRing element, then r ∈ maxIdealAt(P)^n. Uses the `count` formula for ord_P on CoordinateRing elements.
- **How**: Via `ord_P_algebraMap_eq_count`, gets `n ≤ count_M(P)(span r)`, then `Associates.prime_pow_dvd_iff_le` and `Ideal.dvd_iff_le` and `Ideal.span_singleton_le_iff_mem`.
- **Hypotheses**: r ≠ 0; ord_P ≥ n (for the coordinateRing algebraMap image).
- **Uses from project**: `(W_smooth W).ord_P_algebraMap_eq_count`, `maximalIdealAt_isMaximal`, `maximalIdealAt_ne_bot`
- **Used by**: `ord_P_translateAlgEquivOfPoint_algebraMap_le_of_ne_zero`, `ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_ne_zero` (×2 uses ≥3)
- **Visibility**: private
- **Lines**: 2164–2202, proof ~38 lines
- **Notes**: Proof >30 lines.

---

### `theorem ord_P_translateAlgEquivOfPoint_algebraMap_le_of_ne_zero`
- **Type**: `(P : ...) (xk yk : F) (h_ns : ...) (h : (...).IsSome) (r : CoordinateRing) (hr : r ≠ 0) → ord_P (P+k) (algMap r) ≤ ord_P P (τ_k (algMap r))`
- **What**: One direction of CoordRing ord-equality: ord at P+k of r (via algMap) is at most the ord at P of τ_k applied to r.
- **How**: Sets `n_nat = count_{M(P+k)}(span r)` so that `ord_{P+k}(algMap r) = n_nat`; shows r ∈ M(P+k)^n_nat via `mem_pow_maxIdealAt_of_le_ord_P_algebraMap`; applies step 1 `ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_pow_mem`.
- **Hypotheses**: r ≠ 0 in CoordinateRing.
- **Uses from project**: `(W_smooth W).ord_P_algebraMap_eq_count`, `mem_pow_maxIdealAt_of_le_ord_P_algebraMap`, `ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_pow_mem`
- **Used by**: `ord_P_translateAlgEquivOfPoint_algebraMap_eq_of_ne_zero`
- **Visibility**: public
- **Lines**: 2215–2259, proof ~44 lines
- **Notes**: Proof >30 lines.

---

### `theorem ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_ne_zero`
- **Type**: `(P : ...) (xk yk : F) (h_ns : ...) (h : (...).IsSome) (r : CoordinateRing) (hr : r ≠ 0) → ord_P P (τ_k (algMap r)) ≤ ord_P (P+k) (algMap r)`
- **What**: Reverse direction of CoordRing ord-equality: ord at P of τ_k(algMap r) is at most ord at P+k of r.
- **How**: Uses IsLocalization.surj to write `τ_k(algMap r) = τ_k(algMap a) / τ_k(algMap q)` (in the local ring at P). Shows q ∉ maxIdealAt P so `pV_{P+k}(τ_{-k}(algMap q)) = 1` (Item 4 part 1 at swapped roles P+k, -k). Uses step 2 (`ord_P_translateAlgEquivOfPoint_neg_algebraMap_ge_of_pow_mem`) for u ∈ M(P)^m_nat. Then `h_comp: τ_{-k}∘τ_k = id` (via `translateAlgEquivOfPoint_add` + `add_neg_cancel`) gives `τ_{-k}(τ_k(algMap r)) * τ_{-k}(algMap q) = τ_{-k}(algMap u)`, from which `ord_{P+k}(algMap r) ≥ m_nat = ord_P(τ_k(algMap r))`.
- **Hypotheses**: r ≠ 0 in CoordinateRing.
- **Uses from project**: `mem_localRingAt_image_iff_pointValuation_le_one`, `pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome`, `pointValuation_translateAlgEquivOfPoint_algebraMap_eq_one_of_notMem`, `ord_P_translateAlgEquivOfPoint_neg_algebraMap_ge_of_pow_mem`, `mem_pow_maxIdealAt_of_le_ord_P_algebraMap`, `ord_P_algebraMap_eq_count`, `translateAlgEquivOfPoint_add`, `translateAlgEquivOfPoint_zero`, `SmoothPlaneCurve.ord_P_mul`, `SmoothPlaneCurve.ord_P_eq_zero_iff_pointValuation_eq_one`
- **Used by**: `ord_P_translateAlgEquivOfPoint_algebraMap_eq_of_ne_zero`
- **Visibility**: public
- **Lines**: 2278–2549, proof ~271 lines
- **Notes**: Proof >30 lines. Longest proof in the file.

---

### `theorem ord_P_translateAlgEquivOfPoint_algebraMap_eq_of_ne_zero`
- **Type**: `(P : ...) (xk yk : F) (h_ns : ...) (h : (...).IsSome) (r : CoordinateRing) (hr : r ≠ 0) → ord_P P (τ_k (algMap r)) = ord_P (P+k) (algMap r)`
- **What**: CoordinateRing-level ord equality: τ_k exactly transports ord from P+k to P for nonzero CoordinateRing elements.
- **How**: Combines the two inequalities via `le_antisymm`.
- **Hypotheses**: r ≠ 0 in CoordinateRing.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_ne_zero`, `ord_P_translateAlgEquivOfPoint_algebraMap_le_of_ne_zero`
- **Used by**: `translate_ord_eq_all_nonzero` (×2, for numerator and denominator)
- **Visibility**: public
- **Lines**: 2555–2573, proof ~18 lines

---

### `theorem translate_ord_eq_all_nonzero`
- **Type**: `(P : ...) (xk yk : F) (h_ns : ...) (h : (...).IsSome) (g : KE) (hg : g ≠ 0) → ord_P P (τ_k g) = ord_P (P+k) g`
- **What**: K(E)-level ord equality for τ_k: for any nonzero function field element g, the order at P of τ_k(g) equals the order at P+k of g. This is the main exported result of the file.
- **How**: Decomposes g = algMap(a)/algMap(b) via `IsFractionRing.div_surjective`; shows τ_k(g) = τ_k(algMap a)/τ_k(algMap b); uses `ord_P_mul`, `ord_P_inv`, and `ord_P_translateAlgEquivOfPoint_algebraMap_eq_of_ne_zero` for each of a, b.
- **Hypotheses**: g ≠ 0 in K(E); (P + k).IsSome.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_algebraMap_eq_of_ne_zero`, `SmoothPlaneCurve.ord_P_mul`, `SmoothPlaneCurve.ord_P_inv`
- **Used by**: `isTranslateValuationCompatible_some`, `isTranslateValuationCompatible_all` (and external: `DivisorTranslate.lean`, `PoleDivisorFallback.lean`) (≥4 uses)
- **Visibility**: public
- **Lines**: 2587–2663, proof ~76 lines
- **Notes**: Proof >30 lines.

---

### `theorem isTranslateValuationCompatible_some`
- **Type**: `(P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : ...) (h : (...).IsSome) → IsTranslateValuationCompatible W P (Affine.Point.some xk yk h_ns) h`
- **What**: For nonzero k, the named predicate `IsTranslateValuationCompatible` holds: `pointValuation P ∘ τ_k = pointValuation (P+k)` as valuations on K(E)*.
- **How**: Applies `isTranslateValuationCompatible_of_ord_P_eq` (from TranslationOrd.lean), feeding in `translate_ord_eq_all_nonzero`.
- **Hypotheses**: (P + k).IsSome.
- **Uses from project**: `isTranslateValuationCompatible_of_ord_P_eq`, `translate_ord_eq_all_nonzero`
- **Used by**: `isTranslateValuationCompatible_all`
- **Visibility**: public
- **Lines**: 2671–2680, proof ~9 lines

---

### `theorem isTranslateValuationCompatible_all`
- **Type**: `(P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point) (h : (P.toAffinePoint + k).IsSome) → IsTranslateValuationCompatible W P k h`
- **What**: The full discharge of `IsTranslateValuationCompatible` for all k (including k = 0). This is the file's final export.
- **How**: Applies `isTranslateValuationCompatible_of_some_witness`, which reduces to the nonzero case; dispatches k = 0 as an absurdity and k = some xk yk h_ns to `isTranslateValuationCompatible_some`.
- **Hypotheses**: None beyond the IsSome condition.
- **Uses from project**: `isTranslateValuationCompatible_of_some_witness`, `isTranslateValuationCompatible_some`
- **Used by**: not referenced in this file; exported (but not found referenced in the scanned external files either — may be imported implicitly via TranslationOrd)
- **Visibility**: public
- **Lines**: 2688–2696, proof ~8 lines
- **Notes**: Might be dead code in this file if TranslationOrd uses the predicate via a different path.
