# Inventory: ./HasseWeil/EC/TranslationOrd.lean

**Total lines**: 5636. **Sorries**: none. **Imports**: `HasseWeil.EC.Translation`, `HasseWeil.Curves.AlgebraicNonNegOrd`, `HasseWeil.EC.GenericPoint`, `HasseWeil.Curves.SmoothPointTranslate`, `HasseWeil.OrdAtInftyBridge`.

This file is the main infrastructure file for the translation action of `E(F)` on `K(E)`. It establishes:
1. ord-positivity/exact-value results at the smooth point `−T` for `x_gen − xk`, `y_gen − negY xk yk`, and derived quantities.
2. Transcendence of `translateX_xy` for both 2-torsion and non-2-torsion `T`.
3. The unconditional F-algebra automorphisms `translateAlgHom_of_nonTorsion`, `translateAlgHom_of_2tor` and their round-trips on generators `x_gen`, `y_gen`.
4. The unified `translateAlgEquivOfPoint : W.toAffine.Point → (KE ≃ₐ[F] KE)`, proved to be a group homomorphism (the master theorem `translateAlgEquivOfPoint_add`) and injective.
5. A modular Step (B'')/Step (C) framework for the valuation-transport obligation (`IsTranslateValuationCompatible`, `IsTranslateOrdAtInftyCompatible`) needed for the ord-transport arc.

---

## Section 1: The smooth point `−T` and basic XClass/YClass facts (lines 47–511)

### `noncomputable def negSmoothPoint`
- **Type**: `(xk yk : F) → W.toAffine.Nonsingular xk yk → (W_smooth W).SmoothPoint`
- **What**: Packages the smooth point `−T = (xk, negY xk yk)` from a nonsingular point `(xk, yk)`.
- **How**: Direct construction via `Affine.nonsingular_neg`.
- **Hypotheses**: `W.toAffine.Nonsingular xk yk`.
- **Uses from project**: `W_smooth`
- **Used by**: Almost every subsequent theorem in this file; used 95+ times.
- **Visibility**: public
- **Lines**: 47–53, proof 5 lines
- **Notes**: Key infrastructure repeated throughout

### `@[simp] theorem negSmoothPoint_x`
- **Type**: `(negSmoothPoint W xk yk h_ns).x = xk`
- **What**: The x-coordinate of `−T` is `xk`.
- **How**: `rfl`
- **Hypotheses**: `W.toAffine.Nonsingular xk yk`
- **Uses from project**: `negSmoothPoint`
- **Used by**: various proofs needing to unfold the x-coord
- **Visibility**: public
- **Lines**: 54–56, proof 1 line

### `@[simp] theorem negSmoothPoint_y`
- **Type**: `(negSmoothPoint W xk yk h_ns).y = W.toAffine.negY xk yk`
- **What**: The y-coordinate of `−T` is `negY xk yk`.
- **How**: `rfl`
- **Uses from project**: `negSmoothPoint`
- **Used by**: various proofs needing to unfold the y-coord
- **Visibility**: public
- **Lines**: 58–60, proof 1 line

### `theorem x_gen_sub_const_eq_algebraMap_XClass`
- **Type**: `x_gen W - algebraMap F KE xk = algebraMap W.toAffine.CoordinateRing KE (Affine.CoordinateRing.XClass W.toAffine xk)`
- **What**: Identifies `x_gen − xk` in the function field as the image of `XClass` from the coordinate ring.
- **How**: Uses `IsScalarTower.algebraMap_apply` and `map_sub`; `rfl` finishes.
- **Hypotheses**: none beyond the implicit `W`, `F`
- **Uses from project**: `x_gen`
- **Used by**: `one_le_ord_P_x_gen_sub_const`, `ord_P_x_gen_sub_const_le_one_of_maxIdeal_span`
- **Visibility**: public
- **Lines**: 67–84, proof 17 lines

### `theorem XClass_mem_maximalIdealAt`
- **Type**: `P.x = xk → Affine.CoordinateRing.XClass W.toAffine xk ∈ (W_smooth W).maximalIdealAt P`
- **What**: If the x-coordinate of smooth point `P` is `xk`, then `XClass xk` is in the maximal ideal at `P`.
- **How**: Direct from `Affine.CoordinateRing.XYIdeal` being span containing `XClass`; `Ideal.subset_span`.
- **Uses from project**: `W_smooth`
- **Used by**: `one_le_ord_P_x_gen_sub_const`
- **Visibility**: public
- **Lines**: 91–99, proof 8 lines

### `theorem one_le_ord_P_x_gen_sub_const`
- **Type**: `(1 : WithTop ℤ) ≤ (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns) (x_gen W - algebraMap F KE xk)`
- **What**: At the smooth point `−T`, `x_gen − xk` has order at least 1 (i.e., it vanishes at `−T`).
- **How**: Uses `x_gen_sub_const_eq_algebraMap_XClass` + membership in the maximal ideal via `XClass_mem_maximalIdealAt`, then `ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt`, `pointValuation_algebraMap_le_one`, and `IsFractionRing.injective`; case-splits on `WithTop ℤ` and uses omega.
- **Uses from project**: `x_gen_sub_const_eq_algebraMap_XClass`, `XClass_mem_maximalIdealAt`, `negSmoothPoint`, `x_gen`
- **Used by**: `ord_P_x_gen_sub_const_le_one_of_maxIdeal_span` (indirectly), `ord_P_y_gen_sub_const_eq_zero`, `ord_P_translateSlope_xy_le_neg_one`, `ord_P_translateX_xy_lt_zero`, `ord_P_translateX_xy_eq_neg_two_of_non_2_tor`, `one_le_ord_P_A_at_2tor`, `ord_P_B_minus_a1_yk_decomposed_eq_zero_at_2tor`
- **Visibility**: public
- **Lines**: 110–173, proof 63 lines
- **Notes**: >30 lines

### `theorem ord_P_x_gen_sub_const_le_one_of_maxIdeal_span`
- **Type**: given `h_max_eq` that `maximalIdeal (localRingAt(−T)) = span{algMap XClass}`, proves `ord_P (x_gen − xk) ≤ 1`
- **What**: Upper bound on ord using the maxIdeal-span hypothesis; uses `intValuation_singleton` to get valuation = exp(−1), then translates to `ord_P ≤ 1`.
- **How**: `IsDedekindDomain.HeightOneSpectrum.intValuation_singleton` for the single-generator DVR; `valuation_of_algebraMap` to move to K(E)-level; unfold `ord_P` and `Multiplicative.toAdd`.
- **Uses from project**: `negSmoothPoint`, `x_gen_sub_const_eq_algebraMap_XClass`, `x_gen`
- **Used by**: `ord_P_x_gen_sub_const_eq_one_of_maxIdeal_span`
- **Visibility**: public
- **Lines**: 192–255, proof 62 lines
- **Notes**: >30 lines; parallel to `ord_P_y_gen_sub_negY_const_le_one_of_maxIdeal_span`

### `theorem ord_P_x_gen_sub_const_eq_one_of_maxIdeal_span`
- **Type**: given `h_max_eq`, `ord_P (x_gen − xk) = 1`
- **What**: Combines the `≥1` and `≤1` bounds.
- **How**: `le_antisymm` from the two bounds.
- **Uses from project**: `ord_P_x_gen_sub_const_le_one_of_maxIdeal_span`, `one_le_ord_P_x_gen_sub_const`
- **Used by**: `ord_P_x_gen_sub_const_eq_one_of_non_2_tor`
- **Visibility**: public
- **Lines**: 261–272, proof 4 lines

### `theorem polynomialY_evalEval_ne_zero_at_negSmoothPoint`
- **Type**: `yk ≠ W.toAffine.negY xk yk → W.toAffine.polynomialY.evalEval xk (W.toAffine.negY xk yk) ≠ 0`
- **What**: `polynomialY` does not vanish at `−T` when `T` is non-2-torsion.
- **How**: Unfolds `evalEval_polynomialY`; uses `linear_combination` from the non-2-torsion condition.
- **Uses from project**: `negSmoothPoint` (implicit)
- **Used by**: `maximalIdeal_localRingAt_eq_span_XClass_of_non_2_tor`
- **Visibility**: public
- **Lines**: 291–304, proof 13 lines

### `theorem maximalIdeal_localRingAt_eq_span_XClass_of_non_2_tor`
- **Type**: `yk ≠ W.toAffine.negY xk yk → maximalIdeal(localRingAt(−T)) = span{algMap XClass}`
- **What**: For non-2-torsion `T`, the maximal ideal of the local ring at `−T` is generated by the image of `XClass`.
- **How**: Uses project lemmas `yclass_mul_quot_in_xclass_span` and `mk_quot_not_mem` (from `Valuation.lean`), `IsLocalization.map_units` for unit-cancellation, `Ideal.map_span`, `Localization.AtPrime.map_eq_maximalIdeal`.
- **Uses from project**: `negSmoothPoint`, `polynomialY_evalEval_ne_zero_at_negSmoothPoint`, `yclass_mul_quot_in_xclass_span` (from Valuation.lean), `mk_quot_not_mem` (from Valuation.lean)
- **Used by**: `ord_P_x_gen_sub_const_eq_one_of_non_2_tor`
- **Visibility**: public
- **Lines**: 320–401, proof ~80 lines (incl. set-up)
- **Notes**: `set_option maxHeartbeats 1600000` — NO-COMMENT; >30 lines

### `theorem ord_P_x_gen_sub_const_eq_one_of_non_2_tor`
- **Type**: `yk ≠ W.toAffine.negY xk yk → ord_P (x_gen − xk) = 1` at `−T`
- **What**: Unconditional exact ord formula for non-2-torsion (discharge of the span hypothesis).
- **How**: Combines `ord_P_x_gen_sub_const_eq_one_of_maxIdeal_span` + `maximalIdeal_localRingAt_eq_span_XClass_of_non_2_tor`.
- **Uses from project**: `ord_P_x_gen_sub_const_eq_one_of_maxIdeal_span`, `maximalIdeal_localRingAt_eq_span_XClass_of_non_2_tor`
- **Used by**: `ord_P_translateX_xy_eq_neg_two_of_non_2_tor`, `ord_P_translateY_xy_eq_neg_three_of_non_2_tor`
- **Visibility**: public
- **Lines**: 403–412, proof 3 lines

### `theorem pointValuation_x_gen_sub_const_lt_one_at_negSmoothPoint`
- **Type**: `yk ≠ negY xk yk → pointValuation(−T)(x_gen − xk) < 1`
- **What**: Valuation form (strict < 1, meaning the function vanishes at `−T`) for non-2-torsion.
- **How**: `one_le_ord_P_iff_pointValuation_lt_one` applied to the exact ord formula.
- **Uses from project**: `ord_P_x_gen_sub_const_eq_one_of_non_2_tor`, `x_gen_sub_const_ne_zero`
- **Used by**: `pointValuation_xy_sub_const_lt_one_at_negSmoothPoint`, `pointValuation_triple_at_negSmoothPoint`
- **Visibility**: public
- **Lines**: 418–431, proof 13 lines

### `theorem pointValuation_x_gen_sub_const_le_one_at_negSmoothPoint`
- **Type**: `pointValuation(−T)(x_gen − xk) ≤ 1` for non-2-torsion
- **What**: Weakened form (≤ 1).
- **How**: `le_of_lt` from the strict form.
- **Uses from project**: `pointValuation_x_gen_sub_const_lt_one_at_negSmoothPoint`
- **Used by**: possibly downstream consumers in other files
- **Visibility**: public
- **Lines**: 438–444, proof 2 lines

### `theorem pointValuation_x_gen_le_one`
- **Type**: `∀ P, pointValuation P (x_gen W) ≤ 1`
- **What**: `x_gen` lies in the integer ring at every smooth point.
- **How**: `pointValuation_algebraMap_le_one` on the image of `Polynomial.X`.
- **Uses from project**: `x_gen`
- **Used by**: `x_gen_mem_localRingAt_image`, `ord_P_x_gen_nonneg`, `ord_P_translateX_xy_lt_zero`, `ord_P_translateY_xy_eq_neg_three_of_non_2_tor`, `ord_P_translateX_xy_lt_zero_at_2tor`
- **Visibility**: public
- **Lines**: 450–455, proof 4 lines

### `theorem pointValuation_y_gen_le_one`
- **Type**: `∀ P, pointValuation P (y_gen W) ≤ 1`
- **What**: `y_gen` lies in the integer ring at every smooth point.
- **How**: `pointValuation_algebraMap_le_one` on `AdjoinRoot.root`.
- **Uses from project**: `y_gen`
- **Used by**: `y_gen_mem_localRingAt_image`, `ord_P_translateY_xy_eq_neg_three_of_non_2_tor`
- **Visibility**: public
- **Lines**: 461–466, proof 4 lines

### `theorem pointValuation_xy_gen_le_one`
- **Type**: `pointValuation P (x_gen W) ≤ 1 ∧ pointValuation P (y_gen W) ≤ 1`
- **What**: Conjunction of both generator integer-ring facts.
- **How**: Trivial conjunction.
- **Uses from project**: `pointValuation_x_gen_le_one`, `pointValuation_y_gen_le_one`
- **Used by**: (unused inside file; interface lemma)
- **Visibility**: public
- **Lines**: 471–474, proof 2 lines

### `theorem x_gen_mem_localRingAt_image`
- **Type**: `∃ u : localRingAt P, algebraMap u = x_gen W`
- **What**: `x_gen` lifts to the local ring at every smooth point.
- **How**: `mem_localRingAt_image_of_pointValuation_le_one` from `SmoothPlaneCurve`.
- **Uses from project**: `pointValuation_x_gen_le_one`
- **Used by**: (unused inside file)
- **Visibility**: public
- **Lines**: 479–484, proof 2 lines

### `theorem y_gen_mem_localRingAt_image`
- **Type**: `∃ u : localRingAt P, algebraMap u = y_gen W`
- **What**: `y_gen` lifts to the local ring at every smooth point.
- **How**: Same mechanism as `x_gen_mem_localRingAt_image`.
- **Uses from project**: `pointValuation_y_gen_le_one`
- **Used by**: (unused inside file)
- **Visibility**: public
- **Lines**: 488–493, proof 2 lines

### `theorem algebraMap_F_mem_localRingAt_image`
- **Type**: `∃ u : localRingAt P, algebraMap u = algebraMap F KE c`
- **What**: F-constants lift to every local ring.
- **How**: `pointValuation_algebraMap_F_le_one` + `mem_localRingAt_image_of_pointValuation_le_one`.
- **Used by**: (unused inside file)
- **Visibility**: public
- **Lines**: 497–504, proof 3 lines

### `theorem pointValuation_algebraMap_F_le_one_apply`
- **Type**: `pointValuation P (algebraMap F KE c) ≤ 1`
- **What**: Simple restatement of `pointValuation_algebraMap_F_le_one`.
- **Used by**: (unused inside file; thin wrapper)
- **Visibility**: public
- **Lines**: 508–511, proof 1 line

---

## Section 2: y-side ord analysis at smooth points (lines 513–1035)

### `theorem y_gen_sub_const_eq_algebraMap_YClass`
- **Type**: `y_gen W - algebraMap F KE yk' = algebraMap CoordinateRing KE (YClass W.toAffine (Polynomial.C yk'))`
- **What**: Identifies `y_gen − yk'` as image of `YClass`.
- **How**: Analogous computation to `x_gen_sub_const_eq_algebraMap_XClass`.
- **Uses from project**: `y_gen`
- **Used by**: `one_le_ord_P_y_gen_sub_const_at_smoothPoint`, `ord_P_y_gen_sub_negY_const_le_one_of_maxIdeal_span`, `pointValuation_y_gen_sub_const_lt_one_at_smoothPoint`, `pointValuation_y_gen_sub_const_eq_one_at_negSmoothPoint`
- **Visibility**: public
- **Lines**: 518–529, proof 11 lines

### `theorem YClass_mem_maximalIdealAt`
- **Type**: `P.y = yk' → YClass ∈ maximalIdealAt P`
- **What**: `YClass` is in the maximal ideal when y-coordinate matches.
- **How**: `Ideal.subset_span` on the second generator of `XYIdeal`.
- **Used by**: `one_le_ord_P_y_gen_sub_const_at_smoothPoint`
- **Visibility**: public
- **Lines**: 532–540, proof 8 lines

### `theorem one_le_ord_P_y_gen_sub_const_at_smoothPoint`
- **Type**: `P.y = yk' → (1 : WithTop ℤ) ≤ ord_P P (y_gen W - algebraMap F KE yk')`
- **What**: At any smooth point with y-coordinate `yk'`, `y_gen − yk'` has order ≥ 1.
- **How**: Exact parallel of `one_le_ord_P_x_gen_sub_const`; uses `YClass_mem_maximalIdealAt` and the same sequence of ord/valuation bridges.
- **Uses from project**: `y_gen_sub_const_eq_algebraMap_YClass`, `YClass_mem_maximalIdealAt`
- **Used by**: `one_le_ord_P_y_gen_sub_negY_const`, `ord_P_y_gen_sub_const_eq_zero`, `pointValuation_y_gen_sub_const_lt_one_at_smoothPoint`, `one_le_ord_P_A_at_2tor`
- **Visibility**: public
- **Lines**: 548–601, proof 53 lines
- **Notes**: >30 lines; structural duplicate of the x-side proof

### `theorem one_le_ord_P_y_gen_sub_negY_const`
- **Type**: `(1 : WithTop ℤ) ≤ ord_P (negSmoothPoint W xk yk h_ns) (y_gen W - algebraMap F KE (negY xk yk))`
- **What**: Specialisation of the y-side positivity to the smooth point `−T`.
- **How**: Applies `one_le_ord_P_y_gen_sub_const_at_smoothPoint` with `rfl`.
- **Uses from project**: `one_le_ord_P_y_gen_sub_const_at_smoothPoint`, `negSmoothPoint`
- **Used by**: `ord_P_y_gen_sub_const_eq_zero`, `ord_P_y_gen_sub_negY_const_eq_one_of_2_tor`, `one_le_ord_P_A_at_2tor`
- **Visibility**: public
- **Lines**: 605–611, proof 2 lines

### `theorem maximalIdeal_localRingAt_eq_span_YClass_of_2_tor`
- **Type**: `yk = negY xk yk → maximalIdeal(localRingAt(−T)) = span{algMap YClass}`
- **What**: For 2-torsion `T`, the maximal ideal is generated by `YClass` instead of `XClass`.
- **How**: Analogous to `maximalIdeal_localRingAt_eq_span_XClass_of_non_2_tor`; uses `xclass_mul_C_g_in_yclass_span` and `mk_C_g_not_mem` from Valuation.lean, `polynomialX_evalEval_ne_zero_at_2tor` (inlined).
- **Uses from project**: `negSmoothPoint`, `xclass_mul_C_g_in_yclass_span`, `mk_C_g_not_mem`
- **Used by**: `ord_P_y_gen_sub_negY_const_le_one_of_maxIdeal_span`
- **Visibility**: public
- **Lines**: 624–716, proof ~92 lines
- **Notes**: `set_option maxHeartbeats 1600000` — NO-COMMENT; >30 lines

### `theorem ord_P_y_gen_sub_negY_const_le_one_of_maxIdeal_span`
- **Type**: given `h_max_eq`, `ord_P (y_gen − negY xk yk) ≤ 1` at `−T`
- **What**: Upper ord bound for y-side given maxIdeal span hypothesis.
- **How**: Structural copy of `ord_P_x_gen_sub_const_le_one_of_maxIdeal_span` using `intValuation_singleton`.
- **Used by**: `ord_P_y_gen_sub_negY_const_eq_one_of_2_tor`
- **Visibility**: public
- **Lines**: 721–786, proof ~65 lines
- **Notes**: >30 lines

### `theorem ord_P_y_gen_sub_negY_const_eq_one_of_2_tor`
- **Type**: `yk = negY xk yk → ord_P (y_gen − negY xk yk) = 1` at `−T`
- **What**: Exact y-side ord for 2-torsion.
- **How**: `le_antisymm` from `ord_P_y_gen_sub_negY_const_le_one_of_maxIdeal_span` + `one_le_ord_P_y_gen_sub_negY_const`.
- **Used by**: (referenced by 2-torsion slope analysis)
- **Visibility**: public
- **Lines**: 792–801, proof 5 lines

### `theorem pointValuation_y_gen_sub_const_lt_one_at_smoothPoint`
- **Type**: `P.y = yk' → pointValuation P (y_gen − yk') < 1`
- **What**: At any smooth point with y-coordinate `yk'`, `y_gen − yk'` vanishes (has valuation < 1).
- **How**: Uses `one_le_ord_P_y_gen_sub_const_at_smoothPoint` + `YClass_ne_zero` + `one_le_ord_P_iff_pointValuation_lt_one`.
- **Used by**: `pointValuation_y_gen_sub_negY_const_lt_one_at_negSmoothPoint`, `pointValuation_xy_sub_const_lt_one_at_negSmoothPoint`, `pointValuation_triple_at_negSmoothPoint`
- **Visibility**: public
- **Lines**: 808–819, proof 11 lines

### `theorem pointValuation_y_gen_sub_negY_const_lt_one_at_negSmoothPoint`
- **Type**: `pointValuation(−T)(y_gen − negY xk yk) < 1`
- **What**: Specialisation to `−T`.
- **How**: `pointValuation_y_gen_sub_const_lt_one_at_smoothPoint` with `rfl`.
- **Used by**: `pointValuation_xy_sub_const_lt_one_at_negSmoothPoint`, `pointValuation_triple_at_negSmoothPoint`
- **Visibility**: public
- **Lines**: 825–830, proof 3 lines

### `theorem pointValuation_y_gen_sub_const_le_one_at_smoothPoint`
- **Type**: `P.y = yk' → pointValuation P (y_gen − yk') ≤ 1`
- **What**: Weakened ≤ 1 form for any smooth point.
- **How**: `le_of_lt`.
- **Used by**: (unused inside file; interface)
- **Visibility**: public
- **Lines**: 835–838, proof 2 lines

### `theorem pointValuation_y_gen_sub_negY_const_le_one_at_negSmoothPoint`
- **Type**: `pointValuation(−T)(y_gen − negY xk yk) ≤ 1`
- **What**: Weakened form at `−T`.
- **How**: `le_of_lt`.
- **Used by**: (unused inside file)
- **Visibility**: public
- **Lines**: 844–849, proof 2 lines

### `theorem pointValuation_xy_sub_const_lt_one_at_negSmoothPoint`
- **Type**: conjunction of `x_gen − xk` and `y_gen − negY xk yk` vanishing at `−T`, non-2-torsion
- **What**: Bundles both vanishing facts.
- **How**: Direct conjunction.
- **Used by**: (unused inside file; interface)
- **Visibility**: public
- **Lines**: 857–865, proof 4 lines

### `theorem ord_P_y_gen_sub_const_eq_zero`
- **Type**: `yk ≠ negY xk yk → ord_P(−T)(y_gen − yk) = 0`
- **What**: For non-2-torsion `T`, `y_gen − yk` has order exactly 0 at `−T` (since at `−T` the y-value is `negY xk yk ≠ yk`).
- **How**: Decomposes `y_gen − yk = (y_gen − negY xk yk) + (negY xk yk − yk)`; the second term is a nonzero constant (order 0); `ord_P_add_eq_of_lt` via the strict non-archimedean inequality.
- **Uses from project**: `one_le_ord_P_y_gen_sub_negY_const`, `ord_P_algebraMap_F_of_ne_zero`, `SmoothPlaneCurve.ord_P_add_eq_of_lt`
- **Used by**: `pointValuation_y_gen_sub_const_eq_one_at_negSmoothPoint`, `ord_P_translateSlope_xy_le_neg_one`, `ord_P_translateX_xy_lt_zero`, `ord_P_translateX_xy_eq_neg_two_of_non_2_tor`, `ord_P_translateY_xy_eq_neg_three_of_non_2_tor`
- **Visibility**: public
- **Lines**: 880–916, proof 36 lines
- **Notes**: >30 lines

### `theorem pointValuation_y_gen_sub_const_eq_one_at_negSmoothPoint`
- **Type**: `yk ≠ negY xk yk → pointValuation(−T)(y_gen − yk) = 1`
- **What**: Valuation form: `y_gen − yk` is a unit at `−T` for non-2-torsion.
- **How**: From `ord_P = 0` via unfolding `ord_P` def and `WithZero.unzero` extraction.
- **Uses from project**: `ord_P_y_gen_sub_const_eq_zero`, `y_gen_sub_const_eq_algebraMap_YClass`
- **Used by**: `pointValuation_y_gen_sub_const_le_one_at_negSmoothPoint`, `pointValuation_triple_at_negSmoothPoint`
- **Visibility**: public
- **Lines**: 924–951, proof 27 lines

### `theorem pointValuation_y_gen_sub_const_le_one_at_negSmoothPoint`
- **Type**: `pointValuation(−T)(y_gen − yk) ≤ 1` for non-2-torsion
- **What**: Weakening of the equality form.
- **How**: `le_of_eq`.
- **Used by**: (unused inside file; interface)
- **Visibility**: public
- **Lines**: 956–962, proof 2 lines

### `theorem pointValuation_triple_at_negSmoothPoint`
- **Type**: Triple conjunction for non-2-torsion: x-vanishing, y-negY vanishing, y-yk unit
- **What**: All three key valuation facts at `−T` bundled together.
- **How**: Direct conjunction.
- **Used by**: (unused inside file)
- **Visibility**: public
- **Lines**: 976–987, proof 7 lines

### `theorem ord_P_translateSlope_xy_le_neg_one`
- **Type**: `yk ≠ negY xk yk → ord_P(−T)(translateSlope_xy W xk yk) ≤ −1`
- **What**: The chord-slope has a pole at `−T` of order ≥ 1.
- **How**: Rewrites `slope = (y_gen−yk)/(x_gen−xk)` as mul-inv; uses `ord_P_mul + ord_P_inv`, `ord_P_y_gen_sub_const_eq_zero`, `one_le_ord_P_x_gen_sub_const`; integer bound via omega.
- **Uses from project**: `translateSlope_xy_eq`, `ord_P_y_gen_sub_const_eq_zero`, `one_le_ord_P_x_gen_sub_const`, `x_gen_sub_const_ne_zero`
- **Used by**: `ord_P_translateSlope_xy_ne_top`, `ord_P_translateX_xy_lt_zero`
- **Visibility**: public
- **Lines**: 992–1035, proof 43 lines
- **Notes**: >30 lines

### `theorem ord_P_translateSlope_xy_ne_top`
- **Type**: `yk ≠ negY xk yk → ord_P(−T)(translateSlope_xy) ≠ ⊤`
- **What**: The slope function is nonzero at `−T` for non-2-torsion.
- **How**: Contradiction from `ord ≤ −1` and `≠ ⊤`.
- **Uses from project**: `ord_P_translateSlope_xy_le_neg_one`
- **Used by**: `translateSlope_xy_ne_zero_at_negSmoothPoint`
- **Visibility**: public
- **Lines**: 1040–1050, proof 9 lines

### `theorem translateSlope_xy_ne_zero_at_negSmoothPoint`
- **Type**: `yk ≠ negY xk yk → translateSlope_xy W xk yk ≠ 0`
- **What**: The slope is nonzero.
- **How**: Via `ord_P_zero` + `ord_P_translateSlope_xy_ne_top`.
- **Uses from project**: `ord_P_translateSlope_xy_ne_top`
- **Used by**: (unused inside file)
- **Visibility**: public
- **Lines**: 1054–1062, proof 8 lines

---

## Section 3: Algebraic identities and exact ord values (lines 1064–1877)

### `private theorem translateX_xy_mul_sq_eq`
- **Type**: `translateX_xy W xk yk * (x_gen W - algebraMap F KE xk)^2 = (y_gen − yk)^2 + a₁(y_gen − yk)(x_gen − xk) − (a₂ + x_gen + xk)(x_gen − xk)^2`
- **What**: Algebraic identity for `translateX_xy` as a ratio.
- **How**: `field_simp` + `ring` after unfolding `addX` and the slope formula.
- **Uses from project**: `translateX_xy`, `translateSlope_xy_eq`, `x_gen_sub_const_ne_zero`
- **Used by**: `ord_P_translateX_xy_lt_zero`, `ord_P_translateX_xy_eq_neg_two_of_non_2_tor`
- **Visibility**: private
- **Lines**: 1082–1103, proof 21 lines

### `theorem translateY_xy_mul_cube_eq`
- **Type**: `translateY_xy W xk yk * (x_gen W - algebraMap F KE xk)^3 = M_y` where `M_y` is an explicit polynomial in generators
- **What**: Algebraic identity for `translateY_xy` as a ratio.
- **How**: `field_simp` + `ring` after unfolding `addY`, `negY`, `negAddY`, `addX`, slope formula.
- **Uses from project**: `translateY_xy`, `translateSlope_xy_eq`, `x_gen_sub_const_ne_zero`
- **Used by**: `ord_P_translateY_xy_eq_neg_three_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1111–1143, proof 32 lines
- **Notes**: >30 lines

### `private theorem ord_P_algebraMap_R_nonneg`
- **Type**: `(0 : WithTop ℤ) ≤ ord_P P (algebraMap CoordinateRing KE u)`
- **What**: CoordinateRing images have nonneg ord at any smooth point.
- **How**: `pointValuation_algebraMap_le_one` + `ord_P_zero` for the zero case; `WithZero.unzero` arithmetic for the nonzero case.
- **Used by**: `ord_P_x_gen_nonneg`
- **Visibility**: private
- **Lines**: 1147–1174, proof 27 lines

### `theorem ord_P_x_gen_nonneg`
- **Type**: `(0 : WithTop ℤ) ≤ ord_P P (x_gen W)`
- **What**: `x_gen` has nonneg ord everywhere.
- **How**: Instantiates `ord_P_algebraMap_R_nonneg` at `Polynomial.X`.
- **Uses from project**: `ord_P_algebraMap_R_nonneg`, `x_gen`
- **Used by**: `ord_P_translateX_xy_lt_zero`, `ord_P_translateX_xy_eq_neg_two_of_non_2_tor`, `ord_P_translateY_xy_eq_neg_three_of_non_2_tor`, `ord_P_translateX_xy_lt_zero_at_2tor`, `translateX_xy_ne_x_gen_nonTor`, `translateX_xy_ne_x_gen_2tor`
- **Visibility**: public
- **Lines**: 1180–1185, proof 4 lines

### `theorem ord_P_algebraMap_F_nonneg`
- **Type**: `(0 : WithTop ℤ) ≤ ord_P P (algebraMap F KE c)`
- **What**: F-constants have nonneg ord.
- **How**: Zero case via `ord_P_zero`; nonzero case via `ord_P_algebraMap_F_of_ne_zero`.
- **Used by**: `ord_P_translateX_xy_lt_zero`, `ord_P_translateX_xy_eq_neg_two_of_non_2_tor`, `ord_P_translateY_xy_eq_neg_three_of_non_2_tor`, `ord_P_translateX_xy_lt_zero_at_2tor`
- **Visibility**: public
- **Lines**: 1188–1196, proof 8 lines

### `theorem ord_P_translateX_xy_lt_zero`
- **Type**: `yk ≠ negY xk yk → ord_P(−T)(translateX_xy W xk yk) < 0`
- **What**: `translateX_xy` has a pole at `−T` for non-2-torsion. Key step toward transcendence.
- **How**: Uses `translateX_xy_mul_sq_eq` to reduce to `ord_P(N) = 0` where the RHS dominant term `(y_gen − yk)^2` has order 0; `ord_P_add_eq_of_lt` (strict non-arch) + `ord_P_pow + ord_P_mul` to decompose; case-split on `WithTop ℤ` values and omega.
- **Uses from project**: `translateX_xy_mul_sq_eq`, `one_le_ord_P_x_gen_sub_const`, `ord_P_y_gen_sub_const_eq_zero`, `ord_P_x_gen_nonneg`, `ord_P_algebraMap_F_nonneg`, `negSmoothPoint`, `x_gen_sub_const_ne_zero`
- **Used by**: `translateX_xy_transcendental`, `translateX_xy_ne_x_gen_nonTor`
- **Visibility**: public
- **Lines**: 1205–1365, proof 160 lines
- **Notes**: >30 lines; most complex ord calculation in the file (non-2-torsion version)

### `theorem ord_P_translateX_xy_eq_neg_two_of_non_2_tor`
- **Type**: `yk ≠ negY xk yk → ord_P(−T)(translateX_xy W xk yk) = −2`
- **What**: Exact pole order at `−T`.
- **How**: Same algebraic identity as above but using the exact `ord_P (x_gen − xk) = 1`; solves `k + 2 = 0` for k.
- **Uses from project**: `translateX_xy_mul_sq_eq`, `ord_P_x_gen_sub_const_eq_one_of_non_2_tor`, `ord_P_y_gen_sub_const_eq_zero`, `ord_P_x_gen_nonneg`, `ord_P_algebraMap_F_nonneg`, `negSmoothPoint`
- **Used by**: (no callers inside this file; used by other files for the exact pole order)
- **Visibility**: public
- **Lines**: 1379–1517, proof 138 lines
- **Notes**: >30 lines; structural near-duplicate of `ord_P_translateX_xy_lt_zero` with exact ord

### `theorem ord_P_translateY_xy_eq_neg_three_of_non_2_tor`
- **Type**: `yk ≠ negY xk yk → ord_P(−T)(translateY_xy W xk yk) = −3`
- **What**: Exact pole order −3 for the y-translation.
- **How**: Uses `translateY_xy_mul_cube_eq`; proves `ord_P(−yd^3) = 0` (dominant) with all other terms having ord ≥ 1; case-splits to get `k + 3 = 0`.
- **Uses from project**: `translateY_xy_mul_cube_eq`, `ord_P_x_gen_sub_const_eq_one_of_non_2_tor`, `ord_P_y_gen_sub_const_eq_zero`, `ord_P_x_gen_nonneg`, `ord_P_algebraMap_F_nonneg`, `pointValuation_y_gen_le_one`, `negSmoothPoint`
- **Used by**: (no callers inside this file)
- **Visibility**: public
- **Lines**: 1530–1876, proof 346 lines
- **Notes**: `set_option maxHeartbeats 1600000` — NO-COMMENT; largest proof in file; >30 lines

---

## Section 4: Transcendence and AlgHom for non-2-torsion (lines 1878–2479)

### `theorem translateX_xy_transcendental`
- **Type**: `yk ≠ negY xk yk → Transcendental F (translateX_xy W xk yk)`
- **What**: `translateX_xy` is transcendental over `F` for non-2-torsion `T`.
- **How**: `SmoothPlaneCurve.transcendental_of_neg_ord_P` applied to `ord_P_translateX_xy_lt_zero`.
- **Uses from project**: `ord_P_translateX_xy_lt_zero`
- **Used by**: `translateAlgHom_of_nonTorsion`, `translateX_xy_neg_transcendental`, `translateAlgHom_inv_round_trip_x_gen`, `translateAlgHom_inv_round_trip_y_gen`, `translateAlgEquivOfPoint_add`
- **Visibility**: public
- **Lines**: 1888–1893, proof 2 lines

### `noncomputable def translateAlgHom_of_nonTorsion`
- **Type**: `yk ≠ negY xk yk → (KE →ₐ[F] KE)`
- **What**: The F-algebra endomorphism of `K(E)` corresponding to translation by non-2-torsion point `T`.
- **How**: Applies `translateAlgHom` from `EC/Translation.lean` with the `TranslateNonInverse` and `translateBaseHom_injective_of_transcendental` witnesses.
- **Uses from project**: `translateAlgHom`, `x_gen_sub_const_ne_zero`, `translateBaseHom_injective_of_transcendental`, `translateX_xy_transcendental`
- **Used by**: `translateAlgHom_apply_x_gen`, `translateAlgHom_of_nonTorsion_neg`, `translateAlgHom_apply_y_gen`, `translateAlgHom_round_trip_x_gen`, `translateAlgHom_round_trip_y_gen`, `translateAlgHom_inv_round_trip_x_gen`, `translateAlgHom_inv_round_trip_y_gen`, `translateAlgEquiv`, and many group-hom lemmas
- **Visibility**: public
- **Lines**: 1906–1913, proof 5 lines

### `private theorem negY_negY_eq`
- **Type**: `W.toAffine.negY xk (W.toAffine.negY xk yk) = yk`
- **What**: Involution: negY is self-inverse.
- **How**: `ring`.
- **Used by**: `translateAlgHom_of_nonTorsion_neg`, `translateAlgEquiv_symm_eq_neg_point`, `translateX_xy_neg_transcendental`
- **Visibility**: private
- **Lines**: 1924–1927, proof 1 line

### `noncomputable def translateAlgHom_of_nonTorsion_neg`
- **Type**: `yk ≠ negY xk yk → (KE →ₐ[F] KE)`
- **What**: Translation by `−T` (the inverse direction).
- **How**: Applies `translateAlgHom_of_nonTorsion` with `(xk, negY xk yk)` and uses `negY_negY_eq` to verify `−T` is non-2-torsion.
- **Uses from project**: `translateAlgHom_of_nonTorsion`, `negY_negY_eq`, `Affine.nonsingular_neg`
- **Used by**: `translateAlgHom_round_trip_x_gen`, `translateAlgHom_round_trip_y_gen`, `translateAlgHom_neg_apply_x_gen`, `translateAlgHom_neg_apply_y_gen`, `translateAlgEquiv`
- **Visibility**: public
- **Lines**: 1931–1937, proof 5 lines

### `theorem translateAlgHom_apply_x_gen`
- **Type**: `translateAlgHom_of_nonTorsion W xk yk h_ns h_not_2_tor (x_gen W) = translateX_xy W xk yk`
- **What**: The F-AlgHom acts on `x_gen` as `translateX_xy`.
- **How**: Unfolds `translateAlgHom`, `x_gen`, uses `IsFractionRing.liftAlgHom_apply`, `AdjoinRoot.lift_of`, `Polynomial.eval₂_X`.
- **Uses from project**: `translateAlgHom_of_nonTorsion`, `translateAlgHom`, `translateCoordAlgHom`, `translateCoordRingHom`, `translateBaseHom`, `x_gen`
- **Used by**: `translateAlgHom_round_trip_x_gen`, `translateAlgHom_inv_round_trip_x_gen`, `translateAlgEquivOfPoint_add_nonTor_x_gen` (and many group-hom branch theorems)
- **Visibility**: public
- **Lines**: 1947–1969, proof 22 lines

### `noncomputable def liftSomePoint`
- **Type**: `(xk yk : F) → W.toAffine.Nonsingular xk yk → (W_KE W).toAffine.Point`
- **What**: Lifts `T ∈ E(F)` to a point on `W_KE` over `K(E)`.
- **How**: `Affine.Point.some` with `map_nonsingular`.
- **Used by**: `liftSomePoint_neg`, `liftSomePoint_add_neg_eq_zero`, `genericPoint_add_liftSomePoint`, `genericPoint_add_liftSomePoint_neg`, `genericPoint_round_trip`, `liftSomePoint_add_self_eq_zero_of_2tor`, `liftPointToKE_some`, and many round-trip proofs
- **Visibility**: public
- **Lines**: 1978–1983, proof 3 lines

### `noncomputable def liftSomePoint_neg`
- **Type**: `(xk yk : F) → W.toAffine.Nonsingular xk yk → (W_KE W).toAffine.Point`
- **What**: The lift of `−T = (xk, negY xk yk)`.
- **How**: `liftSomePoint W xk (negY xk yk)`.
- **Used by**: `liftSomePoint_add_neg_eq_zero`, `genericPoint_add_liftSomePoint_neg`, many round-trip proofs
- **Visibility**: public
- **Lines**: 1987–1991, proof 2 lines

### `private theorem WKE_negY_algebraMap`
- **Type**: `(W_KE W).toAffine.negY (algebraMap F KE xk) (algebraMap F KE yk') = algebraMap F KE (W.toAffine.negY xk yk')`
- **What**: `algebraMap` commutes with `negY`.
- **How**: Unfold `negY`; `map_mul`, `map_neg`, `map_sub`.
- **Used by**: `liftSomePoint_add_neg_eq_zero`, `liftSomePoint_add_self_eq_zero_of_2tor`
- **Visibility**: private
- **Lines**: 2000–2008, proof 8 lines

### `theorem liftSomePoint_add_neg_eq_zero`
- **Type**: `liftSomePoint W xk yk h_ns + liftSomePoint_neg W xk yk h_ns = 0`
- **What**: `T + (−T) = 0` at the lifted point level.
- **How**: `Affine.Point.add_of_Y_eq` + `WKE_negY_algebraMap` + `negY_negY_eq`.
- **Used by**: `genericPoint_round_trip`, `translateAlgHom_round_trip_x_gen`, `translateAlgHom_round_trip_y_gen`, `translateAlgHom_inv_round_trip_x_gen`, `translateAlgHom_inv_round_trip_y_gen`
- **Visibility**: public
- **Lines**: 2010–2017, proof 6 lines

### `theorem genericPoint_round_trip`
- **Type**: `(genericPoint W + liftSomePoint W xk yk h_ns) + liftSomePoint_neg W xk yk h_ns = genericPoint W`
- **What**: Group law identity for round-trip.
- **How**: `add_assoc`, `liftSomePoint_add_neg_eq_zero`, `add_zero`.
- **Used by**: `translateAlgHom_inv_round_trip_x_gen`, `translateAlgHom_inv_round_trip_y_gen`
- **Visibility**: public
- **Lines**: 2022–2026, proof 3 lines

### `theorem genericPoint_add_liftSomePoint`
- **Type**: `genericPoint W + liftSomePoint W xk yk h_ns = Affine.Point.some (translateX_xy W xk yk) (translateY_xy W xk yk) h`
- **What**: The generic point plus a lifted base-field point gives the translate.
- **How**: `Affine.Point.add_of_X_ne` using `x_gen_sub_const_ne_zero`.
- **Uses from project**: `genericPoint`, `liftSomePoint`, `translateX_xy`, `translateY_xy`, `x_gen_sub_const_ne_zero`
- **Used by**: many round-trip theorems and group-hom branch theorems (27 refs)
- **Visibility**: public
- **Lines**: 2030–2041, proof 10 lines

### `theorem genericPoint_add_liftSomePoint_neg`
- **Type**: Same for `liftSomePoint_neg`
- **What**: Applies `genericPoint_add_liftSomePoint` to `(xk, negY xk yk)`.
- **Used by**: `translateAlgHom_round_trip_x_gen`, `translateAlgHom_round_trip_y_gen`, `translateAlgEquivOfPoint_add`
- **Visibility**: public
- **Lines**: 2045–2058, proof 10 lines

### `theorem translateX_xy_neg_transcendental`
- **Type**: `yk ≠ negY xk yk → Transcendental F (translateX_xy W xk (negY xk yk))`
- **What**: Transcendence for `−T`.
- **How**: `translateX_xy_transcendental` applied to `−T`.
- **Used by**: `translateX_xy_neg_ne_algebraMap`
- **Visibility**: public
- **Lines**: 2069–2075, proof 4 lines

### `theorem translateX_xy_neg_ne_algebraMap`
- **Type**: `yk ≠ negY xk yk → translateX_xy W xk (negY xk yk) ≠ algebraMap F KE xk`
- **What**: The x-translate of `−T` avoids the constant `xk`.
- **How**: Transcendence implies not algebraic; supplies `Polynomial.X - Polynomial.C xk`.
- **Used by**: `translateAlgHom_round_trip_x_gen`, `translateAlgHom_round_trip_y_gen`, `translateAlgEquivOfPoint_nonTor_add_neg`, `translateAlgEquivOfPoint_add`
- **Visibility**: public
- **Lines**: 2079–2086, proof 7 lines

### `theorem translateAlgHom_neg_apply_x_gen`
- **Type**: `translateAlgHom_of_nonTorsion_neg W xk yk h_ns h_not_2_tor (x_gen W) = translateX_xy W xk (negY xk yk)`
- **What**: Action of the `−T` AlgHom on `x_gen`.
- **How**: Specialises `translateAlgHom_apply_x_gen` to `(xk, negY xk yk)`.
- **Used by**: `translateAlgHom_round_trip_x_gen`, `translateAlgHom_round_trip_y_gen`, `translateAlgEquivOfPoint_add` (via inv round-trips)
- **Visibility**: public
- **Lines**: 2094–2100, proof 3 lines

### `theorem translateAlgHom_apply_y_gen`
- **Type**: `translateAlgHom_of_nonTorsion W xk yk h_ns h_not_2_tor (y_gen W) = translateY_xy W xk yk`
- **What**: The F-AlgHom acts on `y_gen` as `translateY_xy`.
- **How**: Unfolds analogously to `translateAlgHom_apply_x_gen`; `AdjoinRoot.lift_root` for the root.
- **Used by**: round-trip theorems and group-hom branch theorems (15 refs)
- **Visibility**: public
- **Lines**: 2104–2121, proof 17 lines

### `theorem translateAlgHom_neg_apply_y_gen`
- **Type**: `translateAlgHom_of_nonTorsion_neg (y_gen W) = translateY_xy W xk (negY xk yk)`
- **What**: Action of `−T` AlgHom on `y_gen`.
- **Used by**: round-trip and group-hom branch theorems
- **Visibility**: public
- **Lines**: 2124–2130, proof 4 lines

### `private theorem σ_commutes_addX`
- **Type**: `σ (addX a b ℓ) = addX (σ a) (σ b) (σ ℓ)` for any `F`-AlgHom `σ`
- **What**: `addX` commutes with F-AlgHoms (F-constants are fixed by commutes).
- **How**: Unfolds `addX`; uses `σ.commutes` for `a₁`, `a₂`.
- **Used by**: `translateAlgHom_round_trip_x_gen`, `translateAlgHom_inv_round_trip_x_gen`, and all group-hom branch x_gen theorems (10 refs total)
- **Visibility**: private
- **Lines**: 2154–2166, proof 12 lines

### `private theorem σ_commutes_negY`
- **Type**: `σ (negY x y) = negY (σ x) (σ y)`
- **What**: `negY` commutes with F-AlgHoms.
- **Used by**: `σ_commutes_addY`
- **Visibility**: private
- **Lines**: 2169–2180, proof 11 lines

### `private theorem σ_commutes_negAddY`
- **Type**: `σ (negAddY a b y₁ ℓ) = negAddY (σ a) (σ b) (σ y₁) (σ ℓ)`
- **What**: `negAddY` commutes with F-AlgHoms.
- **How**: Uses `σ_commutes_addX`.
- **Used by**: `σ_commutes_addY`
- **Visibility**: private
- **Lines**: 2183–2188, proof 5 lines

### `private theorem σ_commutes_addY`
- **Type**: `σ (addY a b y₁ ℓ) = addY (σ a) (σ b) (σ y₁) (σ ℓ)`
- **What**: `addY` commutes with F-AlgHoms.
- **How**: Uses `σ_commutes_negY`, `σ_commutes_addX`, `σ_commutes_negAddY`.
- **Used by**: `translateAlgHom_round_trip_y_gen`, `translateAlgHom_inv_round_trip_y_gen`, all group-hom branch y_gen theorems (8 refs total)
- **Visibility**: private
- **Lines**: 2191–2196, proof 5 lines

### `private theorem σ_commutes_slope_of_X_ne`
- **Type**: `a ≠ b → σ a ≠ σ b → σ (slope a b y₁ y₂) = slope (σ a) (σ b) (σ y₁) (σ y₂)`
- **What**: The slope formula commutes with F-AlgHoms in the secant case.
- **How**: `slope_of_X_ne` + `map_div₀`, `map_sub`.
- **Used by**: all round-trip x_gen/y_gen and group-hom branch theorems (15 refs total)
- **Visibility**: private
- **Lines**: 2199–2205, proof 6 lines

### `theorem translateAlgHom_round_trip_x_gen`
- **Type**: `σ(τ(x_gen W)) = x_gen W` where σ = translation by `−T`, τ = translation by `T`
- **What**: Round-trip on `x_gen`: forward-then-back = identity. Embodies Silverman III.4.10(a).
- **How**: Applies τ to get `translateX_xy T`; applies σ using `σ_commutes_addX`, `σ_commutes_slope_of_X_ne`; links to the group law `(P_neg + T_lift).x = x_gen` via `genericPoint_add_liftSomePoint_neg` + `liftSomePoint_add_neg_eq_zero`; extracts x-coordinate via `Affine.Point.some.injEq`.
- **Uses from project**: `translateAlgHom_apply_x_gen`, `translateAlgHom_neg_apply_x_gen`, `translateAlgHom_neg_apply_y_gen`, `σ_commutes_addX`, `σ_commutes_slope_of_X_ne`, `genericPoint_add_liftSomePoint_neg`, `liftSomePoint_add_neg_eq_zero`, `translateX_xy_neg_ne_algebraMap`, `x_gen_sub_const_ne_zero`
- **Used by**: `translateAlgEquiv`
- **Visibility**: public
- **Lines**: 2218–2273, proof 55 lines
- **Notes**: >30 lines

### `theorem translateAlgHom_round_trip_y_gen`
- **Type**: `σ(τ(y_gen W)) = y_gen W`
- **What**: Round-trip on `y_gen`.
- **How**: Parallel to `translateAlgHom_round_trip_x_gen`; uses `σ_commutes_addY`; extracts `.2` from `injEq`.
- **Used by**: `translateAlgEquiv`
- **Visibility**: public
- **Lines**: 2280–2324, proof 44 lines
- **Notes**: >30 lines

### `theorem algHom_ext_x_y_gen`
- **Type**: `ψ₁ (x_gen W) = ψ₂ (x_gen W) → ψ₁ (y_gen W) = ψ₂ (y_gen W) → ψ₁ = ψ₂`
- **What**: Extensionality for F-AlgHoms on `K(E)`: agreement on the two generators suffices.
- **How**: `IsLocalization.algHom_ext` (peel Frac) + `AdjoinRoot.algHom_ext'` (peel AdjoinRoot) + `Polynomial.algHom_ext` (peel `F[X]`).
- **Used by**: `algEquiv_ext_x_y_gen`, and all master group-hom theorems via `algHom_ext_x_y_gen` (15 refs)
- **Visibility**: public
- **Lines**: 2336–2355, proof 19 lines

### `theorem algEquiv_ext_x_y_gen`
- **Type**: `ψ₁ (x_gen W) = ψ₂ (x_gen W) → ψ₁ (y_gen W) = ψ₂ (y_gen W) → ψ₁ = ψ₂` for AlgEquivs
- **What**: Extensionality for AlgEquivs, reducing to `algHom_ext_x_y_gen`.
- **How**: `AlgEquiv.ext`, `DFunLike.congr_fun`.
- **Used by**: various AlgEquiv identity proofs
- **Visibility**: public
- **Lines**: 2360–2368, proof 8 lines

### `theorem translateAlgHom_inv_round_trip_x_gen`
- **Type**: `τ(σ(x_gen W)) = x_gen W`
- **What**: Inverse round-trip on `x_gen`.
- **How**: Parallel proof using `genericPoint_round_trip` (T then −T).
- **Used by**: `translateAlgEquiv`
- **Visibility**: public
- **Lines**: 2376–2426, proof 50 lines
- **Notes**: >30 lines

### `theorem translateAlgHom_inv_round_trip_y_gen`
- **Type**: `τ(σ(y_gen W)) = y_gen W`
- **What**: Inverse round-trip on `y_gen`.
- **Used by**: `translateAlgEquiv`
- **Visibility**: public
- **Lines**: 2429–2478, proof 49 lines
- **Notes**: >30 lines

---

## Section 5: 2-torsion case — curve identity and transcendence (lines 2480–3010)

### `theorem curve_identity_translate`
- **Type**: `W.toAffine.Equation xk yk → (y_gen − yk)(y_gen + yk + a₁ x_gen + a₃) = (x_gen − xk)(x_gen² + x_gen·xk + xk² + a₂(x_gen + xk) + a₄ − a₁ yk)`
- **What**: Algebraic identity in `K(E)` from subtracting the Weierstrass relation at `(xk, yk)` from the generic relation.
- **How**: `generic_equation`, `translate_constant_equation`, `linear_combination`.
- **Uses from project**: `generic_equation`, `translate_constant_equation`, `x_gen`, `y_gen`
- **Used by**: `ord_P_translateSlope_xy_le_neg_one_at_2tor`
- **Visibility**: public
- **Lines**: 2522–2554, proof 32 lines
- **Notes**: >30 lines

### `theorem A_factorization_at_2tor`
- **Type**: `yk = negY xk yk → (y_gen + yk + a₁ x_gen + a₃) = (y_gen − yk) + a₁(x_gen − xk)`
- **What**: Algebraic simplification of the "A" factor at 2-torsion using `2yk + a₁ xk + a₃ = 0`.
- **How**: `linear_combination`.
- **Used by**: `one_le_ord_P_A_at_2tor`
- **Visibility**: public
- **Lines**: 2574–2589, proof 15 lines

### `theorem one_le_ord_P_A_at_2tor`
- **Type**: `yk = negY xk yk → (1 : WithTop ℤ) ≤ ord_P(−T)(y_gen + yk + a₁ x_gen + a₃)`
- **What**: At smooth 2-torsion `T`, the A-factor has ord ≥ 1.
- **How**: Rewrites A via `A_factorization_at_2tor`; uses `one_le_ord_P_y_gen_sub_negY_const`, `one_le_ord_P_x_gen_sub_const`, `ord_P_mul`, `ord_P_add_le`.
- **Used by**: `ord_P_translateSlope_xy_le_neg_one_at_2tor`
- **Visibility**: public
- **Lines**: 2597–2637, proof 40 lines
- **Notes**: >30 lines

### `theorem polynomialX_evalEval_ne_zero_at_2tor`
- **Type**: `yk = negY xk yk → polynomialX.evalEval xk yk ≠ 0`
- **What**: `polynomialX` does not vanish at smooth 2-torsion points.
- **How**: `polynomialY = 0` from 2-torsion condition; then `Nonsingular` forces `polynomialX ≠ 0`.
- **Used by**: `maximalIdeal_localRingAt_eq_span_YClass_of_2_tor` (inlined), `ord_P_B_minus_a1_yk_decomposed_eq_zero_at_2tor`
- **Visibility**: public
- **Lines**: 2650–2661, proof 11 lines

### `private theorem B_minus_a1_yk_decomposition`
- **Type**: `B − a₁yk = (x_gen − xk)(x_gen + (2xk + a₂)) + (3xk² + 2a₂xk + a₄ − a₁yk)`
- **What**: Decomposition of the B-factor.
- **How**: `push_cast` + `ring`.
- **Used by**: `ord_P_B_minus_a1_yk_eq_zero_at_2tor`
- **Visibility**: private
- **Lines**: 2675–2687, proof 12 lines

### `theorem ord_P_B_minus_a1_yk_decomposed_eq_zero_at_2tor`
- **Type**: `yk = negY xk yk → ord_P(−T)(B-decomposed) = 0`
- **What**: The B-factor has exact order 0 at smooth 2-torsion.
- **How**: `polynomialX_evalEval_ne_zero_at_2tor` → C ≠ 0 → ord C = 0; `one_le_ord_P_x_gen_sub_const` → ord of product ≥ 1; strict non-arch gives sum ord = 0.
- **Used by**: `ord_P_B_minus_a1_yk_eq_zero_at_2tor`
- **Visibility**: public
- **Lines**: 2696–2769, proof 73 lines
- **Notes**: >30 lines

### `theorem ord_P_B_minus_a1_yk_eq_zero_at_2tor`
- **Type**: `yk = negY xk yk → ord_P(−T)(B − a₁yk) = 0`
- **What**: Bridge from decomposed to original B-factor form.
- **How**: Rewrites via `B_minus_a1_yk_decomposition`.
- **Used by**: `ord_P_translateSlope_xy_le_neg_one_at_2tor`
- **Visibility**: public
- **Lines**: 2775–2787, proof 11 lines

### `theorem ord_P_translateSlope_xy_le_neg_one_at_2tor`
- **Type**: `yk = negY xk yk → ord_P(−T)(translateSlope_xy W xk yk) ≤ −1`
- **What**: Slope has a pole at `−T` for 2-torsion `T`.
- **How**: Curve identity → slope = B/A; `A ≠ 0` from B ≠ 0; `ord_P_mul + ord_P_inv + ord_P_add_eq_of_lt`.
- **Uses from project**: `curve_identity_translate`, `one_le_ord_P_A_at_2tor`, `ord_P_B_minus_a1_yk_eq_zero_at_2tor`, `translateSlope_xy_eq`, `x_gen_sub_const_ne_zero`
- **Used by**: `ord_P_translateX_xy_lt_zero_at_2tor`
- **Visibility**: public
- **Lines**: 2799–2858, proof 59 lines
- **Notes**: >30 lines

### `theorem ord_P_translateX_xy_lt_zero_at_2tor`
- **Type**: `yk = negY xk yk → ord_P(−T)(translateX_xy W xk yk) < 0`
- **What**: `translateX_xy` has a pole at `−T` for 2-torsion `T`.
- **How**: Decomposes `translateX_xy = slope² + rest`; uses slope bound `≤ −1` and `ord_P_add_eq_of_lt` (dominant = slope²); case-split on `ord_P slope = ↑n` and omega.
- **Uses from project**: `ord_P_translateSlope_xy_le_neg_one_at_2tor`, `x_gen_sub_const_ne_zero`, `ord_P_algebraMap_F_nonneg`, `ord_P_x_gen_nonneg`
- **Used by**: `translateX_xy_transcendental_2tor`, `translateX_xy_ne_x_gen_2tor`
- **Visibility**: public
- **Lines**: 2880–2997, proof 117 lines
- **Notes**: >30 lines

### `theorem translateX_xy_transcendental_2tor`
- **Type**: `yk = negY xk yk → Transcendental F (translateX_xy W xk yk)`
- **What**: Transcendence for 2-torsion case.
- **How**: `transcendental_of_neg_ord_P` applied to `ord_P_translateX_xy_lt_zero_at_2tor`.
- **Used by**: `translateAlgHom_of_2tor`, `translateX_xy_ne_algebraMap_2tor`, `translateX_xy_2tor_ne_algebraMap_any`
- **Visibility**: public
- **Lines**: 3004–3009, proof 2 lines

---

## Section 6: AlgHom for 2-torsion and round-trips (lines 3011–3245)

### `noncomputable def translateAlgHom_of_2tor`
- **Type**: `yk = negY xk yk → (KE →ₐ[F] KE)`
- **What**: Translation AlgHom for 2-torsion `T`.
- **How**: Same as `translateAlgHom_of_nonTorsion` but using `translateX_xy_transcendental_2tor`.
- **Used by**: `translateAlgHom_of_2tor_apply_x_gen`, `translateAlgHom_of_2tor_apply_y_gen`, `translateAlgEquiv_of_2tor`, and all 2-torsion group-hom branch theorems
- **Visibility**: public
- **Lines**: 3019–3026, proof 5 lines

### `theorem translateAlgHom_of_2tor_apply_x_gen`
- **Type**: `translateAlgHom_of_2tor W xk yk h_ns h_2_tor (x_gen W) = translateX_xy W xk yk`
- **What**: Action of the 2-torsion AlgHom on `x_gen`.
- **How**: Same unfolding as `translateAlgHom_apply_x_gen`.
- **Used by**: round-trips and group-hom branch theorems (referenced many times)
- **Visibility**: public
- **Lines**: 3036–3058, proof 22 lines

### `theorem translateX_xy_ne_algebraMap_2tor`
- **Type**: `yk = negY xk yk → translateX_xy W xk yk ≠ algebraMap F KE xk`
- **What**: 2-torsion x-translate avoids `xk`.
- **Used by**: `translateAlgHom_of_2tor_round_trip_x_gen`, `translateAlgHom_of_2tor_round_trip_y_gen`, `liftSomePoint_add_self_eq_zero_of_2tor`, `translateAlgEquivOfPoint_add`
- **Visibility**: public
- **Lines**: 3062–3069, proof 7 lines

### `theorem translateX_xy_2tor_ne_algebraMap_any`
- **Type**: `yk = negY xk yk → ∀ c, translateX_xy W xk yk ≠ algebraMap F KE c`
- **What**: 2-torsion x-translate avoids all F-constants.
- **Used by**: `translateX_xy_ne_algebraMap_any`
- **Visibility**: public
- **Lines**: 3074–3081, proof 7 lines

### `theorem translateX_xy_nonTor_ne_algebraMap_any`
- **Type**: `yk ≠ negY xk yk → ∀ c, translateX_xy W xk yk ≠ algebraMap F KE c`
- **What**: Non-2-torsion x-translate avoids all F-constants.
- **Used by**: `translateX_xy_ne_algebraMap_any`
- **Visibility**: public
- **Lines**: 3085–3092, proof 7 lines

### `theorem translateX_xy_ne_algebraMap_any`
- **Type**: `W.toAffine.Nonsingular xk yk → ∀ c, translateX_xy W xk yk ≠ algebraMap F KE c`
- **What**: For any nonsingular point `T`, `translateX_xy` avoids all F-constants (unifying 2-tor and non-2-tor).
- **How**: Case-split on `yk = negY xk yk`; delegates to the two special cases.
- **Used by**: `translateAlgEquivOfPoint_add` (discharge of `h_x₂_ne`)
- **Visibility**: public
- **Lines**: 3096–3101, proof 5 lines

### `theorem liftSomePoint_add_self_eq_zero_of_2tor`
- **Type**: `yk = negY xk yk → liftSomePoint W xk yk h_ns + liftSomePoint W xk yk h_ns = 0`
- **What**: `T + T = 0` for 2-torsion `T` at the lifted level.
- **How**: `Affine.Point.add_self_of_Y_eq` + `map_negY` + `h_2_tor`.
- **Used by**: `translateAlgHom_of_2tor_round_trip_x_gen`, `translateAlgHom_of_2tor_round_trip_y_gen`, `translateAlgEquivOfPoint_2tor_add_self`
- **Visibility**: public
- **Lines**: 3113–3124, proof 10 lines

### `theorem translateAlgHom_of_2tor_apply_y_gen`
- **Type**: `translateAlgHom_of_2tor W xk yk h_ns h_2_tor (y_gen W) = translateY_xy W xk yk`
- **What**: Action on `y_gen` for 2-torsion AlgHom.
- **Used by**: round-trip and group-hom branch theorems
- **Visibility**: public
- **Lines**: 3127–3144, proof 17 lines

### `theorem translateAlgHom_of_2tor_round_trip_x_gen`
- **Type**: `τ(τ(x_gen W)) = x_gen W` for 2-torsion τ
- **What**: Self-inverse property on `x_gen`.
- **How**: Parallel of `translateAlgHom_round_trip_x_gen` using `liftSomePoint_add_self_eq_zero_of_2tor`.
- **Used by**: `translateAlgEquiv_of_2tor`
- **Visibility**: public
- **Lines**: 3156–3199, proof 43 lines
- **Notes**: >30 lines

### `theorem translateAlgHom_of_2tor_round_trip_y_gen`
- **Type**: `τ(τ(y_gen W)) = y_gen W` for 2-torsion τ
- **What**: Self-inverse property on `y_gen`.
- **Used by**: `translateAlgEquiv_of_2tor`
- **Visibility**: public
- **Lines**: 3203–3245, proof 42 lines
- **Notes**: >30 lines

---

## Section 7: AlgEquiv constructions and the unified point action (lines 3247–3530)

### `noncomputable def translateAlgEquiv_of_2tor`
- **Type**: `yk = negY xk yk → (KE ≃ₐ[F] KE)`
- **What**: Self-inverse AlgEquiv for 2-torsion `T`.
- **How**: `AlgEquiv.ofAlgHom` with identical forward and backward map; uses `algHom_ext_x_y_gen` for the round-trips.
- **Used by**: `translateAlgEquivOfPoint` (the `.some 2-tor` case), `translateAlgEquiv_of_2tor_symm`, `translateAlgEquiv_of_2tor_self_trans`, `translateAlgEquivOfPoint_2tor_add_self`, `translateAlgEquivOfPoint_add_2tor_main`, etc.
- **Visibility**: public
- **Lines**: 3255–3271, proof 15 lines

### `noncomputable def translateAlgEquiv`
- **Type**: `yk ≠ negY xk yk → (KE ≃ₐ[F] KE)`
- **What**: AlgEquiv for non-2-torsion `T`, with inverse = translation by `−T`.
- **How**: `AlgEquiv.ofAlgHom` with `translateAlgHom_of_nonTorsion` and `_neg`; uses all four round-trips.
- **Used by**: `translateAlgEquivOfPoint` (the `.some non-2-tor` case), `translateAlgEquiv_symm_eq_neg_point`, `translateAlgEquivOfPoint_nonTor_add_neg`, many group-hom branch theorems
- **Visibility**: public
- **Lines**: 3284–3300, proof 16 lines

### `noncomputable def translateAlgEquivOfPoint`
- **Type**: `W.toAffine.Point → (KE ≃ₐ[F] KE)`
- **What**: Unified translation AlgEquiv for any point of `E(F)`: identity at zero, 2-tor variant at 2-torsion, non-2-tor variant otherwise.
- **How**: Pattern match on `Affine.Point`; `dif_pos/neg` on the 2-torsion condition.
- **Used by**: Nearly everything downstream (48 refs to `translateAlgEquivOfPoint_add` alone, plus 48+ to the definition itself)
- **Visibility**: public
- **Lines**: 3320–3327, proof pattern-matching def

### `@[simp] theorem translateAlgEquivOfPoint_zero`
- **Type**: `translateAlgEquivOfPoint W .zero = AlgEquiv.refl`
- **Used by**: `translateAlgEquivOfPoint_zero_apply`, `translateAlgEquivOfPoint_zero_add`, `translateAlgEquivOfPoint_zero_toAlgHom`, `translateAlgEquivOfPoint_eq_refl_iff_zero`
- **Visibility**: public
- **Lines**: 3329–3330, proof 1 line

### `theorem translateAlgEquivOfPoint_some_2tor`
- **Type**: `yk = negY xk yk → translateAlgEquivOfPoint W (.some xk yk h_ns) = translateAlgEquiv_of_2tor W xk yk h_ns h_2_tor`
- **Used by**: master group-hom theorems; `translateAlgEquivOfPoint_2tor_add_self`, `translateAlgEquivOfPoint_add`
- **Visibility**: public
- **Lines**: 3332–3338, proof 3 lines

### `theorem translateAlgEquivOfPoint_some_nonTor`
- **Type**: `yk ≠ negY xk yk → translateAlgEquivOfPoint W (.some xk yk h_ns) = translateAlgEquiv W xk yk h_ns h_not_2_tor`
- **Used by**: master group-hom theorems; `translateAlgEquivOfPoint_nonTor_add_neg`, `translateAlgEquivOfPoint_add`
- **Visibility**: public
- **Lines**: 3340–3346, proof 3 lines

### `@[simp] theorem translateAlgEquivOfPoint_zero_apply`
- **Type**: `translateAlgEquivOfPoint W .zero f = f`
- **Visibility**: public; **Lines**: 3351–3352, proof 1 line

### `theorem translateAlgEquivOfPoint_zero_toAlgHom`
- **Type**: `(translateAlgEquivOfPoint W .zero).toAlgHom = AlgHom.id F KE`
- **Used by**: (unused inside file)
- **Visibility**: public; **Lines**: 3356–3359, proof 3 lines

### `theorem translateAlgEquivOfPoint_zero_add`
- **Type**: `translateAlgEquivOfPoint W (0 + T) = (refl).trans (translateAlgEquivOfPoint W T)`
- **Visibility**: public; **Lines**: 3373–3381, proof 7 lines

### `theorem translateAlgEquivOfPoint_add_zero`
- **Type**: `translateAlgEquivOfPoint W (T + 0) = (translateAlgEquivOfPoint W T).trans refl`
- **Visibility**: public; **Lines**: 3385–3393, proof 7 lines

### `noncomputable def liftPointToKE`
- **Type**: `W.toAffine.Point →+ (W_KE W).toAffine.Point`
- **What**: Abstract lift of F-points to KE-points as a group hom.
- **How**: `WeierstrassCurve.Affine.Point.map (Algebra.ofId F KE)`.
- **Used by**: `liftPointToKE_zero`, `liftPointToKE_add`, `liftPointToKE_some`, and the group-hom branch theorems (all use it to lift `h_sum`)
- **Visibility**: public
- **Lines**: 3404–3406, proof 1 line

### `@[simp] theorem liftPointToKE_zero`; `theorem liftPointToKE_add`; `theorem liftPointToKE_some`
- **What**: Basic properties of `liftPointToKE`.
- **Lines**: 3409–3424, each 1–2 lines

### `theorem neg_some_eq_some`
- **Type**: `-(.some xk yk h_ns) = .some xk (negY xk yk) ((nonsingular_neg).mpr h_ns)`
- **Used by**: `translateAlgEquivOfPoint_add`, `sum_2tor_of_2tor_2tor`, `sum_nonTor_of_2tor_nonTor`, `sum_nonTor_of_nonTor_2tor`
- **Visibility**: public; **Lines**: 3428–3432, proof 1 line

### `theorem sum_2tor_of_2tor_2tor`; `theorem sum_nonTor_of_2tor_nonTor`; `theorem sum_nonTor_of_nonTor_2tor`
- **What**: 2-torsion closure lemmas: sum of two 2-tor points is 2-tor; sum of 2-tor + non-2-tor is non-2-tor.
- **How**: Uses `Affine.Point.add_self_of_Y_eq` + `add_eq_zero_iff_eq_neg` + `neg_some_eq_some` + `abel`; extracts coordinate from `Point.some.injEq`.
- **Used by**: `translateAlgEquivOfPoint_add`
- **Visibility**: public
- **Lines**: 3436–3530, proofs ~28 lines each

---

## Section 8: Group-hom property for `translateAlgEquivOfPoint` (lines 3532–4370)

*This section contains ~25 theorems proving the group-hom property in all cases (2-tor/non-2-tor combinations). The pattern is highly repetitive: `set σ`, apply `translateAlgHom_of_*_apply_x_gen`, unfold `translateX_xy`, apply `σ_commutes_addX`, slope commutation, then use the group-law identity via `genericPoint_add_liftSomePoint` + `liftPointToKE_add` + `Affine.Point.add_of_X_ne`.*

### `theorem translateAlgEquiv_of_2tor_symm`
- **Type**: `(translateAlgEquiv_of_2tor W xk yk h_ns h_2_tor).symm = translateAlgEquiv_of_2tor W xk yk h_ns h_2_tor`
- **Visibility**: public; **Lines**: 3543–3550, proof 3 lines

### `theorem translateAlgEquiv_of_2tor_self_trans`
- **Type**: `τ.trans τ = AlgEquiv.refl` for 2-torsion τ
- **Visibility**: public; **Lines**: 3554–3561, proof 4 lines

### `theorem translateAlgEquivOfPoint_2tor_add_self`
- **Type**: `translateAlgEquivOfPoint W (T + T) = (τ_T).trans (τ_T)` for 2-tor T
- **Visibility**: public; **Lines**: 3566–3582, proof 16 lines

### `theorem translateAlgEquiv_symm_eq_neg_point`
- **Type**: `(translateAlgEquiv W xk yk h_ns h_not_2_tor).symm = translateAlgEquivOfPoint W (-(some xk yk h_ns))`
- **Visibility**: public; **Lines**: 3593–3609, proof 16 lines

### `theorem translateAlgEquivOfPoint_nonTor_add_neg`
- **Type**: `translateAlgEquivOfPoint W (T + (-T)) = (τ_T).trans (τ_{-T})` for non-2-tor T
- **Visibility**: public; **Lines**: 3613–3630, proof 17 lines

### Substantive group-hom on generators (8 theorems, all with `set_option maxHeartbeats 400000`)
Each proves `τ_{T₂}(τ_{T₁}(x_gen or y_gen)) = x or y coord of T₃` where `T₁ + T₂ = T₃` (non-zero). Covers all combinations: both nonTor, both 2-tor, mixed 2-tor+nonTor, mixed nonTor+2-tor. The key step is the group-law identity `(gen + lift T₂) + lift T₁ = gen + lift T₃` using `liftPointToKE_add`.

- **Lines**: 3641–4117
- **Notes**: All have `set_option maxHeartbeats 400000` — NO-COMMENT; all >30 lines

### Master assembler theorems (7 theorems)
`translateAlgEquivOfPoint_add_nonTor_main`, `_add_nonTor_main_2torSum`, `_add_nonTor_2tor_main`, `_add_2tor_nonTor_main`, `_add_2tor_main`; each assembles x+y results into an AlgEquiv equality via `AlgEquiv.coe_algHom_injective` + `algHom_ext_x_y_gen`.

- **Lines**: 4120–4288

### `theorem translateAlgEquivOfPoint_add`
- **Type**: `∀ T₁ T₂, translateAlgEquivOfPoint W (T₁ + T₂) = (τ_{T₁}).trans (τ_{T₂})`
- **What**: Master group-hom theorem; the unified composition law. Cases: T₁=0, T₂=0, sum=0 (2-tor or non-2-tor), sum≠0 (all 4 combinations of torsion type). Dispatches via `rcases`, `by_cases` and delegates to master assemblers. Uses `translateX_xy_ne_algebraMap_any` to discharge `h_x₂_ne` automatically.
- **Uses from project**: all master assembler theorems, `sum_2tor_of_2tor_2tor`, `sum_nonTor_of_*`, `translateAlgEquivOfPoint_zero_add`, `translateAlgEquivOfPoint_add_zero`, `translateAlgEquivOfPoint_2tor_add_self`, `translateAlgEquivOfPoint_nonTor_add_neg`, `translateX_xy_ne_algebraMap_any`
- **Used by**: `translateAlgEquivOfPoint_add_apply`, `translateMulSemiringAction`, `translateAlgEquivOfPoint_injective`
- **Visibility**: public
- **Lines**: 4312–4367, proof 55 lines
- **Notes**: >30 lines; the crowning group-hom result

### `theorem translateAlgEquivOfPoint_add_apply`
- **Type**: `translateAlgEquivOfPoint W (S₁ + S₂) x = τ_{S₂}(τ_{S₁}(x))`
- **What**: Pointwise form of the group-hom theorem.
- **Visibility**: public; **Lines**: 4372–4375, proof 2 lines

### `noncomputable instance translateMulSemiringAction`
- **Type**: `MulSemiringAction (Multiplicative W.toAffine.Point) KE`
- **What**: Packages the group action as a `MulSemiringAction` typeclass instance.
- **How**: Ring-hom axioms from `map_zero/add/one/mul` of AlgEquiv; `mul_smul` uses `translateAlgEquivOfPoint_add` + `add_comm`.
- **Used by**: potential consumers of `MulSemiringAction` typeclass
- **Visibility**: public
- **Lines**: 4389–4411, proof 22 lines

---

## Section 9: Injectivity and Step (B)/(C) framework (lines 4413–5636)

### `theorem translateX_xy_ne_x_gen_nonTor`; `theorem translateX_xy_ne_x_gen_2tor`
- **What**: `translateX_xy ≠ x_gen` via ord comparison at `−T`.
- **Used by**: `translateAlgEquivOfPoint_some_ne_refl`
- **Visibility**: public; **Lines**: 4428–4456

### `theorem translateAlgEquivOfPoint_some_ne_refl`
- **Type**: `∀ xk yk h_ns, translateAlgEquivOfPoint W (.some xk yk h_ns) ≠ AlgEquiv.refl`
- **What**: Every non-zero point acts non-trivially on `K(E)`.
- **Used by**: `translateAlgEquivOfPoint_eq_refl_iff_zero`
- **Visibility**: public; **Lines**: 4461–4487

### `theorem translateAlgEquivOfPoint_eq_refl_iff_zero`
- **Type**: `translateAlgEquivOfPoint W T = AlgEquiv.refl ↔ T = 0`
- **What**: Trivial kernel.
- **Used by**: `translateAlgEquivOfPoint_injective`
- **Visibility**: public; **Lines**: 4493–4501

### `theorem translateAlgEquivOfPoint_injective`
- **Type**: `Function.Injective (translateAlgEquivOfPoint W)`
- **What**: Distinct points give distinct automorphisms.
- **How**: Group-hom property + trivial kernel.
- **Used by**: (unused inside file; key public API)
- **Visibility**: public; **Lines**: 4508–4537

### Step (B'')/Step (C) framework (lines 4539–5636)

This section defines and provides tools for the valuation-transport obligation. It introduces:
- `IsTranslateValuationCompatible` (def, line 4660): `(pointValuation P).comap τ_k = pointValuation(P+k)`
- `IsTranslateLocalRingCompatible` (def, line 4757): ≤1 iff form
- `IsTranslateMaxIdealCompatible` (def, line 4804): <1 iff form
- `IsTranslateMaxIdealCompatible_on_CoordinateRing` (def, line 4881): restricted to CoordinateRing elements
- `IsTranslateXY_evaluatesAt` (def, line 4974): named obligation for the x_gen/y_gen evaluation witnesses
- `IsTranslateOrdAtInftyCompatible` (def, line 5226): `ord_P(τ_k f) = ordAtInfty f` when P+k=0

And a rich set of structural lemmas:
- Base cases at k=0 (discharged unconditionally)
- Bridges between formulations (IsEquiv, iff, pointwise, comap)
- Ore/Piece 3/4/5 bridges from various hypotheses to `IsTranslateValuationCompatible`
- Step (C) bridges for `ordAtInfty`: multiplication, power, inverse, division, addition, subtraction, negation, scalar multiplication, dominant-sum combinator (`ord_P_translateAlgEquivOfPoint_sum_dominant`)

**All definitions are non-sorry.** The obligations are Prop-valued "named hypotheses" to be discharged by downstream workers.

---

## Summary table of `set_option maxHeartbeats` occurrences

| Declaration | Value | Comment present? |
|---|---|---|
| `maximalIdeal_localRingAt_eq_span_XClass_of_non_2_tor` (line 321) | 1600000 | NO-COMMENT |
| `maximalIdeal_localRingAt_eq_span_YClass_of_2_tor` (line 625) | 1600000 | NO-COMMENT |
| `ord_P_translateY_xy_eq_neg_three_of_non_2_tor` (line 1530) | 1600000 | NO-COMMENT |
| `translateAlgEquivOfPoint_add_nonTor_x_gen` (line 3641) | 400000 | NO-COMMENT |
| `translateAlgEquivOfPoint_add_nonTor_y_gen` (line 3702) | 400000 | NO-COMMENT |
| `translateAlgEquivOfPoint_add_2tor_x_gen` (line 3768) | 400000 | NO-COMMENT |
| `translateAlgEquivOfPoint_add_2tor_y_gen` (line 3826) | 400000 | NO-COMMENT |
| `translateAlgEquivOfPoint_add_2tor_nonTor_x_gen` (line 3891) | 400000 | NO-COMMENT |
| `translateAlgEquivOfPoint_add_2tor_nonTor_y_gen` (line 3948) | 400000 | NO-COMMENT |
| `translateAlgEquivOfPoint_add_nonTor_2tor_x_gen` (line 4005) | 400000 | NO-COMMENT |
| `translateAlgEquivOfPoint_add_nonTor_2tor_y_gen` (line 4062) | 400000 | NO-COMMENT |
