# Inventory: ./HasseWeil/AdditionPullback/SilvermanIV14.lean

**File summary**: 3859 lines, 167 theorems (0 defs, 0 instances), 0 sorries.
Imports: `HasseWeil.AdditionPullback.Differential`, `HasseWeil.BridgeFrobenius`, `HasseWeil.HahnSeriesAux`.

The file is a major computation hub for Silverman IV.1.4 and III.5.2: it proves
`isogOneSub_negFrobenius_isSeparable` (Witness #1 of the Hasse bound) and
`kaehler_D_addPullback_x_pair_eq_smul_omega` (general-pair III.5.2 differential
collapse), plus a large library of auxiliary `orderTop`/`leadingCoeff`/Kähler
differential helpers. Two `set_option maxHeartbeats 4000000` occurrences at lines
3306 and 3755.

---

## Group 1: Order at infinity for negFrobenius pullback of localParam

### `theorem ord_neg_addPullback_x_div_y_negFrobenius`
- **Type**: `(h_x : ord(addPullback_x) = -2) → (h_y : ord(addPullback_y) = -3) → ordAtInfty(-addPullback_x / addPullback_y) = 1`
- **What**: Witness-parametric: given the orders of the x and y coordinates of the negFrobenius addition-pullback at infinity, the order of their ratio `-x/y` (= local parameter pullback) is `1 = -2 - (-3)`.
- **How**: Uses `ordAtInfty_neg` for the numerator sign, then `ord_div_concrete` for the division formula.
- **Hypotheses**: `hx`, `hy` carried as parameters; nonzero from finite ord.
- **Uses from project**: `(W_smooth W).ordAtInfty_neg`, `(W_smooth W).ord_div_concrete`
- **Used by**: `ord_neg_addPullback_x_div_y_negFrobenius_unconditional`
- **Visibility**: public
- **Lines**: 88–107, proof 20 lines
- **Notes**: witness-parametric scaffold

### `theorem ord_neg_addPullback_x_div_y_negFrobenius_unconditional`
- **Type**: `(hq : 2 ≤ Fintype.card K) → ordAtInfty(-addPullback_x W (negFrobeniusIsog W) / addPullback_y W (negFrobeniusIsog W)) = 1`
- **What**: Unconditional form: combines the x-ord and y-ord witnesses (both axiom-clean from `Frobenius.lean`) with the parametric lemma above.
- **How**: Applies `ord_addPullback_x_negFrobenius` and `ord_addPullback_y_negFrobenius` to `ord_neg_addPullback_x_div_y_negFrobenius`.
- **Uses from project**: `ord_neg_addPullback_x_div_y_negFrobenius`, `ord_addPullback_x_negFrobenius`, `ord_addPullback_y_negFrobenius`
- **Used by**: unused in file (no internal callers)
- **Visibility**: public
- **Lines**: 118–126, proof 4 lines

### `theorem negFrobeniusIsog_pullback_localParam_eq_pow`
- **Type**: `(negFrobeniusIsog W).pullback (localParam W) = ((mulByInt W.toAffine (-1)).pullback (localParam W)) ^ Fintype.card K`
- **What**: The negFrobenius pullback of the local parameter factors as the q-th power of the `mulByInt(-1)` pullback, using `negFrob = mulByInt(-1) ∘ frobenius`.
- **How**: `Isogeny.comp_algebraMap_eq` + `frobeniusIsog_pullback_apply` (q-power).
- **Uses from project**: `Isogeny.comp_algebraMap_eq`, `frobeniusIsog_pullback_apply`
- **Used by**: `coeff_one_formalIsogenySeries_negFrobeniusIsog_of_orderTop_witness`, `constantCoeff_formalIsogenySeries_negFrobeniusIsog`
- **Visibility**: public
- **Lines**: 138–143, proof 3 lines

### `theorem mulByInt_neg_one_pullback_localParam`
- **Type**: `(mulByInt W.toAffine (-1)).pullback (localParam W) = x_gen W / (y_gen W + a₁·x_gen W + a₃)`
- **What**: Closed form for the `[-1]`-pullback of the local parameter at infinity: `σ(t) = x/(y + a₁x + a₃)`.
- **How**: Unfolds `localParam = -x/y`, applies `mulByInt_pullback_x_neg_one` (fixes x) and `mulByInt_pullback_y_neg_one` (sends y to `-y-a₁x-a₃`), then cancels double negation via `neg_div_neg_eq`.
- **Uses from project**: `localParam`, `mulByInt_pullback_x_neg_one`, `mulByInt_pullback_y_neg_one`
- **Used by**: `orderTop_localExpand_mulByInt_neg_one_pullback_localParam`
- **Visibility**: public
- **Lines**: 149–160, proof 12 lines

### `theorem ord_negFrobeniusIsog_pullback_localParam`
- **Type**: `(hq : 2 ≤ Fintype.card K) → ordAtInfty((negFrobeniusIsog W).pullback (localParam W)) = q`
- **What**: The order of the negFrobenius pullback of the local parameter at infinity is `q = #K`.
- **How**: Uses the x and y pullback orders (`ordAtInfty_negFrobeniusIsog_pullback_x/y_gen`), computes `(-2q) - (-3q) = q` via `ord_div_concrete`.
- **Uses from project**: `ordAtInfty_negFrobeniusIsog_pullback_x_gen`, `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `(W_smooth W).ord_div_concrete`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 172–199, proof 28 lines

---

## Group 2: constantCoeff of formalIsogenySeries

### `@[simp] theorem constantCoeff_formalIsogenySeries_id`
- **Type**: `PowerSeries.constantCoeff (formalIsogenySeries W (Isogeny.id W.toAffine)) = 0`
- **What**: The constant term of the formal power series for the identity isogeny is 0 (since `formalIsogenySeries_id = X`).
- **How**: Direct from `formalIsogenySeries_id = X` and `constantCoeff_X`.
- **Uses from project**: `formalIsogenySeries_id`
- **Used by**: `coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_via_bridge_003`, `constantCoeff_formalIsogenySeries_negFrobeniusIsog`
- **Visibility**: public (`@[simp]`)
- **Lines**: 211–213, proof 2 lines

### `@[simp] theorem constantCoeff_formalIsogenySeries_frobenius`
- **Type**: `(1 ≤ Fintype.card K) → constantCoeff (formalIsogenySeries W (frobeniusIsog W)) = 0`
- **What**: The constant term for the Frobenius is 0 since `formalIsogenySeries_frobenius = X^q` and `q ≥ 1 > 0`.
- **How**: `formalIsogenySeries_frobenius` + `coeff_X_pow` + `if_neg (by omega)`.
- **Uses from project**: `formalIsogenySeries_frobenius`
- **Used by**: unused in file (no internal callers)
- **Visibility**: public (`@[simp]`)
- **Lines**: 217–222, proof 6 lines

---

## Group 3: orderTop of localExpand of denominator of σ(t)

### `private theorem orderTop_a₁_formalX_plus_a₃_ge_neg_two`
- **Type**: `-2 ≤ orderTop (C a₁ * formalX + C a₃ : LaurentSeries K)`
- **What**: The two lower-order terms of the local-parameter denominator have orderTop ≥ -2.
- **How**: `min_orderTop_le_orderTop_add` + case analysis on `a₁ = 0` / `a₃ = 0` + `orderTop_single`.
- **Uses from project**: `formalX_orderTop`
- **Used by**: `orderTop_localExpand_y_gen_plus_a₁_x_gen_plus_a₃`
- **Visibility**: private
- **Lines**: 233–252, proof 20 lines

### `theorem orderTop_localExpand_y_gen_plus_a₁_x_gen_plus_a₃`
- **Type**: `orderTop (formalY W + C a₁ * formalX W + C a₃ : LaurentSeries K) = -3`
- **What**: The denominator `y + a₁x + a₃` of σ(t) has orderTop -3 in Laurent series, since formalY (orderTop -3) strictly dominates the rest (orderTop ≥ -2).
- **How**: `orderTop_add_eq_left` with strict inequality from `orderTop_a₁_formalX_plus_a₃_ge_neg_two` and `formalY_orderTop`.
- **Uses from project**: `formalY_orderTop`, `orderTop_a₁_formalX_plus_a₃_ge_neg_two`
- **Used by**: `orderTop_localExpand_mulByInt_neg_one_pullback_localParam`
- **Visibility**: public
- **Lines**: 258–270, proof 13 lines

### `theorem orderTop_localExpand_mulByInt_neg_one_pullback_localParam`
- **Type**: `orderTop (localExpand W ((mulByInt W.toAffine (-1)).pullback (localParam W))) = 1`
- **What**: The σ-image of the local parameter has orderTop 1 in Laurent series: from `σ(t) = formalX/denom` with `orderTop(formalX) = -2` and `orderTop(denom) = -3`, concludes `-2 - (-3) = 1`.
- **How**: Rewrites via `mulByInt_neg_one_pullback_localParam`, applies `map_div₀`, then uses `orderTop_mul` on `(formalX/denom)*denom = formalX` to extract the orderTop.
- **Uses from project**: `mulByInt_neg_one_pullback_localParam`, `orderTop_localExpand_y_gen_plus_a₁_x_gen_plus_a₃`, `formalX_orderTop`, `localExpand_x_gen`, `localExpand_y_gen`, `localExpand_algebraMap`
- **Used by**: `coeff_one_formalIsogenySeries_negFrobeniusIsog_of_orderTop_witness`, `constantCoeff_formalIsogenySeries_negFrobeniusIsog`, `coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero`
- **Visibility**: public
- **Lines**: 281–321, proof 41 lines
- **Notes**: Proof >30 lines (41); the orderTop extraction is a manual `WithTop ℤ` linear-arithmetic argument

---

## Group 4: coeff 1 of formalIsogenySeries negFrobeniusIsog

### `theorem coeff_one_formalIsogenySeries_negFrobeniusIsog_of_orderTop_witness`
- **Type**: `(hq : 2 ≤ Fintype.card K) → (h_orderTop : 1 ≤ localExpand(σ(localParam)).orderTop) → coeff 1 (formalIsogenySeries W (negFrobeniusIsog W)) = 0`
- **What**: Parametric: given orderTop ≥ 1 of the σ-image, the q-th power has orderTop ≥ q ≥ 2, so coeff 1 = 0.
- **How**: Rewrites via `formalIsogenySeries_coeff` + `negFrobeniusIsog_pullback_localParam_eq_pow` + `map_pow`, then uses `HahnSeries.orderTop_nsmul_le_orderTop_pow` and `HahnSeries.coeff_eq_zero_of_lt_orderTop`.
- **Uses from project**: `formalIsogenySeries_coeff`, `negFrobeniusIsog_pullback_localParam_eq_pow`, `HahnSeries.orderTop_nsmul_le_orderTop_pow`, `HahnSeries.coeff_eq_zero_of_lt_orderTop`
- **Used by**: `coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero`
- **Visibility**: public
- **Lines**: 336–363, proof 28 lines

### `@[simp] theorem constantCoeff_formalIsogenySeries_negFrobeniusIsog`
- **Type**: `(hq : 1 ≤ Fintype.card K) → constantCoeff (formalIsogenySeries W (negFrobeniusIsog W)) = 0`
- **What**: Constant coefficient of the formal series for `-π` is 0 (genuine isogeny, order ≥ q ≥ 1 > 0).
- **How**: Same orderTop power inequality as the `coeff_one` version but for `coeff 0`.
- **Uses from project**: `formalIsogenySeries_coeff`, `negFrobeniusIsog_pullback_localParam_eq_pow`, `orderTop_localExpand_mulByInt_neg_one_pullback_localParam`, `HahnSeries.orderTop_nsmul_le_orderTop_pow`, `HahnSeries.coeff_eq_zero_of_lt_orderTop`
- **Used by**: `coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_via_bridge_003`
- **Visibility**: public (`@[simp]`)
- **Lines**: 372–397, proof 26 lines

### `theorem coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero`
- **Type**: `(hq : 2 ≤ Fintype.card K) → coeff 1 (formalIsogenySeries W (negFrobeniusIsog W)) = 0`
- **What**: Unconditional: discharges the orderTop witness in the parametric form using `orderTop_localExpand_mulByInt_neg_one_pullback_localParam = 1`.
- **How**: Direct application of `coeff_one_formalIsogenySeries_negFrobeniusIsog_of_orderTop_witness` with `.symm.le`.
- **Uses from project**: `coeff_one_formalIsogenySeries_negFrobeniusIsog_of_orderTop_witness`, `orderTop_localExpand_mulByInt_neg_one_pullback_localParam`
- **Used by**: `omegaPullbackCoeff_eq_formalIsogenyLeading_negFrobeniusIsog`, multiple scaffold theorems, `coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_via_bridge_003`, etc.
- **Visibility**: public
- **Lines**: 410–414, proof 3 lines

---

## Group 5: Bridge-001 for negFrobeniusIsog

### `theorem omegaPullbackCoeff_eq_formalIsogenyLeading_negFrobeniusIsog`
- **Type**: `(hq : 2 ≤ Fintype.card K) → omegaPullbackCoeff W (negFrobeniusIsog W) = algebraMap K KE (coeff 1 (formalIsogenySeries W (negFrobeniusIsog W)))`
- **What**: BRIDGE-001 for `-π`: both sides equal 0 (omega-coefficient vanishes for negFrobenius; coeff 1 = 0 from above).
- **How**: Rewrites coeff 1 = 0 via `coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero`, then `map_zero`, then `omegaPullbackCoeff_negFrobeniusIsog` (which says the coeff = 0).
- **Uses from project**: `coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero`, `omegaPullbackCoeff_negFrobeniusIsog`
- **Used by**: `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_bridge_and_leading`
- **Visibility**: public
- **Lines**: 428–434, proof 6 lines

---

## Group 6: Scaffold closers for isogOneSub_negFrobenius (witness-parametric on BRIDGE-001/003)

### `theorem coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_of_witnesses`
- **Type**: `(hq) → (h_add : coeff 1 (formal γ) = coeff 1 (formal id) + coeff 1 (formal negFrob)) → (h_negfrob : coeff 1 (formal negFrob) = 0) → coeff 1 (formal γ) = 1`
- **What**: Scaffold: given additivity and vanishing of the negFrob term, `1 + 0 = 1`.
- **How**: `rw [h_add, coeff_one_formalIsogenySeries_id, h_negfrob, add_zero]`.
- **Uses from project**: `coeff_one_formalIsogenySeries_id`
- **Used by**: `coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_of_h_add`
- **Visibility**: public
- **Lines**: 453–463, proof 2 lines

### `theorem coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_of_h_add`
- **Type**: `(hq) → (h_add) → coeff 1 (formal isogOneSub_negFrobenius W hq) = 1`
- **What**: Same as above but with `h_negfrob` discharged unconditionally.
- **How**: Applies `coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_of_witnesses` with `coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 476–485, proof 3 lines

### `theorem coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_via_bridge_003`
- **Type**: `(hq) → (h_bridge_003 : formal γ = subst F (formal id, formal negFrob)) → coeff 1 (formal γ) = 1`
- **What**: Closes `coeff 1 = 1` given BRIDGE-003 (the formal group substitution identity), using `coeff_one_subst_bivariate` from `FormalIsogenySeries.lean`.
- **How**: Rewrites via `h_bridge_003`, applies `coeff_one_subst_bivariate` with formal group law leading coefficients and the constantCoeff witnesses.
- **Uses from project**: `coeff_one_subst_bivariate`, `formalGroupLaw_coeff_single_zero_one`, `formalGroupLaw_coeff_single_one_one`, `constantCoeff_formalGroupLaw`, `constantCoeff_formalIsogenySeries_id`, `constantCoeff_formalIsogenySeries_negFrobeniusIsog`, `coeff_one_formalIsogenySeries_id`, `coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero`
- **Used by**: `isogOneSub_negFrobenius_isSeparable_of_bridge_001_γ_and_bridge_003`, `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_bridge_001_γ_and_bridge_003`
- **Visibility**: public
- **Lines**: 504–525, proof 22 lines
- **Notes**: Proof >30 lines at 52 lines total (mostly signature)

### `theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_bridge_and_leading`
- **Type**: `(hq) → (h_bridge_γ) → (h_leading_add) → omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1`
- **What**: Witness #1 omega-coeff closer: with BRIDGE-001 for γ and leading-coefficient additivity, fires ω(γ) = 1.
- **How**: Applies `omegaPullbackCoeff_add_of_leading_witness` with BRIDGE-001 for id and negFrob, then `omegaPullbackCoeff_id` + `omegaPullbackCoeff_negFrobeniusIsog` + `add_zero`.
- **Uses from project**: `omegaPullbackCoeff_add_of_leading_witness`, `omegaPullbackCoeff_eq_formalIsogenyLeading_id`, `omegaPullbackCoeff_eq_formalIsogenyLeading_negFrobeniusIsog`, `omegaPullbackCoeff_id`, `omegaPullbackCoeff_negFrobeniusIsog`
- **Used by**: `isogOneSub_negFrobenius_isSeparable_of_bridge_and_leading`, `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_bridge_001_γ_and_bridge_003`
- **Visibility**: public
- **Lines**: 556–572, proof 17 lines

### `theorem isogOneSub_negFrobenius_isSeparable_of_bridge_and_leading`
- **Type**: `(hq) → (h_bridge_γ) → (h_leading_add) → (isogOneSub_negFrobenius W hq).IsSeparable`
- **What**: Witness #1 separability from BRIDGE-001 for γ + leading additivity.
- **How**: Routes through `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_bridge_and_leading` + `isogOneSub_negFrobenius_isSeparable_of_h_coeff_only`.
- **Used by**: `isogOneSub_negFrobenius_isSeparable_of_bridge_001_γ_and_bridge_003`, `isogOneSub_negFrobenius_isSeparable_via_y_lc_and_bridge_001`
- **Visibility**: public
- **Lines**: 580–592, proof 13 lines
- **Notes**: Proof >30 lines at 35 lines (including signature)

### `theorem isogOneSub_negFrobenius_isSeparable_of_bridge_001_γ_and_bridge_003`
- **Type**: `(hq) → (h_bridge_001_γ) → (h_bridge_003) → (isogOneSub_negFrobenius W hq).IsSeparable`
- **What**: Witness #1 closer taking BRIDGE-001 for γ + BRIDGE-003.
- **How**: Derives `coeff 1 = 1` via `coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_via_bridge_003`, then routes to `isogOneSub_negFrobenius_isSeparable_of_bridge_and_leading`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 615–639, proof 25 lines

### `theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_bridge_001_γ_and_bridge_003`
- **Type**: `(hq) → (h_bridge_001_γ) → (h_bridge_003) → omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1`
- **What**: Companion omega-coeff closer taking BRIDGE-001 + BRIDGE-003.
- **Uses from project**: `coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_via_bridge_003`, `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_bridge_and_leading`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 647–671, proof 25 lines

---

## Group 7: Sub-helpers 1–9 (dominant-term identification for addPullbackNumerator)

These 9 short theorems (lines 689–779) compute `localExpand` and `orderTop`/`leadingCoeff` of individual terms of `addPullbackNumerator_reduced_negFrobenius`. Each is 3–10 lines.

### `theorem localExpand_x_gen_sub_frobenius_pullback_x_gen` (L689)
`localExpand W (x_gen W - (frobeniusIsog W).pullback (x_gen W)) = formalX W - (formalX W)^q`.

### `theorem orderTop_formalX_sub_formalX_pow` (L697)
`orderTop(formalX - formalX^q) = -2q` for `q ≥ 2`. Uses strict non-arch via `orderTop_add_eq_right`.

### `theorem localExpand_x_gen_sub_frob_pullback_x_gen_sq` (L720)
Square of the above via `map_pow`.

### `theorem orderTop_formalX_sub_formalX_pow_sq` (L727)
`orderTop((formalX - formalX^q)^2) = -4q` via `orderTop_mul`. Proof >30 lines at 38 lines (long signature).

### `theorem localExpand_x_gen_mul_frob_pullback_x_gen_sq` (L741)
`localExpand W (x_gen * (frob.pullback x_gen)^2) = formalX^(2q+1)`.

### `theorem orderTop_formalX_pow_two_q_plus_one` (L750)
`orderTop(formalX^(2q+1)) = -2 - 4q` via `formalX_pow_orderTop`.

### `theorem leadingCoeff_formalX_pow_two_q_plus_one` (L760)
`leadingCoeff(formalX^(2q+1)) = 1` via `formalX_pow_leadingCoeff`.

### `theorem orderTop_localExpand_x_gen_mul_frob_pullback_x_gen_sq` (L766)
Composes the two above for the dominant term's orderTop.

### `theorem leadingCoeff_localExpand_x_gen_mul_frob_pullback_x_gen_sq` (L776)
Leading coefficient of the dominant term is 1.

---

## Group 8: Sub-helpers 10–30 (remaining terms, orderTop bounds)

These theorems (lines 790–993) are short (3–20 lines each) auxiliary bounds on individual Laurent series terms. Key ones:

### `theorem formalY_pow_orderTop` (L790)
`orderTop(formalY^n) = -3n` by induction on n using `orderTop_mul`.

### `theorem orderTop_HahnSeries_C_ge_zero` (L947)
`0 ≤ orderTop (C c)` for constant Hahn series; handles `c = 0` and `c ≠ 0` cases.
Used by: many sub-helpers in Group 9.

### `theorem localExpand_algebraMap_eq_C` (L959)
`localExpand W (algebraMap K KE c) = HahnSeries.C c`; bridges `localExpand_algebraMap` + `ofPowerSeries_C`.
Used by: `orderTop_localExpand_algebraMap_mul_ge`, `orderTop_localExpand_two_mul_a₆_ge`, `localExpand_addPullback_curve_equation`.

### `theorem orderTop_localExpand_algebraMap_mul_ge` (L969)
`orderTop(localExpand f) ≤ orderTop(localExpand(a * f))` for `a : K`; constant factor does not decrease orderTop.
Used by: many sub-helpers.

### `theorem orderTop_localExpand_two_mul_ge` (L983)
`orderTop(localExpand f) ≤ orderTop(localExpand(2 * f))`; via `2f = f + f` without char-2 issues.

### `theorem orderTop_localExpand_neg` (L991)
`orderTop(localExpand(-f)) = orderTop(localExpand f)` via `map_neg` + `orderTop_neg`.

---

## Group 9: Sub-helpers 31–55 (negFrobenius pullback terms, orderTop bounds)

Sub-helpers 31–55 (lines 997–1359) are the bulk bounds on terms of `addPullbackNumerator_reduced_negFrobenius` at the negFrobenius point. Each is 5–30 lines.

Key items:
- `localExpand_negFrobeniusIsog_pullback_y_gen` (L997): closed form of `localExpand((negFrob).pullback y_gen)`.
- `orderTop_localExpand_negFrobeniusIsog_pullback_y_gen` (L1031, 30 lines): orderTop = -3q for q ≥ 2.
- `orderTop_localExpand_y_gen_mul_negFrobeniusIsog_pullback_y_gen_ge` (L1109, 30 lines): ≥ -3-3q bound.
- `orderTop_localExpand_y_gen_add_negFrobeniusIsog_pullback_y_gen` (L1143, 18 lines): = -3q.
- Sub-helpers 40–48 (L1173–1263): individual bounds for the 8 sub-dominant terms.
- Sub-helpers 49–55 (L1274–1359): promotion of bounds to ≥ -3-3q for cumulative sum.

---

## Group 10: Cumulative sum closure + MAIN THEOREM (orderTop of addPullbackNumerator)

### `theorem orderTop_add_ge_of_both_ge` (L1369)
- **Type**: `n ≤ a.orderTop → n ≤ b.orderTop → n ≤ (a + b).orderTop`
- **What**: Utility: addition preserves orderTop lower bounds via `min_orderTop_le_orderTop_add`.
- **Used by**: many sub-helpers, `orderTop_localExpand_addPullbackNumerator_reduced_negFrobenius_rest_ge`, `m_le_neg_three_orderTop_localExpand_addPullback_y_negFrobenius`
- **Visibility**: public
- **Lines**: 1369–1372, proof 2 lines

### `theorem orderTop_sub_ge_of_both_ge` (L1376)
- **Type**: `n ≤ a.orderTop → n ≤ b.orderTop → n ≤ (a - b).orderTop`
- **What**: Subtraction preserves orderTop bounds via `orderTop_neg` + `orderTop_add_ge_of_both_ge`.
- **Used by**: `orderTop_localExpand_addPullbackNumerator_reduced_negFrobenius_rest_ge`
- **Visibility**: public
- **Lines**: 1376–1382, proof 7 lines

### `theorem orderTop_localExpand_addPullbackNumerator_reduced_negFrobenius_rest_ge` (L1388)
- **Type**: `-3-3q ≤ orderTop(localExpand(7-term rest of addPullbackNumerator_reduced_negFrobenius))`
- **What**: Sequential `add/sub_ge_of_both_ge` chain over all 7 sub-dominant bounds from sub-helpers 50–55.
- **How**: Collects the 7 sub-helper bounds, distributes `localExpand` over add/sub via `simp only [map_add, map_sub]`, then chains.
- **Uses from project**: sub-helpers 51–55 (promoted bounds), `orderTop_localExpand_a₁_mul_x_negFrob_π_y_plus_negFrob_π_x_y_ge`, `orderTop_localExpand_two_mul_y_gen_mul_negFrob_π_y_ge`
- **Used by**: `orderTop_localExpand_addPullbackNumerator_reduced_negFrobenius_eq`, `leadingCoeff_localExpand_addPullbackNumerator_reduced_negFrobenius_eq`
- **Visibility**: public
- **Lines**: 1388–1422, proof 35 lines
- **Notes**: Proof >30 lines (35)

### `theorem orderTop_localExpand_addPullbackNumerator_reduced_negFrobenius_eq` (L1435)
- **Type**: `(hq : 2 ≤ Fintype.card K) → orderTop(localExpand(addPullbackNumerator_reduced_negFrobenius W)) = -2-4q`
- **What**: **MAIN THEOREM** for the numerator: the dominant term `x·(negFrob*x)^2` has orderTop `-2-4q`, strictly less than `-3-3q` of the rest, so strict non-arch (`orderTop_add_eq_right`) extracts the dominant orderTop.
- **How**: Decomposes via `addPullbackNumerator_reduced_negFrobenius` ring identity, uses sub-helpers 45 and 58, applies `HahnSeries.orderTop_add_eq_right`.
- **Uses from project**: `orderTop_localExpand_addPullbackNumerator_reduced_negFrobenius_rest_ge`, `orderTop_localExpand_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq`, `addPullbackNumerator_reduced_negFrobenius`
- **Used by**: `orderTop_localExpand_addPullback_x_negFrobenius_eq`
- **Visibility**: public
- **Lines**: 1435–1487, proof 53 lines
- **Notes**: Proof >30 lines (53); large inline ring identity for the decomposition

### `theorem leadingCoeff_localExpand_addPullbackNumerator_reduced_negFrobenius_eq` (L1493)
- **Type**: `(hq) → leadingCoeff(localExpand(addPullbackNumerator_reduced_negFrobenius W)) = 1`
- **What**: **MAIN COMPANION**: the leading coefficient of the numerator is 1 (dominant term has leadingCoeff = 1 and strictly dominates rest).
- **How**: Same decomposition as above but uses `HahnSeries.leadingCoeff_add_eq_right` + `leadingCoeff_localExpand_x_gen_mul_frob_pullback_x_gen_sq`.
- **Uses from project**: `orderTop_localExpand_addPullbackNumerator_reduced_negFrobenius_rest_ge`, `orderTop_localExpand_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq`, `leadingCoeff_localExpand_x_gen_mul_frob_pullback_x_gen_sq`, `negFrobeniusIsog_pullback_x_gen`
- **Used by**: `leadingCoeff_localExpand_addPullback_x_negFrobenius_eq`
- **Visibility**: public
- **Lines**: 1493–1546, proof 54 lines
- **Notes**: Proof >30 lines (54)

---

## Group 11: Bridge to addPullback_x (orderTop = -2, leadingCoeff = 1)

### `theorem leadingCoeff_formalX_sub_formalX_pow` (L1558)
`leadingCoeff(formalX - formalX^q) = -1` for `q ≥ 2`. The dominant `-formalX^q` term gives leadingCoeff -1 via `leadingCoeff_add_eq_right`.

### `theorem leadingCoeff_formalX_sub_formalX_pow_sq` (L1573)
`leadingCoeff((formalX - formalX^q)^2) = 1` via `leadingCoeff_mul` + `(-1)^2 = 1`.

### `theorem orderTop_localExpand_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq` (L1580)
`orderTop(localExpand((x - negFrob*x)^2)) = -4q` via bridge to frobenius side.

### `theorem leadingCoeff_localExpand_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq` (L1589)
`leadingCoeff(localExpand((x - negFrob*x)^2)) = 1`.

### `theorem localExpand_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_ne_zero` (L1598)
Nonzero from finite orderTop.

### `private theorem x_gen_sub_negFrob_pullback_x_gen_ne_zero_local` (L1611)
`x_gen - (negFrob).pullback(x_gen) ≠ 0` in K(E) via the LaurentSeries side orderTop ≠ ⊤.
- **Visibility**: private
- **Used by**: `orderTop_localExpand_addPullback_x_negFrobenius_eq`, `leadingCoeff_localExpand_addPullback_x_negFrobenius_eq`, `kaehler_D_addSlope_negFrobenius`

### `theorem orderTop_localExpand_addPullback_x_negFrobenius_eq` (L1628)
- **Type**: `(hq : 2 ≤ Fintype.card K) → orderTop(localExpand(addPullback_x W (negFrobeniusIsog W))) = -2`
- **What**: **MAIN COMPANION**: the addition-pullback x-coordinate (= numerator/denominator^2) has orderTop -2 in Laurent series.
- **How**: `addPullbackNumerator_negFrobenius_eq` + `map_div₀` + `HahnSeries.orderTop_div` + the numerator/denominator orderTop results.
- **Uses from project**: `orderTop_localExpand_addPullbackNumerator_reduced_negFrobenius_eq`, `orderTop_localExpand_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq`, `addPullbackNumerator_negFrobenius_eq`, `addPullbackNumerator_negFrobenius_eq_reduced`, `localExpand_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_ne_zero`
- **Used by**: many downstream (orderTop_localExpand_addPullback_x_sq/cube, orderTop_y-case, etc.)
- **Visibility**: public
- **Lines**: 1628–1647, proof 20 lines

### `theorem leadingCoeff_localExpand_addPullback_x_negFrobenius_eq` (L1651)
- **Type**: `(hq) → leadingCoeff(localExpand(addPullback_x W (negFrobeniusIsog W))) = 1`
- **What**: Leading coefficient of the addition-pullback x-coordinate is 1.
- **How**: Same div structure as orderTop version but uses `HahnSeries.leadingCoeff_div`.
- **Used by**: multiple leadingCoeff downstream, `coeff_neg_two_localExpand_addPullback_x_negFrobenius_eq`
- **Visibility**: public
- **Lines**: 1651–1668, proof 18 lines

### `theorem localExpand_addPullback_x_negFrobenius_ne_zero` (L1672)
Nonzero from finite orderTop. Unused in file.

### `theorem coeff_neg_two_localExpand_addPullback_x_negFrobenius_eq` (L1688)
- **Type**: `(hq) → coeff (-2 : ℤ) (localExpand W (addPullback_x W (negFrobeniusIsog W))) = 1`
- **What**: The coefficient at exponent -2 is 1; derived from orderTop = -2 and leadingCoeff = 1 via `coeff_untop_eq_leadingCoeff`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1688–1701, proof 14 lines

---

## Group 12: Powers of addPullback_x (orderTop = -4, -6)

### `theorem orderTop_localExpand_addPullback_x_negFrobenius_sq` (L1712)
`orderTop(localExpand(addPullback_x)^2) = -4` via `orderTop_mul`.

### `theorem orderTop_localExpand_addPullback_x_negFrobenius_cube` (L1722)
`orderTop(localExpand(addPullback_x)^3) = -6` via `pow_add` + `orderTop_mul`.

---

## Group 13: Y-side: orderTop of addPullback_y via curve equation

### `theorem localExpand_addPullback_y_negFrobenius_ne_zero` (L1735)
`localExpand(addPullback_y) ≠ 0` via injectivity of `localExpand` + `ord_addPullback_y_negFrobenius`.

### `theorem localExpand_addPullback_curve_equation` (L1753)
- **Type**: The Weierstrass equation holds for `localExpand(addPullback_x/y)` in `LaurentSeries K`.
- **What**: The curve equation is preserved under `localExpand ∘ addPullback`.
- **How**: Applies `congrArg (localExpand W)` to `addPullback_equation`, then substitutes `localExpand(algebraMap K KE a_i) = C a_i` via `localExpand_algebraMap_eq_C`.
- **Uses from project**: `addPullback_equation`, `localExpand_algebraMap_eq_C`, `negFrobeniusIsog_addNonInverse`
- **Used by**: `orderTop_localExpand_addPullback_LHS_eq`, `leadingCoeff_localExpand_addPullback_LHS_eq`
- **Visibility**: public
- **Lines**: 1753–1783, proof 31 lines

### `theorem orderTop_localExpand_RHS_lower_terms_ge` (L1789)
`-4 ≤ orderTop(a₂·X² + a₄·X + a₆)` where X = localExpand(addPullback_x). Multi-case analysis.
- **Lines**: 1789–1821, proof 33 lines
- **Notes**: Proof >30 lines (33)

### `theorem orderTop_localExpand_addPullback_RHS_eq` (L1826)
`orderTop(X³ + a₂X² + a₄X + a₆) = -6` via strict non-arch (X³ dominates).
- **Lines**: 1826–1859, proof 34 lines
- **Notes**: Proof >30 lines (34)

### `theorem orderTop_localExpand_addPullback_LHS_eq` (L1869)
`orderTop(LHS of curve equation) = -6` via `localExpand_addPullback_curve_equation` + RHS result. Trivial.

### `theorem exists_m_orderTop_localExpand_addPullback_y_negFrobenius` (L1884)
`∃ m : ℤ, orderTop(localExpand(addPullback_y)) = m`. Extracts finiteness from nonzero.

### `theorem orderTop_localExpand_addPullback_y_negFrobenius_sq_eq_two_m` (L1896)
`orderTop(localExpand(addPullback_y)^2) = 2m` parametric in `m`.

### `theorem orderTop_localExpand_addPullback_x_mul_y_negFrobenius_eq` (L1907)
`orderTop(X · Y) = -2 + m` parametric.

### `theorem m_le_neg_three_orderTop_localExpand_addPullback_y_negFrobenius` (L1920)
- **Type**: `(hq) → (m) → (hm : orderTop Y = m) → m ≤ -3`
- **What**: Rules out `m ≥ -2`: if `m ≥ -2`, LHS orderTop ≥ -4 contradicts LHS orderTop = -6.
- **How**: By contradiction: shows Y², a₁XY, a₃Y each have orderTop ≥ -4, hence sum ≥ -4, contradicting = -6. Uses sub-helpers 76, 77.
- **Uses from project**: `orderTop_add_ge_of_both_ge`, `orderTop_localExpand_addPullback_LHS_eq`, `orderTop_localExpand_addPullback_y_negFrobenius_sq_eq_two_m`, `orderTop_localExpand_addPullback_x_mul_y_negFrobenius_eq`
- **Used by**: `orderTop_localExpand_addPullback_y_negFrobenius_eq`, `leadingCoeff_localExpand_addPullback_y_negFrobenius_sq_eq_one`
- **Visibility**: public
- **Lines**: 1920–1982, proof 63 lines
- **Notes**: Proof >30 lines (63)

### `theorem orderTop_y_sq_lt_a1xy_negFrobenius` (L1986)
For `m ≤ -3`: `orderTop(Y²) < orderTop(a₁·X·Y)` parametric in m. Used by the main y-side theorem.
- **Lines**: 1986–2013, proof 28 lines

### `theorem orderTop_y_sq_lt_a3y_negFrobenius` (L2017)
For `m ≤ -3`: `orderTop(Y²) < orderTop(a₃·Y)` parametric. Used by the main y-side theorem.

### `theorem orderTop_localExpand_addPullback_y_negFrobenius_eq` (L2040)
- **Type**: `(hq : 2 ≤ Fintype.card K) → orderTop(localExpand(addPullback_y W (negFrobeniusIsog W))) = -3`
- **What**: **MAIN Y-SIDE**: orderTop of addPullback_y is -3. The case analysis from the curve equation: `m ≤ -3` from sub-helper 78, Y² strictly dominates both a₁XY and a₃Y, so LHS orderTop = 2m = -6, giving m = -3.
- **How**: `obtain ⟨m, hm⟩` from `exists_m`, then `m_le_neg_three`, strict dominances via sub-helpers 79-80, chain of `orderTop_add_eq_left`, use LHS = -6, solve `2m = -6` by `omega`.
- **Uses from project**: `exists_m_orderTop_localExpand_addPullback_y_negFrobenius`, `m_le_neg_three_orderTop_localExpand_addPullback_y_negFrobenius`, `orderTop_y_sq_lt_a1xy_negFrobenius`, `orderTop_y_sq_lt_a3y_negFrobenius`, `orderTop_localExpand_addPullback_LHS_eq`, `orderTop_localExpand_addPullback_y_negFrobenius_sq_eq_two_m`
- **Used by**: `leadingCoeff_localExpand_addPullback_y_negFrobenius_sq_eq_one`, `orderTop_localExpand_isogOneSub_negFrobenius_pullback_localParam`
- **Visibility**: public
- **Lines**: 2040–2082, proof 43 lines
- **Notes**: Proof >30 lines (43)

---

## Group 14: Y-side leadingCoeff

### `theorem leadingCoeff_localExpand_addPullback_x_negFrobenius_cube_eq` (L2091)
`leadingCoeff(X³) = 1`. From `leadingCoeff_mul` + main companion.

### `theorem leadingCoeff_localExpand_addPullback_RHS_eq` (L2104)
`leadingCoeff(RHS) = 1` via X³ strict domination. Proof 33 lines.

### `theorem leadingCoeff_localExpand_addPullback_LHS_eq` (L2141)
`leadingCoeff(LHS) = 1` via curve equation + RHS. Trivial.

### `theorem leadingCoeff_localExpand_addPullback_y_negFrobenius_sq_eq_one` (L2157)
- **Type**: `(hq) → leadingCoeff(localExpand(addPullback_y)^2) = 1`
- **What**: The squared leading coefficient of the y-coordinate is 1 (from curve equation + strict dominance of Y² at m = -3).
- **How**: Uses the actual value m = -3 (from main y-side theorem), reruns strict dominances, applies `leadingCoeff_add_eq_left` twice, matches with LHS leadingCoeff = 1.
- **Used by**: `leadingCoeff_localExpand_addPullback_y_negFrobenius_sq`
- **Visibility**: public
- **Lines**: 2157–2190, proof 34 lines

### `theorem leadingCoeff_localExpand_addPullback_y_negFrobenius_sq` (L2194)
`(leadingCoeff(Y))² = 1`. From `leadingCoeff_mul` applied to squared form.
- **Used by**: `leadingCoeff_localExpand_addPullback_y_negFrobenius_ne_zero`, `leadingCoeff_localExpand_addPullback_y_negFrobenius_eq_neg_one_char_two`

### `theorem leadingCoeff_localExpand_addPullback_y_negFrobenius_ne_zero` (L2204)
`leadingCoeff(Y) ≠ 0`. From `c² = 1 ≠ 0`. Unused in file.

---

## Group 15: Ratio computation and leading-coefficient closer

### `theorem addPullbackAlgHom_negFrobenius_x_gen_eq` (L2219)
- **Type**: `(hq) → addPullbackAlgHom_negFrobenius W hq (x_gen W) = addPullback_x W (negFrobeniusIsog W)`
- **What**: The AlgHom realization of γ sends x_gen to addPullback_x.
- **How**: Unfolds `addPullbackAlgHom_negFrobenius`, uses `IsFractionRing.liftAlgHom_apply` + `lift_algebraMap` + `AdjoinRoot.lift_mk`.
- **Used by**: `localExpand_isogOneSub_negFrobenius_pullback_localParam`, `kaehler_witness_via_slope_deriv_witness`
- **Visibility**: public
- **Lines**: 2219–2235, proof 17 lines

### `theorem addPullbackAlgHom_negFrobenius_y_gen_eq` (L2238)
Analogous for y_gen. Used by same callers.
- **Lines**: 2238–2259, proof 22 lines

### `theorem localExpand_isogOneSub_negFrobenius_pullback_localParam` (L2263)
`localExpand(γ.pullback(localParam)) = -localExpand(addPullback_x) / localExpand(addPullback_y)`.

### `theorem orderTop_localExpand_isogOneSub_negFrobenius_pullback_localParam` (L2276)
`orderTop(...) = 1` from `-2 - (-3) = 1` via `orderTop_div`.

### `theorem leadingCoeff_localExpand_isogOneSub_negFrobenius_pullback_localParam` (L2290)
`leadingCoeff(...) = -1 / leadingCoeff(Y)`.

### `theorem coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_eq_neg_one_div_leadingCoeff` (L2305)
- **Type**: `(hq) → coeff 1 (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) = -1 / leadingCoeff(Y)`
- **What**: Extracts the coeff 1 of the formal series via `coeff_untop_eq_leadingCoeff` at orderTop = 1.
- **Used by**: `coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_eq_one_of_y_lc`, `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`
- **Visibility**: public
- **Lines**: 2305–2326, proof 22 lines

### `theorem coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_eq_one_of_y_lc` (L2338)
Given `leadingCoeff(Y) = -1`, `coeff 1 (formal γ) = 1` since `-1 / -1 = 1`.

### `theorem isogOneSub_negFrobenius_isSeparable_via_y_lc_and_bridge_001` (L2350)
Witness #1 from y-lc = -1 witness + BRIDGE-001 for γ.

### `theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_y_lc_and_bridge_001` (L2370)
ω(γ) = 1 from same.

---

## Group 16: Char-2 sign determination

### `theorem leadingCoeff_localExpand_addPullback_y_negFrobenius_eq_neg_one_char_two` (L2394)
- **Type**: `[CharP K 2] → (hq) → leadingCoeff(Y) = -1`
- **What**: In char 2, pins the sign: `c² = 1` and `(c+1)² = 0` (since `2 = 0`) gives `c = -1`.
- **How**: `CharP.cast_eq_zero` + ring algebra to show `(c+1)^2 = 0`, then `pow_eq_zero_iff`.
- **Uses from project**: `leadingCoeff_localExpand_addPullback_y_negFrobenius_sq`
- **Used by**: char-2 closers (subs 98-99-101)
- **Visibility**: public
- **Lines**: 2394–2419, proof 26 lines

### `theorem isogOneSub_negFrobenius_isSeparable_char_two` (L2425)
Witness #1 in char 2: needs only BRIDGE-001 for γ. Unused in file.

### `theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_char_two` (L2437)
ω(γ) = 1 in char 2. Unused in file.

### `theorem bridge_001_γ_isogOneSub_negFrobenius_char_two` (L2454)
BRIDGE-001 for γ in char 2 from `h_omega : ω(γ) = 1`. Unused in file.

---

## Group 17: Kähler differential building blocks

### `theorem kaehler_D_x_gen_pow_card_eq_zero` (L2484)
- **Type**: `[Fact p.Prime] [CharP K p] → D(x_gen^q) = 0`
- **What**: In characteristic p, the q = p^k-th power has zero Kähler differential: `D(x^q) = q · x^(q-1) · D(x)` and `(q : K) = 0`.
- **How**: `Derivation.leibniz_pow` + `CharP.cast_eq_zero` + divisibility `p ∣ q = p^k`.
- **Uses from project**: `x_gen`
- **Used by**: `kaehler_D_frobeniusIsog_pullback_x_gen`, `kaehler_D_negFrobeniusIsog_pullback_x_gen`
- **Visibility**: public
- **Lines**: 2484–2505, proof 22 lines

### `theorem kaehler_D_frobeniusIsog_pullback_x_gen` (L2510)
`D(frob.pullback(x_gen)) = 0`. Direct from sub-helper 104 + `frobeniusIsog_pullback_apply`.

### `theorem kaehler_D_frobeniusIsog_pullback_y_gen` (L2519)
`D(frob.pullback(y_gen)) = 0`. Same proof shape.
- **Lines**: 2519–2539, proof 21 lines

### `theorem kaehler_D_negFrobeniusIsog_pullback_x_gen` (L2548)
`D((negFrob).pullback(x_gen)) = 0` via `negFrobeniusIsog_pullback_x_gen`.

### `theorem kaehler_D_negFrobeniusIsog_pullback_y_gen` (L2563)
`D((negFrob).pullback(y_gen)) = 0` via Leibniz + sub-helpers 105-106.
- **Used by**: `kaehler_D_addSlope_negFrobenius`
- **Lines**: 2563–2576, proof 14 lines

### `theorem kaehler_D_addPullback_x_via_slope_witness` (L2587)
- **Type**: `(h_α_x : D(α.pullback(x_gen)) = 0) → D(addPullback_x W α) = (2ℓ + a₁) • D(ℓ) - D(x_gen)`
- **What**: Given Kähler-flatness of `α*x`, `D(addPullback_x) = (2ℓ + a₁) • D(slope) - D(x_gen)`.
- **How**: Leibniz expansion of `addX = ℓ² + a₁ℓ - a₂ - x - α*x` using `Derivation.leibniz_pow`, `leibniz`, `map_algebraMap`, and uses `h_α_x` to kill the last term.
- **Used by**: `kaehler_D_addPullback_x_negFrobenius`
- **Visibility**: public
- **Lines**: 2587–2616, proof 30 lines

### `theorem kaehler_D_addPullback_x_negFrobenius` (L2627)
Specializes `kaehler_D_addPullback_x_via_slope_witness` to `negFrobeniusIsog` using sub-helper 107.

### `theorem kaehler_D_addPullback_x_general` (L2644)
- **Type**: `D(addPullback_x W α) = (2ℓ + a₁) • D(ℓ) - D(x_gen) - D(α.pullback(x_gen))`
- **What**: General form (no Frobenius flatness), the full Silverman III.5.2 differential formula including the `D(α*x)` term.
- **How**: Same Leibniz expansion as the witness form but without cancelling the last term.
- **Used by**: `kaehler_D_addPullback_x_general_cleared`
- **Visibility**: public
- **Lines**: 2644–2667, proof 24 lines

---

## Group 18: Kähler witness consumers

### `theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_kaehler_witness` (L2682)
- **Type**: `(hq) → (h_kaehler : (α*(u))⁻¹ • D(γ.pullback(x_gen)) = invariantDifferential) → ω(γ) = 1`
- **What**: Given the Kähler witness, derives ω(γ) = 1 via `omegaPullbackCoeff_unique`.
- **Used by**: `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`
- **Visibility**: public
- **Lines**: 2682–2693, proof 12 lines

### `theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_pullbackKaehler_witness` (L2718)
Given `γ.pullbackKaehler(ω) = ω`, derives ω(γ) = 1.

### `theorem pullbackKaehler_invariantDifferential_id` (L2733)
`id.pullbackKaehler(ω) = ω`. From `omegaPullbackCoeff_id = 1`.

### `theorem pullbackKaehler_invariantDifferential_negFrobeniusIsog` (L2744)
`(negFrob).pullbackKaehler(ω) = 0`. From `omegaPullbackCoeff_negFrobeniusIsog = 0`.

### `theorem pullbackKaehler_invariantDifferential_isogOneSub_negFrobenius_via_additivity_witness` (L2760)
Given III.5.2 additivity `γ.pullbackKaehler ω = id.pullbackKaehler ω + negFrob.pullbackKaehler ω`, concludes `γ.pullbackKaehler ω = ω`.

### `theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_additivity_witness` (L2776)
Composes via pullbackKaehler witness. Unused in file (0 external references).
- **Lines**: 2776–2785, proof 10 lines

### `theorem kaehler_witness_via_slope_deriv_witness` (L2807)
- **Type**: `[CharP K p] → (hq) → (c : KE) → (h_slope_deriv : D(addSlope) = c • D(x_gen)) → (h_KE_identity : ((2ℓ+a₁)·c - 1)·u_gen = α*(u)) → (Kähler witness)`
- **What**: The main closing-arc consumer: from a slope-derivative witness and a K(E) ring identity, produces the Kähler witness for ω(γ) = 1.
- **How**: Rewrites via `addPullbackAlgHom_negFrobenius_x_gen_eq`, `kaehler_D_addPullback_x_negFrobenius`, substitutes `h_slope_deriv`, uses `smul_right_injective` + `field_simp` + `linear_combination`.
- **Uses from project**: `addPullbackAlgHom_negFrobenius_x_gen_eq`, `kaehler_D_addPullback_x_negFrobenius`, `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_kaehler_witness`, `alpha_star_u_eq`, `u_gen_ne_zero`
- **Used by**: `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`
- **Visibility**: public
- **Lines**: 2807–2853, proof 47 lines
- **Notes**: Proof >30 lines (47); uses `linear_combination`

---

## Group 19: Weierstrass equation Kähler derivatives

### `theorem weierstrass_equation_in_KE` (L2872)
- **Type**: `y_gen² + a₁·x·y + a₃·y = x³ + a₂·x² + a₄·x + a₆` in K(E)
- **What**: The Weierstrass equation at the generic point, lifted to K(E).
- **How**: `generic_equation` + `(W_KE W).toAffine.equation_iff`.
- **Used by**: `kaehler_D_weierstrass_equation_K_E`, `kaehler_witness_polynomial_identity_negFrobenius`, `weierstrass_equation_pi_negFrobenius`, `kaehler_D_addPullback_x_eq_one_add_smul_omega`
- **Visibility**: public
- **Lines**: 2872–2880, proof 9 lines

### `theorem kaehler_D_weierstrass_equation_K_E` (L2890)
`D(LHS) = D(RHS)` from `congrArg D` on `weierstrass_equation_in_KE`. Trivial.

### `theorem kaehler_D_y_gen_sq` (L2913)
`D(y²) = y • D(y) + y • D(y)` via `pow_two` + `leibniz` (wall-break avoiding ℕ-smul).

### `theorem kaehler_D_x_gen_sq` (L2922)
`D(x²) = x • D(x) + x • D(x)`. Same.

### `theorem kaehler_D_x_gen_cube` (L2931)
`D(x³) = x² • D(x) + x • D(x²)`. Via `pow_succ` + `leibniz`.

### `theorem kaehler_D_weierstrass_LHS_expanded` (L2943)
Full Leibniz-expanded LHS in KE-smul-only form (bypasses ℕ-smul issues).
- **Lines**: 2943–2969, proof 27 lines

### `theorem kaehler_D_weierstrass_RHS_expanded` (L2973)
Full Leibniz-expanded RHS. Uses sub-helpers 123, 124.
- **Lines**: 2973–3003, proof 31 lines

### `theorem kaehler_curve_equation_K_E` (L3016)
- **Type**: `(a₃ + 2y + a₁x) • D(y) = (3x² + 2a₂x + a₄ - a₁y) • D(x)` in `Ω[K(E)/K]`
- **What**: **The substantive Kähler identity**: differentiating the curve equation gives this relation between D(y) and D(x). No witnesses.
- **How**: Pre-rewrites `2y = y+y` etc. to avoid ℕ→KE cast issues, distributes smul, combines expanded LHS/RHS via `linear_combination (norm := abel) h_eq`.
- **Uses from project**: `kaehler_D_weierstrass_equation_K_E`, `kaehler_D_weierstrass_LHS_expanded`, `kaehler_D_weierstrass_RHS_expanded`
- **Used by**: `kaehler_D_y_gen_eq_num_smul_omega`, `kaehler_D_addSlope_via_curve_equation_negFrobenius`
- **Visibility**: public
- **Lines**: 3016–3051, proof 36 lines
- **Notes**: Proof >30 lines (36); the `linear_combination (norm := abel)` is the key tactic for the Kähler identity

---

## Group 20: Slope differential identities

### `theorem kaehler_D_addSlope_negFrobenius` (L3071)
- **Type**: `[CharP K p] → (x - π*x)² • D(addSlope) = (x - π*x) • D(y) - (y - π*y) • D(x)`
- **What**: Kähler quotient rule for the addition slope under negFrobenius; D(π*x) = D(π*y) = 0 simplifies the full quotient rule.
- **How**: `Derivation.leibniz_div` on `addSlope = N/Den`, uses sub-helpers 107 and 108 to zero D(N) contributions, cancels Den²·Den⁻² = 1.
- **Uses from project**: `addSlope_negFrobeniusIsog_eq`, `kaehler_D_negFrobeniusIsog_pullback_y_gen`, `kaehler_D_negFrobeniusIsog_pullback_x_gen`, `x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero`
- **Used by**: `kaehler_D_addPullback_x_negFrobenius_cleared`, `kaehler_D_addSlope_via_curve_equation_negFrobenius`
- **Visibility**: public
- **Lines**: 3071–3104, proof 34 lines

### `theorem kaehler_D_addSlope_general` (L3111)
- **Type**: `(h_ne : x_gen ≠ α.pullback(x_gen)) → Den² • D(addSlope) = Den • (D(y) - D(α*y)) - N • (D(x) - D(α*x))`
- **What**: General-pair slope differential: the full quotient rule without Frobenius flatness.
- **How**: `slope_of_X_ne` + `leibniz_div` + `map_sub` + `Den²·Den⁻² = 1`.
- **Used by**: `kaehler_D_addPullback_x_general_cleared`
- **Visibility**: public
- **Lines**: 3111–3134, proof 24 lines

### `theorem kaehler_D_addPullback_x_negFrobenius_cleared` (L3155)
`Den² • D(addPullback_x) = (2ℓ + a₁) • Den • D(y) - (2ℓ + a₁) • N • D(x) - Den² • D(x)`. Combines sub-helpers 110 and 128.
- **Lines**: 3155–3176, proof 22 lines

### `theorem kaehler_D_addPullback_x_general_cleared` (L3181)
General-pair cleared form: analogous to above but with `D(α*x)` and `D(α*y)` terms. Combines `kaehler_D_addPullback_x_general` + `kaehler_D_addSlope_general`.
- **Lines**: 3181–3201, proof 21 lines

---

## Group 21: Route B ω-smul leaves

### `theorem kaehler_D_x_gen_eq_u_smul_omega` (L3210)
`D(x_gen) = u_gen • ω`. Immediate from `ω = u_gen⁻¹ • D(x_gen)`.
- **Used by**: `kaehler_D_addPullback_x_eq_one_add_smul_omega`, `kaehler_D_addSlope_via_curve_equation_negFrobenius`

### `theorem kaehler_D_y_gen_eq_num_smul_omega` (L3221)
- **Type**: `D(y_gen) = (3x² + 2a₂x + a₄ - a₁y) • ω`
- **What**: From the Kähler curve equation and `D(x) = u • ω`, derives `D(y) = num • ω` by dividing through by `u ≠ 0`.
- **How**: Uses `kaehler_curve_equation_K_E`, recognizes `u_gen` as `a₃ + 2y + a₁x`, applies `smul_right_injective`.
- **Used by**: `kaehler_D_addPullback_x_eq_one_add_smul_omega`, `kaehler_D_addSlope_via_curve_equation_negFrobenius`
- **Visibility**: public
- **Lines**: 3221–3240, proof 20 lines

### `theorem kaehler_D_alpha_pullback_x_eq_smul_omega` (L3246)
- **Type**: `D(α.pullback(x_gen)) = (α*(u) · omegaPullbackCoeff W α) • ω`
- **What**: For any isogeny α, the Kähler differential of α*x is a scalar multiple of ω.
- **How**: From `omegaPullbackCoeff_spec` + `smul_smul` + `mul_inv_cancel`.
- **Used by**: `kaehler_D_addPullback_x_eq_one_add_smul_omega`, `kaehler_D_addPullback_x_pair_eq_smul_omega`
- **Visibility**: public
- **Lines**: 3246–3259, proof 14 lines

### `theorem kaehler_D_alpha_pullback_y_eq_smul_omega` (L3265)
- **Type**: `D(α.pullback(y_gen)) = (α*(num) · ω(α)) • ω`
- **What**: The Kähler differential of α*y is also a scalar multiple of ω, using the α-image curve equation.
- **How**: `congrArg (Isogeny.pullbackKaehler α)` applied to `kaehler_curve_equation_K_E`, then `pullbackKaehler_smul_KE` + `pullbackKaehler_D` + `smul_right_injective`.
- **Uses from project**: `kaehler_D_alpha_pullback_x_eq_smul_omega`, `kaehler_curve_equation_K_E`, `Isogeny.pullbackKaehler_smul_KE`, `Isogeny.pullbackKaehler_D`
- **Used by**: `kaehler_D_addPullback_x_eq_one_add_smul_omega`, `kaehler_D_addPullback_x_pair_eq_smul_omega`
- **Visibility**: public
- **Lines**: 3265–3304, proof 40 lines
- **Notes**: Proof >30 lines (40)

---

## Group 22: RB-ω4 (the Silverman III.5.2 ring collapse)

### `theorem kaehler_D_addPullback_x_eq_one_add_smul_omega` (L3314)
- **Type**: `(h_ne : x_gen ≠ α.pullback(x_gen)) → D(addPullback_x W α) = (2·addPullback_y + a₁·addPullback_x + a₃) • ((1 + ω(α)) • ω)`
- **What**: **RB-ω4** — the entire Silverman III.5.2 content for the `id ⊞ α` case: `D(addPullback_x) = u₃ • (1 + a_α) • ω`. The isogeny sum's pullback-differential is additive in the omega-coefficient.
- **How**: Substitutes all 4 ω-leaves (RB-ω1-ω3) into `kaehler_D_addPullback_x_general_cleared`, then `smul_right_injective` + `congr 1` reduces to a polynomial identity closed by `linear_combination` of `generic_equation` (at P) and `pullback_equation` (at α(P)), combined with `field_simp`.
- **Uses from project**: `kaehler_D_addPullback_x_general_cleared`, `kaehler_D_x_gen_eq_u_smul_omega`, `kaehler_D_y_gen_eq_num_smul_omega`, `kaehler_D_alpha_pullback_x_eq_smul_omega`, `kaehler_D_alpha_pullback_y_eq_smul_omega`, `generic_equation`, `pullback_equation`, `weierstrass_equation_in_KE`
- **Used by**: `RouteBInduction.lean` (3 uses externally)
- **Visibility**: public
- **Lines**: 3314–3371 (58 lines + 17 lines signature + `set_option` line), proof 58 lines
- **Notes**: `set_option maxHeartbeats 4000000` at line 3306 (NO-COMMENT). Proof >30 lines (75 total). The key III.5.2 arithmetic.

---

## Group 23: Slope via curve equation + Path A closing chain

### `theorem kaehler_D_addSlope_via_curve_equation_negFrobenius` (L3389)
`u · Den² • D(addSlope) = (Den · num - u · N) • D(x)`. Multiplies sub-helper 128 by u and substitutes curve equation to convert D(y) → num/u · D(x).
- **Lines**: 3389–3424, proof 36 lines

### `theorem alpha_star_u_isogOneSub_negFrobenius` (L3433)
`α*(u) = 2·addPullback_y + a₁·addPullback_x + a₃` via explicit unfolding of pullback + sub-helpers 89b/c.
- **Lines**: 3433–3454, proof 22 lines

### `theorem alpha_star_u_plus_u_gen_negFrobenius` (L3472)
`α*(u) + u_gen = -((2ℓ + a₁)·(addPullback_x - x_gen))` by ring algebra.
- **Lines**: 3472–3487, proof 16 lines

### `theorem weierstrass_equation_pi_negFrobenius` (L3499)
The Weierstrass equation at `π(x_gen, y_gen)` obtained by applying `(negFrob).pullback` to `weierstrass_equation_in_KE`.
- **Lines**: 3499–3517, proof 19 lines

### `theorem kaehler_witness_polynomial_identity_negFrobenius` (L3544)
`Den·num - u·N + (addPullback_x - x_gen)·Den² = 0`. Closed by `linear_combination -h_curve + h_curve_pi`.
- **Lines**: 3544–3563, proof 20 lines

### `theorem addPullback_x_sub_x_gen_mul_Den_sq_negFrobenius` (L3579)
`(addPullback_x - x_gen)·Den² = N² + a₁·N·Den - a₂·Den² - (2x + πx)·Den²`. Polynomial substitution via slope linearization + `linear_combination`.
- **Lines**: 3579–3616, proof 38 lines

### `theorem kaehler_witness_curve_form_negFrobenius` (L3630)
`Den·num - u·N + (addPullback_x - x_gen)·Den² = 0` (combining the polynomial form). Used by `kaehler_witness_coefficient_identity_negFrobenius`.

### `theorem kaehler_witness_coefficient_identity_negFrobenius` (L3659)
`(2ℓ + a₁)·(Den·num - u·N) = (α*(u) + u_gen)·Den²`. Combines sub-helpers 132 + 136.
- **Lines**: 3659–3680, proof 22 lines

---

## Group 24: MAIN CLOSERS — Witness #1 unconditional

### `theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one` (L3699)
- **Type**: `(p : ℕ) [Fact p.Prime] [CharP K p] → (hq : 2 ≤ Fintype.card K) → omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1`
- **What**: **Sub-helper 138 (MAIN)**: ω(γ) = 1 axiom-clean, unconditional. The Witness #1 omega-coefficient for the Hasse-Weil bound.
- **How**: Instantiates `kaehler_witness_via_slope_deriv_witness` with explicit witness `c := (Den·num - u·N)/(u·Den²)`. Derives `D(addSlope) = c • D(x_gen)` from `kaehler_D_addSlope_via_curve_equation_negFrobenius` by smul-cancelling `u·Den²`. Derives the K(E) coefficient identity from `kaehler_witness_coefficient_identity_negFrobenius` via `linear_combination u * h_137`.
- **Uses from project**: `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_kaehler_witness`, `kaehler_witness_via_slope_deriv_witness`, `kaehler_D_addSlope_via_curve_equation_negFrobenius`, `kaehler_witness_coefficient_identity_negFrobenius`, `x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero`, `u_gen_ne_zero`, `alpha_star_u_eq`
- **Used by**: GapQfKernel.lean (4 uses), OneSubComapConcrete.lean (1 use), OpenLemmas.lean (3 uses)
- **Visibility**: public
- **Lines**: 3699–3732, proof 34 lines
- **Notes**: Proof >30 lines (34). This is one of the two exported key API declarations.

### `theorem isogOneSub_negFrobenius_isSeparable` (L3739)
- **Type**: `(p : ℕ) [Fact p.Prime] [CharP K p] → (hq : 2 ≤ Fintype.card K) → (isogOneSub_negFrobenius W hq).IsSeparable`
- **What**: **Sub-helper 139 (MAIN)**: Witness #1 of the Hasse-Weil bound: `1 - π` is separable. Axiom-clean, unconditional.
- **How**: Composes `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one` + `isogOneSub_negFrobenius_isSeparable_of_h_coeff_only`.
- **Used by**: GapSpines.lean (4 uses), PoleDivisorFallback.lean (1 use), L6ViaPoleDivisor.lean (2 uses), OpenLemmas.lean (3 uses)
- **Visibility**: public
- **Lines**: 3739–3744, proof 6 lines
- **Notes**: This is the primary exported declaration. Unused in this file (callers are external).

---

## Group 25: General-pair III.5.2

### `theorem kaehler_D_addPullback_x_pair_eq_smul_omega` (L3763)
- **Type**: `(α₁ α₂ : Isogeny W.toAffine W.toAffine) → (h_ne : α₁.pullback(x_gen) ≠ α₂.pullback(x_gen)) → D(addPullback_x_pair α₁ α₂) = (2·addPullback_y_pair + a₁·addPullback_x_pair + a₃) • ((ω(α₁) + ω(α₂)) • ω)`
- **What**: **General-pair III.5.2**: the differential of the pair-addition x-coordinate is `u₃ • (a₁ + a₂) • ω`. The key fact that `ω(α₁ + α₂) = ω(α₁) + ω(α₂)` follows from this when applied appropriately.
- **How**: Mirrors `kaehler_D_addPullback_x_eq_one_add_smul_omega` with both `α₁*x/y` and `α₂*x/y` using the general image-differential leaves (RB-ω3a/3b) for both points; the final scalar collapse uses `linear_combination` of `pullback_equation W α₁` and `pullback_equation W α₂`.
- **Uses from project**: `kaehler_D_alpha_pullback_x_eq_smul_omega`, `kaehler_D_alpha_pullback_y_eq_smul_omega`, `pullback_equation`, `addSlopePair_eq_of_x_ne`
- **Used by**: `RouteBInduction.lean` (2 uses externally)
- **Visibility**: public
- **Lines**: 3763–3858, proof 96 lines
- **Notes**: `set_option maxHeartbeats 4000000` at line 3755 (NO-COMMENT). Proof >30 lines (96). Unused within this file; used externally.

---

## Declaration Statistics

| Category | Count |
|---|---|
| Theorems (public) | 163 |
| Theorems (private) | 2 (`orderTop_a₁_formalX_plus_a₃_ge_neg_two`, `x_gen_sub_negFrob_pullback_x_gen_ne_zero_local`) |
| Defs | 0 |
| Instances | 0 |
| Sorries | 0 |
| `set_option maxHeartbeats 4000000` | 2 (lines 3306, 3755; both NO-COMMENT) |
| Long proofs (>30 lines) | 42 |

## Key API (used by 3+ other declarations in this file or externally)

- `orderTop_add_ge_of_both_ge` — used by ~10 sub-helpers in the cumulative sum section
- `orderTop_localExpand_addPullbackNumerator_reduced_negFrobenius_rest_ge` — used by main theorem + leadingCoeff companion
- `coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero` — used by 6 scaffold theorems
- `kaehler_D_alpha_pullback_x_eq_smul_omega` — used by RB-ω4 + general-pair theorem
- `kaehler_D_alpha_pullback_y_eq_smul_omega` — same
- `weierstrass_equation_in_KE` — used by 4+ theorems
- `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one` — used by 8+ external callers
- `isogOneSub_negFrobenius_isSeparable` — used by 10+ external callers
- `kaehler_D_addPullback_x_eq_one_add_smul_omega` — used by RouteBInduction (3 uses)
- `kaehler_D_addPullback_x_pair_eq_smul_omega` — used by RouteBInduction (2 uses)
- `localExpand_algebraMap_eq_C` — used by 5+ sub-helpers
