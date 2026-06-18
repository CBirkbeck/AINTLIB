# Inventory: ./HasseWeil/Hasse/PoleDivisor2Tor.lean

**File purpose:** Ships the 2-torsion analogue of the `addPullbackNumerator_negFrobenius` bridge
(T-T21-2TORSION-BRIDGE). Everything in the non-2-torsion case (`PoleDivisorFallback.lean`) goes
through `ord_P (translateX_xy) = -2` at `-T`; for 2-torsion T this requires a different proof
because `-T = T` and the slope calculation is different. This file develops the 2-torsion chain
from scratch and assembles `lemma3_pole_at_T_at_2tor`, the companion to the non-2-torsion lemma 3.

**Import:** `HasseWeil.Hasse.PoleDivisorFallback` (single import).

**Total declarations:** 42 (41 theorems + 1 abbrev). No defs, no instances.

---

## Section: TwoTorBridges

### `theorem ord_P_x_gen_sub_const_ge_two_at_2tor`
- **Type**: `(xk yk : K) → W.toAffine.Nonsingular xk yk → yk = W.toAffine.negY xk yk → (2 : ℤ) ≤ (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns) (x_gen W - algebraMap K KE xk)`
- **What**: At a smooth 2-torsion point `(xk, yk)`, the order of `x_gen − xk` at the negated point is at least 2.
- **How**: Uses the curve identity `(y − yk)·A = (x − xk)·(B − a₁·yk)` (`curve_identity_translate`), the shipped `ord_P(y − yk) = 1` (`ord_P_y_gen_sub_negY_const_eq_one_of_2_tor`), and `ord_P A ≥ 1` (`one_le_ord_P_A_at_2tor`); applies `SmoothPlaneCurve.ord_P_mul` twice and `ord_P B_minus_a1_yk = 0` to conclude.
- **Hypotheses**: `K` field with decidable equality, `W.toAffine.IsElliptic`, `(xk,yk)` nonsingular, `yk = negY xk yk` (2-torsion).
- **Uses from project**: `curve_identity_translate`, `ord_P_y_gen_sub_negY_const_eq_one_of_2_tor`, `one_le_ord_P_A_at_2tor`, `ord_P_B_minus_a1_yk_eq_zero_at_2tor`, `SmoothPlaneCurve.ord_P_mul`, `negSmoothPoint`, `x_gen`, `y_gen`, `W_smooth`
- **Used by**: `ord_P_A_eq_one_at_2tor` (direct call), `ord_P_x_gen_sub_const_eq_two_at_2tor` (indirect via `ord_P_A_eq_one_at_2tor`)
- **Visibility**: public
- **Lines**: 79–166, proof length ~88 lines
- **Notes**: Proof >30 lines. Has `omit [Fintype K]` (the `Fintype` hypothesis is not needed for this step).

---

### `theorem ord_P_A_eq_one_at_2tor`
- **Type**: `(xk yk : K) → W.toAffine.Nonsingular xk yk → yk = negY xk yk → (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns) (y_gen W + algebraMap K KE yk + algebraMap K KE W.a₁ * x_gen W + algebraMap K KE W.a₃) = 1`
- **What**: The auxiliary factor `A = y + yk + a₁x + a₃` has ord exactly 1 at the 2-torsion point.
- **How**: Rewrites via `A_factorization_at_2tor`, applies `ord_P_y_gen_sub_negY_const_eq_one_of_2_tor` to get `ord(y − yk) = 1`, calls `ord_P_x_gen_sub_const_ge_two_at_2tor` for the a₁·(x−xk) ≥ 2 bound, then strict-comparison `SmoothPlaneCurve.ord_P_add_eq_of_lt`.
- **Hypotheses**: Same as above.
- **Uses from project**: `A_factorization_at_2tor`, `ord_P_y_gen_sub_negY_const_eq_one_of_2_tor`, `ord_P_x_gen_sub_const_ge_two_at_2tor`, `ord_P_algebraMap_F_nonneg`, `SmoothPlaneCurve.ord_P_mul`, `SmoothPlaneCurve.ord_P_add_eq_of_lt`
- **Used by**: `ord_P_translateSlope_xy_eq_neg_one_at_2tor`, `ord_P_x_gen_sub_const_eq_two_at_2tor`, `ord_P_translateY_xy_eq_neg_three_at_2tor`
- **Visibility**: public
- **Lines**: 167–217, proof length ~51 lines
- **Notes**: Proof >30 lines. Has `omit [Fintype K]`.

---

### `theorem ord_P_translateSlope_xy_eq_neg_one_at_2tor`
- **Type**: `(xk yk : K) → Nonsingular xk yk → yk = negY xk yk → (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns) (translateSlope_xy W xk yk) = -1`
- **What**: The addition slope `slope = Bma / A` at 2-torsion has ord exactly -1 at the negated point.
- **How**: Identifies `slope = Bma / A` via `translateSlope_xy_eq` and the curve identity; uses `ord_P_A_eq_one_at_2tor` and `ord_P_B_minus_a1_yk_eq_zero_at_2tor`, then `SmoothPlaneCurve.ord_P_inv` and `ord_P_mul`.
- **Hypotheses**: Same.
- **Uses from project**: `ord_P_A_eq_one_at_2tor`, `ord_P_B_minus_a1_yk_eq_zero_at_2tor`, `x_gen_sub_const_ne_zero`, `translateSlope_xy_eq`, `curve_identity_translate`, `SmoothPlaneCurve.ord_P_mul`, `SmoothPlaneCurve.ord_P_inv`, `SmoothPlaneCurve.ord_P_eq_top_iff`
- **Used by**: `ord_P_translateX_xy_eq_neg_two_at_2tor`
- **Visibility**: public
- **Lines**: 218–276, proof length ~59 lines
- **Notes**: Proof >30 lines. Has `omit [Fintype K]`.

---

### `theorem ord_P_translateX_xy_eq_neg_two_at_2tor`
- **Type**: `(xk yk : K) → Nonsingular xk yk → yk = negY xk yk → (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns) (translateX_xy W xk yk) = -2`
- **What**: The translation of x_gen under addition by `(xk, yk)` has ord exactly -2 at 2-torsion.
- **How**: Writes `translateX_xy = slope² + rest`, gets `ord(slope²) = -2` via squaring `ord_P_translateSlope_xy_eq_neg_one_at_2tor`, shows `ord(rest) ≥ -1`, applies `SmoothPlaneCurve.ord_P_add_eq_of_lt` (strict comparison -2 < -1). Uses `WeierstrassCurve.Affine.addX` unfolding and `ring`.
- **Hypotheses**: Same.
- **Uses from project**: `ord_P_translateSlope_xy_eq_neg_one_at_2tor`, `ord_P_algebraMap_F_nonneg`, `ord_P_x_gen_nonneg`, `SmoothPlaneCurve.ord_P_mul`, `SmoothPlaneCurve.ord_P_neg`, `SmoothPlaneCurve.ord_P_add_le`, `SmoothPlaneCurve.ord_P_add_eq_of_lt`, `SmoothPlaneCurve.ord_P_zero`, `W_KE`
- **Used by**: `ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two_at_2tor`
- **Visibility**: public
- **Lines**: 277–394, proof length ~118 lines
- **Notes**: Proof >30 lines (longest non-Y proof, 118 lines). Has `omit [Fintype K]`.

---

### `theorem ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two_at_2tor`
- **Type**: `(xT yT : K) → Nonsingular xT yT → yT = negY xT yT → (W_smooth W).ord_P ⟨xT,yT,h_ns⟩ (translateAlgEquivOfPoint W (-(Affine.Point.some xT yT h_ns)) (x_gen W)) = -2`
- **What**: The τ_{-T}-translate of x_gen evaluated at the smooth point T has ord -2 when T is 2-torsion.
- **How**: Applies `neg_some_eq_some` to rewrite `-T`, then `translateAlgEquivOfPoint_some_apply_x_gen`; transfers the 2-torsion hypothesis through the negY involution; equates the negated SmoothPoint with T via `SmoothPoint.ext` and `h_negY_negY`; finally applies `ord_P_translateX_xy_eq_neg_two_at_2tor`.
- **Hypotheses**: Same, plus `[Fintype K]`.
- **Uses from project**: `neg_some_eq_some`, `translateAlgEquivOfPoint_some_apply_x_gen`, `ord_P_translateX_xy_eq_neg_two_at_2tor`, `negSmoothPoint`, `SmoothPlaneCurve.SmoothPoint.ext`
- **Used by**: `bridge_at_x_gen_of_2_tor`
- **Visibility**: public
- **Lines**: 395–442, proof length ~48 lines
- **Notes**: Proof >30 lines.

---

### `theorem bridge_at_x_gen_of_2_tor`
- **Type**: `(xT yT : K) → Nonsingular xT yT → yT = negY xT yT → (W_smooth W).ord_P ⟨xT,yT,h_ns⟩ (translateAlgEquivOfPoint W (-(Affine.Point.some xT yT h_ns)) (x_gen W)) = (W_smooth W).ordAtInfty (x_gen W)`
- **What**: The ord-at-T of τ_{-T}(x_gen) equals the ord-at-infinity of x_gen (both = -2) at 2-torsion.
- **How**: Rewrites via `ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two_at_2tor` (= -2) and `ordAtInfty_x_gen` (= -2).
- **Hypotheses**: K fintype, nonsingular 2-torsion T.
- **Uses from project**: `ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two_at_2tor`, `ordAtInfty_x_gen`
- **Used by**: `bridge_at_x_gen_pow_card_of_2_tor`, `bridge_at_x_gen_pow_card_sub_x_gen_of_2_tor`, `bridge_at_x_gen_sub_x_gen_pow_card_of_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_of_2_tor`, `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor`, `bridge_at_x_gen_sq_mul_negFrobeniusIsog_pullback_x_gen_of_2_tor`, `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_of_2_tor`, `bridge_at_x_gen_add_negFrobeniusIsog_pullback_x_gen_of_2_tor` (8 callers)
- **Visibility**: public
- **Lines**: 443–454, proof length ~12 lines

---

### `theorem bridge_at_x_gen_pow_card_of_2_tor`
- **Type**: `... → (W_smooth W).ord_P ⟨xT,yT,h_ns⟩ (translateAlgEquivOfPoint W ... (x_gen W ^ Fintype.card K)) = (W_smooth W).ordAtInfty (x_gen W ^ Fintype.card K)`
- **What**: The bridge holds for the q-power x_gen^q at 2-torsion.
- **How**: Applies generic helper `ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base` with the x_gen base bridge.
- **Hypotheses**: Same, no `hq` needed.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base`, `bridge_at_x_gen_of_2_tor`, `x_gen_ne_zero`
- **Used by**: `bridge_at_x_gen_pow_card_sub_x_gen_of_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_of_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor` (indirectly), `bridge_at_x_gen_sq_mul_negFrobeniusIsog_pullback_x_gen_of_2_tor`, `bridge_at_negFrobeniusIsog_pullback_y_gen_of_2_tor`
- **Visibility**: public
- **Lines**: 458–468, proof length ~11 lines

---

### `theorem bridge_at_x_gen_pow_card_sub_x_gen_of_2_tor`
- **Type**: `... → 2 ≤ Fintype.card K → (W_smooth W).ord_P ... (translateAlgEquivOfPoint ... (x_gen W ^ q - x_gen W)) = (W_smooth W).ordAtInfty (x_gen W ^ q - x_gen W)`
- **What**: Bridge for `x_gen^q − x_gen` at 2-torsion.
- **How**: Uses strict-comparison helper `ord_P_translateAlgEquivOfPoint_sub_eq_ordAtInfty_of_strict_lt` with the two component bridges and `Conditional.ordAtInfty_x_gen_pow_card_lt_x_gen`.
- **Hypotheses**: K fintype, q ≥ 2.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_sub_eq_ordAtInfty_of_strict_lt`, `bridge_at_x_gen_pow_card_of_2_tor`, `bridge_at_x_gen_of_2_tor`, `Conditional.ordAtInfty_x_gen_pow_card_lt_x_gen`
- **Used by**: `bridge_at_x_gen_sub_x_gen_pow_card_of_2_tor`
- **Visibility**: public
- **Lines**: 474–488, proof length ~15 lines

---

### `theorem bridge_at_x_gen_sub_x_gen_pow_card_of_2_tor`
- **Type**: `... → 2 ≤ Fintype.card K → (W_smooth W).ord_P ... (translateAlgEquivOfPoint ... (x_gen W - x_gen W ^ q)) = (W_smooth W).ordAtInfty (x_gen W - x_gen W ^ q)`
- **What**: Bridge for the negated combination `x_gen − x_gen^q` at 2-torsion.
- **How**: Rewrites as `-(x_gen^q − x_gen)` then applies `ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base`.
- **Hypotheses**: K fintype, q ≥ 2.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base`, `bridge_at_x_gen_pow_card_sub_x_gen_of_2_tor`
- **Used by**: `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_2_tor`
- **Visibility**: public
- **Lines**: 492–507, proof length ~16 lines

---

### `theorem bridge_at_negFrobeniusIsog_pullback_x_gen_of_2_tor`
- **Type**: `... → (W_smooth W).ord_P ... (translateAlgEquivOfPoint ... ((negFrobeniusIsog W).pullback (x_gen W))) = (W_smooth W).ordAtInfty ((negFrobeniusIsog W).pullback (x_gen W))`
- **What**: Bridge for `π_neg^*(x_gen)` at 2-torsion, where π_neg is the neg-Frobenius isogeny.
- **How**: Unfolds via `negFrobeniusIsog_pullback_x_gen` and `frobeniusIsog_pullback_apply` to identify with x_gen^q, then applies `bridge_at_x_gen_pow_card_of_2_tor`.
- **Uses from project**: `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `bridge_at_x_gen_pow_card_of_2_tor`
- **Used by**: `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor`, `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor`, `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_of_2_tor`
- **Visibility**: public
- **Lines**: 512–521, proof length ~10 lines

---

### `theorem bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_2_tor`
- **Type**: `... → 2 ≤ Fintype.card K → bridge for (x_gen W - π_neg^*(x_gen W))`
- **What**: Bridge for the slope denominator `x_gen − π_neg^*(x_gen)` at 2-torsion.
- **How**: Identifies with `x_gen - x_gen^q` and applies `bridge_at_x_gen_sub_x_gen_pow_card_of_2_tor`.
- **Uses from project**: `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `bridge_at_x_gen_sub_x_gen_pow_card_of_2_tor`
- **Used by**: `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor`
- **Visibility**: public
- **Lines**: 525–536, proof length ~12 lines

---

### `theorem bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor`
- **Type**: `... → 2 ≤ q → bridge for (x_gen W - π_neg^*(x_gen W))^2`
- **What**: Bridge for the squared slope denominator at 2-torsion.
- **How**: Pow on the slope denominator bridge via `ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base`.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base`, `x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero`, `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_2_tor`
- **Used by**: `bridge_at_addPullback_x_negFrobenius_of_2_tor`
- **Visibility**: public
- **Lines**: 541–555, proof length ~15 lines

---

### `theorem bridge_at_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor`
- **Type**: `... → bridge for (π_neg^*(x_gen W))^2`
- **What**: Bridge for the square of the Frobenius-pullback of x_gen at 2-torsion.
- **How**: Pow on `bridge_at_negFrobeniusIsog_pullback_x_gen_of_2_tor`.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base`, `bridge_at_negFrobeniusIsog_pullback_x_gen_of_2_tor`, `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `x_gen_ne_zero`
- **Used by**: `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor`
- **Visibility**: public
- **Lines**: 560–573, proof length ~14 lines

---

### `theorem bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor`
- **Type**: `... → bridge for x_gen W * (π_neg^*(x_gen W))^2` (T7 term)
- **What**: Bridge for the T7 dominant term `x · (πx)²` at 2-torsion.
- **How**: Mul on bridges for x_gen and (πx)^2 via `ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each`.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each`, `bridge_at_x_gen_of_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor`, `x_gen_ne_zero`, `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_2_tor`
- **Visibility**: public
- **Lines**: 578–594, proof length ~17 lines

---

### `theorem bridge_at_x_gen_sq_mul_negFrobeniusIsog_pullback_x_gen_of_2_tor`
- **Type**: `... → bridge for x_gen W ^ 2 * π_neg^*(x_gen W)` (T6 term)
- **What**: Bridge for the T6 term `x² · πx` at 2-torsion.
- **How**: Builds x²-bridge via pow on `bridge_at_x_gen_of_2_tor`, then mul with `bridge_at_negFrobeniusIsog_pullback_x_gen_of_2_tor`.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base`, `ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each`, `bridge_at_x_gen_of_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_of_2_tor`, `x_gen_ne_zero`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_2_tor`
- **Visibility**: public
- **Lines**: 598–620, proof length ~23 lines

---

### `theorem bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_of_2_tor`
- **Type**: `... → bridge for x_gen W * π_neg^*(x_gen W)` (T1/T8 building block)
- **What**: Bridge for the product `x · πx` at 2-torsion.
- **How**: Mul on x_gen bridge and πx bridge.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each`, `bridge_at_x_gen_of_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_of_2_tor`, `x_gen_ne_zero`
- **Used by**: `bridge_at_T8_two_a2_x_pi_x_of_2_tor`
- **Visibility**: public
- **Lines**: 624–655, proof length ~32 lines
- **Notes**: Proof >30 lines (marginally).

---

### `theorem ord_P_x_gen_sub_const_eq_two_at_2tor`
- **Type**: `(xk yk : K) → Nonsingular xk yk → yk = negY xk yk → (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns) (x_gen W - algebraMap K KE xk) = 2`
- **What**: Tightens `ord_P (x_gen − xk) ≥ 2` to exact equality 2 at 2-torsion.
- **How**: Re-runs the curve identity computation but uses `ord_P_A_eq_one_at_2tor` (exact, not lower bound) and `ord_P_B_minus_a1_yk_eq_zero_at_2tor` to get `ord((y−yk)·A) = 1 + 1 = 2` exactly, then `ord(x−xk) = 2 − 0 = 2`.
- **Hypotheses**: No `[Fintype K]` needed (`omit`).
- **Uses from project**: `curve_identity_translate`, `ord_P_y_gen_sub_negY_const_eq_one_of_2_tor`, `ord_P_A_eq_one_at_2tor`, `ord_P_B_minus_a1_yk_eq_zero_at_2tor`, `SmoothPlaneCurve.ord_P_mul`
- **Used by**: `ord_P_translateY_xy_eq_neg_three_at_2tor`
- **Visibility**: public
- **Lines**: 656–734, proof length ~79 lines
- **Notes**: Proof >30 lines. Has `omit [Fintype K]`.

---

### `theorem ord_P_translateY_xy_eq_neg_three_at_2tor`
- **Type**: `(xk yk : K) → Nonsingular xk yk → yk = negY xk yk → (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns) (translateY_xy W xk yk) = -3`
- **What**: The translation of y_gen by 2-torsion `(xk, yk)` has ord exactly -3 at the negated point.
- **How**: Uses the algebraic identity `translateY_xy * xd^3 = -yd^3 + T2 + T3 + T4` (via `translateY_xy_mul_cube_eq`), with `ord(yd) = 1` and `ord(xd) = 2` from the 2-torsion lemmas; the dominant term `-yd^3` has `ord = 3`, all corrections T2/T3/T4 have `ord ≥ 4`; strict comparison forces `ord(translateY) + 6 = 3`, i.e. `ord(translateY) = -3`.
- **Hypotheses**: No `[Fintype K]`, has `set_option maxHeartbeats 1600000`.
- **Uses from project**: `ord_P_x_gen_sub_const_eq_two_at_2tor`, `ord_P_y_gen_sub_negY_const_eq_one_of_2_tor`, `ord_P_x_gen_nonneg`, `ord_P_algebraMap_F_nonneg`, `SmoothPlaneCurve.ord_P_mul`, `SmoothPlaneCurve.ord_P_pow`, `SmoothPlaneCurve.ord_P_neg`, `SmoothPlaneCurve.ord_P_add_le`, `SmoothPlaneCurve.ord_P_add_eq_of_lt`, `SmoothPlaneCurve.ord_P_zero`, `translateY_xy_mul_cube_eq`, `pointValuation_y_gen_le_one`
- **Used by**: `twoTorYValueWitness_discharge` (directly), `TwoTorYValueWitness` (comment references)
- **Visibility**: public
- **Lines**: 735–1096, proof length ~362 lines
- **Notes**: BY FAR the longest proof in the file (362 lines). `set_option maxHeartbeats 1600000` with NO justifying comment. Has `omit [Fintype K]`.

---

### `abbrev TwoTorYValueWitness`
- **Type**: `(xT yT : K) → W.toAffine.Nonsingular xT yT → Prop` — the predicate `(W_smooth W).ord_P (negSmoothPoint W xT (negY xT yT) ...) (translateY_xy W xT (negY xT yT)) = -3`
- **What**: Type abbreviation packaging the y-side substantive value (ord = -3) at 2-torsion as a named Prop, so witness-parametric bridges can carry it.
- **How**: Pure abbreviation/definition, no proof.
- **Hypotheses**: None (is a Prop, not a proof).
- **Uses from project**: `negSmoothPoint`, `translateY_xy`, `W_smooth`
- **Used by**: `twoTorYValueWitness_discharge`, `bridge_at_y_gen_of_2_tor_of_witness`, `bridge_at_y_gen_pow_card_of_2_tor_of_witness`, `bridge_at_y_gen_sub_y_gen_pow_card_of_2_tor_of_witness`
- **Visibility**: public
- **Lines**: 1097–1102

---

### `theorem twoTorYValueWitness_discharge`
- **Type**: `(xT yT : K) → Nonsingular xT yT → yT = negY xT yT → TwoTorYValueWitness W xT yT h_ns`
- **What**: Shows that `TwoTorYValueWitness` is provable (not just a hypothesis) for any smooth 2-torsion point; discharges it using `ord_P_translateY_xy_eq_neg_three_at_2tor`.
- **How**: Transfers the 2-torsion condition through the negY involution (negY(negY xT yT) = yT), then calls `ord_P_translateY_xy_eq_neg_three_at_2tor`.
- **Uses from project**: `ord_P_translateY_xy_eq_neg_three_at_2tor`
- **Used by**: `bridge_at_y_gen_of_2_tor`, `bridge_at_y_gen_pow_card_of_2_tor`, `bridge_at_y_gen_sub_y_gen_pow_card_of_2_tor`
- **Visibility**: public
- **Lines**: 1107–1121, proof length ~15 lines

---

### `theorem bridge_at_y_gen_of_2_tor_of_witness`
- **Type**: `... → TwoTorYValueWitness W xT yT h_ns → (W_smooth W).ord_P ⟨xT,yT,h_ns⟩ (translateAlgEquivOfPoint ... (y_gen W)) = (W_smooth W).ordAtInfty (y_gen W)`
- **What**: Witness-parametric y-side base bridge: given the y-value hypothesis, produces the bridge for y_gen.
- **How**: Mirrors `ord_T_translateAlgEquivOfPoint_neg_y_gen_eq_neg_three` structure: rewrites -T, applies `translateAlgEquivOfPoint_some_apply_y_gen`, equates SmoothPoints via `h_negY_negY`, substitutes the witness, and matches with `ordAtInfty_y_gen`.
- **Uses from project**: `neg_some_eq_some`, `translateAlgEquivOfPoint_some_apply_y_gen`, `SmoothPlaneCurve.SmoothPoint.ext`, `ordAtInfty_y_gen`
- **Used by**: `bridge_at_y_gen_pow_card_of_2_tor_of_witness`, `bridge_at_y_gen_sub_y_gen_pow_card_of_2_tor_of_witness`, `bridge_at_y_gen_of_2_tor`
- **Visibility**: public
- **Lines**: 1127–1163, proof length ~37 lines
- **Notes**: Proof >30 lines.

---

### `theorem bridge_at_x_gen_add_negFrobeniusIsog_pullback_x_gen_of_2_tor`
- **Type**: `... → 2 ≤ q → bridge for x_gen W + π_neg^*(x_gen W)`
- **What**: Bridge for x + πx at 2-torsion.
- **How**: Identifies πx = x^q, rewrites with add_comm, then applies `ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt` with x^q bridge, x bridge, and `Conditional.ordAtInfty_x_gen_pow_card_lt_x_gen`.
- **Uses from project**: `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `Conditional.ordAtInfty_x_gen_pow_card_lt_x_gen`, `ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt`, `bridge_at_x_gen_pow_card_of_2_tor`, `bridge_at_x_gen_of_2_tor`
- **Used by**: `bridge_at_T1_a4_x_add_pi_x_of_2_tor`
- **Visibility**: public
- **Lines**: 1164–1185, proof length ~22 lines

---

### `theorem bridge_at_y_gen_pow_card_of_2_tor_of_witness`
- **Type**: `... → TwoTorYValueWitness ... → bridge for y_gen W ^ Fintype.card K`
- **What**: Witness-parametric y-side pow bridge: bridge for y^q given the witness.
- **How**: Pow on `bridge_at_y_gen_of_2_tor_of_witness` via `ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base`.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base`, `y_gen_ne_zero`, `bridge_at_y_gen_of_2_tor_of_witness`
- **Used by**: `bridge_at_y_gen_sub_y_gen_pow_card_of_2_tor_of_witness`, `bridge_at_y_gen_pow_card_of_2_tor`
- **Visibility**: public
- **Lines**: 1189–1201, proof length ~13 lines

---

### `theorem bridge_at_y_gen_sub_y_gen_pow_card_of_2_tor_of_witness`
- **Type**: `... → TwoTorYValueWitness ... → 2 ≤ q → bridge for y_gen W - y_gen W ^ q`
- **What**: Witness-parametric bridge for `y − y^q` at 2-torsion.
- **How**: Rewrites as `-(y^q − y)`; applies neg-bridge after strict-comparison sub-bridge; proves `ord_∞(y^q) < ord_∞(y)` by computing `ord_∞(y^q) = q·(-3) < -3`.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base`, `ord_P_translateAlgEquivOfPoint_sub_eq_ordAtInfty_of_strict_lt`, `bridge_at_y_gen_pow_card_of_2_tor_of_witness`, `bridge_at_y_gen_of_2_tor_of_witness`, `ordAtInfty_y_gen`, `SmoothPlaneCurve.ordAtInfty_pow_of_ord_eq`, `y_gen_ne_zero`
- **Used by**: `bridge_at_y_gen_sub_y_gen_pow_card_of_2_tor`
- **Visibility**: public
- **Lines**: 1207–1249, proof length ~43 lines
- **Notes**: Proof >30 lines.

---

### `theorem bridge_at_y_gen_of_2_tor`
- **Type**: `... → bridge for y_gen W` (UNCONDITIONAL)
- **What**: Unconditional y-side base bridge: composes witness-parametric form with `twoTorYValueWitness_discharge`.
- **How**: One-liner: applies `bridge_at_y_gen_of_2_tor_of_witness` with `twoTorYValueWitness_discharge`.
- **Uses from project**: `bridge_at_y_gen_of_2_tor_of_witness`, `twoTorYValueWitness_discharge`
- **Used by**: `bridge_at_y_gen_pow_card_of_2_tor`, `bridge_at_y_gen_sub_y_gen_pow_card_of_2_tor`, `bridge_at_negFrobeniusIsog_pullback_y_gen_of_2_tor`, `bridge_at_y_gen_add_negFrobeniusIsog_pullback_y_gen_of_2_tor`, `bridge_at_y_gen_mul_negFrobeniusIsog_pullback_y_gen_of_2_tor`, `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_y_gen_of_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_mul_y_gen_of_2_tor` (7+ callers; the most-used bridge in the y-side)
- **Visibility**: public
- **Lines**: 1250–1259, proof length ~10 lines

---

### `theorem bridge_at_y_gen_pow_card_of_2_tor`
- **Type**: `... → bridge for y_gen W ^ q` (UNCONDITIONAL)
- **What**: Unconditional pow bridge for y^q.
- **How**: `bridge_at_y_gen_pow_card_of_2_tor_of_witness` + `twoTorYValueWitness_discharge`.
- **Uses from project**: `bridge_at_y_gen_pow_card_of_2_tor_of_witness`, `twoTorYValueWitness_discharge`
- **Used by**: `bridge_at_negFrobeniusIsog_pullback_y_gen_of_2_tor`, `bridge_at_y_gen_sub_y_gen_pow_card_of_2_tor`
- **Visibility**: public
- **Lines**: 1263–1272, proof length ~10 lines

---

### `theorem bridge_at_y_gen_sub_y_gen_pow_card_of_2_tor`
- **Type**: `... → 2 ≤ q → bridge for y_gen W - y_gen W ^ q` (UNCONDITIONAL)
- **What**: Unconditional bridge for `y − y^q`.
- **How**: `bridge_at_y_gen_sub_y_gen_pow_card_of_2_tor_of_witness` + discharge.
- **Uses from project**: `bridge_at_y_gen_sub_y_gen_pow_card_of_2_tor_of_witness`, `twoTorYValueWitness_discharge`
- **Used by**: (not referenced in this file; exported)
- **Visibility**: public
- **Lines**: 1275–1285, proof length ~11 lines

---

### `theorem bridge_at_negFrobeniusIsog_pullback_y_gen_of_2_tor`
- **Type**: `... → 2 ≤ q → bridge for π_neg^*(y_gen W)` (UNCONDITIONAL)
- **What**: Bridge for the neg-Frobenius pullback of y_gen at 2-torsion.
- **How**: Expands `negFrob.pullback(y_gen) = -y^q - a₁x^q - a₃`; builds individual bridges for each term, then applies add-bridges with strict ord comparisons (−3q dominates −2q). Case-splits on `a₁ = 0` and `a₃ = 0`.
- **Uses from project**: `Conditional.negFrobeniusIsog_pullback_y_gen_eq_pow_form`, `bridge_at_y_gen_pow_card_of_2_tor`, `bridge_at_x_gen_pow_card_of_2_tor`, `ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base`, `ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base`, `ord_P_translateAlgEquivOfPoint_algebraMap_eq_ordAtInfty`, `ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt`, `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `Conditional.ordAtInfty_neg_y_gen_pow_card_lt_rest`
- **Used by**: `bridge_at_y_gen_add_negFrobeniusIsog_pullback_y_gen_of_2_tor`, `bridge_at_y_gen_mul_negFrobeniusIsog_pullback_y_gen_of_2_tor`, `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_y_gen_of_2_tor`
- **Visibility**: public
- **Lines**: 1292–1439, proof length ~148 lines
- **Notes**: Proof >30 lines (148 lines). Substantial case analysis.

---

### `theorem bridge_at_T1_a4_x_add_pi_x_of_2_tor`
- **Type**: `... → 2 ≤ q → bridge for a₄ · (x + π·x)`
- **What**: Bridge for the T1 Num term `a₄·(x + πx)` at 2-torsion.
- **How**: const_mul on `bridge_at_x_gen_add_negFrobeniusIsog_pullback_x_gen_of_2_tor`.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base`, `bridge_at_x_gen_add_negFrobeniusIsog_pullback_x_gen_of_2_tor`, `Conditional.x_gen_add_negFrobeniusIsog_pullback_x_gen_ne_zero`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_2_tor`
- **Visibility**: public
- **Lines**: 1443–1458, proof length ~16 lines

---

### `theorem bridge_at_T2_two_a6_of_2_tor`
- **Type**: `... → bridge for 2 * a₆`
- **What**: Bridge for the constant T2 = `2·a₆` term via algebraMap.
- **How**: Rewrites `2 * a₆ = algebraMap K ... (2 * a₆)` and applies `ord_P_translateAlgEquivOfPoint_algebraMap_eq_ordAtInfty`.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_algebraMap_eq_ordAtInfty`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_2_tor`
- **Visibility**: public
- **Lines**: 1462–1479, proof length ~18 lines

---

### `theorem bridge_at_y_gen_add_negFrobeniusIsog_pullback_y_gen_of_2_tor`
- **Type**: `... → 2 ≤ q → bridge for y_gen W + π_neg^*(y_gen W)`
- **What**: Bridge for `y + πy` (building block for T3) at 2-torsion.
- **How**: Rewrites with add_comm; strict-comparison with `ord(πy) < ord(y)` since `-3q < -3`; then applies the add-bridge helper.
- **Uses from project**: `bridge_at_negFrobeniusIsog_pullback_y_gen_of_2_tor`, `bridge_at_y_gen_of_2_tor`, `ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt`, `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `ordAtInfty_y_gen`
- **Used by**: `bridge_at_T3_a3_y_add_pi_y_of_2_tor`
- **Visibility**: public
- **Lines**: 1484–1509, proof length ~26 lines

---

### `theorem bridge_at_y_gen_mul_negFrobeniusIsog_pullback_y_gen_of_2_tor`
- **Type**: `... → 2 ≤ q → bridge for y_gen W * π_neg^*(y_gen W)` (building block for T4)
- **What**: Bridge for the product `y · πy` at 2-torsion.
- **How**: Mul-bridge; shows πy ≠ 0 via `ordAtInfty_negFrobeniusIsog_pullback_y_gen`.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each`, `bridge_at_y_gen_of_2_tor`, `bridge_at_negFrobeniusIsog_pullback_y_gen_of_2_tor`, `y_gen_ne_zero`, `ordAtInfty_negFrobeniusIsog_pullback_y_gen`
- **Used by**: `bridge_at_T4_two_y_pi_y_of_2_tor`
- **Visibility**: public
- **Lines**: 1513–1533, proof length ~21 lines

---

### `theorem bridge_at_T4_two_y_pi_y_of_2_tor`
- **Type**: `... → 2 ≤ q → bridge for 2 · y_gen W · π_neg^*(y_gen W)`
- **What**: Bridge for the T4 term `2·y·πy` at 2-torsion.
- **How**: Rewrites `2·y·πy = (algebraMap 2) · (y·πy)` and applies const_mul bridge.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base`, `bridge_at_y_gen_mul_negFrobeniusIsog_pullback_y_gen_of_2_tor`, `y_gen_ne_zero`, `ordAtInfty_negFrobeniusIsog_pullback_y_gen`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_2_tor`
- **Visibility**: public
- **Lines**: 1537–1567, proof length ~31 lines
- **Notes**: Proof marginally >30 lines.

---

### `theorem bridge_at_T8_two_a2_x_pi_x_of_2_tor`
- **Type**: `... → bridge for 2·a₂·x·πx` (no `hq` needed)
- **What**: Bridge for the T8 term `2·a₂·x·πx` at 2-torsion.
- **How**: Rewrites `2·a₂·x·πx = algebraMap(2·a₂) · (x·πx)` and const_mul on `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_of_2_tor`.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base`, `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_of_2_tor`, `x_gen_ne_zero`, `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_2_tor`
- **Visibility**: public
- **Lines**: 1568–1594, proof length ~27 lines

---

### `theorem bridge_at_x_gen_mul_negFrobeniusIsog_pullback_y_gen_of_2_tor`
- **Type**: `... → 2 ≤ q → bridge for x_gen W * π_neg^*(y_gen W)` (part of T5)
- **What**: Bridge for the product `x · πy`.
- **How**: Mul-bridge with x_gen and πy; shows πy ≠ 0.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each`, `bridge_at_x_gen_of_2_tor`, `bridge_at_negFrobeniusIsog_pullback_y_gen_of_2_tor`, `x_gen_ne_zero`, `ordAtInfty_negFrobeniusIsog_pullback_y_gen`
- **Used by**: `bridge_at_x_pi_y_add_pi_x_y_of_2_tor`, `bridge_at_T5_a1_x_pi_y_add_pi_x_y_of_2_tor` (internal duplication of the πy ≠ 0 argument)
- **Visibility**: public
- **Lines**: 1598–1618, proof length ~21 lines

---

### `theorem bridge_at_negFrobeniusIsog_pullback_x_gen_mul_y_gen_of_2_tor`
- **Type**: `... → bridge for π_neg^*(x_gen W) * y_gen W` (part of T5; no `hq`)
- **What**: Bridge for the product `πx · y`.
- **How**: Mul-bridge with πx and y_gen.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each`, `bridge_at_negFrobeniusIsog_pullback_x_gen_of_2_tor`, `bridge_at_y_gen_of_2_tor`, `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `x_gen_ne_zero`, `y_gen_ne_zero`
- **Used by**: `bridge_at_x_pi_y_add_pi_x_y_of_2_tor`
- **Visibility**: public
- **Lines**: 1622–1637, proof length ~16 lines

---

### `theorem bridge_at_x_pi_y_add_pi_x_y_of_2_tor`
- **Type**: `... → 2 ≤ q → bridge for x·πy + πx·y`
- **What**: Bridge for the sum `x·πy + πx·y` appearing in T5; strict comparison: ord(x·πy) = −3q−2 < ord(πx·y) = −2q−3 (for q ≥ 2).
- **How**: Computes ordAtInfty of each product via mul-split and known values; strict comparison by linarith; applies add-bridge helper.
- **Uses from project**: `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_y_gen_of_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_mul_y_gen_of_2_tor`, `ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt`, `ordAtInfty_x_gen`, `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `ordAtInfty_negFrobeniusIsog_pullback_x_gen`, `ordAtInfty_y_gen`, `SmoothPlaneCurve.ordAtInfty_mul`
- **Used by**: `bridge_at_T5_a1_x_pi_y_add_pi_x_y_of_2_tor`
- **Visibility**: public
- **Lines**: 1641–1706, proof length ~66 lines
- **Notes**: Proof >30 lines (66 lines). Contains a duplicated πy ≠ 0 / πx ≠ 0 verification inside the `h_sum_ne` subproof.

---

### `theorem bridge_at_T5_a1_x_pi_y_add_pi_x_y_of_2_tor`
- **Type**: `... → 2 ≤ q → bridge for a₁·(x·πy + πx·y)` (T5 term)
- **What**: Bridge for T5 = `a₁·(x·πy + πx·y)` at 2-torsion.
- **How**: const_mul on `bridge_at_x_pi_y_add_pi_x_y_of_2_tor`; shows the sum ≠ 0 via ordAtInfty computations (large block inside the non-zero proof).
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base`, `bridge_at_x_pi_y_add_pi_x_y_of_2_tor`, `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `ordAtInfty_negFrobeniusIsog_pullback_x_gen`, `SmoothPlaneCurve.ordAtInfty_mul`, `SmoothPlaneCurve.ordAtInfty_add_eq_of_lt`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_2_tor`
- **Visibility**: public
- **Lines**: 1710–1796, proof length ~87 lines
- **Notes**: Proof >30 lines (87 lines). The non-zero proof for `h_sum_ne` essentially duplicates the strict-add ord argument from `bridge_at_x_pi_y_add_pi_x_y_of_2_tor`.

---

### `theorem bridge_at_T3_a3_y_add_pi_y_of_2_tor`
- **Type**: `... → 2 ≤ q → bridge for a₃·(y + πy)`
- **What**: Bridge for the T3 term `a₃·(y + πy)` at 2-torsion.
- **How**: const_mul on `bridge_at_y_gen_add_negFrobeniusIsog_pullback_y_gen_of_2_tor`.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base`, `bridge_at_y_gen_add_negFrobeniusIsog_pullback_y_gen_of_2_tor`, `Conditional.y_gen_add_negFrobeniusIsog_pullback_y_gen_ne_zero`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_2_tor`
- **Visibility**: public
- **Lines**: 1797–1812, proof length ~16 lines

---

### `theorem bridge_at_addPullbackNumerator_negFrobenius_of_2_tor`
- **Type**: `... → 2 ≤ q → (W_smooth W).ord_P ⟨xT,yT,h_ns⟩ (translateAlgEquivOfPoint ... (addPullbackNumerator_negFrobenius W)) = (W_smooth W).ordAtInfty (addPullbackNumerator_negFrobenius W)`
- **What**: The full Num bridge at 2-torsion: the ord of τ_{-T}(addPullbackNumerator) at T equals the ord-at-infinity.
- **How**: Unfolds via `addPullbackNumerator_negFrobenius_eq_reduced`, applies `Conditional.reduced_form_eq_dom_plus_list` to reduce to the T7-dominant + list form, then applies `ord_P_translateAlgEquivOfPoint_sum_dominant` with all 7 other-term bridges from the 2-torsion file and the T7 ord computation using `ordAtInfty_negFrobeniusIsog_pullback_x_gen` + `Conditional.ordAtInfty_T*_ge` bounds.
- **Uses from project**: `addPullbackNumerator_negFrobenius_eq_reduced`, `addPullbackNumerator_reduced_negFrobenius`, `Conditional.reduced_form_eq_dom_plus_list`, `ord_P_translateAlgEquivOfPoint_sum_dominant`, `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor`, `bridge_at_T1_a4_x_add_pi_x_of_2_tor`, `bridge_at_T2_two_a6_of_2_tor`, `bridge_at_T3_a3_y_add_pi_y_of_2_tor`, `bridge_at_T4_two_y_pi_y_of_2_tor`, `bridge_at_T5_a1_x_pi_y_add_pi_x_y_of_2_tor`, `bridge_at_x_gen_sq_mul_negFrobeniusIsog_pullback_x_gen_of_2_tor`, `bridge_at_T8_two_a2_x_pi_x_of_2_tor`, `Conditional.ordAtInfty_T1_ge`, `Conditional.ordAtInfty_T2_ge`, `Conditional.ordAtInfty_neg_T3_ge`, `Conditional.ordAtInfty_neg_T4_ge`, `Conditional.ordAtInfty_neg_T5_ge`, `Conditional.ordAtInfty_T6_ge`, `Conditional.ordAtInfty_T8_ge`, `ordAtInfty_negFrobeniusIsog_pullback_x_gen`, `ordAtInfty_x_gen`, `Conditional.withTop_int_lt_of_lt_of_le`, `ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base`
- **Used by**: `bridge_at_addPullback_x_negFrobenius_of_2_tor`
- **Visibility**: public
- **Lines**: 1822–1924, proof length ~103 lines
- **Notes**: Proof >30 lines (103 lines). Uses `List.mem_cons` pattern matching for the 7-term list, matching the non-2-torsion structure exactly.

---

### `theorem bridge_at_addPullback_x_negFrobenius_of_2_tor`
- **Type**: `... → 2 ≤ q → (W_smooth W).ord_P ⟨xT,yT,h_ns⟩ (translateAlgEquivOfPoint ... (addPullback_x W (negFrobeniusIsog W))) = (W_smooth W).ordAtInfty (addPullback_x W (negFrobeniusIsog W))`
- **What**: The bridge for `addPullback_x` (= Num / denom²) at 2-torsion, the key input to Lemma 3.
- **How**: Rewrites via `addPullbackNumerator_negFrobenius_eq` to express as Num / denom²; applies `ord_P_translateAlgEquivOfPoint_div_eq_ordAtInfty_of_each` with Num ≠ 0 (via ordAtInfty computation) and denom² ≠ 0.
- **Uses from project**: `addPullbackNumerator_negFrobenius_eq`, `x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero`, `ordAtInfty_addPullbackNumerator_reduced_negFrobenius_eq`, `ord_P_translateAlgEquivOfPoint_div_eq_ordAtInfty_of_each`, `bridge_at_addPullbackNumerator_negFrobenius_of_2_tor`, `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor`, `addPullbackNumerator_negFrobenius_eq_reduced`
- **Used by**: `lemma3_pole_at_T_at_2tor`
- **Visibility**: public
- **Lines**: 1925–1968, proof length ~44 lines
- **Notes**: Proof >30 lines.

---

### `theorem lemma3_pole_at_T_at_2tor`
- **Type**: `(xT yT : K) → Nonsingular xT yT → yT = negY xT yT → 2 ≤ q → (W_smooth W).ord_P ⟨xT,yT,h_ns⟩ ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) = -2`
- **What**: The ord-2 pole property for `isogOneSub_negFrobenius`'s pullback of x_gen at 2-torsion kernel points.
- **How**: Calls `Conditional.Conditional.lemma3_pole_at_T_of_bridge_and_invariance` with (1) `bridge_at_addPullback_x_negFrobenius_of_2_tor` and (2) a proof that `-T` is in the kernel (since `(1−π̄)(−T) = -T − (-(−T)) = 0`) combined with `xy_family_isogOneSub_negFrobenius`.
- **Uses from project**: `Conditional.Conditional.lemma3_pole_at_T_of_bridge_and_invariance`, `bridge_at_addPullback_x_negFrobenius_of_2_tor`, `isogOneSub_negFrobenius`, `isogOneSub_negFrobenius_toAddMonoidHom`, `xy_family_isogOneSub_negFrobenius`
- **Used by**: unused in this file (exported; consumed by the L6 witnesses chain)
- **Visibility**: public
- **Lines**: 1969–1992, proof length ~24 lines
- **Notes**: This is the leaf export of the entire file; no other theorem in this file calls it.
