# Inventory: ./HasseWeil/Hasse/PoleDivisorFallback.lean

**File**: `HasseWeil/Hasse/PoleDivisorFallback.lean`
**Lines**: 3832
**Total declarations**: 81 (1 def, 80 theorems, 0 instances)
**Sorries**: none (no `sorry` tactic/term in any body; mentions of "sorry" in comments only)

**Set-option maxHeartbeats**: line 3406 (`set_option maxHeartbeats 1600000` with `set_option synthInstance.maxHeartbeats 1600000`, applied to `K_E_separable_over_LinfAt_gamma_pullback_x_gen`; no justifying comment)

**Purpose**: Plan-C path to `pc_sepDeg_eq_pointCount` for `γ = isogOneSub_negFrobenius` (1−π isogeny over F_q). Implements the pole-divisor strategy: `ord_∞(γ*x) = -2`, translation-invariance bridges, numerator bridge, a `Prop`-valued Computation-A obligation, and the final assembly consumers. Also develops AlgEquiv-based bridges between `IntermediateField.adjoin K {f}` and `LinfAt f`/`FractionRing K[X]` framings, and discharges `Algebra.IsSeparable` for the LinfAt structure.

---

## Declarations (outside `Conditional` namespace)

### `def ComputationA_bridge_pullback_x_gen`

- **Type**: `(W : WeierstrassCurve K) → [W.toAffine.IsElliptic] → (hq : 2 ≤ Fintype.card K) → Prop`
- **What**: A named `Prop` asserting the Computation-A identity: `[K(E) : K(γ*x_gen)] = degreePoleDivisor(γ*x_gen)`, where the RHS is expressed as the sum of negative parts of `projectiveDivisorOf` over its support.
- **How**: Pure definition; no proof body. Packages the "function-field extension degree equals pole-divisor degree" identity as a named obligation.
- **Hypotheses**: Elliptic curve `W` over finite field `K`, `#K ≥ 2`.
- **Uses from project**: `isogOneSub_negFrobenius`, `x_gen`, `Curves.SmoothPlaneCurve.projectiveDivisorOf`, `W_smooth`
- **Used by**: `pc_sepDeg_eq_pointCount_of_computationA_and_lemma5`, `finrank_gamma_pullback_x_eq_projectiveDivisorOf_sum`
- **Visibility**: public
- **Lines**: 235–248, 0 proof lines
- **Notes**: Named specification pattern; the consumer is the staged `pc_sepDeg_eq_pointCount_of_computationA_and_lemma5`.

---

### `theorem ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen`

- **Type**: `(W : WeierstrassCurve K) → [W.toAffine.IsElliptic] → (hq : 2 ≤ Fintype.card K) → (W_smooth W).ordAtInfty ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) = ((-2 : ℤ) : WithTop ℤ)`
- **What**: Lemma 1 of the pole-divisor strategy: the pullback of `x_gen` along `γ = 1−π` has a pole of order 2 at infinity.
- **How**: Two rewrites using `isogOneSub_negFrobenius_pullback` and `addPullbackAlgHom_negFrobenius_x_gen_eq`, then `exact ord_addPullback_x_negFrobenius W hq`.
- **Hypotheses**: Elliptic curve, finite field with `#K ≥ 2`.
- **Uses from project**: `isogOneSub_negFrobenius_pullback`, `addPullbackAlgHom_negFrobenius_x_gen_eq`, `ord_addPullback_x_negFrobenius`, `W_smooth`, `x_gen`, `isogOneSub_negFrobenius`
- **Used by**: `Conditional.ord_P_pullback_x_gen_eq_neg_two_of_step_C`, `Conditional.ord_P_pullback_x_gen_eq_neg_two_of_specialized_bridge`, `lemma3_pole_at_T_unconditional`
- **Visibility**: public
- **Lines**: 95–103, 4 proof lines
- **Notes**: Core Lemma 1; 4-line proof.

---

### `theorem no_poles_off_kernel_isogOneSub_negFrobenius`

- **Type**: For any F_q-rational `SmoothPoint P`, if `γ.toAddMonoidHom P ≠ 0` then `0 ≤ (W_smooth W).ord_P P (γ.pullback (x_gen W))`.
- **What**: Lemma 4 (vacuous F_q-rational form): every F_q-rational smooth point lies in `ker γ` (since `γ = 1 − π` acts as zero on rational points), so the no-poles hypothesis is vacuously empty.
- **How**: `exfalso` on the kernel non-membership hypothesis; rewrites `isogOneSub_negFrobenius_toAddMonoidHom` and uses `sub_self`.
- **Hypotheses**: Elliptic curve, finite field with `#K ≥ 2`, smooth point `P`, non-kernel assumption.
- **Uses from project**: `isogOneSub_negFrobenius_toAddMonoidHom`, `W_smooth`, `isogOneSub_negFrobenius`
- **Used by**: `Conditional.pole_gamma_pullback_x_imp_kernel`
- **Visibility**: public
- **Lines**: 131–144, 6 proof lines
- **Notes**: Vacuous Lemma 4 — the substantive geometric version (over geometric points) is not proved here.

---

### `theorem ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two`

- **Type**: For non-2-torsion smooth point `T = (xT, yT)`: `(W_smooth W).ord_P T (translateAlgEquivOfPoint W (-T) (x_gen W)) = (-2 : WithTop ℤ)`.
- **What**: Step (C) bridge at `f = x_gen` for non-2-torsion T: the order of the translated `x_gen` at T equals `-2`.
- **How**: Rewrites `-T` via `neg_some_eq_some`, then applies `translateAlgEquivOfPoint_some_apply_x_gen` to get `translateX_xy`, constructs `negSmoothPoint` equality via `negY ∘ negY = id` (by `ring`), and applies `ord_P_translateX_xy_eq_neg_two_of_non_2_tor`.
- **Hypotheses**: Non-singular point, non-2-torsion condition `yT ≠ negY xT yT`.
- **Uses from project**: `neg_some_eq_some`, `translateAlgEquivOfPoint_some_apply_x_gen`, `ord_P_translateX_xy_eq_neg_two_of_non_2_tor`, `negSmoothPoint`, `W_smooth`, `x_gen`
- **Used by**: `bridge_at_x_gen_of_non_2_tor`, `ord_T_translateAlgEquivOfPoint_neg_x_gen_pow_card_eq`
- **Visibility**: public
- **Lines**: 476–521, 46 lines (proof >30 lines)
- **Notes**: Proof >30 lines.

---

### `theorem ord_T_translateAlgEquivOfPoint_neg_x_gen_pow_card_eq`

- **Type**: For non-2-torsion T: `(W_smooth W).ord_P T (translateAlgEquivOfPoint W (-T) (x_gen W ^ q)) = (W_smooth W).ordAtInfty (x_gen W ^ q)`.
- **What**: Step (C) bridge at `f = x_gen^q` for non-2-torsion T; lifts the x_gen bridge to its q-th power.
- **How**: First establishes the bridge for `x_gen` via `ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two`, then lifts via `ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base`.
- **Hypotheses**: Non-singular, non-2-torsion, `x_gen W ≠ 0`.
- **Uses from project**: `ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two`, `ordAtInfty_x_gen`, `x_gen_ne_zero`, `ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base`
- **Used by**: `bridge_at_x_gen_pow_card_of_non_2_tor`
- **Visibility**: public
- **Lines**: 527–554

---

### `theorem ord_T_translateAlgEquivOfPoint_neg_y_gen_eq_neg_three`

- **Type**: For non-2-torsion T: `(W_smooth W).ord_P T (translateAlgEquivOfPoint W (-T) (y_gen W)) = (-3 : WithTop ℤ)`.
- **What**: Step (C) bridge at `f = y_gen` for non-2-torsion T; order `-3` matches `ordAtInfty(y_gen)`.
- **How**: Analogous to the x_gen bridge; rewrites via `neg_some_eq_some`, `translateAlgEquivOfPoint_some_apply_y_gen`, then `ord_P_translateY_xy_eq_neg_three_of_non_2_tor`.
- **Hypotheses**: Non-singular, non-2-torsion.
- **Uses from project**: `neg_some_eq_some`, `translateAlgEquivOfPoint_some_apply_y_gen`, `ord_P_translateY_xy_eq_neg_three_of_non_2_tor`, `negSmoothPoint`, `W_smooth`, `y_gen`
- **Used by**: `bridge_at_y_gen_of_non_2_tor`
- **Visibility**: public
- **Lines**: 561–606, 46 lines (proof >30 lines)
- **Notes**: Proof >30 lines; direct y-analog of `ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two`.

---

### `theorem bridge_at_x_gen_of_non_2_tor`

- **Type**: For non-2-torsion T: `(W_smooth W).ord_P T (translateAlgEquivOfPoint W (-T) (x_gen W)) = (W_smooth W).ordAtInfty (x_gen W)`.
- **What**: Clean bridge form: translate-ord at T equals ordAtInfty for `x_gen`, without the let-binding form.
- **How**: Rewrites via `ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two` then `ordAtInfty_x_gen`.
- **Hypotheses**: Non-singular, non-2-torsion.
- **Uses from project**: `ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two`, `ordAtInfty_x_gen`
- **Used by**: `bridge_at_y_gen_pow_card_of_non_2_tor` (via y-analog), `bridge_at_x_gen_pow_card_sub_x_gen_of_non_2_tor`, `bridge_at_x_gen_sq_mul_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`, `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`, `bridge_at_x_gen_add_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`, and many others (7+ callers in file)
- **Visibility**: public
- **Lines**: 612–624
- **Notes**: Key API — used by 7+ declarations in this file.

---

### `theorem bridge_at_y_gen_of_non_2_tor`

- **Type**: For non-2-torsion T: `ord_P T (τ_{-T} (y_gen W)) = ordAtInfty (y_gen W)`.
- **What**: Clean bridge for y_gen; bridges translate-ord to ordAtInfty value `-3`.
- **How**: Rewrites via `ord_T_translateAlgEquivOfPoint_neg_y_gen_eq_neg_three` then `ordAtInfty_y_gen`.
- **Uses from project**: `ord_T_translateAlgEquivOfPoint_neg_y_gen_eq_neg_three`, `ordAtInfty_y_gen`
- **Used by**: `bridge_at_y_gen_pow_card_of_non_2_tor`, `bridge_at_y_gen_mul_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`, `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_mul_y_gen_of_non_2_tor`, `bridge_at_y_gen_add_negFrobeniusIsog_pullback_y_gen_of_non_2_tor` (6+ callers)
- **Visibility**: public
- **Lines**: 629–641
- **Notes**: Key API — used by 6+ declarations in this file.

---

### `theorem bridge_at_y_gen_pow_card_of_non_2_tor`

- **Type**: For non-2-torsion T: `ord_P T (τ_{-T} (y_gen W ^ q)) = ordAtInfty (y_gen W ^ q)`.
- **What**: Lifts the y_gen bridge to its q-th power via `ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base`.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base`, `y_gen_ne_zero`, `bridge_at_y_gen_of_non_2_tor`
- **Used by**: `bridge_at_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`
- **Visibility**: public
- **Lines**: 646–658

---

### `theorem bridge_at_x_gen_pow_card_of_non_2_tor`

- **Type**: For non-2-torsion T: `ord_P T (τ_{-T} (x_gen W ^ q)) = ordAtInfty (x_gen W ^ q)`.
- **What**: Clean bridge for x_gen^q; thin wrapper around `ord_T_translateAlgEquivOfPoint_neg_x_gen_pow_card_eq`.
- **Uses from project**: `ord_T_translateAlgEquivOfPoint_neg_x_gen_pow_card_eq`
- **Used by**: `bridge_at_x_gen_sub_x_gen_pow_card_of_non_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`, `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`, `bridge_at_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`
- **Visibility**: public
- **Lines**: 663–673

---

### `theorem ordAtInfty_x_gen_pow_card_eq`

- **Type**: `(W_smooth W).ordAtInfty (x_gen W ^ q) = ((q : ℤ) * (-2 : ℤ) : WithTop ℤ)`.
- **What**: Closed-form value `ordAtInfty(x^q) = -2q`.
- **How**: `ordAtInfty_pow_of_ord_eq` with base `ordAtInfty_x_gen`.
- **Uses from project**: `x_gen_ne_zero`, `ordAtInfty_x_gen`, `ordAtInfty_pow_of_ord_eq`
- **Used by**: `ordAtInfty_x_gen_pow_card_lt_x_gen`, `ordAtInfty_x_gen_sub_x_gen_pow_card_eq`, `ordAtInfty_neg_y_gen_pow_card_lt_rest`, `ordAtInfty_T1_ge`, `ordAtInfty_T8_ge`, and others (3+ callers)
- **Visibility**: public
- **Lines**: 677–682
- **Notes**: Key API — used by 5+ declarations.

---

### `theorem ordAtInfty_x_gen_pow_card_lt_x_gen`

- **Type**: `(W_smooth W).ordAtInfty (x_gen W ^ q) < (W_smooth W).ordAtInfty (x_gen W)` under `hq : 2 ≤ q`.
- **What**: Strict comparison `-2q < -2` (for `q ≥ 2`).
- **How**: Rewrites via `ordAtInfty_x_gen_pow_card_eq` and `ordAtInfty_x_gen`, then `WithTop.coe_lt_coe` and `linarith`.
- **Uses from project**: `ordAtInfty_x_gen_pow_card_eq`, `ordAtInfty_x_gen`
- **Used by**: `bridge_at_x_gen_pow_card_sub_x_gen_of_non_2_tor`, `ordAtInfty_x_gen_sub_x_gen_pow_card_eq`
- **Visibility**: public
- **Lines**: 686–699

---

### `theorem bridge_at_x_gen_pow_card_sub_x_gen_of_non_2_tor`

- **Type**: For non-2-torsion T: `ord_P T (τ_{-T}(x^q − x)) = ordAtInfty(x^q − x)`.
- **What**: Bridge for the slope denominator constituent `x^q − x`.
- **How**: Applies `ord_P_translateAlgEquivOfPoint_sub_eq_ordAtInfty_of_strict_lt` with bridges for `x^q` and `x` plus the strict order comparison.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_sub_eq_ordAtInfty_of_strict_lt`, `bridge_at_x_gen_pow_card_of_non_2_tor`, `bridge_at_x_gen_of_non_2_tor`, `ordAtInfty_x_gen_pow_card_lt_x_gen`
- **Used by**: `bridge_at_x_gen_sub_x_gen_pow_card_of_non_2_tor`
- **Visibility**: public
- **Lines**: 705–719

---

### `theorem bridge_at_x_gen_sub_x_gen_pow_card_of_non_2_tor`

- **Type**: For non-2-torsion T: `ord_P T (τ_{-T}(x − x^q)) = ordAtInfty(x − x^q)`.
- **What**: Bridge for `x − x^q` via negation of `bridge_at_x_gen_pow_card_sub_x_gen_of_non_2_tor`.
- **How**: Uses `h_eq : x − x^q = −(x^q − x)` and `ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base`.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base`, `bridge_at_x_gen_pow_card_sub_x_gen_of_non_2_tor`
- **Used by**: `ord_T_translateAlgEquivOfPoint_neg_x_gen_sub_x_gen_pow_card_eq`, `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`
- **Visibility**: public
- **Lines**: 724–741

---

### `theorem ordAtInfty_x_gen_sub_x_gen_pow_card_eq`

- **Type**: `(W_smooth W).ordAtInfty (x_gen W − x_gen W ^ q) = ((-2 * q : ℤ) : WithTop ℤ)` under `hq`.
- **What**: Closed-form value `ordAtInfty(x − x^q) = -2q`.
- **How**: Rewrites as `−(x^q − x)`, uses `ordAtInfty_neg`, then applies `ordAtInfty_add_eq_of_lt` with the strict comparison.
- **Uses from project**: `ordAtInfty_x_gen_pow_card_lt_x_gen`, `ordAtInfty_x_gen_pow_card_eq`, `ordAtInfty_add_eq_of_lt`
- **Used by**: `ord_T_translateAlgEquivOfPoint_neg_x_gen_sub_x_gen_pow_card_eq`, `x_gen_ne_x_gen_pow_card`, `ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen_eq`
- **Visibility**: public
- **Lines**: 746–779, 34 lines (proof >30 lines)
- **Notes**: Proof >30 lines.

---

### `theorem ord_T_translateAlgEquivOfPoint_neg_x_gen_sub_x_gen_pow_card_eq`

- **Type**: For non-2-torsion T: `ord_P T (τ_{-T}(x − x^q)) = ((-2*q : ℤ) : WithTop ℤ)`.
- **What**: Combines bridge and closed-form for `x − x^q` at T.
- **Uses from project**: `bridge_at_x_gen_sub_x_gen_pow_card_of_non_2_tor`, `ordAtInfty_x_gen_sub_x_gen_pow_card_eq`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 784–796
- **Notes**: Possibly dead code within this file; could be used by other files.

---

### `theorem x_gen_ne_x_gen_pow_card`

- **Type**: `x_gen W ≠ x_gen W ^ q` under `hq`.
- **What**: The generators `x_gen` and `x_gen^q` are distinct elements of `K(E)`.
- **How**: Contradiction: if equal, `x − x^q = 0` so `ordAtInfty = ⊤`, but `ordAtInfty_x_gen_sub_x_gen_pow_card_eq` gives `-2q < ⊤`.
- **Uses from project**: `ordAtInfty_x_gen_sub_x_gen_pow_card_eq`, `ordAtInfty_zero`
- **Used by**: `x_gen_ne_negFrobeniusIsog_pullback_x_gen`
- **Visibility**: public
- **Lines**: 802–818

---

### `theorem x_gen_ne_negFrobeniusIsog_pullback_x_gen`

- **Type**: `x_gen W ≠ (negFrobeniusIsog W).pullback (x_gen W)` under `hq`.
- **What**: `x_gen` and its Frobenius pullback are distinct (the isogeny has non-trivial kernel).
- **How**: Rewrites via `negFrobeniusIsog_pullback_x_gen` and `frobeniusIsog_pullback_apply`, then `x_gen_ne_x_gen_pow_card`.
- **Uses from project**: `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `x_gen_ne_x_gen_pow_card`
- **Used by**: `addSlope_negFrobeniusIsog_eq_secant`
- **Visibility**: public
- **Lines**: 823–828

---

### `theorem addSlope_negFrobeniusIsog_eq_secant`

- **Type**: `addSlope W (negFrobeniusIsog W) = (y_gen W − (negFrobeniusIsog W).pullback (y_gen W)) / (x_gen W − (negFrobeniusIsog W).pullback (x_gen W))`.
- **What**: The addition slope formula for `negFrobeniusIsog` reduces to the secant form (non-tangent case, since x-coordinates differ).
- **How**: Uses `slope_of_X_ne` with `x_gen_ne_negFrobeniusIsog_pullback_x_gen`.
- **Uses from project**: `x_gen_ne_negFrobeniusIsog_pullback_x_gen`, `W_KE`, `addSlope`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 834–842
- **Notes**: Dead code within this file (only defined, not used here).

---

### `theorem bridge_at_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`

- **Type**: For non-2-torsion T: `ord_P T (τ_{-T}(π*x)) = ordAtInfty(π*x)`.
- **What**: Bridge for `(negFrobeniusIsog).pullback x_gen` at non-2-torsion T; reduces to `bridge_at_x_gen_pow_card_of_non_2_tor` via `negFrobeniusIsog_pullback_x_gen`.
- **Uses from project**: `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `bridge_at_x_gen_pow_card_of_non_2_tor`
- **Used by**: `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor`, `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor`, `bridge_at_x_gen_sq_mul_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`, `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_mul_y_gen_of_non_2_tor`, `bridge_at_x_gen_add_negFrobeniusIsog_pullback_x_gen_of_non_2_tor` (6+ callers)
- **Visibility**: public
- **Lines**: 847–857
- **Notes**: Key API — used by 6+ declarations.

---

### `theorem bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`

- **Type**: For non-2-torsion T under `hq`: `ord_P T (τ_{-T}(x − π*x)) = ordAtInfty(x − π*x)`.
- **What**: Bridge for the slope denominator `x − π*x`.
- **Uses from project**: `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `bridge_at_x_gen_sub_x_gen_pow_card_of_non_2_tor`
- **Used by**: `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor`, `bridge_at_addPullback_x_negFrobenius_of_bridge_at_Num` (indirectly)
- **Visibility**: public
- **Lines**: 863–876

---

### `theorem ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen_eq`

- **Type**: `ordAtInfty(x − π*x) = ((-2*q : ℤ) : WithTop ℤ)` under `hq`.
- **What**: Closed-form value for ordAtInfty of the slope denominator.
- **Uses from project**: `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `ordAtInfty_x_gen_sub_x_gen_pow_card_eq`
- **Used by**: `ord_T_translateAlgEquivOfPoint_neg_x_gen_sub_negFrobeniusIsog_pullback_x_gen_eq`, `ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_eq`, `bridge_at_addPullback_x_negFrobenius_of_bridge_at_Num`
- **Visibility**: public
- **Lines**: 881–888

---

### `theorem ord_T_translateAlgEquivOfPoint_neg_x_gen_sub_negFrobeniusIsog_pullback_x_gen_eq`

- **Type**: For non-2-torsion T: `ord_P T (τ_{-T}(x − π*x)) = ((-2*q : ℤ) : WithTop ℤ)`.
- **What**: Combines bridge and closed-form for `x − π*x` at non-2-torsion T.
- **Uses from project**: `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`, `ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen_eq`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 893–905
- **Notes**: Dead code within this file.

---

### `theorem negFrobeniusIsog_pullback_y_gen_eq_pow_form`

- **Type**: `(negFrobeniusIsog W).pullback (y_gen W) = −y^q − a₁·x^q − a₃` in `K(E)`.
- **What**: Algebraic expansion of `π* y_gen` via Weierstrass coefficient and Frobenius pullback.
- **How**: Rewrites via `negFrobeniusIsog_pullback_y_gen` and `frobeniusIsog_pullback_apply`.
- **Uses from project**: `negFrobeniusIsog_pullback_y_gen`, `frobeniusIsog_pullback_apply`
- **Used by**: `bridge_at_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`
- **Visibility**: public
- **Lines**: 921–929

---

### `theorem ordAtInfty_neg_y_gen_pow_card_lt_rest`

- **Type**: `ordAtInfty(−y^q) < ordAtInfty(−a₁·x^q + (−a₃))` under `hq`.
- **What**: Strict comparison establishing that `−y^q` (ord `-3q`) is strictly smaller than the remaining terms in the expansion of `π* y_gen` (ord `≥ -2q`).
- **How**: Computes `ordAtInfty_pow_of_ord_eq` for `−y^q`, then performs case-splits on `a₁ = 0`, `a₃ = 0` to bound the rest via `ordAtInfty_mul`, `ordAtInfty_algebraMap_F_nonzero`, and `ordAtInfty_add_ge_min`. Closes with `linarith`.
- **Hypotheses**: Elliptic curve, `hq : 2 ≤ q`.
- **Uses from project**: `y_gen_ne_zero`, `ordAtInfty_y_gen`, `ordAtInfty_x_gen_pow_card_eq`, `ordAtInfty_algebraMap_F_nonzero`, `ordAtInfty_mul`, `ordAtInfty_add_ge_min`, `ordAtInfty_neg`, `ordAtInfty_zero`
- **Used by**: `bridge_at_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`
- **Visibility**: public
- **Lines**: 934–1026, 94 lines (proof >30 lines)
- **Notes**: Proof >30 lines; handles both `a₁` zero/nonzero and `a₃` zero/nonzero cases.

---

### `theorem bridge_at_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`

- **Type**: For non-2-torsion T under `hq`: `ord_P T (τ_{-T}(π*y)) = ordAtInfty(π*y)`.
- **What**: Bridge for `(negFrobeniusIsog).pullback y_gen` at non-2-torsion T; the dominant term `−y^q` (ord `-3q`) governs via strict-comparison addition.
- **How**: Rewrites via `negFrobeniusIsog_pullback_y_gen_eq_pow_form`, assembles individual term bridges (neg, const-mul, algebraMap), applies `ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt` twice for the inner (a₁·x^q + a₃) sum and the outer (−y^q + rest) sum; uses `ordAtInfty_neg_y_gen_pow_card_lt_rest`.
- **Uses from project**: `negFrobeniusIsog_pullback_y_gen_eq_pow_form`, `bridge_at_y_gen_pow_card_of_non_2_tor`, `bridge_at_x_gen_pow_card_of_non_2_tor`, `ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base`, `ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base`, `ord_P_translateAlgEquivOfPoint_algebraMap_eq_ordAtInfty`, `ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt`, `ordAtInfty_neg_y_gen_pow_card_lt_rest`
- **Used by**: `bridge_at_y_gen_mul_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`, `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`, `bridge_at_y_gen_add_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`, `y_gen_add_negFrobeniusIsog_pullback_y_gen_ne_zero`
- **Visibility**: public
- **Lines**: 1035–1199, 165 lines (proof >30 lines)
- **Notes**: Largest proof in the file by line count (165 lines). Handles case-split on `a₁ = 0`.

---

### `theorem bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor`

- **Type**: For non-2-torsion T: `ord_P T (τ_{-T}((x − π*x)²)) = ordAtInfty((x − π*x)²)`.
- **What**: Bridge for the denominator squared via pow on `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`.
- **Uses from project**: `x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero`, `ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base`, `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`
- **Used by**: `bridge_at_addPullback_x_negFrobenius_of_bridge_at_Num`
- **Visibility**: public
- **Lines**: 1205–1221

---

### `theorem ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_eq`

- **Type**: `ordAtInfty((x − π*x)²) = ((-4*q : ℤ) : WithTop ℤ)` under `hq`.
- **What**: Closed-form ordAtInfty of the denominator squared.
- **Uses from project**: `x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero`, `ordAtInfty_pow`, `ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen_eq`
- **Used by**: `bridge_at_addPullback_x_negFrobenius_of_bridge_at_Num`
- **Visibility**: public
- **Lines**: 1224–1247

---

### `theorem bridge_at_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor`

- **Type**: For non-2-torsion T: `ord_P T (τ_{-T}(π*x)²) = ordAtInfty((π*x)²)`.
- **What**: Bridge for `(π*x)²` via pow on `bridge_at_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`.
- **Uses from project**: `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `x_gen_ne_zero`, `ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base`, `bridge_at_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`
- **Used by**: `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1257–1273

---

### `theorem bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor`

- **Type**: For non-2-torsion T: `ord_P T (τ_{-T}(x · (π*x)²)) = ordAtInfty(x · (π*x)²)`.
- **What**: Bridge for `T7 = x · (π*x)²` (the dominant term in the numerator), via product bridge.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each`, `x_gen_ne_zero`, `bridge_at_x_gen_of_non_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1279–1298

---

### `theorem bridge_at_x_gen_sq_mul_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`

- **Type**: For non-2-torsion T: `ord_P T (τ_{-T}(x² · π*x)) = ordAtInfty(x² · π*x)`.
- **What**: Bridge for `T6 = x² · π*x`, via pow-then-mul.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each`, `x_gen_ne_zero`, `ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base`, `bridge_at_x_gen_of_non_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1301–1327

---

### `theorem bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`

- **Type**: For non-2-torsion T: `ord_P T (τ_{-T}(x · π*x)) = ordAtInfty(x · π*x)`.
- **What**: Bridge for `x · π*x` (building block for T8).
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each`, `x_gen_ne_zero`, `bridge_at_x_gen_of_non_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`
- **Used by**: `bridge_at_T8_two_a2_x_pi_x_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1332–1349

---

### `theorem bridge_at_y_gen_mul_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`

- **Type**: For non-2-torsion T under `hq`: `ord_P T (τ_{-T}(y · π*y)) = ordAtInfty(y · π*y)`.
- **What**: Bridge for `y · π*y` (building block for T4), after showing `π*y ≠ 0`.
- **Uses from project**: `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `y_gen_ne_zero`, `ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each`, `bridge_at_y_gen_of_non_2_tor`, `bridge_at_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`
- **Used by**: `bridge_at_T4_two_y_pi_y_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1354–1377

---

### `theorem bridge_at_x_gen_mul_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`

- **Type**: For non-2-torsion T under `hq`: `ord_P T (τ_{-T}(x · π*y)) = ordAtInfty(x · π*y)`.
- **What**: Bridge for `x · π*y` (building block for T5).
- **Uses from project**: `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `x_gen_ne_zero`, `ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each`, `bridge_at_x_gen_of_non_2_tor`, `bridge_at_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`
- **Used by**: `bridge_at_x_pi_y_add_pi_x_y_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1382–1404

---

### `theorem bridge_at_negFrobeniusIsog_pullback_x_gen_mul_y_gen_of_non_2_tor`

- **Type**: For non-2-torsion T: `ord_P T (τ_{-T}(π*x · y)) = ordAtInfty(π*x · y)`.
- **What**: Bridge for `π*x · y` (building block for T5).
- **Uses from project**: `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `x_gen_ne_zero`, `y_gen_ne_zero`, `ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each`, `bridge_at_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`, `bridge_at_y_gen_of_non_2_tor`
- **Used by**: `bridge_at_x_pi_y_add_pi_x_y_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1409–1426

---

### `theorem bridge_at_x_gen_add_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`

- **Type**: For non-2-torsion T under `hq`: `ord_P T (τ_{-T}(x + π*x)) = ordAtInfty(x + π*x)`.
- **What**: Bridge for `x + π*x` (building block for T1), using strict-add with `π*x` strictly smaller.
- **Uses from project**: `ordAtInfty_negFrobeniusIsog_pullback_x_gen`, `ordAtInfty_x_gen`, `ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt`, `bridge_at_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`, `bridge_at_x_gen_of_non_2_tor`
- **Used by**: `bridge_at_T1_a4_x_add_pi_x_of_non_2_tor`, `x_gen_add_negFrobeniusIsog_pullback_x_gen_ne_zero`
- **Visibility**: public
- **Lines**: 1431–1460, 30 lines

---

### `theorem bridge_at_y_gen_add_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`

- **Type**: For non-2-torsion T under `hq`: `ord_P T (τ_{-T}(y + π*y)) = ordAtInfty(y + π*y)`.
- **What**: Bridge for `y + π*y` (building block for T3), using strict-add.
- **Uses from project**: `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `ordAtInfty_y_gen`, `ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt`, `bridge_at_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`, `bridge_at_y_gen_of_non_2_tor`
- **Used by**: `bridge_at_T3_a3_y_add_pi_y_of_non_2_tor`, `y_gen_add_negFrobeniusIsog_pullback_y_gen_ne_zero`
- **Visibility**: public
- **Lines**: 1465–1492

---

### `theorem bridge_at_T1_a4_x_add_pi_x_of_non_2_tor`

- **Type**: For non-2-torsion T under `hq`: `ord_P T (τ_{-T}(a₄ · (x + π*x))) = ordAtInfty(a₄ · (x + π*x))`.
- **What**: Bridge for T1 = `a₄ · (x + π*x)` via const-mul on the sum bridge.
- **How**: Handles case `a₄ = 0` (trivial) and `a₄ ≠ 0`; uses non-vanishing of `x + π*x` (proved inline via ordAtInfty), applies `ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base`.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base`, `ordAtInfty_negFrobeniusIsog_pullback_x_gen`, `ordAtInfty_x_gen`, `bridge_at_x_gen_add_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1496–1538, 43 lines (proof >30 lines)

---

### `theorem x_gen_add_negFrobeniusIsog_pullback_x_gen_ne_zero`

- **Type**: `x_gen W + (negFrobeniusIsog W).pullback (x_gen W) ≠ 0` under `hq`.
- **What**: Non-vanishing of `x + π*x` (ordAtInfty = `-2q ≠ ⊤`).
- **Uses from project**: `ordAtInfty_negFrobeniusIsog_pullback_x_gen`, `ordAtInfty_x_gen`, `ordAtInfty_add_eq_of_lt`, `ordAtInfty_zero`
- **Used by**: `bridge_at_T1_a4_x_add_pi_x_of_non_2_tor`, `ordAtInfty_T1_ge`
- **Visibility**: public
- **Lines**: 1541–1566

---

### `theorem y_gen_add_negFrobeniusIsog_pullback_y_gen_ne_zero`

- **Type**: `y_gen W + (negFrobeniusIsog W).pullback (y_gen W) ≠ 0` under `hq`.
- **What**: Non-vanishing of `y + π*y` (ordAtInfty = `-3q ≠ ⊤`).
- **Uses from project**: `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `ordAtInfty_y_gen`, `ordAtInfty_add_eq_of_lt`, `ordAtInfty_zero`
- **Used by**: `bridge_at_T3_a3_y_add_pi_y_of_non_2_tor`, `ordAtInfty_neg_T3_ge`, `bridge_at_T4_two_y_pi_y_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1569–1594

---

### `theorem bridge_at_T2_two_a6_of_non_2_tor`

- **Type**: For non-2-torsion T: `ord_P T (τ_{-T}(2 · a₆)) = ordAtInfty(2 · a₆)`.
- **What**: Bridge for T2 = `2 · a₆` (constant); trivial via algebraMap.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_algebraMap_eq_ordAtInfty`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1598–1617

---

### `theorem bridge_at_T3_a3_y_add_pi_y_of_non_2_tor`

- **Type**: For non-2-torsion T under `hq`: `ord_P T (τ_{-T}(a₃ · (y + π*y))) = ordAtInfty(a₃ · (y + π*y))`.
- **What**: Bridge for T3 = `a₃ · (y + π*y)` via const-mul.
- **Uses from project**: `ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base`, `y_gen_add_negFrobeniusIsog_pullback_y_gen_ne_zero`, `bridge_at_y_gen_add_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1621–1638

---

### `theorem bridge_at_T4_two_y_pi_y_of_non_2_tor`

- **Type**: For non-2-torsion T under `hq`: `ord_P T (τ_{-T}(2 · y · π*y)) = ordAtInfty(2 · y · π*y)`.
- **What**: Bridge for T4 = `2 · y · π*y`; rewrites as `algMap 2 · (y · π*y)` and applies const-mul.
- **Uses from project**: `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `y_gen_ne_zero`, `ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base`, `bridge_at_y_gen_mul_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1643–1673, 31 lines (proof >30 lines)

---

### `theorem bridge_at_T8_two_a2_x_pi_x_of_non_2_tor`

- **Type**: For non-2-torsion T: `ord_P T (τ_{-T}(2 · a₂ · x · π*x)) = ordAtInfty(2 · a₂ · x · π*x)`.
- **What**: Bridge for T8 = `2 · a₂ · x · π*x`; rewrites as `algMap(2·a₂) · (x · π*x)` and applies const-mul.
- **Uses from project**: `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `x_gen_ne_zero`, `ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base`, `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1677–1706

---

### `theorem bridge_at_x_pi_y_add_pi_x_y_of_non_2_tor`

- **Type**: For non-2-torsion T under `hq`: `ord_P T (τ_{-T}(x·π*y + π*x·y)) = ordAtInfty(x·π*y + π*x·y)`.
- **What**: Bridge for the sum `x·π*y + π*x·y` (kernel of T5); uses strict-add (`x·π*y` has ord `-3q−2` strictly smaller than `π*x·y` with ord `-2q−3` for `q ≥ 2`).
- **Uses from project**: `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `negFrobeniusIsog_pullback_x_gen`, `x_gen_ne_zero`, `y_gen_ne_zero`, `ordAtInfty_x_gen`, `ordAtInfty_mul`, `ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt`, `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_y_gen_of_non_2_tor`, `bridge_at_negFrobeniusIsog_pullback_x_gen_mul_y_gen_of_non_2_tor`
- **Used by**: `bridge_at_T5_a1_x_pi_y_add_pi_x_y_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1711–1781, 71 lines (proof >30 lines)

---

### `theorem bridge_at_T5_a1_x_pi_y_add_pi_x_y_of_non_2_tor`

- **Type**: For non-2-torsion T under `hq`: `ord_P T (τ_{-T}(a₁ · (x·π*y + π*x·y))) = ordAtInfty(a₁ · (x·π*y + π*x·y))`.
- **What**: Bridge for T5 via const-mul. The inner sum nonzero proof (ord = `-3q−2 < ⊤`) is inline.
- **Uses from project**: `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `negFrobeniusIsog_pullback_x_gen`, `x_gen_ne_zero`, `y_gen_ne_zero`, `ordAtInfty_x_gen`, `ordAtInfty_mul`, `ordAtInfty_add_eq_of_lt`, `ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base`, `bridge_at_x_pi_y_add_pi_x_y_of_non_2_tor`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1785–1869, 85 lines (proof >30 lines)

---

### `theorem withTop_int_lt_of_lt_of_le`

- **Type**: `{a b : ℤ} → a < b → {x : WithTop ℤ} → ((b : ℤ) : WithTop ℤ) ≤ x → ((a : ℤ) : WithTop ℤ) < x`
- **What**: Utility helper: integer strict comparison lifts to WithTop ℤ.
- **How**: `(WithTop.coe_lt_coe.mpr h).trans_le hx`.
- **Hypotheses**: None beyond typeclass constraints.
- **Uses from project**: none
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public (no leading namespace)
- **Lines**: 1880–1883

---

### `theorem ordAtInfty_T1_ge`

- **Type**: `((-3 − 3*q : ℤ) : WithTop ℤ) ≤ ordAtInfty(a₄ · (x + π*x))` under `hq`.
- **What**: Lower bound `≥ -3-3q` for T1.
- **How**: Case-split on `a₄ = 0`; for nonzero: `ordAtInfty_mul` + `ordAtInfty_algebraMap_F_nonzero` + closed-form for `ordAtInfty(x + π*x) = -2q`.
- **Uses from project**: `x_gen_add_negFrobeniusIsog_pullback_x_gen_ne_zero`, `ordAtInfty_negFrobeniusIsog_pullback_x_gen`, `ordAtInfty_x_gen`, `ordAtInfty_mul`, `ordAtInfty_algebraMap_F_nonzero`, `ordAtInfty_add_eq_of_lt`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1895–1952, 58 lines (proof >30 lines)

---

### `theorem ordAtInfty_T2_ge`

- **Type**: Lower bound for T2 = `2 · a₆`: `≥ -3-3q`.
- **What**: Since `2·a₆` is a constant, its ordAtInfty is 0 or ⊤.
- **Uses from project**: `ordAtInfty_algebraMap_F_nonzero`, `ordAtInfty_zero`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1955–1980

---

### `theorem ordAtInfty_neg_T3_ge`

- **Type**: Lower bound for `-T3 = -(a₃ · (y + π*y))`: `≥ -3-3q`.
- **What**: `ordAtInfty(a₃ · (y + π*y)) = ordAtInfty(y+π*y) = -3q ≥ -3-3q`.
- **Uses from project**: `y_gen_add_negFrobeniusIsog_pullback_y_gen_ne_zero`, `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `ordAtInfty_y_gen`, `ordAtInfty_mul`, `ordAtInfty_algebraMap_F_nonzero`, `ordAtInfty_neg`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public
- **Lines**: 1983–2046, 64 lines (proof >30 lines)

---

### `theorem ordAtInfty_neg_T4_ge`

- **Type**: Lower bound for `-T4 = -(2·y·π*y)`: `≥ -3-3q`.
- **What**: Exact value is `-3-3q` (via `ordAtInfty(y) + ordAtInfty(π*y) = -3 + (-3q)`).
- **Uses from project**: `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `y_gen_ne_zero`, `ordAtInfty_y_gen`, `ordAtInfty_mul`, `ordAtInfty_algebraMap_F_nonzero`, `ordAtInfty_neg`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public
- **Lines**: 2049–2112, 64 lines (proof >30 lines)

---

### `theorem ordAtInfty_neg_T5_ge`

- **Type**: Lower bound for `-T5 = -(a₁ · (x·π*y + π*x·y))`: `≥ -3-3q`.
- **What**: Exact value is `-3q-2 ≥ -3-3q`.
- **How**: Computes ordAtInfty of both summands via `ordAtInfty_mul`, combines via strict-add, then case-splits on `a₁ = 0`.
- **Uses from project**: `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `negFrobeniusIsog_pullback_x_gen`, `x_gen_ne_zero`, `y_gen_ne_zero`, `ordAtInfty_x_gen`, `ordAtInfty_mul`, `ordAtInfty_algebraMap_F_nonzero`, `ordAtInfty_add_eq_of_lt`, `ordAtInfty_neg`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public
- **Lines**: 2115–2221, 107 lines (proof >30 lines)

---

### `theorem ordAtInfty_T6_ge`

- **Type**: Lower bound for T6 = `x² · π*x`: `≥ -3-3q`.
- **What**: Exact value `-2q−4` (via mul + pow).
- **Uses from project**: `x_gen_ne_zero`, `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `ordAtInfty_mul`, `ordAtInfty_pow`, `ordAtInfty_x_gen`, `ordAtInfty_negFrobeniusIsog_pullback_x_gen`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public
- **Lines**: 2224–2252, 30 lines

---

### `theorem ordAtInfty_T8_ge`

- **Type**: Lower bound for T8 = `2·a₂·x·π*x`: `≥ -3-3q`.
- **What**: Exact value `-2−2q` (via const-mul, `ordAtInfty_x_gen`, `ordAtInfty_negFrobeniusIsog_pullback_x_gen`).
- **Uses from project**: `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `x_gen_ne_zero`, `ordAtInfty_mul`, `ordAtInfty_x_gen`, `ordAtInfty_negFrobeniusIsog_pullback_x_gen`, `ordAtInfty_algebraMap_F_nonzero`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public
- **Lines**: 2255–2307, 53 lines (proof >30 lines)

---

### `theorem reduced_form_eq_dom_plus_list`

- **Type**: Algebraic identity expressing the 8-term reduced numerator as `T7 + List.sum [T1, T2, -T3, -T4, -T5, T6, T8]`.
- **What**: Rearrangement of the numerator `addPullbackNumerator_reduced_negFrobenius` to isolate the dominant term T7.
- **How**: `simp only [List.sum_cons, List.sum_nil, add_zero]; ring`.
- **Uses from project**: `addPullbackNumerator_reduced_negFrobenius`, `negFrobeniusIsog`, `x_gen`, `y_gen`
- **Used by**: `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Visibility**: public
- **Lines**: 2312–2348

---

### `theorem bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`

- **Type**: For non-2-torsion T under `hq`: `ord_P T (τ_{-T}(Num)) = ordAtInfty(Num)` where `Num = addPullbackNumerator_negFrobenius W`.
- **What**: Main bridge for the Weierstrass-reduced numerator; applies `ord_P_translateAlgEquivOfPoint_sum_dominant` with T7 as dominant term and T1–T8 as the rest.
- **How**: Rewrites via `addPullbackNumerator_negFrobenius_eq_reduced` and `addPullbackNumerator_reduced_negFrobenius`, applies `reduced_form_eq_dom_plus_list`, then `ord_P_translateAlgEquivOfPoint_sum_dominant` with: (1) T7 bridge, (2) list membership dispatch to individual term bridges, (3) strict dominance via `withTop_int_lt_of_lt_of_le` and the 7 `ordAtInfty_T*_ge` bounds.
- **Uses from project**: `addPullbackNumerator_negFrobenius_eq_reduced`, `addPullbackNumerator_reduced_negFrobenius`, `reduced_form_eq_dom_plus_list`, `ord_P_translateAlgEquivOfPoint_sum_dominant`, `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor`, `bridge_at_T1_a4_x_add_pi_x_of_non_2_tor`, `bridge_at_T2_two_a6_of_non_2_tor`, `bridge_at_T3_a3_y_add_pi_y_of_non_2_tor`, `bridge_at_T4_two_y_pi_y_of_non_2_tor`, `bridge_at_T5_a1_x_pi_y_add_pi_x_y_of_non_2_tor`, `bridge_at_x_gen_sq_mul_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`, `bridge_at_T8_two_a2_x_pi_x_of_non_2_tor`, `withTop_int_lt_of_lt_of_le`, `ordAtInfty_T1_ge`, `ordAtInfty_T2_ge`, `ordAtInfty_neg_T3_ge`, `ordAtInfty_neg_T4_ge`, `ordAtInfty_neg_T5_ge`, `ordAtInfty_T6_ge`, `ordAtInfty_T8_ge`, `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `x_gen_ne_zero`, `ordAtInfty_x_gen`, `ordAtInfty_pow`, `ordAtInfty_mul`, `ordAtInfty_negFrobeniusIsog_pullback_x_gen`
- **Used by**: `bridge_at_addPullback_x_negFrobenius_of_bridge_at_Num` (as the discharged numerator bridge)
- **Visibility**: public
- **Lines**: 2359–2456, 98 lines (proof >30 lines)

---

### `theorem bridge_at_addPullback_x_negFrobenius_of_bridge_at_Num` (in Conditional)

- **Type**: For non-2-torsion T under `hq`, parametric on `h_Num_bridge`: `ord_P T (τ_{-T}(addPullback_x W π)) = ordAtInfty(addPullback_x W π)`.
- **What**: Conditional bridge for `addPullback_x`; composes Worker A's division identity with the Num bridge hypothesis and the denominator-squared bridge.
- **How**: Rewrites via `addPullbackNumerator_negFrobenius_eq` to `Num / (x−π*x)²`, uses `ordAtInfty_addPullbackNumerator_reduced_negFrobenius_eq` to show `Num ≠ 0`, applies `ord_P_translateAlgEquivOfPoint_div_eq_ordAtInfty_of_each`.
- **Uses from project**: `x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero`, `addPullbackNumerator_negFrobenius_eq`, `addPullbackNumerator_negFrobenius_eq_reduced`, `ordAtInfty_addPullbackNumerator_reduced_negFrobenius_eq`, `ord_P_translateAlgEquivOfPoint_div_eq_ordAtInfty_of_each`, `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor`
- **Used by**: `bridge_at_addPullback_x_negFrobenius_of_non_2_tor`
- **Visibility**: public (in Conditional namespace)
- **Lines**: 2533–2596, 64 lines (proof >30 lines)

---

### `theorem bridge_at_addPullback_x_negFrobenius_of_non_2_tor`

- **Type**: For non-2-torsion T under `hq`, **unconditional**: `ord_P T (τ_{-T}(addPullback_x W π)) = ordAtInfty(addPullback_x W π)`.
- **What**: Fully unconditional bridge for `addPullback_x`; discharges the conditional form.
- **How**: One-line application of `bridge_at_addPullback_x_negFrobenius_of_bridge_at_Num` with `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`.
- **Uses from project**: `bridge_at_addPullback_x_negFrobenius_of_bridge_at_Num`, `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
- **Used by**: `lemma3_pole_at_T_unconditional`
- **Visibility**: public
- **Lines**: 2583–2596

---

### `theorem lemma3_pole_at_T_unconditional`

- **Type**: For non-2-torsion T = (xT, yT) with `hq`: `(W_smooth W).ord_P T ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) = (-2 : WithTop ℤ)`.
- **What**: **Lemma 3 unconditional**: every non-2-torsion F_q-rational point is a pole of order 2 of `γ*x`.
- **How**: Applies `Conditional.lemma3_pole_at_T_of_bridge_and_invariance` with: (1) the unconditional addPullback bridge, (2) τ_(-T)-invariance from `xy_family_isogOneSub_negFrobenius` (kernel membership proved inline since `-T` satisfies `(1-π)(-T) = 0`).
- **Uses from project**: `Conditional.lemma3_pole_at_T_of_bridge_and_invariance`, `bridge_at_addPullback_x_negFrobenius_of_non_2_tor`, `xy_family_isogOneSub_negFrobenius`, `isogOneSub_negFrobenius_toAddMonoidHom`
- **Used by**: unused in this file (but it is the main Lemma 3 deliverable)
- **Visibility**: public
- **Lines**: 2609–2631
- **Notes**: Key deliverable; likely used by other files in the `Hasse` directory.

---

### `theorem pc_sepDeg_eq_pointCount_of_computationA_and_lemma5` (in Conditional)

- **Type**: Given `h_pc_sep`, `h_pc_fin`, `h_compA`, `h_finrank_eq_2_deg`, `h_lemma5` → `(isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine`.
- **What**: Staged consumer: discharges `sepDegree = pointCount` from Computation A + Lemma 5 + tower argument.
- **How**: From `h_compA + h_lemma5` derives `2·deg = 2·pointCount`, cancels 2, uses `isSeparable_iff_sepDegree_eq_degree`.
- **Uses from project**: `isogOneSub_negFrobenius`, `pointCount`, `ComputationA_bridge_pullback_x_gen`, `Isogeny.isSeparable_iff_sepDegree_eq_degree`
- **Used by**: unused in file; consumed by `finrank_gamma_pullback_x_eq_projectiveDivisorOf_sum` chain
- **Visibility**: public (in Conditional)
- **Lines**: 2653–2695, 43 lines (proof >30 lines)

---

### `theorem lemma5_of_pole_orders_and_support_card` (in Conditional)

- **Type**: Given per-point pole-order values and support cardinality, derives `Σ (-ord P).toNat = 2 · pointCount`.
- **What**: Bookkeeping assembly of Lemma 5 from witnesses.
- **How**: `Finset.sum_congr rfl` + `h_pole_orders` to make all summands equal 2, then `Finset.sum_const + smul_eq_mul + h_support_card`.
- **Uses from project**: `isogOneSub_negFrobenius`, `x_gen`, `W_smooth`, `pointCount`, `projectiveDivisorOf`
- **Used by**: `bridgeB_weightedPoleDegree_eq_projectiveDivisorOf_sum`
- **Visibility**: public (in Conditional)
- **Lines**: 2721–2754

---

## Declarations in second `Conditional` namespace block (lines 2798–3830)

### `theorem Conditional.pole_gamma_pullback_x_imp_kernel`

- **Type**: If `ord_P P (γ*x) < 0` then `γ.toAddMonoidHom P = 0`.
- **What**: Contrapositive of `no_poles_off_kernel_isogOneSub_negFrobenius`.
- **How**: `by_contra` + `no_poles_off_kernel_isogOneSub_negFrobenius` + `not_le_of_gt`.
- **Uses from project**: `no_poles_off_kernel_isogOneSub_negFrobenius`
- **Used by**: unused in file
- **Visibility**: public (in Conditional)
- **Lines**: 2804–2815

---

### `theorem Conditional.pole_gamma_pullback_x_imp_kernel_closed_point`

- **Type**: For a `Sinf`-prime `P` not lying over `xIdeal`, `0 ≤ data.ordAt P`.
- **What**: Closed-point Lemma 4: at the `Sinf`-prime level, non-X primes contribute non-negative order.
- **How**: `Ideal.ramificationIdx_of_not_le` via maximality of `xIdeal` (`xIdeal_isMaximal`), then `data.ordAt = -ramificationIdx`.
- **Uses from project**: `Curves.RamificationAtInfinity.xIdeal_isMaximal`, `Sinf.ordAt`, `isogOneSub_negFrobenius`, `x_gen`
- **Visibility**: public (in Conditional)
- **Lines**: 2834–2879, 46 lines (proof >30 lines)

---

### `theorem Conditional.bridgeA_intermediateField_adjoin_eq_fractionRing_finrank`

- **Type**: Given `Fact (Transcendental K (γ*x)⁻¹)`: `Module.finrank (adjoin K {γ*x}) K(E) = @Module.finrank (FractionRing K[X]) (LinfAt (γ*x)) ...`.
- **What**: Bridge A: identifies the consumer-facing `K⟮f⟯` finrank with the abstract `FractionRing K[X]`-framing of `LinfAt f`. Both compute `[K(E):K(f)]`.
- **How**: Builds AlgEquiv chain `K⟮f⟯ ≃ₐ[K] K⟮f⁻¹⟯ ≃ₐ[K] RatFunc K ≃ₐ[K] FractionRing K[X]` via `IntermediateField.equivOfEq + RatFunc.algEquivOfTranscendental + RatFunc.toFractionRingAlgEquiv`, then applies `Algebra.finrank_eq_of_equiv_equiv`. The commuting square is verified via `IsLocalization.algHom_ext + Polynomial.algHom_ext + RatFunc.algEquivOfTranscendental_X`.
- **Uses from project**: `isogOneSub_negFrobenius`, `x_gen`, `LinfAt`, `LinfAt.algebraFractionRing`, `LinfAt.algebraMap_polynomial_apply`, `polyToFieldOfInv_X`
- **Used by**: `finrank_adjoin_eq_finrank_LinfAt`, `finrank_gamma_pullback_x_eq_projectiveDivisorOf_sum`, `K_E_separable_of_KofF_separable`
- **Visibility**: public (in Conditional)
- **Lines**: 2902–3042, 142 lines (proof >30 lines)
- **Notes**: Very long proof; duplicates some AlgEquiv chain structure with `finrank_adjoin_eq_finrank_LinfAt` and `K_E_separable_of_KofF_separable`.

---

### `theorem Conditional.finrank_gamma_pullback_x_eq_weightedPoleDegree`

- **Type**: Under `hf : Fact (Transcendental K (γ*x)⁻¹)`, `hMF`, `data : Sinf (γ*x)`: the `FractionRing K[X]`-form finrank equals the Sinf-weighted pole degree sum.
- **What**: Specialises `Curves.RamificationAtInfinity.finrank_eq_weighted_poleDegree_of_nonconstant` to `f = γ*x_gen`.
- **How**: `exact @finrank_eq_weighted_poleDegree_of_nonconstant K _ _ _ _ f hf hMF data`.
- **Uses from project**: `Curves.RamificationAtInfinity.finrank_eq_weighted_poleDegree_of_nonconstant`, `isogOneSub_negFrobenius`, `x_gen`, `LinfAt`
- **Used by**: `finrank_gamma_pullback_x_eq_projectiveDivisorOf_sum`
- **Visibility**: public (in Conditional)
- **Lines**: 3080–3106

---

### `theorem Conditional.transcendental_inv`

- **Type**: `Transcendental K y → Transcendental K y⁻¹` for `y : L` in a field algebra.
- **What**: Transcendence is preserved under inversion.
- **How**: One line via `fun halg => h (by simpa using halg.inv)`.
- **Uses from project**: none (general)
- **Used by**: `fact_transcendental_gamma_pullback_x_inv`
- **Visibility**: public (in Conditional)
- **Lines**: 3111–3112

---

### `theorem Conditional.transcendental_gamma_pullback_x`

- **Type**: `Transcendental K ((isogOneSub_negFrobenius W hq).pullback (x_gen W))`.
- **What**: The pullback `γ*x_gen` is transcendental over K (since `γ.pullback` is injective and `x_gen` is transcendental).
- **How**: Injectivity of `pullback` via `pullback_injective`; the algebraic relation would pull back to make `x_gen` algebraic.
- **Uses from project**: `x_gen_transcendental`, `isogOneSub_negFrobenius`, `x_gen`
- **Used by**: `fact_transcendental_gamma_pullback_x_inv`
- **Visibility**: public (in Conditional)
- **Lines**: 3117–3125

---

### `theorem Conditional.fact_transcendental_gamma_pullback_x_inv`

- **Type**: `Fact (Transcendental K ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹)`.
- **What**: The `Fact` instance needed by `LinfAt.algebraFractionRing`.
- **How**: Composes `transcendental_inv + transcendental_gamma_pullback_x`.
- **Uses from project**: `transcendental_inv`, `transcendental_gamma_pullback_x`
- **Used by**: available for call sites (provides the `Fact` instance)
- **Visibility**: public (in Conditional)
- **Lines**: 3130–3133

---

### `theorem Conditional.finrank_adjoin_eq_finrank_LinfAt`

- **Type**: Under `Fact (Transcendental K (γ*x)⁻¹)`: the `adjoin K {γ*x}` finrank equals the `LinfAt (γ*x)` finrank.
- **What**: Equivalent to `bridgeA_intermediateField_adjoin_eq_fractionRing_finrank` but with slightly different framing; rebuilt using the same AlgEquiv chain.
- **How**: Constructs `e₁ : FractionRing K[X] ≃ₐ[K] K⟮f⁻¹⟯` (via `RatFunc.toFractionRingAlgEquiv.symm.trans algEquivOfTranscendental`), uses `e₂ = refl`, verifies the commuting square via `IsLocalization.ringHom_ext + Polynomial.ringHom_ext`.
- **Uses from project**: `isogOneSub_negFrobenius`, `x_gen`, `LinfAt`, `LinfAt.algebraFractionRing`, `LinfAt.algebraMap_fractionRing_apply`, `ratFunToFieldOfInv`, `polyToFieldOfInv_X`
- **Used by**: `finrank_gamma_pullback_x_eq_projectiveDivisorOf_sum`
- **Visibility**: public (in Conditional)
- **Lines**: 3140–3255, 116 lines (proof >30 lines)
- **Notes**: Duplication suspicion: largely overlaps with `bridgeA_intermediateField_adjoin_eq_fractionRing_finrank` (same AlgEquiv chain, same commuting square).

---

### `theorem Conditional.K_E_separable_of_KofF_separable`

- **Type**: Under `hf`, given `h_KofF_sep : @Algebra.IsSeparable (K⟮f⟯) K(E) ...`: derives `@Algebra.IsSeparable (FractionRing K[X]) (LinfAt f) ...`.
- **What**: Transfers separability from the `K⟮f⟯`-form to the `LinfAt`-form via Bridge A's AlgEquiv.
- **How**: Repeats the AlgEquiv chain construction, then `@Algebra.IsSeparable.of_equiv_equiv` with Bridge A's commuting square.
- **Uses from project**: `K_E_separable_over_LinfAt_gamma_pullback_x_gen` (consumed by), same AlgEquiv pattern, `LinfAt.algebraFractionRing`, `polyToFieldOfInv_X`
- **Used by**: `K_E_separable_over_LinfAt_gamma_pullback_x_gen`
- **Visibility**: public (in Conditional)
- **Lines**: 3276–3401, 126 lines (proof >30 lines)
- **Notes**: Third repetition of the AlgEquiv chain construction (see also `bridgeA` and `finrank_adjoin_eq_finrank_LinfAt`).

---

### `theorem Conditional.K_E_separable_over_LinfAt_gamma_pullback_x_gen`

- **Type**: Under `hf`, `[CharP K p]`, `[Fact p.Prime]`, `hq`: `@Algebra.IsSeparable (FractionRing K[X]) (LinfAt (γ*x)) ...`.
- **What**: Fully unconditional separability for `LinfAt (γ*x)` over `FractionRing K[X]`; constructs the tower `K⟮f⟯ ⊆ γ.pullback.fieldRange ⊆ K(E)` and applies `Algebra.IsSeparable.trans`.
- **How**: Builds `gammaBar : K(E) ≃ₐ[K] γ.pullback.fieldRange`, proves upper separability via `of_equiv_equiv` with `h_pc_sep`, proves lower via `of_equiv_equiv` with `functionField_isSeparable` and the `e_f` AlgEquiv for `K⟮f⟯`, then `Algebra.IsSeparable.trans` + `K_E_separable_of_KofF_separable`.
- **Uses from project**: `isogOneSub_negFrobenius_isSeparable`, `x_gen_transcendental`, `functionField_isSeparable`, `K_E_separable_of_KofF_separable`, `LinfAt.algebraFractionRing`
- **Used by**: available for downstream consumers
- **Visibility**: public (in Conditional)
- **Lines**: 3410–3577, 168 lines (proof >30 lines)
- **Notes**: set_option maxHeartbeats 1600000 (and synthInstance.maxHeartbeats 1600000), NO-COMMENT. Proof >30 lines (longest: 168 lines).

---

### `theorem Conditional.weightedPoleDegree_gamma_pullback_x_eq_two_mul_pointCount`

- **Type**: Under witnesses `h_uniform_pole_order`, `h_inertia_one`, `h_card`: `Σ_P (-(data.ordAt P)).toNat * inertiaDeg xIdeal P = 2 * pointCount W.toAffine`.
- **What**: Tier-2.5 milestone #2: the Sinf-weighted pole degree equals `2 · pointCount`.
- **How**: `Finset.sum_congr rfl` substituting `ordAt P = -2` and `inertiaDeg = 1` per-point, then `Finset.sum_const + smul_eq_mul + h_card`.
- **Uses from project**: `isogOneSub_negFrobenius`, `x_gen`, `pointCount`, `primesOverFinset`, `Sinf.ordAt`, `xIdeal`
- **Used by**: `bridgeB_weightedPoleDegree_eq_projectiveDivisorOf_sum`
- **Visibility**: public (in Conditional)
- **Lines**: 3601–3657, 57 lines (proof >30 lines)

---

### `theorem Conditional.bridgeB_weightedPoleDegree_eq_projectiveDivisorOf_sum`

- **Type**: Equates the Sinf-side weighted pole degree sum with the `projectiveDivisorOf`-support sum (both witness-parametric, both equal `2 · pointCount`).
- **What**: Bridge B: transitivity composition via `weightedPoleDegree_gamma_pullback_x_eq_two_mul_pointCount` and `lemma5_of_pole_orders_and_support_card`.
- **How**: `rw [weightedPoleDegree..., ← lemma5_of_pole_orders...]`.
- **Uses from project**: `weightedPoleDegree_gamma_pullback_x_eq_two_mul_pointCount`, `lemma5_of_pole_orders_and_support_card`, `isogOneSub_negFrobenius`, `x_gen`, `pointCount`
- **Used by**: `finrank_gamma_pullback_x_eq_projectiveDivisorOf_sum`
- **Visibility**: public (in Conditional)
- **Lines**: 3688–3743, 56 lines (proof >30 lines)

---

### `theorem Conditional.finrank_gamma_pullback_x_eq_projectiveDivisorOf_sum`

- **Type**: Under all witnesses (`hf`, `hMF`, `data`, `h_uniform_pole_order`, `h_inertia_one`, `h_card`, `h_pole_orders`, `h_support_card`): `Module.finrank (adjoin K {γ*x}) K(E) = Σ_P (-ord P).toNat` over `projectiveDivisorOf` support.
- **What**: Declaration 2 final-form: consumer-facing Computation A bridge composed of Bridge A + `finrank_gamma_pullback_x_eq_weightedPoleDegree` + Bridge B.
- **How**: Three rewrites: `bridgeA_intermediateField_adjoin_eq_fractionRing_finrank`, `finrank_gamma_pullback_x_eq_weightedPoleDegree`, then `bridgeB_weightedPoleDegree_eq_projectiveDivisorOf_sum`.
- **Uses from project**: `bridgeA_intermediateField_adjoin_eq_fractionRing_finrank`, `finrank_gamma_pullback_x_eq_weightedPoleDegree`, `bridgeB_weightedPoleDegree_eq_projectiveDivisorOf_sum`
- **Used by**: unused in file (the final assembly piece)
- **Visibility**: public (in Conditional)
- **Lines**: 3768–3829, 62 lines (proof >30 lines)

---

## Declarations in Conditional namespace block 1 (lines 273–2756)

### `theorem Conditional.pointValuation_eq_of_invariant_and_compatible`

- **Type**: Given `IsTranslateValuationCompatible W P k h` and `translateAlgEquivOfPoint W k f = f`: `(W_smooth W).pointValuation P f = (W_smooth W).pointValuation (P.translate_of_finite k h) f`.
- **What**: If a function is invariant under translation and the Step (B'') compatibility holds, then pointValuation is constant on the τ-orbit.
- **How**: Applies `translateAlgEquivOfPoint_smul_pointValuation_of_compatible`, then rewrites via invariance.
- **Uses from project**: `translateAlgEquivOfPoint_smul_pointValuation_of_compatible`, `IsTranslateValuationCompatible`
- **Used by**: `pointValuation_pullback_x_gen_eq_of_compatible`, `pointValuation_pullback_y_gen_eq_of_compatible`
- **Visibility**: public (in Conditional)
- **Lines**: 292–309

---

### `theorem Conditional.pointValuation_pullback_x_gen_eq_of_compatible`

- **Type**: For `k ∈ ker γ` and `IsTranslateValuationCompatible W P k h`: `pointValuation P (γ*x) = pointValuation (P+k) (γ*x)`.
- **What**: Specialises `pointValuation_eq_of_invariant_and_compatible` to `γ*x_gen` using `xy_family_isogOneSub_negFrobenius`.
- **Uses from project**: `pointValuation_eq_of_invariant_and_compatible`, `xy_family_isogOneSub_negFrobenius`, `isogOneSub_negFrobenius`
- **Used by**: unused in file
- **Visibility**: public (in Conditional)
- **Lines**: 329–343
- **Notes**: Dead code within this file.

---

### `theorem Conditional.pointValuation_pullback_y_gen_eq_of_compatible`

- **Type**: Same as previous but for `γ*y_gen`.
- **What**: y-companion of the orbit-constant valuation lemma.
- **Uses from project**: `pointValuation_eq_of_invariant_and_compatible`, `xy_family_isogOneSub_negFrobenius`, `isogOneSub_negFrobenius`
- **Used by**: unused in file
- **Visibility**: public (in Conditional)
- **Lines**: 347–361
- **Notes**: Dead code within this file.

---

### `theorem Conditional.ord_P_pullback_x_gen_eq_neg_two_of_step_C`

- **Type**: For `T` with `-T ∈ ker γ`, given `IsTranslateOrdAtInftyCompatible W T (-T) h_zero`: `ord_T(γ*x) = -2`.
- **What**: Lemma 3 finite-kernel value via Step (C) + xy_family + Lemma 1.
- **How**: `xy_family_isogOneSub_negFrobenius` provides invariance; `ord_P_eq_ordAtInfty_of_invariant_and_compatible` transports the order; Lemma 1 gives `-2`.
- **Uses from project**: `xy_family_isogOneSub_negFrobenius`, `ord_P_eq_ordAtInfty_of_invariant_and_compatible`, `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen`, `IsTranslateOrdAtInftyCompatible`
- **Used by**: unused in file
- **Visibility**: public (in Conditional)
- **Lines**: 389–412
- **Notes**: Dead code within this file; superseded by `lemma3_pole_at_T_unconditional`.

---

### `theorem Conditional.ord_P_pullback_x_gen_eq_neg_two_of_specialized_bridge`

- **Type**: Weaker hypothesis form: given the bridge AT the specific function only, derives `ord_T(γ*x) = -2`.
- **What**: Smallest viable hypothesis form for Lemma 3.
- **Uses from project**: `xy_family_isogOneSub_negFrobenius`, `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen`, `isogOneSub_negFrobenius`
- **Used by**: unused in file
- **Visibility**: public (in Conditional)
- **Lines**: 432–455
- **Notes**: Dead code within this file.

---

### `theorem Conditional.lemma3_pole_at_T_of_bridge_and_invariance`

- **Type**: Given bridge at `addPullback_x` and τ_{-T}-invariance of `γ*x`: `ord_T(γ*x) = -2`.
- **What**: Conditional Lemma 3 discharge.
- **How**: Rewrites via `isogOneSub_negFrobenius_pullback + addPullbackAlgHom_negFrobenius_x_gen_eq`, uses invariance to equate `ord_T f = ord_T(τ f)`, then bridge + `ord_addPullback_x_negFrobenius`.
- **Uses from project**: `isogOneSub_negFrobenius_pullback`, `addPullbackAlgHom_negFrobenius_x_gen_eq`, `ord_addPullback_x_negFrobenius`, `isogOneSub_negFrobenius`
- **Used by**: `lemma3_pole_at_T_unconditional`
- **Visibility**: public (in Conditional)
- **Lines**: 2472–2512, 41 lines (proof >30 lines)

---

## Summary of Unused Declarations (within this file)

The following declarations appear to have no callers within this file (dead-code candidates; they may be used by other files):
- `ord_T_translateAlgEquivOfPoint_neg_x_gen_sub_x_gen_pow_card_eq`
- `addSlope_negFrobeniusIsog_eq_secant`
- `ord_T_translateAlgEquivOfPoint_neg_x_gen_sub_negFrobeniusIsog_pullback_x_gen_eq`
- `Conditional.pointValuation_pullback_x_gen_eq_of_compatible`
- `Conditional.pointValuation_pullback_y_gen_eq_of_compatible`
- `Conditional.ord_P_pullback_x_gen_eq_neg_two_of_step_C`
- `Conditional.ord_P_pullback_x_gen_eq_neg_two_of_specialized_bridge`
- `Conditional.pole_gamma_pullback_x_imp_kernel`
- `lemma3_pole_at_T_unconditional`
- `Conditional.finrank_gamma_pullback_x_eq_projectiveDivisorOf_sum`
- `Conditional.K_E_separable_over_LinfAt_gamma_pullback_x_gen`
- `ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_eq`
- `Conditional.fact_transcendental_gamma_pullback_x_inv`

## Key API (used by 3+ other declarations in this file)

- `bridge_at_x_gen_of_non_2_tor` (7+ callers)
- `bridge_at_y_gen_of_non_2_tor` (6+ callers)
- `bridge_at_negFrobeniusIsog_pullback_x_gen_of_non_2_tor` (6+ callers)
- `ordAtInfty_x_gen_pow_card_eq` (5+ callers)
- `bridge_at_negFrobeniusIsog_pullback_y_gen_of_non_2_tor` (4 callers)
- `x_gen_add_negFrobeniusIsog_pullback_x_gen_ne_zero` (3 callers)
- `y_gen_add_negFrobeniusIsog_pullback_y_gen_ne_zero` (3 callers)
- `withTop_int_lt_of_lt_of_le` (used uniformly in one large proof)
