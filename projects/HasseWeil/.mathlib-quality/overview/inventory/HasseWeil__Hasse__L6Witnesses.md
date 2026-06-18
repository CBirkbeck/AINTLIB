# Inventory: ./HasseWeil/Hasse/L6Witnesses.lean

**File size**: 4796 lines  
**Namespace**: `HasseWeil` (outer), `HasseWeil.Conditional` (inner, lines 51–1175)  
**Summary**: Ships the substantive L6 witnesses for the Hasse bound chain (T5, T6, T6-SUB), plus a large downstream F.1 development building the order-based kernel-prime `bridge_Bi_kernelToPrime_v2`, its primality/liesOver/ramification properties, the DVR-domination valuation machinery for V.1.3, the closed-point ↔ prime correspondence (injective half axiom-clean; surjective half via one isolated `sorry`), the residue-field rationality results, and several squeeze composers for `Σ inertiaDeg = pointCount`.

---

## Declarations

### `theorem ord_kernel_pullback_x_eq_neg_two` (lines 75–95, proof ~21 lines)
- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) (T : (isogOneSub_negFrobenius W hq).kernel) → ordAtPoint T.val (γ.pullback (x_gen W)) = -2`
- **What**: T6 — every kernel point of `γ = 1 − π` has pullback-ord of `x_gen` equal to `−2`. Covers `.zero` (infinity), 2-torsion, and non-2-torsion cases.
- **How**: Case-splits on `T.val`; infinity case uses `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen`; 2-torsion uses `lemma3_pole_at_T_at_2tor`; non-2-torsion uses `lemma3_pole_at_T_unconditional`.
- **Hypotheses**: Elliptic curve over finite field of size ≥ 2.
- **Uses from project**: `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen`, `lemma3_pole_at_T_at_2tor`, `lemma3_pole_at_T_unconditional`, `SmoothPlaneCurve.ordAtPoint_zero_eq_ordAtInfty`, `SmoothPlaneCurve.ordAtPoint_some_eq_ord_P`
- **Used by**: `inv_gamma_pullback_x_pos_at_kernel`, `ord_kernel_pullback_x_eq_neg_two_of_two_torsion_witness` (indirectly via witness version)
- **Visibility**: public
- **Lines**: 75–95, proof ~21 lines
- **Notes**: None

---

### `theorem pointValuation_polyToFieldOfInv_le_one` (lines 100–137, proof ~38 lines)
- **Type**: Given `pointValuation P f⁻¹ ≤ 1`, for any polynomial `p : Polynomial K`, `pointValuation P (polyToFieldOfInv f p) ≤ 1`.
- **What**: A polynomial in `1/f` lands in the valuation integer ring at `P` when `1/f` itself does. Standard valuation algebra by polynomial induction.
- **How**: `Polynomial.induction_on`; constant case uses `pointValuation_algebraMap_F_le_one`; monomial case uses `mul_le_one'` and `pow_le_one'`.
- **Hypotheses**: Elliptic curve; `pointValuation P f⁻¹ ≤ 1`.
- **Uses from project**: `Curves.RamificationAtInfinity.polyToFieldOfInv_C`, `polyToFieldOfInv_X`, `SmoothPlaneCurve.pointValuation_algebraMap_F_le_one`
- **Used by**: `sinf_carrier_ord_nonneg_of_inv_le_one`
- **Visibility**: public (in `Conditional` namespace)
- **Lines**: 100–137, proof 38 lines
- **Notes**: Proof >30 lines.

---

### `theorem sinf_carrier_ord_nonneg_of_inv_le_one` (lines 143–213, proof ~71 lines)
- **Type**: For any `data : Sinf f` and carrier element `a`, if `pointValuation P f⁻¹ ≤ 1` then `0 ≤ ord_P P (algebraMap a)`.
- **What**: General principle: Sinf-carrier elements have nonneg ord at any smooth point where `1/f` is in the valuation integer ring. Proved by integrality descent: carrier is finite over `Polynomial K`, so every element is integral, and integrality over a valuation subring forces the element into that subring.
- **How**: Uses `Algebra.IsIntegral.of_finite`, `IsIntegral.algebraMap`, builds a codomain-restriction `φ : Polynomial K →+* integer` via `pointValuation_polyToFieldOfInv_le_one`, then applies `Valuation.integer.integers.isIntegral_iff_v_le_one`.
- **Hypotheses**: Elliptic curve; `pointValuation P f⁻¹ ≤ 1`.
- **Uses from project**: `pointValuation_polyToFieldOfInv_le_one`, `Curves.SmoothPlaneCurve.ord_P_zero`, `Curves.SmoothPlaneCurve.pointValuation_algebraMap_F_le_one`
- **Used by**: `Sinf_ord_nonneg_at_affine_kernel_point`
- **Visibility**: public; `set_option maxHeartbeats 1600000` at line 139 (NO-COMMENT)
- **Lines**: 143–213, proof ~71 lines
- **Notes**: Proof >30 lines; maxHeartbeats 1600000 at line 139 (before this decl, NO-COMMENT).

---

### `theorem inv_gamma_pullback_x_pos_at_kernel` (lines 220–228, proof 2 lines)
- **Type**: `ordAtPoint T.val (γ.pullback x_gen)⁻¹ = (2 : WithTop ℤ)` for every kernel point `T`.
- **What**: Immediate corollary of T6: the inverse has a zero of order 2 at each kernel point.
- **How**: `OpenLemmaPrimitives.kernel_point_is_pole_of_gamma_pullback_x` applied to `ord_kernel_pullback_x_eq_neg_two`.
- **Hypotheses**: Elliptic curve over field with ≥ 2 elements.
- **Uses from project**: `ord_kernel_pullback_x_eq_neg_two`, `OpenLemmaPrimitives.kernel_point_is_pole_of_gamma_pullback_x`
- **Used by**: `Sinf_ord_nonneg_at_affine_kernel_point`, `Sinf_ordAtInfty_nonneg_at_infinity_kernel_point`, `Sinf_kernelPrime_ne_bot`, `bridge_Bi_liesOver_v2`, `Sinf_ramificationIdx_eq_two_at_kernel`, `Conditional.inv_gamma_pullback_x_pos_at_kernel` (called by many downstream)
- **Visibility**: public
- **Lines**: 220–228, proof 2 lines
- **Notes**: Key API — used by many downstream declarations.

---

### `theorem Sinf_ord_nonneg_at_affine_kernel_point` (lines 236–274, proof ~39 lines)
- **Type**: For an affine kernel point `T.val = .some xT yT h_ns`, `0 ≤ ord_P ⟨xT, yT, h_ns⟩ (algebraMap a)` for all `a : data.carrier`.
- **What**: Sinf-carrier elements have nonneg ord at affine kernel points. Composes `inv_gamma_pullback_x_pos_at_kernel` with `sinf_carrier_ord_nonneg_of_inv_le_one` after converting the ord-equality to a valuation-le-one bound.
- **How**: Calls `pointValuation_le_one_of_ord_nonneg` to get `pointValuation ≤ 1` from `ord ≥ 0`, then applies `sinf_carrier_ord_nonneg_of_inv_le_one`.
- **Hypotheses**: Elliptic curve; finite kernel point; Sinf data.
- **Uses from project**: `inv_gamma_pullback_x_pos_at_kernel`, `Curves.pointValuation_le_one_of_ord_nonneg`, `sinf_carrier_ord_nonneg_of_inv_le_one`
- **Used by**: `Sinf_ord_nonneg_at_kernel_point_unconditional`
- **Visibility**: public; `set_option maxHeartbeats 1600000` at line 230 (NO-COMMENT)
- **Lines**: 236–274, proof ~39 lines
- **Notes**: Proof >30 lines; maxHeartbeats 1600000 at line 230 (NO-COMMENT).

---

### `theorem ordAtInfty_polyToFieldOfInv_nonneg` (lines 287–342, proof ~56 lines)
- **Type**: If `0 ≤ ordAtInfty f⁻¹`, then `0 ≤ ordAtInfty (polyToFieldOfInv f p)` for any polynomial `p`.
- **What**: The ord-at-infinity analogue of `pointValuation_polyToFieldOfInv_le_one`; a polynomial in `1/f` has nonneg ord-at-infinity when `1/f` does.
- **How**: `Polynomial.induction_on`; constant case via `ordAtInfty_algebraMap_F_nonzero`; add case via `ordAtInfty_add_ge_min`; monomial case via `ordAtInfty_mul` + `ordAtInfty_pow` + `nsmul_nonneg`.
- **Hypotheses**: Elliptic curve; `0 ≤ ordAtInfty f⁻¹`.
- **Uses from project**: `ordAtInfty_algebraMap_F_nonzero`, `SmoothPlaneCurve.ordAtInfty_zero`, `SmoothPlaneCurve.ordAtInfty_add_ge_min`, `SmoothPlaneCurve.ordAtInfty_mul`, `SmoothPlaneCurve.ordAtInfty_pow`
- **Used by**: `ordAtInfty_nonneg_of_isIntegral_polyToFieldOfInv`
- **Visibility**: public
- **Lines**: 287–342, proof ~56 lines
- **Notes**: Proof >30 lines.

---

### `lemma ord_finset_sum_strict_gt` (lines 347–363, proof ~17 lines)
- **Type**: Finset non-archimedean strict-dominance: if all summands have `ordAtInfty > c` then the sum does too.
- **What**: A Finset-induction tool: given a strict lower bound on all summands' `ordAtInfty`, the same lower bound holds for the sum.
- **How**: Finset induction; insert step uses `lt_min` and `ordAtInfty_add_ge_min`.
- **Hypotheses**: Finset, `c ≠ ⊤`, pointwise ord bound.
- **Uses from project**: `SmoothPlaneCurve.ordAtInfty_zero`, `SmoothPlaneCurve.ordAtInfty_add_ge_min`
- **Used by**: `ordAtInfty_nonneg_of_isIntegral_polyToFieldOfInv`
- **Visibility**: public
- **Lines**: 347–363, proof ~17 lines
- **Notes**: None.

---

### `theorem ordAtInfty_nonneg_of_isIntegral_polyToFieldOfInv` (lines 385–513, proof ~129 lines)
- **Type**: If `g : K(E)` is integral over `Polynomial K` via `polyToFieldOfInv f` and `0 ≤ ordAtInfty f⁻¹`, then `0 ≤ ordAtInfty g`.
- **What**: The ord-at-infinity analogue of the pointwise carrier integrality result. Proof by contradiction using leading-term strict-dominance.
- **How**: Contradiction; extracts `m < 0`; splits on `n = natDegree p`: degree-0 (monic ⟹ `p = 1`, contradiction from `eval 1 = 1`); degree ≥ 1 uses `h_sum_strict_gt` (inner sublemma via `ordAtInfty_polyToFieldOfInv_nonneg` + `ordAtInfty_pow_of_ord_eq`) to show `eraseLead` summand dominates, then `ordAtInfty_add_eq_of_lt` gives `ord(aeval p) = n*m ≠ ⊤`, contradicting `aeval p = 0`.
- **Hypotheses**: Elliptic curve; `0 ≤ ordAtInfty f⁻¹`; `g` integral.
- **Uses from project**: `ordAtInfty_polyToFieldOfInv_nonneg`, `ord_finset_sum_strict_gt`, `SmoothPlaneCurve.ordAtInfty_pow_of_ord_eq`, `SmoothPlaneCurve.ordAtInfty_mul`, `SmoothPlaneCurve.ordAtInfty_add_eq_of_lt`, `SmoothPlaneCurve.ordAtInfty_zero`
- **Used by**: `sinf_carrier_ordAtInfty_nonneg_of_inv_nonneg`
- **Visibility**: public
- **Lines**: 385–513, proof ~129 lines
- **Notes**: Proof >30 lines (longest in file at ~129 lines). A complete proof of the integral-element valuation bound at infinity via contradiction and degree argument.

---

### `theorem sinf_carrier_ordAtInfty_nonneg_of_inv_nonneg` (lines 521–543, proof ~23 lines)
- **Type**: For `a : data.carrier`, if `0 ≤ ordAtInfty f⁻¹` then `0 ≤ ordAtInfty (algebraMap a)`.
- **What**: Composes module-finiteness integrality with `ordAtInfty_nonneg_of_isIntegral_polyToFieldOfInv` to get the infinity-place analogue of the carrier ord-nonneg result.
- **How**: `Algebra.IsIntegral.of_finite` + `IsIntegral.algebraMap` then applies `ordAtInfty_nonneg_of_isIntegral_polyToFieldOfInv`.
- **Hypotheses**: Elliptic curve; `0 ≤ ordAtInfty f⁻¹`.
- **Uses from project**: `ordAtInfty_nonneg_of_isIntegral_polyToFieldOfInv`
- **Used by**: `Sinf_ordAtInfty_nonneg_at_infinity_kernel_point`
- **Visibility**: public; `set_option maxHeartbeats 1600000` at line 515 (NO-COMMENT)
- **Lines**: 521–543, proof ~23 lines
- **Notes**: maxHeartbeats 1600000 at line 515 (NO-COMMENT).

---

### `theorem Sinf_ordAtInfty_nonneg_at_infinity_kernel_point` (lines 549–576, proof ~28 lines)
- **Type**: For `T.val = .zero`, `0 ≤ ordAtInfty (algebraMap a)` for all `a : data.carrier`.
- **What**: The infinity-branch of carrier ord-nonneg. Specializes `sinf_carrier_ordAtInfty_nonneg_of_inv_nonneg` using `inv_gamma_pullback_x_pos_at_kernel` to get `0 ≤ ordAtInfty f⁻¹`.
- **How**: Rewrites `ordAtPoint .zero = ordAtInfty`, uses `h_inv_pos` to get `0 ≤ 2`, then applies `sinf_carrier_ordAtInfty_nonneg_of_inv_nonneg`.
- **Hypotheses**: `T.val = .zero`; elliptic curve; Sinf data.
- **Uses from project**: `inv_gamma_pullback_x_pos_at_kernel`, `sinf_carrier_ordAtInfty_nonneg_of_inv_nonneg`
- **Used by**: `Sinf_ord_nonneg_at_kernel_point_unconditional`
- **Visibility**: public; `set_option maxHeartbeats 1600000` at line 545 (NO-COMMENT)
- **Lines**: 549–576, proof ~28 lines
- **Notes**: maxHeartbeats 1600000 at line 545 (NO-COMMENT).

---

### `theorem Sinf_ord_nonneg_at_kernel_point_unconditional` (lines 585–614, proof ~30 lines)
- **Type**: For any kernel point `T` (including infinity), `0 ≤ ordAtPoint T.val (algebraMap a)` for all `a : data.carrier`.
- **What**: The unconditional union of the affine (`Sinf_ord_nonneg_at_affine_kernel_point`) and infinity (`Sinf_ordAtInfty_nonneg_at_infinity_kernel_point`) carrier-ord-nonneg results.
- **How**: Case-splits on `T.val`; dispatches to respective theorems.
- **Hypotheses**: Elliptic curve over finite field; Sinf data.
- **Uses from project**: `Sinf_ordAtInfty_nonneg_at_infinity_kernel_point`, `Sinf_ord_nonneg_at_affine_kernel_point`
- **Used by**: `bridge_Bi_kernelToPrime_v2` (smul_mem), `bridge_Bi_isPrime_v2`, `bridge_Bi_liesOver_v2`, `Sinf_ordAtPoint_nonneg_of_valuation_le_one`, `Sinf_intValuation_eq_exp_neg_ordAtInfty_at_zero`, `Sinf_kernelPrime_pow_le_ord`
- **Visibility**: public; `set_option maxHeartbeats 1600000` at line 578 (NO-COMMENT)
- **Lines**: 585–614, proof ~30 lines
- **Notes**: maxHeartbeats 1600000 at line 578 (NO-COMMENT). Key API — called by 6+ downstream declarations.

---

### `theorem genuine_dual_comp_pullback_x_gen_eq_mulByInt_x_decomp` (lines 647–664)
- **Type**: `(β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK)).pullback (x_gen W) = mulByInt_x W (q*r² − t*r*s + s²)` where `q = #K`, `t = isogTrace`.
- **What**: Obstacle 3 Wall B (x-coord): pullback-level double-Vieta match for composition. **Contains `sorry`.**
- **How**: `sorry`
- **Hypotheses**: Elliptic curve; `V` dual of Frobenius; trace hypothesis; `r, s ≠ 0` in ℤ and in K.
- **Uses from project**: `genuineIsogSmulSub`, `isogTrace`, `isogOneSub_negFrobenius`, `mulByInt_x`, `frobeniusIsog`, `IsDualOf`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 647–664
- **Notes**: **sorry**. Dead code (no callers in file).

---

### `theorem genuine_dual_comp_pullback_y_gen_eq_mulByInt_y_decomp` (lines 667–684)
- **Type**: Analogous y-coord identity to the above. **Contains `sorry`.**
- **What**: Obstacle 3 Wall B (y-coord). **Contains `sorry`.**
- **How**: `sorry`
- **Hypotheses**: Same as x-coord version.
- **Uses from project**: Same as x-coord version, plus `mulByInt_y`, `y_gen`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 667–684
- **Notes**: **sorry**. Dead code (no callers in file).

---

### `theorem degree_quadratic_exists_edge_s_char_divisible` (lines 695–703)
- **Type**: When `(s:K) = 0`, there exists `β : Isogeny` with `β.degree = q*r² − t*r*s + s²`. **Contains `sorry`.**
- **What**: Obstacle 4 Case 1: char-divisible edge case for the QF degree. **Contains `sorry`.**
- **How**: `sorry`
- **Hypotheses**: Elliptic curve; `(s:K) = 0`; `r, s ≠ 0 ∈ ℤ`.
- **Uses from project**: `isogTrace`, `isogOneSub_negFrobenius`, `frobeniusIsog`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 695–703
- **Notes**: **sorry**. Dead code (no callers in file).

---

### `theorem degree_quadratic_exists_edge_r_char_divisible` (lines 706–714)
- **Type**: Symmetric: when `(r:K) = 0`. **Contains `sorry`.**
- **What**: Obstacle 4 Case 2. **Contains `sorry`.**
- **How**: `sorry`
- **Hypotheses**: Elliptic curve; `(r:K) = 0`; `r, s ≠ 0 ∈ ℤ`.
- **Uses from project**: `isogTrace`, `isogOneSub_negFrobenius`, `frobeniusIsog`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 706–714
- **Notes**: **sorry**. Dead code (no callers in file).

---

### `theorem ord_kernel_pullback_x_eq_neg_two_of_two_torsion_witness` (lines 717–748, proof ~32 lines)
- **Type**: Given a 2-torsion witness hypothesis, `ordAtPoint T.val (γ.pullback x_gen) = -2`.
- **What**: Witness-parametric version of T6 where the 2-torsion case is factored as a hypothesis (for modularity before `PoleDivisor2Tor` was complete).
- **How**: Case-splits on `.zero`, 2-torsion, and non-2-torsion; delegates to `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen`, the witness, and `lemma3_pole_at_T_unconditional`.
- **Hypotheses**: Elliptic curve; witness for 2-torsion case.
- **Uses from project**: `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen`, `lemma3_pole_at_T_unconditional`
- **Used by**: `support_card_eq_pointCount_of_two_torsion_ord_witness`
- **Visibility**: public
- **Lines**: 717–748, proof ~32 lines
- **Notes**: Proof >30 lines. Now superseded by `ord_kernel_pullback_x_eq_neg_two` (which has no witness hyp).

---

### `theorem support_card_eq_pointCount_of_per_point_witness` (lines 770–803, proof ~34 lines)
- **Type**: Given that all K-rational projective smooth points are in the support (per-point nonzero witness), `|support (projectiveDivisorOf (γ.pullback x_gen))| = pointCount`.
- **What**: T5 — support cardinality equals point count, conditional on a per-point hypothesis. Uses `Fintype ProjectiveSmoothPoint` and `card_eq_card_affine_point`.
- **How**: Shows `support = Finset.univ` from the per-point witness, then rewrites card via `Finset.card_univ` and `ProjectiveSmoothPoint.card_eq_card_affine_point`.
- **Hypotheses**: Elliptic curve; `Fintype W.toAffine.Point`; per-point nonzero witness.
- **Uses from project**: `Curves.ProjectiveSmoothPoint.card_eq_card_affine_point`
- **Used by**: `support_card_eq_pointCount_of_two_torsion_ord_witness`, `l6_support_card_of_two_torsion_witness`
- **Visibility**: public
- **Lines**: 770–803, proof ~34 lines
- **Notes**: Proof >30 lines.

---

### `theorem h_pole_orders_of_T5_T6_witnesses` (lines 823–843, proof ~21 lines)
- **Type**: Given that every support point has divisor value = −2, derive that `.toNat = 0` and `(-..).toNat = 2` for all support points.
- **What**: T5-T6 combined: a structural lemma converting the signed-integer −2 value to the `toNat` pair consumed by `lemma5_of_pole_orders_and_support_card`.
- **How**: Pure `decide` after rewriting with `h_eq`.
- **Hypotheses**: Elliptic curve; `Fintype W.toAffine.Point`; per-point `= -2` witness.
- **Uses from project**: (none from project beyond type-level)
- **Used by**: unused in this file (probably consumed externally)
- **Visibility**: public
- **Lines**: 823–843, proof ~21 lines
- **Notes**: None.

---

### `theorem finrank_pullback_fieldRange_field_eq_two_of_witness` (lines 860–886, proof ~27 lines)
- **Type**: Identity theorem: the finrank lower step equals 2 if the witness says so.
- **What**: R25-B3-LOWER-WIRE witness wrapper: given the lower-step finrank = 2 hypothesis with `@`-explicit module, the conclusion is the same hypothesis.
- **How**: `h_lower_witness` (trivial).
- **Hypotheses**: Elliptic curve; h_le; h_lower_witness.
- **Uses from project**: (none beyond type)
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 860–886, proof 1 line
- **Notes**: Near-trivial wrapper kept for architectural documentation.

---

### `theorem finrank_pullback_fieldRange_field_eq_two_unconditional` (lines 915–1037, proof ~123 lines)
- **Type**: `Module.finrank K⟮f⟯ γ.pullback.fieldRange = 2` for `f = γ.pullback x_gen`, given `f` transcendental over K and `K⟮f⟯ ≤ fieldRange`.
- **What**: R25-B3-LOWER unconditional (W5): the finrank lower step axiom-clean, via gammaBar/e_f iso-pair transport of `finrank_functionField_eq_two`.
- **How**: Builds `gammaBar : K(E) ≃ₐ[K] fieldRange` via `AlgEquiv.ofInjectiveField` and `e_f : FractionRing K[X] ≃ₐ[K] K⟮f⟯` via `RatFunc.algEquivOfTranscendental`; proves compatibility square on the generator X via `IsLocalization.algHom_ext` + `Polynomial.algHom_ext`; applies `Algebra.finrank_eq_of_equiv_equiv`; uses `finrank_functionField_eq_two`.
- **Hypotheses**: Elliptic curve; `f` transcendental; `K⟮f⟯ ≤ fieldRange`.
- **Uses from project**: `finrank_functionField_eq_two`, `RatFunc.algEquivOfTranscendental`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 915–1037, proof ~123 lines
- **Notes**: Proof >30 lines.

---

### `theorem support_card_eq_pointCount_of_two_torsion_ord_witness` (lines 1064–1111, proof ~48 lines)
- **Type**: Given a 2-torsion ord witness, `|support (projectiveDivisorOf (γ.pullback x_gen))| = pointCount`.
- **What**: T22 substantive: reduces the support-cardinality goal to the single 2-torsion case via case-analysis on projective points.
- **How**: Calls `support_card_eq_pointCount_of_per_point_witness`; per-point proof splits `.infinity` (uses `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen`) and `.affine` (shows kernel membership via `isogOneSub_negFrobenius_toAddMonoidHom` + `sub_self`, then calls `ord_kernel_pullback_x_eq_neg_two_of_two_torsion_witness`).
- **Hypotheses**: Elliptic curve; `Fintype W.toAffine.Point`; 2-torsion ord witness.
- **Uses from project**: `support_card_eq_pointCount_of_per_point_witness`, `ord_kernel_pullback_x_eq_neg_two_of_two_torsion_witness`, `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen`, `isogOneSub_negFrobenius_toAddMonoidHom`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 1064–1111, proof ~48 lines
- **Notes**: Proof >30 lines.

---

### `theorem projectiveDivisorOf_pullback_x_gen_eq_neg_two_of_two_torsion_witness` (lines 1131–1148, proof ~18 lines)
- **Type**: Given 2-torsion ord witness, `projectiveDivisorOf (W_smooth W) (γ.pullback x_gen) P = -2` for all projective smooth points `P`.
- **What**: Pointwise −2 value at all K-rational projective points, combining shipped affine/infinity results with the 2-torsion witness.
- **How**: Splits affine (2-torsion vs non-2-torsion) and infinity cases; `decide` closes the `≠ 0` goals.
- **Hypotheses**: Elliptic curve; 2-torsion ord witness.
- **Uses from project**: `lemma3_pole_at_T_unconditional`, `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen`
- **Used by**: `l6_support_card_of_two_torsion_witness`
- **Visibility**: public
- **Lines**: 1131–1148, proof ~18 lines
- **Notes**: None.

---

### `theorem l6_support_card_of_two_torsion_witness` (lines 1154–1173, proof ~20 lines)
- **Type**: Support cardinality = pointCount conditional on 2-torsion ord witness.
- **What**: L4 witness-parametric: composes `projectiveDivisorOf_pullback_x_gen_eq_neg_two_of_two_torsion_witness` with `support_card_eq_pointCount_of_per_point_witness`.
- **How**: Calls `support_card_eq_pointCount_of_per_point_witness` with per-point proof via `projectiveDivisorOf_pullback_x_gen_eq_neg_two_of_two_torsion_witness` + `decide`.
- **Hypotheses**: Elliptic curve; `Fintype W.toAffine.Point`; 2-torsion ord witness.
- **Uses from project**: `support_card_eq_pointCount_of_per_point_witness`, `projectiveDivisorOf_pullback_x_gen_eq_neg_two_of_two_torsion_witness`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 1154–1173, proof ~20 lines
- **Notes**: None.

---

### `theorem Valuation.isEquiv_iff_eq_of_surjective_withZeroInt` (lines 1209–1254, proof ~46 lines)
- **Type**: Two surjective `ℤᵐ⁰`-valued valuations on a field that are `IsEquiv` are equal.
- **What**: General field-valuation lemma: surjective equivalence on the discrete value group `ℤᵐ⁰` implies value equality.
- **How**: Constructs a "unit" element `e` with `v e = exp 1`; shows `w x = (w e)^(log v x)` for `v x ≠ 0` via `IsEquiv`; uses `hw` surjectivity to pin `log(w e) = 1`; applies `Valuation.ext`.
- **Hypotheses**: Field; two surjective valuations; `IsEquiv`.
- **Uses from project**: none (pure mathlib)
- **Used by**: `Sinf_kernelPrime_valuation_isEquiv_pointValuation_at_affine`, `Sinf_intValuation_eq_exp_neg_ordAtInfty_at_zero`, `Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel`, `Sinf_kernelToPrime_v2_injective`
- **Visibility**: public
- **Lines**: 1209–1254, proof ~46 lines
- **Notes**: Proof >30 lines. General mathlib-eligible lemma (noted in docstring as "not in mathlib").

---

### `theorem Valuation.isEquiv_of_valuationSubring_le` (lines 1263–1271, proof ~9 lines)
- **Type**: If `v.valuationSubring.toLocalSubring ≤ w.valuationSubring.toLocalSubring`, then `v.IsEquiv w`.
- **What**: Maximality glue: a domination in the LocalSubring order forces valuation equivalence, because valuation subrings are maximal for domination.
- **How**: `ValuationSubring.isMax_toLocalSubring.eq_of_le` + `ValuationSubring.toLocalSubring_injective` + `Valuation.isEquiv_iff_valuationSubring`.
- **Hypotheses**: Field; linear-ordered-comm-group-with-zero; domination hypothesis.
- **Uses from project**: none (pure mathlib)
- **Used by**: `Sinf_kernelPrime_valuation_isEquiv_pointValuation_at_affine`
- **Visibility**: public
- **Lines**: 1263–1271, proof ~9 lines
- **Notes**: None.

---

### `noncomputable def bridge_Bi_kernelToPrime_v2` (lines 1279–1333, proof ~55 lines)
- **Type**: `Ideal data.carrier` — the order-based kernel prime at `T`: `{a | 0 < ordAtPoint T.val (algebraMap a)}`.
- **What**: F.1 dispatch: the order-based prime ideal of the Sinf carrier at each kernel point. Packages `zero_mem`, `add_mem`, and `smul_mem` using `ordAtPoint_add_le`, `ordAtPoint_mul`, and `Sinf_ord_nonneg_at_kernel_point_unconditional`.
- **How**: `refine { carrier := ..., add_mem' := ..., zero_mem' := ..., smul_mem' := ... }` with each subgoal proved separately; smul_mem uses `Sinf_ord_nonneg_at_kernel_point_unconditional`.
- **Hypotheses**: Elliptic curve over finite field; Sinf data; kernel point.
- **Uses from project**: `Sinf_ord_nonneg_at_kernel_point_unconditional`, `SmoothPlaneCurve.ordAtPoint_add_le`, `SmoothPlaneCurve.ordAtPoint_mul`, `SmoothPlaneCurve.ordAtPoint_zero_function`
- **Used by**: `bridge_Bi_isPrime_v2`, `bridge_Bi_liesOver_v2`, `Sinf_kernelPrime_pow_le_ord`, `Sinf_kernelPrime_ne_bot`, `Sinf_kernelPrime_heightOne`, `bridge_Biii_ord_eq_neg_two_v2`, `bridge_Bii_kernelToPrime_mem_primesOverFinset_v2`, `Sinf_kernelToPrime_v2_injective`, `Sinf_kappa_kernelPrime_residue_in_base`, `Sinf_kappa_kernelPrime_algebraMap_surjective`, `Sinf_finrank_kappa_kernelPrime_eq_one`, `bridge_Biv_inertia_eq_one_v2`, `bridge_Bii_mem_primesOverFinset_v2`, `Sinf_ramificationIdx_eq_two_at_kernel`, `Sinf_kernelPrime_pow_mem_of_le_ord`, `bridge_Bii_surjective_v2`, `Sinf_primeOver_eq_kernelPrime_place_of_sum_inertia_eq_pointCount`, `Sinf_sum_inertiaDeg_eq_pointCount_of_surjectivity_witness`, `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_finrank_witness`
- **Visibility**: public
- **Lines**: 1279–1333, proof ~55 lines
- **Notes**: Proof >30 lines. **Key API** — the central data structure of the F.1 chain.

---

### `theorem bridge_Bi_isPrime_v2` (lines 1341–1400, proof ~60 lines)
- **Type**: `(bridge_Bi_kernelToPrime_v2 W hq data T).IsPrime`
- **What**: The order-based kernel prime is indeed prime: `1 ∉ P` (via `ordAtPoint_one = 0 < 0` is false) and multiplicativity (`0 < A + B → 0 ≤ A → 0 ≤ B → 0 < A ∨ 0 < B`).
- **How**: `Ideal.IsPrime` split; ne_top uses `ordAtPoint_one`; mem_or_mem uses `ordAtPoint_mul` and `Sinf_ord_nonneg_at_kernel_point_unconditional` with WithTop ℤ arithmetic.
- **Hypotheses**: Elliptic curve over finite field; Sinf data; kernel point.
- **Uses from project**: `Sinf_ord_nonneg_at_kernel_point_unconditional`, `SmoothPlaneCurve.ordAtPoint_one`, `SmoothPlaneCurve.ordAtPoint_mul`
- **Used by**: `Sinf_kernelPrime_heightOne`, `bridge_Bii_kernelToPrime_mem_primesOverFinset_v2`, `Sinf_finrank_kappa_kernelPrime_eq_one`, `bridge_Biv_inertia_eq_one_v2`, `Sinf_primeOver_eq_kernelPrime_of_valuation_eq`, `Sinf_primeOver_eq_kernelPrime_of_algebraMap_X_mem`, `Sinf_kernelPoint_of_inertiaDeg_one_of_primeOver`, `Sinf_exists_kernelPoint_of_primeOver`, `Sinf_primeOver_xIdeal_eq_kernelPrime`
- **Visibility**: public
- **Lines**: 1341–1400, proof ~60 lines
- **Notes**: Proof >30 lines.

---

### `theorem bridge_Bi_liesOver_v2` (lines 1417–1537, proof ~121 lines)
- **Type**: `(bridge_Bi_kernelToPrime_v2 W hq data T).LiesOver xIdeal`
- **What**: The order-based kernel prime lies over `xIdeal = (X) ⊂ Polynomial K`. Proves `xIdeal = P.comap (algebraMap)` via a scalar-tower collapse (algebraMap through the tower gives `aeval f⁻¹ p`) and the forward/reverse directions for `X ∣ p`.
- **How**: Scalar-tower collapse via `IsScalarTower.algebraMap_apply` and `LinfAt.algebraMap_polynomial_apply`; forward uses `ordAtPoint_mul` + `h_ord_g = 2`; reverse (contraposition) splits off the constant term and uses `ordAtPoint_add_eq_of_lt` (strict min).
- **Hypotheses**: Elliptic curve; Sinf data; kernel point.
- **Uses from project**: `Conditional.inv_gamma_pullback_x_pos_at_kernel`, `Conditional.Sinf_ord_nonneg_at_kernel_point_unconditional`, `SmoothPlaneCurve.ordAtPoint_mul`, `SmoothPlaneCurve.ordAtPoint_add_eq_of_lt`, `SmoothPlaneCurve.ordAtPoint_algebraMap_F_of_ne_zero`, `RamificationAtInfinity.xIdeal`, `RamificationAtInfinity.LinfAt.algebraMap_polynomial_apply`, `RamificationAtInfinity.polyToFieldOfInv_X`
- **Used by**: `bridge_Bii_kernelToPrime_mem_primesOverFinset_v2`, `bridge_Biv_inertia_eq_one_v2`, `Sinf_finrank_kappa_kernelPrime_eq_one`, `Sinf_kappa_kernelPrime_algebraMap_surjective`
- **Visibility**: public
- **Lines**: 1417–1537, proof ~121 lines
- **Notes**: Proof >30 lines.

---

### `theorem Sinf_kernelPrime_pow_le_ord` (lines 1560–1628, proof ~69 lines)
- **Type**: `a ∈ (bridge_Bi_kernelToPrime_v2 W hq data T)^n → (n : WithTop ℤ) ≤ ordAtPoint T.val (algebraMap a)`.
- **What**: The easy half of the DVR membership equivalence: membership in `P_T^n` forces curve-order ≥ n. Proved by `Submodule.pow_induction_on_left'`.
- **How**: Three cases of `pow_induction_on_left'`: base (`n = 0`), additive (non-archimedean min), multiplicative (order ≥ 1 from membership in `P_T` + discrete-valued `0 < v → 1 ≤ v`).
- **Hypotheses**: Elliptic curve; Sinf data; kernel point; `a ∈ P_T^n`.
- **Uses from project**: `Conditional.Sinf_ord_nonneg_at_kernel_point_unconditional`, `SmoothPlaneCurve.ordAtPoint_add_le`, `SmoothPlaneCurve.ordAtPoint_mul`
- **Used by**: `Sinf_ramificationIdx_eq_two_at_kernel`
- **Visibility**: public
- **Lines**: 1560–1628, proof ~69 lines
- **Notes**: Proof >30 lines.

---

### `theorem Sinf_kernelPrime_ne_bot` (lines 1644–1691, proof ~48 lines)
- **Type**: `bridge_Bi_kernelToPrime_v2 W hq data T ≠ ⊥`
- **What**: The order-based kernel prime is nonzero: `xc = algebraMap (Polynomial K) carrier X` lies in `P_T` (its ord is 2 > 0) and is nonzero (via `IsFractionRing.injective` and `f ≠ 0`).
- **How**: Scalar-tower collapse shows `algebraMap carrier L xc = f⁻¹`; `Conditional.inv_gamma_pullback_x_pos_at_kernel` gives ord = 2 > 0; injectivity of `algebraMap carrier L` shows `xc ≠ 0`; `Ideal.mem_bot` gives contradiction.
- **Hypotheses**: Elliptic curve; Sinf data; kernel point.
- **Uses from project**: `Conditional.inv_gamma_pullback_x_pos_at_kernel`, `RamificationAtInfinity.LinfAt.algebraMap_polynomial_apply`, `RamificationAtInfinity.polyToFieldOfInv_X`
- **Used by**: `Sinf_kernelPrime_heightOne`
- **Visibility**: public
- **Lines**: 1644–1691, proof ~48 lines
- **Notes**: Proof >30 lines.

---

### `noncomputable def Sinf_kernelPrime_heightOne` (lines 1702–1718, proof ~17 lines)
- **Type**: `IsDedekindDomain.HeightOneSpectrum data.carrier` — packages `P_T` as a height-one prime.
- **What**: Bundles `bridge_Bi_kernelToPrime_v2`, `bridge_Bi_isPrime_v2`, and `Sinf_kernelPrime_ne_bot` into a `HeightOneSpectrum`.
- **How**: Anonymous constructor `{ asIdeal := ..., isPrime := ..., ne_bot := ... }`.
- **Hypotheses**: Elliptic curve; Sinf data; kernel point; `IsDedekindDomain` instances.
- **Uses from project**: `bridge_Bi_kernelToPrime_v2`, `bridge_Bi_isPrime_v2`, `Sinf_kernelPrime_ne_bot`
- **Used by**: `Sinf_kernelPrime_valuation_surjective`, `Sinf_kernelPrime_valuationSubring_isDVR`, `Sinf_ordAtPoint_nonneg_of_valuation_le_one`, `Sinf_kernelPrime_valuationSubring_le_pointValuation_subring`, `Sinf_kernelPrime_valuationSubring_le_pointValuation_at_affine`, `Sinf_kernelPrime_valuation_isEquiv_pointValuation_at_affine`, `Sinf_intValuation_eq_exp_neg_ordAtInfty_at_zero`, `Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel`, `Sinf_intValuation_le_exp_neg_at_kernel`, `Sinf_kernelPrime_pow_mem_of_le_ord`, `Sinf_ramificationIdx_eq_two_at_kernel`, `bridge_Biii_ord_eq_neg_two_v2`, `Sinf_kernelToPrime_v2_injective`, `bridge_Bii_kernelToPrime_mem_primesOverFinset_v2`, `Sinf_primeOver_eq_kernelPrime_of_valuation_eq`
- **Visibility**: public
- **Lines**: 1702–1718
- **Notes**: Key API — the central packaging used by essentially all valuation machinery.

---

### `theorem Curves.SmoothPlaneCurve.pointValuation_eq_exp_neg_of_ord_P_eq` (lines 1726–1738, proof ~13 lines)
- **Type**: For nonzero `f` with `ord_P P f = n`, `pointValuation P f = WithZero.exp (-n)`.
- **What**: Expresses the multiplicative pointValuation in terms of the additive ord via `WithZero.exp`. Immediate from the definition of `ord_P`.
- **How**: Unfolds `ord_P`; uses `WithZero.exp`, `ofAdd_toAdd`, `WithZero.coe_unzero`.
- **Hypotheses**: `f ≠ 0`; `ord_P P f = n`.
- **Uses from project**: `Curves.SmoothPlaneCurve.ord_P`
- **Used by**: `Curves.SmoothPlaneCurve.pointValuation_surjective`, `Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel`
- **Visibility**: public
- **Lines**: 1726–1738, proof ~13 lines
- **Notes**: None.

---

### `theorem Curves.SmoothPlaneCurve.pointValuation_surjective` (lines 1744–1759, proof ~16 lines)
- **Type**: `Function.Surjective (C.pointValuation P)` for any smooth point `P`.
- **What**: The pointValuation is surjective onto `ℤᵐ⁰`, using the DVR uniformizer.
- **How**: Applies `exists_uniformizer`; converts to `pointValuation = exp(-1)` via `pointValuation_eq_exp_neg_of_ord_P_eq`; surjectivity on nonzero targets uses `zpow` with `exp`.
- **Hypotheses**: Field `F`; smooth plane curve; smooth point.
- **Used by**: `Sinf_kernelPrime_valuationSubring_le_pointValuation_at_affine`, `Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel`, `Sinf_kernelToPrime_v2_injective`
- **Visibility**: public
- **Lines**: 1744–1759, proof ~16 lines
- **Notes**: None.

---

### `theorem Sinf_kernelPrime_valuation_surjective` (lines 1765–1796, proof ~32 lines)
- **Type**: `Function.Surjective ((Sinf_kernelPrime_heightOne W hq data T).valuation L)` where `L = LinfAt f`.
- **What**: The carrier adic valuation on `L` is surjective onto `ℤᵐ⁰`. Uses `valuation_exists_uniformizer` and `exp`-power construction.
- **How**: Gets uniformizer `π` with `v π = ofAdd(-1) = exp(-1)`; surjectivity via `zpow`.
- **Hypotheses**: Elliptic curve; Sinf data; kernel point; `IsDedekindDomain`, `isFractionRing` instances.
- **Uses from project**: `Sinf_kernelPrime_heightOne`
- **Used by**: `Sinf_kernelPrime_valuationSubring_isDVR`, `Sinf_kernelPrime_valuationSubring_le_pointValuation_at_affine`, `Sinf_intValuation_eq_exp_neg_ordAtInfty_at_zero`, `Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel`, `Sinf_kernelToPrime_v2_injective`
- **Visibility**: public
- **Lines**: 1765–1796, proof ~32 lines
- **Notes**: Proof >30 lines.

---

### `theorem rankOne_valuationSubring_le_eq_of_ne_top` (lines 1824–1880, proof ~57 lines)
- **Type**: For `A : ValuationSubring L` a DVR, `A ≤ B` and `B ≠ ⊤` implies `A = B`.
- **What**: Rank-one overring = self-or-top: DVR valuation subrings have no proper nontrivial overrings. The geometric crux of V.1.3.
- **How**: Uses `ValuationSubring.primeSpectrumEquiv`, `prime_idealOfLE`, `isMax_toLocalSubring`, `IsLocalRing.maximalIdeal_eq_bot` (for `⊤` = field), `Ideal.comap_bot_of_injective`; transports through `PrimeSpectrum.ext`.
- **Hypotheses**: `[IsDiscreteValuationRing A]`; `A ≤ B`; `B ≠ ⊤`.
- **Uses from project**: none (pure mathlib)
- **Used by**: `Sinf_kernelPrime_valuationSubring_isDVR`, `Sinf_kernelPrime_valuationSubring_le_pointValuation_at_affine`, `Sinf_intValuation_eq_exp_neg_ordAtInfty_at_zero`, `Sinf_kernelToPrime_v2_injective`
- **Visibility**: public
- **Lines**: 1824–1880, proof ~57 lines
- **Notes**: Proof >30 lines. Key API — called by 4+ declarations. Docstring notes it is not in mathlib.

---

### `theorem Sinf_kernelPrime_valuationSubring_isDVR` (lines 1891–1937, proof ~47 lines)
- **Type**: `IsDiscreteValuationRing ((Sinf_kernelPrime_heightOne W hq data T).valuation L).valuationSubring`
- **What**: The adic valuation's valuation subring is a DVR. Used by `rankOne_valuationSubring_le_eq_of_ne_top`.
- **How**: Uses `Sinf_kernelPrime_valuation_surjective` to show `valueGroup v = ⊤`; transports `IsCyclic` and `Nontrivial` of `(ℤᵐ⁰)ˣ` through the top-subgroup equivalence; applies `Valuation.valuationSubring_isDiscreteValuationRing`.
- **Hypotheses**: Elliptic curve; Sinf data; kernel point; `IsDedekindDomain`.
- **Uses from project**: `Sinf_kernelPrime_valuation_surjective`, `Sinf_kernelPrime_heightOne`
- **Used by**: `Sinf_kernelPrime_valuationSubring_le_pointValuation_at_affine`, `Sinf_intValuation_eq_exp_neg_ordAtInfty_at_zero`, `Sinf_kernelToPrime_v2_injective`
- **Visibility**: public
- **Lines**: 1891–1937, proof ~47 lines
- **Notes**: Proof >30 lines.

---

### `theorem Sinf_ordAtPoint_nonneg_of_valuation_le_one` (lines 1962–2032, proof ~71 lines)
- **Type**: If `(Sinf_kernelPrime_heightOne W hq data T).valuation L x ≤ 1`, then `0 ≤ ordAtPoint T.val x`.
- **What**: The easy (forward) half of the carrier-valuation ↔ `ord_T` identification: `v_{P_T}(x) ≤ 1` (x is `P_T`-integral) implies `ord_T(x) ≥ 0`. Uses `IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer` to write `x = n/d` with `d ∉ P_T`, then `Sinf_ord_nonneg_at_kernel_point_unconditional` on `n` and the definition of `P_T` on `d`.
- **How**: `exists_primeCompl_mul_eq_of_integer`; `ordAtPoint_mul` to add ords; `d ∉ P_T` ⟹ `ord_T(d) ≤ 0`; carrier nonneg gives `ord_T(d) = 0`; `ord_T(x) = ord_T(n) ≥ 0`.
- **Hypotheses**: Elliptic curve; Sinf data; kernel point; `v(x) ≤ 1`.
- **Uses from project**: `Conditional.Sinf_ord_nonneg_at_kernel_point_unconditional`, `SmoothPlaneCurve.ordAtPoint_mul`
- **Used by**: `Sinf_kernelPrime_valuationSubring_le_pointValuation_subring`, `Sinf_intValuation_eq_exp_neg_ordAtInfty_at_zero`, `Sinf_kernelToPrime_v2_injective`
- **Visibility**: public
- **Lines**: 1962–2032, proof ~71 lines
- **Notes**: Proof >30 lines.

---

### `theorem Sinf_kernelPrime_valuationSubring_le_pointValuation_subring` (lines 2042–2084, proof ~43 lines)
- **Type**: `(Sinf_kernelPrime_heightOne W hq data T).valuation L).valuationSubring ≤ (C.pointValuation ⟨xT, yT, h_ns⟩).valuationSubring` (for affine `T`).
- **What**: Subring inclusion in the affine case: `v_{P_T}$-integral implies `pointValuation ≤ 1` at the finite point. The easy half of the domination.
- **How**: Applies `Sinf_ordAtPoint_nonneg_of_valuation_le_one` to get `ord ≥ 0`, then `pointValuation_le_one_of_ord_nonneg`.
- **Hypotheses**: Affine kernel point.
- **Uses from project**: `Sinf_ordAtPoint_nonneg_of_valuation_le_one`, `Curves.pointValuation_le_one_of_ord_nonneg`
- **Used by**: `Sinf_kernelPrime_valuationSubring_le_pointValuation_at_affine`
- **Visibility**: public
- **Lines**: 2042–2084, proof ~43 lines
- **Notes**: Proof >30 lines.

---

### `theorem Sinf_kernelPrime_valuationSubring_le_pointValuation_at_affine` (lines 2118–2177, proof ~60 lines)
- **Type**: `(Sinf_kernelPrime_heightOne W hq data T).valuation L).valuationSubring.toLocalSubring ≤ (C.pointValuation ⟨xT, yT, h_ns⟩).valuationSubring.toLocalSubring`
- **What**: The LocalSubring domination in the affine case. The **irreducible residual** underlying the valuation equivalence: the `IsLocalHom` component is the genuinely-open content (`bridge_Bii_bijective`). Per the docstring, isolated as named residual with ticket `T-V-1-3-RAMIDX-EQ-ORDATPOINT`.
- **How**: Applies `Sinf_kernelPrime_valuationSubring_isDVR`, `Sinf_kernelPrime_valuationSubring_le_pointValuation_subring`, then shows `B ≠ ⊤` via `pointValuation_surjective` and `valuationSubring_eq_top_iff`; finally `rankOne_valuationSubring_le_eq_of_ne_top` gives `A = B`, then `le_of_eq`.
- **Hypotheses**: Affine kernel point; `IsDedekindDomain`.
- **Uses from project**: `Sinf_kernelPrime_valuationSubring_isDVR`, `Sinf_kernelPrime_valuationSubring_le_pointValuation_subring`, `rankOne_valuationSubring_le_eq_of_ne_top`, `Curves.SmoothPlaneCurve.pointValuation_surjective`
- **Used by**: `Sinf_kernelPrime_valuation_isEquiv_pointValuation_at_affine`
- **Visibility**: public
- **Lines**: 2118–2177, proof ~60 lines
- **Notes**: Proof >30 lines. Contains the deep geometric content of V.1.3 (the valuation-subring domination).

---

### `theorem Sinf_kernelPrime_valuation_isEquiv_pointValuation_at_affine` (lines 2200–2229, proof ~30 lines)
- **Type**: `((Sinf_kernelPrime_heightOne W hq data T).valuation L).IsEquiv (C.pointValuation ⟨xT, yT, h_ns⟩)` for affine `T`.
- **What**: The adic valuation and the curve's pointValuation at an affine kernel point are equivalent. One-line application of `Valuation.isEquiv_of_valuationSubring_le`.
- **How**: Calls `Sinf_kernelPrime_valuationSubring_le_pointValuation_at_affine`.
- **Hypotheses**: Affine kernel point; `IsDedekindDomain`.
- **Uses from project**: `Valuation.isEquiv_of_valuationSubring_le`, `Sinf_kernelPrime_valuationSubring_le_pointValuation_at_affine`
- **Used by**: `Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel`, `Sinf_kernelToPrime_v2_injective`
- **Visibility**: public
- **Lines**: 2200–2229, proof ~30 lines
- **Notes**: None.

---

### `theorem Sinf_intValuation_eq_exp_neg_ordAtInfty_at_zero` (lines 2242–2322, proof ~81 lines)
- **Type**: For `T.val = .zero`, `(Sinf_kernelPrime_heightOne W hq data T).intValuation a = WithZero.exp (-d)` when `ordAtPoint T.val (algebraMap a) = d`.
- **What**: Value identity at the point at infinity: the carrier's intrinsic adic valuation equals `exp(-ord_∞)` on the carrier. The infinity-branch of the value identity, isolated because `ordAtInfty` is not packaged as a DVR/ValuationSubring in the project.
- **How**: Same DVR-domination strategy as the affine branch, but using `ordAtInftyValuation`: shows `A ≤ B` via `Sinf_ordAtPoint_nonneg_of_valuation_le_one` + `ordAtInftyValuation_le_one_of_ordAtInfty_nonneg`; `B ≠ ⊤` from `ordAtInftyValuation_surjective`; `rankOne_valuationSubring_le_eq_of_ne_top`; then `isEquiv_iff_eq_of_surjective_withZeroInt` + `pointValuation_eq_exp_neg_of_ord_P_eq`.
- **Hypotheses**: `T.val = .zero`; nonzero carrier element; ord = d.
- **Uses from project**: `Sinf_kernelPrime_valuationSubring_isDVR`, `Sinf_ordAtPoint_nonneg_of_valuation_le_one`, `rankOne_valuationSubring_le_eq_of_ne_top`, `Valuation.isEquiv_iff_eq_of_surjective_withZeroInt`, `Sinf_kernelPrime_valuation_surjective`, `SmoothPlaneCurve.ordAtInftyValuation_surjective`, `SmoothPlaneCurve.ordAtInftyValuation_le_one_of_ordAtInfty_nonneg`, `SmoothPlaneCurve.ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`
- **Used by**: `Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel`
- **Visibility**: public
- **Lines**: 2242–2322, proof ~81 lines
- **Notes**: Proof >30 lines.

---

### `theorem Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel` (lines 2367–2418, proof ~52 lines)
- **Type**: For any nonzero `a : data.carrier`, if `ordAtPoint T.val (algebraMap a) = d` then `(Sinf_kernelPrime_heightOne W hq data T).intValuation a = WithZero.exp (-d)`.
- **What**: The single sharply-isolated mathematical gap for V.1.3: the per-element value form `v_{P_T} = exp(-ord_T)`. Case-splits on infinity (delegates to `Sinf_intValuation_eq_exp_neg_ordAtInfty_at_zero`) and affine (uses `Sinf_kernelPrime_valuation_isEquiv_pointValuation_at_affine` + `isEquiv_iff_eq_of_surjective_withZeroInt` + `pointValuation_eq_exp_neg_of_ord_P_eq`).
- **How**: `rcases T.val`; affine branch uses the `IsEquiv` → equality route + `valuation_of_algebraMap`.
- **Hypotheses**: Elliptic curve; nonzero carrier element; explicit ord = d.
- **Uses from project**: `Sinf_intValuation_eq_exp_neg_ordAtInfty_at_zero`, `Sinf_kernelPrime_valuation_isEquiv_pointValuation_at_affine`, `Valuation.isEquiv_iff_eq_of_surjective_withZeroInt`, `Sinf_kernelPrime_valuation_surjective`, `Curves.SmoothPlaneCurve.pointValuation_surjective`, `Curves.SmoothPlaneCurve.pointValuation_eq_exp_neg_of_ord_P_eq`
- **Used by**: `Sinf_intValuation_le_exp_neg_at_kernel`
- **Visibility**: public
- **Lines**: 2367–2418, proof ~52 lines
- **Notes**: Proof >30 lines. Despite the long docstring calling it the "sole sorry of the chain", its proof is NOT a `sorry` — it calls `Sinf_intValuation_eq_exp_neg_ordAtInfty_at_zero` which itself relies on `Sinf_kernelPrime_valuationSubring_le_pointValuation_at_affine` (the genuinely-open domination). The sorries are inherited from `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount`.

---

### `theorem Sinf_intValuation_le_exp_neg_at_kernel` (lines 2438–2486, proof ~49 lines)
- **Type**: If `(m : WithTop ℤ) ≤ ordAtPoint T.val (algebraMap a)` then `(Sinf_kernelPrime_heightOne ...).intValuation a ≤ WithZero.exp (-m)`.
- **What**: The reverse membership direction packaged as a valuation bound. Derived from `Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel`.
- **How**: Case-splits `a = 0` (trivial); for `a ≠ 0` extracts `d` from non-top ord, applies `Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel`, then uses antitonicity of `exp` via `WithZero.exp_le_exp`.
- **Hypotheses**: Elliptic curve; Sinf data; kernel point; ord bound `m ≤ ord_T(algebraMap a)`.
- **Uses from project**: `Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel`
- **Used by**: `Sinf_kernelPrime_pow_mem_of_le_ord`
- **Visibility**: public
- **Lines**: 2438–2486, proof ~49 lines
- **Notes**: Proof >30 lines.

---

### `theorem Sinf_kernelPrime_pow_mem_of_le_ord` (lines 2506–2537, proof ~32 lines)
- **Type**: `(n : WithTop ℤ) ≤ ordAtPoint T.val (algebraMap a) → a ∈ (bridge_Bi_kernelToPrime_v2 ...)^n`
- **What**: The reverse membership direction `ord_T ≥ n ⟹ a ∈ P_T^n`. Uses `intValuation_le_pow_iff_mem` from mathlib and `Sinf_intValuation_le_exp_neg_at_kernel`.
- **How**: Packages `P_T` as `HeightOneSpectrum`, rewrites goal as `a ∈ v.asIdeal^n`, applies `IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem`, then calls `Sinf_intValuation_le_exp_neg_at_kernel`.
- **Hypotheses**: Elliptic curve; Sinf data; kernel point; ord bound.
- **Uses from project**: `Sinf_kernelPrime_heightOne`, `Sinf_intValuation_le_exp_neg_at_kernel`
- **Used by**: `Sinf_ramificationIdx_eq_two_at_kernel`
- **Visibility**: public
- **Lines**: 2506–2537, proof ~32 lines
- **Notes**: Proof >30 lines.

---

### `theorem Sinf_ramificationIdx_eq_two_at_kernel` (lines 2568–2623, proof ~56 lines)
- **Type**: `Ideal.ramificationIdx (algebraMap (Polynomial K) data.carrier) xIdeal (bridge_Bi_kernelToPrime_v2 ...) = 2`
- **What**: The ramification index at each kernel prime is 2. Uses `Ideal.ramificationIdx_spec` with `n = 2`, feeding both membership directions.
- **How**: Shows `xIdeal.map = span{xc}`; for `≤ 2`: `Sinf_kernelPrime_pow_mem_of_le_ord` with `ord_T(f⁻¹) = 2`; for `¬ ≤ 3`: `Sinf_kernelPrime_pow_le_ord` contradicts `3 ≤ 2`.
- **Hypotheses**: Elliptic curve; Sinf data; kernel point.
- **Uses from project**: `Sinf_kernelPrime_pow_mem_of_le_ord`, `Sinf_kernelPrime_pow_le_ord`, `Conditional.inv_gamma_pullback_x_pos_at_kernel`
- **Used by**: `bridge_Biii_ord_eq_neg_two_v2`
- **Visibility**: public
- **Lines**: 2568–2623, proof ~56 lines
- **Notes**: Proof >30 lines.

---

### `theorem bridge_Biii_ord_eq_neg_two_v2` (lines 2642–2659, proof ~18 lines)
- **Type**: `data.ordAt (bridge_Bi_kernelToPrime_v2 ...) = (-2 : ℤ)`
- **What**: Bridge B(iii): the carrier ord at each kernel prime is −2. Reduces to `Sinf_ramificationIdx_eq_two_at_kernel` via `data.ordAt = -(ramificationIdx)`.
- **How**: `change` to ramificationIdx form; `Sinf_ramificationIdx_eq_two_at_kernel`; `norm_num`.
- **Hypotheses**: Elliptic curve; Sinf data; kernel point.
- **Uses from project**: `Sinf_ramificationIdx_eq_two_at_kernel`
- **Used by**: `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_finrank_witness`
- **Visibility**: public
- **Lines**: 2642–2659, proof ~18 lines
- **Notes**: None.

---

### `theorem bridge_Bii_kernelToPrime_mem_primesOverFinset_v2` (lines 2686–2705, proof ~20 lines)
- **Type**: `bridge_Bi_kernelToPrime_v2 W hq data T ∈ primesOverFinset xIdeal data.carrier`
- **What**: Backward direction of linchpin: every order-based kernel prime is in the finset of primes-over-`(X)`. Composes `bridge_Bi_isPrime_v2` and `bridge_Bi_liesOver_v2` with `mem_primesOverFinset_iff`.
- **How**: `mem_primesOverFinset_iff` + the two bridge results.
- **Hypotheses**: Elliptic curve; Sinf data; kernel point; `IsDedekindDomain`.
- **Uses from project**: `bridge_Bi_isPrime_v2`, `bridge_Bi_liesOver_v2`, `RamificationAtInfinity.xIdeal_ne_bot`
- **Used by**: `Sinf_primeOver_eq_kernelPrime_place_of_sum_inertia_eq_pointCount`, `Sinf_sum_inertiaDeg_eq_pointCount_of_surjectivity_witness`, `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_finrank_witness`, `bridge_Bii_mem_primesOverFinset_v2`
- **Visibility**: public
- **Lines**: 2686–2705, proof ~20 lines
- **Notes**: None.

---

### `theorem Sinf_kernelToPrime_v2_injective` (lines 2754–2930, proof ~177 lines)
- **Type**: `Function.Injective (fun T => bridge_Bi_kernelToPrime_v2 W hq data T)`
- **What**: The kernel-to-prime map is injective: distinct kernel points give distinct primes. Proved by valuation-matching: equal primes have equal adic valuations; identify each with the curve's place (affine or infinity); use `maximalIdealAt_injective` for the affine case and a `coordX`-witness for the mixed/infinity cases.
- **How**: Uses `IsDedekindDomain.HeightOneSpectrum.ext`, `Sinf_kernelPrime_valuation_isEquiv_pointValuation_at_affine`, `Valuation.isEquiv_iff_eq_of_surjective_withZeroInt`, `Curves.SmoothPlaneCurve.maximalIdealAt_injective`; mixed case uses `coordX_ne_zero`, `ordAtInfty_coordX`, `pointValuation_algebraMap_le_one`.
- **Hypotheses**: Elliptic curve; Sinf data.
- **Uses from project**: `Sinf_kernelPrime_heightOne`, `Valuation.isEquiv_iff_eq_of_surjective_withZeroInt`, `Sinf_kernelPrime_valuation_surjective`, `Sinf_kernelPrime_valuation_isEquiv_pointValuation_at_affine`, `Curves.SmoothPlaneCurve.pointValuation_surjective`, `Sinf_kernelPrime_valuationSubring_isDVR`, `Sinf_ordAtPoint_nonneg_of_valuation_le_one`, `rankOne_valuationSubring_le_eq_of_ne_top`, `SmoothPlaneCurve.ordAtInftyValuation_surjective`, `SmoothPlaneCurve.maximalIdealAt_injective`, `SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`
- **Used by**: `Sinf_primeOver_eq_kernelPrime_place_of_sum_inertia_eq_pointCount`, `Sinf_sum_inertiaDeg_eq_pointCount_of_surjectivity_witness`, `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_finrank_witness`
- **Visibility**: public
- **Lines**: 2754–2930, proof ~177 lines
- **Notes**: Proof >30 lines (longest non-sorry proof at ~177 lines). Axiom-clean per docstring.

---

### `theorem Sinf_algebraMap_X_mem_of_liesOver` (lines 2944–2966, proof ~23 lines)
- **Type**: For `P.LiesOver xIdeal`, `algebraMap (Polynomial K) data.carrier X ∈ P`.
- **What**: L1 (closed leaf): `LiesOver (X)` implies the generator `algebraMap X` lies in `P`. Pure ideal algebra.
- **How**: `LiesOver.over` gives `xIdeal = P.comap`; `X ∈ span{X}` (via `dvd_refl`); `Ideal.mem_comap`.
- **Hypotheses**: `P.LiesOver xIdeal`.
- **Uses from project**: `RamificationAtInfinity.xIdeal`
- **Used by**: `bridge_Bi_liesOver_v2` (conceptually), `Sinf_primeOver_eq_kernelPrime_of_algebraMap_X_mem`, `Sinf_exists_kernelPoint_of_primeOver`
- **Visibility**: public
- **Lines**: 2944–2966, proof ~23 lines
- **Notes**: None.

---

### `theorem Sinf_liesOver_of_algebraMap_X_mem` (lines 3015–3043, proof ~29 lines)
- **Type**: For a prime `P` with `algebraMap X ∈ P`, `P.LiesOver xIdeal`.
- **What**: L1.5: the converse packaging — `algebraMap X ∈ P` (for a prime `P`) upgrades to `LiesOver`. Uses maximality of `xIdeal`.
- **How**: `Ideal.span_le`; `xIdeal_isMaximal.eq_of_le`; `Ideal.LiesOver.over`.
- **Hypotheses**: `P.IsPrime`; `algebraMap X ∈ P`.
- **Uses from project**: `RamificationAtInfinity.xIdeal_isMaximal`
- **Used by**: `Sinf_kernelPoint_place_eq_of_inertiaDeg_one_of_primeOver`, `Sinf_primeOver_eq_kernelPrime_of_algebraMap_X_mem`, `Sinf_exists_kernelPoint_of_primeOver`
- **Visibility**: public
- **Lines**: 3015–3043, proof ~29 lines
- **Notes**: None.

---

### `theorem residue_in_base_affine_of_pointValuation_le_one` (lines 3088–3139, proof ~52 lines)
- **Type**: For affine smooth `P` and `g` with `pointValuation P g ≤ 1`, there is `lam : F` with `pointValuation P (g − algebraMap F C.FunctionField lam) < 1`.
- **What**: Residue-at-an-affine-point is in the base field: any function regular at `P` has a residue in `F`. Field-agnostic, via `quotientMaximalIdealAtEquiv`.
- **How**: Lifts `g` to `localRingAt P` via `mem_localRingAt_image_of_pointValuation_le_one`; surjectivity of `algebraMap F → ResidueField` via `quotientMaximalIdealAtEquiv.symm_apply_apply`; pulls back the residue; `residue_eq_zero_iff` + `valuation_lt_one_iff_mem`.
- **Hypotheses**: Smooth plane curve over field `F`; affine smooth point; `g` regular at `P`.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`, `SmoothPlaneCurve.quotientMaximalIdealAtEquiv`, `IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem`
- **Used by**: `Sinf_kappa_kernelPrime_residue_in_base`
- **Visibility**: public
- **Lines**: 3088–3139, proof ~52 lines
- **Notes**: Proof >30 lines. General field-agnostic lemma; mathlib-eligible candidate.

---

### `theorem residue_in_base_at_infinity_of_ordAtInfty_nonneg` (lines 3161–3219, proof ~59 lines)
- **Type**: For `g : C.FunctionField` with `0 ≤ ordAtInfty g`, there is `lam : F` with `0 < ordAtInfty (g − algebraMap F C.FunctionField lam)`.
- **What**: Residue-at-infinity is in the base field. Uses the `{1, y}` basis decomposition: x-part uses `ordAtInfty_exists_const_sub_pos_of_fracPolyX_nonneg`; y-part is strictly positive by parity of ord (odd exponents).
- **How**: `exists_decomp` splits `g = α + β·y`; `ordAtInfty_basis_eq_min`; x-part residue from `ordAtInfty_exists_const_sub_pos_of_fracPolyX_nonneg`; y-part positivity from `0 ≤ -2·intDeg q - 3 → 0 < -2·intDeg q - 3` by parity (omega); final `ordAtInfty_add_ge_min`.
- **Hypotheses**: Smooth plane curve over field `F`; `g` regular at infinity.
- **Uses from project**: `SmoothPlaneCurve.exists_decomp`, `SmoothPlaneCurve.ordAtInfty_basis_eq_min`, `SmoothPlaneCurve.ordAtInfty_algebraMap_fracPolyX_of_ne_zero`, `SmoothPlaneCurve.ordAtInfty_coordYInFunctionField`, `SmoothPlaneCurve.ordAtInfty_exists_const_sub_pos_of_fracPolyX_nonneg`, `SmoothPlaneCurve.ordAtInfty_zero`, `SmoothPlaneCurve.ordAtInfty_mul`, `SmoothPlaneCurve.ordAtInfty_add_ge_min`
- **Used by**: `Sinf_kappa_kernelPrime_residue_in_base`
- **Visibility**: public
- **Lines**: 3161–3219, proof ~59 lines
- **Notes**: Proof >30 lines.

---

### `theorem Sinf_kappa_kernelPrime_residue_in_base` (lines 3221–3285, proof ~65 lines)
- **Type**: For any carrier element `a`, there is `lam : K` with `a − algebraMap (Polynomial K) data.carrier (C lam) ∈ bridge_Bi_kernelToPrime_v2 ...`
- **What**: The residue field at each kernel prime is K: every carrier element is congruent to a K-constant mod `P_T`. Case-splits on affine/infinity.
- **How**: Affine: `residue_in_base_affine_of_pointValuation_le_one`; infinity: `residue_in_base_at_infinity_of_ordAtInfty_nonneg`; both use `Sinf_ord_nonneg_at_kernel_point_unconditional` and scalar-tower collapse for the constant embedding.
- **Hypotheses**: Elliptic curve; Sinf data; kernel point.
- **Uses from project**: `Conditional.Sinf_ord_nonneg_at_kernel_point_unconditional`, `residue_in_base_affine_of_pointValuation_le_one`, `residue_in_base_at_infinity_of_ordAtInfty_nonneg`, `Curves.pointValuation_le_one_of_ord_nonneg`
- **Used by**: `Sinf_kappa_kernelPrime_algebraMap_surjective`, `Sinf_residue_in_base_of_primeOver`
- **Visibility**: public
- **Lines**: 3221–3285, proof ~65 lines
- **Notes**: Proof >30 lines.

---

### `theorem Sinf_primeOver_eq_kernelPrime_place_of_sum_inertia_eq_pointCount` (lines 3317–3405, proof ~89 lines)
- **Type**: Given `Σ_{P ∈ primesOverFinset} inertiaDeg (X) P = pointCount`, any prime `P` lying over `xIdeal` is some `bridge_Bi_kernelToPrime_v2 W hq data T`.
- **What**: F.1 unifying bridge combinator: pure Finset/cardinality argument. Given the sum-of-inertia identity, derives that `image = primesOverFinset` and thus every prime is a kernel-prime.
- **How**: Injectivity + backward inclusion give `image ⊆ primesOverFinset` and `image.card = pointCount`; `inertiaDeg_pos` bounds `primesOverFinset.card ≤ pointCount`; cardinality squeeze gives `image = primesOverFinset`; membership extraction.
- **Hypotheses**: Elliptic curve; `Fintype W.toAffine.Point`; Sinf data; sum hypothesis; prime; LiesOver.
- **Uses from project**: `bridge_Bii_kernelToPrime_mem_primesOverFinset_v2`, `Sinf_kernelToPrime_v2_injective`, `kernel_eq_top_of_hom_eq_id_sub_frobenius`, `RamificationAtInfinity.xIdeal_ne_bot`, `RamificationAtInfinity.xIdeal_isMaximal`
- **Used by**: `Sinf_primeOver_eq_kernelPrime_place`
- **Visibility**: public
- **Lines**: 3317–3405, proof ~89 lines
- **Notes**: Proof >30 lines. Depends on `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount` (which has a sorry) only indirectly through `Sinf_primeOver_eq_kernelPrime_place`.

---

### `theorem Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount` (lines 3461–3487)
- **Type**: `∑ P ∈ primesOverFinset xIdeal data.carrier, inertiaDeg (X) P = pointCount W.toAffine`
- **What**: The sum of inertia degrees over all primes above `(X)` equals the number of K-rational points. **Contains `sorry`.** The single irreducible sorry of the chain (K1-K6 plan, K̄-base change needed).
- **How**: `sorry`
- **Hypotheses**: Elliptic curve; `Fintype W.toAffine.Point`; Sinf data.
- **Uses from project**: none
- **Used by**: `Sinf_primeOver_eq_kernelPrime_place`
- **Visibility**: public
- **Lines**: 3461–3487
- **Notes**: **sorry**. The sole `sorry` on the critical path to V.1.3.

---

### `theorem Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_witness` (lines 3497–3516, proof 1 line)
- **Type**: Identity: given the sum hypothesis as `h_witness`, the sum equals `pointCount`. Trivial wrapper.
- **What**: Architecture placeholder: names the sharp irreducible content and allows downstream consumers to wire through a single named hypothesis.
- **How**: `h_witness` (trivial).
- **Hypotheses**: The sum hypothesis.
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 3497–3516, proof 1 line
- **Notes**: Near-trivial.

---

### `def ker_oneSubGeomFrobHom_setOfFixed_K` (lines 3539–3542)
- **Type**: `Set (W.baseChange (AlgebraicClosure K)).toAffine.Point` — `{P | geomFrobeniusPointFun W P = P}`.
- **What**: Phase 3 K3 alias: the K̄-Frobenius-fixed locus as a `setOf`-predicate set (avoids AddSubgroup → Set coercion issues).
- **How**: Definition.
- **Hypotheses**: Elliptic curve.
- **Uses from project**: `geomFrobeniusPointFun`
- **Used by**: `ker_oneSubGeomFrobHom_setOfFixed_card_eq_pointCount`, `geom_poles_card_eq_pointCount_of_pole_eq_ker`, `geom_poles_natCard_eq_pointCount_of_pole_eq_ker`, `geomPoles_oneSubFrob_eq_ker_setOfFixed`, `Sinf_sum_inertiaDeg_eq_pointCount_of_K3_K2K5_witnesses`
- **Visibility**: public
- **Lines**: 3539–3542
- **Notes**: None.

---

### `theorem ker_oneSubGeomFrobHom_setOfFixed_card_eq_pointCount` (lines 3547–3554, proof ~8 lines)
- **Type**: `(ker_oneSubGeomFrobHom_setOfFixed_K W).ncard = Fintype.card W.toAffine.Point`
- **What**: K4: the K̄-fixed-locus has the same cardinality as the point set. Composition of `ker_oneSubGeomFrobHom_eq_fixedLocus` and `ncard_ker_oneSubGeomFrobHom_eq_pointCount`.
- **How**: `← ker_oneSubGeomFrobHom_eq_fixedLocus`; `ncard_ker_oneSubGeomFrobHom_eq_pointCount`.
- **Uses from project**: `ker_oneSubGeomFrobHom_eq_fixedLocus`, `ncard_ker_oneSubGeomFrobHom_eq_pointCount`
- **Used by**: `geom_poles_card_eq_pointCount_of_pole_eq_ker`
- **Visibility**: public
- **Lines**: 3547–3554, proof ~8 lines
- **Notes**: None.

---

### `theorem geom_poles_card_eq_pointCount_of_pole_eq_ker` (lines 3558–3568, proof ~10 lines)
- **Type**: `geomPoles.ncard = Fintype.card W.toAffine.Point` given `geomPoles = ker_oneSubGeomFrobHom_setOfFixed_K W`.
- **What**: K3+K4 dispatcher (ncard form): K3 hypothesis + K4 cardinality = pointCount.
- **How**: Rewrite K3 hypothesis; `ker_oneSubGeomFrobHom_setOfFixed_card_eq_pointCount`.
- **Uses from project**: `ker_oneSubGeomFrobHom_setOfFixed_card_eq_pointCount`
- **Used by**: `geom_poles_natCard_eq_pointCount_of_pole_eq_ker`
- **Visibility**: public
- **Lines**: 3558–3568, proof ~10 lines
- **Notes**: None.

---

### `theorem geom_poles_natCard_eq_pointCount_of_pole_eq_ker` (lines 3573–3579, proof ~6 lines)
- **Type**: `Nat.card geomPoles = Fintype.card W.toAffine.Point` given `geomPoles = ker...`
- **What**: K3+K4 dispatcher (Nat.card form).
- **How**: `Nat.card_coe_set_eq` + `geom_poles_card_eq_pointCount_of_pole_eq_ker`.
- **Uses from project**: `geom_poles_card_eq_pointCount_of_pole_eq_ker`
- **Used by**: `geomPoles_oneSubFrob_card_eq_pointCount`, `Sinf_sum_inertiaDeg_eq_pointCount_of_K3_K2K5_witnesses`
- **Visibility**: public
- **Lines**: 3573–3579, proof ~6 lines
- **Notes**: None.

---

### `def geomPoles_oneSubFrob` (lines 3601–3604)
- **Type**: `Set (W.baseChange (AlgebraicClosure K)).toAffine.Point` — `{P | oneSubGeomFrobHom W P = 0}`
- **What**: Phase 3 K3 — concrete geometric pole set: K̄-points killed by `id − π_K̄`.
- **How**: Definition.
- **Uses from project**: `oneSubGeomFrobHom`
- **Used by**: `geomPoles_oneSubFrob_eq_ker_setOfFixed`, `geomPoles_oneSubFrob_card_eq_pointCount`
- **Visibility**: public
- **Lines**: 3601–3604
- **Notes**: None.

---

### `theorem geomPoles_oneSubFrob_eq_ker_setOfFixed` (lines 3610–3619, proof ~10 lines)
- **Type**: `geomPoles_oneSubFrob W = ker_oneSubGeomFrobHom_setOfFixed_K W`
- **What**: K3 tautological equality: both sides unfold to `{P | geomFrobeniusPointFun W P = P}`.
- **How**: `← ker_oneSubGeomFrobHom_eq_fixedLocus`; `rfl`.
- **Uses from project**: `ker_oneSubGeomFrobHom_eq_fixedLocus`
- **Used by**: `geomPoles_oneSubFrob_card_eq_pointCount`
- **Visibility**: public
- **Lines**: 3610–3619, proof ~10 lines
- **Notes**: None.

---

### `theorem geomPoles_oneSubFrob_card_eq_pointCount` (lines 3627–3631, proof ~5 lines)
- **Type**: `Nat.card (geomPoles_oneSubFrob W) = Fintype.card W.toAffine.Point`
- **What**: K3+K4 concrete form.
- **How**: `geom_poles_natCard_eq_pointCount_of_pole_eq_ker` + `geomPoles_oneSubFrob_eq_ker_setOfFixed`.
- **Uses from project**: `geomPoles_oneSubFrob_eq_ker_setOfFixed`, `geom_poles_natCard_eq_pointCount_of_pole_eq_ker`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 3627–3631, proof ~5 lines
- **Notes**: None.

---

### `theorem Sinf_sum_inertiaDeg_eq_pointCount_of_K3_K2K5_witnesses` (lines 3648–3675, proof ~27 lines)
- **Type**: Given K3 and a K2+K5 splitting witness (`Σ f_P = Nat.card geomPoles`), conclude `Σ f_P = pointCount`.
- **What**: Phase B K2+K5 composer: transitivity through `geom_poles_natCard_eq_pointCount_of_pole_eq_ker`.
- **How**: K3+K4 gives `#geomPoles = pointCount`; compose.
- **Uses from project**: `geom_poles_natCard_eq_pointCount_of_pole_eq_ker`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 3648–3675, proof ~27 lines
- **Notes**: None.

---

### `theorem Sinf_primeOver_eq_kernelPrime_place` (lines 3701–3714, proof ~13 lines)
- **Type**: For any prime `P` lying over `xIdeal`, `∃ T, P = bridge_Bi_kernelToPrime_v2 W hq data T`.
- **What**: F.1 unifying bridge: a bare carrier prime over `(X)` is a kernel-prime place. Pure composition of `Sinf_primeOver_eq_kernelPrime_place_of_sum_inertia_eq_pointCount` with `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount`. Inherits the sorry.
- **How**: Applies the combinator with the sorry-leaf.
- **Uses from project**: `Sinf_primeOver_eq_kernelPrime_place_of_sum_inertia_eq_pointCount`, `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount`
- **Used by**: `Sinf_residue_in_base_of_primeOver`, `Sinf_kernelPoint_place_eq_of_inertiaDeg_one_of_primeOver`
- **Visibility**: public
- **Lines**: 3701–3714, proof ~13 lines
- **Notes**: Inherits sorry from `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount`.

---

### `theorem Sinf_residue_in_base_of_primeOver` (lines 3725–3745, proof ~21 lines)
- **Type**: For any prime `P` over `xIdeal` and carrier element `a`, there is `lam : K` with `a − algebraMap (C lam) ∈ P`.
- **What**: F.1 CORE residue-in-base: pure composition of `Sinf_primeOver_eq_kernelPrime_place` + `Sinf_kappa_kernelPrime_residue_in_base`.
- **How**: `Sinf_primeOver_eq_kernelPrime_place` gives `P = P_T`; `obtain ⟨T, rfl⟩`; apply `Sinf_kappa_kernelPrime_residue_in_base`.
- **Uses from project**: `Sinf_primeOver_eq_kernelPrime_place`, `Sinf_kappa_kernelPrime_residue_in_base`
- **Used by**: `Sinf_residue_surjective_of_primeOver`
- **Visibility**: public
- **Lines**: 3725–3745, proof ~21 lines
- **Notes**: Inherits sorry.

---

### `theorem Sinf_residue_surjective_of_primeOver` (lines 3760–3800, proof ~41 lines)
- **Type**: The residue structure map `(K[X]⧸(X)) → (carrier⧸P)` is surjective for any prime `P` over `xIdeal`.
- **What**: F.1 CORE: for any prime over `(X)`, the residue field is K (surjectivity). Composition of `Sinf_residue_in_base_of_primeOver` with quotient map machinery.
- **How**: `Sinf_residue_in_base_of_primeOver` gives the constant representative; `Ideal.quotientMap_mk`; `Ideal.Quotient.eq`; `neg_mem`.
- **Uses from project**: `Sinf_residue_in_base_of_primeOver`
- **Used by**: `Sinf_inertiaDeg_eq_one_of_primeOver`
- **Visibility**: public
- **Lines**: 3760–3800, proof ~41 lines
- **Notes**: Proof >30 lines. Inherits sorry.

---

### `theorem Sinf_inertiaDeg_eq_one_of_primeOver` (lines 3810–3829, proof ~20 lines)
- **Type**: `Ideal.inertiaDeg xIdeal P = 1` for any prime `P` over `xIdeal`.
- **What**: Reduction 1: pure composition of `Sinf_residue_surjective_of_primeOver` with `Sinf.inertiaDeg_eq_one_of_algebraMap_surjective`.
- **How**: Calls `Sinf_residue_surjective_of_primeOver` then `Curves.RamificationAtInfinity.Sinf.inertiaDeg_eq_one_of_algebraMap_surjective`.
- **Uses from project**: `Sinf_residue_surjective_of_primeOver`, `RamificationAtInfinity.Sinf.inertiaDeg_eq_one_of_algebraMap_surjective`
- **Used by**: `Sinf_kernelPoint_of_inertiaDeg_one_of_primeOver`
- **Visibility**: public
- **Lines**: 3810–3829, proof ~20 lines
- **Notes**: Inherits sorry.

---

### `theorem Sinf_primeOver_eq_kernelPrime_of_valuation_eq` (lines 3846–3883, proof ~38 lines)
- **Type**: Given `vP.valuation L = vT.valuation L`, conclude `P = bridge_Bi_kernelToPrime_v2 W hq data T`.
- **What**: R2e: equal valuations ⟹ equal primes, via `valuation_lt_one_iff_mem`.
- **How**: `Ideal.ext`; `← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem` for both sides; valuation hypothesis.
- **Uses from project**: `Sinf_kernelPrime_heightOne`
- **Used by**: `Sinf_kernelPoint_of_inertiaDeg_one_of_primeOver`
- **Visibility**: public
- **Lines**: 3846–3883, proof ~38 lines
- **Notes**: Proof >30 lines. Axiom-clean.

---

### `theorem Sinf_primeOver_ne_bot_of_algebraMap_X_mem` (lines 3890–3929, proof ~40 lines)
- **Type**: If `algebraMap X ∈ P` then `P ≠ ⊥`.
- **What**: R2 helper: a prime containing `algebraMap X` is nonzero. `xc ≠ 0` via injectivity and `f ≠ 0`.
- **How**: Scalar-tower collapse gives image of `xc` is `f⁻¹`; `x_gen_ne_zero`; injective `pullback`; `IsFractionRing.injective`; `inv_eq_zero`.
- **Uses from project**: `x_gen_ne_zero`, `RamificationAtInfinity.LinfAt.algebraMap_polynomial_apply`, `RamificationAtInfinity.polyToFieldOfInv_X`
- **Used by**: `Sinf_kernelPoint_place_eq_of_inertiaDeg_one_of_primeOver`, `Sinf_kernelPoint_of_inertiaDeg_one_of_primeOver`, `Sinf_primeOver_eq_kernelPrime_of_algebraMap_X_mem`
- **Visibility**: public
- **Lines**: 3890–3929, proof ~40 lines
- **Notes**: Proof >30 lines.

---

### `theorem Sinf_kernelPoint_place_eq_of_inertiaDeg_one_of_primeOver` (lines 3955–4002, proof ~48 lines)
- **Type**: Given `P.IsPrime`, `algebraMap X ∈ P`, `inertiaDeg (X) P = 1`, produces `∃ T` with `vP.valuation L = vT.valuation L`.
- **What**: R2 (isolated sharp core): carrier place ↔ K-rational kernel point, given K-rationality. Now a pure composition via `Sinf_primeOver_eq_kernelPrime_place` (deep pass 2026-05-28).
- **How**: `Sinf_liesOver_of_algebraMap_X_mem` gives LiesOver; `Sinf_primeOver_eq_kernelPrime_place` gives `P = P_T`; equal ideals → `HeightOneSpectrum.ext` → equal valuations.
- **Uses from project**: `Sinf_liesOver_of_algebraMap_X_mem`, `Sinf_primeOver_eq_kernelPrime_place`, `Sinf_primeOver_ne_bot_of_algebraMap_X_mem`, `Sinf_kernelPrime_heightOne`
- **Used by**: `Sinf_kernelPoint_of_inertiaDeg_one_of_primeOver`
- **Visibility**: public
- **Lines**: 3955–4002, proof ~48 lines
- **Notes**: Proof >30 lines. Inherits sorry.

---

### `theorem Sinf_kernelPoint_of_inertiaDeg_one_of_primeOver` (lines 4009–4036, proof ~28 lines)
- **Type**: Given `P.IsPrime`, `algebraMap X ∈ P`, `inertiaDeg (X) P = 1`, produces `∃ T` with `P = bridge_Bi_kernelToPrime_v2 W hq data T`.
- **What**: Reduction 2: pure composition of `Sinf_kernelPoint_place_eq_of_inertiaDeg_one_of_primeOver` (R2a) with `Sinf_primeOver_eq_kernelPrime_of_valuation_eq` (R2e).
- **How**: Calls R2a, then R2e.
- **Uses from project**: `Sinf_kernelPoint_place_eq_of_inertiaDeg_one_of_primeOver`, `Sinf_primeOver_eq_kernelPrime_of_valuation_eq`, `Sinf_primeOver_ne_bot_of_algebraMap_X_mem`
- **Used by**: `Sinf_primeOver_eq_kernelPrime_of_algebraMap_X_mem`
- **Visibility**: public
- **Lines**: 4009–4036, proof ~28 lines
- **Notes**: Inherits sorry.

---

### `theorem Sinf_primeOver_eq_kernelPrime_of_algebraMap_X_mem` (lines 4139–4172, proof ~34 lines)
- **Type**: For `P.IsPrime` and `algebraMap X ∈ P`, `∃ T, P = bridge_Bi_kernelToPrime_v2 W hq data T`.
- **What**: Sharpened core: pure composition of CORE (`Sinf_inertiaDeg_eq_one_of_primeOver`) and Reduction 2 (`Sinf_kernelPoint_of_inertiaDeg_one_of_primeOver`).
- **How**: `Sinf_liesOver_of_algebraMap_X_mem`; `Sinf_inertiaDeg_eq_one_of_primeOver`; `Sinf_kernelPoint_of_inertiaDeg_one_of_primeOver`.
- **Uses from project**: `Sinf_liesOver_of_algebraMap_X_mem`, `Sinf_inertiaDeg_eq_one_of_primeOver`, `Sinf_kernelPoint_of_inertiaDeg_one_of_primeOver`
- **Used by**: `Sinf_exists_kernelPoint_of_primeOver`
- **Visibility**: public
- **Lines**: 4139–4172, proof ~34 lines
- **Notes**: Proof >30 lines. Inherits sorry.

---

### `theorem Sinf_exists_kernelPoint_of_primeOver` (lines 4189–4222, proof ~34 lines)
- **Type**: For `P.IsPrime` and `P.LiesOver xIdeal`, `∃ T, ∀ a, a ∈ P ↔ 0 < ordAtPoint T.val (algebraMap a)`.
- **What**: Minimal place→point fact: produces a kernel point `T` whose membership predicate equals `P`. Composition of L1 (`Sinf_algebraMap_X_mem_of_liesOver`) and the sharpened core.
- **How**: L1 gives `algebraMap X ∈ P`; `Sinf_primeOver_eq_kernelPrime_of_algebraMap_X_mem` gives `P = P_T`; membership Iff is definitional in `P_T`.
- **Uses from project**: `Sinf_algebraMap_X_mem_of_liesOver`, `Sinf_primeOver_eq_kernelPrime_of_algebraMap_X_mem`
- **Used by**: `Sinf_primeOver_xIdeal_eq_kernelPrime`
- **Visibility**: public
- **Lines**: 4189–4222, proof ~34 lines
- **Notes**: Proof >30 lines. Inherits sorry.

---

### `theorem Sinf_primeOver_xIdeal_eq_kernelPrime` (lines 4232–4257, proof ~26 lines)
- **Type**: For `P.IsPrime` and `P.LiesOver xIdeal`, `∃ T, P = bridge_Bi_kernelToPrime_v2 W hq data T`.
- **What**: Forward/surjectivity direction of linchpin: every prime over `(X)` is a kernel-prime. Uses `Sinf_exists_kernelPoint_of_primeOver` + `Ideal.ext`.
- **How**: Gets membership Iff from `Sinf_exists_kernelPoint_of_primeOver`; `Ideal.ext` + `rfl`.
- **Uses from project**: `Sinf_exists_kernelPoint_of_primeOver`
- **Used by**: `bridge_Bii_surjective_v2`
- **Visibility**: public
- **Lines**: 4232–4257, proof ~26 lines
- **Notes**: Inherits sorry.

---

### `theorem bridge_Bii_surjective_v2` (lines 4259–4282, proof ~24 lines)
- **Type**: For `P ∈ primesOverFinset xIdeal data.carrier`, `∃ T, P = bridge_Bi_kernelToPrime_v2 W hq data T`.
- **What**: Surjectivity from primesOverFinset membership. Unpacks `mem_primesOverFinset_iff` then delegates to `Sinf_primeOver_xIdeal_eq_kernelPrime`.
- **How**: `mem_primesOverFinset_iff` gives `⟨IsPrime, LiesOver⟩`; apply `Sinf_primeOver_xIdeal_eq_kernelPrime`.
- **Uses from project**: `Sinf_primeOver_xIdeal_eq_kernelPrime`, `RamificationAtInfinity.xIdeal_ne_bot`
- **Used by**: `bridge_Bii_mem_primesOverFinset_v2`
- **Visibility**: public
- **Lines**: 4259–4282, proof ~24 lines
- **Notes**: Inherits sorry.

---

### `theorem bridge_Bii_mem_primesOverFinset_v2` (lines 4297–4317, proof ~21 lines)
- **Type**: `P ∈ primesOverFinset xIdeal data.carrier ↔ ∃ T, P = bridge_Bi_kernelToPrime_v2 W hq data T`
- **What**: Linchpin Iff: primes over `(X)` are exactly the kernel primes. Forward = `bridge_Bii_surjective_v2`; backward = `bridge_Bii_kernelToPrime_mem_primesOverFinset_v2`.
- **How**: `refine ⟨bridge_Bii_surjective_v2 ..., ?_⟩; rintro ⟨T, rfl⟩; exact ...`.
- **Uses from project**: `bridge_Bii_surjective_v2`, `bridge_Bii_kernelToPrime_mem_primesOverFinset_v2`
- **Used by**: unused in this file (probably consumed by `l6_computationA` externally)
- **Visibility**: public
- **Lines**: 4297–4317, proof ~21 lines
- **Notes**: Inherits sorry.

---

### `theorem Sinf_kappa_kernelPrime_algebraMap_surjective` (lines 4342–4387, proof ~46 lines)
- **Type**: `Function.Surjective (algebraMap (Polynomial K ⧸ xIdeal) (data.kappa (bridge_Bi_kernelToPrime_v2 W hq data T)))` (with `LiesOver` instance).
- **What**: Residue structure map is surjective at each kernel prime. Uses `Sinf_kappa_kernelPrime_residue_in_base` + quotient map.
- **How**: Lifts `w` to `a` via `Quotient.mk_surjective`; `Sinf_kappa_kernelPrime_residue_in_base` gives constant representative; `Ideal.quotientMap_mk`; `neg_mem`.
- **Uses from project**: `Sinf_kappa_kernelPrime_residue_in_base`
- **Used by**: `Sinf_finrank_kappa_kernelPrime_eq_one`
- **Visibility**: public
- **Lines**: 4342–4387, proof ~46 lines
- **Notes**: Proof >30 lines.

---

### `theorem Sinf_finrank_kappa_kernelPrime_eq_one` (lines 4418–4467, proof ~50 lines)
- **Type**: `Module.finrank (Polynomial K ⧸ xIdeal) (data.kappa (bridge_Bi_kernelToPrime_v2 ...)) = 1`
- **What**: B(iv) residue degree is 1 at kernel primes. Proved by `le_antisymm`: lower via `inertiaDeg_pos`, upper via `finrank_le_one` from `Sinf_kappa_kernelPrime_algebraMap_surjective`.
- **How**: `Ideal.inertiaDeg_algebraMap` gives lower bound; `finrank_le_one` with surjectivity gives upper bound.
- **Uses from project**: `bridge_Bi_isPrime_v2`, `bridge_Bi_liesOver_v2`, `Sinf_kappa_kernelPrime_algebraMap_surjective`, `RamificationAtInfinity.xIdeal_isMaximal`
- **Used by**: `bridge_Biv_inertia_eq_one_v2`
- **Visibility**: public
- **Lines**: 4418–4467, proof ~50 lines
- **Notes**: Proof >30 lines.

---

### `theorem bridge_Biv_inertia_eq_one_v2` (lines 4485–4502, proof ~18 lines)
- **Type**: `Ideal.inertiaDeg xIdeal (bridge_Bi_kernelToPrime_v2 W hq data T) = 1`
- **What**: B(iv): inertia degree at each kernel prime is 1. Via `Sinf.inertiaDeg_eq_finrank_kappa` + `bridge_Bi_liesOver_v2` + `Sinf_finrank_kappa_kernelPrime_eq_one`.
- **How**: `data.inertiaDeg_eq_finrank_kappa`; `Sinf_finrank_kappa_kernelPrime_eq_one`.
- **Uses from project**: `bridge_Bi_liesOver_v2`, `Sinf_finrank_kappa_kernelPrime_eq_one`
- **Used by**: `Sinf_sum_inertiaDeg_eq_pointCount_of_surjectivity_witness`, `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_finrank_witness`
- **Visibility**: public
- **Lines**: 4485–4502, proof ~18 lines
- **Notes**: None.

---

### `theorem Sinf_sum_inertiaDeg_eq_pointCount_of_surjectivity_witness` (lines 4525–4590, proof ~66 lines)
- **Type**: Given a surjectivity witness (`∀ P ∈ primesOverFinset, ∃ T, P = P_T`), `Σ f_P = pointCount`.
- **What**: Phase C surjective-kernel-to-prime composer: given surjectivity, image = primesOverFinset; each prime has `f = 1`; Σ 1 = #kernel = pointCount.
- **How**: `Finset.sum_image` via injectivity; `bridge_Biv_inertia_eq_one_v2` for each term; `kernel_eq_top_of_hom_eq_id_sub_frobenius` for cardinality.
- **Uses from project**: `bridge_Bii_kernelToPrime_mem_primesOverFinset_v2`, `Sinf_kernelToPrime_v2_injective`, `bridge_Biv_inertia_eq_one_v2`, `kernel_eq_top_of_hom_eq_id_sub_frobenius`, `RamificationAtInfinity.xIdeal_ne_bot`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 4525–4590, proof ~66 lines
- **Notes**: Proof >30 lines.

---

### `theorem Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_finrank_witness` (lines 4628–4794, proof ~167 lines)
- **Type**: Given `Σ e_P · f_P = 2 · pointCount` (the fundamental ramification identity), `Σ f_P = pointCount`.
- **What**: Phase B squeeze composer: the cardinality squeeze closes the sum-of-inertia identity from the LHS finrank witness. The largest proof in the file.
- **How**: Injectivity + backward inclusion give `image ⊆ primesOverFinset`; each kernel prime contributes `e·f = 2·1 = 2` via `bridge_Biii_ord_eq_neg_two_v2` + `bridge_Biv_inertia_eq_one_v2`; `Finset.sum_sdiff` + zero-complement argument forces `image = primesOverFinset`; sum rewrite + `bridge_Biv_inertia_eq_one_v2` + cardinality.
- **Uses from project**: `bridge_Bii_kernelToPrime_mem_primesOverFinset_v2`, `Sinf_kernelToPrime_v2_injective`, `bridge_Biii_ord_eq_neg_two_v2`, `bridge_Biv_inertia_eq_one_v2`, `kernel_eq_top_of_hom_eq_id_sub_frobenius`, `RamificationAtInfinity.xIdeal_ne_bot`, `RamificationAtInfinity.xIdeal_isMaximal`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 4628–4794, proof ~167 lines
- **Notes**: Proof >30 lines (second longest proof at ~167 lines). Axiom-clean (does NOT inherit sorry from `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount`; the sorry is only inherited by the chain going through `Sinf_primeOver_eq_kernelPrime_place`).

---

## Cross-reference Summary

**Declarations with sorries** (5): `genuine_dual_comp_pullback_x_gen_eq_mulByInt_x_decomp`, `genuine_dual_comp_pullback_y_gen_eq_mulByInt_y_decomp`, `degree_quadratic_exists_edge_s_char_divisible`, `degree_quadratic_exists_edge_r_char_divisible`, `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount`.

**`set_option maxHeartbeats 1600000`** occurs 5 times (lines 139, 230, 515, 545, 578), all without justifying comments.

**Declarations not referenced within this file** (dead-code candidates): `genuine_dual_comp_pullback_x_gen_eq_mulByInt_x_decomp`, `genuine_dual_comp_pullback_y_gen_eq_mulByInt_y_decomp`, `degree_quadratic_exists_edge_s_char_divisible`, `degree_quadratic_exists_edge_r_char_divisible`, `finrank_pullback_fieldRange_field_eq_two_of_witness`, `finrank_pullback_fieldRange_field_eq_two_unconditional`, `h_pole_orders_of_T5_T6_witnesses`, `support_card_eq_pointCount_of_two_torsion_ord_witness`, `l6_support_card_of_two_torsion_witness`, `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_witness`, `geomPoles_oneSubFrob_card_eq_pointCount`, `Sinf_sum_inertiaDeg_eq_pointCount_of_K3_K2K5_witnesses`, `bridge_Bii_mem_primesOverFinset_v2`, `Sinf_sum_inertiaDeg_eq_pointCount_of_surjectivity_witness`, `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_finrank_witness`.
