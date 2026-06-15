# Inventory: ./HasseWeil/EC/MulByIntUnramified.lean

**Total declarations:** 33 (32 theorems/lemmas + 1 noncomputable def)
**Lines:** 1159
**No sorry, no maxHeartbeats overrides**

Imports: `HasseWeil.EC.TranslationOrd`, `HasseWeil.WeilPairing.TorsionGeometric`,
`HasseWeil.EC.IsogenyOrdTransport`, `HasseWeil.EC.WronskianGeneral`, `HasseWeil.EC.DifferentialOrd`

---

### `theorem smulEval_facts_of_zsmul_eq_some`
- **Type**: `{x y x_Q y_Q : F} → W.toAffine.Nonsingular x y → W.toAffine.Nonsingular x_Q y_Q → (n : ℤ) → n ≠ 0 → n • (Affine.Point.some x y h_ns) = Affine.Point.some x_Q y_Q h_ns' → (W.ψ n).evalEval x y ≠ 0 ∧ x_Q = (W.φ n).evalEval x y / (W.ψ n).evalEval x y ^ 2 ∧ y_Q = (W.ω n).evalEval x y / (W.ψ n).evalEval x y ^ 3`
- **What**: If `n•(x,y) = (x_Q, y_Q)` is an affine point (nonsingular), extracts three facts: `ψ_n(x,y) ≠ 0`, and the affine coordinates are `φ_n/ψ_n²` and `ω_n/ψ_n³`. Converse-direction of `zsmul_eq_smulEval`.
- **How**: Routes via `fromAffine`/`toAffineAddEquiv` to pass through Jacobian homogeneous coordinates; reads off the three components of `smulEval` using `Quotient.exact` and `Jacobian.smul_fin3`; uses `zsmul_eq_smulEval` and `fromAffine_some`.
- **Hypotheses**: `W/F` an elliptic curve (IsElliptic omitted); `x,y` nonsingular; `x_Q, y_Q` nonsingular; `n ≠ 0`.
- **Uses from project**: `WeierstrassCurve.zsmul_eq_smulEval`, `WeierstrassCurve.Jacobian.Point.fromAffine_some`, `WeierstrassCurve.Jacobian.Point.toAffineAddEquiv`, `smulEval`
- **Used by**: `fibrePoly_isRoot_of_zsmul_eq_some`, `fibrePoly_derivative_eval_ne_zero`, `ord_P_ΨSq_ff_eq_zero`, `ord_P_ψ_ff_eq_zero`, `ord_P_mulByInt_y_sub_const_eq_one` (5 callers within file)
- **Visibility**: public
- **Lines**: 61–102, proof ~42 lines
- **Notes**: `omit [W.toAffine.IsElliptic]` — IsElliptic not needed. Proof >30 lines.

---

### `theorem evalEval_eq_of_mk_eq`
- **Type**: `{x y : F} → W.toAffine.Equation x y → {p q : (Polynomial F)[X]} → Affine.CoordinateRing.mk W.toAffine p = Affine.CoordinateRing.mk W.toAffine q → p.evalEval x y = q.evalEval x y`
- **What**: For a point `(x,y)` on the curve, `evalEval` factors through the coordinate ring: equal elements in `CoordinateRing` have equal bivariate evaluations.
- **How**: Uses `AdjoinRoot.evalEval_mk` after applying the adjoin-root evaluation at `polynomial(x,y) = 0`.
- **Hypotheses**: `(x,y)` on the Weierstrass curve (`Equation x y`); no IsElliptic or DecidableEq needed.
- **Uses from project**: `AdjoinRoot.evalEval_mk`
- **Used by**: `ΨSq_eval_eq_psi_sq`, `Φ_eval_eq_phi`, `preΨ_two_mul_eval_ne_zero`
- **Visibility**: public
- **Lines**: 107–113, proof ~7 lines

---

### `theorem ΨSq_eval_eq_psi_sq`
- **Type**: `{x y : F} → W.toAffine.Equation x y → (n : ℤ) → (W.ΨSq n).eval x = ((W.ψ n).evalEval x y) ^ 2`
- **What**: The univariate division polynomial `ΨSq_n` evaluates at `x` to `ψ_n(x,y)²` for any point `(x,y)` on the curve.
- **How**: Uses `evalEval_eq_of_mk_eq` with `CoordinateRing.mk_Ψ_sq` and `mk_ψ`, plus `evalEval_pow` and `evalEval_C`.
- **Hypotheses**: `(x,y)` on the curve. No IsElliptic or DecidableEq.
- **Uses from project**: `evalEval_eq_of_mk_eq`, `Affine.CoordinateRing.mk_Ψ_sq`, `Affine.CoordinateRing.mk_ψ`
- **Used by**: `fibrePoly_isRoot_of_zsmul_eq_some`, `fibrePoly_derivative_eval_ne_zero`, `ord_P_ΨSq_ff_eq_zero`
- **Visibility**: public
- **Lines**: 117–126, proof ~10 lines

---

### `theorem Φ_eval_eq_phi`
- **Type**: `{x y : F} → W.toAffine.Equation x y → (n : ℤ) → (W.Φ n).eval x = (W.φ n).evalEval x y`
- **What**: The univariate division polynomial `Φ_n` evaluates at `x` to `φ_n(x,y)` for any point `(x,y)` on the curve.
- **How**: Direct application of `evalEval_eq_of_mk_eq` with `CoordinateRing.mk_φ` and `evalEval_C`.
- **Hypotheses**: `(x,y)` on the curve.
- **Uses from project**: `evalEval_eq_of_mk_eq`, `Affine.CoordinateRing.mk_φ`
- **Used by**: `fibrePoly_isRoot_of_zsmul_eq_some`, `fibrePoly_derivative_eval_ne_zero`
- **Visibility**: public
- **Lines**: 130–134, proof ~5 lines

---

### `theorem algebraMap_poly_eq_aeval_x_gen`
- **Type**: `(p : Polynomial F) → algebraMap (Polynomial F) KE p = Polynomial.aeval (x_gen W) p`
- **What**: The algebra map `F[X] → K(E)` agrees with evaluation at `x_gen`: both send `X` to `x_gen W` and fix `F`.
- **How**: Proves `algebraMap X = x_gen` via the scalar tower, then uses `Polynomial.ringHom_ext` to show both ring homomorphisms agree on `C a` and `X`.
- **Hypotheses**: No extra hypotheses.
- **Uses from project**: `x_gen`
- **Used by**: `ord_P_algebraMap_poly_eq_rootMultiplicity`
- **Visibility**: public
- **Lines**: 141–151, proof ~11 lines

---

### `theorem evalAt_algebraMap_poly`
- **Type**: `(P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) → (p : Polynomial F) → (⟨W⟩).evalAt P (algebraMap (Polynomial F) R p) = p.eval P.x`
- **What**: The evaluation of `algebraMap p` (in the coordinate ring) at a smooth point `P` equals the univariate polynomial evaluation `p(P.x)`.
- **How**: Rewrites `algebraMap` as `AdjoinRoot.of`, then uses `SmoothPlaneCurve.evalAt_mk` and `evalEval_C`.
- **Hypotheses**: No extra.
- **Uses from project**: `SmoothPlaneCurve.evalAt_mk`
- **Used by**: `ord_P_algebraMap_poly_eq_zero_of_eval_ne`, `one_le_ord_P_algebraMap_poly_of_root`
- **Visibility**: public
- **Lines**: 155–165, proof ~11 lines

---

### `theorem ord_P_x_gen_sub_self_eq_one`
- **Type**: `(P : SmoothPoint) → P.y ≠ W.toAffine.negY P.x P.y → (⟨W⟩).ord_P P (x_gen W - algebraMap F KE P.x) = 1`
- **What**: At a non-2-torsion smooth point `P`, the order of `x_gen − P.x` equals `1`: it is a uniformizer at `P`.
- **How**: Bridges to `ord_P_x_gen_sub_const_eq_one_of_non_2_tor` (from `TranslationOrd`) by working with the negation `(P.x, negY P.x P.y)` and using `negSmoothPoint` to recover `P`; exploits the involution `negY ∘ negY = id`.
- **Hypotheses**: `P` non-2-torsion (`P.y ≠ negY P.x P.y`); `W` elliptic, `DecidableEq F`.
- **Uses from project**: `ord_P_x_gen_sub_const_eq_one_of_non_2_tor` (from `TranslationOrd`), `negSmoothPoint`
- **Used by**: `ord_P_algebraMap_poly_eq_rootMultiplicity`
- **Visibility**: public
- **Lines**: 174–194, proof ~21 lines
- **Notes**: `set_option linter.unusedDecidableInType false` (no justifying comment, suppresses lint about `DecidableEq` in signature).

---

### `theorem ord_P_algebraMap_poly_eq_zero_of_eval_ne`
- **Type**: `(P : SmoothPoint) → {q : Polynomial F} → q ≠ 0 → q.eval P.x ≠ 0 → (⟨W⟩).ord_P P (algebraMap (Polynomial F) KE q) = 0`
- **What**: If a nonzero polynomial `q` does not vanish at `P.x`, then the order of its image in `K(E)` at `P` is `0` (it is a unit at `P`).
- **How**: Lifts `q` to `R`, uses `evalAt_algebraMap_poly` to show it is not in the maximal ideal at `P`, then applies `ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt` by contradiction.
- **Hypotheses**: `q ≠ 0` and `q.eval P.x ≠ 0`. No IsElliptic.
- **Uses from project**: `evalAt_algebraMap_poly`, `SmoothPlaneCurve.ker_evalAt`, `SmoothPlaneCurve.ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt`
- **Used by**: `ord_P_algebraMap_poly_eq_rootMultiplicity`, `ord_P_ΨSq_ff_eq_zero`, `ord_P_ψ_ff_two_mul_eq_one` (×2), `ord_P_ψ_ff_eq_zero`, `ord_P_mulByInt_y_sub_const_eq_one` — 6+ uses
- **Visibility**: public
- **Lines**: 199–216, proof ~18 lines

---

### `theorem ord_P_algebraMap_poly_eq_rootMultiplicity`
- **Type**: `(P : SmoothPoint) → P.y ≠ W.toAffine.negY P.x P.y → {p : Polynomial F} → p ≠ 0 → (⟨W⟩).ord_P P (algebraMap (Polynomial F) KE p) = (p.rootMultiplicity P.x : ℤ)`
- **What**: **Step 2 root-multiplicity formula:** for a non-2-torsion smooth point, the order of `algebraMap p` in `K(E)` at `P` equals the multiplicity of `P.x` as a root of `p`.
- **How**: Factors `p = (X − P.x)^m * q` via `pow_mul_divByMonic_rootMultiplicity_eq`; `algebraMap (X−P.x) = x_gen − P.x` of order 1 by `ord_P_x_gen_sub_self_eq_one`; cofactor `q` has order 0 by `ord_P_algebraMap_poly_eq_zero_of_eval_ne`.
- **Hypotheses**: `P` non-2-torsion, `p ≠ 0`.
- **Uses from project**: `algebraMap_poly_eq_aeval_x_gen`, `ord_P_x_gen_sub_self_eq_one`, `ord_P_algebraMap_poly_eq_zero_of_eval_ne`
- **Used by**: `ord_P_mulByInt_x_sub_const_eq_one`, `ord_P_ψ_ff_two_mul_eq_one`
- **Visibility**: public
- **Lines**: 224–247, proof ~24 lines
- **Notes**: `set_option linter.unusedDecidableInType false` (no comment).

---

### `noncomputable def fibrePoly`
- **Type**: `(ℓ : ℤ) → (x_Q : F) → Polynomial F` defined as `W.Φ ℓ - Polynomial.C x_Q * W.ΨSq ℓ`
- **What**: The "fibre polynomial" `g_ℓ(x_Q) = Φ_ℓ − x_Q · ΨSq_ℓ ∈ F[X]`, whose roots are the x-coordinates of points `P'` with `[ℓ]·P' = ±Q` where `Q = (x_Q, y_Q)`.
- **How**: Direct definition.
- **Hypotheses**: None.
- **Uses from project**: `W.Φ`, `W.ΨSq`
- **Used by**: `fibrePoly_monic`, `fibrePoly_eval`, `fibrePoly_isRoot_of_zsmul_eq_some`, `fibrePoly_derivative_eval_ne_zero`, `fibrePoly_rootMultiplicity_eq_one`, `mulByInt_x_sub_const_eq_div`, `ord_P_mulByInt_x_sub_const_eq_one`, `ord_P_mulByInt_y_sub_const_eq_one` (many uses)
- **Visibility**: public
- **Lines**: 253–254

---

### `theorem fibrePoly_monic`
- **Type**: `{ℓ : ℤ} → ℓ ≠ 0 → (x_Q : F) → (fibrePoly W ℓ x_Q).Monic`
- **What**: `g_ℓ(x_Q)` is monic: `Φ_ℓ` is monic of degree `ℓ²` and `C x_Q · ΨSq_ℓ` has smaller degree.
- **How**: Uses `W.leadingCoeff_Φ`, `W.natDegree_Φ`, `W.natDegree_ΨSq_le` and `Polynomial.Monic.sub_of_left`.
- **Hypotheses**: `ℓ ≠ 0`.
- **Uses from project**: `W.leadingCoeff_Φ`, `W.natDegree_Φ`, `W.natDegree_ΨSq_le`, `fibrePoly`
- **Used by**: `fibrePoly_rootMultiplicity_eq_one`, `ord_P_mulByInt_x_sub_const_eq_one`, `ord_P_mulByInt_y_sub_const_eq_one`
- **Visibility**: public
- **Lines**: 259–269, proof ~11 lines

---

### `theorem fibrePoly_eval`
- **Type**: `(ℓ : ℤ) → (x_Q x : F) → (fibrePoly W ℓ x_Q).eval x = (W.Φ ℓ).eval x - x_Q * (W.ΨSq ℓ).eval x`
- **What**: Evaluates the fibre polynomial: `g_ℓ(x_Q)(x) = Φ_ℓ(x) − x_Q · ΨSq_ℓ(x)`.
- **How**: Direct `rw` using the definition and `Polynomial.eval_sub/mul/C`.
- **Hypotheses**: None.
- **Uses from project**: `fibrePoly`
- **Used by**: `fibrePoly_isRoot_of_zsmul_eq_some`
- **Visibility**: public
- **Lines**: 273–275, proof 3 lines

---

### `theorem fibrePoly_isRoot_of_zsmul_eq_some`
- **Type**: `{x y x_Q y_Q : F} → Nonsingular x y → Nonsingular x_Q y_Q → {ℓ : ℤ} → ℓ ≠ 0 → ℓ • (some x y h_ns) = some x_Q y_Q h_ns' → (fibrePoly W ℓ x_Q).eval x = 0`
- **What**: `P.x` is a root of the fibre polynomial `g_ℓ(x_Q)` when `[ℓ]·P = Q = (x_Q, y_Q)`.
- **How**: Extracts `φ_ℓ(P)/ψ_ℓ(P)² = x_Q` from `smulEval_facts_of_zsmul_eq_some`, then uses `Φ_eval_eq_phi` and `ΨSq_eval_eq_psi_sq` plus `fibrePoly_eval` to verify `Φ_ℓ(x) − x_Q · ΨSq_ℓ(x) = 0`.
- **Hypotheses**: `W/F` with omitted IsElliptic; `ℓ ≠ 0`; `[ℓ]·(x,y) = (x_Q, y_Q)`.
- **Uses from project**: `smulEval_facts_of_zsmul_eq_some`, `ΨSq_eval_eq_psi_sq`, `Φ_eval_eq_phi`, `fibrePoly_eval`
- **Used by**: `fibrePoly_rootMultiplicity_eq_one`, `ord_P_mulByInt_y_sub_const_eq_one`
- **Visibility**: public
- **Lines**: 280–291, proof ~12 lines

---

### `theorem psi_evalEval_ne_zero_of_zsmul_ne_zero`
- **Type**: `{x y : F} → Nonsingular x y → (m : ℤ) → m • (some x y h_ns) ≠ 0 → (W.ψ m).evalEval x y ≠ 0`
- **What**: If `[m]·(x,y) ≠ O`, then the division polynomial `ψ_m(x,y) ≠ 0`. Base-field-point analogue of `ψ_m_evalEval_mulByInt_ne_zero`.
- **How**: By contradiction: if `ψ_m(x,y) = 0`, the Jacobian `Z`-coordinate of `m • fromAffine(x,y)` is `0`, which forces `toAffineLift = 0 = O` via `Jacobian.Point.toAffine_of_Z_eq_zero`; but `toAffineLift(m • fromAffine P) = m • P` by functoriality.
- **Hypotheses**: `W/F` with omitted IsElliptic; `m • (some x y h_ns) ≠ 0`.
- **Uses from project**: `WeierstrassCurve.zsmul_eq_smulEval`, `Jacobian.Point.toAffine_of_Z_eq_zero`, `Jacobian.Point.toAffineAddEquiv`
- **Used by**: `preΨ_two_mul_eval_ne_zero`
- **Visibility**: public
- **Lines**: 297–327, proof ~31 lines
- **Notes**: Proof >30 lines.

---

### `theorem preΨ_two_mul_eval_ne_zero`
- **Type**: `{x y x_Q y_Q : F} → Nonsingular x y → Nonsingular x_Q y_Q → {ℓ : ℤ} → y_Q ≠ W.toAffine.negY x_Q y_Q → ℓ • (some x y h_ns) = some x_Q y_Q h_ns' → (W.preΨ (2 * ℓ)).eval x ≠ 0`
- **What**: When `Q = [ℓ]·P` is non-2-torsion, `preΨ_{2ℓ}(P.x) ≠ 0`. Uses `2ℓ•P = 2•Q ≠ O ⟹ ψ_{2ℓ}(P) ≠ 0` and the factorization `ψ_{2ℓ} = preΨ_{2ℓ}·ψ₂` on the curve.
- **How**: Shows `2Q ≠ O` from non-2-torsion of `Q`, then `2ℓ•P ≠ O`, applies `psi_evalEval_ne_zero_of_zsmul_ne_zero`; uses `evalEval_eq_of_mk_eq` and the even-index `Ψ` factorization `W.Ψ (2*ℓ) = C(preΨ(2ℓ)) * ψ₂`.
- **Hypotheses**: `W/F` with omitted IsElliptic; `Q` non-2-torsion; `[ℓ]·P = Q`.
- **Uses from project**: `psi_evalEval_ne_zero_of_zsmul_ne_zero`, `evalEval_eq_of_mk_eq`, `Affine.CoordinateRing.mk_ψ`, `W.Ψ`
- **Used by**: `fibrePoly_derivative_eval_ne_zero`
- **Visibility**: public
- **Lines**: 333–360, proof ~28 lines

---

### `theorem fibrePoly_derivative_eval_ne_zero`
- **Type**: `{x y x_Q y_Q : F} → Nonsingular x y → Nonsingular x_Q y_Q → {ℓ : ℤ} → ℓ ≠ 0 → (ℓ : F) ≠ 0 → y_Q ≠ negY x_Q y_Q → ℓ • (some x y h_ns) = some x_Q y_Q → (fibrePoly W ℓ x_Q).derivative.eval x ≠ 0`
- **What**: `P.x` is a **simple** root of `g_ℓ(x_Q)`: `g'_ℓ(x_Q)(P.x) ≠ 0`. This is the separability/unramifiedness content of [ℓ] (Silverman III.4.10c).
- **How**: From the Wronskian `wronskian_Φ_ΨSq_general` (EC/WronskianGeneral): `ΨSq_ℓ · Φ_ℓ' − Φ_ℓ · ΨSq_ℓ' = ℓ · preΨ_{2ℓ}`; uses `ΨSq_ℓ(P.x)·g'(P.x) = ℓ · preΨ_{2ℓ}(P.x) ≠ 0` from `preΨ_two_mul_eval_ne_zero`. Since `ΨSq_ℓ(P.x) ≠ 0`, `g'(P.x) ≠ 0`.
- **Hypotheses**: `[ℓ]·(x,y) = (x_Q,y_Q)` affine; `ℓ ≠ 0`; `(ℓ:F) ≠ 0` (separability); `Q` non-2-torsion.
- **Uses from project**: `smulEval_facts_of_zsmul_eq_some`, `ΨSq_eval_eq_psi_sq`, `Φ_eval_eq_phi`, `HasseWeil.EC.wronskian_Φ_ΨSq_general`, `preΨ_two_mul_eval_ne_zero`, `fibrePoly`
- **Used by**: `fibrePoly_rootMultiplicity_eq_one`
- **Visibility**: public
- **Lines**: 371–402, proof ~32 lines
- **Notes**: Proof >30 lines. The key lemma `wronskian_Φ_ΨSq_general` (EC/WronskianGeneral) is axiom-clean.

---

### `theorem fibrePoly_rootMultiplicity_eq_one`
- **Type**: `{x y x_Q y_Q : F} → Nonsingular x y → Nonsingular x_Q y_Q → {ℓ : ℤ} → ℓ ≠ 0 → (ℓ : F) ≠ 0 → y_Q ≠ negY x_Q y_Q → ℓ • (some x y h_ns) = some x_Q y_Q → (fibrePoly W ℓ x_Q).rootMultiplicity x = 1`
- **What**: `P.x` is a root of multiplicity exactly 1 of `g_ℓ(x_Q)`. Lower bound from `fibrePoly_isRoot`, upper bound from `fibrePoly_derivative_eval_ne_zero` (simple root ⟹ `rootMultiplicity ≤ 1`) via `isRoot_iterate_derivative_of_lt_rootMultiplicity`.
- **How**: Uses `Polynomial.rootMultiplicity_pos`, `fibrePoly_isRoot_of_zsmul_eq_some`, and `Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity` for the upper bound; `fibrePoly_derivative_eval_ne_zero` provides the contradiction.
- **Hypotheses**: Same as `fibrePoly_derivative_eval_ne_zero`.
- **Uses from project**: `fibrePoly_monic`, `fibrePoly_isRoot_of_zsmul_eq_some`, `fibrePoly_derivative_eval_ne_zero`
- **Used by**: `ord_P_mulByInt_x_sub_const_eq_one`
- **Visibility**: public
- **Lines**: 406–426, proof ~21 lines

---

### `theorem Φ_ff_eq_algebraMap`
- **Type**: `(ℓ : ℤ) → Φ_ff W ℓ = algebraMap (Polynomial F) KE (W.Φ ℓ)`
- **What**: `Φ_ff W ℓ` equals the scalar-tower algebra map of `W.Φ ℓ` from `F[X]` to `K(E)`.
- **How**: Symmetry of `IsScalarTower.algebraMap_apply`.
- **Uses from project**: `Φ_ff`
- **Used by**: `mulByInt_x_sub_const_eq_div`, `ord_P_ψ_ff_two_mul_eq_one` (×2), `ord_P_mulByInt_y_sub_const_eq_one`
- **Visibility**: public
- **Lines**: 432–434, proof 2 lines

---

### `theorem ΨSq_ff_eq_algebraMap`
- **Type**: `(ℓ : ℤ) → ΨSq_ff W ℓ = algebraMap (Polynomial F) KE (W.ΨSq ℓ)`
- **What**: `ΨSq_ff W ℓ` equals the algebra map of `W.ΨSq ℓ`.
- **How**: Symmetry of `IsScalarTower.algebraMap_apply`.
- **Uses from project**: `ΨSq_ff`
- **Used by**: `ord_P_ΨSq_ff_eq_zero`, `mulByInt_x_sub_const_eq_div`, `ord_P_ψ_ff_two_mul_eq_one`, `ord_P_mulByInt_y_sub_const_eq_one`
- **Visibility**: public
- **Lines**: 438–440, proof 2 lines

---

### `theorem ord_P_ΨSq_ff_eq_zero`
- **Type**: `{x y x_Q y_Q : F} → Nonsingular x y → Nonsingular x_Q y_Q → {ℓ : ℤ} → ℓ ≠ 0 → ℓ • (some x y h_ns) = some x_Q y_Q h_ns' → (P : SmoothPoint) → P.x = x → (⟨W⟩).ord_P P (ΨSq_ff W ℓ) = 0`
- **What**: When `[ℓ]·(x,y)` is affine, `ΨSq_ff ℓ` has order 0 at `P` (it is a unit): `ψ_ℓ(P) ≠ 0` forces `ΨSq_ℓ(P.x) ≠ 0`.
- **How**: Extracts `ψ_ℓ(P) ≠ 0` via `smulEval_facts_of_zsmul_eq_some`, uses `ΨSq_eval_eq_psi_sq` and `ΨSq_ff_eq_algebraMap`, then `ord_P_algebraMap_poly_eq_zero_of_eval_ne` with `ΨSq_poly_ne_zero`.
- **Hypotheses**: `[ℓ]·(x,y)` affine; `P.x = x`.
- **Uses from project**: `smulEval_facts_of_zsmul_eq_some`, `ΨSq_eval_eq_psi_sq`, `ΨSq_ff_eq_algebraMap`, `ΨSq_poly_ne_zero`, `ord_P_algebraMap_poly_eq_zero_of_eval_ne`
- **Used by**: `ord_P_mulByInt_x_sub_const_eq_one`, `ord_P_mulByInt_y_sub_const_eq_one`
- **Visibility**: public
- **Lines**: 444–454, proof ~11 lines

---

### `theorem mulByInt_x_sub_const_eq_div`
- **Type**: `{ℓ : ℤ} → ℓ ≠ 0 → (x_Q : F) → mulByInt_x W ℓ - algebraMap F KE x_Q = algebraMap (Polynomial F) KE (fibrePoly W ℓ x_Q) / ΨSq_ff W ℓ`
- **What**: Decomposes `mulByInt_x ℓ − x_Q = g_ℓ(x_Q)(x_gen)/ΨSq_ℓ(x_gen)` as numerator over denominator.
- **How**: Rewrites `mulByInt_x` as `Φ_ff/ΨSq_ff`, uses `Φ_ff_eq_algebraMap`, `ΨSq_ff_eq_algebraMap`, `fibrePoly` definition, and algebra.
- **Hypotheses**: `ℓ ≠ 0`.
- **Uses from project**: `mulByInt_x`, `Φ_ff_eq_algebraMap`, `ΨSq_ff_eq_algebraMap`, `ΨSq_ff_ne_zero`, `fibrePoly`
- **Used by**: `ord_P_mulByInt_x_sub_const_eq_one`, `ord_P_mulByInt_y_sub_const_eq_one`
- **Visibility**: public
- **Lines**: 458–466, proof ~9 lines
- **Notes**: `set_option linter.unusedDecidableInType false`.

---

### `theorem not_2_tor_of_image_not_2_tor`
- **Type**: `{x_Q y_Q : F} → Nonsingular x_Q y_Q → {ℓ : ℤ} → (P : SmoothPoint) → y_Q ≠ negY x_Q y_Q → ℓ • P.toAffinePoint = some x_Q y_Q h_ns' → P.y ≠ negY P.x P.y`
- **What**: If `Q = [ℓ]·P` is non-2-torsion, then `P` itself is non-2-torsion: `2•P = 0 ⟹ 2•Q = 0`, contradiction.
- **How**: Assumes `P` is 2-torsion, shows `2•Q = ℓ•(2•P) = 0` via `smul_comm`; derives contradiction from `Q` non-2-torsion using `neg_some` and `some.injEq`.
- **Hypotheses**: `W/F` with omitted IsElliptic; `Q` non-2-torsion.
- **Uses from project**: (none beyond `SmoothPlaneCurve.SmoothPoint.toAffinePoint_def`)
- **Used by**: `ord_P_mulByInt_x_sub_const_eq_one`
- **Visibility**: public
- **Lines**: 470–489, proof ~20 lines

---

### `theorem ord_P_mulByInt_x_sub_const_eq_one`
- **Type**: `(ℓ : ℤ) → ℓ ≠ 0 → (ℓ : F) ≠ 0 → (P : SmoothPoint) → {x_Q y_Q : F} → Nonsingular x_Q y_Q → y_Q ≠ negY x_Q y_Q → [ℓ]·P.toAffinePoint = some x_Q y_Q h_ns' → (⟨W⟩).ord_P P (mulByInt_x W ℓ - algebraMap F KE x_Q) = 1`
- **What**: **Main lemma (non-2-torsion `x`-case, `e = 1`):** the pullback `[ℓ]^*(x_gen − x_Q)` of the uniformizer at `Q` is a uniformizer at `P`, order `= 1`.
- **How**: Assembles the whole pipeline: `mulByInt_x_sub_const_eq_div` decomposes into `g/ΨSq`; `ord_P (g/ΨSq) = ord_P(g) − ord_P(ΨSq_ff)`; `ord_P(ΨSq_ff) = 0` (`ord_P_ΨSq_ff_eq_zero`); `ord_P(g) = rootMultiplicity P.x g = 1` (`ord_P_algebraMap_poly_eq_rootMultiplicity` + `fibrePoly_rootMultiplicity_eq_one`); also needs `not_2_tor_of_image_not_2_tor` for the non-2-torsion prerequisite of the root-multiplicity formula.
- **Hypotheses**: `[ℓ]` separable (`(ℓ:F) ≠ 0`); `Q` affine non-2-torsion.
- **Uses from project**: `mulByInt_apply`, `not_2_tor_of_image_not_2_tor`, `ΨSq_ff_ne_zero`, `fibrePoly_monic`, `mulByInt_x_sub_const_eq_div`, `ord_P_ΨSq_ff_eq_zero`, `ord_P_algebraMap_poly_eq_rootMultiplicity`, `fibrePoly_rootMultiplicity_eq_one`
- **Used by**: unused in file (exported API)
- **Visibility**: public
- **Lines**: 502–529, proof ~28 lines

---

### `theorem one_le_ord_P_algebraMap_of_evalAt_zero`
- **Type**: `(P : SmoothPoint) → {u : R} → u ≠ 0 → (⟨W⟩).evalAt P u = 0 → 1 ≤ (⟨W⟩).ord_P P (algebraMap R KE u)`
- **What**: If a nonzero element `u` of the coordinate ring vanishes at `P`, then its order in `K(E)` at `P` is `≥ 1` (it is in the maximal ideal).
- **How**: Via `ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt` and `ker_evalAt`; handles the `WithTop ℤ` arithmetic case-splitting on finiteness and sign.
- **Hypotheses**: `u ≠ 0`, `evalAt P u = 0`. No IsElliptic.
- **Uses from project**: `SmoothPlaneCurve.ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt`, `SmoothPlaneCurve.ker_evalAt`, `SmoothPlaneCurve.pointValuation_algebraMap_le_one`, `SmoothPlaneCurve.ord_P_eq_top_iff`
- **Used by**: `one_le_ord_P_algebraMap_poly_of_root`, `ord_P_mulByInt_y_sub_const_eq_one`
- **Visibility**: public
- **Lines**: 537–568, proof ~32 lines
- **Notes**: Proof >30 lines. Involved `WithTop ℤ` arithmetic unpacking with multiple case splits.

---

### `theorem one_le_ord_P_algebraMap_poly_of_root`
- **Type**: `(P : SmoothPoint) → {p : Polynomial F} → p ≠ 0 → p.eval P.x = 0 → 1 ≤ (⟨W⟩).ord_P P (algebraMap (Polynomial F) KE p)`
- **What**: If polynomial `p` vanishes at `P.x`, the order of `algebraMap p` in `K(E)` at `P` is `≥ 1`. Univariate specialization of `one_le_ord_P_algebraMap_of_evalAt_zero`.
- **How**: Lifts `p` to `R`, checks `evalAt P = p.eval P.x = 0` via `evalAt_algebraMap_poly`, then delegates to `one_le_ord_P_algebraMap_of_evalAt_zero`.
- **Hypotheses**: `p ≠ 0`, `p.eval P.x = 0`. No IsElliptic.
- **Uses from project**: `evalAt_algebraMap_poly`, `one_le_ord_P_algebraMap_of_evalAt_zero`
- **Used by**: `ord_P_ψ_ff_two_mul_eq_one`, `ord_P_mulByInt_y_sub_const_eq_one`
- **Visibility**: public
- **Lines**: 573–585, proof ~13 lines

---

### `private theorem mulByInt_neg_mem_kernel_of_torsion`
- **Type**: `(n : ℤ) → (P : SmoothPoint) → [n]·P.toAffinePoint = 0 → -P.toAffinePoint ∈ (mulByInt W.toAffine n).kernel`
- **What**: If `[n]·P = O`, then `-P` is in the kernel of `[n]`: `[n](-P) = -[n]P = 0`.
- **How**: Applies `HasseWeil.Isogeny.mem_kernel_iff` and `map_neg`.
- **Hypotheses**: `[n]·P = O`.
- **Uses from project**: `HasseWeil.Isogeny.mem_kernel_iff`
- **Used by**: `ord_P_mulByInt_x_eq_neg_two_of_torsion'`
- **Visibility**: private
- **Lines**: 588–592, proof ~5 lines

---

### `theorem ord_P_mulByInt_x_eq_neg_two_of_torsion'`
- **Type**: `(n : ℤ) → n ≠ 0 → (n : F) ≠ 0 → (P : SmoothPoint) → [n]·P.toAffinePoint = 0 → (⟨W⟩).ord_P P (mulByInt_x W n) = -2`
- **What**: At an `n`-torsion point `P` with `[n]` separable, `mulByInt_x n` has a pole of order `2` at `P`. (Re-derivation of `ord_P_mulByInt_x_eq_neg_two_of_torsion` from `MulByIntSamePlace`.)
- **How**: Takes `k = -P` in the kernel of `[n]`, uses `isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint` and `hxy_mulByInt` (E[n]-translation invariance of `mulByInt_x`) plus `ord_P_eq_ordAtInfty_of_invariant_and_compatible` to transport `ordAtInfty_mulByInt_x W n = -2` to `P`.
- **Hypotheses**: `n ≠ 0`, `(n:F) ≠ 0`, `[n]·P = O`.
- **Uses from project**: `mulByInt_neg_mem_kernel_of_torsion`, `isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint` (TranslationOrd), `WeilPairing.TorsionGeometric.hxy_mulByInt`, `ord_P_eq_ordAtInfty_of_invariant_and_compatible` (TranslationOrd), `ordAtInfty_mulByInt_x`
- **Used by**: `ord_P_ψ_ff_two_mul_eq_one`
- **Visibility**: public
- **Lines**: 600–611, proof ~12 lines

---

### `theorem Φ_two_mul_eval_ne_zero_of_ΨSq_zero`
- **Type**: `{ℓ : ℤ} → ℓ ≠ 0 → (P : SmoothPoint) → (W.ΨSq (2*ℓ)).eval P.x = 0 → (W.Φ (2*ℓ)).eval P.x ≠ 0`
- **What**: If `ΨSq_{2ℓ}(P.x) = 0`, then `Φ_{2ℓ}(P.x) ≠ 0`: coprimality of `Φ_{2ℓ}` and `ΨSq_{2ℓ}` rules out a common root.
- **How**: Uses `isCoprime_Φ_ΨSq`, extracts a Bézout identity `u·Φ + v·ΨSq = 1`, evaluates at `P.x` with both zero gives `1 = 0`.
- **Hypotheses**: `ℓ ≠ 0`, `ΨSq_{2ℓ}(P.x) = 0`. `W` elliptic (discriminant `Δ' ≠ 0`).
- **Uses from project**: `isCoprime_Φ_ΨSq`
- **Used by**: `ord_P_ψ_ff_two_mul_eq_one`
- **Visibility**: public
- **Lines**: 616–628, proof ~13 lines

---

### `theorem ord_P_ψ_ff_two_mul_eq_one`
- **Type**: `{ℓ : ℤ} → ℓ ≠ 0 → (2*ℓ : F) ≠ 0 → (P : SmoothPoint) → [2ℓ]·P.toAffinePoint = 0 → (⟨W⟩).ord_P P (ψ_ff W (2*ℓ)) = 1`
- **What**: At a `[2ℓ]`-torsion point `P` with `(2ℓ:F) ≠ 0`, the order of `ψ_{2ℓ}` in `K(E)` is exactly `1`.
- **How**: (1) `ord_P(mulByInt_x(2ℓ)) = -2` from `ord_P_mulByInt_x_eq_neg_two_of_torsion'`. (2) `ord_P(Φ_ff(2ℓ)) ≥ 0`. (3) From `mulByInt_x = Φ_ff/ΨSq_ff`, pole forces `ord_P(ΨSq_ff(2ℓ)) > 0`, hence `ΨSq_{2ℓ}(P.x) = 0`. (4) Coprimality `Φ_two_mul_eval_ne_zero_of_ΨSq_zero` gives `ord_P(Φ_ff) = 0`. (5) Recomputing gives `ord_P(ΨSq_ff) = 2`. (6) `ΨSq_ff = ψ_ff²` halves to get `ord_P(ψ_ff) = 1`. Uses integer arithmetic in `WithTop ℤ`.
- **Hypotheses**: `ℓ ≠ 0`, `(2ℓ:F) ≠ 0`, `[2ℓ]·P = O`.
- **Uses from project**: `ord_P_mulByInt_x_eq_neg_two_of_torsion'`, `ΨSq_ff_ne_zero`, `Φ_ff_eq_algebraMap`, `one_le_ord_P_algebraMap_poly_of_root`, `ord_P_algebraMap_poly_eq_zero_of_eval_ne`, `ΨSq_ff_eq_algebraMap`, `ΨSq_poly_ne_zero`, `Φ_two_mul_eval_ne_zero_of_ΨSq_zero`, `ψ_ff_ne_zero`, `ψ_ff_sq_eq_ΨSq_ff`, `Φ_ff_ne_zero`
- **Used by**: `ord_P_mulByInt_y_sub_const_eq_one`
- **Visibility**: public
- **Lines**: 635–709, proof ~75 lines
- **Notes**: Proof >30 lines. Heavy `WithTop ℤ` arithmetic with repeated `obtain ⟨m, hm⟩` existential unpackings.

---

### `theorem ord_P_ψ_ff_eq_zero`
- **Type**: `{x y x_Q y_Q : F} → Nonsingular x y → Nonsingular x_Q y_Q → {ℓ : ℤ} → ℓ ≠ 0 → ℓ • (some x y h_ns) = some x_Q y_Q h_ns' → (P : SmoothPoint) → P.x = x → P.y = y → (⟨W⟩).ord_P P (ψ_ff W ℓ) = 0`
- **What**: When `[ℓ]·P` is affine, `ψ_ff ℓ` has order 0 at `P` (is a unit): `ψ_ℓ(P) ≠ 0`.
- **How**: Extracts `ψ_ℓ(P) ≠ 0` from `smulEval_facts_of_zsmul_eq_some`; `ψ_ff ℓ = mk W.toAffine (W.ψ ℓ)` doesn't vanish at `P` (since `evalAt P ≠ 0`), so it is not in the maximal ideal, hence order `0`.
- **Hypotheses**: `[ℓ]·P = Q` affine; `P.x = x`, `P.y = y`.
- **Uses from project**: `smulEval_facts_of_zsmul_eq_some`, `SmoothPlaneCurve.evalAt_mk`, `SmoothPlaneCurve.ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt`
- **Used by**: `ord_P_mulByInt_y_sub_const_eq_one`
- **Visibility**: public
- **Lines**: 721–737, proof ~17 lines

---

### `private theorem ord_P_y_numerator_eq_zero`
- **Type**: `(P : SmoothPoint) → {X Y : KE} → {x_Q y_Q : F} → c ≠ 0 → ord_P P X ≥ 0 → ord_P P (X − x_Q) ≥ 1 → ord_P P (Y − y_Q) ≥ 1 → ord_P P (3X² + 2a₂X + a₄ − a₁Y) = 0` where `c = 3x_Q² + 2a₂x_Q + a₄ − a₁y_Q`
- **What**: The pulled-back Weierstrass `y`-numerator `3X²+2a₂X+a₄−a₁Y` has order 0 at `P` when its "value at `Q`" is `c ≠ 0` and `X`, `X−x_Q`, `Y−y_Q` have the indicated orders. A unit at `P` because the constant term `c` dominates.
- **How**: Splits as `algebraMap c + R'` where `R' = 3(X−xq)(X+xq)+2a₂(X−xq)−a₁(Y−yq)` has order `≥ 1`; then `ord_P_add_eq_of_lt` (the constant strictly dominates) gives `ord = 0`. Uses `ord_P_algebraMap_F_of_ne_zero` and `ord_P_algebraMap_F_nonneg`.
- **Hypotheses**: `c ≠ 0`; regularity/vanishing orders as stated.
- **Uses from project**: `SmoothPlaneCurve.ord_P_algebraMap_F_of_ne_zero`, `ord_P_algebraMap_F_nonneg`, `SmoothPlaneCurve.ord_P_mul`, `SmoothPlaneCurve.ord_P_add_le`, `SmoothPlaneCurve.ord_P_neg`, `SmoothPlaneCurve.ord_P_add_eq_of_lt`
- **Used by**: `ord_P_mulByInt_y_sub_const_eq_one`
- **Visibility**: private
- **Lines**: 755–812, proof ~58 lines
- **Notes**: Proof >30 lines. `classical` tactic used.

---

### `theorem ord_P_mulByInt_y_sub_const_eq_one`
- **Type**: `(ℓ : ℤ) → ℓ ≠ 0 → (ℓ : F) ≠ 0 → (P : SmoothPoint) → {x_Q y_Q : F} → Nonsingular x_Q y_Q → y_Q = negY x_Q y_Q → [ℓ]·P.toAffinePoint = some x_Q y_Q h_ns' → (⟨W⟩).ord_P P (mulByInt_y W ℓ − algebraMap F KE y_Q) = 1`
- **What**: **Main lemma (`y`-variant, 2-torsion image, `e = 1`):** when `Q = [ℓ]·P` is a **2-torsion** affine point and `[ℓ]` is separable, the pullback `[ℓ]^*(y_gen − y_Q)` is a uniformizer at `P`, order `= 1`.
- **How**: A large proof with two branches. Common skeleton: (1) pulled-back Weierstrass equation; (2) `A = (Y−yq) + a₁(X−xq)`, `(Y−yq)·A = (X−xq)·Bma`; (3) `Bma` has order 0 (`polynomialX_evalEval_ne_zero_at_2tor`); (4) both factors `≥ 1`; (5) `A` has order `n = ord_P(Y−yq)`, forces `M = ord_P(X−xq) = 2n`. **Char ≠ 2 branch:** uses `mulByInt_y_sub_negY` (duplication formula) and `ord_P_ψ_ff_two_mul_eq_one` to get `ord_P(ψ_ff(2ℓ)/ψ_ff(ℓ)⁴) = 1 = n`; **Char 2 branch:** uses `ord_P_mulByInt_y_sub_const_le_one` (DifferentialOrd) and `ord_P_y_numerator_eq_zero` as the upper bound `n ≤ 1`, with `n ≥ 1` giving `n = 1`.
- **Hypotheses**: `[ℓ]` separable (`(ℓ:F) ≠ 0`); `Q` affine 2-torsion.
- **Uses from project**: `mulByInt_apply`, `smulEval_facts_of_zsmul_eq_some`, `ΨSq_ff_ne_zero`, `ψ_ff_ne_zero`, `ord_P_ΨSq_ff_eq_zero`, `ord_P_ψ_ff_eq_zero`, `mulByInt_x_sub_const_eq_div`, `one_le_ord_P_algebraMap_poly_of_root`, `fibrePoly_monic`, `fibrePoly_isRoot_of_zsmul_eq_some`, `one_le_ord_P_algebraMap_of_evalAt_zero`, `mulByInt_pullback_x`, `mulByInt_pullback_y`, `pullback_equation`, `translate_constant_equation`, `x_gen_sub_const_ne_zero`, `y_gen_sub_const_eq_algebraMap_YClass`, `Affine.CoordinateRing.YClass_ne_zero`, `polynomialX_evalEval_ne_zero_at_2tor`, `Φ_ff_eq_algebraMap`, `ΨSq_ff_eq_algebraMap`, `ord_P_algebraMap_F_nonneg`, `ord_P_algebraMap_poly_eq_zero_of_eval_ne`, `ord_P_y_numerator_eq_zero`, `ord_P_mulByInt_y_sub_const_le_one` (DifferentialOrd), `mulByInt_y_sub_negY`, `ord_P_ψ_ff_two_mul_eq_one`
- **Used by**: unused in file (exported API)
- **Visibility**: public
- **Lines**: 850–1157, proof ~308 lines
- **Notes**: Proof >30 lines (longest proof: 308 lines). `classical` tactic used. Single isolated `sorry`-free but has an honest char-2 branch that routes via `ord_P_mulByInt_y_sub_const_le_one` (DifferentialOrd.lean) for the upper bound.
