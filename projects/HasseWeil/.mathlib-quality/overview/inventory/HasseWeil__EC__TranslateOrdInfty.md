# Inventory: ./HasseWeil/EC/TranslateOrdInfty.lean

**Total declarations**: 12 (all `theorem`, no `def`/`instance`/`noncomputable`)
**File purpose**: Discharges `IsTranslateOrdAtInftyCompatible` — the order-at-infinity transport obligation needed by the Weil-pairing divisor machine. Proves that the translation automorphism `τ_k` on `K(E)` carries `pointValuation` at `-k` to `ordAtInftyValuation`, using a *valuation uniqueness* argument pinned by the values on `x_gen` and `y_gen`.

---

### `theorem pointValuation_eq_exp_neg_of_ord_P_eq`

- **Type**: `{C : SmoothPlaneCurve F} {P : C.SmoothPoint} {f : C.FunctionField} {n : ℤ} → f ≠ 0 → C.ord_P P f = (n : WithTop ℤ) → C.pointValuation P f = WithZero.exp (-n)`
- **What**: Converts an additive order statement `ord_P P f = n` into the equivalent multiplicative valuation statement `pointValuation P f = exp(-n)`. Mirror of `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`; kept local to avoid importing `L6Witnesses`.
- **How**: Unfolds `ord_P` as `-(unzero v).toAdd`, deduces `n = -toAdd(unzero v)` by casting, then uses `WithZero.exp`, `ofAdd_toAdd`, `coe_unzero` to reassemble.
- **Hypotheses**: `f ≠ 0` (so valuation is nonzero); `ord_P P f = n` (as a `WithTop ℤ` equality).
- **Uses from project**: `Curves.SmoothPlaneCurve.ord_P` (unfold), `Curves.SmoothPlaneCurve.pointValuation`
- **Used by**: `pointValuation_comap_translateAlgEquivOfPoint_some_eq_ordAtInftyValuation` (3 times), `ord_P_negSmoothPoint_translateAlgEquivOfPoint_eq_ordAtInfty_some` (1 time), `MulByIntSamePlace` (external), `IsogenyOrdTransport` (external), `ProjOrdTransportLocal` (external)
- **Visibility**: public
- **Lines**: 68–79, proof ~11 lines
- **Notes**: Described in doc-comment as a local copy to avoid an extra import; has a direct analogue in `L6Witnesses.lean` (`Curves.SmoothPlaneCurve.pointValuation_eq_exp_neg_of_ord_P_eq`). Likely duplication candidate with that upstream definition.

---

### `theorem valuation_aeval_eq_exp`

- **Type**: `(w : Valuation KE (WithZero (Multiplicative ℤ))) (u : KE) → w u = WithZero.exp 2 → (∀ c : F, c ≠ 0 → w (algebraMap F KE c) = 1) → {p : Polynomial F} → p ≠ 0 → w (Polynomial.aeval u p) = WithZero.exp (2 * (p.natDegree : ℤ))`
- **What**: For a valuation `w` where `w u = exp 2` and `w` is trivial on nonzero constants, the value of `p(u)` for any nonzero polynomial `p` is `exp(2 · natDeg p)`. The leading monomial strictly dominates all others by the strict non-archimedean property.
- **How**: Computes `w(c_i u^i)` for each monomial (using `map_mul`, `map_pow`, `exp_nsmul`), then invokes `Valuation.map_sum_eq_of_lt` to read off the leading term — the leading monomial has value `exp(2n)` while every other has smaller value (proved via `WithZero.exp_lt_exp` and integer comparison).
- **Hypotheses**: Valuation `w` on `K(E)` with `w u = exp 2` and trivial on `F^×`; polynomial `p ≠ 0`.
- **Uses from project**: `x_gen W` (indirectly via specialisation); uses `Valuation.map_sum_eq_of_lt` (mathlib), `WithZero.exp_nsmul`, `WithZero.exp_lt_exp`
- **Used by**: `valuation_algebraMap_polynomial_eq_exp`
- **Visibility**: public
- **Lines**: 91–130, proof ~33 lines
- **Notes**: Proof is 33 lines — just over the 30-line threshold. No `set_option maxHeartbeats`. The `classical` at line 97 is needed for `Finset` decidability.

---

### `theorem aeval_x_gen_eq_algebraMap`

- **Type**: `(p : Polynomial F) → Polynomial.aeval (x_gen W) p = algebraMap (Polynomial F) W.toAffine.FunctionField p`
- **What**: The `aeval (x_gen W)` ring hom and the canonical `algebraMap (Polynomial F) → FunctionField` agree. Identifies the two natural maps from `F[X]` to `K(E)`.
- **How**: Applies `Polynomial.ringHom_ext'` reducing to: (1) constants agree by `IsScalarTower.algebraMap_apply`, (2) `X` maps to `x_gen` on both sides by definition.
- **Hypotheses**: None beyond the curve setup.
- **Uses from project**: `x_gen W`
- **Used by**: `valuation_algebraMap_polynomial_eq_exp`
- **Visibility**: public
- **Lines**: 133–145, proof ~12 lines
- **Notes**: None.

---

### `theorem valuation_algebraMap_polynomial_eq_exp`

- **Type**: `(w : Valuation KE ...) → w (x_gen W) = WithZero.exp 2 → (∀ c : F, c ≠ 0 → w (algebraMap F KE c) = 1) → {p : Polynomial F} → p ≠ 0 → w (algebraMap (Polynomial F) KE p) = WithZero.exp (2 * (p.natDegree : ℤ))`
- **What**: Specialisation of `valuation_aeval_eq_exp` at `u = x_gen W`: for `w` trivial on `F^×` with `w(x_gen) = exp 2`, the value on the image of a nonzero polynomial is `exp(2 · natDeg p)`.
- **How**: Rewrites `algebraMap (Polynomial F) KE p` as `aeval (x_gen W) p` via `aeval_x_gen_eq_algebraMap`, then applies `valuation_aeval_eq_exp`.
- **Hypotheses**: Same as `valuation_aeval_eq_exp` with `u = x_gen W`.
- **Uses from project**: `aeval_x_gen_eq_algebraMap`, `valuation_aeval_eq_exp`, `x_gen W`
- **Used by**: `valuation_algebraMap_fracPolyX_eq_ordAtInftyValuation` (2 calls)
- **Visibility**: public
- **Lines**: 150–158, proof ~7 lines
- **Notes**: Pure specialisation/adapter.

---

### `theorem valuation_algebraMap_fracPolyX_eq_ordAtInftyValuation`

- **Type**: `(w : Valuation KE ...) → w (x_gen W) = WithZero.exp 2 → (∀ c : F, c ≠ 0 → w (algebraMap F KE c) = 1) → (r : FractionRing (Polynomial F)) → w (algebraMap (FractionRing (Polynomial F)) KE r) = (W_smooth W).ordAtInftyValuation (algebraMap (FractionRing (Polynomial F)) KE r)`
- **What**: For `w` with `w(x_gen) = exp 2` and trivial on `F^×`, the value of `w` on the image of any rational function `r ∈ F(x)` in `K(E)` equals `ordAtInftyValuation` applied to the same element. Both equal `exp(2 · intDeg r)`.
- **How**: Handles `r = 0` trivially. For `r ≠ 0`, extracts the fraction `r = p/d` via `IsLocalization.surj`, reduces to `w (algMap p) / w (algMap d)` using `valuation_algebraMap_polynomial_eq_exp` for both numerator and denominator, and matches with `ordAtInfty_algebraMap_polynomial_of_ne_zero` + `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq` for the right-hand side.
- **Hypotheses**: `w` as above; `r` arbitrary in `FractionRing (Polynomial F)`.
- **Uses from project**: `valuation_algebraMap_polynomial_eq_exp`, `W_smooth W`, `ordAtInfty_algebraMap_polynomial_of_ne_zero` (from `SmoothPlaneCurve`), `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq` (from `SmoothPlaneCurve`)
- **Used by**: `eq_ordAtInftyValuation_of_x_y`
- **Visibility**: public
- **Lines**: 166–235, proof ~63 lines
- **Notes**: Proof is 63 lines — long. Uses `IsLocalization.surj` and `FaithfulSMul.algebraMap_injective`. No `set_option maxHeartbeats`.

---

### `theorem ordAtInftyValuation_basis_summands_distinct`

- **Type**: `{r₁ r₂ : FractionRing (Polynomial F)} → ¬(r₁ = 0 ∧ r₂ = 0) → (W_smooth W).ordAtInftyValuation (algebraMap r₁) ≠ (W_smooth W).ordAtInftyValuation (algebraMap r₂ * coordYInFunctionField)`
- **What**: The two summands of the basis decomposition `f = α + β·y` have distinct `ordAtInftyValuation`: the `F(x)` part has even order `−2k`, the `F(x)·y` part has odd order `−2k−3`. If not both zero, these cannot be equal.
- **How**: Case-splits on whether `r₁ = 0` or `r₂ = 0`. When both nonzero, computes both orders via `ordAtInfty_algebraMap_fracPolyX_of_ne_zero` and `ordAtInfty_coordYInFunctionField` + `ordAtInfty_mul`, then uses `WithZero.exp_inj` to reduce equality to `2·a = 2·b + 3` which `omega` refutes.
- **Hypotheses**: Not both `r₁ = 0` and `r₂ = 0`.
- **Uses from project**: `W_smooth W`, `ordAtInfty_algebraMap_fracPolyX_of_ne_zero` (from `SmoothPlaneCurve`), `ordAtInfty_coordYInFunctionField` (from `SmoothPlaneCurve`), `ordAtInfty_mul` (from `SmoothPlaneCurve`), `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq` (from `SmoothPlaneCurve`), `ordAtInftyValuation_ne_zero` (from `SmoothPlaneCurve`), `coordYInFunctionField_ne_zero` (from `SmoothPlaneCurve`)
- **Used by**: `eq_ordAtInftyValuation_of_x_y`
- **Visibility**: public
- **Lines**: 243–293, proof ~44 lines
- **Notes**: Proof is 44 lines. The parity argument (even vs. odd) is the key geometric content — the three-fold pole of `y` is what makes this work.

---

### `theorem eq_ordAtInftyValuation_of_x_y`

- **Type**: `(w : Valuation KE ...) → w (x_gen W) = WithZero.exp 2 → w (y_gen W) = WithZero.exp 3 → (∀ c : F, c ≠ 0 → w (algebraMap F KE c) = 1) → w = (W_smooth W).ordAtInftyValuation`
- **What**: **Master pinning lemma.** A `ℤᵐ⁰`-valued valuation on `K(E)` that agrees with `ordAtInftyValuation` on `x_gen` (value `exp 2`), `y_gen` (value `exp 3`), and is trivial on `F^×` must equal `ordAtInftyValuation`. This is proved by decomposing every `f = α + β·y` (`α, β ∈ F(x)`) and using the parity distinctness of the two summand-values.
- **How**: Uses `exists_decomp` (the basis decomposition `F(x) ⊕ F(x)·y`) to write each `f`. Then `valuation_algebraMap_fracPolyX_eq_ordAtInftyValuation` gives agreement on `F(x)` parts; `coordY_W_smooth_eq_y_gen` bridges the `y`-generator; `ordAtInftyValuation_basis_summands_distinct` provides the distinctness needed for `Valuation.map_add_of_distinct_val` to read off the full valuation.
- **Hypotheses**: Valuation `w` on `K(E)` satisfying the three base-case conditions.
- **Uses from project**: `valuation_algebraMap_fracPolyX_eq_ordAtInftyValuation`, `ordAtInftyValuation_basis_summands_distinct`, `W_smooth W`, `exists_decomp` (from `SmoothPlaneCurve`), `coordY_W_smooth_eq_y_gen` (from `OrdAtInftyBridge`), `coordY_eq_coordYInFunctionField` (from `SmoothPlaneCurve`), `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`, `ordAtInfty_coordYInFunctionField`, `coordYInFunctionField_ne_zero`; `x_gen W`, `y_gen W`
- **Used by**: `pointValuation_comap_translateAlgEquivOfPoint_some_eq_ordAtInftyValuation`; externally by `MulByIntSamePlace`, `OneSubInftyResidues`, `ProjOrdTransportLocal`
- **Visibility**: public
- **Lines**: 302–372, proof ~64 lines
- **Notes**: Proof is 64 lines — one of the longest. Key API consumer from the project.

---

### `theorem ord_P_negSmoothPoint_translateX_xy_eq_neg_two`

- **Type**: `(xk yk : F) → W.toAffine.Nonsingular xk yk → (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns) (translateX_xy W xk yk) = ((-2 : ℤ) : WithTop ℤ)`
- **What**: The order of `τ_T(x_gen) = translateX_xy` at the smooth point `-T = negSmoothPoint` is `-2`, uniformly across the 2-torsion and non-2-torsion cases.
- **How**: Case-splits on whether `yk = W.toAffine.negY xk yk` (2-torsion condition), dispatching to `ord_P_translateX_xy_eq_neg_two_at_2tor` or `ord_P_translateX_xy_eq_neg_two_of_non_2_tor` (both from `TranslationOrd.lean`).
- **Hypotheses**: `(xk, yk)` is a nonsingular point on `W`.
- **Uses from project**: `negSmoothPoint W`, `translateX_xy W`, `ord_P_translateX_xy_eq_neg_two_at_2tor` (from `TranslationOrd`), `ord_P_translateX_xy_eq_neg_two_of_non_2_tor` (from `TranslationOrd`)
- **Used by**: `pointValuation_comap_translateAlgEquivOfPoint_some_eq_ordAtInftyValuation`
- **Visibility**: public
- **Lines**: 378–385, proof ~6 lines
- **Notes**: Pure dispatch lemma unifying the two torsion cases.

---

### `theorem ord_P_negSmoothPoint_translateY_xy_eq_neg_three`

- **Type**: `(xk yk : F) → W.toAffine.Nonsingular xk yk → (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns) (translateY_xy W xk yk) = ((-3 : ℤ) : WithTop ℤ)`
- **What**: The order of `τ_T(y_gen) = translateY_xy` at the smooth point `-T` is `-3`, uniformly across 2-torsion and non-2-torsion cases.
- **How**: Same dispatch structure as the `x_gen` analogue, using `ord_P_translateY_xy_eq_neg_three_at_2tor` and `ord_P_translateY_xy_eq_neg_three_of_non_2_tor`.
- **Hypotheses**: `(xk, yk)` nonsingular on `W`.
- **Uses from project**: `negSmoothPoint W`, `translateY_xy W`, `ord_P_translateY_xy_eq_neg_three_at_2tor` (from `TranslationOrd`), `ord_P_translateY_xy_eq_neg_three_of_non_2_tor` (from `TranslationOrd`)
- **Used by**: `pointValuation_comap_translateAlgEquivOfPoint_some_eq_ordAtInftyValuation`
- **Visibility**: public
- **Lines**: 387–394, proof ~6 lines
- **Notes**: Exact structural parallel to `ord_P_negSmoothPoint_translateX_xy_eq_neg_two`.

---

### `theorem pointValuation_comap_translateAlgEquivOfPoint_some_eq_ordAtInftyValuation`

- **Type**: `(xk yk : F) → W.toAffine.Nonsingular xk yk → ((W_smooth W).pointValuation (negSmoothPoint W xk yk h_ns)).comap (translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns)).toAlgHom.toRingHom = (W_smooth W).ordAtInftyValuation`
- **What**: The pullback (comap) of `pointValuation` at `-T = negSmoothPoint` along the translation automorphism `τ_T` equals `ordAtInftyValuation`. This is the multiplicative valuation-level identity from which the additive order transport is deduced.
- **How**: Sets up the comap valuation `w`, then applies `eq_ordAtInftyValuation_of_x_y` after verifying its three hypotheses: `w(x_gen) = exp 2` via `ord_P_negSmoothPoint_translateX_xy_eq_neg_two` + `pointValuation_eq_exp_neg_of_ord_P_eq`; `w(y_gen) = exp 3` similarly; `w(algMap c) = 1` via `τ.commutes` (AlgEquiv fixes `algebraMap F`) + `ord_P_algebraMap_F_of_ne_zero`.
- **Hypotheses**: `(xk, yk)` nonsingular on `W`.
- **Uses from project**: `eq_ordAtInftyValuation_of_x_y`, `ord_P_negSmoothPoint_translateX_xy_eq_neg_two`, `ord_P_negSmoothPoint_translateY_xy_eq_neg_three`, `pointValuation_eq_exp_neg_of_ord_P_eq` (×3), `translateAlgEquivOfPoint_apply_x_gen` (from `TranslateValuation`), `translateAlgEquivOfPoint_apply_y_gen` (from `TranslateValuation`), `negSmoothPoint W`, `W_smooth W`, `ord_P_eq_top_iff` (from `SmoothPlaneCurve`), `ord_P_algebraMap_F_of_ne_zero` (from `SmoothPlaneCurve`)
- **Used by**: `ord_P_negSmoothPoint_translateAlgEquivOfPoint_eq_ordAtInfty_some`
- **Visibility**: public
- **Lines**: 402–455, proof ~47 lines
- **Notes**: Proof is 47 lines. The key bridge theorem in the chain, packaging the multiplicative valuation equality.

---

### `theorem ord_P_negSmoothPoint_translateAlgEquivOfPoint_eq_ordAtInfty_some`

- **Type**: `(xk yk : F) → W.toAffine.Nonsingular xk yk → (f : KE) → f ≠ 0 → (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns) (translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns) f) = (W_smooth W).ordAtInfty f`
- **What**: Pointwise order transport: `ord_P(-T)(τ_T f) = ordAtInfty(f)` for `f ≠ 0`, when `T = some xk yk h_ns`. Converts the multiplicative valuation identity into the additive order equality.
- **How**: Applies `pointValuation_comap_translateAlgEquivOfPoint_some_eq_ordAtInftyValuation` to get the valuation identity, evaluates it at `f` (using `DFunLike.congr_fun`), extracts integer witnesses `m, n` from `WithTop ℤ` finiteness (using `ord_P_eq_top_iff` and `ordAtInfty_of_ne`), converts both sides to `exp(-m)` and `exp(-n)` via `pointValuation_eq_exp_neg_of_ord_P_eq` and `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`, then uses `WithZero.exp_inj` and `neg_injective` to conclude `m = n`.
- **Hypotheses**: `(xk, yk)` nonsingular; `f ≠ 0`.
- **Uses from project**: `pointValuation_comap_translateAlgEquivOfPoint_some_eq_ordAtInftyValuation`, `pointValuation_eq_exp_neg_of_ord_P_eq`, `negSmoothPoint W`, `W_smooth W`, `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq` (from `SmoothPlaneCurve`), `ordAtInfty_of_ne` (from `SmoothPlaneCurve`), `ord_P_eq_top_iff` (from `SmoothPlaneCurve`)
- **Used by**: `isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint`
- **Visibility**: public
- **Lines**: 462–495, proof ~27 lines
- **Notes**: None.

---

### `theorem isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint`

- **Type**: `(P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point) → P.toAffinePoint + k = Affine.Point.zero → IsTranslateOrdAtInftyCompatible W P k h_zero`
- **What**: **Main theorem.** Unconditionally discharges `IsTranslateOrdAtInftyCompatible`: for any finite smooth point `P` and any group element `k` with `P + k = O` (i.e., `k = -P`), the translation `τ_k` carries `ord_P P` to `ordAtInfty`. This is the principal geometric content gating the Weil-pairing divisor transport.
- **How**: From `P + k = O`, deduces `k = -P`, then extracts coordinates `(xk, yk)` from `P` with `k = some xk (negY P.x P.y) h_ns` and `P = negSmoothPoint W xk yk h_ns` (using `neg_some_eq_some`, `Affine.nonsingular_neg`, `negSmoothPoint_x/y`, `negY_negY`). Then applies `isTranslateOrdAtInftyCompatible_of_nonzero_pointwise_eq` (from `TranslationOrd`) to reduce to the nonzero case, and concludes with `ord_P_negSmoothPoint_translateAlgEquivOfPoint_eq_ordAtInfty_some`.
- **Hypotheses**: `P` is a finite (affine) smooth point on `W`; `P.toAffinePoint + k = O`.
- **Uses from project**: `ord_P_negSmoothPoint_translateAlgEquivOfPoint_eq_ordAtInfty_some`, `isTranslateOrdAtInftyCompatible_of_nonzero_pointwise_eq` (from `TranslationOrd`), `negSmoothPoint W`, `neg_some_eq_some` (from `TranslationOrd`), `negSmoothPoint_x` (from `TranslationOrd`), `negSmoothPoint_y` (from `TranslationOrd`), `W_smooth W`; `SmoothPoint.toAffinePoint_def`, `Affine.nonsingular_neg`, `Affine.negY_negY`
- **Used by**: External callers only (within this file, unused); external: `MulByIntUnramified`, `MulByIntSamePlace` (×2), `OneSubInftyResidues`, `PencilComapWitnesses`, `DivisorTranslate` (×2), `DivisorPullback` (×2)
- **Visibility**: public
- **Lines**: 504–530, proof ~26 lines
- **Notes**: This is the file's exported payoff theorem, widely used across the Weil-pairing stack.
