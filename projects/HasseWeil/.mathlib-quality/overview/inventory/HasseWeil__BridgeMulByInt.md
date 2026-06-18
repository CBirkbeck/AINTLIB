# Inventory: ./HasseWeil/BridgeMulByInt.lean

**File**: `HasseWeil/BridgeMulByInt.lean`
**Imports**: `HasseWeil.FormalIsogenySeries`, `HasseWeil.FormalGroupBridge`, `HasseWeil.HahnSeriesAux`
**Purpose**: T-IV-BRIDGE-001 specialised to `[n]` (multiplication-by-n isogeny). Proves `omegaPullbackCoeff W [n] = algebraMap F KE n` by Laurent-series leading-coefficient computation following Silverman IV.2.3 / III.4.13.

---

## Declaration inventory

---

### `theorem localExpand_algebraMap_polynomial`
- **Type**: `(p : Polynomial F) → localExpand W (algebraMap R KE (algebraMap (Polynomial F) R p)) = localExpand_inner W p`
- **What**: Equates two routes into Laurent series for a polynomial-in-x_gen: going through the function field vs direct polynomial evaluation on `formalX`.
- **How**: Proves equality of two ring homomorphisms `F[X] →+* LaurentSeries F` via `Polynomial.ringHom_ext`, checking agreement on constants (`localExpand_algebraMap`, `IsScalarTower.algebraMap_eq`) and on X (`localExpand_x_gen`, `localExpand_inner_X`).
- **Hypotheses**: `W` elliptic over `F` (field, DecidableEq).
- **Uses from project**: `localExpand_inner_C`, `localExpand_algebraMap`, `localExpand_x_gen`, `localExpand_inner_X`.
- **Used by**: `localExpand_Φ_ff_orderTop`, `localExpand_ΨSq_ff_orderTop`, `localExpand_Φ_ff_leadingCoeff`, `localExpand_ΨSq_ff_leadingCoeff`, `localExpand_preΨ_2n_orderTop`, `localExpand_preΨ_2n_leadingCoeff`, `localExpand_basis_decomp`.
- **Visibility**: public
- **Lines**: L60–L111 (52 lines total)
- **Notes**: Proof is 41 lines excluding signature; longest structural lemma. The tactic proof carefully chains `IsScalarTower.algebraMap_eq` twice to avoid diamond issues.

---

### `theorem localExpand_basis_decomp`
- **Type**: `(p q : Polynomial F) → localExpand W (algebraMap R KE (p • 1 + q • CoordinateRing.mk W.toAffine Polynomial.X)) = localExpand_inner W p + localExpand_inner W q * formalY W`
- **What**: Computes `localExpand` of a coordinate-ring element decomposed in the `{1, y_gen}` basis as a Laurent-series sum.
- **How**: Applies `map_add` and `map_mul`, then uses `localExpand_algebraMap_polynomial` for each component and `localExpand_y_gen` for the y-part.
- **Hypotheses**: `W` elliptic over `F`.
- **Uses from project**: `localExpand_algebraMap_polynomial`, `localExpand_y_gen`, `Affine.CoordinateRing.smul`.
- **Used by**: unused in file (potentially used by importers).
- **Visibility**: public
- **Lines**: L112–L145 (34 lines)
- **Notes**: Not called by any other declaration in this file; exported for external use.

---

### `theorem localExpand_inner_add_mul_formalY_orderTop`
- **Type**: `{p q : Polynomial F} → p ≠ 0 → q ≠ 0 → (localExpand_inner W p + localExpand_inner W q * formalY W).orderTop = min (↑(-2 * p.natDegree)) (↑(-2 * q.natDegree - 3))`
- **What**: orderTop of a `{1, formalY}` basis sum is the minimum of the two components' orderTops (which have different parities: -2d is even, -2d'-3 is odd, so they never coincide).
- **How**: Uses `localExpand_inner_orderTop_eq` and `localExpand_inner_mul_formalY_orderTop` to determine the two components' orders; since they differ (parity argument by `omega`), uses `HahnSeries.orderTop_add_eq_left/right`.
- **Hypotheses**: `p ≠ 0`, `q ≠ 0`.
- **Uses from project**: `localExpand_inner_orderTop_eq`, `localExpand_inner_mul_formalY_orderTop`.
- **Used by**: unused in file (exported).
- **Visibility**: public
- **Lines**: L146–L174 (29 lines)
- **Notes**: Not used within this file; available for external callers computing orderTop of basis decompositions.

---

### `theorem localExpand_Φ_ff_orderTop`
- **Type**: `(n : ℤ) → n ≠ 0 → (localExpand W (Φ_ff W n)).orderTop = ↑(-2 * n.natAbs^2)`
- **What**: The orderTop of `localExpand` applied to the division polynomial numerator `Φ_n` equals `-2 · n.natAbs^2`.
- **How**: Reduces via `localExpand_algebraMap_polynomial` to `localExpand_inner_orderTop_eq` and the mathlib lemma `W.natDegree_Φ`.
- **Hypotheses**: `n ≠ 0` (so `Φ_n ≠ 0`).
- **Uses from project**: `localExpand_algebraMap_polynomial`, `localExpand_inner_orderTop_eq`.
- **Used by**: `localExpand_Φ_ff_ne_zero`, `localExpand_mulByInt_x_orderTop`, `localExpand_a1_Φ_ΨSq_orderTop_ge`.
- **Visibility**: public
- **Lines**: L175–L189 (15 lines)

---

### `theorem localExpand_ΨSq_ff_orderTop`
- **Type**: `(n : ℤ) → (n : F) ≠ 0 → (localExpand W (ΨSq_ff W n)).orderTop = ↑(-2 * (n.natAbs^2 - 1))`
- **What**: orderTop of `localExpand(ΨSq_n)` equals `-2(n^2-1)`, using `natDegree_ΨSq`.
- **How**: Same pattern as `localExpand_Φ_ff_orderTop` via `localExpand_algebraMap_polynomial` and `localExpand_inner_orderTop_eq`.
- **Hypotheses**: `(n : F) ≠ 0` (char condition ensuring `ΨSq_n ≠ 0`).
- **Uses from project**: `localExpand_algebraMap_polynomial`, `localExpand_inner_orderTop_eq`.
- **Used by**: `localExpand_ΨSq_ff_ne_zero`, `localExpand_mulByInt_x_orderTop`, `localExpand_ΨSq_ff_sq_orderTop`, `localExpand_mulByInt_y_orderTop_of_rhs`, `localExpand_a1_Φ_ΨSq_orderTop_ge`.
- **Visibility**: public
- **Lines**: L190–L204 (15 lines)

---

### `theorem localExpand_Φ_ff_ne_zero`
- **Type**: `(n : ℤ) → n ≠ 0 → localExpand W (Φ_ff W n) ≠ 0`
- **What**: Nonvanishing of `localExpand(Φ_n)` for `n ≠ 0`.
- **How**: Contradiction via `localExpand_Φ_ff_orderTop`: if zero then orderTop = ⊤, contradicting the finite value.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `localExpand_Φ_ff_orderTop`.
- **Used by**: unused directly in file (but `localExpand_ΨSq_ff_ne_zero` follows same pattern; `localExpand_mulByInt_x_orderTop` uses `localExpand_ΨSq_ff_ne_zero` not this one).
- **Visibility**: public
- **Lines**: L205–L212 (8 lines)
- **Notes**: Exported nonvanishing witness; not used by other declarations in this file.

---

### `theorem localExpand_ΨSq_ff_ne_zero`
- **Type**: `(n : ℤ) → (n : F) ≠ 0 → localExpand W (ΨSq_ff W n) ≠ 0`
- **What**: Nonvanishing of `localExpand(ΨSq_n)`.
- **How**: Same contradiction pattern via `localExpand_ΨSq_ff_orderTop`.
- **Hypotheses**: `(n : F) ≠ 0`.
- **Uses from project**: `localExpand_ΨSq_ff_orderTop`.
- **Used by**: `localExpand_mulByInt_x_orderTop`, `localExpand_mulByInt_x_leadingCoeff`.
- **Visibility**: public
- **Lines**: L213–L222 (10 lines)

---

### `theorem localExpand_mulByInt_x_orderTop`
- **Type**: `(n : ℤ) → n ≠ 0 → (n : F) ≠ 0 → (localExpand W (mulByInt_x W n)).orderTop = ↑(-2 : ℤ)`
- **What**: The orderTop of `localExpand` of the x-coordinate of `[n]` equals `-2` (same pole order as `x` at `O`), despite `[n]` having degree `n^2`.
- **How**: Unfolds `mulByInt_x = Φ_ff / ΨSq_ff`, applies `map_div₀`, uses `HahnSeries.orderTop_div` with `localExpand_Φ_ff_orderTop` minus `localExpand_ΨSq_ff_orderTop`, then arithmetic via `norm_cast` and `ring`.
- **Hypotheses**: `n ≠ 0`, `(n : F) ≠ 0`.
- **Uses from project**: `localExpand_ΨSq_ff_ne_zero`, `localExpand_Φ_ff_orderTop`, `localExpand_ΨSq_ff_orderTop`.
- **Used by**: `coeff_one_formalIsogenySeries_mulByInt_of_witnesses`.
- **Visibility**: public
- **Lines**: L223–L245 (23 lines)

---

### `theorem localExpand_Φ_ff_leadingCoeff`
- **Type**: `(n : ℤ) → (localExpand W (Φ_ff W n)).leadingCoeff = 1`
- **What**: The leading coefficient of `localExpand(Φ_n)` is `1` (as `Φ_n` is monic).
- **How**: Case splits on `n = 0` (using `W.Φ_zero`) and `n ≠ 0` (using `localExpand_algebraMap_polynomial`, `localExpand_inner_leadingCoeff`, `W.leadingCoeff_Φ`).
- **Hypotheses**: None (holds for all `n`).
- **Uses from project**: `localExpand_algebraMap_polynomial`, `localExpand_inner_leadingCoeff`.
- **Used by**: `localExpand_mulByInt_x_leadingCoeff`.
- **Visibility**: public
- **Lines**: L246–L263 (18 lines)

---

### `theorem localExpand_ΨSq_ff_leadingCoeff`
- **Type**: `(n : ℤ) → (n : F) ≠ 0 → (localExpand W (ΨSq_ff W n)).leadingCoeff = (n : F)^2`
- **What**: The leading coefficient of `localExpand(ΨSq_n)` is `n^2`.
- **How**: Via `localExpand_algebraMap_polynomial`, `localExpand_inner_leadingCoeff`, `W.leadingCoeff_ΨSq`.
- **Hypotheses**: `(n : F) ≠ 0`.
- **Uses from project**: `localExpand_algebraMap_polynomial`, `localExpand_inner_leadingCoeff`.
- **Used by**: `localExpand_mulByInt_x_leadingCoeff`, `localExpand_ΨSq_ff_sq_orderTop` (indirectly via `localExpand_mulByInt_y_leadingCoeff_of_rhs`).
- **Visibility**: public
- **Lines**: L264–L273 (10 lines)

---

### `theorem localExpand_mulByInt_x_leadingCoeff`
- **Type**: `(n : ℤ) → (n : F) ≠ 0 → (localExpand W (mulByInt_x W n)).leadingCoeff = ((n : F)^2)⁻¹`
- **What**: Leading coefficient of `localExpand(mulByInt_x W n)` is `1/n^2`.
- **How**: Uses `HahnSeries.leadingCoeff_div` with `localExpand_Φ_ff_leadingCoeff` (= 1) divided by `localExpand_ΨSq_ff_leadingCoeff` (= n^2).
- **Hypotheses**: `(n : F) ≠ 0`.
- **Uses from project**: `localExpand_ΨSq_ff_ne_zero`, `localExpand_Φ_ff_leadingCoeff`, `localExpand_ΨSq_ff_leadingCoeff`.
- **Used by**: `coeff_one_formalIsogenySeries_mulByInt_of_witnesses`.
- **Visibility**: public
- **Lines**: L274–L295 (22 lines)

---

### `theorem preΨ_u_eq_ΨSq_sq_mul_alpha_star_u`
- **Type**: `(n : ℤ) → n ≠ 0 → (n : F) ≠ 0 → algebraMap (Polynomial F) KE (W.preΨ (2 * n)) * u_gen W = (ΨSq_ff W n)^2 * alpha_star_u W (mulByInt W.toAffine n)`
- **What**: Wronskian-derived identity: `preΨ(2n) · u_gen = ΨSq^2 · αu` in the function field. This expresses `αu` (the pull-back of `u_gen` under `[n]`) in terms of polynomial quantities, avoiding the y-expansion of `ω_n/ψ_n^3`.
- **How**: Applies the Wronskian identity `divPoly_wronskian_identity` and the polynomial Wronskian `wronskian_Φ_ΨSq` to rewrite the bracket `Φ'·ΨSq - Φ·ΨSq' = C(n)·preΨ(2n)`, then cancels `algebraMap F KE n` using `mul_left_cancel₀` (injectivity of `algebraMap F KE`).
- **Hypotheses**: `n ≠ 0`, `(n : F) ≠ 0`.
- **Uses from project**: `divPoly_wronskian_identity`, `wronskian_Φ_ΨSq`, `Φ_ff`, `ΨSq_ff`.
- **Used by**: `two_mulByInt_y_ΨSq_sq_eq`.
- **Visibility**: public
- **Lines**: L296–L345 (50 lines)
- **Notes**: Proof is 47 lines; the key cancellation step uses `IsScalarTower.algebraMap_apply` to identify `Φ_ff` and `ΨSq_ff` with their polynomial images, then `map_sub`/`map_mul`.

---

### `theorem ΨSq_ff_ne_zero_of_cast`
- **Type**: `(n : ℤ) → (n : F) ≠ 0 → ΨSq_ff W n ≠ 0`
- **What**: `ΨSq_ff W n` is nonzero in the function field `KE` when `(n : F) ≠ 0`.
- **How**: Injectivity of the composite `Polynomial F → CoordinateRing → FunctionField` via `IsFractionRing.injective` and `CoordinateRing.algebraMap_poly_injective`.
- **Hypotheses**: `(n : F) ≠ 0`.
- **Uses from project**: none explicit (uses mathlib injectivity).
- **Used by**: `mulByInt_x_mul_ΨSq_ff`.
- **Visibility**: public
- **Lines**: L346–L357 (12 lines)

---

### `theorem mulByInt_x_mul_ΨSq_ff`
- **Type**: `(n : ℤ) → (n : F) ≠ 0 → mulByInt_x W n * ΨSq_ff W n = Φ_ff W n`
- **What**: The identity `(Φ_n / ΨSq_n) * ΨSq_n = Φ_n` (cancellation of denominator).
- **How**: Unfolds `mulByInt_x` as `Φ_ff / ΨSq_ff` and applies `div_mul_cancel₀` with `ΨSq_ff_ne_zero_of_cast`.
- **Hypotheses**: `(n : F) ≠ 0`.
- **Uses from project**: `ΨSq_ff_ne_zero_of_cast`.
- **Used by**: `two_mulByInt_y_ΨSq_sq_eq`.
- **Visibility**: public
- **Lines**: L358–L364 (7 lines)

---

### `theorem two_mulByInt_y_ΨSq_sq_eq`
- **Type**: `(n : ℤ) → n ≠ 0 → (n : F) ≠ 0 → (2 : KE) * mulByInt_y W n * (ΨSq_ff W n)^2 = algebraMap (Polynomial F) KE (W.preΨ (2*n)) * u_gen W - algebraMap F KE W.a₁ * Φ_ff W n * ΨSq_ff W n - algebraMap F KE W.a₃ * (ΨSq_ff W n)^2`
- **What**: Explicit formula for `2 · mulByInt_y · ΨSq^2` in terms of polynomial quantities, derived from the Wronskian-αu identity. This avoids the y-expansion of `ω_n/ψ_n^3`.
- **How**: Applies `preΨ_u_eq_ΨSq_sq_mul_alpha_star_u`, unfolds `alpha_star_u_eq` and the definition of `alpha_star_u`, uses `mulByInt_pullback_x/y` to identify pull-backs, and closes by `linear_combination` using `mulByInt_x_mul_ΨSq_ff`.
- **Hypotheses**: `n ≠ 0`, `(n : F) ≠ 0`.
- **Uses from project**: `preΨ_u_eq_ΨSq_sq_mul_alpha_star_u`, `alpha_star_u_eq`, `alpha_star_u`, `mulByInt_pullback_x`, `mulByInt_pullback_y`, `mulByInt_x_mul_ΨSq_ff`.
- **Used by**: `localExpand_mulByInt_y_orderTop_of_rhs`, `localExpand_mulByInt_y_leadingCoeff_of_rhs`.
- **Visibility**: public
- **Lines**: L365–L401 (37 lines)
- **Notes**: Proof >30 lines (37 lines total). Key step: the `rw [...] at h_preΨ` block rewrites the αu expression using definitional unfolding + pullback formulas, then `linear_combination` finishes.

---

### `theorem localExpand_const`
- **Type**: `(c : F) → localExpand W (algebraMap F KE c) = HahnSeries.single (0 : ℤ) c`
- **What**: `localExpand` of a scalar constant is the Hahn-series single at degree 0.
- **How**: Combines `localExpand_algebraMap` with `HahnSeries.ofPowerSeries_C`.
- **Hypotheses**: None.
- **Uses from project**: `localExpand_algebraMap`.
- **Used by**: `localExpand_a_mul_x_gen`, `localExpand_u_gen_orderTop`, `localExpand_u_gen_leadingCoeff`, `localExpand_a1_Φ_ΨSq_orderTop_ge`, `localExpand_a3_ΨSq_sq_orderTop_ge` (8 total uses).
- **Visibility**: public
- **Lines**: L402–L409 (8 lines)
- **Notes**: Key internal utility; used 8 times across the file — qualifies as `keyApi`.

---

### `private lemma orderTop_single_zero_mul`
- **Type**: `{c : F} → c ≠ 0 → (s : LaurentSeries F) → (HahnSeries.single (0 : ℤ) c * s).orderTop = s.orderTop`
- **What**: Multiplication by a nonzero constant (as `single 0 c`) preserves orderTop.
- **How**: Via `HahnSeries.orderTop_mul` and `HahnSeries.orderTop_single`, then `zero_add` in `WithTop ℤ`.
- **Hypotheses**: `c ≠ 0`.
- **Uses from project**: none.
- **Used by**: `localExpand_u_gen_orderTop` (L458, L463), `localExpand_u_gen_leadingCoeff` (L506, L514) — 5 uses total.
- **Visibility**: private
- **Lines**: L410–L416 (7 lines)
- **Notes**: Qualifies as `keyApi` with 5 uses.

---

### `private lemma leadingCoeff_single_zero_mul`
- **Type**: `(c : F) → (s : LaurentSeries F) → (HahnSeries.single (0 : ℤ) c * s).leadingCoeff = c * s.leadingCoeff`
- **What**: Leading coefficient of constant-times-series.
- **How**: Via `HahnSeries.leadingCoeff_mul` and `HahnSeries.leadingCoeff_of_single`.
- **Hypotheses**: None (holds even for `c = 0`).
- **Uses from project**: none.
- **Used by**: `localExpand_u_gen_leadingCoeff`.
- **Visibility**: private
- **Lines**: L417–L423 (7 lines)

---

### `private lemma localExpand_a_mul_x_gen`
- **Type**: `(a : F) → localExpand W (algebraMap F KE a * x_gen W) = HahnSeries.single (0 : ℤ) a * formalX W`
- **What**: Computes `localExpand(a · x_gen)` as `(single 0 a) * formalX`.
- **How**: `map_mul`, `localExpand_x_gen`, `localExpand_const`.
- **Hypotheses**: None.
- **Uses from project**: `localExpand_x_gen`, `localExpand_const`.
- **Used by**: `localExpand_u_gen_orderTop`, `localExpand_u_gen_leadingCoeff`.
- **Visibility**: private
- **Lines**: L424–L434 (11 lines)

---

### `theorem localExpand_u_gen_orderTop`
- **Type**: `(h2 : (2 : F) ≠ 0) → (localExpand W (u_gen W)).orderTop = ↑(-3 : ℤ)`
- **What**: In char ≠ 2, `localExpand(u_gen)` has orderTop `-3`. The `2·formalY` term (orderTop -3, odd) dominates over `a₁·formalX` (orderTop -2 or ⊤) and `a₃` (orderTop 0 or ⊤).
- **How**: Unfolds `u_gen`, converts to Laurent series via `localExpand_y_gen`, `localExpand_a_mul_x_gen`, `localExpand_const`; uses `orderTop_single_zero_mul` + `formalY_orderTop`; shows `T+U` has orderTop ≥ -2 > -3 = orderTop of S, then applies `HahnSeries.orderTop_add_eq_left`.
- **Hypotheses**: char ≠ 2 (`(2 : F) ≠ 0`).
- **Uses from project**: `localExpand_y_gen`, `localExpand_a_mul_x_gen`, `localExpand_const`, `orderTop_single_zero_mul`, `formalY_orderTop`, `formalX_orderTop`.
- **Used by**: `localExpand_preΨ_u_gen_orderTop`.
- **Visibility**: public
- **Lines**: L435–L489 (55 lines)
- **Notes**: Proof is 51 lines; longer than 30 lines. Uses `set` tactic to name the three components S, T, U.

---

### `theorem localExpand_u_gen_leadingCoeff`
- **Type**: `(h2 : (2 : F) ≠ 0) → (localExpand W (u_gen W)).leadingCoeff = -2`
- **What**: In char ≠ 2, `localExpand(u_gen)` has leading coefficient `-2` (from `2 * formalY.leadingCoeff = 2 * (-1) = -2`).
- **How**: Same structure as `localExpand_u_gen_orderTop`, using `HahnSeries.leadingCoeff_add_eq_left` once dominance (S.orderTop < (T+U).orderTop) is re-established.
- **Hypotheses**: char ≠ 2.
- **Uses from project**: `localExpand_y_gen`, `localExpand_a_mul_x_gen`, `localExpand_const`, `orderTop_single_zero_mul`, `leadingCoeff_single_zero_mul`, `formalY_orderTop`, `formalX_orderTop`, `formalY_leadingCoeff`.
- **Used by**: `localExpand_preΨ_u_gen_leadingCoeff`.
- **Visibility**: public
- **Lines**: L490–L535 (46 lines)
- **Notes**: Proof >30 lines (43 lines). Duplicates the orderTop computation structure from `localExpand_u_gen_orderTop` to re-establish dominance.

---

### `private lemma n_ne_zero_of_2n`
- **Type**: `(n : ℤ) → ((2 * n : ℤ) : F) ≠ 0 → n ≠ 0`
- **What**: Derives `n ≠ 0` from `(2n : F) ≠ 0`.
- **How**: Contradiction: if `n = 0`, push_cast and ring gives `(2·0 : F) = 0`.
- **Hypotheses**: char-ish condition on `F`.
- **Uses from project**: none.
- **Used by**: `natDegree_preΨ_2n`, `localExpand_preΨ_2n_orderTop`.
- **Visibility**: private
- **Lines**: L536–L542 (7 lines)

---

### `private lemma natDegree_preΨ_2n`
- **Type**: `(n : ℤ) → ((2 * n : ℤ) : F) ≠ 0 → (W.preΨ (2 * n)).natDegree = 2 * n.natAbs^2 - 2`
- **What**: natDegree of the pre-division-polynomial `preΨ(2n)` is `2n^2 - 2` (since `2n` is even).
- **How**: Applies `W.natDegree_preΨ`, selects the even branch (`if_pos h2n_even`), then does arithmetic with `Int.natAbs_mul`, `Nat.pow_le_pow_left`, and `omega`.
- **Hypotheses**: `(2n : F) ≠ 0`.
- **Uses from project**: `n_ne_zero_of_2n`.
- **Used by**: `localExpand_preΨ_2n_orderTop`.
- **Visibility**: private
- **Lines**: L543–L563 (21 lines)

---

### `private lemma leadingCoeff_preΨ_2n`
- **Type**: `(n : ℤ) → ((2 * n : ℤ) : F) ≠ 0 → (W.preΨ (2 * n)).leadingCoeff = (n : F)`
- **What**: Leading coefficient of `preΨ(2n)` is `n` (for `2n` even, the formula gives `(2n)/2 = n`).
- **How**: Uses `W.leadingCoeff_preΨ`, selects even branch, and `Int.mul_ediv_cancel_left`.
- **Hypotheses**: `(2n : F) ≠ 0`.
- **Uses from project**: none beyond mathlib.
- **Used by**: `localExpand_preΨ_2n_leadingCoeff`.
- **Visibility**: private
- **Lines**: L564–L574 (11 lines)

---

### `private lemma localExpand_preΨ_2n_orderTop`
- **Type**: `(n : ℤ) → ((2 * n : ℤ) : F) ≠ 0 → (localExpand W (algebraMap (Polynomial F) KE (W.preΨ (2 * n)))).orderTop = ↑(-4 * n.natAbs^2 + 4)`
- **What**: orderTop of `localExpand(preΨ(2n))` equals `-4n^2 + 4`.
- **How**: Applies `localExpand_algebraMap_polynomial`, `localExpand_inner_orderTop_eq`, `natDegree_preΨ_2n`, then arithmetic via `norm_cast`, `Nat.cast_sub`, `push_cast`, `ring`.
- **Hypotheses**: `(2n : F) ≠ 0`.
- **Uses from project**: `localExpand_algebraMap_polynomial`, `localExpand_inner_orderTop_eq`, `natDegree_preΨ_2n`, `n_ne_zero_of_2n`.
- **Used by**: `localExpand_preΨ_u_gen_orderTop`.
- **Visibility**: private
- **Lines**: L575–L595 (21 lines)

---

### `private lemma localExpand_preΨ_2n_leadingCoeff`
- **Type**: `(n : ℤ) → ((2 * n : ℤ) : F) ≠ 0 → (localExpand W (algebraMap (Polynomial F) KE (W.preΨ (2 * n)))).leadingCoeff = (n : F)`
- **What**: Leading coefficient of `localExpand(preΨ(2n))` is `n`.
- **How**: Via `localExpand_algebraMap_polynomial`, `localExpand_inner_leadingCoeff`, `leadingCoeff_preΨ_2n`.
- **Hypotheses**: `(2n : F) ≠ 0`.
- **Uses from project**: `localExpand_algebraMap_polynomial`, `localExpand_inner_leadingCoeff`, `leadingCoeff_preΨ_2n`.
- **Used by**: `localExpand_preΨ_u_gen_leadingCoeff`.
- **Visibility**: private
- **Lines**: L596–L607 (12 lines)

---

### `private lemma orderTop_two_ls`
- **Type**: `(h2 : (2 : F) ≠ 0) → ((2 : LaurentSeries F)).orderTop = ↑(0 : ℤ)`
- **What**: orderTop of `2` in `LaurentSeries F` is `0` (in char ≠ 2).
- **How**: Identifies `(2 : LaurentSeries F)` with `algebraMap F (LaurentSeries F) 2` then with `HahnSeries.single 0 2`, and uses `HahnSeries.orderTop_single h2`.
- **Hypotheses**: `(2 : F) ≠ 0`.
- **Uses from project**: none.
- **Used by**: `two_ls_ne_zero`, `localExpand_mulByInt_y_orderTop_of_rhs`, `localExpand_mulByInt_y_leadingCoeff_of_rhs`.
- **Visibility**: private
- **Lines**: L608–L617 (10 lines)

---

### `private lemma leadingCoeff_two_ls`
- **Type**: `((2 : LaurentSeries F)).leadingCoeff = (2 : F)`
- **What**: Leading coefficient of `2 : LaurentSeries F` is `2 : F`.
- **How**: Same identification as `orderTop_two_ls` but using `HahnSeries.leadingCoeff_of_single`.
- **Hypotheses**: None.
- **Uses from project**: none.
- **Used by**: `localExpand_mulByInt_y_leadingCoeff_of_rhs`.
- **Visibility**: private
- **Lines**: L618–L627 (10 lines)

---

### `private lemma two_ls_ne_zero`
- **Type**: `(h2 : (2 : F) ≠ 0) → (2 : LaurentSeries F) ≠ 0`
- **What**: `2 : LaurentSeries F` is nonzero in char ≠ 2.
- **How**: Contradiction via `orderTop_two_ls` (orderTop = 0 ≠ ⊤ = orderTop(0)).
- **Hypotheses**: `(2 : F) ≠ 0`.
- **Uses from project**: `orderTop_two_ls`.
- **Used by**: **unused in file** (not called by any declaration in this file).
- **Visibility**: private
- **Lines**: L628–L634 (7 lines)
- **Notes**: Dead code candidate within this file.

---

### `private lemma localExpand_ΨSq_ff_sq_orderTop`
- **Type**: `(n : ℤ) → (n : F) ≠ 0 → ((localExpand W (ΨSq_ff W n))^2).orderTop = ↑(-4 * n.natAbs^2 + 4)`
- **What**: orderTop of `localExpand(ΨSq_n)^2` equals `-4n^2+4`.
- **How**: Uses `pow_two`, `HahnSeries.orderTop_mul`, `localExpand_ΨSq_ff_orderTop` twice, then arithmetic.
- **Hypotheses**: `(n : F) ≠ 0`.
- **Uses from project**: `localExpand_ΨSq_ff_orderTop`.
- **Used by**: `localExpand_mulByInt_y_orderTop_of_rhs`, `localExpand_a3_ΨSq_sq_orderTop_ge`.
- **Visibility**: private
- **Lines**: L635–L658 (24 lines)

---

### `private lemma localExpand_mulByInt_y_orderTop_of_rhs`
- **Type**: `... (hRHS_ord : (localExpand W RHS).orderTop = ↑(-4*n.natAbs^2+1)) → (localExpand W (mulByInt_y W n)).orderTop = ↑(-3)`
- **What**: Witness-parametric lemma: given that the RHS of `two_mulByInt_y_ΨSq_sq_eq` under `localExpand` has orderTop `-4n^2+1`, solves for `localExpand(mulByInt_y W n).orderTop = -3`.
- **How**: Applies `two_mulByInt_y_ΨSq_sq_eq`, takes `localExpand` of both sides, uses `HahnSeries.orderTop_mul` three times (for `2`, `Y`, `Q^2`), then lifts `Y.orderTop` from `WithTop ℤ` using `WithTop.coe_inj` and solves by `omega`.
- **Hypotheses**: `n ≠ 0`, `(n : F) ≠ 0`, char ≠ 2, plus the RHS orderTop hypothesis.
- **Uses from project**: `two_mulByInt_y_ΨSq_sq_eq`, `localExpand_ΨSq_ff_orderTop`, `localExpand_ΨSq_ff_sq_orderTop`, `orderTop_two_ls`.
- **Used by**: `localExpand_mulByInt_y_orderTop`.
- **Visibility**: private
- **Lines**: L659–L714 (56 lines)
- **Notes**: Proof >30 lines (53 lines). Uses `lift Y.orderTop to ℤ using hY_ord_ne` — a clever `WithTop` lift pattern.

---

### `private lemma localExpand_mulByInt_y_leadingCoeff_of_rhs`
- **Type**: `... (hRHS_lead : (localExpand W RHS).leadingCoeff = -(2*(n:F))) → (localExpand W (mulByInt_y W n)).leadingCoeff = -((n:F)^3)⁻¹`
- **What**: Witness-parametric lemma: given the RHS leading coefficient is `-2n`, solves for `localExpand(mulByInt_y W n).leadingCoeff = -1/n^3`.
- **How**: Same structure as the orderTop variant; uses `HahnSeries.leadingCoeff_mul` three times, `leadingCoeff_two_ls`, `localExpand_ΨSq_ff_leadingCoeff` (indirectly via `hQsq_lead`), then `field_simp` + `linear_combination`.
- **Hypotheses**: `n ≠ 0`, `(n : F) ≠ 0`, char ≠ 2, plus the RHS leadingCoeff hypothesis.
- **Uses from project**: `two_mulByInt_y_ΨSq_sq_eq`, `localExpand_ΨSq_ff_leadingCoeff`, `leadingCoeff_two_ls`.
- **Used by**: `localExpand_mulByInt_y_leadingCoeff`.
- **Visibility**: private
- **Lines**: L715–L759 (45 lines)
- **Notes**: Proof >30 lines (43 lines).

---

### `private lemma localExpand_preΨ_u_gen_orderTop`
- **Type**: `(n : ℤ) → ((2*n:ℤ):F) ≠ 0 → (2:F) ≠ 0 → (localExpand W (algebraMap (Polynomial F) KE (W.preΨ (2*n)) * u_gen W)).orderTop = ↑(-4*n.natAbs^2+1)`
- **What**: orderTop of `localExpand(preΨ(2n) · u_gen)` equals `-4n^2+1 = (-4n^2+4) + (-3)`.
- **How**: `map_mul`, `HahnSeries.orderTop_mul`, `localExpand_preΨ_2n_orderTop`, `localExpand_u_gen_orderTop`, arithmetic.
- **Hypotheses**: `(2n : F) ≠ 0`, char ≠ 2.
- **Uses from project**: `localExpand_preΨ_2n_orderTop`, `localExpand_u_gen_orderTop`.
- **Used by**: `localExpand_rhs_two_mulByInt_y_ΨSq_sq_orderTop`, `localExpand_rhs_two_mulByInt_y_ΨSq_sq_leadingCoeff`.
- **Visibility**: private
- **Lines**: L760–L770 (11 lines)

---

### `private lemma localExpand_preΨ_u_gen_leadingCoeff`
- **Type**: `(n : ℤ) → ((2*n:ℤ):F) ≠ 0 → (2:F) ≠ 0 → (localExpand W (algebraMap (Polynomial F) KE (W.preΨ (2*n)) * u_gen W)).leadingCoeff = -(2*(n:F))`
- **What**: Leading coefficient of `localExpand(preΨ(2n) · u_gen)` is `-2n`.
- **How**: `map_mul`, `HahnSeries.leadingCoeff_mul`, `localExpand_preΨ_2n_leadingCoeff` (gives n), `localExpand_u_gen_leadingCoeff` (gives -2), then `ring`.
- **Hypotheses**: `(2n : F) ≠ 0`, char ≠ 2.
- **Uses from project**: `localExpand_preΨ_2n_leadingCoeff`, `localExpand_u_gen_leadingCoeff`.
- **Used by**: `localExpand_rhs_two_mulByInt_y_ΨSq_sq_leadingCoeff`.
- **Visibility**: private
- **Lines**: L771–L779 (9 lines)

---

### `private lemma localExpand_a1_Φ_ΨSq_orderTop_ge`
- **Type**: `(n : ℤ) → n ≠ 0 → (n : F) ≠ 0 → ↑(-4*n.natAbs^2+2) ≤ (localExpand W (algebraMap F KE W.a₁ * Φ_ff W n * ΨSq_ff W n)).orderTop`
- **What**: orderTop of `localExpand(a₁ · Φ · ΨSq)` is at least `-4n^2+2` (strictly higher than `-4n^2+1` of the dominant term).
- **How**: Cases `a₁ = 0` (trivial, ⊤) and `a₁ ≠ 0`: uses `HahnSeries.orderTop_mul` twice with `localExpand_const`, `localExpand_Φ_ff_orderTop`, `localExpand_ΨSq_ff_orderTop`, then `WithTop.coe_le_coe` + arithmetic.
- **Hypotheses**: `n ≠ 0`, `(n : F) ≠ 0`.
- **Uses from project**: `localExpand_const`, `localExpand_Φ_ff_orderTop`, `localExpand_ΨSq_ff_orderTop`.
- **Used by**: `localExpand_rhs_two_mulByInt_y_ΨSq_sq_orderTop`, `localExpand_rhs_two_mulByInt_y_ΨSq_sq_leadingCoeff`.
- **Visibility**: private
- **Lines**: L780–L804 (25 lines)

---

### `private lemma localExpand_a3_ΨSq_sq_orderTop_ge`
- **Type**: `(n : ℤ) → (n : F) ≠ 0 → ↑(-4*n.natAbs^2+4) ≤ (localExpand W (algebraMap F KE W.a₃ * (ΨSq_ff W n)^2)).orderTop`
- **What**: orderTop of `localExpand(a₃ · ΨSq^2)` is at least `-4n^2+4`.
- **How**: Cases `a₃ = 0` and `a₃ ≠ 0`; uses `localExpand_const`, `localExpand_ΨSq_ff_sq_orderTop`, `HahnSeries.orderTop_mul`.
- **Hypotheses**: `(n : F) ≠ 0`.
- **Uses from project**: `localExpand_const`, `localExpand_ΨSq_ff_sq_orderTop`.
- **Used by**: `localExpand_rhs_two_mulByInt_y_ΨSq_sq_orderTop`, `localExpand_rhs_two_mulByInt_y_ΨSq_sq_leadingCoeff`.
- **Visibility**: private
- **Lines**: L805–L823 (19 lines)

---

### `private lemma localExpand_rhs_two_mulByInt_y_ΨSq_sq_orderTop`
- **Type**: `... (h2nF : ((2*n:ℤ):F) ≠ 0) → (localExpand W (preΨ(2n)*u_gen - a₁*Φ*ΨSq - a₃*ΨSq^2)).orderTop = ↑(-4*n.natAbs^2+1)`
- **What**: The full RHS of `two_mulByInt_y_ΨSq_sq_eq` under `localExpand` has orderTop `-4n^2+1`, dominated by the `preΨ(2n)*u_gen` term.
- **How**: Rewrites the subtraction as `A + (-B + -C)`, applies `map_add/map_neg`, uses `localExpand_preΨ_u_gen_orderTop` (A.orderTop = -4n²+1), `localExpand_a1_Φ_ΨSq_orderTop_ge` + `localExpand_a3_ΨSq_sq_orderTop_ge` (B, C.orderTop ≥ -4n²+2), `HahnSeries.min_orderTop_le_orderTop_add`, `HahnSeries.orderTop_add_eq_left`.
- **Hypotheses**: `n ≠ 0`, `(n : F) ≠ 0`, char ≠ 2, `(2n : F) ≠ 0`.
- **Uses from project**: `localExpand_preΨ_u_gen_orderTop`, `localExpand_a1_Φ_ΨSq_orderTop_ge`, `localExpand_a3_ΨSq_sq_orderTop_ge`.
- **Used by**: `localExpand_mulByInt_y_orderTop`.
- **Visibility**: private
- **Lines**: L824–L864 (41 lines)
- **Notes**: Proof >30 lines (39 lines). Structure mirrors `localExpand_rhs_two_mulByInt_y_ΨSq_sq_leadingCoeff`.

---

### `private lemma localExpand_rhs_two_mulByInt_y_ΨSq_sq_leadingCoeff`
- **Type**: `... (h2nF : ((2*n:ℤ):F) ≠ 0) → (localExpand W RHS).leadingCoeff = -(2*(n:F))`
- **What**: The leadingCoeff of the same RHS is `-2n`, coming from the dominant `preΨ(2n)*u_gen` term.
- **How**: Same structure (rewrite as `A + (-B + -C)`, prove A dominates, use `HahnSeries.leadingCoeff_add_eq_left`).
- **Hypotheses**: `n ≠ 0`, `(n : F) ≠ 0`, char ≠ 2, `(2n : F) ≠ 0`.
- **Uses from project**: `localExpand_preΨ_u_gen_orderTop`, `localExpand_preΨ_u_gen_leadingCoeff`, `localExpand_a1_Φ_ΨSq_orderTop_ge`, `localExpand_a3_ΨSq_sq_orderTop_ge`.
- **Used by**: `localExpand_mulByInt_y_leadingCoeff`.
- **Visibility**: private
- **Lines**: L865–L904 (40 lines)
- **Notes**: Proof >30 lines (38 lines). Largely duplicates the orderTop dominance argument from `localExpand_rhs_two_mulByInt_y_ΨSq_sq_orderTop`.

---

### `theorem localExpand_mulByInt_y_orderTop`
- **Type**: `(n : ℤ) → n ≠ 0 → (n : F) ≠ 0 → (2 : F) ≠ 0 → ((2*n:ℤ):F) ≠ 0 → (localExpand W (mulByInt_y W n)).orderTop = ↑(-3)`
- **What**: Main lemma: orderTop of `localExpand(mulByInt_y W n)` is `-3` (matching the pole of `y` at `O`).
- **How**: Assembles `localExpand_mulByInt_y_orderTop_of_rhs` with `localExpand_rhs_two_mulByInt_y_ΨSq_sq_orderTop`.
- **Hypotheses**: `n ≠ 0`, `(n : F) ≠ 0`, char ≠ 2, `(2n : F) ≠ 0`.
- **Uses from project**: `localExpand_mulByInt_y_orderTop_of_rhs`, `localExpand_rhs_two_mulByInt_y_ΨSq_sq_orderTop`.
- **Used by**: `coeff_one_formalIsogenySeries_mulByInt`.
- **Visibility**: public
- **Lines**: L905–L912 (8 lines)

---

### `theorem localExpand_mulByInt_y_leadingCoeff`
- **Type**: `(n : ℤ) → n ≠ 0 → (n : F) ≠ 0 → (2 : F) ≠ 0 → ((2*n:ℤ):F) ≠ 0 → (localExpand W (mulByInt_y W n)).leadingCoeff = -((n:F)^3)⁻¹`
- **What**: Main lemma: leading coefficient of `localExpand(mulByInt_y W n)` is `-1/n^3`.
- **How**: Assembles `localExpand_mulByInt_y_leadingCoeff_of_rhs` with `localExpand_rhs_two_mulByInt_y_ΨSq_sq_leadingCoeff`.
- **Hypotheses**: `n ≠ 0`, `(n : F) ≠ 0`, char ≠ 2, `(2n : F) ≠ 0`.
- **Uses from project**: `localExpand_mulByInt_y_leadingCoeff_of_rhs`, `localExpand_rhs_two_mulByInt_y_ΨSq_sq_leadingCoeff`.
- **Used by**: `coeff_one_formalIsogenySeries_mulByInt`.
- **Visibility**: public
- **Lines**: L913–L930 (18 lines)

---

### `private theorem coeff_one_formalIsogenySeries_mulByInt_of_witnesses`
- **Type**: `(n : ℤ) → n ≠ 0 → (n : F) ≠ 0 → (hy_ord : ...) → (hy_lead : ...) → PowerSeries.coeff 1 (formalIsogenySeries W (mulByInt W.toAffine n)) = (n : F)`
- **What**: Witness-parametric core: given the orderTop (-3) and leadingCoeff (-1/n^3) of `localExpand(mulByInt_y W n)`, proves that the coefficient of `T^1` in the formal isogeny series of `[n]` is `n`.
- **How**: Unfolds `formalIsogenySeries_coeff` and `localParam` via `mulByInt_pullback_x/y`; then Laurent-series computation: `-X/Y` has orderTop `(-2)-(-3)=1` via `HahnSeries.orderTop_div`, leadingCoeff `-(1/n^2)/(-1/n^3) = n` via `HahnSeries.leadingCoeff_div` + `field_simp`; coeff at position 1 = leadingCoeff via `HahnSeries.leadingCoeff_of_ne_zero` + `WithTop.coe_untop`.
- **Hypotheses**: `n ≠ 0`, `(n : F) ≠ 0`, plus the two witness hypotheses.
- **Uses from project**: `formalIsogenySeries_coeff`, `localParam`, `mulByInt_pullback_x`, `mulByInt_pullback_y`, `localExpand_mulByInt_x_orderTop`, `localExpand_mulByInt_x_leadingCoeff`.
- **Used by**: `coeff_one_formalIsogenySeries_mulByInt`.
- **Visibility**: private
- **Lines**: L931–L1002 (72 lines)
- **Notes**: Proof >30 lines (57 lines). The key mathematical insight is at L969–L986: orderTop of ratio = 1 forces the series to start at degree 1, so coeff 1 = leadingCoeff.

---

### `private theorem coeff_one_formalIsogenySeries_mulByInt`
- **Type**: `(n : ℤ) → n ≠ 0 → (n : F) ≠ 0 → (h2 : (2 : F) ≠ 0) → PowerSeries.coeff 1 (formalIsogenySeries W (mulByInt W.toAffine n)) = (n : F)`
- **What**: Derives `(2n : F) ≠ 0` from `h2` and `hnF`, then assembles the proof from `coeff_one_formalIsogenySeries_mulByInt_of_witnesses` with `localExpand_mulByInt_y_orderTop/leadingCoeff`.
- **How**: `push_cast; exact mul_ne_zero h2 hnF` for the auxiliary fact; then exact application.
- **Hypotheses**: `n ≠ 0`, `(n : F) ≠ 0`, char ≠ 2.
- **Uses from project**: `coeff_one_formalIsogenySeries_mulByInt_of_witnesses`, `localExpand_mulByInt_y_orderTop`, `localExpand_mulByInt_y_leadingCoeff`.
- **Used by**: `omegaPullbackCoeff_eq_formalIsogenyLeading_of_mulByInt`.
- **Visibility**: private
- **Lines**: L1003–L1034 (32 lines)
- **Notes**: Proof 11 lines (assembly only). The 32-line count includes the long doc-comment.

---

### `theorem omegaPullbackCoeff_eq_formalIsogenyLeading_of_mulByInt`
- **Type**: `(n : ℤ) → n ≠ 0 → (n : F) ≠ 0 → (h2 : (2 : F) ≠ 0) → omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap F KE (PowerSeries.coeff 1 (formalIsogenySeries W (mulByInt W.toAffine n)))`
- **What**: T-IV-BRIDGE-001 for `[n]`: the ω-pullback coefficient of `[n]` equals (the algebraMap of) the linear coefficient of its formal isogeny series.
- **How**: Rewrites the RHS using `coeff_one_formalIsogenySeries_mulByInt` (giving `n`), then applies `bridge_mulByInt` (from `FormalGroupBridge.lean`) which gives LHS = `algebraMap F KE n`.
- **Hypotheses**: `n ≠ 0`, `(n : F) ≠ 0`, char ≠ 2.
- **Uses from project**: `coeff_one_formalIsogenySeries_mulByInt`, `bridge_mulByInt`.
- **Used by**: unused in file (the exported capstone theorem).
- **Visibility**: public
- **Lines**: L1035–L1043 (9 lines)
- **Notes**: No sorry, no maxHeartbeats. This is the main theorem of the file.
