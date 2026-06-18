# Inventory: ./HasseWeil/EC/MulByIntSamePlace.lean

**Total declarations**: 28 (0 defs, 28 theorems, 0 instances)
**Sorries**: none (0 sorry tactic/term in any body)
**set_option maxHeartbeats**: none (only linter options)
**File length**: 990 lines

---

## Imports

- `HasseWeil.EC.IsogenyOrdTransport`
- `HasseWeil.WeilPairing.TorsionGeometric`
- `HasseWeil.WeilPairing.TorsionKernelRational`
- `HasseWeil.EC.TranslateOrdInfty`
- `HasseWeil.EC.MulByIntUnramified`

---

## Purpose

Supplies the `Valuation.IsEquiv` ("same-place") inputs for `[ℓ]`:
the comap valuation `(pointValuation P).comap ([ℓ].pullback)` is IsEquiv to the place-valuation at the image `[ℓ]·P`. Two cases: affine image (fully proven, sorry-free) and torsion image `O` (also proven, sorry-free—the file header's claim of a residual sorry refers to an *earlier* version; the torsion-pole route via translation invariance is now complete).

---

## Declarations

### `private theorem mulByInt_coords_at_affine`

- **Type**: `(ℓ : ℤ) → ℓ ≠ 0 → (P : SmoothPoint) → W.Nonsingular x y → [ℓ]·P = some x y h_ns → ψ_ℓ(P) ≠ 0 ∧ x = φ_ℓ(P)/ψ_ℓ(P)² ∧ y = ω_ℓ(P)/ψ_ℓ(P)³`
- **What**: Extracts the division-polynomial coordinate formula at an affine image: if `[ℓ]·P = (x,y)` then `ψ_ℓ(P) ≠ 0` and the Jacobian coordinates give exactly `(x,y)`.
- **How**: Uses `zsmul_affine_point_eq_gen` (the main division-polynomial specialisation), combined with `WeierstrassCurve.zsmul_eq_smulEval` and `Jacobian.Point.toAffineAddEquiv` to transport the Z-coordinate zero contradiction.
- **Hypotheses**: `ℓ ≠ 0`, `P` smooth, affine image `[ℓ]·P = some x y h_ns`
- **Uses from project**: `mulByInt_apply`, `zsmul_affine_point_eq_gen`, `WeierstrassCurve.zsmul_eq_smulEval`, `SmoothPlaneCurve.SmoothPoint.toAffinePoint_def`
- **Used by**: `pointValuation_mulByInt_x_sub_lt_one`, `pointValuation_mulByInt_y_sub_lt_one`
- **Visibility**: private
- **Lines**: 83–132 (proof ~40 lines)
- **Notes**: Proof >30 lines (51 lines total).

---

### `private theorem pointValuation_aeval_sub_eval_lt_one`

- **Type**: `(P : SmoothPoint) → pointValuation P u ≤ 1 → pointValuation P (u − a) < 1 → (q : F[X]) → pointValuation P (q(u) − q(a)) < 1`
- **What**: Univariate value bridge: if `u` is regular at `P` and `u ≡ a` mod `m_P`, then `q(u) ≡ q(a)` mod `m_P` for any polynomial `q`.
- **How**: Polynomial induction (`Polynomial.induction_on`): constant case `sub_self`, additive case by strong-triangle-inequality (`map_add`), monomial step decomposes `c·u^{n+1} − c·a^{n+1}` as `u·(...) + cₙ·(u−a)` then uses `pointValuation_mul_lt_one_of_le_and_lt`.
- **Hypotheses**: `u` regular at `P`, `u ≡ a` mod `m_P`
- **Uses from project**: `pointValuation_mul_lt_one_of_le_and_lt`, `SmoothPlaneCurve.pointValuation_algebraMap_F_le_one`
- **Used by**: `pointValuation_mulByInt_x_sub_lt_one`, `pointValuation_mulByInt_y_sub_lt_one`, `pointValuation_bivariate_bridge`
- **Visibility**: private
- **Lines**: 144–183 (proof ~32 lines)
- **Notes**: Proof >30 lines (40 lines total).

---

### `private theorem pointValuation_algebraMap_sub_evalAt_lt_one`

- **Type**: `(P : SmoothPoint) → (r : CoordinateRing) → pointValuation P (algMap r − algMap_F (evalAt P r)) < 1`
- **What**: A coordinate-ring element `r` is congruent modulo `m_P` to its evaluation `evalAt P r` at `P`, because `r − evalAt(r)` lies in `ker(evalAt P) = m_P`.
- **How**: Uses `ker_evalAt` to show the difference lies in `maximalIdealAt P`, then `pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`.
- **Hypotheses**: `P` smooth, `r` in the coordinate ring
- **Uses from project**: `SmoothPlaneCurve.ker_evalAt`, `SmoothPlaneCurve.evalAt_algebraMap`, `Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`
- **Used by**: `pointValuation_mulByInt_y_sub_lt_one` (for `ω_ff`, `ψ_ff` residues)
- **Visibility**: private
- **Lines**: 187–202 (proof ~15 lines)

---

### `private theorem algebraMap_polynomial_eq_aeval_x_gen`

- **Type**: `(p : F[X]) → algebraMap (F[X]) KE p = aeval (x_gen W) p`
- **What**: The ring map `F[X] → K(E)` coincides with evaluation at the generator `x_gen`.
- **How**: Rewrites `x_gen` as the image of `Polynomial.X` under `algebraMap` via `IsScalarTower`, then uses `Polynomial.aeval_algebraMap_apply`.
- **Hypotheses**: none beyond the variable context
- **Uses from project**: `x_gen W`
- **Used by**: `Φ_ff_eq_aeval`, `ΨSq_ff_eq_aeval`
- **Visibility**: private
- **Lines**: 205–210 (proof ~5 lines)

---

### `private theorem Φ_ff_eq_aeval`

- **Type**: `(ℓ : ℤ) → Φ_ff W ℓ = aeval (x_gen W) (W.Φ ℓ)`
- **What**: The function-field division-polynomial numerator `Φ_ff` equals the polynomial `W.Φ ℓ` evaluated at `x_gen`.
- **How**: Unfolds `Φ_ff`, applies `algebraMap_polynomial_eq_aeval_x_gen` and `IsScalarTower.algebraMap_apply`.
- **Hypotheses**: none
- **Uses from project**: `Φ_ff`, `algebraMap_polynomial_eq_aeval_x_gen`
- **Used by**: `pointValuation_mulByInt_x_sub_lt_one`
- **Visibility**: private
- **Lines**: 213–216 (proof ~3 lines)

---

### `private theorem ΨSq_ff_eq_aeval`

- **Type**: `(ℓ : ℤ) → ΨSq_ff W ℓ = aeval (x_gen W) (W.ΨSq ℓ)`
- **What**: The function-field division-polynomial denominator `ΨSq_ff` equals `W.ΨSq ℓ` evaluated at `x_gen`.
- **How**: Same pattern as `Φ_ff_eq_aeval`.
- **Hypotheses**: none
- **Uses from project**: `ΨSq_ff`, `algebraMap_polynomial_eq_aeval_x_gen`
- **Used by**: `pointValuation_mulByInt_x_sub_lt_one`
- **Visibility**: private
- **Lines**: 219–222 (proof ~3 lines)

---

### `private theorem pointValuation_mulByInt_x_sub_lt_one`

- **Type**: `[IsAlgClosed F] → (ℓ : ℤ) → ℓ ≠ 0 → (P : SmoothPoint) → W.Nonsingular x y → [ℓ]·P = some x y h_ns → pointValuation P (mulByInt_x ℓ − x) < 1`
- **What**: The `x`-coordinate pullback `[ℓ]^*x_gen` is congruent modulo `m_P` to the image `x`-coordinate when `[ℓ]·P = (x,y)`.
- **How**: Extracts `ψ_ℓ(P) ≠ 0` and coordinate formulas from `mulByInt_coords_at_affine`, shows `ΨSq_ff` is a unit at `P` via `Φ_ff_eq_aeval`/`ΨSq_ff_eq_aeval` + `pointValuation_aeval_sub_eval_lt_one`, then writes `mulByInt_x ℓ − x = (Φ_ff − x·ΨSq_ff)·ΨSq_ff⁻¹` and decomposes using `evalEval_ψ_sq`, `evalEval_φ_eq_Φ`, `ΨSq_ff_ne_zero`.
- **Hypotheses**: `IsAlgClosed F`, `ℓ ≠ 0`, affine image
- **Uses from project**: `mulByInt_coords_at_affine`, `WeierstrassCurve.evalEval_ψ_sq`, `WeierstrassCurve.evalEval_φ_eq_Φ`, `ΨSq_ff_ne_zero`, `Φ_ff_eq_aeval`, `ΨSq_ff_eq_aeval`, `pointValuation_aeval_sub_eval_lt_one`, `pointValuation_x_gen_le_one`, `x_gen_sub_const_eq_algebraMap_XClass`, `XClass_mem_maximalIdealAt`, `pointValuation_algebraMap_F_eq_one_of_ne_zero`, `pointValuation_add_le_one`, `mulByInt_x`
- **Used by**: `pointValuation_mulByInt_x_le_one`, `pointValuation_mulByInt_pullback_algebraMap_sub_evalAt_lt_one`, `pointValuation_mulByInt_x_sub_lt_one_of_ne_zero`
- **Visibility**: private
- **Lines**: 226–279 (proof ~53 lines)
- **Notes**: Proof >30 lines (54 lines total).

---

### `private theorem pointValuation_mulByInt_y_sub_lt_one`

- **Type**: `[IsAlgClosed F] → (ℓ : ℤ) → ℓ ≠ 0 → (P : SmoothPoint) → W.Nonsingular x y → [ℓ]·P = some x y h_ns → pointValuation P (mulByInt_y ℓ − y) < 1`
- **What**: The `y`-coordinate pullback `[ℓ]^*y_gen` is congruent modulo `m_P` to the image `y`-coordinate.
- **How**: Residues `ω_ff ≡ ω_ℓ(P)` and `ψ_ff ≡ ψ_ℓ(P)` mod `m_P` via `pointValuation_algebraMap_sub_evalAt_lt_one`; shows `ψ_ff³` is a unit using `pointValuation_aeval_sub_eval_lt_one` on `X³`; then writes `mulByInt_y ℓ − y = (ω_ff − y·ψ_ff³)·(ψ_ff³)⁻¹` and bounds the numerator using `ψ_ff_ne_zero`, `hxy_eq`, strong triangle.
- **Hypotheses**: `IsAlgClosed F`, `ℓ ≠ 0`, affine image
- **Uses from project**: `mulByInt_coords_at_affine`, `pointValuation_algebraMap_sub_evalAt_lt_one`, `ψ_ff_ne_zero`, `pointValuation_aeval_sub_eval_lt_one`, `pointValuation_algebraMap_F_eq_one_of_ne_zero`, `pointValuation_add_le_one`, `pointValuation_mul_lt_one_of_le_and_lt`, `mulByInt_y`, `ω_ff`, `ψ_ff`
- **Used by**: `pointValuation_mulByInt_y_le_one`, `pointValuation_mulByInt_pullback_algebraMap_sub_evalAt_lt_one`, `pointValuation_mulByInt_y_sub_lt_one_of_ne_zero`
- **Visibility**: private
- **Lines**: 283–350 (proof ~67 lines)
- **Notes**: Proof >30 lines (68 lines total). The longest of the generator bridge proofs.

---

### `private theorem pointValuation_bivariate_bridge`

- **Type**: `(P : SmoothPoint) → u ≡ a, v ≡ b mod m_P (both regular) → (p : F[X][X]) → pointValuation P (p(u,v) − p(a,b)) < 1`
- **What**: Bivariate polynomial value bridge: if `u ≡ a` and `v ≡ b` modulo `m_P`, then any `F[X][X]`-polynomial `p` satisfies `p(u,v) ≡ p(a,b)` modulo `m_P`.
- **How**: Outer induction on `p` using `Polynomial.induction_on`: constant case reduces to `pointValuation_aeval_sub_eval_lt_one` in `u`; additive case by triangle; monomial step decomposes `Au·v − Ab·b = Au·(v−b) + b·(Au−Ab)` and uses `pointValuation_mul_lt_one_of_le_and_lt`.
- **Hypotheses**: `u` regular at `P`, `u ≡ a` mod `m_P`; `v` regular at `P`, `v ≡ b` mod `m_P`
- **Uses from project**: `pointValuation_aeval_sub_eval_lt_one`, `pointValuation_mul_lt_one_of_le_and_lt`, `pointValuation_add_le_one`, `SmoothPlaneCurve.pointValuation_algebraMap_F_le_one`
- **Used by**: `pointValuation_mulByInt_pullback_algebraMap_sub_evalAt_lt_one`
- **Visibility**: private
- **Lines**: 362–417 (proof ~55 lines)
- **Notes**: Proof >30 lines (56 lines total).

---

### `private theorem mulByInt_pullback_algebraMap_mk_eq`

- **Type**: `(ℓ : ℤ) → ℓ ≠ 0 → (p : F[X][X]) → [ℓ].pullback(algMap(mk p)) = p(mulByInt_x ℓ, mulByInt_y ℓ)`
- **What**: The comorphism `[ℓ].pullback` on a coordinate-ring generator `mk p` is evaluation of `p` at the division coordinate functions `(mulByInt_x ℓ, mulByInt_y ℓ)`.
- **How**: Unfolds `mulByInt` and identifies `pullback` with `mulByInt_pullbackAlgHom` via `IsLocalization.lift_eq`; then `AdjoinRoot.lift_mk` reduces to `eval₂_eval₂RingHom_apply`.
- **Hypotheses**: `ℓ ≠ 0`
- **Uses from project**: `mulByInt_pullbackAlgHom`, `mulByInt_coordHom`, `mulByInt_xHom`, `mulByInt_y`, `mulByInt_weierstrass`, `mulByInt_x`
- **Used by**: `pointValuation_mulByInt_pullback_algebraMap_sub_evalAt_lt_one`
- **Visibility**: private
- **Lines**: 422–437 (proof ~15 lines)

---

### `private theorem pointValuation_mulByInt_x_le_one`

- **Type**: `[IsAlgClosed F] → (ℓ : ℤ) → (ℓ : F) ≠ 0 → ... → pointValuation P (mulByInt_x ℓ) ≤ 1`
- **What**: `[ℓ]^*x_gen` is regular at `P` when `[ℓ]·P` is affine.
- **How**: Writes `mulByInt_x ℓ = (mulByInt_x ℓ − x) + x` and applies `pointValuation_add_le_one` to the `x`-bridge and the constant bound.
- **Hypotheses**: `IsAlgClosed F`, `(ℓ : F) ≠ 0`, affine image
- **Uses from project**: `pointValuation_mulByInt_x_sub_lt_one`, `pointValuation_add_le_one`, `SmoothPlaneCurve.pointValuation_algebraMap_F_le_one`
- **Used by**: `pointValuation_mulByInt_pullback_algebraMap_sub_evalAt_lt_one`
- **Visibility**: private
- **Lines**: 440–449 (proof ~9 lines)

---

### `private theorem pointValuation_mulByInt_y_le_one`

- **Type**: `[IsAlgClosed F] → (ℓ : ℤ) → (ℓ : F) ≠ 0 → ... → pointValuation P (mulByInt_y ℓ) ≤ 1`
- **What**: `[ℓ]^*y_gen` is regular at `P` when `[ℓ]·P` is affine.
- **How**: Same pattern as `pointValuation_mulByInt_x_le_one`.
- **Hypotheses**: same as above
- **Uses from project**: `pointValuation_mulByInt_y_sub_lt_one`, `pointValuation_add_le_one`, `SmoothPlaneCurve.pointValuation_algebraMap_F_le_one`
- **Used by**: `pointValuation_mulByInt_pullback_algebraMap_sub_evalAt_lt_one`
- **Visibility**: private
- **Lines**: 452–461 (proof ~9 lines)

---

### `private theorem pointValuation_mulByInt_pullback_algebraMap_sub_evalAt_lt_one`

- **Type**: `[IsAlgClosed F] → (ℓ : ℤ) → (ℓ : F) ≠ 0 → ... → (r : CoordinateRing) → pointValuation P ([ℓ].pullback(algMap r) − algMap_F(evalAt Q r)) < 1`
- **What**: For any coordinate-ring element `r`, the pullback `[ℓ]^*(algMap r)` is congruent to the value of `r` at the image point `Q` modulo `m_P`.
- **How**: Surjects `r = mk p`; rewrites pullback via `mulByInt_pullback_algebraMap_mk_eq`; reduces to `pointValuation_bivariate_bridge` with generators `mulByInt_x/y` and bridges from `pointValuation_mulByInt_x/y_sub_lt_one` and `x/y_le_one`.
- **Hypotheses**: `IsAlgClosed F`, `(ℓ : F) ≠ 0`, affine image
- **Uses from project**: `mulByInt_pullback_algebraMap_mk_eq`, `pointValuation_bivariate_bridge`, `pointValuation_mulByInt_x_le_one`, `pointValuation_mulByInt_y_le_one`, `pointValuation_mulByInt_x_sub_lt_one`, `pointValuation_mulByInt_y_sub_lt_one`, `Curves.SmoothPlaneCurve.evalAt_mk`
- **Used by**: `pointValuation_mulByInt_pullback_algebraMap_le_one`, `pointValuation_mulByInt_pullback_algebraMap_eq_one_of_notMem`, `pointValuation_mulByInt_pullback_algebraMap_lt_one_of_mem`
- **Visibility**: private
- **Lines**: 467–485 (proof ~18 lines)

---

### `private theorem pointValuation_mulByInt_pullback_algebraMap_le_one`

- **Type**: `[IsAlgClosed F] → ... → (r : CoordinateRing) → pointValuation P ([ℓ].pullback(algMap r)) ≤ 1`
- **What**: **(A) Regularity**: any `[ℓ]^*(algMap r)` is regular at `P` when `[ℓ]·P` is affine.
- **How**: Splits as `([ℓ]^*(algMap r) − evalAt Q r) + evalAt Q r` and applies `pointValuation_add_le_one`.
- **Hypotheses**: `IsAlgClosed F`, `(ℓ : F) ≠ 0`, affine image
- **Uses from project**: `pointValuation_mulByInt_pullback_algebraMap_sub_evalAt_lt_one`, `pointValuation_add_le_one`, `SmoothPlaneCurve.pointValuation_algebraMap_F_le_one`
- **Used by**: `pointValuation_mulByInt_pullback_le_one_of_le_one`
- **Visibility**: private
- **Lines**: 488–504 (proof ~16 lines)

---

### `private theorem pointValuation_mulByInt_pullback_algebraMap_eq_one_of_notMem`

- **Type**: `[IsAlgClosed F] → ... → r ∉ maximalIdealAt Q → pointValuation P ([ℓ].pullback(algMap r)) = 1`
- **What**: **(B′) Unit transfer**: if `r` is a unit at `Q` (not in `m_Q`), then `[ℓ]^*(algMap r)` is a unit at `P`.
- **How**: `r ∉ m_Q` gives `evalAt Q r ≠ 0`; the residue `algMap(evalAt Q r)` has valuation 1; the split via `map_add_eq_of_lt_right` and the congruence lemma finishes.
- **Hypotheses**: `IsAlgClosed F`, `(ℓ : F) ≠ 0`, affine image, `r` a unit at `Q`
- **Uses from project**: `pointValuation_mulByInt_pullback_algebraMap_sub_evalAt_lt_one`, `pointValuation_algebraMap_F_eq_one_of_ne_zero`, `SmoothPlaneCurve.ker_evalAt`
- **Used by**: `pointValuation_mulByInt_pullback_le_one_of_le_one`, `pointValuation_mulByInt_pullback_lt_one_of_lt_one`
- **Visibility**: private
- **Lines**: 507–530 (proof ~23 lines)

---

### `private theorem pointValuation_mulByInt_pullback_algebraMap_lt_one_of_mem`

- **Type**: `[IsAlgClosed F] → ... → r ∈ maximalIdealAt Q → pointValuation P ([ℓ].pullback(algMap r)) < 1`
- **What**: **(B) Vanishing transfer**: if `r ∈ m_Q`, then `[ℓ]^*(algMap r) ∈ m_P`.
- **How**: `r ∈ m_Q` gives `evalAt Q r = 0` via `ker_evalAt`; the sub-0 term vanishes, leaving just the residue sub-statement.
- **Hypotheses**: `IsAlgClosed F`, `(ℓ : F) ≠ 0`, affine image, `r ∈ m_Q`
- **Uses from project**: `pointValuation_mulByInt_pullback_algebraMap_sub_evalAt_lt_one`, `SmoothPlaneCurve.ker_evalAt`
- **Used by**: `pointValuation_mulByInt_pullback_lt_one_of_lt_one`
- **Visibility**: private
- **Lines**: 533–545 (proof ~12 lines)

---

### `private theorem pointValuation_mulByInt_pullback_le_one_of_le_one`

- **Type**: `[IsAlgClosed F] → ... → pointValuation Q g ≤ 1 → pointValuation P ([ℓ].pullback g) ≤ 1`
- **What**: Forward regularity transfer: if `g` is regular at the affine image `Q`, then `[ℓ]^*g` is regular at `P`.
- **How**: Writes `g = u/v` using `IsLocalization.surj` on the local ring at `Q`; the denominator `v ∉ m_Q` gives `[ℓ]^*(algMap v)` a unit via the unit-transfer lemma; numerator `[ℓ]^*(algMap u)` is regular by the regularity-transfer lemma; combine with `map_div₀`.
- **Hypotheses**: `IsAlgClosed F`, `(ℓ : F) ≠ 0`, affine image, `g` regular at `Q`
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one`, `pointValuation_mulByInt_pullback_algebraMap_eq_one_of_notMem`, `pointValuation_mulByInt_pullback_algebraMap_le_one`, `SmoothPlaneCurve.maximalIdealAt_isMaximal`, `SmoothPlaneCurve.pointValuation_algebraMap_le_one`
- **Used by**: `mulByInt_samePlace_le_one_iff_affine`
- **Visibility**: private
- **Lines**: 549–580 (proof ~31 lines)
- **Notes**: Proof >30 lines (32 lines total).

---

### `private theorem pointValuation_mulByInt_pullback_lt_one_of_lt_one`

- **Type**: `[IsAlgClosed F] → ... → pointValuation Q g < 1 → pointValuation P ([ℓ].pullback g) < 1`
- **What**: Forward vanishing transfer: if `g ∈ m_Q`, then `[ℓ]^*g ∈ m_P`.
- **How**: Same `IsLocalization.surj` decomposition `g = u/v`; shows `v` is a unit at `Q` (valuation = 1, not in `m_Q`), then `u ∈ m_Q` (from `pV_Q(algMap u) = pV_Q(g) < 1`); combines `algebraMap_lt_one_of_mem` + unit-transfer for denominator.
- **Hypotheses**: `IsAlgClosed F`, `(ℓ : F) ≠ 0`, affine image, `g ∈ m_Q`
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one`, `pointValuation_mulByInt_pullback_algebraMap_eq_one_of_notMem`, `pointValuation_mulByInt_pullback_algebraMap_lt_one_of_mem`, `SmoothPlaneCurve.maximalIdealAt_isMaximal`, `SmoothPlaneCurve.pointValuation_algebraMap_le_one`, `SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`
- **Used by**: `mulByInt_samePlace_le_one_iff_affine`
- **Visibility**: private
- **Lines**: 583–628 (proof ~45 lines)
- **Notes**: Proof >30 lines (46 lines total).

---

### `theorem mulByInt_samePlace_le_one_iff_affine`

- **Type**: `[IsAlgClosed F] → (ℓ : ℤ) → (ℓ : F) ≠ 0 → (P : SmoothPoint) → W.Nonsingular x y → [ℓ]·P = some x y h_ns → (g : FunctionField) → pointValuation P ([ℓ].pullback g) ≤ 1 ↔ pointValuation ⟨x,y,h_ns⟩ g ≤ 1`
- **What**: Same-place equivalence for the affine-image case: `[ℓ]^*g` is regular at `P` iff `g` is regular at the affine image `Q = [ℓ]·P`. Proven sorry-free and axiom-clean.
- **How**: The `←` direction is `pointValuation_mulByInt_pullback_le_one_of_le_one`. The `→` direction is the contrapositive: if `pV_Q g > 1` then `pV_Q g⁻¹ < 1`, so `[ℓ]^*(g⁻¹) ∈ m_P` by `pointValuation_mulByInt_pullback_lt_one_of_lt_one`; but `[ℓ]^*g · [ℓ]^*(g⁻¹) = 1` forces `pV_P([ℓ]^*g) ≥ 1` to be inconsistent with the strict product bound.
- **Hypotheses**: `IsAlgClosed F`, `(ℓ : F) ≠ 0`, affine image
- **Uses from project**: `pointValuation_mulByInt_pullback_le_one_of_le_one`, `pointValuation_mulByInt_pullback_lt_one_of_lt_one`
- **Used by**: `mulByInt_comap_pointValuation_isEquiv_affine`; also referenced in module doc header
- **Visibility**: public
- **Lines**: 640–672 (proof ~32 lines)
- **Notes**: Proof >30 lines (33 lines total).

---

### `private theorem ord_algebraMap_mul_ge_aux'`

- **Type**: `(c : F) → n ≤ ordAtInfty f → n ≤ ordAtInfty (algMap_F c · f)`
- **What**: Auxiliary: `ordAtInfty(c·f) ≥ n` when `ordAtInfty f ≥ n` (constants are units at `∞`).
- **How**: Case split on `c = 0` and `f = 0`; in the non-zero case uses `ordAtInfty_mul` + `ordAtInfty_algebraMap_F_nonzero` to add zero.
- **Hypotheses**: `n ≤ ordAtInfty f`
- **Uses from project**: `SmoothPlaneCurve.ordAtInfty_mul`, `SmoothPlaneCurve.ordAtInfty_zero`, `SmoothPlaneCurve.ordAtInfty_algebraMap_F_nonzero`
- **Used by**: `ordAtInfty_mulByInt_y_eq_neg_three_general` (6 times)
- **Visibility**: private
- **Lines**: 687–698 (proof ~11 lines)

---

### `private theorem ord_add_ge_of_both_ge_aux'`

- **Type**: `n ≤ ordAtInfty f → n ≤ ordAtInfty g → n ≤ ordAtInfty (f + g)`
- **What**: Auxiliary: if both `f` and `g` have pole order `≥ n` at `∞`, so does their sum.
- **How**: `le_trans (le_min hf hg) ordAtInfty_add_ge_min`.
- **Hypotheses**: bounds on `ordAtInfty f` and `ordAtInfty g`
- **Uses from project**: `SmoothPlaneCurve.ordAtInfty_add_ge_min`
- **Used by**: `ordAtInfty_mulByInt_y_eq_neg_three_general`
- **Visibility**: private
- **Lines**: 702–707 (proof ~5 lines)

---

### `theorem ordAtInfty_mulByInt_y_eq_neg_three_general`

- **Type**: `(ℓ : ℤ) → ℓ ≠ 0 → (ℓ : F) ≠ 0 → ordAtInfty (mulByInt_y W ℓ) = −3`
- **What**: The `∞`-order of the `y`-division function is exactly `−3`. Proven purely from the curve equation and `ordAtInfty(mulByInt_x ℓ) = −2`, without assuming `IsAlgClosed`.
- **How**: From `pullback_equation` the pair `(mulByInt_x, mulByInt_y)` satisfies the Weierstrass equation. The RHS has `ordAtInfty = −6` (dominant term `X³`). Progressively sharper steps via `ordAtInfty_add_eq_of_lt` identify ord_∞ of LHS with `2·ord_∞(Y)`. Constraint `m ≤ −3` from below and `m ≥ −3` from leading-term dominance, then `omega` gives `m = −3`.
- **Hypotheses**: `ℓ ≠ 0`, `(ℓ : F) ≠ 0`
- **Uses from project**: `ordAtInfty_mulByInt_x`, `mulByInt_x_ne_zero`, `pullback_equation`, `mulByInt_pullback_x`, `mulByInt_pullback_y`, `ord_algebraMap_mul_ge_aux'`, `ord_add_ge_of_both_ge_aux'`, `SmoothPlaneCurve.ordAtInfty_add_eq_of_lt`, `SmoothPlaneCurve.ordAtInfty_mul`, `SmoothPlaneCurve.ord_pow_concrete`, `SmoothPlaneCurve.ordAtInfty_eq_top_iff`, `SmoothPlaneCurve.ordAtInfty_zero`, `SmoothPlaneCurve.ordAtInfty_algebraMap_F_nonzero`
- **Used by**: `ord_P_mulByInt_y_eq_neg_three_of_torsion`
- **Visibility**: public
- **Lines**: 712–841 (proof ~129 lines)
- **Notes**: By far the longest proof in the file (130 lines). Complex ord-at-infinity arithmetic by case analysis with many intermediate steps.

---

### `private theorem mulByInt_neg_mem_kernel_of_torsion'`

- **Type**: `(ℓ : ℤ) → (P : SmoothPoint) → [ℓ]·P = 0 → −P.toAffinePoint ∈ ker[ℓ]`
- **What**: If `P` is `ℓ`-torsion, then `−P` lies in the kernel of `[ℓ]`.
- **How**: One line: `map_neg` + `hQ.neg_zero` via `Isogeny.mem_kernel_iff`.
- **Hypotheses**: `[ℓ]·P = 0`
- **Uses from project**: `HasseWeil.Isogeny.mem_kernel_iff`
- **Used by**: `ord_P_mulByInt_x_eq_neg_two_of_torsion`, `ord_P_mulByInt_y_eq_neg_three_of_torsion`
- **Visibility**: private
- **Lines**: 844–848 (proof ~4 lines)

---

### `theorem ord_P_mulByInt_x_eq_neg_two_of_torsion`

- **Type**: `(ℓ : ℤ) → ℓ ≠ 0 → (ℓ : F) ≠ 0 → (P : SmoothPoint) → [ℓ]·P = 0 → ord_P P (mulByInt_x ℓ) = −2`
- **What**: At an `ℓ`-torsion point `P` (with `[ℓ]·P = O`), the `x`-division function has order `−2` at `P`.
- **How**: Sets `k = −P`; uses `mulByInt_neg_mem_kernel_of_torsion'` to see `k ∈ ker[ℓ]`, hence `mulByInt_x ℓ` is `k`-translation-invariant (`hxy_mulByInt`); `isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint` provides compatibility; `ord_P_eq_ordAtInfty_of_invariant_and_compatible` transports `ordAtInfty(mulByInt_x ℓ) = −2` to `ord_P P = −2`.
- **Hypotheses**: `ℓ ≠ 0`, `(ℓ : F) ≠ 0`, `[ℓ]·P = 0`
- **Uses from project**: `mulByInt_neg_mem_kernel_of_torsion'`, `isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint`, `WeilPairing.TorsionGeometric.hxy_mulByInt`, `ord_P_eq_ordAtInfty_of_invariant_and_compatible`, `ordAtInfty_mulByInt_x`
- **Used by**: `comap_pointValuation_mulByInt_eq_infty`
- **Visibility**: public
- **Lines**: 853–864 (proof ~11 lines)

---

### `theorem ord_P_mulByInt_y_eq_neg_three_of_torsion`

- **Type**: `(ℓ : ℤ) → ℓ ≠ 0 → (ℓ : F) ≠ 0 → (P : SmoothPoint) → [ℓ]·P = 0 → ord_P P (mulByInt_y ℓ) = −3`
- **What**: At an `ℓ`-torsion point `P`, the `y`-division function has order `−3` at `P`.
- **How**: Same transport pattern as the `x` case, using `ordAtInfty_mulByInt_y_eq_neg_three_general` in place of `ordAtInfty_mulByInt_x`.
- **Hypotheses**: `ℓ ≠ 0`, `(ℓ : F) ≠ 0`, `[ℓ]·P = 0`
- **Uses from project**: `mulByInt_neg_mem_kernel_of_torsion'`, `isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint`, `WeilPairing.TorsionGeometric.hxy_mulByInt`, `ord_P_eq_ordAtInfty_of_invariant_and_compatible`, `ordAtInfty_mulByInt_y_eq_neg_three_general`
- **Used by**: `comap_pointValuation_mulByInt_eq_infty`
- **Visibility**: public
- **Lines**: 868–879 (proof ~11 lines)

---

### `theorem comap_pointValuation_mulByInt_eq_infty`

- **Type**: `[IsAlgClosed F] → (ℓ : ℤ) → (ℓ : F) ≠ 0 → (P : SmoothPoint) → [ℓ]·P = 0 → (pointValuation P).comap([ℓ].pullback) = ordAtInftyValuation`
- **What**: When `[ℓ]·P = O`, the comap valuation at `P` via `[ℓ]` equals the infinity valuation. This is the key torsion-image same-place identity.
- **How**: Uses `eq_ordAtInftyValuation_of_x_y`: checks the comap sends `x_gen` to `exp(2)` (via `ord_P_mulByInt_x_eq_neg_two_of_torsion` + `pointValuation_eq_exp_neg_of_ord_P_eq`), `y_gen` to `exp(3)` (similarly), and constants to `1`; these three conditions uniquely determine the valuation.
- **Hypotheses**: `IsAlgClosed F`, `(ℓ : F) ≠ 0`, `[ℓ]·P = 0`
- **Uses from project**: `mulByInt_pullback_x`, `mulByInt_pullback_y`, `ord_P_mulByInt_x_eq_neg_two_of_torsion`, `ord_P_mulByInt_y_eq_neg_three_of_torsion`, `pointValuation_eq_exp_neg_of_ord_P_eq`, `mulByInt_x_ne_zero`, `pointValuation_algebraMap_F_eq_one_of_ne_zero`, `eq_ordAtInftyValuation_of_x_y`
- **Used by**: `mulByInt_samePlace_le_one_iff_infty`
- **Visibility**: public
- **Lines**: 884–912 (proof ~28 lines)

---

### `theorem mulByInt_samePlace_le_one_iff_infty`

- **Type**: `[IsAlgClosed F] → (ℓ : ℤ) → (ℓ : F) ≠ 0 → (P : SmoothPoint) → [ℓ]·P = 0 → (g : FunctionField) → pointValuation P ([ℓ].pullback g) ≤ 1 ↔ ordAtInftyValuation g ≤ 1`
- **What**: Same-place equivalence for the torsion-image case: `[ℓ]^*g` is regular at `P` iff `g` is regular at `∞`. Proven axiom-clean.
- **How**: Reads directly off `comap_pointValuation_mulByInt_eq_infty`: the comap identity means the two valuations coincide, hence `≤ 1` is equivalent.
- **Hypotheses**: `IsAlgClosed F`, `(ℓ : F) ≠ 0`, `[ℓ]·P = 0`
- **Uses from project**: `comap_pointValuation_mulByInt_eq_infty`
- **Used by**: `mulByInt_comap_pointValuation_isEquiv_infty`
- **Visibility**: public
- **Lines**: 918–929 (proof ~11 lines)

---

### `theorem mulByInt_comap_pointValuation_isEquiv_affine`

- **Type**: `[IsAlgClosed F] → ... → ((pointValuation P).comap([ℓ].pullback)).IsEquiv(pointValuation ⟨x,y,h_ns⟩)`
- **What**: Packages `mulByInt_samePlace_le_one_iff_affine` into `Valuation.IsEquiv` form for the affine-image case, ready for `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`.
- **How**: `Valuation.isEquiv_of_val_le_one` + `mulByInt_samePlace_le_one_iff_affine`.
- **Hypotheses**: `IsAlgClosed F`, `(ℓ : F) ≠ 0`, affine image
- **Uses from project**: `mulByInt_samePlace_le_one_iff_affine`
- **Used by**: unused within this file (external API)
- **Visibility**: public
- **Lines**: 940–950 (proof ~10 lines)

---

### `theorem mulByInt_comap_pointValuation_isEquiv_infty`

- **Type**: `[IsAlgClosed F] → ... → ((pointValuation P).comap([ℓ].pullback)).IsEquiv(ordAtInftyValuation)`
- **What**: Packages `mulByInt_samePlace_le_one_iff_infty` into `Valuation.IsEquiv` form for the torsion-image case.
- **How**: `Valuation.isEquiv_of_val_le_one` + `mulByInt_samePlace_le_one_iff_infty`.
- **Hypotheses**: `IsAlgClosed F`, `(ℓ : F) ≠ 0`, `[ℓ]·P = 0`
- **Uses from project**: `mulByInt_samePlace_le_one_iff_infty`
- **Used by**: unused within this file (external API)
- **Visibility**: public
- **Lines**: 955–964 (proof ~9 lines)

---

### `theorem pointValuation_mulByInt_x_sub_lt_one_of_ne_zero`

- **Type**: `[IsAlgClosed F] → (ℓ : ℤ) → ℓ ≠ 0 → ... → pointValuation P (mulByInt_x ℓ − x) < 1`
- **What**: Public wrapper exposing the `x`-residue bridge with only `ℓ ≠ 0` (not `(ℓ : F) ≠ 0`) — the "separability-free" version, for the inseparable `p ∣ ℓ` pencil summand.
- **How**: One-line delegation to `pointValuation_mulByInt_x_sub_lt_one`.
- **Hypotheses**: `IsAlgClosed F`, `ℓ ≠ 0`, affine image
- **Uses from project**: `pointValuation_mulByInt_x_sub_lt_one`
- **Used by**: unused within this file (external API)
- **Visibility**: public
- **Lines**: 975–980 (proof 1 line)

---

### `theorem pointValuation_mulByInt_y_sub_lt_one_of_ne_zero`

- **Type**: `[IsAlgClosed F] → (ℓ : ℤ) → ℓ ≠ 0 → ... → pointValuation P (mulByInt_y ℓ − y) < 1`
- **What**: Public wrapper for the `y`-residue bridge with only `ℓ ≠ 0`, for the inseparable pencil.
- **How**: One-line delegation to `pointValuation_mulByInt_y_sub_lt_one`.
- **Hypotheses**: `IsAlgClosed F`, `ℓ ≠ 0`, affine image
- **Uses from project**: `pointValuation_mulByInt_y_sub_lt_one`
- **Used by**: unused within this file (external API)
- **Visibility**: public
- **Lines**: 983–988 (proof 1 line)

---

## Summary

| Metric | Count |
|--------|-------|
| Total declarations | 28 |
| Defs | 0 |
| Lemmas/Theorems | 28 |
| Instances | 0 |
| Sorries | 0 |
| Long proofs (>30 lines) | 10 |

**Key API** (used by 3+ others in file):
- `mulByInt_coords_at_affine` — used by 2 (x-bridge, y-bridge)
- `pointValuation_aeval_sub_eval_lt_one` — used by 3 (x-bridge, y-bridge, bivariate)
- `pointValuation_mulByInt_x_sub_lt_one` — used by 3 (x_le_one, pullback_sub, public wrapper)
- `pointValuation_mulByInt_y_sub_lt_one` — used by 3 (y_le_one, pullback_sub, public wrapper)
- `pointValuation_mulByInt_pullback_algebraMap_sub_evalAt_lt_one` — used by 3 (le_one, eq_one, lt_one)
- `pointValuation_mulByInt_pullback_algebraMap_eq_one_of_notMem` — used by 2 (le_one, lt_one)
- `ord_algebraMap_mul_ge_aux'` — used by 6 times in `ordAtInfty_mulByInt_y_eq_neg_three_general`
- `mulByInt_neg_mem_kernel_of_torsion'` — used by 2 (x-torsion, y-torsion)

**Unused within file** (external API candidates):
- `mulByInt_comap_pointValuation_isEquiv_affine`
- `mulByInt_comap_pointValuation_isEquiv_infty`
- `pointValuation_mulByInt_x_sub_lt_one_of_ne_zero`
- `pointValuation_mulByInt_y_sub_lt_one_of_ne_zero`
- `ordAtInfty_mulByInt_y_eq_neg_three_general` (only used by `ord_P_mulByInt_y_eq_neg_three_of_torsion` in file)
- `ord_P_mulByInt_x_eq_neg_two_of_torsion` (only used by `comap_pointValuation_mulByInt_eq_infty`)
- `ord_P_mulByInt_y_eq_neg_three_of_torsion` (only used by `comap_pointValuation_mulByInt_eq_infty`)
- `mulByInt_samePlace_le_one_iff_affine` (only used by `mulByInt_comap_pointValuation_isEquiv_affine`)
- `mulByInt_samePlace_le_one_iff_infty` (only used by `mulByInt_comap_pointValuation_isEquiv_infty`)
