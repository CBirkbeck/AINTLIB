# Inventory: ./HasseWeil/Verschiebung/Genuine.lean

**File**: `HasseWeil/Verschiebung/Genuine.lean`
**Lines**: 1–1654
**Purpose**: V-side (Verschiebung) genuine `r·V − s·id` isogeny family, mirroring the π-side
(Frobenius) D-track. Exports the universal constructor `genuineIsogSmulSubV_universal_unconditional`
and supporting lemmas for the T26-A/B/MAIN tickets. One `sorry` remains in
`addPullback_x_pair_x_ord_neg` (Silverman IV.1.4 / formal-group subgroup closure, BRIDGE-003).

---

## Declarations

### `theorem sigma_verschiebung_pullback_x_eq`
- **Type**: `(h_subset : (mulByInt W.toAffine (#K : ℤ)).pullback.range ≤ (frobeniusIsog W).pullback.range) → (mulByInt W.toAffine (-1)).pullback (verschiebungPullback_of_witness W h_subset (x_gen W)) = verschiebungPullback_of_witness W h_subset (x_gen W)`
- **What**: The σ-action (i.e., `mulByInt -1` pullback) fixes `V.pb(x_gen)`. In other words, `V.pb(x_gen)` is fixed by the negation involution.
- **How**: Uses `verschiebung_pullback_commute_mulByInt_neg_one` (σ–V pullback commutation) and `mulByInt_pullback_x_neg_one` (σ fixes `x_gen`).
- **Hypotheses**: Finite field K, elliptic curve W, the Session-3 range inclusion `Im([q]*) ⊆ Im(π*)`.
- **Uses from project**: `verschiebung_pullback_commute_mulByInt_neg_one`, `verschiebungPullback_of_witness`, `mulByInt_pullback_x_neg_one`, `x_gen`
- **Used by**: unused in file (leaf)
- **Visibility**: public
- **Lines**: 55–67, proof ~13 lines
- **Notes**: Not referenced anywhere else in this file; exported for external consumers.

---

### `theorem sigma_verschiebung_pullback_y_eq`
- **Type**: `h_subset → (mulByInt W.toAffine (-1)).pullback (verschiebungPullback_of_witness W h_subset (y_gen W)) = -(verschiebungPullback_of_witness W h_subset (y_gen W)) - a₁ * V.pb(x_gen) - a₃`
- **What**: The σ-action on `V.pb(y_gen)` sends it to `-V.pb(y_gen) - a₁·V.pb(x_gen) - a₃`, mirroring the usual σ-action on `y_gen`.
- **How**: Uses `verschiebung_pullback_commute_mulByInt_neg_one` then `mulByInt_pullback_y_neg_one`; pushes V.pb (a K-AlgHom) over the linear combination via `map_sub/map_neg/map_mul/AlgHom.commutes`.
- **Hypotheses**: Same as above.
- **Uses from project**: `verschiebung_pullback_commute_mulByInt_neg_one`, `verschiebungPullback_of_witness`, `mulByInt_pullback_y_neg_one`, `x_gen`, `y_gen`
- **Used by**: unused in file (leaf)
- **Visibility**: public
- **Lines**: 70–88, proof ~19 lines
- **Notes**: Not referenced elsewhere in this file.

---

### `theorem sigma_zsmul_verschiebung_pullback_x_eq`
- **Type**: `h_subset → (r : ℤ) → r ≠ 0 → (mulByInt W.toAffine (-1)).pullback (((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (x_gen W)) = ((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (x_gen W)`
- **What**: The σ-action fixes `(V.zsmul r).pb(x_gen)`, i.e., the x-coordinate pullback of the r-fold Verschiebung is σ-invariant.
- **How**: Unfolds `(V.zsmul r).pb = V.pb ∘ (mulByInt r).pb`, applies `verschiebung_pullback_commute_mulByInt_neg_one` to the inner factor, then uses `sigma_mulByInt_pullback_x_eq` for `n = r`.
- **Hypotheses**: r ≠ 0, plus h_subset.
- **Uses from project**: `verschiebung_pullback_commute_mulByInt_neg_one`, `verschiebungPullback_of_witness`, `verschiebungIsog_of_witness`, `sigma_mulByInt_pullback_x_eq`, `x_gen`
- **Used by**: `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_sigma_invariant`
- **Visibility**: public
- **Lines**: 94–110, proof ~17 lines

---

### `theorem sigma_zsmul_verschiebung_pullback_y_eq`
- **Type**: `h_subset → (r : ℤ) → r ≠ 0 → (mulByInt W.toAffine (-1)).pullback (((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (y_gen W)) = -... - a₁*... - a₃`
- **What**: The σ-action on `(V.zsmul r).pb(y_gen)` gives the standard `-... - a₁·... - a₃` expression, mirroring the y-gen σ-action.
- **How**: Same strategy as the x-case: unfold via `verschiebung_pullback_commute_mulByInt_neg_one`, then `sigma_mulByInt_pullback_y_eq`; push V.pb linearity via `simp [map_sub, map_neg, map_mul, AlgHom.commutes]`.
- **Hypotheses**: r ≠ 0, plus h_subset.
- **Uses from project**: `verschiebung_pullback_commute_mulByInt_neg_one`, `verschiebungPullback_of_witness`, `verschiebungIsog_of_witness`, `sigma_mulByInt_pullback_y_eq`, `x_gen`, `y_gen`
- **Used by**: `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_sigma_invariant`
- **Visibility**: public
- **Lines**: 115–143, proof ~29 lines

---

### `theorem addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_sigma_invariant`
- **Type**: `h_subset → r s : ℤ → hr → hs → h_x_ne → (mulByInt W.toAffine (-1)).pullback (addPullback_x_pair (V.zsmul r) (mulByInt (-s))) = addPullback_x_pair (V.zsmul r) (mulByInt (-s))`
- **What**: The x-coordinate of `(rV + (−s)·id)` in the function field is σ-invariant (fixed by the `-1` pullback), hence lies in the σ-fixed subfield K(x).
- **How**: Term-mode application of the generic `addPullback_x_pair_sigma_invariant`, with the four σ-symmetry hypotheses supplied by `sigma_zsmul_verschiebung_pullback_x/y_eq` and `sigma_mulByInt_pullback_x/y_eq (-s)`.
- **Hypotheses**: h_subset, r ≠ 0, s ≠ 0, x-coordinate mismatch h_x_ne.
- **Uses from project**: `addPullback_x_pair_sigma_invariant`, `sigma_zsmul_verschiebung_pullback_x_eq`, `sigma_zsmul_verschiebung_pullback_y_eq`, `sigma_mulByInt_pullback_x_eq`, `sigma_mulByInt_pullback_y_eq`, `verschiebungIsog_of_witness`
- **Used by**: `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image`
- **Visibility**: public
- **Lines**: 156–174, proof ~1 line (term-mode)

---

### `theorem addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image`
- **Type**: `h_subset → r s : ℤ → hr → hs → h_x_ne → ∃ a : FractionRing (Polynomial K), addPullback_x_pair ((V.zsmul r).pullback) (mulByInt (-s)) = algebraMap a`
- **What**: The x-coordinate of the pair pullback lies in the image of `Frac(K[X]) → K(E)`, i.e., it is a rational function in x.
- **How**: Direct application of `sigma_fixed_implies_in_KX_image` to `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_sigma_invariant`.
- **Hypotheses**: h_subset, r ≠ 0, s ≠ 0, h_x_ne.
- **Uses from project**: `sigma_fixed_implies_in_KX_image`, `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_sigma_invariant`, `verschiebungIsog_of_witness`
- **Used by**: `addBaseHomPair_injective_zsmul_verschiebung_mulByInt_neg_of_pole`, `intDegree_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pos`, `ord_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_lt_zero`
- **Visibility**: public
- **Lines**: 180–194, proof ~1 line (term-mode)
- **Notes**: Referenced 11 times in file; key intermediate API.

---

### `theorem addBaseHomPair_injective_zsmul_verschiebung_mulByInt_neg_of_pole`
- **Type**: `h_subset → r s hr hs → h_x_ne → h_pole : ord_∞(addPullback_x_pair ...) < 0 → Function.Injective (addBaseHomPair (V.zsmul r) (mulByInt (-s)))`
- **What**: Given a negative order-at-infinity (pole) of the pair x-coordinate, the base homomorphism pair `addBaseHomPair` is injective.
- **How**: Rewrites `addBaseHomPair = aeval` via `addBaseHomPair_eq_aeval`; applies `transcendental_iff_injective.mp` to reduce to transcendence; uses `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image` to extract a K(x)-preimage `a`; shows `a` algebraic leads to a constant, which either has ord = ⊤ or ord = 0, both contradicting `h_pole`; uses `algebraic_in_fracRing_eq_const` and `ordAtInfty_algebraMap_F_nonzero`.
- **Hypotheses**: h_subset, r ≠ 0, s ≠ 0, h_x_ne, h_pole.
- **Uses from project**: `addBaseHomPair_eq_aeval`, `transcendental_iff_injective`, `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image`, `algebraic_in_fracRing_eq_const`, `ordAtInfty_algebraMap_F_nonzero`, `verschiebungIsog_of_witness`
- **Used by**: `addCoordAlgHomPair_injective_zsmul_verschiebung_mulByInt_neg_of_pole`
- **Visibility**: public
- **Lines**: 211–266, proof ~56 lines
- **Notes**: Proof longer than 30 lines (≈56 lines). Pattern mirrors the π-side lemma in Frobenius.lean.

---

### `theorem addCoordAlgHomPair_injective_zsmul_verschiebung_mulByInt_neg_of_pole`
- **Type**: `h_subset → r s hr hs → h_x_ne → h_pole → Function.Injective (addCoordAlgHomPair (AddNonInversePair_of_x_ne h_x_ne))`
- **What**: Given a pole bound, the full coordinate algebra homomorphism pair `addCoordAlgHomPair` is injective.
- **How**: One-line application of `addCoordAlgHomPair_injective_of_baseHom_inj` to `addBaseHomPair_injective_zsmul_verschiebung_mulByInt_neg_of_pole`.
- **Hypotheses**: Same as above.
- **Uses from project**: `addCoordAlgHomPair_injective_of_baseHom_inj`, `AddNonInversePair_of_x_ne`, `addBaseHomPair_injective_zsmul_verschiebung_mulByInt_neg_of_pole`, `verschiebungIsog_of_witness`
- **Used by**: `genuineIsogSmulSubV_of_pole_witness`
- **Visibility**: public
- **Lines**: 270–289, proof ~20 lines

---

### `noncomputable def genuineIsogSmulSubV_of_pole_witness`
- **Type**: `h_subset → r s hr hs → h_x_ne → h_pole → Isogeny W.toAffine W.toAffine`
- **What**: Constructs the genuine `r·V − s·id` isogeny (as an element of `Isogeny W.toAffine W.toAffine`) from a pole-bound witness, witness-parametric on h_subset and h_x_ne.
- **How**: Term-mode: calls `addIsog` with `AddNonInversePair_of_x_ne h_x_ne` and `addCoordAlgHomPair_injective_zsmul_verschiebung_mulByInt_neg_of_pole ...`.
- **Hypotheses**: h_subset, r ≠ 0, s ≠ 0, h_x_ne, h_pole.
- **Uses from project**: `addIsog`, `AddNonInversePair_of_x_ne`, `addCoordAlgHomPair_injective_zsmul_verschiebung_mulByInt_neg_of_pole`, `verschiebungIsog_of_witness`
- **Used by**: `genuineIsogSmulSubV_universal`
- **Visibility**: public
- **Lines**: 306–321, ~16 lines (term-mode)

---

### `@[simp] theorem genuineIsogSmulSubV_of_pole_witness_toAddMonoidHom`
- **Type**: `... → Isogeny.toAddMonoidHom (genuineIsogSmulSubV_of_pole_witness ...) = ((V.zsmul r).toAddMonoidHom + (mulByInt (-s)).toAddMonoidHom)`
- **What**: Simp lemma: the `toAddMonoidHom` of the constructed genuine isogeny equals the sum of the two summand homs.
- **How**: `rfl`.
- **Hypotheses**: Same inputs as `genuineIsogSmulSubV_of_pole_witness`.
- **Uses from project**: `genuineIsogSmulSubV_of_pole_witness`, `verschiebungIsog_of_witness`
- **Used by**: unused in file (exported API)
- **Visibility**: public
- **Lines**: 323–339, proof ~1 line

---

### `private theorem polyEq_of_mulByInt_x_eq_pow`
- **Type**: `(n m : ℤ) → n ≠ 0 → m ≠ 0 → (k : ℕ) → mulByInt_x W n = (mulByInt_x W m) ^ k → W.Φ n * (W.ΨSq m) ^ k = (W.Φ m) ^ k * W.ΨSq n`
- **What**: From an equality of x-coordinate rational functions in K(E), derives the corresponding polynomial equality in K[X] by clearing denominators and using algebraMap injectivity.
- **How**: Cross-multiplies the division formula (`mulByInt_x = Φ_ff/ΨSq_ff`) via `field_simp + linear_combination`; lifts to K[X] via `Φ_ff_eq_algebraMap_polynomial`, `ΨSq_ff_eq_algebraMap_polynomial`, and `IsFractionRing.injective`+`Affine.CoordinateRing.algebraMap_poly_injective`.
- **Hypotheses**: n ≠ 0, m ≠ 0.
- **Uses from project**: `ΨSq_ff_ne_zero`, `Φ_ff_eq_algebraMap_polynomial`, `ΨSq_ff_eq_algebraMap_polynomial`, `mulByInt_x`
- **Used by**: `h_x_ne_zsmul_verschiebung_mulByInt_neg`, `V_pullback_x_gen_ne_x_gen`
- **Visibility**: private
- **Lines**: 389–429, proof ~41 lines
- **Notes**: Proof longer than 30 lines (≈41 lines).

---

### `theorem h_x_ne_zsmul_verschiebung_mulByInt_neg`
- **Type**: `h_subset → r s hr hs → (r : K) ≠ 0 → (s : K) ≠ 0 → ((V.zsmul r).pullback (x_gen W)) ≠ (mulByInt (-s)).pullback (x_gen W)`
- **What**: (T26-B core) The x-coordinate pullbacks of `V.zsmul r` and `mulByInt (-s)` are distinct — the central x-mismatch hypothesis for the genuine V-side family.
- **How**: By contradiction: assume equality; step 1 rewrites LHS/RHS to `mulByInt_x` form via `mulByInt_pullback_x`; step 2 applies `(frobeniusIsog W).pullback` to both sides; step 3 simplifies LHS via `mulByInt_q_factor_via_witness` + `mulByInt_pullback_mulByInt_x_eq_mul`; step 4 simplifies RHS via `frobeniusIsog_pullback_apply` (q-power map); step 5 lifts to K[X] via `polyEq_of_mulByInt_x_eq_pow`; step 6 uses `isCoprime_Φ_ΨSq` + mutual divisibility + `natDegree_Φ` to derive `r².q² = q.s²`, hence `s² = r².q`; step 7 uses `FiniteField.card'` to get a prime p | q | s², hence p | s, contradicting (s : K) ≠ 0 via `CharP.intCast_eq_zero_iff`.
- **Hypotheses**: h_subset, r ≠ 0, s ≠ 0, (r : K) ≠ 0, (s : K) ≠ 0.
- **Uses from project**: `mulByInt_pullback_x`, `mulByInt_x_neg`, `mulByInt_q_factor_via_witness`, `mulByInt_pullback_mulByInt_x_eq_mul`, `frobeniusIsog_pullback_apply`, `polyEq_of_mulByInt_x_eq_pow`, `isCoprime_Φ_ΨSq`, `verschiebungIsog_of_witness`, `verschiebungPullback_of_witness`, `x_gen`
- **Used by**: `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_sigma_invariant` (via h_x_ne), `addBaseHomPair_injective_zsmul_verschiebung_mulByInt_neg_of_pole`, `genuineIsogSmulSubV_universal`, `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pole`, `intDegree_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pos`, `ord_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_lt_zero`, `genuineIsogSmulSubV_universal_unconditional`
- **Visibility**: public
- **Lines**: 438–602, proof ~165 lines
- **Notes**: Longest proof in file (≈165 lines). Substantive polynomial-degree argument (T26-B). Referenced 8 times.

---

### `theorem mulByInt_pow_pullback_x_gen_mem_frobenius_fieldRange`
- **Type**: `h_subset → k : ℕ → 1 ≤ k → (mulByInt W.toAffine ((#K^k : ℕ) : ℤ)).pullback (x_gen W) ∈ (frobeniusIsog W).pullback.fieldRange`
- **What**: `[q^k]*(x_gen)` lies in the image of π* (the Frobenius pullback's fieldRange), for every k ≥ 1. This is the x-generator half of the universal-in-k inclusion.
- **How**: Uses `mulByInt_pow_pullback_x_gen_eq_pow_qpow` to rewrite as a `q^k`-th power; factors `q^k = q * q^(k-1)` and uses `pow_mem` plus `frobeniusIsog_pullback_mem_iff` (a q-th power lies in Im(π*)).
- **Hypotheses**: h_subset, k ≥ 1.
- **Uses from project**: `mulByInt_pow_pullback_x_gen_eq_pow_qpow`, `isogenyIterate`, `verschiebungIsog_of_witness`, `frobeniusIsog_pullback_mem_iff`, `x_gen`
- **Used by**: `mulByInt_pullback_fieldRange_subset_frobenius_universal_in_k`, `mulByInt_pow_pullback_x_gen_mem_frobenius_subalgebra`
- **Visibility**: public
- **Lines**: 625–647, proof ~23 lines

---

### `theorem mulByInt_pow_pullback_y_gen_mem_frobenius_fieldRange`
- **Type**: same shape as x-version for y_gen
- **What**: `[q^k]*(y_gen)` lies in Im(π*) for k ≥ 1. Y-generator analog.
- **How**: Same as x-version using `mulByInt_pow_pullback_y_gen_eq_pow_qpow` and `frobeniusIsog_pullback_mem_iff`.
- **Hypotheses**: h_subset, k ≥ 1.
- **Uses from project**: `mulByInt_pow_pullback_y_gen_eq_pow_qpow`, `isogenyIterate`, `verschiebungIsog_of_witness`, `frobeniusIsog_pullback_mem_iff`, `y_gen`
- **Used by**: `mulByInt_pullback_fieldRange_subset_frobenius_universal_in_k`, `mulByInt_pow_pullback_y_gen_mem_frobenius_subalgebra`
- **Visibility**: public
- **Lines**: 650–668, proof ~19 lines

---

### `theorem mulByInt_pullback_fieldRange_subset_frobenius_universal_in_k`
- **Type**: `h_subset → k : ℕ → 1 ≤ k → ∀ z : K(E), (mulByInt W.toAffine ((#K^k : ℕ) : ℤ)).pullback z ∈ (frobeniusIsog W).pullback.fieldRange`
- **What**: Universal-in-k inclusion: for all k ≥ 1 and all z ∈ K(E), the [q^k]-pullback of z lies in Im(π*). This is the IntermediateField version.
- **How**: Uses `functionField_eq_intermediateField_adjoin_xy` (K(E) = K(x_gen, y_gen)); maps the pullback over the adjoin via `IntermediateField.adjoin_map` + `IntermediateField.adjoin_le_iff`; discharges generators via x/y-gen fieldRange membership lemmas.
- **Hypotheses**: h_subset, k ≥ 1.
- **Uses from project**: `functionField_eq_intermediateField_adjoin_xy`, `mulByInt_pow_pullback_x_gen_mem_frobenius_fieldRange`, `mulByInt_pow_pullback_y_gen_mem_frobenius_fieldRange`, `x_gen`, `y_gen`
- **Used by**: `mulByInt_pow_pullback_range_subset_frobenius_universal_in_k`
- **Visibility**: public
- **Lines**: 677–708, proof ~32 lines
- **Notes**: Proof longer than 30 lines (≈32 lines).

---

### `theorem mulByInt_pow_pullback_range_subset_frobenius_universal_in_k`
- **Type**: `h_subset → k → 1 ≤ k → (mulByInt W.toAffine ((#K^k : ℕ) : ℤ)).pullback.range ≤ (frobeniusIsog W).pullback.range`
- **What**: Subalgebra-typed version of the universal-in-k inclusion (`AlgHom.range` ≤ `AlgHom.range`).
- **How**: Rintro the range membership, apply `mulByInt_pullback_fieldRange_subset_frobenius_universal_in_k`.
- **Hypotheses**: h_subset, k ≥ 1.
- **Uses from project**: `mulByInt_pullback_fieldRange_subset_frobenius_universal_in_k`
- **Used by**: unused in file (exported for external consumers)
- **Visibility**: public
- **Lines**: 715–728, proof ~14 lines

---

### `theorem mulByInt_pow_pullback_x_gen_mem_frobenius_subalgebra`
- **Type**: `h_subset → k → 1 ≤ k → (mulByInt W.toAffine ((#K^k : ℕ) : ℤ)).pullback (x_gen W) ∈ (frobeniusIsog W).pullback.range`
- **What**: Subalgebra form of x_gen membership: `[q^k]*(x_gen) ∈ (frobeniusIsog W).pullback.range`.
- **How**: Direct application of `mulByInt_pow_pullback_x_gen_mem_frobenius_fieldRange`.
- **Hypotheses**: h_subset, k ≥ 1.
- **Uses from project**: `mulByInt_pow_pullback_x_gen_mem_frobenius_fieldRange`
- **Used by**: unused in file (exported for `PurelyInsep.lean`, `QthRoots.lean`)
- **Visibility**: public
- **Lines**: 734–741, ~1 line proof

---

### `theorem mulByInt_pow_pullback_y_gen_mem_frobenius_subalgebra`
- **Type**: same for y_gen
- **What**: Subalgebra form of y_gen membership.
- **How**: Direct application of `mulByInt_pow_pullback_y_gen_mem_frobenius_fieldRange`.
- **Hypotheses**: h_subset, k ≥ 1.
- **Uses from project**: `mulByInt_pow_pullback_y_gen_mem_frobenius_fieldRange`
- **Used by**: unused in file (exported)
- **Visibility**: public
- **Lines**: 745–752, ~1 line proof

---

### `theorem h_subset_of_isDualOf`
- **Type**: `(V : Isogeny W.toAffine W.toAffine) → IsDualOf W.toAffine V (frobeniusIsog W) → (mulByInt W.toAffine (#K : ℤ)).pullback.range ≤ (frobeniusIsog W).pullback.range`
- **What**: (T26-A) From an `IsDualOf` witness `V` (i.e., `V ∘ π = π ∘ V = [q]`), derives the range inclusion `Im([q]*) ⊆ Im(π*)` that the rest of the pipeline consumes.
- **How**: Extracts `V.comp π = mulByInt q` from `hV.1` using `frobeniusIsog_degree`; for any `w = (mulByInt q).pullback z`, rewrites as `π.pullback (V.pullback z)` by `DFunLike.congr_fun (congrArg Isogeny.pullback h_comp) z`.
- **Hypotheses**: IsDualOf V (frobeniusIsog W).
- **Uses from project**: `frobeniusIsog_degree`, `IsDualOf`, `verschiebungIsog_of_witness` (indirect)
- **Used by**: `genuineIsogSmulSubV_universal`, `genuineIsogSmulSubV_universal_unconditional` (9 internal references)
- **Visibility**: public
- **Lines**: 778–799, proof ~22 lines

---

### `theorem V_pullback_x_gen_ne_x_gen`
- **Type**: `(V : Isogeny W.toAffine W.toAffine) → IsDualOf W.toAffine V (frobeniusIsog W) → V.pullback (x_gen W) ≠ x_gen W`
- **What**: (T11-DISCHARGE-X-NE) For any V with IsDualOf-witness, `V.pb(x_gen) ≠ x_gen`. This is Worker C's T11 hypothesis, discharged substantively.
- **How**: By contradiction: assume equality; raises to q-th power via `frobeniusIsog_pullback_apply` and composition to get `x_gen^q = mulByInt_x W q`; lifts to polynomial equation `X^q * W.ΨSq q = W.Φ q` in K[X] via algebraMap injectivity; uses `isCoprime_Φ_ΨSq` to show `W.ΨSq q` is a unit (hence degree 0); then `natDegree_Φ` gives `natDegree(W.Φ q) = q²`, but degree computation via the equation gives q = q²; contradicts `q ≥ 2`.
- **Hypotheses**: IsDualOf V (frobeniusIsog W).
- **Uses from project**: `frobeniusIsog_pullback_apply`, `mulByInt_pullback_x`, `mulByInt_x`, `ΨSq_ff_ne_zero`, `isCoprime_Φ_ΨSq`, `polyEq_of_mulByInt_x_eq_pow`, `frobeniusIsog_degree`, `x_gen`
- **Used by**: `h_x_ne_id_V_zsmul_neg_one`
- **Visibility**: public
- **Lines**: 840–959, proof ~120 lines
- **Notes**: Proof longer than 30 lines (≈120 lines). Substantive polynomial-degree argument (T11-DISCHARGE-X-NE). 3 uses in file.

---

### `theorem h_x_ne_id_V_zsmul_neg_one`
- **Type**: `(V : Isogeny ...) → IsDualOf W.toAffine V (frobeniusIsog W) → (Isogeny.id W.toAffine).pullback (x_gen W) ≠ (V.zsmul (-1)).pullback (x_gen W)`
- **What**: Discharges T11's hypothesis `id.pb(x_gen) ≠ (V.zsmul -1).pb(x_gen)` from IsDualOf. Reduces to `V_pullback_x_gen_ne_x_gen` by unfolding `id.pb = id` and `(V.zsmul -1).pb = V.pb ∘ (mulByInt -1).pb = V.pb ∘ (mulByInt_x W 1) = V.pb(x_gen)`.
- **How**: Unfolds `id.pb x_gen = x_gen` (rfl) and `(V.zsmul -1).pb x_gen = V.pb x_gen` via `Isogeny.comp_algebraMap_eq`, `mulByInt_pullback_x`, `mulByInt_x_neg`, `mulByInt_x_one`; then applies `V_pullback_x_gen_ne_x_gen`.
- **Hypotheses**: IsDualOf V (frobeniusIsog W).
- **Uses from project**: `V_pullback_x_gen_ne_x_gen`, `mulByInt_pullback_x`, `mulByInt_x_neg`, `mulByInt_x_one`, `Isogeny.comp_algebraMap_eq`, `x_gen`
- **Used by**: unused in file (exported for Worker C's T11)
- **Visibility**: public
- **Lines**: 970–991, proof ~22 lines

---

### `noncomputable def genuineIsogSmulSubV_universal`
- **Type**: `(V : Isogeny ...) → IsDualOf W.toAffine V (frobeniusIsog W) → r s hr hs → (r : K) ≠ 0 → (s : K) ≠ 0 → h_pole → Isogeny W.toAffine W.toAffine`
- **What**: (T26-MAIN parametric) Universal V-side genuine `r·V − s·id` isogeny, parameterised by T10's universal V (via IsDualOf) and a pole-bound witness. Folds in T26-A (`h_subset_of_isDualOf`) and T26-B (`h_x_ne_zsmul_verschiebung_mulByInt_neg`).
- **How**: Term-mode: calls `genuineIsogSmulSubV_of_pole_witness` with `h_subset_of_isDualOf` and `h_x_ne_zsmul_verschiebung_mulByInt_neg` pre-applied.
- **Hypotheses**: IsDualOf, r ≠ 0, s ≠ 0, (r : K) ≠ 0, (s : K) ≠ 0, h_pole.
- **Uses from project**: `genuineIsogSmulSubV_of_pole_witness`, `h_subset_of_isDualOf`, `h_x_ne_zsmul_verschiebung_mulByInt_neg`, `verschiebungIsog_of_witness`
- **Used by**: `genuineIsogSmulSubV_universal_unconditional`, `genuineIsogSmulSubV_universal_toAddMonoidHom`
- **Visibility**: public
- **Lines**: 1025–1040, ~16 lines (term-mode)

---

### `@[simp] theorem genuineIsogSmulSubV_universal_toAddMonoidHom`
- **Type**: `... → Isogeny.toAddMonoidHom (genuineIsogSmulSubV_universal ...) = ((V.zsmul r) + (mulByInt (-s))).toAddMonoidHom`
- **What**: Simp lemma: toAddMonoidHom of the universal genuine isogeny equals the sum of summand homs.
- **How**: `rfl`.
- **Hypotheses**: All of `genuineIsogSmulSubV_universal`.
- **Uses from project**: `genuineIsogSmulSubV_universal`, `h_subset_of_isDualOf`, `verschiebungIsog_of_witness`
- **Used by**: unused in file (exported API)
- **Visibility**: public
- **Lines**: 1042–1057, proof ~1 line

---

### `theorem ordAtInfty_zsmul_mulByInt_neg_pullback_x_neg`
- **Type**: `(s : ℤ) → s ≠ 0 → (W_smooth W).ordAtInfty ((mulByInt W.toAffine (-s)).pullback (x_gen W)) < 0`
- **What**: Wall-A brick: the (−s) summand's x-pullback has a pole at O, i.e., ord_∞ < 0. The `−s` summand reduces to O.
- **How**: Rewrites `(mulByInt (-s)).pb x_gen = mulByInt_x W s` via `mulByInt_pullback_x` + `mulByInt_x_neg`; applies `ordAtInfty_mulByInt_x_neg`.
- **Hypotheses**: s ≠ 0.
- **Uses from project**: `mulByInt_pullback_x`, `mulByInt_x_neg`, `ordAtInfty_mulByInt_x_neg`, `x_gen`, `W_smooth`
- **Used by**: `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pole`
- **Visibility**: public
- **Lines**: 1117–1128, proof ~12 lines

---

### `theorem ordAtInfty_zsmul_verschiebung_pullback_x_neg`
- **Type**: `h_subset → (r : ℤ) → r ≠ 0 → (W_smooth W).ordAtInfty (((V.zsmul r).pullback (x_gen W)) < 0`
- **What**: Wall-A brick: the `rV` summand's x-pullback has a pole at O (reduces to O). Universal in q, requires no separability.
- **How**: Sets `X₁ = V.pb(mulByInt_x r)`; uses `mulByInt_q_factor_via_witness` + `mulByInt_pullback_mulByInt_x_eq_mul` + `frobeniusIsog_pullback_apply` to derive `X₁^q = mulByInt_x W (r*q)`; then `ordAtInfty_mulByInt_x_neg` gives `q * ord(X₁) = ord(X₁^q) < 0`; concludes `ord(X₁) < 0` via `nsmul` monotonicity and contradiction.
- **Hypotheses**: h_subset, r ≠ 0.
- **Uses from project**: `mulByInt_pullback_x`, `mulByInt_q_factor_via_witness`, `mulByInt_pullback_mulByInt_x_eq_mul`, `frobeniusIsog_pullback_apply`, `ordAtInfty_mulByInt_x_neg`, `mulByInt_x_ne_zero`, `verschiebungIsog_of_witness`, `verschiebungPullback_of_witness`, `x_gen`, `W_smooth`
- **Used by**: `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pole`
- **Visibility**: public
- **Lines**: 1139–1211, proof ~73 lines
- **Notes**: Proof longer than 30 lines (≈73 lines). Handles the inseparable factor `(r·q : K) = 0` via the unconditional negative-bound form.

---

### `theorem addPullback_x_pair_ord_neg_of_sum_reduces_witness`
- **Type**: `h_x_ne → h_y_sum_ne : Y_sum ≠ 0 → h_base : ord_∞ X_sum ≤ 0 → h_reduces : 0 < ord_∞(−X_sum/Y_sum) → ord_∞(addPullback_x_pair α₁ α₂) < 0`
- **What**: Given a sum that "reduces to O" (the IV.1.4-level data), concludes the x-coordinate has a pole. Axiom-clean discrete-valuation assembly.
- **How**: Uses `addPullback_pair_equation` to place the sum on the curve; shows X_sum ≠ 0 from h_base + no-top contradiction; then calls `ordAtInfty_x_neg_of_equation_of_neg_div_pos`.
- **Hypotheses**: h_x_ne, h_y_sum_ne, h_base, h_reduces.
- **Uses from project**: `addPullback_pair_equation`, `AddNonInversePair_of_x_ne`, `ordAtInfty_x_neg_of_equation_of_neg_div_pos`, `W_smooth`, `addPullback_x_pair`, `addPullback_y_pair`
- **Used by**: unused in file (architectural scaffold; the axiom-clean consumer chain goes via `addPullback_x_pair_x_ord_neg`)
- **Visibility**: public
- **Lines**: 1251–1271, proof ~21 lines

---

### `theorem addPullback_x_pair_sum_reduces_of_iv14_witness`
- **Type**: `h_α₁ h_α₂ h_y_sum_ne h_base h_iv14 (IV.1.4 identity) → Y_sum ≠ 0 ∧ ord_∞ X_sum ≤ 0 ∧ 0 < ord_∞(−X_sum/Y_sum)`
- **What**: Reduces the full "sum-reduces-to-O" triple to three named residuals (h_y_sum_ne, h_base, and the IV.1.4 formal-group identity `h_iv14`), with item 3 produced axiom-clean from h_iv14 via the formal group order machinery.
- **How**: Items 1 and 2 pass through; item 3 is discharged by `orderTop_localExpand_eq_ordAtInfty` and `orderTop_localExpand_z_sum_pos_of_iv14_identity`.
- **Hypotheses**: Summand pole-bounds h_α₁, h_α₂; h_y_sum_ne; h_base; IV.1.4 identity h_iv14.
- **Uses from project**: `orderTop_localExpand_eq_ordAtInfty`, `orderTop_localExpand_z_sum_pos_of_iv14_identity`, `localExpand`, `formalIsogenySeries`, `formalGroupLaw`, `W_smooth`
- **Used by**: unused in file (scaffold for future IV.1.4 discharge)
- **Visibility**: public
- **Lines**: 1298–1318, proof ~21 lines

---

### `theorem addPullback_x_pair_x_ord_neg`
- **Type**: `h_x_ne → h_α₁ : ord_∞(α₁.pb x_gen) < 0 → h_α₂ : ord_∞(α₂.pb x_gen) < 0 → ord_∞(addPullback_x_pair α₁ α₂) < 0`
- **What**: **(sorry)** Silverman VII.2.2 / BRIDGE-003: the kernel of reduction at O (points with x-pullback having a pole) is closed under addition. The single remaining deep residual in the V-side pole bound chain.
- **How**: `sorry` — requires the formal-group IV.1.4 pair-level identity, which is the one step not yet proven.
- **Hypotheses**: h_x_ne, both summands have poles at O.
- **Uses from project**: none (sorry)
- **Used by**: `addPullback_x_pair_sum_reduces_to_O`, `addPullback_x_pair_ord_neg_of_summands_reduce`
- **Visibility**: public
- **Lines**: 1350–1356, proof = 1 line (`sorry`)
- **Notes**: **SORRY**. This is the lone BRIDGE-003 gap. Everything downstream is derived from this one sorry axiom-clean.

---

### `theorem addPullback_x_pair_sum_reduces_to_O`
- **Type**: `h_x_ne → h_α₁ → h_α₂ → (Y_sum ≠ 0 ∧ ord_∞ X_sum ≤ 0 ∧ 0 < ord_∞(−X_sum/Y_sum))`
- **What**: The "sum reduces to O" triple, derived axiom-clean from `addPullback_x_pair_x_ord_neg` (the single sorry). Three valuation facets via `addPullback_pair_equation` + shipped Weierstrass valuation bricks.
- **How**: Calls `addPullback_x_pair_x_ord_neg`; deduces X_sum ≠ 0 from pole; calls `addPullback_pair_equation`, `ordAtInfty_y_ne_zero_of_equation_of_ord_x_neg`, and `ordAtInfty_neg_div_pos_of_equation_of_ord_x_neg`.
- **Hypotheses**: h_x_ne, h_α₁, h_α₂.
- **Uses from project**: `addPullback_x_pair_x_ord_neg`, `addPullback_pair_equation`, `AddNonInversePair_of_x_ne`, `ordAtInfty_y_ne_zero_of_equation_of_ord_x_neg`, `ordAtInfty_neg_div_pos_of_equation_of_ord_x_neg`, `W_smooth`, `addPullback_x_pair`, `addPullback_y_pair`
- **Used by**: `addPullback_x_pair_ord_neg_of_summands_reduce`
- **Visibility**: public
- **Lines**: 1376–1404, proof ~29 lines

---

### `theorem addPullback_x_pair_ord_neg_of_summands_reduce`
- **Type**: `h_x_ne → h_α₁ → h_α₂ → ord_∞(addPullback_x_pair α₁ α₂) < 0`
- **What**: The generic kernel-of-reduction subgroup closure: both summands reduce to O ⟹ sum reduces to O (x-coordinate has a pole).
- **How**: One-line delegation to `addPullback_x_pair_x_ord_neg`.
- **Hypotheses**: h_x_ne, h_α₁, h_α₂.
- **Uses from project**: `addPullback_x_pair_x_ord_neg`
- **Used by**: `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pole`
- **Visibility**: public
- **Lines**: 1456–1466, proof ~1 line (term-mode)

---

### `theorem addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pole`
- **Type**: `h_subset → r s hr hs → (r : K) ≠ 0 → (s : K) ≠ 0 → ord_∞(addPullback_x_pair (V.zsmul r) (mulByInt (-s))) < 0`
- **What**: Combines the two summand-reduction bricks and the x-mismatch to conclude the pair-pullback x-coordinate has a pole at O. The resolved V-side `h_pole` substrate.
- **How**: Term-mode: calls `addPullback_x_pair_ord_neg_of_summands_reduce` with `h_x_ne_zsmul_verschiebung_mulByInt_neg`, `ordAtInfty_zsmul_verschiebung_pullback_x_neg`, `ordAtInfty_zsmul_mulByInt_neg_pullback_x_neg`.
- **Hypotheses**: h_subset, r ≠ 0, s ≠ 0, (r : K) ≠ 0, (s : K) ≠ 0.
- **Uses from project**: `addPullback_x_pair_ord_neg_of_summands_reduce`, `h_x_ne_zsmul_verschiebung_mulByInt_neg`, `ordAtInfty_zsmul_verschiebung_pullback_x_neg`, `ordAtInfty_zsmul_mulByInt_neg_pullback_x_neg`, `verschiebungIsog_of_witness`
- **Used by**: `intDegree_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pos`, `ord_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_lt_zero`
- **Visibility**: public
- **Lines**: 1482–1495, proof ~14 lines

---

### `theorem intDegree_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pos`
- **Type**: `h_subset → r s hr hs → (r : K) ≠ 0 → (s : K) ≠ 0 → 0 < RatFunc.intDegree (RatFunc.ofFractionRing (KX_image_choose))`
- **What**: The K(x)-preimage of the pair pullback has strictly positive intDegree, as a sub-leaf feeding the `ord = -2·intDegree` bridge.
- **How**: Uses `h_x_ne_zsmul_verschiebung_mulByInt_neg` to get h_x_ne; calls `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pole` for the ord < 0 fact; rewrites via the K(x)-image `ha`; shows `a ≠ 0` from ord < 0 + ordAtInfty_zero; applies `ordAtInfty_algebraMap_fracPolyX_of_ne_zero` (gives ord = -2·intDegree); concludes `intDegree > 0` by linarith.
- **Hypotheses**: h_subset, r ≠ 0, s ≠ 0, (r : K) ≠ 0, (s : K) ≠ 0.
- **Uses from project**: `h_x_ne_zsmul_verschiebung_mulByInt_neg`, `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image`, `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pole`, `W_smooth`, `verschiebungIsog_of_witness`
- **Used by**: `ord_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_lt_zero`
- **Visibility**: public
- **Lines**: 1508–1552, proof ~45 lines
- **Notes**: Proof longer than 30 lines (≈45 lines). Arithmetic via `ordAtInfty_algebraMap_fracPolyX_of_ne_zero`.

---

### `theorem ord_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_lt_zero`
- **Type**: `h_subset → r s hr hs → (r : K) ≠ 0 → (s : K) ≠ 0 → ord_∞(addPullback_x_pair (V.zsmul r) (mulByInt (-s))) < 0`
- **What**: T-PFA-4-WEAK substrate (Round 8 reviewer repair): the V-side pair pullback has strictly negative ord, without needing the exact -2 value. Closes `h_pole` for `genuineIsogSmulSubV_universal`.
- **How**: Extracts K(x)-image `a` via `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image`; uses `intDegree_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pos` for intDegree > 0; shows `a ≠ 0`; applies `ordAtInfty_algebraMap_fracPolyX_of_ne_zero` (ord = -2·intDegree); concludes via linarith.
- **Hypotheses**: h_subset, r ≠ 0, s ≠ 0, (r : K) ≠ 0, (s : K) ≠ 0.
- **Uses from project**: `h_x_ne_zsmul_verschiebung_mulByInt_neg`, `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image`, `intDegree_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pos`, `W_smooth`, `verschiebungIsog_of_witness`
- **Used by**: `genuineIsogSmulSubV_universal_unconditional`
- **Visibility**: public
- **Lines**: 1565–1623, proof ~59 lines
- **Notes**: Proof longer than 30 lines (≈59 lines). Relies transitively on the sorry in `addPullback_x_pair_x_ord_neg`.

---

### `noncomputable def genuineIsogSmulSubV_universal_unconditional`
- **Type**: `(V : Isogeny ...) → IsDualOf W.toAffine V (frobeniusIsog W) → r s hr hs → (r : K) ≠ 0 → (s : K) ≠ 0 → Isogeny W.toAffine W.toAffine`
- **What**: Universal V-side genuine `r·V − s·id` isogeny, with the pole bound discharged internally by `ord_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_lt_zero`. Once the sorry in BRIDGE-003 is closed, this becomes axiom-clean end-to-end.
- **How**: Term-mode: calls `genuineIsogSmulSubV_universal` with `ord_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_lt_zero` applied.
- **Hypotheses**: IsDualOf, r ≠ 0, s ≠ 0, (r : K) ≠ 0, (s : K) ≠ 0.
- **Uses from project**: `genuineIsogSmulSubV_universal`, `ord_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_lt_zero`, `h_subset_of_isDualOf`
- **Used by**: `genuineIsogSmulSubV_universal_unconditional_toAddMonoidHom`
- **Visibility**: public
- **Lines**: 1632–1640, ~9 lines (term-mode)

---

### `@[simp] theorem genuineIsogSmulSubV_universal_unconditional_toAddMonoidHom`
- **Type**: `... → Isogeny.toAddMonoidHom (genuineIsogSmulSubV_universal_unconditional ...) = ((V.zsmul r) + (mulByInt (-s))).toAddMonoidHom`
- **What**: Simp lemma: toAddMonoidHom of the unconditional universal genuine isogeny equals the sum of summand homs.
- **How**: `rfl`.
- **Hypotheses**: All of `genuineIsogSmulSubV_universal_unconditional`.
- **Uses from project**: `genuineIsogSmulSubV_universal_unconditional`, `h_subset_of_isDualOf`, `verschiebungIsog_of_witness`
- **Used by**: unused in file (exported API)
- **Visibility**: public
- **Lines**: 1642–1652, proof ~1 line

---

## Summary Statistics

- **Total declarations**: 35 (32 theorems + 3 noncomputable defs; `polyEq_of_mulByInt_x_eq_pow` is private)
- **Defs**: 3 (`genuineIsogSmulSubV_of_pole_witness`, `genuineIsogSmulSubV_universal`, `genuineIsogSmulSubV_universal_unconditional`)
- **Lemmas/theorems**: 32
- **Instances**: 0
- **Sorries**: 1 (`addPullback_x_pair_x_ord_neg`)
- **maxHeartbeats**: none
- **Long proofs (>30 lines)**: 7 (`addBaseHomPair_injective_...`, `polyEq_of_mulByInt_x_eq_pow`, `h_x_ne_zsmul_verschiebung_mulByInt_neg`, `V_pullback_x_gen_ne_x_gen`, `mulByInt_pullback_fieldRange_subset_frobenius_universal_in_k`, `ordAtInfty_zsmul_verschiebung_pullback_x_neg`, `intDegree_...`, `ord_addPullback_x_pair_...`)

## Key API

Declarations referenced by 3+ others in this file:
- `h_x_ne_zsmul_verschiebung_mulByInt_neg` (8 uses): the T26-B x-mismatch lemma
- `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image` (11 uses): K(x)-image witness
- `h_subset_of_isDualOf` (9 uses): T26-A range-inclusion extractor
- `addPullback_x_pair_x_ord_neg` (7 uses): the single sorry; everything downstream uses it
- `genuineIsogSmulSubV_of_pole_witness` (6 uses)
- `addPullback_x_pair_sum_reduces_to_O` (4 uses)
- `addPullback_x_pair_ord_neg_of_summands_reduce` (4 uses)
- `mulByInt_pow_pullback_x_gen_mem_frobenius_fieldRange` (4 uses)
- `genuineIsogSmulSubV_universal` (4 uses)
- `V_pullback_x_gen_ne_x_gen` (3 uses)
- `ordAtInfty_zsmul_verschiebung_pullback_x_neg` (3 uses)
- `ordAtInfty_zsmul_mulByInt_neg_pullback_x_neg` (3 uses)
- `mulByInt_pow_pullback_y_gen_mem_frobenius_fieldRange` (3 uses)

## Unused declarations (dead-code candidates in file)

- `sigma_verschiebung_pullback_x_eq` — not referenced within this file
- `sigma_verschiebung_pullback_y_eq` — not referenced within this file
- `genuineIsogSmulSubV_of_pole_witness_toAddMonoidHom` — not referenced within this file
- `genuineIsogSmulSubV_universal_toAddMonoidHom` — not referenced within this file
- `h_x_ne_id_V_zsmul_neg_one` — not referenced within this file
- `addPullback_x_pair_ord_neg_of_sum_reduces_witness` — not referenced by other proofs in this file
- `addPullback_x_pair_sum_reduces_of_iv14_witness` — only in a comment reference
- `mulByInt_pow_pullback_range_subset_frobenius_universal_in_k` — not referenced within this file
- `mulByInt_pow_pullback_x_gen_mem_frobenius_subalgebra` — not referenced within this file
- `mulByInt_pow_pullback_y_gen_mem_frobenius_subalgebra` — not referenced within this file
- `genuineIsogSmulSubV_universal_unconditional_toAddMonoidHom` — not referenced within this file

(All are public exports consumed by other files.)
