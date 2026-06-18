# Inventory: ./HasseWeil/Verschiebung/Cascade.lean

**File**: `HasseWeil/Verschiebung/Cascade.lean`
**Total lines**: 639
**Imports**: `HasseWeil.Verschiebung.IsDual`, `HasseWeil.Verschiebung.QthRoots`, `HasseWeil.Hasse.HoleE`, `HasseWeil.AdditionPullback.Frobenius`

---

## Summary

This file is a wire-up / cascade assembly file. It connects the Verschiebung chain (Sessions 2–5) to the Hasse-Weil bound machine from `Hasse/HoleE.lean`. All proofs are short (≤ 12 lines) and consist entirely of calls to upstream project lemmas. There are no `sorry`s and no `set_option maxHeartbeats` directives. The file also ships per-prime specializations of the Hasse-Weil bound for q = 2, 3, 5, 7 and for F_4, F_9 as corollaries of the parametric core.

---

### `theorem verschiebungIsog_isDualOf_frobenius_of_qth_root_witness`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] → (h_qth_root : ∀ z : W.toAffine.FunctionField, ∃ g, g ^ Fintype.card K = (mulByInt W.toAffine (Fintype.card K : ℕ : ℤ)).pullback z) → IsDualOf W.toAffine (verschiebungIsog_of_witness W (mulByInt_q_pullback_image_subset_frobenius_of_element_witness W h_qth_root)) (frobeniusIsog W)`
- **What**: Given a universal q-th-root function for the [q]-pullback, the Verschiebung constructed from the resulting inclusion witnesses is dual to the Frobenius isogeny.
- **How**: One-line proof: applies `verschiebungIsog_of_witness_isDualOf_frobenius` directly (from `IsDual.lean`); the inclusion argument is supplied by `mulByInt_q_pullback_image_subset_frobenius_of_element_witness`.
- **Hypotheses**: W is an elliptic curve over a finite field K; every element of K(E) has a q-th root in the [q]-pullback image.
- **Uses from project**: `verschiebungIsog_of_witness` (IsDual.lean), `mulByInt_q_pullback_image_subset_frobenius_of_element_witness` (PurelyInsep.lean), `verschiebungIsog_of_witness_isDualOf_frobenius` (IsDual.lean), `frobeniusIsog` (Frobenius.lean), `IsDualOf` (DualIsogeny.lean)
- **Used by**: `verschiebungIsog_isDualOf_frobenius_of_factor` (line 139), `verschiebungIsog_isDualOf_frobenius_q_three_char_three` (line 312), `verschiebungIsog_isDualOf_frobenius_q_five_char_five` (line 469), `verschiebungIsog_isDualOf_frobenius_q_seven_char_seven` (line 538); also used by `Route2Universal.lean` and `OpenLemmas.lean`
- **Visibility**: public
- **Lines**: 78–88, proof length ~1 line
- **Notes**: None.

---

### `theorem qth_root_of_q_factors_through_frobenius`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] → (h_factor : ∃ ψ : Isogeny W.toAffine W.toAffine, ψ.comp (frobeniusIsog W) = mulByInt W.toAffine (Fintype.card K : ℕ : ℤ)) → ∀ z : W.toAffine.FunctionField, ∃ g, g ^ Fintype.card K = (mulByInt W.toAffine (Fintype.card K : ℕ : ℤ)).pullback z`
- **What**: Given that [q] factors through the q-Frobenius isogeny (i.e. ∃ ψ with ψ ∘ φ_q = [q]), every function-field element has a q-th root in the [q]-pullback range.
- **How**: Destructs the factorization witness; for each z, uses ψ.pullback z as the q-th root. The key step rewrites `(ψ ∘ φ_q)^*(z)` using `frobeniusIsog_pullback_apply` (which gives `φ_q^*(f) = f^q`) to convert the [q]-pullback into a q-th power.
- **Hypotheses**: W elliptic over finite field K; [q] factors as ψ ∘ φ_q for some isogeny ψ.
- **Uses from project**: `frobeniusIsog` (Frobenius.lean), `frobeniusIsog_pullback_apply` (Frobenius.lean), `mulByInt` (IsogenyAG or basic)
- **Used by**: `verschiebungIsog_isDualOf_frobenius_of_factor` (lines 137, 140); also used by `OpenLemmas.lean` and `OpenLemmaPrimitives.lean`
- **Visibility**: public
- **Lines**: 104–122, proof length ~12 lines
- **Notes**: Proof is the longest in the file at ~12 lines (well under 30). The `show` tactic at line 119–120 uses a `rfl` to rewrite the composition pullback.

---

### `theorem verschiebungIsog_isDualOf_frobenius_of_factor`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] → (h_factor : ∃ ψ : Isogeny W.toAffine W.toAffine, ψ.comp (frobeniusIsog W) = mulByInt W.toAffine (Fintype.card K : ℕ : ℤ)) → IsDualOf W.toAffine (verschiebungIsog_of_witness W (mulByInt_q_pullback_image_subset_frobenius_of_element_witness W (qth_root_of_q_factors_through_frobenius W h_factor))) (frobeniusIsog W)`
- **What**: From a single factorization hypothesis ψ ∘ φ_q = [q], produces the full IsDualOf certificate for the Verschiebung (both compositions equal [q]).
- **How**: Chains `qth_root_of_q_factors_through_frobenius` and `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness` in one line.
- **Hypotheses**: W elliptic over finite field K; [q] factors through Frobenius.
- **Uses from project**: `qth_root_of_q_factors_through_frobenius` (this file), `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness` (this file), `mulByInt_q_pullback_image_subset_frobenius_of_element_witness` (PurelyInsep.lean), `verschiebungIsog_of_witness` (IsDual.lean), `frobeniusIsog` (Frobenius.lean)
- **Used by**: Used by `GapSpines.lean` (line 66)
- **Visibility**: public
- **Lines**: 129–140, proof length ~2 lines
- **Notes**: None.

---

### `theorem mulByInt_q_factor_isog_of_subset_witness`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] → (h_subset : (mulByInt W.toAffine (Fintype.card K : ℕ : ℤ)).pullback.range ≤ (frobeniusIsog W).pullback.range) → ∃ ψ : Isogeny W.toAffine W.toAffine, ψ.comp (frobeniusIsog W) = mulByInt W.toAffine (Fintype.card K : ℕ : ℤ)`
- **What**: Packages the Session 3 inclusion `Im([q]*) ⊆ Im(φ_q*)` into the existential factorization form ψ ∘ φ_q = [q], by taking ψ = verschiebungIsog_of_witness.
- **How**: Constructs the witness pair directly from `verschiebungIsog_of_witness` and `verschiebung_comp_frobenius_eq_mulByInt_q` (IsDual.lean).
- **Hypotheses**: W elliptic; [q]-pullback range contained in Frobenius-pullback range.
- **Uses from project**: `verschiebungIsog_of_witness` (IsDual.lean), `verschiebung_comp_frobenius_eq_mulByInt_q` (IsDual.lean), `frobeniusIsog` (Frobenius.lean), `mulByInt`
- **Used by**: `Conditional.iterated_silverman_II_2_12_of_subset_witness` (line 193); also used by `GapSpines.lean` (line 59)
- **Visibility**: public
- **Lines**: 147–156, proof length ~2 lines
- **Notes**: None.

---

### `namespace Conditional`

(Opens at line 175, closes at line 196; contains one theorem.)

---

### `theorem Conditional.iterated_silverman_II_2_12_of_subset_witness`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] → (h_subset : (mulByInt W.toAffine (Fintype.card K : ℕ : ℤ)).pullback.range ≤ (frobeniusIsog W).pullback.range) → (∃ ψ : Isogeny W.toAffine W.toAffine, ψ.comp (frobeniusIsog W) = mulByInt W.toAffine (Fintype.card K : ℕ : ℤ)) ∧ IsDualOf W.toAffine (verschiebungIsog_of_witness W h_subset) (frobeniusIsog W)`
- **What**: The conditional Silverman II.2.12 (iterated): from the Session 3 pullback-range inclusion, the multiplication-by-q map factors as ψ ∘ φ_q AND the Verschiebung-is-dual certificate holds simultaneously.
- **How**: `refine ⟨mulByInt_q_factor_isog_of_subset_witness W h_subset, ?_⟩` then `exact verschiebungIsog_of_witness_isDualOf_frobenius W h_subset`.
- **Hypotheses**: W elliptic; pullback-range inclusion hypothesis.
- **Uses from project**: `mulByInt_q_factor_isog_of_subset_witness` (this file), `verschiebungIsog_of_witness_isDualOf_frobenius` (IsDual.lean), `verschiebungIsog_of_witness` (IsDual.lean), `frobeniusIsog` (Frobenius.lean)
- **Used by**: unused in file (dead-code candidate; may be used by other files)
- **Visibility**: public (inside `Conditional` namespace)
- **Lines**: 183–194, proof length ~3 lines
- **Notes**: Namespace `Conditional` makes explicit that the inclusion hypothesis is upstream substantive content.

---

### `theorem hasse_bound_witness_parametric_assembled`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] → (hq : 2 ≤ Fintype.card K) → (h_pc_sep : ...) → (h_pc_fin : ...) → (h_sepDeg_eq_pointCount : ...) → [h_pc_ker_finite : ...] → (h_qf_nonneg : ∀ r s : ℤ, 0 ≤ q * r² − trace(π, 1−π̄) * r * s + s²) → |#E(F_q) − q − 1| ≤ 2√q`
- **What**: The Hasse-Weil bound `|#E(F_q) − q − 1| ≤ 2√q`, witness-parametric on the standard deferred witnesses (separability of 1−π̄, finite-dimensional function field, sepDegree = pointCount, signed quadratic form non-negativity).
- **How**: Immediate delegation to `hasse_bound_via_signed_QF_negFrobenius_qf_nonneg` from `HoleE.lean`.
- **Hypotheses**: Elliptic curve over finite field K with #K ≥ 2; finiteness of points; separability, finite-dim, sepDeg = pointCount witnesses; QF non-negativity.
- **Uses from project**: `isogOneSub_negFrobenius` (HoleE.lean or related), `isogTrace` (related), `pointCount`, `frobeniusIsog` (Frobenius.lean), `hasse_bound_via_signed_QF_negFrobenius_qf_nonneg` (HoleE.lean)
- **Used by**: `hasse_bound_sq_witness_parametric_assembled` (line 253 — oh wait, that calls `hasse_bound_sq_via_signed_QF_negFrobenius_qf_nonneg` directly), `hasse_bound_witness_parametric_assembled_q_three` (line 361), `hasse_bound_witness_parametric_assembled_q_five` (line 427), `hasse_bound_witness_parametric_assembled_q_seven` (line 498), `hasse_bound_for_finite_field` (line 586)
- **Visibility**: public
- **Lines**: 216–233, proof length ~1 line
- **Notes**: This is the first time the Hasse-Weil bound `|#E(F_q) − q − 1| ≤ 2√q` appears as a typed theorem, per the doc-string.

---

### `theorem hasse_bound_sq_witness_parametric_assembled`

- **Type**: Same witnesses as `hasse_bound_witness_parametric_assembled`, conclusion is `(#E(F_q) − q − 1)² ≤ 4q` as integers.
- **What**: Squared-integer form of the Hasse-Weil bound.
- **How**: Delegates to `hasse_bound_sq_via_signed_QF_negFrobenius_qf_nonneg` (HoleE.lean).
- **Hypotheses**: Same as `hasse_bound_witness_parametric_assembled`.
- **Uses from project**: `isogOneSub_negFrobenius`, `isogTrace`, `pointCount`, `frobeniusIsog`, `hasse_bound_sq_via_signed_QF_negFrobenius_qf_nonneg` (HoleE.lean)
- **Used by**: `hasse_bound_sq_witness_parametric_assembled_q_three` (line 386), `hasse_bound_sq_witness_parametric_assembled_q_five` (line 451), `hasse_bound_sq_witness_parametric_assembled_q_seven` (line 522)
- **Visibility**: public
- **Lines**: 237–254, proof length ~1 line
- **Notes**: None.

---

### `theorem mulByInt_three_pullback_cube_root_q_three_char_three`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 3] → (h_card : Fintype.card K = 3) → (h_y_cube : ...) → (h_x_cube : ...) → (h_xy_subfield : ∀ z, ∃ g, g^3 = [3]^*z) → ∀ z, ∃ g, g^3 = [3]^*z`
- **What**: A trivial bridge for q=3: given the universal cube-root function as a hypothesis `h_xy_subfield`, it simply returns that hypothesis. The other hypotheses (`h_y_cube`, `h_x_cube`) are not used in the body.
- **How**: The proof body is just `h_xy_subfield` — the conclusion IS the hypothesis.
- **Hypotheses**: [CharP K 3]; Fintype.card K = 3; cube-root witnesses for y_gen, x_gen, and all elements.
- **Uses from project**: `mulByInt`, `x_gen` (basic curve declarations)
- **Used by**: unused in file (dead-code candidate)
- **Visibility**: public
- **Lines**: 272–288, proof length ~1 line
- **Notes**: This theorem is vacuously trivial — it discards `h_y_cube` and `h_x_cube` and just returns `h_xy_subfield`. It appears to be scaffolding/documentation of the expected witness structure for q=3.

---

### `theorem verschiebungIsog_isDualOf_frobenius_q_three_char_three`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] [CharP K 3] → (h_card : Fintype.card K = 3) → (h_cube_root : ∀ z, ∃ g, g^3 = [3]^*z) → IsDualOf W.toAffine (verschiebungIsog_of_witness W (mulByInt_q_pullback_image_subset_frobenius_of_element_witness W h_cube_root)) (frobeniusIsog W)`
- **What**: Q=3 char=3 specialization of `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness`.
- **How**: Direct application of `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness`.
- **Hypotheses**: [CharP K 3]; Fintype.card K = 3; universal cube-root function.
- **Uses from project**: `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness` (this file), `mulByInt_q_pullback_image_subset_frobenius_of_element_witness` (PurelyInsep.lean), `verschiebungIsog_of_witness` (IsDual.lean), `frobeniusIsog`
- **Used by**: unused in file (dead-code candidate)
- **Visibility**: public
- **Lines**: 301–312, proof length ~1 line
- **Notes**: Pure specialization wrapper.

---

### `theorem hasse_bound_witness_parametric_assembled_q_three`

- **Type**: Same as `hasse_bound_witness_parametric_assembled` with `[CharP K 3]` and `h_card : Fintype.card K = 3` added; hq replaced by `(h_card ▸ by decide : 2 ≤ Fintype.card K)`.
- **What**: Hasse-Weil bound for q=3 char=3.
- **How**: Delegates to `hasse_bound_witness_parametric_assembled`.
- **Hypotheses**: Same as parametric version, specialized to char 3 / card 3.
- **Uses from project**: `hasse_bound_witness_parametric_assembled` (this file), `isogOneSub_negFrobenius`, `isogTrace`, `pointCount`, `frobeniusIsog`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 342–363, proof length ~2 lines
- **Notes**: The `h_card ▸ by decide` idiom appears 4 times in the signature to unify the `hq` proof.

---

### `theorem hasse_bound_sq_witness_parametric_assembled_q_three`

- **Type**: Same witnesses as `hasse_bound_witness_parametric_assembled_q_three`; conclusion `(#E − q − 1)² ≤ 4q`.
- **What**: Squared bound for q=3 char=3.
- **How**: Delegates to `hasse_bound_sq_witness_parametric_assembled`.
- **Hypotheses**: Same as `hasse_bound_witness_parametric_assembled_q_three`.
- **Uses from project**: `hasse_bound_sq_witness_parametric_assembled` (this file), `isogOneSub_negFrobenius`, `isogTrace`, `frobeniusIsog`, `pointCount`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 367–388, proof length ~2 lines
- **Notes**: None.

---

### `theorem hasse_bound_witness_parametric_assembled_q_five`

- **Type**: Same parametric form with `[CharP K 5]` and `Fintype.card K = 5`.
- **What**: Hasse-Weil bound for q=5 char=5. Third prime milestone.
- **How**: Delegates to `hasse_bound_witness_parametric_assembled`.
- **Hypotheses**: Standard witnesses, specialized to char 5.
- **Uses from project**: `hasse_bound_witness_parametric_assembled` (this file), `isogOneSub_negFrobenius`, `isogTrace`, `pointCount`, `frobeniusIsog`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 408–429, proof length ~2 lines
- **Notes**: Direct transposition of q=3 shape.

---

### `theorem hasse_bound_sq_witness_parametric_assembled_q_five`

- **Type**: Squared bound for q=5 char=5.
- **What**: Integer squared form of the Hasse bound for q=5 char=5.
- **How**: Delegates to `hasse_bound_sq_witness_parametric_assembled`.
- **Hypotheses**: Same as `hasse_bound_witness_parametric_assembled_q_five`.
- **Uses from project**: `hasse_bound_sq_witness_parametric_assembled` (this file), `isogOneSub_negFrobenius`, `isogTrace`, `pointCount`, `frobeniusIsog`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 432–453, proof length ~2 lines
- **Notes**: None.

---

### `theorem verschiebungIsog_isDualOf_frobenius_q_five_char_five`

- **Type**: `[CharP K 5] → (h_card : Fintype.card K = 5) → (h_fifth_root : ∀ z, ∃ g, g^5 = [5]^*z) → IsDualOf ...`
- **What**: Q=5 char=5 specialization of `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness`.
- **How**: Direct application.
- **Hypotheses**: [CharP K 5]; Fintype.card K = 5; universal 5th-root function.
- **Uses from project**: `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness` (this file), `mulByInt_q_pullback_image_subset_frobenius_of_element_witness`, `verschiebungIsog_of_witness`, `frobeniusIsog`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 458–469, proof length ~1 line
- **Notes**: None.

---

### `theorem hasse_bound_witness_parametric_assembled_q_seven`

- **Type**: Same parametric form with `[CharP K 7]` and `Fintype.card K = 7`. Fourth prime milestone.
- **What**: Hasse-Weil bound for q=7 char=7.
- **How**: Delegates to `hasse_bound_witness_parametric_assembled`.
- **Hypotheses**: Standard witnesses specialized to char 7.
- **Uses from project**: `hasse_bound_witness_parametric_assembled` (this file), `isogOneSub_negFrobenius`, `isogTrace`, `pointCount`, `frobeniusIsog`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 479–500, proof length ~2 lines
- **Notes**: None.

---

### `theorem hasse_bound_sq_witness_parametric_assembled_q_seven`

- **Type**: Squared bound for q=7 char=7.
- **What**: Integer squared form of the Hasse bound for q=7.
- **How**: Delegates to `hasse_bound_sq_witness_parametric_assembled`.
- **Hypotheses**: Same as `hasse_bound_witness_parametric_assembled_q_seven`.
- **Uses from project**: `hasse_bound_sq_witness_parametric_assembled` (this file), `isogOneSub_negFrobenius`, `isogTrace`, `pointCount`, `frobeniusIsog`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 503–524, proof length ~2 lines
- **Notes**: None.

---

### `theorem verschiebungIsog_isDualOf_frobenius_q_seven_char_seven`

- **Type**: `[CharP K 7] → (h_card : Fintype.card K = 7) → (h_seventh_root : ∀ z, ∃ g, g^7 = [7]^*z) → IsDualOf ...`
- **What**: Q=7 char=7 specialization of `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness`.
- **How**: Direct application.
- **Hypotheses**: [CharP K 7]; Fintype.card K = 7; universal 7th-root function.
- **Uses from project**: `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness` (this file), `mulByInt_q_pullback_image_subset_frobenius_of_element_witness`, `verschiebungIsog_of_witness`, `frobeniusIsog`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 527–538, proof length ~1 line
- **Notes**: None.

---

### `theorem hasse_bound_for_finite_field`

- **Type**: Same signature as `hasse_bound_witness_parametric_assembled` (pure re-export).
- **What**: The Hasse-Weil bound `|#E(F_q) − q − 1| ≤ 2√q` for all finite fields F_q (any prime power q ≥ 2), with a name emphasizing its fully parametric nature.
- **How**: Delegates to `hasse_bound_witness_parametric_assembled`.
- **Hypotheses**: Same as `hasse_bound_witness_parametric_assembled`.
- **Uses from project**: `hasse_bound_witness_parametric_assembled` (this file)
- **Used by**: `hasse_bound_F_four` (line 613), `hasse_bound_F_nine` (line 636)
- **Visibility**: public
- **Lines**: 570–587, proof length ~2 lines
- **Notes**: Explicitly documented as a re-export of `hasse_bound_witness_parametric_assembled` for clarity.

---

### `theorem hasse_bound_F_four`

- **Type**: `[CharP K 2] → (h_card : Fintype.card K = 4) → [standard witnesses] → |#E(F_4) − 4 − 1| ≤ 2√4`
- **What**: Hasse-Weil bound for F_4 = F_{2^2}; demonstrates parametric coverage of F_{p^k} with k ≥ 2.
- **How**: Delegates to `hasse_bound_for_finite_field` with `h_card ▸ by decide`.
- **Hypotheses**: [CharP K 2]; Fintype.card K = 4; standard witnesses.
- **Uses from project**: `hasse_bound_for_finite_field` (this file), `isogOneSub_negFrobenius`, `isogTrace`, `pointCount`, `frobeniusIsog`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 594–614, proof length ~2 lines
- **Notes**: None.

---

### `theorem hasse_bound_F_nine`

- **Type**: `[CharP K 3] → (h_card : Fintype.card K = 9) → [standard witnesses] → |#E(F_9) − 9 − 1| ≤ 2√9`
- **What**: Hasse-Weil bound for F_9 = F_{3^2}.
- **How**: Delegates to `hasse_bound_for_finite_field`.
- **Hypotheses**: [CharP K 3]; Fintype.card K = 9; standard witnesses.
- **Uses from project**: `hasse_bound_for_finite_field` (this file), `isogOneSub_negFrobenius`, `isogTrace`, `pointCount`, `frobeniusIsog`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 617–637, proof length ~2 lines
- **Notes**: None.

---

## Cross-reference summary

### Key API (used by 3+ other declarations in this file)

- `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness`: used by 4 declarations (lines 139, 312, 469, 538)
- `hasse_bound_witness_parametric_assembled`: used by 4 declarations (lines 361, 427, 498, 586)
- `hasse_bound_sq_witness_parametric_assembled`: used by 3 declarations (lines 386, 451, 522)

### Declarations with no internal callers (dead-code candidates within this file)

- `Conditional.iterated_silverman_II_2_12_of_subset_witness`
- `mulByInt_three_pullback_cube_root_q_three_char_three`
- `verschiebungIsog_isDualOf_frobenius_q_three_char_three`
- `hasse_bound_witness_parametric_assembled_q_three`
- `hasse_bound_sq_witness_parametric_assembled_q_three`
- `hasse_bound_witness_parametric_assembled_q_five`
- `hasse_bound_sq_witness_parametric_assembled_q_five`
- `verschiebungIsog_isDualOf_frobenius_q_five_char_five`
- `hasse_bound_witness_parametric_assembled_q_seven`
- `hasse_bound_sq_witness_parametric_assembled_q_seven`
- `verschiebungIsog_isDualOf_frobenius_q_seven_char_seven`
- `hasse_bound_F_four`
- `hasse_bound_F_nine`

(Note: several of these — particularly the per-prime `_q_three/_q_five/_q_seven` variants and `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness` — ARE used by other files in the project.)
