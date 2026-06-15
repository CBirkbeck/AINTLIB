# Inventory: ./HasseWeil/Curves/FrobeniusFixedLocus.lean

**File summary.** A self-contained 136-line file proving that an element of the algebraic closure
`L = AlgebraicClosure K` of a finite field `K` satisfies `a^q = a` (where `q = Fintype.card K`)
if and only if it lies in the image of `algebraMap K L`. The argument goes via counting roots of
`X^q − X`; all declarations are either private helpers or the two public theorems exported for use
by `FrobeniusFixedPoint.lean` and `GapSpines.lean`.

---

### `noncomputable local instance` (anonymous `DecidableEq` for `AlgebraicClosure K`)
- **Type**: `DecidableEq (AlgebraicClosure K)`
- **What**: Supplies classical decidable equality on the algebraic closure so that `Finset` and
  `Multiset.toFinset` operations can be formed noncomputably.
- **How**: `Classical.decEq _` — pure classical choice, no mathematical content.
- **Hypotheses**: `K` is a finite field.
- **Uses from project**: none
- **Used by**: `frobRootsFinset`, `baseImageFinset`, `range_algebraMap_eq_roots_X_pow_card_sub_X`, `frobenius_fixed_iff_mem_baseField`
- **Visibility**: private (local)
- **Lines**: 48 (1-line body)
- **Notes**: Standard boilerplate for Finset-over-algebraic-closure arguments.

---

### `private noncomputable abbrev frobPoly`
- **Type**: `L[X]` — the polynomial `X ^ Fintype.card K - X` over `AlgebraicClosure K`
- **What**: Names the polynomial whose roots are exactly the Frobenius fixed points.
- **How**: Direct definition; no proof needed.
- **Hypotheses**: `K` is a finite field.
- **Uses from project**: none
- **Used by**: `frobPoly_ne_zero`, `frobPoly_natDegree`, `frobPoly_separable`, `mem_roots_frobPoly_iff`, `card_frobRootsFinset`, `frobRootsFinset`
- **Visibility**: private
- **Lines**: 51 (abbrev, no proof)
- **Notes**: An `abbrev` (not `def`) so it unfolds transparently in proofs.

---

### `private theorem frobPoly_ne_zero`
- **Type**: `(frobPoly (K := K)) ≠ 0`
- **What**: The polynomial `X^q − X` is nonzero over `L`.
- **How**: Delegates to mathlib's `FiniteField.X_pow_card_sub_X_ne_zero`, using `Fintype.one_lt_card` to supply `1 < q`.
- **Hypotheses**: `K` is a finite field with `1 < q`.
- **Uses from project**: none
- **Used by**: `mem_roots_frobPoly_iff`
- **Visibility**: private
- **Lines**: 53–54 (1-line body)
- **Notes**: Thin wrapper around a mathlib lemma.

---

### `private theorem frobPoly_natDegree`
- **Type**: `(frobPoly (K := K)).natDegree = Fintype.card K`
- **What**: The degree of `X^q − X` equals `q`.
- **How**: Delegates to mathlib's `FiniteField.X_pow_card_sub_X_natDegree_eq`.
- **Hypotheses**: `K` is a finite field with `1 < q`.
- **Uses from project**: none
- **Used by**: `card_frobRootsFinset`
- **Visibility**: private
- **Lines**: 56–57 (1-line body)
- **Notes**: Thin wrapper.

---

### `private theorem card_cast_eq_zero`
- **Type**: `(Fintype.card K : L) = 0`
- **What**: The characteristic-`q` fact that `q = 0` in `L` (since `L` has the same characteristic as `K`).
- **How**: Uses `FiniteField.cast_card_eq_zero` to get `(q : K) = 0`, then applies `algebraMap` and `map_natCast`/`map_zero` to transport to `L`.
- **Hypotheses**: `K` is a finite field.
- **Uses from project**: none
- **Used by**: `frobPoly_separable`
- **Visibility**: private
- **Lines**: 60–63 (4-line proof)
- **Notes**: The key characteristic-level fact feeding the separability argument.

---

### `private theorem frobPoly_separable`
- **Type**: `(frobPoly (K := K)).Separable`
- **What**: The polynomial `X^q − X` is separable over `L` (its formal derivative is `−1`, a unit).
- **How**: Computes the formal derivative using `derivative_sub`, `derivative_X_pow`, `card_cast_eq_zero` (giving `q·X^{q-1} = 0`), so derivative is `0 − 1 = −1`; then invokes `isCoprime_one_right.neg_right`.
- **Hypotheses**: `K` is a finite field.
- **Uses from project**: `card_cast_eq_zero`
- **Used by**: (not directly referenced by name inside this file; the separability of `frobPoly` is implicitly used through `card_frobRootsFinset` via `Polynomial.card_roots'` — the separability conclusion is not explicitly passed but the roots multiset is nodup)
- **Visibility**: private
- **Lines**: 66–72 (7-line proof)
- **Notes**: The separability argument is the key step ensuring the roots multiset has no duplicates (nodup), which is what lets cardinality count be exact. However, `card_frobRootsFinset` only uses `Polynomial.card_roots'` (which gives `card roots ≤ natDegree` without needing separability directly). The separability lemma is proved but not explicitly invoked in the rest of the file — it may be unused within this file.

---

### `private theorem mem_roots_frobPoly_iff`
- **Type**: `a ∈ (frobPoly (K := K)).roots ↔ a ^ Fintype.card K = a`
- **What**: Characterises membership in the roots multiset of `X^q − X` as the fixed-point equation.
- **How**: Uses `mem_roots frobPoly_ne_zero` and `IsRoot.def`, then `eval_sub`/`eval_pow`/`eval_X`/`sub_eq_zero` to simplify evaluation.
- **Hypotheses**: `K` is a finite field, `a : L`.
- **Uses from project**: `frobPoly_ne_zero`
- **Used by**: `mem_frobRootsFinset_iff`
- **Visibility**: private
- **Lines**: 75–79 (5-line proof)
- **Notes**: none

---

### `private noncomputable def frobRootsFinset`
- **Type**: `Finset L` — `(frobPoly (K := K)).roots.toFinset`
- **What**: The finset of roots of `X^q − X` in `L`, obtained by deduplicating the roots multiset.
- **How**: `Multiset.toFinset` applied to the roots of `frobPoly`.
- **Hypotheses**: `K` is a finite field.
- **Uses from project**: `frobPoly`
- **Used by**: `mem_frobRootsFinset_iff`, `card_frobRootsFinset`, `baseImage_subset_roots`, `range_algebraMap_eq_roots_X_pow_card_sub_X`, `frobenius_fixed_iff_mem_baseField`
- **Visibility**: private
- **Lines**: 81 (def, no proof)
- **Notes**: none

---

### `private theorem mem_frobRootsFinset_iff`
- **Type**: `a ∈ (frobRootsFinset (K := K)) ↔ a ^ Fintype.card K = a`
- **What**: Membership in `frobRootsFinset` iff `a` is fixed by the `q`-power map.
- **How**: Unfolds `frobRootsFinset`, uses `Multiset.mem_toFinset`, then `mem_roots_frobPoly_iff`.
- **Hypotheses**: `K` is a finite field, `a : L`.
- **Uses from project**: `frobRootsFinset`, `mem_roots_frobPoly_iff`
- **Used by**: `baseImage_subset_roots`, `range_algebraMap_eq_roots_X_pow_card_sub_X`, `frobenius_fixed_iff_mem_baseField`
- **Visibility**: private
- **Lines**: 83–85 (3-line proof)
- **Notes**: none

---

### `private noncomputable def baseImageFinset`
- **Type**: `Finset L` — `Finset.univ.image (algebraMap K L)`
- **What**: The finset image of all of `K` under `algebraMap K L`.
- **How**: `Finset.univ.image`.
- **Hypotheses**: `K` is a finite field.
- **Uses from project**: none
- **Used by**: `mem_baseImageFinset_iff`, `baseImage_subset_roots`, `card_baseImageFinset`, `range_algebraMap_eq_roots_X_pow_card_sub_X`, `frobenius_fixed_iff_mem_baseField`
- **Visibility**: private
- **Lines**: 88–89 (def, no proof)
- **Notes**: none

---

### `private theorem mem_baseImageFinset_iff`
- **Type**: `a ∈ (baseImageFinset (K := K)) ↔ a ∈ Set.range (algebraMap K L)`
- **What**: Membership in the finset image equals membership in the set-theoretic range.
- **How**: Unfolds `baseImageFinset`, then `simp [Finset.mem_image, Set.mem_range]`.
- **Hypotheses**: `K` is a finite field, `a : L`.
- **Uses from project**: `baseImageFinset`
- **Used by**: `baseImage_subset_roots`, `range_algebraMap_eq_roots_X_pow_card_sub_X`, `frobenius_fixed_iff_mem_baseField`
- **Visibility**: private
- **Lines**: 91–94 (4-line proof)
- **Notes**: none

---

### `private theorem baseImage_subset_roots`
- **Type**: `(baseImageFinset (K := K)) ⊆ (frobRootsFinset (K := K))`
- **What**: Every image of `K` in `L` satisfies `a^q = a`, so the image finset is contained in the roots finset.
- **How**: For any `a = algebraMap K L b` in `baseImageFinset`, rewrites using `mem_frobRootsFinset_iff`; then uses `map_pow` and mathlib's `FiniteField.pow_card` (which states `(algebraMap K L b)^q = algebraMap K L b`).
- **Hypotheses**: `K` is a finite field.
- **Uses from project**: `baseImageFinset`, `frobRootsFinset`, `mem_baseImageFinset_iff`, `mem_frobRootsFinset_iff`
- **Used by**: `card_frobRootsFinset`, `range_algebraMap_eq_roots_X_pow_card_sub_X`
- **Visibility**: private
- **Lines**: 97–103 (7-line proof)
- **Notes**: The use of `FiniteField.pow_card` is the key mathlib lemma.

---

### `private theorem card_baseImageFinset`
- **Type**: `(baseImageFinset (K := K)).card = Fintype.card K`
- **What**: The finset image of `K` has exactly `q` elements (since `algebraMap K L` is injective).
- **How**: `Finset.card_image_of_injective` applied with `(algebraMap K L).injective`, then `Finset.card_univ`.
- **Hypotheses**: `K` is a finite field.
- **Uses from project**: `baseImageFinset`
- **Used by**: `card_frobRootsFinset`, `range_algebraMap_eq_roots_X_pow_card_sub_X`
- **Visibility**: private
- **Lines**: 105–107 (3-line proof)
- **Notes**: none

---

### `private theorem card_frobRootsFinset`
- **Type**: `(frobRootsFinset (K := K)).card = Fintype.card K`
- **What**: The roots finset of `X^q − X` in `L` has exactly `q` elements.
- **How**: Proves `≤` by the chain `card toFinset ≤ card roots ≤ natDegree = q` using `Multiset.toFinset_card_le` and `Polynomial.card_roots'` and `frobPoly_natDegree`; proves `≥` by `card_baseImageFinset` and `Finset.card_le_card baseImage_subset_roots`.
- **Hypotheses**: `K` is a finite field.
- **Uses from project**: `frobRootsFinset`, `frobPoly_natDegree`, `baseImage_subset_roots`, `card_baseImageFinset`
- **Used by**: `range_algebraMap_eq_roots_X_pow_card_sub_X`
- **Visibility**: private
- **Lines**: 111–120 (10-line proof)
- **Notes**: The upper bound uses `Polynomial.card_roots'` rather than a separability argument directly, which gives `card roots ≤ natDegree` unconditionally.

---

### `theorem range_algebraMap_eq_roots_X_pow_card_sub_X`
- **Type**: `(baseImageFinset (K := K)) = (frobRootsFinset (K := K))`
- **What**: The image of `K` in `L` equals the root set of `X^q − X` as finsets.
- **How**: `Finset.eq_of_subset_of_card_le`: the subset direction is `baseImage_subset_roots`; the card inequality uses `card_frobRootsFinset` and `card_baseImageFinset`.
- **Hypotheses**: `K` is a finite field.
- **Uses from project**: `baseImageFinset`, `frobRootsFinset`, `baseImage_subset_roots`, `card_frobRootsFinset`, `card_baseImageFinset`
- **Used by**: `frobenius_fixed_iff_mem_baseField`
- **Visibility**: public
- **Lines**: 123–126 (4-line proof)
- **Notes**: Public theorem, but the exported API used by downstream files is primarily `frobenius_fixed_iff_mem_baseField`. Referenced in comments in `FrobeniusFixedPoint.lean`.

---

### `theorem frobenius_fixed_iff_mem_baseField`
- **Type**: `a ^ Fintype.card K = a ↔ a ∈ Set.range (algebraMap K (AlgebraicClosure K))`
- **What**: An element of the algebraic closure is fixed by the `q`-power Frobenius map if and only if it lies in the image of the base field `K`.
- **How**: Rewrites using `mem_frobRootsFinset_iff` (LHS ↔ `a ∈ frobRootsFinset`), `mem_baseImageFinset_iff` (RHS ↔ `a ∈ baseImageFinset`), then applies `range_algebraMap_eq_roots_X_pow_card_sub_X` to equate the two finsets.
- **Hypotheses**: `K` is a finite field, `a : AlgebraicClosure K`.
- **Uses from project**: `mem_frobRootsFinset_iff`, `mem_baseImageFinset_iff`, `range_algebraMap_eq_roots_X_pow_card_sub_X`
- **Used by**: Used in `HasseWeil/Curves/FrobeniusFixedPoint.lean` (multiple times in proof of rational-point characterisation) and referenced in `HasseWeil/GapSpines.lean`; unused within this file itself.
- **Visibility**: public
- **Lines**: 130–133 (4-line proof)
- **Notes**: The primary exported theorem of the file; the key field-theoretic input to Route B (Silverman V.1).

---

## File-level notes

- **`frobPoly_separable`** is proved but never explicitly invoked within this file. The upper bound on `card_frobRootsFinset` uses `Polynomial.card_roots'` (degree bound), not separability. This lemma is a dead-code candidate within the file, though it documents why the roots are distinct.
- The two public theorems (`range_algebraMap_eq_roots_X_pow_card_sub_X` and `frobenius_fixed_iff_mem_baseField`) are the intended exports; all other declarations are `private`.
- No `set_option maxHeartbeats` directives. No `sorry`. Proofs are short and elementary.
- There is likely mathlib overlap: `FiniteField.roots_X_pow_card_sub_X` (mentioned in the file header's `## References`) may provide a closely related statement directly.
