# Inventory: ./HasseWeil/Verschiebung/PurelyInsep.lean

**File summary**: 12 declarations (2 defs/abbrevs, 9 theorems, 1 instance). 0 sorries. 1 `set_option` (not `maxHeartbeats`). 0 long proofs (>30 lines). Proves `IsPurelyInseparable (frobeniusIsog_intermediateField W) (FunctionField W)` and provides the element-wise membership API for the Frobenius pullback range. Key API: `frobeniusIsog_subalgebra` (used 4×), `frobeniusIsog_intermediateField` (used 5×).

---

### `theorem mulByInt_q_apply_mem_range`
- **Type**: `(z : W.toAffine.FunctionField) → (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z ∈ (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range`
- **What**: Every element of K(E) lies in the range of the [q]*-pullback. Trivial pointer lemma.
- **How**: One-line anonymous constructor `⟨z, rfl⟩` — the element witnesses itself.
- **Hypotheses**: K finite field, W an elliptic curve.
- **Uses from project**: `mulByInt` (via import)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: L80–83, proof length 1 line
- **Notes**: Likely a scaffolding lemma; not referenced in the file and may be used externally only.

---

### `theorem mem_frobenius_range_iff`
- **Type**: `(f : W.toAffine.FunctionField) → f ∈ (frobeniusIsog W).pullback.range ↔ ∃ g, g ^ Fintype.card K = f`
- **What**: Characterizes membership in the Frobenius pullback range as being a q-th power (using π* x = x^q).
- **How**: Both directions use `frobeniusIsog_pullback_apply` (from `HasseWeil/Frobenius.lean`) which states π* f = f^q. The iff is discharged by rewriting along this identity.
- **Hypotheses**: K finite field, W an elliptic curve.
- **Uses from project**: `frobeniusIsog_pullback_apply` (Frobenius.lean), `frobeniusIsog` (FrobeniusIsogeny.lean)
- **Used by**: `frobeniusIsog_subalgebra_inv_mem`, `mem_frobeniusIsog_intermediateField_iff`
- **Visibility**: public
- **Lines**: L87–99, proof length ~10 lines
- **Notes**: Core characterization lemma used by the `IsPurelyInseparable` instance pipeline.

---

### `noncomputable abbrev frobeniusIsog_subalgebra`
- **Type**: `Subalgebra K W.toAffine.FunctionField`
- **What**: Abbreviation for the Subalgebra `(frobeniusIsog W).pullback.range` — the image of the Frobenius isogeny pullback in K(E).
- **How**: Direct definitional abbreviation; no proof content.
- **Hypotheses**: K finite field, W an elliptic curve.
- **Uses from project**: `frobeniusIsog` (FrobeniusIsogeny.lean)
- **Used by**: `pow_card_mem_frobenius_subalgebra`, `frobeniusIsog_subalgebra_inv_mem`, `frobeniusIsog_intermediateField`, `pow_card_mem_frobeniusIsog_intermediateField`
- **Visibility**: public
- **Lines**: L109–110, proof length N/A (abbrev)
- **Notes**: Key abbreviation used by 4+ other declarations in this file.

---

### `theorem pow_card_mem_frobenius_subalgebra`
- **Type**: `(x : W.toAffine.FunctionField) → x ^ Fintype.card K ∈ frobeniusIsog_subalgebra W`
- **What**: Every element of K(E) has its q-th power in the Frobenius pullback subalgebra, i.e., x^q = π*(x) ∈ Im(π*).
- **How**: Provides the witness `x` directly and rewrites using `frobeniusIsog_pullback_apply`.
- **Hypotheses**: K finite field, W an elliptic curve.
- **Uses from project**: `frobeniusIsog_subalgebra` (this file), `frobeniusIsog_pullback_apply` (Frobenius.lean)
- **Used by**: `pow_card_mem_frobeniusIsog_intermediateField`
- **Visibility**: public
- **Lines**: L114–118, proof length 4 lines
- **Notes**: Immediate consequence of `frobeniusIsog_pullback_apply`.

---

### `theorem frobeniusIsog_subalgebra_inv_mem`
- **Type**: `(f : W.toAffine.FunctionField) → f ∈ frobeniusIsog_subalgebra W → f⁻¹ ∈ frobeniusIsog_subalgebra W`
- **What**: The Frobenius pullback subalgebra is closed under field inversion: (g^q)⁻¹ = (g⁻¹)^q.
- **How**: Uses `mem_frobenius_range_iff` to extract a q-th root `g`, then provides `g⁻¹` as the q-th root of `f⁻¹` via `inv_pow`.
- **Hypotheses**: K finite field, W an elliptic curve.
- **Uses from project**: `mem_frobenius_range_iff` (this file), `frobeniusIsog_subalgebra` (this file)
- **Used by**: `frobeniusIsog_intermediateField`
- **Visibility**: public
- **Lines**: L128–133, proof length 4 lines
- **Notes**: Required to promote the Subalgebra to an IntermediateField.

---

### `noncomputable def frobeniusIsog_intermediateField`
- **Type**: `IntermediateField K W.toAffine.FunctionField`
- **What**: Promotes the Frobenius pullback subalgebra to an `IntermediateField` by supplying the inverse-closure witness. This field-typed carrier is needed to attach the `IsPurelyInseparable` typeclass.
- **How**: Calls `Subalgebra.toIntermediateField` with the inverse-closure proof `frobeniusIsog_subalgebra_inv_mem`.
- **Hypotheses**: K finite field, W an elliptic curve.
- **Uses from project**: `frobeniusIsog_subalgebra` (this file), `frobeniusIsog_subalgebra_inv_mem` (this file)
- **Used by**: `mem_frobeniusIsog_intermediateField_iff`, `pow_card_mem_frobeniusIsog_intermediateField`, `pow_card_mem_algebraMap_range`, `frobeniusIsog_intermediateField_isPurelyInseparable`, `frobeniusIsog_intermediateField_eq_fieldRange`, `mulByInt_q_pullback_image_subset_frobenius_of_element_witness` (indirectly)
- **Visibility**: public
- **Lines**: L139–142, proof length N/A (def by term)
- **Notes**: Key definition — the pivot for the `IsPurelyInseparable` instance.

---

### `theorem mem_frobeniusIsog_intermediateField_iff`
- **Type**: `(f : W.toAffine.FunctionField) → f ∈ frobeniusIsog_intermediateField W ↔ ∃ g, g ^ Fintype.card K = f`
- **What**: Membership in `frobeniusIsog_intermediateField W` is equivalent to being a q-th power — lifting `mem_frobenius_range_iff` to the IntermediateField level.
- **How**: Direct application of `mem_frobenius_range_iff`; trivially true since the IntermediateField has the same carrier.
- **Hypotheses**: K finite field, W an elliptic curve.
- **Uses from project**: `frobeniusIsog_intermediateField` (this file), `mem_frobenius_range_iff` (this file)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: L145–148, proof length 1 line (term)
- **Notes**: Convenience re-export; may only be used by external files.

---

### `theorem pow_card_mem_frobeniusIsog_intermediateField`
- **Type**: `(x : W.toAffine.FunctionField) → x ^ Fintype.card K ∈ frobeniusIsog_intermediateField W`
- **What**: Every element of K(E) has its q-th power in the IntermediateField `frobeniusIsog_intermediateField W`.
- **How**: Direct lift of `pow_card_mem_frobenius_subalgebra` — the IntermediateField has the same carrier as the subalgebra.
- **Hypotheses**: K finite field, W an elliptic curve.
- **Uses from project**: `pow_card_mem_frobenius_subalgebra` (this file), `frobeniusIsog_intermediateField` (this file)
- **Used by**: `pow_card_mem_algebraMap_range`
- **Visibility**: public
- **Lines**: L152–154, proof length 1 line (term)
- **Notes**: Minimal bridge lemma from subalgebra to intermediate field level.

---

### `theorem pow_card_mem_algebraMap_range`
- **Type**: `(x : W.toAffine.FunctionField) → x ^ Fintype.card K ∈ (algebraMap (frobeniusIsog_intermediateField W) W.toAffine.FunctionField).range`
- **What**: Re-expresses the q-th power membership in the form `algebraMap.range` required by `isPurelyInseparable_iff_pow_mem`.
- **How**: Provides the element `⟨x ^ Fintype.card K, _⟩` as the preimage, with membership from `pow_card_mem_frobeniusIsog_intermediateField`.
- **Hypotheses**: K finite field, W an elliptic curve.
- **Uses from project**: `pow_card_mem_frobeniusIsog_intermediateField` (this file), `frobeniusIsog_intermediateField` (this file)
- **Used by**: `frobeniusIsog_intermediateField_isPurelyInseparable`
- **Visibility**: public
- **Lines**: L160–164, proof length 4 lines
- **Notes**: Adapter lemma to match the `algebraMap.range` form expected by mathlib's `IsPurelyInseparable` API.

---

### `instance frobeniusIsog_intermediateField_isPurelyInseparable`
- **Type**: `IsPurelyInseparable (frobeniusIsog_intermediateField W) W.toAffine.FunctionField`
- **What**: The extension K(E)/Im(π*) is purely inseparable — every element of K(E) has a p-power-th power in Im(π*). This is Silverman III.6.2 step for the Frobenius range.
- **How**: Destructs `FiniteField.card'` to get `q = p^n`, makes `p.Prime` a `Fact`, applies `isPurelyInseparable_iff_pow_mem` at prime `p`, then uses `pow_card_mem_algebraMap_range` after rewriting `p^n = Fintype.card K`.
- **Hypotheses**: K finite field (and hence has prime characteristic with `q = p^n`), W an elliptic curve.
- **Uses from project**: `pow_card_mem_algebraMap_range` (this file), `frobeniusIsog_intermediateField` (this file)
- **Used by**: unused in file (primary export)
- **Visibility**: public
- **Lines**: L166–181 (with `set_option`), proof length ~12 lines
- **Notes**: Has `set_option backward.isDefEq.respectTransparency false` — no justifying comment present. The `isPurelyInseparable_iff_pow_mem` mathlib lemma is the key tool.

---

### `theorem frobeniusIsog_intermediateField_eq_fieldRange`
- **Type**: `frobeniusIsog_intermediateField W = (frobeniusIsog W).pullback.fieldRange`
- **What**: The constructed `IntermediateField` agrees with the canonical `AlgHom.fieldRange` of the Frobenius pullback map.
- **How**: Uses `IntermediateField.toSubalgebra_injective` and `rfl` — both have the same carrier by construction.
- **Hypotheses**: K finite field, W an elliptic curve.
- **Uses from project**: `frobeniusIsog_intermediateField` (this file), `frobeniusIsog` (FrobeniusIsogeny.lean)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: L188–192, proof length 3 lines
- **Notes**: Bridge lemma for transferring `finrank` facts proved for `fieldRange` to the `frobeniusIsog_intermediateField` form. Possibly only used externally (Route B).

---

### `theorem mulByInt_q_pullback_image_subset_frobenius_of_element_witness`
- **Type**: Given `h_qth_root : ∀ z, ∃ g, g ^ Fintype.card K = (mulByInt W.toAffine (Fintype.card K : ℤ)).pullback z`, then `(mulByInt W.toAffine (Fintype.card K : ℤ)).pullback.range ≤ (frobeniusIsog W).pullback.range`
- **What**: Element-wise witness form: given a function producing q-th roots for every [q]*-pullback element, the inclusion Im([q]*) ⊆ Im(π*) holds.
- **How**: Directly delegates to `mulByInt_q_pullback_image_subset_frobenius_witness` from `HasseWeil/Verschiebung/FieldTower.lean`.
- **Hypotheses**: The q-th root hypothesis `h_qth_root` (that every [q]*-pullback element is a q-th power in K(E)).
- **Uses from project**: `mulByInt_q_pullback_image_subset_frobenius_witness` (FieldTower.lean)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: L234–242, proof length 1 line (term)
- **Notes**: Parametric/witness form; the unconditional discharge requires Silverman III.6.1 degree decomposition (not yet in the project). Re-exports the FieldTower lemma with a different name.
