# Inventory: ./HasseWeil/Verschiebung/Construction.lean

**File**: `HasseWeil/Verschiebung/Construction.lean`
**Lines**: 156 total
**Import**: `HasseWeil.Verschiebung.FieldTower`
**Namespace**: `HasseWeil`
**Variables**: `{K : Type*} [Field K] [Fintype K] [DecidableEq K]`, `(W : WeierstrassCurve K) [W.toAffine.IsElliptic]`

## Summary

This file constructs the Verschiebung pullback `V* : K(E) →ₐ[K] K(E)` from the Session 3 inclusion witness `Im([q]*) ⊆ Im(π*)`, and proves the factoring identity `[q]* = π* ∘ V*`. The construction has 5 declarations: 3 defs and 2 theorems, no sorries, no `set_option maxHeartbeats`, no long proofs.

---

## Declarations

### `noncomputable def frobeniusIsog_rangeEquiv`

- **Type**: `W.toAffine.FunctionField ≃ₐ[K] (frobeniusIsog W).pullback.range`
- **What**: The Frobenius isogeny's pullback, viewed as an `AlgEquiv` onto its range subalgebra. This is the canonical `K(E) ≃ₐ[K] Im(π*)`.
- **How**: Single call to `AlgEquiv.ofInjective`, exploiting that any AlgHom between fields is injective (via `.toRingHom.injective`).
- **Hypotheses**: `W` an elliptic curve over a finite field `K`.
- **Uses from project**: `frobeniusIsog` (imported via `FieldTower`)
- **Used by**: `frobeniusIsog_rangeEquiv_apply`, `mulByInt_q_pullback_restricted`, `verschiebungPullback_of_witness`, `mulByInt_q_factor_via_witness`
- **Visibility**: public
- **Lines**: 58–62, proof length 1 line (term-mode)
- **Notes**: `noncomputable` as expected for function-field constructions.

---

### `@[simp] theorem frobeniusIsog_rangeEquiv_apply`

- **Type**: `∀ (z : W.toAffine.FunctionField), ((frobeniusIsog_rangeEquiv W) z : W.toAffine.FunctionField) = (frobeniusIsog W).pullback z`
- **What**: The coercion of `frobeniusIsog_rangeEquiv` back to the ambient `K(E)` equals the Frobenius pullback directly. This is the expected definitional simp lemma for the range equivalence.
- **How**: `simp [frobeniusIsog_rangeEquiv]` unfolds the definition; `AlgEquiv.ofInjective` carries the natural coercion property.
- **Hypotheses**: None beyond the ambient variables.
- **Uses from project**: `frobeniusIsog_rangeEquiv` (this file)
- **Used by**: `mulByInt_q_factor_via_witness`
- **Visibility**: public (`@[simp]`)
- **Lines**: 66–69, proof length 1 line
- **Notes**: Tagged `@[simp]`; used in the factoring identity proof.

---

### `noncomputable def mulByInt_q_pullback_restricted`

- **Type**: `(h_subset : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤ (frobeniusIsog W).pullback.range) → W.toAffine.FunctionField →ₐ[K] (frobeniusIsog W).pullback.range`
- **What**: Given the Session 3 inclusion witness `h_subset`, restricts the codomain of `(mulByInt W q).pullback` so that it lands in the Frobenius image subalgebra. This is the intermediate step (K(E) → Im(π*)) before composing with π*⁻¹.
- **How**: Uses `AlgHom.codRestrict` with the membership proof `h_subset ⟨z, rfl⟩` (which says the image of any element lands in the Frobenius range).
- **Hypotheses**: The inclusion `Im([q]*) ⊆ Im(π*)` as an explicit witness `h_subset`.
- **Uses from project**: `frobeniusIsog` (via FieldTower), `mulByInt` (via FieldTower)
- **Used by**: `mulByInt_q_pullback_restricted_coe`, `verschiebungPullback_of_witness`, `mulByInt_q_factor_via_witness`
- **Visibility**: public
- **Lines**: 80–87, proof length 1 line (term-mode)
- **Notes**: `noncomputable`; witness-parametric design allows the downstream `verschiebungPullback_of_witness` to be used before Session 3's unconditional discharge.

---

### `@[simp] theorem mulByInt_q_pullback_restricted_coe`

- **Type**: `∀ (h_subset : ...) (z : W.toAffine.FunctionField), ((mulByInt_q_pullback_restricted W h_subset z) : W.toAffine.FunctionField) = (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z`
- **What**: The coercion of `mulByInt_q_pullback_restricted` back to `K(E)` equals `(mulByInt W q).pullback` directly. Definitionally trivial (`rfl`).
- **How**: Proof is `rfl` — the coercion from a `codRestrict`ed hom is definitionally equal to the original hom.
- **Hypotheses**: The inclusion witness `h_subset`.
- **Uses from project**: `mulByInt_q_pullback_restricted` (this file)
- **Used by**: `mulByInt_q_factor_via_witness`
- **Visibility**: public (`@[simp]`)
- **Lines**: 91–99, proof length 1 line
- **Notes**: Tagged `@[simp]`; the `rfl` proof confirms the codRestrict definitional reduction works cleanly.

---

### `noncomputable def verschiebungPullback_of_witness`

- **Type**: `(h_subset : ...) → W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField`
- **What**: The Verschiebung pullback `V* : K(E) →ₐ[K] K(E)`, constructed witness-parametrically as the composition `π*⁻¹ ∘ ([q]* restricted to Im(π*))`. This is the main object of the file.
- **How**: Composes `(frobeniusIsog_rangeEquiv W).symm.toAlgHom` with `mulByInt_q_pullback_restricted W h_subset` using `AlgHom.comp`.
- **Hypotheses**: The Session 3 inclusion witness `h_subset : Im([q]*) ⊆ Im(π*)`.
- **Uses from project**: `frobeniusIsog_rangeEquiv` (this file), `mulByInt_q_pullback_restricted` (this file)
- **Used by**: `mulByInt_q_factor_via_witness`; also used extensively in `HasseWeil/Verschiebung/IsDual.lean` and `HasseWeil/Hasse/OpenLemmaPrimitives.lean`
- **Visibility**: public
- **Lines**: 115–121, proof length 1 line (term-mode)
- **Notes**: `noncomputable`; the key definition of the entire Verschiebung module.

---

### `theorem mulByInt_q_factor_via_witness`

- **Type**: `(h_subset : ...) → (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback = (frobeniusIsog W).pullback.comp (verschiebungPullback_of_witness W h_subset)`
- **What**: The factoring identity `[q]* = π* ∘ V*`, derived from V*'s construction. This is the main theorem of the file, confirming the Verschiebung definition is correct.
- **How**: Applies `AlgHom.ext` to reduce to a pointwise equality. Then rewrites π*(V*z) by:
  1. `frobeniusIsog_rangeEquiv_apply` to rewrite π* in terms of the range equivalence;
  2. `AlgEquiv.apply_symm_apply` to cancel the symm/apply pair;
  3. `mulByInt_q_pullback_restricted_coe` to recover `(mulByInt W q).pullback z`.
  The intermediate `h_apply_pi` lemma handles the coercion from the range subalgebra back to `K(E)`.
- **Hypotheses**: The inclusion witness `h_subset`.
- **Uses from project**: `frobeniusIsog_rangeEquiv_apply` (this file), `mulByInt_q_pullback_restricted_coe` (this file), `verschiebungPullback_of_witness` (this file), `frobeniusIsog_rangeEquiv` (this file)
- **Visibility**: public
- **Lines**: 125–155, proof length ~30 lines (including comments and blank lines, ~20 tactic lines)
- **Notes**: No `sorry`. The proof is cleanly structured with an explicit local `have h_apply_pi` to handle the coercion step. Uses `AlgEquiv.apply_symm_apply` from mathlib. Used extensively in `IsDual.lean` and `OpenLemmaPrimitives.lean`.

---

## Cross-file usage summary

All 5 declarations are used by other files in the project:
- `verschiebungPullback_of_witness` and `mulByInt_q_factor_via_witness` are heavily used in `HasseWeil/Verschiebung/IsDual.lean` and `HasseWeil/Hasse/OpenLemmaPrimitives.lean`.
- `frobeniusIsog_rangeEquiv` is the key infrastructure shared within this file.

There are no declarations unused in the project. No sorries, no `set_option maxHeartbeats`, no proofs longer than 30 lines.
