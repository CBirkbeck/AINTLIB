# Inventory: ./HasseWeil/Frobenius.lean

**File**: `HasseWeil/Frobenius.lean`
**Lines**: 1–317
**Imports**: `HasseWeil.Endomorphism`, `HasseWeil.FrobeniusIsogeny`, `HasseWeil.OrdAtInftyBridge`, `Mathlib.FieldTheory.Finite.Basic`
**No `set_option maxHeartbeats` occurrences. No `sorry` in any proof body.**

---

## Declarations

---

### `noncomputable def pointCount`

- **Type**: `(E : Affine F) [Fintype E.Point] : ℕ`
- **What**: Defines the number of F-rational points on an affine elliptic curve E over a finite field F, including the point at infinity, as the Fintype cardinality of E.Point.
- **How**: One-liner: `Fintype.card E.Point`.
- **Hypotheses**: F is a field, finite, with decidable equality; E.Point is a Fintype.
- **Uses from project**: none
- **Used by**: `pointCount_eq_of_witness` (this file); widely used in `GapSpines.lean`, `HasseWeilSkeleton.lean`, `Hasse/PointFix.lean`, `Hasse/BoundOfWitnesses.lean`
- **Visibility**: public
- **Lines**: 35–35, proof length: definition (no proof body)
- **Notes**: none

---

### `noncomputable def frobeniusIsog`

- **Type**: `Isogeny W.toAffine W.toAffine`
- **What**: Constructs the q-th power Frobenius endomorphism as an `Isogeny` over K: the pullback is `FiniteField.frobeniusAlgHom K` (sending f ↦ f^q), and the group homomorphism on K-rational points is the identity (since x^q = x for all x ∈ K).
- **How**: Structure fields set directly: `pullback := FiniteField.frobeniusAlgHom K W.toAffine.FunctionField` and `toAddMonoidHom := AddMonoidHom.id _`.
- **Hypotheses**: W is a Weierstrass curve over a finite field K with IsElliptic.
- **Uses from project**: none (uses mathlib's `FiniteField.frobeniusAlgHom`)
- **Used by**: `frobeniusIsog_pullback_apply`, `ordAtInfty_frobeniusIsog_pullback_x_gen`, `ordAtInfty_frobeniusIsog_pullback_y_gen`, `ordAtInfty_frobeniusIsog_pullback_x_gen_sub_x_gen`, `ordAtInfty_frobeniusIsog_pullback_y_gen_sub_y_gen`, `frobeniusIsog_degree`, `frobeniusIsog_pullback_universal_commute`, `frobeniusIsog_mulByInt_pullback_comm`, `frobeniusIsog_universal_commute_isog`, `frobeniusIsog_pullback_eq_pow_pow`, `frobeniusIsog_pullback_range`, `frobeniusIsog_pullback_mem_iff`, `frobeniusIsog_pullback_pow_mem`, `mulByInt_pullback_pow_witness_iff_mem_frobenius_range`, `pointCount_eq_of_witness`; heavily used throughout the project (GapSpines, Hasse/*, Verschiebung/*, WeilPairing/*, AdditionPullback/*)
- **Visibility**: public
- **Lines**: 53–56, definition (no proof body)
- **Notes**: Key API; the Frobenius isogeny that the entire project pivots on.

---

### `theorem frobeniusIsog_pullback_apply`

- **Type**: `(f : W.toAffine.FunctionField) : (frobeniusIsog W).pullback f = f ^ Fintype.card K`
- **What**: Shows that the Frobenius isogeny's pullback sends every function field element f to its q-th power (where q = #K).
- **How**: Unfolds the definition via `change` to `FiniteField.frobeniusAlgHom K ... f = f ^ Fintype.card K`, then applies `FiniteField.coe_frobeniusAlgHom`.
- **Hypotheses**: W elliptic over finite K.
- **Uses from project**: `frobeniusIsog`
- **Used by**: `ordAtInfty_frobeniusIsog_pullback_x_gen`, `ordAtInfty_frobeniusIsog_pullback_y_gen`, `ordAtInfty_frobeniusIsog_pullback_x_gen_sub_x_gen`, `ordAtInfty_frobeniusIsog_pullback_y_gen_sub_y_gen`, `frobeniusIsog_pullback_universal_commute`, `frobeniusIsog_pullback_eq_pow_pow`, `frobeniusIsog_pullback_range`, `frobeniusIsog_pullback_mem_iff`; heavily used in `AdditionPullback/SilvermanIV14.lean`, `GapSpines.lean`, `Hasse/OpenLemmaPrimitives.lean`, `Verschiebung/Genuine.lean`
- **Visibility**: public
- **Lines**: 58–62, proof length: ~4 lines
- **Notes**: This is the most-used declaration from this file across the project.

---

### `private theorem nsmul_coe_eq_coe_mul`

- **Type**: `(n : ℕ) (z : ℤ) : (n : ℕ) • ((z : ℤ) : WithTop ℤ) = (((n : ℤ) * z : ℤ) : WithTop ℤ)`
- **What**: An arithmetic identity: n-fold additive scalar multiplication of a coerced integer in `WithTop ℤ` equals the coercion of the product `n * z`.
- **How**: Induction on n: base is `simp`; inductive step unfolds `succ_nsmul` and uses `push_cast` plus `rfl`.
- **Hypotheses**: none (pure arithmetic)
- **Uses from project**: none
- **Used by**: `ordAtInfty_frobeniusIsog_pullback_x_gen`, `ordAtInfty_frobeniusIsog_pullback_y_gen`
- **Visibility**: private
- **Lines**: 78–85, proof length: ~7 lines
- **Notes**: Helper lemma; private; not accessible outside file. Suspected to be provable by `norm_cast` or `simp` but kept as a named helper.

---

### `theorem ordAtInfty_frobeniusIsog_pullback_x_gen`

- **Type**: `(W_smooth W).ordAtInfty ((frobeniusIsog W).pullback (x_gen W)) = ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ)`
- **What**: Computes the order at infinity of π*(x_gen) as −2q, since π*(x_gen) = x_gen^q and the order-at-infinity of x_gen^n is −2n.
- **How**: Rewrites via `frobeniusIsog_pullback_apply` (gets x_gen^q), then `ordAtInfty_x_gen_pow` (gets −2·q as nsmul form), then `nsmul_coe_eq_coe_mul` to convert to the coerced product.
- **Hypotheses**: W elliptic over finite K.
- **Uses from project**: `frobeniusIsog_pullback_apply`, `W_smooth`, `x_gen`, `ordAtInfty_x_gen_pow` (from OrdAtInftyBridge), `nsmul_coe_eq_coe_mul`
- **Used by**: `ordAtInfty_frobeniusIsog_pullback_x_gen_sub_x_gen` (this file)
- **Visibility**: public
- **Lines**: 89–95, proof length: ~6 lines
- **Notes**: Not referenced outside this file; potential dead code for external consumers.

---

### `theorem ordAtInfty_frobeniusIsog_pullback_y_gen`

- **Type**: `(W_smooth W).ordAtInfty ((frobeniusIsog W).pullback (y_gen W)) = ((-3 * (Fintype.card K : ℤ)) : WithTop ℤ)`
- **What**: Computes the order at infinity of π*(y_gen) as −3q.
- **How**: Same pattern as `ordAtInfty_frobeniusIsog_pullback_x_gen` but using `ordAtInfty_y_gen_pow` and factor −3.
- **Hypotheses**: W elliptic over finite K.
- **Uses from project**: `frobeniusIsog_pullback_apply`, `W_smooth`, `y_gen`, `ordAtInfty_y_gen_pow`, `nsmul_coe_eq_coe_mul`
- **Used by**: `ordAtInfty_frobeniusIsog_pullback_y_gen_sub_y_gen` (this file)
- **Visibility**: public
- **Lines**: 98–104, proof length: ~6 lines
- **Notes**: Not referenced outside this file; potential dead code for external consumers.

---

### `private theorem two_le_fintype_card_K`

- **Type**: `(2 : ℕ) ≤ Fintype.card K`
- **What**: Shows that a finite field has at least 2 elements, since a field requires 0 ≠ 1.
- **How**: Applies `Fintype.one_lt_card_iff_nontrivial.mpr inferInstance`.
- **Hypotheses**: K is a finite field.
- **Uses from project**: none
- **Used by**: `ordAtInfty_frobeniusIsog_pullback_x_gen_sub_x_gen`, `ordAtInfty_frobeniusIsog_pullback_y_gen_sub_y_gen`
- **Visibility**: private
- **Lines**: 108–109, proof length: 1 line
- **Notes**: private; could be inlined.

---

### `theorem ordAtInfty_frobeniusIsog_pullback_x_gen_sub_x_gen`

- **Type**: `(W_smooth W).ordAtInfty ((frobeniusIsog W).pullback (x_gen W) - x_gen W) = ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ)`
- **What**: Computes ord_∞(π*(x_gen) − x_gen) = −2q for q ≥ 2; the strict dominance of the pole at −2q over the pole at −2 (since q ≥ 2) allows using the non-archimedean property that ord(a − b) = ord(a) when ord(a) < ord(b).
- **How**: Uses `two_le_fintype_card_K` to get q ≥ 2, derives the strict inequality −2q < −2 by linear arithmetic, applies `ordAtInfty_sub_eq_of_lt` from `SmoothPlaneCurve` (OrdAtInftyBridge/Infinity.lean), and concludes by `ordAtInfty_frobeniusIsog_pullback_x_gen`.
- **Hypotheses**: W elliptic over finite K; uses q ≥ 2 (follows from K being a field).
- **Uses from project**: `two_le_fintype_card_K`, `W_smooth`, `x_gen`, `ordAtInfty_frobeniusIsog_pullback_x_gen`, `ordAtInfty_x_gen` (from OrdAtInftyBridge); `ordAtInfty_sub_eq_of_lt` (from Curves/Infinity.lean via SmoothPlaneCurve)
- **Used by**: unused in this file; potential consumer in `AdditionPullback/Frobenius.lean` context
- **Visibility**: public
- **Lines**: 114–126, proof length: ~12 lines
- **Notes**: Not referenced outside this file; dead code candidate.

---

### `theorem ordAtInfty_frobeniusIsog_pullback_y_gen_sub_y_gen`

- **Type**: `(W_smooth W).ordAtInfty ((frobeniusIsog W).pullback (y_gen W) - y_gen W) = ((-3 * (Fintype.card K : ℤ)) : WithTop ℤ)`
- **What**: Computes ord_∞(π*(y_gen) − y_gen) = −3q for q ≥ 2, by the same non-archimedean dominance argument.
- **How**: Same strategy as `ordAtInfty_frobeniusIsog_pullback_x_gen_sub_x_gen`, using the y-gen versions.
- **Hypotheses**: W elliptic over finite K.
- **Uses from project**: `two_le_fintype_card_K`, `W_smooth`, `y_gen`, `ordAtInfty_frobeniusIsog_pullback_y_gen`, `ordAtInfty_y_gen` (from OrdAtInftyBridge); `ordAtInfty_sub_eq_of_lt`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 129–141, proof length: ~12 lines
- **Notes**: Not referenced outside this file; dead code candidate.

---

### `@[simp] theorem frobeniusIsog_degree`

- **Type**: `(frobeniusIsog W).degree = Fintype.card K`
- **What**: The degree of the Frobenius isogeny equals q = #K (Silverman III.4.6); i.e., the function field extension [K(E) : π*(K(E))] has degree q.
- **How**: Unfolds `degree` to `Module.finrank` via `change`, then applies `frobenius_finrank_functionField K W` from `FrobeniusIsogeny.lean`.
- **Hypotheses**: W elliptic over finite K.
- **Uses from project**: `frobeniusIsog`; `frobenius_finrank_functionField` (from `FrobeniusIsogeny.lean`)
- **Used by**: `pointCount_eq_of_witness` (this file); used widely: `GapSpines.lean`, `Hasse/QuadraticForm.lean`, `Hasse/OpenLemmaPrimitives.lean`
- **Visibility**: public (with `@[simp]`)
- **Lines**: 146–150, proof length: ~4 lines
- **Notes**: `@[simp]`-tagged; key API.

---

### `theorem frobeniusIsog_pullback_universal_commute`

- **Type**: `(g : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField) : (frobeniusIsog W).pullback.comp g = g.comp (frobeniusIsog W).pullback`
- **What**: The Frobenius pullback (f ↦ f^q) commutes with every K-algebra endomorphism g of K(E), since ring homs preserve powers: g(f^q) = g(f)^q.
- **How**: Applies `AlgHom.ext` then uses `frobeniusIsog_pullback_apply` twice and `map_pow`.
- **Hypotheses**: W elliptic over finite K; g any K-algebra endomorphism.
- **Uses from project**: `frobeniusIsog`, `frobeniusIsog_pullback_apply`
- **Used by**: `frobeniusIsog_mulByInt_pullback_comm`, `frobeniusIsog_universal_commute_isog` (this file); used in `AdditionPullback.lean`, `Hasse/OpenLemmaPrimitives.lean`, `Verschiebung/IsDual.lean`
- **Visibility**: public
- **Lines**: 164–171, proof length: ~7 lines
- **Notes**: Core commutation lemma; heavily used across the project.

---

### `theorem frobeniusIsog_mulByInt_pullback_comm`

- **Type**: `(n : ℤ) : (frobeniusIsog W).pullback.comp (mulByInt W.toAffine n).pullback = (mulByInt W.toAffine n).pullback.comp (frobeniusIsog W).pullback`
- **What**: The Frobenius pullback commutes with the [n]-multiplication pullback for every integer n; this is the Route A `h_pb_comm` witness for α = π (unconditional).
- **How**: One-liner: direct application of `frobeniusIsog_pullback_universal_commute` with `g = (mulByInt W.toAffine n).pullback`.
- **Hypotheses**: W elliptic over finite K.
- **Uses from project**: `frobeniusIsog`, `mulByInt`, `frobeniusIsog_pullback_universal_commute`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 178–181, proof length: 1 line
- **Notes**: Not referenced outside this file; dead code candidate for current usage, though documented as the h_pb_comm witness.

---

### `theorem frobeniusIsog_universal_commute_isog`

- **Type**: `(ψ : Isogeny W.toAffine W.toAffine) : (frobeniusIsog W).comp ψ = ψ.comp (frobeniusIsog W)`
- **What**: The Frobenius isogeny commutes with any isogeny ψ at the isogeny level (not just pullback level); the group-hom component is trivial since Frobenius has identity toAddMonoidHom over 𝔽_q.
- **How**: Derives the pullback commutation from `frobeniusIsog_pullback_universal_commute` (symmetrised), proves the AddMonoidHom component by `id_comp`/`comp_id`, then destructs ψ and equates the two `Isogeny.mk` expressions using the two commutativity facts.
- **Hypotheses**: W elliptic over finite K; ψ any isogeny E → E.
- **Uses from project**: `frobeniusIsog`, `frobeniusIsog_pullback_universal_commute`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 188–202, proof length: ~14 lines
- **Notes**: Not referenced outside this file; dead code candidate. Isogeny-level version of the universal commute.

---

### `theorem frobeniusIsog_pullback_eq_pow_pow`

- **Type**: `(p n : ℕ) (h_card : Fintype.card K = p ^ n) (f : W.toAffine.FunctionField) : (frobeniusIsog W).pullback f = f ^ p ^ n`
- **What**: When q = p^n, the Frobenius pullback sends f to f^(p^n), identifying the q-Frobenius with the n-fold iterated p-Frobenius at the function field level.
- **How**: Rewrites via `frobeniusIsog_pullback_apply` then substitutes `h_card`.
- **Hypotheses**: W elliptic over finite K; q = p^n explicitly provided.
- **Uses from project**: `frobeniusIsog_pullback_apply`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 209–212, proof length: ~3 lines
- **Notes**: Not referenced outside this file; dead code candidate. Documents the p^n structure of Frobenius.

---

### `theorem frobeniusIsog_pullback_range`

- **Type**: `Set.range (frobeniusIsog W).pullback = Set.range ((· ^ Fintype.card K) : W.toAffine.FunctionField → W.toAffine.FunctionField)`
- **What**: The set-image of the Frobenius pullback equals the set of q-th powers in K(E).
- **How**: Set extensionality; both directions unpack using `frobeniusIsog_pullback_apply`.
- **Hypotheses**: W elliptic over finite K.
- **Uses from project**: `frobeniusIsog`, `frobeniusIsog_pullback_apply`
- **Used by**: `frobeniusIsog_pullback_mem_iff` logically (though stated independently); referenced in `Verschiebung/QthRoots.lean` (via `frobeniusIsog_pullback_range_inv_mem`)
- **Visibility**: public
- **Lines**: 226–235, proof length: ~9 lines
- **Notes**: Verschiebung infrastructure; supports `AlgHom.factor` construction.

---

### `theorem frobeniusIsog_pullback_mem_iff`

- **Type**: `(f : W.toAffine.FunctionField) : f ∈ (frobeniusIsog W).pullback.fieldRange ↔ ∃ g, g ^ Fintype.card K = f`
- **What**: Membership in the field-range (subfield image) of the Frobenius pullback is equivalent to being a q-th power.
- **How**: Both directions use `frobeniusIsog_pullback_apply` with `change` to convert between the AlgHom form and the power form.
- **Hypotheses**: W elliptic over finite K.
- **Uses from project**: `frobeniusIsog`, `frobeniusIsog_pullback_apply`
- **Used by**: `frobeniusIsog_pullback_pow_mem`, `mulByInt_pullback_pow_witness_iff_mem_frobenius_range` (this file); used in `Verschiebung/QthRoots.lean`, `Verschiebung/Genuine.lean`
- **Visibility**: public
- **Lines**: 241–252, proof length: ~11 lines
- **Notes**: Key membership characterisation for Verschiebung.

---

### `theorem frobeniusIsog_pullback_pow_mem`

- **Type**: `(f : W.toAffine.FunctionField) : f ^ Fintype.card K ∈ (frobeniusIsog W).pullback.fieldRange`
- **What**: Every q-th power lies in the field-range of the Frobenius pullback; the "easy direction" of `frobeniusIsog_pullback_mem_iff`.
- **How**: One-liner: applies the `mpr` direction of `frobeniusIsog_pullback_mem_iff` with witness `f` and `rfl`.
- **Hypotheses**: W elliptic over finite K.
- **Uses from project**: `frobeniusIsog_pullback_mem_iff`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 256–258, proof length: 1 line
- **Notes**: Not referenced outside this file in the grep results; potential dead code for current usage.

---

### `theorem mulByInt_pullback_pow_witness_iff_mem_frobenius_range`

- **Type**: `(z : W.toAffine.FunctionField) : (∃ g, g ^ Fintype.card K = (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z) ↔ (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z ∈ (frobeniusIsog W).pullback.fieldRange`
- **What**: The [q]-multiplication pullback of z is a q-th power if and only if it lies in the Frobenius field-range; this is the witness form of the Verschiebung-existence inclusion [q]*(K(E)) ⊆ π*(K(E)).
- **How**: Symmetry of `frobeniusIsog_pullback_mem_iff` applied to the specific element `(mulByInt W.toAffine q).pullback z`.
- **Hypotheses**: W elliptic over finite K.
- **Uses from project**: `mulByInt`, `frobeniusIsog`, `frobeniusIsog_pullback_mem_iff`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 272–278, proof length: 1 line
- **Notes**: Not referenced outside this file; Verschiebung infrastructure, deferred to "Session 2" per doc-string.

---

### `theorem pointCount_eq_of_witness`

- **Type**: `(β : Isogeny W.toAffine W.toAffine) (hβ_deg : (β.degree : ℤ) = pointCount W.toAffine) : (pointCount W.toAffine : ℤ) = Fintype.card K + 1 - isogTrace (frobeniusIsog W) β`
- **What**: Given a genuine isogeny β with degree equal to the point count (the V.1.3 keystone), the number of rational points satisfies #E(𝔽_q) = q + 1 − tr(π, β), where the trace uses the Frobenius isogeny; this is Silverman V.1.1.
- **How**: Unfolds `isogTrace`, rewrites `frobeniusIsog_degree` (gets q), substitutes `hβ_deg`, and closes by `ring`.
- **Hypotheses**: W elliptic over finite K with Fintype W.toAffine.Point; β an isogeny with degree = #E(𝔽_q).
- **Uses from project**: `pointCount`, `frobeniusIsog`, `frobeniusIsog_degree`, `isogTrace` (from `Endomorphism.lean`)
- **Used by**: used in `Hasse/PointFix.lean` and `Hasse/BoundOfWitnesses.lean`
- **Visibility**: public
- **Lines**: 306–312, proof length: ~6 lines
- **Notes**: Witness-parametric version of Silverman V.1.1; replaces old placeholder declarations (`pointCount_eq`, `traceOfFrobenius`, `pointCount_eq_sub_trace`) that were deleted.

---

## Summary statistics

| Category | Count |
|---|---|
| Total declarations | 17 |
| noncomputable defs | 2 (`pointCount`, `frobeniusIsog`) |
| Theorems/lemmas | 15 |
| Instances | 0 |
| Private declarations | 2 (`nsmul_coe_eq_coe_mul`, `two_le_fintype_card_K`) |
| Sorry | 0 |
| set_option maxHeartbeats | 0 |
| Proofs > 30 lines | 0 |

## Key API (used by 3+ others in this file)

- `frobeniusIsog`: referenced in almost every theorem
- `frobeniusIsog_pullback_apply`: used in `ordAtInfty_frobeniusIsog_pullback_x_gen`, `ordAtInfty_frobeniusIsog_pullback_y_gen`, `ordAtInfty_frobeniusIsog_pullback_x_gen_sub_x_gen`, `ordAtInfty_frobeniusIsog_pullback_y_gen_sub_y_gen`, `frobeniusIsog_pullback_universal_commute`, `frobeniusIsog_pullback_eq_pow_pow`, `frobeniusIsog_pullback_range`, `frobeniusIsog_pullback_mem_iff`
- `frobeniusIsog_pullback_universal_commute`: used in `frobeniusIsog_mulByInt_pullback_comm`, `frobeniusIsog_universal_commute_isog`
- `frobeniusIsog_pullback_mem_iff`: used in `frobeniusIsog_pullback_pow_mem`, `mulByInt_pullback_pow_witness_iff_mem_frobenius_range`

## Unused in file (dead-code candidates)

The following public declarations are not referenced by any other declaration inside this file, and no external references were found in the grep search:

- `ordAtInfty_frobeniusIsog_pullback_x_gen` (used only by `ordAtInfty_frobeniusIsog_pullback_x_gen_sub_x_gen`)
- `ordAtInfty_frobeniusIsog_pullback_y_gen` (used only by `ordAtInfty_frobeniusIsog_pullback_y_gen_sub_y_gen`)
- `ordAtInfty_frobeniusIsog_pullback_x_gen_sub_x_gen` — no external callers found
- `ordAtInfty_frobeniusIsog_pullback_y_gen_sub_y_gen` — no external callers found
- `frobeniusIsog_mulByInt_pullback_comm` — no external callers found
- `frobeniusIsog_universal_commute_isog` — no external callers found
- `frobeniusIsog_pullback_eq_pow_pow` — no external callers found
- `frobeniusIsog_pullback_range` — referenced only indirectly in `Verschiebung/QthRoots.lean` comments
- `frobeniusIsog_pullback_pow_mem` — no external callers found
- `mulByInt_pullback_pow_witness_iff_mem_frobenius_range` — no external callers found

## Notes

This is a clean, sorry-free, well-organised file serving as the main interface between the abstract `Isogeny` type and the concrete Frobenius endomorphism. The ord-at-infinity lemmas (`ordAtInfty_frobeniusIsog_*`) and the Verschiebung infrastructure lemmas (`pullback_range`, `pullback_mem_iff`, `pullback_pow_mem`, `mulByInt_pullback_pow_witness_iff`) appear to be parked/forward-looking: no external callers are found by grep, suggesting they were scaffolded for future use (Verschiebung sub-ticket, addition-pullback Frobenius case) but are currently unused in the build tree.
