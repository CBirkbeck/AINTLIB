# Inventory: ./HasseWeil/Verschiebung/IsDual.lean

**File**: `HasseWeil/Verschiebung/IsDual.lean`
**Total lines**: 732
**Total declarations**: 12 (2 defs, 10 theorems, 0 instances)
**Sorries**: none
**maxHeartbeats overrides**: none

---

## Imports

- `HasseWeil.Verschiebung.Construction` — provides `verschiebungPullback_of_witness`, `mulByInt_q_factor_via_witness`
- `HasseWeil.DualIsogeny` — provides `IsDualOf`, `frobeniusIsog`, `frobeniusIsog_degree`, `frobeniusIsog_pullback_universal_commute`, `frobeniusIsog_pullback_apply`
- `HasseWeil.EC.GenericPointZsmul` — provides `mulByInt_comp_eq_mul`, `x_gen`, `y_gen`

---

## Declaration Inventory

---

### `noncomputable def verschiebungIsog_of_witness`

- **Type**: `(h_subset : (mulByInt W.toAffine q).pullback.range ≤ (frobeniusIsog W).pullback.range) → Isogeny W.toAffine W.toAffine` where `q = (Fintype.card K : ℕ) : ℤ`
- **What**: Bundles the witness-parametric Verschiebung pullback `verschiebungPullback_of_witness` together with the point map `(mulByInt W.toAffine q).toAddMonoidHom` into a full `Isogeny` structure. The point map is `[q]`'s map because Frobenius acts as the identity on `𝔽_q`-points.
- **How**: Direct structure-builder; `pullback` field from `verschiebungPullback_of_witness`, `toAddMonoidHom` field directly from `mulByInt`.
- **Hypotheses**: `W : WeierstrassCurve K`, `K` a finite field, `W.toAffine.IsElliptic`, `h_subset : Im([q]*) ⊆ Im(π*)`.
- **Uses from project**: `verschiebungPullback_of_witness`, `frobeniusIsog`, `mulByInt`
- **Used by**: `verschiebung_comp_frobenius_eq_mulByInt_q`, `frobenius_comp_verschiebung_eq_mulByInt_q`, `verschiebungIsog_of_witness_isDualOf_frobenius`, `verschiebung_pullback_commute_mulByInt_neg_one`, `verschiebungIsog_frobeniusIsog_comm`, `mulByInt_pow_pullback_x_gen_eq_pow_qpow`, `mulByInt_pow_pullback_y_gen_eq_pow_qpow`
- **Visibility**: public
- **Lines**: 60–67, proof length ~7 lines (structure literal)
- **Notes**: None

---

### `theorem verschiebung_comp_frobenius_eq_mulByInt_q`

- **Type**: `(h_subset : ...) → (verschiebungIsog_of_witness W h_subset).comp (frobeniusIsog W) = mulByInt W.toAffine q`
- **What**: Proves the first composition identity `V ∘ π = [q]` at the level of `Isogeny` equality, i.e., both pullback and toAddMonoidHom fields agree.
- **How**: Unfolds `Isogeny.comp` by `show`-casting, derives `h_pb` from `mulByInt_q_factor_via_witness` (pullback factoring `π* ∘ V* = [q]*`), derives `h_hom` from `AddMonoidHom.comp_id` (since `frobeniusIsog.toAddMonoidHom = id` on `𝔽_q`-points), then reassembles via `rcases` on the target isogeny and `rw`.
- **Hypotheses**: Same as `verschiebungIsog_of_witness`. Uses that `frobeniusIsog W` has `toAddMonoidHom = AddMonoidHom.id`.
- **Uses from project**: `verschiebungIsog_of_witness`, `verschiebungPullback_of_witness`, `frobeniusIsog`, `mulByInt`, `mulByInt_q_factor_via_witness`
- **Used by**: `verschiebungIsog_of_witness_isDualOf_frobenius`, `verschiebungIsog_frobeniusIsog_comm`
- **Visibility**: public
- **Lines**: 71–112, proof length ~42 lines
- **Notes**: Proof >30 lines; the bulk is the `show` unfolding and `rcases` reassembly pattern to handle structural isogeny equality.

---

### `theorem frobenius_comp_verschiebung_eq_mulByInt_q`

- **Type**: `(h_subset : ...) → (frobeniusIsog W).comp (verschiebungIsog_of_witness W h_subset) = mulByInt W.toAffine q`
- **What**: Proves the second composition identity `π ∘ V = [q]` at the `Isogeny` level.
- **How**: Reduces pullback equality `V* ∘ π* = π* ∘ V*` via `frobeniusIsog_pullback_universal_commute` (Frobenius universal commutation with any K-algebra hom), then uses `mulByInt_q_factor_via_witness` for `π* ∘ V* = [q]*`. The hom equality uses `AddMonoidHom.id_comp`.
- **Hypotheses**: Same as `verschiebungIsog_of_witness`.
- **Uses from project**: `verschiebungIsog_of_witness`, `verschiebungPullback_of_witness`, `frobeniusIsog`, `mulByInt`, `mulByInt_q_factor_via_witness`, `frobeniusIsog_pullback_universal_commute`
- **Used by**: `verschiebungIsog_of_witness_isDualOf_frobenius`, `verschiebungIsog_frobeniusIsog_comm`
- **Visibility**: public
- **Lines**: 116–156, proof length ~41 lines
- **Notes**: Proof >30 lines; the key asymmetry from the first composition is the use of `frobeniusIsog_pullback_universal_commute` to commute V* past π*.

---

### `theorem verschiebungIsog_of_witness_isDualOf_frobenius`

- **Type**: `(h_subset : ...) → IsDualOf W.toAffine (verschiebungIsog_of_witness W h_subset) (frobeniusIsog W)`
- **What**: Assembles the `IsDualOf` predicate for `V` and `π`, i.e., packages both composition identities into the dual-isogeny bundle.
- **How**: Uses `refine ⟨?_, ?_⟩` to split `IsDualOf` into two goals; rewrites `frobeniusIsog_degree` to express `mulByInt (frobeniusIsog W).degree` as `mulByInt q`, then applies `verschiebung_comp_frobenius_eq_mulByInt_q` and `frobenius_comp_verschiebung_eq_mulByInt_q`.
- **Hypotheses**: Same as `verschiebungIsog_of_witness`.
- **Uses from project**: `verschiebungIsog_of_witness`, `frobeniusIsog`, `frobeniusIsog_degree`, `verschiebung_comp_frobenius_eq_mulByInt_q`, `frobenius_comp_verschiebung_eq_mulByInt_q`, `IsDualOf`
- **Used by**: unused in file (exported API)
- **Visibility**: public
- **Lines**: 159–171, proof length ~13 lines
- **Notes**: The capstone theorem of the file for the `IsDualOf` goal.

---

### `theorem verschiebung_pullback_commute_mulByInt_neg_one`

- **Type**: `(h_subset : ...) → (verschiebungPullback_of_witness W h_subset).comp (mulByInt W.toAffine (-1)).pullback = (mulByInt W.toAffine (-1)).pullback.comp (verschiebungPullback_of_witness W h_subset)`
- **What**: Proves that V* (the Verschiebung pullback) commutes with σ* = `[−1]*` (the negation pullback) at the level of K-algebra homomorphisms on `K(E)`. This is the foundation for the V-side σ-symmetry hypotheses.
- **How**: Uses injectivity of `frobeniusIsog_pullback_injective` to reduce to comparing `π*` applied to both sides. The LHS reduces to `[q]*(σ* z)` via the factor identity `mulByInt_q_factor_via_witness`; the RHS via `frobeniusIsog_pullback_universal_commute` and the factor identity. Both sides reduce to `σ*([q]* z)`. The commutativity of `σ*` and `[q]*` is obtained by showing `[q] ∘ [-1] = [-1] ∘ [q]` as isogenies via `mulByInt_comp_eq_mul` (both equal `mulByInt (-q)` since `-q·1 = 1·(-q)`), then extracting pullback equality.
- **Hypotheses**: Same as `verschiebungIsog_of_witness`.
- **Uses from project**: `verschiebungPullback_of_witness`, `frobeniusIsog`, `frobeniusIsog_pullback_universal_commute`, `mulByInt_q_factor_via_witness`, `mulByInt_comp_eq_mul`
- **Used by**: unused in file (exported API; noted as foundation for `addPullback_x_pair_sigma_invariant` in Worker B's V-side D-track)
- **Visibility**: public
- **Lines**: 185–289, proof length ~105 lines
- **Notes**: Proof >30 lines; longest in the file's first half. The `h_mul_comm` sub-proof (lines 234–282) is a 49-line subproof establishing pullback commutativity of `[q]` and `[-1]` via an isogeny-level `congr`+`rfl` argument.

---

### `theorem sigma_V_commute_of_hV`

- **Type**: `(V : Isogeny W.toAffine W.toAffine) → (hV : IsDualOf W.toAffine V (frobeniusIsog W)) → ∀ f, (mulByInt W.toAffine (-1)).pullback (V.pullback f) = V.pullback ((mulByInt W.toAffine (-1)).pullback f)`
- **What**: General form of `verschiebung_pullback_commute_mulByInt_neg_one`: for any `V` dual to Frobenius, σ* = `[−1]*` commutes with V* at the function-field level. Labelled "σ-V commute from `IsDualOf V π`", tagged R25h Worker-A Round 3.
- **How**: Same π*-injectivity strategy; uses `hV.1 : V.comp (frobeniusIsog W) = mulByInt q` (after rewriting `frobeniusIsog_degree`) together with `congrArg Isogeny.pullback` to obtain the factor identity. The rest of the argument repeats the `frobeniusIsog_pullback_universal_commute` + `mulByInt_comp_eq_mul` commutativity chain from the witness-form theorem.
- **Hypotheses**: `V : Isogeny W.toAffine W.toAffine`, `hV : IsDualOf W.toAffine V (frobeniusIsog W)`.
- **Uses from project**: `frobeniusIsog`, `frobeniusIsog_degree`, `frobeniusIsog_pullback_universal_commute`, `mulByInt`, `mulByInt_comp_eq_mul`, `IsDualOf`
- **Used by**: unused in file (exported API for Worker B/C)
- **Visibility**: public
- **Lines**: 313–385, proof length ~73 lines
- **Notes**: Proof >30 lines; largely mirrors `verschiebung_pullback_commute_mulByInt_neg_one` but takes an abstract `hV : IsDualOf` instead of `h_subset`.

---

### `noncomputable def isogenyIterate`

- **Type**: `(φ : Isogeny W.toAffine W.toAffine) → (k : ℕ) → Isogeny W.toAffine W.toAffine`
- **What**: Defines the k-fold iterate of an endoisogeny `φ` by left-extending: `isogenyIterate φ 0 = id`, `isogenyIterate φ (k+1) = (isogenyIterate φ k).comp φ`. The new copy is placed on the outside so pullbacks unfold as `φ*` outside the iterate.
- **How**: `Nat.rec` recursion.
- **Hypotheses**: `W : WeierstrassCurve K` finite elliptic.
- **Uses from project**: `Isogeny.id`, `Isogeny.comp`
- **Used by**: `isogenyIterate_zero`, `isogenyIterate_succ`, `mulByInt_pow_pullback_x_gen_eq_pow_qpow`, `mulByInt_pow_pullback_y_gen_eq_pow_qpow`
- **Visibility**: public
- **Lines**: 404–406, proof length ~3 lines (term-mode)
- **Notes**: None

---

### `@[simp] theorem isogenyIterate_zero`

- **Type**: `(φ : Isogeny W.toAffine W.toAffine) → isogenyIterate W φ 0 = Isogeny.id W.toAffine`
- **What**: Base case unfolding of `isogenyIterate` at zero; tagged `@[simp]`.
- **How**: `rfl`.
- **Hypotheses**: None beyond the isogeny.
- **Uses from project**: `isogenyIterate`
- **Used by**: `mulByInt_pow_pullback_x_gen_eq_pow_qpow` (in zero case), `mulByInt_pow_pullback_y_gen_eq_pow_qpow` (in zero case)
- **Visibility**: public
- **Lines**: 408–409, proof length 1 line
- **Notes**: None

---

### `@[simp] theorem isogenyIterate_succ`

- **Type**: `(φ : Isogeny W.toAffine W.toAffine) → (k : ℕ) → isogenyIterate W φ (k + 1) = (isogenyIterate W φ k).comp φ`
- **What**: Successor unfolding of `isogenyIterate`; tagged `@[simp]`.
- **How**: `rfl`.
- **Hypotheses**: None beyond the isogeny.
- **Uses from project**: `isogenyIterate`
- **Used by**: `mulByInt_pow_pullback_x_gen_eq_pow_qpow` (via `rw [isogenyIterate_succ]`), `mulByInt_pow_pullback_y_gen_eq_pow_qpow`
- **Visibility**: public
- **Lines**: 411–412, proof length 1 line
- **Notes**: None

---

### `theorem verschiebungIsog_frobeniusIsog_comm`

- **Type**: `(h_subset : ...) → (verschiebungIsog_of_witness W h_subset).comp (frobeniusIsog W) = (frobeniusIsog W).comp (verschiebungIsog_of_witness W h_subset)`
- **What**: Bundles both composition identities to show `V ∘ π = π ∘ V` as isogenies (both equal `[q]`).
- **How**: Two `rw` calls using `verschiebung_comp_frobenius_eq_mulByInt_q` and `frobenius_comp_verschiebung_eq_mulByInt_q`.
- **Hypotheses**: Same as `verschiebungIsog_of_witness`.
- **Uses from project**: `verschiebungIsog_of_witness`, `frobeniusIsog`, `verschiebung_comp_frobenius_eq_mulByInt_q`, `frobenius_comp_verschiebung_eq_mulByInt_q`
- **Used by**: unused in file (exported for inductive composition arguments)
- **Visibility**: public
- **Lines**: 418–425, proof length ~8 lines
- **Notes**: None

---

### `theorem mulByInt_pow_pullback_x_gen_eq_pow_qpow`

- **Type**: `(h_subset : ...) → (k : ℕ) → (mulByInt W.toAffine (q^k : ℕ) : ℤ).pullback (x_gen W) = ((isogenyIterate W (verschiebungIsog_of_witness W h_subset) k).pullback (x_gen W)) ^ (q^k)`
- **What**: Proves that `[q^k]*(x_gen) = (V^k*(x_gen))^{q^k}` at the function-field level; the x-coordinate iterate identity used in Silverman III.6.1 / Worker C's polynomial-side argument.
- **How**: Induction on `k`. Base: uses `mulByInt_one_pullback_eq_id` and `simp`. Inductive step: decomposes `[q^{k+1}] = [q] ∘ [q^k]` via `mulByInt_comp_eq_mul`, gets `[q]*(x_gen) = (V*(x_gen))^q` from `mulByInt_q_factor_via_witness` + `frobeniusIsog_pullback_apply` (Frobenius acts as `q`-power on function field), applies `map_pow` for K-algebra distribution, establishes `[q^k]*(V*(x_gen)) = V*([q^k]*(x_gen))` (V-commutativity with `[q^k]`) via `frobeniusIsog_pullback_universal_commute` + `mulByInt_comp_eq_mul`, substitutes the induction hypothesis, and closes with `pow_mul` / `ring_nf`.
- **Hypotheses**: Same as `verschiebungIsog_of_witness`. `k : ℕ`.
- **Uses from project**: `verschiebungIsog_of_witness`, `verschiebungPullback_of_witness`, `frobeniusIsog`, `isogenyIterate`, `isogenyIterate_succ`, `mulByInt_q_factor_via_witness`, `mulByInt_comp_eq_mul`, `frobeniusIsog_pullback_universal_commute`, `frobeniusIsog_pullback_apply`, `mulByInt_one_pullback_eq_id`, `x_gen`
- **Used by**: unused in file (exported for Worker C)
- **Visibility**: public
- **Lines**: 442–609, proof length ~168 lines
- **Notes**: Proof >30 lines; the longest proof in the file. The inner `h_comm_at_x` subproof (establishing V-commutativity with `[q^k]`) is ~75 lines and uses π*-injectivity + a chain of factor-identity rewrites. No `sorry`.

---

### `theorem mulByInt_pow_pullback_y_gen_eq_pow_qpow`

- **Type**: `(h_subset : ...) → (k : ℕ) → (mulByInt W.toAffine (q^k : ℕ) : ℤ).pullback (y_gen W) = ((isogenyIterate W (verschiebungIsog_of_witness W h_subset) k).pullback (y_gen W)) ^ (q^k)`
- **What**: y-coordinate analog of `mulByInt_pow_pullback_x_gen_eq_pow_qpow`: proves `[q^k]*(y_gen) = (V^k*(y_gen))^{q^k}`.
- **How**: Identical induction structure to the x-case, replacing `x_gen` with `y_gen` throughout; uses the same key lemmas.
- **Hypotheses**: Same as `mulByInt_pow_pullback_x_gen_eq_pow_qpow`.
- **Uses from project**: `verschiebungIsog_of_witness`, `verschiebungPullback_of_witness`, `frobeniusIsog`, `isogenyIterate`, `isogenyIterate_succ`, `mulByInt_q_factor_via_witness`, `mulByInt_comp_eq_mul`, `frobeniusIsog_pullback_universal_commute`, `frobeniusIsog_pullback_apply`, `mulByInt_one_pullback_eq_id`, `y_gen`
- **Used by**: unused in file (exported for Worker C, symmetric to x-case)
- **Visibility**: public
- **Lines**: 615–730, proof length ~116 lines
- **Notes**: Proof >30 lines; near-verbatim copy of `mulByInt_pow_pullback_x_gen_eq_pow_qpow` with `y_gen` substituted for `x_gen`. Duplication could be factored via a common lemma taking a `gen : FunctionField` argument — potential cleanup target.

---

## Cross-Reference Summary

### Key API (used by 3+ other declarations in file)

| Declaration | Used by count | Callers |
|---|---|---|
| `verschiebungIsog_of_witness` | 7 | `verschiebung_comp_frobenius`, `frobenius_comp_verschiebung`, `isDualOf_frobenius`, `pullback_commute_neg_one`, `frobeniusIsog_comm`, `pow_pullback_x_gen`, `pow_pullback_y_gen` |
| `verschiebungPullback_of_witness` | 6 | `verschiebungIsog_of_witness` (via field), `verschiebung_comp_frobenius`, `frobenius_comp_verschiebung`, `pullback_commute_neg_one`, `pow_pullback_x_gen`, `pow_pullback_y_gen` |
| `mulByInt_q_factor_via_witness` | 6 | `verschiebung_comp_frobenius`, `frobenius_comp_verschiebung`, `pullback_commute_neg_one`, `pow_pullback_x_gen`, `pow_pullback_y_gen`, `sigma_V_commute_of_hV` (implicitly via `hV.1`) |
| `frobeniusIsog_pullback_universal_commute` | 5 | `frobenius_comp_verschiebung`, `pullback_commute_neg_one`, `sigma_V_commute_of_hV`, `pow_pullback_x_gen`, `pow_pullback_y_gen` |
| `isogenyIterate` | 4 | `isogenyIterate_zero`, `isogenyIterate_succ`, `pow_pullback_x_gen`, `pow_pullback_y_gen` |
| `verschiebung_comp_frobenius_eq_mulByInt_q` | 2 | `isDualOf_frobenius`, `frobeniusIsog_comm` |
| `frobenius_comp_verschiebung_eq_mulByInt_q` | 2 | `isDualOf_frobenius`, `frobeniusIsog_comm` |
| `isogenyIterate_succ` | 2 | `pow_pullback_x_gen`, `pow_pullback_y_gen` |

### Dead-code candidates (unused in this file)

All of the following are public exports not called by any other declaration within this file:
- `verschiebungIsog_of_witness_isDualOf_frobenius`
- `verschiebung_pullback_commute_mulByInt_neg_one`
- `sigma_V_commute_of_hV`
- `verschiebungIsog_frobeniusIsog_comm`
- `mulByInt_pow_pullback_x_gen_eq_pow_qpow`
- `mulByInt_pow_pullback_y_gen_eq_pow_qpow`
