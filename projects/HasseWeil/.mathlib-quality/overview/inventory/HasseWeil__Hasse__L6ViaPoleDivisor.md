# Inventory: ./HasseWeil/Hasse/L6ViaPoleDivisor.lean

**File**: `HasseWeil/Hasse/L6ViaPoleDivisor.lean`
**Total lines**: 398
**Imports**: `HasseWeil.Hasse.PoleDivisorFallback`, `HasseWeil.Hasse.OpenLemmas`, `HasseWeil.Hasse.OpenLemmaPrimitives`
**Namespaces**: `HasseWeil`, `HasseWeil.Conditional`

This file assembles the L6 identity (`sepDegree(1 − π) = #E(𝔽_q)`) as a witness-parametric closure,
consuming the shipped composer `pc_sepDeg_eq_pointCount_of_computationA_and_lemma5` from
`PoleDivisorFallback.lean`. All six declarations are `theorem`s; no defs, instances, or structures.
No `sorry`, no `set_option maxHeartbeats`.

---

### `theorem finrank_pullback_fieldRange_eq_degree`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] (φ : Isogeny W.toAffine W.toAffine) : Module.finrank φ.pullback.fieldRange W.toAffine.FunctionField = φ.degree`
- **What**: Proves that the finrank of K(E) over the field range of an isogeny pullback equals the degree of the isogeny.
- **How**: Constructs `gammaBar : K(E) ≃ₐ[K] φ.pullback.fieldRange` via `AlgEquiv.ofInjectiveField φ.pullback`, then applies mathlib's `Algebra.finrank_eq_of_equiv_equiv` with `gammaBar.toRingEquiv` and `RingEquiv.refl` to transfer the finrank. The commutativity square is discharged by `rfl` since `gammaBar` is definitionally the inclusion.
- **Hypotheses**: W is an elliptic curve over a finite field K; φ is an endoisogeny of W.
- **Uses from project**: `Isogeny` (type), `W.toAffine.FunctionField` (type); relies on `φ.pullback` as a ring homomorphism and `φ.degree` as the associated degree.
- **Used by**: Referenced in docstring comments only; not called by any declaration within this file.
- **Visibility**: public
- **Lines**: 86–105 (proof ~16 lines)
- **Notes**: Not referenced within this file — dead-code candidate (may be used by other files). The comment at lines 107–112 records a failed attempt at a "lower step" composition and defers it to a future session.

---

### `theorem bridgeA_intermediateField_finrank_eq_two_mul_degree_of_witness`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) (h_tower_witness : Module.finrank (IntermediateField.adjoin K {(isogOneSub_negFrobenius W hq).pullback (x_gen W)}) W.toAffine.FunctionField = 2 * (isogOneSub_negFrobenius W hq).degree) : <same conclusion as h_tower_witness>`
- **What**: States the B3 tower formula `[K(E) : K⟮γ*x⟯] = 2 · γ.degree` for `γ = isogOneSub_negFrobenius W hq`, packaged as a named theorem from its hypothesis.
- **How**: The proof is `h_tower_witness` — the theorem is definitionally the hypothesis itself, acting as a named wrapper to satisfy the L6 composer's interface.
- **Hypotheses**: Elliptic curve W over finite K with `|K| ≥ 2`; witness `h_tower_witness` providing the tower formula.
- **Uses from project**: `isogOneSub_negFrobenius`, `x_gen`.
- **Used by**: Referenced in docstrings only; not called by any other declaration within this file.
- **Visibility**: public
- **Lines**: 118–141 (proof = 1 line: `h_tower_witness`)
- **Notes**: Effectively a renaming/alias for the hypothesis. Not referenced within the file — dead-code candidate inside this file. Serves as a named checkpoint for the B3 witness.

---

### `theorem l6_v_1_1_sepDegree_eq_pointCount_of_witnesses`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] (hq : 2 ≤ Fintype.card K) (h_finrank_eq_2_deg : ...) (h_compA : ComputationA_bridge_pullback_x_gen W hq) (h_lemma5 : ...) : (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine`
- **What**: The B4 L6 closure: discharges `sepDegree(1 − π) = #E(𝔽_q)` from three substantive witnesses (B3 tower formula, ComputationA bridge, Lemma 5 pole-sum identity).
- **How**: Extracts characteristic `p` via `FiniteField.card'`; instantiates `CharP K p` and `Fact p.Prime`; then invokes `isogOneSub_negFrobenius_isSeparable` (Witness #1) and `isogOneSub_negFrobenius_finiteDimensional` (Witness #2); finally calls `pc_sepDeg_eq_pointCount_of_computationA_and_lemma5` with all five inputs.
- **Hypotheses**: Elliptic curve W over finite K with `|K| ≥ 2` and finitely many K-points; B3 tower formula; ComputationA bridge; Lemma 5 pole-sum witness.
- **Uses from project**: `isogOneSub_negFrobenius`, `isogOneSub_negFrobenius_isSeparable`, `isogOneSub_negFrobenius_finiteDimensional`, `pc_sepDeg_eq_pointCount_of_computationA_and_lemma5`, `ComputationA_bridge_pullback_x_gen`, `x_gen`, `W_smooth`, `pointCount`.
- **Used by**: `witness_pc_sepDeg_of_witnesses` (line 236), `l6_v_1_1_sepDegree_eq_pointCount_of_primitive_witnesses` (line 334), `hasse_bound_from_L6_witnesses` (line 392).
- **Visibility**: public
- **Lines**: 165–199 (proof ~14 lines)
- **Notes**: This is the central keystone of the file; called by 3 other declarations — qualifies as key API.

---

### `theorem witness_pc_sepDeg_of_witnesses`

- **Type**: Same signature as `l6_v_1_1_sepDegree_eq_pointCount_of_witnesses` (takes the same three hypotheses and produces the same conclusion).
- **What**: The B5 witness-wire: packages the B4 result under a name aligned with the `HasseWitnesses` bundle interface for `pc_sepDeg_eq_pointCount`.
- **How**: Direct delegation to `l6_v_1_1_sepDegree_eq_pointCount_of_witnesses`.
- **Hypotheses**: Same as `l6_v_1_1_sepDegree_eq_pointCount_of_witnesses`.
- **Uses from project**: `l6_v_1_1_sepDegree_eq_pointCount_of_witnesses`, `isogOneSub_negFrobenius`, `x_gen`, `W_smooth`, `pointCount`, `ComputationA_bridge_pullback_x_gen`.
- **Used by**: Not referenced within this file — dead-code candidate (intended as a named interface point for downstream bundle wiring).
- **Visibility**: public
- **Lines**: 218–237 (proof = 2 lines, term-mode)
- **Notes**: Essentially a synonym for `l6_v_1_1_sepDegree_eq_pointCount_of_witnesses`; its separate existence is motivated by naming alignment with the `witnessBundle` field.

---

### `theorem l6_v_1_1_sepDegree_eq_pointCount_of_primitive_witnesses`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] (hq : 2 ≤ Fintype.card K) [hf : Fact (Transcendental K (...)⁻¹)] (hMF : ...) (data : Sinf (...)) (h_uniform_pole_order : ...) (h_inertia_one : ...) (h_card : ...) (h_pole_orders : ...) (h_support_card : ...) (h_finrank_eq_2_deg : ...) : (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine`
- **What**: B4-alt — a finer-grained L6 closure taking per-prime Sinf-side witnesses (uniform pole order −2, inertia degree 1, prime-fiber cardinality) and per-point projectiveDivisorOf-side witnesses (pole orders, support cardinality) directly, then composing them to derive `sepDegree(1 − π) = #E(𝔽_q)`.
- **How**: Step 1 derives `h_compA` via `finrank_gamma_pullback_x_eq_projectiveDivisorOf_sum`; Step 2 derives `h_lemma5` via `lemma5_of_pole_orders_and_support_card`; Step 3 calls `l6_v_1_1_sepDegree_eq_pointCount_of_witnesses`.
- **Hypotheses**: All of B4's hypotheses plus: `Transcendental K` instance (for the `LinfAt` algebra), `Module.Finite` for `LinfAt`, a `Sinf` data bundle, uniform pole-order witnesses, uniform inertia-degree witnesses, prime-fiber count equals `pointCount`, per-point pole-order witnesses, support-cardinality witness, and B3 tower formula.
- **Uses from project**: `isogOneSub_negFrobenius`, `x_gen`, `W_smooth`, `pointCount`, `LinfAt`, `LinfAt.algebraFractionRing`, `Sinf`, `primesOverFinset`, `xIdeal`, `finrank_gamma_pullback_x_eq_projectiveDivisorOf_sum`, `lemma5_of_pole_orders_and_support_card`, `l6_v_1_1_sepDegree_eq_pointCount_of_witnesses`.
- **Used by**: Not referenced within this file — dead-code candidate in this file (intended as a downstream entry point).
- **Visibility**: public
- **Lines**: 265–335 (proof ~15 lines)
- **Notes**: Proof >30 lines if one counts the signature (signature is very long). Proof body itself is ~15 lines. This is the most comprehensively parameterized form, exposing all primitive witnesses.

---

### `theorem hasse_bound_from_L6_witnesses`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] (hq : 2 ≤ Fintype.card K) (h_finrank_eq_2_deg : ...) (h_compA : ComputationA_bridge_pullback_x_gen W hq) (h_lemma5 : ...) (h_qf_nonneg : ∀ r s : ℤ, 0 ≤ q * r² − trace * r * s + s²) : |#E(𝔽_q) − q − 1| ≤ 2 * √q`
- **What**: Top-level Hasse bound consumer: given L6's three substantive witnesses plus the quadratic-form nonnegativity witness `h_qf_nonneg`, discharges the full Hasse bound `|#E(𝔽_q) − q − 1| ≤ 2√q`.
- **How**: Calls `hasse_bound_of_witnesses W` with a witness bundle constructed via `refine`. The `pc_sep` field is discharged by extracting characteristic from `FiniteField.card'` and invoking `isogOneSub_negFrobenius_isSeparable`; `pc_fin` is discharged by `isogOneSub_negFrobenius_finiteDimensional`; `pc_sepDeg_eq_pointCount` is discharged by `l6_v_1_1_sepDegree_eq_pointCount_of_witnesses`.
- **Hypotheses**: Elliptic curve W, finite K with `|K| ≥ 2`, finitely many K-points; B3 tower formula; ComputationA bridge; Lemma 5 pole-sum; quadratic-form nonnegativity.
- **Uses from project**: `isogOneSub_negFrobenius`, `isogOneSub_negFrobenius_isSeparable`, `isogOneSub_negFrobenius_finiteDimensional`, `l6_v_1_1_sepDegree_eq_pointCount_of_witnesses`, `hasse_bound_of_witnesses`, `ComputationA_bridge_pullback_x_gen`, `x_gen`, `W_smooth`, `pointCount`, `isogTrace`, `frobeniusIsog`.
- **Used by**: Not referenced within this file — intended as a top-level external entry point.
- **Visibility**: public
- **Lines**: 355–393 (proof ~10 lines tactic body)
- **Notes**: The `h_qf_nonneg` hypothesis is the `qf_nonneg` Hasse witness (Silverman V.1.1 quadratic-form positivity), the one remaining open substantive obligation in the overall project.

---

## Summary statistics

| Metric | Value |
|--------|-------|
| Total declarations | 6 |
| Theorems | 6 |
| Defs | 0 |
| Instances | 0 |
| Sorries | 0 |
| `set_option maxHeartbeats` occurrences | 0 |
| Long proofs (>30 lines) | 0 |

**Key API** (referenced by 3+ declarations within the file):
- `l6_v_1_1_sepDegree_eq_pointCount_of_witnesses` — called by `witness_pc_sepDeg_of_witnesses`, `l6_v_1_1_sepDegree_eq_pointCount_of_primitive_witnesses`, and `hasse_bound_from_L6_witnesses`.
- `isogOneSub_negFrobenius` — appears in all 6 declarations.

**Unused within file** (dead-code candidates):
- `finrank_pullback_fieldRange_eq_degree` — not called by anything in this file.
- `bridgeA_intermediateField_finrank_eq_two_mul_degree_of_witness` — not called by anything in this file.
- `witness_pc_sepDeg_of_witnesses` — not called by anything in this file.
- `l6_v_1_1_sepDegree_eq_pointCount_of_primitive_witnesses` — not called by anything in this file.
- `hasse_bound_from_L6_witnesses` — not called by anything in this file.
