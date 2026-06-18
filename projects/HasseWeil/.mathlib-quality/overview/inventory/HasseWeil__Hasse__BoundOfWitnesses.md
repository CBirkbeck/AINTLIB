# Inventory: ./HasseWeil/Hasse/BoundOfWitnesses.lean

**File**: `HasseWeil/Hasse/BoundOfWitnesses.lean`
**Imports**: `HasseWeil.HasseBound`, `HasseWeil.Hasse.PointFix`
**Namespace**: `HasseWeil`
**Total declarations**: 6 (all theorems, no defs/instances)

---

## Module docstring summary

Witness-parametric companions of the Hasse bound (Silverman V.1.1). Provides
`traceOfFrobenius_sq_le_of_witness`, `hasse_bound_of_t_witness`,
`hasse_bound_sq_of_t_witness`, `hasse_bound_of_full_witnesses`,
`hasse_bound_of_all_witnesses`, and `hasse_bound_sq_of_all_witnesses`.
The file's role is to expose a clean plug-in API: callers supply witnesses
for the point-count identity and the quadratic-form degree family and receive
the Hasse bound without needing the still-sorry unconditional chain.

---

### `theorem traceOfFrobenius_sq_le_of_witness`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] (t : ℤ) (β : ℤ → ℤ → Isogeny W.toAffine W.toAffine) (h_deg : ∀ r s : ℤ, ((β r s).degree : ℤ) = (Fintype.card K : ℤ) * r ^ 2 - t * r * s + s ^ 2) : t ^ 2 ≤ 4 * (Fintype.card K : ℤ)`
- **What**: Proves the discriminant bound `t² ≤ 4q` given a family of isogenies whose degrees realise the binary quadratic form `q·r² − t·r·s + s²` for all integer pairs `(r, s)`.
- **How**: Applies `trace_sq_le_four_mul_deg` (from `HasseBound.lean`) at `q = Fintype.card K`, substituting the degree formula via `h_deg` and noting degrees are nonneg via `Int.natCast_nonneg`.
- **Hypotheses**: `W` an elliptic curve over a finite field `K`; a family `β` of self-isogenies whose integer degrees equal `q·r² − t·r·s + s²`.
- **Uses from project**: `trace_sq_le_four_mul_deg` (from `HasseBound.lean`).
- **Used by**: `hasse_bound_of_t_witness`, `hasse_bound_sq_of_t_witness` (within this file).
- **Visibility**: public
- **Lines**: 55–65 (proof: 3 lines)
- **Notes**: Short proof; no sorry; no maxHeartbeats override.

---

### `theorem hasse_bound_of_t_witness`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] (t : ℤ) (h_pc : (pointCount W.toAffine : ℤ) = Fintype.card K + 1 - t) (β : ℤ → ℤ → Isogeny W.toAffine W.toAffine) (h_deg : ∀ r s : ℤ, ((β r s).degree : ℤ) = (Fintype.card K : ℤ) * r ^ 2 - t * r * s + s ^ 2) : |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤ 2 * sqrt (Fintype.card K : ℝ)`
- **What**: Proves the Hasse bound `|#E(𝔽_q) − q − 1| ≤ 2√q` in real-valued form, given a point-count witness `#E(𝔽_q) = q + 1 − t` and the quadratic-form degree witness family.
- **How**: Rewrites the LHS as `|−t|` via the point-count hypothesis and a cast to `ℝ` (`exact_mod_cast`), then applies `abs_le_two_sqrt_of_sq_le` using the discriminant bound from `traceOfFrobenius_sq_le_of_witness`.
- **Hypotheses**: Elliptic curve over a finite field; `Fintype` on `W.toAffine.Point`; point-count and quadratic-form degree witnesses.
- **Uses from project**: `traceOfFrobenius_sq_le_of_witness` (this file), `abs_le_two_sqrt_of_sq_le` (from `HasseBound.lean`).
- **Used by**: `hasse_bound_of_full_witnesses` (this file).
- **Visibility**: public
- **Lines**: 76–90 (proof: 7 lines)
- **Notes**: No sorry; no maxHeartbeats override; straightforward cast-and-apply argument.

---

### `theorem hasse_bound_sq_of_t_witness`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] (t : ℤ) (h_pc : ...) (β : ...) (h_deg : ...) : ((pointCount W.toAffine : ℤ) - Fintype.card K - 1) ^ 2 ≤ 4 * (Fintype.card K : ℤ)`
- **What**: Integer-form Hasse bound: `(#E(𝔽_q) − q − 1)² ≤ 4q`, given the same witnesses as `hasse_bound_of_t_witness`.
- **How**: Rewrites the LHS as `(−t)² = t²` via `htrace` and `neg_sq`, then applies `traceOfFrobenius_sq_le_of_witness` directly.
- **Hypotheses**: Same as `hasse_bound_of_t_witness`.
- **Uses from project**: `traceOfFrobenius_sq_le_of_witness` (this file).
- **Used by**: `hasse_bound_sq_of_all_witnesses` (this file).
- **Visibility**: public
- **Lines**: 94–105 (proof: 4 lines)
- **Notes**: No sorry; no maxHeartbeats override; two-step proof.

---

### `theorem hasse_bound_of_full_witnesses`

- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] (β_pc : Isogeny W.toAffine W.toAffine) (h_pc_hom : β_pc.toAddMonoidHom = (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom) (h_pc_ker_deg : Nat.card β_pc.kernel = β_pc.degree) (β : ℤ → ℤ → Isogeny W.toAffine W.toAffine) (h_deg : ...) : |...| ≤ 2 * sqrt (Fintype.card K : ℝ)`
- **What**: Hasse bound in the "fully-chained" form: the caller provides the `1−π` isogeny with its point-map witness and `#ker = deg` witness, plus the quadratic-form family; the trace `t` is computed internally as `isogTrace (frobeniusIsog W) β_pc`.
- **How**: Directly composes `pointCount_eq_of_hom_kernel_witness` (from `PointFix.lean`) to produce the point-count witness and passes it to `hasse_bound_of_t_witness`.
- **Hypotheses**: `β_pc` whose `toAddMonoidHom = id − frob` and `Nat.card(ker β_pc) = β_pc.degree`; quadratic-form degree family.
- **Uses from project**: `pointCount_eq_of_hom_kernel_witness` (from `HasseWeil.Hasse.PointFix`), `hasse_bound_of_t_witness` (this file), `isogTrace` (from `PointFix`), `frobeniusIsog` (from `PointFix`).
- **Used by**: `hasse_bound_of_all_witnesses`, `hasse_bound_sq_of_all_witnesses` (this file).
- **Visibility**: public
- **Lines**: 117–130 (proof: term-mode, 2 lines)
- **Notes**: No sorry; no maxHeartbeats override; thin wrapper (term-mode proof).

---

### `theorem hasse_bound_of_all_witnesses`

- **Type**: (see lines 169–197; signature takes `β_pc`, `h_pc_hom`, `h_pc_sep`, `h_pc_fin`, `h_pc_fiber_witness`, `[h_pc_ker_finite]`, `β_qf`, `h_qf_deg`) `: |...| ≤ 2 * sqrt (Fintype.card K : ℝ)`
- **What**: Consolidated Hasse bound from upstream witnesses. Gathers all dependencies of the Silverman V.1 chain: the `1−π` isogeny at the point-map level, its separability, a finite-dimensionality instance, a one-fiber cardinality witness, finiteness of the kernel, and the quadratic-form degree family. Derives `#ker = deg` internally via `Isogeny.card_kernel_eq_degree_of_separable_witness`.
- **How**: Uses `Isogeny.card_kernel_eq_degree_of_separable_witness` (from `EC/IsogenyKernel.lean`) to convert `(h_pc_sep, h_pc_fin, h_pc_fiber_witness)` into `h_pc_ker_deg`, then delegates to `hasse_bound_of_full_witnesses`.
- **Hypotheses**: Elliptic curve over a finite field; `β_pc` a separable self-isogeny equalling `id − frob` at the group-hom level, with a finite-dimensional function-field extension, a one-fiber cardinality witness, and a finite kernel; a quadratic-form degree family `β_qf`.
- **Uses from project**: `Isogeny.card_kernel_eq_degree_of_separable_witness` (from `HasseWeil.EC.IsogenyKernel`), `hasse_bound_of_full_witnesses` (this file), `isogTrace`, `frobeniusIsog` (from `PointFix`).
- **Used by**: unused in file (top-level API for external callers).
- **Visibility**: public
- **Lines**: 169–197 (proof: term-mode, 4 lines)
- **Notes**: No sorry; no maxHeartbeats override; the docstring contains a detailed witness-to-ticket table mapping each hypothesis to its Silverman reference and outstanding ticket.

---

### `theorem hasse_bound_sq_of_all_witnesses`

- **Type**: Same hypotheses as `hasse_bound_of_all_witnesses`; conclusion: `((pointCount W.toAffine : ℤ) - Fintype.card K - 1) ^ 2 ≤ 4 * (Fintype.card K : ℤ)`
- **What**: Integer-form variant of `hasse_bound_of_all_witnesses`: same upstream witnesses, squared conclusion.
- **How**: Applies `hasse_bound_sq_of_t_witness` with the trace computed from `isogTrace (frobeniusIsog W) β_pc`, after deriving `h_pc_ker_deg` via `Isogeny.card_kernel_eq_degree_of_separable_witness` and then `pointCount_eq_of_hom_kernel_witness`.
- **Hypotheses**: Same as `hasse_bound_of_all_witnesses`.
- **Uses from project**: `hasse_bound_sq_of_t_witness` (this file), `pointCount_eq_of_hom_kernel_witness` (from `PointFix`), `Isogeny.card_kernel_eq_degree_of_separable_witness` (from `EC/IsogenyKernel`), `isogTrace`, `frobeniusIsog` (from `PointFix`).
- **Used by**: unused in file (top-level API for external callers).
- **Visibility**: public
- **Lines**: 201–224 (proof: term-mode, 5 lines)
- **Notes**: No sorry; no maxHeartbeats override; parallel to `hasse_bound_of_all_witnesses` with squared conclusion.

---

## Summary statistics

| Metric | Value |
|--------|-------|
| Total declarations | 6 |
| Theorems/lemmas | 6 |
| Defs | 0 |
| Instances | 0 |
| Sorries | 0 |
| maxHeartbeats overrides | 0 |
| Proofs > 30 lines | 0 |

## Key API (used by 3+ declarations in this file)

- `traceOfFrobenius_sq_le_of_witness` — used by `hasse_bound_of_t_witness` and `hasse_bound_sq_of_t_witness` (2 direct callers, plus indirectly via the full/all variants = conceptual center of the file).
- `hasse_bound_of_full_witnesses` — used by `hasse_bound_of_all_witnesses` and `hasse_bound_sq_of_all_witnesses`.
- `Isogeny.card_kernel_eq_degree_of_separable_witness` — called in both `hasse_bound_of_all_witnesses` and `hasse_bound_sq_of_all_witnesses`.

## Unused declarations (dead-code candidates in this file)

- `hasse_bound_of_all_witnesses` — not referenced by anything else in this file (top-level external API).
- `hasse_bound_sq_of_all_witnesses` — not referenced by anything else in this file (top-level external API).

## Notes

This is a thin glue/API file with no mathematical content beyond composition: every proof delegates immediately to a previously established lemma. The file serves as a documented plug-in interface mapping Silverman V.1 witnesses to the Hasse bound, with a ticket table in the `hasse_bound_of_all_witnesses` docstring. No sorries, no maxHeartbeats overrides, no proofs exceed 10 lines.
