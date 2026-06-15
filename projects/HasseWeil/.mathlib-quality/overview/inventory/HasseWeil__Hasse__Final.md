# Inventory: ./HasseWeil/Hasse/Final.lean

**File purpose**: Public-facing canonical entry point for the Hasse bound. Bridges the
`HasseWitnesses` record (defined in `Hasse/Witnesses.lean`) to the two main bound theorems
in `Hasse/HoleE.lean` (absolute-value form and squared-integer form).

**Total declarations**: 2 (both `theorem`)

---

### `theorem hasse_bound_of_witnesses`

- **Type**:
  ```
  (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
  {hq : 2 ≤ Fintype.card K} (hw : HasseWitnesses W hq) :
  |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤ 2 * Real.sqrt (Fintype.card K : ℝ)
  ```
- **What**: Derives the Hasse bound `|#E(F_q) − q − 1| ≤ 2√q` for an elliptic curve W over a
  finite field K, given a fully-discharged `HasseWitnesses` bundle (separability, finite-dimensionality,
  V.1.3 degree equality, and QF non-negativity).
- **How**: First establishes `Finite (isogOneSub_negFrobenius W hq).kernel` by rewriting the kernel
  as `⊤` via `kernel_eq_top_of_hom_eq_id_sub_frobenius` (from `Hasse/PointFix.lean`), then
  delegates to `hasse_bound_via_signed_QF_negFrobenius_qf_nonneg` (from `Hasse/HoleE.lean`),
  passing the four fields of `hw` individually.
- **Hypotheses**: K is a finite field with ≥ 2 elements; W is an elliptic curve over K with a
  finitely many K-rational points; the witness bundle `hw` discharges separability of (1−π),
  finite-dimensionality, V.1.3 (sepDeg = pointCount), and QF non-negativity.
- **Uses from project**:
  - `isogOneSub_negFrobenius` (from `HasseWeil.AdditionPullback.Frobenius`)
  - `kernel_eq_top_of_hom_eq_id_sub_frobenius` (from `Hasse.PointFix`)
  - `hasse_bound_via_signed_QF_negFrobenius_qf_nonneg` (from `Hasse.HoleE`)
  - `HasseWitnesses` + its fields `pc_sep`, `pc_fin`, `pc_sepDeg_eq_pointCount`, `qf_nonneg`
    (from `Hasse.Witnesses`)
  - `pointCount` (from `HasseWeil.Frobenius`)
- **Used by**: unused in this file (called by `Hasse/OpenLemmas.lean` and `Hasse/L6ViaPoleDivisor.lean`)
- **Visibility**: public
- **Lines**: 48–58 (proof body lines 53–58, proof length 6 lines)
- **Notes**: No `set_option maxHeartbeats`. No sorry. The `haveI` block at lines 53–56 is boilerplate
  to promote `Finite` from the `⊤` subgroup for the downstream lemma's typeclass; the mathematical
  work is entirely in `hasse_bound_via_signed_QF_negFrobenius_qf_nonneg`.

---

### `theorem hasse_bound_sq_of_witnesses`

- **Type**:
  ```
  (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
  {hq : 2 ≤ Fintype.card K} (hw : HasseWitnesses W hq) :
  ((pointCount W.toAffine : ℤ) - Fintype.card K - 1) ^ 2 ≤ 4 * (Fintype.card K : ℤ)
  ```
- **What**: Squared-integer form of the Hasse bound: `(#E(F_q) − q − 1)² ≤ 4q`, from the same
  `HasseWitnesses` bundle, stated over `ℤ` rather than `ℝ`.
- **How**: Structurally identical to `hasse_bound_of_witnesses`: the same `haveI` boilerplate for
  `Finite (isogOneSub_negFrobenius W hq).kernel` via `kernel_eq_top_of_hom_eq_id_sub_frobenius`,
  then delegates to `hasse_bound_sq_via_signed_QF_negFrobenius_qf_nonneg` (from `Hasse/HoleE.lean`).
- **Hypotheses**: Same as `hasse_bound_of_witnesses`.
- **Uses from project**:
  - `isogOneSub_negFrobenius` (from `HasseWeil.AdditionPullback.Frobenius`)
  - `kernel_eq_top_of_hom_eq_id_sub_frobenius` (from `Hasse.PointFix`)
  - `hasse_bound_sq_via_signed_QF_negFrobenius_qf_nonneg` (from `Hasse.HoleE`)
  - `HasseWitnesses` + fields `pc_sep`, `pc_fin`, `pc_sepDeg_eq_pointCount`, `qf_nonneg`
    (from `Hasse.Witnesses`)
  - `pointCount` (from `HasseWeil.Frobenius`)
- **Used by**: unused in this file (called by `Hasse/OpenLemmas.lean`)
- **Visibility**: public
- **Lines**: 62–72 (proof body lines 67–72, proof length 6 lines)
- **Notes**: No `set_option maxHeartbeats`. No sorry. Proof is a near-verbatim duplicate of
  `hasse_bound_of_witnesses` with `hasse_bound_sq_via_signed_QF_negFrobenius_qf_nonneg` in place of
  the real-valued variant. The duplicated `haveI` block (lines 67–70) is identical to lines 53–56.

---

## Summary statistics

| Metric | Value |
|---|---|
| Total declarations | 2 |
| Theorems / lemmas | 2 |
| Defs | 0 |
| Instances | 0 |
| Declarations with `sorry` | 0 |
| `set_option maxHeartbeats` occurrences | 0 |
| Long proofs (>30 lines) | 0 |
| Unused in file | both (all public API, consumers are in other files) |
| Key API (used 3+ times in file) | none (file has only 2 declarations, no shared helpers) |

## Notable observations

The file is a thin two-theorem adapter: it exists solely to package the `HasseWitnesses` record into
the low-level HoleE chain. The `haveI` block establishing `Finite (isogOneSub_negFrobenius …).kernel`
is copy-pasted identically in both theorems and could be extracted into a private lemma. Both theorems
are currently unused within this file and are consumed by `Hasse/OpenLemmas.lean` and
`Hasse/L6ViaPoleDivisor.lean`.
