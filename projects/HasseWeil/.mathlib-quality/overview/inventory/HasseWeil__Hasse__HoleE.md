# Inventory: ./HasseWeil/Hasse/HoleE.lean

**File**: `HasseWeil/Hasse/HoleE.lean`
**Lines**: 1–195
**Total declarations**: 4 theorems, 0 defs, 0 instances

---

## Summary

This file is the "HOLE E closer" — it packages the Hasse bound proof under the
hypothesis that the one-minus-Frobenius isogeny `isogOneSub_negFrobenius W hq`
is separable, finite-dimensional, and that a fiber-count witness holds, together
with a quadratic-form non-negativity hypothesis. The file previously contained
many placeholder theorems (deleted 2026-05-28) and now contains four live
theorems, all `sorry`-free. All four are direct applications of `BoundOfWitnesses`
/ `QuadraticForm` lemmas instantiated at `isogOneSub_negFrobenius`.

---

## Declarations

---

### `theorem hasse_bound_via_signed_QF_negFrobenius_beta_param`

- **Type**:
  ```
  (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
  (hq : 2 ≤ Fintype.card K)
  (h_pc_sep : (isogOneSub_negFrobenius W hq).IsSeparable)
  (h_pc_fin : @FiniteDimensional … (isogOneSub_negFrobenius W hq).toAlgebra.toModule)
  (h_sepDeg_eq_pointCount : (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine)
  [Finite (isogOneSub_negFrobenius W hq).kernel]
  (β_qf : ℤ → ℤ → Isogeny W.toAffine W.toAffine)
  (h_qf_deg : ∀ r s : ℤ, ((β_qf r s).degree : ℤ) =
    (Fintype.card K : ℤ) * r^2 - isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s^2)
  : |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤ 2 * Real.sqrt (Fintype.card K : ℝ)
  ```
- **What**: The Hasse bound `|#E(𝔽_q) − q − 1| ≤ 2√q` given a parametric isogeny
  family `β_qf` whose degree equals the quadratic form `q·r² − t·r·s + s²` (with t
  the trace of Frobenius on `isogOneSub_negFrobenius`). Avoids hard-coding the
  placeholder `isogSmulSub`.
- **How**: One-line application of `hasse_bound_of_all_witnesses`, supplying
  `isogOneSub_negFrobenius W hq` as the point-count isogeny and building the fiber
  witness from `hole_d_of_hom_and_sepDegree` (using `h_sepDeg_eq_pointCount` and
  the trivially-satisfied homomorphism condition `rfl`).
- **Hypotheses**: W is an elliptic curve over a finite field K with `|K| ≥ 2`; the
  isogeny `1 − π` (negFrobenius variant) is separable and has finite-dimensional
  function-field extension; its separable degree equals `#E(𝔽_q)`; an isogeny
  family parametrised by integers has degree equal to the explicit QF expression.
- **Uses from project**: `isogOneSub_negFrobenius`, `isogTrace`, `frobeniusIsog`,
  `pointCount`, `hasse_bound_of_all_witnesses`, `hole_d_of_hom_and_sepDegree`
- **Used by**: unused in file (no callers within HoleE.lean); called from no other
  project file (no external callers found by grep)
- **Visibility**: public
- **Lines**: 66–91, proof body lines 83–91 (≈9 lines)
- **Notes**: No `sorry`, no `set_option`. Proof is a single structured application
  term; the `β_qf`-parametric design was introduced to avoid the structurally-false
  degree equality when `isogSmulSub` was the placeholder.

---

### `theorem hasse_bound_via_signed_QF_negFrobenius_qf_nonneg`

- **Type**:
  ```
  (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
  (hq : 2 ≤ Fintype.card K)
  (h_pc_sep : (isogOneSub_negFrobenius W hq).IsSeparable)
  (h_pc_fin : @FiniteDimensional … (isogOneSub_negFrobenius W hq).toAlgebra.toModule)
  (h_sepDeg_eq_pointCount : (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine)
  [h_pc_ker_finite : Finite (isogOneSub_negFrobenius W hq).kernel]
  (h_qf_nonneg : ∀ r s : ℤ, 0 ≤ (Fintype.card K : ℤ) * r^2
    - isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s^2)
  : |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤ 2 * Real.sqrt (Fintype.card K : ℝ)
  ```
- **What**: The Hasse bound under a non-negativity hypothesis on the quadratic form
  `q·r² − t·r·s + s²` rather than an isogeny-family degree equality. This is the
  main live entry point for `Verschiebung/Cascade.lean` and `Hasse/Final.lean`.
- **How**: One-line application of `hasse_bound_of_all_qf_nonneg_witnesses` from
  `QuadraticForm.lean`, using `hole_d_of_hom_and_sepDegree` for the fiber witness
  (same pattern as `beta_param`).
- **Hypotheses**: Same as `beta_param` except the QF hypothesis is weakened to
  non-negativity rather than an isogeny-family degree equality.
- **Uses from project**: `isogOneSub_negFrobenius`, `isogTrace`, `frobeniusIsog`,
  `pointCount`, `hasse_bound_of_all_qf_nonneg_witnesses`, `hole_d_of_hom_and_sepDegree`
- **Used by**: `hasse_bound_via_signed_QF_negFrobenius_streamlined_qf_nonneg` (within
  this file); `Verschiebung/Cascade.lean`; `Hasse/Final.lean`
- **Visibility**: public
- **Lines**: 108–131, proof body lines 124–131 (≈8 lines)
- **Notes**: No `sorry`, no `set_option`. The key live downstream theorem in the Hasse
  bound assembly; consumed by at least 3 external callers.

---

### `theorem hasse_bound_sq_via_signed_QF_negFrobenius_qf_nonneg`

- **Type**:
  ```
  (same hypotheses as hasse_bound_via_signed_QF_negFrobenius_qf_nonneg)
  : ((pointCount W.toAffine : ℤ) - Fintype.card K - 1)^2 ≤ 4 * (Fintype.card K : ℤ)
  ```
- **What**: The squared-integer form of the Hasse bound `(#E − q − 1)² ≤ 4q`
  (integer statement, no square roots), under the same QF non-negativity hypothesis.
- **How**: One-line application of `hasse_bound_sq_of_all_qf_nonneg_witnesses`
  from `QuadraticForm.lean`, with the same fiber-witness construction via
  `hole_d_of_hom_and_sepDegree`.
- **Hypotheses**: Same as `hasse_bound_via_signed_QF_negFrobenius_qf_nonneg`.
- **Uses from project**: `isogOneSub_negFrobenius`, `isogTrace`, `frobeniusIsog`,
  `pointCount`, `hasse_bound_sq_of_all_qf_nonneg_witnesses`,
  `hole_d_of_hom_and_sepDegree`
- **Used by**: unused in file; `Verschiebung/Cascade.lean`, `Hasse/Final.lean`
- **Visibility**: public
- **Lines**: 134–157, proof body lines 150–157 (≈8 lines)
- **Notes**: No `sorry`, no `set_option`. Squared form is useful for integer
  discriminant arguments downstream.

---

### `theorem hasse_bound_via_signed_QF_negFrobenius_streamlined_qf_nonneg`

- **Type**:
  ```
  (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
  (hq : 2 ≤ Fintype.card K)
  (h_pc_sep : (isogOneSub_negFrobenius W hq).IsSeparable)
  (h_pc_fin : @FiniteDimensional … (isogOneSub_negFrobenius W hq).toAlgebra.toModule)
  (h_pc_fiber_witness : ∃ P₀ : W.toAffine.Point,
    Nat.card {P // (isogOneSub_negFrobenius W hq).toAddMonoidHom P
                  = (isogOneSub_negFrobenius W hq).toAddMonoidHom P₀}
    = (isogOneSub_negFrobenius W hq).sepDegree)
  [Finite (isogOneSub_negFrobenius W hq).kernel]
  (h_qf_nonneg : ∀ r s : ℤ, 0 ≤ …)
  : |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤ 2 * Real.sqrt (Fintype.card K : ℝ)
  ```
- **What**: A streamlined variant that takes the fiber witness `h_pc_fiber_witness`
  explicitly (rather than deriving it from `h_sepDeg_eq_pointCount`), forwarding
  directly to `hasse_bound_via_signed_QF_negFrobenius_qf_nonneg` after deriving
  `h_sepDeg_eq_pointCount` from the fiber witness via
  `isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_witnesses`.
- **How**: Two-line proof: apply
  `isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_witnesses` to convert the
  fiber witness to `sepDegree = pointCount`, then delegate to
  `hasse_bound_via_signed_QF_negFrobenius_qf_nonneg`.
- **Hypotheses**: Same as the `qf_nonneg` theorem but with an explicit fiber-count
  witness (`∃ P₀, Nat.card of fibre = sepDegree`) instead of `sepDegree = pointCount`.
- **Uses from project**: `isogOneSub_negFrobenius`, `isogTrace`, `frobeniusIsog`,
  `pointCount`, `isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_witnesses`,
  `hasse_bound_via_signed_QF_negFrobenius_qf_nonneg`
- **Used by**: unused in file, no external callers found
- **Visibility**: public
- **Lines**: 162–184, proof body lines 181–184 (≈4 lines)
- **Notes**: No `sorry`, no `set_option`. Provides an alternative interface that
  exposes the fiber-count witness explicitly; useful when that witness is easier to
  supply directly than going via `sepDegree = pointCount`.

---

## Cross-reference summary

| Declaration in this file | Called by (within file) | Called by (other files) |
|---|---|---|
| `hasse_bound_via_signed_QF_negFrobenius_beta_param` | — | none found |
| `hasse_bound_via_signed_QF_negFrobenius_qf_nonneg` | `_streamlined_qf_nonneg` | `Verschiebung/Cascade.lean`, `Hasse/Final.lean` |
| `hasse_bound_sq_via_signed_QF_negFrobenius_qf_nonneg` | — | `Verschiebung/Cascade.lean`, `Hasse/Final.lean` |
| `hasse_bound_via_signed_QF_negFrobenius_streamlined_qf_nonneg` | — | none found |

## Key project declarations used

| Project declaration | Used by (in this file) |
|---|---|
| `isogOneSub_negFrobenius` | all 4 theorems |
| `isogTrace` | all 4 theorems |
| `frobeniusIsog` | all 4 theorems |
| `pointCount` | all 4 theorems |
| `hole_d_of_hom_and_sepDegree` | 1st, 2nd, 3rd theorems |
| `hasse_bound_of_all_witnesses` | `beta_param` |
| `hasse_bound_of_all_qf_nonneg_witnesses` | `qf_nonneg` |
| `hasse_bound_sq_of_all_qf_nonneg_witnesses` | `sq_qf_nonneg` |
| `isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_witnesses` | `streamlined_qf_nonneg` |
| `hasse_bound_via_signed_QF_negFrobenius_qf_nonneg` | `streamlined_qf_nonneg` |
