# Inventory: ./HasseWeil/WeilPairing/HasseAssembly.lean

**File**: `HasseWeil/WeilPairing/HasseAssembly.lean`
**Lines**: 1–171
**Module**: `HasseWeil.WeilPairing` (Route 2A capstone assembly)
**Imports**: `HasseWeil.WeilPairing.DetDeg`, `HasseWeil.WeilPairing.Assembly`, `HasseWeil.HasseWeilSkeleton`

---

## Overview

This is the final capstone assembly file for Route 2A of the Hasse bound proof. It bridges the Weil-pairing Frobenius-matrix determinant data (from `DetDeg.lean`) into the shipped Hasse-bound skeleton reduction (`Assembly.lean`), closing the `qf_nonneg_skeleton` GAP-QF leaf and hence `|#E(F_q) − q − 1| ≤ 2√q`. Four declarations, no sorries, no `set_option maxHeartbeats`.

---

## Declarations

### `theorem qf_nonneg_skeleton_of_weil_det_data`

- **Type**:
  ```
  qf_nonneg_skeleton_of_weil_det_data (hq : 2 ≤ Fintype.card K)
      (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
      (hres : ∀ r s : ℤ, ¬ ((ringChar K) : ℤ) ∣ s → ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ ringChar K →
        ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ), M.det = (q : ZMod ℓ) ∧
        (1 - M).det = (#E : ZMod ℓ) ∧ ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (deg r s : ZMod ℓ)) :
    ∀ r s : ℤ, 0 ≤ q * r ^ 2 − isogTrace(π)(1−π) * r * s + s ^ 2
  ```
- **What**: Proves the Hasse quadratic form `q·r²−t·rs+s²≥0` for all `(r,s)∈ℤ²`, given per-`ℓ` Frobenius-matrix determinant data (only when `p∤s`). This is the GAP-QF leaf closed by the Weil-pairing DET-DEG approach (p∤s variant).
- **How**: Extracts the prime characteristic `p` and `Fact p.Prime` instance via `FiniteField.card'`, then translates `ringChar K = p` and delegates entirely to `qf_nonneg_of_frob_det_residual` from `Assembly.lean`, rewriting the `ringChar`-gated hypothesis into the `p`-gated form.
- **Hypotheses**: `K` finite field with `#K ≥ 2`; `W` elliptic over `K`; `deg : ℤ² → ℤ` a non-negative degree function; per-`ℓ` matrix data `hres` for `p∤s`.
- **Uses from project**: `qf_nonneg_of_frob_det_residual` (Assembly.lean), `isogTrace` (Endomorphism.lean), `frobeniusIsog` (Frobenius.lean), `isogOneSub_negFrobenius` (AdditionPullback/Frobenius.lean).
- **Used by**: `hasse_bound_via_weil_pairing` (line 145 in this file).
- **Visibility**: public
- **Lines**: 74–94 (proof body: lines 84–94, ~11 lines)
- **Notes**: None. No sorry, no maxHeartbeats.

---

### `theorem qf_nonneg_skeleton_of_weil_det_data_both`

- **Type**:
  ```
  qf_nonneg_skeleton_of_weil_det_data_both (hq : 2 ≤ Fintype.card K)
      (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
      (hres : ∀ r s : ℤ, ¬ ((ringChar K) : ℤ) ∣ r → ¬ ((ringChar K) : ℤ) ∣ s →
          ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ ringChar K →
        ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ), ...same three det conditions...) :
    ∀ r s : ℤ, 0 ≤ q * r ^ 2 − isogTrace(π)(1−π) * r * s + s ^ 2
  ```
- **What**: Identical conclusion to `qf_nonneg_skeleton_of_weil_det_data`, but requires the per-`ℓ` Frobenius matrix data only on the strictly smaller locus `{p∤r ∧ p∤s}` (both coordinates coprime to char). This is the "Route B" variant that avoids the inseparable `p∣r` pencil scaling.
- **How**: Same structure as the p∤s variant: `FiniteField.card'` for the prime and characteristic instances, `ringChar K = p` rewrite, then `qf_nonneg_of_frob_det_residual_both` (the stronger "coprime-BOTH" arithmetic discriminant lemma from `Assembly.lean`) handles the reduction.
- **Hypotheses**: Same as above but `hres` only needs matrix data when `p∤r` AND `p∤s`.
- **Uses from project**: `qf_nonneg_of_frob_det_residual_both` (Assembly.lean), `isogTrace` (Endomorphism.lean), `frobeniusIsog` (Frobenius.lean), `isogOneSub_negFrobenius` (AdditionPullback/Frobenius.lean).
- **Used by**: `hasse_bound_via_weil_pairing_both` (line 168 in this file).
- **Visibility**: public
- **Lines**: 103–121 (proof body: lines 114–121, ~8 lines)
- **Notes**: This is the variant consumed by the unconditional Hasse bound in `HasseBound.lean` via `FrobMatrixData.lean`. No sorry, no maxHeartbeats.

---

### `theorem hasse_bound_via_weil_pairing`

- **Type**:
  ```
  hasse_bound_via_weil_pairing (hq : 2 ≤ Fintype.card K)
      (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
      (hres : ∀ r s : ℤ, ¬ ((ringChar K) : ℤ) ∣ s → ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ ringChar K →
        ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ), M.det = (q : ZMod ℓ) ∧ ...) :
    |(↑(pointCount W.toAffine) − ↑(Fintype.card K) − 1 : ℝ)| ≤ 2 * Real.sqrt (Fintype.card K : ℝ)
  ```
- **What**: Proves the Hasse bound `|#E(F_q) − q − 1| ≤ 2√q` from per-`ℓ` Frobenius-matrix determinant data (p∤s variant). This is the Route-2A capstone milestone — the full Hasse inequality for an elliptic curve over a finite field.
- **How**: One-liner term-mode proof: calls `hasse_bound_of_full_qf_nonneg_witnesses` from `HasseWeilSkeleton` with four arguments: `isogOneSub_negFrobenius` (the 1−π isogeny), `isogOneSub_negFrobenius_toAddMonoidHom` (its group-hom witness), `ker_deg_skeleton` (the kernel-degree leaf, already closed), and `qf_nonneg_skeleton_of_weil_det_data` (the GAP-QF leaf just proved).
- **Hypotheses**: Finite field `K` with `#K ≥ 2`, elliptic curve `W` over `K` with finitely many points, non-negative degree function `deg`, and per-`ℓ` matrix data for `p∤s`.
- **Uses from project**: `hasse_bound_of_full_qf_nonneg_witnesses` (Hasse/QuadraticForm.lean), `isogOneSub_negFrobenius` (AdditionPullback/Frobenius.lean), `isogOneSub_negFrobenius_toAddMonoidHom` (AdditionPullback/Frobenius.lean), `ker_deg_skeleton` (GapSpines.lean), `qf_nonneg_skeleton_of_weil_det_data` (this file), `pointCount` (Frobenius.lean).
- **Used by**: `FrobMatrixData.lean` (external; specifically used at line 360 of that file).
- **Visibility**: public
- **Lines**: 132–145 (term-mode proof: lines 142–145, 4 lines total including conclusion)
- **Notes**: No sorry, no maxHeartbeats. The `hres` hypothesis carries the open geometric residual (K̄-base-change Frobenius pencil scaling).

---

### `theorem hasse_bound_via_weil_pairing_both`

- **Type**:
  ```
  hasse_bound_via_weil_pairing_both (hq : 2 ≤ Fintype.card K)
      (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
      (hres : ∀ r s : ℤ, ¬ ((ringChar K) : ℤ) ∣ r → ¬ ((ringChar K) : ℤ) ∣ s →
          ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ ringChar K → ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ), ...) :
    |(↑(pointCount W.toAffine) − ↑(Fintype.card K) − 1 : ℝ)| ≤ 2 * Real.sqrt (Fintype.card K : ℝ)
  ```
- **What**: Identical conclusion to `hasse_bound_via_weil_pairing` (the full Hasse bound), but the per-`ℓ` matrix data is only required on the "coprime-BOTH" locus `{p∤r ∧ p∤s}`. This is the form actually consumed by the unconditional `hasse_bound_unconditional` in `HasseBound.lean`.
- **How**: Same term-mode structure as `hasse_bound_via_weil_pairing`, but uses `qf_nonneg_skeleton_of_weil_det_data_both` instead of the p∤s variant.
- **Hypotheses**: Same as `hasse_bound_via_weil_pairing` but `hres` only required for `p∤r ∧ p∤s`.
- **Uses from project**: `hasse_bound_of_full_qf_nonneg_witnesses` (Hasse/QuadraticForm.lean), `isogOneSub_negFrobenius` (AdditionPullback/Frobenius.lean), `isogOneSub_negFrobenius_toAddMonoidHom` (AdditionPullback/Frobenius.lean), `ker_deg_skeleton` (GapSpines.lean), `qf_nonneg_skeleton_of_weil_det_data_both` (this file), `pointCount` (Frobenius.lean).
- **Used by**: `FrobMatrixData.lean` (external; specifically at line 389 of that file).
- **Visibility**: public
- **Lines**: 154–168 (term-mode proof: lines 165–168, 4 lines total)
- **Notes**: No sorry, no maxHeartbeats. This is the capstone form used in the axiom-clean unconditional Hasse bound.

---

## Summary statistics

| Metric | Value |
|--------|-------|
| Total declarations | 4 |
| Theorems/lemmas | 4 |
| Defs | 0 |
| Instances | 0 |
| Sorries | 0 |
| `set_option maxHeartbeats` | 0 |
| Long proofs (>30 lines) | 0 |

## Key API (used by 3+ declarations in file)

- `isogTrace`: appears in all 4 theorem signatures
- `frobeniusIsog`: appears in all 4 theorem signatures
- `isogOneSub_negFrobenius`: appears in all 4 theorem signatures
- `hasse_bound_of_full_qf_nonneg_witnesses`: used by both `hasse_bound_via_weil_pairing` and `hasse_bound_via_weil_pairing_both`
- `ker_deg_skeleton`: used by both `hasse_bound_via_weil_pairing` and `hasse_bound_via_weil_pairing_both`
- `isogOneSub_negFrobenius_toAddMonoidHom`: used by both `hasse_bound_via_weil_pairing` and `hasse_bound_via_weil_pairing_both`

## Unused declarations (dead-code candidates within this file)

All four declarations are used by external files (`FrobMatrixData.lean`): none are dead code within the project.

## Notable observations

- Pure assembly glue file: all proofs are short (≤11 lines), no sorry, no maxHeartbeats. The file is entirely a reduction layer between the Weil-pairing DET-DEG machinery and the shipped arithmetic skeleton.
- The two `_both` variants (coprime-BOTH locus) exist to bypass the inseparable `p∣r` pencil sorry; this is the "reviewer round-23, Route B" design documented in the module docstring.
- `FiniteField.card'` is the key Mathlib lemma that extracts `p`, `CharP K p`, and `Fact p.Prime` from `[Field K] [Fintype K]`, used identically in both tactic proofs.
