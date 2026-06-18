# Inventory: ./HasseWeil/WeilPairing/Assembly.lean

**File**: `HasseWeil/WeilPairing/Assembly.lean`
**Lines**: 99
**Imports**: `HasseWeil.WeilPairing.Reduction`, `HasseWeil.WeilPairing.Discriminant`, `HasseWeil.WeilPairing.PairingDet`
**Namespace**: `HasseWeil.WeilPairing`
**Open**: `Matrix`

This is the Route-2A capstone file. It contains exactly three theorems, all public, with no sorry, no set_option maxHeartbeats, no instances, no defs. All three are short composition proofs routing through `Discriminant` and `Reduction`/`PairingDet`.

---

## Declarations

---

### `theorem qf_nonneg_of_frob_det_residual`

- **Type**:
  ```
  {p : ℕ} (hp : p.Prime) {q t : ℤ} (hq : 0 < q)
  (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
  (hres : ∀ r s : ℤ, ¬ (p : ℤ) ∣ s → ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
    ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
      M.det = (q : ZMod ℓ) ∧ (1 - M).det = ((q + 1 - t : ℤ) : ZMod ℓ) ∧
      ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (deg r s : ZMod ℓ)) →
  ∀ r s : ℤ, 0 ≤ q * r ^ 2 - t * r * s + s ^ 2
  ```
- **What**: Given a non-negative degree function `deg` and Frobenius matrix data (a 2×2 matrix `M` over `ZMod ℓ` with the three required determinants) for every separable pair `(r, s)` with `p ∤ s` and every auxiliary prime `ℓ ≠ p`, proves that the Hasse quadratic form `q·r² − t·rs + s²` is non-negative for all `(r, s)`.
- **How**: Applies `qf_nonneg_of_nonneg_on_coprime` (from `Discriminant.lean`) to reduce to the `{p ∤ s}` locus, then uses `deg_eq_of_frob_det_data` (from `Reduction.lean`) to identify `deg r s = q·r² − t·rs + s²`, concluding via `hdeg_nonneg`.
- **Hypotheses**: `p` prime; `0 < q`; `deg` non-negative; for all `(r, s)` with `p ∤ s`, for all primes `ℓ ≠ p`, a 2×2 matrix `M` over `ZMod ℓ` with `det M = q`, `det(1−M) = q+1−t`, `det(rM−sI) = deg r s` in `ZMod ℓ`.
- **Uses from project**: `qf_nonneg_of_nonneg_on_coprime` (Discriminant.lean), `deg_eq_of_frob_det_data` (Reduction.lean)
- **Used by**: `qf_nonneg_of_pairing_scaling` (within this file)
- **Visibility**: public
- **Lines**: 35–46 (proof: 5 lines)
- **Notes**: No sorry, no maxHeartbeats.

---

### `theorem qf_nonneg_of_frob_det_residual_both`

- **Type**:
  ```
  {p : ℕ} (hp : p.Prime) {q t : ℤ} (hq : 0 < q)
  (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
  (hres : ∀ r s : ℤ, ¬ (p : ℤ) ∣ r → ¬ (p : ℤ) ∣ s → ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
    ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
      M.det = (q : ZMod ℓ) ∧ (1 - M).det = ((q + 1 - t : ℤ) : ZMod ℓ) ∧
      ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (deg r s : ZMod ℓ)) →
  ∀ r s : ℤ, 0 ≤ q * r ^ 2 - t * r * s + s ^ 2
  ```
- **What**: Variant of `qf_nonneg_of_frob_det_residual` where the per-`ℓ` Frobenius matrix data is only required on the smaller locus `{p ∤ r ∧ p ∤ s}` (both coordinates coprime to `p`), which is precisely the locus where the Weil-pairing pencil scaling is available without inseparable-`p ∣ r` geometric input. The discriminant lift used is `qf_nonneg_of_nonneg_on_coprime_both` (reviewer round-23 Route B).
- **How**: Applies `qf_nonneg_of_nonneg_on_coprime_both` (from `Discriminant.lean`) then `deg_eq_of_frob_det_data` (from `Reduction.lean`) identically to the `{p ∤ s}` version. Proof structure is verbatim parallel to `qf_nonneg_of_frob_det_residual`.
- **Hypotheses**: Same as `qf_nonneg_of_frob_det_residual` but the matrix-data hypothesis additionally requires `p ∤ r`.
- **Uses from project**: `qf_nonneg_of_nonneg_on_coprime_both` (Discriminant.lean), `deg_eq_of_frob_det_data` (Reduction.lean)
- **Used by**: unused in file (leaf export, intended for downstream callers outside this file)
- **Visibility**: public
- **Lines**: 56–67 (proof: 5 lines)
- **Notes**: No sorry, no maxHeartbeats. Route B (reviewer round-23) variant; its only current external reference in the project is a comment in `PencilDualDivisor.lean:63`.

---

### `theorem qf_nonneg_of_pairing_scaling`

- **Type**:
  ```
  {p : ℕ} (hp : p.Prime) {q t : ℤ} (hq : 0 < q)
  (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
  (hscale : ∀ r s : ℤ, ¬ (p : ℤ) ∣ s → ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
    ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
      Mᵀ * symJ (ZMod ℓ) * M = (q : ZMod ℓ) • symJ (ZMod ℓ) ∧
      (1 - M)ᵀ * symJ (ZMod ℓ) * (1 - M) = ((q + 1 - t : ℤ) : ZMod ℓ) • symJ (ZMod ℓ) ∧
      ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1)ᵀ * symJ (ZMod ℓ)
          * ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1)
        = (deg r s : ZMod ℓ) • symJ (ZMod ℓ)) →
  ∀ r s : ℤ, 0 ≤ q * r ^ 2 - t * r * s + s ^ 2
  ```
- **What**: The cleanest top-level reduction: takes per-isogeny Weil-pairing *scaling* data (symplectic conjugacy `φᵀ J φ = (deg φ)·J` for `φ ∈ {M, 1−M, rM−sI}`) rather than raw determinant equalities, and derives Hasse non-negativity. This is the direct output form of the Weil-pairing identity `e(φS, φT) = e(S, T)^{deg φ}`.
- **How**: Applies `qf_nonneg_of_frob_det_residual` and in the inner step uses `frob_det_data_of_scaling` (from `PairingDet.lean`) to convert the three symplectic scaling identities into the three determinant equalities that `qf_nonneg_of_frob_det_residual` expects.
- **Hypotheses**: Same signature parameters as the other two theorems, but the matrix data takes the form `φᵀ * symJ * φ = (deg φ) • symJ` for the three isogenies, with `symJ` being the standard 2×2 symplectic matrix `!![0, 1; -1, 0]`.
- **Uses from project**: `qf_nonneg_of_frob_det_residual` (this file), `frob_det_data_of_scaling` (PairingDet.lean), `symJ` (PairingDet.lean)
- **Used by**: unused in file (leaf export)
- **Visibility**: public
- **Lines**: 69–97 (proof: 7 lines, inside `open Matrix in` block)
- **Notes**: No sorry, no maxHeartbeats. Uses a local `open Matrix in` scope. This is the intended top-level interface for callers supplying Weil-pairing scaling witnesses.

---

## Summary Statistics

| | Count |
|---|---|
| Total declarations | 3 |
| Theorems (lemmas) | 3 |
| Defs | 0 |
| Instances | 0 |
| Sorries | 0 |
| set_option maxHeartbeats | 0 |

## Key API

- `deg_eq_of_frob_det_data` (from Reduction.lean): used by both `qf_nonneg_of_frob_det_residual` and `qf_nonneg_of_frob_det_residual_both`
- `qf_nonneg_of_frob_det_residual` (this file): used by `qf_nonneg_of_pairing_scaling`

## Long Proofs (>30 lines)

None.

## Unused Declarations (within file)

- `qf_nonneg_of_frob_det_residual_both` — not called by anything else in this file (only referenced in a comment in PencilDualDivisor.lean outside this file)
- `qf_nonneg_of_pairing_scaling` — not called by anything else in this file

## Notes

This is a pure composition/assembly file: all three theorems are short (≤7 tactic lines) glue proofs connecting `Discriminant.lean` (discriminant lemma) with `Reduction.lean`/`PairingDet.lean` (det-from-scaling). The file is entirely sorry-free and axiom-clean (no sorryAx). The two "unused in file" theorems are the intended external API exports for the Route-2A program.
