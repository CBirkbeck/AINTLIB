# Inventory: ./HasseWeil/WeilPairing/Reduction.lean

**File purpose**: The **Route-2 reduction skeleton** (Silverman V.2.3.1): reduces Leaf 1 (the signed degree identity `deg(rπ − s) = q·r² − t·rs + s²`) to a single per-prime finite-level residual — for every prime `ℓ ≠ p` there is a `2×2` matrix `M` over `ZMod ℓ` (the matrix of Frobenius on `E[ℓ]`) whose determinant/trace reduce to `q`/`t` and for which `det(r·M − s·1) = deg(rπ − s) (mod ℓ)`. Everything here is characteristic-free `2×2` linear algebra + integer separation; the actual finite-level Weil pairing supplies the residual elsewhere. Two interfaces are provided: a trace-based one (`*_frobMatrix_data`) and a determinant-only one (`*_frob_det_data`), the latter being what the Weil pairing discharges directly.

**Imports**: `HasseWeil.WeilPairing.IntegerSeparation`, `HasseWeil.WeilPairing.MatrixDet`, `Mathlib.Tactic.LinearCombination`

**Total declarations**: 4 `theorem`

**Module options**: none. No `sorry`, no `maxHeartbeats`.

**Standing context**: `namespace HasseWeil.WeilPairing`, `open Matrix`. No file-level `variable`; each theorem is self-contained over `{p q t Dν r s : ℤ}` and `ZMod ℓ`.

---

## Declarations

### `theorem deg_eq_of_frobMatrix_data`
- **Type**: `{p : ℕ} {q t Dν r s : ℤ} (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ), M.det = (q : ZMod ℓ) ∧ M.trace = (t : ZMod ℓ) ∧ ((r : ZMod ℓ) • M − (s : ZMod ℓ) • 1).det = (Dν : ZMod ℓ)) : Dν = q * r ^ 2 - t * r * s + s ^ 2`
- **What**: **Route-2 reduction (trace form)**: from the per-`ℓ` Frobenius matrix data (`det M = q`, `tr M = t`, `det(rM − s1) = Dν` in `ZMod ℓ`, for every prime `ℓ ≠ p`), the integer identity `Dν = q·r² − t·rs + s²` follows.
- **How**: For each prime `ℓ ≠ p`, the `2×2` identity `det_smul_sub_smul_one_fin_two_of` turns the hypotheses into `Dν ≡ q·r² − t·rs + s² (mod ℓ)` (`push_cast`/`ring`); `int_eq_of_congr_all_primes_ne` lifts congruence-mod-every-prime-`≠p` to integer equality.
- **Hypotheses**: the universally-quantified per-`ℓ` matrix data.
- **Uses from project**: `int_eq_of_congr_all_primes_ne` (IntegerSeparation), `det_smul_sub_smul_one_fin_two_of` (MatrixDet)
- **Used by (within file)**: `qf_nonneg_of_frobMatrix_data`
- **Visibility**: public
- **Lines**: 51–63, proof length: ~6 lines
- **Notes**: **No external consumers** — see summary (b). Superseded by the det-only interface below.

### `theorem qf_nonneg_of_frobMatrix_data`
- **Type**: `{p : ℕ} {q t Dν r s : ℤ} (hDν : 0 ≤ Dν) (h : … same matrix data as above …) : 0 ≤ q * r ^ 2 - t * r * s + s ^ 2`
- **What**: **Non-negativity corollary (Leaf 1, trace form)**: if `Dν` is additionally a non-negative integer (e.g. a degree), the residual yields `0 ≤ q·r² − t·rs + s²` — the Hasse quadratic-form non-negativity.
- **How**: Rewrites `0 ≤ Dν` along the equality `Dν = q·r² − t·rs + s²` from `deg_eq_of_frobMatrix_data` (term-mode `▸`).
- **Hypotheses**: `0 ≤ Dν` plus the per-`ℓ` matrix data.
- **Uses from project**: `deg_eq_of_frobMatrix_data` (this file)
- **Used by (within file)**: none. **Used by (project)**: none.
- **Visibility**: public
- **Lines**: 68–74, proof length: 1 line (term)
- **Notes**: **Dead candidate.** No consumer anywhere; the live Hasse-bound path uses the det-only `deg_eq_of_frob_det_data` instead (and reads non-negativity from the actual degree downstream).

### `theorem frob_det_congruence`
- **Type**: `{ℓ : ℕ} {M : Matrix (Fin 2) (Fin 2) (ZMod ℓ)} {q t Dν r s : ℤ} (hdetM : M.det = (q : ZMod ℓ)) (hdet1M : (1 − M).det = ((q + 1 − t : ℤ) : ZMod ℓ)) (hdetrMs : ((r : ZMod ℓ) • M − (s : ZMod ℓ) • 1).det = (Dν : ZMod ℓ)) : (Dν : ZMod ℓ) = ((q * r ^ 2 - t * r * s + s ^ 2 : ℤ) : ZMod ℓ)`
- **What**: **Per-`ℓ` congruence from the det-only Frobenius data**: from `det M = q`, `det(1 − M) = q+1−t` (`= #E`), and `det(rM − sI) = Dν`, derive `Dν ≡ q·r² − t·rs + s² (mod ℓ)`. (Recovers the trace internally from `det(1 − M)`.)
- **How**: Reads the trace off `det(1 − M)` via `det_one_sub_fin_two` (`det(1−M) = 1 − tr M + det M`) and `linear_combination`, giving `tr M = t`; then `det_smul_sub_smul_one_fin_two_of` + `push_cast`/`ring`.
- **Hypotheses**: the three det conditions for a fixed `ℓ`.
- **Uses from project**: `det_one_sub_fin_two`, `det_smul_sub_smul_one_fin_two_of` (MatrixDet)
- **Used by (within file)**: `deg_eq_of_frob_det_data`. **Used by (project)**: `PairingDet`.
- **Visibility**: public
- **Lines**: 85–97, proof length: ~9 lines

### `theorem deg_eq_of_frob_det_data`
- **Type**: `{p : ℕ} {q t Dν r s : ℤ} (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ), M.det = (q : ZMod ℓ) ∧ (1 − M).det = ((q + 1 − t : ℤ) : ZMod ℓ) ∧ ((r : ZMod ℓ) • M − (s : ZMod ℓ) • 1).det = (Dν : ZMod ℓ)) : Dν = q * r ^ 2 - t * r * s + s ^ 2`
- **What**: **Route-2A det-only reduction → `deg(rπ − s) = N`**: from the per-`ℓ` *determinant-only* Frobenius data (for every prime `ℓ ≠ p`), the signed degree identity follows. This is the interface the finite-level Weil pairing discharges (via `PairingDet`), since the pairing produces `det` values, not the trace directly.
- **How**: For each prime `ℓ ≠ p`, `frob_det_congruence` gives `Dν ≡ q·r² − t·rs + s² (mod ℓ)`; `int_eq_of_congr_all_primes_ne` lifts to integer equality.
- **Hypotheses**: the universally-quantified per-`ℓ` det-only data.
- **Uses from project**: `int_eq_of_congr_all_primes_ne` (IntegerSeparation), `frob_det_congruence` (this file)
- **Used by (within file)**: none. **Used by (project)**: `PencilDualDivisor`, `Assembly`, `DetDeg` (the live Route-2A reduction interface).
- **Visibility**: public
- **Lines**: 102–111, proof length: ~6 lines

---

## Cross-reference summary

| Declaration | Used by (within file) | Used by (project) |
|---|---|---|
| `deg_eq_of_frobMatrix_data` | `qf_nonneg_of_frobMatrix_data` | — |
| `qf_nonneg_of_frobMatrix_data` | — | — |
| `frob_det_congruence` | `deg_eq_of_frob_det_data` | `PairingDet` |
| `deg_eq_of_frob_det_data` | — | `PencilDualDivisor`, `Assembly`, `DetDeg` |

**Key API** (live spine): `deg_eq_of_frob_det_data` (the Route-2A reduction used by Assembly/DetDeg/PencilDualDivisor) and its core `frob_det_congruence` (also used by PairingDet).

## Notes / cleanup analysis

- **(a/b) Dead / superseded sub-route**: the **trace-based pair** `deg_eq_of_frobMatrix_data` (L51) + `qf_nonneg_of_frobMatrix_data` (L68) has **no external consumers anywhere in the project** (verified by grep). They are the earlier "trace form" interface, superseded by the determinant-only `frob_det_congruence` / `deg_eq_of_frob_det_data` (the docstrings explicitly say the Weil pairing "produces det values, not the trace"). `qf_nonneg_of_frobMatrix_data` is fully dead (used by nothing); `deg_eq_of_frobMatrix_data` is used only to prove that dead corollary. **Both are strong removal candidates** — deleting them drops no live functionality.
- **(c) mathlib-fit**: the `2×2` determinant identities are imported from the project's own `MatrixDet` (`det_smul_sub_smul_one_fin_two_of`, `det_one_sub_fin_two`); those wrap mathlib's `Matrix.det_fin_two`. Appropriate factoring; nothing hand-rolled here that mathlib provides directly.
- **(d) Internal duplication**: `deg_eq_of_frobMatrix_data` and `deg_eq_of_frob_det_data` are near-identical reductions (both: per-`ℓ` data → `int_eq_of_congr_all_primes_ne`), differing only in trace-vs-det input. Removing the trace pair eliminates this redundancy.
- **(e) Generalisation**: the reductions are already characteristic-free and abstract in `(q,t,Dν,r,s)`; no over-specialisation.
- **No `sorry`, no `maxHeartbeats`, no proof >30 lines.**
