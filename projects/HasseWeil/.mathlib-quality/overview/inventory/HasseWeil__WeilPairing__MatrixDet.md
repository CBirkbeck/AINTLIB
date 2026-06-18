# Inventory: ./HasseWeil/WeilPairing/MatrixDet.lean

**File summary:** Pure commutative-ring linear algebra (no elliptic-curve content). Provides the 2×2 determinant identity `det(r·M − s·1) = r²·det M − r·s·tr M + s²` and two specialisations used by `Reduction.lean` to connect the Frobenius matrix data to the pencil degree formula (Silverman V.2.3.1, Step 6).

**Total declarations:** 3 theorems, 0 defs, 0 instances. No `sorry`, no `set_option maxHeartbeats`.

---

### `theorem det_smul_sub_smul_one_fin_two`

- **Type**: `{R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (r s : R) : (r • M - s • (1 : Matrix (Fin 2) (Fin 2) R)).det = r ^ 2 * M.det - r * s * M.trace + s ^ 2`
- **What**: The core 2×2 determinant identity: `det(r·M − s·1) = r²·det M − r·s·tr M + s²` for any 2×2 matrix over a commutative ring. This is the characteristic-polynomial evaluation `χ_M(r, s)` without forming the char poly.
- **How**: Rewrites the matrix explicitly as a literal `!![…; …]` via `ext`/`fin_cases`, then applies `Matrix.det_fin_two_of`, `Matrix.det_fin_two`, and `Matrix.trace_fin_two`, finishing with `ring`.
- **Hypotheses**: `R` a commutative ring, `M` a 2×2 matrix over `R`, `r s : R`.
- **Uses from project**: none.
- **Used by**: `det_smul_sub_smul_one_fin_two_of` (this file), `Reduction.lean` (via the `_of` specialisation).
- **Visibility**: public
- **Lines**: 28–38 (proof ~7 lines)
- **Notes**: none.

---

### `theorem det_smul_sub_smul_one_fin_two_of`

- **Type**: `{R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (r s q t : R) (hdet : M.det = q) (htr : M.trace = t) : (r • M - s • (1 : Matrix (Fin 2) (Fin 2) R)).det = q * r ^ 2 - t * r * s + s ^ 2`
- **What**: Specialisation of `det_smul_sub_smul_one_fin_two` with given values `q = det M` and `t = tr M`; rewrites the result to `q·r² − t·r·s + s²`. This is the exact form consumed by the Frobenius matrix-data assembly when `q = #𝔽_q` and `t` is the Frobenius trace.
- **How**: Directly `rw [det_smul_sub_smul_one_fin_two, hdet, htr]; ring`.
- **Hypotheses**: Same as above plus `hdet : M.det = q` and `htr : M.trace = t`.
- **Uses from project**: `det_smul_sub_smul_one_fin_two` (this file).
- **Used by**: `Reduction.lean` (called at lines 61 and 95 of that file).
- **Visibility**: public
- **Lines**: 43–47 (proof 2 lines)
- **Notes**: none.

---

### `theorem det_one_sub_fin_two`

- **Type**: `{R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) : (1 - M).det = 1 - M.trace + M.det`
- **What**: For a 2×2 matrix `M` over a commutative ring, `det(1 − M) = 1 − tr M + det M`. Used in the Hasse-bound assembly to read the Frobenius trace from `det(1 − π|E[ℓ]) = deg(1 − π) = #E`, giving `tr(π|E[ℓ]) = 1 + q − #E`.
- **How**: Same strategy as `det_smul_sub_smul_one_fin_two`: rewrite `1 − M` as a literal `!![…; …]` via `ext`/`fin_cases`/`simp`, then `Matrix.det_fin_two_of`, `Matrix.det_fin_two`, `Matrix.trace_fin_two`, close with `ring`.
- **Hypotheses**: `R` a commutative ring, `M` a 2×2 matrix over `R`.
- **Uses from project**: none.
- **Used by**: `Reduction.lean` (line 91: `have hone := det_one_sub_fin_two M`).
- **Visibility**: public
- **Lines**: 51–58 (proof ~7 lines)
- **Notes**: none.
