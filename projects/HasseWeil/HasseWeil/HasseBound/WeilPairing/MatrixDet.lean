import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Route 2 — the 2×2 determinant identity (Silverman V.2.3.1, Step 6)

The linear-algebra bridge of the Weil-pairing route: for a `2×2` matrix `M` over a commutative
ring,

  `det(r • M − s • 1) = r² · det M − r·s · tr M + s²`.

With `M = ρ_ℓ(π)` the matrix of Frobenius on `E[ℓ]` (`det M ≡ q`, `tr M ≡ t (mod ℓ)`), this turns
`det(ρ_ℓ(rπ − s)) = det(r • M − s • 1)` into `q·r² − t·rs + s² (mod ℓ)` — which the finite-level
Weil pairing identifies with `deg(rπ − s) (mod ℓ)`.  Feeding that congruence (one per prime `ℓ ≠ p`)
into `int_eq_of_congr_all_primes_ne` (Step 7) closes Leaf 1.

This file is pure commutative-ring linear algebra — no elliptic-curve content.
-/

namespace HasseWeil.WeilPairing

open Matrix

/-- **The 2×2 determinant identity** `det(r·M − s·1) = r²·det M − r·s·tr M + s²`.

The characteristic-polynomial value of `M` at the "point" `(r,s)`, written without forming the
characteristic polynomial: a direct `det_fin_two` computation. -/
theorem det_smul_sub_smul_one_fin_two {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (r s : R) :
    (r • M - s • (1 : Matrix (Fin 2) (Fin 2) R)).det
      = r ^ 2 * M.det - r * s * M.trace + s ^ 2 := by
  have hlit : r • M - s • (1 : Matrix (Fin 2) (Fin 2) R)
      = !![r * M 0 0 - s, r * M 0 1; r * M 1 0, r * M 1 1 - s] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, Matrix.sub_apply]
  rw [hlit, Matrix.det_fin_two_of, Matrix.det_fin_two M, Matrix.trace_fin_two M]
  ring

/-- **Specialised to the Frobenius matrix data** `det M = q`, `tr M = t`:
`det(r·M − s·1) = q·r² − t·r·s + s²`.  This is the exact value the finite-level pairing must match
with `deg(rπ − s)` modulo `ℓ`. -/
theorem det_smul_sub_smul_one_fin_two_of {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (r s q t : R)
    (hdet : M.det = q) (htr : M.trace = t) :
    (r • M - s • (1 : Matrix (Fin 2) (Fin 2) R)).det = q * r ^ 2 - t * r * s + s ^ 2 := by
  rw [det_smul_sub_smul_one_fin_two, hdet, htr]; ring

/-- **Trace from `det(1 − M)`** (2×2): `(1 − M).det = 1 − tr M + det M`. The assembly reads the
Frobenius trace off `det(1 − π|E[ℓ]) = deg(1 − π) = #E`, giving `tr(π|E[ℓ]) = 1 + q − #E = t`. -/
theorem det_one_sub_fin_two {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    (1 - M).det = 1 - M.trace + M.det := by
  have hlit : (1 : Matrix (Fin 2) (Fin 2) R) - M
      = !![1 - M 0 0, -M 0 1; -M 1 0, 1 - M 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply]
  rw [hlit, Matrix.det_fin_two_of, Matrix.det_fin_two M, Matrix.trace_fin_two M]
  ring

end HasseWeil.WeilPairing
