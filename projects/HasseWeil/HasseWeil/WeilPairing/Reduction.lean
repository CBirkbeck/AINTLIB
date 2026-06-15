import HasseWeil.WeilPairing.IntegerSeparation
import HasseWeil.WeilPairing.MatrixDet
import Mathlib.Tactic.LinearCombination

/-!
# Route 2 — the reduction of Leaf 1 to the finite-level Weil-pairing residual (Silverman V.2.3.1)

This file fuses Step 6 (the 2×2 determinant identity) and Step 7 (integer separation) into the
**Route-2 reduction skeleton**: the signed degree identity

  `deg(rπ − s) = q·r² − t·rs + s²`

follows from a single, textbook-buildable **residual** — that for every auxiliary prime `ℓ ≠ p` the
action of Frobenius on `E[ℓ]` is represented by a `2×2` matrix `M` over `ZMod ℓ` whose determinant
and trace reduce to `q` and `t`, and for which the action of `rπ − s` (= `r·M − s·1`) has
determinant equal to `deg(rπ − s)` modulo `ℓ`:

  **residual `ℓ`** : `∃ M, det M = q ∧ tr M = t ∧ det(r·M − s·1) = deg(rπ − s)`   (in `ZMod ℓ`).

The first two conjuncts are the Frobenius matrix data (`det = deg`, `tr` from `deg(1−π)=#E`); the
third is the finite-level Weil-pairing **determinant–degree** identity `det(ψ|E[ℓ]) ≡ deg ψ` applied
to `ψ = rπ − s` (using that `ψ ↦ ψ|E[ℓ]` is a ring map, so `(rπ−s)|E[ℓ] = r·M − s·1`).

Everything in this file is characteristic-free arithmetic and `2×2` linear algebra; the **only**
remaining mathematical content of Route 2 is the construction of the finite-level Weil pairing that
supplies the residual.  This is the Route-2 analogue of the old `DualAddMulByIntResidual` reduction,
but the residual here is Silverman's actual finite-field ingredient (III.8.6 / V.2.3.1), **not** the
characteristic-`p` dual additivity that has no elementary proof in the text.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, V.2.3.1, III.8.6.
-/

namespace HasseWeil.WeilPairing

open Matrix

/-- **Route-2 reduction (Silverman V.2.3.1): the signed degree identity from the finite-level
Weil-pairing residual.**

Let `q, t` be the Frobenius data (`q = #𝔽_q`, `t` = trace of Frobenius) and `Dν` an integer
(intended: `Dν = deg(rπ − s)`).  If for **every** prime `ℓ ≠ p` there is a `2×2` matrix `M` over
`ZMod ℓ` (the matrix of Frobenius on `E[ℓ]`) with

  `det M = q`,  `tr M = t`,  and  `det(r·M − s·1) = Dν`   (all in `ZMod ℓ`),

then `Dν = q·r² − t·rs + s²` as integers.

Proof: by the 2×2 identity (`det_smul_sub_smul_one_fin_two_of`), `det(r·M − s·1) = q·r² − t·rs + s²`
in `ZMod ℓ`, so the hypothesis gives `Dν ≡ q·r² − t·rs + s² (mod ℓ)` for every prime `ℓ ≠ p`;
integer separation (`int_eq_of_congr_all_primes_ne`) lifts this to an equality of integers. -/
theorem deg_eq_of_frobMatrix_data {p : ℕ} {q t Dν r s : ℤ}
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
        M.det = (q : ZMod ℓ) ∧ M.trace = (t : ZMod ℓ) ∧
        ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (Dν : ZMod ℓ)) :
    Dν = q * r ^ 2 - t * r * s + s ^ 2 := by
  apply int_eq_of_congr_all_primes_ne (p := p)
  intro ℓ hℓ hℓne
  obtain ⟨M, hdet, htr, hψ⟩ := h ℓ hℓ hℓne
  rw [← hψ,
    det_smul_sub_smul_one_fin_two_of M (r : ZMod ℓ) (s : ZMod ℓ) (q : ZMod ℓ) (t : ZMod ℓ) hdet htr]
  push_cast
  ring

/-- **Non-negativity corollary (Leaf 1).** If additionally `Dν` is a degree (a non-negative
integer, e.g. `Dν = deg(rπ − s)`), the residual yields `0 ≤ q·r² − t·rs + s²` — exactly the Hasse
quadratic-form non-negativity. -/
theorem qf_nonneg_of_frobMatrix_data {p : ℕ} {q t Dν r s : ℤ} (hDν : 0 ≤ Dν)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
        M.det = (q : ZMod ℓ) ∧ M.trace = (t : ZMod ℓ) ∧
        ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (Dν : ZMod ℓ)) :
    0 ≤ q * r ^ 2 - t * r * s + s ^ 2 :=
  (deg_eq_of_frobMatrix_data h) ▸ hDν

/-! ### Det-only residual interface (what the Weil pairing supplies directly)

`PairingDet.det_eq_of_symplectic_adjoint` produces **`det` values** (`det(ψ|E[ℓ]) = deg ψ`), not the
trace.  We package the residual purely in terms of `det M = q`, `det(1 − M) = #E = q+1−t`, and
`det(rM − sI) = Dν` — reading the trace off `det(1 − M)` internally via `det_one_sub_fin_two`. -/

/-- **Per-`ℓ` congruence from the det-only Frobenius data.** If `M` (the matrix of Frobenius on
`E[ℓ]`) has `det M = q`, `det(1 − M) = q+1−t` (`= #E`), and `det(rM − sI) = Dν`, then
`Dν ≡ qr² − trs + s² (mod ℓ)`. -/
theorem frob_det_congruence {ℓ : ℕ} {M : Matrix (Fin 2) (Fin 2) (ZMod ℓ)} {q t Dν r s : ℤ}
    (hdetM : M.det = (q : ZMod ℓ))
    (hdet1M : (1 - M).det = ((q + 1 - t : ℤ) : ZMod ℓ))
    (hdetrMs : ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (Dν : ZMod ℓ)) :
    (Dν : ZMod ℓ) = ((q * r ^ 2 - t * r * s + s ^ 2 : ℤ) : ZMod ℓ) := by
  have htr : M.trace = (t : ZMod ℓ) := by
    have hone := det_one_sub_fin_two M
    rw [hdet1M, hdetM] at hone
    push_cast at hone
    linear_combination hone
  rw [← hdetrMs, det_smul_sub_smul_one_fin_two_of M (r : ZMod ℓ) (s : ZMod ℓ)
    (q : ZMod ℓ) (t : ZMod ℓ) hdetM htr]
  push_cast; ring

/-- **Route-2A det-only reduction → `deg(rπ − s) = N`.** From the per-`ℓ` det-only Frobenius data
(for every prime `ℓ ≠ p`), the signed degree identity `deg(rπ − s) = q·r² − t·rs + s²` follows. This
is the interface the finite-level Weil pairing discharges via `PairingDet`. -/
theorem deg_eq_of_frob_det_data {p : ℕ} {q t Dν r s : ℤ}
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
        M.det = (q : ZMod ℓ) ∧ (1 - M).det = ((q + 1 - t : ℤ) : ZMod ℓ) ∧
        ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (Dν : ZMod ℓ)) :
    Dν = q * r ^ 2 - t * r * s + s ^ 2 := by
  apply int_eq_of_congr_all_primes_ne (p := p)
  intro ℓ hℓ hℓne
  obtain ⟨M, h1, h2, h3⟩ := h ℓ hℓ hℓne
  exact frob_det_congruence h1 h2 h3

end HasseWeil.WeilPairing
