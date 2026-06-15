import HasseWeil.WeilPairing.Reduction
import HasseWeil.WeilPairing.Discriminant
import HasseWeil.WeilPairing.PairingDet

/-!
# Route 2A — the capstone reduction (Silverman V.2.3.1 + V.1.1)

`qf_nonneg` (the Hasse quadratic-form non-negativity) follows from a **single residual**: the
finite-level Weil-pairing det data for Frobenius, supplied only on the **separable** locus `p ∤ s`.

This composes the two shipped halves:
* `deg_eq_of_frob_det_data` — per `(r,s)` with `p∤s`, the per-`ℓ` det data ⟹
  `deg(rπ−s) = qr²−trs+s²`, hence `0 ≤ qr²−trs+s²` (a degree is `≥ 0`);
* `qf_nonneg_of_nonneg_on_coprime` (the discriminant lemma) — `≥ 0` on `{p∤s}` ⟹ `t²≤4q`
  ⟹ `≥ 0` everywhere.

The **entire** remaining mathematical work of Route 2A is now exactly the hypothesis `hres`:
that the finite-level Weil pairing on `E[ℓ] ≅ 𝔽_ℓ²` supplies, for each `ℓ ≠ p` and each
separable `rπ − s` (`p∤s`), a Frobenius matrix `M` with `det M = q`, `det(1−M) = #E = q+1−t`,
and `det(rM−sI) = deg(rπ−s)` — each a `det = deg` instance discharged by
`PairingDet.det_eq_of_symplectic_adjoint` once the pairing, its symplectic adjoint, and
`φ̂φ = [deg]` are in hand.
-/

namespace HasseWeil.WeilPairing

open Matrix

/-- **Route-2A capstone: `qf_nonneg` from the separable Weil-pairing det-residual.**

Given `0 < q`, a prime `p`, a degree function `deg` (with `deg r s = deg(rπ − s) ≥ 0`), and the
per-`ℓ` Frobenius **det data** for every separable `rπ − s` (`p ∤ s`) — namely a matrix `M`
over `ZMod ℓ` with `det M = q`, `det(1−M) = q+1−t`, and `det(rM − sI) = deg r s` — the Hasse
quadratic form `q·r² − t·rs + s²` is non-negative for **all** `(r,s)`. -/
theorem qf_nonneg_of_frob_det_residual {p : ℕ} (hp : p.Prime) {q t : ℤ} (hq : 0 < q)
    (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hres : ∀ r s : ℤ, ¬ (p : ℤ) ∣ s → ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
        M.det = (q : ZMod ℓ) ∧ (1 - M).det = ((q + 1 - t : ℤ) : ZMod ℓ) ∧
        ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (deg r s : ZMod ℓ)) :
    ∀ r s : ℤ, 0 ≤ q * r ^ 2 - t * r * s + s ^ 2 := by
  apply qf_nonneg_of_nonneg_on_coprime hq hp
  intro r s hps
  have hd : deg r s = q * r ^ 2 - t * r * s + s ^ 2 :=
    deg_eq_of_frob_det_data (fun ℓ hℓ hℓne => hres r s hps ℓ hℓ hℓne)
  rw [← hd]; exact hdeg_nonneg r s

/-- **Route-2A capstone (coprime-BOTH): `qf_nonneg` from the Weil-pairing det-residual on `p ∤ r ∧ p ∤ s`.**

Identical to `qf_nonneg_of_frob_det_residual` but requesting the per-`ℓ` Frobenius det data only on
the **smaller** locus `{p ∤ r ∧ p ∤ s}` (both coordinates coprime to `p`) — exactly where the
Weil-pairing pencil scaling is available without the inseparable `p ∣ r` geometric input.  The
discriminant lift is the stronger `qf_nonneg_of_nonneg_on_coprime_both` (reviewer round-23, Route B);
its proof is identical to the `{p ∤ s}` version (`deg_eq_of_frob_det_data` per `(r,s)` with
`p ∤ r ∧ p ∤ s`). -/
theorem qf_nonneg_of_frob_det_residual_both {p : ℕ} (hp : p.Prime) {q t : ℤ} (hq : 0 < q)
    (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hres : ∀ r s : ℤ, ¬ (p : ℤ) ∣ r → ¬ (p : ℤ) ∣ s → ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
        M.det = (q : ZMod ℓ) ∧ (1 - M).det = ((q + 1 - t : ℤ) : ZMod ℓ) ∧
        ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (deg r s : ZMod ℓ)) :
    ∀ r s : ℤ, 0 ≤ q * r ^ 2 - t * r * s + s ^ 2 := by
  apply qf_nonneg_of_nonneg_on_coprime_both hq hp
  intro r s hpr hps
  have hd : deg r s = q * r ^ 2 - t * r * s + s ^ 2 :=
    deg_eq_of_frob_det_data (fun ℓ hℓ hℓne => hres r s hpr hps ℓ hℓ hℓne)
  rw [← hd]; exact hdeg_nonneg r s

open Matrix in
/-- **Route-2A top-level reduction: `qf_nonneg` from the per-isogeny Weil-pairing scaling data.**

The cleanest, additivity-free form of the capstone. Given `0 < q`, a prime `p`, a non-negative
degree function `deg` (`deg r s = deg(rπ − s)`), and — for every separable `rπ − s` (`p ∤ s`) and
every auxiliary prime `ℓ ≠ p` — a Frobenius matrix `M` over `ZMod ℓ` satisfying the **per-isogeny
Weil-pairing scaling identities** `φᵀ J φ = (deg φ) • J` for `φ ∈ {π, 1−π, rπ−s}` (with `J = symJ`,
`deg π = q`, `deg(1−π) = q+1−t = #E`, `deg(rπ−s) = deg r s`), the Hasse quadratic form
`q·r² − t·rs + s²` is non-negative for **all** `(r,s)`.

This isolates the entire remaining mathematical work as the scaling identities — the direct output
of the finite-level Weil pairing (`e(φS,φT) = e(S,T)^{deg φ}`), which holds per isogeny and needs no
dual-additivity. The `det = deg` step is discharged internally by `frob_det_data_of_scaling`. -/
theorem qf_nonneg_of_pairing_scaling {p : ℕ} (hp : p.Prime) {q t : ℤ} (hq : 0 < q)
    (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hscale : ∀ r s : ℤ, ¬ (p : ℤ) ∣ s → ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
        Mᵀ * symJ (ZMod ℓ) * M = (q : ZMod ℓ) • symJ (ZMod ℓ) ∧
        (1 - M)ᵀ * symJ (ZMod ℓ) * (1 - M)
          = ((q + 1 - t : ℤ) : ZMod ℓ) • symJ (ZMod ℓ) ∧
        ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1)ᵀ * symJ (ZMod ℓ)
            * ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1)
          = (deg r s : ZMod ℓ) • symJ (ZMod ℓ)) :
    ∀ r s : ℤ, 0 ≤ q * r ^ 2 - t * r * s + s ^ 2 := by
  apply qf_nonneg_of_frob_det_residual hp hq deg hdeg_nonneg
  intro r s hps ℓ hℓ hℓne
  obtain ⟨M, hπ, h1, hrs⟩ := hscale r s hps ℓ hℓ hℓne
  exact ⟨M, frob_det_data_of_scaling hπ h1 hrs⟩

end HasseWeil.WeilPairing
