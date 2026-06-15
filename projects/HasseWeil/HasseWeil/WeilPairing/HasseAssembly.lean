/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.DetDeg
import HasseWeil.WeilPairing.Assembly
import HasseWeil.GapSpines
import HasseWeil.Hasse.QuadraticForm

set_option linter.style.longLine false

/-!
# Route 2A — the capstone assembly: Weil-pairing Frobenius data → the Hasse bound (V.2.3.1)

This file performs the **final connection** (ticket `T-R2-ASSEMBLE`): it feeds the per-`ℓ`
Frobenius-matrix determinant data produced by the Weil pairing (`HasseWeil/WeilPairing/DetDeg.lean`,
`det(ρ_ℓ φ) = deg φ`, Silverman III.8.6) into the **shipped** Hasse-bound reduction
(`HasseWeil/WeilPairing/{Reduction,Assembly}.lean`, `qf_nonneg_of_frob_det_residual`), closing the
top GAP-QF leaf (III.6.3 qf-nonneg) and hence the Hasse bound `|#E(F_q) − q − 1| ≤ 2√q`.

## What the assembly proves

Over a finite field `K` (`q = #K`, `t = isogTrace π (1−π) = 1 + q − #E`), the Hasse quadratic form
`q·r² − t·rs + s²` is non-negative for all `(r,s)`, **given** the per-`ℓ` Frobenius determinant data:
for every separable `rπ − s` (`p ∤ s`) and every auxiliary prime `ℓ ≠ p`, a `2×2` matrix `M` over
`ZMod ℓ` with

  `det M = q`,  `det(1 − M) = q + 1 − t (= #E)`,  `det(rM − sI) = deg(rπ − s)`.

This is exactly the data the Weil-pairing `DET-DEG` (`det_rhoEll_eq_degree`) supplies for the matrix
`M = ρ_ℓ(π)`: applying `det_rhoEll_eq_degree` at `π`, `1−π`, `rπ−s` (with the `ρ_ℓ` ring-map
identities `1 − ρ_ℓ(π) = ρ_ℓ(1−π)`, `r·ρ_ℓ(π) − s·1 = ρ_ℓ(rπ−s)`, both shipped in `DetDeg.lean`)
gives the three determinants as the geometric degrees `deg π = q`, `deg(1−π) = #E`, `deg(rπ−s)`,
each manifestly `≥ 0`.

## The single genuinely-new residual

The entire remaining mathematical content is `hres` — the existence, for the curve over `K̄`, of the
Frobenius matrix data for every `ℓ ≠ p`.  This is precisely the output of the bridge
`DetDeg.frob_det_data_of_weil_scaling` (which derives the three determinants from the per-isogeny
Weil-pairing scalings `e_ℓ(φS,φT) = e_ℓ(S,T)^{deg φ}`), applied to the base change of `E` to `K̄`.
The remaining gap is the base change itself (`E[ℓ]` over `K̄` for every `ℓ`, the Frobenius pencil's
scalings — the separable `1−π`, `rπ−s` via the proven `weilPairing_scaling`, and the inseparable `π`
via the Frobenius/Galois equivariance `e_ℓ(πS,πT) = e_ℓ(S,T)^q`, `π` acting as `ζ ↦ ζ^q` on `μ_ℓ`).
It is carried here as the explicit hypothesis `hres`, the same way the project carries its other
geometric residuals (cf. `qf_nonneg_skeleton_of_pivot_chain`, `weilPairing_scaling`'s `hcomm`/`hfact`).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.6 (`det φ_ℓ = deg φ`), V.1.1 / V.2.3.1
  (the Hasse-bound assembly).
-/

open WeierstrassCurve Real Matrix

namespace HasseWeil.WeilPairing

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]

/-- **GAP-QF top leaf via the Weil pairing** (Silverman III.6.3 / V.2.3.1, the Route-2A capstone).

Given the per-`ℓ` Frobenius-matrix determinant data `hres` (the output of the Weil-pairing
`DET-DEG`, `det(ρ_ℓ φ) = deg φ`, for `φ ∈ {π, 1−π, rπ−s}`, on the base change of `E` to `K̄`) and a
non-negative degree function `deg` realising the third determinant, the Hasse quadratic form
`(#K)·r² − tr(π)·rs + s²` is non-negative for **all** `(r,s)` — exactly the conclusion the
legacy `qf_nonneg_skeleton` chain targeted (retired 2026-06-11).

This is the additivity-free Weil-pairing route to the GAP-QF leaf: the determinant data avoids the
characteristic-`p` dual-additivity wall (the retired `genuineIsogSmulSub_degree_eq_signed`), because the
per-isogeny scaling `det(ρ_ℓ φ) = deg φ` holds for every `φ` individually (Silverman III.8.6). It
composes `det = deg` (`DetDeg`) with the shipped arithmetic reduction
`qf_nonneg_of_frob_det_residual`. -/
theorem qf_nonneg_skeleton_of_weil_det_data (hq : 2 ≤ Fintype.card K)
    (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hres : ∀ r s : ℤ, ¬ ((ringChar K) : ℤ) ∣ s → ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ ringChar K →
      ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
        M.det = ((Fintype.card K : ℤ) : ZMod ℓ) ∧
        (1 - M).det = ((Fintype.card K + 1 -
            isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) : ℤ) : ZMod ℓ) ∧
        ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (deg r s : ZMod ℓ)) :
    ∀ r s : ℤ, 0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
      isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  -- `p = char K` is prime; `q = #K > 0`.
  obtain ⟨p, hCharP, ⟨n, hn⟩, hp_prime, hcard⟩ := FiniteField.card' K
  haveI : Fact p.Prime := ⟨hp_prime⟩
  haveI : CharP K p := hCharP
  have hpchar : ringChar K = p := by
    rw [ringChar.eq_iff]; exact hCharP
  have hqpos : (0 : ℤ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  -- Feed the shipped det-data reduction with `q = #K`, `t = isogTrace`.
  refine qf_nonneg_of_frob_det_residual hp_prime hqpos deg hdeg_nonneg ?_
  intro r s hps ℓ hℓ hℓne
  exact hres r s (by rwa [hpchar]) ℓ hℓ (by rwa [hpchar])

/-- **GAP-QF top leaf via the Weil pairing, coprime-BOTH form** (reviewer round-23, Route B).

Identical to `qf_nonneg_skeleton_of_weil_det_data` but requesting the per-`ℓ` Frobenius det data only
on the locus `{p ∤ r ∧ p ∤ s}` (both coordinates coprime to `p = char K`).  This is exactly the locus
on which the Weil-pairing pencil scaling for `rπ − s` is available **without** the inseparable
`p ∣ r` geometric input (the last pencil `sorry`).  The discriminant lift is the stronger
`qf_nonneg_of_frob_det_residual_both`. -/
theorem qf_nonneg_skeleton_of_weil_det_data_both (hq : 2 ≤ Fintype.card K)
    (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hres : ∀ r s : ℤ, ¬ ((ringChar K) : ℤ) ∣ r → ¬ ((ringChar K) : ℤ) ∣ s →
        ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ ringChar K →
      ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
        M.det = ((Fintype.card K : ℤ) : ZMod ℓ) ∧
        (1 - M).det = ((Fintype.card K + 1 -
            isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) : ℤ) : ZMod ℓ) ∧
        ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (deg r s : ZMod ℓ)) :
    ∀ r s : ℤ, 0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
      isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  obtain ⟨p, hCharP, ⟨n, hn⟩, hp_prime, hcard⟩ := FiniteField.card' K
  haveI : Fact p.Prime := ⟨hp_prime⟩
  haveI : CharP K p := hCharP
  have hpchar : ringChar K = p := by rw [ringChar.eq_iff]; exact hCharP
  have hqpos : (0 : ℤ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  refine qf_nonneg_of_frob_det_residual_both hp_prime hqpos deg hdeg_nonneg ?_
  intro r s hpr hps ℓ hℓ hℓne
  exact hres r s (by rwa [hpchar]) (by rwa [hpchar]) ℓ hℓ (by rwa [hpchar])

/-- **The Hasse bound via the Weil pairing** (Silverman V.1.1, the Route-2A capstone milestone).

`|#E(F_q) − q − 1| ≤ 2√q`, assembled from the per-`ℓ` Frobenius-matrix determinant data `hres`
(the Weil-pairing `DET-DEG` output, Silverman III.8.6) via the GAP-QF leaf
`qf_nonneg_skeleton_of_weil_det_data` and the shipped Hasse-bound milestone wiring
`hasse_bound_of_full_qf_nonneg_witnesses` (with the second leaf `ker_deg_skeleton` already closed).

The Weil-pairing route discharges the GAP-QF leaf directly from the determinant
data — bypassing the characteristic-`p` dual-additivity wall. -/
theorem hasse_bound_via_weil_pairing (hq : 2 ≤ Fintype.card K)
    (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hres : ∀ r s : ℤ, ¬ ((ringChar K) : ℤ) ∣ s → ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ ringChar K →
      ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
        M.det = ((Fintype.card K : ℤ) : ZMod ℓ) ∧
        (1 - M).det = ((Fintype.card K + 1 -
            isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) : ℤ) : ZMod ℓ) ∧
        ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (deg r s : ZMod ℓ)) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * Real.sqrt (Fintype.card K : ℝ) :=
  hasse_bound_of_full_qf_nonneg_witnesses W (isogOneSub_negFrobenius W hq)
    (isogOneSub_negFrobenius_toAddMonoidHom W hq)
    (ker_deg_skeleton W hq)
    (qf_nonneg_skeleton_of_weil_det_data W hq deg hdeg_nonneg hres)

/-- **The Hasse bound via the Weil pairing, coprime-BOTH form** (reviewer round-23, Route B).

`|#E(F_q) − q − 1| ≤ 2√q`, assembled from the per-`ℓ` Frobenius-matrix determinant data `hres`
requested only on the locus `{p ∤ r ∧ p ∤ s}` (both coordinates coprime to `p = char K`).  This is the
form that the unconditional Hasse bound consumes: on `{p ∤ r ∧ p ∤ s}` the pencil `rπ − s` is genuine
and the Weil-pairing scaling holds **without** the inseparable `p ∣ r` geometric input.  Via the
coprime-BOTH GAP-QF leaf `qf_nonneg_skeleton_of_weil_det_data_both`. -/
theorem hasse_bound_via_weil_pairing_both (hq : 2 ≤ Fintype.card K)
    (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hres : ∀ r s : ℤ, ¬ ((ringChar K) : ℤ) ∣ r → ¬ ((ringChar K) : ℤ) ∣ s →
        ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ ringChar K →
      ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
        M.det = ((Fintype.card K : ℤ) : ZMod ℓ) ∧
        (1 - M).det = ((Fintype.card K + 1 -
            isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) : ℤ) : ZMod ℓ) ∧
        ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (deg r s : ZMod ℓ)) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * Real.sqrt (Fintype.card K : ℝ) :=
  hasse_bound_of_full_qf_nonneg_witnesses W (isogOneSub_negFrobenius W hq)
    (isogOneSub_negFrobenius_toAddMonoidHom W hq)
    (ker_deg_skeleton W hq)
    (qf_nonneg_skeleton_of_weil_det_data_both W hq deg hdeg_nonneg hres)

end HasseWeil.WeilPairing
