/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.HasseBound.QuadraticForm
import HasseWeil.HasseBound.WeilPairing.Assembly
import HasseWeil.HasseBound.WeilPairing.DetDeg
import HasseWeil.Isogeny.VerschiebungFactorization

/-!
# Hasse bound from Weil-pairing determinant data

This file derives nonnegativity of the Hasse quadratic form from residual Frobenius determinant
matrices over `ZMod ℓ`, then uses that result to prove the Hasse bound.

## Main results

* `qf_nonneg_skeleton_of_weil_det_data` proves quadratic-form nonnegativity when determinant data
  is available whenever the second coordinate is coprime to the characteristic.
* `qf_nonneg_skeleton_of_weil_det_data_both` uses data on the locus where both coordinates are
  coprime to the characteristic.
* `hasse_bound_via_weil_pairing` and `hasse_bound_via_weil_pairing_both` assemble the corresponding
  Hasse bounds.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.6, V.1.1, and V.2.3.1.
-/

open WeierstrassCurve

namespace HasseWeil.WeilPairing

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]

omit [Fintype W.toAffine.Point] in
/-- The Hasse quadratic form is nonnegative given Frobenius determinant data whenever `p ∤ s`. -/
theorem qf_nonneg_skeleton_of_weil_det_data (hq : 2 ≤ Fintype.card K)
    (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hres : ∀ r s : ℤ, ¬ ((ringChar K) : ℤ) ∣ s →
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ ringChar K →
      ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
        M.det = ((Fintype.card K : ℤ) : ZMod ℓ) ∧
        (1 - M).det = ((Fintype.card K + 1 -
            isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) : ℤ) : ZMod ℓ) ∧
        ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (deg r s : ZMod ℓ)) :
    ∀ r s : ℤ, 0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
      isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  obtain ⟨p, hCharP, ⟨_, _⟩, hp_prime, _⟩ := FiniteField.card' K
  have : Fact p.Prime := ⟨hp_prime⟩
  have : CharP K p := hCharP
  have hpchar : ringChar K = p := by
    rw [ringChar.eq_iff]; exact hCharP
  have hqpos : (0 : ℤ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  refine qf_nonneg_of_frob_det_residual hp_prime hqpos deg hdeg_nonneg ?_
  intro r s hps ℓ hℓ hℓne
  exact hres r s (by rwa [hpchar]) ℓ hℓ (by rwa [hpchar])

omit [Fintype W.toAffine.Point] in
/-- The Hasse quadratic form is nonnegative given Frobenius determinant data when `p ∤ r` and
`p ∤ s`. -/
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
  obtain ⟨p, hCharP, ⟨_, _⟩, hp_prime, _⟩ := FiniteField.card' K
  have : Fact p.Prime := ⟨hp_prime⟩
  have : CharP K p := hCharP
  have hpchar : ringChar K = p := by
    rw [ringChar.eq_iff]
    exact hCharP
  have hqpos : (0 : ℤ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  refine qf_nonneg_of_frob_det_residual_both hp_prime hqpos deg hdeg_nonneg ?_
  intro r s hpr hps ℓ hℓ hℓne
  exact hres r s (by rwa [hpchar]) (by rwa [hpchar]) ℓ hℓ (by rwa [hpchar])

/-- The Hasse bound follows from Frobenius determinant data whenever `p ∤ s`. -/
theorem hasse_bound_via_weil_pairing (hq : 2 ≤ Fintype.card K)
    (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hres : ∀ r s : ℤ, ¬ ((ringChar K) : ℤ) ∣ s →
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
    (qf_nonneg_skeleton_of_weil_det_data W hq deg hdeg_nonneg hres)

/-- The Hasse bound follows from Frobenius determinant data when `p ∤ r` and `p ∤ s`. -/
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
