/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.HasseAssembly
import HasseWeil.IsogenyBaseChange

/-!
# Frobenius matrix data over the algebraic closure

This file supplies the per-`ℓ` Frobenius-matrix determinant data used by
`hasse_bound_via_weil_pairing`, after base-changing `E/K` to `AlgebraicClosure K`.

## Main definitions

* `frobeniusHomBaseChange`: the `q`-power Frobenius on base-changed points.
* `FrobBaseChangeScalings`: the three Weil-pairing scaling assumptions over `K̄`.
* `FrobBaseChangeScalingsCoprime`: the coprime-BOTH variant of the scaling assumptions.

## Main results

* `frob_det_residual_baseChange`: base-change scaling data gives the residual matrix.
* `hres_of_baseChange_scalings`: the assembled `hres` input for the Hasse-bound route.
* `hasse_bound_unconditional_of_baseChange_scalings`: the Hasse bound from the scaling leaf.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.1 (the pairing + Galois equivariance),
  III.8.6 (`det φ_ℓ = deg φ`), V.1.1 / V.2.3.1 (the Hasse bound assembly).

## Name-clash note

`pullbackDivisor_kappaDivisor` is declared in both `HfactLemma.lean` and `PairingNondeg.lean`.
This file imports neither directly, so no clash arises and no rename is needed.
-/

open WeierstrassCurve Real Matrix

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.TorsionGeometric

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]

section BaseChange

/-- The `q`-power Frobenius `AddMonoidHom` on the base-changed points of `E`. -/
noncomputable def frobeniusHomBaseChange
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic] :
    (W.baseChange L).toAffine.Point →+ (W.baseChange L).toAffine.Point :=
  (Isogeny.frobeniusIsog_baseChange_charP_pow p r W L).toAddMonoidHom

end BaseChange

/-- The Frobenius Weil-pairing scaling on base-changed `ℓ`-torsion. -/
def FrobeniusScaling
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic] : Prop :=
  ∀ ℓ : ℕ, ∀ hℓp : ℓ.Prime, ℓ ≠ ringChar K → ∀ (hℓF : (ℓ : L) ≠ 0),
    letI : Fact ℓ.Prime := ⟨hℓp⟩
    WeilScales (W.baseChange L) ℓ hℓF (frobeniusHomBaseChange W p r L) (Fintype.card K)

/-- The `1 - π` Weil-pairing scaling on base-changed `ℓ`-torsion. -/
def OneSubFrobeniusScaling
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) : Prop :=
  ∀ ℓ : ℕ, ∀ hℓp : ℓ.Prime, ℓ ≠ ringChar K → ∀ (hℓF : (ℓ : L) ≠ 0),
    letI : Fact ℓ.Prime := ⟨hℓp⟩
    WeilScales (W.baseChange L) ℓ hℓF
      (AddMonoidHom.id (W.baseChange L).toAffine.Point - frobeniusHomBaseChange W p r L)
      (isogOneSub_negFrobenius W hq).degree

/-- The `rπ - s` pencil Weil-pairing scaling on base-changed `ℓ`-torsion. -/
def PencilScaling
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    (deg : ℤ → ℤ → ℤ) : Prop :=
  ∀ r' s' : ℤ, ¬ ((ringChar K : ℤ)) ∣ s' → ∀ ℓ : ℕ, ∀ hℓp : ℓ.Prime,
    ℓ ≠ ringChar K → ∀ (hℓF : (ℓ : L) ≠ 0), letI : Fact ℓ.Prime := ⟨hℓp⟩
      WeilScales (W.baseChange L) ℓ hℓF
        (r' • frobeniusHomBaseChange W p r L -
          s' • AddMonoidHom.id (W.baseChange L).toAffine.Point)
        (deg r' s').toNat

/-- The coprime-BOTH variant of the pencil Weil-pairing scaling. -/
def PencilScalingCoprime
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    (deg : ℤ → ℤ → ℤ) : Prop :=
  ∀ r' s' : ℤ, ¬ ((ringChar K : ℤ)) ∣ r' → ¬ ((ringChar K : ℤ)) ∣ s' →
    ∀ ℓ : ℕ, ∀ hℓp : ℓ.Prime, ℓ ≠ ringChar K →
    ∀ (hℓF : (ℓ : L) ≠ 0), letI : Fact ℓ.Prime := ⟨hℓp⟩
      WeilScales (W.baseChange L) ℓ hℓF
        (r' • frobeniusHomBaseChange W p r L -
          s' • AddMonoidHom.id (W.baseChange L).toAffine.Point)
        (deg r' s').toNat

/-- The three base-change Weil-pairing scaling leaves for the Frobenius pencil. -/
def FrobBaseChangeScalings
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) : Prop :=
  FrobeniusScaling W p r L ∧ OneSubFrobeniusScaling W p r L hq ∧
    PencilScaling W p r L deg

/-- The coprime-BOTH variant of the base-change Weil-pairing scaling leaves. -/
def FrobBaseChangeScalingsCoprime
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) : Prop :=
  FrobeniusScaling W p r L ∧ OneSubFrobeniusScaling W p r L hq ∧
    PencilScalingCoprime W p r L deg

omit [Fintype W.toAffine.Point] in
/-- The trace identity `#K + 1 - t = deg(1 - π)` for the Frobenius isogeny. -/
theorem card_add_one_sub_isogTrace_eq_degree (hq : 2 ≤ Fintype.card K) :
    (Fintype.card K + 1 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) : ℤ) =
      ((isogOneSub_negFrobenius W hq).degree : ℤ) := by
  unfold isogTrace
  rw [frobeniusIsog_degree]
  ring

omit [Fintype W.toAffine.Point] in
/-- The base-changed Weil-pairing scalings give the residual Frobenius matrix. -/
theorem frob_det_residual_baseChange
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (r' s' : ℤ) (ℓ : ℕ) (hℓp : ℓ.Prime) (hℓF : (ℓ : L) ≠ 0)
    (hsc :
      letI : Fact ℓ.Prime := ⟨hℓp⟩
      WeilScales (W.baseChange L) ℓ hℓF (frobeniusHomBaseChange W p r L) (Fintype.card K) ∧
        WeilScales (W.baseChange L) ℓ hℓF
          (AddMonoidHom.id (W.baseChange L).toAffine.Point - frobeniusHomBaseChange W p r L)
          (isogOneSub_negFrobenius W hq).degree ∧
        WeilScales (W.baseChange L) ℓ hℓF
          (r' • frobeniusHomBaseChange W p r L -
            s' • AddMonoidHom.id (W.baseChange L).toAffine.Point)
          (deg r' s').toNat) :
    ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
      M.det = ((Fintype.card K : ℤ) : ZMod ℓ) ∧
      (1 - M).det = ((Fintype.card K + 1 -
          isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) : ℤ) : ZMod ℓ) ∧
      ((r' : ZMod ℓ) • M - (s' : ZMod ℓ) • 1).det = (deg r' s' : ZMod ℓ) := by
  letI : Fact ℓ.Prime := ⟨hℓp⟩
  obtain ⟨hπ, h1, hrs⟩ := hsc
  have hDd : ((deg r' s').toNat : ℤ) = deg r' s' := Int.toNat_of_nonneg (hdeg_nonneg r' s')
  exact frob_det_residual_of_weil_scaling (W.baseChange L) ℓ hℓF
    (frobeniusHomBaseChange W p r L)
    (Fintype.card K)
    (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))
    (deg r' s') r' s'
    (Fintype.card K) (isogOneSub_negFrobenius W hq).degree (deg r' s').toNat
    rfl
    (card_add_one_sub_isogTrace_eq_degree W hq).symm
    hDd
    hπ h1 hrs

/-- A prime different from the characteristic has nonzero image in the field. -/
theorem natCast_ne_zero_of_prime_ne_ringChar
    {p : ℕ} (hp : p.Prime) (L : Type*) [Field L] [CharP L p]
    (ℓ : ℕ) (hℓp : ℓ.Prime) (hℓne : ℓ ≠ p) : (ℓ : L) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff L p ℓ]
  intro hdvd
  exact hℓne (((Nat.prime_dvd_prime_iff_eq hp hℓp).mp hdvd).symm)

omit [Fintype W.toAffine.Point] in
/-- The base-change scaling leaf gives the `hres` input for `hasse_bound_via_weil_pairing`. -/
theorem hres_of_baseChange_scalings
    (p r : ℕ) [hp : Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hpchar : ringChar K = p)
    (hscale : FrobBaseChangeScalings W p r L hq deg) :
    ∀ r' s' : ℤ, ¬ ((ringChar K : ℤ)) ∣ s' → ∀ ℓ : ℕ, ℓ.Prime →
      ℓ ≠ ringChar K →
      ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
        M.det = ((Fintype.card K : ℤ) : ZMod ℓ) ∧
        (1 - M).det = ((Fintype.card K + 1 -
            isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) : ℤ) : ZMod ℓ) ∧
        ((r' : ZMod ℓ) • M - (s' : ZMod ℓ) • 1).det = (deg r' s' : ZMod ℓ) := by
  haveI : CharP L p := charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective K L) p
  obtain ⟨hFrob, hOneSub, hPencil⟩ := hscale
  intro r' s' hps ℓ hℓp hℓne
  have hℓF : (ℓ : L) ≠ 0 :=
    natCast_ne_zero_of_prime_ne_ringChar hp.out L ℓ hℓp (by rwa [hpchar] at hℓne)
  exact frob_det_residual_baseChange W p r L hq deg hdeg_nonneg r' s' ℓ hℓp hℓF
    ⟨hFrob ℓ hℓp hℓne hℓF, hOneSub ℓ hℓp hℓne hℓF,
      hPencil r' s' hps ℓ hℓp hℓne hℓF⟩

omit [Fintype W.toAffine.Point] in
/-- The coprime-BOTH base-change scaling leaf gives the `hres` input for Route B. -/
theorem hres_of_baseChange_scalings_coprime
    (p r : ℕ) [hp : Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hpchar : ringChar K = p)
    (hscale : FrobBaseChangeScalingsCoprime W p r L hq deg) :
    ∀ r' s' : ℤ, ¬ ((ringChar K : ℤ)) ∣ r' → ¬ ((ringChar K : ℤ)) ∣ s' →
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ ringChar K →
      ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
        M.det = ((Fintype.card K : ℤ) : ZMod ℓ) ∧
        (1 - M).det = ((Fintype.card K + 1 -
            isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) : ℤ) : ZMod ℓ) ∧
        ((r' : ZMod ℓ) • M - (s' : ZMod ℓ) • 1).det = (deg r' s' : ZMod ℓ) := by
  haveI : CharP L p := charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective K L) p
  obtain ⟨hFrob, hOneSub, hPencil⟩ := hscale
  intro r' s' hpr hps ℓ hℓp hℓne
  have hℓF : (ℓ : L) ≠ 0 :=
    natCast_ne_zero_of_prime_ne_ringChar hp.out L ℓ hℓp (by rwa [hpchar] at hℓne)
  exact frob_det_residual_baseChange W p r L hq deg hdeg_nonneg r' s' ℓ hℓp hℓF
    ⟨hFrob ℓ hℓp hℓne hℓF, hOneSub ℓ hℓp hℓne hℓF,
      hPencil r' s' hpr hps ℓ hℓp hℓne hℓF⟩

noncomputable local instance : DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- The unconditional Hasse bound from the base-change scaling leaf. -/
theorem hasse_bound_unconditional_of_baseChange_scalings
    (hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hscale : ∀ (p r : ℕ) (_ : Fact p.Prime) (_ : CharP K p)
      (_ : Fact (Fintype.card K = p ^ r)),
      FrobBaseChangeScalings W p r (AlgebraicClosure K) hq deg) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * Real.sqrt (Fintype.card K : ℝ) := by
  obtain ⟨p, hCharP, ⟨n, _hn⟩, hp_prime, hcard⟩ := FiniteField.card' K
  haveI : Fact p.Prime := ⟨hp_prime⟩
  haveI : CharP K p := hCharP
  haveI : Fact (Fintype.card K = p ^ (n : ℕ)) := ⟨hcard⟩
  have hpchar : ringChar K = p := by rw [ringChar.eq_iff]; exact hCharP
  haveI : ExpChar (AlgebraicClosure K) p :=
    haveI : CharP (AlgebraicClosure K) p :=
      charP_of_injective_algebraMap
        (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)) p
    ExpChar.prime hp_prime
  haveI : (W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic := inferInstance
  exact hasse_bound_via_weil_pairing W hq deg hdeg_nonneg
    (hres_of_baseChange_scalings W p (n : ℕ) (AlgebraicClosure K) hq deg hdeg_nonneg hpchar
      (hscale p (n : ℕ) ⟨hp_prime⟩ hCharP ⟨hcard⟩))

/-- The unconditional Hasse bound from the coprime-BOTH base-change scaling leaf. -/
theorem hasse_bound_unconditional_of_baseChange_scalings_coprime
    (hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s)
    (hscale : ∀ (p r : ℕ) (_ : Fact p.Prime) (_ : CharP K p)
      (_ : Fact (Fintype.card K = p ^ r)),
      FrobBaseChangeScalingsCoprime W p r (AlgebraicClosure K) hq deg) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * Real.sqrt (Fintype.card K : ℝ) := by
  obtain ⟨p, hCharP, ⟨n, _hn⟩, hp_prime, hcard⟩ := FiniteField.card' K
  haveI : Fact p.Prime := ⟨hp_prime⟩
  haveI : CharP K p := hCharP
  haveI : Fact (Fintype.card K = p ^ (n : ℕ)) := ⟨hcard⟩
  have hpchar : ringChar K = p := by rw [ringChar.eq_iff]; exact hCharP
  haveI : ExpChar (AlgebraicClosure K) p :=
    haveI : CharP (AlgebraicClosure K) p :=
      charP_of_injective_algebraMap
        (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)) p
    ExpChar.prime hp_prime
  haveI : (W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic := inferInstance
  exact hasse_bound_via_weil_pairing_both W hq deg hdeg_nonneg
    (hres_of_baseChange_scalings_coprime W p (n : ℕ) (AlgebraicClosure K) hq deg
      hdeg_nonneg hpchar
      (hscale p (n : ℕ) ⟨hp_prime⟩ hCharP ⟨hcard⟩))

end HasseWeil.WeilPairing
