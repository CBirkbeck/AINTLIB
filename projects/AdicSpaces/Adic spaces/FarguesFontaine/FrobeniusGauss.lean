/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.FrobeniusAction
import «Adic spaces».FarguesFontaine.GaussNorm
import «Adic spaces».FarguesFontaine.RobbaLoc
import «Adic spaces».FarguesFontaine.UniformizerEquivariance

/-!
# Frobenius and the Gauss valuations (D-iii foundation)

The radius-change law of the Witt Frobenius on `A_inf = W(O_F)`:

* `FarguesFontaine.teichCoeff_frob` : `φ` is the coefficient-wise `p`-th power;
* `FarguesFontaine.gaussValue_frob` : `w_{ρ^p}(φ x) = w_ρ(x)^p` — Frobenius
  intertwines the Gauss valuations with the `p`-th power of the radius
  (κ ↦ p·κ on windows; `q ↦ q/p` on the `BIQ`-exponent indexing).
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- Frobenius acts coefficient-wise as the `p`-th power on Teichmüller
coordinates. -/
theorem teichCoeff_frob (x : Ainf p F) (n : ℕ) :
    teichCoeff p F (frob p F x) n = teichCoeff p F x n ^ p := by
  rw [teichCoeff, teichCoeff]
  have hcoeff : (frob p F x).coeff n = x.coeff n ^ p := by
    show (WittVector.frobeniusEquiv p (OF F) x).coeff n = x.coeff n ^ p
    rw [WittVector.frobeniusEquiv_apply, frobenius_eq_map_frobenius,
      WittVector.map_coeff]
    exact frobenius_def _ _
  rw [hcoeff, map_pow]

/-- The Gauss term at the `p`-th-power radius of a Frobenius image is the
`p`-th power of the Gauss term. -/
theorem gaussTerm_frob (ρ : NNReal) (x : Ainf p F) (n : ℕ) :
    gaussTerm p F (ρ ^ p) (frob p F x) n = gaussTerm p F ρ x n ^ p := by
  rw [gaussTerm, gaussTerm, teichCoeff_frob, mul_pow, ← pow_mul, ← pow_mul,
    mul_comm n p, pow_mul]
  congr 1
  push_cast
  rw [Valuation.map_pow]

/-- **The Frobenius radius-change law**: `w_{ρ^p}(φ x) = w_ρ(x)^p`. -/
theorem gaussValue_frob {ρ : NNReal} (hρ1 : ρ ≤ 1) (x : Ainf p F) :
    gaussValue p F (ρ ^ p) (frob p F x) = gaussValue p F ρ x ^ p := by
  rw [gaussValue, gaussValue]
  have hmono : Monotone (fun t : NNReal => t ^ p) :=
    fun a b hab => pow_le_pow_left₀ zero_le hab p
  have hcont : ContinuousAt (fun t : NNReal => t ^ p)
      (⨆ n, gaussTerm p F ρ x n) := (continuous_pow p).continuousAt
  rw [Monotone.map_ciSup_of_continuousAt hcont hmono
    (bddAbove_range_gaussTerm p F hρ1 x)]
  congr 1
  funext n
  exact gaussTerm_frob p F ρ x n

/-- Frobenius sends the inverted element to a unit of `Bloc`. -/
theorem isUnit_frob_p_teichPi_image (y : Submonoid.powers
    ((p : Ainf p F) * teichPi p F ϖ)) :
    IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ) (frob p F (y : Ainf p F))) := by
  obtain ⟨k, hk⟩ := y.2
  rw [show (y : Ainf p F) = ((p : Ainf p F) * teichPi p F ϖ) ^ k from hk.symm,
    map_pow, map_pow]
  refine IsUnit.pow k ?_
  rw [map_mul, frob_natCast, frob_teichPi, map_mul, map_pow]
  exact (isUnit_p_image p F ϖ).mul ((isUnit_teichPi_image p F ϖ).pow p)

/-- **Frobenius on `Bloc`**, by the universal property of the localization. -/
noncomputable def frobBloc : Bloc p F ϖ →+* Bloc p F ϖ :=
  IsLocalization.lift (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ))
    (g := (algebraMap (Ainf p F) (Bloc p F ϖ)).comp (frob p F).toRingHom)
    (fun y => isUnit_frob_p_teichPi_image p F ϖ y)

@[simp]
theorem frobBloc_algebraMap (x : Ainf p F) :
    frobBloc p F ϖ (algebraMap (Ainf p F) (Bloc p F ϖ) x)
      = algebraMap (Ainf p F) (Bloc p F ϖ) (frob p F x) :=
  IsLocalization.lift_eq _ x

/-- **The radius-change law on `Bloc`**: `w_{ρ^p}(φ z) = w_ρ(z)^p`. -/
theorem wLoc_frobBloc {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hρp0 : 0 < ρ ^ p) (hρp1 : ρ ^ p < 1) (z : Bloc p F ϖ) :
    wLoc p F ϖ hρp0 hρp1 (frobBloc p F ϖ z) = wLoc p F ϖ hρ0 hρ1 z ^ p := by
  obtain ⟨⟨a, y⟩, hz⟩ := IsLocalization.surj
    (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) z
  obtain ⟨m, hm⟩ := y.2
  have hz' : z * algebraMap (Ainf p F) (Bloc p F ϖ)
      (((p : Ainf p F) * teichPi p F ϖ) ^ m) = algebraMap _ _ a := by
    rw [show ((p : Ainf p F) * teichPi p F ϖ) ^ m = (y : Ainf p F) from hm]
    exact hz
  have himg : frobBloc p F ϖ z * algebraMap (Ainf p F) (Bloc p F ϖ)
      (frob p F (((p : Ainf p F) * teichPi p F ϖ) ^ m))
      = algebraMap _ _ (frob p F a) := by
    have hmap := congrArg (frobBloc p F ϖ) hz'
    rwa [map_mul, frobBloc_algebraMap, frobBloc_algebraMap] at hmap
  have h1 := congrArg (wLoc p F ϖ hρp0 hρp1) himg
  have h2 := congrArg (wLoc p F ϖ hρ0 hρ1) hz'
  rw [Valuation.map_mul, wLoc_algebraMap, wLoc_algebraMap,
    gaussValue_frob p F hρ1.le, gaussValue_frob p F hρ1.le] at h1
  rw [Valuation.map_mul, wLoc_algebraMap, wLoc_algebraMap] at h2
  have hval : gaussValue p F ρ (((p : Ainf p F) * teichPi p F ϖ) ^ m)
      = (ρ * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ m :=
    gaussValue_p_teichPi_pow p F ϖ hρ0 hρ1 m
  have hπ0 : (0 : NNReal) < perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) := by
    refine pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr ?_)
    exact fun hcon => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext hcon)
  have hne : ((ρ * perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ m) ^ p ≠ 0 :=
    pow_ne_zero p (pow_ne_zero m (mul_ne_zero hρ0.ne' hπ0.ne'))
  rw [hval] at h1 h2
  -- h1 : wLoc_{ρ^p}(φz) * ((ρ·vπ)^m)^p = gaussValue_ρ(a)^p  (after the pow-collapse)
  -- h2 : wLoc_ρ(z) * (ρ·vπ)^m = gaussValue_ρ(a)
  refine mul_right_cancel₀ hne ?_
  calc wLoc p F ϖ hρp0 hρp1 (frobBloc p F ϖ z)
        * ((ρ * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ m) ^ p
      = gaussValue p F ρ a ^ p := h1
    _ = (wLoc p F ϖ hρ0 hρ1 z * (ρ * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ m) ^ p := by rw [h2]
    _ = wLoc p F ϖ hρ0 hρ1 z ^ p * ((ρ * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ m) ^ p := by
        rw [mul_pow]

end FarguesFontaine

end
