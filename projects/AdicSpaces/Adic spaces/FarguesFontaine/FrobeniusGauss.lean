/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.FrobeniusAction
import «Adic spaces».FarguesFontaine.GaussNorm

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

end FarguesFontaine

end
