/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.RobbaLoc

/-!
# Uniformizer-equivariance of `Bloc` and its Gauss valuations (D-i-t1)

If `[ϖ']^k = [ϖ]` then `p·[ϖ']` and `p·[ϖ]` generate the same saturation, so
the localizations agree and the Gauss valuations correspond:

* `FarguesFontaine.isLocalization_twist_Bloc` / `blocTwistEquiv` :
  `Bloc-in-ϖ' ≃+* Bloc-in-ϖ` canonically;
* `FarguesFontaine.wLoc_blocTwistEquiv` : `wLoc` is invariant through the
  change isomorphism (the Gauss value is uniformizer-free).

These feed the `B^I`-equivariance (D-i-t2) used to compare the two
circle-localizations in the chart-transition data of the curve.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- **`Bloc` is uniformizer-invariant**: if `[ϖ']^k = [ϖ]` then `Bloc-in-ϖ` is
also the localization away from `p·[ϖ']`. -/
theorem isLocalization_twist_Bloc {ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k)
    (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) :
    IsLocalization (Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ'))
      (Bloc p F ϖ) where
  map_units := by
    rintro ⟨y, m, rfl⟩
    have hϖ'unit : IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ')) := by
      refine isUnit_of_mul_isUnit_left
        (y := algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ' ^ (k - 1))) ?_
      rw [← map_mul, ← pow_succ']
      rw [show k - 1 + 1 = k from by omega, h]
      exact isUnit_teichPi_image p F ϖ
    have hunit : IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ)
        ((p : Ainf p F) * teichPi p F ϖ')) := by
      rw [map_mul]
      exact (isUnit_p_image p F ϖ).mul hϖ'unit
    show IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ)
      (((p : Ainf p F) * teichPi p F ϖ') ^ m))
    rw [map_pow]
    exact hunit.pow m
  surj := by
    intro z
    obtain ⟨⟨a, y⟩, hz⟩ := IsLocalization.surj
      (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) z
    obtain ⟨m, hm⟩ := y.2
    refine ⟨⟨a * (p : Ainf p F) ^ (k * m - m),
      ⟨((p : Ainf p F) * teichPi p F ϖ') ^ (k * m), k * m, rfl⟩⟩, ?_⟩
    show z * algebraMap (Ainf p F) (Bloc p F ϖ)
        (((p : Ainf p F) * teichPi p F ϖ') ^ (k * m))
      = algebraMap (Ainf p F) (Bloc p F ϖ) (a * (p : Ainf p F) ^ (k * m - m))
    have hexp : ((p : Ainf p F) * teichPi p F ϖ') ^ (k * m)
        = ((p : Ainf p F) * teichPi p F ϖ) ^ m * (p : Ainf p F) ^ (k * m - m) := by
      have hteich' : teichPi p F ϖ' ^ (k * m) = teichPi p F ϖ ^ m := by
        rw [pow_mul, h]
      have hpsplit : (p : Ainf p F) ^ (k * m)
          = (p : Ainf p F) ^ m * (p : Ainf p F) ^ (k * m - m) := by
        rw [← pow_add]
        congr 1
        have : m ≤ k * m := Nat.le_mul_of_pos_left m hk
        omega
      rw [mul_pow, mul_pow, hteich', hpsplit]
      ring
    rw [hexp, map_mul, ← mul_assoc,
      show ((p : Ainf p F) * teichPi p F ϖ) ^ m = (y : Ainf p F) from hm, hz,
      ← map_mul]
  exists_of_eq := by
    intro x y hxy
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq
      (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) (S := Bloc p F ϖ) hxy
    obtain ⟨m, hm⟩ := c.2
    refine ⟨⟨((p : Ainf p F) * teichPi p F ϖ') ^ (k * m), k * m, rfl⟩, ?_⟩
    show ((p : Ainf p F) * teichPi p F ϖ') ^ (k * m) * x
      = ((p : Ainf p F) * teichPi p F ϖ') ^ (k * m) * y
    have hexp : ((p : Ainf p F) * teichPi p F ϖ') ^ (k * m)
        = ((p : Ainf p F) * teichPi p F ϖ) ^ m * (p : Ainf p F) ^ (k * m - m) := by
      have hteich' : teichPi p F ϖ' ^ (k * m) = teichPi p F ϖ ^ m := by
        rw [pow_mul, h]
      have hpsplit : (p : Ainf p F) ^ (k * m)
          = (p : Ainf p F) ^ m * (p : Ainf p F) ^ (k * m - m) := by
        rw [← pow_add]
        congr 1
        have : m ≤ k * m := Nat.le_mul_of_pos_left m hk
        omega
      rw [mul_pow, mul_pow, hteich', hpsplit]
      ring
    rw [hexp]
    have hc' : ((p : Ainf p F) * teichPi p F ϖ) ^ m * x
        = ((p : Ainf p F) * teichPi p F ϖ) ^ m * y := by
      rw [show ((p : Ainf p F) * teichPi p F ϖ) ^ m = (c : Ainf p F) from hm]
      exact hc
    calc ((p : Ainf p F) * teichPi p F ϖ) ^ m * (p : Ainf p F) ^ (k * m - m) * x
        = (p : Ainf p F) ^ (k * m - m) * (((p : Ainf p F) * teichPi p F ϖ) ^ m * x) := by
          ring
      _ = (p : Ainf p F) ^ (k * m - m) * (((p : Ainf p F) * teichPi p F ϖ) ^ m * y) := by
          rw [hc']
      _ = ((p : Ainf p F) * teichPi p F ϖ) ^ m * (p : Ainf p F) ^ (k * m - m) * y := by
          ring


/-- **The uniformizer-change isomorphism** `Bloc-in-ϖ' ≃+* Bloc-in-ϖ`. -/
noncomputable def blocTwistEquiv {ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k)
    (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) :
    Bloc p F ϖ' ≃+* Bloc p F ϖ :=
  letI := isLocalization_twist_Bloc p F ϖ hk h
  (IsLocalization.algEquiv (Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ'))
    (Bloc p F ϖ') (Bloc p F ϖ)).toRingEquiv

@[simp]
theorem blocTwistEquiv_algebraMap {ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k)
    (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) (y : Ainf p F) :
    blocTwistEquiv p F ϖ hk h (algebraMap (Ainf p F) (Bloc p F ϖ') y)
      = algebraMap (Ainf p F) (Bloc p F ϖ) y := by
  letI := isLocalization_twist_Bloc p F ϖ hk h
  exact (IsLocalization.algEquiv (Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ'))
    (Bloc p F ϖ') (Bloc p F ϖ)).commutes y

/-- Gauss value of powers of the localized element. -/
theorem gaussValue_p_teichPi_pow (ϖ'' : PseudoUniformizer F) {ρ : NNReal}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (m : ℕ) :
    gaussValue p F ρ (((p : Ainf p F) * teichPi p F ϖ'') ^ m)
      = (ρ * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ'' : OF F) : F)) ^ m := by
  induction m with
  | zero =>
    rw [pow_zero, pow_zero]
    exact gaussValue_one p F hρ1.le
  | succ n ih =>
    rw [pow_succ, pow_succ, gaussValue_mul p F hρ0 hρ1, ih,
      gaussValue_p_teichPi p F ϖ'' hρ1]

/-- **The Gauss valuations are uniformizer-invariant** through the change
isomorphism. -/
theorem wLoc_blocTwistEquiv {ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k)
    (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) {ρ : NNReal} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (z : Bloc p F ϖ') :
    wLoc p F ϖ hρ0 hρ1 (blocTwistEquiv p F ϖ hk h z)
      = wLoc p F ϖ' hρ0 hρ1 z := by
  obtain ⟨⟨a, y⟩, hz⟩ := IsLocalization.surj
    (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ')) z
  obtain ⟨m, hm⟩ := y.2
  have hz' : z * algebraMap (Ainf p F) (Bloc p F ϖ')
      (((p : Ainf p F) * teichPi p F ϖ') ^ m) = algebraMap _ _ a := by
    rw [show ((p : Ainf p F) * teichPi p F ϖ') ^ m = (y : Ainf p F) from hm]
    exact hz
  have himg : blocTwistEquiv p F ϖ hk h z * algebraMap (Ainf p F) (Bloc p F ϖ)
      (((p : Ainf p F) * teichPi p F ϖ') ^ m) = algebraMap _ _ a := by
    have hmap := congrArg (blocTwistEquiv p F ϖ hk h) hz'
    rwa [map_mul, blocTwistEquiv_algebraMap, blocTwistEquiv_algebraMap] at hmap
  have hval := gaussValue_p_teichPi_pow p F ϖ' hρ0 hρ1 m
  have hne : (ρ * perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ' : OF F) : F)) ^ m ≠ 0 :=
    pow_ne_zero m (mul_ne_zero hρ0.ne' (vpi_pos p F ϖ').ne')
  have h1 := congrArg (wLoc p F ϖ hρ0 hρ1) himg
  have h2 := congrArg (wLoc p F ϖ' hρ0 hρ1) hz'
  rw [Valuation.map_mul, wLoc_algebraMap, wLoc_algebraMap, hval] at h1
  rw [Valuation.map_mul, wLoc_algebraMap, wLoc_algebraMap, hval] at h2
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

end FarguesFontaine

end
