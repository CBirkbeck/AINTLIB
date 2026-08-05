/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.BigWindows
import «Adic spaces».FarguesFontaine.ChartComparison
import «Adic spaces».FarguesFontaine.UniformizerEquivariance

/-!
# The Big-window chart rings are the rational-exponent interval rings

`FarguesFontaine.chartRingEquivBIQ` : the presheaf value of the `n`-th
Big-window chart datum (at the twisted uniformizer `ϖ^{1/p^n}`) is canonically
ring-isomorphic to `BIQ (1/p^n) (1/p^{n+1})` in the base uniformizer —
composing the ID2d comparison (`presheafChartRingEquivBISub`), the radius
rewriting to `vpiQ`-form (the twist bridges), and the on-the-nose
uniformizer-invariance `BISub_twist`. This normalizes all chart rings onto
the single `BIQ`-functor, the substrate of the Y-structure presheaf.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)
variable {ρ₁ ρ₂ ρ₁' ρ₂' : NNReal}
variable {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}

/-- Positivity of the scaled exponents. -/
theorem invPowQ_pos (s : ℕ) : (0 : ℚ) < 1 / (p ^ s : ℚ) := by
  have hp : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  positivity

/-- **The Big-window chart's interval ring is `BIQ` at the scaled exponents**
(nonnegative side): the `[|ϖ_n|, |ϖ_n|^{1/p}]`-interval ring in the twisted
uniformizer `ϖ_n = ϖ^{1/p^n}` IS `BIQ (1/p^n) (1/p^{n+1})` in the base
uniformizer, on the nose after the `blocTwistEquiv`-identification of the
underlying localizations — here stated at the level of the radii. -/
theorem vpiQ_frobRoot_one (n : ℕ) :
    vpiQ p F (PseudoUniformizer.frobRoot p F ϖ n) 1
      = vpiQ p F ϖ (1 / (p ^ n : ℚ)) := by
  rw [vpiQ_frobRoot p F ϖ n 1]

theorem vpiQ_frobRoot_invP (n : ℕ) :
    vpiQ p F (PseudoUniformizer.frobRoot p F ϖ n) (1 / (p : ℚ))
      = vpiQ p F ϖ (1 / (p ^ (n + 1) : ℚ)) := by
  rw [vpiQ_frobRoot p F ϖ n (1 / (p : ℚ))]
  congr 1
  have hp : ((p : ℚ)) ≠ 0 := by
    exact_mod_cast (Nat.Prime.pos (Fact.out : Nat.Prime p)).ne'
  field_simp
  ring


omit [CharP F p] in
/-- `rhoRight` is a rational-exponent radius. -/
theorem rhoRight_eq_vpiQ (ϖ'' : PseudoUniformizer F) (a b : ℕ) :
    rhoRight p F ϖ'' a b = vpiQ p F ϖ'' ((b : ℚ) / (a : ℚ)) := by
  rw [rhoRight, vpiQ]
  congr 1
  push_cast
  rfl

/-- Transport a subring equality of `B^I`'s to a ring equivalence. -/
noncomputable def biSubringCongr {ρ₁ ρ₂ : NNReal}
    {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {S T : Subring ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))}
    (h : S = T) : ↥S ≃+* ↥T := by
  subst h
  exact RingEquiv.refl _

theorem biSubringCongr_continuous {ρ₁ ρ₂ : NNReal}
    {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {S T : Subring ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))}
    (h : S = T) : Continuous (biSubringCongr p F h) := by
  subst h
  exact continuous_id

/-- The ID2d comparison instantiated at the twisted uniformizer (step 1). -/
noncomputable def chartEquivStep1 (n : ℕ) :
    presheafValue (chartData p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1)
      ≃+* ↥(BISub p F (PseudoUniformizer.frobRoot p F ϖ n)
          (vpi_pos p F (PseudoUniformizer.frobRoot p F ϖ n))
          (perfectoidValuation_toOF_lt_one p F (PseudoUniformizer.frobRoot p F ϖ n))
          (rhoRight_pos p F (PseudoUniformizer.frobRoot p F ϖ n) p 1)
          (rhoRight_lt_one p F (PseudoUniformizer.frobRoot p F ϖ n) p 1
            (Nat.Prime.pos (Fact.out : Nat.Prime p)) one_pos)) :=
  presheafChartRingEquivBISub p F (PseudoUniformizer.frobRoot p F ϖ n)
    (hρ₁0 := vpi_pos p F (PseudoUniformizer.frobRoot p F ϖ n))
    (hρ₁1 := perfectoidValuation_toOF_lt_one p F
      (PseudoUniformizer.frobRoot p F ϖ n))
    (hρ₂0 := rhoRight_pos p F (PseudoUniformizer.frobRoot p F ϖ n) p 1)
    (hρ₂1 := rhoRight_lt_one p F (PseudoUniformizer.frobRoot p F ϖ n) p 1
      (Nat.Prime.pos (Fact.out : Nat.Prime p)) one_pos)
    p 1 (Nat.Prime.pos (Fact.out : Nat.Prime p)) one_pos
    (Nat.Prime.one_le (Fact.out : Nat.Prime p)) rfl
    (by rw [rhoRight_pow_exact p F (PseudoUniformizer.frobRoot p F ϖ n) p 1
          (Nat.Prime.pos (Fact.out : Nat.Prime p)), pow_one])

/-- Radius rewriting to `vpiQ`-form in the twisted uniformizer (step 2). -/
noncomputable def chartEquivStep2 (n : ℕ) :
    ↥(BISub p F (PseudoUniformizer.frobRoot p F ϖ n)
        (vpi_pos p F (PseudoUniformizer.frobRoot p F ϖ n))
        (perfectoidValuation_toOF_lt_one p F (PseudoUniformizer.frobRoot p F ϖ n))
        (rhoRight_pos p F (PseudoUniformizer.frobRoot p F ϖ n) p 1)
        (rhoRight_lt_one p F (PseudoUniformizer.frobRoot p F ϖ n) p 1
          (Nat.Prime.pos (Fact.out : Nat.Prime p)) one_pos))
      ≃+* ↥(BISub p F (PseudoUniformizer.frobRoot p F ϖ n)
          (vpiQ_pos p F ϖ (1 / (p ^ n : ℚ)))
          (vpiQ_lt_one p F ϖ (invPowQ_pos p n))
          (vpiQ_pos p F ϖ (1 / (p ^ (n + 1) : ℚ)))
          (vpiQ_lt_one p F ϖ (invPowQ_pos p (n + 1)))) :=
  biCongr p F (PseudoUniformizer.frobRoot p F ϖ n)
    (by rw [← vpiQ_frobRoot_one p F ϖ n, vpiQ_one])
    (by rw [← vpiQ_frobRoot_invP p F ϖ n, rhoRight_eq_vpiQ]
        norm_num)

/-- Uniformizer-invariance transport (step 3). -/
noncomputable def chartEquivStep3 (n : ℕ) :
    ↥(BISub p F (PseudoUniformizer.frobRoot p F ϖ n)
        (vpiQ_pos p F ϖ (1 / (p ^ n : ℚ)))
        (vpiQ_lt_one p F ϖ (invPowQ_pos p n))
        (vpiQ_pos p F ϖ (1 / (p ^ (n + 1) : ℚ)))
        (vpiQ_lt_one p F ϖ (invPowQ_pos p (n + 1))))
      ≃+* ↥(BIQ p F ϖ (1 / (p ^ n : ℚ)) (1 / (p ^ (n + 1) : ℚ))
          (invPowQ_pos p n) (invPowQ_pos p (n + 1))) :=
  biSubringCongr p F
    (BISub_twist p F ϖ
      (hk := pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) n)
      (teichPi_frobRoot_pow p F ϖ n))

/-- **The chart ring of the `n`-th Big window IS `BIQ (1/p^n) (1/p^{n+1})`**:
the ID2d comparison at the twisted uniformizer, the radius rewriting, and the
uniformizer-invariance of `B^I`, composed. -/
noncomputable def chartRingEquivBIQ (n : ℕ) :
    presheafValue (chartData p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1)
      ≃+* ↥(BIQ p F ϖ (1 / (p ^ n : ℚ)) (1 / (p ^ (n + 1) : ℚ))
          (invPowQ_pos p n) (invPowQ_pos p (n + 1))) :=
  (chartEquivStep1 p F ϖ n).trans
    ((chartEquivStep2 p F ϖ n).trans (chartEquivStep3 p F ϖ n))

theorem biCongr_symm_continuous (h₁ : ρ₁ = ρ₁') (h₂ : ρ₂ = ρ₂')
    {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {hρ₁0' : 0 < ρ₁'} {hρ₁1' : ρ₁' < 1} {hρ₂0' : 0 < ρ₂'} {hρ₂1' : ρ₂' < 1} :
    Continuous (biCongr p F ϖ h₁ h₂ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) (hρ₁0' := hρ₁0') (hρ₁1' := hρ₁1')
      (hρ₂0' := hρ₂0') (hρ₂1' := hρ₂1')).symm := by
  subst h₁
  subst h₂
  exact continuous_id

theorem biSubringCongr_symm_continuous
    {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {S T : Subring ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))}
    (h : S = T) : Continuous (biSubringCongr p F h).symm := by
  subst h
  exact continuous_id

theorem chartEquivStep1_continuous (n : ℕ) :
    Continuous (chartEquivStep1 p F ϖ n) := by
  rw [chartEquivStep1]
  exact presheafChartRingEquivBISub_continuous p F
    (PseudoUniformizer.frobRoot p F ϖ n) p 1
    (Nat.Prime.pos (Fact.out : Nat.Prime p)) one_pos
    (Nat.Prime.one_le (Fact.out : Nat.Prime p)) rfl
    (by rw [rhoRight_pow_exact p F (PseudoUniformizer.frobRoot p F ϖ n) p 1
          (Nat.Prime.pos (Fact.out : Nat.Prime p)), pow_one])

theorem chartEquivStep1_symm_continuous (n : ℕ) :
    Continuous (chartEquivStep1 p F ϖ n).symm := by
  rw [chartEquivStep1]
  exact presheafChartRingEquivBISub_symm_continuous p F
    (PseudoUniformizer.frobRoot p F ϖ n) p 1
    (Nat.Prime.pos (Fact.out : Nat.Prime p)) one_pos
    (Nat.Prime.one_le (Fact.out : Nat.Prime p)) rfl
    (by rw [rhoRight_pow_exact p F (PseudoUniformizer.frobRoot p F ϖ n) p 1
          (Nat.Prime.pos (Fact.out : Nat.Prime p)), pow_one])

theorem chartEquivStep2_continuous (n : ℕ) :
    Continuous (chartEquivStep2 p F ϖ n) := by
  rw [chartEquivStep2]
  exact biCongr_continuous p F (PseudoUniformizer.frobRoot p F ϖ n) _ _

theorem powQ_pos (m : ℕ) : (0 : ℚ) < (p ^ m : ℚ) := by
  have hp : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  positivity

theorem powQ_div_pos (m : ℕ) : (0 : ℚ) < (p ^ m : ℚ) / (p : ℚ) := by
  have hp : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  positivity

omit [CharP F p] in
theorem vpiQ_pPow_one (m : ℕ) :
    vpiQ p F (PseudoUniformizer.pPow F ϖ (p ^ m)
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1
      = vpiQ p F ϖ ((p ^ m : ℚ)) := by
  rw [vpiQ_pPow p F ϖ (p ^ m) (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m) 1]
  congr 1
  push_cast
  ring

omit [CharP F p] in
theorem vpiQ_pPow_invP (m : ℕ) :
    vpiQ p F (PseudoUniformizer.pPow F ϖ (p ^ m)
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) (1 / (p : ℚ))
      = vpiQ p F ϖ ((p ^ m : ℚ) / (p : ℚ)) := by
  rw [vpiQ_pPow p F ϖ (p ^ m)
    (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m) (1 / (p : ℚ))]
  congr 1
  push_cast
  ring

/-- The `p^m`-th power uniformizer (abbreviation for the negative-side
charts). -/
noncomputable def pPowM (m : ℕ) : PseudoUniformizer F :=
  PseudoUniformizer.pPow F ϖ (p ^ m)
    (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)

theorem teichPi_pPowM (m : ℕ) :
    teichPi p F ϖ ^ p ^ m = teichPi p F (pPowM p F ϖ m) :=
  (teichPi_pPow p F ϖ (p ^ m)
    (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)).symm

theorem vpiQ_pPowM_one (m : ℕ) :
    vpiQ p F (pPowM p F ϖ m) 1 = vpiQ p F ϖ ((p ^ m : ℚ)) :=
  vpiQ_pPow_one p F ϖ m

theorem vpiQ_pPowM_invP (m : ℕ) :
    vpiQ p F (pPowM p F ϖ m) (1 / (p : ℚ))
      = vpiQ p F ϖ ((p ^ m : ℚ) / (p : ℚ)) :=
  vpiQ_pPow_invP p F ϖ m

/-- The ID2d comparison instantiated at the power uniformizer (negative side,
step 1). -/
noncomputable def chartEquivStep1Neg (m : ℕ) :
    presheafValue (chartData p F (pPowM p F ϖ m) 1 1 p 1)
      ≃+* ↥(BISub p F (pPowM p F ϖ m)
          (vpi_pos p F (pPowM p F ϖ m))
          (perfectoidValuation_toOF_lt_one p F (pPowM p F ϖ m))
          (rhoRight_pos p F (pPowM p F ϖ m) p 1)
          (rhoRight_lt_one p F (pPowM p F ϖ m) p 1
            (Nat.Prime.pos (Fact.out : Nat.Prime p)) one_pos)) :=
  presheafChartRingEquivBISub p F (pPowM p F ϖ m)
    (hρ₁0 := vpi_pos p F (pPowM p F ϖ m))
    (hρ₁1 := perfectoidValuation_toOF_lt_one p F (pPowM p F ϖ m))
    (hρ₂0 := rhoRight_pos p F (pPowM p F ϖ m) p 1)
    (hρ₂1 := rhoRight_lt_one p F (pPowM p F ϖ m) p 1
      (Nat.Prime.pos (Fact.out : Nat.Prime p)) one_pos)
    p 1 (Nat.Prime.pos (Fact.out : Nat.Prime p)) one_pos
    (Nat.Prime.one_le (Fact.out : Nat.Prime p)) rfl
    (by rw [rhoRight_pow_exact p F (pPowM p F ϖ m) p 1
          (Nat.Prime.pos (Fact.out : Nat.Prime p)), pow_one])

/-- Radius rewriting (negative side, step 2). -/
noncomputable def chartEquivStep2Neg (m : ℕ) :
    ↥(BISub p F (pPowM p F ϖ m)
        (vpi_pos p F (pPowM p F ϖ m))
        (perfectoidValuation_toOF_lt_one p F (pPowM p F ϖ m))
        (rhoRight_pos p F (pPowM p F ϖ m) p 1)
        (rhoRight_lt_one p F (pPowM p F ϖ m) p 1
          (Nat.Prime.pos (Fact.out : Nat.Prime p)) one_pos))
      ≃+* ↥(BISub p F (pPowM p F ϖ m)
          (vpiQ_pos p F ϖ ((p ^ m : ℚ)))
          (vpiQ_lt_one p F ϖ (powQ_pos p m))
          (vpiQ_pos p F ϖ ((p ^ m : ℚ) / (p : ℚ)))
          (vpiQ_lt_one p F ϖ (powQ_div_pos p m))) :=
  biCongr p F (pPowM p F ϖ m)
    (by rw [← vpiQ_pPowM_one p F ϖ m, vpiQ_one])
    (by rw [← vpiQ_pPowM_invP p F ϖ m, rhoRight_eq_vpiQ]
        norm_num)

/-- Uniformizer-invariance transport (negative side, step 3). -/
noncomputable def chartEquivStep3Neg (m : ℕ) :
    ↥(BISub p F (pPowM p F ϖ m)
        (vpiQ_pos p F ϖ ((p ^ m : ℚ)))
        (vpiQ_lt_one p F ϖ (powQ_pos p m))
        (vpiQ_pos p F ϖ ((p ^ m : ℚ) / (p : ℚ)))
        (vpiQ_lt_one p F ϖ (powQ_div_pos p m)))
      ≃+* ↥(BIQ p F ϖ ((p ^ m : ℚ)) ((p ^ m : ℚ) / (p : ℚ))
          (powQ_pos p m) (powQ_div_pos p m)) :=
  biSubringCongr p F
    (BISub_twist p F (pPowM p F ϖ m)
      (ϖ' := ϖ) (hk := pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)
      (teichPi_pPowM p F ϖ m)).symm

/-- **The chart ring of the `(-m)`-th Big window IS `BIQ (p^m) (p^{m-1})`**
(negative side). -/
noncomputable def chartRingEquivBIQNeg (m : ℕ) :
    presheafValue (chartData p F (pPowM p F ϖ m) 1 1 p 1)
      ≃+* ↥(BIQ p F ϖ ((p ^ m : ℚ)) ((p ^ m : ℚ) / (p : ℚ))
          (powQ_pos p m) (powQ_div_pos p m)) :=
  (chartEquivStep1Neg p F ϖ m).trans
    ((chartEquivStep2Neg p F ϖ m).trans (chartEquivStep3Neg p F ϖ m))

/-- The subring-equality transport preserves the ambient value. -/
theorem biSubringCongr_coe_val
    {S T : Subring ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))}
    (h : S = T) (z : ↥S) :
    ((biSubringCongr p F h z : ↥T)
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = ((z : ↥S) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := by
  subst h
  rfl

/-- The window exponents decrease. -/
theorem invPow_succ_lt (n : ℕ) : (1 / (p ^ (n + 1) : ℚ)) < 1 / (p ^ n : ℚ) := by
  have hp : (1 : ℚ) < p := by
    exact_mod_cast Nat.Prime.one_lt (Fact.out : Nat.Prime p)
  have h0 : (0 : ℚ) < (p ^ n : ℚ) := by positivity
  have h1 : (0 : ℚ) < (p ^ (n + 1) : ℚ) := by positivity
  refine one_div_lt_one_div_of_lt h0 ?_
  rw [pow_succ]
  nlinarith

/-- **The restriction hom from the `n`-th window chart to a rational
sub-interval** (route (c)): the chart identification composed with the
decreasing-orientation `BIQ`-restriction. -/
noncomputable def windowResBIQ (n : ℕ) (r₁ r₂ : ℚ) (hr₁ : 0 < r₁)
    (hr₂ : 0 < r₂)
    (hr₁m : 1 / (p ^ (n + 1) : ℚ) ≤ r₁ ∧ r₁ ≤ 1 / (p ^ n : ℚ))
    (hr₂m : 1 / (p ^ (n + 1) : ℚ) ≤ r₂ ∧ r₂ ≤ 1 / (p ^ n : ℚ)) :
    presheafValue (chartData p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1)
      →+* ↥(BIQ p F ϖ r₁ r₂ hr₁ hr₂) :=
  (biResQ p F ϖ (1 / (p ^ n : ℚ)) (1 / (p ^ (n + 1) : ℚ)) r₁ r₂
      (invPowQ_pos p n) (invPowQ_pos p (n + 1)) hr₁ hr₂
      (invPow_succ_lt p n) hr₁m hr₂m).comp
    (chartRingEquivBIQ p F ϖ n).toRingHom

/-- The negative-side window exponents decrease. -/
theorem powQ_div_lt (m : ℕ) : (p ^ m : ℚ) / (p : ℚ) < (p ^ m : ℚ) := by
  have hp : (1 : ℚ) < p := by
    exact_mod_cast Nat.Prime.one_lt (Fact.out : Nat.Prime p)
  have h0 : (0 : ℚ) < (p ^ m : ℚ) := by positivity
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- **The restriction hom from the `(-m)`-th window chart to a rational
sub-interval** (route (c), negative side). -/
noncomputable def windowResBIQNeg (m : ℕ) (r₁ r₂ : ℚ) (hr₁ : 0 < r₁)
    (hr₂ : 0 < r₂)
    (hr₁m : (p ^ m : ℚ) / (p : ℚ) ≤ r₁ ∧ r₁ ≤ (p ^ m : ℚ))
    (hr₂m : (p ^ m : ℚ) / (p : ℚ) ≤ r₂ ∧ r₂ ≤ (p ^ m : ℚ)) :
    presheafValue (chartData p F (pPowM p F ϖ m) 1 1 p 1)
      →+* ↥(BIQ p F ϖ r₁ r₂ hr₁ hr₂) :=
  (biResQ p F ϖ ((p ^ m : ℚ)) ((p ^ m : ℚ) / (p : ℚ)) r₁ r₂
      (powQ_pos p m) (powQ_div_pos p m) hr₁ hr₂
      (powQ_div_lt p m) hr₁m hr₂m).comp
    (chartRingEquivBIQNeg p F ϖ m).toRingHom

end FarguesFontaine

end
