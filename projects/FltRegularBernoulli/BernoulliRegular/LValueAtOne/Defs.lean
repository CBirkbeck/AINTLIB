module

public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import BernoulliRegular.BernoulliGeneralized

/-!
# Basic `L(1, χ)` definitions

This file packages the canonical odd/even right-hand sides together with the
functional-equation reduction for the odd formula.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Topology

namespace BernoulliRegular

section LValueAtOne

variable (p : ℕ) [hp : Fact p.Prime]

/-- T021 right-hand side: the value predicted for `L(1, χ)` when `χ` is odd
primitive modulo `p`. -/
noncomputable def oddLValueRhs (χ : DirichletCharacter ℂ p) : ℂ :=
  ((((Real.pi : ℝ) : ℂ) * Complex.I) * gaussSum χ (ZMod.stdAddChar (N := p)) / (p : ℂ)) *
    BernoulliGen χ⁻¹ 1

/-- The logarithmic sum appearing in the corrected even-character formula at
`s = 1`. -/
noncomputable def evenLValueLogSum (χ : DirichletCharacter ℂ p) : ℂ :=
  ∑ a : ZMod p, χ⁻¹ a * ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ)

/-- T022 right-hand side: the value predicted for `L(1, χ)` when `χ` is even
primitive modulo `p`. -/
noncomputable def evenLValueRhs (χ : DirichletCharacter ℂ p) : ℂ :=
  -(gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹ * evenLValueLogSum p χ

/-- Functional-equation reduction of the odd `L(1, χ)` formula to the special
value formula for `L(0, χ⁻¹)`. -/
theorem odd_LFunction_one_eq_oddLValueRhs_of_LFunction_inv_zero
    {χ : DirichletCharacter ℂ p} (hχ_prim : χ.IsPrimitive) (hχ_odd : χ.Odd)
    (hχ0 : DirichletCharacter.LFunction χ⁻¹ 0 = -BernoulliGen χ⁻¹ 1) :
    DirichletCharacter.LFunction χ 1 = oddLValueRhs p χ := by
  have hp_ne_one : p ≠ 1 := hp.out.ne_one
  have hp_ne_zero : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  have hχinv_odd : (χ⁻¹).Odd := by
    rw [DirichletCharacter.Odd] at hχ_odd ⊢
    rw [MulChar.inv_apply_eq_inv', hχ_odd]
    norm_num
  have hL1 : DirichletCharacter.LFunction χ 1 =
      ((Real.pi : ℝ) : ℂ) * DirichletCharacter.completedLFunction χ 1 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ := χ) (s := 1)
        (Or.inl one_ne_zero), hχ_odd.gammaFactor_def]
    simp [Complex.Gammaℝ_def, Complex.Gamma_one, Complex.cpow_neg_one, mul_comm]
  have hL0 : DirichletCharacter.completedLFunction χ⁻¹ 0 =
      DirichletCharacter.LFunction χ⁻¹ 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ := χ⁻¹) (s := 0)
        (Or.inr hp_ne_one), hχinv_odd.gammaFactor_def]
    simp
  have hfe := DirichletCharacter.IsPrimitive.completedLFunction_one_sub (χ := χ) hχ_prim (0 : ℂ)
  rw [DirichletCharacter.rootNumber, if_neg hχ_odd.not_even, pow_one,
    ← mul_comm_div, ← mul_comm_div, ← Complex.cpow_sub _ _ hp_ne_zero, sub_sub, add_halves,
    hL0, hχ0] at hfe
  have hfe' : DirichletCharacter.completedLFunction χ 1 =
      (p : ℂ) ^ (-1 : ℂ) * Complex.I * gaussSum χ (ZMod.stdAddChar (N := p)) *
        BernoulliGen χ⁻¹ 1 := by
    simpa using hfe
  calc
    DirichletCharacter.LFunction χ 1
        = ((Real.pi : ℝ) : ℂ) * DirichletCharacter.completedLFunction χ 1 := hL1
    _ = ((Real.pi : ℝ) : ℂ) *
          (((p : ℂ) ^ (-1 : ℂ)) * Complex.I * gaussSum χ (ZMod.stdAddChar (N := p)) *
            BernoulliGen χ⁻¹ 1) := by rw [hfe']
    _ = ((((Real.pi : ℝ) : ℂ) * Complex.I) * gaussSum χ (ZMod.stdAddChar (N := p)) / (p : ℂ)) *
          BernoulliGen χ⁻¹ 1 := by
      simp [Complex.cpow_neg_one, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ = oddLValueRhs p χ := rfl

end LValueAtOne

end BernoulliRegular
