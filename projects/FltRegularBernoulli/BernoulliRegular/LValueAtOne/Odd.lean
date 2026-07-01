module

public import BernoulliRegular.LValueAtOne.Sine

/-!
# Odd-character `L(1, χ)` formulas

This file packages the odd `L(0, χ)` and `L(1, χ)` evaluations from the
sine-side boundary-value identities.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace BernoulliRegular

section LValueAtOne

variable (p : ℕ) [hp : Fact p.Prime]

/-- Rewrite `L(0, χ)` for an odd character as a finite sum of the values
`sinZeta (a / p) 1`. -/
theorem odd_LFunction_zero_eq_pi_inv_mul_sum_sinZeta_one
    {χ : DirichletCharacter ℂ p} (hχ_odd : χ.Odd) :
    DirichletCharacter.LFunction χ 0 =
      (((Real.pi : ℝ) : ℂ)⁻¹) *
        ∑ a : ZMod p, χ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 := by
  have hs : ∀ n : ℕ, (1 : ℂ) ≠ -n := by
    intro n h
    have hre : (1 : ℝ) = -(n : ℝ) := by
      simpa using congrArg Complex.re h
    nlinarith
  have hχ_odd_fun : Function.Odd (fun a : ZMod p => χ a) :=
    fun a => DirichletCharacter.Odd.eval_neg (ψ := χ) a hχ_odd
  rw [DirichletCharacter.LFunction, ZMod.LFunction_def_odd hχ_odd_fun]
  simp only [neg_zero, Complex.cpow_zero, one_mul]
  calc
    ∑ a : ZMod p, χ a * HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle a) 0
        = ∑ a : ZMod p,
            χ a * ((((Real.pi : ℝ) : ℂ)⁻¹) * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1) := by
              refine Finset.sum_congr rfl fun a _ => ?_
              have hvalue := HurwitzZeta.hurwitzZetaOdd_one_sub
                (s := (1 : ℂ)) (a := ZMod.toAddCircle a) hs
              have hsin : Complex.sin (((Real.pi : ℝ) : ℂ) * (2⁻¹ : ℂ)) = 1 := by
                simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
                  using Complex.sin_pi_div_two
              simpa [Complex.Gamma_one, Complex.cpow_neg_one, hsin, mul_assoc, mul_left_comm,
                mul_comm, div_eq_mul_inv] using congrArg (fun z : ℂ => χ a * z) hvalue
    _ = ∑ a : ZMod p,
          (((Real.pi : ℝ) : ℂ)⁻¹) * (χ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1) := by
            refine Finset.sum_congr rfl fun a _ => by ring
    _ = (((Real.pi : ℝ) : ℂ)⁻¹) *
          ∑ a : ZMod p, χ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 := by
            rw [Finset.mul_sum]

/-- The odd special value `L(0, χ) = -B_{1,χ}` follows from the classical
boundary-value formula `sinZeta (a / p) 1 = π (1 / 2 - a / p)` for
nonzero residues `a`. -/
theorem odd_LFunction_zero_eq_neg_BernoulliGen_one_of_sinZeta_one_formula
    {χ : DirichletCharacter ℂ p} (hχ_odd : χ.Odd) (hχ_ne_one : χ ≠ 1)
    (hsin : ∀ a : ZMod p, a ≠ 0 →
      HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 =
        (((Real.pi : ℝ) : ℂ) * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ)))) :
    DirichletCharacter.LFunction χ 0 = -BernoulliGen χ 1 := by
  have hp_ne_one : p ≠ 1 := hp.out.ne_one
  have hχ_zero : χ 0 = 0 := χ.map_zero' hp_ne_one
  have hsum_zero : ∑ a : ZMod p, χ a = 0 := MulChar.sum_eq_zero_of_ne_one hχ_ne_one
  have hpi : (((Real.pi : ℝ) : ℂ)⁻¹) * (((Real.pi : ℝ) : ℂ)) = 1 := by
    field_simp [Real.pi_ne_zero]
  calc
    DirichletCharacter.LFunction χ 0
        = (((Real.pi : ℝ) : ℂ)⁻¹) *
            ∑ a : ZMod p, χ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 :=
          odd_LFunction_zero_eq_pi_inv_mul_sum_sinZeta_one (p := p) hχ_odd
    _ = (((Real.pi : ℝ) : ℂ)⁻¹) *
          ∑ a : ZMod p, χ a * ((((Real.pi : ℝ) : ℂ) * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ)))) := by
            refine congrArg (fun z : ℂ => (((Real.pi : ℝ) : ℂ)⁻¹) * z) ?_
            refine Finset.sum_congr rfl fun a _ => ?_
            rcases eq_or_ne a 0 with rfl | ha
            · simp [hχ_zero]
            · rw [hsin a ha]
    _ = ∑ a : ZMod p, χ a * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          calc
            (((Real.pi : ℝ) : ℂ)⁻¹) *
                (χ a * (((Real.pi : ℝ) : ℂ) * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ))))
                = ((((Real.pi : ℝ) : ℂ)⁻¹) * (((Real.pi : ℝ) : ℂ))) *
                    (χ a * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ))) := by
                      ring
            _ = χ a * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ)) := by
                  rw [hpi, one_mul]
    _ = -∑ a : ZMod p, χ a * ((a.val : ℂ) / (p : ℂ)) := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
          have hconst : ∑ a : ZMod p, χ a * (1 / 2 : ℂ) = 0 := by
            rw [← Finset.sum_mul, hsum_zero, zero_mul]
          rw [hconst, zero_sub]
    _ = -BernoulliGen χ 1 := by
          congr 1
          rw [BernoulliGen_one_of_ne_one (R := ℂ) (N := p) (χ := χ) hχ_ne_one]
          refine Finset.sum_congr rfl fun a _ => ?_
          congr 1
          change (a.val : ℂ) / (p : ℂ) = ((((a.val : ℚ) / p : ℚ)) : ℂ)
          rw [Rat.cast_div]
          push_cast
          rfl

/-- **T021b / T021b1**: Odd special value `L(0, χ) = -BernoulliGen χ 1` for
odd nontrivial Dirichlet characters modulo `p`, packaged independently of the
endpoint scaffolding by feeding the endpoint identity
`sinZeta_toAddCircle_one_eq_boundary` into the generic reduction lemma. -/
theorem odd_LFunction_zero_eq_neg_BernoulliGen_one
    {χ : DirichletCharacter ℂ p} (hχ_odd : χ.Odd) (hχ_ne_one : χ ≠ 1) :
    DirichletCharacter.LFunction χ 0 = -BernoulliGen χ 1 :=
  odd_LFunction_zero_eq_neg_BernoulliGen_one_of_sinZeta_one_formula (p := p)
    hχ_odd hχ_ne_one
    (fun _ ha => sinZeta_toAddCircle_one_eq_boundary (p := p) ha)

/-- **T021 / T021c / T021c1**: `L(1, χ)` for odd primitive characters
modulo `p`. Closes the full odd-side formula by applying the functional-equation
reduction `odd_LFunction_one_eq_oddLValueRhs_of_LFunction_inv_zero` to the
packaged odd special-value theorem at `χ⁻¹`. -/
theorem odd_LFunction_one_eq_oddLValueRhs
    {χ : DirichletCharacter ℂ p} (hχ_prim : χ.IsPrimitive) (hχ_odd : χ.Odd)
    (hχ_ne_one : χ ≠ 1) :
    DirichletCharacter.LFunction χ 1 = oddLValueRhs p χ := by
  have hχinv_odd : (χ⁻¹).Odd := by
    rw [DirichletCharacter.Odd] at hχ_odd ⊢
    rw [MulChar.inv_apply_eq_inv', hχ_odd]
    norm_num
  have hχinv_ne_one : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ_ne_one
    calc χ = χ⁻¹⁻¹ := (inv_inv χ).symm
      _ = (1 : DirichletCharacter ℂ p)⁻¹ := by rw [h]
      _ = 1 := inv_one
  exact odd_LFunction_one_eq_oddLValueRhs_of_LFunction_inv_zero (p := p) hχ_prim hχ_odd
    (odd_LFunction_zero_eq_neg_BernoulliGen_one (p := p) hχinv_odd hχinv_ne_one)

end LValueAtOne

end BernoulliRegular
