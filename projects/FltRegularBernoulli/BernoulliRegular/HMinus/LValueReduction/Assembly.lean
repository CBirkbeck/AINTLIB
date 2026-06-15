module

public import BernoulliRegular.HMinus.LValueReduction.LValues

/-!
# Generic `hMinus` assembly lemmas

This file packages the algebraic reduction from residue and `hPlus`
factorizations to the odd Bernoulli-product formula for `hMinus`.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators

namespace BernoulliRegular

section Assembly

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]

/-- Once the residues of `ζ_K` and `ζ_{K⁺}` are expressed in a common
even-part normalization, the exact odd-side coefficient is the quotient of the
cyclotomic and maximal-real-subfield class-number factors. This isolates the
coefficient target needed before any Gauss-product simplification. -/
theorem hMinus_LValue_formula_of_residue_and_Kplus_residue
    (hp_odd' : p ≠ 2)
    {KplusResidue : ℂ}
    (hres :
      ((NumberField.dedekindZeta_residue K : ℝ) : ℂ) =
        KplusResidue *
          Finset.prod (oddCharacters (p := p))
            (fun χ => DirichletCharacter.LFunction χ 1))
    (hresPlus :
      ((NumberField.dedekindZeta_residue (NumberField.maximalRealSubfield K) : ℝ) : ℂ) =
        KplusResidue) :
    ((hMinus K : ℕ) : ℂ) =
      cyclotomicRelativeLValueCoefficient (p := p) (K := K) *
        Finset.prod (oddCharacters (p := p))
          (fun χ => DirichletCharacter.LFunction χ 1) := by
  let O : ℂ :=
    Finset.prod (oddCharacters (p := p)) (fun χ => DirichletCharacter.LFunction χ 1)
  have hh : ((h K : ℕ) : ℂ) = ((hPlus K : ℕ) : ℂ) * ((hMinus K : ℕ) : ℂ) := by
    exact_mod_cast (h_eq_hPlus_mul_hMinus (p := p) (hp_odd := hp_odd') (K := K))
  have hhplus_ne : ((hPlus K : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card
      (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
  have hmain : ((hPlus K : ℕ) : ℂ) * ((hMinus K : ℕ) : ℂ) =
      ((hPlus K : ℕ) : ℂ) *
        (cyclotomicRelativeLValueCoefficient (p := p) (K := K) * O) := by
    rw [← hh,
      h_formula_cyclotomic_complex (p := p) (K := K) hp_odd',
      hres,
      hPlus_formula_complex (K := K),
      hresPlus]
    simp [O, cyclotomicRelativeLValueCoefficient]
    field_simp [maximalRealSubfieldClassNumberFactor_ne_zero (K := K)]
  exact mul_left_cancel₀ hhplus_ne hmain

omit [IsCyclotomicExtension {p} ℚ K] in
/-- To finish `hMinus_formula`, it is enough to know the intermediate odd
`L`-value formula together with the corresponding product formula for the
Gauss-sum factors. This packages the final algebraic rewrite from the
`L(1, χ)` stage to the Bernoulli-product stage. -/
theorem hMinus_formula_of_LValue_formula_and_gauss_product
    {coefficient : ℂ}
    (hLValues :
      ((hMinus K : ℕ) : ℂ) =
        coefficient *
          Finset.prod (oddCharacters (p := p))
            (fun χ => DirichletCharacter.LFunction χ 1))
    (hgauss :
      coefficient *
          Finset.prod (oddCharacters (p := p)) (fun χ =>
            ((((Real.pi : ℝ) : ℂ) * Complex.I) * gaussSum χ (ZMod.stdAddChar (N := p)) / (p : ℂ))) =
        (2 * p : ℂ) *
          Finset.prod (oddCharacters (p := p))
            (fun _ : DirichletCharacter ℂ p => (-(1 / 2 : ℂ)))) :
    ((hMinus K : ℕ) : ℂ) =
      (2 * p : ℂ) *
        Finset.prod (oddCharacters (p := p)) (fun χ =>
          (-(1 / 2 : ℂ)) * BernoulliGen χ⁻¹ 1) := by
  have hodd :
      Finset.prod (oddCharacters (p := p)) (fun χ => DirichletCharacter.LFunction χ 1) =
        Finset.prod (oddCharacters (p := p)) (fun χ => oddLValueRhs p χ) := by
    simpa [oddLProduct] using oddLProduct_one_eq_prod_oddLValueRhs (p := p)
  rw [hLValues, hodd, oddLValueRhs_product_eq_gauss_product_mul_bernoulli_product (p := p)]
  calc
    coefficient *
        (Finset.prod (oddCharacters (p := p)) (fun χ =>
            ((((Real.pi : ℝ) : ℂ) * Complex.I) * gaussSum χ (ZMod.stdAddChar (N := p)) / (p : ℂ))) *
          Finset.prod (oddCharacters (p := p)) (fun χ => BernoulliGen χ⁻¹ 1)) =
      (coefficient *
          Finset.prod (oddCharacters (p := p)) (fun χ =>
            ((((Real.pi : ℝ) : ℂ) * Complex.I) *
              gaussSum χ (ZMod.stdAddChar (N := p)) / (p : ℂ)))) *
        Finset.prod (oddCharacters (p := p)) (fun χ => BernoulliGen χ⁻¹ 1) := by
          ring
    _ =
      ((2 * p : ℂ) *
          Finset.prod (oddCharacters (p := p))
            (fun _ : DirichletCharacter ℂ p => (-(1 / 2 : ℂ)))) *
        Finset.prod (oddCharacters (p := p)) (fun χ => BernoulliGen χ⁻¹ 1) := by
          rw [hgauss]
    _ =
      (2 * p : ℂ) *
        (Finset.prod (oddCharacters (p := p))
            (fun _ : DirichletCharacter ℂ p => (-(1 / 2 : ℂ))) *
          Finset.prod (oddCharacters (p := p)) (fun χ => BernoulliGen χ⁻¹ 1)) := by
            ring
    _ =
      (2 * p : ℂ) *
        Finset.prod (oddCharacters (p := p)) (fun χ =>
          (-(1 / 2 : ℂ)) * BernoulliGen χ⁻¹ 1) := by
            rw [← Finset.prod_mul_distrib]

/-- Once the cyclotomic residue is identified with the even/odd `L(1, χ)`
product and the even part is matched with the `K⁺` side of the analytic class
number formula, the quotient computation for `h⁻` is formal. This packages the
result in the exact `hLValues` shape consumed by
`hMinus_formula_of_LValue_formula_and_gauss_product`. -/
theorem hMinus_LValue_formula_of_residue_and_hPlus
    (hp_odd' : p ≠ 2)
    {coefficient plusFactor : ℂ}
    (hh_formula :
      ((h K : ℕ) : ℂ) =
        ((NumberField.dedekindZeta_residue K : ℝ) : ℂ) * (coefficient * plusFactor))
    (hres :
      ((NumberField.dedekindZeta_residue K : ℝ) : ℂ) =
        Finset.prod (evenNontrivialCharacters (p := p)) (fun χ => evenLValueRhs p χ) *
          Finset.prod (oddCharacters (p := p)) (fun χ => DirichletCharacter.LFunction χ 1))
    (hplus :
      ((hPlus K : ℕ) : ℂ) =
        plusFactor * Finset.prod (evenNontrivialCharacters (p := p)) (fun χ => evenLValueRhs p χ)) :
    ((hMinus K : ℕ) : ℂ) =
      coefficient *
        Finset.prod (oddCharacters (p := p)) (fun χ => DirichletCharacter.LFunction χ 1) := by
  let O : ℂ :=
    Finset.prod (oddCharacters (p := p)) (fun χ => DirichletCharacter.LFunction χ 1)
  have hh : ((h K : ℕ) : ℂ) = ((hPlus K : ℕ) : ℂ) * ((hMinus K : ℕ) : ℂ) := by
    exact_mod_cast (h_eq_hPlus_mul_hMinus (p := p) (hp_odd := hp_odd') (K := K))
  have hhplus_ne : ((hPlus K : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card
      (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
  have hmain : ((hPlus K : ℕ) : ℂ) * ((hMinus K : ℕ) : ℂ) =
      ((hPlus K : ℕ) : ℂ) * (coefficient * O) := by
    rw [← hh, hh_formula, hres, hplus]
    simp [O]
    ring
  exact mul_left_cancel₀ hhplus_ne hmain

theorem hMinus_LValue_formula_of_residue_and_hPlus_cyclotomic
    (hp_odd' : p ≠ 2)
    (hres :
      ((NumberField.dedekindZeta_residue K : ℝ) : ℂ) =
        Finset.prod (evenNontrivialCharacters (p := p)) (fun χ => evenLValueRhs p χ) *
          Finset.prod (oddCharacters (p := p)) (fun χ => DirichletCharacter.LFunction χ 1))
    (hplus :
      ((hPlus K : ℕ) : ℂ) =
        cyclotomicHPlusFactor (K := K) *
          Finset.prod (evenNontrivialCharacters (p := p)) (fun χ => evenLValueRhs p χ)) :
    ((hMinus K : ℕ) : ℂ) =
      cyclotomicRelativeLValueCoefficient (p := p) (K := K) *
        Finset.prod (oddCharacters (p := p)) (fun χ => DirichletCharacter.LFunction χ 1) := by
  apply hMinus_LValue_formula_of_residue_and_hPlus (p := p) (K := K) hp_odd'
    (coefficient := cyclotomicRelativeLValueCoefficient (p := p) (K := K))
    (plusFactor := cyclotomicHPlusFactor (K := K))
  · calc
      ((h K : ℕ) : ℂ) =
          ((NumberField.dedekindZeta_residue K : ℝ) : ℂ) *
            cyclotomicClassNumberFactor (p := p) (K := K) :=
            h_formula_cyclotomic_complex (p := p) (K := K) hp_odd'
      _ = ((NumberField.dedekindZeta_residue K : ℝ) : ℂ) *
            (cyclotomicRelativeLValueCoefficient (p := p) (K := K) *
              cyclotomicHPlusFactor (K := K)) := by
            rw [cyclotomicClassNumberFactor_eq_relative_coefficient_mul_hPlusFactor
              (p := p) (K := K)]
  · exact hres
  · exact hplus

theorem hMinus_formula_of_residue_and_hPlus_and_gauss
    (hp_odd' : p ≠ 2)
    {coefficient plusFactor : ℂ}
    (hh_formula :
      ((h K : ℕ) : ℂ) =
        ((NumberField.dedekindZeta_residue K : ℝ) : ℂ) * (coefficient * plusFactor))
    (hres :
      ((NumberField.dedekindZeta_residue K : ℝ) : ℂ) =
        Finset.prod (evenNontrivialCharacters (p := p)) (fun χ => evenLValueRhs p χ) *
          Finset.prod (oddCharacters (p := p)) (fun χ => DirichletCharacter.LFunction χ 1))
    (hplus :
      ((hPlus K : ℕ) : ℂ) =
        plusFactor * Finset.prod (evenNontrivialCharacters (p := p)) (fun χ => evenLValueRhs p χ))
    (hgauss :
      coefficient *
          Finset.prod (oddCharacters (p := p)) (fun χ =>
            ((((Real.pi : ℝ) : ℂ) * Complex.I) * gaussSum χ (ZMod.stdAddChar (N := p)) / (p : ℂ))) =
        (2 * p : ℂ) *
          Finset.prod (oddCharacters (p := p))
            (fun _ : DirichletCharacter ℂ p => (-(1 / 2 : ℂ)))) :
    ((hMinus K : ℕ) : ℂ) =
      (2 * p : ℂ) *
        Finset.prod (oddCharacters (p := p)) (fun χ =>
          (-(1 / 2 : ℂ)) * BernoulliGen χ⁻¹ 1) := by
  apply hMinus_formula_of_LValue_formula_and_gauss_product (p := p) (K := K)
    (coefficient := coefficient)
  · exact hMinus_LValue_formula_of_residue_and_hPlus
      (p := p) (K := K) hp_odd' (coefficient := coefficient) hh_formula hres hplus
  · exact hgauss

end Assembly

end BernoulliRegular
