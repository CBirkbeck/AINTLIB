module

public import BernoulliRegular.GaussSum.SignInvariant.BranchChoice
public import BernoulliRegular.GaussSum.SignInvariant.Trace
public import BernoulliRegular.HMinus.LValueReduction.Factors
public import BernoulliRegular.LValueAtOne

/-!
# `L(1, χ)` evaluations for `hMinus`

This file rewrites the odd and even cyclotomic `L`-products at `s = 1` into
the explicit formulas used in the `hMinus` reduction chain.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators

namespace BernoulliRegular

section LValues

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]

/-- Rewrite the odd part of the cyclotomic `L`-product at `s = 1` using the
explicit odd-character evaluation. -/
theorem oddLProduct_one_eq_prod_oddLValueRhs :
    oddLProduct p (1 : ℂ) =
      Finset.prod (oddCharacters (p := p)) fun χ ↦ oddLValueRhs p χ := by
  classical
  unfold oddLProduct
  refine Finset.prod_congr rfl fun χ hχ ↦ ?_
  have hχ_odd : χ.Odd := (Finset.mem_filter.mp hχ).2
  have hχ_ne_one : χ ≠ 1 := by
    rintro rfl
    exact DirichletCharacter.Odd.not_even _ hχ_odd (by
      change (1 : DirichletCharacter ℂ p) (-1) = 1
      rw [MulChar.one_apply (isUnit_one.neg)])
  simpa using odd_LFunction_one_eq_oddLValueRhs (p := p)
    (hχ_prim := DirichletCharacter.isPrimitive_of_ne_one (p := p) hχ_ne_one)
    (hχ_odd := hχ_odd) (hχ_ne_one := hχ_ne_one)

/-- Rewrite the even nontrivial part of the cyclotomic `L`-product at `s = 1`
using the explicit even-character evaluation. -/
theorem evenLProduct_one_eq_prod_evenLValueRhs :
    evenLProduct p (1 : ℂ) =
      Finset.prod (evenNontrivialCharacters (p := p)) fun χ ↦ evenLValueRhs p χ := by
  classical
  unfold evenLProduct
  refine Finset.prod_congr rfl fun χ hχ ↦ ?_
  have hχ_mem := Finset.mem_filter.mp hχ
  have hχ_even : χ.Even := hχ_mem.2.1
  have hχ_ne_one : χ ≠ 1 := hχ_mem.2.2
  simpa using even_LFunction_one_eq_evenLValueRhs (p := p)
    (hχ_prim := DirichletCharacter.isPrimitive_of_ne_one (p := p) hχ_ne_one)
    (hχ_even := hχ_even) (hχ_ne_one := hχ_ne_one)

/-- The odd characters modulo `p` form exactly half of all characters. -/
lemma card_oddCharacters (hp_odd' : p ≠ 2) :
    (oddCharacters (p := p)).card = (p - 1) / 2 := by
  classical
  let E : Finset (DirichletCharacter ℂ p) := Finset.univ.filter fun χ ↦ χ.Even
  let O : Finset (DirichletCharacter ℂ p) := oddCharacters (p := p)
  have hdisj : Disjoint E O := by
    refine Finset.disjoint_left.mpr ?_
    intro χ hχE hχO
    have hχ_even : χ.Even := by simpa [E] using hχE
    have hχ_odd : χ.Odd := by simpa [O, oddCharacters] using hχO
    exact DirichletCharacter.Odd.not_even χ hχ_odd hχ_even
  have hunion : E ∪ O = (Finset.univ : Finset (DirichletCharacter ℂ p)) := by
    ext χ
    simp only [E, O, oddCharacters, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_true]
    exact DirichletCharacter.even_or_odd χ
  have hcard_total : E.card + O.card = p - 1 := by
    calc
      E.card + O.card = (E ∪ O).card := by
        rw [← Finset.card_union_of_disjoint hdisj]
      _ = Nat.card (DirichletCharacter ℂ p) := by
        rw [hunion, Finset.card_univ, Nat.card_eq_fintype_card]
      _ = p - 1 := card_dirichletCharacter_complex (p := p)
  have hcard_even : E.card = (p - 1) / 2 := card_even_characters (p := p) hp_odd'
  rcases hp.out.odd_of_ne_two hp_odd' with ⟨m, hm⟩
  have hhalf : (p - 1) / 2 = m := by omega
  rw [hhalf] at hcard_even
  have hcard_odd : O.card = m := by omega
  rw [hhalf]
  simpa [O, oddCharacters] using hcard_odd

/-- **T023d2**: For an odd Dirichlet character modulo a prime `p`, the Gauss
sum contribution from the inverse pair `(χ, χ⁻¹)` is `-(p : ℂ)`. -/
theorem odd_gaussSum_mul_gaussSum_inv_stdAddChar
    {χ : DirichletCharacter ℂ p} (hχ_odd : χ.Odd) :
    gaussSum χ (ZMod.stdAddChar (N := p)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) =
      -(p : ℂ) := by
  have hχ_ne_one : χ ≠ 1 := by
    rintro rfl
    exact DirichletCharacter.Odd.not_even _ hχ_odd (by
      change (1 : DirichletCharacter ℂ p) (-1) = 1
      rw [MulChar.one_apply (isUnit_one.neg)])
  rw [gaussSum_mul_gaussSum_inv_stdAddChar (p := p) (χ := χ) hχ_ne_one]
  rw [DirichletCharacter.Odd] at hχ_odd
  rw [hχ_odd]
  simp

/-- **T023d3**: An odd self-inverse Dirichlet character modulo a prime `p` is
the quadratic character. -/
theorem odd_selfInverse_character_eq_quadratic
    (hp_odd' : p ≠ 2) {χ : DirichletCharacter ℂ p}
    (hχ_odd : χ.Odd) (hχself : χ = χ⁻¹) :
    χ = quadraticCharComplex p := by
  have hχ_ne_one : χ ≠ 1 := by
    rintro rfl
    exact DirichletCharacter.Odd.not_even _ hχ_odd (by
      change (1 : DirichletCharacter ℂ p) (-1) = 1
      rw [MulChar.one_apply (isUnit_one.neg)])
  exact nontrivial_selfInverse_character_eq_quadratic (p := p) hp_odd' hχ_ne_one hχself

/-- **T023d3**: In the `p ≡ 3 [ZMOD 4]` case, the quadratic character is odd. -/
theorem quadraticCharComplex_odd_of_mod_four_eq_three_lvalue
    (hp_odd' : p ≠ 2) (hp₄ : p % 4 = 3) :
    (quadraticCharComplex p).Odd := by
  simpa [DirichletCharacter.Odd] using
    quadraticCharComplex_eval_neg_one_of_mod_four_eq_three (p := p) hp_odd' hp₄

/-- **T023d3**: If an odd self-inverse character exists modulo `p`, then
necessarily `p ≡ 3 [ZMOD 4]`. -/
theorem odd_selfInverse_character_mod_four_eq_three
    (hp_odd' : p ≠ 2) {χ : DirichletCharacter ℂ p}
    (hχ_odd : χ.Odd) (hχself : χ = χ⁻¹) :
    p % 4 = 3 := by
  have hquad : χ = quadraticCharComplex p :=
    odd_selfInverse_character_eq_quadratic (p := p) hp_odd' hχ_odd hχself
  have hquad_odd : (quadraticCharComplex p).Odd := by simpa [hquad] using hχ_odd
  have hneg : quadraticCharComplex p (-1 : ZMod p) = -1 := by
    simpa [DirichletCharacter.Odd] using hquad_odd
  have hmod1_ne : p % 4 ≠ 1 := by
    intro hp₄
    rw [quadraticCharComplex_eval_neg_one_of_mod_four_eq_one (p := p) hp_odd' hp₄] at hneg
    norm_num at hneg
  rcases hp.out.odd_of_ne_two hp_odd' with ⟨k, hk⟩
  have hp_mod2 : p % 2 = 1 := by
    omega
  have hp_mod4_lt : p % 4 < 4 := Nat.mod_lt _ (by decide)
  omega

/-- **T023d3**: Odd self-inverse characters exist exactly in the
`p ≡ 3 [ZMOD 4]` case. -/
theorem exists_odd_selfInverse_character_iff_mod_four_eq_three
    (hp_odd' : p ≠ 2) :
    (∃ χ : DirichletCharacter ℂ p, χ.Odd ∧ χ = χ⁻¹) ↔ p % 4 = 3 := by
  constructor
  · rintro ⟨χ, hχ_odd, hχself⟩
    exact odd_selfInverse_character_mod_four_eq_three (p := p) hp_odd' hχ_odd hχself
  · intro hp₄
    exact ⟨quadraticCharComplex p, quadraticCharComplex_odd_of_mod_four_eq_three_lvalue (p := p)
      hp_odd' hp₄, (quadraticCharComplex_inv (p := p)).symm⟩

/-- **T023d3**: In the `p ≡ 1 [ZMOD 4]` case, no odd Dirichlet character is
self-inverse. -/
theorem odd_character_ne_inv_of_mod_four_eq_one
    (hp_odd' : p ≠ 2) (hp₄ : p % 4 = 1) {χ : DirichletCharacter ℂ p}
    (hχ_odd : χ.Odd) :
    χ ≠ χ⁻¹ := by
  intro hχself
  have hp₄' := odd_selfInverse_character_mod_four_eq_three (p := p) hp_odd' hχ_odd hχself
  omega

/-- Factor the universal odd-side scalar
`((((Real.pi : ℝ) : ℂ) * Complex.I) / p)` out of the weighted Gauss product
and rewrite it as a single power. -/
theorem odd_weightedGaussProduct_eq_scalar_pow_mul (hp_odd' : p ≠ 2) :
    Finset.prod (oddCharacters (p := p)) (fun χ ↦
      ((((Real.pi : ℝ) : ℂ) * Complex.I) * gaussSum χ (ZMod.stdAddChar (N := p)) / (p : ℂ))) =
      (((((Real.pi : ℝ) : ℂ) * Complex.I) / (p : ℂ)) ^ ((p - 1) / 2)) *
        Finset.prod (oddCharacters (p := p))
          (fun χ ↦ gaussSum χ (ZMod.stdAddChar (N := p))) := by
  let C : ℂ := ((((Real.pi : ℝ) : ℂ) * Complex.I) / (p : ℂ))
  have hp_ne : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  calc
    Finset.prod (oddCharacters (p := p)) (fun χ ↦
        ((((Real.pi : ℝ) : ℂ) * Complex.I) * gaussSum χ (ZMod.stdAddChar (N := p)) / (p : ℂ))) =
      Finset.prod (oddCharacters (p := p)) (fun χ ↦
        C * gaussSum χ (ZMod.stdAddChar (N := p))) := by
          refine Finset.prod_congr rfl ?_
          intro χ hχ
          dsimp [C]
          field_simp [hp_ne]
    _ =
      (Finset.prod (oddCharacters (p := p)) (fun _ : DirichletCharacter ℂ p ↦ C)) *
        Finset.prod (oddCharacters (p := p))
          (fun χ ↦ gaussSum χ (ZMod.stdAddChar (N := p))) := by
            rw [Finset.prod_mul_distrib]
    _ =
      (C ^ (oddCharacters (p := p)).card) *
        Finset.prod (oddCharacters (p := p))
          (fun χ ↦ gaussSum χ (ZMod.stdAddChar (N := p))) := by
            rw [Finset.prod_const]
    _ =
      (C ^ ((p - 1) / 2)) *
        Finset.prod (oddCharacters (p := p))
          (fun χ ↦ gaussSum χ (ZMod.stdAddChar (N := p))) := by
            rw [card_oddCharacters (p := p) hp_odd']
    _ =
      (((((Real.pi : ℝ) : ℂ) * Complex.I) / (p : ℂ)) ^ ((p - 1) / 2)) *
        Finset.prod (oddCharacters (p := p))
          (fun χ ↦ gaussSum χ (ZMod.stdAddChar (N := p))) := by
            rfl

/-- Package the `K⁺` residue bridge into the exact even-value `hPlus` formula
consumed by the downstream `hMinus` assembly theorems. -/
theorem hPlus_formula_of_evenLProduct (hp_odd' : p ≠ 2) :
    ((hPlus K : ℕ) : ℂ) =
      maximalRealSubfieldClassNumberFactor (K := K) * evenLProduct p (1 : ℂ) :=
  hPlus_formula_of_Kplus_residue (K := K)
    (KplusResidue := evenLProduct p (1 : ℂ))
    (complex_maximalRealSubfield_residue_eq_evenLProduct_one (p := p) (K := K) hp_odd')

/-- Package the `K⁺` residue bridge into the exact even-value `hPlus` formula
consumed by the downstream `hMinus` assembly theorems. -/
theorem hPlus_formula_of_evenLValueRhs (hp_odd' : p ≠ 2) :
    ((hPlus K : ℕ) : ℂ) =
      maximalRealSubfieldClassNumberFactor (K := K) *
        Finset.prod (evenNontrivialCharacters (p := p)) (fun χ ↦ evenLValueRhs p χ) := by
  calc
    ((hPlus K : ℕ) : ℂ) =
        maximalRealSubfieldClassNumberFactor (K := K) * evenLProduct p (1 : ℂ) :=
          hPlus_formula_of_evenLProduct (p := p) (K := K) hp_odd'
    _ =
        maximalRealSubfieldClassNumberFactor (K := K) *
          Finset.prod (evenNontrivialCharacters (p := p)) (fun χ ↦ evenLValueRhs p χ) := by
            rw [evenLProduct_one_eq_prod_evenLValueRhs (p := p)]

/-- Package the `K⁺` residue bridge into the exact even-value `hPlus` formula
consumed by the downstream `hMinus` assembly theorems. -/
theorem hPlus_formula_of_evenLValues_cyclotomicFactor (hp_odd' : p ≠ 2) :
    ((hPlus K : ℕ) : ℂ) =
      cyclotomicHPlusFactor (K := K) *
        Finset.prod (evenNontrivialCharacters (p := p)) (fun χ ↦ evenLValueRhs p χ) := by
  simpa [cyclotomicHPlusFactor] using
    (hPlus_formula_of_evenLValueRhs (p := p) (K := K) hp_odd')

/-- The cyclotomic `K⁺` class-number formula in the exact `hplus` shape used
by the downstream `hMinus` assembly theorem. -/
theorem hPlus_formula_of_evenLValues (hp_odd' : p ≠ 2) :
    ((hPlus K : ℕ) : ℂ) =
      cyclotomicHPlusFactor (K := K) *
        Finset.prod (evenNontrivialCharacters (p := p)) (fun χ ↦ evenLValueRhs p χ) :=
  hPlus_formula_of_evenLValues_cyclotomicFactor (p := p) (K := K) hp_odd'

set_option linter.unusedSectionVars false

/-- The residue formula for `ζ_K` at `s = 1`, rewritten using the explicit odd
and even evaluations of the character `L`-values. -/
theorem residue_ready_factorization_explicit_LValues :
    NumberField.dedekindZeta_residue K =
      ((Finset.prod (evenNontrivialCharacters (p := p)) (fun χ ↦ evenLValueRhs p χ) *
          Finset.prod (oddCharacters (p := p)) (fun χ ↦ oddLValueRhs p χ)).re) := by
  rw [residue_ready_factorization_even_odd (p := p) (K := K),
    evenLProduct_one_eq_prod_evenLValueRhs (p := p),
    oddLProduct_one_eq_prod_oddLValueRhs (p := p)]

/-- Split the product of the odd `L(1, χ)` right-hand sides into the Gauss-sum
factor and the Bernoulli factor. -/
theorem oddLValueRhs_product_eq_gauss_product_mul_bernoulli_product :
    Finset.prod (oddCharacters (p := p)) (fun χ ↦ oddLValueRhs p χ) =
      Finset.prod (oddCharacters (p := p)) (fun χ ↦
        ((((Real.pi : ℝ) : ℂ) * Complex.I) * gaussSum χ (ZMod.stdAddChar (N := p)) / (p : ℂ))) *
        Finset.prod (oddCharacters (p := p)) (fun χ ↦ BernoulliGen χ⁻¹ 1) := by
  classical
  unfold oddLValueRhs
  rw [Finset.prod_mul_distrib]

end LValues

end BernoulliRegular
