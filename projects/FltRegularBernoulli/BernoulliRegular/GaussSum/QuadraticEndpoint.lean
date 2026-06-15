module

public import BernoulliRegular.GaussSum.SignInvariant.BranchChoice

/-!
# Final quadratic Gauss-sum endpoint

This module repackages the sign-invariant endpoint theorems into the final
quadratic Gauss-sum statement used downstream.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

section GaussSum

variable (p : ℕ) [hp : Fact p.Prime]

/-- **T023d1g3**: In the `p ≡ 1 [ZMOD 4]` branch, the quadratic Gauss sum for
the raw quadratic character equals `√p`. -/
theorem gaussSum_quadraticChar_stdAddChar_of_mod_four_eq_one
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 1) :
    gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
      (ZMod.stdAddChar (N := p)) = (Real.sqrt p : ℂ) := by
  simpa [quadraticCharComplex] using
    gaussSum_quadraticCharComplex_eq_sqrt_of_mod_four_eq_one (p := p) hp₂ hp₄

/-- **T023d1g3**: In the `p ≡ 3 [ZMOD 4]` branch, the quadratic Gauss sum for
the raw quadratic character equals `I * √p`. -/
theorem gaussSum_quadraticChar_stdAddChar_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
      (ZMod.stdAddChar (N := p)) = Complex.I * (Real.sqrt p : ℂ) := by
  simpa [quadraticCharComplex] using
    gaussSum_quadraticCharComplex_eq_I_mul_sqrt_of_mod_four_eq_three (p := p) hp₂ hp₄

/-- **T023d1g3**: The quadratic Gauss sum with the standard additive character
has the expected positive branch in each `mod 4` case. -/
theorem gaussSum_quadraticChar_stdAddChar (hp₂ : p ≠ 2) :
    gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
      (ZMod.stdAddChar (N := p)) =
        if p % 4 = 1 then (Real.sqrt p : ℂ) else Complex.I * (Real.sqrt p : ℂ) := by
  by_cases hp₄ : p % 4 = 1
  · simp [hp₄, gaussSum_quadraticChar_stdAddChar_of_mod_four_eq_one (p := p) hp₂ hp₄]
  · have hpodd : p % 2 = 1 := by
      rcases hp.out.odd_of_ne_two hp₂ with ⟨k, hk⟩
      omega
    have hp₄' : p % 4 = 3 := by
      omega
    simp [hp₄, gaussSum_quadraticChar_stdAddChar_of_mod_four_eq_three (p := p) hp₂ hp₄']

end GaussSum

end BernoulliRegular
