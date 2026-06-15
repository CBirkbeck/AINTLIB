module

public import BernoulliRegular.HMinus.LValueReduction.LValues

/-!
# The cyclotomic Gauss-product target

This file isolates the exact Gauss-product identity needed by the final
`hMinus` assembly theorem and rewrites it into the raw odd-character product
shape proved later.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators

namespace BernoulliRegular

section GaussGoal

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]

/-- The exact cyclotomic Gauss-product statement needed as the `hgauss`
input for the final `hMinus` assembly theorem. -/
def cyclotomicHGaussGoal : Prop :=
  cyclotomicRelativeLValueCoefficient (p := p) (K := K) *
      Finset.prod (oddCharacters (p := p)) (fun χ =>
        ((((Real.pi : ℝ) : ℂ) * Complex.I) * gaussSum χ (ZMod.stdAddChar (N := p)) / (p : ℂ))) =
    (2 * p : ℂ) *
      Finset.prod (oddCharacters (p := p))
        (fun _ : DirichletCharacter ℂ p => (-(1 / 2 : ℂ)))

theorem cyclotomicHGaussGoal_iff_rawGaussProduct
    (hp_odd' : p ≠ 2) :
    cyclotomicHGaussGoal (p := p) K ↔
      Finset.prod (oddCharacters (p := p))
          (fun χ => gaussSum χ (ZMod.stdAddChar (N := p))) =
        (Complex.I ^ ((p - 1) / 2)) *
          ((((Real.sqrt ((p : ℝ) ^ ((p - 1) / 2)) : ℝ) : ℂ))) := by
  let n : ℕ := (p - 1) / 2
  let S : ℂ := (((Real.sqrt ((p : ℝ) ^ n) : ℝ) : ℂ))
  let G : ℂ :=
    Finset.prod (oddCharacters (p := p))
      (fun χ => gaussSum χ (ZMod.stdAddChar (N := p)))
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast hp.out.pos
  have hp_ne : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  have hI_ne : Complex.I ^ n ≠ 0 :=
    pow_ne_zero _ Complex.I_ne_zero
  have hS_ne : S ≠ 0 := by
    dsimp [S]
    exact Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 <| pow_pos hp_pos _)
  have h2p_ne : (2 * p : ℂ) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero two_ne_zero hp.out.ne_zero
  have hpi_ne : (((Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have htwo_pow_ne : ((2 : ℂ) ^ n) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hpow_pi_ne : ((((2 * Real.pi) ^ n : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast pow_ne_zero n (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hpow_nonneg : 0 ≤ (p : ℝ) ^ n := by
    positivity
  have hS_sq : S ^ 2 = (p : ℂ) ^ n := by
    dsimp [S]
    calc
      ((((Real.sqrt ((p : ℝ) ^ n) : ℝ) : ℂ)) ^ 2)
          = ((((p : ℝ) ^ n : ℝ) : ℂ)) := by
              rw [pow_two, ← Complex.ofReal_mul]
              simp [hpow_nonneg]
      _ = (p : ℂ) ^ n := by
              norm_num
  have hneg_half_pow : (-(1 / 2 : ℂ)) ^ n = ((-1 : ℂ) ^ n) / (2 : ℂ) ^ n := by
    rw [show (-(1 / 2 : ℂ)) = (-1 : ℂ) / 2 by norm_num, div_pow]
  have hscalar :
      ((((((2 * p : ℕ) : ℝ) * Real.sqrt ((p : ℝ) ^ n)) /
            (2 * Real.pi) ^ n : ℝ) : ℂ) *
          (((((Real.pi : ℝ) : ℂ) * Complex.I) / (p : ℂ)) ^ n)) =
        (((2 * p : ℂ) * (Complex.I ^ n)) / (((2 : ℂ) ^ n) * S)) := by
    have hpi_pow_ne : (((Real.pi : ℝ) : ℂ) ^ n) ≠ 0 :=
      pow_ne_zero _ hpi_ne
    have hp_pow_ne : (p : ℂ) ^ n ≠ 0 :=
      pow_ne_zero _ hp_ne
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, div_pow, mul_pow]
    rw [show (((2 * Real.pi : ℝ) : ℂ)) = (2 : ℂ) * (((Real.pi : ℝ) : ℂ)) by norm_num, mul_pow]
    rw [← hS_sq]
    field_simp [hS_ne, hp_pow_ne, hpi_pow_ne, htwo_pow_ne]
    simp [S, mul_assoc, mul_comm]
  have hI_twice :
      (Complex.I ^ n) * ((Complex.I ^ n) * S) = ((-1 : ℂ) ^ n) * S := by
    calc
      (Complex.I ^ n) * ((Complex.I ^ n) * S) = (Complex.I ^ (n + n)) * S := by
        rw [← mul_assoc, ← pow_add]
      _ = (Complex.I ^ (2 * n)) * S := by
        congr 1
        rw [two_mul]
      _ = ((Complex.I ^ 2) ^ n) * S := by rw [pow_mul]
      _ = ((-1 : ℂ) ^ n) * S := by rw [Complex.I_sq]
  have hI_sq_pow : (Complex.I ^ n) ^ 2 = (-1 : ℂ) ^ n := by
    calc
      (Complex.I ^ n) ^ 2 = Complex.I ^ (n * 2) := by rw [pow_mul]
      _ = Complex.I ^ (2 * n) := by
            congr 1
            ring
      _ = (Complex.I ^ 2) ^ n := by rw [pow_mul]
      _ = (-1 : ℂ) ^ n := by rw [Complex.I_sq]
  constructor
  · intro h
    rw [cyclotomicHGaussGoal, odd_weightedGaussProduct_eq_scalar_pow_mul (p := p) hp_odd',
      cyclotomicRelativeLValueCoefficient_eq_final (p := p) (K := K) hp_odd',
      Finset.prod_const] at h
    rw [card_oddCharacters (p := p) hp_odd'] at h
    have h0 :
      ((((((2 * p : ℕ) : ℝ) * Real.sqrt ((p : ℝ) ^ n)) /
          (2 * Real.pi) ^ n : ℝ) : ℂ) *
        ((((Real.pi : ℝ) : ℂ) * Complex.I) / (p : ℂ)) ^ n * G =
        (2 * p : ℂ) * (-(1 / 2 : ℂ)) ^ n) := by
          simpa [n, G, mul_assoc] using h
    have hmid : (Complex.I ^ n) * G = ((-1 : ℂ) ^ n) * S := by
      rw [hscalar, hneg_half_pow] at h0
      have h' := h0
      field_simp [h2p_ne, hS_ne, htwo_pow_ne] at h'
      simpa [mul_assoc, mul_left_comm, mul_comm] using h'
    apply mul_left_cancel₀ hI_ne
    calc
      (Complex.I ^ n) * G = ((-1 : ℂ) ^ n) * S := hmid
      _ = (Complex.I ^ n) * ((Complex.I ^ n) * S) := hI_twice.symm
  · intro hraw
    have hraw' : G = (Complex.I ^ n) * S := by
      simpa [n, G, S] using hraw
    have hgoal :
      ((((((2 * p : ℕ) : ℝ) * Real.sqrt ((p : ℝ) ^ n)) /
          (2 * Real.pi) ^ n : ℝ) : ℂ) *
        ((((Real.pi : ℝ) : ℂ) * Complex.I) / (p : ℂ)) ^ n * G =
        (2 * p : ℂ) * (-(1 / 2 : ℂ)) ^ n) := by
          rw [hscalar, hneg_half_pow, hraw']
          have h' :
              ((2 * p : ℂ) * (Complex.I ^ n) / (((2 : ℂ) ^ n) * S)) * (Complex.I ^ n * S) =
                (2 * p : ℂ) * (((-1 : ℂ) ^ n) / (2 : ℂ) ^ n) := by
              field_simp [h2p_ne, hS_ne, htwo_pow_ne]
              simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hI_sq_pow
          exact h'
    rw [cyclotomicHGaussGoal, odd_weightedGaussProduct_eq_scalar_pow_mul (p := p) hp_odd',
      cyclotomicRelativeLValueCoefficient_eq_final (p := p) (K := K) hp_odd',
      Finset.prod_const]
    rw [card_oddCharacters (p := p) hp_odd']
    simpa [n, G, mul_assoc] using hgoal

end GaussGoal

end BernoulliRegular
