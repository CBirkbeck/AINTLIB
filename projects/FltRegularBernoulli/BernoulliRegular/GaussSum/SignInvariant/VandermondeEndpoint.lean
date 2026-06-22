module

public import BernoulliRegular.GaussSum.SignInvariant.VandermondeScalar

/-!
# Final endpoint for the Vandermonde determinant route

This file completes the scalar evaluation left open in the determinant/Vandermonde
package, giving the determinant of the normalized finite Fourier transform as an
explicit fourth root of unity.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

open scoped BigOperators ComplexConjugate

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

theorem one_sub_fourierPow_complement_eq_negI_mul_exp_mul_doubleSin
  {k : ℕ} (_hk0 : 0 < k) (hkp : k < p) :
    (1 : ℂ) - fourierBaseRoot (p := p) ^ (p - k) =
      (-Complex.I) *
        Complex.exp ((Real.pi * (k : ℝ) / p) * Complex.I) *
        ((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) := by
  let a : ℝ := Real.pi * (k : ℝ) / p
  let S : ℂ := ((2 * Real.sin a : ℝ) : ℂ)
  have hpow : fourierBaseRoot (p := p) ^ (p - k) =
      Complex.exp ((2 * Real.pi * (k : ℝ) / p) * Complex.I) := by
    simpa [Nat.sub_sub_self (Nat.le_of_lt hkp)] using
      (BernoulliRegular.fourierPow_eq_exp_pos_complement (p := p) (k := p - k)
        (Nat.sub_le _ _))
  have hhalf : (2 * Real.pi * (k : ℝ) / p) / 2 = a := by
    dsimp [a]
    ring
  calc
    (1 : ℂ) - fourierBaseRoot (p := p) ^ (p - k)
        = 1 - Complex.exp ((2 * Real.pi * (k : ℝ) / p) * Complex.I) := by
            rw [hpow]
    _ = S *
          (Real.cos (a - Real.pi / 2) + Real.sin (a - Real.pi / 2) * Complex.I) := by
            simpa [a, S, hhalf] using
              (BernoulliRegular.one_sub_exp_ofReal_mul_I (2 * Real.pi * (k : ℝ) / p))
    _ = (-Complex.I) * Complex.exp (a * Complex.I) * S := by
            rw [Complex.exp_mul_I, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
            apply Complex.ext <;>
            simp [S, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
    _ = (-Complex.I) * Complex.exp ((Real.pi * (k : ℝ) / p) * Complex.I) *
          ((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) := by
            simp [a, S]

theorem one_sub_fourierPow_complement_pow_order_eq_negI_pow_mul_negOnePow_mul_doubleSin_pow
    {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    ((1 : ℂ) - fourierBaseRoot (p := p) ^ (p - k)) ^ p =
      (-Complex.I) ^ p *
        ((-1 : ℂ) ^ k) *
        (((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) ^ p) := by
  let a : ℂ := (Real.pi * (k : ℝ) / p) * Complex.I
  rw [one_sub_fourierPow_complement_eq_negI_mul_exp_mul_doubleSin (p := p) hk0 hkp, mul_assoc,
    mul_pow, mul_pow]
  have hexp : Complex.exp a ^ p = (-1 : ℂ) ^ k := by
    rw [← Complex.exp_nat_mul]
    have hp0 : (p : ℝ) ≠ 0 := by
      exact_mod_cast hp.out.ne_zero
    have hmulReal : (p : ℝ) * (Real.pi * (k : ℝ) / p) = (k : ℝ) * Real.pi := by
      field_simp [hp0]
    have hmulCast : (p : ℂ) * ((Real.pi * (k : ℝ) / p : ℝ) : ℂ) = (k : ℂ) * (Real.pi : ℂ) := by
      exact_mod_cast hmulReal
    calc
      Complex.exp ((p : ℂ) * a)
          = Complex.exp (((p : ℂ) * ((Real.pi * (k : ℝ) / p : ℝ) : ℂ)) * Complex.I) := by
              simp [a, mul_assoc]
      _ = Complex.exp (((k : ℂ) * (Real.pi : ℂ)) * Complex.I) := by
            rw [hmulCast]
      _ = Complex.exp ((k : ℂ) * (Real.pi * Complex.I)) := by
            rw [← mul_assoc]
      _ = Complex.exp (Real.pi * Complex.I) ^ k := by
            rw [Complex.exp_nat_mul]
      _ = (-1 : ℂ) ^ k := by rw [Complex.exp_pi_mul_I]
  have hfinal := congrArg
      (fun x : ℂ => (-Complex.I) ^ p *
        (x * (((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) ^ p))) hexp
  simpa [a, mul_assoc, mul_left_comm, mul_comm] using hfinal

theorem weightedPairFactor_eq_negI_pow_mul_root_mul_doubleSin_pow
    {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    ((fourierBaseRoot (p := p)) ^ k - 1) ^ (p - k) *
      ((fourierBaseRoot (p := p)) ^ (p - k) - 1) ^ k =
        (-Complex.I) ^ p *
          (fourierBaseRoot (p := p)) ^ (k * (p - k)) *
          (((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) ^ p) := by
  let z : ℂ := fourierBaseRoot (p := p) ^ (p - k)
  have hfirst : fourierBaseRoot (p := p) ^ k - 1 =
      fourierBaseRoot (p := p) ^ k * (1 - z) := by
    dsimp [z]
    calc
      fourierBaseRoot (p := p) ^ k - 1 =
          fourierBaseRoot (p := p) ^ k - fourierBaseRoot (p := p) ^ p := by
            rw [(BernoulliRegular.fourierBaseRoot_isPrimitiveRoot (p := p)).pow_eq_one]
      _ = fourierBaseRoot (p := p) ^ k -
            fourierBaseRoot (p := p) ^ k * fourierBaseRoot (p := p) ^ (p - k) := by
            congr 1
            rw [← pow_add]
            congr 1
            omega
      _ = fourierBaseRoot (p := p) ^ k * (1 - fourierBaseRoot (p := p) ^ (p - k)) := by
            ring
  have hsecond : (fourierBaseRoot (p := p) ^ (p - k) - 1) ^ k =
      (-1 : ℂ) ^ k * (1 - z) ^ k := by
    dsimp [z]
    rw [show fourierBaseRoot (p := p) ^ (p - k) - 1 =
        (-1 : ℂ) * (1 - fourierBaseRoot (p := p) ^ (p - k)) by ring,
      mul_pow]
  have hpowcombine : (1 - z) ^ (p - k) * (1 - z) ^ k = (1 - z) ^ p := by
    rw [← pow_add]
    congr 1
    omega
  calc
    ((fourierBaseRoot (p := p)) ^ k - 1) ^ (p - k) *
        ((fourierBaseRoot (p := p)) ^ (p - k) - 1) ^ k
        = (fourierBaseRoot (p := p) ^ (k * (p - k))) *
            ((-1 : ℂ) ^ k * (1 - z) ^ p) := by
              rw [hfirst, mul_pow, ← pow_mul, hsecond]
              rw [show (fourierBaseRoot (p := p) ^ (k * (p - k))) * (1 - z) ^ (p - k) *
                  ((-1 : ℂ) ^ k * (1 - z) ^ k) =
                    (fourierBaseRoot (p := p) ^ (k * (p - k))) *
                      (((-1 : ℂ) ^ k) * ((1 - z) ^ (p - k) * (1 - z) ^ k)) by ac_rfl,
                hpowcombine]
    _ = (fourierBaseRoot (p := p) ^ (k * (p - k))) *
          ((-1 : ℂ) ^ k *
            ((-Complex.I) ^ p * ((-1 : ℂ) ^ k) *
              (((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) ^ p))) := by
            rw [one_sub_fourierPow_complement_pow_order_eq_negI_pow_mul_negOnePow_mul_doubleSin_pow
              (p := p) hk0 hkp]
    _ = (-Complex.I) ^ p *
          (fourierBaseRoot (p := p)) ^ (k * (p - k)) *
          (((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) ^ p) := by
            have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
              rw [← mul_pow]
              simp
            rw [show (fourierBaseRoot (p := p) ^ (k * (p - k))) *
                ((-1 : ℂ) ^ k * (((-Complex.I) ^ p * (-1 : ℂ) ^ k) *
                  (((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) ^ p))) =
                  (fourierBaseRoot (p := p) ^ (k * (p - k))) *
                    (((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) *
                        ((-Complex.I) ^ p *
                          (((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) ^ p))) by
                  ac_rfl,
              hsign]
            simp [mul_assoc, mul_left_comm, mul_comm]

theorem
    fourierCyclotomicSingleDifferenceProduct_eq_negI_pow_mul_rootPower_mul_halfRangeDoubleSinPow
    (hp2 : p ≠ 2) :
    fourierCyclotomicSingleDifferenceProduct p =
      (-Complex.I) ^ (p * ((p - 1) / 2)) *
        (fourierBaseRoot (p := p)) ^
          (∑ d ∈ Finset.range ((p - 1) / 2), (d + 1) * (p - (d + 1))) *
        (∏ d ∈ Finset.range ((p - 1) / 2),
          (((2 * Real.sin (Real.pi * ((d + 1 : ℕ) / p : ℝ)) : ℝ) : ℂ))) ^ p := by
  let n : ℕ := (p - 1) / 2
  let S : ℕ → ℂ := fun d =>
    (((2 * Real.sin (Real.pi * ((d + 1 : ℕ) / p : ℝ)) : ℝ) : ℂ))
  have hrootprod :
      ∏ d ∈ Finset.range n,
          (fourierBaseRoot (p := p)) ^ ((d + 1) * (p - (d + 1))) =
        (fourierBaseRoot (p := p)) ^
          (∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum (Finset.range n)
        (fun d => (d + 1) * (p - (d + 1))) (fourierBaseRoot (p := p)))
  have hsinprod :
      ∏ d ∈ Finset.range n, S d ^ p = (∏ d ∈ Finset.range n, S d) ^ p := by
    simpa using (Finset.prod_pow (Finset.range n) p S)
  calc
    fourierCyclotomicSingleDifferenceProduct p
        = ∏ d ∈ Finset.range n,
            ((-Complex.I) ^ p *
              (fourierBaseRoot (p := p)) ^ ((d + 1) * (p - (d + 1))) *
              S d ^ p) := by
                rw [BernoulliRegular.fourierCyclotomicSingleDifferenceProduct_eq_weightedPairProduct
                  (p := p) hp2]
                refine Finset.prod_congr rfl ?_
                intro d hd
                have hdlt : d < n := Finset.mem_range.mp hd
                have hdp : d + 1 < p := by
                  dsimp [n] at hdlt
                  omega
                simpa [S, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
                  weightedPairFactor_eq_negI_pow_mul_root_mul_doubleSin_pow (p := p)
                    (k := d + 1) (Nat.succ_pos d) hdp
    _ = (∏ _ ∈ Finset.range n, (-Complex.I) ^ p) *
          (∏ d ∈ Finset.range n,
            (fourierBaseRoot (p := p)) ^ ((d + 1) * (p - (d + 1)))) *
          (∏ d ∈ Finset.range n, S d ^ p) := by
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ = (-Complex.I) ^ (p * n) *
          (fourierBaseRoot (p := p)) ^
            (∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) *
          (∏ d ∈ Finset.range n, S d) ^ p := by
            rw [Finset.prod_const, Finset.card_range, pow_mul, hrootprod, hsinprod]
    _ = (-Complex.I) ^ (p * ((p - 1) / 2)) *
          (fourierBaseRoot (p := p)) ^
            (∑ d ∈ Finset.range ((p - 1) / 2), (d + 1) * (p - (d + 1))) *
          (∏ d ∈ Finset.range ((p - 1) / 2),
            (((2 * Real.sin (Real.pi * ((d + 1 : ℕ) / p : ℝ)) : ℝ) : ℂ))) ^ p := by
            simp [n, S]

/-- The determinant of the normalized finite Fourier transform is the explicit
fourth root of unity `I ^ ((p - 1) / 2)`. -/
theorem det_normalizedDft_eq_I_pow_orderHalf (hp2 : p ≠ 2) :
    LinearMap.det (normalizedDft p) = Complex.I ^ ((p - 1) / 2) := by
  let n : ℕ := (p - 1) / 2
  let e : ℕ := ∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))
  let S : ℂ := ∏ d ∈ Finset.range n,
    (((2 * Real.sin (Real.pi * ((d + 1 : ℕ) / p : ℝ)) : ℝ) : ℂ))
  have hsingle : fourierCyclotomicSingleDifferenceProduct p =
      (-Complex.I) ^ (p * n) * (fourierBaseRoot (p := p)) ^ e * S ^ p := by
    simpa [n, e, S] using
      fourierCyclotomicSingleDifferenceProduct_eq_negI_pow_mul_rootPower_mul_halfRangeDoubleSinPow
        (p := p) hp2
  have hroot : (fourierBaseRoot (p := p)) ^ (p.choose 3 + e) = 1 := by
    simpa [n, e] using
      BernoulliRegular.fourierBaseRoot_pow_chooseThree_add_halfWeightedExponent_eq_one (p := p) hp2
  have hSreal : ∏ d ∈ Finset.range n,
      2 * Real.sin (Real.pi * ((d + 1 : ℕ) / p : ℝ)) = Real.sqrt p := by
    simpa [n] using BernoulliRegular.halfRangeDoubleSinProduct_eq_sqrt_order (p := p) hp2
  have hS : S = (Real.sqrt p : ℂ) := by
    calc
      S = (((∏ d ∈ Finset.range n,
          2 * Real.sin (Real.pi * ((d + 1 : ℕ) / p : ℝ)) : ℝ)) : ℂ) := by
            simp [S]
      _ = (Real.sqrt p : ℂ) := by
            exact_mod_cast hSreal
  have hsqrt_ne : (Real.sqrt p : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.2
    apply Real.sqrt_ne_zero'.2
    exact_mod_cast hp.out.pos
  calc
    LinearMap.det (normalizedDft p)
        = ((Real.sqrt p : ℂ)⁻¹) ^ p *
            ((fourierBaseRoot (p := p)) ^ (p.choose 3) *
              fourierCyclotomicSingleDifferenceProduct p) :=
                BernoulliRegular.det_normalizedDft_eq_chooseThreeSingleDifferenceForm (p := p)
    _ = ((Real.sqrt p : ℂ)⁻¹) ^ p *
          ((fourierBaseRoot (p := p)) ^ (p.choose 3) *
            (((-Complex.I) ^ (p * n) * (fourierBaseRoot (p := p)) ^ e) * S ^ p)) := by
              rw [hsingle]
    _ = ((Real.sqrt p : ℂ)⁻¹) ^ p *
          (((-Complex.I) ^ (p * n)) *
            (((fourierBaseRoot (p := p)) ^ (p.choose 3 + e)) * S ^ p)) := by
              rw [show (fourierBaseRoot (p := p)) ^ (p.choose 3) *
                  (((-Complex.I) ^ (p * n) * (fourierBaseRoot (p := p)) ^ e) * S ^ p) =
                    ((-Complex.I) ^ (p * n)) *
                      (((fourierBaseRoot (p := p)) ^ (p.choose 3) *
                        (fourierBaseRoot (p := p)) ^ e) * S ^ p) by ac_rfl,
                ← pow_add]
        _ = ((Real.sqrt p : ℂ)⁻¹) ^ p * (((-Complex.I) ^ (p * n)) * (1 * S ^ p)) := by
          rw [hroot]
        _ = ((Real.sqrt p : ℂ)⁻¹) ^ p * (((-Complex.I) ^ (p * n)) * S ^ p) := by
          simp
    _ = ((-Complex.I) ^ (p * n)) * (((Real.sqrt p : ℂ)⁻¹) ^ p * S ^ p) := by
          ac_rfl
    _ = ((-Complex.I) ^ (p * n)) * (((Real.sqrt p : ℂ)⁻¹) ^ p * (Real.sqrt p : ℂ) ^ p) := by
          rw [hS]
    _ = (-Complex.I) ^ (p * n) := by
          rw [← mul_pow]
          simp [hsqrt_ne]
    _ = Complex.I ^ ((p - 1) / 2) := by
          simpa [n] using BernoulliRegular.negI_pow_orderHalfMul_eq_I_pow_half (p := p) hp2

/-- If `p ≡ 1 (mod 4)`, the determinant route lands in the real branch. -/
theorem det_normalizedDft_eq_negOnePow_of_mod_four_eq_one
    (hp2 : p ≠ 2) (hp4 : p % 4 = 1) :
    LinearMap.det (normalizedDft p) = (-1 : ℂ) ^ ((p - 1) / 4) := by
  have hhalf : (p - 1) / 2 = 2 * ((p - 1) / 4) := by
    omega
  rw [det_normalizedDft_eq_I_pow_orderHalf (p := p) hp2, hhalf, pow_mul]
  simp

/-- If `p ≡ 3 (mod 4)`, the determinant route lands in the imaginary branch. -/
theorem det_normalizedDft_eq_negOnePow_mul_I_of_mod_four_eq_three
    (hp2 : p ≠ 2) (hp4 : p % 4 = 3) :
    LinearMap.det (normalizedDft p) = (-1 : ℂ) ^ ((p - 3) / 4) * Complex.I := by
  have hhalf : (p - 1) / 2 = 2 * ((p - 3) / 4) + 1 := by
    omega
  rw [det_normalizedDft_eq_I_pow_orderHalf (p := p) hp2, hhalf, pow_add, pow_mul]
  simp [mul_comm]

end SignInvariant

end BernoulliRegular
