module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.RingTheory.RootsOfUnity.Lemmas
public import BernoulliRegular.GaussSum.SignInvariant.Vandermonde
public import BernoulliRegular.LValueAtOne

/-!
# Scalar preliminaries for the Vandermonde determinant route

This file isolates the elementary Fourier-root and trigonometric identities
needed for the final scalar evaluation in the determinant computation.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

open scoped BigOperators ComplexConjugate

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

/-- For an odd prime `p`, decompose `p` as `2 * ((p - 1) / 2) + 1`. -/
private theorem eq_two_mul_pred_div_two_add_one (hp2 : p ≠ 2) :
    p = 2 * ((p - 1) / 2) + 1 := by
  rw [Nat.two_mul_div_two_of_even (hp.out.even_sub_one hp2),
    Nat.sub_add_cancel hp.out.one_le]

theorem fourierBaseRoot_eq_exp_neg_one_div :
    fourierBaseRoot (p := p) = Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) / p)) := by
  rw [fourierBaseRoot]
  calc
    ZMod.stdAddChar (N := p) (-(1 : ZMod p)) = Complex.exp (-(2 * Real.pi * Complex.I) / p) := by
      simpa using (ZMod.stdAddChar_coe (N := p) (-1))
    _ = Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) / p)) := by
          congr 1
          have hp0 : (p : ℂ) ≠ 0 := by
            exact_mod_cast hp.out.ne_zero
          push_cast
          field_simp [hp0]

theorem fourierBaseRoot_isPrimitiveRoot :
    IsPrimitiveRoot (fourierBaseRoot (p := p)) p := by
  rw [fourierBaseRoot_eq_exp_neg_one_div (p := p)]
  exact Complex.isPrimitiveRoot_exp_of_isCoprime (-1) p hp.out.ne_zero ⟨-1, 0, by simp⟩

theorem fourierBaseRoot_pow_eq_exp_neg (r : ℕ) :
    fourierBaseRoot (p := p) ^ r =
      Complex.exp ((-(2 * Real.pi * (r : ℝ) / p)) * Complex.I) := by
  rw [fourierBaseRoot]
  calc
    ZMod.stdAddChar (N := p) (-(1 : ZMod p)) ^ r =
        ZMod.stdAddChar (N := p) ((r : ℕ) • (-(1 : ZMod p))) :=
          (AddChar.map_nsmul_eq_pow _ _ _).symm
    _ = ZMod.stdAddChar (N := p) (-(r : ZMod p)) := by
          congr
          rw [nsmul_eq_mul]
          ring
    _ = Complex.exp (-(2 * Real.pi * Complex.I * r) / p) := by
          simpa using (ZMod.stdAddChar_coe (N := p) (j := -(r : ℤ)))
    _ = Complex.exp ((-(2 * Real.pi * (r : ℝ) / p)) * Complex.I) := by
          congr 1
          have hp0 : (p : ℂ) ≠ 0 := by
            exact_mod_cast hp.out.ne_zero
          push_cast
          field_simp [hp0]

theorem doubleSin_complement {k : ℕ} (hk : k ≤ p) :
    2 * Real.sin (Real.pi * ((p - k : ℕ) / p : ℝ)) =
      2 * Real.sin (Real.pi * (k : ℝ) / p) := by
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  rw [show Real.pi * ((p - k : ℕ) / p : ℝ) = Real.pi - Real.pi * (k : ℝ) / p by
      rw [Nat.cast_sub hk]
      field_simp [hp0]]
  rw [Real.sin_pi_sub]

theorem complexDoubleSin_complement {k : ℕ} (hk : k ≤ p) :
    2 * Complex.sin (Real.pi * ((p - k : ℕ) / p : ℝ)) =
      2 * Complex.sin (Real.pi * (k : ℝ) / p) := by
  simpa [Complex.ofReal_sin] using
    congrArg (fun x : ℝ => (x : ℂ)) (doubleSin_complement (p := p) hk)

theorem doubleSin_pos {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    0 < 2 * Real.sin (Real.pi * (k : ℝ) / p) := by
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast hp.out.pos
  have hkp' : (k : ℝ) < p := by
    exact_mod_cast hkp
  have hang : Real.pi * (k : ℝ) / p ∈ Set.Ioo 0 Real.pi := by
    constructor
    · exact div_pos (by positivity) hp0
    · have hfrac : (k : ℝ) / p < 1 :=
        (div_lt_one hp0).2 hkp'
      have hmul : Real.pi * ((k : ℝ) / p) < Real.pi := by
        simpa [one_mul] using (mul_lt_mul_of_pos_left hfrac Real.pi_pos)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hsin : 0 < Real.sin (Real.pi * (k : ℝ) / p) :=
    Real.sin_pos_of_mem_Ioo hang
  positivity

theorem fourierPow_eq_exp_pos_complement {k : ℕ} (hkp : k ≤ p) :
    fourierBaseRoot (p := p) ^ k =
      Complex.exp ((2 * Real.pi * ((p - k : ℕ) : ℝ) / p) * Complex.I) := by
  have hperiod : Complex.exp (((-2 : ℝ) * Real.pi) * Complex.I) = 1 := by
    rw [Complex.exp_mul_I]
    simp
  calc
    fourierBaseRoot (p := p) ^ k =
        Complex.exp ((-(2 * Real.pi * (k : ℝ) / p)) * Complex.I) :=
          fourierBaseRoot_pow_eq_exp_neg (p := p) k
    _ = Complex.exp
          (((2 * Real.pi * ((p - k : ℕ) : ℝ) / p) * Complex.I) +
            (((-2 : ℝ) * Real.pi) * Complex.I)) := by
          congr 1
          have hp0 : (p : ℂ) ≠ 0 := by
            exact_mod_cast hp.out.ne_zero
          have hcalc :
              -(((2 : ℂ) * k) / p) = ((2 : ℂ) * (p - k : ℕ)) / p - 2 := by
            rw [Nat.cast_sub hkp]
            field_simp [hp0]
            ring
          simpa [sub_eq_add_neg, div_eq_mul_inv, mul_assoc, mul_left_comm,
            mul_comm, mul_add, add_mul] using
            congrArg (fun x : ℂ => (Real.pi : ℂ) * x * Complex.I) hcalc
    _ = Complex.exp ((2 * Real.pi * ((p - k : ℕ) : ℝ) / p) * Complex.I) := by
          rw [Complex.exp_add, hperiod, mul_one]

theorem one_sub_fourierPow_norm_eq_doubleSin {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    ‖1 - fourierBaseRoot (p := p) ^ k‖ = 2 * Real.sin (Real.pi * (k : ℝ) / p) := by
  have ht0 : 0 < 2 * Real.pi * ((p - k : ℕ) : ℝ) / p := by
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast hp.out.pos
    have hpk0 : (0 : ℝ) < (p - k : ℕ) := by
      exact_mod_cast (Nat.sub_pos_of_lt hkp)
    positivity
  have ht2π : 2 * Real.pi * ((p - k : ℕ) : ℝ) / p < 2 * Real.pi := by
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast hp.out.pos
    have hpk_lt : ((p - k : ℕ) : ℝ) < p := by
      exact_mod_cast (Nat.sub_lt hp.out.pos hk0)
    have hfrac : (((p - k : ℕ) : ℝ) / p) < 1 := (div_lt_one hp0).2 hpk_lt
    have hmul : (2 * Real.pi) * (((p - k : ℕ) : ℝ) / p) < (2 * Real.pi) * 1 :=
      mul_lt_mul_of_pos_left hfrac Real.two_pi_pos
    simpa [one_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  calc
    ‖1 - fourierBaseRoot (p := p) ^ k‖ =
        ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * ((p - k : ℕ) : ℝ) / p) * Complex.I)‖ := by
          rw [fourierPow_eq_exp_pos_complement (p := p) (k := k) hkp.le]
    _ = 2 * Real.sin ((2 * Real.pi * ((p - k : ℕ) : ℝ) / p) / 2) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            (norm_one_sub_exp_ofReal_mul_I
              (t := 2 * Real.pi * ((p - k : ℕ) : ℝ) / p) ht0 ht2π)
    _ = 2 * Real.sin (Real.pi * (k : ℝ) / p) := by
          rw [show (2 * Real.pi * ((p - k : ℕ) : ℝ) / p) / 2 =
            Real.pi * ((p - k : ℕ) / p : ℝ) by ring]
          exact doubleSin_complement (p := p) hkp.le

theorem one_sub_fourierPow_mul_one_sub_fourierPow_complement_eq_doubleSin_sq
    {k : ℕ} (hkp : k ≤ p) :
    (1 - fourierBaseRoot (p := p) ^ k) * (1 - fourierBaseRoot (p := p) ^ (p - k)) =
      (2 * Complex.sin (Real.pi * (k : ℝ) / p)) ^ 2 := by
  have hpow : fourierBaseRoot (p := p) ^ p = 1 :=
    (fourierBaseRoot_isPrimitiveRoot (p := p)).pow_eq_one
  rcases eq_or_lt_of_le hkp with h_eq | hklt
  · subst k
    rw [hpow, Nat.sub_self, pow_zero]
    simp
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero, Nat.sub_zero, hpow]
    simp
  have hnorm :
      ‖1 - fourierBaseRoot (p := p) ^ k‖ ^ 2 =
        (2 * Real.sin (Real.pi * (k : ℝ) / p)) ^ 2 := by
    rw [one_sub_fourierPow_norm_eq_doubleSin (p := p) hk0 hklt]
  have hpowComp : fourierBaseRoot (p := p) ^ (p - k) = conj (fourierBaseRoot (p := p) ^ k) := by
    rw [fourierPow_eq_exp_pos_complement (p := p) (k := p - k) (Nat.sub_le _ _)]
    have hsub : p - (p - k) = k := by omega
    rw [hsub, fourierBaseRoot_pow_eq_exp_neg (p := p) k, ← Complex.exp_conj]
    have hconjArg :
        (starRingEnd ℂ) (-(2 * Real.pi * (k : ℝ) / p) * Complex.I) =
          (2 * Real.pi * (k : ℝ) / p) * Complex.I := by
      apply Complex.ext <;> simp [Complex.conj_ofReal, Complex.conj_I]
    rw [hconjArg]
  have hconjSub :
      1 - fourierBaseRoot (p := p) ^ (p - k) =
        conj (1 - fourierBaseRoot (p := p) ^ k) := by
    rw [hpowComp, map_sub, map_one]
  calc
    (1 - fourierBaseRoot (p := p) ^ k) * (1 - fourierBaseRoot (p := p) ^ (p - k))
        = (1 - fourierBaseRoot (p := p) ^ k) * conj (1 - fourierBaseRoot (p := p) ^ k) := by
          rw [hconjSub]
    _ = ((‖1 - fourierBaseRoot (p := p) ^ k‖ ^ 2 : ℝ) : ℂ) := by
          simpa using Complex.mul_conj' (1 - fourierBaseRoot (p := p) ^ k)
    _ = (2 * Complex.sin (Real.pi * (k : ℝ) / p)) ^ 2 := by
          simpa [Complex.ofReal_sin] using congrArg (fun x : ℝ => (x : ℂ)) hnorm

theorem fourierBaseRoot_prod_one_sub_pow_eq_order :
    ∏ d ∈ Finset.range (p - 1), (1 - fourierBaseRoot (p := p) ^ (d + 1)) = p := by
  have hp_eq : (p - 1 : ℕ) + 1 = p := Nat.sub_add_cancel hp.out.one_le
  have hμ : IsPrimitiveRoot (fourierBaseRoot (p := p)) ((p - 1) + 1) := by
    rw [hp_eq]
    exact fourierBaseRoot_isPrimitiveRoot (p := p)
  convert
      (IsPrimitiveRoot.prod_one_sub_pow_eq_order
        (n := p - 1) (μ := fourierBaseRoot (p := p)) hμ) using 1
  simpa [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℂ)) hp_eq.symm

theorem fourierCyclotomicSingleDifferenceProduct_eq_weightedPairProduct
    (hp2 : p ≠ 2) :
    fourierCyclotomicSingleDifferenceProduct p =
      ∏ d ∈ Finset.range ((p - 1) / 2),
        (fourierBaseRoot (p := p) ^ (d + 1) - 1) ^ (p - (d + 1)) *
          (fourierBaseRoot (p := p) ^ (p - (d + 1)) - 1) ^ (d + 1) := by
  let n : ℕ := (p - 1) / 2
  have hp_eqn : p = 2 * n + 1 := eq_two_mul_pred_div_two_add_one (p := p) hp2
  have hp_add : p = n + n + 1 := by
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using hp_eqn
  have hp_sub : p - 1 = n + n := by
    have := congrArg (fun m : ℕ => m - 1) hp_eqn
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using this
  unfold fourierCyclotomicSingleDifferenceProduct
  rw [hp_sub, Finset.prod_range_add]
  have hfirst :
      ∏ d ∈ Finset.range n,
          (fourierBaseRoot (p := p) ^ (d + 1) - 1) ^ (n + n - d) =
        ∏ d ∈ Finset.range n,
          (fourierBaseRoot (p := p) ^ (d + 1) - 1) ^ (p - (d + 1)) := by
    refine Finset.prod_congr rfl ?_
    intro d hd
    have hd' : d < n := Finset.mem_range.mp hd
    have hexp : n + n - d = p - (d + 1) := by omega
    rw [hexp]
  have hreflect :
      (∏ d ∈ Finset.range n,
          (fourierBaseRoot (p := p) ^ (n + d + 1) - 1) ^ (n - d)) =
        ∏ d ∈ Finset.range n,
          (fourierBaseRoot (p := p) ^ (p - (d + 1)) - 1) ^ (d + 1) := by
    rw [← Finset.prod_range_reflect
      (fun d => (fourierBaseRoot (p := p) ^ (n + d + 1) - 1) ^ (n - d)) n]
    refine Finset.prod_congr rfl ?_
    intro d hd
    have hd' : d < n := Finset.mem_range.mp hd
    have hbase : n + (n - 1 - d) + 1 = p - (d + 1) := by omega
    have hpow : n - (n - 1 - d) = d + 1 := by omega
    rw [hbase, hpow]
  have hsecond :
      (∏ x ∈ Finset.range n,
          (fourierBaseRoot (p := p) ^ (n + x + 1) - 1) ^ (n + n - (n + x))) =
        ∏ x ∈ Finset.range n,
          (fourierBaseRoot (p := p) ^ (n + x + 1) - 1) ^ (n - x) := by
    refine Finset.prod_congr rfl ?_
    intro x hx
    have hexp : n + n - (n + x) = n - x := Nat.add_sub_add_left n n x
    rw [hexp]
  rw [hfirst, hsecond, hreflect, ← Finset.prod_mul_distrib]
  have hhalf : (n + n) / 2 = n := by omega
  rw [hhalf]

theorem two_mul_sum_range_halfWeightedExponent_eq_choose_three_succ
    (hp2 : p ≠ 2) :
    2 * (∑ d ∈ Finset.range ((p - 1) / 2), (d + 1) * (p - (d + 1))) = (p + 1).choose 3 := by
  let n : ℕ := (p - 1) / 2
  have hp_eqn : p = 2 * n + 1 := eq_two_mul_pred_div_two_add_one (p := p) hp2
  have hp_add : p = n + n + 1 := by simpa [two_mul, add_assoc, add_left_comm, add_comm] using hp_eqn
  have hsplit :
      ∑ i ∈ Finset.range (p + 1), i * (p - i) =
        (∑ i ∈ Finset.range (n + 1), i * (p - i)) +
          ∑ i ∈ Finset.range (n + 1), (n + 1 + i) * (p - (n + 1 + i)) := by
    have hp_split : p + 1 = (n + 1) + (n + 1) := by
      calc
        p + 1 = (n + n + 1) + 1 := by rw [hp_add]
        _ = (n + 1) + (n + 1) := by ring
    rw [hp_split, Finset.sum_range_add]
  have hreflect :
      ∑ i ∈ Finset.range (n + 1), (n + 1 + i) * (p - (n + 1 + i)) =
        ∑ i ∈ Finset.range (n + 1), i * (p - i) := by
    rw [← Finset.sum_range_reflect
      (fun i => (n + 1 + i) * (p - (n + 1 + i))) (n + 1)]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    have hi_le : i ≤ n := Nat.lt_succ_iff.mp hi'
    have hfirst : n + 1 + (n + 1 - 1 - i) = p - i := by omega
    have hip : i ≤ p := by omega
    rw [hfirst, Nat.sub_sub_self hip, Nat.mul_comm]
  have hshift :
      ∑ i ∈ Finset.range (n + 1), i * (p - i) =
        ∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1)) := by
    rw [show n + 1 = 1 + n by simp [Nat.add_comm], Finset.sum_range_add]
    simp [add_comm]
  calc
    2 * (∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) =
        ∑ i ∈ Finset.range (p + 1), i * (p - i) := by
          rw [← hshift, two_mul, hsplit, hreflect]
    _ = (p + 1).choose 3 := by
          simpa using (sum_range_weightedRootExponent_eq_choose_three (n := p + 1))

theorem dvd_chooseThree_add_halfWeightedExponent (hp2 : p ≠ 2) :
    p ∣ p.choose 3 + ∑ d ∈ Finset.range ((p - 1) / 2), (d + 1) * (p - (d + 1)) := by
  let n : ℕ := (p - 1) / 2
  have hsum := two_mul_sum_range_halfWeightedExponent_eq_choose_three_succ (p := p) hp2
  have hchoose3 : 3 * p.choose 3 = p * (p - 1).choose 2 := by
    simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hp.out.one_le,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.add_one_mul_choose_eq (p - 1) 2).symm
  have hdvd_choose2 : p ∣ p.choose 2 := by
    rw [Nat.choose_two_right, Nat.mul_div_assoc _ (hp.out.even_sub_one hp2).two_dvd]
    exact dvd_mul_right p ((p - 1) / 2)
  have hdvd2 :
      p ∣ 2 * (p.choose 3 + ∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) := by
    have hsum'' :
        (∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) +
          (∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) = (p + 1).choose 3 := by
      simpa [n, two_mul] using hsum
    have hEq :
        2 * (p.choose 3 + ∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) =
          p * (p - 1).choose 2 + p.choose 2 := by
      calc
        2 * (p.choose 3 + ∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1)))
            = (p.choose 3 + ∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) +
                (p.choose 3 + ∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) := by
                  rw [two_mul]
        _ = p.choose 3 + p.choose 3 +
              ((∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) +
                (∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1)))) := by ring
        _ = 2 * p.choose 3 + (p + 1).choose 3 := by rw [hsum'', two_mul]
        _ = 3 * p.choose 3 + p.choose 2 := by rw [Nat.choose_succ_succ' p 2]; ring
        _ = p * (p - 1).choose 2 + p.choose 2 := by rw [hchoose3]
    rw [hEq]
    exact dvd_add (dvd_mul_right p ((p - 1).choose 2)) hdvd_choose2
  exact (hp.out.odd_of_ne_two hp2).coprime_two_right.dvd_of_dvd_mul_left hdvd2

theorem fourierBaseRoot_pow_chooseThree_add_halfWeightedExponent_eq_one
    (hp2 : p ≠ 2) :
    fourierBaseRoot (p := p) ^
        (p.choose 3 + ∑ d ∈ Finset.range ((p - 1) / 2), (d + 1) * (p - (d + 1))) = 1 := by
  obtain ⟨m, hm⟩ := dvd_chooseThree_add_halfWeightedExponent (p := p) hp2
  rw [hm, pow_mul, (fourierBaseRoot_isPrimitiveRoot (p := p)).pow_eq_one]
  simp

theorem halfRangeDoubleSinProduct_eq_sqrt_order (hp2 : p ≠ 2) :
    ∏ d ∈ Finset.range ((p - 1) / 2),
      2 * Real.sin (Real.pi * ((d + 1 : ℕ) / p : ℝ)) = Real.sqrt p := by
  let n : ℕ := (p - 1) / 2
  let S : ℕ → ℝ := fun k => 2 * Real.sin (Real.pi * (k : ℝ) / p)
  have hp_eqn : p = 2 * n + 1 := eq_two_mul_pred_div_two_add_one (p := p) hp2
  have hp_add : p = n + n + 1 := by
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using hp_eqn
  have hp_sub : p - 1 = n + n := by
    have := congrArg (fun m : ℕ => m - 1) hp_eqn
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using this
  have hpair :
      ∏ d ∈ Finset.range (p - 1), (1 - fourierBaseRoot (p := p) ^ (d + 1)) =
        (((∏ d ∈ Finset.range n, S (d + 1)) ^ 2 : ℝ) : ℂ) := by
    rw [hp_sub, Finset.prod_range_add]
    have hreflect :
        (∏ d ∈ Finset.range n, (1 - fourierBaseRoot (p := p) ^ (n + d + 1))) =
          ∏ d ∈ Finset.range n, (1 - fourierBaseRoot (p := p) ^ (p - (d + 1))) := by
      rw [← Finset.prod_range_reflect (fun d => 1 - fourierBaseRoot (p := p) ^ (n + d + 1)) n]
      refine Finset.prod_congr rfl ?_
      intro d hd
      have hd' : d < n := Finset.mem_range.mp hd
      congr 2
      omega
    rw [hreflect, ← Finset.prod_mul_distrib]
    calc
      ∏ d ∈ Finset.range n,
          ((1 - fourierBaseRoot (p := p) ^ (d + 1)) *
            (1 - fourierBaseRoot (p := p) ^ (p - (d + 1)))) =
          ∏ d ∈ Finset.range n, ((((S (d + 1) : ℝ) : ℂ)) ^ 2) := by
            refine Finset.prod_congr rfl ?_
            intro d hd
            have hd' : d < n := Finset.mem_range.mp hd
            have hle : d + 1 ≤ p := by omega
            simpa [S, Complex.ofReal_sin] using
              (one_sub_fourierPow_mul_one_sub_fourierPow_complement_eq_doubleSin_sq
                (p := p) (k := d + 1) hle)
      _ = (((∏ d ∈ Finset.range n, S (d + 1)) ^ 2 : ℝ) : ℂ) := by
            rw [← Finset.prod_pow]
            simp
  have hsqC : (((∏ d ∈ Finset.range n, S (d + 1)) ^ 2 : ℝ) : ℂ) = (p : ℂ) := by
    rw [← hpair]
    exact fourierBaseRoot_prod_one_sub_pow_eq_order (p := p)
  have hsq : (∏ d ∈ Finset.range n, S (d + 1)) ^ 2 = (p : ℝ) := by
    exact_mod_cast hsqC
  have hpos : 0 < ∏ d ∈ Finset.range n, S (d + 1) := by
    refine Finset.prod_pos ?_
    intro d hd
    have hd' : d < n := Finset.mem_range.mp hd
    have hdk : d + 1 < p := by omega
    exact doubleSin_pos (p := p) (Nat.succ_pos d) hdk
  have hsq' : (∏ d ∈ Finset.range n, S (d + 1)) ^ 2 = (Real.sqrt p) ^ 2 := by
    rw [Real.sq_sqrt (show 0 ≤ (p : ℝ) by positivity)]
    exact hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq' with hEq | hEq
  · simpa [n, S, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hEq
  · exfalso
    have hsqrt_pos : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp.out.pos)
    linarith

theorem negI_pow_orderHalfMul_eq_I_pow_half (hp2 : p ≠ 2) :
    (-Complex.I) ^ (p * ((p - 1) / 2)) = Complex.I ^ ((p - 1) / 2) := by
  let n : ℕ := (p - 1) / 2
  have hp_eqn : p = 2 * n + 1 := eq_two_mul_pred_div_two_add_one (p := p) hp2
  calc
    (-Complex.I) ^ (p * n) = (-Complex.I) ^ (2 * (n * n) + n) := by
      congr
      rw [hp_eqn]
      ring
    _ = ((-Complex.I) ^ 2) ^ (n * n) * (-Complex.I) ^ n := by
          rw [pow_add, pow_mul]
    _ = (-1 : ℂ) ^ (n * n) * (((-1 : ℂ) ^ n) * Complex.I ^ n) := by
          rw [show (-Complex.I) ^ 2 = (-1 : ℂ) by simp,
            show (-Complex.I) ^ n = (((-1 : ℂ) * Complex.I) ^ n) by ring,
            mul_pow]
    _ = (-1 : ℂ) ^ (n * n + n) * Complex.I ^ n := by
          have hpowNegOne : (-1 : ℂ) ^ (n * n) * (-1 : ℂ) ^ n = (-1 : ℂ) ^ (n * n + n) := by
            rw [← pow_add]
          rw [show (-1 : ℂ) ^ (n * n) * (((-1 : ℂ) ^ n) * Complex.I ^ n) =
              ((-1 : ℂ) ^ (n * n) * (-1 : ℂ) ^ n) * Complex.I ^ n by ac_rfl,
            hpowNegOne]
    _ = Complex.I ^ n := by
          have hEven : Even (n * n + n) := by
            simpa [pow_two, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              Nat.even_mul_succ_self n
          rcases hEven with ⟨m, hm⟩
          rw [hm, ← two_mul, pow_mul]
          simp
    _ = Complex.I ^ ((p - 1) / 2) := by
          simp [n]

end SignInvariant

end BernoulliRegular
