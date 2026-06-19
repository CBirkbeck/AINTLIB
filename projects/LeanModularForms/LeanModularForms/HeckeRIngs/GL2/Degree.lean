/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.MultiplicationTable

/-!
# Degree formulas for GL₂ Hecke operators

Shimura Theorem 3.24, identities 6 and 7: degree formulas for the GL₂ Hecke algebra.

## Main results

* `deg_T_diag_ppow` — `deg(T(pⁱ, p^{i+k})) = p^{k−1}(p+1)` for k > 0
* `deg_T_diag_scalar` — `deg(T(c,c)) = 1`
* `deg_T_sum_prime_pow` — `deg(T(pᵏ)) = 1 + p + ⋯ + pᵏ`
* `deg_T_sum` — `deg(T(m)) = σ₁(m)`

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Theorem 3.24
-/

open HeckeRing HeckeRing.GLn HeckeRing.GL2
open scoped ArithmeticFunction.sigma

namespace HeckeRing.GL2

variable (p : ℕ) (hp : p.Prime)

include hp in
/-- Theorem 3.24(6): `deg(T(pⁱ, p^{i+k})) = p^{k-1}(p+1)` for k > 0. -/
theorem deg_T_diag_ppow (i k : ℕ) (hk : 0 < k) :
    HeckeCoset_deg (GL_pair 2) (T_diag (![p ^ i, p ^ (i + k)])) = ↑(p ^ (k - 1) * (p + 1)) :=
  HeckeCoset_deg_T_diag_two_prime p hp (![p ^ i, p ^ (i + k)])
    (fun j ↦ by fin_cases j <;> exact pow_pos hp.pos _)
    (fun j hj ↦ by
      obtain rfl : j = 0 := by lia
      simpa only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, zero_add, Fin.mk_one,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] using Nat.pow_dvd_pow p (Nat.le_add_right i k))
    k hk (by
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero,
        Nat.pow_div (Nat.le_add_right i k) hp.pos, add_tsub_cancel_left])

/-- Scalar case: `deg(T(c, c)) = 1`. -/
theorem deg_T_diag_scalar (c : ℕ) (hc : 0 < c) :
    HeckeCoset_deg (GL_pair 2) (T_diag (fun _ ↦ c)) = 1 :=
  HeckeCoset_deg_T_diag_two_scalar (fun _ ↦ c) (fun _ ↦ hc) (divChain_const 2 c) rfl

private lemma deg_T_ad_of_pos (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (hdvd : a ∣ d) :
    deg (GL_pair 2) (T_ad a d) = HeckeCoset_deg (GL_pair 2) (T_diag ![a, d]) := by
  simp only [T_ad_of_pos a d ha hd hdvd, T_elem, Nat.succ_eq_add_one, Nat.reduceAdd, deg_T_single,
    one_mul]

include hp in
private lemma deg_ppow_term_lt (i k : ℕ) (h2i : 2 * i < k) :
    deg (GL_pair 2) (T_ad (p ^ i) (p ^ (k - i))) = ↑(p ^ (k - 2 * i - 1) * (p + 1)) := by
  rw [show k - i = i + (k - 2 * i) by lia, deg_T_ad_of_pos _ _ (pow_pos hp.pos i)
    (pow_pos hp.pos _) (Nat.pow_dvd_pow p (Nat.le_add_right i _))]
  exact deg_T_diag_ppow p hp i (k - 2 * i) (by lia)

include hp in
private lemma deg_ppow_term_eq (i k : ℕ) (h2i : 2 * i = k) :
    deg (GL_pair 2) (T_ad (p ^ i) (p ^ (k - i))) = 1 := by
  rw [show k - i = i by lia, deg_T_ad_of_pos _ _ (pow_pos hp.pos i) (pow_pos hp.pos i) dvd_rfl,
    Matrix.vec_single_eq_const, Matrix.vecCons_const]
  exact deg_T_diag_scalar (p ^ i) (pow_pos hp.pos i)

include hp in
private lemma deg_ppow_shift (i k : ℕ) (hi : i < k / 2 + 1) :
    deg (GL_pair 2) (T_ad (p ^ (i + 1)) (p ^ (k + 2 - (i + 1)))) =
    deg (GL_pair 2) (T_ad (p ^ i) (p ^ (k - i))) := by
  by_cases h2i : 2 * i < k
  · rw [deg_ppow_term_lt p hp (i + 1) (k + 2) (by lia),
      show k + 2 - 2 * (i + 1) - 1 = k - 2 * i - 1 by lia, ← deg_ppow_term_lt p hp i k h2i]
  · rw [deg_ppow_term_eq p hp (i + 1) (k + 2) (by lia), deg_ppow_term_eq p hp i k (by lia)]

private lemma deg_T_sum_prime_pow_aux (k : ℕ)
    (ih : deg (GL_pair 2) (T_sum ⟨p ^ k, pow_pos hp.pos k⟩) =
      ∑ j ∈ Finset.range (k + 1), (p : ℤ) ^ j) :
    deg (GL_pair 2) (T_sum ⟨p ^ (k + 2), pow_pos hp.pos (k + 2)⟩) =
    ∑ j ∈ Finset.range (k + 2 + 1), (p : ℤ) ^ j := by
  rw [T_sum_ppow_expansion p hp (k + 2), map_sum, Nat.add_div_right k two_pos,
    Finset.sum_range_succ']
  have h_tail : ∑ i ∈ Finset.range (k / 2 + 1),
      deg (GL_pair 2) (T_ad (p ^ (i + 1)) (p ^ (k + 2 - (i + 1)))) =
      ∑ i ∈ Finset.range (k / 2 + 1), deg (GL_pair 2) (T_ad (p ^ i) (p ^ (k - i))) :=
    Finset.sum_congr rfl fun i hi ↦ deg_ppow_shift p hp i k (Finset.mem_range.mp hi)
  rw [T_sum_ppow_expansion p hp k, map_sum] at ih
  rw [h_tail, ih, show deg (GL_pair 2) (T_ad (p ^ 0) (p ^ (k + 2 - 0))) =
      ↑(p ^ (k + 1) * (p + 1)) by
    simpa [show k + 2 - 0 - 1 = k + 1 by lia] using deg_ppow_term_lt p hp 0 (k + 2) (by lia)]
  conv_rhs => rw [Finset.sum_range_succ, Finset.sum_range_succ]
  push_cast
  ring

/-- `deg(T(pᵏ)) = 1 + p + ⋯ + pᵏ`. -/
theorem deg_T_sum_prime_pow (k : ℕ) :
    deg (GL_pair 2) (T_sum ⟨p ^ k, pow_pos hp.pos k⟩) =
    ∑ j ∈ Finset.range (k + 1), (p : ℤ) ^ j := by
  induction k using Nat.twoStepInduction with
  | zero =>
    rw [T_sum_ppow_expansion p hp 0, map_sum]
    simp only [Nat.zero_div, zero_add, Finset.range_one, zero_tsub, pow_zero, Finset.sum_singleton,
      T_ad_one_one, map_one]
  | one =>
    rw [T_sum_ppow_expansion p hp 1, map_sum]
    simpa only [Nat.reduceDiv, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, tsub_zero,
      pow_one, Nat.reduceAdd, geom_sum_two, mul_zero, tsub_self, one_mul, Nat.cast_add,
      Nat.cast_one] using deg_ppow_term_lt p hp 0 1 (by lia)
  | more k ih _ => exact deg_T_sum_prime_pow_aux p hp k ih

/-- Theorem 3.24(7): `deg(T(m)) = σ₁(m)`. -/
theorem deg_T_sum (m : ℕ+) : deg (GL_pair 2) (T_sum m) = (σ 1) (m : ℕ) := by
  obtain ⟨n, hn⟩ := m
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd hn (lt_irrefl 0)
  | one =>
    simp only [T_sum, PNat.mk_ofNat, PNat.val_ofNat, Nat.divisors_one, Finset.sum_singleton,
      Order.lt_one_iff, Nat.div_self, T_ad_one_one, map_one, ArithmeticFunction.sigma_one,
      Nat.cast_one]
  | prime_pow p k hp _ =>
    rw [deg_T_sum_prime_pow p hp k]
    exact_mod_cast (ArithmeticFunction.sigma_one_apply_prime_pow hp).symm
  | coprime a b ha hb hcop iha ihb =>
    have ha_pos : 0 < a := zero_lt_one.trans ha
    have hb_pos : 0 < b := zero_lt_one.trans hb
    rw [show T_sum ⟨a * b, hn⟩ = T_sum ⟨a, ha_pos⟩ * T_sum ⟨b, hb_pos⟩ from
      (T_sum_mul_coprime ⟨a, ha_pos⟩ ⟨b, hb_pos⟩ hcop).symm, map_mul, iha ha_pos, ihb hb_pos]
    exact_mod_cast (ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop).symm

end HeckeRing.GL2
