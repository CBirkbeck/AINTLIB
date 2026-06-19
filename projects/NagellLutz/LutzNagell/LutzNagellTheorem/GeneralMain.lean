import LutzNagell.LutzNagellTheorem.GeneralCurve
import LutzNagell.LutzNagellTheorem.GeneralPrimeOrder
import LutzNagell.LutzNagellTheorem.GeneralIntegralMultiple
import LutzNagell.LutzNagellTheorem.ShortWeierstrass
import Mathlib.GroupTheory.OrderOfElement

/-!
# Generalized Lutz–Nagell integrality theorem

For a nonzero finite-order point on a general Weierstrass curve
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with `aᵢ ∈ ℤ`, either:
- the coordinates `x, y` are integers, or
- the point has order exactly 2 and `4x, 8y ∈ ℤ`.

## Main results

* `lutz_nagell_integrality_general`: the generalized integrality theorem.
-/

namespace LutzNagell
namespace LutzNagellTheorem

open WeierstrassCurve

variable (W : WeierstrassCurve ℤ)

/-- Convert `n • P = 0` on affine points to `(n : ℤ) • P = 0` on Jacobian points. -/
lemma nsmul_eq_zero_affine_to_jac
    {x y : ℚ} {hns : (curveQ W).toAffine.Nonsingular x y}
    {n : ℕ} (h : n • (Affine.Point.some _ _ hns) = 0) :
    (n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0 := by
  rw [natCast_zsmul]
  have h2 := congrArg (Jacobian.Point.toAffineAddEquiv (curveQ W)).symm h
  simp only [map_nsmul, map_zero] at h2
  exact h2

/-! ### Helper lemmas for the main theorem -/

/-- A nonzero affine point is of the form `.some hns`. -/
lemma exists_some_of_ne_zero
    {Q : Affine.Point ((curveQ W).toAffine)} (hQ : Q ≠ 0) :
    ∃ x y, ∃ hns : (curveQ W).toAffine.Nonsingular x y, Q = .some _ _ hns := by
  rcases Q with _ | ⟨_, _, hns⟩
  · exact absurd rfl hQ
  · exact ⟨_, _, hns, rfl⟩

private lemma integrality_of_odd_prime_factor
    {x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y)
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hpm : p ∣ addOrderOf (Affine.Point.some _ _ hpt))
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) :
    (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y := by
  set P := Affine.Point.some _ _ hpt
  have hm_pos := htor.addOrderOf_pos
  set k := addOrderOf P / p
  have hkp : k * p = addOrderOf P := Nat.div_mul_cancel hpm
  have hk_pos : 0 < k := Nat.div_pos (Nat.le_of_dvd hm_pos hpm) hp.pos
  have hQ_ne : k • P ≠ 0 := by
    intro h
    exact absurd (Nat.le_of_dvd hk_pos (addOrderOf_dvd_of_nsmul_eq_zero h))
      (not_le.mpr (by
        calc k = k * 1 := (mul_one k).symm
          _ < k * p := Nat.mul_lt_mul_of_pos_left hp.one_lt hk_pos
          _ = addOrderOf P := hkp))
  have hpQ : p • (k • P) = 0 := by
    rw [← mul_nsmul, hkp, addOrderOf_nsmul_eq_zero]
  obtain ⟨x', y', hns', hQ_eq⟩ := exists_some_of_ne_zero W hQ_ne
  have hne_jac : Jacobian.Point.fromAffine (Affine.Point.some _ _ hns') ≠ 0 := by
    rw [← map_zero (Jacobian.Point.toAffineAddEquiv (curveQ W)).symm]
    exact (Jacobian.Point.toAffineAddEquiv (curveQ W)).symm.injective.ne
      (Affine.Point.some_ne_zero hns')
  obtain ⟨hx'_int, hy'_int⟩ := prime_order_integrality_general W hns' hp hodd
    (nsmul_eq_zero_affine_to_jac W (hQ_eq ▸ hpQ)) hne_jac
  exact integral_of_nsmul_integral_general W hpt
    (show (k : ℤ) ≠ 0 by exact_mod_cast hk_pos.ne') hns'
    (show (k : ℤ) • P = Affine.Point.some _ _ hns' by rw [natCast_zsmul]; exact hQ_eq)
    hx'_int hy'_int

private lemma integrality_of_four_dvd_order
    {x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y)
    (h4 : 4 ∣ addOrderOf (Affine.Point.some _ _ hpt))
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) :
    (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y := by
  set P := Affine.Point.some _ _ hpt
  have hm_pos := htor.addOrderOf_pos
  set k := addOrderOf P / 4
  have hk4 : k * 4 = addOrderOf P := Nat.div_mul_cancel h4
  have hk_pos : 0 < k := Nat.div_pos (Nat.le_of_dvd hm_pos h4) (by norm_num)
  have hQ_ne : k • P ≠ 0 := by
    intro h
    exact absurd (Nat.le_of_dvd hk_pos (addOrderOf_dvd_of_nsmul_eq_zero h))
      (not_le.mpr (by omega))
  have h4Q : 4 • (k • P) = 0 := by
    rw [← mul_nsmul, hk4, addOrderOf_nsmul_eq_zero]
  have h2Q_ne : (2 : ℕ) • (k • P) ≠ 0 := by
    intro h; rw [← mul_nsmul] at h
    exact absurd (Nat.le_of_dvd (by omega) (addOrderOf_dvd_of_nsmul_eq_zero h))
      (not_le.mpr (by omega))
  obtain ⟨x', y', hns', hQ_eq⟩ := exists_some_of_ne_zero W hQ_ne
  obtain ⟨hx'_int, hy'_int⟩ := integrality_of_order_four_general W hns'
    (nsmul_eq_zero_affine_to_jac W (hQ_eq ▸ h4Q)) (hQ_eq ▸ h2Q_ne)
  exact integral_of_nsmul_integral_general W hpt
    (show (k : ℤ) ≠ 0 by exact_mod_cast hk_pos.ne') hns'
    (show (k : ℤ) • P = Affine.Point.some _ _ hns' by rw [natCast_zsmul]; exact hQ_eq)
    hx'_int hy'_int

/-- **Generalized Lutz–Nagell integrality.** For a nonzero finite-order point on a general
Weierstrass curve with integral coefficients, either the coordinates are integral, or the
point has order 2 and `4x, 8y ∈ ℤ`. -/
theorem lutz_nagell_integrality_general
    {x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) :
    ((∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y)
    ∨ (addOrderOf (Affine.Point.some _ _ hpt) = 2 ∧
        (∃ n : ℤ, (n : ℚ) = 4 * x) ∧ ∃ m : ℤ, (m : ℚ) = 8 * y) := by
  set P := Affine.Point.some _ _ hpt
  have hP_ne : P ≠ 0 := Affine.Point.some_ne_zero hpt
  have hm_ne_one : addOrderOf P ≠ 1 :=
    fun h ↦ hP_ne (AddMonoid.addOrderOf_eq_one_iff.mp h)
  by_cases hord2 : addOrderOf P = 2
  · right
    have h2P : (2 : ℕ) • P = 0 := by rw [← hord2, addOrderOf_nsmul_eq_zero]
    exact ⟨hord2, bounded_den_of_order_two_general W hpt
      (nsmul_eq_zero_affine_to_jac W h2P)⟩
  · left
    by_cases h_odd : ∃ p, p.Prime ∧ p ≠ 2 ∧ p ∣ addOrderOf P
    · obtain ⟨p, hp, hodd, hpm⟩ := h_odd
      exact integrality_of_odd_prime_factor W hpt hp hodd hpm htor
    · push Not at h_odd
      have h_all_two : ∀ q, q.Prime → q ∣ addOrderOf P → q = 2 := by
        intro q hq hqm; by_contra hne; exact h_odd q hq hne hqm
      have h2_dvd : 2 ∣ addOrderOf P := by
        obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm_ne_one
        exact (h_all_two q hq hqm) ▸ hqm
      have h4_dvd : 4 ∣ addOrderOf P := by
        obtain ⟨k₁, hk₁⟩ := h2_dvd
        obtain ⟨q, hq, hqk₁⟩ := Nat.exists_prime_and_dvd (show k₁ ≠ 1 by omega)
        have hqm : q ∣ addOrderOf P := dvd_trans hqk₁ ⟨2, by linarith⟩
        rw [h_all_two q hq hqm] at hqk₁
        obtain ⟨j, hj⟩ := hqk₁
        exact ⟨j, by linarith⟩
      exact integrality_of_four_dvd_order W hpt h4_dvd htor

/-! ## Short Weierstrass specialization

For a short Weierstrass curve `y² = x³ + Ax + B`, the order-2 branch of the general
theorem collapses to full integrality: `a₁ = a₃ = 0` forces `ψ₂ = 2y`, so order 2
gives `y = 0`, and then `x` is a root of the monic `X³ + AX + B ∈ ℤ[X]`. -/

/-- **Short Weierstrass Lutz–Nagell integrality.** Derived from the general version.
For a nonzero finite-order point on `y² = x³ + Ax + B` with integral coefficients,
the coordinates are integers. -/
theorem lutz_nagell_integrality_short (A B : ℤ)
    {x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) :
    (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y := by
  rcases lutz_nagell_integrality_general (shortCurveZ A B) hpt htor with
    ⟨hx, hy⟩ | ⟨hord2, _, _⟩
  · exact ⟨hx, hy⟩
  · have h2P : (2 : ℕ) • Affine.Point.some _ _ hpt = 0 := by
      convert addOrderOf_nsmul_eq_zero (x := Affine.Point.some _ _ hpt) using 2
      exact hord2.symm
    have hψ₂ := evalEval_ψ_eq_zero_of_zsmul_eq_zero_general (shortCurveZ A B) hpt 2
      (nsmul_eq_zero_affine_to_jac (shortCurveZ A B) h2P)
    rw [WeierstrassCurve.ψ_two, WeierstrassCurve.ψ₂,
        WeierstrassCurve.Affine.evalEval_polynomialY] at hψ₂
    simp only [curveQ_a₁, curveQ_a₃, shortCurveZ_a₁, shortCurveZ_a₃,
               Int.cast_zero, zero_mul, add_zero] at hψ₂
    have hy0 : y = 0 := by linarith
    refine ⟨?_, ⟨0, by push_cast; exact hy0.symm⟩⟩
    have hcurve := (shortCurveQ_equation_iff A B x y).mp hpt.left
    rw [hy0, zero_pow (by norm_num : 2 ≠ 0)] at hcurve
    open Polynomial in
    have hroot : aeval x (X ^ 3 + C A * X + C B : ℤ[X]) = 0 := by
      simp only [map_add, map_mul, map_pow, aeval_X, aeval_C,
                 algebraMap_int_eq, Int.coe_castRingHom]; linarith
    open Polynomial in
    have hmonic : (X ^ 3 + C A * X + C B : ℤ[X]).Monic := by
      apply Monic.add_of_left
      · exact Monic.add_of_left (monic_X_pow 3)
          (degree_C_mul_X_le A |>.trans_lt (by rw [degree_X_pow]; norm_num))
      · exact degree_C_le.trans_lt (by
          rw [degree_add_eq_left_of_degree_lt
            (degree_C_mul_X_le A |>.trans_lt (by rw [degree_X_pow]; norm_num))]
          rw [degree_X_pow]; norm_num)
    obtain ⟨x₀, hx₀⟩ := RingHom.mem_rangeS.mp (isInteger_of_is_root_of_monic hmonic hroot)
    exact ⟨x₀, by simpa only [algebraMap_int_eq, Int.coe_castRingHom] using hx₀⟩

end LutzNagellTheorem
end LutzNagell
