import LutzNagell.DivisionPolynomialDegree
import LutzNagell.ZSMul
import LutzNagell.LutzNagellTheorem.GeneralDenominators
import LutzNagell.LutzNagellTheorem.EvalBridge
import LutzNagell.LutzNagellTheorem.GeneralCurve
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Localization.Rat

/-!
# Prime-order and order-4 torsion integrality for general Weierstrass curves

If `P ≠ 0` has odd prime order or order 4 on a general Weierstrass curve with integral
coefficients, then `P` has integral affine coordinates.

For order 2, we prove the weaker bound `4x, 8y ∈ ℤ`.
-/

namespace LutzNagell
namespace LutzNagellTheorem

open WeierstrassCurve Polynomial

variable (W : WeierstrassCurve ℤ)

/-! ### y integral from x integral on general curve -/

/-- If `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with `aᵢ ∈ ℤ` and `x ∈ ℤ`, then `y ∈ ℤ`.

`y` is a root of the monic polynomial `Y² + (a₁x₀ + a₃)Y - (x₀³ + a₂x₀² + a₄x₀ + a₆) ∈ ℤ[Y]`. -/
theorem y_integral_of_x_integral_on_general_curve
    {x y : ℚ}
    (hcurve : y ^ 2 + (W.a₁ : ℚ) * x * y + (W.a₃ : ℚ) * y =
      x ^ 3 + (W.a₂ : ℚ) * x ^ 2 + (W.a₄ : ℚ) * x + (W.a₆ : ℚ))
    {x₀ : ℤ} (hx : (x₀ : ℚ) = x) :
    ∃ y₀ : ℤ, (y₀ : ℚ) = y := by
  set c₁ : ℤ := W.a₁ * x₀ + W.a₃
  set c₀ : ℤ := -(x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)
  have hroot : aeval y (X ^ 2 + C c₁ * X + C c₀ : ℤ[X]) = 0 := by
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, algebraMap_int_eq, Int.coe_castRingHom]
    subst hx; push_cast [c₁, c₀]; nlinarith
  have hmonic : (X ^ 2 + C c₁ * X + C c₀ : ℤ[X]).Monic := by
    apply Polynomial.Monic.add_of_left
    · exact Polynomial.Monic.add_of_left (monic_X_pow 2)
        (degree_C_mul_X_le c₁ |>.trans_lt (by norm_num [degree_X_pow]))
    · exact degree_C_le.trans_lt (by
        rw [degree_add_eq_left_of_degree_lt
          (degree_C_mul_X_le c₁ |>.trans_lt (by norm_num [degree_X_pow]))]
        norm_num [degree_X_pow])
  obtain ⟨y₀, hy₀⟩ := RingHom.mem_rangeS.mp (isInteger_of_is_root_of_monic hmonic hroot)
  exact ⟨y₀, by simpa only [algebraMap_int_eq, Int.coe_castRingHom] using hy₀⟩

/-! ### Extract ψ = 0 from torsion (general version) -/

/-- If `n • P = 0` in the Jacobian point group of `curveQ W`, then `ψ_n(x,y) = 0`. -/
theorem evalEval_ψ_eq_zero_of_zsmul_eq_zero_general
    {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y) (n : ℤ)
    (htors : n • (Jacobian.Point.fromAffine
      (Affine.Point.some _ _ hns)) = 0) :
    ((curveQ W).ψ n).evalEval x y = 0 := by
  have heval := zsmul_eq_smulEval (curveQ W) hns n
  have hzero := Jacobian.Point.zero_point (W' := (curveQ W).toJacobian)
  rw [Jacobian.Point.ext_iff] at htors
  rw [heval, hzero] at htors
  exact (Jacobian.Z_eq_zero_of_equiv (Quotient.exact htors)).mpr rfl

/-! ### ψ₂ = 0 implies 2•P = 0 (converse direction) -/

/-- If `ψ₂(x,y) = 0` (i.e., `2y + a₁x + a₃ = 0`), then `2 • P = 0` in the affine group. -/
theorem two_nsmul_eq_zero_of_ψ₂_eq_zero
    {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y)
    (hψ : (curveQ W).ψ₂.evalEval x y = 0) :
    (2 : ℕ) • (Affine.Point.some _ _ hns) = 0 := by
  rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY] at hψ
  have hy : y = (curveQ W).toAffine.negY x y := by
    unfold WeierstrassCurve.Affine.negY; linarith
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_of_Y_eq (h₁ := hns) (h₂ := hns) rfl hy

/-! ### Odd prime torsion: x integral -/


/-- For odd prime `p`, if `p • P = 0` on a general integral Weierstrass curve, then `x ∈ ℤ`. -/
theorem x_integral_of_odd_prime_torsion_general
    {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y)
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (htors : (p : ℤ) • (Jacobian.Point.fromAffine
      (Affine.Point.some _ _ hns)) = 0) :
    ∃ x₀ : ℤ, (x₀ : ℚ) = x := by
  have hψ := evalEval_ψ_eq_zero_of_zsmul_eq_zero_general W hns (p : ℤ) htors
  have hodd_int : ¬Even (p : ℤ) := by rwa [Int.even_coe_nat, hp.even_iff]
  rw [evalEval_ψ_odd (curveQ W) hns.left (p : ℤ) hodd_int] at hψ
  have hmap : (curveQ W).preΨ (p : ℤ) = (W.preΨ (p : ℤ)).map (algebraMap ℤ ℚ) := by
    change (W.map (algebraMap ℤ ℚ)).preΨ (p : ℤ) = _; rw [WeierstrassCurve.map_preΨ]
  rw [hmap, eval_map] at hψ
  change aeval x (W.preΨ (p : ℤ)) = 0 at hψ
  have hdvd := den_dvd_of_is_root hψ
  have hp_ne : ((p : ℤ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hdvd_p : (IsFractionRing.den ℤ x : ℤ) ∣ (p : ℤ) := by
    refine dvd_trans hdvd ?_
    have hlc : (W.preΨ (↑p : ℤ)).leadingCoeff = (↑p : ℤ) := by
      have := W.leadingCoeff_preΨ hp_ne
      simp only [show ¬Even (Int.ofNat p) from hodd_int, ite_false] at this
      exact_mod_cast this
    rw [hlc]
  have hdvd_nat : x.den ∣ p := by
    rw [← Rat.isFractionRingDen x]; exact Int.natAbs_dvd_natAbs.mpr hdvd_p
  have hden_one : x.den = 1 := by
    rcases hp.eq_one_or_self_of_dvd x.den hdvd_nat with h | h
    · exact h
    · exact absurd h (fun h => den_ne_prime_of_on_general_curve W
        ((curveQ_equation_iff W x y).mp hns.left) hp h)
  exact ⟨x.num, by rwa [← Rat.den_eq_one_iff]⟩

/-! ### Order-4 torsion: integrality -/


/-- If `P` has 4-torsion (4•P = 0, 2•P ≠ 0) on a general integral curve, then `P` is integral.

From `ψ₄(P) = 0` and `ψ₄ = C(preΨ₄) * ψ₂`, either `preΨ₄(x) = 0`
(→ x.den | 2 → x integral) or `ψ₂(P) = 0` (→ 2•P = 0, contradicting hypothesis). -/
theorem integrality_of_order_four_general
    {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y)
    (h4 : (4 : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0)
    (h2ne : (2 : ℕ) • (Affine.Point.some _ _ hns) ≠ 0) :
    (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y := by
  have hψ₄ := evalEval_ψ_eq_zero_of_zsmul_eq_zero_general W hns 4 h4
  rw [WeierstrassCurve.ψ_four] at hψ₄
  simp only [evalEval_mul, evalEval_C] at hψ₄
  rcases mul_eq_zero.mp hψ₄ with hpreΨ | hψ₂
  · have hmap : (curveQ W).preΨ₄ = W.preΨ₄.map (algebraMap ℤ ℚ) := by
      change (W.map (algebraMap ℤ ℚ)).preΨ₄ = _; rw [WeierstrassCurve.map_preΨ₄]
    rw [hmap, eval_map] at hpreΨ
    change aeval x W.preΨ₄ = 0 at hpreΨ
    have hdvd := den_dvd_of_is_root hpreΨ
    rw [W.leadingCoeff_preΨ₄ (by norm_num : (2 : ℤ) ≠ 0)] at hdvd
    have hdvd_nat : x.den ∣ 2 := by
      rw [← Rat.isFractionRingDen x]; exact Int.natAbs_dvd_natAbs.mpr hdvd
    have hden_one : x.den = 1 := by
      rcases (by decide : Nat.Prime 2).eq_one_or_self_of_dvd x.den hdvd_nat with h | h
      · exact h
      · exact absurd h (fun h => den_ne_prime_of_on_general_curve W
          ((curveQ_equation_iff W x y).mp hns.left) (by decide) h)
    have hx₀ : (x.num : ℚ) = x := by rwa [← Rat.den_eq_one_iff]
    exact ⟨⟨x.num, hx₀⟩, y_integral_of_x_integral_on_general_curve W
      ((curveQ_equation_iff W x y).mp hns.left) hx₀⟩
  · exact absurd (two_nsmul_eq_zero_of_ψ₂_eq_zero W hns hψ₂) h2ne

/-! ### Odd prime order: full integrality -/


/-- If `P` has odd prime order on a general integral curve, then `P` has integral coordinates. -/
theorem prime_order_integrality_general
    {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y)
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (htors : (p : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0)
    (_hne : Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) ≠ 0) :
    (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y := by
  obtain ⟨x₀, hx₀⟩ := x_integral_of_odd_prime_torsion_general W hns hp hodd htors
  exact ⟨⟨x₀, hx₀⟩, y_integral_of_x_integral_on_general_curve W
    ((curveQ_equation_iff W x y).mp hns.left) hx₀⟩

/-! ### Order-2 torsion: bounded denominators -/


/-- If `2•P = 0` on a general integral curve, then `4x ∈ ℤ` and `8y ∈ ℤ`.

From `ψ₂ = 0`: `2y + a₁x + a₃ = 0`. Substituting into the curve equation gives
`4x³ + b₂x² + 2b₄x + b₆ = 0`, with leading coefficient 4. By the rational root theorem,
`x.den | 4`, so `4x ∈ ℤ`. Then `8y = -4(a₁x + a₃) ∈ ℤ`. -/
theorem bounded_den_of_order_two_general
    {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y)
    (h2 : (2 : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0) :
    (∃ n : ℤ, (n : ℚ) = 4 * x) ∧ ∃ m : ℤ, (m : ℚ) = 8 * y := by
  have hψ := evalEval_ψ_eq_zero_of_zsmul_eq_zero_general W hns 2 h2
  rw [WeierstrassCurve.ψ_two] at hψ
  have hψ_num : 2 * y + (W.a₁ : ℚ) * x + (W.a₃ : ℚ) = 0 := by
    have h := hψ
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY] at h
    simp only [curveQ_a₁, curveQ_a₃] at h; linarith
  have hΨ_zero : (curveQ W).Ψ₂Sq.eval x = 0 := by
    have h := evalEval_eq_of_mk_eq (curveQ W) hns.left
      (Affine.CoordinateRing.mk_ψ₂_sq (W := curveQ W))
    rw [evalEval_pow, hψ, zero_pow two_ne_zero, evalEval_C] at h
    linarith
  have hmap : (curveQ W).Ψ₂Sq = W.Ψ₂Sq.map (algebraMap ℤ ℚ) := by
    change (W.map (algebraMap ℤ ℚ)).Ψ₂Sq = _; rw [WeierstrassCurve.map_Ψ₂Sq]
  rw [hmap, eval_map] at hΨ_zero
  change aeval x W.Ψ₂Sq = 0 at hΨ_zero
  have hdvd := den_dvd_of_is_root hΨ_zero
  rw [W.leadingCoeff_Ψ₂Sq (by norm_num : (4 : ℤ) ≠ 0)] at hdvd
  have hden_eq := Rat.isFractionRingDen x
  have hdvd_nat : x.den ∣ 4 := by rw [← hden_eq]; exact Int.natAbs_dvd_natAbs.mpr hdvd
  have hfour_x : ∃ n : ℤ, (n : ℚ) = 4 * x := by
    obtain ⟨k, hk⟩ := hdvd_nat
    set d := x.den with hd_def
    set α := x.num with hα_def
    have hd_ne : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hd_def ▸ x.pos.ne')
    have hx_eq : (x : ℚ) = ↑α / ↑d := by rw [hα_def, hd_def]; exact (Rat.num_div_den x).symm
    have h4_eq : (4 : ℚ) = ↑d * ↑k := by rw [hd_def]; exact_mod_cast hk
    refine ⟨α * k, ?_⟩
    rw [hx_eq, h4_eq]
    push_cast
    field_simp
  obtain ⟨n₀, hn₀⟩ := hfour_x
  exact ⟨⟨n₀, hn₀⟩, -(W.a₁ * n₀) - 4 * W.a₃, by
    push_cast; linarith [show (↑W.a₁ : ℚ) * ↑n₀ = 4 * ↑W.a₁ * x from by rw [hn₀]; ring]⟩

end LutzNagellTheorem
end LutzNagell
