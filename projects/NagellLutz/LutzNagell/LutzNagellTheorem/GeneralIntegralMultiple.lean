import LutzNagell.DivisionPolynomialDegree
import LutzNagell.ZSMul
import LutzNagell.LutzNagellTheorem.EvalBridge
import LutzNagell.LutzNagellTheorem.GeneralCurve
import LutzNagell.LutzNagellTheorem.GeneralPrimeOrder
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Integral multiple implies integral point (general Weierstrass curves)

If `n • P` has integral affine coordinates on a general Weierstrass curve
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` over `ℚ` with `aᵢ ∈ ℤ`,
then `P` already has integral affine coordinates.
-/

namespace LutzNagell
namespace LutzNagellTheorem

open WeierstrassCurve Polynomial

variable (W : WeierstrassCurve ℤ)

/-! ### The x-coordinate formula -/


/-- The x-coordinate of `n • P` satisfies `x' · ΨSq_n(x) = Φ_n(x)`. -/
theorem x_coord_nsmul_eq_general
    {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y)
    {n : ℤ} (_hn : n ≠ 0)
    {x' y' : ℚ} (hns' : (curveQ W).toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns') :
    x' * ((curveQ W).ΨSq n).eval x = ((curveQ W).Φ n).eval x := by
  classical
  open Jacobian in
  have hJac : n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) =
      Jacobian.Point.fromAffine (Affine.Point.some _ _ hns') := by
    have h := congrArg (Jacobian.Point.toAffineAddEquiv (curveQ W)).symm hnP
    simp only [map_zsmul] at h
    convert h using 1 <;> rfl
  have hsmul := zsmul_eq_smulEval (curveQ W) hns n
  open Jacobian in
  have hX := X_eq_of_equiv (show smulEval (curveQ W) x y n ≈ ![x', y', 1] by
    rw [Jacobian.Point.ext_iff] at hJac; rw [hsmul] at hJac; exact Quotient.exact hJac)
  simp only [smulEval, Function.comp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hX
  norm_num at hX
  simp only [← algebraMap_int_eq, ← WeierstrassCurve.map_φ,
    ← WeierstrassCurve.map_ψ] at hX
  rw [evalEval_φ_eq_eval_Φ (curveQ W) hns.left n] at hX
  have hΨSq := evalEval_Ψ_sq_eq_eval_ΨSq (curveQ W) hns.left n
  rw [← evalEval_ψ_eq_evalEval_Ψ (curveQ W) hns.left n] at hΨSq
  rw [hΨSq] at hX
  linarith

/-! ### Monic polynomial from the coordinate formula -/

/-- `Φ_n - C c * ΨSq_n` is monic over `ℤ` for any `c : ℤ` and `n ≠ 0`. -/
theorem monic_Φ_sub_smul_ΨSq_general
    {n : ℤ} (hn : n ≠ 0) (c : ℤ) :
    (W.Φ n - C c * W.ΨSq n).Monic := by
  apply Polynomial.Monic.sub_of_left (leadingCoeff_Φ _ n)
  apply degree_lt_degree
  calc (C c * W.ΨSq n).natDegree
      _ ≤ (W.ΨSq n).natDegree := natDegree_C_mul_le _ _
      _ = n.natAbs ^ 2 - 1 := natDegree_ΨSq _ hn
      _ < n.natAbs ^ 2 := Nat.pred_lt (pow_ne_zero 2 (Int.natAbs_pos.mpr hn).ne')
      _ = (W.Φ n).natDegree := (natDegree_Φ _ n).symm

/-! ### x integral from the coordinate formula + monic polynomial -/

/-- If `n • P` has integral x-coordinate, then `P` has integral x-coordinate. -/
theorem x_integral_of_nsmul_x_integral_general
    {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0)
    {x' y' : ℚ} (hns' : (curveQ W).toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')
    {c : ℤ} (hc : (c : ℚ) = x') :
    ∃ x₀ : ℤ, (x₀ : ℚ) = x := by
  have hcoord := x_coord_nsmul_eq_general W hns hn hns' hnP
  rw [← hc] at hcoord
  have hΦ_map : (curveQ W).Φ n = (W.Φ n).map (algebraMap ℤ ℚ) := by
    simp [curveQ, map_Φ]
  have hΨSq_map : (curveQ W).ΨSq n = (W.ΨSq n).map (algebraMap ℤ ℚ) := by
    simp [curveQ, map_ΨSq]
  have hroot : aeval x (W.Φ n - C c * W.ΨSq n) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
      ← hΦ_map, ← hΨSq_map]
    simp only [algebraMap_int_eq, Int.coe_castRingHom, eval_sub, eval_mul, eval_C]
    linarith
  obtain ⟨x₀, hx₀⟩ := RingHom.mem_rangeS.mp
    (isInteger_of_is_root_of_monic (monic_Φ_sub_smul_ΨSq_general W hn c) hroot)
  exact ⟨x₀, by simpa only [algebraMap_int_eq, Int.coe_castRingHom] using hx₀⟩

/-! ### Main theorem -/

/-- If `n • P` has integral coordinates on a general integral Weierstrass curve,
then `P` has integral coordinates. -/
theorem integral_of_nsmul_integral_general
    {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0)
    {x' y' : ℚ} (hns' : (curveQ W).toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')
    (hx' : ∃ x₀ : ℤ, (x₀ : ℚ) = x') (_hy' : ∃ y₀ : ℤ, (y₀ : ℚ) = y') :
    (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y := by
  obtain ⟨c, hc⟩ := hx'
  have hx_int := x_integral_of_nsmul_x_integral_general W hns hn hns' hnP hc
  refine ⟨hx_int, ?_⟩
  obtain ⟨x₀, hx₀⟩ := hx_int
  exact y_integral_of_x_integral_on_general_curve W ((curveQ_equation_iff W x y).mp hns.left) hx₀

end LutzNagellTheorem
end LutzNagell
