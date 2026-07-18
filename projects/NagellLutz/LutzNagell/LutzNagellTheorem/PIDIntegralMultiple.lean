import LutzNagell.DivisionPolynomialDegree
import LutzNagell.LutzNagellTheorem.PIDPrimeOrder
import LutzNagell.ZSMul
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Integral multiple implies integral point (over integrally closed domains)

If `n • P` has integral affine coordinates on a Weierstrass curve over `K = Frac(R)`,
then `P` already has integral affine coordinates.

Generalization of `GeneralIntegralMultiple.lean` from `ℤ/ℚ` to an integrally closed
domain `R`. The integral-root step uses `IsIntegrallyClosed.isIntegral_iff` rather than
the unique-factorization integral-root theorem, so a UFD hypothesis is not needed.

## Main results

* `isInteger_of_nsmul_isInteger`: if `n • P` has integral coordinates, so does `P`.
* `x_isInteger_of_nsmul_x_isInteger`: the `x`-coordinate half (needs only `IsIntegrallyClosed`).
* `x_coord_nsmul_eq`: the coordinate identity `x' · ΨSq_n(x) = Φ_n(x)` for `n • P`.
* `monic_Φ_sub_smul_ΨSq`: the polynomial `Φ_n - c • ΨSq_n` is monic.
-/

namespace LutzNagell
namespace PID

open WeierstrassCurve Polynomial IsFractionRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
variable (W : WeierstrassCurve R)

omit [IsIntegrallyClosed R] in
/-- `Φ_n - C c * ΨSq_n` is monic over `R` for any `c : R` and `n ≠ 0` (in `R`). -/
theorem monic_Φ_sub_smul_ΨSq
    {n : ℤ} (hn : (n : R) ≠ 0) (c : R) :
    (W.Φ n - C c * W.ΨSq n).Monic := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine Polynomial.Monic.sub_of_left (leadingCoeff_Φ _ n) (degree_lt_degree ?_)
  calc (C c * W.ΨSq n).natDegree
      _ ≤ (W.ΨSq n).natDegree := natDegree_C_mul_le _ _
      _ = n.natAbs ^ 2 - 1 := natDegree_ΨSq _ hn
      _ < n.natAbs ^ 2 := Nat.pred_lt (pow_ne_zero 2 (Int.natAbs_ne_zero.mpr hn0))
      _ = (W.Φ n).natDegree := (natDegree_Φ _ n).symm

/-- The x-coordinate of `n • P` satisfies `x' · ΨSq_n(x) = Φ_n(x)`, for a Weierstrass curve
over a field. -/
theorem x_coord_nsmul_eq {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)
    {x y : F} (hns : E.toAffine.Nonsingular x y)
    {n : ℤ} (_hn : n ≠ 0)
    {x' y' : F} (hns' : E.toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns') :
    x' * (E.ΨSq n).eval x = (E.Φ n).eval x := by
  have hJac : n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) =
      Jacobian.Point.fromAffine (Affine.Point.some _ _ hns') := by
    have h := congrArg (Jacobian.Point.toAffineAddEquiv E).symm hnP
    rw [map_zsmul] at h
    simpa using h
  have hsmul := zsmul_eq_smulEval E hns n
  open Jacobian in
  have hX := X_eq_of_equiv (show smulEval E x y n ≈ ![x', y', 1] by
    rw [Jacobian.Point.ext_iff, hsmul] at hJac; exact Quotient.exact hJac)
  simp only [smulEval, Function.comp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hX
  norm_num at hX
  rw [evalEval_φ_eq_eval_Φ E hns.left n] at hX
  have hΨSq := evalEval_Ψ_sq_eq_eval_ΨSq E hns.left n
  rw [← evalEval_ψ_eq_evalEval_Ψ E hns.left n] at hΨSq
  rw [hΨSq] at hX
  exact hX.symm

/-- If `n • P` has integral x-coordinate, then `P` has integral x-coordinate. -/
theorem x_isInteger_of_nsmul_x_isInteger
    {x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0) (hn_R : (n : R) ≠ 0)
    {x' y' : K} (hns' : (curveK R K W).toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')
    {c : R} (hc : algebraMap R K c = x') :
    IsLocalization.IsInteger R x := by
  have hcoord := x_coord_nsmul_eq (curveK R K W) hns hn hns' hnP
  have hroot : aeval x (W.Φ n - C c * W.ΨSq n) = 0 := by
    simp only [← hc, curveK, map_Φ, map_ΨSq, aeval_def, eval₂_eq_eval_map, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_C, eval_sub, eval_mul, eval_C] at hcoord ⊢
    linear_combination -hcoord
  have hint : IsIntegral R x := ⟨_, monic_Φ_sub_smul_ΨSq W hn_R c, hroot⟩
  exact RingHom.mem_rangeS.mpr (IsIntegrallyClosed.isIntegral_iff.mp hint)

/-- If `n • P` has integral coordinates, then `P` has integral coordinates.

The `y`-coordinate step (`y_isInteger_of_x_isInteger_on_curve`) still goes through the
unique-factorization integral-root theorem, so this result keeps the `UniqueFactorizationMonoid`
hypothesis; the `x`-coordinate step only needs `IsIntegrallyClosed`. -/
theorem isInteger_of_nsmul_isInteger [UniqueFactorizationMonoid R]
    {x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0) (hn_R : (n : R) ≠ 0)
    {x' y' : K} (hns' : (curveK R K W).toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')
    (hx' : IsLocalization.IsInteger R x') (_hy' : IsLocalization.IsInteger R y') :
    (IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y := by
  obtain ⟨c, hc⟩ := hx'
  obtain ⟨x₀, hx₀⟩ := x_isInteger_of_nsmul_x_isInteger W hns hn hn_R hns' hnP hc
  exact ⟨⟨x₀, hx₀⟩, y_isInteger_of_x_isInteger_on_curve W
    ((curveK_equation_iff R K W x y).mp hns.left) hx₀⟩

end PID
end LutzNagell
