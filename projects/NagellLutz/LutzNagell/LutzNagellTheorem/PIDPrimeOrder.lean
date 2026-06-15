import LutzNagell.DivisionPolynomialDegree
import LutzNagell.ZSMul
import LutzNagell.LutzNagellTheorem.PIDDenominators
import LutzNagell.LutzNagellTheorem.EvalBridge
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Prime-order torsion integrality for Weierstrass curves over UFDs

Generalization of `GeneralPrimeOrder.lean` from `ℤ/ℚ` to a UFD `R` with fraction field `K`.

When `(p : R)` is squarefree (i.e., `p` does not ramify in `R`), torsion points of
odd prime order `p` have integral coordinates. More generally, every prime factor of the
denominator must appear with multiplicity ≥ 2 in the division polynomial's leading coefficient.

## Main results

* `y_isInteger_of_x_isInteger_on_curve`: y ∈ R from x ∈ R on the curve.
* `isInteger_of_root_squarefree_leading_coeff`: the core new theorem — x ∈ R when the
  relevant leading coeff is squarefree. Combines the rational root theorem with the
  generalized denominator lemma.
-/

namespace LutzNagell
namespace PID

open WeierstrassCurve Polynomial IsFractionRing

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
variable (W : WeierstrassCurve R)

/-! ### y integral from x integral on curve -/

omit [DecidableEq K] in
/-- If `(x, y)` lies on the curve with `aᵢ ∈ R` and `x ∈ R`, then `y ∈ R`. -/
theorem y_isInteger_of_x_isInteger_on_curve
    {x y : K}
    (hcurve : y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆)
    {x₀ : R} (hx : algebraMap R K x₀ = x) :
    IsLocalization.IsInteger R y := by
  set c₁ : R := W.a₁ * x₀ + W.a₃
  set c₀ : R := -(x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)
  have hroot : aeval y (X ^ 2 + C c₁ * X + C c₀ : R[X]) = 0 := by
    simp only [map_add, map_mul, map_pow, map_neg, aeval_X, aeval_C, c₁, c₀]
    have hc := hcurve; rw [← hx] at hc; linear_combination hc
  have hmonic : (X ^ 2 + C c₁ * X + C c₀ : R[X]).Monic := by
    apply Polynomial.Monic.add_of_left
    · exact Polynomial.Monic.add_of_left (monic_X_pow 2)
        (degree_C_mul_X_le c₁ |>.trans_lt (by norm_num [degree_X_pow]))
    · exact degree_C_le.trans_lt (by
        rw [degree_add_eq_left_of_degree_lt
          (degree_C_mul_X_le c₁ |>.trans_lt (by norm_num [degree_X_pow]))]
        norm_num [degree_X_pow])
  exact isInteger_of_is_root_of_monic hmonic hroot

/-! ### Extract ψ = 0 from torsion -/

omit [IsDomain R] [UniqueFactorizationMonoid R] [DecidableEq K] [IsFractionRing R K] in
/-- If `n • P = 0` in the Jacobian point group, then `ψ_n(x,y) = 0`. -/
theorem evalEval_ψ_eq_zero_of_zsmul_eq_zero
    {x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y) (n : ℤ)
    (htors : n • (Jacobian.Point.fromAffine
      (Affine.Point.some _ _ hns)) = 0) :
    ((curveK R K W).ψ n).evalEval x y = 0 := by
  have heval := zsmul_eq_smulEval (curveK R K W) hns n
  have hzero := Jacobian.Point.zero_point (W' := (curveK R K W).toJacobian)
  rw [Jacobian.Point.ext_iff] at htors
  rw [heval, hzero] at htors
  exact (Jacobian.Z_eq_zero_of_equiv (Quotient.exact htors)).mpr rfl

/-! ### General integrality from squarefree leading coefficient -/

omit [DecidableEq K] in
/-- **Key theorem.** If `x` is a root of `f ∈ R[X]` whose leading coefficient is squarefree,
and `(x, y)` lies on the curve, then `x ∈ R`.

This combines the rational root theorem (`den ∣ leadingCoeff`) with the denominator lemma
(no prime factor of `den` can appear exactly once — but in a squarefree element, every prime
factor appears exactly once, so `den` can have no prime factors at all, hence is a unit). -/
theorem isInteger_of_root_squarefree_leading_coeff
    {x y : K}
    (heq : y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆)
    {f : R[X]} (hroot : aeval x f = 0)
    (hsf : Squarefree f.leadingCoeff) :
    IsLocalization.IsInteger R x := by
  have hdvd := den_dvd_of_is_root hroot
  have hunit : IsUnit (IsFractionRing.den R x : R) := by
    by_contra h
    have hne : (IsFractionRing.den R x : R) ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp (IsFractionRing.den R x).2
    obtain ⟨q, hq_irr, hq_dvd⟩ := WfDvdMonoid.exists_irreducible_factor h hne
    have hq_prime : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq_irr
    have hq2_not : ¬ q ^ 2 ∣ (IsFractionRing.den R x : R) := by
      intro h2; rw [sq] at h2
      exact hq_prime.not_unit (hsf q (dvd_trans h2 hdvd))
    exact den_no_simple_prime_factor_of_on_curve W heq hq_prime hq_dvd hq2_not
  exact isInteger_of_isUnit_den hunit

/-! ### Odd prime torsion (squarefree case)

The following theorems connect the abstract `isInteger_of_root_squarefree_leading_coeff`
to the concrete division polynomial setting. They require matching the leading coefficient
of `preΨ_p` with `(p : R)`, which involves casting from `ℤ` to `R`.

These require matching the leading coefficient of `preΨ_p` with `(p : R)`,
which involves casting from `ℤ` to `R`. -/

omit [DecidableEq K] in
/-- For odd prime `p`, if `p • P = 0` and `(p : R)` is squarefree, then `x ∈ R`. -/
theorem x_isInteger_of_odd_prime_torsion_squarefree
    {x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y)
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (htors : (p : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0)
    (hsf : Squarefree (p : R)) :
    IsLocalization.IsInteger R x := by
  have hψ := evalEval_ψ_eq_zero_of_zsmul_eq_zero W hns (p : ℤ) htors
  have hodd_int : ¬Even (p : ℤ) := by rwa [Int.even_coe_nat, hp.even_iff]
  rw [evalEval_ψ_odd (curveK R K W) hns.left (p : ℤ) hodd_int] at hψ
  have hmap : (curveK R K W).preΨ (p : ℤ) = (W.preΨ (p : ℤ)).map (algebraMap R K) := by
    change (W.map (algebraMap R K)).preΨ (p : ℤ) = _; rw [WeierstrassCurve.map_preΨ]
  rw [hmap, eval_map] at hψ
  change aeval x (W.preΨ (p : ℤ)) = 0 at hψ
  -- The leading coeff of preΨ_p is (p : R) (for odd p), which is squarefree by hypothesis
  have hsf_lc : Squarefree (W.preΨ (↑p : ℤ)).leadingCoeff := by
    have hp_R_ne : ((↑p : ℤ) : R) ≠ 0 := by rw [Int.cast_natCast]; exact hsf.ne_zero
    rw [W.leadingCoeff_preΨ hp_R_ne]
    simp [hodd_int, Int.cast_natCast]; exact hsf
  exact isInteger_of_root_squarefree_leading_coeff W
    ((curveK_equation_iff R K W x y).mp hns.left) hψ hsf_lc

/-! ### ψ₂ = 0 implies 2•P = 0 -/

omit [IsDomain R] [UniqueFactorizationMonoid R] [IsFractionRing R K] in
/-- If `ψ₂(x,y) = 0`, then `2 • P = 0` in the affine group. -/
theorem two_nsmul_eq_zero_of_ψ₂_eq_zero
    {x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y)
    (hψ : (curveK R K W).ψ₂.evalEval x y = 0) :
    (2 : ℕ) • (Affine.Point.some _ _ hns) = 0 := by
  rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY] at hψ
  rw [two_nsmul]
  apply WeierstrassCurve.Affine.Point.add_of_Y_eq (h₁ := hns) (h₂ := hns) rfl
  simp only [WeierstrassCurve.Affine.negY, curveK]
  linear_combination hψ

/-! ### Order-4 torsion -/

/-- If `P` has 4-torsion and `Squarefree (2 : R)`, then `P` has integral coordinates. -/
theorem integrality_of_order_four_squarefree
    {x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y)
    (h4 : (4 : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0)
    (h2ne : (2 : ℕ) • (Affine.Point.some _ _ hns) ≠ 0)
    (hsf : Squarefree (2 : R)) :
    (IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y := by
  have hψ₄ := evalEval_ψ_eq_zero_of_zsmul_eq_zero W hns 4 h4
  rw [WeierstrassCurve.ψ_four] at hψ₄
  simp only [evalEval_mul, evalEval_C] at hψ₄
  rcases mul_eq_zero.mp hψ₄ with hpreΨ | hψ₂
  · have hmap : (curveK R K W).preΨ₄ = W.preΨ₄.map (algebraMap R K) := by
      change (W.map (algebraMap R K)).preΨ₄ = _; rw [WeierstrassCurve.map_preΨ₄]
    rw [hmap, eval_map] at hpreΨ
    change aeval x W.preΨ₄ = 0 at hpreΨ
    have hsf_lc : Squarefree W.preΨ₄.leadingCoeff := by
      rw [W.leadingCoeff_preΨ₄ hsf.ne_zero]; exact hsf
    have hx_int := isInteger_of_root_squarefree_leading_coeff W
      ((curveK_equation_iff R K W x y).mp hns.left) hpreΨ hsf_lc
    obtain ⟨x₀, hx₀⟩ := hx_int
    exact ⟨⟨x₀, hx₀⟩, y_isInteger_of_x_isInteger_on_curve W
      ((curveK_equation_iff R K W x y).mp hns.left) hx₀⟩
  · exact absurd (two_nsmul_eq_zero_of_ψ₂_eq_zero W hns hψ₂) h2ne

/-! ### Order-2 torsion: bounded denominators -/

omit [DecidableEq K] in
/-- If `2•P = 0`, then `den(x) ∣ (4 : R)`. Requires `(4 : R) ≠ 0`
(automatic for `CharZero R`). -/
theorem den_dvd_of_order_two (h4_ne : (4 : R) ≠ 0)
    {x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y)
    (h2 : (2 : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0) :
    (IsFractionRing.den R x : R) ∣ (4 : R) := by
  have hψ := evalEval_ψ_eq_zero_of_zsmul_eq_zero W hns 2 h2
  rw [WeierstrassCurve.ψ_two] at hψ
  have hΨ_zero : (curveK R K W).Ψ₂Sq.eval x = 0 := by
    have h := evalEval_eq_of_mk_eq (curveK R K W) hns.left
      (Affine.CoordinateRing.mk_ψ₂_sq (W := curveK R K W))
    rw [evalEval_pow, hψ, zero_pow two_ne_zero, evalEval_C] at h
    linear_combination -h
  have hmap : (curveK R K W).Ψ₂Sq = W.Ψ₂Sq.map (algebraMap R K) := by
    change (W.map (algebraMap R K)).Ψ₂Sq = _; rw [WeierstrassCurve.map_Ψ₂Sq]
  rw [hmap, eval_map] at hΨ_zero
  change aeval x W.Ψ₂Sq = 0 at hΨ_zero
  have hdvd := den_dvd_of_is_root hΨ_zero
  have := W.leadingCoeff_Ψ₂Sq h4_ne
  rw [this] at hdvd; exact hdvd

/-! ### Combined integrality -/

omit [DecidableEq K] in
/-- Full integrality for odd prime order when `(p : R)` is squarefree. -/
theorem prime_order_integrality_squarefree
    {x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y)
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (htors : (p : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0)
    (hsf : Squarefree (p : R)) :
    (IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y := by
  have hx_int := x_isInteger_of_odd_prime_torsion_squarefree W hns hp hodd htors hsf
  obtain ⟨x₀, hx₀⟩ := hx_int
  exact ⟨⟨x₀, hx₀⟩, y_isInteger_of_x_isInteger_on_curve W
    ((curveK_equation_iff R K W x y).mp hns.left) hx₀⟩

end PID
end LutzNagell
