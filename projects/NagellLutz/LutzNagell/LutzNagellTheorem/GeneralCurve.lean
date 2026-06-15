import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic.Ring

/-!
# General Weierstrass model for the generalized Lutz-Nagell theorem

This file sets up a general Weierstrass curve `W : WeierstrassCurve ℤ` and its base change to `ℚ`,
along with basic rewriting lemmas (equation, coefficients).

Downstream generalized Lutz-Nagell files import this file instead of `ShortWeierstrass.lean`.
-/

open scoped Polynomial.Bivariate

namespace LutzNagell
namespace LutzNagellTheorem

open WeierstrassCurve

variable (W : WeierstrassCurve ℤ)

/-- The base change of `W` to `ℚ`. -/
abbrev curveQ (W : WeierstrassCurve ℤ) : WeierstrassCurve ℚ :=
  W.map (algebraMap ℤ ℚ)

@[simp] lemma curveQ_a₁ : (curveQ W).a₁ = (W.a₁ : ℚ) := by simp [curveQ]
@[simp] lemma curveQ_a₂ : (curveQ W).a₂ = (W.a₂ : ℚ) := by simp [curveQ]
@[simp] lemma curveQ_a₃ : (curveQ W).a₃ = (W.a₃ : ℚ) := by simp [curveQ]
@[simp] lemma curveQ_a₄ : (curveQ W).a₄ = (W.a₄ : ℚ) := by simp [curveQ]
@[simp] lemma curveQ_a₆ : (curveQ W).a₆ = (W.a₆ : ℚ) := by simp [curveQ]

lemma curveQ_equation_iff (x y : ℚ) :
    (curveQ W).toAffine.Equation x y ↔
      y ^ 2 + (W.a₁ : ℚ) * x * y + (W.a₃ : ℚ) * y =
        x ^ 3 + (W.a₂ : ℚ) * x ^ 2 + (W.a₄ : ℚ) * x + (W.a₆ : ℚ) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [curveQ]

end LutzNagellTheorem
end LutzNagell
