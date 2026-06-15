import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Ring

/-!
# General Weierstrass model over a PID and its fraction field

This file sets up a general Weierstrass curve `W : WeierstrassCurve R` for a PID `R` and its
base change to the fraction field `K`, along with basic rewriting lemmas.

This generalizes `GeneralCurve.lean` from `ℤ/ℚ` to an arbitrary PID `R` with fraction field `K`.
-/

open scoped Polynomial.Bivariate

namespace LutzNagell
namespace PID

open WeierstrassCurve

variable (R : Type*) [CommRing R]
variable (K : Type*) [Field K] [Algebra R K]
variable (W : WeierstrassCurve R)

/-- The base change of `W` to the fraction field `K`. -/
abbrev curveK : WeierstrassCurve K := W.map (algebraMap R K)

@[simp] lemma curveK_a₁ : (curveK R K W).a₁ = algebraMap R K W.a₁ := by simp [curveK]
@[simp] lemma curveK_a₂ : (curveK R K W).a₂ = algebraMap R K W.a₂ := by simp [curveK]
@[simp] lemma curveK_a₃ : (curveK R K W).a₃ = algebraMap R K W.a₃ := by simp [curveK]
@[simp] lemma curveK_a₄ : (curveK R K W).a₄ = algebraMap R K W.a₄ := by simp [curveK]
@[simp] lemma curveK_a₆ : (curveK R K W).a₆ = algebraMap R K W.a₆ := by simp [curveK]

lemma curveK_equation_iff (x y : K) :
    (curveK R K W).toAffine.Equation x y ↔
      y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x +
        algebraMap R K W.a₆ := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [curveK]

end PID
end LutzNagell
