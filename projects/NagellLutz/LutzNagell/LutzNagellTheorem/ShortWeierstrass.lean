import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic.Ring

/-!
# Short Weierstrass model for Lutz-Nagell

This file sets up the short Weierstrass curve

`y^2 = x^3 + A*x + B`

over `ℤ` and its base change to `ℚ`, and proves basic rewriting lemmas (equation, discriminant).

Downstream Lutz-Nagell files should import this file instead of re-expanding `Δ`/`Equation`.
-/

open scoped Polynomial.Bivariate

namespace LutzNagell
namespace LutzNagellTheorem

open WeierstrassCurve

/-- The short Weierstrass curve over `ℤ`: `y^2 = x^3 + A*x + B`. -/
def shortCurveZ (A B : ℤ) : WeierstrassCurve ℤ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B }

/-- The short Weierstrass curve over `ℚ`, obtained from `shortCurveZ` by base change. -/
def shortCurveQ (A B : ℤ) : WeierstrassCurve ℚ :=
  (shortCurveZ A B).map (algebraMap ℤ ℚ)

@[simp] lemma shortCurveZ_a₁ (A B : ℤ) : (shortCurveZ A B).a₁ = 0 := rfl
@[simp] lemma shortCurveZ_a₂ (A B : ℤ) : (shortCurveZ A B).a₂ = 0 := rfl
@[simp] lemma shortCurveZ_a₃ (A B : ℤ) : (shortCurveZ A B).a₃ = 0 := rfl
@[simp] lemma shortCurveZ_a₄ (A B : ℤ) : (shortCurveZ A B).a₄ = A := rfl
@[simp] lemma shortCurveZ_a₆ (A B : ℤ) : (shortCurveZ A B).a₆ = B := rfl

@[simp] lemma shortCurveQ_a₁ (A B : ℤ) : (shortCurveQ A B).a₁ = 0 := by
  simp [shortCurveQ, shortCurveZ]

@[simp] lemma shortCurveQ_a₂ (A B : ℤ) : (shortCurveQ A B).a₂ = 0 := by
  simp [shortCurveQ, shortCurveZ]

@[simp] lemma shortCurveQ_a₃ (A B : ℤ) : (shortCurveQ A B).a₃ = 0 := by
  simp [shortCurveQ, shortCurveZ]

@[simp] lemma shortCurveQ_a₄ (A B : ℤ) : (shortCurveQ A B).a₄ = (A : ℚ) := by
  simp [shortCurveQ, shortCurveZ]

@[simp] lemma shortCurveQ_a₆ (A B : ℤ) : (shortCurveQ A B).a₆ = (B : ℚ) := by
  simp [shortCurveQ, shortCurveZ]

lemma shortCurveQ_equation_iff (A B : ℤ) (x y : ℚ) :
    (shortCurveQ A B).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + (A : ℚ) * x + (B : ℚ) := by
  simpa [shortCurveQ, shortCurveZ, add_assoc, add_comm, add_left_comm, mul_assoc]
    using (WeierstrassCurve.Affine.equation_iff (W := shortCurveQ A B) x y)

lemma shortCurveZ_delta (A B : ℤ) :
    (shortCurveZ A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, shortCurveZ]
  ring1

end LutzNagellTheorem
end LutzNagell
