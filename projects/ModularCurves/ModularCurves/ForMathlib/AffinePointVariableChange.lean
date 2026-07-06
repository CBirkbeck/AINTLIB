/-
Copyright (c) 2026 Christopher Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# General coordinate change on affine points of a Weierstrass curve

mathlib provides the action `C • W` of a `WeierstrassCurve.VariableChange` on a curve, together
with the special-case transports `equation_iff_variableChange` / `nonsingular_iff_variableChange`
(which move a single point to the origin, i.e. `C = (1, x, 0, y)`). Descending a group law across
charts (ticket `T-W7`) needs the **general**-`C` coordinate transformation `(x, y) ↦ (X, Y)` and
the fact that it carries `Equation`/`Nonsingular` on `W` to `Equation`/`Nonsingular` on `C • W`.

For `C = (u, r, s, t)` the substitution is `x = u²X + r`, `y = u³Y + u²sX + t`; solving for the new
coordinates gives `X = u⁻²(x - r)` and `Y = u⁻³(y - s(x - r) - t)`. Under this substitution the
affine Weierstrass polynomial scales by `u⁻⁶`, so the defining equation is preserved.

## Main definitions

* `WeierstrassCurve.VariableChange.vcX` / `vcY`: the transformed affine coordinates.

## Main results

* `WeierstrassCurve.VariableChange.equation_smul`: `C • W` satisfies the Weierstrass equation at
  the transformed coordinates whenever `W` does at `(x, y)`.
-/

namespace WeierstrassCurve.VariableChange

variable {R : Type*} [CommRing R] (C : VariableChange R)

/-- The `x`-coordinate of `(x, y)` after the coordinate change `C = (u, r, s, t)`: `u⁻²(x - r)`. -/
def vcX (x : R) : R := (↑C.u⁻¹ : R) ^ 2 * (x - C.r)

/-- The `y`-coordinate of `(x, y)` after the coordinate change `C = (u, r, s, t)`:
`u⁻³(y - s(x - r) - t)`. -/
def vcY (x y : R) : R := (↑C.u⁻¹ : R) ^ 3 * (y - C.s * (x - C.r) - C.t)

variable (W : WeierstrassCurve R)

/-- The general coordinate change `C` carries a solution of the Weierstrass equation of `W` to a
solution of the equation of `C • W`: the equation polynomial scales by `u⁻⁶`. -/
lemma equation_smul {x y : R} (h : W.toAffine.Equation x y) :
    (C • W).toAffine.Equation (C.vcX x) (C.vcY x y) := by
  rw [Affine.equation_iff] at h ⊢
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, vcX, vcY]
  linear_combination (↑C.u⁻¹ : R) ^ 6 * h

/-- The general coordinate change `C` preserves nonsingularity: the gradient of the Weierstrass
polynomial transforms by an invertible Jacobian (`∂/∂Y ↦ u⁻³·∂/∂Y`,
`∂/∂X ↦ u⁻⁴(∂/∂X + s·∂/∂Y)`), so a smooth point of `W` maps to a smooth point of `C • W`. -/
lemma nonsingular_smul {x y : R} (h : W.toAffine.Nonsingular x y) :
    (C • W).toAffine.Nonsingular (C.vcX x) (C.vcY x y) := by
  rw [Affine.nonsingular_iff] at h ⊢
  obtain ⟨heq, hns⟩ := h
  refine ⟨equation_smul C W heq, ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨hc1, hc2⟩ := hc
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    vcX, vcY] at hc1 hc2
  have hu3 : IsUnit ((↑C.u⁻¹ : R) ^ 3) := C.u⁻¹.isUnit.pow 3
  have hu4 : IsUnit ((↑C.u⁻¹ : R) ^ 4) := C.u⁻¹.isUnit.pow 4
  have hdY : 2 * y + W.a₁ * x + W.a₃ = 0 :=
    hu3.mul_right_eq_zero.mp (by linear_combination hc2)
  have hdX : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0 :=
    hu4.mul_right_eq_zero.mp (by
      linear_combination hc1 - (↑C.u⁻¹ : R) ^ 4 * C.s * hdY)
  rcases hns with hns | hns
  · exact hns (by linear_combination hdX)
  · exact hns (by linear_combination hdY)

/-- The map on affine points induced by the coordinate change `C`, sending a point `(x, y)` on `W`
to `(u⁻²(x - r), u⁻³(y - s(x - r) - t))` on `C • W` (and the point at infinity to itself). -/
def pointMap : W.toAffine.Point → (C • W).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (C.vcX x) (C.vcY x y) (nonsingular_smul C W h)

@[simp] lemma pointMap_zero : C.pointMap W .zero = .zero := rfl

@[simp] lemma pointMap_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    C.pointMap W (.some x y h) = .some (C.vcX x) (C.vcY x y) (nonsingular_smul C W h) := rfl

/-- The coordinate change commutes with the `y`-negation `negY`: transforming then negating equals
negating then transforming. This is the coordinate identity behind `pointMap_neg`. -/
lemma negY_smul (x y : R) :
    (C • W).toAffine.negY (C.vcX x) (C.vcY x y) = C.vcY x (W.toAffine.negY x y) := by
  simp only [Affine.negY, variableChange_a₁, variableChange_a₃, vcX, vcY]
  ring

/-- The coordinate change transforms the `x`-coordinate of a sum: for the transformed slope
`u⁻¹(ℓ - s)`, the `addX` of `C • W` is `vcX` of the `addX` of `W`. A polynomial identity in `ℓ`. -/
lemma addX_smul (x₁ x₂ ℓ : R) :
    (C • W).toAffine.addX (C.vcX x₁) (C.vcX x₂) (↑C.u⁻¹ * (ℓ - C.s))
      = C.vcX (W.toAffine.addX x₁ x₂ ℓ) := by
  simp only [Affine.addX, variableChange_a₁, variableChange_a₂, vcX]
  ring

/-- The coordinate change transforms the pre-negation `y`-coordinate of a sum. -/
lemma negAddY_smul (x₁ x₂ y₁ ℓ : R) :
    (C • W).toAffine.negAddY (C.vcX x₁) (C.vcX x₂) (C.vcY x₁ y₁) (↑C.u⁻¹ * (ℓ - C.s))
      = C.vcY (W.toAffine.addX x₁ x₂ ℓ) (W.toAffine.negAddY x₁ x₂ y₁ ℓ) := by
  simp only [Affine.negAddY, Affine.addX, variableChange_a₁, variableChange_a₂, vcX, vcY]
  ring

/-- The coordinate change transforms the `y`-coordinate of a sum. -/
lemma addY_smul (x₁ x₂ y₁ ℓ : R) :
    (C • W).toAffine.addY (C.vcX x₁) (C.vcX x₂) (C.vcY x₁ y₁) (↑C.u⁻¹ * (ℓ - C.s))
      = C.vcY (W.toAffine.addX x₁ x₂ ℓ) (W.toAffine.addY x₁ x₂ y₁ ℓ) := by
  rw [Affine.addY, Affine.addY, addX_smul, negAddY_smul, negY_smul]

/-- The induced point map is a group anti/homomorphism for negation: `pointMap (-P) = -pointMap P`.
Valid over any `CommRing` (mathlib's `Point.neg` needs no field). -/
lemma pointMap_neg (P : W.toAffine.Point) : C.pointMap W (-P) = -(C.pointMap W P) := by
  cases P with
  | zero => rfl
  | some x y h => rw [Affine.Point.neg_some, pointMap_some, pointMap_some,
      Affine.Point.neg_some]; simp only [negY_smul]

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} (C : VariableChange F)

/-- The coordinate change scales the addition `slope` (secant case): the secant of `C • W` through
the transformed points is `u⁻¹` times the `s`-shifted secant of `W`. -/
lemma slope_smul_of_X_ne {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) :
    (C • W).toAffine.slope (C.vcX x₁) (C.vcX x₂) (C.vcY x₁ y₁) (C.vcY x₂ y₂)
      = ↑C.u⁻¹ * (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s) := by
  have hu : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
  have hx' : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hvx : C.vcX x₁ ≠ C.vcX x₂ := by
    simp only [vcX]
    intro he
    have hcancel : x₁ - C.r = x₂ - C.r := mul_left_cancel₀ (pow_ne_zero 2 hu) he
    exact hx (by linear_combination hcancel)
  have hnum : C.vcY x₁ y₁ - C.vcY x₂ y₂ = ↑C.u⁻¹ ^ 3 * ((y₁ - y₂) - C.s * (x₁ - x₂)) := by
    simp only [vcY]; ring
  have hden : C.vcX x₁ - C.vcX x₂ = ↑C.u⁻¹ ^ 2 * (x₁ - x₂) := by simp only [vcX]; ring
  rw [Affine.slope_of_X_ne hvx, Affine.slope_of_X_ne hx, hnum, hden]
  field_simp

/-- The coordinate change scales the addition `slope` (tangent case): the tangent slope of `C • W`
at the transformed point is `u⁻¹` times the `s`-shifted tangent slope of `W`. The hypothesis
`hne` (the point is not `2`-torsion) makes the tangent denominator nonzero; in the group-law
`else` branch it follows from the two points lying on the curve. -/
lemma slope_smul_of_Y_ne {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ ≠ W.toAffine.negY x₂ y₂)
    (hne : y₁ ≠ W.toAffine.negY x₁ y₁) :
    (C • W).toAffine.slope (C.vcX x₁) (C.vcX x₂) (C.vcY x₁ y₁) (C.vcY x₂ y₂)
      = ↑C.u⁻¹ * (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s) := by
  subst hx
  have hu : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
  have hvy : C.vcY x₁ y₁ ≠ (C • W).toAffine.negY (C.vcX x₁) (C.vcY x₁ y₂) := by
    rw [negY_smul]
    simp only [vcY]
    intro he
    exact hy (by linear_combination mul_left_cancel₀ (pow_ne_zero 3 hu) he)
  have hd : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hne
  have hnum : 3 * C.vcX x₁ ^ 2 + 2 * (C • W).toAffine.a₂ * C.vcX x₁ + (C • W).toAffine.a₄
        - (C • W).toAffine.a₁ * C.vcY x₁ y₁
      = ↑C.u⁻¹ ^ 4 * ((3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁)
        - C.s * (y₁ - W.toAffine.negY x₁ y₁)) := by
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₄, Affine.negY, vcX, vcY]; ring
  have hden : C.vcY x₁ y₁ - (C • W).toAffine.negY (C.vcX x₁) (C.vcY x₁ y₁)
      = ↑C.u⁻¹ ^ 3 * (y₁ - W.toAffine.negY x₁ y₁) := by
    rw [negY_smul]; simp only [vcY]; ring
  rw [Affine.slope_of_Y_ne rfl hvy, Affine.slope_of_Y_ne rfl hy, hnum, hden]
  field_simp

/-- The coordinate change scales the addition `slope` by `u⁻¹` (with the `s`-shift), in either the
secant or tangent branch of the group law (i.e. whenever the sum is not the point at infinity). -/
lemma slope_smul {x₁ x₂ y₁ y₂ : F} (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂))
    (hne : x₁ = x₂ → y₁ ≠ W.toAffine.negY x₁ y₁) :
    (C • W).toAffine.slope (C.vcX x₁) (C.vcX x₂) (C.vcY x₁ y₁) (C.vcY x₂ y₂)
      = ↑C.u⁻¹ * (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s) := by
  by_cases hx : x₁ = x₂
  · exact slope_smul_of_Y_ne C hx (fun hy => hxy ⟨hx, hy⟩) (hne hx)
  · exact slope_smul_of_X_ne C hx

end Field

end WeierstrassCurve.VariableChange
