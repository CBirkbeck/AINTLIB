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

* `WeierstrassCurve.VariableChange.vcX` / `vcY`: the transformed affine coordinates, with inverses
  `ivcX` / `ivcY`.
* `WeierstrassCurve.VariableChange.pointMap`: the induced map on affine points; `pointHom` /
  `pointEquiv` package it (over a field) as a group homomorphism / isomorphism.

## Main results

* `equation_smul_iff` / `nonsingular_smul_iff`: the transformed coordinates satisfy the Weierstrass
  equation / are nonsingular **iff** `(x, y)` is on `W` (preserved and reflected).
* `pointMap_add` / `pointHom` / `pointEquiv`: the elliptic-curve group law is invariant under a
  Weierstrass coordinate change, as a full group isomorphism `W.Point ≃+ (C • W).Point`. Torsion is
  carried to torsion (`pointEquiv_zsmul`).
* `vcX_comp` / `vcY_comp` / `pointMap_mul` / `pointMap_one`: the descent **cocycle** — coordinate
  changes compose (`(C * C') = C ∘ C'`) with the identity change acting trivially, so `pointMap` is
  an action of the `VariableChange` group on points.
* `vcX_map` / `vcY_map`: **naturality** in the base ring (the coordinate change commutes with ring
  maps `φ : R →+* A`).

Together these are the affine/fibrewise descent datum for the elliptic-curve group law; the
scheme-level descent (ticket `T-W7`) consumes them once the group-scheme framework is available.
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

/-- Equation-preservation is an iff: since `u⁻⁶` is a unit, the coordinate change reflects the
Weierstrass equation as well as preserving it. -/
lemma equation_smul_iff {x y : R} :
    (C • W).toAffine.Equation (C.vcX x) (C.vcY x y) ↔ W.toAffine.Equation x y := by
  rw [Affine.equation_iff, Affine.equation_iff]
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, vcX, vcY]
  constructor
  · intro h
    rw [← sub_eq_zero]
    refine (IsUnit.mul_right_eq_zero (C.u⁻¹.isUnit.pow 6)).mp ?_
    linear_combination h
  · intro h
    linear_combination (↑C.u⁻¹ : R) ^ 6 * h

/-- Nonsingularity is likewise reflected by the coordinate change (the Jacobian is invertible), so
a smooth point of `C • W` pulls back to a smooth point of `W`. -/
lemma nonsingular_smul' {x y : R} (h : (C • W).toAffine.Nonsingular (C.vcX x) (C.vcY x y)) :
    W.toAffine.Nonsingular x y := by
  rw [Affine.nonsingular_iff] at h ⊢
  obtain ⟨heq, hns⟩ := h
  refine ⟨(equation_smul_iff C W).mp heq, ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨hc1, hc2⟩ := hc
  rcases hns with hns | hns
  · refine hns ?_
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₄, vcX, vcY]
    linear_combination (↑C.u⁻¹ : R) ^ 4 * hc1 + (↑C.u⁻¹ : R) ^ 4 * C.s * hc2
  · refine hns ?_
    simp only [variableChange_a₁, variableChange_a₃, vcX, vcY]
    linear_combination (↑C.u⁻¹ : R) ^ 3 * hc2

/-- Nonsingularity is both preserved and reflected by the coordinate change. -/
lemma nonsingular_smul_iff {x y : R} :
    (C • W).toAffine.Nonsingular (C.vcX x) (C.vcY x y) ↔ W.toAffine.Nonsingular x y :=
  ⟨nonsingular_smul' C W, nonsingular_smul C W⟩

/-- The `x`-coordinate map inverse to `vcX`: `x = u²X + r`. -/
def ivcX (X : R) : R := ↑C.u ^ 2 * X + C.r

/-- The `y`-coordinate map inverse to `vcY`: `y = u³Y + s·u²X + t`. -/
def ivcY (X Y : R) : R := ↑C.u ^ 3 * Y + C.s * ↑C.u ^ 2 * X + C.t

@[simp] lemma vcX_ivcX (X : R) : C.vcX (C.ivcX X) = X := by
  have huu : (↑C.u⁻¹ : R) * ↑C.u = 1 := Units.inv_mul C.u
  simp only [vcX, ivcX]
  linear_combination (X * (↑C.u⁻¹ * ↑C.u + 1)) * huu

@[simp] lemma vcY_ivcX_ivcY (X Y : R) : C.vcY (C.ivcX X) (C.ivcY X Y) = Y := by
  have huu : (↑C.u⁻¹ : R) * ↑C.u = 1 := Units.inv_mul C.u
  simp only [vcY, ivcX, ivcY]
  linear_combination (Y * ((↑C.u⁻¹ * ↑C.u) ^ 2 + ↑C.u⁻¹ * ↑C.u + 1)) * huu

/-- Descent cocycle for the `x`-coordinate: applying `C'` then `C` is the change `C * C'`. -/
lemma vcX_comp (C C' : VariableChange R) (x : R) : (C * C').vcX x = C.vcX (C'.vcX x) := by
  have hu' : (↑C'.u⁻¹ : R) * ↑C'.u = 1 := Units.inv_mul C'.u
  simp only [vcX, mul_def, mul_inv_rev, Units.val_mul]
  linear_combination (-(↑C.u⁻¹ : R) ^ 2 * C.r * (↑C'.u⁻¹ * ↑C'.u + 1)) * hu'

/-- Descent cocycle for the `y`-coordinate. -/
lemma vcY_comp (C C' : VariableChange R) (x y : R) :
    (C * C').vcY x y = C.vcY (C'.vcX x) (C'.vcY x y) := by
  have hu' : (↑C'.u⁻¹ : R) * ↑C'.u = 1 := Units.inv_mul C'.u
  simp only [vcX, vcY, mul_def, mul_inv_rev, Units.val_mul]
  linear_combination ((↑C.u⁻¹ : R) ^ 3 * C.s *
      (-(x - C'.r) * ↑C'.u⁻¹ ^ 2 + C.r * ((↑C'.u⁻¹ * ↑C'.u) ^ 2 + ↑C'.u⁻¹ * ↑C'.u + 1))
    - (↑C.u⁻¹ : R) ^ 3 * C.t * ((↑C'.u⁻¹ * ↑C'.u) ^ 2 + ↑C'.u⁻¹ * ↑C'.u + 1)) * hu'

variable {A : Type*} [CommRing A]

/-- Naturality of `vcX` in the base ring: the coordinate change commutes with a ring map `φ`. -/
lemma vcX_map (φ : R →+* A) (C : VariableChange R) (x : R) :
    (C.map φ).vcX (φ x) = φ (C.vcX x) := by
  have hu : (↑(C.map φ).u⁻¹ : A) = φ ↑C.u⁻¹ := by
    rw [WeierstrassCurve.VariableChange.map_u]; simp
  simp only [vcX, hu, WeierstrassCurve.VariableChange.map_r, map_mul, map_pow, map_sub]

/-- Naturality of `vcY` in the base ring. -/
lemma vcY_map (φ : R →+* A) (C : VariableChange R) (x y : R) :
    (C.map φ).vcY (φ x) (φ y) = φ (C.vcY x y) := by
  have hu : (↑(C.map φ).u⁻¹ : A) = φ ↑C.u⁻¹ := by
    rw [WeierstrassCurve.VariableChange.map_u]; simp
  simp only [vcY, hu, WeierstrassCurve.VariableChange.map_r, WeierstrassCurve.VariableChange.map_s,
    WeierstrassCurve.VariableChange.map_t, map_mul, map_pow, map_sub]

/-- The map on affine points induced by the coordinate change `C`, sending a point `(x, y)` on `W`
to `(u⁻²(x - r), u⁻³(y - s(x - r) - t))` on `C • W` (and the point at infinity to itself). -/
def pointMap : W.toAffine.Point → (C • W).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (C.vcX x) (C.vcY x y) (nonsingular_smul C W h)

@[simp] lemma pointMap_zero : C.pointMap W .zero = .zero := rfl

@[simp] lemma pointMap_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    C.pointMap W (.some x y h) = .some (C.vcX x) (C.vcY x y) (nonsingular_smul C W h) := rfl

private lemma eqRec_point_zero {W₁ W₂ : WeierstrassCurve R} (h : W₁ = W₂) :
    h ▸ (Affine.Point.zero : W₁.toAffine.Point) = Affine.Point.zero := by subst h; rfl

private lemma eqRec_point_some {W₁ W₂ : WeierstrassCurve R} (h : W₁ = W₂) {x y : R}
    (hns : W₁.toAffine.Nonsingular x y) :
    h ▸ (Affine.Point.some x y hns : W₁.toAffine.Point) = Affine.Point.some x y (h ▸ hns) := by
  subst h; rfl

/-- Point-level descent cocycle: transporting `(C * C').pointMap` along `mul_smul` equals
`C.pointMap ∘ C'.pointMap`. The content is the coordinate cocycle `vcX_comp`/`vcY_comp`. -/
lemma pointMap_mul (C C' : VariableChange R) (P : W.toAffine.Point) :
    mul_smul C C' W ▸ (C * C').pointMap W P = C.pointMap (C' • W) (C'.pointMap W P) := by
  cases P with
  | zero => rw [pointMap_zero, eqRec_point_zero]; rfl
  | some x y h =>
    rw [pointMap_some, pointMap_some, pointMap_some, eqRec_point_some]
    simp only [vcX_comp, vcY_comp]

/-- Unit condition of the descent cocycle: the identity coordinate change induces the identity on
points (transported along `one_smul`). With `pointMap_mul` this makes `pointMap` an action. -/
lemma pointMap_one (P : W.toAffine.Point) :
    one_smul (M := VariableChange R) W ▸ (1 : VariableChange R).pointMap W P = P := by
  have hX : ∀ x : R, (1 : VariableChange R).vcX x = x := fun x => by
    rw [show (1 : VariableChange R) = ⟨1, 0, 0, 0⟩ from rfl]; simp [vcX]
  have hY : ∀ x y : R, (1 : VariableChange R).vcY x y = y := fun x y => by
    rw [show (1 : VariableChange R) = ⟨1, 0, 0, 0⟩ from rfl]; simp [vcY]
  cases P with
  | zero => rw [pointMap_zero, eqRec_point_zero]
  | some x y h => rw [pointMap_some, eqRec_point_some]; simp only [hX, hY]

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

omit [DecidableEq F] in
/-- `vcX` is injective (the coordinate change scales by the unit `u⁻²`). -/
lemma vcX_ne {x₁ x₂ : F} (hx : x₁ ≠ x₂) : C.vcX x₁ ≠ C.vcX x₂ := fun he =>
  hx (by
    have := mul_left_cancel₀ (pow_ne_zero 2 (Units.ne_zero C.u⁻¹)) (by simpa only [vcX] using he)
    linear_combination this)

/-- The induced point map is additive: `pointMap (P + Q) = pointMap P + pointMap Q`. Together with
`pointMap_neg` this makes `pointMap` a group homomorphism `W.Point → (C • W).Point` — the affine
statement that the group law is invariant under the coordinate change (ticket `T-W7`). -/
lemma pointMap_add (P Q : W.toAffine.Point) :
    C.pointMap W (P + Q) = C.pointMap W P + C.pointMap W Q := by
  cases P with
  | zero =>
    show C.pointMap W (0 + Q) = C.pointMap W 0 + C.pointMap W Q
    rw [zero_add, show C.pointMap W (0 : W.toAffine.Point) = 0 from rfl, zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      show C.pointMap W (.some x₁ y₁ h₁ + 0)
        = C.pointMap W (.some x₁ y₁ h₁) + C.pointMap W 0
      rw [add_zero, show C.pointMap W (0 : W.toAffine.Point) = 0 from rfl, add_zero]
    | some x₂ y₂ h₂ =>
      rw [pointMap_some, pointMap_some]
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
      · obtain ⟨hx, hy⟩ := hxy
        have hvy : C.vcY x₁ y₁ = (C • W).toAffine.negY (C.vcX x₂) (C.vcY x₂ y₂) := by
          rw [negY_smul, hx, hy]
        rw [Affine.Point.add_of_Y_eq hx hy, Affine.Point.add_of_Y_eq (by rw [hx]) hvy,
          show C.pointMap W (0 : W.toAffine.Point) = 0 from rfl]
      · by_cases hx : x₁ = x₂
        · have hy : y₁ ≠ W.toAffine.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
          have hne : y₁ ≠ W.toAffine.negY x₁ y₁ := by
            rcases Affine.Y_eq_of_X_eq h₁.1 h₂.1 hx with h | h
            · rw [show W.toAffine.negY x₁ y₁ = W.toAffine.negY x₂ y₂ from by rw [hx, h]]; exact hy
            · exact absurd h hy
          have hvy : C.vcY x₁ y₁ ≠ (C • W).toAffine.negY (C.vcX x₂) (C.vcY x₂ y₂) := by
            rw [hx, negY_smul]
            simp only [vcY]
            intro he
            have hc := mul_left_cancel₀ (pow_ne_zero 3 (Units.ne_zero C.u⁻¹)) he
            exact hy (by linear_combination hc)
          rw [Affine.Point.add_of_Y_ne hy, Affine.Point.add_of_Y_ne hvy, pointMap_some]
          simp only [slope_smul_of_Y_ne C hx hy hne, addX_smul, addY_smul]
        · have hvx : C.vcX x₁ ≠ C.vcX x₂ := vcX_ne C hx
          rw [Affine.Point.add_of_X_ne hx, Affine.Point.add_of_X_ne hvx, pointMap_some]
          simp only [slope_smul_of_X_ne C hx, addX_smul, addY_smul]

/-- The induced point map is injective (the coordinate change is a monomorphism on points). -/
lemma pointMap_injective : Function.Injective (C.pointMap W) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) hPQ
  · rfl
  · simp [pointMap] at hPQ
  · simp [pointMap] at hPQ
  · simp only [pointMap_some, Affine.Point.some.injEq] at hPQ
    obtain ⟨hX, hY⟩ := hPQ
    have hx : x₁ = x₂ := by by_contra hne; exact vcX_ne C hne hX
    subst hx
    have hc := mul_left_cancel₀ (pow_ne_zero 3 (Units.ne_zero C.u⁻¹)) (by simpa only [vcY] using hY)
    obtain rfl : y₁ = y₂ := by linear_combination hc
    rfl

/-- The coordinate change `C` as a group homomorphism on affine points,
`W.Point →+ (C • W).Point`. This is the affine form of the invariance of the elliptic-curve group
law under a change of Weierstrass coordinates (ticket `T-W7`). -/
def pointHom : W.toAffine.Point →+ (C • W).toAffine.Point where
  toFun := C.pointMap W
  map_zero' := rfl
  map_add' := C.pointMap_add

@[simp] lemma pointHom_apply (P : W.toAffine.Point) : C.pointHom P = C.pointMap W P := rfl

lemma pointHom_injective : Function.Injective (C.pointHom (W := W)) := C.pointMap_injective

omit [DecidableEq F] in
/-- The induced point map is surjective: every point of `C • W` is the image of its preimage under
the inverse coordinate maps `ivcX`/`ivcY`. -/
lemma pointMap_surjective : Function.Surjective (C.pointMap W) := by
  rintro (_ | ⟨X, Y, h⟩)
  · exact ⟨0, rfl⟩
  · refine ⟨.some (C.ivcX X) (C.ivcY X Y) ?_, ?_⟩
    · apply nonsingular_smul' C W
      rwa [vcX_ivcX, vcY_ivcX_ivcY]
    · rw [pointMap_some]
      simp only [vcX_ivcX, vcY_ivcX_ivcY]

/-- The coordinate change `C` as a group **isomorphism** on affine points,
`W.Point ≃+ (C • W).Point`: the elliptic-curve group law is invariant under a change of
Weierstrass coordinates (ticket `T-W7`). -/
noncomputable def pointEquiv : W.toAffine.Point ≃+ (C • W).toAffine.Point :=
  AddEquiv.ofBijective C.pointHom ⟨C.pointMap_injective, C.pointMap_surjective⟩

@[simp] lemma pointEquiv_apply (P : W.toAffine.Point) : C.pointEquiv P = C.pointMap W P := rfl

/-- The group iso is compatible with multiplication-by-`n`, so it carries `n`-torsion to
`n`-torsion — the invariance a level structure needs under a coordinate change (ticket `T-W8`). -/
lemma pointEquiv_zsmul (n : ℤ) (P : W.toAffine.Point) :
    C.pointEquiv (n • P) = n • C.pointEquiv P := map_zsmul _ _ _

end Field

end WeierstrassCurve.VariableChange
