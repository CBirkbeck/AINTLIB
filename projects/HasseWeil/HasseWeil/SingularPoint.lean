/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Singular points on Weierstrass curves

We characterize singular points on Weierstrass curves and prove that a Weierstrass curve
(over an algebraically closed field of characteristic ≠ 2) has a singular point iff `Δ = 0`.
We also prove the node/cusp dichotomy: a singular point is a node (two distinct tangent
directions) iff `c₄ ≠ 0`, and a cusp (one tangent direction) iff `c₄ = 0`.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.4
-/

open Polynomial WeierstrassCurve

variable {R : Type*} [CommRing R]

namespace WeierstrassCurve

/-! ### Singular points -/

/-- A point `(x, y)` is **singular** on the Weierstrass curve `W` if it satisfies the
equation and both partial derivatives vanish. Reference: Silverman III.1.4. -/
def Singular (W : WeierstrassCurve R) (x y : R) : Prop :=
  W.toAffine.Equation x y ∧
  W.toAffine.polynomialX.evalEval x y = 0 ∧
  W.toAffine.polynomialY.evalEval x y = 0

variable {W : WeierstrassCurve R}

theorem Singular.equation {x y : R} (h : W.Singular x y) :
    W.toAffine.Equation x y := h.1

theorem Singular.not_nonsingular {x y : R} (h : W.Singular x y) :
    ¬W.toAffine.Nonsingular x y := by
  rintro ⟨_, hx | hy⟩
  · exact hx h.2.1
  · exact hy h.2.2

/-! ### Δ = 0 from a singular point -/

variable {F : Type*} [Field F]

/-- A singular point on a Weierstrass curve over a field forces `Δ = 0`. -/
theorem Δ_eq_zero_of_singular {W : WeierstrassCurve F} {x y : F}
    (h : W.Singular x y) : W.Δ = 0 := by
  by_contra hΔ
  exact h.not_nonsingular
    ((Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp h.equation)

/-! ### Tangent cone discriminant -/

/-- The tangent cone discriminant at a point with `x`-coordinate `x₀` on a Weierstrass curve.
At a singular point, this determines whether the singularity is a node (`≠ 0`) or cusp (`= 0`).
It is the discriminant of the quadratic form `Y² + a₁XY - (3x₀ + a₂)X²`. -/
def tangentConeDisc (W : WeierstrassCurve R) (x : R) : R :=
  W.a₁ ^ 2 + 12 * x + 4 * W.a₂

/-- At a singular point, `c₄ = (tangentConeDisc x₀)²`.
The proof uses the singularity conditions `∂F/∂X = 0` and `∂F/∂Y = 0` to eliminate
`a₃` and `a₄` from the expression `c₄ = b₂² - 24b₄`. -/
theorem c₄_eq_tangentConeDisc_sq_of_singular {W : WeierstrassCurve R} {x y : R}
    (h : W.Singular x y) : W.c₄ = (W.tangentConeDisc x) ^ 2 := by
  obtain ⟨_, hpX, hpY⟩ := h
  rw [Affine.evalEval_polynomialX] at hpX
  rw [Affine.evalEval_polynomialY] at hpY
  simp only [c₄, b₂, b₄, tangentConeDisc]
  linear_combination (48 : R) * hpX + (-24 * W.a₁) * hpY

/-! ### Existence of singular points when Δ = 0 -/

section ExistsSingular

variable (W : WeierstrassCurve F) [IsAlgClosed F]

/-- Over an algebraically closed field of characteristic ≠ 2, `Δ = 0` implies
the existence of a singular point on the Weierstrass curve.

The proof uses `twoTorsionPolynomial_discr : discr(4x³ + b₂x² + 2b₄x + b₆) = 16Δ`.
When `Δ = 0`, the cubic has a repeated root `x₀`. Setting `y₀ = -(a₁x₀ + a₃)/2`,
the point `(x₀, y₀)` is singular on the curve.

Reference: Silverman III.1.4. -/
theorem exists_singular_of_Δ_eq_zero (h2 : (2 : F) ≠ 0) (hΔ : W.Δ = 0) :
    ∃ x y, W.Singular x y := by
  have h4 : (4 : F) ≠ 0 := by
    intro h; apply h2
    have h22 : (4 : F) = 2 * 2 := by ring
    rw [h22] at h; exact mul_self_eq_zero.mp h
  have ha : W.twoTorsionPolynomial.a ≠ (0 : F) := h4
  have hdisc : W.twoTorsionPolynomial.discr = 0 := by
    rw [twoTorsionPolynomial_discr, hΔ, mul_zero]
  have hsplits : (W.twoTorsionPolynomial.toPoly.map (RingHom.id F)).Splits :=
    IsAlgClosed.splits _
  obtain ⟨x, y, z, hroots⟩ := (Cubic.splits_iff_roots_eq_three ha).mp hsplits
  have hdup : x = y ∨ x = z ∨ y = z := by
    by_contra hall
    push Not at hall
    exact absurd ⟨hall.1, hall.2.1, hall.2.2⟩
      (not_not.mpr hdisc ∘ (Cubic.discr_ne_zero_iff_roots_ne ha hroots).mpr)
  suffices key : ∀ (x₀ : F),
      W.twoTorsionPolynomial.toPoly.eval x₀ = 0 →
      W.twoTorsionPolynomial.toPoly.derivative.eval x₀ = 0 →
      W.Singular x₀ (-(W.a₁ * x₀ + W.a₃) / 2) by
    have hfact := Cubic.eq_prod_three_roots ha hroots
    have htp : W.twoTorsionPolynomial.toPoly =
        (Cubic.map (RingHom.id F) W.twoTorsionPolynomial).toPoly := by
      simp [Cubic.map_toPoly, Polynomial.map_id]
    rcases hdup with hxy | hxz | hyz
    · subst hxy
      refine ⟨x, _, key x ?_ ?_⟩
      · rw [htp, hfact]
        simp [eval_mul, eval_sub, eval_C, eval_X, RingHom.id_apply, sub_self]
      · rw [htp, hfact]
        simp only [derivative_mul, derivative_C, derivative_sub, derivative_X,
          eval_mul, eval_add, eval_sub, eval_C, eval_X, eval_one,
          RingHom.id_apply, sub_self, zero_mul, mul_zero, add_zero]
    · subst hxz
      refine ⟨x, _, key x ?_ ?_⟩
      · rw [htp, hfact]
        simp [eval_mul, eval_sub, eval_C, eval_X, RingHom.id_apply, sub_self]
      · rw [htp, hfact]
        simp only [derivative_mul, derivative_C, derivative_sub, derivative_X,
          eval_mul, eval_add, eval_sub, eval_C, eval_X, eval_one,
          RingHom.id_apply, sub_self, zero_mul, mul_zero, add_zero]
    · subst hyz
      refine ⟨y, _, key y ?_ ?_⟩
      · rw [htp, hfact]
        simp [eval_mul, eval_sub, eval_C, eval_X, RingHom.id_apply, sub_self]
      · rw [htp, hfact]
        simp only [derivative_mul, derivative_C, derivative_sub, derivative_X,
          eval_mul, eval_add, eval_sub, eval_C, eval_X, eval_one,
          RingHom.id_apply, sub_self, zero_mul, mul_zero, add_zero]
  intro x₀ heval hderiv
  set y₀ := -(W.a₁ * x₀ + W.a₃) / 2 with hy₀def
  have hpY : W.toAffine.polynomialY.evalEval x₀ y₀ = 0 := by
    rw [Affine.evalEval_polynomialY, hy₀def]; field_simp; ring
  have hy₀ : 2 * y₀ = -(W.a₁ * x₀ + W.a₃) := by rw [hy₀def]; field_simp
  have heq : W.toAffine.Equation x₀ y₀ := by
    rw [Affine.equation_iff']
    simp only [twoTorsionPolynomial, Cubic.toPoly, b₂, b₄, b₆,
      eval_add, eval_mul, eval_C, eval_X, eval_pow] at heval
    have hsq : (2 * y₀) ^ 2 = (W.a₁ * x₀ + W.a₃) ^ 2 := by rw [hy₀]; ring
    have key : 4 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ -
        (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) = 0 := by
      linear_combination hsq + 2 * (W.a₁ * x₀ + W.a₃) * hy₀ - heval
    exact or_iff_not_imp_left.mp (mul_eq_zero.mp key) h4
  have hpX : W.toAffine.polynomialX.evalEval x₀ y₀ = 0 := by
    rw [Affine.evalEval_polynomialX]
    simp only [twoTorsionPolynomial, Cubic.toPoly] at hderiv
    simp only [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_pow,
      eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero, zero_mul,
      zero_add, mul_one, b₂, b₄] at hderiv
    have key : 4 * (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) = 0 := by
      linear_combination 2 * W.a₁ * hy₀ - hderiv
    exact or_iff_not_imp_left.mp (mul_eq_zero.mp key) h4
  exact ⟨heq, hpX, hpY⟩

end ExistsSingular

/-- Over an algebraically closed field of characteristic ≠ 2, a Weierstrass curve has
a singular point if and only if `Δ = 0`. -/
theorem exists_singular_iff_Δ_eq_zero [IsAlgClosed F] {W : WeierstrassCurve F}
    (h2 : (2 : F) ≠ 0) :
    (∃ x y, W.Singular x y) ↔ W.Δ = 0 :=
  ⟨fun ⟨_, _, h⟩ ↦ Δ_eq_zero_of_singular h, exists_singular_of_Δ_eq_zero W h2⟩

/-! ### Node and cusp characterization -/

/-- A Weierstrass curve has a **node** if it has a singular point at which the tangent cone
has two distinct tangent directions (nonzero tangent cone discriminant).
Reference: Silverman III.1.4(b). -/
def HasNode (W : WeierstrassCurve R) : Prop :=
  ∃ x y, W.Singular x y ∧ W.tangentConeDisc x ≠ 0

/-- A Weierstrass curve has a **cusp** if it has a singular point at which the tangent cone
has a single tangent direction (zero tangent cone discriminant).
Reference: Silverman III.1.4(c). -/
def HasCusp (W : WeierstrassCurve R) : Prop :=
  ∃ x y, W.Singular x y ∧ W.tangentConeDisc x = 0

theorem HasNode.Δ_eq_zero_and_c₄_ne_zero {W : WeierstrassCurve F} (h : W.HasNode) :
    W.Δ = 0 ∧ W.c₄ ≠ 0 := by
  obtain ⟨x, y, hsing, hdisc⟩ := h
  exact ⟨Δ_eq_zero_of_singular hsing,
    by rw [c₄_eq_tangentConeDisc_sq_of_singular hsing]; exact pow_ne_zero 2 hdisc⟩

theorem HasCusp.Δ_eq_zero_and_c₄_eq_zero {W : WeierstrassCurve F} (h : W.HasCusp) :
    W.Δ = 0 ∧ W.c₄ = 0 := by
  obtain ⟨x, y, hsing, hdisc⟩ := h
  exact ⟨Δ_eq_zero_of_singular hsing,
    by rw [c₄_eq_tangentConeDisc_sq_of_singular hsing, hdisc]; ring⟩

/-- Over an algebraically closed field of characteristic ≠ 2, a Weierstrass curve has a node
iff `Δ = 0 ∧ c₄ ≠ 0`. Reference: Silverman III.1.4(b). -/
theorem hasNode_iff [IsAlgClosed F] {W : WeierstrassCurve F} (h2 : (2 : F) ≠ 0) :
    W.HasNode ↔ W.Δ = 0 ∧ W.c₄ ≠ 0 := by
  constructor
  · exact HasNode.Δ_eq_zero_and_c₄_ne_zero
  · intro ⟨hΔ, hc₄⟩
    obtain ⟨x₀, y₀, hsing⟩ := exists_singular_of_Δ_eq_zero W h2 hΔ
    exact ⟨x₀, y₀, hsing, fun hdisc ↦ hc₄ (by
      rw [c₄_eq_tangentConeDisc_sq_of_singular hsing, hdisc]; ring)⟩

/-- Over an algebraically closed field of characteristic ≠ 2, a Weierstrass curve has a cusp
iff `Δ = 0 ∧ c₄ = 0`. Reference: Silverman III.1.4(c). -/
theorem hasCusp_iff [IsAlgClosed F] {W : WeierstrassCurve F} (h2 : (2 : F) ≠ 0) :
    W.HasCusp ↔ W.Δ = 0 ∧ W.c₄ = 0 := by
  constructor
  · exact HasCusp.Δ_eq_zero_and_c₄_eq_zero
  · intro ⟨hΔ, hc₄⟩
    obtain ⟨x₀, y₀, hsing⟩ := exists_singular_of_Δ_eq_zero W h2 hΔ
    exact ⟨x₀, y₀, hsing,
      sq_eq_zero_iff.mp (by rwa [← c₄_eq_tangentConeDisc_sq_of_singular hsing])⟩

end WeierstrassCurve
