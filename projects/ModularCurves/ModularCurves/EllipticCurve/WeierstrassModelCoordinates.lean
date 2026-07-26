/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.WeierstrassModel

/-!
# Homogeneous coordinates on a projective Weierstrass model

A triple satisfying the homogeneous Weierstrass equation induces an evaluation
map from the model's homogeneous coordinate ring. If one coordinate is a unit,
this map sends the irrelevant ideal onto the unit ideal, which is the algebraic
input required by `Proj.fromOfGlobalSections`.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace WeierstrassCurve.Projective

variable {R : Type u} [CommRing R]

/-- A generalized Weierstrass relation in a Cartier frame gives homogeneous
projective coordinates `[Xr:Y:r³]` on the corresponding cubic. -/
lemma equation_X_mul_r_Y_r_pow_three
    (W : WeierstrassCurve R) (X Y r : R)
    (h : Y ^ 2 + W.a₁ * X * Y * r + W.a₃ * Y * r ^ 3 =
      X ^ 3 + W.a₂ * X ^ 2 * r ^ 2 + W.a₄ * X * r ^ 4 + W.a₆ * r ^ 6) :
    W.toProjective.Equation ![X * r, Y, r ^ 3] := by
  rw [equation_iff]
  simp only [fin3_def_ext]
  linear_combination r ^ 3 * h

end WeierstrassCurve.Projective

namespace ModularCurves

open HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R A : Type u} [CommRing R] [CommRing A]

/-- Evaluation of the projective Weierstrass coordinate ring at a triple
satisfying the homogeneous equation. -/
noncomputable def projModelEval
    (W : WeierstrassCurve R) (f : R →+* A) (P : Fin 3 → A)
    (hP : (W.map f).toProjective.Equation P) : projCoordRing W →+* A :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom f P) (by
    intro a ha
    rw [projIdeal_toIdeal, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul]
    have hF : MvPolynomial.eval₂ f P W.toProjective.polynomial = 0 := by
      rw [WeierstrassCurve.Projective.Equation,
        WeierstrassCurve.Projective.map_polynomial, MvPolynomial.eval_map] at hP
      exact hP
    change MvPolynomial.eval₂ f P W.toProjective.polynomial *
      MvPolynomial.eval₂ f P c = 0
    rw [hF, zero_mul])

@[simp]
lemma projModelEval_mk
    (W : WeierstrassCurve R) (f : R →+* A) (P : Fin 3 → A)
    (hP : (W.map f).toProjective.Equation P)
    (p : MvPolynomial (Fin 3) R) :
    projModelEval W f P hP
        (Ideal.Quotient.mk (projIdeal W).toIdeal p) =
      MvPolynomial.eval₂ f P p :=
  Ideal.Quotient.lift_mk _ _ _

@[simp]
lemma projModelEval_X
    (W : WeierstrassCurve R) (f : R →+* A) (P : Fin 3 → A)
    (hP : (W.map f).toProjective.Equation P) (i : Fin 3) :
    projModelEval W f P hP
        (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i)) = P i := by
  rw [projModelEval_mk]
  simp only [MvPolynomial.eval₂_X]

/-- A unit homogeneous coordinate makes the image of the irrelevant ideal the
unit ideal. -/
lemma projModelEval_irrelevant_map_top_of_isUnit
    (W : WeierstrassCurve R) (f : R →+* A) (P : Fin 3 → A)
    (hP : (W.map f).toProjective.Equation P) (i : Fin 3)
    (hi : IsUnit (P i)) :
    (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal W))).toIdeal.map
        (projModelEval W f P hP) = ⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _ ?_ hi
  rw [← projModelEval_X W f P hP i]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
      (mk_X_mem_quotientGrading_one W i))

@[simp]
lemma projModelEval_algebraMapGradeZero
    (W : WeierstrassCurve R) (f : R →+* A) (P : Fin 3 → A)
    (hP : (W.map f).toProjective.Equation P) (r : R) :
    projModelEval W f P hP
        (algebraMap (↥(quotientGrading (projIdeal W) 0))
          (projCoordRing W) (algebraMapGradeZero (projIdeal W) r)) = f r := by
  have hmk : algebraMap R (projCoordRing W) r =
      Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.C r) := by
    rw [IsScalarTower.algebraMap_eq R (MvPolynomial (Fin 3) R) (projCoordRing W),
      RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
  rw [show (algebraMap (↥(quotientGrading (projIdeal W) 0)) (projCoordRing W))
      (algebraMapGradeZero (projIdeal W) r) = algebraMap R (projCoordRing W) r from rfl,
    hmk, projModelEval_mk]
  simp only [MvPolynomial.eval₂_C]

/-- The morphism to the projective Weierstrass model defined by a homogeneous
coordinate triple with one unit coordinate. -/
noncomputable def projModelFromOfGlobalSections
    {X : Scheme.{u}} (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens))) (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P) (i : Fin 3)
    (hi : IsUnit (P i)) : X ⟶ projModel W :=
  Proj.fromOfGlobalSections _ (projModelEval W f P hP)
    (projModelEval_irrelevant_map_top_of_isUnit W f P hP i hi)

/-- The morphism defined by homogeneous coordinates lies over the base map
induced by its coefficient homomorphism. -/
@[reassoc]
theorem projModelFromOfGlobalSections_projModelπ
    {X : Scheme.{u}} (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens))) (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P) (i : Fin 3)
    (hi : IsUnit (P i)) :
    projModelFromOfGlobalSections W f P hP i hi ≫ projModelπ W =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f) := by
  have key :
      ((projModelEval W f P hP).comp
        (algebraMap (↥(quotientGrading (projIdeal W) 0)) (projCoordRing W))).comp
          (algebraMapGradeZero (projIdeal W)) = f := by
    ext r
    exact projModelEval_algebraMapGradeZero W f P hP r
  rw [projModelFromOfGlobalSections, projModelπ]
  simp only [Proj.fromOfGlobalSections_toSpecZero_assoc]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, key]

/-- The inverse image of a standard projective chart under the coordinate
morphism is the basic open of the corresponding coordinate. -/
lemma projModelFromOfGlobalSections_preimage_basicOpen
    {X : Scheme.{u}} (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens))) (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P) (i : Fin 3)
    (hi : IsUnit (P i)) (j : Fin 3) :
    projModelFromOfGlobalSections W f P hP i hi ⁻¹ᵁ
        Proj.basicOpen (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)) =
      X.basicOpen (P j) := by
  rw [projModelFromOfGlobalSections,
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos
      (mk_X_mem_quotientGrading_one W j)]
  exact congr_arg X.basicOpen (projModelEval_X W f P hP j)

end ModularCurves
