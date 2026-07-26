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

end ModularCurves
