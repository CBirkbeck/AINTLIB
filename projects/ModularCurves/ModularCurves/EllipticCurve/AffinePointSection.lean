/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.WeierstrassModel

/-!
# Sections of the projective model through affine points (T-E14b-2)

**(STREAM-OMEGA 2026-07-14; board: T-E14 continuation.)** For an affine point
`(p, q)` on a Weierstrass curve `W/R` (i.e. satisfying the affine Weierstrass
equation), the section `[p : q : 1] : Spec R ⟶ projModel W` of the structure
morphism — the scheme-level "the section through `(p, q)`". Mirrors `projModelZero`
(the section `[0:1:0]` at infinity) verbatim, with the evaluation
`X ↦ p, Y ↦ q, Z ↦ 1` in place of `X ↦ 0, Y ↦ 1, Z ↦ 0`.

This is the vocabulary in which KM 4.6.2's Legendre `δ`-condition is stated: *"the
adapted `x` satisfies `x(P₂) = 0, x(Q₂) = 1`"* becomes "`P` is carried by the adapted
chart to `projModelAffineSection … 0 0 …` and `Q` to `projModelAffineSection … 1 0 …`"
(on `2`-torsion, `y = 0` is forced in char ≠ 2, so pinning `x` pins the point).
-/

universe u

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

/-- Evaluation of the homogeneous coordinate ring at an affine point `[p : q : 1]`
of the curve. -/
def projModelAffineEval (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) : projCoordRing W →+* R :=
  Ideal.Quotient.lift _ (MvPolynomial.eval ![p, q, 1]) (by
    intro a ha
    rw [projIdeal_toIdeal, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    have hF : MvPolynomial.eval ![p, q, 1] W.toProjective.polynomial = 0 := by
      rw [WeierstrassCurve.Projective.eval_polynomial]
      have he := (WeierstrassCurve.Affine.equation_iff (W := W.toAffine) p q).mp h
      show q ^ 2 * 1 + W.a₁ * p * q * 1 + W.a₃ * q * 1 ^ 2 -
        (p ^ 3 + W.a₂ * p ^ 2 * 1 + W.a₄ * p * 1 ^ 2 + W.a₆ * 1 ^ 3) = 0
      linear_combination he
    rw [map_mul, hF, zero_mul])

@[simp]
lemma projModelAffineEval_mk (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) (f : MvPolynomial (Fin 3) R) :
    projModelAffineEval W p q h (Ideal.Quotient.mk (projIdeal W).toIdeal f) =
      MvPolynomial.eval ![p, q, 1] f :=
  Ideal.Quotient.lift_mk _ _ _

/-- The class of `Z` lies in the irrelevant ideal of the quotient grading. -/
lemma mk_Z_mem_irrelevant (W : WeierstrassCurve R) :
    Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X 2) ∈
      (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal W))).toIdeal := by
  show GradedRing.proj (quotientGrading (projIdeal W)) 0
      (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X 2)) = 0
  rw [GradedRing.proj_apply,
    decompose_quotientGrading_mk (projIdeal W)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X _ _)),
    DirectSum.coe_of_apply]
  simp

/-- The affine-point evaluation maps the irrelevant ideal onto the unit ideal. -/
lemma projModelAffineEval_irrelevant_map_top (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal W))).toIdeal.map
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelAffineEval W p q h)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp
      (projModelAffineEval W p q h))
      (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X 2)) = 1 := by
    rw [RingHom.comp_apply, projModelAffineEval_mk]
    rw [show MvPolynomial.eval ![p, q, 1] (MvPolynomial.X 2) = 1 from by simp]
    exact map_one _
  rw [← h1]
  exact Ideal.mem_map_of_mem _ (mk_Z_mem_irrelevant W)

/-- **(T-E14b-2)** The section `[p : q : 1]` of the projective Weierstrass model
through an affine point of the curve, via `Proj.fromOfGlobalSections` at the
evaluation `X ↦ p, Y ↦ q, Z ↦ 1`. -/
def projModelAffineSection (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) : Spec (.of R) ⟶ projModel W :=
  Proj.fromOfGlobalSections _
    ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelAffineEval W p q h))
    (projModelAffineEval_irrelevant_map_top W p q h)

/-- Evaluation at `[p:q:1]` retracts the degree-zero inclusion. -/
@[simp]
lemma projModelAffineEval_algebraMapGradeZero (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) (r : R) :
    projModelAffineEval W p q h (algebraMap (↥(quotientGrading (projIdeal W) 0))
      (projCoordRing W) (algebraMapGradeZero (projIdeal W) r)) = r := by
  have hmk : algebraMap R (projCoordRing W) r =
      Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.C r) := by
    rw [IsScalarTower.algebraMap_eq R (MvPolynomial (Fin 3) R) (projCoordRing W),
      RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
  rw [show (algebraMap (↥(quotientGrading (projIdeal W) 0)) (projCoordRing W))
      (algebraMapGradeZero (projIdeal W) r) = algebraMap R (projCoordRing W) r from rfl,
    hmk, projModelAffineEval_mk]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14b-2)** The affine-point section is a section of the structure morphism. -/
@[reassoc (attr := simp)]
theorem projModelAffineSection_projModelπ (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    projModelAffineSection W p q h ≫ projModelπ W = 𝟙 _ := by
  have key : (((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp
        (projModelAffineEval W p q h)).comp
          (algebraMap (↥(quotientGrading (projIdeal W) 0)) (projCoordRing W))).comp
      (algebraMapGradeZero (projIdeal W)) =
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    ext r
    show (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (projModelAffineEval W p q h
        (algebraMap _ (projCoordRing W) (algebraMapGradeZero (projIdeal W) r))) = _
    rw [projModelAffineEval_algebraMapGradeZero]
  rw [projModelAffineSection, projModelπ]
  simp only [Proj.fromOfGlobalSections_toSpecZero_assoc]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, key, CommRingCat.ofHom_hom]
  exact toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of R)

end ModularCurves
