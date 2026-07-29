/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.RingTheory.Extension.Presentation.Basic
import ModularCurves.ForMathlib.MvPolynomialProjectiveClosure

/-!
# Projective closures of algebra presentations

A finite-variable algebra presentation realizes its affine spectrum as the standard open chart
of a proper homogenized projective closure over the coefficient ring.
-/

open CategoryTheory

universe u

namespace Algebra.Presentation

noncomputable section

variable {R S : Type u} {ι κ : Type} [CommRing R] [CommRing S] [Algebra R S]

/-- The quotient by a presentation's displayed relations is the presented algebra. -/
noncomputable def relationQuotientEquiv (P : Presentation R S ι κ) :
    (P.Ring ⧸ Ideal.span (Set.range P.relation)) ≃ₐ[R] S :=
  (Ideal.quotientEquivAlgOfEq R P.span_range_relation_eq_ker).trans
    (P.quotientEquiv.restrictScalars R)

/-- The homogenized projective closure attached to a presentation. -/
abbrev projectiveClosure (P : Presentation R S ι κ) :
    AlgebraicGeometry.Scheme.{u} :=
  MvPolynomial.homogenizedProj P.relation
    (fun j ↦ (P.relation j).totalDegree)

/-- The structure morphism of a presentation's projective closure. -/
noncomputable def projectiveClosureπ (P : Presentation R S ι κ) :
    projectiveClosure P ⟶ AlgebraicGeometry.Spec (.of R) :=
  MvPolynomial.homogenizedProjπ P.relation
    (fun j ↦ (P.relation j).totalDegree)

/-- The projective closure of a finite-variable presentation is proper. -/
lemma projectiveClosureπ_isProper [Finite ι] (P : Presentation R S ι κ) :
    AlgebraicGeometry.IsProper (projectiveClosureπ P) :=
  MvPolynomial.homogenizedProjπ_isProper P.relation
    (fun j ↦ (P.relation j).totalDegree)

/-- The presented affine scheme as the standard open chart of its projective closure. -/
noncomputable def affineOpen (P : Presentation R S ι κ) :
    AlgebraicGeometry.Spec (.of S) ⟶ projectiveClosure P :=
  AlgebraicGeometry.Spec.map (relationQuotientEquiv P).toCommRingCatIso.hom ≫
    MvPolynomial.homogenizedChartOpen P.relation
      (fun j ↦ (P.relation j).totalDegree) (fun _ ↦ le_rfl)

/-- The affine chart of a presentation's projective closure is an open immersion. -/
lemma affineOpen_isOpenImmersion (P : Presentation R S ι κ) :
    AlgebraicGeometry.IsOpenImmersion (affineOpen P) := by
  unfold affineOpen
  exact @AlgebraicGeometry.IsOpenImmersion.comp _ _ _ _ _ (by infer_instance)
    (MvPolynomial.homogenizedChartOpen_isOpenImmersion P.relation
      (fun j ↦ (P.relation j).totalDegree) (fun _ ↦ le_rfl))

/-- The affine chart immersion commutes with the structure morphisms to the coefficient ring. -/
lemma affineOpen_comp_projectiveClosureπ (P : Presentation R S ι κ) :
    affineOpen P ≫ projectiveClosureπ P =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  unfold affineOpen projectiveClosureπ
  rw [Category.assoc,
    MvPolynomial.homogenizedChartOpen_comp_homogenizedProjπ]
  rw [← AlgebraicGeometry.Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom
    (relationQuotientEquiv P).toAlgHom.comp_algebraMap

end

end Algebra.Presentation
