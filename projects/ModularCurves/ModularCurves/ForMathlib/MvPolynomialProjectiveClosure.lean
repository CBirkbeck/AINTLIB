/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import ModularCurves.ForMathlib.GradedQuotient
import ModularCurves.ForMathlib.MvPolynomialHomogenize

/-!
# Projective closures from homogenized relations

A family of affine polynomial relations determines a homogeneous quotient after adjoining one
variable. With finitely many polynomial variables, its `Proj` is proper over the coefficient ring.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory HomogeneousIdeal MorphismProperty

noncomputable section

universe u

variable {R : Type u} {σ κ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective scheme cut out by a family of homogenized polynomial relations. -/
@[reducible]
def homogenizedProj (g : κ → MvPolynomial σ R) (d : κ → ℕ) : Scheme.{u} :=
  Proj (quotientGrading (homogenizedIdeal g d))

/-- The structure morphism of a homogenized projective closure to its coefficient ring. -/
def homogenizedProjπ (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    homogenizedProj g d ⟶ Spec (.of R) :=
  Proj.toSpecZero _ ≫
    Spec.map (CommRingCat.ofHom (algebraMapGradeZero (homogenizedIdeal g d)))

/-- A homogenized projective closure in finitely many variables is proper over its coefficient
ring. -/
lemma homogenizedProjπ_isProper [Finite σ] (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    IsProper (homogenizedProjπ g d) := by
  let I := homogenizedIdeal g d
  haveI hfiniteR : Algebra.FiniteType R (MvPolynomial (Option σ) R ⧸ I.toIdeal) :=
    Algebra.FiniteType.of_surjective
      (Ideal.Quotient.mkₐ R I.toIdeal) (Ideal.Quotient.mkₐ_surjective R _)
  haveI hfiniteZero :
      Algebra.FiniteType (↥(quotientGrading I 0))
        (MvPolynomial (Option σ) R ⧸ I.toIdeal) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R
      (↥(quotientGrading I 0)) (MvPolynomial (Option σ) R ⧸ I.toIdeal)
  haveI hproj : IsProper (Proj.toSpecZero (quotientGrading I)) := inferInstance
  haveI hclosed : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (algebraMapGradeZero I))) :=
    IsClosedImmersion.spec_of_surjective _
      (algebraMapGradeZero_surjective_mvPolynomial I)
  haveI hbase : IsProper
      (Spec.map (CommRingCat.ofHom (algebraMapGradeZero I))) := inferInstance
  change IsProper
    (Proj.toSpecZero (quotientGrading I) ≫
      Spec.map (CommRingCat.ofHom (algebraMapGradeZero I)))
  exact IsStableUnderComposition.comp_mem _ _ hproj hbase

end

end MvPolynomial
