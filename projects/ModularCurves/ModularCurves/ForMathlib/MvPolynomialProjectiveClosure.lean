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
import ModularCurves.ForMathlib.ProjectiveSpaceChart

/-!
# Projective closures from homogenized relations

A family of affine polynomial relations determines a homogeneous quotient after adjoining one
variable. With finitely many polynomial variables, its `Proj` is proper over the coefficient ring.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory HomogeneousIdeal HomogeneousLocalization MorphismProperty

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

section OptionChart

local instance : DecidableEq (Option σ) := Classical.decEq _

private def optionNeNoneEquiv (σ : Type*) : {x : Option σ // x ≠ none} ≃ σ where
  toFun x := x.1.get (Option.ne_none_iff_isSome.mp x.2)
  invFun x := ⟨some x, by simp⟩
  left_inv x := Subtype.ext (Option.some_get _)
  right_inv x := Option.get_some _ _

private lemma rename_dehomogenizeAux_none (p : MvPolynomial (Option σ) R) :
    rename (optionNeNoneEquiv σ) (dehomogenizeAux R none p) =
      dehomogenizeOption R p := by
  classical
  apply RingHom.congr_fun
    (f := (rename (optionNeNoneEquiv σ)).toRingHom.comp (dehomogenizeAux R none))
    (g := dehomogenizeOption R)
  refine ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · simp
  · cases i with
    | none => simp
    | some i => simp [optionNeNoneEquiv]

/-- The standard projective chart at the added homogenizing variable is affine space in the
original variables. -/
noncomputable def optionChartRingEquiv :
    Away (homogeneousSubmodule (Option σ) R) (X none : MvPolynomial (Option σ) R) ≃+*
      MvPolynomial σ R := by
  classical
  exact (chartRingEquiv R (none : Option σ)).trans
    (renameEquiv R (optionNeNoneEquiv σ)).toRingEquiv

/-- Under the standard chart equivalence, a homogeneous lift divided by the homogenizing
variable to its chosen degree is the original polynomial. -/
lemma optionChartRingEquiv_apply_mk_homogenizeOption
    (p : MvPolynomial σ R) (n : ℕ) (h : p.totalDegree ≤ n) :
    optionChartRingEquiv
      (Away.mk _ (X_mem_homogeneousSubmodule_one R (none : Option σ)) n
        (homogenizeOption p n)
        (by
          simpa using (mem_homogeneousSubmodule _ _).mpr
            (homogenizeOption_isHomogeneous p n))) = p := by
  classical
  change rename (optionNeNoneEquiv σ)
      (dehomogenizeAt R none
        (Away.mk _ (X_mem_homogeneousSubmodule_one R (none : Option σ)) n
          (homogenizeOption p n) _)) = p
  rw [dehomogenizeAt_mk, rename_dehomogenizeAux_none,
    dehomogenizeOption_homogenizeOption p n h]

end OptionChart

end

end MvPolynomial
