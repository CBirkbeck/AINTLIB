/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.FiniteAffineImageProjective
import ModularCurves.ForMathlib.ProjectiveFactorization

/-!
# Projective factorizations of affine compactifications

The homogenized projective closures chosen by finite algebra presentations, and the wrappers
through which the Chow construction uses them, have the concrete projective factorization.
-/

open CategoryTheory

noncomputable section

universe u

namespace Algebra.Presentation

variable {R S : Type u} {κ : Type} [CommRing R] [CommRing S] [Algebra R S]
variable {n : ℕ}

/-- A finite-variable presentation's projective closure has a projective factorization. -/
lemma projectiveClosureπ_isProjectiveFactorization
    (P : Presentation R S (Fin n) κ) :
    AlgebraicGeometry.IsProjectiveFactorization (projectiveClosureπ P) :=
  MvPolynomial.homogenizedProjπ_isProjectiveFactorization P.relation
    (fun j => (P.relation j).totalDegree)

end Algebra.Presentation

namespace AlgebraicGeometry.Scheme.AffineProjectiveClosure

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of R)) [IsAffine X] [LocallyOfFinitePresentation f]

/-- The chosen projective closure of an affine finitely presented morphism has a projective
factorization. -/
lemma π_isProjectiveFactorization :
    IsProjectiveFactorization (π f) := by
  letI := algebra f
  letI := finitePresentation f
  exact Algebra.Presentation.projectiveClosureπ_isProjectiveFactorization
    (presentation f)

end AlgebraicGeometry.Scheme.AffineProjectiveClosure

namespace AlgebraicGeometry.Scheme.FiniteAffineImageCover

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (xπ : X ⟶ Spec (.of R)) {ι : Type u} (U : ι → X.Opens)

/-- Every projective compactification used by a finite affine image cover has a projective
factorization. -/
lemma projectiveπ_isProjectiveFactorization [IsNoetherian X]
    [LocallyOfFinitePresentation xπ] (hU : ∀ i, IsAffineOpen (U i)) (i : ι) :
    IsProjectiveFactorization (projectiveπ xπ U hU i) := by
  letI : IsAffine (chart U i).toScheme := chart_isAffineOpen U hU i
  letI : LocallyOfFinitePresentation (chartπ xπ U i) :=
    chartπ_locallyOfFinitePresentation xπ U i
  exact AffineProjectiveClosure.π_isProjectiveFactorization (chartπ xπ U i)

end AlgebraicGeometry.Scheme.FiniteAffineImageCover
