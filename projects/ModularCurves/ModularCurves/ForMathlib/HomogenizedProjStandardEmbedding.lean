/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.HomogeneousProjReindex

/-!
# Standard projective embeddings of homogenized closures

A homogenized presentation in `Fin n` affine variables is naturally a closed subscheme of
projective space with `Fin (n+1)` homogeneous coordinates.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {R : Type u} [CommRing R] {κ : Type} {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogenized projective closure embedded in standard polynomial projective space. -/
def homogenizedProjStandardι
    (g : κ → MvPolynomial (Fin n) R) (d : κ → ℕ) :
    homogenizedProj g d ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) R) :=
  homogenizedProjι g d ≫
    (homogeneousProjReindexIso R (_root_.finSuccEquiv n).symm).hom

/-- The standard projective embedding of a homogenized closure is a closed immersion. -/
lemma homogenizedProjStandardι_isClosedImmersion
    (g : κ → MvPolynomial (Fin n) R) (d : κ → ℕ) :
    IsClosedImmersion (homogenizedProjStandardι g d) := by
  haveI : IsClosedImmersion (homogenizedProjι g d) :=
    homogenizedProjι_isClosedImmersion g d
  unfold homogenizedProjStandardι
  infer_instance

/-- The standard projective embedding of a homogenized closure lies over the coefficient
spectrum. -/
lemma homogenizedProjStandardι_comp_homogeneousProjπ
    (g : κ → MvPolynomial (Fin n) R) (d : κ → ℕ) :
    homogenizedProjStandardι g d ≫
        homogeneousProjπ (R := R) (σ := Fin (n + 1)) =
      homogenizedProjπ g d := by
  unfold homogenizedProjStandardι
  rw [Category.assoc,
    homogeneousProjReindexIso_hom_comp_homogeneousProjπ,
    homogenizedProjι_comp_homogeneousProjπ]

end

end MvPolynomial
