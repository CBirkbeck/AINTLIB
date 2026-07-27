/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.HomogeneousProjProper
import ModularCurves.ForMathlib.HomogenizedProjStandardEmbedding

/-!
# Projective factorizations over affine schemes

A morphism to an affine scheme has a projective factorization if it factors through a closed
immersion into a finite-dimensional polynomial projective space over the same base.
-/

open CategoryTheory

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/-- A factorization through a closed subscheme of finite-dimensional projective space. -/
def IsProjectiveFactorization {X : Scheme.{u}} {R : Type u} [CommRing R]
    (f : X ⟶ Spec (.of R)) : Prop :=
  ∃ (d : ℕ) (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R)),
    IsClosedImmersion i ∧
      i ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (d + 1)) = f

namespace IsProjectiveFactorization

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]
variable {f : X ⟶ Spec (.of R)}

/-- A morphism admitting a projective factorization is proper. -/
lemma isProper (h : IsProjectiveFactorization f) : IsProper f := by
  obtain ⟨d, i, hi, hif⟩ := h
  letI : IsClosedImmersion i := hi
  letI : IsProper
      (MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (d + 1))) :=
    MvPolynomial.homogeneousProjπ_isProper
  rw [← hif]
  infer_instance

/-- Precomposition with a closed immersion preserves projective factorizations. -/
lemma comp_isClosedImmersion (h : IsProjectiveFactorization f)
    (i : Y ⟶ X) (hi : IsClosedImmersion i) :
    IsProjectiveFactorization (i ≫ f) := by
  obtain ⟨d, j, hj, hjf⟩ := h
  letI : IsClosedImmersion i := hi
  letI : IsClosedImmersion j := hj
  refine ⟨d, i ≫ j, inferInstance, ?_⟩
  rw [Category.assoc, hjf]

end IsProjectiveFactorization

end AlgebraicGeometry

namespace MvPolynomial

open AlgebraicGeometry

variable {R : Type u} [CommRing R] {κ : Type} {n : ℕ}

/-- Every homogenized projective closure has a projective factorization over its coefficient
spectrum. -/
lemma homogenizedProjπ_isProjectiveFactorization
    (g : κ → MvPolynomial (Fin n) R) (d : κ → ℕ) :
    IsProjectiveFactorization (homogenizedProjπ g d) :=
  ⟨n, homogenizedProjStandardι g d,
    homogenizedProjStandardι_isClosedImmersion g d,
    homogenizedProjStandardι_comp_homogeneousProjπ g d⟩

end MvPolynomial
