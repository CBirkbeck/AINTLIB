/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.RelativeProjectiveFactorization

/-!
# Chosen data in a relative projective factorization

This file gives stable names to the dimension and closed embedding contained in a relative
projective factorization.
-/

open CategoryTheory

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.IsRelativeProjectiveFactorization

variable {R : Type u} [CommRing R] {X S : Scheme.{u}}
variable {s : S ⟶ Spec (.of R)} {f : X ⟶ S}

/-- A chosen relative projective dimension. -/
def chosenDimension (h : IsRelativeProjectiveFactorization s f) : ℕ :=
  h.choose

/-- The chosen closed embedding into relative projective space. -/
def chosenEmbedding (h : IsRelativeProjectiveFactorization s f) :
    X ⟶ relativeProjectiveScheme s h.chosenDimension :=
  h.choose_spec.choose

/-- The chosen embedding is a closed immersion. -/
lemma chosenEmbedding_isClosedImmersion
    (h : IsRelativeProjectiveFactorization s f) :
    IsClosedImmersion h.chosenEmbedding :=
  h.choose_spec.choose_spec.1

attribute [local instance] chosenEmbedding_isClosedImmersion

/-- Projection of the chosen embedding to the base recovers the original morphism. -/
@[reassoc]
lemma chosenEmbedding_relativeProjectiveToBase
    (h : IsRelativeProjectiveFactorization s f) :
    h.chosenEmbedding ≫ relativeProjectiveToBase s h.chosenDimension = f :=
  h.choose_spec.choose_spec.2

/-- The absolute projective-space map underlying the chosen relative factorization. -/
def chosenProjectiveMap (h : IsRelativeProjectiveFactorization s f) :
    X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (h.chosenDimension + 1)) R) :=
  h.chosenEmbedding ≫ relativeProjectiveToProjective s h.chosenDimension

/-- The chosen projective map is compatible with the structural map to the affine base. -/
@[reassoc]
lemma chosenProjectiveMap_homogeneousProjπ
    (h : IsRelativeProjectiveFactorization s f) :
    h.chosenProjectiveMap ≫
        MvPolynomial.homogeneousProjπ
          (R := R) (σ := Fin (h.chosenDimension + 1)) =
      f ≫ s := by
  rw [chosenProjectiveMap, Category.assoc,
    ← relativeProjective_projection_condition]
  exact h.chosenEmbedding_relativeProjectiveToBase_assoc s

end AlgebraicGeometry.IsRelativeProjectiveFactorization
