/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.MvPolynomialProjectiveClosure

/-!
# Properness of polynomial projective space

The degree-zero part of a homogeneous polynomial ring is its coefficient ring. Therefore the
usual structural morphism from polynomial `Proj` to the coefficient spectrum is proper when
there are finitely many homogeneous coordinates.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coefficient algebra map onto the degree-zero homogeneous polynomial piece is bijective. -/
lemma algebraMap_homogeneousSubmodule_zero_bijective :
    Function.Bijective (algebraMap R (homogeneousSubmodule σ R 0)) := by
  constructor
  · intro a b hab
    have h := congrArg Subtype.val hab
    simpa using MvPolynomial.C_injective σ R h
  · intro x
    obtain ⟨y, hy⟩ := Submodule.mem_one.mp
      ((MvPolynomial.homogeneousSubmodule_zero (σ := σ) (R := R)).le x.2)
    exact ⟨y, Subtype.ext (by simpa using hy)⟩

/-- The degree-zero homogeneous polynomial piece is the coefficient ring. -/
noncomputable def homogeneousGradeZeroRingEquiv :
    R ≃+* homogeneousSubmodule σ R 0 :=
  RingEquiv.ofBijective _ algebraMap_homogeneousSubmodule_zero_bijective

/-- A polynomial ring in finitely many variables is finite type over its degree-zero piece. -/
instance homogeneousSubmodule_zero_finiteType [Finite σ] :
    Algebra.FiniteType (homogeneousSubmodule σ R 0) (MvPolynomial σ R) := by
  letI := IsScalarTower.of_algebraMap_eq
    (R := R) (S := homogeneousSubmodule σ R 0) (A := MvPolynomial σ R)
    (fun r => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    (R := R) (S := homogeneousSubmodule σ R 0) (A := MvPolynomial σ R)

/-- The affine comparison from the degree-zero piece to the coefficient spectrum is an
isomorphism. -/
instance isIso_specMap_algebraMap_homogeneousSubmodule_zero :
    IsIso
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (homogeneousSubmodule σ R 0)))) := by
  have h : CommRingCat.ofHom (algebraMap R (homogeneousSubmodule σ R 0)) =
      (homogeneousGradeZeroRingEquiv (R := R) (σ := σ)).toCommRingCatIso.hom := rfl
  rw [h]
  infer_instance

/-- Polynomial projective space in finitely many homogeneous coordinates is proper over its
coefficient spectrum. -/
lemma homogeneousProjπ_isProper [Finite σ] :
    IsProper (homogeneousProjπ (R := R) (σ := σ)) := by
  dsimp only [homogeneousProjπ]
  infer_instance

end

end MvPolynomial
