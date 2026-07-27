/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.ProjectiveFactorization

/-!
# Relative projective factorizations

Standard relative projective space over a scheme is the base change of polynomial projective
space. A compatible absolute projective factorization becomes a relative one over a separated
intermediate scheme.
-/

open CategoryTheory Limits

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/-- Standard relative projective `d`-space over a scheme mapping to an affine base. -/
abbrev relativeProjectiveScheme
    {R : Type u} [CommRing R] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of R)) (d : ℕ) : Scheme.{u} :=
  pullback s (MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (d + 1)))

/-- The projection from relative projective space to its base scheme. -/
abbrev relativeProjectiveToBase
    {R : Type u} [CommRing R] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of R)) (d : ℕ) :
    relativeProjectiveScheme s d ⟶ S :=
  pullback.fst s (MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (d + 1)))

/-- The projection from relative projective space to absolute projective space. -/
abbrev relativeProjectiveToProjective
    {R : Type u} [CommRing R] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of R)) (d : ℕ) :
    relativeProjectiveScheme s d ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R) :=
  pullback.snd s (MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (d + 1)))

/-- The two projections from relative projective space commute over the affine base. -/
@[reassoc]
lemma relativeProjective_projection_condition
    {R : Type u} [CommRing R] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of R)) (d : ℕ) :
    relativeProjectiveToBase s d ≫ s =
      relativeProjectiveToProjective s d ≫
        MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (d + 1)) :=
  pullback.condition

/-- Relative projective space is proper over its base. -/
instance relativeProjectiveToBase_isProper
    {R : Type u} [CommRing R] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of R)) (d : ℕ) :
    IsProper (relativeProjectiveToBase s d) := by
  letI : IsProper
      (MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (d + 1))) :=
    MvPolynomial.homogeneousProjπ_isProper
  infer_instance

/-- A factorization through a closed subscheme of relative projective space. -/
def IsRelativeProjectiveFactorization
    {R : Type u} [CommRing R] {X S : Scheme.{u}}
    (s : S ⟶ Spec (.of R)) (f : X ⟶ S) : Prop :=
  ∃ (d : ℕ) (i : X ⟶ relativeProjectiveScheme s d),
    IsClosedImmersion i ∧ i ≫ relativeProjectiveToBase s d = f

namespace IsRelativeProjectiveFactorization

variable {R : Type u} [CommRing R] {X Y S : Scheme.{u}}
variable {s : S ⟶ Spec (.of R)} {f : X ⟶ S}

/-- A morphism admitting a relative projective factorization is proper. -/
lemma isProper (h : IsRelativeProjectiveFactorization s f) :
    IsProper f := by
  obtain ⟨d, i, hi, hif⟩ := h
  letI : IsClosedImmersion i := hi
  rw [← hif]
  infer_instance

/-- Precomposition with a closed immersion preserves relative projective factorizations. -/
lemma comp_isClosedImmersion (h : IsRelativeProjectiveFactorization s f)
    (i : Y ⟶ X) (hi : IsClosedImmersion i) :
    IsRelativeProjectiveFactorization s (i ≫ f) := by
  obtain ⟨d, j, hj, hjf⟩ := h
  letI : IsClosedImmersion i := hi
  letI : IsClosedImmersion j := hj
  refine ⟨d, i ≫ j, inferInstance, ?_⟩
  rw [Category.assoc, hjf]

end IsRelativeProjectiveFactorization

/-- The projection from relative projective space has its tautological factorization. -/
lemma relativeProjectiveToBase_isRelativeProjectiveFactorization
    {R : Type u} [CommRing R] {S : Scheme.{u}}
    (s : S ⟶ Spec (.of R)) (d : ℕ) :
    IsRelativeProjectiveFactorization s (relativeProjectiveToBase s d) :=
  ⟨d, 𝟙 _, inferInstance, Category.id_comp _⟩

namespace IsProjectiveFactorization

variable {R : Type u} [CommRing R] {X S : Scheme.{u}}
variable {s : S ⟶ Spec (.of R)} {f : X ⟶ S}

/-- A compatible absolute projective factorization is relative over a separated intermediate
scheme. -/
lemma relative [IsSeparated s]
    (h : IsProjectiveFactorization (f ≫ s)) :
    IsRelativeProjectiveFactorization s f := by
  obtain ⟨d, j, hj, hjf⟩ := h
  let i : X ⟶ relativeProjectiveScheme s d :=
    pullback.lift f j hjf.symm
  have hi : IsClosedImmersion i := by
    letI : IsClosedImmersion j := hj
    have hcomp :
        IsClosedImmersion (i ≫ relativeProjectiveToProjective s d) := by
      rw [show i ≫ relativeProjectiveToProjective s d = j by
        dsimp only [i, relativeProjectiveToProjective]
        rw [pullback.lift_snd]]
      infer_instance
    letI : IsClosedImmersion
        (i ≫ relativeProjectiveToProjective s d) := hcomp
    exact IsClosedImmersion.of_comp i (relativeProjectiveToProjective s d)
  refine ⟨d, i, hi, ?_⟩
  dsimp only [i, relativeProjectiveToBase]
  rw [pullback.lift_fst]

end IsProjectiveFactorization

end AlgebraicGeometry
