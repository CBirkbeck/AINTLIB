/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.ForMathlib.SpecQuotientIso
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# A closed immersion of finite locally free schemes of equal rank is an isomorphism (YFULL γ)

Over an **affine** base `S`, a closed immersion `j : X ⟶ Y` between schemes finite, flat,
and locally of finite presentation over `S` whose global-section `Γ(S)`-modules `Γ(Y)`,
`Γ(X)` have equal rank at every prime is an isomorphism. This is the scheme form of the
same-degree effective-Cartier-divisor equality (a subdivisor of equal degree is the whole
divisor).

Over an affine base both `X` and `Y` are affine (finite over affine), so `j` transports to
`Spec` of its (surjective) global-sections comorphism, and
`isIso_SpecMap_of_surjective_of_flat_rankAtStalk_eq` applies.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

/-- A closed immersion `j : X ⟶ Y` of schemes finite flat locally-of-finite-presentation over
an **affine** base `S`, whose `Γ(S)`-modules `Γ(Y)` and `Γ(X)` have equal rank at every prime,
is an isomorphism. -/
theorem isIso_of_isClosedImmersion_of_rankAtStalk_eq_isAffineBase
    {X Y S : Scheme.{u}} [IsAffine S] (g : Y ⟶ S) (j : X ⟶ Y)
    [IsClosedImmersion j] [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    [IsFinite (j ≫ g)] [Flat (j ≫ g)] [LocallyOfFinitePresentation (j ≫ g)]
    (h : letI : Algebra ↑Γ(S, ⊤) ↑Γ(Y, ⊤) := (g.appTop).hom.toAlgebra
         letI : Algebra ↑Γ(S, ⊤) ↑Γ(X, ⊤) := (j ≫ g).appTop.hom.toAlgebra
         ∀ p : PrimeSpectrum ↑Γ(S, ⊤),
           Module.rankAtStalk (R := ↑Γ(S, ⊤)) ↑Γ(Y, ⊤) p =
             Module.rankAtStalk (R := ↑Γ(S, ⊤)) ↑Γ(X, ⊤) p) :
    IsIso j := by
  haveI : IsAffine Y := isAffine_of_isAffineHom g
  haveI : IsAffine X := isAffine_of_isAffineHom (j ≫ g)
  letI : Algebra ↑Γ(S, ⊤) ↑Γ(Y, ⊤) := (g.appTop).hom.toAlgebra
  letI : Algebra ↑Γ(S, ⊤) ↑Γ(X, ⊤) := (j ≫ g).appTop.hom.toAlgebra
  haveI : Module.Finite ↑Γ(S, ⊤) ↑Γ(Y, ⊤) :=
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp (inferInstance : IsFinite g)).2
  haveI : Module.Flat ↑Γ(S, ⊤) ↑Γ(Y, ⊤) :=
    HasRingHomProperty.appTop (P := @Flat) g inferInstance
  haveI : Module.Finite ↑Γ(S, ⊤) ↑Γ(X, ⊤) :=
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp (inferInstance : IsFinite (j ≫ g))).2
  haveI : Module.Flat ↑Γ(S, ⊤) ↑Γ(X, ⊤) :=
    HasRingHomProperty.appTop (P := @Flat) (j ≫ g) inferInstance
  have hsurj : Function.Surjective (j.appTop).hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (f := j)).2
  have hcompat : ∀ r : ↑Γ(S, ⊤),
      (j.appTop).hom (algebraMap ↑Γ(S, ⊤) ↑Γ(Y, ⊤) r) = algebraMap ↑Γ(S, ⊤) ↑Γ(X, ⊤) r :=
    fun r => rfl
  have hspec := isIso_SpecMap_of_surjective_of_flat_rankAtStalk_eq (R₀ := ↑Γ(S, ⊤))
    (R := ↑Γ(Y, ⊤)) (S := ↑Γ(X, ⊤)) h (j.appTop).hom hcompat hsurj
  refine (MorphismProperty.arrow_mk_iso_iff (P := MorphismProperty.isomorphisms Scheme)
    (arrowIsoSpecΓOfIsAffine j)).mpr ?_
  exact hspec

end ModularCurves
