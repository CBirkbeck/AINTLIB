/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.LowDegreeFiniteProjectiveReplacement

/-!
# Local exactness from a residue fibre

This file transports exactness of a short complex over a residue field to
surjectivity of the finite-projective low-degree replacement.
-/

open Function
open CategoryTheory
open TensorProduct
open scoped ChangeOfRings

universe u

namespace ModularCurves
namespace LowDegreeFiniteReplacement

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

local instance residueLocalHZeroFinite
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R (LinearMap.ker S.f.hom)] :
    Module.Finite R (HZero S.moduleCatToCycles) :=
  Module.Finite.ker_moduleCatToCycles S

local instance residueLocalHOneFinite
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.homology] :
    Module.Finite R (HOne S.moduleCatToCycles) :=
  Module.Finite.quotient_range_moduleCatToCycles S

private theorem surjective_of_subsingleton_rangeQuotient
    {A M N : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) [Subsingleton (N ⧸ LinearMap.range f)] :
    Function.Surjective f := by
  intro y
  have hy : Submodule.Quotient.mk (p := LinearMap.range f) y = 0 :=
    Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero] at hy
  exact hy

private theorem surjective_of_homologyEquiv_of_exact
    {A M N : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (T : ShortComplex (ModuleCat.{u} A))
    (e : (N ⧸ LinearMap.range f) ≃ₗ[A] T.homology)
    (h : Function.Exact T.f.hom T.g.hom) :
    Function.Surjective f := by
  have hT : T.Exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mpr h
  have hzero : CategoryTheory.Limits.IsZero T.homology :=
    (T.exact_iff_isZero_homology).mp hT
  letI : Subsingleton T.homology :=
    ModuleCat.isZero_iff_subsingleton.mp hzero
  letI : Subsingleton (N ⧸ LinearMap.range f) :=
    (Equiv.subsingleton_congr e.toEquiv).mpr inferInstance
  exact surjective_of_subsingleton_rangeQuotient f

/-- Exactness after base change makes the first differential of the finite-projective
replacement surjective. -/
theorem shortComplexBaseChange_kZeroToKOne_surjective_of_exact
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Flat R S.X₁]
    [Module.Flat R (LinearMap.ker S.g.hom)]
    [Module.Finite R (LinearMap.ker S.f.hom)]
    [Module.Finite R S.homology]
    (A : Type u) [CommRing A] [Algebra R A]
    (hbij : Function.Bijective
      (kerBaseChangeComparison A S.g.hom))
    (hexact : Function.Exact
      (S.f.hom.baseChange A) (S.g.hom.baseChange A)) :
    Function.Surjective
      ((kZeroToKOne S.moduleCatToCycles).baseChange A) := by
  let T := ShortComplex.moduleCatMk
    (S.f.hom.baseChange A) (S.g.hom.baseChange A)
    (LinearMap.baseChange_comp_eq_zero S.f.hom S.g.hom
      (shortComplexModuleCatCompEqZero S) A)
  exact surjective_of_homologyEquiv_of_exact
    ((kZeroToKOne S.moduleCatToCycles).baseChange A) T
    (shortComplexBaseChangeHomologyOneEquiv S A hbij) hexact

end LowDegreeFiniteReplacement
end ModularCurves
