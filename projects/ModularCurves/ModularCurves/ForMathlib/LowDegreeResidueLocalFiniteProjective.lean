/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.LowDegreeResidueLocalExact

/-!
# A finite-projective kernel near an exact residue fibre

This file spreads surjectivity of the low-degree replacement from a residue
field to a principal neighborhood and records arbitrary base change for its
finite-projective kernel.
-/

open CategoryTheory

universe u

namespace ModularCurves
namespace LowDegreeFiniteReplacement

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- A linear map is surjective near `p`, with a finite-projective kernel that commutes
with every further algebra base change. -/
def HasAwayFiniteProjectiveKernelAt
    {P Q : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] Q) (p : Ideal R) : Prop :=
  ∃ r : R, r ∉ p ∧
    Function.Surjective (f.baseChange (Localization.Away r)) ∧
    Module.Finite (Localization.Away r)
      (LinearMap.ker (f.baseChange (Localization.Away r))) ∧
    Module.Projective (Localization.Away r)
      (LinearMap.ker (f.baseChange (Localization.Away r))) ∧
    ∀ (A : Type*) [CommRing A] [Algebra (Localization.Away r) A],
      Function.Bijective
        (kerBaseChangeComparison A
          (f.baseChange (Localization.Away r)))

local instance residueLocalFiniteProjectiveHZeroFinite
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R (LinearMap.ker S.f.hom)] :
    Module.Finite R (HZero S.moduleCatToCycles) :=
  Module.Finite.ker_moduleCatToCycles S

local instance residueLocalFiniteProjectiveHOneFinite
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.homology] :
    Module.Finite R (HOne S.moduleCatToCycles) :=
  Module.Finite.quotient_range_moduleCatToCycles S

/-- If a short complex is exact over a residue field, its finite-projective replacement is
surjective on a principal neighborhood, with finite-projective kernel commuting with every
further base change. -/
theorem exists_away_finiteProjective_kernel_of_residueField_exact
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Flat R S.X₁]
    [Module.Flat R (LinearMap.ker S.g.hom)]
    [Module.Finite R (LinearMap.ker S.f.hom)]
    [Module.Finite R S.homology]
    (p : Ideal R) [p.IsPrime]
    (hbij : Function.Bijective
      (kerBaseChangeComparison p.ResidueField S.g.hom))
    (hexact : Function.Exact
      (S.f.hom.baseChange p.ResidueField)
      (S.g.hom.baseChange p.ResidueField)) :
    HasAwayFiniteProjectiveKernelAt
      (kZeroToKOne S.moduleCatToCycles) p := by
  letI : Module.Projective R (KZero S.moduleCatToCycles) :=
    kZero_projective S.moduleCatToCycles
  exact LinearMap.exists_away_finiteProjective_ker_of_residueField_surjective
    (kZeroToKOne S.moduleCatToCycles) p
    (shortComplexBaseChange_kZeroToKOne_surjective_of_exact
      S p.ResidueField hbij hexact)

end LowDegreeFiniteReplacement
end ModularCurves
