/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCechFirstLaurent

/-!
# Homogeneous-weight coordinates for the projective twist Cech complex

This file reindexes each standard-intersection factor of the existing ordered Cech complex by its
allowed global homogeneous Laurent weights.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance : DecidableEq σ := Classical.decEq σ

/-- The degree-`n` coordinate Cech term, with each standard-intersection factor reindexed by the
global degree-`d` homogeneous Laurent weights allowed on its ordered tuple. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechObject
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    ModuleCat.{u} Γ(Spec (CommRingCat.of R),
      (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
  ∏ᶜ fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
    ModuleCat.of
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        {e : HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun k => (a.1 k).down)})

/-- The existing structure-sheaf coordinate Cech term is factorwise equivalent to its
homogeneous-weight presentation. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechObjectIso
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n ≅
      coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n :=
  Pi.mapIso fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
    (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
      (R := R) a.1 d).toModuleIso

/-- The degreewise homogeneous-weight comparison is the landed factor equivalence on every
ordered tuple. -/
@[reassoc]
theorem coordinateHomogeneousLaurentOrderedCechObjectIso_hom_comp_π
    [LinearOrder σ] (d : ℤ) (n : ℕ)
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    (coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d n).hom ≫
      Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        ModuleCat.of
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          (AddMonoidAlgebra
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            {e : HomogeneousLaurentExponent σ d //
              e.IsAllowedOn (fun k => (b.1 k).down)})) a =
      Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        Scheme.Modules.baseCechFactor
          (homogeneousProjπ (R := R) (σ := σ))
          (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
          (coordinateOpenCover (R := R) (σ := σ)) n b.1) a ≫
        (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
          (R := R) a.1 d).toModuleIso.hom := by
  exact Pi.mapIso_hom_π
    (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
        (R := R) b.1 d).toModuleIso) a

end

end MvPolynomial
