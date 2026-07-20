/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwist
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCech

/-!
# Cech factors for twists on polynomial projective space

This file begins the ordered standard-cover calculation of the cohomology of
projective-space twists. It identifies the sections of `O(d)` on each ordered
intersection with the sections of the structure sheaf there.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard coordinate cover, lifted to the universe of the projective scheme. -/
abbrev coordinateOpenCover (i : ULift.{u} σ) :
    (Proj (homogeneousSubmodule σ R)).Opens :=
  coordinateOpen (R := R) i.down

/-- Every member of the universe-lifted standard coordinate cover is affine. -/
theorem coordinateOpenCover_isAffineOpen (i : ULift.{u} σ) :
    IsAffineOpen (coordinateOpenCover (R := R) i) :=
  coordinateOpen_isAffineOpen i.down

/-- The universe-lifted standard coordinate opens cover projective space. -/
theorem iSup_coordinateOpenCover_eq_top :
    ⨆ i : ULift.{u} σ, coordinateOpenCover (R := R) i = ⊤ := by
  apply top_unique
  rw [← iSup_coordinateOpen_eq_top (R := R)]
  exact iSup_le fun i => le_iSup (coordinateOpenCover (R := R)) (ULift.up i)

/-- The intersection of the standard coordinate charts indexed by a Cech tuple. -/
abbrev coordinateOpenCechIntersection {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    (Proj (homogeneousSubmodule σ R)).Opens :=
  ∏ᶜ fun k : Fin (n + 1) => coordinateOpenCover (R := R) (a k)

/-- A standard Cech intersection is contained in each chart occurring in its tuple. -/
theorem coordinateOpenCechIntersection_le {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ)
    (k : Fin (n + 1)) :
    coordinateOpenCechIntersection (R := R) a ≤ coordinateOpenCover (R := R) (a k) :=
  leOfHom (Pi.π (fun l : Fin (n + 1) => coordinateOpenCover (R := R) (a l)) k)

/-- Every finite intersection in the standard coordinate cover is affine. -/
theorem coordinateOpenCechIntersection_isAffineOpen {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) :
    IsAffineOpen (coordinateOpenCechIntersection (R := R) a) := by
  rw [show coordinateOpenCechIntersection (R := R) a =
      ⨅ k : Fin (n + 1), coordinateOpenCover (R := R) (a k) from
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      (Preorder.isLimitIInf _)).to_eq]
  exact IsAffineOpen.iInf fun k => coordinateOpenCover_isAffineOpen (R := R) (a k)

/-- The standard frame of `O(d)` restricted to an ordered Cech intersection. -/
noncomputable def coordinateHyperplaneTwistCechTrivialization {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) (j : σ) (d : ℤ) :
    (coordinateHyperplaneTwist (R := R) j d).restrict
        (coordinateOpenCechIntersection (R := R) a).ι ≅
      Scheme.Modules.unitObj
        (coordinateOpenCechIntersection (R := R) a).toScheme :=
  Scheme.Modules.restrictIsoOfPullbackIso
    (coordinateHyperplaneTwist (R := R) j d)
    (coordinateOpenCechIntersection (R := R) a)
    (Scheme.Modules.restrictTrivialization
      (coordinateOpenCechIntersection_le (R := R) a 0)
      (Scheme.Modules.pullbackIsoOfRestrictIso
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (a 0))
        (coordinateHyperplaneTwistTrivialization (R := R) (a 0).down j d)))

/-- A twist Cech factor is the corresponding structure-sheaf section module. -/
noncomputable def coordinateHyperplaneTwistBaseCechFactorIsoUnit {n : ℕ}
    (a : Fin (n + 1) → ULift.{u} σ) (j : σ) (d : ℤ) :
    Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (σ := σ)) n a ≅
      Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n a :=
  Scheme.Modules.baseModulePresheafObjIsoUnitOfRestrictIso
    (homogeneousProjπ (R := R) (σ := σ))
    (coordinateHyperplaneTwist (R := R) j d)
    (coordinateOpenCechIntersection (R := R) a)
    (coordinateHyperplaneTwistCechTrivialization (R := R) a j d)

/-- The degree-`n` ordered Cech object of `O(d)` is factorwise identified with
the ordered Cech object of the structure sheaf. -/
noncomputable def coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (σ := σ)) n ≅
      Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n :=
  Pi.mapIso (fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
    coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.1 j d)

/-- The degreewise twist-to-unit Cech comparison is the landed factor
comparison on every ordered tuple. -/
@[reassoc]
theorem coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit_hom_comp_π
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ)
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    (coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit
        (R := R) j d n).hom ≫
      Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        Scheme.Modules.baseCechFactor
          (homogeneousProjπ (R := R) (σ := σ))
          (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
          (coordinateOpenCover (R := R) (σ := σ)) n b.1) a =
    Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)
        (coordinateOpenCover (R := R) (σ := σ)) n b.1) a ≫
      (coordinateHyperplaneTwistBaseCechFactorIsoUnit
        (R := R) a.1 j d).hom := by
  exact Pi.mapIso_hom_π
    (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) b.1 j d) a

end

end MvPolynomial
