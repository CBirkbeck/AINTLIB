/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCech

/-!
# Quasicoherence after a positive projective twist

The concrete positive coordinate twist is trivial on every member of the
standard affine cover. Tensoring a quasicoherent module by it is therefore
locally isomorphic to the original module and remains quasicoherent.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory HomogeneousIdeal MonoidalCategory
  Opposite TopologicalSpace

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance positiveTwistQuasicoherentMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- Tensoring a quasicoherent module on polynomial projective space by a
nonnegative coordinate twist preserves quasicoherence. -/
theorem moduleTensorCoordinateHyperplanePoleSheafPower_isQuasicoherent
    [Fintype σ] (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] (j : σ) (n : ℕ) :
    (M ⊗ coordinateHyperplanePoleSheafPower (R := R) j n).IsQuasicoherent := by
  let X := Proj (homogeneousSubmodule σ R)
  let P := coordinateHyperplanePoleSheafPower (R := R) j n
  let MP : X.Modules := M ⊗ P
  let U : ULift.{u} σ → X.Opens :=
    coordinateOpenCover (R := R)
  have hlocal (i : ULift.{u} σ) :
      (MP.over (U i)).IsQuasicoherent := by
    letI : IsAffine (U i).toScheme :=
      coordinateOpenCover_isAffineOpen (R := R) i
    let eP : P.restrict (U i).ι ≅
        Scheme.Modules.unitObj (U i).toScheme :=
      coordinateHyperplanePoleSheafPowerTrivialization
        (R := R) i.down j n
    let e :
        MP.restrict (U i).ι ≅ M.restrict (U i).ι :=
      ModularCurves.restrictMonoidalTensorIso (U i).ι M P ≪≫
        (Iso.refl _ ⊗ᵢ eP) ≪≫
        (Iso.refl _ ⊗ᵢ
          (ModularCurves.monoidalUnitObjIso (U i).toScheme).symm) ≪≫
        ρ_ (M.restrict (U i).ι)
    have hRestrict :
        (MP.restrict (U i).ι).IsQuasicoherent :=
      (Scheme.Modules.isQuasicoherent (U i).toScheme).prop_of_iso
        e.symm inferInstance
    letI : (MP.restrict (U i).ι).IsQuasicoherent :=
      hRestrict
    exact
      Scheme.Modules.isQuasicoherent_over_of_restrict_of_isAffineOpen
        MP (U i)
  have hcover :
      (Opens.grothendieckTopology X).CoversTop U := by
    rw [Opens.coversTop_iff, IsOpenCover,
      iSup_coordinateOpenCover_eq_top]
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ MP _ U hcover hlocal

end

end MvPolynomial
