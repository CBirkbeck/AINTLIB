/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistPullbackEquivalence
import ModularCurves.ForMathlib.EquivalenceRightAdjointMate

/-!
# Pushforward projection formula for projective-space twists

The inverse-equivalence mate of negative-twist pullback compatibility gives
the positive-twist projection formula for pushforward along an arbitrary
morphism into polynomial projective space.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory HomogeneousIdeal MonoidalCategory

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]
variable {X : Scheme.{u}}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Positive coordinate twists satisfy the projection formula for
pushforward along every morphism into polynomial projective space. -/
noncomputable def coordinateHyperplanePoleSheafPowerPushforwardTensorIso
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ) :
    let Pj := Proj (homogeneousSubmodule σ R)
    letI := Scheme.Modules.monoidalCategory Pj
    letI := Scheme.Modules.monoidalCategory X
    Scheme.Modules.pushforward f ⋙
        tensorRight (coordinateHyperplanePoleSheafPower (R := R) j n) ≅
      tensorRight ((Scheme.Modules.pullback f).obj
        (coordinateHyperplanePoleSheafPower (R := R) j n)) ⋙
        Scheme.Modules.pushforward f := by
  let Pj := Proj (homogeneousSubmodule σ R)
  letI : MonoidalCategory Pj.Modules :=
    Scheme.Modules.monoidalCategory Pj
  letI : MonoidalCategory X.Modules :=
    Scheme.Modules.monoidalCategory X
  let E := coordinateHyperplanePoleSheafPowerTensorEquivalence
    (R := R) j n
  let EX := pullbackCoordinateHyperplanePoleSheafPowerTensorEquivalence
    f j n
  let h := coordinateHyperplaneIdealModulePowerTensorEquivalenceCompPullbackIso
    f j n
  exact inverseEquivalenceCommutesWithRightAdjoint
    E.symm EX.symm
    (Scheme.Modules.pullback f) (Scheme.Modules.pushforward f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) h

end

end MvPolynomial
