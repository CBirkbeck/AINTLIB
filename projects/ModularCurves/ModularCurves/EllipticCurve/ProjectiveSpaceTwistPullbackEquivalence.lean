/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistTensorEquivalence
import ModularCurves.ForMathlib.PullbackTensorGeneral

/-!
# Pullback equivalences from projective-space twists

The concrete equivalence given by tensoring with `O(n)` pulls back along an
arbitrary morphism to polynomial projective space. Its inverse is tensoring
with the pullback of `O(-n)`.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory HomogeneousIdeal MonoidalCategory

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]
variable {X : Scheme.{u}}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Tensoring by the pullback of `O(n)` is an equivalence, with inverse
given by tensoring by the pullback of `O(-n)`. -/
noncomputable def pullbackCoordinateHyperplanePoleSheafPowerTensorEquivalence
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ) :
    X.Modules ≌ X.Modules := by
  let Pj := Proj (homogeneousSubmodule σ R)
  letI : MonoidalCategory Pj.Modules :=
    Scheme.Modules.monoidalCategory Pj
  letI : SymmetricCategory Pj.Modules :=
    Scheme.Modules.symmetricCategory Pj
  letI : MonoidalCategory X.Modules :=
    Scheme.Modules.monoidalCategory X
  letI : SymmetricCategory X.Modules :=
    Scheme.Modules.symmetricCategory X
  letI : (Scheme.Modules.pullback f).Monoidal :=
    Scheme.Modules.pullbackMonoidal f
  let N := coordinateHyperplaneIdealModulePower (R := R) j n
  let P := coordinateHyperplanePoleSheafPower (R := R) j n
  let q := coordinateHyperplanePowerPairing (R := R) j n
  letI : IsIso q :=
    coordinateHyperplanePowerPairing_isIso (R := R) j n
  let eNP : N ⊗ P ≅ 𝟙_ Pj.Modules :=
    asIso q ≪≫ (ModularCurves.monoidalUnitObjIso Pj).symm
  let ePbNP :
      (Scheme.Modules.pullback f).obj N ⊗
          (Scheme.Modules.pullback f).obj P ≅ 𝟙_ X.Modules :=
    Functor.Monoidal.μIso (Scheme.Modules.pullback f) N P ≪≫
      (Scheme.Modules.pullback f).mapIso eNP ≪≫
      (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).symm
  let ePbPN :
      (Scheme.Modules.pullback f).obj P ⊗
          (Scheme.Modules.pullback f).obj N ≅ 𝟙_ X.Modules :=
    (β_ _ _) ≪≫ ePbNP
  let F := tensorRight ((Scheme.Modules.pullback f).obj P)
  let G := tensorRight ((Scheme.Modules.pullback f).obj N)
  let eta : 𝟭 X.Modules ≅ F ⋙ G :=
    (rightUnitorNatIso X.Modules).symm ≪≫
      (tensoringRight X.Modules).mapIso ePbPN.symm ≪≫
      tensorRightTensor _ _
  let epsilon : G ⋙ F ≅ 𝟭 X.Modules :=
    (tensorRightTensor _ _).symm ≪≫
      (tensoringRight X.Modules).mapIso ePbNP ≪≫
      rightUnitorNatIso X.Modules
  exact CategoryTheory.Equivalence.mk F G eta epsilon

/-- The functor of the pulled-back positive-twist equivalence is right
tensoring by the pullback of `O(n)`. -/
@[simp]
theorem pullbackCoordinateHyperplanePoleSheafPowerTensorEquivalence_functor
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ) :
    letI := Scheme.Modules.monoidalCategory X
    (pullbackCoordinateHyperplanePoleSheafPowerTensorEquivalence f j n).functor =
      tensorRight ((Scheme.Modules.pullback f).obj
        (coordinateHyperplanePoleSheafPower (R := R) j n)) := by
  rfl

/-- The inverse functor of the pulled-back positive-twist equivalence is
right tensoring by the pullback of `O(-n)`. -/
@[simp]
theorem pullbackCoordinateHyperplanePoleSheafPowerTensorEquivalence_inverse
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ) :
    letI := Scheme.Modules.monoidalCategory X
    (pullbackCoordinateHyperplanePoleSheafPowerTensorEquivalence f j n).inverse =
      tensorRight ((Scheme.Modules.pullback f).obj
        (coordinateHyperplaneIdealModulePower (R := R) j n)) := by
  rfl

/-- Negative projective twists commute with pullback. This is the
left-adjoint comparison whose mate gives the positive-twist projection
formula for pushforward. -/
noncomputable def coordinateHyperplaneIdealModulePowerTensorEquivalenceCompPullbackIso
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ) :
    let Pj := Proj (homogeneousSubmodule σ R)
    letI := Scheme.Modules.monoidalCategory Pj
    letI := Scheme.Modules.monoidalCategory X
    (coordinateHyperplanePoleSheafPowerTensorEquivalence
        (R := R) j n).inverse ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback f ⋙
        (pullbackCoordinateHyperplanePoleSheafPowerTensorEquivalence
          f j n).inverse := by
  let Pj := Proj (homogeneousSubmodule σ R)
  letI : MonoidalCategory Pj.Modules :=
    Scheme.Modules.monoidalCategory Pj
  letI : MonoidalCategory X.Modules :=
    Scheme.Modules.monoidalCategory X
  letI : (Scheme.Modules.pullback f).Monoidal :=
    Scheme.Modules.pullbackMonoidal f
  rw [coordinateHyperplanePoleSheafPowerTensorEquivalence_inverse,
    pullbackCoordinateHyperplanePoleSheafPowerTensorEquivalence_inverse]
  exact (Functor.Monoidal.commTensorRight
    (coordinateHyperplaneIdealModulePower (R := R) j n)
    (F := Scheme.Modules.pullback f)).symm

end

end MvPolynomial
