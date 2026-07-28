/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistPairingIso

/-!
# Tensor equivalences from projective-space twists

Tensoring by the concrete positive coordinate-hyperplane twist `O(n)` is an
equivalence, with quasi-inverse given by tensoring by `O(-n)`.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory HomogeneousIdeal MonoidalCategory

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Tensoring by `O(n)` on polynomial projective space is an equivalence. -/
noncomputable def coordinateHyperplanePoleSheafPowerTensorEquivalence
    (j : σ) (n : ℕ) :
    let X := Proj (homogeneousSubmodule σ R)
    X.Modules ≌ X.Modules := by
  let X := Proj (homogeneousSubmodule σ R)
  letI : MonoidalCategory X.Modules :=
    Scheme.Modules.monoidalCategory X
  letI : SymmetricCategory X.Modules :=
    Scheme.Modules.symmetricCategory X
  let N := coordinateHyperplaneIdealModulePower (R := R) j n
  let P := coordinateHyperplanePoleSheafPower (R := R) j n
  let q := coordinateHyperplanePowerPairing (R := R) j n
  letI : IsIso q :=
    coordinateHyperplanePowerPairing_isIso (R := R) j n
  let eNP : N ⊗ P ≅ 𝟙_ X.Modules :=
    asIso q ≪≫ (ModularCurves.monoidalUnitObjIso X).symm
  let ePN : P ⊗ N ≅ 𝟙_ X.Modules :=
    (β_ P N) ≪≫ eNP
  let F := tensorRight P
  let G := tensorRight N
  let eta : 𝟭 X.Modules ≅ F ⋙ G :=
    (rightUnitorNatIso X.Modules).symm ≪≫
      (tensoringRight X.Modules).mapIso ePN.symm ≪≫
      tensorRightTensor P N
  let epsilon : G ⋙ F ≅ 𝟭 X.Modules :=
    (tensorRightTensor N P).symm ≪≫
      (tensoringRight X.Modules).mapIso eNP ≪≫
      rightUnitorNatIso X.Modules
  letI : F.IsEquivalence := Functor.IsEquivalence.mk' G eta epsilon
  exact F.asEquivalence

/-- The functor underlying the positive-twist equivalence is right tensoring
by the concrete module `O(n)`. -/
@[simp]
theorem coordinateHyperplanePoleSheafPowerTensorEquivalence_functor
    (j : σ) (n : ℕ) :
    let X := Proj (homogeneousSubmodule σ R)
    letI := Scheme.Modules.monoidalCategory X
    (coordinateHyperplanePoleSheafPowerTensorEquivalence
      (R := R) j n).functor =
      tensorRight (coordinateHyperplanePoleSheafPower (R := R) j n) := by
  rfl

end

end MvPolynomial
