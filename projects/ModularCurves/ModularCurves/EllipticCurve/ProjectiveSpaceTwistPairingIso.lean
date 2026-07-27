/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwist
import ModularCurves.ForMathlib.SchemeModuleOpenCoverIso
import ModularCurves.Picard.DualPullback.LocalTrivializationInv

/-!
# Cancellation for projective-space twists

The explicit evaluation pairing between the concrete coordinate-hyperplane
twists `O(-n)` and `O(n)` is an isomorphism over every commutative base ring.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory HomogeneousIdeal MonoidalCategory

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem coordinateHyperplanePowerPairing_over_isIso
    (i j : σ) (n : ℕ) :
    IsIso ((coordinateHyperplanePowerPairing (R := R) j n).over
      (coordinateOpen (R := R) i)) := by
  let X := Proj (homogeneousSubmodule σ R)
  let U := coordinateOpen (R := R) i
  let M := coordinateHyperplaneIdealModulePower (R := R) j n
  let N := coordinateHyperplanePoleSheafPower (R := R) j n
  let MN : X.Modules := M ⊗ N
  let eM := coordinateHyperplaneIdealModulePowerTrivialization (R := R) i j n
  let eN := coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j n
  let eMN :=
    ModularCurves.restrictMonoidalTensorIso U.ι M N ≪≫
      (eM ⊗ᵢ eN) ≪≫ ModularCurves.unitObjTensorIso U.toScheme
  let pS := Scheme.Modules.overTrivializationOfRestrictIso MN U eMN
  let pT : (Scheme.Modules.unitObj X).over U ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) := Iso.refl _
  let q := coordinateHyperplanePowerPairing (R := R) j n
  let m := q.over U
  let oneU : Γ(X, U) := 1
  let x := ModularCurves.overTrivializationSection MN U pS oneU
  let y : (Scheme.Modules.unitObj X).over U |>.val.obj
      (.op (Over.mk (𝟙 U))) := oneU
  have hs : pS.inv.val.app (.op (Over.mk (𝟙 U))) oneU = x := rfl
  have hx :
      x = ModularCurves.tensorSection M N U
        (coordinateHyperplaneIdealModulePowerFrameSection (R := R) i j n)
        (coordinateHyperplanePoleSheafPowerFrameSection (R := R) i j n) := by
    exact ModularCurves.overTrivializationSection_tensor_one M N U eM eN
  have hm : m.val.app (.op (Over.mk (𝟙 U))) x = y := by
    change (coordinateHyperplanePowerPairing (R := R) j n).val.app
      (.op U) x = oneU
    rw [hx]
    exact coordinateHyperplanePowerPairing_frameSection (R := R) i j n
  have ht : pT.hom.val.app (.op (Over.mk (𝟙 U))) y = oneU := rfl
  letI : ∀ V, IsMulCommutative (X.ringCatSheaf.obj.obj V) :=
    fun V ↦ by
      change IsMulCommutative (X.presheaf.obj V)
      exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b
  exact Scheme.Modules.isIso_of_local_trivializations_terminal_oneT
    U pS pT m x y hs hm ht

private theorem coordinateHyperplanePowerPairing_restrict_isIso
    (i j : σ) (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (coordinateOpen (R := R) i).ι).map
      (coordinateHyperplanePowerPairing (R := R) j n)) := by
  letI := coordinateHyperplanePowerPairing_over_isIso (R := R) i j n
  exact Scheme.Modules.isIso_restrict_of_isIso_over
    (coordinateHyperplanePowerPairing (R := R) j n)
    (coordinateOpen (R := R) i)

/-- The concrete evaluation pairing `O(-n) ⊗ O(n) ⟶ O` on polynomial
projective space is an isomorphism over every commutative base ring. -/
theorem coordinateHyperplanePowerPairing_isIso (j : σ) (n : ℕ) :
    IsIso (coordinateHyperplanePowerPairing (R := R) j n) := by
  let U : ULift.{u} σ → (Proj (homogeneousSubmodule σ R)).Opens :=
    fun i ↦ coordinateOpen (R := R) i.down
  apply Scheme.Modules.isIso_of_isIso_restrict
    (coordinateHyperplanePowerPairing (R := R) j n) U
  · apply top_unique
    rw [← iSup_coordinateOpen_eq_top (R := R)]
    exact iSup_le fun i ↦ le_iSup U (ULift.up i)
  · intro i
    exact coordinateHyperplanePowerPairing_restrict_isIso
      (R := R) i.down j n

end

end MvPolynomial
