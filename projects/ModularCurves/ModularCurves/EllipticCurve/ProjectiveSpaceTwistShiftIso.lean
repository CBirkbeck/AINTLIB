/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistPairingIso

/-!
# Shift isomorphisms for projective-space twists

Positive powers of the coordinate-hyperplane twist are additive, and
tensoring `O(-m)` with `O(n)` for `m ≤ n` gives `O(n-m)`.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory HomogeneousIdeal MonoidalCategory

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance projectiveSpaceTwistShiftMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The recursively defined positive powers satisfy `O(m+n) ≅ O(m) ⊗ O(n)`. -/
noncomputable def coordinateHyperplanePoleSheafPower_addIso
    (j : σ) :
    ∀ m n : ℕ,
      coordinateHyperplanePoleSheafPower (R := R) j (m + n) ≅
        coordinateHyperplanePoleSheafPower (R := R) j m ⊗
          coordinateHyperplanePoleSheafPower (R := R) j n
  | m, 0 => (ρ_ (coordinateHyperplanePoleSheafPower (R := R) j m)).symm
  | m, n + 1 =>
      (coordinateHyperplanePoleSheafPower_addIso j m n ⊗ᵢ
          Iso.refl (coordinateHyperplanePoleSheaf (R := R) j)) ≪≫
        α_ (coordinateHyperplanePoleSheafPower (R := R) j m)
          (coordinateHyperplanePoleSheafPower (R := R) j n)
          (coordinateHyperplanePoleSheaf (R := R) j)

/-- Cancelling equal negative and positive powers gives
`O(-m) ⊗ O(m+n) ≅ O(n)`. -/
noncomputable def
    coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerAddIso
    (j : σ) (m n : ℕ) :
    coordinateHyperplaneIdealModulePower (R := R) j m ⊗
        coordinateHyperplanePoleSheafPower (R := R) j (m + n) ≅
      coordinateHyperplanePoleSheafPower (R := R) j n := by
  let X := Proj (homogeneousSubmodule σ R)
  let N := coordinateHyperplaneIdealModulePower (R := R) j m
  let Pm := coordinateHyperplanePoleSheafPower (R := R) j m
  let Pn := coordinateHyperplanePoleSheafPower (R := R) j n
  let q := coordinateHyperplanePowerPairing (R := R) j m
  letI : IsIso q :=
    coordinateHyperplanePowerPairing_isIso (R := R) j m
  let eNP : N ⊗ Pm ≅ 𝟙_ X.Modules :=
    asIso q ≪≫ (ModularCurves.monoidalUnitObjIso X).symm
  exact
    (Iso.refl N ⊗ᵢ
      coordinateHyperplanePoleSheafPower_addIso (R := R) j m n) ≪≫
      (α_ N Pm Pn).symm ≪≫
      (eNP ⊗ᵢ Iso.refl Pn) ≪≫
      λ_ Pn

/-- If `m ≤ n`, then `O(-m) ⊗ O(n) ≅ O(n-m)`. -/
noncomputable def
    coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE
    (j : σ) (m n : ℕ) (h : m ≤ n) :
    coordinateHyperplaneIdealModulePower (R := R) j m ⊗
        coordinateHyperplanePoleSheafPower (R := R) j n ≅
      coordinateHyperplanePoleSheafPower (R := R) j (n - m) :=
  eqToIso (congrArg
      (fun k ↦ coordinateHyperplaneIdealModulePower (R := R) j m ⊗
        coordinateHyperplanePoleSheafPower (R := R) j k)
      (Nat.add_sub_of_le h).symm) ≪≫
    coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerAddIso
      (R := R) j m (n - m)

end

end MvPolynomial
