/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveCoordinateTwistMap
import ModularCurves.ForMathlib.SchemeModulePullbackLocalIso

/-!
# Pullbacks of projective coordinate twist maps

The canonical coordinate section of `O(n)` pulls back to a unit morphism on
an arbitrary source, invertible over the preimage of its standard chart.
Tensoring gives the corresponding coordinate multiplication map on every
source module.
-/

open CategoryTheory MonoidalCategory

noncomputable section

universe u

namespace MvPolynomial

open AlgebraicGeometry HomogeneousIdeal

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- Pullback of the canonical coordinate morphism `O -> O(n)`. -/
noncomputable def coordinateHyperplanePolePullbackUnitHom
    {X : Scheme.{u}}
    (g : X ⟶ Proj (homogeneousSubmodule σ R))
    (j : σ) (n : ℕ) :
    Scheme.Modules.unitObj X ⟶
      (Scheme.Modules.pullback g).obj
        (coordinateHyperplanePoleSheafPower (R := R) j n) :=
  Scheme.Modules.pullbackUnitHom g
    (coordinateHyperplanePoleUnitHomPower (R := R) j n)

/-- The pulled-back coordinate morphism is invertible on the preimage of its
standard projective chart. -/
theorem coordinateHyperplanePolePullbackUnitHom_restrict_self_isIso
    {X : Scheme.{u}}
    (g : X ⟶ Proj (homogeneousSubmodule σ R))
    (j : σ) (n : ℕ) :
    IsIso
      ((Scheme.Modules.restrictFunctor
        (g ⁻¹ᵁ coordinateOpen (R := R) j).ι).map
        (coordinateHyperplanePolePullbackUnitHom
          (R := R) g j n)) := by
  letI :
      IsIso
        ((Scheme.Modules.restrictFunctor
          (coordinateOpen (R := R) j).ι).map
          (coordinateHyperplanePoleUnitHomPower (R := R) j n)) :=
    coordinateHyperplanePoleUnitHomPower_restrict_self_isIso
      (R := R) j n
  exact
    Scheme.Modules.isIso_restrict_pullbackUnitHom_of_restrict
      g (coordinateHyperplanePoleUnitHomPower (R := R) j n)
        (coordinateOpen (R := R) j)

/-- Multiplication of a source module by the pullback of the `n`th power of
a projective coordinate. -/
noncomputable def coordinateHyperplanePolePullbackTwistMap
    {X : Scheme.{u}}
    (g : X ⟶ Proj (homogeneousSubmodule σ R))
    (M : X.Modules) (j : σ) (n : ℕ) :
    M ⟶
      M ⊗
        (Scheme.Modules.pullback g).obj
          (coordinateHyperplanePoleSheafPower (R := R) j n) :=
  Scheme.Modules.tensorByUnitHom M
    ((Scheme.Modules.pullback g).obj
      (coordinateHyperplanePoleSheafPower (R := R) j n))
    (coordinateHyperplanePolePullbackUnitHom (R := R) g j n)

/-- Multiplication by a pulled-back coordinate power is invertible on the
preimage of its standard projective chart. -/
theorem coordinateHyperplanePolePullbackTwistMap_restrict_self_isIso
    {X : Scheme.{u}}
    (g : X ⟶ Proj (homogeneousSubmodule σ R))
    (M : X.Modules) (j : σ) (n : ℕ) :
    IsIso
      ((Scheme.Modules.restrictFunctor
        (g ⁻¹ᵁ coordinateOpen (R := R) j).ι).map
        (coordinateHyperplanePolePullbackTwistMap
          (R := R) g M j n)) := by
  letI :
      IsIso
        ((Scheme.Modules.restrictFunctor
          (g ⁻¹ᵁ coordinateOpen (R := R) j).ι).map
          (coordinateHyperplanePolePullbackUnitHom
            (R := R) g j n)) :=
    coordinateHyperplanePolePullbackUnitHom_restrict_self_isIso
      (R := R) g j n
  exact Scheme.Modules.isIso_restrict_tensorByUnitHom
    M
    ((Scheme.Modules.pullback g).obj
      (coordinateHyperplanePoleSheafPower (R := R) j n))
    (coordinateHyperplanePolePullbackUnitHom (R := R) g j n)
    (g ⁻¹ᵁ coordinateOpen (R := R) j)

end MvPolynomial
