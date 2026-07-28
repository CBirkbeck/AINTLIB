/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwist
import ModularCurves.ForMathlib.SchemeModuleOpenCoverIso

/-!
# Projective coordinate twist maps

A morphism from the structure module to a module induces multiplication
into its tensor twist. For the coordinate-hyperplane pole sheaf and its
nonnegative powers, this map is invertible on the corresponding standard
projective chart.
-/

open CategoryTheory MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- Tensor a module with a morphism from the structure module. -/
noncomputable def tensorByUnitHom
    {X : Scheme.{u}} (M L : X.Modules)
    (q : unitObj X ⟶ L) :
    M ⟶ (M ⊗ L) :=
  (ρ_ M).inv ≫
    (𝟙 M ⊗ₘ ((ModularCurves.monoidalUnitObjIso X).hom ≫ q))

/-- Tensoring by a structure-module morphism is invertible on every open
where that morphism is invertible. -/
theorem isIso_restrict_tensorByUnitHom
    {X : Scheme.{u}} (M L : X.Modules)
    (q : unitObj X ⟶ L) (U : X.Opens)
    [IsIso ((restrictFunctor U.ι).map q)] :
    IsIso ((restrictFunctor U.ι).map (tensorByUnitHom M L q)) := by
  let F := restrictFunctor U.ι
  letI : (pullback U.ι).Monoidal :=
    pullbackMonoidal U.ι
  letI : F.Monoidal :=
    Functor.Monoidal.transport (restrictFunctorIsoPullback U.ι).symm
  haveI :
      IsIso
        (F.map ((ModularCurves.monoidalUnitObjIso X).hom ≫ q)) := by
    rw [F.map_comp]
    infer_instance
  unfold tensorByUnitHom
  rw [F.map_comp]
  rw [Functor.Monoidal.map_rightUnitor_inv]
  rw [Functor.Monoidal.map_tensor]
  rw [F.map_id]
  infer_instance

end AlgebraicGeometry.Scheme.Modules

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory HomogeneousIdeal MonoidalCategory

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem coordinateHyperplanePoleUnitHom_over_self_isIso
    (j : σ) :
    IsIso
      ((coordinateHyperplanePoleUnitHom (R := R) j).over
        (coordinateOpen (R := R) j)) := by
  let X := Proj (homogeneousSubmodule σ R)
  let U := coordinateOpen (R := R) j
  let M := ModularCurves.idealModule
    (coordinateHyperplaneι (R := R) j)
  letI : ∀ V, IsMulCommutative (X.ringCatSheaf.obj.obj V) :=
    fun V ↦ by
      change IsMulCommutative (X.presheaf.obj V)
      exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b
  let e :=
    ModularCurves.SheafOfModules.dualOverIsoOfIso
      X.ringCatSheaf M U
      (AlgebraicGeometry.Scheme.Modules.overTrivializationOfRestrictIso
        M U
          (coordinateHyperplaneIdealModuleTrivialization
          (R := R) j j).symm)
  let q := (coordinateHyperplanePoleUnitHom (R := R) j).over U
  have hq :
      q ≫ e.hom =
        ModularCurves.SheafOfModules.overUnitScalarEnd
          X.ringCatSheaf U 1 := by
    have h :=
      coordinateHyperplanePoleUnitHom_over_comp_trivialization
        (R := R) j j
    rw [coordinateHyperplaneLocalEquation_self] at h
    change q ≫ e.hom =
      ModularCurves.SheafOfModules.overUnitScalarEnd
        X.ringCatSheaf U 1 at h
    exact h
  have hone :
      ModularCurves.SheafOfModules.overUnitScalarEnd
          X.ringCatSheaf U 1 =
        𝟙 _ :=
    (ModularCurves.SheafOfModules.overUnitScalarEndRingHom
      X.ringCatSheaf U).map_one
  have hqe : IsIso (q ≫ e.hom) := by
    rw [hq, hone]
    exact CategoryTheory.IsIso.id _
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ q e.hom
    e.isIso_hom hqe

/-- The canonical coordinate morphism `O -> O(1)` is invertible on its
own standard projective chart. -/
theorem coordinateHyperplanePoleUnitHom_restrict_self_isIso
    (j : σ) :
    IsIso
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctor
        (coordinateOpen (R := R) j).ι).map
        (coordinateHyperplanePoleUnitHom (R := R) j)) := by
  letI := coordinateHyperplanePoleUnitHom_over_self_isIso (R := R) j
  exact
    AlgebraicGeometry.Scheme.Modules.isIso_restrict_of_isIso_over
      (coordinateHyperplanePoleUnitHom (R := R) j)
      (coordinateOpen (R := R) j)

/-- The iterated coordinate morphism `O -> O(n)`. -/
noncomputable def coordinateHyperplanePoleUnitHomPower
    (j : σ) :
    ∀ n : ℕ,
      AlgebraicGeometry.Scheme.Modules.unitObj
          (Proj (homogeneousSubmodule σ R)) ⟶
        coordinateHyperplanePoleSheafPower (R := R) j n
  | 0 => (ModularCurves.monoidalUnitObjIso
      (Proj (homogeneousSubmodule σ R))).inv
  | n + 1 =>
      coordinateHyperplanePoleUnitHomPower j n ≫
        AlgebraicGeometry.Scheme.Modules.tensorByUnitHom
          (coordinateHyperplanePoleSheafPower (R := R) j n)
          (coordinateHyperplanePoleSheaf (R := R) j)
          (coordinateHyperplanePoleUnitHom (R := R) j) ≫
        eqToHom
          (coordinateHyperplanePoleSheafPower_succ
            (R := R) j n).symm

/-- The iterated coordinate morphism `O -> O(n)` is invertible on its
own standard projective chart. -/
theorem coordinateHyperplanePoleUnitHomPower_restrict_self_isIso
    (j : σ) :
    ∀ n : ℕ,
      IsIso
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctor
          (coordinateOpen (R := R) j).ι).map
          (coordinateHyperplanePoleUnitHomPower (R := R) j n)) := by
  intro n
  induction n with
  | zero =>
      simp only [coordinateHyperplanePoleUnitHomPower]
      exact Functor.map_isIso _
        (ModularCurves.monoidalUnitObjIso
          (Proj (homogeneousSubmodule σ R))).inv
  | succ n ih =>
      let F := AlgebraicGeometry.Scheme.Modules.restrictFunctor
        (coordinateOpen (R := R) j).ι
      haveI hPower :
          IsIso
            (F.map
              (coordinateHyperplanePoleUnitHomPower (R := R) j n)) :=
        ih
      haveI hCoordinate :
          IsIso
            (F.map
              (coordinateHyperplanePoleUnitHom (R := R) j)) :=
        coordinateHyperplanePoleUnitHom_restrict_self_isIso (R := R) j
      haveI hStep :
          IsIso
            (F.map
              (AlgebraicGeometry.Scheme.Modules.tensorByUnitHom
                (coordinateHyperplanePoleSheafPower (R := R) j n)
                (coordinateHyperplanePoleSheaf (R := R) j)
                (coordinateHyperplanePoleUnitHom (R := R) j))) :=
        AlgebraicGeometry.Scheme.Modules.isIso_restrict_tensorByUnitHom
          (coordinateHyperplanePoleSheafPower (R := R) j n)
          (coordinateHyperplanePoleSheaf (R := R) j)
          (coordinateHyperplanePoleUnitHom (R := R) j)
          (coordinateOpen (R := R) j)
      change IsIso (F.map (_ ≫ _ ≫ _))
      rw [F.map_comp, F.map_comp]
      infer_instance

/-- Multiplication of a module by the `n`th power of a projective
coordinate. -/
noncomputable def coordinateHyperplanePoleTwistMap
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j : σ) (n : ℕ) :
    M ⟶ M ⊗ coordinateHyperplanePoleSheafPower (R := R) j n :=
  AlgebraicGeometry.Scheme.Modules.tensorByUnitHom M
    (coordinateHyperplanePoleSheafPower (R := R) j n)
    (coordinateHyperplanePoleUnitHomPower (R := R) j n)

/-- Multiplication by the `n`th power of a projective coordinate is
invertible on the corresponding standard chart. -/
theorem coordinateHyperplanePoleTwistMap_restrict_self_isIso
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j : σ) (n : ℕ) :
    IsIso
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctor
        (coordinateOpen (R := R) j).ι).map
        (coordinateHyperplanePoleTwistMap (R := R) M j n)) := by
  letI :
      IsIso
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctor
          (coordinateOpen (R := R) j).ι).map
          (coordinateHyperplanePoleUnitHomPower (R := R) j n)) :=
    coordinateHyperplanePoleUnitHomPower_restrict_self_isIso
      (R := R) j n
  exact
    AlgebraicGeometry.Scheme.Modules.isIso_restrict_tensorByUnitHom
      M (coordinateHyperplanePoleSheafPower (R := R) j n)
      (coordinateHyperplanePoleUnitHomPower (R := R) j n)
      (coordinateOpen (R := R) j)

end MvPolynomial
