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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

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
  Scheme.Modules.restrictOpenTrivialization
    (coordinateOpenCechIntersection_le (R := R) a 0)
    (coordinateHyperplaneTwistTrivialization (R := R) (a 0).down j d)

private noncomputable def baseModulePresheafObjIsoUnitOfOverIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (Scheme.Modules.baseModulePresheaf π M).obj (op U) ≅
      (Scheme.Modules.baseModulePresheaf π (Scheme.Modules.unitObj X)).obj (op U) := by
  let eVal := (SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso e
  let eTop := (PresheafOfModules.evaluation (X.ringCatSheaf.over U).obj
    (.op (Over.mk (𝟙 U)))).mapIso eVal
  let f : Γ(S, (⊤ : S.Opens)) →+* Γ(X, U) :=
    (X.presheaf.map
      ((Limits.initialOpOfTerminal Limits.isTerminalTop).to (op U))).hom.comp
        π.appTop.hom
  exact (ModuleCat.restrictScalars f).mapIso eTop

private theorem baseModulePresheafObjIsoUnitOfOverIso_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {U V : X.Opens} (hVU : V ≤ U)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (Scheme.Modules.baseModulePresheaf π M).map (homOfLE hVU).op ≫
        (baseModulePresheafObjIsoUnitOfOverIso π M V
          (ModularCurves.SheafOfModules.restrictOverTrivialization
            X.ringCatSheaf M U e (Over.mk (homOfLE hVU)))).hom =
      (baseModulePresheafObjIsoUnitOfOverIso π M U e).hom ≫
        (Scheme.Modules.baseModulePresheaf π
          (Scheme.Modules.unitObj X)).map (homOfLE hVU).op := by
  ext x
  change e.hom.val.app (.op (Over.mk (homOfLE hVU)))
      (M.presheaf.map (homOfLE hVU).op x) =
    X.presheaf.map (homOfLE hVU).op
      (e.hom.val.app (.op (Over.mk (𝟙 U))) x)
  let k : Over.mk (homOfLE hVU) ⟶ Over.mk (𝟙 U) :=
    Over.mkIdTerminal.from (Over.mk (homOfLE hVU))
  have hnat := PresheafOfModules.naturality_apply e.hom.val k.op x
  change e.hom.val.app (.op (Over.mk (homOfLE hVU)))
      ((M.over U).val.map k.op x) =
    (X.ringCatSheaf.over U).obj.map k.op
      (e.hom.val.app (.op (Over.mk (𝟙 U))) x) at hnat
  dsimp only [k] at hnat
  change e.hom.val.app (.op (Over.mk (homOfLE hVU)))
      (M.presheaf.map
        (Over.mkIdTerminal.from (Over.mk (homOfLE hVU))).left.op x) =
    X.presheaf.map
      (Over.mkIdTerminal.from (Over.mk (homOfLE hVU))).left.op
        (e.hom.val.app (.op (Over.mk (𝟙 U))) x) at hnat
  rw [Over.mkIdTerminal_from_left] at hnat
  exact hnat

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
  baseModulePresheafObjIsoUnitOfOverIso
    (homogeneousProjπ (R := R) (σ := σ))
    (coordinateHyperplaneTwist (R := R) j d)
    (coordinateOpenCechIntersection (R := R) a)
    (Scheme.Modules.overTrivializationOfRestrictIso
      (coordinateHyperplaneTwist (R := R) j d)
      (coordinateOpenCechIntersection (R := R) a)
      (coordinateHyperplaneTwistCechTrivialization (R := R) a j d))

/-- The inclusion of a full ordered Cech intersection into the intersection
obtained by deleting one entry. -/
abbrev coordinateOpenCechDelete [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) :
    coordinateOpenCechIntersection (R := R) a.1 ⟶
      coordinateOpenCechIntersection (R := R) (a.delete k).1 :=
  (((FormalCoproduct.mk _ (coordinateOpenCover (R := R) (σ := σ))).mapPower
    (SimplexCategory.δ k).toOrderHom.toFun).φ a.1)

/-- The order relation underlying `coordinateOpenCechDelete`. -/
theorem coordinateOpenCechDelete_le [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) :
    coordinateOpenCechIntersection (R := R) a.1 ≤
      coordinateOpenCechIntersection (R := R) (a.delete k).1 :=
  leOfHom (coordinateOpenCechDelete (R := R) a k)

/-- Deleting a noninitial entry preserves the anchor frame on the smaller
standard intersection. -/
theorem coordinateHyperplaneTwistCechTrivialization_restrict_delete_of_ne_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ 0) (j : σ) (d : ℤ) :
    Scheme.Modules.restrictOpenTrivialization
        (coordinateOpenCechDelete_le (R := R) a k)
        (coordinateHyperplaneTwistCechTrivialization
          (R := R) (a.delete k).1 j d) =
      coordinateHyperplaneTwistCechTrivialization (R := R) a.1 j d := by
  obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hk
  rw [coordinateHyperplaneTwistCechTrivialization,
    Scheme.Modules.restrictOpenTrivialization_comp]
  rfl

/-- Every noninitial Cech face is ordinary restriction in the chosen twist
coordinates. -/
theorem coordinateHyperplaneTwistBaseCechFactorIsoUnit_naturality_delete_of_ne_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ 0) (j : σ) (d : ℤ) :
    (Scheme.Modules.baseModulePresheaf
        (homogeneousProjπ (R := R) (σ := σ))
        (coordinateHyperplaneTwist (R := R) j d)).map
          (coordinateOpenCechDelete (R := R) a k).op ≫
      (coordinateHyperplaneTwistBaseCechFactorIsoUnit
        (R := R) a.1 j d).hom =
    (coordinateHyperplaneTwistBaseCechFactorIsoUnit
        (R := R) (a.delete k).1 j d).hom ≫
      (Scheme.Modules.baseModulePresheaf
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
          (coordinateOpenCechDelete (R := R) a k).op := by
  let M := coordinateHyperplaneTwist (R := R) j d
  let U := coordinateOpenCechIntersection (R := R) (a.delete k).1
  let V := coordinateOpenCechIntersection (R := R) a.1
  let hVU := coordinateOpenCechDelete_le (R := R) a k
  let eU := Scheme.Modules.overTrivializationOfRestrictIso M U
    (coordinateHyperplaneTwistCechTrivialization (R := R) (a.delete k).1 j d)
  have hframe :=
    coordinateHyperplaneTwistCechTrivialization_restrict_delete_of_ne_zero
      (R := R) a k hk j d
  have hover :
      Scheme.Modules.overTrivializationOfRestrictIso M V
          (coordinateHyperplaneTwistCechTrivialization (R := R) a.1 j d) =
        ModularCurves.SheafOfModules.restrictOverTrivialization
          (Proj (homogeneousSubmodule σ R)).ringCatSheaf M U eU
            (Over.mk (homOfLE hVU)) := by
    rw [← hframe]
    exact Scheme.Modules.overTrivializationOfRestrictOpenTrivialization hVU _
  change (Scheme.Modules.baseModulePresheaf
      (homogeneousProjπ (R := R) (σ := σ)) M).map (homOfLE hVU).op ≫
    (baseModulePresheafObjIsoUnitOfOverIso
      (homogeneousProjπ (R := R) (σ := σ)) M V _).hom =
    (baseModulePresheafObjIsoUnitOfOverIso
      (homogeneousProjπ (R := R) (σ := σ)) M U eU).hom ≫
      (Scheme.Modules.baseModulePresheaf
        (homogeneousProjπ (R := R) (σ := σ))
          (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
            (homOfLE hVU).op
  rw [hover]
  exact baseModulePresheafObjIsoUnitOfOverIso_naturality
    (homogeneousProjπ (R := R) (σ := σ)) M hVU eU

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
