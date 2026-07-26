/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafAwayCoordinate
import ModularCurves.EllipticCurve.PoleSheafCartierTrivialization

/-!
# Pole-coordinate transitions on Cartier/away overlaps

The pole coordinates induced by a Cartier generator are compared with the
canonical coordinates away from the marked section. The transition for
`O(n[z])` is the `n`th power of the restricted Cartier generator.
-/

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace ModularCurves

noncomputable section

local instance cartierAwayOverlapIsMulCommutative
    (X : Scheme.{u}) : ∀ V, IsMulCommutative (X.ringCatSheaf.obj.obj V) :=
  fun V ↦ by
    change IsMulCommutative (X.presheaf.obj V)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

private theorem dualUnitSectionsEquiv_over_comp_eq_overTrivializationCoefficient
    {X : Scheme.{u}} (M : X.Modules)
    (f : Scheme.Modules.unitObj X ⟶ M) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U
        (f.over U ≫ e.hom) =
      overTrivializationCoefficient M U e
        (f.val.app (.op (⊤ : X.Opens))
          (show X.presheaf.obj (.op (⊤ : X.Opens)) from 1)) := by
  rw [SheafOfModules.dualUnitSectionsEquiv_apply]
  unfold overTrivializationCoefficient
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  have hnat := PresheafOfModules.naturality_apply f.val
    (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op
    (show X.presheaf.obj (.op (⊤ : X.Opens)) from 1)
  have hone :
      (Scheme.Modules.unitObj X).val.map
          (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op
          (show X.presheaf.obj (.op (⊤ : X.Opens)) from 1) =
        (show X.presheaf.obj (.op U) from 1) := by
    change X.presheaf.map (homOfLE le_top).op 1 = 1
    exact map_one _
  rw [hone] at hnat
  change f.val.app (.op U)
      (show X.presheaf.obj (.op U) from 1) =
    M.presheaf.map (homOfLE le_top).op
      (f.val.app (.op ⊤)
        (show X.presheaf.obj (.op ⊤) from 1)) at hnat
  exact congrArg
    (fun x ↦ e.hom.val.app (.op (Over.mk (𝟙 U))) x) hnat

private theorem dualUnitSectionsEquiv_overUnitScalarEnd
    {X : Scheme.{u}} (U : X.Opens) (r : Γ(X, U)) :
    SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U
        (SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) = r := by
  rw [SheafOfModules.dualUnitSectionsEquiv_apply]
  erw [SheafOfModules.overUnitScalarEnd_app_apply]
  change (1 : Γ(X, U)) * X.presheaf.map (𝟙 (.op U)) r = r
  rw [X.presheaf.map_id]
  simp

private theorem overTrivializationCoefficient_unitHom_apply_one_eq_of_comp_eq_scalar
    {X : Scheme.{u}} (M : X.Modules)
    (f : Scheme.Modules.unitObj X ⟶ M) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U))
    (h : f.over U ≫ e.hom =
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) :
    overTrivializationCoefficient M U e
        (f.val.app (.op (⊤ : X.Opens))
          (show X.presheaf.obj (.op (⊤ : X.Opens)) from 1)) = r := by
  have hEval :=
    dualUnitSectionsEquiv_over_comp_eq_overTrivializationCoefficient
      M f U e
  have hMapEval := congrArg
    (SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U) h
  have hScalar :=
    dualUnitSectionsEquiv_overUnitScalarEnd (X := X) U r
  exact hEval.symm.trans (hMapEval.trans hScalar)

private theorem overTrivialization_hom_eq_comp_scalar_of_unit_coefficients
    {X : Scheme.{u}} (M : X.Modules)
    (f : Scheme.Modules.unitObj X ⟶ M) (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U))
    (he : overTrivializationCoefficient M U e
        (f.val.app (.op (⊤ : X.Opens))
          (show X.presheaf.obj (.op (⊤ : X.Opens)) from 1)) = r)
    (hg : overTrivializationCoefficient M U g
        (f.val.app (.op (⊤ : X.Opens))
          (show X.presheaf.obj (.op (⊤ : X.Opens)) from 1)) = 1) :
    e.hom = g.hom ≫
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r := by
  have heMap : f.over U ≫ e.hom =
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r := by
    apply (SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U).injective
    exact
      (dualUnitSectionsEquiv_over_comp_eq_overTrivializationCoefficient
        M f U e).trans
        (he.trans
          (dualUnitSectionsEquiv_overUnitScalarEnd (X := X) U r).symm)
  have hgMap : f.over U ≫ g.hom =
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U 1 := by
    apply (SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U).injective
    exact
      (dualUnitSectionsEquiv_over_comp_eq_overTrivializationCoefficient
        M f U g).trans
        (hg.trans
          (dualUnitSectionsEquiv_overUnitScalarEnd (X := X) U 1).symm)
  have hgMapId : f.over U ≫ g.hom = 𝟙 _ :=
    hgMap.trans
      (map_one (SheafOfModules.overUnitScalarEndRingHom X.ringCatSheaf U))
  have hf : f.over U = g.inv := by
    apply (cancel_mono g.hom).1
    exact hgMapId.trans g.inv_hom_id.symm
  have hInv : g.inv ≫ e.hom =
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r := by
    rw [← hf]
    exact heMap
  rw [← hInv, ← Category.assoc, g.hom_inv_id, Category.id_comp]

private theorem sectionPoleUnitHom_over_comp_cartierTrivialization
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) :
    ((sectionPoleUnitHom π z hz).over U.1) ≫
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheaf π z hz) U.1
          (sectionPoleSheafTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd)).hom =
      SheafOfModules.overUnitScalarEnd C.ringCatSheaf U.1 r := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  let eGen := localIdealGeneratorIso z U r hr hspan hnzd
  let eIdeal := Scheme.Modules.overTrivializationOfRestrictIso
    (sectionIdealModule π z hz) U.1 eGen.symm
  let ePoleOver := SheafOfModules.dualOverIsoOfIso C.ringCatSheaf
    (sectionIdealModule π z hz) U.1 eIdeal
  have he :
      Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheaf π z hz) U.1
          (sectionPoleSheafTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd) =
        ePoleOver := by
    change Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheaf π z hz) U.1
        (restrictTrivializationOfOverIso
          (sectionPoleSheaf π z hz) U.1 ePoleOver) = ePoleOver
    exact overTrivializationOfRestrictTrivializationOfOverIso
      (sectionPoleSheaf π z hz) U.1 ePoleOver
  rw [he]
  exact sectionPoleUnitHom_over_comp_dualGeneratorTrivialization
    z hz U r hr hspan hnzd

private theorem sectionPoleUnitHom_over_comp_awayTrivialization
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (V : C.Opens) (hV : z ⁻¹ᵁ V = ⊥) :
    ((sectionPoleUnitHom π z hz).over V) ≫
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheaf π z hz) V
          (sectionPoleSheafTrivializationOfSectionPreimageEqBot
            z hz V hV)).hom =
      SheafOfModules.overUnitScalarEnd C.ringCatSheaf V 1 := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  let hIso : IsIso (restrictIdealModuleToUnit z V.ι) :=
    restrictIdealModuleToUnit_isIso_of_preimage_eq_bot z V hV
  let eRestrict := @asIso _ _ _ _ (restrictIdealModuleToUnit z V.ι) hIso
  let eIdeal := Scheme.Modules.overTrivializationOfRestrictIso
    (sectionIdealModule π z hz) V eRestrict
  let ePoleOver := SheafOfModules.dualOverIsoOfIso C.ringCatSheaf
    (sectionIdealModule π z hz) V eIdeal
  have he :
      Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheaf π z hz) V
          (sectionPoleSheafTrivializationOfSectionPreimageEqBot
            z hz V hV) =
        ePoleOver := by
    change Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheaf π z hz) V
        (restrictTrivializationOfOverIso
          (sectionPoleSheaf π z hz) V ePoleOver) = ePoleOver
    exact overTrivializationOfRestrictTrivializationOfOverIso
      (sectionPoleSheaf π z hz) V ePoleOver
  rw [he]
  exact sectionPoleUnitHom_over_comp_trivializationOfSectionPreimageEqBot
    z hz V hV

private theorem overTrivializationCoefficient_restrictOpenTrivialization
    {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme)
    (m : Γ(M, (⊤ : X.Opens))) :
    overTrivializationCoefficient M V
        (Scheme.Modules.overTrivializationOfRestrictIso M V
          (Scheme.Modules.restrictOpenTrivialization hVU e)) m =
      X.presheaf.map (homOfLE hVU).op
        (overTrivializationCoefficient M U
          (Scheme.Modules.overTrivializationOfRestrictIso M U e) m) := by
  rw [Scheme.Modules.overTrivializationOfRestrictOpenTrivialization]
  exact overTrivializationCoefficient_restrict M hVU
    (Scheme.Modules.overTrivializationOfRestrictIso M U e) m

private theorem sectionPoleSheaf_cartier_subopen_unit_coefficient
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (W : C.Opens) (hWU : W ≤ U.1) :
    overTrivializationCoefficient (sectionPoleSheaf π z hz) W
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheaf π z hz) W
          (Scheme.Modules.restrictOpenTrivialization hWU
            (sectionPoleSheafTrivializationOfCartierGenerator
              z hz U r hr hspan hnzd)))
        ((sectionPoleUnitHom π z hz).val.app (.op (⊤ : C.Opens))
          (show C.presheaf.obj (.op (⊤ : C.Opens)) from 1)) =
      C.presheaf.map (homOfLE hWU).op r := by
  let m :=
    (sectionPoleUnitHom π z hz).val.app (.op (⊤ : C.Opens))
      (show C.presheaf.obj (.op (⊤ : C.Opens)) from 1)
  have hres := overTrivializationCoefficient_restrictOpenTrivialization
    (sectionPoleSheaf π z hz) hWU
    (sectionPoleSheafTrivializationOfCartierGenerator
      z hz U r hr hspan hnzd) m
  have hU :=
    overTrivializationCoefficient_unitHom_apply_one_eq_of_comp_eq_scalar
      (sectionPoleSheaf π z hz) (sectionPoleUnitHom π z hz) U.1
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheaf π z hz) U.1
          (sectionPoleSheafTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd))
        r (sectionPoleUnitHom_over_comp_cartierTrivialization
          z hz U r hr hspan hnzd)
  exact hres.trans
    (congrArg (C.presheaf.map (homOfLE hWU).op) hU)

private theorem sectionPoleSheaf_away_subopen_unit_coefficient
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (V : C.Opens) (hV : z ⁻¹ᵁ V = ⊥)
    (W : C.Opens) (hWV : W ≤ V) :
    overTrivializationCoefficient (sectionPoleSheaf π z hz) W
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheaf π z hz) W
          (Scheme.Modules.restrictOpenTrivialization hWV
            (sectionPoleSheafTrivializationOfSectionPreimageEqBot
              z hz V hV)))
        ((sectionPoleUnitHom π z hz).val.app (.op (⊤ : C.Opens))
          (show C.presheaf.obj (.op (⊤ : C.Opens)) from 1)) = 1 := by
  let m :=
    (sectionPoleUnitHom π z hz).val.app (.op (⊤ : C.Opens))
      (show C.presheaf.obj (.op (⊤ : C.Opens)) from 1)
  have hres := overTrivializationCoefficient_restrictOpenTrivialization
    (sectionPoleSheaf π z hz) hWV
    (sectionPoleSheafTrivializationOfSectionPreimageEqBot z hz V hV) m
  have hVcoeff :=
    overTrivializationCoefficient_unitHom_apply_one_eq_of_comp_eq_scalar
      (sectionPoleSheaf π z hz) (sectionPoleUnitHom π z hz) V
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheaf π z hz) V
          (sectionPoleSheafTrivializationOfSectionPreimageEqBot z hz V hV))
        1 (sectionPoleUnitHom_over_comp_awayTrivialization z hz V hV)
  exact hres.trans
    ((congrArg (C.presheaf.map (homOfLE hWV).op) hVcoeff).trans (map_one _))

private theorem sectionPoleSheaf_cartier_away_subopen_transition
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (V : C.Opens) (hV : z ⁻¹ᵁ V = ⊥)
    (W : C.Opens) (hWU : W ≤ U.1) (hWV : W ≤ V) :
    (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheaf π z hz) W
        (Scheme.Modules.restrictOpenTrivialization hWU
          (sectionPoleSheafTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd))).hom =
      (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheaf π z hz) W
          (Scheme.Modules.restrictOpenTrivialization hWV
            (sectionPoleSheafTrivializationOfSectionPreimageEqBot
              z hz V hV))).hom ≫
        SheafOfModules.overUnitScalarEnd C.ringCatSheaf W
          (C.presheaf.map (homOfLE hWU).op r) := by
  exact overTrivialization_hom_eq_comp_scalar_of_unit_coefficients
    (sectionPoleSheaf π z hz) (sectionPoleUnitHom π z hz) W
    (Scheme.Modules.overTrivializationOfRestrictIso
      (sectionPoleSheaf π z hz) W
      (Scheme.Modules.restrictOpenTrivialization hWU
        (sectionPoleSheafTrivializationOfCartierGenerator
          z hz U r hr hspan hnzd)))
    (Scheme.Modules.overTrivializationOfRestrictIso
      (sectionPoleSheaf π z hz) W
      (Scheme.Modules.restrictOpenTrivialization hWV
        (sectionPoleSheafTrivializationOfSectionPreimageEqBot z hz V hV)))
    (C.presheaf.map (homOfLE hWU).op r)
    (sectionPoleSheaf_cartier_subopen_unit_coefficient
      z hz U r hr hspan hnzd W hWU)
    (sectionPoleSheaf_away_subopen_unit_coefficient z hz V hV W hWV)

/-- On a Cartier/away overlap, the simple-pole frames differ by the
restricted Cartier generator. -/
theorem sectionPoleSheaf_cartier_away_overlap_transition
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (V : C.Opens) (hV : z ⁻¹ᵁ V = ⊥) :
    let W := U.1 ⊓ V
    let eCartier :=
      Scheme.Modules.restrictOpenTrivialization
        (inf_le_left : W ≤ U.1)
        (sectionPoleSheafTrivializationOfCartierGenerator
          z hz U r hr hspan hnzd)
    let eAway :=
      Scheme.Modules.restrictOpenTrivialization
        (inf_le_right : W ≤ V)
        (sectionPoleSheafTrivializationOfSectionPreimageEqBot z hz V hV)
    let rW := C.presheaf.map (homOfLE (inf_le_left : W ≤ U.1)).op r
    (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheaf π z hz) W eCartier).hom =
      (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheaf π z hz) W eAway).hom ≫
        SheafOfModules.overUnitScalarEnd C.ringCatSheaf W rW := by
  exact sectionPoleSheaf_cartier_away_subopen_transition
    z hz U r hr hspan hnzd V hV (U.1 ⊓ V) inf_le_left inf_le_right

private theorem sectionPoleSheafPower_cartier_away_subopen_transition
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (V : C.Opens) (hV : z ⁻¹ᵁ V = ⊥)
    (W : C.Opens) (hWU : W ≤ U.1) (hWV : W ≤ V) (n : ℕ) :
    (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheafPower π z hz n) W
        (Scheme.Modules.restrictOpenTrivialization hWU
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd n))).hom =
      (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheafPower π z hz n) W
          (Scheme.Modules.restrictOpenTrivialization hWV
            (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
              z hz V hV n))).hom ≫
        SheafOfModules.overUnitScalarEnd C.ringCatSheaf W
          (C.presheaf.map (homOfLE hWU).op r ^ n) := by
  let eCartier :=
    Scheme.Modules.restrictOpenTrivialization hWU
      (sectionPoleSheafTrivializationOfCartierGenerator
        z hz U r hr hspan hnzd)
  let eAway :=
    Scheme.Modules.restrictOpenTrivialization hWV
      (sectionPoleSheafTrivializationOfSectionPreimageEqBot z hz V hV)
  let rW := C.presheaf.map (homOfLE hWU).op r
  have hOver := sectionPoleSheaf_cartier_away_subopen_transition
    z hz U r hr hspan hnzd V hV W hWU hWV
  have hOpen :=
    restrictTrivializationOfOverIso_hom_eq_comp_scalar
      (sectionPoleSheaf π z hz) W
      (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheaf π z hz) W eCartier)
      (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheaf π z hz) W eAway)
      rW hOver
  have heCartier :=
    restrictTrivializationOfOverTrivializationOfRestrictIso
      (sectionPoleSheaf π z hz) W eCartier
  have heAway :=
    restrictTrivializationOfOverTrivializationOfRestrictIso
      (sectionPoleSheaf π z hz) W eAway
  rw [heCartier, heAway] at hOpen
  have hPower := sectionPoleSheafPowerTrivialization_hom_eq_comp_scalar
    z hz W eCartier eAway
      (Scheme.Modules.openTopSection W rW) hOpen n
  have heCartierPower :=
    sectionPoleSheafPowerTrivialization_restrictOpen
      z hz hWU
        (sectionPoleSheafTrivializationOfCartierGenerator
          z hz U r hr hspan hnzd) n
  have heAwayPower :=
    sectionPoleSheafPowerTrivialization_restrictOpen
      z hz hWV
        (sectionPoleSheafTrivializationOfSectionPreimageEqBot z hz V hV) n
  have heCartierPower' :
      Scheme.Modules.restrictOpenTrivialization hWU
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd n) =
        sectionPoleSheafPowerTrivialization z hz W eCartier n := by
    simpa only [eCartier,
      sectionPoleSheafPowerTrivializationOfCartierGenerator] using
      heCartierPower
  have heAwayPower' :
      Scheme.Modules.restrictOpenTrivialization hWV
          (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
            z hz V hV n) =
        sectionPoleSheafPowerTrivialization z hz W eAway n := by
    simpa only [eAway,
      sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot] using
      heAwayPower
  have hPower' :
      (Scheme.Modules.restrictOpenTrivialization hWU
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd n)).hom =
        (Scheme.Modules.restrictOpenTrivialization hWV
            (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
              z hz V hV n)).hom ≫
          unitEndomorphismOfTopSection
            (Scheme.Modules.openTopSection W (rW ^ n)) := by
    rw [heCartierPower', heAwayPower']
    convert hPower using 1
    unfold Scheme.Modules.openTopSection
    simp only [map_pow]
  exact overTrivializationOfRestrictIso_hom_eq_comp_scalar
    (sectionPoleSheafPower π z hz n) W
    (Scheme.Modules.restrictOpenTrivialization hWU
      (sectionPoleSheafPowerTrivializationOfCartierGenerator
        z hz U r hr hspan hnzd n))
    (Scheme.Modules.restrictOpenTrivialization hWV
      (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
        z hz V hV n))
    (rW ^ n) hPower'

/-- On a Cartier/away overlap, coefficients of a pole-power section differ by
the corresponding power of the restricted Cartier generator. -/
theorem sectionPoleSheafPower_cartier_away_overlap_coefficient
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (V : C.Opens) (hV : z ⁻¹ᵁ V = ⊥)
    (n : ℕ)
    (m : Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens))) :
    let W := U.1 ⊓ V
    let eCartier :=
      Scheme.Modules.restrictOpenTrivialization
        (inf_le_left : W ≤ U.1)
        (sectionPoleSheafPowerTrivializationOfCartierGenerator
          z hz U r hr hspan hnzd n)
    let eAway :=
      Scheme.Modules.restrictOpenTrivialization
        (inf_le_right : W ≤ V)
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz V hV n)
    let rW := C.presheaf.map (homOfLE (inf_le_left : W ≤ U.1)).op r
    overTrivializationCoefficient
        (sectionPoleSheafPower π z hz n) W
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheafPower π z hz n) W eCartier) m =
      overTrivializationCoefficient
          (sectionPoleSheafPower π z hz n) W
          (Scheme.Modules.overTrivializationOfRestrictIso
            (sectionPoleSheafPower π z hz n) W eAway) m *
        rW ^ n := by
  dsimp only
  exact overTrivializationCoefficient_eq_mul_of_transition
    (sectionPoleSheafPower π z hz n) (U.1 ⊓ V)
    (Scheme.Modules.overTrivializationOfRestrictIso
      (sectionPoleSheafPower π z hz n) (U.1 ⊓ V)
      (Scheme.Modules.restrictOpenTrivialization inf_le_left
        (sectionPoleSheafPowerTrivializationOfCartierGenerator
          z hz U r hr hspan hnzd n)))
    (Scheme.Modules.overTrivializationOfRestrictIso
      (sectionPoleSheafPower π z hz n) (U.1 ⊓ V)
      (Scheme.Modules.restrictOpenTrivialization inf_le_right
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz V hV n)))
    (C.presheaf.map (homOfLE inf_le_left).op r ^ n)
    (sectionPoleSheafPower_cartier_away_subopen_transition
      z hz U r hr hspan hnzd V hV (U.1 ⊓ V)
        inf_le_left inf_le_right n)
    m

end

end ModularCurves
