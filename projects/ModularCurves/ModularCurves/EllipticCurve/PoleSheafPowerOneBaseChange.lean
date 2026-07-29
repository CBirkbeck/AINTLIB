/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafPowerOneSection
import ModularCurves.EllipticCurve.PoleSheafFiltrationBaseChange
import ModularCurves.ForMathlib.AffineModuleBaseChange

/-!
# Base change for the constant first-pole section

The literal constant section of the first pole module is preserved by
arbitrary base change.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory TopologicalSpace

universe u

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

namespace ModularCurves

private theorem affinePullbackUnitTop_map
    {X Y : Scheme.{u}} (g : Y ⟶ X) {M N : X.Modules}
    (q : M ⟶ N) (m : Γ(M, (⊤ : X.Opens))) :
    ((Scheme.Modules.pullback g).map q).val.app (.op ⊤)
        (Scheme.Modules.affinePullbackUnitTop g M m) =
      Scheme.Modules.affinePullbackUnitTop g N
        (q.val.app (.op ⊤) m) := by
  let htop : (⊤ : Y.Opens) = g ⁻¹ᵁ (⊤ : X.Opens) := by simp
  exact Scheme.Modules.pullbackUnit_map_transportT
    g q (⊤ : X.Opens) (⊤ : Y.Opens) htop m

private theorem pullbackUnitIso_hom_affinePullbackUnitTop_one
    {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (Scheme.Modules.pullbackUnitIso g).hom.val.app (.op ⊤)
        (Scheme.Modules.affinePullbackUnitTop g
          (Scheme.Modules.unitObj X)
          (show X.presheaf.obj (.op ⊤) from 1)) =
      (show Y.presheaf.obj (.op ⊤) from 1) := by
  let htop : (⊤ : Y.Opens) = g ⁻¹ᵁ (⊤ : X.Opens) := by simp
  let pulledOne :=
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
      (Scheme.Modules.unitObj X)).val.app (.op ⊤)
        (show X.presheaf.obj (.op ⊤) from 1))
  let oneYPre : Γ(Scheme.Modules.unitObj Y,
      g ⁻¹ᵁ (⊤ : X.Opens)) :=
    show Y.presheaf.obj (.op (g ⁻¹ᵁ (⊤ : X.Opens))) from 1
  let oneY : Γ(Scheme.Modules.unitObj Y, (⊤ : Y.Opens)) :=
    show Y.presheaf.obj (.op ⊤) from 1
  have hnat := PresheafOfModules.naturality_apply
    (Scheme.Modules.pullbackUnitIso g).hom.val (eqToHom htop).op pulledOne
  have hone := Scheme.Modules.pullbackUnitIso_hom_unit_oneT g
  change
    (Scheme.Modules.pullbackUnitIso g).hom.val.app (.op ⊤)
        (((Scheme.Modules.pullback g).obj
          (Scheme.Modules.unitObj X)).presheaf.map
            (eqToHom htop).op pulledOne) = oneY
  change (Scheme.Modules.pullbackUnitIso g).hom.val.app
      (.op (g ⁻¹ᵁ (⊤ : X.Opens))) pulledOne = oneYPre at hone
  have htransport :
      (Scheme.Modules.pullbackUnitIso g).hom.val.app (.op ⊤)
          (((Scheme.Modules.pullback g).obj
            (Scheme.Modules.unitObj X)).presheaf.map
              (eqToHom htop).op pulledOne) =
        (Scheme.Modules.unitObj Y).presheaf.map (eqToHom htop).op
        ((Scheme.Modules.pullbackUnitIso g).hom.val.app
          (.op (g ⁻¹ᵁ (⊤ : X.Opens))) pulledOne) := hnat
  have honeTransport :
      (Scheme.Modules.unitObj Y).presheaf.map (eqToHom htop).op
          ((Scheme.Modules.pullbackUnitIso g).hom.val.app
            (.op (g ⁻¹ᵁ (⊤ : X.Opens))) pulledOne) =
        (Scheme.Modules.unitObj Y).presheaf.map (eqToHom htop).op
          oneYPre :=
      congrArg (fun x =>
        (Scheme.Modules.unitObj Y).presheaf.map (eqToHom htop).op x) hone
  have hrestrict :
      (Scheme.Modules.unitObj Y).presheaf.map (eqToHom htop).op
          oneYPre = oneY :=
    PresheafOfModules.unit_map_one
      Y.ringCatSheaf.obj (eqToHom htop).op
  exact htransport.trans (honeTransport.trans hrestrict)

private theorem monoidalUnitSection_baseChange
    {X Y : Scheme.{u}} (g : Y ⟶ X) :
    letI : (Scheme.Modules.pullback g).Monoidal :=
      Scheme.Modules.pullbackMonoidal g
    (Functor.OplaxMonoidal.η (Scheme.Modules.pullback g)).val.app (.op ⊤)
        (Scheme.Modules.affinePullbackUnitTop g (𝟙_ X.Modules)
          (monoidalUnitSection X)) =
      monoidalUnitSection Y := by
  dsimp only
  letI : (Scheme.Modules.pullback g).Monoidal :=
    Scheme.Modules.pullbackMonoidal g
  let pulled := Scheme.Modules.affinePullbackUnitTop g (𝟙_ X.Modules)
    (monoidalUnitSection X)
  let oneX : Γ(Scheme.Modules.unitObj X, (⊤ : X.Opens)) :=
    show X.presheaf.obj (.op ⊤) from 1
  let oneY : Γ(Scheme.Modules.unitObj Y, (⊤ : Y.Opens)) :=
    show Y.presheaf.obj (.op ⊤) from 1
  have hunit := congrArg Iso.hom
    (Scheme.Modules.pullback_monoidalUnitObjIso g)
  change Functor.OplaxMonoidal.η (Scheme.Modules.pullback g) ≫
      (monoidalUnitObjIso Y).hom =
    (Scheme.Modules.pullback g).map (monoidalUnitObjIso X).hom ≫
      (Scheme.Modules.pullbackUnitIso g).hom at hunit
  have hunitApp := congrArg (fun q => q.val.app (.op ⊤) pulled) hunit
  change (monoidalUnitObjIso Y).hom.val.app (.op ⊤)
      ((Functor.OplaxMonoidal.η
        (Scheme.Modules.pullback g)).val.app (.op ⊤) pulled) =
    (Scheme.Modules.pullbackUnitIso g).hom.val.app (.op ⊤)
      (((Scheme.Modules.pullback g).map
        (monoidalUnitObjIso X).hom).val.app (.op ⊤) pulled) at hunitApp
  have honeX : (monoidalUnitObjIso X).hom.val.app (.op ⊤)
      (monoidalUnitSection X) = oneX :=
    Scheme.Modules.iso_inv_hom_app_applyT
      (monoidalUnitObjIso X) (.op ⊤)
        (show X.presheaf.obj (.op ⊤) from 1)
  have hmap := affinePullbackUnitTop_map g (monoidalUnitObjIso X).hom
    (monoidalUnitSection X)
  have hmapImage := congrArg (fun x =>
    (Scheme.Modules.pullbackUnitIso g).hom.val.app (.op ⊤) x) hmap
  have honeImage := congrArg (fun x =>
    (Scheme.Modules.pullbackUnitIso g).hom.val.app (.op ⊤)
      (Scheme.Modules.affinePullbackUnitTop g
        (Scheme.Modules.unitObj X) x)) honeX
  have hpullOne : (Scheme.Modules.pullbackUnitIso g).hom.val.app (.op ⊤)
      (Scheme.Modules.affinePullbackUnitTop g
        (Scheme.Modules.unitObj X) oneX) = oneY :=
    pullbackUnitIso_hom_affinePullbackUnitTop_one g
  have honeY : (monoidalUnitObjIso Y).hom.val.app (.op ⊤)
      (monoidalUnitSection Y) = oneY :=
    Scheme.Modules.iso_inv_hom_app_applyT
      (monoidalUnitObjIso Y) (.op ⊤)
        (show Y.presheaf.obj (.op ⊤) from 1)
  have himage : (monoidalUnitObjIso Y).hom.val.app (.op ⊤)
      ((Functor.OplaxMonoidal.η
        (Scheme.Modules.pullback g)).val.app (.op ⊤) pulled) =
      (monoidalUnitObjIso Y).hom.val.app (.op ⊤)
        (monoidalUnitSection Y) := by
    exact hunitApp.trans (hmapImage.trans
      (honeImage.trans (hpullOne.trans honeY.symm)))
  have hback := congrArg (fun x =>
    (monoidalUnitObjIso Y).inv.val.app (.op ⊤) x) himage
  exact (Scheme.Modules.iso_hom_inv_app_applyT
      (monoidalUnitObjIso Y) (.op ⊤)
        ((Functor.OplaxMonoidal.η
          (Scheme.Modules.pullback g)).val.app (.op ⊤) pulled)).symm.trans
    (hback.trans (Scheme.Modules.iso_hom_inv_app_applyT
      (monoidalUnitObjIso Y) (.op ⊤) (monoidalUnitSection Y)))

/-- The literal constant section of the first pole module is preserved by
arbitrary base change. -/
theorem sectionPoleSheafPowerOneSection_baseChange
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    let g := pullback.fst π t
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    (sectionPoleSheafPowerBaseChangeIso hsm z hz t 1).hom.val.app (.op ⊤)
        (Scheme.Modules.affinePullbackUnitTop g
          (sectionPoleSheafPower π z hz 1)
          (show Γ(sectionPoleSheafPower π z hz 1, (⊤ : C.Opens)) from
            sectionPoleSheafPowerOneSection π z hz)) =
      (show Γ(sectionPoleSheafPower πT zT hzT 1,
          (⊤ : (pullback π t).Opens)) from
        sectionPoleSheafPowerOneSection πT zT hzT) := by
  dsimp only
  let g := pullback.fst π t
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  let e0 := sectionPoleSheafPowerBaseChangeIso hsm z hz t 0
  let e1 := sectionPoleSheafPowerBaseChangeIso hsm z hz t 1
  let q := sectionPoleSheafSuccHom π z hz 0
  let qT := sectionPoleSheafSuccHom πT zT hzT 0
  letI : IsSeparated πT := inferInstance
  letI : (Scheme.Modules.pullback g).Monoidal :=
    Scheme.Modules.pullbackMonoidal g
  have hq := sectionPoleSheafSuccHom_baseChange hsm z hz t 0
  change (Scheme.Modules.pullback g).map q ≫ e1.hom =
    e0.hom ≫ qT at hq
  have hqApp := congrArg (fun k => k.val.app (.op ⊤)
      (Scheme.Modules.affinePullbackUnitTop g (𝟙_ C.Modules)
        (monoidalUnitSection C))) hq
  change e1.hom.val.app (.op ⊤)
      (((Scheme.Modules.pullback g).map q).val.app (.op ⊤)
        (Scheme.Modules.affinePullbackUnitTop g (𝟙_ C.Modules)
          (monoidalUnitSection C))) =
    qT.val.app (.op ⊤)
      (e0.hom.val.app (.op ⊤)
        (Scheme.Modules.affinePullbackUnitTop g (𝟙_ C.Modules)
          (monoidalUnitSection C))) at hqApp
  change e1.hom.val.app (.op ⊤)
      (Scheme.Modules.affinePullbackUnitTop g
        (sectionPoleSheafPower π z hz 1)
        (q.val.app (.op ⊤) (monoidalUnitSection C))) =
    qT.val.app (.op ⊤) (monoidalUnitSection (pullback π t))
  have hmap := affinePullbackUnitTop_map g q (monoidalUnitSection C)
  have he0 : e0.hom.val.app (.op ⊤)
      (Scheme.Modules.affinePullbackUnitTop g (𝟙_ C.Modules)
        (monoidalUnitSection C)) =
      monoidalUnitSection (pullback π t) :=
    monoidalUnitSection_baseChange g
  calc
    _ = e1.hom.val.app (.op ⊤)
        (((Scheme.Modules.pullback g).map q).val.app (.op ⊤)
          (Scheme.Modules.affinePullbackUnitTop g (𝟙_ C.Modules)
            (monoidalUnitSection C))) :=
      congrArg (fun x => e1.hom.val.app (.op ⊤) x) hmap.symm
    _ = qT.val.app (.op ⊤)
        (e0.hom.val.app (.op ⊤)
          (Scheme.Modules.affinePullbackUnitTop g (𝟙_ C.Modules)
            (monoidalUnitSection C))) := hqApp
    _ = qT.val.app (.op ⊤) (monoidalUnitSection (pullback π t)) :=
      congrArg (fun x => qT.val.app (.op ⊤) x) he0

end ModularCurves
