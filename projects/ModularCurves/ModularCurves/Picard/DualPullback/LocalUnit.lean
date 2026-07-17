import ModularCurves.Picard.DualPullback.LocalSection

/-!
# The local pullback unit on the canonical section

The local structure-module comparison and its inverse both preserve the canonical section
`1`.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite



namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

theorem localPullbackUnitIso_hom_pulled_oneT
    (f : Y ⟶ X) (U : X.Opens) :
    let W := U.ι ⁻¹ᵁ U
    let g := f ∣_ U
    let VY := f ⁻¹ᵁ U
    let ZY := VY.ι ⁻¹ᵁ VY
    let hpre : ZY = g ⁻¹ᵁ W := by
      change (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
        (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U)
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
      exact congrArg (fun q : VY.toScheme ⟶ X ↦ q ⁻¹ᵁ U)
        (morphismRestrict_ι f U).symm
    let QY := VY.overEquivalence.symm.functor.obj ZY
    let kY : QY ⟶ Over.mk (𝟙 VY) := Over.mkIdTerminal.from QY
    (localPullbackUnitIso f U).hom.val.app (.op ZY)
        (((pullback g).obj (unitObj U.toScheme)).presheaf.map
          (eqToHom hpre).op
            (((pullbackPushforwardAdjunction g).unit.app
              (unitObj U.toScheme)).val.app (.op W)
                (show U.toScheme.presheaf.obj (.op W) from 1))) =
      (_root_.SheafOfModules.unit (Y.ringCatSheaf.over VY)).val.map
        kY.op
          (show (Y.ringCatSheaf.over VY).obj.obj
            (.op (Over.mk (𝟙 VY))) from 1) := by
  dsimp only
  let W := U.ι ⁻¹ᵁ U
  let g := f ∣_ U
  let VY := f ⁻¹ᵁ U
  let ZY := VY.ι ⁻¹ᵁ VY
  let hpre : ZY = g ⁻¹ᵁ W := by
    change (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
      (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
    exact congrArg (fun q : VY.toScheme ⟶ X ↦ q ⁻¹ᵁ U)
      (morphismRestrict_ι f U).symm
  let QY := VY.overEquivalence.symm.functor.obj ZY
  let kY : QY ⟶ Over.mk (𝟙 VY) := Over.mkIdTerminal.from QY
  let s := ((pullback g).obj (unitObj U.toScheme)).presheaf.map
    (eqToHom hpre).op
      (((pullbackPushforwardAdjunction g).unit.app
        (unitObj U.toScheme)).val.app (.op W)
          (show U.toScheme.presheaf.obj (.op W) from 1))
  have hlocal := congrArg (fun q ↦ q.val.app (.op ZY) s)
    (localPullbackUnitIso_hom_eqP f U)
  change (localPullbackUnitIso f U).hom.val.app (.op ZY) s = _
  calc
    _ = (pullbackUnitIso g).hom.val.app (.op ZY) s := hlocal
    _ = _ := by
      let htop : ZY = g ⁻¹ᵁ (⊤ : U.toScheme.Opens) :=
        hpre.trans (congrArg (fun T ↦ g ⁻¹ᵁ T) U.ι_preimage_self)
      have hs := pullbackUnit_one_transport_topT g W ZY
        U.ι_preimage_self hpre
      change s = ((pullback g).obj (unitObj U.toScheme)).presheaf.map
        (eqToHom htop).op
          (((pullbackPushforwardAdjunction g).unit.app
            (unitObj U.toScheme)).val.app (.op ⊤)
              (show U.toScheme.presheaf.obj (.op ⊤) from 1)) at hs
      have hnat := PresheafOfModules.naturality_apply
        (pullbackUnitIso g).hom.val (eqToHom htop).op
          (((pullbackPushforwardAdjunction g).unit.app
            (unitObj U.toScheme)).val.app (.op ⊤)
              (show U.toScheme.presheaf.obj (.op ⊤) from 1))
      have hone := pullbackUnitIso_hom_unit_oneT g
      rw [hs]
      have htransport :
          (pullbackUnitIso g).hom.val.app (.op ZY)
              (((pullback g).obj (unitObj U.toScheme)).presheaf.map
                (eqToHom htop).op
                  (((pullbackPushforwardAdjunction g).unit.app
                    (unitObj U.toScheme)).val.app (.op ⊤)
                      (show U.toScheme.presheaf.obj (.op ⊤) from 1))) =
            (unitObj VY.toScheme).presheaf.map (eqToHom htop).op
              ((pullbackUnitIso g).hom.val.app
                (.op (g ⁻¹ᵁ (⊤ : U.toScheme.Opens)))
                  (((pullbackPushforwardAdjunction g).unit.app
                    (unitObj U.toScheme)).val.app (.op ⊤)
                      (show U.toScheme.presheaf.obj (.op ⊤) from 1))) := hnat
      have honeTransport :
          (unitObj VY.toScheme).presheaf.map (eqToHom htop).op
              ((pullbackUnitIso g).hom.val.app
                (.op (g ⁻¹ᵁ (⊤ : U.toScheme.Opens)))
                  (((pullbackPushforwardAdjunction g).unit.app
                    (unitObj U.toScheme)).val.app (.op ⊤)
                      (show U.toScheme.presheaf.obj (.op ⊤) from 1))) =
            (unitObj VY.toScheme).presheaf.map (eqToHom htop).op
              (show VY.toScheme.presheaf.obj
                (.op (g ⁻¹ᵁ (⊤ : U.toScheme.Opens))) from 1) :=
        congrArg (fun z ↦ (unitObj VY.toScheme).presheaf.map
          (eqToHom htop).op z) hone
      let oneV : (unitObj VY.toScheme).presheaf.obj (.op ZY) :=
        show VY.toScheme.presheaf.obj (.op ZY) from 1
      have hrestrict :
          (unitObj VY.toScheme).presheaf.map (eqToHom htop).op
              (show VY.toScheme.presheaf.obj
                (.op (g ⁻¹ᵁ (⊤ : U.toScheme.Opens))) from 1) =
            oneV :=
        PresheafOfModules.unit_map_one
          VY.toScheme.ringCatSheaf.obj (eqToHom htop).op
      have hterminal :
          (_root_.SheafOfModules.unit
              (Y.ringCatSheaf.over VY)).val.map kY.op
                (show (Y.ringCatSheaf.over VY).obj.obj
                  (.op (Over.mk (𝟙 VY))) from 1) =
            oneV :=
        PresheafOfModules.unit_map_one
          (Y.ringCatSheaf.over VY).obj kY.op
      exact Eq.trans htransport
        (Eq.trans honeTransport (Eq.trans hrestrict hterminal.symm))

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite



namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

theorem localPullbackModuleIso_inv_pulledSectionT (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens) (x : M.val.obj (.op U)) :
    let W := U.ι ⁻¹ᵁ U
    let g := f ∣_ U
    let VY := f ⁻¹ᵁ U
    let ZY := VY.ι ⁻¹ᵁ VY
    let hpre : ZY = g ⁻¹ᵁ W := by
      change (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
        (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U)
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
      exact congrArg (fun q : VY.toScheme ⟶ X ↦ q ⁻¹ᵁ U)
        (morphismRestrict_ι f U).symm
    let A := (overEquiv U).functor.obj (M.over U)
    let a := ((pullbackPushforwardAdjunction g).unit.app A).val.app
      (.op W) (localModuleSection M U W x)
    let s := ((pullback g).obj A).presheaf.map (eqToHom hpre).op a
    let xg := ((pullbackPushforwardAdjunction f).unit.app M).val.app
      (.op U) x
    (localPullbackModuleIso f M U).inv.val.app (.op ZY)
        (localModuleSection ((pullback f).obj M) VY ZY xg) = s := by
  dsimp only
  let W := U.ι ⁻¹ᵁ U
  let g := f ∣_ U
  let VY := f ⁻¹ᵁ U
  let ZY := VY.ι ⁻¹ᵁ VY
  let hpre : ZY = g ⁻¹ᵁ W := by
    change (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
      (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
    exact congrArg (fun q : VY.toScheme ⟶ X ↦ q ⁻¹ᵁ U)
      (morphismRestrict_ι f U).symm
  let A := (overEquiv U).functor.obj (M.over U)
  let a := ((pullbackPushforwardAdjunction g).unit.app A).val.app
    (.op W) (localModuleSection M U W x)
  let s := ((pullback g).obj A).presheaf.map (eqToHom hpre).op a
  let xg := ((pullbackPushforwardAdjunction f).unit.app M).val.app
    (.op U) x
  have hmodule := localPullbackModuleIso_pulledSectionT f M U x
  change (localPullbackModuleIso f M U).hom.val.app (.op ZY) s =
    localModuleSection ((pullback f).obj M) VY ZY xg at hmodule
  rw [← hmodule]
  have hcomp := congrArg (fun q ↦ q.val.app (.op ZY))
    (localPullbackModuleIso f M U).hom_inv_id
  have h := ConcreteCategory.congr_hom hcomp s
  erw [sheafOfModules_comp_app_apply] at h
  exact h

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite



namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

theorem localOverUnit_pulled_one_eqT (f : Y ⟶ X) (U : X.Opens) :
    let W := U.ι ⁻¹ᵁ U
    let g := f ∣_ U
    let VY := f ⁻¹ᵁ U
    let ZY := VY.ι ⁻¹ᵁ VY
    let hpre : ZY = g ⁻¹ᵁ W := by
      change (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
        (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U)
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
      exact congrArg (fun q : VY.toScheme ⟶ X ↦ q ⁻¹ᵁ U)
        (morphismRestrict_ι f U).symm
    let QX := U.overEquivalence.symm.functor.obj W
    let kX : QX ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from QX
    let O := (overEquiv U).functor.obj
      (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    let r := (_root_.SheafOfModules.unit
      (X.ringCatSheaf.over U)).val.map kX.op
        (show (X.ringCatSheaf.over U).obj.obj
          (.op (Over.mk (𝟙 U))) from 1)
    ((pullback g).obj O).presheaf.map (eqToHom hpre).op
        (((pullbackPushforwardAdjunction g).unit.app O).val.app (.op W) r) =
      ((pullback g).obj (unitObj U.toScheme)).presheaf.map
        (eqToHom hpre).op
          (((pullbackPushforwardAdjunction g).unit.app
            (unitObj U.toScheme)).val.app (.op W)
              (show U.toScheme.presheaf.obj (.op W) from 1)) := by
  dsimp only
  let W := U.ι ⁻¹ᵁ U
  let QX := U.overEquivalence.symm.functor.obj W
  let kX : QX ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from QX
  have hr := PresheafOfModules.unit_map_one
    (X.ringCatSheaf.over U).obj kX.op
  change (_root_.SheafOfModules.unit
      (X.ringCatSheaf.over U)).val.map kX.op
        (show (X.ringCatSheaf.over U).obj.obj
          (.op (Over.mk (𝟙 U))) from 1) =
    (show U.toScheme.presheaf.obj (.op W) from 1) at hr
  rw [hr]
  let g := f ∣_ U
  let VY := f ⁻¹ᵁ U
  let ZY := VY.ι ⁻¹ᵁ VY
  let hpre : ZY = g ⁻¹ᵁ W := by
    change (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
      (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
    exact congrArg (fun q : VY.toScheme ⟶ X ↦ q ⁻¹ᵁ U)
      (morphismRestrict_ι f U).symm
  let z := ((pullback g).obj (unitObj U.toScheme)).presheaf.map
    (eqToHom hpre).op
      (((pullbackPushforwardAdjunction g).unit.app
        (unitObj U.toScheme)).val.app (.op W)
          (show U.toScheme.presheaf.obj (.op W) from 1))
  change z = z
  rfl

end AlgebraicGeometry.Scheme.Modules
