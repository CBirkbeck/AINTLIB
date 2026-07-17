import ModularCurves.Picard.DualPullback.LocalUnit

/-!
# Local trivializations of pulled dual modules

A local trivialization of a module determines compatible trivializations of its dual and
of the pullback of that dual; the distinguished dual section maps to `1`.
-/

universe u v

open AlgebraicGeometry CategoryTheory Opposite



namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

theorem localDualMiddle_pulledSectionT (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (d : (dualObj M).over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (hd : d.hom.val.app (.op (Over.mk (𝟙 U))) e.hom =
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1)) :
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
    let N := (pullback f).obj (dualObj M)
    let xg := ((pullbackPushforwardAdjunction f).unit.app
      (dualObj M)).val.app (.op U) e.hom
    let O := (overEquiv U).functor.obj
      (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    let q := (overEquiv U).functor.map d.hom
    let r := (_root_.SheafOfModules.unit
      (X.ringCatSheaf.over U)).val.map kX.op
        (show (X.ringCatSheaf.over U).obj.obj
          (.op (Over.mk (𝟙 U))) from 1)
    let t := ((pullback g).obj O).presheaf.map (eqToHom hpre).op
      (((pullbackPushforwardAdjunction g).unit.app O).val.app (.op W) r)
    ((pullback g).map q).val.app (.op ZY)
        ((localPullbackModuleIso f (dualObj M) U).inv.val.app (.op ZY)
          (localModuleSection N VY ZY xg)) = t := by
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
  let QX := U.overEquivalence.symm.functor.obj W
  let kX : QX ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from QX
  let N := (pullback f).obj (dualObj M)
  let xg := ((pullbackPushforwardAdjunction f).unit.app
    (dualObj M)).val.app (.op U) e.hom
  let A := (overEquiv U).functor.obj ((dualObj M).over U)
  let O := (overEquiv U).functor.obj
    (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))
  let q := (overEquiv U).functor.map d.hom
  let a := ((pullbackPushforwardAdjunction g).unit.app A).val.app
    (.op W) (localModuleSection (dualObj M) U W e.hom)
  let s := ((pullback g).obj A).presheaf.map (eqToHom hpre).op a
  let r := (_root_.SheafOfModules.unit
    (X.ringCatSheaf.over U)).val.map kX.op
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1)
  let t := ((pullback g).obj O).presheaf.map (eqToHom hpre).op
    (((pullbackPushforwardAdjunction g).unit.app O).val.app (.op W) r)
  have hinv := localPullbackModuleIso_inv_pulledSectionT f
    (dualObj M) U e.hom
  change (localPullbackModuleIso f (dualObj M) U).inv.val.app
      (.op ZY) (localModuleSection N VY ZY xg) = s at hinv
  have hq := overEquiv_map_localModuleSectionT
    (dualObj M) U d.hom e.hom
  change q.val.app (.op W) (localModuleSection (dualObj M) U W e.hom) =
    (_root_.SheafOfModules.unit
      (X.ringCatSheaf.over U)).val.map kX.op
        (d.hom.val.app (.op (Over.mk (𝟙 U))) e.hom) at hq
  have hqr : q.val.app (.op W)
      (localModuleSection (dualObj M) U W e.hom) = r := by
    rw [hq, hd]
  have hpull := pullbackUnit_map_transportT g q W ZY hpre
    (localModuleSection (dualObj M) U W e.hom)
  change ((pullback g).map q).val.app (.op ZY) s =
    ((pullback g).obj O).presheaf.map (eqToHom hpre).op
      (((pullbackPushforwardAdjunction g).unit.app O).val.app (.op W)
        (q.val.app (.op W)
          (localModuleSection (dualObj M) U W e.hom))) at hpull
  rw [hinv, hpull, hqr]

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite



namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

theorem app_eq_of_eq_three_compT {A B C D : X.Modules}
    (F : A ⟶ D) (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (hF : F = a ≫ b ≫ c) (U : Opposite X.Opens)
    (x : A.val.obj U) (z : C.val.obj U) (w : D.val.obj U)
    (hmiddle : b.val.app U (a.val.app U x) = z)
    (htail : c.val.app U z = w) :
    F.val.app U x = w := by
  have happ := congrArg (fun q ↦ q.val.app U x) hF
  rw [three_comp_app_applyT] at happ
  rw [happ, hmiddle, htail]

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite



namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

theorem localTrivialization_overEquiv_pulledSectionT
    (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (d : (dualObj M).over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (p : ((pullback f).obj (dualObj M)).over (f ⁻¹ᵁ U) ≅
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (f ⁻¹ᵁ U)))
    (hd : d.hom.val.app (.op (Over.mk (𝟙 U))) e.hom =
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1))
    (hp : (overEquiv (f ⁻¹ᵁ U)).functor.map p.hom =
      (localPullbackModuleIso f (dualObj M) U).inv ≫
        (pullback (f ∣_ U)).map
          ((overEquiv U).functor.map d.hom) ≫
        (localPullbackUnitIso f U).hom) :
    let VY := f ⁻¹ᵁ U
    let ZY := VY.ι ⁻¹ᵁ VY
    let QY := VY.overEquivalence.symm.functor.obj ZY
    let kY : QY ⟶ Over.mk (𝟙 VY) := Over.mkIdTerminal.from QY
    let N := (pullback f).obj (dualObj M)
    let xg := ((pullbackPushforwardAdjunction f).unit.app
      (dualObj M)).val.app (.op U) e.hom
    ((overEquiv VY).functor.map p.hom).val.app (.op ZY)
        (localModuleSection N VY ZY xg) =
      (_root_.SheafOfModules.unit
        (Y.ringCatSheaf.over VY)).val.map kY.op
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
  let QX := U.overEquivalence.symm.functor.obj W
  let kX : QX ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from QX
  let QY := VY.overEquivalence.symm.functor.obj ZY
  let kY : QY ⟶ Over.mk (𝟙 VY) := Over.mkIdTerminal.from QY
  let N := (pullback f).obj (dualObj M)
  let xg := ((pullbackPushforwardAdjunction f).unit.app
    (dualObj M)).val.app (.op U) e.hom
  let O := (overEquiv U).functor.obj
    (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))
  let q := (overEquiv U).functor.map d.hom
  let r := (_root_.SheafOfModules.unit
    (X.ringCatSheaf.over U)).val.map kX.op
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1)
  let t := ((pullback g).obj O).presheaf.map (eqToHom hpre).op
    (((pullbackPushforwardAdjunction g).unit.app O).val.app (.op W) r)
  have hmiddle := localDualMiddle_pulledSectionT f M U e d hd
  change ((pullback g).map q).val.app (.op ZY)
      ((localPullbackModuleIso f (dualObj M) U).inv.val.app (.op ZY)
        (localModuleSection N VY ZY xg)) = t at hmiddle
  have ht := localOverUnit_pulled_one_eqT f U
  change t = ((pullback g).obj (unitObj U.toScheme)).presheaf.map
      (eqToHom hpre).op
        (((pullbackPushforwardAdjunction g).unit.app
          (unitObj U.toScheme)).val.app (.op W)
            (show U.toScheme.presheaf.obj (.op W) from 1)) at ht
  have hunit := localPullbackUnitIso_hom_pulled_oneT f U
  change (localPullbackUnitIso f U).hom.val.app (.op ZY)
      (((pullback g).obj (unitObj U.toScheme)).presheaf.map
        (eqToHom hpre).op
          (((pullbackPushforwardAdjunction g).unit.app
            (unitObj U.toScheme)).val.app (.op W)
              (show U.toScheme.presheaf.obj (.op W) from 1))) =
    (_root_.SheafOfModules.unit
      (Y.ringCatSheaf.over VY)).val.map kY.op
        (show (Y.ringCatSheaf.over VY).obj.obj
          (.op (Over.mk (𝟙 VY))) from 1) at hunit
  let F := (overEquiv VY).functor.map p.hom
  let a := (localPullbackModuleIso f (dualObj M) U).inv
  let b := (pullback g).map q
  let c := (localPullbackUnitIso f U).hom
  let x := localModuleSection N VY ZY xg
  let w := (_root_.SheafOfModules.unit
    (Y.ringCatSheaf.over VY)).val.map kY.op
      (show (Y.ringCatSheaf.over VY).obj.obj
        (.op (Over.mk (𝟙 VY))) from 1)
  have htail : c.val.app (.op ZY) t = w := by
    have htApplied : c.val.app (.op ZY) t =
        c.val.app (.op ZY)
          (((pullback g).obj (unitObj U.toScheme)).presheaf.map
            (eqToHom hpre).op
              (((pullbackPushforwardAdjunction g).unit.app
                (unitObj U.toScheme)).val.app (.op W)
                  (show U.toScheme.presheaf.obj (.op W) from 1))) :=
      congrArg (fun z ↦ c.val.app (.op ZY) z) ht
    exact Eq.trans htApplied hunit
  exact app_eq_of_eq_three_compT F a b c hp (.op ZY) x t w hmiddle htail

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

noncomputable def localPullbackTrivializationT
    (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ((pullback f).obj M).over (f ⁻¹ᵁ U) ≅
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (f ⁻¹ᵁ U)) :=
  (overEquiv (f ⁻¹ᵁ U)).fullyFaithfulFunctor.preimageIso
    ((localPullbackModuleIso f M U).symm ≪≫
      (pullback (f ∣_ U)).mapIso ((overEquiv U).functor.mapIso e) ≪≫
      localPullbackUnitIso f U)

theorem localDualPullback_trivialization_homT
    (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    localDualPullback f M U e.hom =
      (localPullbackTrivializationT f M U e).hom := by
  apply (overEquiv (f ⁻¹ᵁ U)).functor.map_injective
  simp only [localDualPullback, Functor.FullyFaithful.map_preimage,
    localPullbackTrivializationT,
    Functor.FullyFaithful.preimageIso_hom, Iso.trans_hom,
    Functor.mapIso_hom]
  rfl

theorem dualOverIsoOfIso_hom_terminal_apply_trivializationT
    (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ((ModularCurves.SheafOfModules.dualOverIsoOfIso
        X.ringCatSheaf M U e).hom.val.app
      (.op (Over.mk (𝟙 U)))) e.hom =
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1) := by
  change ModularCurves.SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M U
        (ModularCurves.SheafOfModules.restrictOverTrivialization
          X.ringCatSheaf M U e (Over.mk (𝟙 U))) e.hom = 1
  let eR := ModularCurves.SheafOfModules.restrictOverTrivialization
    X.ringCatSheaf M U e (Over.mk (𝟙 U))
  change (eR.inv ≫ e.hom).val.app (.op (Over.mk (𝟙 U)))
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1) =
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1)
  erw [sheafOfModules_comp_app_apply]
  let oneU : (X.ringCatSheaf.over U).obj.obj
      (.op (Over.mk (𝟙 U))) := 1
  change e.hom.val.app (.op (Over.mk (𝟙 U)))
      (eR.inv.val.app (.op (Over.mk (𝟙 U))) oneU) = oneU
  have hrestrict :
      eR.inv.val.app (.op (Over.mk (𝟙 U))) oneU =
        e.inv.val.app (.op (Over.mk (𝟙 U))) oneU := by
    exact ModularCurves.SheafOfModules.restrictOverTrivialization_inv_app_apply
      X.ringCatSheaf M U e (Over.mk (𝟙 U))
        (.op (Over.mk (𝟙 U))) oneU
  have hrestrictApplied := congrArg
    (fun z ↦ e.hom.val.app (.op (Over.mk (𝟙 U))) z) hrestrict
  have hcomp := congrArg (fun q ↦ q.val.app (.op (Over.mk (𝟙 U))))
    e.inv_hom_id
  have hcancel : e.hom.val.app (.op (Over.mk (𝟙 U)))
      (e.inv.val.app (.op (Over.mk (𝟙 U))) oneU) = oneU :=
    ConcreteCategory.congr_hom hcomp oneU
  exact Eq.trans hrestrictApplied hcancel

theorem dualOverIsoOfIso_inv_terminal_apply_oneT
    (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ((ModularCurves.SheafOfModules.dualOverIsoOfIso
        X.ringCatSheaf M U e).inv.val.app
      (.op (Over.mk (𝟙 U))))
        (show (X.ringCatSheaf.over U).obj.obj
          (.op (Over.mk (𝟙 U))) from 1) = e.hom := by
  let d := ModularCurves.SheafOfModules.dualOverIsoOfIso
    X.ringCatSheaf M U e
  have hb := dualOverIsoOfIso_hom_terminal_apply_trivializationT M U e
  have h := congrArg
    (fun x ↦ d.inv.val.app (.op (Over.mk (𝟙 U))) x) hb.symm
  have hcomp := congrArg (fun q ↦ q.val.app (.op (Over.mk (𝟙 U))))
    d.hom_inv_id
  have hright := ConcreteCategory.congr_hom hcomp
    (show ((ModularCurves.SheafOfModules.dual X.ringCatSheaf M).over U).val.obj
      (.op (Over.mk (𝟙 U))) from e.hom)
  exact h.trans hright

theorem localPullbackTrivialization_hom_unit_coreT
    (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (d : (dualObj M).over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (p : ((pullback f).obj (dualObj M)).over (f ⁻¹ᵁ U) ≅
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (f ⁻¹ᵁ U)))
    (hd : d.hom.val.app (.op (Over.mk (𝟙 U))) e.hom =
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1))
    (hp : (overEquiv (f ⁻¹ᵁ U)).functor.map p.hom =
      (localPullbackModuleIso f (dualObj M) U).inv ≫
        (pullback (f ∣_ U)).map
          ((overEquiv U).functor.map d.hom) ≫
        (localPullbackUnitIso f U).hom) :
    p.hom.val.app (.op (Over.mk (𝟙 (f ⁻¹ᵁ U))))
        (((pullbackPushforwardAdjunction f).unit.app (dualObj M)).val.app
          (.op U) e.hom) =
      (show (Y.ringCatSheaf.over (f ⁻¹ᵁ U)).obj.obj
        (.op (Over.mk (𝟙 (f ⁻¹ᵁ U)))) from 1) := by
  let VY := f ⁻¹ᵁ U
  let N := (pullback f).obj (dualObj M)
  let xg := ((pullbackPushforwardAdjunction f).unit.app
    (dualObj M)).val.app (.op U) e.hom
  refine terminal_apply_eq_of_overEquivT (X := Y) N VY p.hom xg
    (show (Y.ringCatSheaf.over VY).obj.obj
      (.op (Over.mk (𝟙 VY))) from 1) ?_
  exact localTrivialization_overEquiv_pulledSectionT
    f M U e d p hd hp

theorem localPullbackTrivialization_hom_unit_appT
    (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    let d := ModularCurves.SheafOfModules.dualOverIsoOfIso
      X.ringCatSheaf M U e
    let p := localPullbackTrivializationT f (dualObj M) U d
    p.hom.val.app (.op (Over.mk (𝟙 (f ⁻¹ᵁ U))))
        (((pullbackPushforwardAdjunction f).unit.app (dualObj M)).val.app
          (.op U) e.hom) =
      (show (Y.ringCatSheaf.over (f ⁻¹ᵁ U)).obj.obj
        (.op (Over.mk (𝟙 (f ⁻¹ᵁ U)))) from 1) := by
  let d := ModularCurves.SheafOfModules.dualOverIsoOfIso
    X.ringCatSheaf M U e
  let p := localPullbackTrivializationT f (dualObj M) U d
  apply localPullbackTrivialization_hom_unit_coreT f M U e d p
  · exact dualOverIsoOfIso_hom_terminal_apply_trivializationT M U e
  · dsimp only [p, localPullbackTrivializationT]
    simp only [Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage, Iso.trans_hom,
      Functor.mapIso_hom]
    rfl

end AlgebraicGeometry.Scheme.Modules
