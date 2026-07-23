import ModularCurves.EllipticCurve.PoleSheaf
import ModularCurves.ForMathlib.AffineModuleBaseChange

/-!
# Pullback of pure tensor sections

This file evaluates the canonical monoidal comparison for pullback of sheaves of
modules on sections coming from the pullback adjunction unit. The implementation
follows the construction of sheaf pullback through presheaf pullback and
sheafification; the only public result is `pullback_δ_unit_tensorSection`.
-/

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

noncomputable section

noncomputable local instance pullbackTensorSectionMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

namespace ModularCurves

private abbrev pullbackTensorRingSheaf (X : Scheme.{u}) :=
  (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
    X.ringCatSheaf.property⟩ : Sheaf _ RingCat.{u})

private abbrev pullbackTensorSheafificationUnit (X : Scheme.{u}) :=
  𝟙 (pullbackTensorRingSheaf X).obj

private abbrev pullbackTensorSheafification (X : Scheme.{u}) :=
  PresheafOfModules.sheafification.{u} (pullbackTensorSheafificationUnit X)

private abbrev pullbackTensorSheafificationW (X : Scheme.{u}) :=
  PresheafOfModules.sheafificationW.{u} (pullbackTensorSheafificationUnit X)

private local instance pullbackTensorSheafificationLocalization (X : Scheme.{u}) :
    (pullbackTensorSheafification X).IsLocalization
      (pullbackTensorSheafificationW X) :=
  PresheafOfModules.sheafificationW_isLocalization (pullbackTensorRingSheaf X)

private local instance pullbackTensorSheafificationWMonoidal (X : Scheme.{u}) :
    (pullbackTensorSheafificationW X).IsMonoidal :=
  PresheafOfModules.sheafificationW_isMonoidal _

private local instance pullbackTensorSheafModulesMonoidal (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules (pullbackTensorRingSheaf X)) := by
  change MonoidalCategory X.Modules
  exact Scheme.Modules.monoidalCategory X

private abbrev pullbackTensorLocalizedSheafification (X : Scheme.{u}) :=
  Localization.Monoidal.toMonoidalCategory
    (L := pullbackTensorSheafification X)
    (W := pullbackTensorSheafificationW X) (Iso.refl _)

private local instance pullbackTensorLocalizedSheafificationMonoidal
    (X : Scheme.{u}) :
    (pullbackTensorLocalizedSheafification X).Monoidal := inferInstance

private abbrev pullbackTensorPresheafPullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  PresheafOfModules.pullback.{u}
    (_root_.PresheafOfModules.schemeRingPresheafHom f)

private abbrev pullbackTensorSheafHom
    {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  (⟨_root_.PresheafOfModules.schemeRingPresheafHom f⟩ :
    pullbackTensorRingSheaf X ⟶
      ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
        RingCat.{u} _ _).obj (pullbackTensorRingSheaf Y))

private abbrev pullbackTensorSheafPullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  SheafOfModules.pullback.{u} (pullbackTensorSheafHom f)

@[implicit_reducible]
private noncomputable def pullbackTensorSheafPullbackLifting
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Localization.Lifting (pullbackTensorLocalizedSheafification X)
      (pullbackTensorSheafificationW X)
      (pullbackTensorPresheafPullback f ⋙
        pullbackTensorLocalizedSheafification Y)
      (pullbackTensorSheafPullback f) :=
  ⟨SheafOfModules.sheafificationCompPullback (pullbackTensorSheafHom f)⟩

private theorem pullback_μ_formula
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules) :
    letI : (Scheme.Modules.pullback f).Monoidal :=
      Scheme.Modules.pullbackMonoidal f
    let G := pullbackTensorPresheafPullback f ⋙
      pullbackTensorLocalizedSheafification Y
    letI : (pullbackTensorPresheafPullback f).Monoidal :=
      _root_.PresheafOfModules.pullbackMonoidal f
    letI : G.Monoidal := inferInstance
    let e := SheafOfModules.sheafificationCompPullback
      (pullbackTensorSheafHom f)
    Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) M N =
      (((Scheme.Modules.pullback f).map
          (Scheme.Modules.sheafifyValIso M).inv ≫ e.hom.app M.val) ⊗ₘ
        ((Scheme.Modules.pullback f).map
          (Scheme.Modules.sheafifyValIso N).inv ≫ e.hom.app N.val)) ≫
        Functor.LaxMonoidal.μ G M.val N.val ≫
        e.inv.app (M.val ⊗ N.val) ≫
        (Scheme.Modules.pullback f).map (monoidalTensorObjIso M N).inv := by
  dsimp only
  let L := pullbackTensorLocalizedSheafification X
  let W := pullbackTensorSheafificationW X
  let F := pullbackTensorSheafPullback f
  let G := pullbackTensorPresheafPullback f ⋙
    pullbackTensorLocalizedSheafification Y
  letI lX : (pullbackTensorLocalizedSheafification X).Monoidal := inferInstance
  letI lY : (pullbackTensorLocalizedSheafification Y).Monoidal := inferInstance
  letI pF : (pullbackTensorPresheafPullback f).Monoidal :=
    _root_.PresheafOfModules.pullbackMonoidal f
  letI pgF : G.Monoidal := inferInstance
  letI liftF : Localization.Lifting L W G F :=
    pullbackTensorSheafPullbackLifting f
  letI fM : F.Monoidal :=
    @Localization.Monoidal.functorMonoidalOfComp
      _ _ _ _ _ _ _ _ _ L W _ lX F G pgF _ liftF
  let eM := (Scheme.Modules.sheafifyValIso M).symm
  let eN := (Scheme.Modules.sheafifyValIso N).symm
  have h := @Localization.Monoidal.curriedTensorPreIsoPost_hom_app_app'
    _ _ _ _ _ _ _ _ _ L W _ lX F G pgF _ liftF _ _ _ _ eM eN
  exact h

private theorem pullback_factor_unit
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (x : M.val.obj (.op U)) :
    let PB := pullbackTensorPresheafPullback f
    let shAdjY := PresheafOfModules.sheafificationAdjunction
      (𝟙 Y.ringCatSheaf.obj)
    let preAdj := PresheafOfModules.pullbackPushforwardAdjunction
      (_root_.PresheafOfModules.schemeRingPresheafHom f)
    let e := SheafOfModules.sheafificationCompPullback
      (pullbackTensorSheafHom f)
    ((((Scheme.Modules.pullback f).map
        (Scheme.Modules.sheafifyValIso M).inv ≫ e.hom.app M.val).val.app
          (.op (f ⁻¹ᵁ U)))
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
        (.op U) x)) =
      (shAdjY.unit.app (PB.obj M.val)).app (.op (f ⁻¹ᵁ U))
        ((preAdj.unit.app M.val).app (.op U) x) := by
  dsimp only
  let LX := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let pbAdj := Scheme.Modules.pullbackPushforwardAdjunction f
  let c := Scheme.Modules.sheafifyValIso M
  let e := SheafOfModules.sheafificationCompPullback
    (pullbackTensorSheafHom f)
  have hnat := pbAdj.unit.naturality c.inv
  have happ := congrArg (fun q => q.val.app (.op U) x) hnat
  conv_lhs at happ =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  conv_rhs at happ =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  change
    ((pbAdj.unit.app (LX.obj M.val)).val.app (.op U))
        (c.inv.val.app (.op U) x) =
      (((Scheme.Modules.pullback f).map c.inv).val.app
        (.op (f ⁻¹ᵁ U)))
          ((pbAdj.unit.app M).val.app (.op U) x) at happ
  have hc := Scheme.Modules.sheafifyValIso_inv_app_apply M U x
  have he := Scheme.Modules.sheafificationCompPullback_hom_unit_app_apply
    f M.val U x
  conv_lhs =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  rw [← happ, hc]
  exact he

private theorem composite_pullback_μ_tensorSection
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (P Q : X.PresheafOfModules) (U : X.Opens)
    (x : P.obj (.op U)) (y : Q.obj (.op U)) :
    let PB := pullbackTensorPresheafPullback f
    let LY := pullbackTensorLocalizedSheafification Y
    let G := PB ⋙ LY
    let shAdjY := PresheafOfModules.sheafificationAdjunction
      (𝟙 Y.ringCatSheaf.obj)
    let preAdj := PresheafOfModules.pullbackPushforwardAdjunction
      (_root_.PresheafOfModules.schemeRingPresheafHom f)
    letI : PB.Monoidal := _root_.PresheafOfModules.pullbackMonoidal f
    letI : G.Monoidal := inferInstance
    (Functor.LaxMonoidal.μ G P Q).val.app (.op (f ⁻¹ᵁ U))
        (tensorSection (G.obj P) (G.obj Q) (f ⁻¹ᵁ U)
          ((shAdjY.unit.app (PB.obj P)).app (.op (f ⁻¹ᵁ U))
            ((preAdj.unit.app P).app (.op U) x))
          ((shAdjY.unit.app (PB.obj Q)).app (.op (f ⁻¹ᵁ U))
            ((preAdj.unit.app Q).app (.op U) y))) =
      (shAdjY.unit.app (PB.obj (P ⊗ Q))).app (.op (f ⁻¹ᵁ U))
        ((preAdj.unit.app (P ⊗ Q)).app (.op U) (x ⊗ₜ y)) := by
  dsimp only
  let PB := pullbackTensorPresheafPullback f
  let LY := pullbackTensorLocalizedSheafification Y
  let G := PB ⋙ LY
  let shAdjY := PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)
  let preAdj := PresheafOfModules.pullbackPushforwardAdjunction
    (_root_.PresheafOfModules.schemeRingPresheafHom f)
  letI pF : PB.Monoidal := _root_.PresheafOfModules.pullbackMonoidal f
  letI gF : G.Monoidal := inferInstance
  let r := (shAdjY.unit.app (PB.obj (P ⊗ Q))).app
    (.op (f ⁻¹ᵁ U))
      ((preAdj.unit.app (P ⊗ Q)).app (.op U) (x ⊗ₜ y))
  have hmap := PresheafOfModules.sheafification_map_pullback_δ_unit_tmul
    (φ := _root_.PresheafOfModules.schemeRingPresheafHom f)
    Y.ringCatSheaf.property P Q (.op U) x y
  have hsh := sheafification_δ_unit_tmul_eq_tensorSection
    (X := Y) (PB.obj P) (PB.obj Q) (f ⁻¹ᵁ U)
      ((preAdj.unit.app P).app (.op U) x)
      ((preAdj.unit.app Q).app (.op U) y)
  dsimp only at hmap hsh
  change
    (LY.map (Functor.OplaxMonoidal.δ PB P Q)).val.app
        (.op (f ⁻¹ᵁ U)) r =
      (shAdjY.unit.app (PB.obj P ⊗ PB.obj Q)).app
        (.op (f ⁻¹ᵁ U))
          (((preAdj.unit.app P).app (.op U) x) ⊗ₜ
            ((preAdj.unit.app Q).app (.op U) y)) at hmap
  change
    (Functor.OplaxMonoidal.δ LY (PB.obj P) (PB.obj Q)).val.app
        (.op (f ⁻¹ᵁ U))
          ((shAdjY.unit.app (PB.obj P ⊗ PB.obj Q)).app
            (.op (f ⁻¹ᵁ U))
              (((preAdj.unit.app P).app (.op U) x) ⊗ₜ
                ((preAdj.unit.app Q).app (.op U) y))) =
      tensorSection (G.obj P) (G.obj Q) (f ⁻¹ᵁ U)
        ((shAdjY.unit.app (PB.obj P)).app (.op (f ⁻¹ᵁ U))
          ((preAdj.unit.app P).app (.op U) x))
        ((shAdjY.unit.app (PB.obj Q)).app (.op (f ⁻¹ᵁ U))
          ((preAdj.unit.app Q).app (.op U) y)) at hsh
  have hdelta :
      (Functor.OplaxMonoidal.δ G P Q).val.app (.op (f ⁻¹ᵁ U)) r =
        tensorSection (G.obj P) (G.obj Q) (f ⁻¹ᵁ U)
          ((shAdjY.unit.app (PB.obj P)).app (.op (f ⁻¹ᵁ U))
            ((preAdj.unit.app P).app (.op U) x))
          ((shAdjY.unit.app (PB.obj Q)).app (.op (f ⁻¹ᵁ U))
            ((preAdj.unit.app Q).app (.op U) y)) := by
    change
      ((LY.map (Functor.OplaxMonoidal.δ PB P Q) ≫
          Functor.OplaxMonoidal.δ LY (PB.obj P) (PB.obj Q)).val.app
        (.op (f ⁻¹ᵁ U))) r = _
    conv_lhs =>
      erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
        ModuleCat.comp_apply]
    rw [hmap, hsh]
  have hinv := Functor.Monoidal.δ_μ G P Q
  have hinvApply := congrArg (fun q => q.val.app (.op (f ⁻¹ᵁ U)) r) hinv
  conv_lhs at hinvApply =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  change
    (Functor.LaxMonoidal.μ G P Q).val.app (.op (f ⁻¹ᵁ U))
        ((Functor.OplaxMonoidal.δ G P Q).val.app
          (.op (f ⁻¹ᵁ U)) r) = r at hinvApply
  rw [hdelta] at hinvApply
  exact hinvApply

private theorem sheafificationCompPullback_inv_unit
    {X Y : Scheme.{u}} (f : Y ⟶ X) (P : X.PresheafOfModules)
    (U : X.Opens) (x : P.obj (.op U)) :
    let LX := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let PB := pullbackTensorPresheafPullback f
    let shAdjX := PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)
    let shAdjY := PresheafOfModules.sheafificationAdjunction
      (𝟙 Y.ringCatSheaf.obj)
    let preAdj := PresheafOfModules.pullbackPushforwardAdjunction
      (_root_.PresheafOfModules.schemeRingPresheafHom f)
    let e := SheafOfModules.sheafificationCompPullback
      (pullbackTensorSheafHom f)
    (e.inv.app P).val.app (.op (f ⁻¹ᵁ U))
        ((shAdjY.unit.app (PB.obj P)).app (.op (f ⁻¹ᵁ U))
          ((preAdj.unit.app P).app (.op U) x)) =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (LX.obj P)).val.app (.op U))
          ((shAdjX.unit.app P).app (.op U) x) := by
  dsimp only
  let LX := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let shAdjX := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let pbAdj := Scheme.Modules.pullbackPushforwardAdjunction f
  let e := SheafOfModules.sheafificationCompPullback
    (pullbackTensorSheafHom f)
  let a := ((pbAdj.unit.app (LX.obj P)).val.app (.op U))
    ((shAdjX.unit.app P).app (.op U) x)
  have he := Scheme.Modules.sheafificationCompPullback_hom_unit_app_apply
    f P U x
  have heInv := congrArg
    (fun z => (e.inv.app P).val.app (.op (f ⁻¹ᵁ U)) z) he
  have hcancel := congrArg (fun q => q.val.app (.op (f ⁻¹ᵁ U)) a)
    (e.app P).hom_inv_id
  conv_lhs at hcancel =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  exact heInv.symm.trans hcancel

private theorem pullback_monoidalTensorObjIso_inv_unit
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules)
    (U : X.Opens) (x : M.val.obj (.op U)) (y : N.val.obj (.op U)) :
    let LX := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let shAdjX := PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)
    let h := (monoidalTensorObjIso M N).inv
    (((Scheme.Modules.pullback f).map h).val.app (.op (f ⁻¹ᵁ U)))
        ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          (LX.obj (M.val ⊗ N.val))).val.app (.op U))
            ((shAdjX.unit.app (M.val ⊗ N.val)).app (.op U) (x ⊗ₜ y))) =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (M ⊗ N)).val.app (.op U)) (tensorSection M N U x y) := by
  dsimp only
  let LX := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let shAdjX := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let pbAdj := Scheme.Modules.pullbackPushforwardAdjunction f
  let h := (monoidalTensorObjIso M N).inv
  let t := (shAdjX.unit.app (M.val ⊗ N.val)).app (.op U) (x ⊗ₜ y)
  have hnat := pbAdj.unit.naturality h
  have happ := congrArg (fun q => q.val.app (.op U) t) hnat
  conv_lhs at happ =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  conv_rhs at happ =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  change
    ((pbAdj.unit.app (M ⊗ N)).val.app (.op U))
        (h.val.app (.op U) t) =
      (((Scheme.Modules.pullback f).map h).val.app (.op (f ⁻¹ᵁ U)))
        (((pbAdj.unit.app (LX.obj (M.val ⊗ N.val))).val.app (.op U)) t) at happ
  exact happ.symm

private theorem pullback_μ_unit_tensorSection
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules)
    (U : X.Opens) (x : M.val.obj (.op U)) (y : N.val.obj (.op U)) :
    letI : (Scheme.Modules.pullback f).Monoidal :=
      Scheme.Modules.pullbackMonoidal f
    (Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) M N).val.app
        (.op (f ⁻¹ᵁ U))
        (tensorSection
          ((Scheme.Modules.pullback f).obj M)
          ((Scheme.Modules.pullback f).obj N) (f ⁻¹ᵁ U)
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
            (.op U) x)
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
            (.op U) y)) =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (M ⊗ N)).val.app (.op U)) (tensorSection M N U x y) := by
  dsimp only
  let PB := Scheme.Modules.pullback f
  let prePB := pullbackTensorPresheafPullback f
  let LY := pullbackTensorLocalizedSheafification Y
  let G := prePB ⋙ LY
  let e := SheafOfModules.sheafificationCompPullback
    (pullbackTensorSheafHom f)
  let cM := Scheme.Modules.sheafifyValIso M
  let cN := Scheme.Modules.sheafifyValIso N
  let aM := PB.map cM.inv ≫ e.hom.app M.val
  let aN := PB.map cN.inv ≫ e.hom.app N.val
  let h := (monoidalTensorObjIso M N).inv
  let uM := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
    (.op U) x
  let uN := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
    (.op U) y
  let t := tensorSection (PB.obj M) (PB.obj N) (f ⁻¹ᵁ U) uM uN
  let shAdjY := PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)
  let preAdj := PresheafOfModules.pullbackPushforwardAdjunction
    (_root_.PresheafOfModules.schemeRingPresheafHom f)
  let vM := (shAdjY.unit.app (prePB.obj M.val)).app (.op (f ⁻¹ᵁ U))
    ((preAdj.unit.app M.val).app (.op U) x)
  let vN := (shAdjY.unit.app (prePB.obj N.val)).app (.op (f ⁻¹ᵁ U))
    ((preAdj.unit.app N.val).app (.op U) y)
  let raw := (shAdjY.unit.app (prePB.obj (M.val ⊗ N.val))).app
    (.op (f ⁻¹ᵁ U))
      ((preAdj.unit.app (M.val ⊗ N.val)).app (.op U) (x ⊗ₜ y))
  let LX := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let shAdjX := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let source := (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
    (LX.obj (M.val ⊗ N.val))).val.app (.op U))
      ((shAdjX.unit.app (M.val ⊗ N.val)).app (.op U) (x ⊗ₜ y))
  letI pbMonoidal : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
  letI prePBMonoidal : prePB.Monoidal :=
    _root_.PresheafOfModules.pullbackMonoidal f
  letI gMonoidal : G.Monoidal := inferInstance
  have hformula := pullback_μ_formula f M N
  dsimp only at hformula
  have hformulaApply := congrArg
    (fun q => q.val.app (.op (f ⁻¹ᵁ U)) t) hformula
  change
    (Functor.LaxMonoidal.μ PB M N).val.app (.op (f ⁻¹ᵁ U)) t =
      (PB.map h).val.app (.op (f ⁻¹ᵁ U))
        ((e.inv.app (M.val ⊗ N.val)).val.app (.op (f ⁻¹ᵁ U))
          ((Functor.LaxMonoidal.μ G M.val N.val).val.app
            (.op (f ⁻¹ᵁ U))
              ((aM ⊗ₘ aN).val.app (.op (f ⁻¹ᵁ U)) t))) at hformulaApply
  have hmap := tensorSection_map aM aN (f ⁻¹ᵁ U) uM uN
  have hfactorM := pullback_factor_unit f M U x
  have hfactorN := pullback_factor_unit f N U y
  have hmiddle := composite_pullback_μ_tensorSection
    f M.val N.val U x y
  have heInv := sheafificationCompPullback_inv_unit
    f (M.val ⊗ N.val) U (x ⊗ₜ y)
  have hfinal := pullback_monoidalTensorObjIso_inv_unit
    f M N U x y
  dsimp only at hfactorM hfactorN hmiddle heInv hfinal
  change aM.val.app (.op (f ⁻¹ᵁ U)) uM = vM at hfactorM
  change aN.val.app (.op (f ⁻¹ᵁ U)) uN = vN at hfactorN
  change
    (Functor.LaxMonoidal.μ G M.val N.val).val.app (.op (f ⁻¹ᵁ U))
        (tensorSection (G.obj M.val) (G.obj N.val) (f ⁻¹ᵁ U) vM vN) =
      raw at hmiddle
  change (e.inv.app (M.val ⊗ N.val)).val.app
    (.op (f ⁻¹ᵁ U)) raw = source at heInv
  change (PB.map h).val.app (.op (f ⁻¹ᵁ U)) source =
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (M ⊗ N)).val.app (.op U)) (tensorSection M N U x y) at hfinal
  have hchain :
      (Functor.LaxMonoidal.μ PB M N).val.app (.op (f ⁻¹ᵁ U)) t =
        (PB.map h).val.app (.op (f ⁻¹ᵁ U)) source := by
    calc
      _ = (PB.map h).val.app (.op (f ⁻¹ᵁ U))
          ((e.inv.app (M.val ⊗ N.val)).val.app (.op (f ⁻¹ᵁ U))
            ((Functor.LaxMonoidal.μ G M.val N.val).val.app
              (.op (f ⁻¹ᵁ U))
                ((aM ⊗ₘ aN).val.app (.op (f ⁻¹ᵁ U)) t))) :=
        hformulaApply
      _ = (PB.map h).val.app (.op (f ⁻¹ᵁ U))
          ((e.inv.app (M.val ⊗ N.val)).val.app (.op (f ⁻¹ᵁ U))
            ((Functor.LaxMonoidal.μ G M.val N.val).val.app
              (.op (f ⁻¹ᵁ U))
                (tensorSection (G.obj M.val) (G.obj N.val) (f ⁻¹ᵁ U)
                  (aM.val.app (.op (f ⁻¹ᵁ U)) uM)
                  (aN.val.app (.op (f ⁻¹ᵁ U)) uN)))) :=
        congrArg
          (fun z => (PB.map h).val.app (.op (f ⁻¹ᵁ U))
            ((e.inv.app (M.val ⊗ N.val)).val.app (.op (f ⁻¹ᵁ U))
              ((Functor.LaxMonoidal.μ G M.val N.val).val.app
                (.op (f ⁻¹ᵁ U)) z))) hmap
      _ = (PB.map h).val.app (.op (f ⁻¹ᵁ U))
          ((e.inv.app (M.val ⊗ N.val)).val.app (.op (f ⁻¹ᵁ U))
            ((Functor.LaxMonoidal.μ G M.val N.val).val.app
              (.op (f ⁻¹ᵁ U))
                (tensorSection (G.obj M.val) (G.obj N.val) (f ⁻¹ᵁ U)
                  vM vN))) := by
        rw [hfactorM, hfactorN]
      _ = (PB.map h).val.app (.op (f ⁻¹ᵁ U))
          ((e.inv.app (M.val ⊗ N.val)).val.app (.op (f ⁻¹ᵁ U))
            raw) :=
        congrArg
          (fun z => (PB.map h).val.app (.op (f ⁻¹ᵁ U))
            ((e.inv.app (M.val ⊗ N.val)).val.app
              (.op (f ⁻¹ᵁ U)) z)) hmiddle
      _ = (PB.map h).val.app (.op (f ⁻¹ᵁ U)) source :=
        congrArg (fun z => (PB.map h).val.app (.op (f ⁻¹ᵁ U)) z) heInv
  exact hchain.trans hfinal

/-- The canonical pullback cotensorator sends the pullback-unit image of a pure
tensor section to the pure tensor of the two pullback-unit sections. -/
theorem pullback_δ_unit_tensorSection
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules)
    (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) :
    letI : (Scheme.Modules.pullback f).Monoidal :=
      Scheme.Modules.pullbackMonoidal f
    (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) M N).val.app
        (.op (f ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          (M ⊗ N)).val.app (.op U) (tensorSection M N U x y)) =
      tensorSection
        ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
          (.op U) x)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
          (.op U) y) := by
  dsimp only
  let PB := Scheme.Modules.pullback f
  let uM := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
    (.op U) x
  let uN := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
    (.op U) y
  let t := tensorSection (PB.obj M) (PB.obj N) (f ⁻¹ᵁ U) uM uN
  letI pbMonoidal : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
  have hμ := pullback_μ_unit_tensorSection f M N U x y
  dsimp only at hμ
  change
    (Functor.LaxMonoidal.μ PB M N).val.app (.op (f ⁻¹ᵁ U)) t =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (M ⊗ N)).val.app (.op U)) (tensorSection M N U x y) at hμ
  have hinv := Functor.Monoidal.μ_δ PB M N
  have hinvApply := congrArg (fun q => q.val.app (.op (f ⁻¹ᵁ U)) t) hinv
  conv_lhs at hinvApply =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  change
    (Functor.OplaxMonoidal.δ PB M N).val.app (.op (f ⁻¹ᵁ U))
        ((Functor.LaxMonoidal.μ PB M N).val.app (.op (f ⁻¹ᵁ U)) t) = t at hinvApply
  rw [hμ] at hinvApply
  exact hinvApply

end ModularCurves

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical comparison from open restriction to pullback sends a
restriction-unit section to the corresponding pullback-unit section. -/
theorem restrictFunctorIsoPullback_hom_unit_app_apply
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (U : X.Opens) (x : M.val.obj (.op U)) :
    ((restrictFunctorIsoPullback f).app M).hom.val.app (.op (f ⁻¹ᵁ U))
        (((restrictAdjunction f).unit.app M).val.app (.op U) x) =
      ((pullbackPushforwardAdjunction f).unit.app M).val.app (.op U) x := by
  let adjr := restrictAdjunction f
  let adjp := pullbackPushforwardAdjunction f
  let e := (restrictFunctorIsoPullback f).app M
  have he := Adjunction.homEquiv_leftAdjointUniq_hom_app adjr adjp M
  change (adjr.homEquiv _ _) e.hom = adjp.unit.app M at he
  rw [Adjunction.homEquiv_unit] at he
  have happ := congrArg (fun q => q.val.app (.op U) x) he
  conv_lhs at happ =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  exact happ

/-- The inverse comparison from pullback to open restriction sends a pullback-unit section to
the corresponding restriction-unit section. -/
theorem restrictFunctorIsoPullback_inv_unit_app_apply
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (U : X.Opens) (x : M.val.obj (.op U)) :
    ((restrictFunctorIsoPullback f).app M).inv.val.app (.op (f ⁻¹ᵁ U))
        (((pullbackPushforwardAdjunction f).unit.app M).val.app (.op U) x) =
      ((restrictAdjunction f).unit.app M).val.app (.op U) x := by
  let e := (restrictFunctorIsoPullback f).app M
  let r := ((restrictAdjunction f).unit.app M).val.app (.op U) x
  have hhom := restrictFunctorIsoPullback_hom_unit_app_apply f M U x
  have happ := congrArg
    (fun z => e.inv.val.app (.op (f ⁻¹ᵁ U)) z) hhom
  have hcancel := congrArg (fun q => q.val.app (.op (f ⁻¹ᵁ U)) r)
    e.hom_inv_id
  conv_lhs at hcancel =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  exact happ.symm.trans hcancel

/-- On top sections, the inverse comparison from pullback to open restriction carries the
transported pullback unit to the transported restriction unit. -/
theorem restrictFunctorIsoPullback_inv_affinePullbackUnitTop
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (x : M.val.obj (.op (⊤ : X.Opens))) :
    ((restrictFunctorIsoPullback f).app M).inv.val.app (.op ⊤)
        (affinePullbackUnitTop f M x) =
      (M.restrict f).presheaf.map
        (eqToHom (Scheme.Hom.preimage_top f).symm).op
        (((restrictAdjunction f).unit.app M).val.app (.op ⊤) x) := by
  let e := (restrictFunctorIsoPullback f).app M
  let P := (pullback f).obj M
  let R := M.restrict f
  let htop := Scheme.Hom.preimage_top f
  let unitTop := (((pullbackPushforwardAdjunction f).unit.app M).val.app
    (.op (⊤ : X.Opens))) x
  have hnat := e.inv.val.naturality (eqToHom htop.symm).op
  have hnatApply := ConcreteCategory.congr_hom hnat unitTop
  change e.inv.val.app (.op (⊤ : Y.Opens))
      (P.presheaf.map (eqToHom htop.symm).op unitTop) =
    R.presheaf.map (eqToHom htop.symm).op
      (e.inv.val.app (.op (f ⁻¹ᵁ (⊤ : X.Opens))) unitTop) at hnatApply
  rw [restrictFunctorIsoPullback_inv_unit_app_apply] at hnatApply
  exact hnatApply

end AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

private theorem restrictMonoidalTensorIso_hom
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M N : X.Modules) :
    let PB := Scheme.Modules.pullback f
    let eT := (Scheme.Modules.restrictFunctorIsoPullback f).app (M ⊗ N)
    let eM := (Scheme.Modules.restrictFunctorIsoPullback f).app M
    let eN := (Scheme.Modules.restrictFunctorIsoPullback f).app N
    letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
    (restrictMonoidalTensorIso f M N).hom =
      eT.hom ≫ Functor.OplaxMonoidal.δ PB M N ≫ (eM.inv ⊗ₘ eN.inv) := by
  rfl

private theorem restrictMonoidalTensorIso_restrictUnit_tensorSection
    {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (x : Γ(M, U)) (y : Γ(N, U)) :
    let Z := U.ι ⁻¹ᵁ U
    let F := Scheme.Modules.restrictFunctor U.ι
    (restrictMonoidalTensorIso U.ι M N).hom.val.app (.op Z)
        (((Scheme.Modules.restrictAdjunction U.ι).unit.app
          (M ⊗ N)).val.app (.op U) (tensorSection M N U x y)) =
      tensorSection (F.obj M) (F.obj N) Z
        (((Scheme.Modules.restrictAdjunction U.ι).unit.app M).val.app
          (.op U) x)
        (((Scheme.Modules.restrictAdjunction U.ι).unit.app N).val.app
          (.op U) y) := by
  dsimp only
  let Z := U.ι ⁻¹ᵁ U
  let F := Scheme.Modules.restrictFunctor U.ι
  let PB := Scheme.Modules.pullback U.ι
  let eT := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app (M ⊗ N)
  let eM := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
  let eN := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app N
  let rT := ((Scheme.Modules.restrictAdjunction U.ι).unit.app
    (M ⊗ N)).val.app (.op U) (tensorSection M N U x y)
  let pM := ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app
    M).val.app (.op U) x
  let pN := ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app
    N).val.app (.op U) y
  letI pbMonoidal : PB.Monoidal := Scheme.Modules.pullbackMonoidal U.ι
  have hT := Scheme.Modules.restrictFunctorIsoPullback_hom_unit_app_apply
    U.ι (M ⊗ N) U (tensorSection M N U x y)
  have hδ := pullback_δ_unit_tensorSection U.ι M N U x y
  have hmap := tensorSection_map eM.inv eN.inv Z pM pN
  have hM := Scheme.Modules.restrictFunctorIsoPullback_inv_unit_app_apply
    U.ι M U x
  have hN := Scheme.Modules.restrictFunctorIsoPullback_inv_unit_app_apply
    U.ι N U y
  have hcomp := restrictMonoidalTensorIso_hom U.ι M N
  dsimp only at hT hδ hM hN
  change eT.hom.val.app (.op Z) rT =
    ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app
      (M ⊗ N)).val.app (.op U) (tensorSection M N U x y) at hT
  change
    (Functor.OplaxMonoidal.δ PB M N).val.app (.op Z)
        (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app
          (M ⊗ N)).val.app (.op U) (tensorSection M N U x y)) =
      tensorSection (PB.obj M) (PB.obj N) Z pM pN at hδ
  change eM.inv.val.app (.op Z) pM =
    ((Scheme.Modules.restrictAdjunction U.ι).unit.app M).val.app
      (.op U) x at hM
  change eN.inv.val.app (.op Z) pN =
    ((Scheme.Modules.restrictAdjunction U.ι).unit.app N).val.app
      (.op U) y at hN
  change
    (eM.inv ⊗ₘ eN.inv).val.app (.op Z)
        (tensorSection (PB.obj M) (PB.obj N) Z pM pN) =
      tensorSection (F.obj M) (F.obj N) Z
        (eM.inv.val.app (.op Z) pM) (eN.inv.val.app (.op Z) pN) at hmap
  dsimp only at hcomp
  have hcompApply := congrArg (fun q => q.val.app (.op Z) rT) hcomp
  conv_rhs at hcompApply =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have hpullback :
      (restrictMonoidalTensorIso U.ι M N).hom.val.app (.op Z) rT =
        (eM.inv ⊗ₘ eN.inv).val.app (.op Z)
          (tensorSection (PB.obj M) (PB.obj N) Z pM pN) := by
    calc
      _ = (eM.inv ⊗ₘ eN.inv).val.app (.op Z)
          ((Functor.OplaxMonoidal.δ PB M N).val.app (.op Z)
            (eT.hom.val.app (.op Z) rT)) := hcompApply
      _ = (eM.inv ⊗ₘ eN.inv).val.app (.op Z)
          ((Functor.OplaxMonoidal.δ PB M N).val.app (.op Z)
            (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app
              (M ⊗ N)).val.app (.op U) (tensorSection M N U x y))) := by
        rw [hT]
      _ = (eM.inv ⊗ₘ eN.inv).val.app (.op Z)
          (tensorSection (PB.obj M) (PB.obj N) Z pM pN) := by
        rw [hδ]
  have hrestrict :
      (eM.inv ⊗ₘ eN.inv).val.app (.op Z)
          (tensorSection (PB.obj M) (PB.obj N) Z pM pN) =
        tensorSection (F.obj M) (F.obj N) Z
          (((Scheme.Modules.restrictAdjunction U.ι).unit.app M).val.app
            (.op U) x)
          (((Scheme.Modules.restrictAdjunction U.ι).unit.app N).val.app
            (.op U) y) := by
    rw [hmap, hM, hN]
  exact hpullback.trans hrestrict

/-- The canonical restriction tensor comparison sends a local pure tensor to
the pure tensor of the corresponding restricted local sections. -/
theorem restrictMonoidalTensorIso_localModuleSection
    {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (x : Γ(M, U)) (y : Γ(N, U)) :
    let Z := U.ι ⁻¹ᵁ U
    let F := Scheme.Modules.restrictFunctor U.ι
    let P : X.Modules := M ⊗ N
    (restrictMonoidalTensorIso U.ι M N).hom.val.app (.op Z)
        (((Scheme.Modules.overFunctorEquiv U).app P).hom.val.app
          (.op Z)
          (Scheme.Modules.localModuleSection P U Z
            (tensorSection M N U x y))) =
      tensorSection (F.obj M) (F.obj N) Z
        (((Scheme.Modules.overFunctorEquiv U).app M).hom.val.app (.op Z)
          (Scheme.Modules.localModuleSection M U Z x))
        (((Scheme.Modules.overFunctorEquiv U).app N).hom.val.app (.op Z)
          (Scheme.Modules.localModuleSection N U Z y)) := by
  dsimp only
  rw [Scheme.Modules.overFunctorEquiv_hom_localModuleSection_preimageT
      (M ⊗ N) U (tensorSection M N U x y),
    Scheme.Modules.overFunctorEquiv_hom_localModuleSection_preimageT M U x,
    Scheme.Modules.overFunctorEquiv_hom_localModuleSection_preimageT N U y]
  exact restrictMonoidalTensorIso_restrictUnit_tensorSection M N U x y

private theorem overTrivialization_hom_app_injective
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Function.Injective (e.hom.val.app (.op (Over.mk (𝟙 U)))) := by
  intro x y hxy
  have hback := congrArg
    (fun z ↦ e.inv.val.app (.op (Over.mk (𝟙 U))) z) hxy
  have hcomp := congrArg
    (fun q ↦ q.val.app (.op (Over.mk (𝟙 U)))) e.hom_inv_id
  have hx := ConcreteCategory.congr_hom hcomp x
  have hy := ConcreteCategory.congr_hom hcomp y
  exact hx.symm.trans (hback.trans hy)

private theorem overTrivializationOfRestrictIso_local_one
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme) :
    let Z := U.ι ⁻¹ᵁ U
    e.hom.val.app (.op Z)
        (((Scheme.Modules.overFunctorEquiv U).app M).hom.val.app (.op Z)
          (Scheme.Modules.localModuleSection M U Z
            (overTrivializationSection M U
              (Scheme.Modules.overTrivializationOfRestrictIso M U e) 1))) =
      (show Γ(U.toScheme, Z) from 1) := by
  dsimp only
  let eOver := Scheme.Modules.overTrivializationOfRestrictIso M U e
  let x := overTrivializationSection M U eOver 1
  have h := Scheme.Modules.overEquiv_map_localModuleSectionT M U eOver.hom x
  dsimp only [x] at h
  rw [overTrivializationSection_coefficient] at h
  change _ = (X.ringCatSheaf.over U).obj.map _ 1 at h
  rw [map_one] at h
  simp only [eOver, Scheme.Modules.overTrivializationOfRestrictIso,
    Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom] at h
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at h
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at h
  change e.hom.val.app (.op (U.ι ⁻¹ᵁ U))
      (((Scheme.Modules.overFunctorEquiv U).app M).hom.val.app
        (.op (U.ι ⁻¹ᵁ U))
        (Scheme.Modules.localModuleSection M U (U.ι ⁻¹ᵁ U)
          (overTrivializationSection M U eOver 1))) =
      (show Γ(U.toScheme, U.ι ⁻¹ᵁ U) from 1) at h
  exact h

private theorem tensorSection_map_restrictIso
    {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (eM : M.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme)
    (eN : N.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme)
    (Z : U.toScheme.Opens)
    (x : Γ((Scheme.Modules.restrictFunctor U.ι).obj M, Z))
    (y : Γ((Scheme.Modules.restrictFunctor U.ι).obj N, Z)) :
    (eM.hom ⊗ₘ eN.hom).val.app (.op Z)
        (tensorSection ((Scheme.Modules.restrictFunctor U.ι).obj M)
          ((Scheme.Modules.restrictFunctor U.ι).obj N) Z x y) =
      tensorSection (Scheme.Modules.unitObj U.toScheme)
        (Scheme.Modules.unitObj U.toScheme) Z
        (eM.hom.val.app (.op Z) x) (eN.hom.val.app (.op Z) y) := by
  exact tensorSection_map
    (X := U.toScheme)
    (M := (Scheme.Modules.restrictFunctor U.ι).obj M)
    (M' := Scheme.Modules.unitObj U.toScheme)
    (N := (Scheme.Modules.restrictFunctor U.ι).obj N)
    (N' := Scheme.Modules.unitObj U.toScheme)
    eM.hom eN.hom Z x y

private theorem overTrivialization_tensor_one_coefficient
    {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (eM : M.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme)
    (eN : N.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme) :
    let eT := Scheme.Modules.overTrivializationOfRestrictIso (M ⊗ N) U
      (restrictMonoidalTensorIso U.ι M N ≪≫
        (eM ⊗ᵢ eN) ≪≫ unitObjTensorIso U.toScheme)
    eT.hom.val.app (.op (Over.mk (𝟙 U)))
        (tensorSection M N U
          (overTrivializationSection M U
            (Scheme.Modules.overTrivializationOfRestrictIso M U eM) 1)
          (overTrivializationSection N U
            (Scheme.Modules.overTrivializationOfRestrictIso N U eN) 1)) =
      (show Γ(X, U) from 1) := by
  dsimp only
  apply Scheme.Modules.terminal_apply_eq_of_overEquivT
  dsimp only
  simp only [Scheme.Modules.overTrivializationOfRestrictIso,
    Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom]
  change _ = (X.ringCatSheaf.over U).obj.map _ 1
  rw [map_one]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  change (restrictMonoidalTensorIso U.ι M N ≪≫
      (eM ⊗ᵢ eN) ≪≫ unitObjTensorIso U.toScheme).hom.val.app
        (.op (U.ι ⁻¹ᵁ U)) _ =
    (show Γ(U.toScheme, U.ι ⁻¹ᵁ U) from 1)
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [restrictMonoidalTensorIso_localModuleSection]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  simp only [MonoidalCategory.tensorIso_hom]
  let Z := U.ι ⁻¹ᵁ U
  let xM := ((Scheme.Modules.overFunctorEquiv U).app M).hom.val.app (.op Z)
    (Scheme.Modules.localModuleSection M U Z
      (overTrivializationSection M U
        (Scheme.Modules.overTrivializationOfRestrictIso M U eM) 1))
  let xN := ((Scheme.Modules.overFunctorEquiv U).app N).hom.val.app (.op Z)
    (Scheme.Modules.localModuleSection N U Z
      (overTrivializationSection N U
        (Scheme.Modules.overTrivializationOfRestrictIso N U eN) 1))
  change (unitObjTensorIso U.toScheme).hom.val.app (.op Z)
      ((eM.hom ⊗ₘ eN.hom).val.app (.op Z)
        (tensorSection ((Scheme.Modules.restrictFunctor U.ι).obj M)
          ((Scheme.Modules.restrictFunctor U.ι).obj N) Z xM xN)) =
    (show Γ(U.toScheme, Z) from 1)
  have hmap := tensorSection_map_restrictIso M N U eM eN Z xM xN
  have hmap' := congrArg
    (fun q ↦ (unitObjTensorIso U.toScheme).hom.val.app (.op Z) q) hmap
  refine hmap'.trans ?_
  have hxM : eM.hom.val.app (.op Z) xM =
      (show Γ(U.toScheme, Z) from 1) := by
    dsimp only [Z, xM]
    exact overTrivializationOfRestrictIso_local_one M U eM
  have hxN : eN.hom.val.app (.op Z) xN =
      (show Γ(U.toScheme, Z) from 1) := by
    dsimp only [Z, xN]
    exact overTrivializationOfRestrictIso_local_one N U eN
  rw [hxM, hxN]
  rw [unitObjTensorIso_hom_tensorSection, one_mul]

/-- The coefficient-one section in the tensor-product trivialization is the
pure tensor of the two coefficient-one frame sections. -/
theorem overTrivializationSection_tensor_one
    {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (eM : M.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme)
    (eN : N.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme) :
    overTrivializationSection (M ⊗ N) U
        (Scheme.Modules.overTrivializationOfRestrictIso (M ⊗ N) U
          (restrictMonoidalTensorIso U.ι M N ≪≫
            (eM ⊗ᵢ eN) ≪≫ unitObjTensorIso U.toScheme)) 1 =
      tensorSection M N U
        (overTrivializationSection M U
          (Scheme.Modules.overTrivializationOfRestrictIso M U eM) 1)
        (overTrivializationSection N U
          (Scheme.Modules.overTrivializationOfRestrictIso N U eN) 1) := by
  let eT := Scheme.Modules.overTrivializationOfRestrictIso (M ⊗ N) U
    (restrictMonoidalTensorIso U.ι M N ≪≫
      (eM ⊗ᵢ eN) ≪≫ unitObjTensorIso U.toScheme)
  apply overTrivialization_hom_app_injective (M ⊗ N) U eT
  rw [overTrivializationSection_coefficient]
  exact (overTrivialization_tensor_one_coefficient M N U eM eN).symm

end ModularCurves
