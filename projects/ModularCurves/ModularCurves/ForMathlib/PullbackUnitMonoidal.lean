/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.PullbackTensorGeneral

/-!
# The monoidal pullback unit is the structure-sheaf pullback

The monoidal structure on pullback is descended through sheafification, whereas
`pullbackUnitIso` is defined by the pullback-pushforward adjunction. This file proves
that the two canonical unit comparisons agree. The proof compares their transposes
through the composite sheafification and pullback adjunctions.
-/

open AlgebraicGeometry CategoryTheory MonoidalCategory SheafOfModules
  TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

noncomputable local instance rawPresheafMonoidalCategoryStruct (Z : Scheme.{u}) :
    MonoidalCategoryStruct
      (_root_.PresheafOfModules Z.ringCatSheaf.obj) := by
  change MonoidalCategoryStruct
    (_root_.PresheafOfModules (Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
  infer_instance

noncomputable local instance rawPresheafMonoidalCategory (Z : Scheme.{u}) :
    MonoidalCategory
      (_root_.PresheafOfModules Z.ringCatSheaf.obj) := by
  change MonoidalCategory
    (_root_.PresheafOfModules (Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
  infer_instance

private noncomputable abbrev schemePresheafPullback (f : Y ⟶ X) :
    X.PresheafOfModules ⥤ Y.PresheafOfModules :=
  PresheafOfModules.pullback
    (_root_.PresheafOfModules.schemeRingPresheafHom f)

private noncomputable abbrev schemePresheafPushforward (f : Y ⟶ X) :
    Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  PresheafOfModules.pushforward
    (_root_.PresheafOfModules.schemeRingPresheafHom f)

private noncomputable def presheafPullbackUnitHom (f : Y ⟶ X) :
    (schemePresheafPullback f).obj
        (PresheafOfModules.unit X.ringCatSheaf.obj) ⟶
      PresheafOfModules.unit Y.ringCatSheaf.obj := by
  letI : (schemePresheafPullback f).OplaxMonoidal :=
    _root_.PresheafOfModules.pullbackOplaxMonoidal
      (_root_.PresheafOfModules.schemeRingPresheafHom f)
  exact Functor.OplaxMonoidal.η (schemePresheafPullback f)

private noncomputable def sheafifiedPresheafPullbackUnitHom (f : Y ⟶ X) :
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((schemePresheafPullback f).obj
          (PresheafOfModules.unit X.ringCatSheaf.obj)) ⟶
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        (PresheafOfModules.unit Y.ringCatSheaf.obj) :=
  (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
    (presheafPullbackUnitHom f)

private theorem sheafification_homEquiv_pullbackUnit
    (f : Y ⟶ X) :
    let shAdj := PresheafOfModules.sheafificationAdjunction
      (𝟙 Y.ringCatSheaf.obj)
    (shAdj.homEquiv _ _)
        (sheafifiedPresheafPullbackUnitHom f ≫
          (sheafifyValIso (unitObj Y)).hom) =
      presheafPullbackUnitHom f := by
  let shAdj := PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)
  have hcounit : (shAdj.homEquiv
      (PresheafOfModules.unit Y.ringCatSheaf.obj) (unitObj Y))
      ((sheafifyValIso (unitObj Y)).hom) =
      𝟙 (PresheafOfModules.unit Y.ringCatSheaf.obj) := by
    change (shAdj.homEquiv
      (PresheafOfModules.unit Y.ringCatSheaf.obj) (unitObj Y))
      (shAdj.counit.app (unitObj Y)) = _
    rw [← Adjunction.homEquiv_symm_id shAdj (unitObj Y)]
    exact Equiv.apply_symm_apply _ _
  dsimp only [sheafifiedPresheafPullbackUnitHom]
  rw [Adjunction.homEquiv_naturality_left]
  rw [hcounit]
  exact Category.comp_id _

private theorem presheafPullback_homEquiv_unit
    (f : Y ⟶ X) :
  let φ := _root_.PresheafOfModules.schemeRingPresheafHom f
  let pbAdj : schemePresheafPullback f ⊣ schemePresheafPushforward f :=
    PresheafOfModules.pullbackPushforwardAdjunction φ
  (pbAdj.homEquiv _ _) (presheafPullbackUnitHom f) =
      (SheafOfModules.unitToPushforwardObjUnit
        f.toRingCatSheafHom).val := by
  let φ := _root_.PresheafOfModules.schemeRingPresheafHom f
  let pbAdj : schemePresheafPullback f ⊣ schemePresheafPushforward f :=
    PresheafOfModules.pullbackPushforwardAdjunction φ
  letI : (_root_.PresheafOfModules.pushforwardFactored φ).LaxMonoidal :=
    _root_.PresheafOfModules.pushforwardFactoredLaxMonoidal φ
  letI : (schemePresheafPullback f).OplaxMonoidal :=
    _root_.PresheafOfModules.pullbackOplaxMonoidal φ
  change (pbAdj.homEquiv _ _)
    (((_root_.PresheafOfModules.pullbackPushforwardFactoredAdjunction φ).homEquiv _ _).symm
      (Functor.LaxMonoidal.ε
        (_root_.PresheafOfModules.pushforwardFactored φ))) = _
  rw [_root_.PresheafOfModules.pullbackPushforwardFactoredAdjunction_eq]
  change ((PresheafOfModules.pullbackPushforwardAdjunction φ).homEquiv _ _)
    (((PresheafOfModules.pullbackPushforwardAdjunction φ).homEquiv _ _).symm
      (Functor.LaxMonoidal.ε
        (_root_.PresheafOfModules.pushforwardFactored φ))) = _
  rw [Equiv.apply_symm_apply]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  rfl

private theorem compositePullback_homEquiv_unit (f : Y ⟶ X) :
    let shAdj := PresheafOfModules.sheafificationAdjunction
      (𝟙 Y.ringCatSheaf.obj)
    let pbAdj := PresheafOfModules.pullbackPushforwardAdjunction
      (_root_.PresheafOfModules.schemeRingPresheafHom f)
    let adj := pbAdj.comp shAdj
    (adj.homEquiv (PresheafOfModules.unit X.ringCatSheaf.obj) (unitObj Y))
        (sheafifiedPresheafPullbackUnitHom f ≫
          (sheafifyValIso (unitObj Y)).hom) =
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val := by
  let shAdj := PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)
  let pbAdj := PresheafOfModules.pullbackPushforwardAdjunction
    (_root_.PresheafOfModules.schemeRingPresheafHom f)
  let adj := pbAdj.comp shAdj
  have hsheaf := sheafification_homEquiv_pullbackUnit f
  have hpb := presheafPullback_homEquiv_unit f
  change (pbAdj.homEquiv _ _)
      ((shAdj.homEquiv _ _)
        (sheafifiedPresheafPullbackUnitHom f ≫
          (sheafifyValIso (unitObj Y)).hom)) = _
  exact (congrArg (pbAdj.homEquiv _ _) hsheaf).trans hpb

private theorem compositeSheafPullback_homEquiv_unit (f : Y ⟶ X) :
    let shAdj := PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)
    let pbAdj := SheafOfModules.pullbackPushforwardAdjunction
      f.toRingCatSheafHom
    let adj := shAdj.comp pbAdj
    (adj.homEquiv (PresheafOfModules.unit X.ringCatSheaf.obj) (unitObj Y))
        ((Scheme.Modules.pullback f).map
            (sheafifyValIso (unitObj X)).hom ≫
          (pullbackUnitIso f).hom) =
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val := by
  let shAdj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let pbAdj := SheafOfModules.pullbackPushforwardAdjunction
    f.toRingCatSheafHom
  let adj := shAdj.comp pbAdj
  have hright : (pbAdj.homEquiv (unitObj X) (unitObj Y))
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
    dsimp only [pbAdj, unitObj]
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      f.toRingCatSheafHom
  have hcounit : (shAdj.homEquiv
      (PresheafOfModules.unit X.ringCatSheaf.obj) (unitObj X))
      ((sheafifyValIso (unitObj X)).hom) =
      𝟙 (PresheafOfModules.unit X.ringCatSheaf.obj) := by
    change (shAdj.homEquiv
      (PresheafOfModules.unit X.ringCatSheaf.obj) (unitObj X))
      (shAdj.counit.app (unitObj X)) = _
    rw [← Adjunction.homEquiv_symm_id shAdj (unitObj X)]
    exact Equiv.apply_symm_apply _ _
  have hcounit' : (shAdj.homEquiv (unitObj X).val (unitObj X))
      (sheafifyValIso (unitObj X)).hom = 𝟙 (unitObj X).val :=
    hcounit
  have hpull := pbAdj.homEquiv_naturality_left
    (sheafifyValIso (unitObj X)).hom
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
  have hpull' : (pbAdj.homEquiv _ _)
      ((Scheme.Modules.pullback f).map
          (sheafifyValIso (unitObj X)).hom ≫
        SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) =
      (sheafifyValIso (unitObj X)).hom ≫
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    hpull.trans (congrArg
      (fun q => (sheafifyValIso (unitObj X)).hom ≫ q) hright)
  have hsheaf := shAdj.homEquiv_naturality_right
    (sheafifyValIso (unitObj X)).hom
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
  have hsheaf' : (shAdj.homEquiv _ _)
      ((sheafifyValIso (unitObj X)).hom ≫
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) =
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val := by
    refine hsheaf.trans ?_
    rw [hcounit']
    rfl
  change (shAdj.homEquiv _ _)
      ((pbAdj.homEquiv _ _)
        ((Scheme.Modules.pullback f).map
            (sheafifyValIso (unitObj X)).hom ≫
          SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)) = _
  exact (congrArg (shAdj.homEquiv _ _) hpull').trans hsheaf'

private theorem sheafificationCompPullback_unit (f : Y ⟶ X) :
    (SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).hom.app
          (PresheafOfModules.unit X.ringCatSheaf.obj) ≫
        sheafifiedPresheafPullbackUnitHom f ≫
        (sheafifyValIso (unitObj Y)).hom =
      (Scheme.Modules.pullback f).map
          (sheafifyValIso (unitObj X)).hom ≫
        (pullbackUnitIso f).hom := by
  let shAdjX := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let pbAdj := SheafOfModules.pullbackPushforwardAdjunction
    f.toRingCatSheafHom
  let adj₁ := shAdjX.comp pbAdj
  let shAdjY := PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)
  let prePbAdj := PresheafOfModules.pullbackPushforwardAdjunction
    (_root_.PresheafOfModules.schemeRingPresheafHom f)
  let adj₂ := prePbAdj.comp shAdjY
  have huniq := Adjunction.homEquiv_leftAdjointUniq_hom_app adj₁ adj₂
    (PresheafOfModules.unit X.ringCatSheaf.obj)
  change (adj₁.homEquiv _ _)
      ((SheafOfModules.sheafificationCompPullback
        f.toRingCatSheafHom).hom.app
          (PresheafOfModules.unit X.ringCatSheaf.obj)) =
    adj₂.unit.app (PresheafOfModules.unit X.ringCatSheaf.obj) at huniq
  have htranspose := (Adjunction.homEquiv_unit adj₂ _ _
    (sheafifiedPresheafPullbackUnitHom f ≫
      (sheafifyValIso (unitObj Y)).hom)).symm
  apply (adj₁.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, huniq]
  refine htranspose.trans ?_
  rw [compositePullback_homEquiv_unit f]
  exact (compositeSheafPullback_homEquiv_unit f).symm

noncomputable local instance unitPullbackModuleMonoidalCategory (Z : Scheme.{u}) :
    MonoidalCategory Z.Modules :=
  Scheme.Modules.monoidalCategory Z

noncomputable local instance unitPullbackSheafificationLocalization (Z : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).IsLocalization
      (PresheafOfModules.sheafificationW (𝟙 Z.ringCatSheaf.obj)) := by
  change (PresheafOfModules.sheafification
      (𝟙 (⟨Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
        Z.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat Z).obj)).IsLocalization
    (PresheafOfModules.sheafificationW
      (𝟙 (⟨Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
        Z.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat Z).obj))
  infer_instance

noncomputable local instance unitPullbackSheafificationWMonoidal (Z : Scheme.{u}) :
    (PresheafOfModules.sheafificationW
      (𝟙 Z.ringCatSheaf.obj)).IsMonoidal := by
  change (PresheafOfModules.sheafificationW
    (𝟙 (⟨Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
      Z.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat Z).obj)).IsMonoidal
  infer_instance

private abbrev unitPullbackRingSheaf (Z : Scheme.{u}) :=
  (⟨Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
    Z.ringCatSheaf.property⟩ : Sheaf _ RingCat.{u})

noncomputable local instance unitPullbackExactModuleMonoidalCategory (Z : Scheme.{u}) :
    MonoidalCategory (SheafOfModules (unitPullbackRingSheaf Z)) := by
  change MonoidalCategory Z.Modules
  exact unitPullbackModuleMonoidalCategory Z

private noncomputable abbrev unitPullbackSheafification (Z : Scheme.{u}) :=
  PresheafOfModules.sheafification (𝟙 (unitPullbackRingSheaf Z).obj)

private noncomputable abbrev unitPullbackSheafificationW (Z : Scheme.{u}) :=
  PresheafOfModules.sheafificationW (𝟙 (unitPullbackRingSheaf Z).obj)

private noncomputable abbrev unitPullbackLocalizedSheafification (Z : Scheme.{u}) :=
  Localization.Monoidal.toMonoidalCategory
    (L := unitPullbackSheafification Z) (W := unitPullbackSheafificationW Z) (Iso.refl _)

private noncomputable abbrev unitPullbackPresheafPullback (f : Y ⟶ X) :=
  PresheafOfModules.pullback
    (_root_.PresheafOfModules.schemeRingPresheafHom f)

private noncomputable abbrev unitPullbackSheafHom (f : Y ⟶ X) :=
  (⟨_root_.PresheafOfModules.schemeRingPresheafHom f⟩ : unitPullbackRingSheaf X ⟶
    ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj (unitPullbackRingSheaf Y))

private noncomputable abbrev unitPullbackSheafPullback (f : Y ⟶ X) :=
  SheafOfModules.pullback (unitPullbackSheafHom f)

@[implicit_reducible]
private noncomputable def unitPullbackSheafPullbackLifting (f : Y ⟶ X) :
    Localization.Lifting (unitPullbackLocalizedSheafification X)
      (unitPullbackSheafificationW X)
      (unitPullbackPresheafPullback f ⋙ unitPullbackLocalizedSheafification Y)
      (unitPullbackSheafPullback f) :=
  ⟨SheafOfModules.sheafificationCompPullback (unitPullbackSheafHom f)⟩

private theorem unitPullbackLocalizedSheafification_ε (Z : Scheme.{u}) :
    Functor.LaxMonoidal.ε (unitPullbackLocalizedSheafification Z) = 𝟙 _ := by
  rfl

private theorem unitPullbackLocalizedSheafification_η (Z : Scheme.{u}) :
    Functor.OplaxMonoidal.η (unitPullbackLocalizedSheafification Z) = 𝟙 _ := by
  rfl

private theorem unitPullbackSheafPullbackLifting_iso (f : Y ⟶ X) :
    letI : Localization.Lifting (unitPullbackLocalizedSheafification X)
      (unitPullbackSheafificationW X)
      (unitPullbackPresheafPullback f ⋙ unitPullbackLocalizedSheafification Y)
      (unitPullbackSheafPullback f) := unitPullbackSheafPullbackLifting f
    Localization.Lifting.iso (unitPullbackLocalizedSheafification X)
      (unitPullbackSheafificationW X)
      (unitPullbackPresheafPullback f ⋙ unitPullbackLocalizedSheafification Y)
      (unitPullbackSheafPullback f) =
    SheafOfModules.sheafificationCompPullback (unitPullbackSheafHom f) := by
  rfl

noncomputable local instance unitPullbackPullbackMonoidal (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Monoidal :=
  Scheme.Modules.pullbackMonoidal f

private theorem pullback_monoidalUnitObjIso_hom (f : Y ⟶ X) :
    Functor.OplaxMonoidal.η (Scheme.Modules.pullback f) ≫
        (sheafifyValIso (unitObj Y)).hom =
      (Scheme.Modules.pullback f).map
          (sheafifyValIso (unitObj X)).hom ≫
        (pullbackUnitIso f).hom := by
  letI pF : (unitPullbackPresheafPullback f).Monoidal :=
    _root_.PresheafOfModules.pullbackMonoidal f
  letI pgF : (unitPullbackPresheafPullback f ⋙
      unitPullbackLocalizedSheafification Y).Monoidal := inferInstance
  letI liftF : Localization.Lifting (unitPullbackLocalizedSheafification X)
      (unitPullbackSheafificationW X)
      (unitPullbackPresheafPullback f ⋙ unitPullbackLocalizedSheafification Y)
      (unitPullbackSheafPullback f) := unitPullbackSheafPullbackLifting f
  have hepsilon := @Localization.Monoidal.functorMonoidalOfComp_ε
    _ _ _ _ _ _ _ _ _ (unitPullbackLocalizedSheafification X)
    (unitPullbackSheafificationW X) _ _ (unitPullbackSheafPullback f)
    (unitPullbackPresheafPullback f ⋙ unitPullbackLocalizedSheafification Y) pgF _ liftF
  change Functor.LaxMonoidal.ε (Scheme.Modules.pullback f) = _ at hepsilon
  apply (cancel_epi
    (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).hom).1
  change Functor.LaxMonoidal.ε (Scheme.Modules.pullback f) ≫
        Functor.OplaxMonoidal.η (Scheme.Modules.pullback f) ≫
          (sheafifyValIso (unitObj Y)).hom =
    Functor.LaxMonoidal.ε (Scheme.Modules.pullback f) ≫
        (Scheme.Modules.pullback f).map
          (sheafifyValIso (unitObj X)).hom ≫
      (pullbackUnitIso f).hom
  slice_lhs 1 2 => rw [Functor.Monoidal.ε_η]
  rw [Category.id_comp]
  rw [hepsilon]
  let p := Functor.LaxMonoidal.ε
      (unitPullbackPresheafPullback f ⋙ unitPullbackLocalizedSheafification Y) ≫
    (Localization.Lifting.iso (unitPullbackLocalizedSheafification X)
      (unitPullbackSheafificationW X)
      (unitPullbackPresheafPullback f ⋙ unitPullbackLocalizedSheafification Y)
      (unitPullbackSheafPullback f)).inv.app
        (𝟙_ (_root_.PresheafOfModules (unitPullbackRingSheaf X).obj)) ≫
    (unitPullbackSheafPullback f).map
      (Functor.OplaxMonoidal.η (unitPullbackLocalizedSheafification X))
  change (sheafifyValIso (unitObj Y)).hom =
    p ≫ (Scheme.Modules.pullback f).map
        (sheafifyValIso (unitObj X)).hom ≫
      (pullbackUnitIso f).hom
  let q :=
    (SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).hom.app
          (PresheafOfModules.unit X.ringCatSheaf.obj) ≫
        sheafifiedPresheafPullbackUnitHom f ≫
        (sheafifyValIso (unitObj Y)).hom
  have hq : q = (Scheme.Modules.pullback f).map
          (sheafifyValIso (unitObj X)).hom ≫
        (pullbackUnitIso f).hom :=
    sheafificationCompPullback_unit f
  have hpq : p ≫ (Scheme.Modules.pullback f).map
          (sheafifyValIso (unitObj X)).hom ≫
        (pullbackUnitIso f).hom = p ≫ q := by
    rw [Category.assoc, hq]
    rfl
  rw [hpq]
  dsimp only [q]
  dsimp only [p]
  simp
  rw [unitPullbackLocalizedSheafification_ε]
  rw [unitPullbackLocalizedSheafification_η]
  rw [unitPullbackSheafPullbackLifting_iso]
  erw [Category.id_comp]
  have hmapId := (unitPullbackSheafPullback f).map_id
    ((unitPullbackLocalizedSheafification X).obj
      (𝟙_ (_root_.PresheafOfModules (unitPullbackRingSheaf X).obj)))
  erw [hmapId]
  erw [Category.id_comp]
  change (sheafifyValIso (unitObj Y)).hom =
    (unitPullbackLocalizedSheafification Y).map
        (Functor.LaxMonoidal.ε (unitPullbackPresheafPullback f)) ≫
      (SheafOfModules.sheafificationCompPullback
        (unitPullbackSheafHom f)).inv.app
          (PresheafOfModules.unit X.ringCatSheaf.obj) ≫
      (SheafOfModules.sheafificationCompPullback
        (unitPullbackSheafHom f)).hom.app
          (PresheafOfModules.unit X.ringCatSheaf.obj) ≫
      (unitPullbackLocalizedSheafification Y).map
        (Functor.OplaxMonoidal.η (unitPullbackPresheafPullback f)) ≫
      (sheafifyValIso (unitObj Y)).hom
  erw [Iso.inv_hom_id_app_assoc]
  have hεη : (unitPullbackLocalizedSheafification Y).map
        (Functor.LaxMonoidal.ε (unitPullbackPresheafPullback f)) ≫
      (unitPullbackLocalizedSheafification Y).map
        (Functor.OplaxMonoidal.η (unitPullbackPresheafPullback f)) = 𝟙 _ :=
    Functor.Monoidal.map_ε_η (unitPullbackPresheafPullback f)
      (unitPullbackLocalizedSheafification Y)
  symm
  calc
    _ = ((unitPullbackLocalizedSheafification Y).map
          (Functor.LaxMonoidal.ε (unitPullbackPresheafPullback f)) ≫
        (unitPullbackLocalizedSheafification Y).map
          (Functor.OplaxMonoidal.η (unitPullbackPresheafPullback f))) ≫
        (sheafifyValIso (unitObj Y)).hom :=
      (Category.assoc _ _ _).symm
    _ = (𝟙 _) ≫ (sheafifyValIso (unitObj Y)).hom :=
      congrArg (fun k => k ≫ (sheafifyValIso (unitObj Y)).hom) hεη
    _ = _ := Category.id_comp _

/-- The monoidal unit comparison of sheaf pullback agrees with the canonical
pullback isomorphism for the structure sheaf. -/
theorem pullback_monoidalUnitObjIso (f : Y ⟶ X) :
    (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).symm ≪≫
        sheafifyValIso (unitObj Y) =
      (Scheme.Modules.pullback f).mapIso (sheafifyValIso (unitObj X)) ≪≫
        pullbackUnitIso f := by
  apply Iso.ext
  exact pullback_monoidalUnitObjIso_hom f

end AlgebraicGeometry.Scheme.Modules
