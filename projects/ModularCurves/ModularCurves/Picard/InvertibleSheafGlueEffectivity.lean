import ModularCurves.Picard.InvertibleSheafGlueDataDescent
import ModularCurves.Picard.DualPullback.OpenAdjunction
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import ModularCurves.ForMathlib.SchemeModuleRestrictLimits

/-!
# Effectivity of affine-intersection line-bundle descent

This file glues the chartwise unit modules attached to an
`AffineIntersectionUnitCocycle`. The glued module is the usual Cech equalizer of
the chart extensions, with one overlap map twisted by the transition isomorphism.
-/

universe u u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

private noncomputable def restrictPushforwardPresheafIsoOfIsPullback
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) (M : X.Modules) :
    (toPresheafOfModules V).obj
        ((restrictFunctor iV).obj ((pushforward f).obj M)) ≅
      (toPresheafOfModules V).obj
        ((pushforward f').obj ((restrictFunctor iU).obj M)) := by
  refine PresheafOfModules.isoMk (fun W ↦ ?_) ?_
  · let h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W.unop
    let e := M.presheaf.mapIso (eqToIso h).op
    refine ModuleCat.isoMk e ?_
    intro r
    ext x
    let eR : Γ(X, f ⁻¹ᵁ iV ''ᵁ W.unop) ≅ Γ(U, f' ⁻¹ᵁ W.unop) :=
      X.presheaf.mapIso (eqToIso h).op ≪≫ iU.appIso _
    have hring : (iV.appIso W.unop).inv ≫ f.app _ = f'.app W.unop ≫ eR.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
      simp only [Scheme.Hom.app_eq_appLE, Iso.trans_hom, Functor.mapIso_hom,
        Iso.op_hom, eqToIso.hom, eqToHom_op, Scheme.Hom.appIso_hom',
        Scheme.Hom.map_appLE, eR, Scheme.Hom.appLE_comp_appLE, H.w]
    have hring' : (iV.appIso W.unop).inv ≫ f.app _ ≫ eR.hom =
        f'.app W.unop := by
      rw [← Category.assoc, hring]
      simp
    have hring'' : f'.app W.unop ≫ (iU.appIso (f' ⁻¹ᵁ W.unop)).inv =
        (iV.appIso W.unop).inv ≫ f.app _ ≫
          (X.presheaf.mapIso (eqToIso h).op).hom := by
      rw [← hring']
      simp only [eR, Iso.trans_hom, Category.assoc]
      rw [Iso.hom_inv_id, Category.comp_id]
    have hring''' : f'.app W.unop ≫ (iU.appIso (f' ⁻¹ᵁ W.unop)).inv =
        (iV.appIso W.unop).inv ≫ f.app _ ≫
          X.presheaf.map (eqToHom h).op := by
      simpa only [Functor.mapIso_hom, Iso.op_hom, eqToIso.hom] using hring''
    have hr' : (iU.appIso (f' ⁻¹ᵁ W.unop)).inv ((f'.app W.unop).hom r) =
        (X.presheaf.map (eqToHom h).op).hom
          ((f.app (iV ''ᵁ W.unop)).hom ((iV.appIso W.unop).inv r)) := by
      have hr := ConcreteCategory.congr_hom hring''' r
      change (iU.appIso (f' ⁻¹ᵁ W.unop)).inv ((f'.app W.unop).hom r) =
        (X.presheaf.map (eqToHom h).op).hom
          ((f.app (iV ''ᵁ W.unop)).hom ((iV.appIso W.unop).inv r)) at hr
      exact hr
    let x' : M.val.obj (.op (f ⁻¹ᵁ iV ''ᵁ W.unop)) := x
    let rU : Γ(X, iU ''ᵁ (f' ⁻¹ᵁ W.unop)) :=
      (iU.appIso (f' ⁻¹ᵁ W.unop)).inv ((f'.app W.unop).hom r)
    let rX : Γ(X, f ⁻¹ᵁ iV ''ᵁ W.unop) :=
      (f.app (iV ''ᵁ W.unop)).hom ((iV.appIso W.unop).inv r)
    change SMul.smul rU
        (e.hom x' : M.val.obj (.op (iU ''ᵁ (f' ⁻¹ᵁ W.unop)))) =
      e.hom (SMul.smul rX x')
    rw [show rU = (X.presheaf.map (eqToHom h).op).hom rX from hr']
    exact ((M.val.map (eqToHom h).op).hom.map_smul rX x').symm
  · intro W W' g
    apply ModuleCat.hom_ext
    ext x
    let x' : Γ(M, f ⁻¹ᵁ iV ''ᵁ W.unop) := x
    change M.presheaf.map _ (M.presheaf.map _ x') =
      M.presheaf.map _ (M.presheaf.map _ x')
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) x'

private noncomputable def restrictPushforwardIsoOfIsPullbackApp
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) (M : X.Modules) :
    (restrictFunctor iV).obj ((pushforward f).obj M) ≅
      (pushforward f').obj ((restrictFunctor iU).obj M) :=
  (fullyFaithfulToPresheafOfModules).preimageIso
    (restrictPushforwardPresheafIsoOfIsPullback f f' iU iV H M)

private noncomputable def restrictPushforwardIsoOfIsPullback
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) :
    pushforward f ⋙ restrictFunctor iV ≅
      restrictFunctor iU ⋙ pushforward f' :=
  NatIso.ofComponents
    (fun M ↦ restrictPushforwardIsoOfIsPullbackApp f f' iU iV H M)
    (by
      intro M N q
      apply (fullyFaithfulToPresheafOfModules).map_injective
      apply PresheafOfModules.hom_ext
      intro W
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      let h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W.unop
      change (N.val.map (eqToHom h).op).hom ((q.val.app _).hom x) =
        (q.val.app _).hom
          (show M.val.obj (.op (iU ''ᵁ (f' ⁻¹ᵁ W.unop))) from
            (M.val.map (eqToHom h).op).hom x)
      exact ConcreteCategory.congr_hom (q.val.naturality (eqToHom h).op).symm x)

private theorem restrictPushforwardIsoOfIsPullback_hom
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) (M : X.Modules) :
    (toPresheafOfModules V).map
        ((restrictPushforwardIsoOfIsPullback f f' iU iV H).hom.app M) =
      (restrictPushforwardPresheafIsoOfIsPullback
        f f' iU iV H M).hom := by
  change (toPresheafOfModules V).map
      (fullyFaithfulToPresheafOfModules.preimage
        (restrictPushforwardPresheafIsoOfIsPullback
          f f' iU iV H M).hom) = _
  exact (fullyFaithfulToPresheafOfModules (X := V)).map_preimage _

private theorem restrictPushforwardIsoOfIsPullback_hom_app
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) (M : X.Modules) (W : V.Opens) :
    ((restrictPushforwardIsoOfIsPullback f f' iU iV H).hom.app M).val.app (.op W) =
      (restrictPushforwardPresheafIsoOfIsPullback
        f f' iU iV H M).hom.app (.op W) :=
  congrArg (fun q ↦ q.app (.op W))
    (restrictPushforwardIsoOfIsPullback_hom f f' iU iV H M)

private theorem restrictPushforwardIsoOfIsPullback_hom_app_apply
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) (M : X.Modules) (W : V.Opens)
    (x : Γ((restrictFunctor iV).obj ((pushforward f).obj M), W)) :
    (((restrictPushforwardIsoOfIsPullback f f' iU iV H).hom.app M).app W).hom x =
      ((restrictPushforwardPresheafIsoOfIsPullback
        f f' iU iV H M).hom.app (.op W)).hom x := by
  change (((restrictPushforwardIsoOfIsPullback
    f f' iU iV H).hom.app M).val.app (.op W)).hom x = _
  rw [restrictPushforwardIsoOfIsPullback_hom_app]
  rfl

/-- In a pullback square whose vertical maps are open immersions, restricting
the pushforward of the structure sheaf agrees with pushing forward the
structure sheaf from the pullback. -/
noncomputable def restrictPushforwardUnitIsoOfIsPullback
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) :
    (restrictFunctor iV).obj ((pushforward f).obj (unitObj X)) ≅
      (pushforward f').obj (unitObj U) :=
  (restrictPushforwardIsoOfIsPullback f f' iU iV H).app (unitObj X) ≪≫
    (pushforward f').mapIso (restrictUnitIso iU)

private theorem restrictPushforwardUnitIsoOfIsPullback_eq
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) :
    restrictPushforwardUnitIsoOfIsPullback f f' iU iV H =
      (restrictPushforwardIsoOfIsPullback f f' iU iV H).app (unitObj X) ≪≫
        (pushforward f').mapIso (restrictUnitIso iU) :=
  rfl

private theorem restrictUnitIso_inv_unitToPushforward
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) :
    (restrictUnitIso iV).inv ≫
        (restrictFunctor iV).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom ≫
        (restrictPushforwardUnitIsoOfIsPullback f f' iU iV H).inv := by
  let e := restrictPushforwardUnitIsoOfIsPullback f f' iU iV H
  apply (cancel_mono e.hom).1
  change (((restrictUnitIso iV).inv ≫
      (restrictFunctor iV).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ≫
      e.hom) =
    ((SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom ≫
      e.inv) ≫ e.hom)
  have hright :
      (SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom ≫
          e.inv) ≫ e.hom =
        SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom := by
    let p := SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom
    have hassoc : (p ≫ e.inv) ≫ e.hom = p ≫ (e.inv ≫ e.hom) :=
      Category.assoc p e.inv e.hom
    have hcancel : p ≫ (e.inv ≫ e.hom) = p ≫ 𝟙 _ :=
      congrArg (fun q ↦ p ≫ q) e.inv_hom_id
    have hid : p ≫ 𝟙 _ = p := Category.comp_id p
    exact hassoc.trans (hcancel.trans hid)
  refine Eq.trans ?_ hright.symm
  apply (fullyFaithfulToPresheafOfModules).map_injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  erw [sheafOfModules_comp_app_apply]
  erw [sheafOfModules_comp_app_apply]
  have hrestrict :
      ((restrictUnitIso iV).inv.val.app W).hom' x =
        (iV.appIso W.unop).inv x := by
    simpa using restrictUnitIso_inv_app_applyP iV W.unop x
  change (e.hom.val.app W).hom'
      ((((restrictFunctor iV).map
        (SheafOfModules.unitToPushforwardObjUnit
          f.toRingCatSheafHom)).val.app W).hom'
        (((restrictUnitIso iV).inv.val.app W).hom' x)) = _
  rw [hrestrict]
  have hmap :
      (((restrictFunctor iV).map
        (SheafOfModules.unitToPushforwardObjUnit
          f.toRingCatSheafHom)).val.app W).hom'
          ((iV.appIso W.unop).inv x) =
        ((SheafOfModules.unitToPushforwardObjUnit
          f.toRingCatSheafHom).val.app
            (iV.opensFunctor.op.obj W)).hom'
          ((iV.appIso W.unop).inv x) := by
    exact restrictFunctor_map_app_apply iV
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
      W ((iV.appIso W.unop).inv x)
  rw [hmap]
  change (e.hom.val.app W).hom'
      (((SheafOfModules.unitToPushforwardObjUnit
        f.toRingCatSheafHom).val.app
          (iV.opensFunctor.op.obj W)).hom'
        ((iV.appIso W.unop).inv x)) =
    ((SheafOfModules.unitToPushforwardObjUnit
      f'.toRingCatSheafHom).val.app W).hom' x
  have hunitLeft :=
    SheafOfModules.unitToPushforwardObjUnit_val_app_apply
      f.toRingCatSheafHom (X := iV.opensFunctor.op.obj W)
        ((iV.appIso W.unop).inv x)
  have hunitRight :=
    SheafOfModules.unitToPushforwardObjUnit_val_app_apply
      f'.toRingCatSheafHom (X := W) x
  have hunitLeftMapped :
      (e.hom.val.app W).hom'
          (((SheafOfModules.unitToPushforwardObjUnit
            f.toRingCatSheafHom).val.app
              (iV.opensFunctor.op.obj W)).hom'
            ((iV.appIso W.unop).inv x)) =
        (e.hom.val.app W).hom'
        ((f.toRingCatSheafHom.hom.app
          (iV.opensFunctor.op.obj W)).hom
            ((iV.appIso W.unop).inv x)) :=
    congrArg (fun y ↦ (e.hom.val.app W).hom' y) hunitLeft
  have hbaseChange :
      (e.hom.val.app W).hom'
          ((f.toRingCatSheafHom.hom.app
            (iV.opensFunctor.op.obj W)).hom
              ((iV.appIso W.unop).inv x)) =
        (f'.toRingCatSheafHom.hom.app W).hom x := by
    let h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      H W.unop
    let eR : Γ(X, f ⁻¹ᵁ iV ''ᵁ W.unop) ≅
        Γ(U, f' ⁻¹ᵁ W.unop) :=
      X.presheaf.mapIso (eqToIso h).op ≪≫ iU.appIso _
    change eR.hom
        ((f.app (iV ''ᵁ W.unop)).hom
          ((iV.appIso W.unop).inv x)) =
      (f'.app W.unop).hom x
    have hring : (iV.appIso W.unop).inv ≫
        f.app (iV ''ᵁ W.unop) =
      f'.app W.unop ≫ eR.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
      simp only [Scheme.Hom.app_eq_appLE, Iso.trans_hom,
        Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, eqToHom_op,
        Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, eR,
        Scheme.Hom.appLE_comp_appLE, H.w]
    have hx :
        (f.app (iV ''ᵁ W.unop)).hom ((iV.appIso W.unop).inv x) =
          eR.inv ((f'.app W.unop).hom x) :=
      ConcreteCategory.congr_hom hring x
    exact (congrArg eR.hom hx).trans
      (Iso.inv_hom_id_apply eR ((f'.app W.unop).hom x))
  exact hunitLeftMapped.trans (hbaseChange.trans hunitRight.symm)

private theorem pullbackPushforwardAdjunction_comp_homEquiv
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (M : C.Modules) (N : B.Modules) (P : A.Modules)
    (a : (pullback g).obj M ⟶ N)
    (b : (pullback f).obj N ⟶ P) :
    (((pullbackPushforwardAdjunction g).comp
      (pullbackPushforwardAdjunction f)).homEquiv M P)
        ((pullback f).map a ≫ b) =
      (pullbackPushforwardAdjunction g).homEquiv M N a ≫
        (pushforward g).map
          ((pullbackPushforwardAdjunction f).homEquiv N P b) := by
  rw [Adjunction.comp_homEquiv]
  change (pullbackPushforwardAdjunction g).homEquiv _ _
      ((pullbackPushforwardAdjunction f).homEquiv _ _
        ((pullback f).map a ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_right]

private def pullbackPushforwardCompAdjunction
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    pullback g ⋙ pullback f ⊣ pushforward f ⋙ pushforward g :=
  (pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)

private noncomputable def pullbackCompCongrIso
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (h' : A ⟶ C) (h : f ≫ g = h') :
    pullback g ⋙ pullback f ≅ pullback h' :=
  pullbackComp f g ≪≫ pullbackCongr h

private noncomputable def pushforwardCompCongrIso
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (h' : A ⟶ C) (h : f ≫ g = h') :
    pushforward f ⋙ pushforward g ≅ pushforward h' :=
  pushforwardComp f g ≪≫ pushforwardCongr h

private theorem conjugateEquiv_pullbackCompCongrIso_hom
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (h' : A ⟶ C) (h : f ≫ g = h') :
    conjugateEquiv (pullbackPushforwardAdjunction h')
        (pullbackPushforwardCompAdjunction f g)
        (pullbackCompCongrIso f g h' h).hom =
      (pushforwardCompCongrIso f g h' h).inv := by
  let adjfg := pullbackPushforwardAdjunction (f ≫ g)
  change conjugateEquiv (pullbackPushforwardAdjunction h')
      (pullbackPushforwardCompAdjunction f g)
      ((pullbackComp f g).hom ≫ (pullbackCongr h).hom) = _
  have hcongr : conjugateEquiv (pullbackPushforwardAdjunction h') adjfg
      (pullbackCongr h).hom = (pushforwardCongr h).inv := by
    exact conjugateEquiv_pullbackCongr_homT h
  have hcomp : conjugateEquiv adjfg
      (pullbackPushforwardCompAdjunction f g) (pullbackComp f g).hom =
        (pushforwardComp f g).inv := by
    exact conjugateEquiv_pullbackComp_hom f g
  rw [← conjugateEquiv_comp
    (pullbackPushforwardAdjunction h') adjfg
    (pullbackPushforwardCompAdjunction f g)]
  rw [hcongr, hcomp]
  rfl

private theorem homEquiv_comp_conjugate_iso_cancel
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) (e : R₂ ≅ R₁)
    (h : conjugateEquiv adj₁ adj₂ α = e.inv)
    {X : C} {Y : D} (p : L₁.obj X ⟶ Y) :
    adj₂.homEquiv X Y (α.app X ≫ p) ≫ e.hom.app Y =
      adj₁.homEquiv X Y p := by
  have hmate := homEquiv_comp_conjugate adj₁ adj₂ α p
  rw [h] at hmate
  calc
    _ = (adj₁.homEquiv X Y p ≫ e.inv.app Y) ≫ e.hom.app Y :=
      congrArg (fun q ↦ q ≫ e.hom.app Y) hmate
    _ = adj₁.homEquiv X Y p ≫
        (e.inv.app Y ≫ e.hom.app Y) := Category.assoc _ _ _
    _ = adj₁.homEquiv X Y p ≫ 𝟙 _ := congrArg
      (fun q ↦ adj₁.homEquiv X Y p ≫ q) (e.app Y).inv_hom_id
    _ = _ := Category.comp_id _

private theorem homEquiv_comp_conjugate_iso_cancel_naturality
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) (e : R₂ ≅ R₁)
    (h : conjugateEquiv adj₁ adj₂ α = e.inv)
    {X : C} {Y Z : D} (p : L₁.obj X ⟶ Y) (q : Y ⟶ Z) :
    adj₂.homEquiv X Y (α.app X ≫ p) ≫ e.hom.app Y ≫ R₁.map q =
      adj₁.homEquiv X Z (p ≫ q) := by
  rw [← Category.assoc,
    homEquiv_comp_conjugate_iso_cancel adj₁ adj₂ α e h p]
  rw [Adjunction.homEquiv_naturality_right]

private theorem homEquiv_comp_conjugate_iso_cancel_of_comp_eq
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) (e : R₂ ≅ R₁)
    (h : conjugateEquiv adj₁ adj₂ α = e.inv)
    {X : C} {Y Z : D} (b : L₂.obj X ⟶ Y) (q : Y ⟶ Z)
    (p : L₁.obj X ⟶ Z) (hb : b ≫ q = α.app X ≫ p) :
    adj₂.homEquiv X Y b ≫ e.hom.app Y ≫ R₁.map q =
      adj₁.homEquiv X Z p := by
  rw [← e.hom.naturality q, ← Category.assoc]
  rw [← Adjunction.homEquiv_naturality_right, hb]
  exact homEquiv_comp_conjugate_iso_cancel adj₁ adj₂ α e h p

private theorem pullbackPushforwardAdjunction_homEquiv_compCongr_inv
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (h' : A ⟶ C) (h : f ≫ g = h')
    (M : C.Modules) (N : B.Modules) (P : A.Modules)
    (a : (pullback g).obj M ⟶ N) (b : (pullback f).obj N ⟶ P) :
    let compIso := pullbackCompCongrIso f g h' h
    let pushIso := pushforwardCompCongrIso f g h' h
    (pullbackPushforwardAdjunction h').homEquiv M P
        (compIso.inv.app M ≫ (pullback f).map a ≫ b) =
      (pullbackPushforwardAdjunction g).homEquiv M N a ≫
        (pushforward g).map
          ((pullbackPushforwardAdjunction f).homEquiv N P b) ≫
        pushIso.hom.app P := by
  dsimp only
  have hcancel := homEquiv_comp_conjugate_iso_cancel
    (pullbackPushforwardAdjunction h')
    (pullbackPushforwardCompAdjunction f g)
    (pullbackCompCongrIso f g h' h).hom
    (pushforwardCompCongrIso f g h' h)
    (conjugateEquiv_pullbackCompCongrIso_hom f g h' h)
    ((pullbackCompCongrIso f g h' h).inv.app M ≫
      (pullback f).map a ≫ b)
  have hcombine := pullbackPushforwardAdjunction_comp_homEquiv
    f g M N P a b
  simp only [Iso.hom_inv_id_app_assoc] at hcancel
  calc
    _ = (pullbackPushforwardCompAdjunction f g).homEquiv M P
          ((pullback f).map a ≫ b) ≫
        (pushforwardCompCongrIso f g h' h).hom.app P := hcancel.symm
    _ = ((pullbackPushforwardAdjunction g).homEquiv M N a ≫
          (pushforward g).map
            ((pullbackPushforwardAdjunction f).homEquiv N P b)) ≫
        (pushforwardCompCongrIso f g h' h).hom.app P := congrArg
          (fun m ↦ m ≫
            (pushforwardCompCongrIso f g h' h).hom.app P) hcombine
    _ = _ := Category.assoc _ _ _

private theorem pullbackPushforwardAdjunction_homEquiv_comp_inv
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (M : C.Modules) (N : B.Modules) (P : A.Modules)
    (a : (pullback g).obj M ⟶ N) (b : (pullback f).obj N ⟶ P) :
    (pullbackPushforwardAdjunction (f ≫ g)).homEquiv M P
        ((pullbackComp f g).inv.app M ≫ (pullback f).map a ≫ b) =
      (pullbackPushforwardAdjunction g).homEquiv M N a ≫
        (pushforward g).map
          ((pullbackPushforwardAdjunction f).homEquiv N P b) ≫
        (pushforwardComp f g).hom.app P := by
  have hcancel := homEquiv_comp_conjugate_iso_cancel
    (pullbackPushforwardAdjunction (f ≫ g))
    (pullbackPushforwardCompAdjunction f g) (pullbackComp f g).hom
    (pushforwardComp f g) (conjugateEquiv_pullbackComp_hom f g)
    ((pullbackComp f g).inv.app M ≫ (pullback f).map a ≫ b)
  have hcombine := pullbackPushforwardAdjunction_comp_homEquiv
    f g M N P a b
  simp only [Iso.hom_inv_id_app_assoc] at hcancel
  calc
    _ = (pullbackPushforwardCompAdjunction f g).homEquiv M P
          ((pullback f).map a ≫ b) ≫
        (pushforwardComp f g).hom.app P := hcancel.symm
    _ = ((pullbackPushforwardAdjunction g).homEquiv M N a ≫
          (pushforward g).map
            ((pullbackPushforwardAdjunction f).homEquiv N P b)) ≫
        (pushforwardComp f g).hom.app P := congrArg
          (fun m ↦ m ≫ (pushforwardComp f g).hom.app P) hcombine
    _ = _ := Category.assoc _ _ _

private theorem eq_hom_comp_of_inv_comp_comp_eq
    {C : Type u₁} [Category.{v₁} C] {X Y Z W : C}
    (e : X ≅ Y) (a : X ⟶ Z) (b : Y ⟶ Z) (u : Z ⟶ W) [Mono u]
    (h : (e.inv ≫ a) ≫ u = b ≫ u) :
    a = e.hom ≫ b := by
  rw [← e.inv_comp_eq]
  apply (cancel_mono u).1
  exact h

private theorem restrictUnitIso_conjugate
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (q : unitObj Y ⟶ unitObj Y) :
    (restrictUnitIso f).inv ≫ (restrictFunctor f).map q ≫
        (restrictUnitIso f).hom =
      (pullbackUnitIso f).inv ≫ (pullback f).map q ≫
        (pullbackUnitIso f).hom := by
  let E := restrictFunctorIsoPullback f
  let e := E.app (unitObj Y)
  let r := restrictUnitIso f
  let p := pullbackUnitIso f
  have hlow : e.inv ≫ r.hom = p.hom := by
    exact ModularCurves.restrictFunctorIsoPullback_inv_comp_restrictUnitIsoLow f
  have hentry : r.inv ≫ e.hom = p.inv := by
    have hiso : e.symm ≪≫ r = p := Iso.ext hlow
    change (e.symm ≪≫ r).inv = p.inv
    exact congrArg Iso.inv hiso
  have hnat : (restrictFunctor f).map q ≫ e.hom =
      e.hom ≫ (pullback f).map q := by
    exact E.hom.naturality q
  have hnat' := congrArg
    (fun m ↦ r.inv ≫ m ≫ e.inv ≫ r.hom) hnat
  have hentry' := congrArg
    (fun m ↦ m ≫ (pullback f).map q ≫ e.inv ≫ r.hom) hentry
  have hlow' := congrArg
    (fun m ↦ p.inv ≫ (pullback f).map q ≫ m) hlow
  have hcancel := congrArg
    (fun m ↦ r.inv ≫ (restrictFunctor f).map q ≫ m ≫ r.hom)
    e.hom_inv_id
  have hsource : r.inv ≫ (restrictFunctor f).map q ≫
      e.hom ≫ e.inv ≫ r.hom =
        r.inv ≫ (restrictFunctor f).map q ≫ r.hom := by
    convert hcancel using 1 <;> rfl
  have hnat'' : r.inv ≫ (restrictFunctor f).map q ≫
      e.hom ≫ e.inv ≫ r.hom =
        r.inv ≫ e.hom ≫ (pullback f).map q ≫ e.inv ≫ r.hom := by
    convert hnat' using 1 <;> rfl
  have htarget := hentry'.trans hlow'
  have htarget' : r.inv ≫ e.hom ≫ (pullback f).map q ≫
      e.inv ≫ r.hom = p.inv ≫ (pullback f).map q ≫ p.hom := by
    convert htarget using 1 <;> rfl
  have hchain := hsource.symm.trans (hnat''.trans htarget')
  change r.inv ≫ (restrictFunctor f).map q ≫ r.hom =
    p.inv ≫ (pullback f).map q ≫ p.hom
  exact hchain

private theorem restrictPushforwardUnitIso_inv_map
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) (N : X.Modules)
    (q : unitObj X ⟶ N) :
    (restrictPushforwardUnitIsoOfIsPullback f f' iU iV H).inv ≫
        (restrictFunctor iV).map ((pushforward f).map q) ≫
        (restrictPushforwardIsoOfIsPullback f f' iU iV H).hom.app N =
      (pushforward f').map
        ((restrictUnitIso iU).inv ≫ (restrictFunctor iU).map q) := by
  let e := restrictPushforwardIsoOfIsPullback f f' iU iV H
  let r := restrictUnitIso iU
  let u := (pushforward f').mapIso r
  have he : restrictPushforwardUnitIsoOfIsPullback f f' iU iV H =
      e.app (unitObj X) ≪≫ u :=
    restrictPushforwardUnitIsoOfIsPullback_eq f f' iU iV H
  rw [he]
  let eU := e.app (unitObj X)
  let eN := e.app N
  let m := (pushforward f ⋙ restrictFunctor iV).map q
  let n := (restrictFunctor iU ⋙ pushforward f').map q
  change (eU ≪≫ u).inv ≫ m ≫ eN.hom =
    (pushforward f').map (r.inv ≫ (restrictFunctor iU).map q)
  have hnat : m ≫ eN.hom = eU.hom ≫ n :=
    e.hom.naturality q
  have hreassoc :
      (eU ≪≫ u).inv ≫ m ≫ eN.hom =
        u.inv ≫ (eU.inv ≫ (m ≫ eN.hom)) := by
    change (u.inv ≫ eU.inv) ≫ m ≫ eN.hom =
      u.inv ≫ (eU.inv ≫ (m ≫ eN.hom))
    have houter :
        (u.inv ≫ eU.inv) ≫ m ≫ eN.hom =
          (u.inv ≫ eU.inv) ≫ (m ≫ eN.hom) :=
      Category.assoc (u.inv ≫ eU.inv) m eN.hom
    have hinner :
        (u.inv ≫ eU.inv) ≫ (m ≫ eN.hom) =
          u.inv ≫ (eU.inv ≫ (m ≫ eN.hom)) :=
      Category.assoc u.inv eU.inv (m ≫ eN.hom)
    exact houter.trans hinner
  have hnaturality :
      u.inv ≫ (eU.inv ≫ (m ≫ eN.hom)) =
        u.inv ≫ (eU.inv ≫ (eU.hom ≫ n)) :=
    congrArg (fun z ↦ u.inv ≫ (eU.inv ≫ z)) hnat
  have hcancel :
      u.inv ≫ (eU.inv ≫ (eU.hom ≫ n)) = u.inv ≫ n := by
    have hinner : eU.inv ≫ (eU.hom ≫ n) = n := by
      have hassoc :
          eU.inv ≫ (eU.hom ≫ n) = (eU.inv ≫ eU.hom) ≫ n :=
        (Category.assoc eU.inv eU.hom n).symm
      have hpair : (eU.inv ≫ eU.hom) ≫ n = 𝟙 _ ≫ n :=
        congrArg (fun z ↦ z ≫ n) eU.inv_hom_id
      exact hassoc.trans (hpair.trans (Category.id_comp n))
    exact congrArg (fun z ↦ u.inv ≫ z) hinner
  have hmap : u.inv ≫ n =
      (pushforward f').map (r.inv ≫ (restrictFunctor iU).map q) := by
    change (pushforward f').map r.inv ≫
      (pushforward f').map ((restrictFunctor iU).map q) = _
    exact ((pushforward f').map_comp r.inv ((restrictFunctor iU).map q)).symm
  exact hreassoc.trans (hnaturality.trans (hcancel.trans hmap))

private theorem restrictUnitIso_inv_unitToPushforward_baseChange
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) :
    (restrictUnitIso iV).inv ≫
        (restrictFunctor iV).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (restrictPushforwardIsoOfIsPullback f f' iU iV H).hom.app
          (unitObj X) =
      SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom ≫
        (pushforward f').map (restrictUnitIso iU).inv := by
  have hunit := restrictUnitIso_inv_unitToPushforward f f' iU iV H
  have hcancel :
      (restrictPushforwardUnitIsoOfIsPullback f f' iU iV H).inv ≫
          (restrictPushforwardIsoOfIsPullback f f' iU iV H).hom.app
            (unitObj X) =
        (pushforward f').map (restrictUnitIso iU).inv := by
    rw [restrictPushforwardUnitIsoOfIsPullback_eq]
    let e := (restrictPushforwardIsoOfIsPullback f f' iU iV H).app
      (unitObj X)
    change ((pushforward f').map (restrictUnitIso iU).inv ≫ e.inv) ≫
      e.hom = _
    have hcancel' := congrArg
      (fun m ↦ (pushforward f').map (restrictUnitIso iU).inv ≫ m)
      e.inv_hom_id
    convert hcancel' using 1 <;> rfl
  have hunit' := congrArg
    (fun m ↦ m ≫
      (restrictPushforwardIsoOfIsPullback f f' iU iV H).hom.app
        (unitObj X)) hunit
  have hcancel' := congrArg
    (fun m ↦ SheafOfModules.unitToPushforwardObjUnit
      f'.toRingCatSheafHom ≫ m) hcancel
  have hchain := hunit'.trans hcancel'
  convert hchain using 1 <;> rfl

private theorem restrictPushforwardIsoOfIsPullback_comp
    {A B C A' B' C' : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')
    (iA : A' ⟶ A) (iB : B' ⟶ B) (iC : C' ⟶ C)
    [IsOpenImmersion iA] [IsOpenImmersion iB] [IsOpenImmersion iC]
    (Hf : IsPullback f' iA iB f) (Hg : IsPullback g' iB iC g)
    (M : A.Modules) :
    (restrictFunctor iC).map ((pushforwardComp f g).hom.app M) ≫
          (restrictPushforwardIsoOfIsPullback (f ≫ g) (f' ≫ g') iA iC
            (Hf.paste_horiz Hg)).hom.app M =
      (restrictPushforwardIsoOfIsPullback g g' iB iC Hg).hom.app
          ((pushforward f).obj M) ≫
        (pushforward g').map
          ((restrictPushforwardIsoOfIsPullback f f' iA iB Hf).hom.app M) ≫
        (pushforwardComp f' g').hom.app ((restrictFunctor iA).obj M) := by
  let l₁ := (restrictFunctor iC).map ((pushforwardComp f g).hom.app M)
  let l₂ := (restrictPushforwardIsoOfIsPullback (f ≫ g) (f' ≫ g') iA iC
    (Hf.paste_horiz Hg)).hom.app M
  let r₁ := (restrictPushforwardIsoOfIsPullback g g' iB iC Hg).hom.app
    ((pushforward f).obj M)
  let r₂ := (pushforward g').map
    ((restrictPushforwardIsoOfIsPullback f f' iA iB Hf).hom.app M)
  let r₃ := (pushforwardComp f' g').hom.app ((restrictFunctor iA).obj M)
  change l₁ ≫ l₂ = r₁ ≫ r₂ ≫ r₃
  apply hom_ext
  intro W
  ext x
  change (l₂.app W).hom ((l₁.app W).hom x) =
    (r₃.app W).hom ((r₂.app W).hom ((r₁.app W).hom x))
  dsimp only [l₁, l₂, r₁, r₂, r₃]
  simp only [pushforwardComp_hom_app_app]
  change
    (((restrictPushforwardIsoOfIsPullback (f ≫ g) (f' ≫ g') iA iC
      (Hf.paste_horiz Hg)).hom.app M).app W).hom x =
      (((pushforward g').map
        ((restrictPushforwardIsoOfIsPullback f f' iA iB Hf).hom.app M)).app W).hom
        ((((restrictPushforwardIsoOfIsPullback g g' iB iC Hg).hom.app
          ((pushforward f).obj M)).app W).hom x)
  rw [restrictPushforwardIsoOfIsPullback_hom_app_apply
    (f ≫ g) (f' ≫ g') iA iC (Hf.paste_horiz Hg) M W x]
  rw [restrictPushforwardIsoOfIsPullback_hom_app_apply
    g g' iB iC Hg ((pushforward f).obj M) W x]
  let y : Γ((restrictFunctor iB).obj ((pushforward f).obj M), g' ⁻¹ᵁ W) :=
    ((restrictPushforwardPresheafIsoOfIsPullback
      g g' iB iC Hg ((pushforward f).obj M)).hom.app (.op W)).hom x
  change
    ((restrictPushforwardPresheafIsoOfIsPullback
      (f ≫ g) (f' ≫ g') iA iC (Hf.paste_horiz Hg) M).hom.app (.op W)).hom x =
      ((((restrictPushforwardIsoOfIsPullback f f' iA iB Hf).hom.app M).app
        (g' ⁻¹ᵁ W)).hom y)
  rw [restrictPushforwardIsoOfIsPullback_hom_app_apply
    f f' iA iB Hf M (g' ⁻¹ᵁ W) y]
  dsimp [y, restrictPushforwardPresheafIsoOfIsPullback]
  let x' : M.val.obj (.op ((f ≫ g) ⁻¹ᵁ iC ''ᵁ W)) := x
  change M.presheaf.map _ x' = M.presheaf.map _ (M.presheaf.map _ x')
  let hfg := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (Hf.paste_horiz Hg) W
  let hg := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback Hg W
  let hf := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback Hf
    (g' ⁻¹ᵁ W)
  let a := (Opens.map f.base).op.map (eqToIso hg).op.hom
  let b := (eqToIso hf).op.hom
  let d := (eqToIso hfg).op.hom
  have hd : d = a ≫ b := Subsingleton.elim _ _
  have hdirect : M.presheaf.map d x' = M.presheaf.map (a ≫ b) x' :=
    ConcreteCategory.congr_hom (M.presheaf.congr_map hd) x'
  have hcomp : M.presheaf.map (a ≫ b) x' =
      M.presheaf.map b (M.presheaf.map a x') :=
    ConcreteCategory.congr_hom (M.presheaf.map_comp a b) x'
  exact hdirect.trans hcomp

private theorem restrictPushforwardIsoOfIsPullback_hom_congr
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f₁ f₂ : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H₁ : IsPullback f₁ iU iV f) (H₂ : IsPullback f₂ iU iV f)
    (h : f₁ = f₂) (M : X.Modules) :
    (restrictPushforwardIsoOfIsPullback f f₂ iU iV H₂).hom.app M =
      (restrictPushforwardIsoOfIsPullback f f₁ iU iV H₁).hom.app M ≫
        (pushforwardCongr h).hom.app ((restrictFunctor iU).obj M) := by
  apply hom_ext
  intro W
  ext x
  let x' : Γ((restrictFunctor iV).obj ((pushforward f).obj M), W) := x
  rw [restrictPushforwardIsoOfIsPullback_hom_app_apply
    f f₂ iU iV H₂ M W x']
  change
    ((restrictPushforwardPresheafIsoOfIsPullback
      f f₂ iU iV H₂ M).hom.app (.op W)).hom x' =
      (((pushforwardCongr h).hom.app ((restrictFunctor iU).obj M)).app W).hom
        ((((restrictPushforwardIsoOfIsPullback
          f f₁ iU iV H₁).hom.app M).app W).hom x')
  rw [restrictPushforwardIsoOfIsPullback_hom_app_apply
    f f₁ iU iV H₁ M W x']
  rw [pushforwardCongr_hom_app_app]
  dsimp [x', restrictPushforwardPresheafIsoOfIsPullback]
  let x'' : M.val.obj (.op (f ⁻¹ᵁ iV ''ᵁ W)) := x
  change M.presheaf.map _ x'' = M.presheaf.map _ (M.presheaf.map _ x'')
  let h₁' := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H₁ W
  let h₂' := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H₂ W
  let hpre : f₂ ⁻¹ᵁ W = f₁ ⁻¹ᵁ W :=
    congrArg (fun q : U ⟶ V ↦ q ⁻¹ᵁ W) h.symm
  let a := (eqToIso h₁').op.hom
  let b := (Scheme.Hom.opensFunctor iU).op.map (eqToHom hpre).op
  let d := (eqToIso h₂').op.hom
  have hd : d = a ≫ b := Subsingleton.elim _ _
  have hdirect : M.presheaf.map d x'' = M.presheaf.map (a ≫ b) x'' :=
    ConcreteCategory.congr_hom (M.presheaf.congr_map hd) x''
  have hcomp : M.presheaf.map (a ≫ b) x'' =
      M.presheaf.map b (M.presheaf.map a x'') :=
    ConcreteCategory.congr_hom (M.presheaf.map_comp a b) x''
  exact hdirect.trans hcomp

private theorem restrictPushforwardIsoOfIsPullback_comp_of_eq
    {A B C A' B' C' : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')
    (h' : A' ⟶ C') (iA : A' ⟶ A) (iB : B' ⟶ B) (iC : C' ⟶ C)
    [IsOpenImmersion iA] [IsOpenImmersion iB] [IsOpenImmersion iC]
    (Hf : IsPullback f' iA iB f) (Hg : IsPullback g' iB iC g)
    (Hh : IsPullback h' iA iC (f ≫ g)) (h : f' ≫ g' = h')
    (M : A.Modules) :
    (restrictFunctor iC).map ((pushforwardComp f g).hom.app M) ≫
          (restrictPushforwardIsoOfIsPullback (f ≫ g) h' iA iC Hh).hom.app M =
      (restrictPushforwardIsoOfIsPullback g g' iB iC Hg).hom.app
          ((pushforward f).obj M) ≫
        (pushforward g').map
          ((restrictPushforwardIsoOfIsPullback f f' iA iB Hf).hom.app M) ≫
        (pushforwardComp f' g').hom.app ((restrictFunctor iA).obj M) ≫
        (pushforwardCongr h).hom.app ((restrictFunctor iA).obj M) := by
  rw [restrictPushforwardIsoOfIsPullback_hom_congr
    (f ≫ g) (f' ≫ g') h' iA iC (Hf.paste_horiz Hg) Hh h M]
  have hcomp := restrictPushforwardIsoOfIsPullback_comp
    f g f' g' iA iB iC Hf Hg M
  exact congrArg (fun q ↦ q ≫
    (pushforwardCongr h).hom.app ((restrictFunctor iA).obj M)) hcomp

private theorem restrictPushforwardUnitIso_inv_map_comp_of_eq
    {A B C A' B' C' : Scheme.{u}}
    {P : C'.Modules}
    (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')
    (h' : A' ⟶ C') (iA : A' ⟶ A) (iB : B' ⟶ B) (iC : C' ⟶ C)
    [IsOpenImmersion iA] [IsOpenImmersion iB] [IsOpenImmersion iC]
    (Hf : IsPullback f' iA iB f) (Hg : IsPullback g' iB iC g)
    (Hh : IsPullback h' iA iC (f ≫ g)) (h : f' ≫ g' = h')
    (a : P ⟶ (pushforward g').obj (unitObj B'))
    (m : unitObj B ⟶ (pushforward f).obj (unitObj A)) :
    a ≫ (restrictPushforwardUnitIsoOfIsPullback g g' iB iC Hg).inv ≫
          (restrictFunctor iC).map
            ((pushforward g).map m ≫
              (pushforwardComp f g).hom.app (unitObj A)) ≫
          (restrictPushforwardUnitIsoOfIsPullback
            (f ≫ g) h' iA iC Hh).hom =
      a ≫ (pushforward g').map
            ((restrictUnitIso iB).inv ≫
              (restrictFunctor iB).map m ≫
              (restrictPushforwardIsoOfIsPullback
                f f' iA iB Hf).hom.app (unitObj A)) ≫
          (pushforwardComp f' g').hom.app
            ((restrictFunctor iA).obj (unitObj A)) ≫
          (pushforwardCongr h).hom.app
            ((restrictFunctor iA).obj (unitObj A)) ≫
    (pushforward h').map (restrictUnitIso iA).hom := by
  let outerUnitInv :
      (pushforward g').obj (unitObj B') ⟶
        (restrictFunctor iC).obj ((pushforward g).obj (unitObj B)) :=
    (restrictPushforwardUnitIsoOfIsPullback g g' iB iC Hg).inv
  let gm :
      (pushforward g).obj (unitObj B) ⟶
        (pushforward g).obj ((pushforward f).obj (unitObj A)) :=
    (pushforward g).map m
  let gmR :
      (restrictFunctor iC).obj ((pushforward g).obj (unitObj B)) ⟶
        (restrictFunctor iC).obj
          ((pushforward g).obj ((pushforward f).obj (unitObj A))) :=
    (restrictFunctor iC).map gm
  let pc : (pushforward g).obj ((pushforward f).obj (unitObj A)) ⟶
      (pushforward (f ≫ g)).obj (unitObj A) :=
    (pushforwardComp f g).hom.app (unitObj A)
  let pcR :
      (restrictFunctor iC).obj
          ((pushforward g).obj ((pushforward f).obj (unitObj A))) ⟶
        (restrictFunctor iC).obj
          ((pushforward (f ≫ g)).obj (unitObj A)) :=
    (restrictFunctor iC).map pc
  let combinedR :
      (restrictFunctor iC).obj ((pushforward g).obj (unitObj B)) ⟶
        (restrictFunctor iC).obj
          ((pushforward (f ≫ g)).obj (unitObj A)) :=
    (restrictFunctor iC).map (gm ≫ pc)
  let directBase :
      (restrictFunctor iC).obj
          ((pushforward (f ≫ g)).obj (unitObj A)) ⟶
        (pushforward h').obj ((restrictFunctor iA).obj (unitObj A)) :=
    (restrictPushforwardIsoOfIsPullback
      (f ≫ g) h' iA iC Hh).hom.app (unitObj A)
  let outerBase :
      (restrictFunctor iC).obj
          ((pushforward g).obj ((pushforward f).obj (unitObj A))) ⟶
        (pushforward g').obj
          ((restrictFunctor iB).obj ((pushforward f).obj (unitObj A))) :=
    (restrictPushforwardIsoOfIsPullback
      g g' iB iC Hg).hom.app ((pushforward f).obj (unitObj A))
  let localM :
      unitObj B' ⟶
        (restrictFunctor iB).obj ((pushforward f).obj (unitObj A)) :=
    (restrictUnitIso iB).inv ≫ (restrictFunctor iB).map m
  let innerBase :
      (restrictFunctor iB).obj ((pushforward f).obj (unitObj A)) ⟶
        (pushforward f').obj ((restrictFunctor iA).obj (unitObj A)) :=
    (restrictPushforwardIsoOfIsPullback
      f f' iA iB Hf).hom.app (unitObj A)
  let pc' : (pushforward g').obj
        ((pushforward f').obj ((restrictFunctor iA).obj (unitObj A))) ⟶
      (pushforward (f' ≫ g')).obj
        ((restrictFunctor iA).obj (unitObj A)) :=
    (pushforwardComp f' g').hom.app ((restrictFunctor iA).obj (unitObj A))
  let congr' :
      (pushforward (f' ≫ g')).obj
          ((restrictFunctor iA).obj (unitObj A)) ⟶
        (pushforward h').obj ((restrictFunctor iA).obj (unitObj A)) :=
    (pushforwardCongr h).hom.app ((restrictFunctor iA).obj (unitObj A))
  let final :
      (pushforward h').obj ((restrictFunctor iA).obj (unitObj A)) ⟶
        (pushforward h').obj (unitObj A') :=
    (pushforward h').map (restrictUnitIso iA).hom
  have hdirectRaw := congrArg Iso.hom
    (restrictPushforwardUnitIsoOfIsPullback_eq
      (f ≫ g) h' iA iC Hh)
  rw [hdirectRaw]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  change a ≫ outerUnitInv ≫ combinedR ≫ directBase ≫ final =
    a ≫ (pushforward g').map (localM ≫ innerBase) ≫
      pc' ≫ congr' ≫ final
  have hcombined : combinedR = gmR ≫ pcR := by
    exact (restrictFunctor iC).map_comp gm pc
  have hbaseRaw := restrictPushforwardIsoOfIsPullback_comp_of_eq
    f g f' g' h' iA iB iC Hf Hg Hh h (unitObj A)
  have hbase : pcR ≫ directBase =
      outerBase ≫ (pushforward g').map innerBase ≫ pc' ≫ congr' := by
    dsimp only [pcR, directBase, outerBase, innerBase, pc', congr']
    exact hbaseRaw
  have houter : outerUnitInv ≫ gmR ≫ outerBase =
      (pushforward g').map localM := by
    dsimp only [outerUnitInv, gmR, gm, outerBase, localM]
    exact restrictPushforwardUnitIso_inv_map
      g g' iB iC Hg ((pushforward f).obj (unitObj A)) m
  have hmap :
      (pushforward g').map localM ≫ (pushforward g').map innerBase =
        (pushforward g').map (localM ≫ innerBase) :=
    ((pushforward g').map_comp localM innerBase).symm
  have hbase' := congrArg
    (fun q ↦
      a ≫ outerUnitInv ≫ gmR ≫ q ≫ final) hbase
  have houter' := congrArg
    (fun q ↦
      a ≫ q ≫ (pushforward g').map innerBase ≫
        pc' ≫ congr' ≫ final) houter
  have hmap' := congrArg
    (fun q ↦
      a ≫ q ≫ pc' ≫ congr' ≫ final) hmap
  calc
    _ = a ≫ outerUnitInv ≫ gmR ≫ pcR ≫ directBase ≫ final := by
          rw [hcombined]
          simp only [Category.assoc]
    _ = a ≫ outerUnitInv ≫ gmR ≫ outerBase ≫
        (pushforward g').map innerBase ≫ pc' ≫ congr' ≫ final := by
          simpa only [Category.assoc] using hbase'
    _ = a ≫ (pushforward g').map localM ≫
        (pushforward g').map innerBase ≫ pc' ≫ congr' ≫ final := by
          simpa only [Category.assoc] using houter'
    _ = _ := by simpa only [Category.assoc] using hmap'

private noncomputable def restrictPushforwardUnitIsoBefore
    {A B C A' B' C' : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')
    (h' : A' ⟶ C') (iA : A' ⟶ A) (iB : B' ⟶ B) (iC : C' ⟶ C)
    [IsOpenImmersion iA] [IsOpenImmersion iB] [IsOpenImmersion iC]
    (_Hf : IsPullback f' iA iB f) (Hg : IsPullback g' iB iC g)
    (Hh : IsPullback h' iA iC (f ≫ g)) (_h : f' ≫ g' = h')
    (a : unitObj C' ⟶ (pushforward g').obj (unitObj B'))
    (m : unitObj B ⟶ (pushforward f).obj (unitObj A)) :
    unitObj C' ⟶ (pushforward h').obj (unitObj A') :=
  a ≫ (restrictPushforwardUnitIsoOfIsPullback g g' iB iC Hg).inv ≫
    (restrictFunctor iC).map
      ((pushforward g).map m ≫
        (pushforwardComp f g).hom.app (unitObj A)) ≫
    (restrictPushforwardUnitIsoOfIsPullback
      (f ≫ g) h' iA iC Hh).hom

private noncomputable def restrictPushforwardUnitIsoAfter
    {A B C A' B' C' : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')
    (h' : A' ⟶ C') (iA : A' ⟶ A) (iB : B' ⟶ B) (iC : C' ⟶ C)
    [IsOpenImmersion iA] [IsOpenImmersion iB] [IsOpenImmersion iC]
    (Hf : IsPullback f' iA iB f) (_Hg : IsPullback g' iB iC g)
    (_Hh : IsPullback h' iA iC (f ≫ g)) (h : f' ≫ g' = h')
    (a : unitObj C' ⟶ (pushforward g').obj (unitObj B'))
    (m : unitObj B ⟶ (pushforward f).obj (unitObj A)) :
    unitObj C' ⟶ (pushforward h').obj (unitObj A') :=
  a ≫ (pushforward g').map
      ((restrictUnitIso iB).inv ≫
        (restrictFunctor iB).map m ≫
        (restrictPushforwardIsoOfIsPullback
          f f' iA iB Hf).hom.app (unitObj A)) ≫
    (pushforwardComp f' g').hom.app
      ((restrictFunctor iA).obj (unitObj A)) ≫
    (pushforwardCongr h).hom.app
      ((restrictFunctor iA).obj (unitObj A)) ≫
    (pushforward h').map (restrictUnitIso iA).hom

private theorem restrictPushforwardUnitIsoBefore_eq_after
    {A B C A' B' C' : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')
    (h' : A' ⟶ C') (iA : A' ⟶ A) (iB : B' ⟶ B) (iC : C' ⟶ C)
    [IsOpenImmersion iA] [IsOpenImmersion iB] [IsOpenImmersion iC]
    (Hf : IsPullback f' iA iB f) (Hg : IsPullback g' iB iC g)
    (Hh : IsPullback h' iA iC (f ≫ g)) (h : f' ≫ g' = h')
    (a : unitObj C' ⟶ (pushforward g').obj (unitObj B'))
    (m : unitObj B ⟶ (pushforward f).obj (unitObj A)) :
    restrictPushforwardUnitIsoBefore
        f g f' g' h' iA iB iC Hf Hg Hh h a m =
      restrictPushforwardUnitIsoAfter
        f g f' g' h' iA iB iC Hf Hg Hh h a m := by
  exact restrictPushforwardUnitIso_inv_map_comp_of_eq
    f g f' g' h' iA iB iC Hf Hg Hh h a m

private noncomputable def restrictProductIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {I : Type u} (P : I → Y.Modules) (Q : I → X.Modules)
    (e : ∀ i, (restrictFunctor f).obj (P i) ≅ Q i) :
    (restrictFunctor f).obj (∏ᶜ P) ≅ ∏ᶜ Q := by
  letI : PreservesLimits (restrictFunctor f) := restrictFunctor_preservesLimits f
  let d : Discrete.functor P ⋙ restrictFunctor f ≅
      Discrete.functor (fun i ↦ (restrictFunctor f).obj (P i)) :=
    Discrete.natIso fun _ ↦ Iso.refl _
  exact preservesLimitIso (restrictFunctor f) (Discrete.functor P) ≪≫
    HasLimit.isoOfNatIso d ≪≫ Pi.mapIso e

@[reassoc]
private theorem restrictProductIso_hom_π
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {I : Type u} (P : I → Y.Modules) (Q : I → X.Modules)
    (e : ∀ i, (restrictFunctor f).obj (P i) ≅ Q i) (i : I) :
    (restrictProductIso f P Q e).hom ≫ Pi.π Q i =
      (restrictFunctor f).map (Pi.π P i) ≫ (e i).hom := by
  letI : PreservesLimits (restrictFunctor f) := restrictFunctor_preservesLimits f
  let d : Discrete.functor P ⋙ restrictFunctor f ≅
      Discrete.functor (fun j ↦ (restrictFunctor f).obj (P j)) :=
    Discrete.natIso fun _ ↦ Iso.refl _
  have hproj :
      (preservesLimitIso (restrictFunctor f) (Discrete.functor P)).hom ≫
          (HasLimit.isoOfNatIso d).hom ≫
            Pi.π (fun j ↦ (restrictFunctor f).obj (P j)) i =
        (restrictFunctor f).map (Pi.π P i) := by
    change (preservesLimitIso (restrictFunctor f) (Discrete.functor P)).hom ≫
        ((HasLimit.isoOfNatIso d).hom ≫
          limit.π (Discrete.functor fun j ↦ (restrictFunctor f).obj (P j))
            (Discrete.mk i)) = _
    rw [HasLimit.isoOfNatIso_hom_π]
    change (preservesLimitIso (restrictFunctor f) (Discrete.functor P)).hom ≫
        limit.π (Discrete.functor P ⋙ restrictFunctor f) (Discrete.mk i) ≫ 𝟙 _ =
      (restrictFunctor f).map (limit.π (Discrete.functor P) (Discrete.mk i))
    rw [Category.comp_id]
    exact preservesLimitIso_hom_π _ _ _
  dsimp only [restrictProductIso]
  simp only [Iso.trans_hom, Category.assoc, Pi.mapIso_hom_π]
  simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ (e i).hom) hproj

@[reassoc]
private theorem restrictProductIso_inv_π
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {I : Type u} (P : I → Y.Modules) (Q : I → X.Modules)
    (e : ∀ i, (restrictFunctor f).obj (P i) ≅ Q i) (i : I) :
    (restrictProductIso f P Q e).inv ≫
        (restrictFunctor f).map (Pi.π P i) =
      Pi.π Q i ≫ (e i).inv := by
  rw [← cancel_mono (e i).hom]
  simp only [Category.assoc]
  rw [← restrictProductIso_hom_π]
  simp

private noncomputable def AffineIntersectionUnitCocycle.chartExtension
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (_c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    D.glued.Modules :=
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  (pushforward (D.ι i)).obj (unitObj (D.U i))

/-- On a chart, a chart-extension factor restricts to the pushforward of the
structure sheaf from the corresponding ordered overlap. -/
noncomputable def AffineIntersectionUnitCocycle.chartExtensionRestrictIso
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).obj
        (c.chartExtension hopen hpush i) ≅
      (pushforward (D.t i k ≫ D.f k i)).obj (unitObj (D.V (i, k))) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  letI : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  letI : IsOpenImmersion (D.f i k) := D.f_open i k
  exact restrictPushforwardUnitIsoOfIsPullback
    (D.ι i) (D.t i k ≫ D.f k i) (D.f i k) (D.ι k)
    (IsPullback.of_isLimit (D.vPullbackConeIsLimit i k)).flip

private noncomputable def AffineIntersectionUnitCocycle.overlapExtension
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (_c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    D.glued.Modules :=
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  (pushforward (D.f i j ≫ D.ι i)).obj (unitObj (D.V (i, j)))

/-- On a chart, an overlap-extension factor restricts to the pushforward of
the structure sheaf from the corresponding canonical triple intersection. -/
noncomputable def AffineIntersectionUnitCocycle.overlapExtensionRestrictIso
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).obj
        (c.overlapExtension hopen hpush i j) ≅
      (pushforward t.p₃).obj (unitObj t.pullback) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  letI : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  have H : IsPullback t.p₁₂ t.p₃ (sq i j).p (D.ι k) := by
    have H' := t.isPullback₂.paste_vert (sq j k).isPullback
    rw [t.p₂₃_p₃] at H'
    rw [(sq i j).hp₂] at H'
    exact H'
  letI : IsOpenImmersion t.p₁₂ :=
    MorphismProperty.of_isPullback H.flip inferInstance
  exact restrictPushforwardUnitIsoOfIsPullback
    (sq i j).p t.p₃ t.p₁₂ (D.ι k) H.flip

private noncomputable def AffineIntersectionUnitCocycle.chartToOverlapLeft
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    c.chartExtension hopen hpush i ⟶ c.overlapExtension hopen hpush i j :=
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  (pushforward (D.ι i)).map
      ((pullbackPushforwardAdjunction (D.f i j)).homEquiv _ _
        ((c.chartTransitionIso hopen hpush i j).hom ≫
          (pullbackUnitIso (D.t i j ≫ D.f j i)).hom)) ≫
    (pushforwardComp (D.f i j) (D.ι i)).hom.app _

private theorem AffineIntersectionUnitCocycle.chartToOverlapLeft_eq
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    c.chartToOverlapLeft hopen hpush i j =
      (pushforward (D.ι i)).map
          ((pullbackPushforwardAdjunction (D.f i j)).homEquiv _ _
            ((pullbackUnitIso (D.f i j)).hom ≫
              (c.overlapTransitionIso i j).hom)) ≫
        (pushforwardComp (D.f i j) (D.ι i)).hom.app _ := by
  dsimp only [AffineIntersectionUnitCocycle.chartToOverlapLeft]
  rw [c.chartTransitionIso_hom]
  simp
  rfl

private noncomputable def AffineIntersectionUnitCocycle.chartToOverlapRight
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    c.chartExtension hopen hpush j ⟶ c.overlapExtension hopen hpush i j :=
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  (pushforward (D.ι j)).map
      ((pullbackPushforwardAdjunction (D.t i j ≫ D.f j i)).homEquiv _ _
        (pullbackUnitIso (D.t i j ≫ D.f j i)).hom) ≫
    (pushforwardComp (D.t i j ≫ D.f j i) (D.ι j)).hom.app _ ≫
    (pushforwardCongr (D.glue_condition i j)).hom.app _

private theorem AffineIntersectionUnitCocycle.chartToOverlapRight_eq
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let f := D.t i j ≫ D.f j i
    c.chartToOverlapRight hopen hpush i j =
      (pushforward (D.ι j)).map
          (SheafOfModules.unitToPushforwardObjUnit
            f.toRingCatSheafHom) ≫
        (pushforwardComp f (D.ι j)).hom.app _ ≫
        (pushforwardCongr (D.glue_condition i j)).hom.app _ := by
  dsimp only [AffineIntersectionUnitCocycle.chartToOverlapRight]
  rw [ModularCurves.pullbackUnitIso_homEquivLow]
  rfl

private noncomputable def AffineIntersectionUnitCocycle.chartGlueSource
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    D.glued.Modules :=
  ∏ᶜ fun i : J ↦ c.chartExtension hopen hpush i

/-- Over a fixed chart, the restricted Cech source is the product of the
structure sheaves pushed forward from its ordered overlaps with all charts. -/
noncomputable def AffineIntersectionUnitCocycle.chartGlueSourceRestrictIso
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).obj
        (c.chartGlueSource hopen hpush) ≅
      ∏ᶜ fun i : J ↦
        (pushforward (D.t i k ≫ D.f k i)).obj (unitObj (D.V (i, k))) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  letI : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  exact restrictProductIso (D.ι k)
    (fun i : J ↦ c.chartExtension hopen hpush i)
    (fun i : J ↦
      (pushforward (D.t i k ≫ D.f k i)).obj (unitObj (D.V (i, k))))
    (fun i ↦ c.chartExtensionRestrictIso hopen hpush k i)

@[reassoc]
theorem AffineIntersectionUnitCocycle.chartGlueSourceRestrictIso_hom_π
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (c.chartGlueSourceRestrictIso hopen hpush k).hom ≫
        Pi.π (fun j : J ↦
          (pushforward (D.t j k ≫ D.f k j)).obj (unitObj (D.V (j, k)))) i =
      (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (Pi.π (fun j : J ↦ c.chartExtension hopen hpush j) i) ≫
        (c.chartExtensionRestrictIso hopen hpush k i).hom := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  letI : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  simpa only [AffineIntersectionUnitCocycle.chartGlueSourceRestrictIso,
    AffineIntersectionUnitCocycle.chartGlueSource] using
    restrictProductIso_hom_π (D.ι k)
      (fun j : J ↦ c.chartExtension hopen hpush j)
      (fun j : J ↦
        (pushforward (D.t j k ≫ D.f k j)).obj (unitObj (D.V (j, k))))
      (fun j ↦ c.chartExtensionRestrictIso hopen hpush k j) i

@[reassoc]
theorem AffineIntersectionUnitCocycle.chartGlueSourceRestrictIso_inv_π
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (c.chartGlueSourceRestrictIso hopen hpush k).inv ≫
        (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (Pi.π (fun j : J ↦ c.chartExtension hopen hpush j) i) =
      Pi.π (fun j : J ↦
          (pushforward (D.t j k ≫ D.f k j)).obj (unitObj (D.V (j, k)))) i ≫
        (c.chartExtensionRestrictIso hopen hpush k i).inv := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  letI : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  simpa only [AffineIntersectionUnitCocycle.chartGlueSourceRestrictIso,
    AffineIntersectionUnitCocycle.chartGlueSource] using
    restrictProductIso_inv_π (D.ι k)
      (fun j : J ↦ c.chartExtension hopen hpush j)
      (fun j : J ↦
        (pushforward (D.t j k ≫ D.f k j)).obj (unitObj (D.V (j, k))))
      (fun j ↦ c.chartExtensionRestrictIso hopen hpush k j) i

private noncomputable def AffineIntersectionUnitCocycle.chartLocalTupleComponent
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    unitObj (D.U k) ⟶
      (pushforward (D.t i k ≫ D.f k i)).obj (unitObj (D.V (i, k))) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  exact (pullbackPushforwardAdjunction (D.t i k ≫ D.f k i)).homEquiv _ _
    ((c.chartTransitionIso hopen hpush i k).inv ≫
      (pullbackUnitIso (D.f i k)).hom)

private theorem AffineIntersectionUnitCocycle.chartLocalTupleComponent_eq
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    c.chartLocalTupleComponent hopen hpush k i =
      (pullbackPushforwardAdjunction (D.t i k ≫ D.f k i)).homEquiv _ _
        ((pullbackUnitIso (D.t i k ≫ D.f k i)).hom ≫
          (c.overlapTransitionIso i k).inv) := by
  dsimp only [AffineIntersectionUnitCocycle.chartLocalTupleComponent]
  rw [c.chartTransitionIso_inv]
  simp

private noncomputable def AffineIntersectionUnitCocycle.chartLocalTuple
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    unitObj (D.U k) ⟶
      ∏ᶜ fun i : J ↦
        (pushforward (D.t i k ≫ D.f k i)).obj (unitObj (D.V (i, k))) :=
  Pi.lift fun i ↦ c.chartLocalTupleComponent hopen hpush k i

@[reassoc]
private theorem AffineIntersectionUnitCocycle.chartLocalTuple_π
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    c.chartLocalTuple hopen hpush k ≫
        Pi.π (fun j : J ↦
          (pushforward (D.t j k ≫ D.f k j)).obj (unitObj (D.V (j, k)))) i =
      c.chartLocalTupleComponent hopen hpush k i := by
  dsimp only [AffineIntersectionUnitCocycle.chartLocalTuple]
  exact Pi.lift_π _ i

private noncomputable def AffineIntersectionUnitCocycle.chartLocalSource
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    unitObj (D.U k) ⟶
      (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).obj
        (c.chartGlueSource hopen hpush) :=
  c.chartLocalTuple hopen hpush k ≫
    (c.chartGlueSourceRestrictIso hopen hpush k).inv

@[reassoc]
private theorem AffineIntersectionUnitCocycle.chartLocalSource_π
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    c.chartLocalSource hopen hpush k ≫
        (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (Pi.π (fun j : J ↦ c.chartExtension hopen hpush j) i) =
      c.chartLocalTupleComponent hopen hpush k i ≫
        (c.chartExtensionRestrictIso hopen hpush k i).inv := by
  dsimp only [AffineIntersectionUnitCocycle.chartLocalSource]
  rw [Category.assoc,
    c.chartGlueSourceRestrictIso_inv_π, ← Category.assoc, c.chartLocalTuple_π]

private noncomputable def AffineIntersectionUnitCocycle.chartTransitionCoordinateIso
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) {T : Scheme.{u}}
    (g : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).V (i, j)) :
    unitObj T ≅ unitObj T :=
  (pullbackUnitIso g).symm ≪≫ (pullback g).mapIso (c.overlapTransitionIso i j) ≪≫
    pullbackUnitIso g

private theorem AffineIntersectionUnitCocycle.chartTransitionCoordinateIso_hom
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) {T : Scheme.{u}}
    (g : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).V (i, j)) :
    (c.chartTransitionCoordinateIso hopen hpush i j g).hom =
      c.chartTransitionIsoCoordinatePullback hopen hpush i j g := by
  rw [c.chartTransitionIsoCoordinatePullback_eq]
  rfl

private theorem
    AffineIntersectionUnitCocycle.pullbackUnitIso_hom_comp_chartTransitionCoordinateIso_inv
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) {T : Scheme.{u}}
    (g : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).V (i, j)) :
    (pullbackUnitIso g).hom ≫
        (c.chartTransitionCoordinateIso hopen hpush i j g).inv =
      (pullback g).map (c.overlapTransitionIso i j).inv ≫
        (pullbackUnitIso g).hom := by
  dsimp only [AffineIntersectionUnitCocycle.chartTransitionCoordinateIso]
  simp

private theorem AffineIntersectionUnitCocycle.chartTransitionCoordinate_inv_comp
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j k : J) :
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    (c.chartTransitionCoordinateIso hopen hpush i k t.p₁₃).inv ≫
        c.chartTransitionIsoCoordinatePullback hopen hpush i j t.p₁₂ =
      (c.chartTransitionCoordinateIso hopen hpush j k t.p₂₃).inv := by
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  have h := c.chartTransitionIsoCoordinatePullback_cocycle hopen hpush i j k
  dsimp only at h
  have hp₁₂ : t.p₁₂ = Spec.map (CommRingCat.ofHom ((F.map
      (Scheme.GlueData.affineIntersectionPairToTripleLeft i j k)).hom.toRingHom)) := by
    rfl
  have hp₂₃ : t.p₂₃ = Spec.map (CommRingCat.ofHom ((F.map
      (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j k)).hom.toRingHom)) := by
    rfl
  have hp₁₃ : t.p₁₃ = Spec.map (CommRingCat.ofHom ((F.map
      (Scheme.GlueData.affineIntersectionPairToTripleRight i j k)).hom.toRingHom)) := by
    rfl
  have ht :
      c.chartTransitionIsoCoordinatePullback hopen hpush i j t.p₁₂ ≫
          c.chartTransitionIsoCoordinatePullback hopen hpush j k t.p₂₃ =
        c.chartTransitionIsoCoordinatePullback hopen hpush i k t.p₁₃ := by
    rw [hp₁₂, hp₂₃, hp₁₃]
    exact h
  let eij := c.chartTransitionCoordinateIso hopen hpush i j t.p₁₂
  let ejk := c.chartTransitionCoordinateIso hopen hpush j k t.p₂₃
  let eik := c.chartTransitionCoordinateIso hopen hpush i k t.p₁₃
  have hij : eij.hom =
      c.chartTransitionIsoCoordinatePullback hopen hpush i j t.p₁₂ := by
    dsimp only [eij]
    exact c.chartTransitionCoordinateIso_hom hopen hpush i j t.p₁₂
  have hjk : ejk.hom =
      c.chartTransitionIsoCoordinatePullback hopen hpush j k t.p₂₃ := by
    dsimp only [ejk]
    exact c.chartTransitionCoordinateIso_hom hopen hpush j k t.p₂₃
  have hik : eik.hom =
      c.chartTransitionIsoCoordinatePullback hopen hpush i k t.p₁₃ := by
    dsimp only [eik]
    exact c.chartTransitionCoordinateIso_hom hopen hpush i k t.p₁₃
  have he : eij.hom ≫ ejk.hom = eik.hom := by
    have hleft : eij.hom ≫ ejk.hom =
        c.chartTransitionIsoCoordinatePullback hopen hpush i j t.p₁₂ ≫
          c.chartTransitionIsoCoordinatePullback hopen hpush j k t.p₂₃ :=
      congrArg₂ (fun p q ↦ p ≫ q) hij hjk
    exact hleft.trans (ht.trans hik.symm)
  rw [← cancel_mono ejk.hom, Category.assoc]
  rw [← c.chartTransitionCoordinateIso_hom hopen hpush i j t.p₁₂]
  change eik.inv ≫ eij.hom ≫ ejk.hom = ejk.inv ≫ ejk.hom
  rw [he]
  simp

private noncomputable def AffineIntersectionUnitCocycle.chartGlueTarget
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    D.glued.Modules :=
  ∏ᶜ fun ij : J × J ↦ c.overlapExtension hopen hpush ij.1 ij.2

/-- Over a fixed chart, the restricted Cech target is the product of the
structure sheaves pushed forward from the canonical triple intersections. -/
noncomputable def AffineIntersectionUnitCocycle.chartGlueTargetRestrictIso
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).obj
        (c.chartGlueTarget hopen hpush) ≅
      ∏ᶜ fun ij : J × J ↦
        let t := affineIntersectionChartChosenPullback₃ hopen hpush ij.1 ij.2 k
        (pushforward t.p₃).obj (unitObj t.pullback) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  letI : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  exact restrictProductIso (D.ι k)
    (fun ij : J × J ↦ c.overlapExtension hopen hpush ij.1 ij.2)
    (fun ij : J × J ↦
      let t := affineIntersectionChartChosenPullback₃ hopen hpush ij.1 ij.2 k
      (pushforward t.p₃).obj (unitObj t.pullback))
    (fun ij ↦ c.overlapExtensionRestrictIso hopen hpush k ij.1 ij.2)

@[reassoc]
theorem AffineIntersectionUnitCocycle.chartGlueTargetRestrictIso_hom_π
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) (ij : J × J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (c.chartGlueTargetRestrictIso hopen hpush k).hom ≫
        Pi.π (fun lm : J × J ↦
          let t := affineIntersectionChartChosenPullback₃ hopen hpush lm.1 lm.2 k
          (pushforward t.p₃).obj (unitObj t.pullback)) ij =
      (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (Pi.π (fun lm : J × J ↦
            c.overlapExtension hopen hpush lm.1 lm.2) ij) ≫
        (c.overlapExtensionRestrictIso hopen hpush k ij.1 ij.2).hom := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  letI : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  simpa only [AffineIntersectionUnitCocycle.chartGlueTargetRestrictIso,
    AffineIntersectionUnitCocycle.chartGlueTarget] using
    restrictProductIso_hom_π (D.ι k)
      (fun lm : J × J ↦ c.overlapExtension hopen hpush lm.1 lm.2)
      (fun lm : J × J ↦
        let t := affineIntersectionChartChosenPullback₃ hopen hpush lm.1 lm.2 k
        (pushforward t.p₃).obj (unitObj t.pullback))
      (fun lm ↦ c.overlapExtensionRestrictIso hopen hpush k lm.1 lm.2) ij

private noncomputable def AffineIntersectionUnitCocycle.chartGlueLeft
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F) :
    c.chartGlueSource hopen hpush ⟶ c.chartGlueTarget hopen hpush :=
  Pi.lift fun ij ↦
    Pi.π (fun i : J ↦ c.chartExtension hopen hpush i) ij.1 ≫
      c.chartToOverlapLeft hopen hpush ij.1 ij.2

private noncomputable def AffineIntersectionUnitCocycle.chartGlueRight
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F) :
    c.chartGlueSource hopen hpush ⟶ c.chartGlueTarget hopen hpush :=
  Pi.lift fun ij ↦
    Pi.π (fun i : J ↦ c.chartExtension hopen hpush i) ij.2 ≫
      c.chartToOverlapRight hopen hpush ij.1 ij.2

private noncomputable def AffineIntersectionUnitCocycle.chartToOverlapLeftInner
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    unitObj (D.U i) ⟶
      (pushforward (D.f i j)).obj (unitObj (D.V (i, j))) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  exact (pullbackPushforwardAdjunction (D.f i j)).homEquiv _ _
    ((pullbackUnitIso (D.f i j)).hom ≫ (c.overlapTransitionIso i j).hom)

private theorem AffineIntersectionUnitCocycle.chartToOverlapLeftInner_eq
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    c.chartToOverlapLeftInner hopen hpush i j =
      SheafOfModules.unitToPushforwardObjUnit
          (D.f i j).toRingCatSheafHom ≫
        (pushforward (D.f i j)).map (c.overlapTransitionIso i j).hom := by
  dsimp only [AffineIntersectionUnitCocycle.chartToOverlapLeftInner]
  rw [Adjunction.homEquiv_naturality_right]
  rw [ModularCurves.pullbackUnitIso_homEquivLow]
  rfl

private theorem affineIntersectionChartTriple_p₁₂_open
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j k : J) :
    IsOpenImmersion
      (affineIntersectionChartChosenPullback₃ hopen hpush i j k).p₁₂ := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  exact MorphismProperty.of_isPullback t.isPullback₁.flip (D.f_open i k)

private noncomputable def
    AffineIntersectionUnitCocycle.chartToTripleLeftRestricted
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    unitObj (D.V (i, k)) ⟶
      (pushforward t.p₁₃).obj
        ((@restrictFunctor _ _ t.p₁₂
          (affineIntersectionChartTriple_p₁₂_open
            hopen hpush i j k)).obj (unitObj (D.V (i, j)))) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  have Hinner : IsPullback t.p₁₃ t.p₁₂ (D.f i k) (D.f i j) :=
    t.isPullback₁.flip
  letI hfik : IsOpenImmersion (D.f i k) := D.f_open i k
  letI hp₁₂ : IsOpenImmersion t.p₁₂ :=
    affineIntersectionChartTriple_p₁₂_open hopen hpush i j k
  exact (@restrictUnitIso _ _ (D.f i k) hfik).inv ≫
    (@restrictFunctor _ _ (D.f i k) hfik).map
      (c.chartToOverlapLeftInner hopen hpush i j) ≫
    (@restrictPushforwardIsoOfIsPullback _ _ _ _
      (D.f i j) t.p₁₃ t.p₁₂ (D.f i k) hfik hp₁₂ Hinner).hom.app
        (unitObj (D.V (i, j)))

private noncomputable def
    AffineIntersectionUnitCocycle.chartToTripleLeftPullback
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    (pullback t.p₁₃).obj (unitObj (D.V (i, k))) ⟶
      (@restrictFunctor _ _ t.p₁₂
        (affineIntersectionChartTriple_p₁₂_open
          hopen hpush i j k)).obj (unitObj (D.V (i, j))) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  letI hp₁₂ : IsOpenImmersion t.p₁₂ :=
    affineIntersectionChartTriple_p₁₂_open hopen hpush i j k
  exact (pullbackUnitIso t.p₁₃).hom ≫
    (@restrictUnitIso _ _ t.p₁₂ hp₁₂).inv ≫
    (@restrictFunctor _ _ t.p₁₂ hp₁₂).map
      (c.overlapTransitionIso i j).hom

private theorem
    AffineIntersectionUnitCocycle.chartToTripleLeftRestricted_eq
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    c.chartToTripleLeftRestricted hopen hpush k i j =
      (pullbackPushforwardAdjunction t.p₁₃).homEquiv _ _
        (c.chartToTripleLeftPullback hopen hpush k i j) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  have Hinner : IsPullback t.p₁₃ t.p₁₂ (D.f i k) (D.f i j) :=
    t.isPullback₁.flip
  letI hfik : IsOpenImmersion (D.f i k) := D.f_open i k
  letI hp₁₂ : IsOpenImmersion t.p₁₂ :=
    affineIntersectionChartTriple_p₁₂_open hopen hpush i j k
  let rV := @restrictUnitIso _ _ (D.f i k) hfik
  let rU := @restrictUnitIso _ _ t.p₁₂ hp₁₂
  let q := (c.overlapTransitionIso i j).hom
  let unitMap := SheafOfModules.unitToPushforwardObjUnit
    (D.f i j).toRingCatSheafHom
  let unitMap' := SheafOfModules.unitToPushforwardObjUnit
    t.p₁₃.toRingCatSheafHom
  let unitBase := @restrictPushforwardUnitIsoOfIsPullback _ _ _ _
    (D.f i j) t.p₁₃ t.p₁₂ (D.f i k) hfik hp₁₂ Hinner
  let base := @restrictPushforwardIsoOfIsPullback _ _ _ _
    (D.f i j) t.p₁₃ t.p₁₂ (D.f i k) hfik hp₁₂ Hinner
  let restricted := @restrictFunctor _ _ (D.f i k) hfik
  let restricted' := @restrictFunctor _ _ t.p₁₂ hp₁₂
  let localMap := rV.inv ≫
    restricted.map (c.chartToOverlapLeftInner hopen hpush i j) ≫
    base.hom.app (unitObj (D.V (i, j)))
  let beta := (pullbackUnitIso t.p₁₃).hom ≫
    rU.inv ≫ restricted'.map q
  change localMap = (pullbackPushforwardAdjunction t.p₁₃).homEquiv _ _ beta
  have hm := c.chartToOverlapLeftInner_eq hopen hpush i j
  have hmap : restricted.map
      (c.chartToOverlapLeftInner hopen hpush i j) =
    restricted.map unitMap ≫
      restricted.map ((pushforward (D.f i j)).map q) := by
    rw [hm]
    exact restricted.map_comp unitMap ((pushforward (D.f i j)).map q)
  have hunit : rV.inv ≫ restricted.map unitMap =
      unitMap' ≫ unitBase.inv := by
    exact @restrictUnitIso_inv_unitToPushforward _ _ _ _
      (D.f i j) t.p₁₃ t.p₁₂ (D.f i k) hfik hp₁₂ Hinner
  have hbase : unitBase.inv ≫
      restricted.map ((pushforward (D.f i j)).map q) ≫
      base.hom.app (unitObj (D.V (i, j))) =
    (pushforward t.p₁₃).map (rU.inv ≫ restricted'.map q) := by
    exact @restrictPushforwardUnitIso_inv_map _ _ _ _
      (D.f i j) t.p₁₃ t.p₁₂ (D.f i k) hfik hp₁₂ Hinner
      (unitObj (D.V (i, j))) q
  have hmate : (pullbackPushforwardAdjunction t.p₁₃).homEquiv _ _ beta =
      unitMap' ≫
        (pushforward t.p₁₃).map (rU.inv ≫ restricted'.map q) := by
    dsimp only [beta]
    rw [Adjunction.homEquiv_naturality_right]
    rw [ModularCurves.pullbackUnitIso_homEquivLow]
    rfl
  let tail := base.hom.app (unitObj (D.V (i, j)))
  have hmap' := congrArg (fun m => rV.inv ≫ m ≫ tail) hmap
  have hunit' := congrArg (fun m => m ≫
    restricted.map ((pushforward (D.f i j)).map q) ≫ tail) hunit
  have hbase' := congrArg (fun m => unitMap' ≫ m) hbase
  have hchain := hmap'.trans (hunit'.trans (hbase'.trans hmate.symm))
  dsimp only [localMap]
  exact hchain

private theorem
    AffineIntersectionUnitCocycle.chartToTripleLeftPullback_comp_restrictUnitIso
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    c.chartToTripleLeftPullback hopen hpush k i j ≫
        (@restrictUnitIso _ _ t.p₁₂
          (affineIntersectionChartTriple_p₁₂_open hopen hpush i j k)).hom =
      (pullbackUnitIso t.p₁₃).hom ≫
        c.chartTransitionIsoCoordinatePullback hopen hpush i j t.p₁₂ := by
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  letI hp₁₂ : IsOpenImmersion t.p₁₂ :=
    affineIntersectionChartTriple_p₁₂_open hopen hpush i j k
  let q := (c.overlapTransitionIso i j).hom
  dsimp only [AffineIntersectionUnitCocycle.chartToTripleLeftPullback]
  have hconj := restrictUnitIso_conjugate t.p₁₂ q
  have hconj' := congrArg
    (fun m ↦ (pullbackUnitIso t.p₁₃).hom ≫ m) hconj
  have hcoord := c.chartTransitionIsoCoordinatePullback_eq
    hopen hpush i j t.p₁₂
  have hcoord' := congrArg
    (fun m ↦ (pullbackUnitIso t.p₁₃).hom ≫ m) hcoord
  have h := hconj'.trans hcoord'.symm
  convert h using 1 <;> rfl

private theorem pullbackCompCongrIso_unit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h' : X ⟶ Z)
    (h : f ≫ g = h') :
    (pullbackCompCongrIso f g h' h).hom.app (unitObj Z) ≫
        (pullbackUnitIso h').hom =
      (pullback f).map (pullbackUnitIso g).hom ≫
        (pullbackUnitIso f).hom := by
  have hcongr := ModularCurves.pullbackUnitIso_congrLow h
  have hcongr' := congrArg
    (fun m ↦ (pullbackComp f g).hom.app (unitObj Z) ≫ m)
    hcongr
  have hcomp := ModularCurves.pullbackUnitIso_compLow f g
  have hfg := hcongr'.trans hcomp
  dsimp only [pullbackCompCongrIso]
  exact hfg

private theorem
    AffineIntersectionUnitCocycle.chartLocalCompositePullback_eq
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    let q := D.t i k ≫ D.f k i
    (pullback t.p₁₃).map
          ((pullbackUnitIso q).hom ≫ (c.overlapTransitionIso i k).inv) ≫
        c.chartToTripleLeftPullback hopen hpush k i j ≫
        (@restrictUnitIso _ _ t.p₁₂
          (affineIntersectionChartTriple_p₁₂_open hopen hpush i j k)).hom =
      (pullbackCompCongrIso t.p₁₃ q t.p₃ t.p₁₃_p₃).hom.app
          (unitObj (D.U k)) ≫
        (pullbackUnitIso t.p₃).hom ≫
        (c.chartTransitionCoordinateIso hopen hpush i k t.p₁₃).inv ≫
        c.chartTransitionIsoCoordinatePullback hopen hpush i j t.p₁₂ := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  let q := D.t i k ≫ D.f k i
  let alpha := (pullbackUnitIso q).hom ≫ (c.overlapTransitionIso i k).inv
  let compIso := pullbackCompCongrIso t.p₁₃ q t.p₃ t.p₁₃_p₃
  let eik := c.chartTransitionCoordinateIso hopen hpush i k t.p₁₃
  let tij := c.chartTransitionIsoCoordinatePullback hopen hpush i j t.p₁₂
  have htail := c.chartToTripleLeftPullback_comp_restrictUnitIso
    hopen hpush k i j
  have htail' := congrArg
    (fun m ↦ (pullback t.p₁₃).map alpha ≫ m) htail
  have hmap : (pullback t.p₁₃).map alpha =
      (pullback t.p₁₃).map (pullbackUnitIso q).hom ≫
        (pullback t.p₁₃).map (c.overlapTransitionIso i k).inv := by
    exact (pullback t.p₁₃).map_comp _ _
  have hunit : compIso.hom.app (unitObj (D.U k)) ≫
      (pullbackUnitIso t.p₃).hom =
        (pullback t.p₁₃).map (pullbackUnitIso q).hom ≫
          (pullbackUnitIso t.p₁₃).hom :=
    pullbackCompCongrIso_unit t.p₁₃ q t.p₃ t.p₁₃_p₃
  have heik := c.pullbackUnitIso_hom_comp_chartTransitionCoordinateIso_inv
    hopen hpush i k t.p₁₃
  have hmap' := congrArg
    (fun m ↦ m ≫ (pullbackUnitIso t.p₁₃).hom) hmap
  have heik' := congrArg
    (fun m ↦ (pullback t.p₁₃).map (pullbackUnitIso q).hom ≫ m) heik
  have hunit' := congrArg (fun m ↦ m ≫ eik.inv) hunit
  have hhead := hmap'.trans (heik'.symm.trans hunit'.symm)
  have hhead' := congrArg (fun m ↦ m ≫ tij) hhead
  have h := htail'.trans hhead'
  convert h using 1 <;> rfl

private noncomputable def
    AffineIntersectionUnitCocycle.chartLocalComponentLeftBaseChanged
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    unitObj (D.U k) ⟶ (pushforward t.p₃).obj (unitObj t.pullback) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  let q := D.t i k ≫ D.f k i
  have Houter : IsPullback q (D.f i k) (D.ι k) (D.ι i) :=
    (IsPullback.of_isLimit (D.vPullbackConeIsLimit i k)).flip
  have Hinner : IsPullback t.p₁₃ t.p₁₂ (D.f i k) (D.f i j) :=
    t.isPullback₁.flip
  have Hdirect : IsPullback t.p₃ t.p₁₂ (D.ι k) (D.f i j ≫ D.ι i) := by
    have H' := t.isPullback₂.paste_vert (sq j k).isPullback
    rw [t.p₂₃_p₃] at H'
    rw [(sq i j).hp₂] at H'
    exact H'.flip
  letI hιk : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  letI hfik : IsOpenImmersion (D.f i k) := D.f_open i k
  letI hp₁₂ : IsOpenImmersion t.p₁₂ :=
    affineIntersectionChartTriple_p₁₂_open hopen hpush i j k
  exact @restrictPushforwardUnitIsoAfter _ _ _ _ _ _
    (D.f i j) (D.ι i) t.p₁₃ q t.p₃ t.p₁₂ (D.f i k) (D.ι k)
    hp₁₂ hfik hιk Hinner Houter Hdirect t.p₁₃_p₃
    (c.chartLocalTupleComponent hopen hpush k i)
    (c.chartToOverlapLeftInner hopen hpush i j)

private theorem
    AffineIntersectionUnitCocycle.chartLocalComponentLeftBaseChanged_eq
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    let q := D.t i k ≫ D.f k i
    c.chartLocalComponentLeftBaseChanged hopen hpush k i j =
      c.chartLocalTupleComponent hopen hpush k i ≫
        (pushforward q).map
          (c.chartToTripleLeftRestricted hopen hpush k i j) ≫
        (pushforwardComp t.p₁₃ q).hom.app _ ≫
        (pushforwardCongr t.p₁₃_p₃).hom.app _ ≫
        (pushforward t.p₃).map
          (@restrictUnitIso _ _ t.p₁₂
            (affineIntersectionChartTriple_p₁₂_open
              hopen hpush i j k)).hom := by
  rfl

private noncomputable def
    AffineIntersectionUnitCocycle.chartLocalComponentLeftBeforeBaseChange
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    unitObj (D.U k) ⟶ (pushforward t.p₃).obj (unitObj t.pullback) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  let q := D.t i k ≫ D.f k i
  have Houter : IsPullback q (D.f i k) (D.ι k) (D.ι i) :=
    (IsPullback.of_isLimit (D.vPullbackConeIsLimit i k)).flip
  have Hinner : IsPullback t.p₁₃ t.p₁₂ (D.f i k) (D.f i j) :=
    t.isPullback₁.flip
  have Hdirect : IsPullback t.p₃ t.p₁₂ (D.ι k) (D.f i j ≫ D.ι i) := by
    have H' := t.isPullback₂.paste_vert (sq j k).isPullback
    rw [t.p₂₃_p₃] at H'
    rw [(sq i j).hp₂] at H'
    exact H'.flip
  letI hιk : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  letI hfik : IsOpenImmersion (D.f i k) := D.f_open i k
  letI hp₁₂ : IsOpenImmersion t.p₁₂ :=
    affineIntersectionChartTriple_p₁₂_open hopen hpush i j k
  exact @restrictPushforwardUnitIsoBefore _ _ _ _ _ _
    (D.f i j) (D.ι i) t.p₁₃ q t.p₃ t.p₁₂ (D.f i k) (D.ι k)
    hp₁₂ hfik hιk Hinner Houter Hdirect t.p₁₃_p₃
    (c.chartLocalTupleComponent hopen hpush k i)
    (c.chartToOverlapLeftInner hopen hpush i j)

private theorem AffineIntersectionUnitCocycle.chartLocalComponent_left_toBefore
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    c.chartLocalTupleComponent hopen hpush k i ≫
          (c.chartExtensionRestrictIso hopen hpush k i).inv ≫
          (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
            (c.chartToOverlapLeft hopen hpush i j) ≫
          (c.overlapExtensionRestrictIso hopen hpush k i j).hom =
      c.chartLocalComponentLeftBeforeBaseChange hopen hpush k i j := by
  rw [c.chartToOverlapLeft_eq hopen hpush i j]
  rfl

private theorem AffineIntersectionUnitCocycle.chartLocalComponent_left_before_after
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    c.chartLocalComponentLeftBeforeBaseChange hopen hpush k i j =
      c.chartLocalComponentLeftBaseChanged hopen hpush k i j := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  let q := D.t i k ≫ D.f k i
  have Houter : IsPullback q (D.f i k) (D.ι k) (D.ι i) :=
    (IsPullback.of_isLimit (D.vPullbackConeIsLimit i k)).flip
  have Hinner : IsPullback t.p₁₃ t.p₁₂ (D.f i k) (D.f i j) :=
    t.isPullback₁.flip
  have Hdirect : IsPullback t.p₃ t.p₁₂ (D.ι k) (D.f i j ≫ D.ι i) := by
    have H' := t.isPullback₂.paste_vert (sq j k).isPullback
    rw [t.p₂₃_p₃] at H'
    rw [(sq i j).hp₂] at H'
    exact H'.flip
  letI hιk : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  letI hfik : IsOpenImmersion (D.f i k) := D.f_open i k
  letI hp₁₂ : IsOpenImmersion t.p₁₂ :=
    affineIntersectionChartTriple_p₁₂_open hopen hpush i j k
  exact @restrictPushforwardUnitIsoBefore_eq_after _ _ _ _ _ _
    (D.f i j) (D.ι i) t.p₁₃ q t.p₃ t.p₁₂ (D.f i k) (D.ι k)
    hp₁₂ hfik hιk Hinner Houter Hdirect t.p₁₃_p₃
    (c.chartLocalTupleComponent hopen hpush k i)
    (c.chartToOverlapLeftInner hopen hpush i j)

private theorem AffineIntersectionUnitCocycle.chartLocalComponent_left_baseChange
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    c.chartLocalTupleComponent hopen hpush k i ≫
          (c.chartExtensionRestrictIso hopen hpush k i).inv ≫
          (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
            (c.chartToOverlapLeft hopen hpush i j) ≫
          (c.overlapExtensionRestrictIso hopen hpush k i j).hom =
      c.chartLocalComponentLeftBaseChanged hopen hpush k i j := by
  exact (c.chartLocalComponent_left_toBefore hopen hpush k i j).trans
    (c.chartLocalComponent_left_before_after hopen hpush k i j)

private noncomputable def AffineIntersectionUnitCocycle.chartLocalLeftMap
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    (pushforward (D.t i k ≫ D.f k i)).obj (unitObj (D.V (i, k))) ⟶
      (pushforward t.p₃).obj (unitObj t.pullback) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
  exact (c.chartExtensionRestrictIso hopen hpush k i).inv ≫
    R.map (c.chartToOverlapLeft hopen hpush i j) ≫
    (c.overlapExtensionRestrictIso hopen hpush k i j).hom

private noncomputable def AffineIntersectionUnitCocycle.chartLocalRightMap
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    (pushforward (D.t j k ≫ D.f k j)).obj (unitObj (D.V (j, k))) ⟶
      (pushforward t.p₃).obj (unitObj t.pullback) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
  exact (c.chartExtensionRestrictIso hopen hpush k j).inv ≫
    R.map (c.chartToOverlapRight hopen hpush i j) ≫
    (c.overlapExtensionRestrictIso hopen hpush k i j).hom

private theorem AffineIntersectionUnitCocycle.chartLocalLeftMap_eq
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    let q := D.t i k ≫ D.f k i
    c.chartLocalLeftMap hopen hpush k i j =
      (pushforward q).map
          (c.chartToTripleLeftRestricted hopen hpush k i j) ≫
        (pushforwardComp t.p₁₃ q).hom.app _ ≫
        (pushforwardCongr t.p₁₃_p₃).hom.app _ ≫
        (pushforward t.p₃).map
          (@restrictUnitIso _ _ t.p₁₂
            (affineIntersectionChartTriple_p₁₂_open
              hopen hpush i j k)).hom := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  let q := D.t i k ≫ D.f k i
  have Houter : IsPullback q (D.f i k) (D.ι k) (D.ι i) :=
    (IsPullback.of_isLimit (D.vPullbackConeIsLimit i k)).flip
  have Hinner : IsPullback t.p₁₃ t.p₁₂ (D.f i k) (D.f i j) :=
    t.isPullback₁.flip
  have Hdirect : IsPullback t.p₃ t.p₁₂ (D.ι k) (D.f i j ≫ D.ι i) := by
    have H' := t.isPullback₂.paste_vert (sq j k).isPullback
    rw [t.p₂₃_p₃] at H'
    rw [(sq i j).hp₂] at H'
    exact H'.flip
  letI hιk : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  letI hfik : IsOpenImmersion (D.f i k) := D.f_open i k
  letI hp₁₂ : IsOpenImmersion t.p₁₂ :=
    affineIntersectionChartTriple_p₁₂_open hopen hpush i j k
  dsimp only
  rw [AffineIntersectionUnitCocycle.chartLocalLeftMap]
  rw [c.chartToOverlapLeft_eq hopen hpush i j]
  have hbase :=
    (@restrictPushforwardUnitIso_inv_map_comp_of_eq
      (D.V (i, j)) (D.U i) D.glued t.pullback (D.V (i, k))
      (D.U (show D.J from k)) _
      (D.f i j) (D.ι i) t.p₁₃ q t.p₃ t.p₁₂ (D.f i k) (D.ι k)
      hp₁₂ hfik hιk Hinner Houter Hdirect t.p₁₃_p₃
      (𝟙 ((pushforward q).obj (unitObj (D.V (i, k)))))
      (c.chartToOverlapLeftInner hopen hpush i j))
  exact hbase

private theorem affineIntersectionChartTriple_p₁₃_right_self_isIso
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i k : J) :
    IsIso (affineIntersectionChartChosenPullback₃ hopen hpush i k k).p₁₃ := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i k k
  letI : IsOpenImmersion (D.f i k) := D.f_open i k
  letI : Mono (D.f i k) := IsOpenImmersion.mono (D.f i k)
  have H : IsPullback t.p₁₂ t.p₁₃ (D.f i k) (D.f i k) :=
    t.isPullback₁
  exact H.isIso_snd_iso_of_mono (inst := IsOpenImmersion.mono (D.f i k))

private theorem
    AffineIntersectionUnitCocycle.chartToTripleLeftRestricted_right_self_isIso
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i : J) :
    IsIso (c.chartToTripleLeftRestricted hopen hpush k i k) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i k k
  letI : IsIso t.p₁₃ :=
    affineIntersectionChartTriple_p₁₃_right_self_isIso hopen hpush i k
  letI : (pullback t.p₁₃).IsEquivalence :=
    pullback_isEquivalence_of_iso (asIso t.p₁₃)
  letI : (pullback t.p₁₃).Full := by infer_instance
  letI : (pullback t.p₁₃).Faithful := by infer_instance
  letI : IsIso (pullbackPushforwardAdjunction t.p₁₃).unit := by
    infer_instance
  letI : IsIso
      (c.chartToTripleLeftPullback hopen hpush k i k) := by
    let p := (pullbackUnitIso t.p₁₃).hom
    let r := (@restrictUnitIso _ _ t.p₁₂
      (affineIntersectionChartTriple_p₁₂_open hopen hpush i k k)).inv
    let m := (@restrictFunctor _ _ t.p₁₂
      (affineIntersectionChartTriple_p₁₂_open hopen hpush i k k)).map
        (c.overlapTransitionIso i k).hom
    have hp : IsIso p := (pullbackUnitIso t.p₁₃).isIso_hom
    have hr : IsIso r :=
      (@restrictUnitIso _ _ t.p₁₂
        (affineIntersectionChartTriple_p₁₂_open hopen hpush i k k)).isIso_inv
    have hm : IsIso m := by
      dsimp only [m]
      exact ((@restrictFunctor _ _ t.p₁₂
        (affineIntersectionChartTriple_p₁₂_open hopen hpush i k k)).mapIso
          (c.overlapTransitionIso i k)).isIso_hom
    change IsIso (p ≫ r ≫ m)
    have hpr : IsIso (p ≫ r) := IsIso.comp_isIso' hp hr
    have hprm : IsIso ((p ≫ r) ≫ m) := IsIso.comp_isIso' hpr hm
    exact hprm
  rw [c.chartToTripleLeftRestricted_eq hopen hpush k i k]
  have heq := Adjunction.homEquiv_apply
    (pullbackPushforwardAdjunction t.p₁₃)
    (unitObj (D.V (i, k)))
    ((@restrictFunctor _ _ t.p₁₂
      (affineIntersectionChartTriple_p₁₂_open hopen hpush i k k)).obj
        (unitObj (D.V (i, k))))
    (c.chartToTripleLeftPullback hopen hpush k i k)
  rw [heq]
  let eunit := (asIso (pullbackPushforwardAdjunction t.p₁₃).unit).app
    (unitObj (D.V (i, k)))
  have hunit : IsIso ((pullbackPushforwardAdjunction t.p₁₃).unit.app
      (unitObj (D.V (i, k)))) := by
    change IsIso eunit.hom
    exact eunit.isIso_hom
  let emap := (pushforward t.p₁₃).mapIso
    (asIso (c.chartToTripleLeftPullback hopen hpush k i k))
  have hmap : IsIso ((pushforward t.p₁₃).map
      (c.chartToTripleLeftPullback hopen hpush k i k)) := by
    change IsIso emap.hom
    exact emap.isIso_hom
  exact IsIso.comp_isIso' hunit hmap

private theorem AffineIntersectionUnitCocycle.chartLocalLeftMap_right_self_isIso
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i : J) :
    IsIso (c.chartLocalLeftMap hopen hpush k i k) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i k k
  let q := D.t i k ≫ D.f k i
  letI : IsIso (c.chartToTripleLeftRestricted hopen hpush k i k) :=
    c.chartToTripleLeftRestricted_right_self_isIso hopen hpush k i
  rw [c.chartLocalLeftMap_eq hopen hpush k i k]
  let emap := (pushforward q).mapIso
    (asIso (c.chartToTripleLeftRestricted hopen hpush k i k))
  have hmap : IsIso ((pushforward q).map
      (c.chartToTripleLeftRestricted hopen hpush k i k)) := by
    change IsIso emap.hom
    exact emap.isIso_hom
  have hcomp : IsIso ((pushforwardComp t.p₁₃ q).hom.app
      ((@restrictFunctor _ _ t.p₁₂
        (affineIntersectionChartTriple_p₁₂_open hopen hpush i k k)).obj
          (unitObj (D.V (i, k))))) := by
    infer_instance
  have hcongr : IsIso ((pushforwardCongr t.p₁₃_p₃).hom.app
      ((@restrictFunctor _ _ t.p₁₂
        (affineIntersectionChartTriple_p₁₂_open hopen hpush i k k)).obj
          (unitObj (D.V (i, k))))) := by
    infer_instance
  let r := @restrictUnitIso _ _ t.p₁₂
    (affineIntersectionChartTriple_p₁₂_open hopen hpush i k k)
  let er := (pushforward t.p₃).mapIso r
  have hunit : IsIso ((pushforward t.p₃).map r.hom) := by
    change IsIso er.hom
    exact er.isIso_hom
  exact IsIso.comp_isIso' hmap
    (IsIso.comp_isIso' hcomp (IsIso.comp_isIso' hcongr hunit))

private theorem AffineIntersectionUnitCocycle.chartLocalComponent_left
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    c.chartLocalTupleComponent hopen hpush k i ≫
          (c.chartExtensionRestrictIso hopen hpush k i).inv ≫
          (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
            (c.chartToOverlapLeft hopen hpush i j) ≫
          (c.overlapExtensionRestrictIso hopen hpush k i j).hom =
      (pullbackPushforwardAdjunction t.p₃).homEquiv _ _
        ((pullbackUnitIso t.p₃).hom ≫
          (c.chartTransitionCoordinateIso hopen hpush i k t.p₁₃).inv ≫
          c.chartTransitionIsoCoordinatePullback hopen hpush i j t.p₁₂) := by
  refine (c.chartLocalComponent_left_baseChange hopen hpush k i j).trans ?_
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  let q := D.t i k ≫ D.f k i
  let a := (pullbackUnitIso q).hom ≫ (c.overlapTransitionIso i k).inv
  let N := (@restrictFunctor _ _ t.p₁₂
    (affineIntersectionChartTriple_p₁₂_open hopen hpush i j k)).obj
      (unitObj (D.V (i, j)))
  let b := c.chartToTripleLeftPullback hopen hpush k i j
  let r := (@restrictUnitIso _ _ t.p₁₂
    (affineIntersectionChartTriple_p₁₂_open hopen hpush i j k)).hom
  let p := (pullbackUnitIso t.p₃).hom ≫
    (c.chartTransitionCoordinateIso hopen hpush i k t.p₁₃).inv ≫
    c.chartTransitionIsoCoordinatePullback hopen hpush i j t.p₁₂
  let compIso := pullbackCompCongrIso t.p₁₃ q t.p₃ t.p₁₃_p₃
  let pushIso := pushforwardCompCongrIso t.p₁₃ q t.p₃ t.p₁₃_p₃
  let adjComp := pullbackPushforwardCompAdjunction t.p₁₃ q
  change c.chartLocalComponentLeftBaseChanged hopen hpush k i j =
    (pullbackPushforwardAdjunction t.p₃).homEquiv _ _ p
  have hmate : adjComp.homEquiv _ _
        ((pullback t.p₁₃).map a ≫ b) ≫
      pushIso.hom.app N ≫ (pushforward t.p₃).map r =
        (pullbackPushforwardAdjunction t.p₃).homEquiv _ _ p := by
    apply homEquiv_comp_conjugate_iso_cancel_of_comp_eq
      (pullbackPushforwardAdjunction t.p₃) adjComp compIso.hom pushIso
      (conjugateEquiv_pullbackCompCongrIso_hom
        t.p₁₃ q t.p₃ t.p₁₃_p₃)
    exact c.chartLocalCompositePullback_eq hopen hpush k i j
  rw [c.chartLocalComponentLeftBaseChanged_eq hopen hpush k i j]
  rw [c.chartLocalTupleComponent_eq hopen hpush k i]
  rw [c.chartToTripleLeftRestricted_eq hopen hpush k i j]
  have hcombine := pullbackPushforwardAdjunction_comp_homEquiv
    t.p₁₃ q (unitObj (D.U k)) (unitObj (D.V (i, k))) N a b
  have hcombine' := congrArg
    (fun m ↦ m ≫ pushIso.hom.app N ≫ (pushforward t.p₃).map r)
    hcombine.symm
  have hchain := hcombine'.trans hmate
  convert hchain using 1 <;> rfl

private noncomputable def
    AffineIntersectionUnitCocycle.chartToTripleRightRestricted
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (_c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    unitObj (D.V (j, k)) ⟶
      (pushforward t.p₂₃).obj
        ((@restrictFunctor _ _ t.p₁₂
          (affineIntersectionChartTriple_p₁₂_open
            hopen hpush i j k)).obj (unitObj (D.V (i, j)))) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  let f := D.t i j ≫ D.f j i
  letI hfjk : IsOpenImmersion (D.f j k) := D.f_open j k
  letI hp₁₂ : IsOpenImmersion t.p₁₂ :=
    affineIntersectionChartTriple_p₁₂_open hopen hpush i j k
  exact (@restrictUnitIso _ _ (D.f j k) hfjk).inv ≫
    (@restrictFunctor _ _ (D.f j k) hfjk).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
    (@restrictPushforwardIsoOfIsPullback _ _ _ _
      f t.p₂₃ t.p₁₂ (D.f j k) hfjk hp₁₂ t.isPullback₂.flip).hom.app
        (unitObj (D.V (i, j)))

private noncomputable def
    AffineIntersectionUnitCocycle.chartToTripleRightPullback
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (_c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    (pullback t.p₂₃).obj (unitObj (D.V (j, k))) ⟶
      (@restrictFunctor _ _ t.p₁₂
        (affineIntersectionChartTriple_p₁₂_open
          hopen hpush i j k)).obj (unitObj (D.V (i, j))) := by
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  letI hp₁₂ : IsOpenImmersion t.p₁₂ :=
    affineIntersectionChartTriple_p₁₂_open hopen hpush i j k
  exact (pullbackUnitIso t.p₂₃).hom ≫
    (@restrictUnitIso _ _ t.p₁₂ hp₁₂).inv

private theorem
    AffineIntersectionUnitCocycle.chartToTripleRightRestricted_eq
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    c.chartToTripleRightRestricted hopen hpush k i j =
      (pullbackPushforwardAdjunction
        (affineIntersectionChartChosenPullback₃ hopen hpush i j k).p₂₃).homEquiv _ _
          (c.chartToTripleRightPullback hopen hpush k i j) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  let f := D.t i j ≫ D.f j i
  letI hfjk : IsOpenImmersion (D.f j k) := D.f_open j k
  letI hp₁₂ : IsOpenImmersion t.p₁₂ :=
    affineIntersectionChartTriple_p₁₂_open hopen hpush i j k
  let rU := @restrictUnitIso _ _ t.p₁₂ hp₁₂
  let beta := (pullbackUnitIso t.p₂₃).hom ≫ rU.inv
  have hbase := @restrictUnitIso_inv_unitToPushforward_baseChange _ _ _ _
    f t.p₂₃ t.p₁₂ (D.f j k) hfjk hp₁₂ t.isPullback₂.flip
  let adj := pullbackPushforwardAdjunction t.p₂₃
  let p := (pullbackUnitIso t.p₂₃).hom
  let q := rU.inv
  have hmate : (pullbackPushforwardAdjunction t.p₂₃).homEquiv _ _ beta =
      SheafOfModules.unitToPushforwardObjUnit t.p₂₃.toRingCatSheafHom ≫
        (pushforward t.p₂₃).map rU.inv := by
    have hnat : adj.homEquiv _ _ (p ≫ q) =
        adj.homEquiv _ _ p ≫ (pushforward t.p₂₃).map q :=
      adj.homEquiv_naturality_right p q
    have hunit := ModularCurves.pullbackUnitIso_homEquivLow t.p₂₃
    have hunit' := congrArg
      (fun m ↦ m ≫ (pushforward t.p₂₃).map q) hunit
    exact hnat.trans hunit'
  dsimp only [AffineIntersectionUnitCocycle.chartToTripleRightRestricted,
    AffineIntersectionUnitCocycle.chartToTripleRightPullback]
  exact hbase.trans hmate.symm

private noncomputable def
    AffineIntersectionUnitCocycle.chartLocalComponentRightBaseChanged
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    unitObj (D.U k) ⟶ (pushforward t.p₃).obj (unitObj t.pullback) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  let f := D.t i j ≫ D.f j i
  let q := D.t j k ≫ D.f k j
  have Houter : IsPullback q (D.f j k) (D.ι k) (D.ι j) :=
    (IsPullback.of_isLimit (D.vPullbackConeIsLimit j k)).flip
  have Hinner : IsPullback t.p₂₃ t.p₁₂ (D.f j k) f :=
    t.isPullback₂.flip
  have Hdirect : IsPullback t.p₃ t.p₁₂ (D.ι k) (f ≫ D.ι j) := by
    have H' := t.isPullback₂.paste_vert (sq j k).isPullback
    rw [t.p₂₃_p₃] at H'
    exact H'.flip
  letI hιk : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  letI hfjk : IsOpenImmersion (D.f j k) := D.f_open j k
  letI hp₁₂ : IsOpenImmersion t.p₁₂ :=
    affineIntersectionChartTriple_p₁₂_open hopen hpush i j k
  exact @restrictPushforwardUnitIsoAfter _ _ _ _ _ _
    f (D.ι j) t.p₂₃ q t.p₃ t.p₁₂ (D.f j k) (D.ι k)
    hp₁₂ hfjk hιk Hinner Houter Hdirect t.p₂₃_p₃
    (c.chartLocalTupleComponent hopen hpush k j)
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)

private theorem
    AffineIntersectionUnitCocycle.chartLocalComponentRightBaseChanged_eq
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    let q := D.t j k ≫ D.f k j
    c.chartLocalComponentRightBaseChanged hopen hpush k i j =
      c.chartLocalTupleComponent hopen hpush k j ≫
        (pushforward q).map
          (c.chartToTripleRightRestricted hopen hpush k i j) ≫
        (pushforwardComp t.p₂₃ q).hom.app _ ≫
        (pushforwardCongr t.p₂₃_p₃).hom.app _ ≫
        (pushforward t.p₃).map
          (@restrictUnitIso _ _ t.p₁₂
            (affineIntersectionChartTriple_p₁₂_open
              hopen hpush i j k)).hom := by
  rfl

private noncomputable def
    AffineIntersectionUnitCocycle.chartLocalComponentRightBeforeBaseChange
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    unitObj (D.U k) ⟶ (pushforward t.p₃).obj (unitObj t.pullback) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  let f := D.t i j ≫ D.f j i
  let q := D.t j k ≫ D.f k j
  have Houter : IsPullback q (D.f j k) (D.ι k) (D.ι j) :=
    (IsPullback.of_isLimit (D.vPullbackConeIsLimit j k)).flip
  have Hinner : IsPullback t.p₂₃ t.p₁₂ (D.f j k) f :=
    t.isPullback₂.flip
  have Hdirect : IsPullback t.p₃ t.p₁₂ (D.ι k) (f ≫ D.ι j) := by
    have H' := t.isPullback₂.paste_vert (sq j k).isPullback
    rw [t.p₂₃_p₃] at H'
    exact H'.flip
  letI hιk : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  letI hfjk : IsOpenImmersion (D.f j k) := D.f_open j k
  letI hp₁₂ : IsOpenImmersion t.p₁₂ :=
    affineIntersectionChartTriple_p₁₂_open hopen hpush i j k
  exact @restrictPushforwardUnitIsoBefore _ _ _ _ _ _
    f (D.ι j) t.p₂₃ q t.p₃ t.p₁₂ (D.f j k) (D.ι k)
    hp₁₂ hfjk hιk Hinner Houter Hdirect t.p₂₃_p₃
    (c.chartLocalTupleComponent hopen hpush k j)
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)

private theorem
    AffineIntersectionUnitCocycle.chartLocalComponent_right_toBefore
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    c.chartLocalTupleComponent hopen hpush k j ≫
          (c.chartExtensionRestrictIso hopen hpush k j).inv ≫
          (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
            (c.chartToOverlapRight hopen hpush i j) ≫
          (c.overlapExtensionRestrictIso hopen hpush k i j).hom =
      c.chartLocalComponentRightBeforeBaseChange hopen hpush k i j := by
  rw [c.chartToOverlapRight_eq hopen hpush i j]
  rfl

private theorem
    AffineIntersectionUnitCocycle.chartLocalComponent_right_before_after
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    c.chartLocalComponentRightBeforeBaseChange hopen hpush k i j =
      c.chartLocalComponentRightBaseChanged hopen hpush k i j := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  let f := D.t i j ≫ D.f j i
  let q := D.t j k ≫ D.f k j
  have Houter : IsPullback q (D.f j k) (D.ι k) (D.ι j) :=
    (IsPullback.of_isLimit (D.vPullbackConeIsLimit j k)).flip
  have Hinner : IsPullback t.p₂₃ t.p₁₂ (D.f j k) f :=
    t.isPullback₂.flip
  have Hdirect : IsPullback t.p₃ t.p₁₂ (D.ι k) (f ≫ D.ι j) := by
    have H' := t.isPullback₂.paste_vert (sq j k).isPullback
    rw [t.p₂₃_p₃] at H'
    exact H'.flip
  letI hιk : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  letI hfjk : IsOpenImmersion (D.f j k) := D.f_open j k
  letI hp₁₂ : IsOpenImmersion t.p₁₂ :=
    affineIntersectionChartTriple_p₁₂_open hopen hpush i j k
  exact @restrictPushforwardUnitIsoBefore_eq_after _ _ _ _ _ _
    f (D.ι j) t.p₂₃ q t.p₃ t.p₁₂ (D.f j k) (D.ι k)
    hp₁₂ hfjk hιk Hinner Houter Hdirect t.p₂₃_p₃
    (c.chartLocalTupleComponent hopen hpush k j)
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)

private theorem
    AffineIntersectionUnitCocycle.chartLocalComponent_right_baseChange
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    c.chartLocalTupleComponent hopen hpush k j ≫
          (c.chartExtensionRestrictIso hopen hpush k j).inv ≫
          (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
            (c.chartToOverlapRight hopen hpush i j) ≫
          (c.overlapExtensionRestrictIso hopen hpush k i j).hom =
      c.chartLocalComponentRightBaseChanged hopen hpush k i j := by
  exact (c.chartLocalComponent_right_toBefore hopen hpush k i j).trans
    (c.chartLocalComponent_right_before_after hopen hpush k i j)

private theorem
    AffineIntersectionUnitCocycle.chartLocalCompositeRightPullback_eq
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    let q := D.t j k ≫ D.f k j
    (pullback t.p₂₃).map
          ((pullbackUnitIso q).hom ≫ (c.overlapTransitionIso j k).inv) ≫
        c.chartToTripleRightPullback hopen hpush k i j ≫
        (@restrictUnitIso _ _ t.p₁₂
          (affineIntersectionChartTriple_p₁₂_open hopen hpush i j k)).hom =
      (pullbackCompCongrIso t.p₂₃ q t.p₃ t.p₂₃_p₃).hom.app
          (unitObj (D.U k)) ≫
        (pullbackUnitIso t.p₃).hom ≫
        (c.chartTransitionCoordinateIso hopen hpush j k t.p₂₃).inv := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  let q := D.t j k ≫ D.f k j
  let a := (pullbackUnitIso q).hom ≫ (c.overlapTransitionIso j k).inv
  let compIso := pullbackCompCongrIso t.p₂₃ q t.p₃ t.p₂₃_p₃
  let ejk := c.chartTransitionCoordinateIso hopen hpush j k t.p₂₃
  let r := (@restrictUnitIso _ _ t.p₁₂
    (affineIntersectionChartTriple_p₁₂_open hopen hpush i j k)).hom
  have htail : c.chartToTripleRightPullback hopen hpush k i j ≫ r =
      (pullbackUnitIso t.p₂₃).hom := by
    dsimp only [AffineIntersectionUnitCocycle.chartToTripleRightPullback, r]
    let e := @restrictUnitIso _ _ t.p₁₂
      (affineIntersectionChartTriple_p₁₂_open hopen hpush i j k)
    have hcancel := congrArg
      (fun m ↦ (pullbackUnitIso t.p₂₃).hom ≫ m) e.inv_hom_id
    convert hcancel using 1 <;> rfl
  have htail' := congrArg
    (fun m ↦ (pullback t.p₂₃).map a ≫ m) htail
  have hmap : (pullback t.p₂₃).map a =
      (pullback t.p₂₃).map (pullbackUnitIso q).hom ≫
        (pullback t.p₂₃).map (c.overlapTransitionIso j k).inv := by
    exact (pullback t.p₂₃).map_comp _ _
  have hunit : compIso.hom.app (unitObj (D.U k)) ≫
      (pullbackUnitIso t.p₃).hom =
        (pullback t.p₂₃).map (pullbackUnitIso q).hom ≫
          (pullbackUnitIso t.p₂₃).hom :=
    pullbackCompCongrIso_unit t.p₂₃ q t.p₃ t.p₂₃_p₃
  have hejk := c.pullbackUnitIso_hom_comp_chartTransitionCoordinateIso_inv
    hopen hpush j k t.p₂₃
  have hmap' := congrArg
    (fun m ↦ m ≫ (pullbackUnitIso t.p₂₃).hom) hmap
  have hejk' := congrArg
    (fun m ↦ (pullback t.p₂₃).map (pullbackUnitIso q).hom ≫ m) hejk
  have hunit' := congrArg (fun m ↦ m ≫ ejk.inv) hunit
  have hhead := hmap'.trans (hejk'.symm.trans hunit'.symm)
  have h := htail'.trans hhead
  convert h using 1 <;> rfl

private theorem AffineIntersectionUnitCocycle.chartLocalComponent_right
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    c.chartLocalTupleComponent hopen hpush k j ≫
          (c.chartExtensionRestrictIso hopen hpush k j).inv ≫
          (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
            (c.chartToOverlapRight hopen hpush i j) ≫
          (c.overlapExtensionRestrictIso hopen hpush k i j).hom =
      (pullbackPushforwardAdjunction t.p₃).homEquiv _ _
        ((pullbackUnitIso t.p₃).hom ≫
          (c.chartTransitionCoordinateIso hopen hpush j k t.p₂₃).inv) := by
  refine (c.chartLocalComponent_right_baseChange hopen hpush k i j).trans ?_
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  let q := D.t j k ≫ D.f k j
  let a := (pullbackUnitIso q).hom ≫ (c.overlapTransitionIso j k).inv
  let N := (@restrictFunctor _ _ t.p₁₂
    (affineIntersectionChartTriple_p₁₂_open hopen hpush i j k)).obj
      (unitObj (D.V (i, j)))
  let b := c.chartToTripleRightPullback hopen hpush k i j
  let r := (@restrictUnitIso _ _ t.p₁₂
    (affineIntersectionChartTriple_p₁₂_open hopen hpush i j k)).hom
  let p := (pullbackUnitIso t.p₃).hom ≫
    (c.chartTransitionCoordinateIso hopen hpush j k t.p₂₃).inv
  let compIso := pullbackCompCongrIso t.p₂₃ q t.p₃ t.p₂₃_p₃
  let pushIso := pushforwardCompCongrIso t.p₂₃ q t.p₃ t.p₂₃_p₃
  let adjComp := pullbackPushforwardCompAdjunction t.p₂₃ q
  change c.chartLocalComponentRightBaseChanged hopen hpush k i j =
    (pullbackPushforwardAdjunction t.p₃).homEquiv _ _ p
  have hmate : adjComp.homEquiv _ _
        ((pullback t.p₂₃).map a ≫ b) ≫
      pushIso.hom.app N ≫ (pushforward t.p₃).map r =
        (pullbackPushforwardAdjunction t.p₃).homEquiv _ _ p := by
    apply homEquiv_comp_conjugate_iso_cancel_of_comp_eq
      (pullbackPushforwardAdjunction t.p₃) adjComp compIso.hom pushIso
      (conjugateEquiv_pullbackCompCongrIso_hom
        t.p₂₃ q t.p₃ t.p₂₃_p₃)
    exact c.chartLocalCompositeRightPullback_eq hopen hpush k i j
  rw [c.chartLocalComponentRightBaseChanged_eq hopen hpush k i j]
  rw [c.chartLocalTupleComponent_eq hopen hpush k j]
  rw [c.chartToTripleRightRestricted_eq hopen hpush k i j]
  have hcombine := pullbackPushforwardAdjunction_comp_homEquiv
    t.p₂₃ q (unitObj (D.U k)) (unitObj (D.V (j, k))) N a b
  have hcombine' := congrArg
    (fun m ↦ m ≫ pushIso.hom.app N ≫ (pushforward t.p₃).map r)
    hcombine.symm
  have hchain := hcombine'.trans hmate
  convert hchain using 1 <;> rfl

private theorem AffineIntersectionUnitCocycle.chartLocalComponent_equalizes
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    c.chartLocalTupleComponent hopen hpush k i ≫
          (c.chartExtensionRestrictIso hopen hpush k i).inv ≫
          (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
            (c.chartToOverlapLeft hopen hpush i j) ≫
          (c.overlapExtensionRestrictIso hopen hpush k i j).hom =
      c.chartLocalTupleComponent hopen hpush k j ≫
          (c.chartExtensionRestrictIso hopen hpush k j).inv ≫
          (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
            (c.chartToOverlapRight hopen hpush i j) ≫
          (c.overlapExtensionRestrictIso hopen hpush k i j).hom := by
  let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
  dsimp only
  rw [c.chartLocalComponent_left hopen hpush k i j,
    c.chartLocalComponent_right hopen hpush k i j]
  have htransition :=
    c.chartTransitionCoordinate_inv_comp hopen hpush i j k
  have htransition' := congrArg
    (fun m ↦ (pullbackUnitIso t.p₃).hom ≫ m) htransition
  have hcoord :
      ((pullbackUnitIso t.p₃).hom ≫
          (c.chartTransitionCoordinateIso hopen hpush i k t.p₁₃).inv) ≫
        c.chartTransitionIsoCoordinatePullback hopen hpush i j t.p₁₂ =
      (pullbackUnitIso t.p₃).hom ≫
        (c.chartTransitionCoordinateIso hopen hpush j k t.p₂₃).inv := by
    exact (Category.assoc _ _ _).trans htransition'
  exact congrArg ((pullbackPushforwardAdjunction t.p₃).homEquiv _ _) hcoord

@[reassoc]
private theorem AffineIntersectionUnitCocycle.chartGlueLeft_π
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    c.chartGlueLeft hopen hpush ≫
        Pi.π (fun lm : J × J ↦
          c.overlapExtension hopen hpush lm.1 lm.2) (i, j) =
      Pi.π (fun l : J ↦ c.chartExtension hopen hpush l) i ≫
        c.chartToOverlapLeft hopen hpush i j := by
  dsimp only [AffineIntersectionUnitCocycle.chartGlueLeft]
  exact Pi.lift_π _ (i, j)

@[reassoc]
private theorem AffineIntersectionUnitCocycle.chartGlueRight_π
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    c.chartGlueRight hopen hpush ≫
        Pi.π (fun lm : J × J ↦
          c.overlapExtension hopen hpush lm.1 lm.2) (i, j) =
      Pi.π (fun l : J ↦ c.chartExtension hopen hpush l) j ≫
        c.chartToOverlapRight hopen hpush i j := by
  dsimp only [AffineIntersectionUnitCocycle.chartGlueRight]
  exact Pi.lift_π _ (i, j)

@[reassoc]
private theorem AffineIntersectionUnitCocycle.restrictChartGlueLeft_π
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (c.chartGlueLeft hopen hpush) ≫
        (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (Pi.π (fun lm : J × J ↦
            c.overlapExtension hopen hpush lm.1 lm.2) (i, j)) =
      (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (Pi.π (fun l : J ↦ c.chartExtension hopen hpush l) i) ≫
      (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (c.chartToOverlapLeft hopen hpush i j) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
  have h := congrArg R.map (c.chartGlueLeft_π hopen hpush i j)
  exact (R.map_comp _ _).symm.trans (h.trans (R.map_comp _ _))

@[reassoc]
private theorem AffineIntersectionUnitCocycle.restrictChartGlueRight_π
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (c.chartGlueRight hopen hpush) ≫
        (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (Pi.π (fun lm : J × J ↦
            c.overlapExtension hopen hpush lm.1 lm.2) (i, j)) =
      (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (Pi.π (fun l : J ↦ c.chartExtension hopen hpush l) j) ≫
      (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (c.chartToOverlapRight hopen hpush i j) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
  have h := congrArg R.map (c.chartGlueRight_π hopen hpush i j)
  exact (R.map_comp _ _).symm.trans (h.trans (R.map_comp _ _))

@[reassoc]
private theorem AffineIntersectionUnitCocycle.restrictChartGlueLeft_target_π
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (c.chartGlueLeft hopen hpush) ≫
        (c.chartGlueTargetRestrictIso hopen hpush k).hom ≫
        Pi.π (fun lm : J × J ↦
          let s := affineIntersectionChartChosenPullback₃
            hopen hpush lm.1 lm.2 k
          (pushforward s.p₃).obj (unitObj s.pullback)) (i, j) =
      (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (Pi.π (fun l : J ↦ c.chartExtension hopen hpush l) i) ≫
        (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (c.chartToOverlapLeft hopen hpush i j) ≫
        (c.overlapExtensionRestrictIso hopen hpush k i j).hom := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
  let e := c.overlapExtensionRestrictIso hopen hpush k i j
  let sourceMap := R.map (c.chartGlueLeft hopen hpush)
  let targetMap := (c.chartGlueTargetRestrictIso hopen hpush k).hom
  let targetProjection := Pi.π (fun lm : J × J ↦
    let s := affineIntersectionChartChosenPullback₃ hopen hpush lm.1 lm.2 k
    (pushforward s.p₃).obj (unitObj s.pullback)) (i, j)
  let overlapProjection := R.map (Pi.π (fun lm : J × J ↦
    c.overlapExtension hopen hpush lm.1 lm.2) (i, j))
  let chartProjection := R.map
    (Pi.π (fun l : J ↦ c.chartExtension hopen hpush l) i)
  let overlapMap := R.map (c.chartToOverlapLeft hopen hpush i j)
  have htarget : targetMap ≫ targetProjection = overlapProjection ≫ e.hom :=
    c.chartGlueTargetRestrictIso_hom_π hopen hpush k (i, j)
  have hleft : sourceMap ≫ overlapProjection = chartProjection ≫ overlapMap :=
    c.restrictChartGlueLeft_π hopen hpush k i j
  have hassocStart : sourceMap ≫ targetMap ≫ targetProjection =
      sourceMap ≫ (targetMap ≫ targetProjection) :=
    Category.assoc sourceMap targetMap targetProjection
  have htarget' : sourceMap ≫ (targetMap ≫ targetProjection) =
      sourceMap ≫ (overlapProjection ≫ e.hom) :=
    congrArg (fun m ↦ sourceMap ≫ m) htarget
  have hassocMiddle : sourceMap ≫ (overlapProjection ≫ e.hom) =
      (sourceMap ≫ overlapProjection) ≫ e.hom :=
    (Category.assoc sourceMap overlapProjection e.hom).symm
  have hleft' : (sourceMap ≫ overlapProjection) ≫ e.hom =
      (chartProjection ≫ overlapMap) ≫ e.hom :=
    congrArg (fun m ↦ m ≫ e.hom) hleft
  exact hassocStart.trans (htarget'.trans (hassocMiddle.trans hleft'))

@[reassoc]
private theorem AffineIntersectionUnitCocycle.restrictChartGlueRight_target_π
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (c.chartGlueRight hopen hpush) ≫
        (c.chartGlueTargetRestrictIso hopen hpush k).hom ≫
        Pi.π (fun lm : J × J ↦
          let s := affineIntersectionChartChosenPullback₃
            hopen hpush lm.1 lm.2 k
          (pushforward s.p₃).obj (unitObj s.pullback)) (i, j) =
      (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (Pi.π (fun l : J ↦ c.chartExtension hopen hpush l) j) ≫
        (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
          (c.chartToOverlapRight hopen hpush i j) ≫
        (c.overlapExtensionRestrictIso hopen hpush k i j).hom := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
  let e := c.overlapExtensionRestrictIso hopen hpush k i j
  let sourceMap := R.map (c.chartGlueRight hopen hpush)
  let targetMap := (c.chartGlueTargetRestrictIso hopen hpush k).hom
  let targetProjection := Pi.π (fun lm : J × J ↦
    let s := affineIntersectionChartChosenPullback₃ hopen hpush lm.1 lm.2 k
    (pushforward s.p₃).obj (unitObj s.pullback)) (i, j)
  let overlapProjection := R.map (Pi.π (fun lm : J × J ↦
    c.overlapExtension hopen hpush lm.1 lm.2) (i, j))
  let chartProjection := R.map
    (Pi.π (fun l : J ↦ c.chartExtension hopen hpush l) j)
  let overlapMap := R.map (c.chartToOverlapRight hopen hpush i j)
  have htarget : targetMap ≫ targetProjection = overlapProjection ≫ e.hom :=
    c.chartGlueTargetRestrictIso_hom_π hopen hpush k (i, j)
  have hright : sourceMap ≫ overlapProjection = chartProjection ≫ overlapMap :=
    c.restrictChartGlueRight_π hopen hpush k i j
  have hassocStart : sourceMap ≫ targetMap ≫ targetProjection =
      sourceMap ≫ (targetMap ≫ targetProjection) :=
    Category.assoc sourceMap targetMap targetProjection
  have htarget' : sourceMap ≫ (targetMap ≫ targetProjection) =
      sourceMap ≫ (overlapProjection ≫ e.hom) :=
    congrArg (fun m ↦ sourceMap ≫ m) htarget
  have hassocMiddle : sourceMap ≫ (overlapProjection ≫ e.hom) =
      (sourceMap ≫ overlapProjection) ≫ e.hom :=
    (Category.assoc sourceMap overlapProjection e.hom).symm
  have hright' : (sourceMap ≫ overlapProjection) ≫ e.hom =
      (chartProjection ≫ overlapMap) ≫ e.hom :=
    congrArg (fun m ↦ m ≫ e.hom) hright
  exact hassocStart.trans (htarget'.trans (hassocMiddle.trans hright'))

private theorem AffineIntersectionUnitCocycle.chartLocalSource_equalizes
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    c.chartLocalSource hopen hpush k ≫
          (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
            (c.chartGlueLeft hopen hpush) =
      c.chartLocalSource hopen hpush k ≫
          (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).map
            (c.chartGlueRight hopen hpush) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
  change c.chartLocalSource hopen hpush k ≫
      R.map (c.chartGlueLeft hopen hpush) =
    c.chartLocalSource hopen hpush k ≫
      R.map (c.chartGlueRight hopen hpush)
  apply (cancel_mono (c.chartGlueTargetRestrictIso hopen hpush k).hom).1
  apply Pi.hom_ext
  rintro ⟨i, j⟩
  let e := c.overlapExtensionRestrictIso hopen hpush k i j
  have hleft := c.restrictChartGlueLeft_target_π hopen hpush k i j
  have hleft' := congrArg
    (fun m ↦ c.chartLocalSource hopen hpush k ≫ m) hleft
  have hsourceLeft := c.chartLocalSource_π hopen hpush k i
  have hsourceLeft' := congrArg
    (fun m ↦ m ≫ R.map (c.chartToOverlapLeft hopen hpush i j) ≫ e.hom)
    hsourceLeft
  have hright := c.restrictChartGlueRight_target_π hopen hpush k i j
  have hright' := congrArg
    (fun m ↦ c.chartLocalSource hopen hpush k ≫ m) hright
  have hsourceRight := c.chartLocalSource_π hopen hpush k j
  have hsourceRight' := congrArg
    (fun m ↦ m ≫ R.map (c.chartToOverlapRight hopen hpush i j) ≫ e.hom)
    hsourceRight
  simp only [Category.assoc] at hleft' hsourceLeft' hright' hsourceRight'
  have hcomponent := c.chartLocalComponent_equalizes hopen hpush k i j
  have hchain := hleft'.trans (hsourceLeft'.trans
    (hcomponent.trans (hsourceRight'.symm.trans hright'.symm)))
  simpa only [R, D, e, Category.assoc] using hchain

/-- The module obtained by gluing the chartwise unit modules along the given
affine-intersection transition cocycle. -/
noncomputable def AffineIntersectionUnitCocycle.gluedModule
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    D.glued.Modules :=
  equalizer (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush)

private noncomputable def
    AffineIntersectionUnitCocycle.chartLocalEqualizerInclusion
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
    R.obj (c.gluedModule hopen hpush) ⟶
      R.obj (c.chartGlueSource hopen hpush) :=
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
  R.map (equalizer.ι
    (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush))

private noncomputable def
    AffineIntersectionUnitCocycle.chartLocalEqualizerComponent
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
    R.obj (c.gluedModule hopen hpush) ⟶
      (pushforward (D.t i k ≫ D.f k i)).obj (unitObj (D.V (i, k))) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
  exact c.chartLocalEqualizerInclusion hopen hpush k ≫
      R.map (Pi.π (fun l : J ↦ c.chartExtension hopen hpush l) i) ≫
    (c.chartExtensionRestrictIso hopen hpush k i).hom

private theorem
    AffineIntersectionUnitCocycle.chartLocalEqualizerComponent_equalizes
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    c.chartLocalEqualizerComponent hopen hpush k i ≫
        c.chartLocalLeftMap hopen hpush k i j =
      c.chartLocalEqualizerComponent hopen hpush k j ≫
        c.chartLocalRightMap hopen hpush k i j := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
  let e := c.overlapExtensionRestrictIso hopen hpush k i j
  let targetIso := c.chartGlueTargetRestrictIso hopen hpush k
  let targetProjection := Pi.π (fun lm : J × J ↦
    let t := affineIntersectionChartChosenPullback₃ hopen hpush lm.1 lm.2 k
    (pushforward t.p₃).obj (unitObj t.pullback)) (i, j)
  have hcondition := congrArg R.map (equalizer.condition
    (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush))
  have hcondition' :
      R.map (equalizer.ι
            (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush)) ≫
          R.map (c.chartGlueLeft hopen hpush) =
        R.map (equalizer.ι
            (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush)) ≫
          R.map (c.chartGlueRight hopen hpush) := by
    simpa only [R.map_comp] using hcondition
  have hcomponent := congrArg
    (fun m ↦ m ≫ targetIso.hom ≫ targetProjection) hcondition'
  have hleft := c.restrictChartGlueLeft_target_π hopen hpush k i j
  have hleft' := congrArg
    (fun m ↦ R.map (equalizer.ι
      (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush)) ≫ m) hleft
  have hright := c.restrictChartGlueRight_target_π hopen hpush k i j
  have hright' := congrArg
    (fun m ↦ R.map (equalizer.ι
      (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush)) ≫ m) hright
  dsimp only [AffineIntersectionUnitCocycle.chartLocalEqualizerComponent,
    AffineIntersectionUnitCocycle.chartLocalEqualizerInclusion,
    AffineIntersectionUnitCocycle.gluedModule,
    AffineIntersectionUnitCocycle.chartLocalLeftMap,
    AffineIntersectionUnitCocycle.chartLocalRightMap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change
    R.map (equalizer.ι
          (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush)) ≫
        R.map (Pi.π (fun l : J ↦ c.chartExtension hopen hpush l) i) ≫
          R.map (c.chartToOverlapLeft hopen hpush i j) ≫ e.hom =
      R.map (equalizer.ι
          (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush)) ≫
        R.map (Pi.π (fun l : J ↦ c.chartExtension hopen hpush l) j) ≫
          R.map (c.chartToOverlapRight hopen hpush i j) ≫ e.hom
  have hchain := hleft'.symm.trans (hcomponent.trans hright')
  convert hchain using 1
  · rfl
  · rfl

private theorem
    AffineIntersectionUnitCocycle.chartLocalTupleComponent_equalizes_maps
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i j : J) :
    c.chartLocalTupleComponent hopen hpush k i ≫
        c.chartLocalLeftMap hopen hpush k i j =
      c.chartLocalTupleComponent hopen hpush k j ≫
        c.chartLocalRightMap hopen hpush k i j := by
  exact c.chartLocalComponent_equalizes hopen hpush k i j

private noncomputable def AffineIntersectionUnitCocycle.chartLocalLift
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    unitObj (D.U k) ⟶
      (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).obj
        (c.gluedModule hopen hpush) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  letI : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
  letI : PreservesLimits R := restrictFunctor_preservesLimits (D.ι k)
  exact equalizer.lift
      (c.chartLocalSource hopen hpush k)
      (c.chartLocalSource_equalizes hopen hpush k) ≫
    (PreservesEqualizer.iso R
      (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush)).inv

@[reassoc]
private theorem AffineIntersectionUnitCocycle.chartLocalLift_ι
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
    c.chartLocalLift hopen hpush k ≫
        R.map (equalizer.ι
          (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush)) =
      c.chartLocalSource hopen hpush k := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  letI : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
  letI : PreservesLimits R := restrictFunctor_preservesLimits (D.ι k)
  dsimp only [AffineIntersectionUnitCocycle.chartLocalLift,
    AffineIntersectionUnitCocycle.gluedModule]
  rw [Category.assoc, PreservesEqualizer.iso_inv_ι, equalizer.lift_ι]

private theorem AffineIntersectionUnitCocycle.chartLocalTupleComponent_self_isIso
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) :
    IsIso (c.chartLocalTupleComponent hopen hpush k k) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let h := D.t k k ≫ D.f k k
  letI : IsIso (D.t k k) := by
    rw [D.t_id]
    infer_instance
  letI : IsIso (D.f k k) := D.f_id k
  letI : IsIso h := inferInstance
  letI : (pullback h).IsEquivalence :=
    pullback_isEquivalence_of_iso (asIso h)
  letI : (pullback h).Full := by infer_instance
  letI : (pullback h).Faithful := by infer_instance
  letI : IsIso (pullbackPushforwardAdjunction h).unit := by infer_instance
  have hunit : IsIso ((pullbackPushforwardAdjunction h).unit.app
      (unitObj (D.U k))) := by infer_instance
  have hmap : IsIso ((pushforward h).map (pullbackUnitIso h).hom) := by
    infer_instance
  rw [c.chartLocalTupleComponent_eq hopen hpush k k]
  rw [c.overlapTransitionIso_self]
  simp only [Iso.refl_inv, Category.comp_id]
  change IsIso ((pullbackPushforwardAdjunction h).homEquiv _ _
    (pullbackUnitIso h).hom)
  rw [Adjunction.homEquiv_apply]
  exact IsIso.comp_isIso' hunit hmap

private noncomputable def AffineIntersectionUnitCocycle.chartLocalProjection
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
    R.obj (c.gluedModule hopen hpush) ⟶ unitObj (D.U k) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
  letI : IsIso (c.chartLocalTupleComponent hopen hpush k k) :=
    c.chartLocalTupleComponent_self_isIso hopen hpush k
  exact R.map (equalizer.ι
        (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush)) ≫
      R.map (Pi.π (fun i : J ↦ c.chartExtension hopen hpush i) k) ≫
      (c.chartExtensionRestrictIso hopen hpush k k).hom ≫
    inv (c.chartLocalTupleComponent hopen hpush k k)

private noncomputable def AffineIntersectionUnitCocycle.gluedModuleChartComponent
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i : J) :
    c.gluedModule hopen hpush ⟶ c.chartExtension hopen hpush i :=
  equalizer.ι (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush) ≫
    Pi.π (fun j : J ↦ c.chartExtension hopen hpush j) i

private noncomputable def AffineIntersectionUnitCocycle.gluedModulePullbackHom
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (pullback (D.ι i)).obj (c.gluedModule hopen hpush) ⟶ unitObj (D.U i) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  letI : IsOpenImmersion (D.ι i) := D.ι_isOpenImmersion i
  exact (restrictFunctorIsoPullback (D.ι i)).inv.app
      (c.gluedModule hopen hpush) ≫
    c.chartLocalProjection hopen hpush i

private theorem AffineIntersectionUnitCocycle.chartLocalLift_projection
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) :
    c.chartLocalLift hopen hpush k ≫
        c.chartLocalProjection hopen hpush k = 𝟙 _ := by
  letI : IsIso (c.chartLocalTupleComponent hopen hpush k k) :=
    c.chartLocalTupleComponent_self_isIso hopen hpush k
  dsimp only [AffineIntersectionUnitCocycle.chartLocalProjection]
  rw [c.chartLocalLift_ι_assoc]
  rw [c.chartLocalSource_π_assoc]
  simp

private theorem
    AffineIntersectionUnitCocycle.chartLocalProjection_tupleComponent
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i : J) :
    c.chartLocalProjection hopen hpush k ≫
        c.chartLocalTupleComponent hopen hpush k i =
      c.chartLocalEqualizerComponent hopen hpush k i := by
  letI : IsIso (c.chartLocalTupleComponent hopen hpush k k) :=
    c.chartLocalTupleComponent_self_isIso hopen hpush k
  letI : IsIso (c.chartLocalLeftMap hopen hpush k i k) :=
    c.chartLocalLeftMap_right_self_isIso hopen hpush k i
  apply (cancel_mono (c.chartLocalLeftMap hopen hpush k i k)).1
  have htuple := c.chartLocalTupleComponent_equalizes_maps
    hopen hpush k i k
  have hequalizer := c.chartLocalEqualizerComponent_equalizes
    hopen hpush k i k
  change
    (c.chartLocalEqualizerComponent hopen hpush k k ≫
          inv (c.chartLocalTupleComponent hopen hpush k k) ≫
        c.chartLocalTupleComponent hopen hpush k i) ≫
        c.chartLocalLeftMap hopen hpush k i k =
      c.chartLocalEqualizerComponent hopen hpush k i ≫
        c.chartLocalLeftMap hopen hpush k i k
  simp only [Category.assoc]
  rw [htuple]
  simpa only [IsIso.inv_hom_id_assoc] using hequalizer.symm

private theorem restrictAdjunction_counit_inv_unit
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    inv ((restrictAdjunction f).counit.app (unitObj X)) =
      (restrictUnitIso f).inv ≫
        (restrictFunctor f).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have hq : ((restrictAdjunction f).homEquiv _ _)
      (restrictUnitIso f).hom = q :=
    ModularCurves.restrictAdjunction_homEquiv_restrictUnitIsoLow f
  have hmate := ((restrictAdjunction f).homEquiv _ _).symm_apply_apply
    (restrictUnitIso f).hom
  rw [hq] at hmate
  change (restrictFunctor f).map q ≫
      (restrictAdjunction f).counit.app (unitObj X) =
    (restrictUnitIso f).hom at hmate
  apply (cancel_mono ((restrictAdjunction f).counit.app (unitObj X))).1
  have hleft : inv ((restrictAdjunction f).counit.app (unitObj X)) ≫
      (restrictAdjunction f).counit.app (unitObj X) = 𝟙 _ :=
    IsIso.inv_hom_id _
  have hright : ((restrictUnitIso f).inv ≫ (restrictFunctor f).map q) ≫
      (restrictAdjunction f).counit.app (unitObj X) = 𝟙 _ := by
    let r := restrictUnitIso f
    let m := (restrictFunctor f).map q
    let ε := (restrictAdjunction f).counit.app (unitObj X)
    have hassoc : (r.inv ≫ m) ≫ ε = r.inv ≫ (m ≫ ε) :=
      Category.assoc r.inv m ε
    have hmate' : r.inv ≫ (m ≫ ε) = r.inv ≫ r.hom :=
      congrArg (fun n ↦ r.inv ≫ n) hmate
    have hcancel : r.inv ≫ r.hom = 𝟙 _ := r.inv_hom_id
    exact hassoc.trans (hmate'.trans hcancel)
  exact hleft.trans hright.symm

private theorem
    AffineIntersectionUnitCocycle.chartExtensionRestrictIso_self_counit
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (@restrictFunctorIsoPullback _ _ (D.ι i) (D.ι_isOpenImmersion i)).inv.app
          (c.chartExtension hopen hpush i) ≫
        (c.chartExtensionRestrictIso hopen hpush i i).hom =
      (pullbackPushforwardAdjunction (D.ι i)).counit.app (unitObj (D.U i)) ≫
        c.chartLocalTupleComponent hopen hpush i i := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let f := D.ι i
  let f' := D.t i i ≫ D.f i i
  let iU := D.f i i
  let H : IsPullback f' iU f f :=
    (IsPullback.of_isLimit (D.vPullbackConeIsLimit i i)).flip
  letI : IsOpenImmersion f := D.ι_isOpenImmersion i
  letI : IsOpenImmersion iU := D.f_open i i
  let adjr := restrictAdjunction f
  let adjp := pullbackPushforwardAdjunction f
  let e := restrictPushforwardUnitIsoOfIsPullback f f' iU f H
  let u := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let u' := SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom
  have hcounitInv : inv (adjr.counit.app (unitObj (D.U i))) =
      (restrictUnitIso f).inv ≫ (restrictFunctor f).map u :=
    restrictAdjunction_counit_inv_unit f
  have hbase := restrictUnitIso_inv_unitToPushforward f f' iU f H
  have hbase0 : (restrictUnitIso f).inv ≫
      (restrictFunctor f).map u = u' ≫ e.inv := by
    simpa only [u, u', e] using hbase
  have hbase' : (restrictUnitIso f).inv ≫
        (restrictFunctor f).map u ≫ e.hom = u' := by
    have hbaseWhiskered :
        ((restrictUnitIso f).inv ≫ (restrictFunctor f).map u) ≫ e.hom =
          (u' ≫ e.inv) ≫ e.hom :=
      congrArg (fun m ↦ m ≫ e.hom) hbase0
    have hassoc : (u' ≫ e.inv) ≫ e.hom =
        u' ≫ (e.inv ≫ e.hom) :=
      Category.assoc u' e.inv e.hom
    have hcancel : u' ≫ (e.inv ≫ e.hom) = u' ≫ 𝟙 _ :=
      congrArg (fun m ↦ u' ≫ m) e.inv_hom_id
    have hid : u' ≫ 𝟙 _ = u' := Category.comp_id u'
    exact hbaseWhiskered.trans (hassoc.trans (hcancel.trans hid))
  have htuple : c.chartLocalTupleComponent hopen hpush i i = u' := by
    rw [c.chartLocalTupleComponent_eq hopen hpush i i]
    rw [c.overlapTransitionIso_self]
    simp only [Iso.refl_inv, Category.comp_id]
    exact ModularCurves.pullbackUnitIso_homEquivLow f'
  have hcounitBase : adjr.counit.app (unitObj (D.U i)) ≫
      c.chartLocalTupleComponent hopen hpush i i = e.hom := by
    have htupleInv : c.chartLocalTupleComponent hopen hpush i i =
        inv (adjr.counit.app (unitObj (D.U i))) ≫ e.hom := by
      exact htuple.trans (hbase'.symm.trans
        (congrArg (fun m ↦ m ≫ e.hom) hcounitInv.symm))
    rw [htupleInv, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have huniq := Adjunction.leftAdjointUniq_hom_app_counit
    adjp adjr (unitObj (D.U i))
  change (restrictFunctorIsoPullback f).inv.app
      ((pushforward f).obj (unitObj (D.U i))) ≫
        adjr.counit.app (unitObj (D.U i)) =
      adjp.counit.app (unitObj (D.U i)) at huniq
  change (restrictFunctorIsoPullback f).inv.app
        ((pushforward f).obj (unitObj (D.U i))) ≫ e.hom =
      adjp.counit.app (unitObj (D.U i)) ≫
        c.chartLocalTupleComponent hopen hpush i i
  rw [← hcounitBase]
  calc
    _ = ((restrictFunctorIsoPullback f).inv.app
          ((pushforward f).obj (unitObj (D.U i))) ≫
        adjr.counit.app (unitObj (D.U i))) ≫
          c.chartLocalTupleComponent hopen hpush i i :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg
      (fun m ↦ m ≫ c.chartLocalTupleComponent hopen hpush i i) huniq

private theorem
    AffineIntersectionUnitCocycle.chartLocalEqualizerComponent_eq_chartComponent
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
    c.chartLocalEqualizerComponent hopen hpush k i =
      R.map (c.gluedModuleChartComponent hopen hpush i) ≫
        (c.chartExtensionRestrictIso hopen hpush k i).hom := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
  dsimp only [AffineIntersectionUnitCocycle.chartLocalEqualizerComponent,
    AffineIntersectionUnitCocycle.chartLocalEqualizerInclusion,
    AffineIntersectionUnitCocycle.gluedModuleChartComponent,
    AffineIntersectionUnitCocycle.gluedModule,
    AffineIntersectionUnitCocycle.chartGlueSource]
  rw [R.map_comp]
  exact (Category.assoc _ _ _).symm

private theorem AffineIntersectionUnitCocycle.gluedModuleChartComponent_adjunct
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    ((pullbackPushforwardAdjunction (D.ι i)).homEquiv _ _).symm
        (c.gluedModuleChartComponent hopen hpush i) =
      c.gluedModulePullbackHom hopen hpush i := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let f := D.ι i
  let R := @restrictFunctor _ _ f (D.ι_isOpenImmersion i)
  let P := pullback f
  let M := c.gluedModule hopen hpush
  let N := unitObj (D.U i)
  let q : M ⟶ (pushforward f).obj N :=
    c.gluedModuleChartComponent hopen hpush i
  let tuple := c.chartLocalTupleComponent hopen hpush i i
  let e := c.chartExtensionRestrictIso hopen hpush i i
  let rIso := @restrictFunctorIsoPullback _ _ f (D.ι_isOpenImmersion i)
  let adj := pullbackPushforwardAdjunction f
  letI : IsOpenImmersion (D.ι i) := D.ι_isOpenImmersion i
  letI : IsIso (c.chartLocalTupleComponent hopen hpush i i) :=
    c.chartLocalTupleComponent_self_isIso hopen hpush i
  apply (cancel_mono tuple).1
  dsimp only [AffineIntersectionUnitCocycle.gluedModulePullbackHom]
  rw [Category.assoc, c.chartLocalProjection_tupleComponent hopen hpush i i]
  rw [c.chartLocalEqualizerComponent_eq_chartComponent hopen hpush i i]
  change (adj.homEquiv M N).symm q ≫ tuple =
    (rIso.inv.app M ≫ R.map q) ≫ e.hom
  have hsymm : (adj.homEquiv M N).symm q =
      P.map q ≫ adj.counit.app N :=
    Adjunction.homEquiv_symm_apply adj M N q
  have hsymm' : (adj.homEquiv M N).symm q ≫ tuple =
      (P.map q ≫ adj.counit.app N) ≫ tuple :=
    congrArg (fun m ↦ m ≫ tuple) hsymm
  have hnat : P.map q ≫ rIso.inv.app ((pushforward f).obj N) =
      rIso.inv.app M ≫ R.map q :=
    rIso.inv.naturality q
  have hnat' : (rIso.inv.app M ≫ R.map q) ≫ e.hom =
      (P.map q ≫ rIso.inv.app ((pushforward f).obj N)) ≫ e.hom :=
    congrArg (fun m ↦ m ≫ e.hom) hnat.symm
  have hassoc₁ :
      (P.map q ≫ rIso.inv.app ((pushforward f).obj N)) ≫ e.hom =
        P.map q ≫
          (rIso.inv.app ((pushforward f).obj N) ≫ e.hom) :=
    Category.assoc (P.map q) (rIso.inv.app ((pushforward f).obj N)) e.hom
  have hself : rIso.inv.app ((pushforward f).obj N) ≫ e.hom =
      adj.counit.app N ≫ tuple :=
    c.chartExtensionRestrictIso_self_counit hopen hpush i
  have hself' : P.map q ≫
      (rIso.inv.app ((pushforward f).obj N) ≫ e.hom) =
        P.map q ≫ (adj.counit.app N ≫ tuple) :=
    congrArg (fun m ↦ P.map q ≫ m) hself
  have hassoc₂ : P.map q ≫ (adj.counit.app N ≫ tuple) =
      (P.map q ≫ adj.counit.app N) ≫ tuple :=
    (Category.assoc (P.map q) (adj.counit.app N) tuple).symm
  have hright := hnat'.trans (hassoc₁.trans (hself'.trans hassoc₂))
  exact hsymm'.trans hright.symm

private theorem AffineIntersectionUnitCocycle.gluedModuleChartComponent_overlap
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    c.gluedModuleChartComponent hopen hpush i ≫
        c.chartToOverlapLeft hopen hpush i j =
      c.gluedModuleChartComponent hopen hpush j ≫
        c.chartToOverlapRight hopen hpush i j := by
  have h := congrArg
    (fun m ↦ m ≫ Pi.π (fun lm : J × J ↦
      c.overlapExtension hopen hpush lm.1 lm.2) (i, j))
    (equalizer.condition
      (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush))
  dsimp only [AffineIntersectionUnitCocycle.gluedModuleChartComponent,
    AffineIntersectionUnitCocycle.gluedModule,
    AffineIntersectionUnitCocycle.chartGlueSource]
  calc
    _ = equalizer.ι (c.chartGlueLeft hopen hpush)
          (c.chartGlueRight hopen hpush) ≫
        (Pi.π (fun l : J ↦ c.chartExtension hopen hpush l) i ≫
          c.chartToOverlapLeft hopen hpush i j) := Category.assoc _ _ _
    _ = equalizer.ι (c.chartGlueLeft hopen hpush)
          (c.chartGlueRight hopen hpush) ≫
        (c.chartGlueLeft hopen hpush ≫
          Pi.π (fun lm : J × J ↦
            c.overlapExtension hopen hpush lm.1 lm.2) (i, j)) := congrArg
              (fun m ↦ equalizer.ι (c.chartGlueLeft hopen hpush)
                (c.chartGlueRight hopen hpush) ≫ m)
              (c.chartGlueLeft_π hopen hpush i j).symm
    _ = (equalizer.ι (c.chartGlueLeft hopen hpush)
          (c.chartGlueRight hopen hpush) ≫
        c.chartGlueLeft hopen hpush) ≫
          Pi.π (fun lm : J × J ↦
            c.overlapExtension hopen hpush lm.1 lm.2) (i, j) :=
      (Category.assoc _ _ _).symm
    _ = (equalizer.ι (c.chartGlueLeft hopen hpush)
          (c.chartGlueRight hopen hpush) ≫
        c.chartGlueRight hopen hpush) ≫
          Pi.π (fun lm : J × J ↦
            c.overlapExtension hopen hpush lm.1 lm.2) (i, j) := h
    _ = equalizer.ι (c.chartGlueLeft hopen hpush)
          (c.chartGlueRight hopen hpush) ≫
        (c.chartGlueRight hopen hpush ≫
          Pi.π (fun lm : J × J ↦
            c.overlapExtension hopen hpush lm.1 lm.2) (i, j)) :=
      Category.assoc _ _ _
    _ = equalizer.ι (c.chartGlueLeft hopen hpush)
          (c.chartGlueRight hopen hpush) ≫
        (Pi.π (fun l : J ↦ c.chartExtension hopen hpush l) j ≫
          c.chartToOverlapRight hopen hpush i j) := congrArg
              (fun m ↦ equalizer.ι (c.chartGlueLeft hopen hpush)
                (c.chartGlueRight hopen hpush) ≫ m)
              (c.chartGlueRight_π hopen hpush i j)
    _ = _ := (Category.assoc _ _ _).symm

private theorem AffineIntersectionUnitCocycle.gluedModuleChartComponent_left_mate
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let M := c.gluedModule hopen hpush
    (pullbackPushforwardAdjunction (sq i j).p).homEquiv M
        (unitObj (sq i j).pullback)
        ((pullbackComp (sq i j).p₁ (D.ι i)).inv.app M ≫
          (pullback (sq i j).p₁).map
            (c.gluedModulePullbackHom hopen hpush i) ≫
          (c.chartTransitionIso hopen hpush i j).hom ≫
          (pullbackUnitIso (sq i j).p₂).hom) =
      c.gluedModuleChartComponent hopen hpush i ≫
        c.chartToOverlapLeft hopen hpush i j := by
  dsimp only
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let M := c.gluedModule hopen hpush
  have hmate := pullbackPushforwardAdjunction_homEquiv_comp_inv
    (D.f i j) (D.ι i) M (unitObj (D.U i))
    (unitObj (sq i j).pullback)
    (c.gluedModulePullbackHom hopen hpush i)
    ((c.chartTransitionIso hopen hpush i j).hom ≫
      (pullbackUnitIso (sq i j).p₂).hom)
  have hadj := congrArg
    ((pullbackPushforwardAdjunction (D.ι i)).homEquiv M (unitObj (D.U i)))
    (c.gluedModuleChartComponent_adjunct hopen hpush i)
  have hround :
      ((pullbackPushforwardAdjunction (D.ι i)).homEquiv M (unitObj (D.U i)))
          (((pullbackPushforwardAdjunction (D.ι i)).homEquiv
            M (unitObj (D.U i))).symm
            (c.gluedModuleChartComponent hopen hpush i)) =
        c.gluedModuleChartComponent hopen hpush i :=
    ((pullbackPushforwardAdjunction (D.ι i)).homEquiv
      M (unitObj (D.U i))).apply_symm_apply _
  rw [← hadj, hround] at hmate
  exact hmate

private theorem AffineIntersectionUnitCocycle.gluedModuleChartComponent_right_mate
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let M := c.gluedModule hopen hpush
    let compIso := pullbackCompCongrIso (sq i j).p₂ (D.ι j)
      (sq i j).p (D.glue_condition i j)
    (pullbackPushforwardAdjunction (sq i j).p).homEquiv M
        (unitObj (sq i j).pullback)
        (compIso.inv.app M ≫
          (pullback (sq i j).p₂).map
            (c.gluedModulePullbackHom hopen hpush j) ≫
          (pullbackUnitIso (sq i j).p₂).hom) =
      c.gluedModuleChartComponent hopen hpush j ≫
        c.chartToOverlapRight hopen hpush i j := by
  dsimp only
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let M := c.gluedModule hopen hpush
  have hmate := pullbackPushforwardAdjunction_homEquiv_compCongr_inv
    (D.t i j ≫ D.f j i) (D.ι j) (D.f i j ≫ D.ι i)
    (D.glue_condition i j) M (unitObj (D.U j))
    (unitObj (sq i j).pullback)
    (c.gluedModulePullbackHom hopen hpush j)
    ((pullbackUnitIso (sq i j).p₂).hom)
  have hadj := congrArg
    ((pullbackPushforwardAdjunction (D.ι j)).homEquiv M (unitObj (D.U j)))
    (c.gluedModuleChartComponent_adjunct hopen hpush j)
  have hround :
      ((pullbackPushforwardAdjunction (D.ι j)).homEquiv M (unitObj (D.U j)))
          (((pullbackPushforwardAdjunction (D.ι j)).homEquiv
            M (unitObj (D.U j))).symm
            (c.gluedModuleChartComponent hopen hpush j)) =
        c.gluedModuleChartComponent hopen hpush j :=
    ((pullbackPushforwardAdjunction (D.ι j)).homEquiv
      M (unitObj (D.U j))).apply_symm_apply _
  rw [← hadj, hround] at hmate
  exact hmate

private theorem AffineIntersectionUnitCocycle.gluedModulePullbackHom_overlap
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let M := c.gluedModule hopen hpush
    let rightComp := pullbackCompCongrIso (sq i j).p₂ (D.ι j)
      (sq i j).p (D.glue_condition i j)
    (pullbackComp (sq i j).p₁ (D.ι i)).inv.app M ≫
          (pullback (sq i j).p₁).map
            (c.gluedModulePullbackHom hopen hpush i) ≫
          (c.chartTransitionIso hopen hpush i j).hom ≫
          (pullbackUnitIso (sq i j).p₂).hom =
      rightComp.inv.app M ≫
          (pullback (sq i j).p₂).map
            (c.gluedModulePullbackHom hopen hpush j) ≫
          (pullbackUnitIso (sq i j).p₂).hom := by
  dsimp only
  apply ((pullbackPushforwardAdjunction
    (affineIntersectionChartChosenPullback hopen hpush i j).p).homEquiv
      (c.gluedModule hopen hpush)
      (unitObj
        (affineIntersectionChartChosenPullback hopen hpush i j).pullback)).injective
  exact (c.gluedModuleChartComponent_left_mate hopen hpush i j).trans
    ((c.gluedModuleChartComponent_overlap hopen hpush i j).trans
      (c.gluedModuleChartComponent_right_mate hopen hpush i j).symm)

private theorem AffineIntersectionUnitCocycle.gluedModulePullbackHom_transition
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let M := c.gluedModule hopen hpush
    let rightComp := pullbackCompCongrIso (sq i j).p₂ (D.ι j)
      (sq i j).p (D.glue_condition i j)
    (pullback (sq i j).p₁).map
          (c.gluedModulePullbackHom hopen hpush i) ≫
        (c.chartTransitionIso hopen hpush i j).hom =
      (pullbackComp (sq i j).p₁ (D.ι i)).hom.app M ≫
        rightComp.inv.app M ≫
        (pullback (sq i j).p₂).map
          (c.gluedModulePullbackHom hopen hpush j) := by
  dsimp only [affineIntersectionChartChosenPullback]
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let M := c.gluedModule hopen hpush
  let e := (pullbackComp (D.f i j) (D.ι i)).app M
  let a := (pullback (D.f i j)).map
      (c.gluedModulePullbackHom hopen hpush i) ≫
    (c.chartTransitionIso hopen hpush i j).hom
  let b := (pullbackCompCongrIso (D.t i j ≫ D.f j i) (D.ι j)
        (D.f i j ≫ D.ι i) (D.glue_condition i j)).inv.app M ≫
      (pullback (D.t i j ≫ D.f j i)).map
        (c.gluedModulePullbackHom hopen hpush j)
  let q := (pullbackUnitIso (D.t i j ≫ D.f j i)).hom
  have h : (e.inv ≫ a) ≫ q = b ≫ q := by
    have hoverlap := c.gluedModulePullbackHom_overlap hopen hpush i j
    dsimp only [affineIntersectionChartChosenPullback] at hoverlap
    change e.inv ≫ a ≫ q = b ≫ q at hoverlap
    simpa only [Category.assoc] using hoverlap
  have hab := eq_hom_comp_of_inv_comp_comp_eq e a b q h
  change a = e.hom ≫ b
  exact hab

private theorem pullbackCompCongrIso_hom_refl
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (pullbackCompCongrIso f g (f ≫ g) rfl).hom.app M =
      (pullbackComp f g).hom.app M := by
  change (pullbackComp f g).hom.app M ≫ 𝟙 _ = _
  rw [Category.comp_id]

private theorem pullbackCompCongrIso_inv_proof_irrel
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h' : X ⟶ Z) (h₁ h₂ : f ≫ g = h') (M : Z.Modules) :
    (pullbackCompCongrIso f g h' h₁).inv.app M =
      (pullbackCompCongrIso f g h' h₂).inv.app M := by
  have h : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  rfl

private theorem AffineIntersectionUnitCocycle.chartLocalProjection_source
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) :
    c.chartLocalProjection hopen hpush k ≫
        c.chartLocalSource hopen hpush k =
      c.chartLocalEqualizerInclusion hopen hpush k := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
  apply (cancel_mono (c.chartGlueSourceRestrictIso hopen hpush k).hom).1
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc]
  rw [c.chartGlueSourceRestrictIso_hom_π]
  let e := c.chartExtensionRestrictIso hopen hpush k i
  have hsource := c.chartLocalSource_π hopen hpush k i
  have hsource' := congrArg
    (fun m ↦ c.chartLocalProjection hopen hpush k ≫ m ≫ e.hom) hsource
  have hprojection := c.chartLocalProjection_tupleComponent
    hopen hpush k i
  calc
    c.chartLocalProjection hopen hpush k ≫
          c.chartLocalSource hopen hpush k ≫
        R.map (Pi.π (fun j : J ↦ c.chartExtension hopen hpush j) i) ≫
      e.hom =
        c.chartLocalProjection hopen hpush k ≫
            c.chartLocalTupleComponent hopen hpush k i ≫ e.inv ≫
          e.hom := by simpa only [Category.assoc] using hsource'
    _ = c.chartLocalProjection hopen hpush k ≫
        c.chartLocalTupleComponent hopen hpush k i := by simp
    _ = c.chartLocalEqualizerComponent hopen hpush k i := hprojection
    _ = c.chartLocalEqualizerInclusion hopen hpush k ≫
          R.map (Pi.π (fun j : J ↦ c.chartExtension hopen hpush j) i) ≫
        e.hom := rfl

private theorem AffineIntersectionUnitCocycle.chartLocalLift_inclusion
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) :
    c.chartLocalLift hopen hpush k ≫
        c.chartLocalEqualizerInclusion hopen hpush k =
      c.chartLocalSource hopen hpush k := by
  exact c.chartLocalLift_ι hopen hpush k

private theorem AffineIntersectionUnitCocycle.chartLocalEqualizerInclusion_mono
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) :
    Mono (c.chartLocalEqualizerInclusion hopen hpush k) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  letI : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  let R := @restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)
  letI : PreservesLimits R := restrictFunctor_preservesLimits (D.ι k)
  letI : R.PreservesMonomorphisms := by infer_instance
  letI : Mono (equalizer.ι
      (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush)) := by
    infer_instance
  change Mono (R.map (equalizer.ι
    (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush)))
  infer_instance

private theorem AffineIntersectionUnitCocycle.chartLocalProjection_lift
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) :
    c.chartLocalProjection hopen hpush k ≫
        c.chartLocalLift hopen hpush k = 𝟙 _ := by
  letI : Mono (c.chartLocalEqualizerInclusion hopen hpush k) :=
    c.chartLocalEqualizerInclusion_mono hopen hpush k
  apply (cancel_mono (c.chartLocalEqualizerInclusion hopen hpush k)).1
  rw [Category.assoc, c.chartLocalLift_inclusion hopen hpush k]
  rw [c.chartLocalProjection_source hopen hpush k]
  rw [Category.id_comp]

/-- The Cech equalizer obtained from an affine-intersection unit cocycle restricts
to the structure sheaf on every gluing chart. -/
noncomputable def AffineIntersectionUnitCocycle.gluedModuleRestrictIso
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (k : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (@restrictFunctor _ _ (D.ι k) (D.ι_isOpenImmersion k)).obj
        (c.gluedModule hopen hpush) ≅ unitObj (D.U k) where
  hom := c.chartLocalProjection hopen hpush k
  inv := c.chartLocalLift hopen hpush k
  hom_inv_id := c.chartLocalProjection_lift hopen hpush k
  inv_hom_id := c.chartLocalLift_projection hopen hpush k

/-- The canonical pullback trivialization of the Cech-glued module on a gluing chart. -/
noncomputable def AffineIntersectionUnitCocycle.gluedModuleLocalIso
    {A J : Type u} [CommRing A]
    {F : Functor (Finset J) (CommAlgCat.{u} A)}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (pullback (D.ι i)).obj (c.gluedModule hopen hpush) ≅ unitObj (D.U i) := by
  dsimp only
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  letI : IsOpenImmersion (D.ι i) := D.ι_isOpenImmersion i
  exact (restrictFunctorIsoPullback (D.ι i)).symm.app
      (c.gluedModule hopen hpush) ≪≫
    c.gluedModuleRestrictIso hopen hpush i

private theorem AffineIntersectionUnitCocycle.gluedModuleLocalIso_transition
    {A J : Type u} [CommRing A]
    {F : Functor (Finset J) (CommAlgCat.{u} A)}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let M := c.gluedModule hopen hpush
    (pullback (sq i j).p₁).map (c.gluedModuleLocalIso hopen hpush i).hom ≫
        (c.chartTransitionIso hopen hpush i j).hom =
      (((pullbackComp (sq i j).p₁ (D.ι i)).app M) ≪≫
          ((pullbackCongr (sq i j).hp₁).app M)).hom ≫
        (((pullbackComp (sq i j).p₂ (D.ι j)).app M) ≪≫
          ((pullbackCongr (sq i j).hp₂).app M)).inv ≫
        (pullback (sq i j).p₂).map
          (c.gluedModuleLocalIso hopen hpush j).hom := by
  dsimp only
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let M := c.gluedModule hopen hpush
  change
    (pullback (sq i j).p₁).map
          (c.gluedModulePullbackHom hopen hpush i) ≫
        (c.chartTransitionIso hopen hpush i j).hom = _
  rw [show (((pullbackComp (sq i j).p₁ (D.ι i)).app M) ≪≫
      ((pullbackCongr (sq i j).hp₁).app M)).hom =
        (pullbackComp (sq i j).p₁ (D.ι i)).hom.app M from
    pullbackCompCongrIso_hom_refl (sq i j).p₁ (D.ι i) M]
  rw [show (((pullbackComp (sq i j).p₂ (D.ι j)).app M) ≪≫
      ((pullbackCongr (sq i j).hp₂).app M)).inv =
        (pullbackCompCongrIso (sq i j).p₂ (D.ι j)
          (sq i j).p (D.glue_condition i j)).inv.app M from
    pullbackCompCongrIso_inv_proof_irrel (sq i j).p₂ (D.ι j)
      (sq i j).p (sq i j).hp₂ (D.glue_condition i j) M]
  change
    (pullback (sq i j).p₁).map
          (c.gluedModulePullbackHom hopen hpush i) ≫
        (c.chartTransitionIso hopen hpush i j).hom =
      (pullbackComp (sq i j).p₁ (D.ι i)).hom.app M ≫
        (pullbackCompCongrIso (sq i j).p₂ (D.ι j)
          (sq i j).p (D.glue_condition i j)).inv.app M ≫
        (pullback (sq i j).p₂).map
          (c.gluedModulePullbackHom hopen hpush j)
  exact c.gluedModulePullbackHom_transition hopen hpush i j

private theorem AffineIntersectionUnitCocycle.chartDescentData_hom
    {A J : Type u} [CommRing A]
    {F : Functor (Finset J) (CommAlgCat.{u} A)}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    (c.chartDescentData hopen hpush).hom i j =
      (c.chartTransitionIso hopen hpush i j).hom := by
  change c.chartDescentHom hopen hpush i j = _
  rw [AffineIntersectionUnitCocycle.chartDescentHom_def]

/-- The descent datum induced by the glued Cech equalizer is the datum defined by the
original affine-intersection transition cocycle. -/
noncomputable def AffineIntersectionUnitCocycle.gluedModuleDescentIso
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let sq₃ := affineIntersectionChartChosenPullback₃ hopen hpush
    Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData D.ι).obj
          (c.gluedModule hopen hpush)) ≅
      c.chartDescentData hopen hpush := by
  dsimp only
  refine Pseudofunctor.DescentData'.isoMk
    (c.gluedModuleLocalIso hopen hpush) ?_
  intro i j
  as_aux_lemma =>
    rw [c.chartDescentData_hom hopen hpush i j]
    rw [Pseudofunctor.DescentData'.ofDescentData_hom]
    rw [pullbackPseudofunctor_toDescentData_hom]
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let M := c.gluedModule hopen hpush
    change
      (pullback (sq i j).p₁).map
            (c.gluedModuleLocalIso hopen hpush i).hom ≫
          (c.chartTransitionIso hopen hpush i j).hom =
        ((((pullbackComp (sq i j).p₁ (D.ι i)).app M) ≪≫
              ((pullbackCongr (sq i j).hp₁).app M)).hom ≫
            (((pullbackComp (sq i j).p₂ (D.ι j)).app M) ≪≫
              ((pullbackCongr (sq i j).hp₂).app M)).inv) ≫
          (pullback (sq i j).p₂).map
            (c.gluedModuleLocalIso hopen hpush j).hom
    simpa only [Category.assoc] using
        c.gluedModuleLocalIso_transition hopen hpush i j

private theorem isoComposite_inv_hom_eq_of_stage
    {C : Type u₁} [Category.{u₂} C] {A B M U V W : C}
    (eLeft : A ≅ M) (eRight : B ≅ M) (a : A ≅ U) (b : B ≅ V)
    (uLeft : U ≅ W) (uRight : V ≅ W) (stage : U ⟶ V)
    (hstage : a.hom ≫ stage = eLeft.hom ≫ eRight.inv ≫ b.hom) :
    (eLeft.symm ≪≫ a ≪≫ uLeft).inv ≫
        (eRight.symm ≪≫ b ≪≫ uRight).hom =
      uLeft.inv ≫ stage ≫ uRight.hom := by
  have hcore : a.inv ≫ eLeft.hom ≫ eRight.inv ≫ b.hom = stage := by
    apply (cancel_epi a.hom).1
    simp only [Iso.hom_inv_id_assoc]
    exact hstage.symm
  apply (cancel_epi uLeft.hom).1
  apply (cancel_mono uRight.inv).1
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id]
  exact hcore

section

variable {A J : Type u} [CommRing A]
  {F : Functor (Finset J) (CommAlgCat.{u} A)}
  (c : AffineIntersectionUnitCocycle F)
  (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
  (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)

local notation "D" => Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush

private theorem AffineIntersectionUnitCocycle.gluedModuleStageTransition
    (i j : J) {T : Scheme.{u}}
    (q : T ⟶ (D).glued) (g : T ⟶ (D).V (i, j))
    (gLeft : T ⟶ (D).U i) (gRight : T ⟶ (D).U j)
    (hqLeft : gLeft ≫ (D).ι i = q) (hqRight : gRight ≫ (D).ι j = q)
    (hLeft : g ≫ (D).f i j = gLeft)
    (hRight : g ≫ ((D).t i j ≫ (D).f j i) = gRight) :
    (pullback gLeft).map (c.gluedModuleLocalIso hopen hpush i).hom ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := pullbackPseudofunctor)
          (c.chartTransitionIso hopen hpush i j).hom
          g gLeft gRight hLeft hRight =
      (((pullbackComp gLeft ((D).ι i)).app (c.gluedModule hopen hpush)) ≪≫
          ((pullbackCongr hqLeft).app (c.gluedModule hopen hpush))).hom ≫
        (((pullbackComp gRight ((D).ι j)).app (c.gluedModule hopen hpush)) ≪≫
          ((pullbackCongr hqRight).app (c.gluedModule hopen hpush))).inv ≫
            (pullback gRight).map
              (c.gluedModuleLocalIso hopen hpush j).hom := by
  let E := c.gluedModuleDescentIso hopen hpush
  have hE := Pseudofunctor.DescentData'.comm
    E.hom q gLeft gRight hqLeft hqRight
  rw [Pseudofunctor.DescentData'.pullHom'_ofDescentData_hom] at hE
  rw [pullbackPseudofunctor_toDescentData_hom
    (f := (D).ι) (M := c.gluedModule hopen hpush) (q := q)
    (f₁ := gLeft) (f₂ := gRight) (hf₁ := hqLeft) (hf₂ := hqRight)] at hE
  rw [c.chartDescent_pullHom_eq hopen hpush i j q g gLeft gRight
    hqLeft hqRight hLeft hRight] at hE
  exact hE

/-- On any test scheme mapping through an ordered overlap, the two composite pullbacks of the
canonical chart trivializations of the glued module differ by the pulled-back chart transition. -/
theorem AffineIntersectionUnitCocycle.gluedModuleCompositeTrivialization_transition
    (i j : J) {T : Scheme.{u}}
    (q : T ⟶ (D).glued) (g : T ⟶ (D).V (i, j))
    (gLeft : T ⟶ (D).U i) (gRight : T ⟶ (D).U j)
    (hqLeft : gLeft ≫ (D).ι i = q) (hqRight : gRight ≫ (D).ι j = q)
    (hLeft : g ≫ (D).f i j = gLeft)
    (hRight : g ≫ ((D).t i j ≫ (D).f j i) = gRight) :
    (pullbackCompositeTrivialization gLeft ((D).ι i) q hqLeft
          (c.gluedModule hopen hpush) (c.gluedModuleLocalIso hopen hpush i)).inv ≫
        (pullbackCompositeTrivialization gRight ((D).ι j) q hqRight
          (c.gluedModule hopen hpush) (c.gluedModuleLocalIso hopen hpush j)).hom =
      c.chartTransitionIsoCoordinatePullback hopen hpush i j g := by
  let tLeft := c.gluedModuleLocalIso hopen hpush i
  let tRight := c.gluedModuleLocalIso hopen hpush j
  let eLeft : (pullback gLeft).obj
        ((pullback ((D).ι i)).obj (c.gluedModule hopen hpush)) ≅
      (pullback q).obj (c.gluedModule hopen hpush) :=
    ((pullbackComp gLeft ((D).ι i)).app (c.gluedModule hopen hpush)) ≪≫
      ((pullbackCongr hqLeft).app (c.gluedModule hopen hpush))
  let eRight : (pullback gRight).obj
        ((pullback ((D).ι j)).obj (c.gluedModule hopen hpush)) ≅
      (pullback q).obj (c.gluedModule hopen hpush) :=
    ((pullbackComp gRight ((D).ι j)).app (c.gluedModule hopen hpush)) ≪≫
      ((pullbackCongr hqRight).app (c.gluedModule hopen hpush))
  let a := (pullback gLeft).mapIso tLeft
  let b := (pullback gRight).mapIso tRight
  let stageTransition :
      (pullback gLeft).obj (unitObj ((D).U i)) ⟶
        (pullback gRight).obj (unitObj ((D).U j)) :=
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := pullbackPseudofunctor)
      (c.chartTransitionIso hopen hpush i j).hom
      g gLeft gRight hLeft hRight
  have hE' : a.hom ≫ stageTransition =
      eLeft.hom ≫ eRight.inv ≫ b.hom := by
    exact c.gluedModuleStageTransition hopen hpush i j q g gLeft gRight
      hqLeft hqRight hLeft hRight
  let tailLeft := pullbackCompositeTrivialization gLeft ((D).ι i) q hqLeft
    (c.gluedModule hopen hpush) tLeft
  let tailRight := pullbackCompositeTrivialization gRight ((D).ι j) q hqRight
    (c.gluedModule hopen hpush) tRight
  let manualLeft : (pullback q).obj (c.gluedModule hopen hpush) ≅ unitObj T :=
    eLeft.symm ≪≫ a ≪≫ pullbackUnitIso gLeft
  let manualRight : (pullback q).obj (c.gluedModule hopen hpush) ≅ unitObj T :=
    eRight.symm ≪≫ b ≪≫ pullbackUnitIso gRight
  have tailLeft_eq : tailLeft = manualLeft := by
    dsimp only [tailLeft, manualLeft, eLeft, a]
    exact pullbackCompositeTrivialization_eq gLeft ((D).ι i) q hqLeft
      (c.gluedModule hopen hpush) tLeft
  have tailRight_eq : tailRight = manualRight := by
    dsimp only [tailRight, manualRight, eRight, b]
    exact pullbackCompositeTrivialization_eq gRight ((D).ι j) q hqRight
      (c.gluedModule hopen hpush) tRight
  have hmanual : manualLeft.inv ≫ manualRight.hom =
      (pullbackUnitIso gLeft).inv ≫ stageTransition ≫
        (pullbackUnitIso gRight).hom := by
    exact isoComposite_inv_hom_eq_of_stage eLeft eRight a b
      (pullbackUnitIso gLeft) (pullbackUnitIso gRight) stageTransition hE'
  change tailLeft.inv ≫ tailRight.hom = _
  calc
    tailLeft.inv ≫ tailRight.hom =
        manualLeft.inv ≫ manualRight.hom := by rw [tailLeft_eq, tailRight_eq]
    _ = (pullbackUnitIso gLeft).inv ≫ stageTransition ≫
          (pullbackUnitIso gRight).hom := hmanual
    _ = c.chartTransitionIsoCoordinatePullback hopen hpush i j g :=
      c.chartTransitionPullHom_toUnit hopen hpush i j g gLeft gRight hLeft hRight

end

private def affineIntersectionChartOpen
    (D : Scheme.GlueData.{u}) (k : D.J) : D.glued.Opens :=
  @Scheme.Hom.opensRange _ _ (D.ι k) (D.ι_isOpenImmersion k)

private theorem affineIntersectionChart_iSup_opensRange
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    ⨆ k, affineIntersectionChartOpen D k = ⊤ := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  apply TopologicalSpace.Opens.ext
  rw [TopologicalSpace.Opens.coe_iSup]
  ext x
  simp only [affineIntersectionChartOpen, Set.mem_iUnion,
    TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  exact D.ι_jointly_surjective x

section DescentEffectivity

variable {A J : Type u} [CommRing A]
  {F : Functor (Finset J) (CommAlgCat.{u} A)}
  (c : AffineIntersectionUnitCocycle F)
  (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
  (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)

local notation "D" =>
  Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
local notation "sq" => affineIntersectionChartChosenPullback hopen hpush
local notation "sq₃" => affineIntersectionChartChosenPullback₃ hopen hpush

/-- The canonical comparison between the two iterated pullbacks to a chosen chart overlap. -/
noncomputable def affineIntersectionPullbackComparisonIso
    (M : (D).glued.Modules) (i j : J) :
    (pullback (sq i j).p₁).obj ((pullback ((D).ι i)).obj M) ≅
      (pullback (sq i j).p₂).obj ((pullback ((D).ι j)).obj M) :=
  pullbackDescentComparisonIso (D).ι M (sq i j).p
    (sq i j).p₁ (sq i j).p₂ (sq i j).hp₁ (sq i j).hp₂

theorem affineIntersectionPullbackComparisonIso_hom
    (M : (D).glued.Modules) (i j : J) :
    (affineIntersectionPullbackComparisonIso hopen hpush M i j).hom =
      ((((pullbackComp (sq i j).p₁ ((D).ι i)).app M) ≪≫
          ((pullbackCongr (sq i j).hp₁).app M)).hom ≫
        (((pullbackComp (sq i j).p₂ ((D).ι j)).app M) ≪≫
          ((pullbackCongr (sq i j).hp₂).app M)).inv) :=
  rfl

/-- A family of chart trivializations realizes the transition maps of an
affine-intersection unit cocycle. -/
def AffineIntersectionUnitCocycle.IsCompatibleChartTrivialization
    (M : (D).glued.Modules)
    (e : ∀ i, (pullback ((D).ι i)).obj M ≅ unitObj ((D).U i)) : Prop :=
  ∀ i j,
    (pullback (sq i j).p₁).map (e i).hom ≫
          (c.chartTransitionIso hopen hpush i j).hom =
      ((((pullbackComp (sq i j).p₁ ((D).ι i)).app M) ≪≫
            ((pullbackCongr (sq i j).hp₁).app M)).hom ≫
          (((pullbackComp (sq i j).p₂ ((D).ι j)).app M) ≪≫
            ((pullbackCongr (sq i j).hp₂).app M)).inv) ≫
        (pullback (sq i j).p₂).map (e j).hom

/-- Compatible chart trivializations identify the pullback descent datum of a module
with the descent datum defined by an affine-intersection unit cocycle. -/
noncomputable def AffineIntersectionUnitCocycle.descentIsoOfCompatibleChartTrivialization
    (M : (D).glued.Modules)
    (e : ∀ i, (pullback ((D).ι i)).obj M ≅ unitObj ((D).U i))
    (h : c.IsCompatibleChartTrivialization hopen hpush M e) :
    Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush :=
  pullbackPseudofunctorDescentIsoOfCompatible
    (D).ι M (affineIntersectionChartChosenPullback hopen hpush)
    (affineIntersectionChartChosenPullback₃ hopen hpush)
    (c.chartDescentData hopen hpush) e fun i j ↦
      (congrArg
        (fun m ↦ (pullback (sq i j).p₁).map (e i).hom ≫ m)
        (c.chartDescentData_hom hopen hpush i j)).trans (h i j)

private noncomputable def AffineIntersectionUnitCocycle.descentChartComponent
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush)
    (i : J) :
    M ⟶ c.chartExtension hopen hpush i :=
  (pullbackPushforwardAdjunction ((D).ι i)).homEquiv _ _ (e.hom.hom i)

private noncomputable def AffineIntersectionUnitCocycle.descentChartSource
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush) :
    M ⟶ c.chartGlueSource hopen hpush :=
  Pi.lift fun i ↦ c.descentChartComponent hopen hpush M e i

@[reassoc]
private theorem AffineIntersectionUnitCocycle.descentChartSource_π
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush)
    (i : J) :
    c.descentChartSource hopen hpush M e ≫
        Pi.π (fun j : J ↦ c.chartExtension hopen hpush j) i =
      c.descentChartComponent hopen hpush M e i := by
  exact Pi.lift_π _ i

private theorem AffineIntersectionUnitCocycle.descentIso_transition
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush)
    (i j : J) :
    (pullback (sq i j).p₁).map (e.hom.hom i) ≫
        (c.chartTransitionIso hopen hpush i j).hom =
      (affineIntersectionPullbackComparisonIso hopen hpush M i j).hom ≫
        (pullback (sq i j).p₂).map (e.hom.hom j) := by
  rw [← c.chartDescentData_hom hopen hpush i j]
  exact pullbackPseudofunctorDescentIso_transition
    (D).ι M (affineIntersectionChartChosenPullback hopen hpush)
    (affineIntersectionChartChosenPullback₃ hopen hpush)
    (c.chartDescentData hopen hpush) e i j

private theorem AffineIntersectionUnitCocycle.descentChartComponent_left_mate
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush)
    (i j : J) :
    (pullbackPushforwardAdjunction (sq i j).p).homEquiv M
        (unitObj (sq i j).pullback)
        ((pullbackComp (sq i j).p₁ ((D).ι i)).inv.app M ≫
          (pullback (sq i j).p₁).map (e.hom.hom i) ≫
          (c.chartTransitionIso hopen hpush i j).hom ≫
          (pullbackUnitIso (sq i j).p₂).hom) =
      c.descentChartComponent hopen hpush M e i ≫
        c.chartToOverlapLeft hopen hpush i j := by
  have hmate := pullbackPushforwardAdjunction_homEquiv_comp_inv
    ((D).f i j) ((D).ι i) M (unitObj ((D).U i))
    (unitObj (sq i j).pullback) (e.hom.hom i)
    ((c.chartTransitionIso hopen hpush i j).hom ≫
      (pullbackUnitIso (sq i j).p₂).hom)
  simp only [affineIntersectionChartChosenPullback,
    AffineIntersectionUnitCocycle.descentChartComponent,
    AffineIntersectionUnitCocycle.chartToOverlapLeft] at hmate ⊢
  convert hmate using 1 <;> rfl

private theorem AffineIntersectionUnitCocycle.descentChartComponent_right_mate
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush)
    (i j : J) :
    let compIso := pullbackCompCongrIso (sq i j).p₂ ((D).ι j)
      (sq i j).p ((D).glue_condition i j)
    (pullbackPushforwardAdjunction (sq i j).p).homEquiv M
        (unitObj (sq i j).pullback)
        (compIso.inv.app M ≫
          (pullback (sq i j).p₂).map (e.hom.hom j) ≫
          (pullbackUnitIso (sq i j).p₂).hom) =
      c.descentChartComponent hopen hpush M e j ≫
        c.chartToOverlapRight hopen hpush i j := by
  dsimp only
  have hmate := pullbackPushforwardAdjunction_homEquiv_compCongr_inv
    ((D).t i j ≫ (D).f j i) ((D).ι j)
    ((D).f i j ≫ (D).ι i) ((D).glue_condition i j)
    M (unitObj ((D).U j)) (unitObj (sq i j).pullback)
    (e.hom.hom j) (pullbackUnitIso (sq i j).p₂).hom
  simp only [affineIntersectionChartChosenPullback,
    AffineIntersectionUnitCocycle.descentChartComponent,
    pushforwardCompCongrIso, Iso.trans_hom, NatTrans.comp_app,
    AffineIntersectionUnitCocycle.chartToOverlapRight] at hmate ⊢
  convert hmate using 1 <;> rfl

private theorem AffineIntersectionUnitCocycle.descentChartComponent_overlap
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush)
    (i j : J) :
    c.descentChartComponent hopen hpush M e i ≫
        c.chartToOverlapLeft hopen hpush i j =
      c.descentChartComponent hopen hpush M e j ≫
        c.chartToOverlapRight hopen hpush i j := by
  rw [← c.descentChartComponent_left_mate hopen hpush M e i j,
    ← c.descentChartComponent_right_mate hopen hpush M e i j]
  apply congrArg ((pullbackPushforwardAdjunction (sq i j).p).homEquiv M
    (unitObj (sq i j).pullback))
  let leftComp := (pullbackComp (sq i j).p₁ ((D).ι i)).app M
  let rightComp := pullbackCompCongrIso (sq i j).p₂ ((D).ι j)
    (sq i j).p ((D).glue_condition i j) |>.app M
  let q := (pullbackUnitIso (sq i j).p₂).hom
  have htransition := c.descentIso_transition hopen hpush M e i j
  have hcomparison :
      (affineIntersectionPullbackComparisonIso hopen hpush M i j).hom =
        leftComp.hom ≫ rightComp.inv := by
    change
      (((pullbackComp (sq i j).p₁ ((D).ι i)).app M) ≪≫
          ((pullbackCongr (sq i j).hp₁).app M)).hom ≫
        (((pullbackComp (sq i j).p₂ ((D).ι j)).app M) ≪≫
          ((pullbackCongr (sq i j).hp₂).app M)).inv = _
    rw [show (((pullbackComp (sq i j).p₁ ((D).ι i)).app M) ≪≫
        ((pullbackCongr (sq i j).hp₁).app M)).hom = leftComp.hom from
      pullbackCompCongrIso_hom_refl (sq i j).p₁ ((D).ι i) M]
    rw [show (((pullbackComp (sq i j).p₂ ((D).ι j)).app M) ≪≫
        ((pullbackCongr (sq i j).hp₂).app M)).inv = rightComp.inv from
      pullbackCompCongrIso_inv_proof_irrel (sq i j).p₂ ((D).ι j)
        (sq i j).p (sq i j).hp₂ ((D).glue_condition i j) M]
    rfl
  rw [hcomparison] at htransition
  let rightTail := rightComp.inv ≫
    (pullback (sq i j).p₂).map (e.hom.hom j)
  have hpre := congrArg (fun m ↦ leftComp.inv ≫ m) htransition
  have hcancel : leftComp.inv ≫ (leftComp.hom ≫ rightTail) = rightTail := by
    have hassoc : leftComp.inv ≫ (leftComp.hom ≫ rightTail) =
        (leftComp.inv ≫ leftComp.hom) ≫ rightTail :=
      (Category.assoc _ _ _).symm
    have hunit := congrArg (fun m ↦ m ≫ rightTail) leftComp.inv_hom_id
    exact hassoc.trans (hunit.trans (Category.id_comp rightTail))
  have hcore := hpre.trans hcancel
  have hpost := congrArg (fun m ↦ m ≫ q) hcore
  have hassoc := congrArg (fun m ↦ m ≫ q)
    (Category.assoc leftComp.inv
      ((pullback (sq i j).p₁).map (e.hom.hom i))
      (c.chartTransitionIso hopen hpush i j).hom)
  change leftComp.inv ≫
      (pullback (sq i j).p₁).map (e.hom.hom i) ≫
      (c.chartTransitionIso hopen hpush i j).hom ≫ q =
    rightComp.inv ≫ (pullback (sq i j).p₂).map (e.hom.hom j) ≫ q
  exact hassoc.trans hpost

private theorem AffineIntersectionUnitCocycle.descentChartSource_equalizes
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush) :
    c.descentChartSource hopen hpush M e ≫
        c.chartGlueLeft hopen hpush =
      c.descentChartSource hopen hpush M e ≫
        c.chartGlueRight hopen hpush := by
  apply Pi.hom_ext
  rintro ⟨i, j⟩
  let source := c.descentChartSource hopen hpush M e
  let leftMap := c.chartGlueLeft hopen hpush
  let rightMap := c.chartGlueRight hopen hpush
  let overlapProjection := Pi.π (fun ij : J × J ↦
    c.overlapExtension hopen hpush ij.1 ij.2) (i, j)
  let chartProjection (k : J) := Pi.π (fun l : J ↦
    c.chartExtension hopen hpush l) k
  let toLeft := c.chartToOverlapLeft hopen hpush i j
  let toRight := c.chartToOverlapRight hopen hpush i j
  have hleftProjection := congrArg (fun m ↦ source ≫ m)
    (c.chartGlueLeft_π hopen hpush i j)
  have hleftSource := congrArg (fun m ↦ m ≫ toLeft)
    (c.descentChartSource_π hopen hpush M e i)
  have hleft : (source ≫ leftMap) ≫ overlapProjection =
      c.descentChartComponent hopen hpush M e i ≫ toLeft :=
    (Category.assoc source leftMap overlapProjection).trans
      (hleftProjection.trans
        ((Category.assoc source (chartProjection i) toLeft).symm.trans hleftSource))
  have hrightProjection := congrArg (fun m ↦ source ≫ m)
    (c.chartGlueRight_π hopen hpush i j)
  have hrightSource := congrArg (fun m ↦ m ≫ toRight)
    (c.descentChartSource_π hopen hpush M e j)
  have hright : (source ≫ rightMap) ≫ overlapProjection =
      c.descentChartComponent hopen hpush M e j ≫ toRight :=
    (Category.assoc source rightMap overlapProjection).trans
      (hrightProjection.trans
        ((Category.assoc source (chartProjection j) toRight).symm.trans hrightSource))
  exact hleft.trans
    ((c.descentChartComponent_overlap hopen hpush M e i j).trans hright.symm)

private noncomputable def AffineIntersectionUnitCocycle.descentToGluedHom
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush) :
    M ⟶ c.gluedModule hopen hpush :=
  equalizer.lift (c.descentChartSource hopen hpush M e)
    (c.descentChartSource_equalizes hopen hpush M e)

@[reassoc]
private theorem AffineIntersectionUnitCocycle.descentToGluedHom_ι
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush) :
    c.descentToGluedHom hopen hpush M e ≫
        equalizer.ι (c.chartGlueLeft hopen hpush)
          (c.chartGlueRight hopen hpush) =
      c.descentChartSource hopen hpush M e := by
  exact equalizer.lift_ι _ _

@[reassoc]
private theorem AffineIntersectionUnitCocycle.descentToGluedHom_chartComponent
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush)
    (i : J) :
    c.descentToGluedHom hopen hpush M e ≫
        c.gluedModuleChartComponent hopen hpush i =
      c.descentChartComponent hopen hpush M e i := by
  let p : c.chartGlueSource hopen hpush ⟶
      c.chartExtension hopen hpush i :=
    Pi.π (fun j : J ↦ c.chartExtension hopen hpush j) i
  let g := c.descentToGluedHom hopen hpush M e
  let equalizerInclusion := equalizer.ι
    (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush)
  have hι := c.descentToGluedHom_ι hopen hpush M e
  have hιp := congrArg (fun m ↦ m ≫ p) hι
  calc
    _ = g ≫ (equalizerInclusion ≫ p) := rfl
    _ = (g ≫ equalizerInclusion) ≫ p :=
      (Category.assoc g equalizerInclusion p).symm
    _ = c.descentChartSource hopen hpush M e ≫ p := hιp
    _ = _ := c.descentChartSource_π hopen hpush M e i

private theorem AffineIntersectionUnitCocycle.descentIso_component_isIso
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush)
    (i : J) :
    IsIso (e.hom.hom i) := by
  refine ⟨⟨e.inv.hom i, ?_, ?_⟩⟩
  · have h := congrArg (fun q => q.hom i) e.hom_inv_id
    change e.hom.hom i ≫ e.inv.hom i = 𝟙 _ at h
    exact h
  · have h := congrArg (fun q => q.hom i) e.inv_hom_id
    change e.inv.hom i ≫ e.hom.hom i = 𝟙 _ at h
    exact h

private theorem AffineIntersectionUnitCocycle.descentToGluedHom_pullback
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush)
    (i : J) :
    (pullback ((D).ι i)).map (c.descentToGluedHom hopen hpush M e) ≫
        (c.gluedModuleLocalIso hopen hpush i).hom =
      e.hom.hom i := by
  let adjG := (pullbackPushforwardAdjunction ((D).ι i)).homEquiv
    (c.gluedModule hopen hpush) (unitObj ((D).U i))
  let adjM := (pullbackPushforwardAdjunction ((D).ι i)).homEquiv
    M (unitObj ((D).U i))
  let chart : c.gluedModule hopen hpush ⟶
      (pushforward ((D).ι i)).obj (unitObj ((D).U i)) :=
    c.gluedModuleChartComponent hopen hpush i
  have hround : adjG (adjG.symm chart) = chart := adjG.apply_symm_apply chart
  change
    (pullback ((D).ι i)).map (c.descentToGluedHom hopen hpush M e) ≫
      c.gluedModulePullbackHom hopen hpush i =
      e.hom.hom i
  rw [← c.gluedModuleChartComponent_adjunct hopen hpush i]
  apply ((pullbackPushforwardAdjunction ((D).ι i)).homEquiv
    M (unitObj ((D).U i))).injective
  rw [Adjunction.homEquiv_naturality_left]
  change c.descentToGluedHom hopen hpush M e ≫
      adjG (adjG.symm chart) = adjM (e.hom.hom i)
  rw [hround]
  change c.descentToGluedHom hopen hpush M e ≫
      c.gluedModuleChartComponent hopen hpush i =
    c.descentChartComponent hopen hpush M e i
  exact c.descentToGluedHom_chartComponent hopen hpush M e i

private theorem AffineIntersectionUnitCocycle.descentToGluedHom_pullback_isIso
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush)
    (i : J) :
    IsIso ((pullback ((D).ι i)).map
      (c.descentToGluedHom hopen hpush M e)) := by
  have h := c.descentToGluedHom_pullback hopen hpush M e i
  haveI : IsIso
      ((pullback ((D).ι i)).map (c.descentToGluedHom hopen hpush M e) ≫
        (c.gluedModuleLocalIso hopen hpush i).hom) :=
    h.symm ▸ c.descentIso_component_isIso hopen hpush M e i
  exact IsIso.of_isIso_comp_right _
    (c.gluedModuleLocalIso hopen hpush i).hom

private theorem AffineIntersectionUnitCocycle.descentToGluedHom_restrict_isIso
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush)
    (i : J) :
    IsIso ((@restrictFunctor _ _ ((D).ι i) ((D).ι_isOpenImmersion i)).map
      (c.descentToGluedHom hopen hpush M e)) := by
  letI : IsOpenImmersion ((D).ι i) := (D).ι_isOpenImmersion i
  let R := restrictFunctor ((D).ι i)
  let P := pullback ((D).ι i)
  let E := restrictFunctorIsoPullback ((D).ι i)
  letI : IsIso (P.map (c.descentToGluedHom hopen hpush M e)) :=
    c.descentToGluedHom_pullback_isIso hopen hpush M e i
  have h := E.hom.naturality (c.descentToGluedHom hopen hpush M e)
  haveI : IsIso
      (R.map (c.descentToGluedHom hopen hpush M e) ≫
        E.hom.app (c.gluedModule hopen hpush)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (E.hom.app (c.gluedModule hopen hpush))

private theorem AffineIntersectionUnitCocycle.descentToGluedHom_chartOpen_isIso
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush)
    (i : J) :
    IsIso ((restrictFunctor (affineIntersectionChartOpen (D) i).ι).map
      (c.descentToGluedHom hopen hpush M e)) := by
  let f := (D).ι i
  letI : IsOpenImmersion f := (D).ι_isOpenImmersion i
  let q := f.isoOpensRange
  let r := f.opensRange.ι
  change IsIso ((restrictFunctor r).map
    (c.descentToGluedHom hopen hpush M e))
  letI : (restrictFunctor q.hom).IsEquivalence := by infer_instance
  haveI : IsIso ((restrictFunctor f).map
      (c.descentToGluedHom hopen hpush M e)) :=
    c.descentToGluedHom_restrict_isIso hopen hpush M e i
  let E : restrictFunctor f ≅ restrictFunctor r ⋙ restrictFunctor q.hom :=
    restrictFunctorCongr f.isoOpensRange_hom_ι.symm ≪≫
      restrictFunctorComp q.hom r
  have h := E.hom.naturality (c.descentToGluedHom hopen hpush M e)
  haveI hmapped : IsIso
      ((restrictFunctor r ⋙ restrictFunctor q.hom).map
        (c.descentToGluedHom hopen hpush M e)) := by
    haveI : IsIso
        (E.hom.app M ≫
          (restrictFunctor r ⋙ restrictFunctor q.hom).map
            (c.descentToGluedHom hopen hpush M e)) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_left (E.hom.app M) _
  letI : IsIso ((restrictFunctor q.hom).map
      ((restrictFunctor r).map
        (c.descentToGluedHom hopen hpush M e))) := by
    change IsIso ((restrictFunctor r ⋙ restrictFunctor q.hom).map
      (c.descentToGluedHom hopen hpush M e))
    exact hmapped
  exact isIso_of_reflects_iso _ (restrictFunctor q.hom)

/-- A module on an affine-intersection glued scheme whose induced descent datum
is the datum of a unit cocycle is canonically isomorphic to the concrete Cech
equalizer realizing that cocycle. -/
noncomputable def AffineIntersectionUnitCocycle.gluedModuleIsoOfDescentIso
    (M : (D).glued.Modules)
    (e : Pseudofunctor.DescentData'.ofDescentData sq sq₃
        ((pullbackPseudofunctor.toDescentData (D).ι).obj M) ≅
      c.chartDescentData hopen hpush) :
    M ≅ c.gluedModule hopen hpush := by
  let g := c.descentToGluedHom hopen hpush M e
  letI : IsIso g := isIso_of_isIso_restrict g
    (fun i => affineIntersectionChartOpen (D) i)
    (affineIntersectionChart_iSup_opensRange hopen hpush)
    (fun i => c.descentToGluedHom_chartOpen_isIso hopen hpush M e i)
  exact asIso g

/-- A module with chart trivializations compatible with an affine-intersection unit cocycle
is isomorphic to the concrete Cech equalizer realizing that cocycle. -/
noncomputable def AffineIntersectionUnitCocycle.gluedModuleIsoOfCompatibleChartTrivialization
    (M : (D).glued.Modules)
    (e : ∀ i, (pullback ((D).ι i)).obj M ≅ unitObj ((D).U i))
    (h : c.IsCompatibleChartTrivialization hopen hpush M e) :
    M ≅ c.gluedModule hopen hpush :=
  c.gluedModuleIsoOfDescentIso hopen hpush M
    (c.descentIsoOfCompatibleChartTrivialization hopen hpush M e h)

end DescentEffectivity

private theorem specMap_ΓSpecIso_inv_map_iso_hom
    {A B : CommRingCat.{u}} (φ : A ≅ B) (x : A) :
    (Spec.map φ.inv).appTop.hom
        ((Scheme.ΓSpecIso B).inv.hom (φ.hom.hom x)) =
      (Scheme.ΓSpecIso A).inv.hom x := by
  have hnat : φ.inv ≫ (Scheme.ΓSpecIso A).inv =
      (Scheme.ΓSpecIso B).inv ≫ (Spec.map φ.inv).appTop :=
    Scheme.ΓSpecIso_inv_naturality φ.inv
  have h := ConcreteCategory.congr_hom hnat (φ.hom.hom x)
  have h' := h.symm
  change
    (Spec.map φ.inv).appTop.hom
        ((Scheme.ΓSpecIso B).inv.hom (φ.hom.hom x)) =
      (Scheme.ΓSpecIso A).inv.hom (φ.inv.hom (φ.hom.hom x)) at h'
  have hcancel : φ.inv.hom (φ.hom.hom x) = x :=
    Iso.hom_inv_id_apply φ x
  exact h'.trans (congrArg (Scheme.ΓSpecIso A).inv.hom hcancel)

/-- The overlap section of the affine-intersection cocycle is the original change-of-basis
unit after transport to the geometric intersection open. -/
theorem affineIntersectionUnitCocycle_overlapTransitionSection
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    let c := affineIntersectionUnitCocycle π U e
    let q := π.affineIntersectionOverlapIso U hU i j
    q.inv.appTop.hom (c.overlapTransitionSection i j : _) =
      openTopSection (U i ⊓ U j)
        (trivializingCoverTransitionUnitOn U e (U i ⊓ U j) i j
          inf_le_left inf_le_right : Γ(X, U i ⊓ U j)) := by
  classical
  have hpair :
      X.finiteIntersectionOpen U
          (Scheme.GlueData.affineIntersectionPairIndex i j) = U i ⊓ U j :=
    X.finiteIntersectionOpen_affineIntersectionPairIndex U i j
  let s := Scheme.GlueData.affineIntersectionPairIndex i j
  have hs : s.Nonempty := by
    simp [s, Scheme.GlueData.affineIntersectionPairIndex]
  let q' := π.affineIntersectionSchemeIso U s hs (hU s hs) ≪≫
    X.isoOfEq hpair
  have hq : π.affineIntersectionOverlapIso U hU i j = q' := by
    dsimp only [q', s]
    unfold Scheme.Hom.affineIntersectionOverlapIso
    congr
  dsimp only
  rw [hq]
  let V := X.finiteIntersectionOpen U s
  let hVi : V ≤ U i := iInf_le_of_le i (iInf_le_of_le (by simp
    [s, Scheme.GlueData.affineIntersectionPairIndex]) le_rfl)
  let hVj : V ≤ U j := iInf_le_of_le j (iInf_le_of_le (by simp
    [s, Scheme.GlueData.affineIntersectionPairIndex]) le_rfl)
  let r := trivializingCoverTransitionUnitOn U e V i j hVi hVj
  let φ := π.finiteIntersectionRingIso U s hs
  let A := (forget₂ (CommAlgCat Γ(S, (⊤ : S.Opens))) CommRingCat).obj
    (π.finiteIntersectionRing U s)
  let B := CommRingCat.of ((π.affineIntersectionFunctor U).obj s)
  let E := π.affineIntersectionSchemeIso U s hs (hU s hs)
  letI : IsAffine V.toScheme := hU s hs
  have hsection :
      ((affineIntersectionUnitCocycle π U e).overlapTransitionSection i j : _) =
        (Scheme.ΓSpecIso B).inv.hom
          (φ.hom.hom (V.topIso.inv.hom (r : Γ(X, V)))) := by
    rfl
  rw [hsection]
  change ((E ≪≫ X.isoOfEq hpair).inv.appTop).hom
      ((Scheme.ΓSpecIso B).inv.hom
        (φ.hom.hom (V.topIso.inv.hom (r : Γ(X, V))))) = _
  have hspec :
      (Spec.map φ.inv).appTop.hom
          ((Scheme.ΓSpecIso B).inv.hom
            (φ.hom.hom (V.topIso.inv.hom (r : Γ(X, V))))) =
        (Scheme.ΓSpecIso A).inv.hom (V.topIso.inv.hom (r : Γ(X, V))) := by
    exact specMap_ΓSpecIso_inv_map_iso_hom φ
      (V.topIso.inv.hom (r : Γ(X, V)))
  have hE :
      E.inv.appTop.hom
          ((Scheme.ΓSpecIso B).inv.hom
            (φ.hom.hom (V.topIso.inv.hom (r : Γ(X, V))))) =
        V.topIso.inv.hom (r : Γ(X, V)) := by
    change V.toScheme.isoSpec.hom.appTop.hom
        ((Spec.map φ.inv).appTop.hom
          ((Scheme.ΓSpecIso B).inv.hom
            (φ.hom.hom (V.topIso.inv.hom (r : Γ(X, V)))))) = _
    rw [hspec]
    change V.toScheme.toSpecΓ.appTop.hom
        ((Scheme.ΓSpecIso A).inv.hom (V.topIso.inv.hom (r : Γ(X, V)))) = _
    rw [Scheme.toSpecΓ_appTop]
    exact Iso.inv_hom_id_apply _ _
  rw [Iso.trans_inv, Scheme.Hom.comp_appTop]
  change (X.isoOfEq hpair).inv.appTop.hom
      (E.inv.appTop.hom
        ((Scheme.ΓSpecIso B).inv.hom
          (φ.hom.hom (V.topIso.inv.hom (r : Γ(X, V)))))) = _
  rw [hE]
  let W := U i ⊓ U j
  have htop : V.topIso.inv ≫ (X.homOfLE hpair.ge).appTop =
      X.presheaf.map (homOfLE hpair.ge).op ≫ W.topIso.inv :=
    topIso_inv_naturality hpair.ge
  rw [Scheme.isoOfEq_inv]
  change (V.topIso.inv ≫ (X.homOfLE hpair.ge).appTop).hom (r : Γ(X, V)) = _
  rw [htop]
  change W.topIso.inv.hom
    (X.presheaf.map (homOfLE hpair.ge).op (r : Γ(X, V))) = _
  have hopen (a : Γ(X, W)) :
      openTopSection W a = W.topIso.inv.hom a := by
    unfold openTopSection
    rw [Scheme.Opens.ι_appIso, Scheme.Opens.topIso_inv]
    change X.presheaf.map _ a = X.presheaf.map _ a
    congr 2
  rw [hopen]
  apply congrArg W.topIso.inv.hom
  have hr := congrArg Units.val
    (trivializingCoverTransitionUnitOn_restrict U e hpair.ge i j hVi hVj)
  change X.presheaf.map (homOfLE hpair.ge).op (r : Γ(X, V)) =
    (trivializingCoverTransitionUnitOn U e W i j
      (hpair.ge.trans hVi) (hpair.ge.trans hVj) : Γ(X, W)) at hr
  change X.presheaf.map (homOfLE hpair.ge).op (r : Γ(X, V)) =
    (trivializingCoverTransitionUnitOn U e W i j
      (hpair.ge.trans hVi) (hpair.ge.trans hVj) : Γ(X, W))
  exact hr

/-- Pulling the affine overlap transition to the geometric intersection gives the original
change-of-basis scalar. -/
theorem affineIntersectionUnitCocycle_pullback_overlapTransitionIso
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    let c := affineIntersectionUnitCocycle π U e
    let q := π.affineIntersectionOverlapIso U hU i j
    (pullback q.inv).map (c.overlapTransitionIso i j).hom ≫
        (pullbackUnitIso q.inv).hom =
      (pullbackUnitIso q.inv).hom ≫
        ModularCurves.unitEndomorphismOfTopSection
          (openTopSection (U i ⊓ U j)
            (trivializingCoverTransitionUnitOn U e (U i ⊓ U j) i j
              inf_le_left inf_le_right : Γ(X, U i ⊓ U j))) := by
  dsimp only
  rw [AffineIntersectionUnitCocycle.overlapTransitionIso,
    ModularCurves.unitAutomorphismOfTopUnit_hom, pullbackUnitIso_scalar,
    affineIntersectionUnitCocycle_overlapTransitionSection]

private theorem overlap_common_map
    {C : Type u₁} [Category.{v₁} C]
    {W A B G V X : C}
    (f : W ⟶ A) (p : A ⟶ B) (d : B ⟶ G) (s : A ⟶ G)
    (g : G ⟶ X) (c : B ⟶ V) (ι : V ⟶ X)
    (r : W ⟶ V) (w : W ⟶ X)
    (hp : p ≫ d = s) (hd : d ≫ g = c ≫ ι)
    (hc : (f ≫ p) ≫ c = r) (hι : r ≫ ι = w) :
    (f ≫ s) ≫ g = w := by
  rw [← hp, Category.assoc, Category.assoc, hd]
  rw [← Category.assoc, ← Category.assoc, hc, hι]

/-- On the geometric intersection, the left affine-overlap chart map is the canonical open
inclusion. -/
theorem affineIntersectionOverlapIso_inv_comp_left_chartIso
    {X S : Scheme.{u}} (π : X ⟶ S) {J : Type u}
    (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let q := π.affineIntersectionOverlapIso U hU i j
    (q.inv ≫ (sq i j).p₁) ≫
        (π.affineIntersectionChartIso U hU i).hom =
      X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) := by
  dsimp only [affineIntersectionChartChosenPullback]
  let q := π.affineIntersectionOverlapIso U hU i j
  have h := π.affineIntersectionGlueData_f_chartIso U hU i j
  calc
    (q.inv ≫ (π.affineIntersectionGlueData U hU).f i j) ≫
        (π.affineIntersectionChartIso U hU i).hom =
      q.inv ≫ ((π.affineIntersectionGlueData U hU).f i j ≫
        (π.affineIntersectionChartIso U hU i).hom) :=
          Category.assoc _ _ _
    _ = _ := (congrArg (q.inv ≫ ·) h).trans
      ((π.affineIntersectionOverlapIso U hU i j).inv_hom_id_assoc _)

/-- On the geometric intersection, the right affine-overlap chart map is the canonical open
inclusion. -/
theorem affineIntersectionOverlapIso_inv_comp_right_chartIso
    {X S : Scheme.{u}} (π : X ⟶ S) {J : Type u}
    (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let q := π.affineIntersectionOverlapIso U hU i j
    (q.inv ≫ (sq i j).p₂) ≫
        (π.affineIntersectionChartIso U hU j).hom =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) := by
  dsimp only [affineIntersectionChartChosenPullback]
  let q := π.affineIntersectionOverlapIso U hU i j
  have h := π.affineIntersectionGlueData_t_f_chartIso U hU i j
  calc
    (q.inv ≫ ((π.affineIntersectionGlueData U hU).t i j ≫
        (π.affineIntersectionGlueData U hU).f j i)) ≫
          (π.affineIntersectionChartIso U hU j).hom =
      q.inv ≫ ((π.affineIntersectionGlueData U hU).t i j ≫
        (π.affineIntersectionGlueData U hU).f j i ≫
          (π.affineIntersectionChartIso U hU j).hom) := by
            simp only [Category.assoc]
    _ = _ := (congrArg (q.inv ≫ ·) h).trans
      ((π.affineIntersectionOverlapIso U hU i j).inv_hom_id_assoc _)

/-- The affine overlap, transported to the geometric intersection and then mapped back to the
original scheme, is the canonical inclusion of that intersection. -/
theorem affineIntersectionOverlapIso_inv_comp_gluedToOriginal
    {X S : Scheme.{u}} (π : X ⟶ S) {J : Type u}
    (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let f := (π.affineIntersectionOverlapIso U hU i j).inv
    let g := π.affineIntersectionGluedToOriginal U hU
    (f ≫ (sq i j).p) ≫ g = (U i ⊓ U j).ι := by
  dsimp only
  let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let D := π.affineIntersectionGlueData U hU
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let f := (π.affineIntersectionOverlapIso U hU i j).inv
  let g := π.affineIntersectionGluedToOriginal U hU
  exact overlap_common_map f (sq i j).p₁ (D.ι i) (sq i j).p g
    (π.affineIntersectionChartIso U hU i).hom (U i).ι
    (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (U i ⊓ U j).ι
    (sq i j).hp₁
    (π.affineIntersectionGlueData_ι_affineIntersectionGluedToOriginal_eq_chartIso U hU i)
    (affineIntersectionOverlapIso_inv_comp_left_chartIso π U hU i j)
    (X.homOfLE_ι (inf_le_left : U i ⊓ U j ≤ U i))

/-- A chosen trivialization on an original open induces a trivialization on the corresponding
chart of the affine-intersection glued model. -/
noncomputable def affineIntersectionOriginalChartTrivialization
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i : J) :
    let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let D := Scheme.GlueData.ofAffineIntersectionFunctor
      (π.affineIntersectionFunctor U) hopen hpush
    let g : D.glued ⟶ X := π.affineIntersectionGluedToOriginal U hU
    (pullback (D.ι i)).obj ((pullback g).obj N) ≅ unitObj (D.U i) := by
  let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let D := Scheme.GlueData.ofAffineIntersectionFunctor
    (π.affineIntersectionFunctor U) hopen hpush
  let g : D.glued ⟶ X := π.affineIntersectionGluedToOriginal U hU
  let q := π.affineIntersectionChartIso U hU i
  let e' : (pullback (U i).ι).obj N ≅ unitObj (U i).toScheme :=
    (restrictFunctorIsoPullback (U i).ι).symm.app N ≪≫ e i
  let h : D.ι i ≫ g = q.hom ≫ (U i).ι :=
    π.affineIntersectionGlueData_ι_affineIntersectionGluedToOriginal_eq_chartIso U hU i
  exact (pullbackComp (D.ι i) g).app N ≪≫
    (pullbackCongr h).app N ≪≫
    (pullbackComp q.hom (U i).ι).symm.app N ≪≫
    (pullback q.hom).mapIso e' ≪≫
    pullbackUnitIso q.hom

private theorem affineIntersectionOriginalChartTrivialization_eq_square
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i : J) :
    let D := π.affineIntersectionGlueData U hU
    let g := π.affineIntersectionGluedToOriginal U hU
    let q := π.affineIntersectionChartIso U hU i
    let e' : (pullback (U i).ι).obj N ≅ unitObj (U i).toScheme :=
      (restrictFunctorIsoPullback (U i).ι).symm.app N ≪≫ e i
    let h : D.ι i ≫ g = q.hom ≫ (U i).ι :=
      π.affineIntersectionGlueData_ι_affineIntersectionGluedToOriginal_eq_chartIso U hU i
    affineIntersectionOriginalChartTrivialization π U e hU i =
      pullbackSquareTrivialization (D.ι i) g q.hom (U i).ι h N e' := by
  rfl

private theorem pullbackRestrictOpenTrivialization
    {X : Scheme.{u}} {N : X.Modules} {U V : X.Opens} (hVU : V ≤ U)
    (e : N.restrict U.ι ≅ unitObj U.toScheme) :
    (restrictFunctorIsoPullback V.ι).symm.app N ≪≫
        restrictOpenTrivialization hVU e =
      restrictTrivialization hVU
        ((restrictFunctorIsoPullback U.ι).symm.app N ≪≫ e) := by
  rw [restrictOpenTrivialization_eq_pullback]
  unfold restrictOpenTrivializationPullback
  apply Iso.ext
  simp only [Iso.trans_hom]
  let R := (restrictFunctorIsoPullback V.ι).app N
  change R.inv ≫ R.hom ≫ _ = _
  exact R.inv_hom_id_assoc _

private noncomputable def affineIntersectionTransportedChartTrivialization
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (k : J) {Y Z : Scheme.{u}}
    (p : Y ⟶ (π.affineIntersectionGlueData U hU).U k) (f : Z ⟶ Y) :
    let D := π.affineIntersectionGlueData U hU
    let g := π.affineIntersectionGluedToOriginal U hU
    (pullback f).obj
          ((pullback p).obj ((pullback (D.ι k)).obj ((pullback g).obj N))) ⟶
      unitObj Z :=
  let D := π.affineIntersectionGlueData U hU
  let g := π.affineIntersectionGluedToOriginal U hU
  let q := π.affineIntersectionChartIso U hU k
  let e' : (pullback (U k).ι).obj N ≅ unitObj (U k).toScheme :=
    (restrictFunctorIsoPullback (U k).ι).symm.app N ≪≫ e k
  let h : D.ι k ≫ g = q.hom ≫ (U k).ι :=
    π.affineIntersectionGlueData_ι_affineIntersectionGluedToOriginal_eq_chartIso
      U hU k
  let hOuter : (f ≫ p) ≫ (D.ι k ≫ g) =
      ((f ≫ p) ≫ q.hom) ≫ (U k).ι :=
    (Category.assoc (f ≫ p) (D.ι k) g).symm.trans
      ((congrArg ((f ≫ p) ≫ ·) h).trans
        (Category.assoc (f ≫ p) q.hom (U k).ι))
  (pullbackComp f p).hom.app
        ((pullback (D.ι k)).obj ((pullback g).obj N)) ≫
    (pullback (f ≫ p)).map ((pullbackComp (D.ι k) g).hom.app N) ≫
      (pullbackSquareTrivialization (f ≫ p) (D.ι k ≫ g)
        ((f ≫ p) ≫ q.hom) (U k).ι hOuter N e').hom

private theorem affineIntersectionOriginalChartTrivialization_comp_precomp_hom
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (k : J) {Y Z : Scheme.{u}}
    (p : Y ⟶ (π.affineIntersectionGlueData U hU).U k) (f : Z ⟶ Y) :
    (pullback f).map ((pullback p).map
          (affineIntersectionOriginalChartTrivialization π U e hU k).hom) ≫
        (pullback f).map (pullbackUnitIso p).hom ≫
      (pullbackUnitIso f).hom =
    affineIntersectionTransportedChartTrivialization π U e hU k p f := by
  dsimp only [affineIntersectionTransportedChartTrivialization]
  let D := π.affineIntersectionGlueData U hU
  let g := π.affineIntersectionGluedToOriginal U hU
  let q := π.affineIntersectionChartIso U hU k
  let e' : (pullback (U k).ι).obj N ≅ unitObj (U k).toScheme :=
    (restrictFunctorIsoPullback (U k).ι).symm.app N ≪≫ e k
  let h : D.ι k ≫ g = q.hom ≫ (U k).ι :=
    π.affineIntersectionGlueData_ι_affineIntersectionGluedToOriginal_eq_chartIso
      U hU k
  have hpre := pullbackSquareTrivialization_comp_precomp_hom
    f p (D.ι k) g q.hom (U k).ι h N e'
  rw [← affineIntersectionOriginalChartTrivialization_eq_square
    π U e hU k] at hpre
  exact hpre

private theorem affineIntersection_chartTransition_comp_flattenRight
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let c := affineIntersectionUnitCocycle π U e
    let q := π.affineIntersectionOverlapIso U hU i j
    let s := openTopSection (U i ⊓ U j)
      (trivializingCoverTransitionUnitOn U e (U i ⊓ U j) i j
        inf_le_left inf_le_right : Γ(X, U i ⊓ U j))
    (pullback q.inv).map (c.chartTransitionIso hopen hpush i j).hom ≫
          (pullback q.inv).map (pullbackUnitIso (sq i j).p₂).hom ≫
        (pullbackUnitIso q.inv).hom =
      (pullback q.inv).map (pullbackUnitIso (sq i j).p₁).hom ≫
          (pullbackUnitIso q.inv).hom ≫
        ModularCurves.unitEndomorphismOfTopSection s := by
  dsimp only
  dsimp only [affineIntersectionChartChosenPullback]
  rw [AffineIntersectionUnitCocycle.chartTransitionIso_hom]
  let D := π.affineIntersectionGlueData U hU
  let q := π.affineIntersectionOverlapIso U hU i j
  let c := affineIntersectionUnitCocycle π U e
  have hcancel := pullback_unitTransition_comp_flattenRight
    (D.f i j) (D.t i j ≫ D.f j i) q (c.overlapTransitionIso i j)
  rw [hcancel]
  have hscalar := affineIntersectionUnitCocycle_pullback_overlapTransitionIso
    π U e hU i j
  exact congrArg
    (fun z =>
      (pullback q.inv).map
        (pullbackUnitIso (D.f i j)).hom ≫ z) hscalar

private theorem eq_of_map_components
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) [F.Faithful]
    {X Y Z W V : C} (f : X ⟶ Y) (t : Y ⟶ Z)
    (a : X ⟶ W) (b : W ⟶ V) (g : V ⟶ Z)
    (h : F.map f ≫ F.map t = (F.map a ≫ F.map b) ≫ F.map g) :
    f ≫ t = (a ≫ b) ≫ g := by
  apply F.map_injective
  rw [F.map_comp, F.map_comp, F.map_comp]
  exact h

private theorem comp_four_assoc
    {C : Type u₁} [Category.{v₁} C]
    {A B C' D E : C} (f : A ⟶ B) (g : B ⟶ C')
    (h : C' ⟶ D) (k : D ⟶ E) :
    ((f ≫ g) ≫ h) ≫ k = f ≫ (g ≫ h ≫ k) := by
  simp only [Category.assoc]

private theorem comp_four_group_first_three
    {C : Type u₁} [Category.{v₁} C]
    {A B C' D E : C} (f : A ⟶ B) (g : B ⟶ C')
    (h : C' ⟶ D) (k : D ⟶ E) :
    f ≫ g ≫ h ≫ k = (f ≫ g ≫ h) ≫ k := by
  simp only [Category.assoc]

private theorem comp_five_group_last_three
    {C : Type u₁} [Category.{v₁} C]
    {A B C' D E F : C} (f : A ⟶ B) (g : B ⟶ C')
    (h : C' ⟶ D) (k : D ⟶ E) (l : E ⟶ F) :
    ((((f ≫ g) ≫ h) ≫ k) ≫ l) = (f ≫ g) ≫ (h ≫ k ≫ l) := by
  simp only [Category.assoc]

private theorem comp_pair_with_triple_of_eq
    {C : Type u₁} [Category.{v₁} C]
    {A B C' D E F : C} (f : A ⟶ B) (g : B ⟶ C')
    (h : C' ⟶ D) (k : D ⟶ E) (l : E ⟶ F) (t : C' ⟶ F)
    (ht : h ≫ k ≫ l = t) :
    ((((f ≫ g) ≫ h) ≫ k) ≫ l) = (f ≫ g) ≫ t :=
  (comp_five_group_last_three f g h k l).trans
    (congrArg ((f ≫ g) ≫ ·) ht)

private theorem overlap_source_map
    {C : Type u₁} [Category.{v₁} C]
    {W A B G X : C} (f : W ⟶ A) (p : A ⟶ B)
    (d : B ⟶ G) (s : A ⟶ G) (g : G ⟶ X)
    (hp : p ≫ d = s) :
    (f ≫ p) ≫ (d ≫ g) = (f ≫ s) ≫ g :=
  (Category.assoc (f ≫ p) d g).symm.trans
    (congrArg (· ≫ g)
      ((Category.assoc f p d).trans (congrArg (f ≫ ·) hp)))

private theorem restrictTrivialization_transition
    {X : Scheme.{u}} {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (i j : J) :
    let W := U i ⊓ U j
    let ei : (pullback (U i).ι).obj N ≅ unitObj (U i).toScheme :=
      (restrictFunctorIsoPullback (U i).ι).symm.app N ≪≫ e i
    let ej : (pullback (U j).ι).obj N ≅ unitObj (U j).toScheme :=
      (restrictFunctorIsoPullback (U j).ι).symm.app N ≪≫ e j
    (restrictTrivialization (inf_le_left : W ≤ U i) ei).inv ≫
        (restrictTrivialization (inf_le_right : W ≤ U j) ej).hom =
      ModularCurves.unitEndomorphismOfTopSection
        (openTopSection W
          (trivializingCoverTransitionUnitOn U e W i j
            inf_le_left inf_le_right : Γ(X, W))) := by
  dsimp only
  let W := U i ⊓ U j
  let eWi := restrictOpenTrivialization
    (inf_le_left : W ≤ U i) (e i)
  let eWj := restrictOpenTrivialization
    (inf_le_right : W ≤ U j) (e j)
  let R := (restrictFunctorIsoPullback W.ι).app N
  have hi := pullbackRestrictOpenTrivialization
    (inf_le_left : W ≤ U i) (e i)
  have hj := pullbackRestrictOpenTrivialization
    (inf_le_right : W ≤ U j) (e j)
  have hscalar := openTrivializationTransitionUnit_hom W eWi eWj
  rw [← hi, ← hj]
  change (eWi.inv ≫ R.hom) ≫ R.inv ≫ eWj.hom = _
  rw [Category.assoc, R.hom_inv_id_assoc]
  exact hscalar

private theorem precomp_square
    {C : Type u₁} [Category.{v₁} C]
    {W A B V X : C} (f : W ⟶ A) (p : A ⟶ B)
    (d : B ⟶ X) (q : B ⟶ V) (ι : V ⟶ X)
    (h : d = q ≫ ι) :
    (f ≫ p) ≫ d = ((f ≫ p) ≫ q) ≫ ι :=
  (congrArg ((f ≫ p) ≫ ·) h).trans (Category.assoc _ q ι).symm

private noncomputable abbrev affineIntersectionLeftOuterStatement
    {X S : Scheme.{u}} (π : X ⟶ S) {J : Type u}
    (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) : Prop :=
  let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let D := π.affineIntersectionGlueData U hU
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let q := π.affineIntersectionOverlapIso U hU i j
  let g := π.affineIntersectionGluedToOriginal U hU
  let qi := π.affineIntersectionChartIso U hU i
  (q.inv ≫ (sq i j).p₁) ≫ (D.ι i ≫ g) =
    ((q.inv ≫ (sq i j).p₁) ≫ qi.hom) ≫ (U i).ι

private theorem affineIntersectionLeftOuterProof
    {X S : Scheme.{u}} (π : X ⟶ S) {J : Type u}
    (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    affineIntersectionLeftOuterStatement π U hU i j := by
  dsimp only [affineIntersectionLeftOuterStatement]
  let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let D := π.affineIntersectionGlueData U hU
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let q := π.affineIntersectionOverlapIso U hU i j
  let g := π.affineIntersectionGluedToOriginal U hU
  let qi := π.affineIntersectionChartIso U hU i
  let hi : D.ι i ≫ g = qi.hom ≫ (U i).ι :=
    π.affineIntersectionGlueData_ι_affineIntersectionGluedToOriginal_eq_chartIso U hU i
  exact precomp_square q.inv (sq i j).p₁ (D.ι i ≫ g) qi.hom (U i).ι hi

private noncomputable abbrev affineIntersectionRightOuterStatement
    {X S : Scheme.{u}} (π : X ⟶ S) {J : Type u}
    (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) : Prop :=
  let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let D := π.affineIntersectionGlueData U hU
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let q := π.affineIntersectionOverlapIso U hU i j
  let g := π.affineIntersectionGluedToOriginal U hU
  let qj := π.affineIntersectionChartIso U hU j
  (q.inv ≫ (sq i j).p₂) ≫ (D.ι j ≫ g) =
    ((q.inv ≫ (sq i j).p₂) ≫ qj.hom) ≫ (U j).ι

private theorem affineIntersectionRightOuterProof
    {X S : Scheme.{u}} (π : X ⟶ S) {J : Type u}
    (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    affineIntersectionRightOuterStatement π U hU i j := by
  dsimp only [affineIntersectionRightOuterStatement]
  let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let D := π.affineIntersectionGlueData U hU
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let q := π.affineIntersectionOverlapIso U hU i j
  let g := π.affineIntersectionGluedToOriginal U hU
  let qj := π.affineIntersectionChartIso U hU j
  let hj : D.ι j ≫ g = qj.hom ≫ (U j).ι :=
    π.affineIntersectionGlueData_ι_affineIntersectionGluedToOriginal_eq_chartIso U hU j
  exact precomp_square q.inv (sq i j).p₂ (D.ι j ≫ g) qj.hom (U j).ι hj

private theorem affineIntersectionTwoTransition
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let D := π.affineIntersectionGlueData U hU
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let g := π.affineIntersectionGluedToOriginal U hU
    let M := (pullback g).obj N
    let q := π.affineIntersectionOverlapIso U hU i j
    let Li := ((pullbackComp (sq i j).p₁ (D.ι i)).app M) ≪≫
      ((pullbackCongr (sq i j).hp₁).app M)
    let Lj := ((pullbackComp (sq i j).p₂ (D.ι j)).app M) ≪≫
      ((pullbackCongr (sq i j).hp₂).app M)
    let scalar := ModularCurves.unitEndomorphismOfTopSection
      (openTopSection (U i ⊓ U j)
        (trivializingCoverTransitionUnitOn U e (U i ⊓ U j) i j
          inf_le_left inf_le_right : Γ(X, U i ⊓ U j)))
    affineIntersectionTransportedChartTrivialization
          π U e hU i (sq i j).p₁ q.inv ≫ scalar =
      ((pullback q.inv).map Li.hom ≫ (pullback q.inv).map Lj.inv) ≫
        affineIntersectionTransportedChartTrivialization
          π U e hU j (sq i j).p₂ q.inv := by
  classical
  dsimp only
  let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let D := π.affineIntersectionGlueData U hU
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let g := π.affineIntersectionGluedToOriginal U hU
  let q := π.affineIntersectionOverlapIso U hU i j
  let hcI := affineIntersectionOverlapIso_inv_comp_left_chartIso π U hU i j
  let hcJ := affineIntersectionOverlapIso_inv_comp_right_chartIso π U hU i j
  let hSourceI : (q.inv ≫ (sq i j).p₁) ≫ (D.ι i ≫ g) =
      (q.inv ≫ (sq i j).p) ≫ g :=
    overlap_source_map q.inv (sq i j).p₁ (D.ι i) (sq i j).p g (sq i j).hp₁
  let hSourceJ : (q.inv ≫ (sq i j).p₂) ≫ (D.ι j ≫ g) =
      (q.inv ≫ (sq i j).p) ≫ g :=
    overlap_source_map q.inv (sq i j).p₂ (D.ι j) (sq i j).p g (sq i j).hp₂
  let hCommon : (q.inv ≫ (sq i j).p) ≫ g = (U i ⊓ U j).ι :=
    affineIntersectionOverlapIso_inv_comp_gluedToOriginal π U hU i j
  have hscalar := restrictTrivialization_transition U e i j
  apply pullbackSquareTrivialization_two_transition
    (X := X) (A := (sq i j).pullback) (B₁ := D.U i) (B₂ := D.U j)
    (D := D.glued) (N := N) (U₁ := U i) (U₂ := U j) (W := U i ⊓ U j)
  · exact hcI
  · exact hcJ
  · exact hSourceI
  · exact hSourceJ
  · exact hCommon
  · exact hscalar

private theorem affineIntersectionLeftScalarNormalization
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let q := π.affineIntersectionOverlapIso U hU i j
    let scalar := ModularCurves.unitEndomorphismOfTopSection
      (openTopSection (U i ⊓ U j)
        (trivializingCoverTransitionUnitOn U e (U i ⊓ U j) i j
          inf_le_left inf_le_right : Γ(X, U i ⊓ U j)))
    (pullback q.inv).map
          ((pullback (sq i j).p₁).map
            (affineIntersectionOriginalChartTrivialization π U e hU i).hom) ≫
        (pullback q.inv).map (pullbackUnitIso (sq i j).p₁).hom ≫
          (pullbackUnitIso q.inv).hom ≫ scalar =
      affineIntersectionTransportedChartTrivialization
          π U e hU i (sq i j).p₁ q.inv ≫ scalar := by
  classical
  dsimp only
  let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let q := π.affineIntersectionOverlapIso U hU i j
  let scalar := ModularCurves.unitEndomorphismOfTopSection
    (openTopSection (U i ⊓ U j)
      (trivializingCoverTransitionUnitOn U e (U i ⊓ U j) i j
        inf_le_left inf_le_right : Γ(X, U i ⊓ U j)))
  have hi := affineIntersectionOriginalChartTrivialization_comp_precomp_hom
    π U e hU i (sq i j).p₁ q.inv
  exact (comp_four_group_first_three _ _ _ _).trans
    (congrArg (fun z => z ≫ scalar) hi)

private theorem affineIntersectionRightPrefixNormalization
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let D := π.affineIntersectionGlueData U hU
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let g := π.affineIntersectionGluedToOriginal U hU
    let M := (pullback g).obj N
    let q := π.affineIntersectionOverlapIso U hU i j
    let Li := ((pullbackComp (sq i j).p₁ (D.ι i)).app M) ≪≫
      ((pullbackCongr (sq i j).hp₁).app M)
    let Lj := ((pullbackComp (sq i j).p₂ (D.ι j)).app M) ≪≫
      ((pullbackCongr (sq i j).hp₂).app M)
    let tj := (pullback (sq i j).p₂).map
      (affineIntersectionOriginalChartTrivialization π U e hU j).hom
    ((((pullback q.inv).map Li.hom ≫ (pullback q.inv).map Lj.inv) ≫
          (pullback q.inv).map tj) ≫
        (pullback q.inv).map (pullbackUnitIso (sq i j).p₂).hom) ≫
      (pullbackUnitIso q.inv).hom =
      ((pullback q.inv).map Li.hom ≫ (pullback q.inv).map Lj.inv) ≫
        affineIntersectionTransportedChartTrivialization
          π U e hU j (sq i j).p₂ q.inv := by
  classical
  dsimp only
  let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let D := π.affineIntersectionGlueData U hU
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let g := π.affineIntersectionGluedToOriginal U hU
  let M := (pullback g).obj N
  let q := π.affineIntersectionOverlapIso U hU i j
  let Li := ((pullbackComp (sq i j).p₁ (D.ι i)).app M) ≪≫
    ((pullbackCongr (sq i j).hp₁).app M)
  let Lj := ((pullbackComp (sq i j).p₂ (D.ι j)).app M) ≪≫
    ((pullbackCongr (sq i j).hp₂).app M)
  let tj := (pullback (sq i j).p₂).map
    (affineIntersectionOriginalChartTrivialization π U e hU j).hom
  have hj := affineIntersectionOriginalChartTrivialization_comp_precomp_hom
    π U e hU j (sq i j).p₂ q.inv
  exact comp_pair_with_triple_of_eq
    ((pullback q.inv).map Li.hom)
    ((pullback q.inv).map Lj.inv)
    ((pullback q.inv).map tj)
    ((pullback q.inv).map (pullbackUnitIso (sq i j).p₂).hom)
    (pullbackUnitIso q.inv).hom _ hj

private theorem affineIntersectionOriginalChartTrivialization_scalar_transition
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let D := π.affineIntersectionGlueData U hU
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let g := π.affineIntersectionGluedToOriginal U hU
    let M := (pullback g).obj N
    let q := π.affineIntersectionOverlapIso U hU i j
    let Li := ((pullbackComp (sq i j).p₁ (D.ι i)).app M) ≪≫
      ((pullbackCongr (sq i j).hp₁).app M)
    let Lj := ((pullbackComp (sq i j).p₂ (D.ι j)).app M) ≪≫
      ((pullbackCongr (sq i j).hp₂).app M)
    let tj := (pullback (sq i j).p₂).map
      (affineIntersectionOriginalChartTrivialization π U e hU j).hom
    let scalar := ModularCurves.unitEndomorphismOfTopSection
      (openTopSection (U i ⊓ U j)
        (trivializingCoverTransitionUnitOn U e (U i ⊓ U j) i j
          inf_le_left inf_le_right : Γ(X, U i ⊓ U j)))
    (pullback q.inv).map
          ((pullback (sq i j).p₁).map
            (affineIntersectionOriginalChartTrivialization π U e hU i).hom) ≫
        (pullback q.inv).map (pullbackUnitIso (sq i j).p₁).hom ≫
          (pullbackUnitIso q.inv).hom ≫ scalar =
    ((((pullback q.inv).map Li.hom ≫ (pullback q.inv).map Lj.inv) ≫
          (pullback q.inv).map tj) ≫
        (pullback q.inv).map (pullbackUnitIso (sq i j).p₂).hom) ≫
      (pullbackUnitIso q.inv).hom := by
  exact (affineIntersectionLeftScalarNormalization π U e hU i j).trans
    ((affineIntersectionTwoTransition π U e hU i j).trans
      (affineIntersectionRightPrefixNormalization π U e hU i j).symm)

private theorem affineIntersectionOriginalChartTrivialization_pulled_transition
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let D := π.affineIntersectionGlueData U hU
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let g := π.affineIntersectionGluedToOriginal U hU
    let M := (pullback g).obj N
    let c := affineIntersectionUnitCocycle π U e
    let q := π.affineIntersectionOverlapIso U hU i j
    let Li := ((pullbackComp (sq i j).p₁ (D.ι i)).app M) ≪≫
      ((pullbackCongr (sq i j).hp₁).app M)
    let Lj := ((pullbackComp (sq i j).p₂ (D.ι j)).app M) ≪≫
      ((pullbackCongr (sq i j).hp₂).app M)
    let tj := (pullback (sq i j).p₂).map
      (affineIntersectionOriginalChartTrivialization π U e hU j).hom
    (pullback q.inv).map
          ((pullback (sq i j).p₁).map
            (affineIntersectionOriginalChartTrivialization π U e hU i).hom) ≫
        (pullback q.inv).map (c.chartTransitionIso hopen hpush i j).hom =
      ((pullback q.inv).map Li.hom ≫ (pullback q.inv).map Lj.inv) ≫
        (pullback q.inv).map tj := by
  classical
  dsimp only
  let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let D := π.affineIntersectionGlueData U hU
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let g := π.affineIntersectionGluedToOriginal U hU
  let M := (pullback g).obj N
  let c := affineIntersectionUnitCocycle π U e
  let q := π.affineIntersectionOverlapIso U hU i j
  let Li := ((pullbackComp (sq i j).p₁ (D.ι i)).app M) ≪≫
    ((pullbackCongr (sq i j).hp₁).app M)
  let Lj := ((pullbackComp (sq i j).p₂ (D.ι j)).app M) ≪≫
    ((pullbackCongr (sq i j).hp₂).app M)
  let tj := (pullback (sq i j).p₂).map
    (affineIntersectionOriginalChartTrivialization π U e hU j).hom
  let rightUnitMapped := (pullback q.inv).mapIso
    (pullbackUnitIso (sq i j).p₂)
  apply (cancel_mono rightUnitMapped.hom).1
  apply (cancel_mono (pullbackUnitIso q.inv).hom).1
  refine Eq.trans (comp_four_assoc _ _ _ _) ?_
  have htransition := affineIntersection_chartTransition_comp_flattenRight
    π U e hU i j
  refine Eq.trans (congrArg
    (fun z =>
      (pullback q.inv).map
        ((pullback (sq i j).p₁).map
          (affineIntersectionOriginalChartTrivialization π U e hU i).hom) ≫ z)
    htransition) ?_
  exact affineIntersectionOriginalChartTrivialization_scalar_transition
    π U e hU i j

/-- The chart trivializations induced from an affine cover of the original scheme are
compatible with the affine-intersection unit cocycle. -/
theorem affineIntersectionOriginalChartTrivialization_isCompatible
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s)) :
    let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let D := Scheme.GlueData.ofAffineIntersectionFunctor
      (π.affineIntersectionFunctor U) hopen hpush
    let g : D.glued ⟶ X := π.affineIntersectionGluedToOriginal U hU
    let M := (pullback g).obj N
    let c := affineIntersectionUnitCocycle π U e
    c.IsCompatibleChartTrivialization hopen hpush M
      (affineIntersectionOriginalChartTrivialization π U e hU) := by
  classical
  dsimp only [AffineIntersectionUnitCocycle.IsCompatibleChartTrivialization]
  intro i j
  let q := π.affineIntersectionOverlapIso U hU i j
  letI : (pullback q.inv).IsEquivalence :=
    pullback_isEquivalence_of_iso q.symm
  letI : (pullback q.inv).Faithful := by infer_instance
  apply eq_of_map_components (pullback q.inv)
  exact affineIntersectionOriginalChartTrivialization_pulled_transition
    π U e hU i j

/-- The chart trivializations induced from an affine cover of the original scheme have the
transition maps used by the affine-intersection gluing construction. -/
theorem affineIntersectionOriginalChartTrivialization_transition
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let D := Scheme.GlueData.ofAffineIntersectionFunctor
      (π.affineIntersectionFunctor U) hopen hpush
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let g : D.glued ⟶ X := π.affineIntersectionGluedToOriginal U hU
    let M := (pullback g).obj N
    let c := affineIntersectionUnitCocycle π U e
    (pullbackPseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.map
          (affineIntersectionOriginalChartTrivialization π U e hU i).hom ≫
        (c.chartTransitionIso hopen hpush i j).hom =
      (affineIntersectionPullbackComparisonIso hopen hpush M i j).hom ≫
        (pullbackPseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.map
          (affineIntersectionOriginalChartTrivialization π U e hU j).hom := by
  classical
  dsimp only
  rw [affineIntersectionPullbackComparisonIso_hom]
  let q := π.affineIntersectionOverlapIso U hU i j
  letI : (pullback q.inv).IsEquivalence :=
    pullback_isEquivalence_of_iso q.symm
  letI : (pullback q.inv).Faithful := by infer_instance
  apply eq_of_map_components (pullback q.inv)
  exact affineIntersectionOriginalChartTrivialization_pulled_transition
    π U e hU i j

/-- Pulling an invertible sheaf to its affine-intersection glued model recovers the
concrete Cech equalizer built from the transition units of a trivializing cover. -/
noncomputable def affineIntersectionOriginalGluedModuleIso
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s)) :
    let hopen := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let hpush := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
    let D := Scheme.GlueData.ofAffineIntersectionFunctor
      (π.affineIntersectionFunctor U) hopen hpush
    let g : D.glued ⟶ X := π.affineIntersectionGluedToOriginal U hU
    let c := affineIntersectionUnitCocycle π U e
    (pullback g).obj N ≅ c.gluedModule hopen hpush := by
  dsimp only
  exact (affineIntersectionUnitCocycle π U e).gluedModuleIsoOfCompatibleChartTrivialization
    (π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU)
    (π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU)
    ((pullback (π.affineIntersectionGluedToOriginal U hU)).obj N)
    (affineIntersectionOriginalChartTrivialization π U e hU)
    (affineIntersectionOriginalChartTrivialization_isCompatible π U e hU)

private noncomputable def trivializationOnOpensRange
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (e : (restrictFunctor f).obj M ≅ unitObj Y) :
    (pullback f.opensRange.ι).obj M ≅ unitObj (f.opensRange : Scheme.{u}) := by
  let q := f.isoOpensRange
  let e' : (pullback f).obj M ≅ unitObj Y :=
    (restrictFunctorIsoPullback f).symm.app M ≪≫ e
  exact (pullbackCongr f.isoOpensRange_inv_comp).symm.app M ≪≫
    (pullbackComp q.inv f).symm.app M ≪≫
    (pullback q.inv).mapIso e' ≪≫ pullbackUnitIso q.inv

/-- The Cech equalizer attached to an affine-intersection unit cocycle is an
invertible sheaf on the glued scheme. -/
theorem AffineIntersectionUnitCocycle.gluedModule_isInvertible
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F) :
    IsInvertible (c.gluedModule hopen hpush) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  refine ⟨J, fun k ↦ affineIntersectionChartOpen D k,
    affineIntersectionChart_iSup_opensRange hopen hpush, fun k ↦ ?_⟩
  letI : IsOpenImmersion (D.ι k) := D.ι_isOpenImmersion k
  exact ⟨trivializationOnOpensRange (D.ι k) (c.gluedModule hopen hpush)
    (c.gluedModuleRestrictIso hopen hpush k)⟩

end

end AlgebraicGeometry.Scheme.Modules
