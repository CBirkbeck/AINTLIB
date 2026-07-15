import ModularCurves.Picard.InvertibleSheafGlueDataDescent
import ModularCurves.Picard.DualPullback.OpenAdjunction
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent

/-!
# Effectivity of affine-intersection line-bundle descent

This file glues the chartwise unit modules attached to an
`AffineIntersectionUnitCocycle`. The glued module is the usual Cech equalizer of
the chart extensions, with one overlap map twisted by the transition isomorphism.
-/

universe u u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Restriction of scheme modules along an open immersion preserves all limits. -/
theorem restrictFunctor_preservesLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesLimits (restrictFunctor f) := by
  letI : PreservesLimits (restrictFunctor f ⋙ toPresheafOfModules X) := by
    dsimp [restrictFunctor, toPresheafOfModules]
    change PreservesLimits (SheafOfModules.forget _ ⋙
      PresheafOfModules.pushforward _)
    exact comp_preservesLimits _ _
  exact preservesLimits_of_reflects_of_preserves
    (restrictFunctor f) (toPresheafOfModules X)

/-- In a pullback square whose vertical maps are open immersions, restricting
the pushforward of the structure sheaf agrees with pushing forward the
structure sheaf from the pullback. -/
noncomputable def restrictPushforwardUnitIsoOfIsPullback
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) :
    (restrictFunctor iV).obj ((pushforward f).obj (unitObj X)) ≅
      (pushforward f').obj (unitObj U) := by
  refine (fullyFaithfulToPresheafOfModules).preimageIso
    (PresheafOfModules.isoMk (fun W ↦ ?_) ?_)
  · let h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W.unop
    let e : Γ(X, f ⁻¹ᵁ iV ''ᵁ W.unop) ≅ Γ(U, f' ⁻¹ᵁ W.unop) :=
      X.presheaf.mapIso (eqToIso h).op ≪≫ iU.appIso _
    refine ModuleCat.isoMk
      ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab).mapIso e) ?_
    intro r
    ext x
    dsimp [ModuleCat.smul]
    change (f'.app _).hom r * e.hom
        (show Γ(X, f ⁻¹ᵁ iV ''ᵁ W.unop) from x) =
      e.hom ((f.app _).hom ((iV.appIso _).inv r) *
        (show Γ(X, f ⁻¹ᵁ iV ''ᵁ W.unop) from x))
    rw [map_mul]
    congr 1
    have hring : (iV.appIso W.unop).inv ≫ f.app _ = f'.app W.unop ≫ e.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
      simp only [Scheme.Hom.app_eq_appLE, Iso.trans_hom, Functor.mapIso_hom,
        Iso.op_hom, eqToIso.hom, eqToHom_op, Scheme.Hom.appIso_hom',
        Scheme.Hom.map_appLE, e, Scheme.Hom.appLE_comp_appLE, H.w]
    have hx := congr($(hring) r)
    apply_fun e.hom at hx
    simpa using hx.symm
  · intro W W' g
    let hW := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W.unop
    let hW' := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W'.unop
    have eW : f' ⁻¹ᵁ W.unop ≤ iU ⁻¹ᵁ (f ⁻¹ᵁ iV ''ᵁ W.unop) := by
      rw [← hW, iU.preimage_image_eq]
    have eW' : f' ⁻¹ᵁ W'.unop ≤ iU ⁻¹ᵁ (f ⁻¹ᵁ iV ''ᵁ W'.unop) := by
      rw [← hW', iU.preimage_image_eq]
    let gx := (TopologicalSpace.Opens.map f.base).op.map
      ((iV.opensFunctor).op.map g)
    let gu := (TopologicalSpace.Opens.map f'.base).op.map g
    have heq : X.presheaf.map gx ≫
          iU.appLE (f ⁻¹ᵁ iV ''ᵁ W'.unop) (f' ⁻¹ᵁ W'.unop) eW' =
        iU.appLE (f ⁻¹ᵁ iV ''ᵁ W.unop) (f' ⁻¹ᵁ W.unop) eW ≫
          U.presheaf.map gu := by
      calc
        _ = iU.appLE (f ⁻¹ᵁ iV ''ᵁ W.unop) (f' ⁻¹ᵁ W'.unop) _ :=
          iU.map_appLE eW' gx
        _ = _ := (iU.appLE_map eW gu).symm
    ext x
    dsimp
    simp [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    change (iU.appLE _ _ _).hom
        (X.presheaf.map _ (show Γ(X, f ⁻¹ᵁ iV ''ᵁ W.unop) from x)) =
      U.presheaf.map _ ((iU.appLE _ _ _).hom
        (show Γ(X, f ⁻¹ᵁ iV ''ᵁ W.unop) from x))
    simp only [← CommRingCat.comp_apply]
    exact congr($(heq) x)

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
    have hr' : (iU.appIso _).inv ((f'.app _).hom r) =
        (X.presheaf.map (eqToHom h).op).hom
          ((f.app _).hom ((iV.appIso _).inv r)) := by
      simpa only [CommRingCat.comp_apply] using
        ConcreteCategory.congr_hom hring''' r
    let x' : M.val.obj (.op (f ⁻¹ᵁ iV ''ᵁ W.unop)) := x
    change (iU.appIso _).inv ((f'.app _).hom r) •
        (show M.val.obj (.op (iU ''ᵁ (f' ⁻¹ᵁ W.unop))) from e.hom x') =
      e.hom ((f.app _).hom ((iV.appIso _).inv r) • x')
    rw [hr']
    exact ((M.val.map (eqToHom h).op).hom.map_smul
      ((f.app _).hom ((iV.appIso _).inv r)) x').symm
  · intro W W' g
    apply ModuleCat.hom_ext
    ext x
    change M.presheaf.map _ (M.presheaf.map _ x) =
      M.presheaf.map _ (M.presheaf.map _ x)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) x

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

private theorem restrictPushforwardUnitIsoOfIsPullback_eq
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) :
    restrictPushforwardUnitIsoOfIsPullback f f' iU iV H =
      (restrictPushforwardIsoOfIsPullback f f' iU iV H).app (unitObj X) ≪≫
        (pushforward f').mapIso (restrictUnitIso iU) := by
  apply Iso.ext
  apply (fullyFaithfulToPresheafOfModules).map_injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
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
    calc
      _ = SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom ≫
          (e.inv ≫ e.hom) := Category.assoc _ _ _
      _ = SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom ≫
          𝟙 _ := congrArg
            (fun q ↦ SheafOfModules.unitToPushforwardObjUnit
              f'.toRingCatSheafHom ≫ q) e.inv_hom_id
      _ = _ := Category.comp_id _
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
  refine Eq.trans ?_ hunitRight.symm
  calc
    _ = (e.hom.val.app W).hom'
        ((f.toRingCatSheafHom.hom.app
          (iV.opensFunctor.op.obj W)).hom
            ((iV.appIso W.unop).inv x)) :=
      congrArg (fun y ↦ (e.hom.val.app W).hom' y) hunitLeft
    _ = (f'.toRingCatSheafHom.hom.app W).hom x := by
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
      have hx := ConcreteCategory.congr_hom hring x
      apply_fun eR.hom at hx
      simpa using hx

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
  change (e.app (unitObj X) ≪≫ u).inv ≫
      (pushforward f ⋙ restrictFunctor iV).map q ≫ e.hom.app N =
    (pushforward f').map (r.inv ≫ (restrictFunctor iU).map q)
  let hnat := e.hom.naturality q
  calc
    _ = u.inv ≫ ((e.app (unitObj X)).inv ≫
        ((pushforward f ⋙ restrictFunctor iV).map q ≫ e.hom.app N)) := by
          simp only [Iso.trans_inv, Category.assoc]
          rfl
    _ = u.inv ≫ ((e.app (unitObj X)).inv ≫
        (e.hom.app (unitObj X) ≫
          (restrictFunctor iU ⋙ pushforward f').map q)) := by rw [hnat]
    _ = u.inv ≫ (restrictFunctor iU ⋙ pushforward f').map q := by
      have ehom : (e.app (unitObj X)).hom = e.hom.app (unitObj X) := rfl
      rw [← ehom]
      let m := (restrictFunctor iU ⋙ pushforward f').map q
      have hinner : (e.app (unitObj X)).inv ≫
          (e.app (unitObj X)).hom ≫ m = m := by
        rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      exact congrArg (fun z ↦ u.inv ≫ z) hinner
    _ = _ := by
      change (pushforward f').map r.inv ≫
        (pushforward f').map ((restrictFunctor iU).map q) = _
      exact ((pushforward f').map_comp r.inv ((restrictFunctor iU).map q)).symm

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
  change
    ((restrictPushforwardPresheafIsoOfIsPullback
      (f ≫ g) (f' ≫ g') iA iC (Hf.paste_horiz Hg) M).hom.app (.op W)).hom x =
      ((((restrictPushforwardIsoOfIsPullback f f' iA iB Hf).hom.app M).app
        (g' ⁻¹ᵁ W)).hom
          (((restrictPushforwardPresheafIsoOfIsPullback
            g g' iB iC Hg ((pushforward f).obj M)).hom.app (.op W)).hom x))
  rw [restrictPushforwardIsoOfIsPullback_hom_app_apply]
  dsimp [restrictPushforwardPresheafIsoOfIsPullback]
  change M.presheaf.map _ x = M.presheaf.map _ (M.presheaf.map _ x)
  rw [← Functor.map_comp_apply]
  exact ConcreteCategory.congr_hom
    (M.presheaf.congr_map (Subsingleton.elim _ _)) x

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
  rw [restrictPushforwardIsoOfIsPullback_hom_app_apply]
  change
    ((restrictPushforwardPresheafIsoOfIsPullback
      f f₂ iU iV H₂ M).hom.app (.op W)).hom x =
      (((pushforwardCongr h).hom.app ((restrictFunctor iU).obj M)).app W).hom
        ((((restrictPushforwardIsoOfIsPullback
          f f₁ iU iV H₁).hom.app M).app W).hom x)
  rw [restrictPushforwardIsoOfIsPullback_hom_app_apply]
  rw [pushforwardCongr_hom_app_app]
  dsimp [restrictPushforwardPresheafIsoOfIsPullback]
  change M.presheaf.map _ x = M.presheaf.map _ (M.presheaf.map _ x)
  rw [← Functor.map_comp_apply]
  exact ConcreteCategory.congr_hom
    (M.presheaf.congr_map (Subsingleton.elim _ _)) x

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
  have he : eij.hom ≫ ejk.hom = eik.hom := by
    dsimp only [eij, ejk, eik]
    simpa only [c.chartTransitionCoordinateIso_hom] using ht
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
    dsimp only [AffineIntersectionUnitCocycle.chartToTripleLeftPullback]
    infer_instance
  rw [c.chartToTripleLeftRestricted_eq hopen hpush k i k]
  rw [Adjunction.homEquiv_apply]
  have hunit : IsIso ((pullbackPushforwardAdjunction t.p₁₃).unit.app
      (unitObj (D.V (i, k)))) := by
    infer_instance
  have hmap : IsIso ((pushforward t.p₁₃).map
      (c.chartToTripleLeftPullback hopen hpush k i k)) := by
    infer_instance
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
  have hmap : IsIso ((pushforward q).map
      (c.chartToTripleLeftRestricted hopen hpush k i k)) := by
    infer_instance
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
  have hunit : IsIso ((pushforward t.p₃).map
      (@restrictUnitIso _ _ t.p₁₂
        (affineIntersectionChartTriple_p₁₂_open hopen hpush i k k)).hom) := by
    infer_instance
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
  have hmate : (pullbackPushforwardAdjunction t.p₂₃).homEquiv _ _ beta =
      SheafOfModules.unitToPushforwardObjUnit t.p₂₃.toRingCatSheafHom ≫
        (pushforward t.p₂₃).map rU.inv := by
    dsimp only [beta]
    rw [Adjunction.homEquiv_naturality_right]
    rw [ModularCurves.pullbackUnitIso_homEquivLow]
    rfl
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
  have htarget := c.chartGlueTargetRestrictIso_hom_π hopen hpush k (i, j)
  have htarget' := congrArg
    (fun m ↦ R.map (c.chartGlueLeft hopen hpush) ≫ m) htarget
  have hleft := c.restrictChartGlueLeft_π hopen hpush k i j
  have hleft' := congrArg (fun m ↦ m ≫ e.hom) hleft
  calc
    _ = R.map (c.chartGlueLeft hopen hpush) ≫
        (R.map (Pi.π (fun lm : J × J ↦
          c.overlapExtension hopen hpush lm.1 lm.2) (i, j)) ≫ e.hom) := htarget'
    _ = (R.map (c.chartGlueLeft hopen hpush) ≫
        R.map (Pi.π (fun lm : J × J ↦
          c.overlapExtension hopen hpush lm.1 lm.2) (i, j))) ≫ e.hom :=
      (Category.assoc _ _ _).symm
    _ = (R.map (Pi.π (fun l : J ↦ c.chartExtension hopen hpush l) i) ≫
        R.map (c.chartToOverlapLeft hopen hpush i j)) ≫ e.hom := hleft'
    _ = _ := Category.assoc _ _ _

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
  have htarget := c.chartGlueTargetRestrictIso_hom_π hopen hpush k (i, j)
  have htarget' := congrArg
    (fun m ↦ R.map (c.chartGlueRight hopen hpush) ≫ m) htarget
  have hright := c.restrictChartGlueRight_π hopen hpush k i j
  have hright' := congrArg (fun m ↦ m ≫ e.hom) hright
  calc
    _ = R.map (c.chartGlueRight hopen hpush) ≫
        (R.map (Pi.π (fun lm : J × J ↦
          c.overlapExtension hopen hpush lm.1 lm.2) (i, j)) ≫ e.hom) := htarget'
    _ = (R.map (c.chartGlueRight hopen hpush) ≫
        R.map (Pi.π (fun lm : J × J ↦
          c.overlapExtension hopen hpush lm.1 lm.2) (i, j))) ≫ e.hom :=
      (Category.assoc _ _ _).symm
    _ = (R.map (Pi.π (fun l : J ↦ c.chartExtension hopen hpush l) j) ≫
        R.map (c.chartToOverlapRight hopen hpush i j)) ≫ e.hom := hright'
    _ = _ := Category.assoc _ _ _

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
  exact R.map (equalizer.ι
        (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush)) ≫
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

end

end AlgebraicGeometry.Scheme.Modules
