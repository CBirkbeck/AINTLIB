import ModularCurves.Picard.InvertibleSheafGlueDataDescent

/-!
# Effectivity of affine-intersection line-bundle descent

This file glues the chartwise unit modules attached to an
`AffineIntersectionUnitCocycle`. The glued module is the usual Cech equalizer of
the chart extensions, with one overlap map twisted by the transition isomorphism.
-/

universe u

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

private noncomputable def restrictPushforwardIsoOfIsPullbackApp
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) (M : X.Modules) :
    (restrictFunctor iV).obj ((pushforward f).obj M) ≅
      (pushforward f').obj ((restrictFunctor iU).obj M) := by
  refine (fullyFaithfulToPresheafOfModules).preimageIso
    (PresheafOfModules.isoMk (fun W ↦ ?_) ?_)
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

end

end AlgebraicGeometry.Scheme.Modules
