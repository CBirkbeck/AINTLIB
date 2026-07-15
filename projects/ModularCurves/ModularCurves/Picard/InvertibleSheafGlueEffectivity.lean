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

private noncomputable def AffineIntersectionUnitCocycle.chartGlueTarget
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    D.glued.Modules :=
  ∏ᶜ fun ij : J × J ↦ c.overlapExtension hopen hpush ij.1 ij.2

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
