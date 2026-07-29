import ModularCurves.Picard.DualPullback.Naturality

/-!
# Over-site restriction coherence

Comparison of iterated over-site restriction with restriction on open subschemes.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u v₁ v₂ u₁ u₂

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

theorem pushforwardCongr₂_hom_app_apply
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : C ⥤ D} {T : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [Functor.IsContinuous F J K] [Functor.IsContinuous G J K]
    (f : T ⟶ (G.sheafPushforwardContinuous RingCat J K).obj S)
    {g : T ⟶ (F.sheafPushforwardContinuous RingCat J K).obj S}
    (e : F ≅ G)
    (he : f ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom _ _ _).app S = g)
    (M : _root_.SheafOfModules S) (U : Opposite C)
    (x : ((_root_.SheafOfModules.pushforward f).obj M).val.obj U) :
    ((_root_.SheafOfModules.pushforwardCongr₂ f e he).hom.app M).val.app U x =
      M.val.map (e.hom.app U.unop).op x := by
  rfl

noncomputable def restrictOpenCompIso {U V : X.Opens} (i : V ⟶ U) :
    restrictFunctor V.ι ≅
      restrictFunctor U.ι ⋙ restrictFunctor (X.homOfLE (leOfHom i)) :=
  restrictFunctorCongr (X.homOfLE_ι (leOfHom i)).symm ≪≫
    restrictFunctorComp (X.homOfLE (leOfHom i)) U.ι

noncomputable def overRestrictionStage1 (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (overEquiv V).functor.map
    ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).inv.app M)

theorem overRestrictionStage1_app_apply
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (W : Opposite V.toScheme.Opens)
    (x : ((overEquiv V).functor.obj (M.over V)).val.obj W) :
    (overRestrictionStage1 M i).val.app W x = x := by
  rfl

noncomputable def overRestrictionStage2 (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (overMapCompOverEquiv i).hom.app (M.over U)

noncomputable def overMapCompOverEquivStage1 {U V : X.Opens}
    (i : V ⟶ U) :=
  _root_.SheafOfModules.pushforwardComp
    ((TopologicalSpace.Opens.overPullbackSheafEquivOver V).app
      X.ringCatSheaf).inv
    (Sheaf.pushforwardOverMapIso X.ringCatSheaf i).inv

theorem overMapCompOverEquivStage1_app_apply
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (W : Opposite V.toScheme.Opens)
    (x : ((restrictFunctor V.ι).obj M).val.obj W) :
    ((overMapCompOverEquivStage1 i).hom.app (M.over U)).val.app W x = x := by
  rfl

noncomputable def overMapOpenIso {U V : X.Opens} (i : V ⟶ U) :
    (X.homOfLE (leOfHom i)).opensFunctor ⋙
        (TopologicalSpace.Opens.overEquivalence U).symm.functor ≅
      (TopologicalSpace.Opens.overEquivalence V).symm.functor ⋙ Over.map i := by
  refine NatIso.ofComponents (fun W ↦ Over.isoMk (eqToIso ?_) ?_) ?_
  · suffices U.ι ''ᵁ ((X.homOfLE (leOfHom i)) ''ᵁ W) = V.ι ''ᵁ W by
      simpa
    simp [← Scheme.Hom.comp_image]
  · cat_disch
  · cat_disch

noncomputable def overRestrictionStage3 (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (restrictFunctor (X.homOfLE (leOfHom i))).map
    ((overFunctorEquiv U).hom.app M)

theorem overRestrictionStage3_app_apply
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (W : Opposite V.toScheme.Opens)
    (x : ((restrictFunctor (X.homOfLE (leOfHom i))).obj
      ((overEquiv U).functor.obj (M.over U))).val.obj W) :
    (overRestrictionStage3 M i).val.app W x = x := by
  dsimp only [overRestrictionStage3]
  rw [restrictFunctor_map_app_apply]
  exact overFunctorEquiv_hom_app_apply U M _ x

noncomputable def restrictOpenCompMap (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (restrictOpenCompIso i).hom.app M

theorem overRestrictionStage2_app_apply
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (W : Opposite V.toScheme.Opens)
    (x : ((restrictFunctor V.ι).obj M).val.obj W) :
    (overRestrictionStage2 M i).val.app W x =
      (restrictOpenCompMap M i).val.app W x := by
  haveI : (Scheme.Hom.opensFunctor (X.homOfLE (leOfHom i))).IsContinuous
      (Opens.grothendieckTopology V.toScheme)
      (Opens.grothendieckTopology U.carrier) :=
    inferInstanceAs
      ((X.homOfLE (leOfHom i)).opensFunctor.IsContinuous _
        (Opens.grothendieckTopology U.toScheme))
  haveI := U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence
  haveI : (TopologicalSpace.Opens.overEquivalence U).symm.functor.IsContinuous
      (Opens.grothendieckTopology U.toScheme)
      ((Opens.grothendieckTopology X).over U) :=
    inferInstanceAs
      (U.overEquivalence.inverse.IsContinuous
        (Opens.grothendieckTopology U.carrier)
        ((Opens.grothendieckTopology X).over U))
  haveI : (Scheme.Hom.opensFunctor (X.homOfLE (leOfHom i))).IsContinuous
      (Opens.grothendieckTopology V.toScheme)
      (Opens.grothendieckTopology U.toScheme) :=
    inferInstanceAs
      ((X.homOfLE (leOfHom i)).opensFunctor.IsContinuous
        (Opens.grothendieckTopology V.toScheme)
        (Opens.grothendieckTopology U.toScheme))
  haveI := V.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence
  haveI : (TopologicalSpace.Opens.overEquivalence V).symm.functor.IsContinuous
      (Opens.grothendieckTopology V.toScheme)
      ((Opens.grothendieckTopology X).over V) :=
    inferInstanceAs
      (V.overEquivalence.inverse.IsContinuous
        (Opens.grothendieckTopology V.carrier)
        ((Opens.grothendieckTopology X).over V))
  haveI : ((TopologicalSpace.Opens.overEquivalence V).symm.functor ⋙
      Over.map i).IsContinuous
      (Opens.grothendieckTopology V.toScheme)
      ((Opens.grothendieckTopology X).over U) :=
    Functor.isContinuous_comp
      (TopologicalSpace.Opens.overEquivalence V).symm.functor
      (Over.map i)
      (Opens.grothendieckTopology V.toScheme)
      ((Opens.grothendieckTopology X).over V)
      ((Opens.grothendieckTopology X).over U)
  haveI : ((X.homOfLE (leOfHom i)).opensFunctor ⋙
      (TopologicalSpace.Opens.overEquivalence U).symm.functor).IsContinuous
      (Opens.grothendieckTopology V.toScheme)
      ((Opens.grothendieckTopology X).over U) := by
    let h₁ : (X.homOfLE (leOfHom i)).opensFunctor.IsContinuous
        (Opens.grothendieckTopology V.toScheme)
        (Opens.grothendieckTopology U.toScheme) := inferInstance
    let h₂ : (TopologicalSpace.Opens.overEquivalence U).symm.functor.IsContinuous
        (Opens.grothendieckTopology U.toScheme)
        ((Opens.grothendieckTopology X).over U) := inferInstance
    exact @Functor.isContinuous_comp _ _ _ _ _ _
      (X.homOfLE (leOfHom i)).opensFunctor
      (TopologicalSpace.Opens.overEquivalence U).symm.functor
      (Opens.grothendieckTopology V.toScheme)
      (Opens.grothendieckTopology U.toScheme)
      ((Opens.grothendieckTopology X).over U) h₁ h₂
  let φ : (TopologicalSpace.Opens.sheafRestrict V).obj X.ringCatSheaf ⟶
      (((TopologicalSpace.Opens.overEquivalence V).symm.functor ⋙
          Over.map i).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology V.toScheme)
        ((Opens.grothendieckTopology X).over U)).obj
          (X.ringCatSheaf.over U) :=
    ((TopologicalSpace.Opens.overPullbackSheafEquivOver V).app
        X.ringCatSheaf).inv ≫
      ((TopologicalSpace.Opens.overEquivalence V).symm.functor.sheafPushforwardContinuous RingCat
          (Opens.grothendieckTopology V.toScheme)
          ((Opens.grothendieckTopology X).over V)).map
        (Sheaf.pushforwardOverMapIso X.ringCatSheaf i).inv
  let hF : ((X.homOfLE (leOfHom i)).opensFunctor ⋙
      (TopologicalSpace.Opens.overEquivalence U).symm.functor).IsContinuous
      (Opens.grothendieckTopology V.toScheme)
      ((Opens.grothendieckTopology X).over U) := inferInstance
  let hG : ((TopologicalSpace.Opens.overEquivalence V).symm.functor ⋙
      Over.map i).IsContinuous
      (Opens.grothendieckTopology V.toScheme)
      ((Opens.grothendieckTopology X).over U) := inferInstance
  dsimp only [overRestrictionStage2, restrictOpenCompMap,
    restrictOpenCompIso, overMapCompOverEquiv, Iso.trans_hom,
    NatTrans.comp_app]
  erw [sheafOfModules_comp_app_apply]
  erw [sheafOfModules_comp_app_apply]
  erw [sheafOfModules_comp_app_apply]
  erw [overMapCompOverEquivStage1_app_apply M i W x]
  erw [@pushforwardCongr₂_hom_app_apply
    V.toScheme.Opens _ (Over U) _
    (Opens.grothendieckTopology V.toScheme)
    ((Opens.grothendieckTopology X).over U)
    ((X.homOfLE (leOfHom i)).opensFunctor ⋙
      (TopologicalSpace.Opens.overEquivalence U).symm.functor)
    ((TopologicalSpace.Opens.overEquivalence V).symm.functor ⋙ Over.map i)
    ((TopologicalSpace.Opens.sheafRestrict V).obj X.ringCatSheaf)
    (X.ringCatSheaf.over U) hF hG φ _ (overMapOpenIso i) _
    (M.over U) W x]
  erw [sheafOfModules_comp_app_apply]
  have hcongr := ConcreteCategory.congr_hom
    (restrictFunctorCongr_hom_app_app
      (U := W.unop) (X.homOfLE_ι (leOfHom i)).symm M) x
  let hopen : ((X.homOfLE (leOfHom i)) ≫ U.ι) ''ᵁ W.unop =
      V.ι ''ᵁ W.unop := by
    apply TopologicalSpace.Opens.ext
    change Set.image
      (fun x ↦ ((X.homOfLE (leOfHom i) ≫ U.ι) x)) W.unop =
        Set.image (fun x ↦ V.ι x) W.unop
    rw [X.homOfLE_ι]
  let y := M.presheaf.map
    (eqToHom hopen).op x
  let q := ConcreteCategory.hom
    (((restrictFunctorComp (X.homOfLE (leOfHom i)) U.ι).hom.app M).app W.unop)
  have hq : q
      (ConcreteCategory.hom
        (((restrictFunctorCongr
          (X.homOfLE_ι (leOfHom i)).symm).hom.app M).app W.unop) x) =
      q y := by
    exact congrArg q hcongr
  have hcomp := ConcreteCategory.congr_hom
    (restrictFunctorComp_hom_app_app
      (U := W.unop) (X.homOfLE (leOfHom i)) U.ι M) y
  have hfirst :
      (M.over U).val.map ((overMapOpenIso i).hom.app W.unop).op x = q y := by
    rw [hcomp]
    change M.presheaf.map _ x =
      M.presheaf.map _ (M.presheaf.map _ x)
    erw [← M.presheaf.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) x
  exact hfirst.trans hq.symm

noncomputable def overRestrictionComparisonLeft (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    (overEquiv V).functor.obj (M.over V) ⟶
      (restrictFunctor (X.homOfLE (leOfHom i))).obj
        ((restrictFunctor U.ι).obj M) :=
  overRestrictionStage1 M i ≫
    overRestrictionStage2 M i ≫
      overRestrictionStage3 M i

noncomputable def overRestrictionComparisonRight (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    (overEquiv V).functor.obj (M.over V) ⟶
      (restrictFunctor (X.homOfLE (leOfHom i))).obj
        ((restrictFunctor U.ι).obj M) :=
  (overFunctorEquiv V).hom.app M ≫
    restrictOpenCompMap M i

theorem overRestrictionComparison_app_apply (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (W : Opposite V.toScheme.Opens)
    (x : ((overEquiv V).functor.obj (M.over V)).val.obj W) :
    (overRestrictionComparisonLeft M i).val.app W x =
      (overRestrictionComparisonRight M i).val.app W x := by
  change (overRestrictionStage3 M i).val.app W
      ((overRestrictionStage2 M i).val.app W
        ((overRestrictionStage1 M i).val.app W x)) =
    (restrictOpenCompMap M i).val.app W
      (((overFunctorEquiv V).hom.app M).val.app W x)
  rw [overRestrictionStage3_app_apply]
  exact overRestrictionStage2_app_apply M i W x

theorem overRestrictionComparison (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    overRestrictionComparisonLeft M i =
      overRestrictionComparisonRight M i := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact overRestrictionComparison_app_apply M i W x

theorem overRestrictModuleIso_comp_overFunctorEquiv (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    (overRestrictModuleIso M i).hom ≫
        (restrictFunctor (X.homOfLE (leOfHom i))).map
          ((overFunctorEquiv U).hom.app M) =
      (overFunctorEquiv V).hom.app M ≫
        (restrictOpenCompIso i).hom.app M := by
  change overRestrictionComparisonLeft M i =
    overRestrictionComparisonRight M i
  exact overRestrictionComparison M i

theorem overRestrictionComparison_inv (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    (overFunctorEquiv V).inv.app M ≫
        (overRestrictModuleIso M i).hom =
      (restrictOpenCompIso i).hom.app M ≫
        (restrictFunctor (X.homOfLE (leOfHom i))).map
          ((overFunctorEquiv U).inv.app M) := by
  let R := restrictFunctor (X.homOfLE (leOfHom i))
  let eVh := (overFunctorEquiv V).hom.app M
  let eVi := (overFunctorEquiv V).inv.app M
  let eUh := R.map ((overFunctorEquiv U).hom.app M)
  let eUi := R.map ((overFunctorEquiv U).inv.app M)
  let r := (overRestrictModuleIso M i).hom
  let c := (restrictOpenCompIso i).hom.app M
  have h : r ≫ eUh = eVh ≫ c :=
    overRestrictModuleIso_comp_overFunctorEquiv M i
  have hU : eUh ≫ eUi = 𝟙 _ := by
    exact (R.mapIso ((overFunctorEquiv U).app M)).hom_inv_id
  have hV : eVi ≫ eVh = 𝟙 _ :=
    (overFunctorEquiv V).inv_hom_id_app M
  change eVi ≫ r = c ≫ eUi
  calc
    eVi ≫ r = (eVi ≫ r) ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = (eVi ≫ r) ≫ (eUh ≫ eUi) :=
      congrArg (fun q ↦ (eVi ≫ r) ≫ q) hU.symm
    _ = eVi ≫ (r ≫ eUh) ≫ eUi := by
      simp only [Category.assoc]
    _ = eVi ≫ (eVh ≫ c) ≫ eUi :=
      congrArg (fun q ↦ eVi ≫ q ≫ eUi) h
    _ = (eVi ≫ eVh) ≫ c ≫ eUi := by
      simp only [Category.assoc]
    _ = (𝟙 _ ≫ c) ≫ eUi :=
      congrArg (fun q ↦ (q ≫ c) ≫ eUi) hV
    _ = c ≫ eUi := by
      rw [Category.id_comp]

variable {X Y : Scheme.{u}}

noncomputable def localPullbackRestrictIso (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens) :
    (pullback (f ∣_ U)).obj ((restrictFunctor U.ι).obj M) ≅
      (restrictFunctor (f ⁻¹ᵁ U).ι).obj ((pullback f).obj M) :=
  (pullback (f ∣_ U)).mapIso ((restrictFunctorIsoPullback U.ι).app M) ≪≫
    (pullbackComp (f ∣_ U) U.ι).app M ≪≫
    (pullbackCongr (morphismRestrict_ι f U)).app M ≪≫
    ((pullbackComp (f ⁻¹ᵁ U).ι f).app M).symm ≪≫
    ((restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app
      ((pullback f).obj M)).symm

theorem localPullbackRestrictIso_eq (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens) :
    localPullbackRestrictIso f M U =
      (pullback (f ∣_ U)).mapIso
          ((restrictFunctorIsoPullback U.ι).app M) ≪≫
        (pullbackSquareIso (f ∣_ U) U.ι (f ⁻¹ᵁ U).ι f
          (morphismRestrict_ι f U)).app M ≪≫
        ((restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app
          ((pullback f).obj M)).symm := by
  rfl

theorem localPullbackRestrictIso_naturality (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    (pullback (f ∣_ V)).map ((restrictOpenCompIso i).hom.app M) ≫
        (openPullbackRestrictIso f i).hom.app
          ((restrictFunctor U.ι).obj M) ≫
        (restrictFunctor
          (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
            (localPullbackRestrictIso f M U).hom =
      (localPullbackRestrictIso f M V).hom ≫
        (restrictOpenCompIso
          ((TopologicalSpace.Opens.map f.base).map i)).hom.app
            ((pullback f).obj M) :=
  localPullbackRestrictIso_naturalityF f M i
end AlgebraicGeometry.Scheme.Modules
