import ModularCurves.Picard.DualPullback.LocalModuleRestriction

/-!
# Pullback coherence for structure modules

Option-free compatibility of pullback and restriction with the structure-module unit.
-/

universe u v w u₁ u₂ v₁ v₂

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

theorem localPullbackUnitIso_hom_eqP (f : Y ⟶ X) (U : X.Opens) :
    (localPullbackUnitIso f U).hom = (pullbackUnitIso (f ∣_ U)).hom := by
  let P := pullback (f ∣_ U)
  let e := (pullbackUnitIso (f ∣_ U)).hom
  change P.map (𝟙 _) ≫ e ≫ 𝟙 _ = e
  erw [P.map_id]
  simp

example (U : X.Opens) :
    (unitObj X).over U =
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U) := by
  rfl

example {U V : X.Opens} (i : V ⟶ U) :
    overRestrictUnitIso i =
      (overRestrictModuleIso (unitObj X) i).symm := by
  rfl

theorem restrictUnitIso_inv_app_applyP {A B : Scheme.{u}} (g : A ⟶ B)
    [IsOpenImmersion g] (W : A.Opens) (x : Γ(A, W)) :
    ((restrictUnitIso g).inv.val.app (op W)).hom' x =
      (g.appIso W).inv x := by
  rfl

theorem overFunctorEquiv_unitP (U : X.Opens) :
    (overFunctorEquiv U).app (unitObj X) =
      (restrictUnitIso U.ι).symm := by
  apply Iso.ext
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((overFunctorEquiv U).hom.app (unitObj X)).val.app W x =
    ((restrictUnitIso U.ι).inv.val.app W).hom' x
  rw [overFunctorEquiv_hom_app_apply]
  have hrestrict : ((restrictUnitIso U.ι).inv.val.app W).hom' x =
      (U.ι.appIso W.unop).inv x :=
    restrictUnitIso_inv_app_applyP
      (A := U.toScheme) (B := X) U.ι W.unop x
  rw [hrestrict, Scheme.Opens.ι_appIso]
  change x = x
  rfl

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

theorem overEquivalence_inverse_obj_leftP (U : X.Opens)
    (Z : U.toScheme.Opens) :
    (U.overEquivalence.symm.functor.obj Z).left = U.ι ''ᵁ Z := by
  rfl

theorem overEquivalence_left_eq_comp_imageP {U V : X.Opens}
    (i : V ⟶ U) (Z : V.toScheme.Opens) :
    (V.overEquivalence.symm.functor.obj Z).left =
      (X.homOfLE (leOfHom i) ≫ U.ι) ''ᵁ Z := by
  rw [overEquivalence_inverse_obj_leftP]
  simp

theorem comp_image_eq_overEquivalence_leftP {U V : X.Opens}
    (i : V ⟶ U) (Z : V.toScheme.Opens) :
    (X.homOfLE (leOfHom i) ≫ U.ι) ''ᵁ Z =
      (U.overEquivalence.symm.functor.obj
        (X.homOfLE (leOfHom i) ''ᵁ Z)).left := by
  rw [overEquivalence_inverse_obj_leftP]
  rw [Scheme.Hom.comp_image]

theorem restrictOpenCompMap_unit_app_applyP {U V : X.Opens}
    (i : V ⟶ U) (Z : V.toScheme.Opensᵒᵖ)
    (x : ((restrictFunctor V.ι).obj (unitObj X)).val.obj Z) :
    (restrictOpenCompMap (unitObj X) i).val.app Z x =
      ((X.homOfLE (leOfHom i)).appIso Z.unop).inv x := by
  let g := X.homOfLE (leOfHom i)
  let hι : V.ι = g ≫ U.ι := (X.homOfLE_ι (leOfHom i)).symm
  let a := (restrictFunctorCongr hι).hom.app (unitObj X)
  let b := (restrictFunctorComp g U.ι).hom.app (unitObj X)
  dsimp only [restrictOpenCompMap, restrictOpenCompIso, Iso.trans_hom,
    NatTrans.comp_app]
  erw [sheafOfModules_comp_app_apply]
  change b.val.app Z (a.val.app Z x) = _
  have ha := ConcreteCategory.congr_hom
    (restrictFunctorCongr_hom_app_app
      (U := Z.unop) hι (unitObj X)) x
  have hfirst := congrArg (fun y => b.val.app Z y) ha
  refine Eq.trans hfirst ?_
  change ((restrictFunctorComp g U.ι).hom.app (unitObj X)).val.app Z _ = _
  erw [ConcreteCategory.congr_hom
    (restrictFunctorComp_hom_app_app
      (U := Z.unop) g U.ι (unitObj X)) _]
  change X.presheaf.map _ (X.presheaf.map _ x) = _
  erw [← X.presheaf.map_comp_apply]
  rw [Scheme.Hom.appIso_homOfLE_inv]
  exact ConcreteCategory.congr_hom
    (X.presheaf.congr_map (Subsingleton.elim _ _)) x

theorem overMapCompOverEquiv_unitP {U V : X.Opens} (i : V ⟶ U) :
    (overMapCompOverEquiv i).app
        (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)) =
      (restrictUnitIso (X.homOfLE (leOfHom i))).symm := by
  apply Iso.ext
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((overMapCompOverEquiv i).hom.app
      ((unitObj X).over U)).val.app Z x =
    ((restrictUnitIso (X.homOfLE (leOfHom i))).inv.val.app Z).hom' x
  change (overRestrictionStage2 (unitObj X) i).val.app Z x =
    ((restrictUnitIso (X.homOfLE (leOfHom i))).inv.val.app Z).hom' x
  have hstage : (overRestrictionStage2 (unitObj X) i).val.app Z x =
      (restrictOpenCompMap (unitObj X) i).val.app Z x :=
    overRestrictionStage2_app_apply (X := X) (unitObj X) i Z x
  have hopen : (restrictOpenCompMap (unitObj X) i).val.app Z x =
      ((X.homOfLE (leOfHom i)).appIso Z.unop).inv x :=
    restrictOpenCompMap_unit_app_applyP i Z x
  have hrestrict :
      ((restrictUnitIso (X.homOfLE (leOfHom i))).inv.val.app Z).hom' x =
        ((X.homOfLE (leOfHom i)).appIso Z.unop).inv x :=
    restrictUnitIso_inv_app_applyP
      (A := V.toScheme) (B := U.toScheme)
      (X.homOfLE (leOfHom i)) Z.unop x
  exact hstage.trans (hopen.trans hrestrict.symm)

theorem overRestrictUnitIso_eq_restrictUnitIsoP {U V : X.Opens}
    (i : V ⟶ U) :
    overRestrictUnitIso i = restrictUnitIso (X.homOfLE (leOfHom i)) := by
  rw [overRestrictUnitIso, overMapCompOverEquiv_unitP]
  rfl

end AlgebraicGeometry.Scheme.Modules

open CategoryTheory


namespace CategoryTheory

theorem homEquiv_comp_conjugate
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {X : C} {Y : D} (p : L₁.obj X ⟶ Y) :
    (adj₂.homEquiv X Y) (α.app X ≫ p) =
      (adj₁.homEquiv X Y) p ≫
        (conjugateEquiv adj₁ adj₂ α).app Y := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_comp]
  calc
    adj₂.unit.app X ≫ R₂.map (α.app X) ≫ R₂.map p =
        (adj₂.unit.app X ≫ R₂.map (α.app X)) ≫ R₂.map p :=
      (Category.assoc _ _ _).symm
    _ = (adj₁.unit.app X ≫
          (conjugateEquiv adj₁ adj₂ α).app (L₁.obj X)) ≫ R₂.map p :=
      congrArg (fun k => k ≫ R₂.map p)
        (unit_conjugateEquiv adj₁ adj₂ α X).symm
    _ = adj₁.unit.app X ≫
        ((conjugateEquiv adj₁ adj₂ α).app (L₁.obj X) ≫ R₂.map p) :=
      Category.assoc _ _ _
    _ = adj₁.unit.app X ≫
        (R₁.map p ≫ (conjugateEquiv adj₁ adj₂ α).app Y) :=
      congrArg (fun k => adj₁.unit.app X ≫ k)
        ((conjugateEquiv adj₁ adj₂ α).naturality p).symm
    _ = (adj₁.unit.app X ≫ R₁.map p) ≫
        (conjugateEquiv adj₁ adj₂ α).app Y :=
      (Category.assoc _ _ _).symm

theorem homEquiv_comp_of_homEquiv_eq_unit
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {L₁ L₂ : C ⥤ D} {R : D ⥤ C}
    (adj₁ : L₁ ⊣ R) (adj₂ : L₂ ⊣ R)
    {X : C} {Y : D} (e : L₁.obj X ⟶ L₂.obj X)
    (he : (adj₁.homEquiv X (L₂.obj X)) e = adj₂.unit.app X)
    (p : L₂.obj X ⟶ Y) :
    (adj₁.homEquiv X Y) (e ≫ p) = (adj₂.homEquiv X Y) p := by
  rw [adj₁.homEquiv_naturality_right, he, Adjunction.homEquiv_unit]

end CategoryTheory

open AlgebraicGeometry CategoryTheory


namespace ModularCurves

private theorem comp_hom_invLow {C : Type v} [Category.{w} C]
    {A B D : C} (q : A ⟶ B) (e : B ≅ D) :
    (q ≫ e.hom) ≫ e.inv = q := by
  simp

theorem unitToPushforwardObjUnit_compLow {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app (Scheme.Modules.unitObj X) := by
  apply SheafOfModules.hom_ext
  ext U
  rfl

theorem pullbackUnitIso_homEquivLow {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
        (Scheme.Modules.pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  erw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]

theorem pullbackUnitIso_comp_conjugateLow {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    CategoryTheory.conjugateEquiv
        (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
        ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
          (Scheme.Modules.pullbackPushforwardAdjunction f))
        (Scheme.Modules.pullbackComp f g).hom =
      (Scheme.Modules.pushforwardComp f g).inv := by
  let adjc := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let adjd := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  have hconj : CategoryTheory.conjugateEquiv adjc adjd
      (Scheme.Modules.pullbackComp f g).inv =
        (Scheme.Modules.pushforwardComp f g).hom :=
    Scheme.Modules.conjugateEquiv_pullbackComp_inv f g
  have hconjIso : CategoryTheory.conjugateIsoEquiv adjc adjd
      (Scheme.Modules.pullbackComp f g).symm =
        Scheme.Modules.pushforwardComp f g := by
    apply Iso.ext
    exact hconj
  have h := congrArg Iso.inv hconjIso
  exact h

theorem pullbackUnitIso_comp_leftLow {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    let adjf := Scheme.Modules.pullbackPushforwardAdjunction f
    let adjg := Scheme.Modules.pullbackPushforwardAdjunction g
    let adjc := adjg.comp adjf
    let α := (Scheme.Modules.pullbackComp f g).app (Scheme.Modules.unitObj Z)
    let τ := Scheme.Modules.pushforwardComp f g
    (adjc.homEquiv _ _)
        (α.hom ≫ (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom) =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom ≫
        τ.inv.app (Scheme.Modules.unitObj X) := by
  let adjf := Scheme.Modules.pullbackPushforwardAdjunction f
  let adjg := Scheme.Modules.pullbackPushforwardAdjunction g
  let adjc := adjg.comp adjf
  let adjd := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let α := (Scheme.Modules.pullbackComp f g).app (Scheme.Modules.unitObj Z)
  let τ := Scheme.Modules.pushforwardComp f g
  have hconj' : CategoryTheory.conjugateEquiv adjd adjc
      (Scheme.Modules.pullbackComp f g).hom = τ.inv :=
    pullbackUnitIso_comp_conjugateLow f g
  have hfg := pullbackUnitIso_homEquivLow (f ≫ g)
  have hmate := CategoryTheory.homEquiv_comp_conjugate adjd adjc
    (Scheme.Modules.pullbackComp f g).hom
    (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom
  rw [hconj', hfg] at hmate
  exact hmate

theorem pullbackUnitIso_comp_rightLow {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    let adjf := Scheme.Modules.pullbackPushforwardAdjunction f
    let adjg := Scheme.Modules.pullbackPushforwardAdjunction g
    let adjc := adjg.comp adjf
    (adjc.homEquiv _ _)
        ((Scheme.Modules.pullback f).map
            (Scheme.Modules.pullbackUnitIso g).hom ≫
          (Scheme.Modules.pullbackUnitIso f).hom) =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  let adjf := Scheme.Modules.pullbackPushforwardAdjunction f
  let adjg := Scheme.Modules.pullbackPushforwardAdjunction g
  let adjc := adjg.comp adjf
  have hf := pullbackUnitIso_homEquivLow f
  have hg := pullbackUnitIso_homEquivLow g
  change (adjg.homEquiv _ _)
    ((adjf.homEquiv _ _)
      ((Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫
        (Scheme.Modules.pullbackUnitIso f).hom)) = _
  rw [Adjunction.homEquiv_naturality_left, hf]
  let pg := (Scheme.Modules.pullbackUnitIso g).hom
  let uf := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let ug := SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom
  change (adjg.homEquiv _ _) (pg ≫ uf) =
    ug ≫ (Scheme.Modules.pushforward g).map uf
  have hnat : (adjg.homEquiv _ _) (pg ≫ uf) =
      (adjg.homEquiv _ _) pg ≫ (Scheme.Modules.pushforward g).map uf :=
    adjg.homEquiv_naturality_right pg uf
  have hg' : (adjg.homEquiv _ _) pg = ug := hg
  exact hnat.trans
    (congrArg (fun k => k ≫ (Scheme.Modules.pushforward g).map uf) hg')

theorem pullbackUnitIso_compLow {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((Scheme.Modules.pullbackComp f g).app (Scheme.Modules.unitObj Z)).hom ≫
        (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom =
      (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫
        (Scheme.Modules.pullbackUnitIso f).hom := by
  let adjf := Scheme.Modules.pullbackPushforwardAdjunction f
  let adjg := Scheme.Modules.pullbackPushforwardAdjunction g
  let adjc := adjg.comp adjf
  let τ := Scheme.Modules.pushforwardComp f g
  apply (adjc.homEquiv _ _).injective
  let q : Scheme.Modules.unitObj Z ⟶
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g).obj
        (Scheme.Modules.unitObj X) :=
    SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward g).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
  have hcancel : (q ≫ τ.hom.app (Scheme.Modules.unitObj X)) ≫
      τ.inv.app (Scheme.Modules.unitObj X) = q :=
    comp_hom_invLow q (τ.app (Scheme.Modules.unitObj X))
  have hunit : SheafOfModules.unitToPushforwardObjUnit
        (f ≫ g).toRingCatSheafHom ≫
      τ.inv.app (Scheme.Modules.unitObj X) =
      (q ≫ τ.hom.app (Scheme.Modules.unitObj X)) ≫
        τ.inv.app (Scheme.Modules.unitObj X) :=
    congrArg (fun k => k ≫ τ.inv.app (Scheme.Modules.unitObj X))
      (unitToPushforwardObjUnit_compLow f g)
  have hleft : (adjc.homEquiv _ _)
      (((Scheme.Modules.pullbackComp f g).app
          (Scheme.Modules.unitObj Z)).hom ≫
        (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom) =
    SheafOfModules.unitToPushforwardObjUnit
        (f ≫ g).toRingCatSheafHom ≫
      τ.inv.app (Scheme.Modules.unitObj X) :=
    pullbackUnitIso_comp_leftLow f g
  have hright : (adjc.homEquiv _ _)
      ((Scheme.Modules.pullback f).map
          (Scheme.Modules.pullbackUnitIso g).hom ≫
        (Scheme.Modules.pullbackUnitIso f).hom) = q :=
    pullbackUnitIso_comp_rightLow f g
  exact hleft.trans (hunit.trans (hcancel.trans hright.symm))

end ModularCurves

open AlgebraicGeometry CategoryTheory


namespace ModularCurves

theorem restrictAdjunction_homEquiv_restrictUnitIsoLow
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    ((Scheme.Modules.restrictAdjunction f).homEquiv _ _)
        (Scheme.Modules.restrictUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  change (Scheme.Modules.restrictAdjunction f).unit.app
      (Scheme.Modules.unitObj Y) ≫
    (Scheme.Modules.pushforward f).map
      (Scheme.Modules.restrictUnitIso f).hom = _
  apply SheafOfModules.hom_ext
  ext U
  change (((Scheme.Modules.restrictAdjunction f).unit.app
      (Scheme.Modules.unitObj Y)).val.app U ≫
        (((Scheme.Modules.pushforward f).map
          (Scheme.Modules.restrictUnitIso f).hom).val.app U))
      (show Γ(Y, U.unop) from 1) = _
  let a := ((Scheme.Modules.restrictAdjunction f).unit.app
    (Scheme.Modules.unitObj Y)).val.app U
  let b := ((Scheme.Modules.pushforward f).map
    (Scheme.Modules.restrictUnitIso f).hom).val.app U
  have hcomp : ConcreteCategory.hom (a ≫ b) (1 : Γ(Y, U.unop)) =
      ConcreteCategory.hom b (ConcreteCategory.hom a (1 : Γ(Y, U.unop))) :=
    ConcreteCategory.comp_apply a b (1 : Γ(Y, U.unop))
  change ConcreteCategory.hom (a ≫ b) (1 : Γ(Y, U.unop)) = _
  rw [hcomp]
  dsimp only [a, b, Scheme.Modules.restrictAdjunction]
  erw [SheafOfModules.pushforwardPushforwardAdj_unit_app_val_app]
  change (f.appIso (f ⁻¹ᵁ U.unop)).hom
      (Y.presheaf.map _ (1 : Γ(Y, U.unop))) =
    (f.app U.unop).hom 1
  simp

theorem restrictFunctorIsoPullback_inv_comp_restrictUnitIsoLow
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctorIsoPullback f).inv.app
        (Scheme.Modules.unitObj Y) ≫
        (Scheme.Modules.restrictUnitIso f).hom =
      (Scheme.Modules.pullbackUnitIso f).hom := by
  let e := (Scheme.Modules.restrictFunctorIsoPullback f).app
    (Scheme.Modules.unitObj Y)
  apply (cancel_epi e.hom).1
  erw [Iso.hom_inv_id_assoc]
  let adjr := Scheme.Modules.restrictAdjunction f
  let adjp := Scheme.Modules.pullbackPushforwardAdjunction f
  apply (adjr.homEquiv _ _).injective
  let p := (Scheme.Modules.pullbackUnitIso f).hom
  have hrestrict := restrictAdjunction_homEquiv_restrictUnitIsoLow f
  have hrestrict' : (adjr.homEquiv _ _)
      (Scheme.Modules.restrictUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    hrestrict
  have he := CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app
    adjr adjp (Scheme.Modules.unitObj Y)
  change (adjr.homEquiv _ _) e.hom =
    adjp.unit.app (Scheme.Modules.unitObj Y) at he
  have hcompare := CategoryTheory.homEquiv_comp_of_homEquiv_eq_unit
    adjr adjp e.hom he p
  have hp0 := pullbackUnitIso_homEquivLow f
  exact hrestrict'.trans (hp0.symm.trans hcompare.symm)

theorem pullbackUnitIso_congrLow {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) :
    ((Scheme.Modules.pullbackCongr h).app (Scheme.Modules.unitObj Y)).hom ≫
        (Scheme.Modules.pullbackUnitIso g).hom =
      (Scheme.Modules.pullbackUnitIso f).hom := by
  subst g
  simp [Scheme.Modules.pullbackCongr]

end ModularCurves
