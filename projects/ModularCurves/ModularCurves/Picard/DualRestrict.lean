import ModularCurves.Picard.Dual

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u v₁ v₂ u₁ u₂

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

theorem sheafOfModules_comp_app_apply
    {D : Type u} [Category.{u} D] {J : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {A B C : _root_.SheafOfModules R}
    (p : A ⟶ B) (q : B ⟶ C) (Z : Opposite D) (x : A.val.obj Z) :
    (p ≫ q).val.app Z x = q.val.app Z (p.val.app Z x) :=
  rfl

theorem overFunctorEquiv_hom_app_apply (T : X.Opens) (M : X.Modules)
    (Z : Opposite T.toScheme.Opens)
    (x : ((overEquiv T).functor.obj (M.over T)).val.obj Z) :
    ((overFunctorEquiv T).hom.app M).val.app Z x = x := by
  dsimp only [overFunctorEquiv, Iso.trans_hom, NatTrans.comp_app]
  erw [sheafOfModules_comp_app_apply]
  rfl

theorem overFunctorEquiv_inv_app_apply (T : X.Opens) (M : X.Modules)
    (Z : Opposite T.toScheme.Opens)
    (x : ((restrictFunctor T.ι).obj M).val.obj Z) :
    ((overFunctorEquiv T).inv.app M).val.app Z x = x := by
  dsimp only [overFunctorEquiv, Iso.trans_inv, NatTrans.comp_app]
  erw [sheafOfModules_comp_app_apply]
  rfl

theorem overEquiv_map_app_apply (T : X.Opens)
    {A B : _root_.SheafOfModules (X.ringCatSheaf.over T)}
    (p : A ⟶ B) (Z : Opposite T.toScheme.Opens)
    (x : ((overEquiv T).functor.obj A).val.obj Z) :
    ((overEquiv T).functor.map p).val.app Z x =
      p.val.app (op (T.overEquivalence.symm.functor.obj Z.unop)) x :=
  rfl

theorem restrictFunctor_map_app_apply {Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {M N : Y.Modules} (p : M ⟶ N)
    (Z : Opposite X.Opens) (x : ((restrictFunctor f).obj M).val.obj Z) :
    ((restrictFunctor f).map p).val.app Z x =
      p.val.app (f.opensFunctor.op.obj Z) x :=
  rfl

theorem equivalence_counitInv_map_inverse_comp_counit
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (F : C ≌ D) {A B : D} (f : A ⟶ B) :
    (F.counitIso.app A).inv ≫ F.functor.map (F.inverse.map f) ≫
      (F.counitIso.app B).hom = f := by
  have h :
      (F.counitIso.app A).inv ≫ F.functor.map (F.inverse.map f) ≫
          (F.counitIso.app B).hom =
        (F.counitIso.app A).inv ≫ ((F.counitIso.app A).hom ≫ f) :=
    congrArg (fun q ↦ (F.counitIso.app A).inv ≫ q)
      (F.counit_naturality f)
  exact h.trans ((F.counitIso.app A).inv_hom_id_assoc f)

theorem comp_appIso_hom_apply {A B C : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C)
    [IsOpenImmersion f] [IsOpenImmersion g]
    (U : A.Opens) (x : Γ(C, (f ≫ g) ''ᵁ U)) :
    ((f ≫ g).appIso U).hom x =
      (f.appIso U).hom
        ((g.appIso (f ''ᵁ U)).hom
          (C.presheaf.map
            (eqToHom (Scheme.Hom.comp_image f g U).symm).op x)) := by
  have h := congrArg Iso.hom (Scheme.Hom.comp_appIso f g U)
  have hx := ConcreteCategory.congr_hom h x
  simp only [Iso.trans_hom, CategoryTheory.comp_apply,
    Functor.mapIso_hom] at hx
  convert hx using 1
  congr 3

theorem appIso_congr_apply {A B : Scheme.{u}}
    (f g : A ⟶ B) [IsOpenImmersion f] [IsOpenImmersion g]
    (hfg : f = g) (U : A.Opens) (hU : f ''ᵁ U = g ''ᵁ U)
    (x : Γ(B, g ''ᵁ U)) :
    (f.appIso U).hom (B.presheaf.map (eqToHom hU).op x) =
      (g.appIso U).hom x := by
  subst g
  have he : hU = rfl := Subsingleton.elim _ _
  rw [he]
  simp

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

def imageOverFunctor (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :
    Over W ⥤ Over (j ''ᵁ W) :=
  Over.post j.opensFunctor

abbrev imageOver (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) (Z : Over W) :
    Over (j ''ᵁ W) :=
  (imageOverFunctor j W).obj Z

example (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (Z : Opposite (Over W))
    (x : (((restrictFunctor j).obj M).over W).val.obj Z) :
    (M.over (j ''ᵁ W)).val.obj (op (imageOver j W Z.unop)) :=
  x

noncomputable example (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) (Z : Opposite (Over W))
    (x : (_root_.SheafOfModules.unit
      (Y.ringCatSheaf.over (j ''ᵁ W))).val.obj
        (op (imageOver j W Z.unop))) :
    (_root_.SheafOfModules.unit (X.ringCatSheaf.over W)).val.obj Z :=
  (j.appIso Z.unop.left).hom x

noncomputable def localDualRestrictApp (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens)
    (alpha : M.over (j ''ᵁ W) ⟶
      _root_.SheafOfModules.unit (Y.ringCatSheaf.over (j ''ᵁ W)))
    (Z : Opposite (Over W)) :
    (((restrictFunctor j).obj M).over W).val.presheaf.obj Z ⟶
      (_root_.SheafOfModules.unit
        (X.ringCatSheaf.over W)).val.presheaf.obj Z :=
  AddCommGrpCat.ofHom
    { toFun := fun x ↦ (j.appIso Z.unop.left).hom
        (alpha.val.app (op (imageOver j W Z.unop)) x)
      map_zero' := by
        calc
          (j.appIso Z.unop.left).hom
              (alpha.val.app (op (imageOver j W Z.unop)) 0) =
            (j.appIso Z.unop.left).hom 0 :=
              congrArg _ (alpha.val.app
                (op (imageOver j W Z.unop))).hom.map_zero
          _ = 0 := (j.appIso Z.unop.left).hom.hom.map_zero
      map_add' := by
        intro x y
        calc
          (j.appIso Z.unop.left).hom
              (alpha.val.app (op (imageOver j W Z.unop)) (x + y)) =
            (j.appIso Z.unop.left).hom
              (alpha.val.app (op (imageOver j W Z.unop)) x +
                alpha.val.app (op (imageOver j W Z.unop)) y) :=
              congrArg _ ((alpha.val.app
                (op (imageOver j W Z.unop))).hom.map_add x y)
          _ = (j.appIso Z.unop.left).hom
                (alpha.val.app (op (imageOver j W Z.unop)) x) +
              (j.appIso Z.unop.left).hom
                (alpha.val.app (op (imageOver j W Z.unop)) y) :=
            (j.appIso Z.unop.left).hom.hom.map_add _ _ }

theorem localDualRestrictApp_naturality (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens)
    (alpha : M.over (j ''ᵁ W) ⟶
      _root_.SheafOfModules.unit (Y.ringCatSheaf.over (j ''ᵁ W)))
    {Z Z' : Opposite (Over W)} (f : Z ⟶ Z') :
    (((restrictFunctor j).obj M).over W).val.presheaf.map f ≫
        localDualRestrictApp M j W alpha Z' =
      localDualRestrictApp M j W alpha Z ≫
        (_root_.SheafOfModules.unit
          (X.ringCatSheaf.over W)).val.presheaf.map f := by
  ext x
  change (j.appIso Z'.unop.left).hom
      (alpha.val.app (op (imageOver j W Z'.unop))
        (((M.restrict j).over W).val.map f x)) =
    ((_root_.SheafOfModules.unit
      (X.ringCatSheaf.over W)).val.map f)
      ((j.appIso Z.unop.left).hom
        (alpha.val.app (op (imageOver j W Z.unop)) x))
  have hsource :
      ((M.restrict j).over W).val.map f x =
        (M.over (j ''ᵁ W)).val.map
          ((imageOverFunctor j W).op.map f) x := rfl
  have halpha := CategoryTheory.congr_fun
    (alpha.val.naturality ((imageOverFunctor j W).op.map f)) x
  have happ := CategoryTheory.congr_fun
    (j.appIso_hom_naturality f.unop.left.op)
    (alpha.val.app (op (imageOver j W Z.unop)) x)
  calc
    (j.appIso Z'.unop.left).hom
        (alpha.val.app (op (imageOver j W Z'.unop))
          (((M.restrict j).over W).val.map f x)) =
      (j.appIso Z'.unop.left).hom
        (alpha.val.app (op (imageOver j W Z'.unop))
          ((M.over (j ''ᵁ W)).val.map
            ((imageOverFunctor j W).op.map f) x)) :=
      congrArg (fun y ↦ (j.appIso Z'.unop.left).hom
        (alpha.val.app (op (imageOver j W Z'.unop)) y)) hsource
    _ = (j.appIso Z'.unop.left).hom
        ((_root_.SheafOfModules.unit
          (Y.ringCatSheaf.over (j ''ᵁ W))).val.map
            ((imageOverFunctor j W).op.map f)
              (alpha.val.app (op (imageOver j W Z.unop)) x)) := congrArg _ halpha
    _ = ((_root_.SheafOfModules.unit
        (X.ringCatSheaf.over W)).val.map f)
          ((j.appIso Z.unop.left).hom
            (alpha.val.app (op (imageOver j W Z.unop)) x)) := happ

theorem localDualRestrictApp_smul (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens)
    (alpha : M.over (j ''ᵁ W) ⟶
      _root_.SheafOfModules.unit (Y.ringCatSheaf.over (j ''ᵁ W)))
    (Z : Opposite (Over W))
    (r : (X.ringCatSheaf.over W).obj.obj Z)
    (x : (((restrictFunctor j).obj M).over W).val.obj Z) :
    localDualRestrictApp M j W alpha Z (r • x) =
      r • localDualRestrictApp M j W alpha Z x := by
  let rU : Γ(X, Z.unop.left) := r
  let rX : (Y.ringCatSheaf.over (j ''ᵁ W)).obj.obj
      (op (imageOver j W Z.unop)) :=
    (j.appIso Z.unop.left).inv rU
  let xX : (M.over (j ''ᵁ W)).val.obj
      (op (imageOver j W Z.unop)) := x
  let yX : (Y.ringCatSheaf.over (j ''ᵁ W)).obj.obj
      (op (imageOver j W Z.unop)) :=
    alpha.val.app (op (imageOver j W Z.unop)) xX
  change (j.appIso Z.unop.left).hom
      (alpha.val.app (op (imageOver j W Z.unop)) (rX • xX)) =
    rU • (j.appIso Z.unop.left).hom
      yX
  calc
    (j.appIso Z.unop.left).hom
        (alpha.val.app (op (imageOver j W Z.unop)) (rX • xX)) =
      (j.appIso Z.unop.left).hom
        (rX • yX) :=
      congrArg _ ((alpha.val.app
        (op (imageOver j W Z.unop))).hom.map_smul rX xX)
    _ = rU • (j.appIso Z.unop.left).hom yX := by
      change (j.appIso Z.unop.left).hom
          (rX * yX) =
        rU * (j.appIso Z.unop.left).hom yX
      calc
        (j.appIso Z.unop.left).hom (rX * yX) =
            (j.appIso Z.unop.left).hom rX *
              (j.appIso Z.unop.left).hom yX :=
          (j.appIso Z.unop.left).hom.hom.map_mul rX yX
        _ = rU * (j.appIso Z.unop.left).hom yX :=
          congrArg (fun a ↦ a * (j.appIso Z.unop.left).hom yX)
            (Iso.inv_hom_id_apply (j.appIso Z.unop.left) rU)

noncomputable def localDualRestrict (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens)
    (alpha : M.over (j ''ᵁ W) ⟶
      _root_.SheafOfModules.unit (Y.ringCatSheaf.over (j ''ᵁ W))) :
    ((restrictFunctor j).obj M).over W ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over W) where
  val := PresheafOfModules.homMk
    { app := localDualRestrictApp M j W alpha
      naturality := by
        intro Z Z' f
        exact localDualRestrictApp_naturality M j W alpha f }
    (localDualRestrictApp_smul M j W alpha)

theorem localDualRestrict_app_apply (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens)
    (alpha : M.over (j ''ᵁ W) ⟶
      _root_.SheafOfModules.unit (Y.ringCatSheaf.over (j ''ᵁ W)))
    (Z : Opposite (Over W))
    (x : (((restrictFunctor j).obj M).over W).val.obj Z) :
    (localDualRestrict M j W alpha).val.app Z x =
      (j.appIso Z.unop.left).hom
        (alpha.val.app (op (imageOver j W Z.unop)) x) :=
  rfl

theorem localDualRestrict_dualRestrict (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    {V W : Opposite X.Opens} (f : V ⟶ W)
    (alpha : M.over (j ''ᵁ V.unop) ⟶
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (j ''ᵁ V.unop))) :
    localDualRestrict M j W.unop
        (ModularCurves.SheafOfModules.dualRestrict Y.ringCatSheaf M
          (j.opensFunctor.op.map f) alpha) =
      ModularCurves.SheafOfModules.dualRestrict X.ringCatSheaf
        ((restrictFunctor j).obj M) f
          (localDualRestrict M j V.unop alpha) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem localDualRestrict_add (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens)
    (alpha beta : M.over (j ''ᵁ W) ⟶
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (j ''ᵁ W))) :
    localDualRestrict M j W (alpha + beta) =
      localDualRestrict M j W alpha + localDualRestrict M j W beta := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (j.appIso Z.unop.left).hom
      ((alpha + beta).val.app (op (imageOver j W Z.unop)) x) =
    (j.appIso Z.unop.left).hom
        (alpha.val.app (op (imageOver j W Z.unop)) x) +
      (j.appIso Z.unop.left).hom
        (beta.val.app (op (imageOver j W Z.unop)) x)
  calc
    (j.appIso Z.unop.left).hom
        ((alpha + beta).val.app (op (imageOver j W Z.unop)) x) =
      (j.appIso Z.unop.left).hom
        (alpha.val.app (op (imageOver j W Z.unop)) x +
          beta.val.app (op (imageOver j W Z.unop)) x) := rfl
    _ = (j.appIso Z.unop.left).hom
          (alpha.val.app (op (imageOver j W Z.unop)) x) +
        (j.appIso Z.unop.left).hom
          (beta.val.app (op (imageOver j W Z.unop)) x) :=
      (j.appIso Z.unop.left).hom.hom.map_add _ _

theorem localDualRestrict_smul (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens) (r : Γ(X, W))
    (alpha : M.over (j ''ᵁ W) ⟶
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (j ''ᵁ W))) :
    letI : Module (Γ(Y, j ''ᵁ W))
        (M.over (j ''ᵁ W) ⟶
          _root_.SheafOfModules.unit
            (Y.ringCatSheaf.over (j ''ᵁ W))) :=
      ModularCurves.SheafOfModules.dualSectionsModule
        Y.ringCatSheaf M (j ''ᵁ W)
    letI : Module (Γ(X, W))
        (((restrictFunctor j).obj M).over W ⟶
          _root_.SheafOfModules.unit
            (X.ringCatSheaf.over W)) :=
      ModularCurves.SheafOfModules.dualSectionsModule
        X.ringCatSheaf ((restrictFunctor j).obj M) W
    localDualRestrict M j W ((j.appIso W).inv r • alpha) =
      r • localDualRestrict M j W alpha := by
  letI : Module (Γ(Y, j ''ᵁ W))
      (M.over (j ''ᵁ W) ⟶
        _root_.SheafOfModules.unit
          (Y.ringCatSheaf.over (j ''ᵁ W))) :=
    ModularCurves.SheafOfModules.dualSectionsModule
      Y.ringCatSheaf M (j ''ᵁ W)
  letI : Module (Γ(X, W))
      (((restrictFunctor j).obj M).over W ⟶
        _root_.SheafOfModules.unit
          (X.ringCatSheaf.over W)) :=
    ModularCurves.SheafOfModules.dualSectionsModule
      X.ringCatSheaf ((restrictFunctor j).obj M) W
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let rX : Γ(Y, j ''ᵁ W) := (j.appIso W).inv r
  let yX : Γ(Y, j ''ᵁ Z.unop.left) :=
    alpha.val.app (op (imageOver j W Z.unop)) x
  let sX : Γ(Y, j ''ᵁ Z.unop.left) :=
    Y.presheaf.map (j.opensFunctor.map Z.unop.hom).op rX
  let sU : Γ(X, Z.unop.left) :=
    X.presheaf.map Z.unop.hom.op r
  change (j.appIso Z.unop.left).hom (yX * sX) =
    (j.appIso Z.unop.left).hom yX * sU
  have hs : (j.appIso Z.unop.left).hom sX = sU := by
    have hnat := CategoryTheory.congr_fun
      (j.appIso_hom_naturality Z.unop.hom.op) rX
    have hnat' :
        (j.appIso Z.unop.left).hom sX =
          X.presheaf.map Z.unop.hom.op
            ((j.appIso W).hom rX) := by
      simpa only [sX, CommRingCat.comp_apply, Quiver.Hom.unop_op] using hnat
    have hr : (j.appIso W).hom rX = r :=
      Iso.inv_hom_id_apply (j.appIso W) r
    exact hnat'.trans (congrArg
      (X.presheaf.map Z.unop.hom.op) hr)
  calc
    (j.appIso Z.unop.left).hom (yX * sX) =
        (j.appIso Z.unop.left).hom yX *
          (j.appIso Z.unop.left).hom sX :=
      (j.appIso Z.unop.left).hom.hom.map_mul yX sX
    _ = (j.appIso Z.unop.left).hom yX * sU :=
      congrArg ((j.appIso Z.unop.left).hom yX * ·) hs

noncomputable def dualRestrictPresheafHom (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j] :
    ((restrictFunctor j).obj (dualObj M)).val ⟶
      (dualObj ((restrictFunctor j).obj M)).val where
  app W :=
    ModuleCat.homMk
      (AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (localDualRestrict M j W.unop)
        (localDualRestrict_add M j W.unop)))
      (by
        intro r
        ext alpha
        exact (localDualRestrict_smul M j W.unop r alpha).symm)
  naturality := by
    intro V W f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro alpha
    change localDualRestrict M j W.unop
        (ModularCurves.SheafOfModules.dualRestrict Y.ringCatSheaf M
          (j.opensFunctor.op.map f) alpha) =
      ModularCurves.SheafOfModules.dualRestrict X.ringCatSheaf
        ((restrictFunctor j).obj M) f
          (localDualRestrict M j V.unop alpha)
    exact localDualRestrict_dualRestrict M j f alpha

noncomputable def dualRestrictHom (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j] :
    (restrictFunctor j).obj (dualObj M) ⟶
      dualObj ((restrictFunctor j).obj M) :=
  ⟨dualRestrictPresheafHom M j⟩

noncomputable def restrictIsoHomInvCongr {A B : Scheme.{u}} (e : A ≅ B) :
    restrictFunctor (𝟙 A) ≅ restrictFunctor (e.hom ≫ e.inv) :=
  restrictFunctorCongr e.hom_inv_id.symm

noncomputable def restrictIsoInvHomCongr {A B : Scheme.{u}} (e : A ≅ B) :
    restrictFunctor (e.inv ≫ e.hom) ≅ restrictFunctor (𝟙 B) :=
  restrictFunctorCongr e.inv_hom_id

noncomputable def restrictIsoEquiv {A B : Scheme.{u}} (e : A ≅ B) :
    A.Modules ≌ B.Modules := by
  let F := restrictFunctor e.inv
  let G := restrictFunctor e.hom
  let eta : 𝟭 A.Modules ≅ F ⋙ G :=
    (restrictFunctorId (X := A)).symm ≪≫
      restrictIsoHomInvCongr e ≪≫
      restrictFunctorComp e.hom e.inv
  let epsilon : G ⋙ F ≅ 𝟭 B.Modules :=
    (restrictFunctorComp e.inv e.hom).symm ≪≫
      restrictIsoInvHomCongr e ≪≫
      restrictFunctorId (X := B)
  letI : F.IsEquivalence := Functor.IsEquivalence.mk' G eta epsilon
  exact F.asEquivalence

noncomputable def localEquiv (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :
    _root_.SheafOfModules (X.ringCatSheaf.over W) ≌
      _root_.SheafOfModules (Y.ringCatSheaf.over (j ''ᵁ W)) :=
  (overEquiv W).trans
    (restrictIsoEquiv (j.isoImage W)) |>.trans
      (overEquiv (j ''ᵁ W)).symm

noncomputable def localSchemeModuleIsoOverFunctor (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :=
  (restrictFunctor (j.isoImage W).inv).mapIso
    ((overFunctorEquiv W).app ((restrictFunctor j).obj M))

noncomputable def localSchemeModuleIsoCompW (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :=
  ((restrictFunctorComp (j.isoImage W).inv W.ι).app
    ((restrictFunctor j).obj M)).symm

noncomputable def localSchemeModuleIsoCompU (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :=
  ((restrictFunctorComp ((j.isoImage W).inv ≫ W.ι) j).app M).symm

theorem localSchemeModule_morphism_eq (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens) :
    ((j.isoImage W).inv ≫ W.ι) ≫ j = (j ''ᵁ W).ι := by
  simp

noncomputable def localSchemeModuleIsoCongr (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :=
  (restrictFunctorCongr (localSchemeModule_morphism_eq j W)).app M

noncomputable def localSchemeModuleIsoOverImage (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :=
  ((overFunctorEquiv (j ''ᵁ W)).app M).symm

theorem localSchemeModuleIsoOverImage_inv_app_apply (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (V : Opposite (j ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (j ''ᵁ W)).functor.obj
      (M.over (j ''ᵁ W))).val.obj V) :
    (localSchemeModuleIsoOverImage M j W).inv.val.app V x = x := by
  exact overFunctorEquiv_hom_app_apply (j ''ᵁ W) M V x

theorem localSchemeModuleIsoOverFunctor_inv_app_apply (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (V : Opposite (j ''ᵁ W).toScheme.Opens)
    (x : ((restrictFunctor (j.isoImage W).inv).obj
      ((restrictFunctor W.ι).obj
        ((restrictFunctor j).obj M))).val.obj V) :
    (localSchemeModuleIsoOverFunctor M j W).inv.val.app V x = x := by
  dsimp only [localSchemeModuleIsoOverFunctor, Functor.mapIso_inv]
  erw [restrictFunctor_map_app_apply]
  exact overFunctorEquiv_inv_app_apply W ((restrictFunctor j).obj M)
    ((j.isoImage W).inv.opensFunctor.op.obj V) x

noncomputable def localSchemeModuleIsoStage2 (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :=
  localSchemeModuleIsoOverFunctor M j W ≪≫
    localSchemeModuleIsoCompW M j W

theorem localSchemeModuleIsoStage2_inv (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :
    (localSchemeModuleIsoStage2 M j W).inv =
      (localSchemeModuleIsoCompW M j W).inv ≫
        (localSchemeModuleIsoOverFunctor M j W).inv :=
  rfl

noncomputable def localSchemeModuleIsoStage3 (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :=
  localSchemeModuleIsoStage2 M j W ≪≫
    localSchemeModuleIsoCompU M j W

theorem localSchemeModuleIsoStage3_inv (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :
    (localSchemeModuleIsoStage3 M j W).inv =
      (localSchemeModuleIsoCompU M j W).inv ≫
        (localSchemeModuleIsoStage2 M j W).inv :=
  rfl

noncomputable def localSchemeModuleIsoStage4 (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :=
  localSchemeModuleIsoStage3 M j W ≪≫
    localSchemeModuleIsoCongr M j W

theorem localSchemeModuleIsoStage4_inv (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :
    (localSchemeModuleIsoStage4 M j W).inv =
      (localSchemeModuleIsoCongr M j W).inv ≫
        (localSchemeModuleIsoStage3 M j W).inv :=
  rfl

noncomputable def localSchemeModuleIsoStage5 (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :=
  localSchemeModuleIsoStage4 M j W ≪≫
    localSchemeModuleIsoOverImage M j W

theorem localSchemeModuleIsoStage5_inv (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :
    (localSchemeModuleIsoStage5 M j W).inv =
      (localSchemeModuleIsoOverImage M j W).inv ≫
        (localSchemeModuleIsoStage4 M j W).inv :=
  rfl

noncomputable def localSchemeModuleIso (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens) :
    (restrictFunctor (j.isoImage W).inv).obj
        ((overEquiv W).functor.obj (((restrictFunctor j).obj M).over W)) ≅
      (overEquiv (j ''ᵁ W)).functor.obj (M.over (j ''ᵁ W)) :=
  localSchemeModuleIsoStage5 M j W

theorem overEquivalence_inverse_obj_left (T : Y.Opens)
    (V : T.toScheme.Opens) :
    (T.overEquivalence.symm.functor.obj V).left = T.ι ''ᵁ V :=
  rfl

theorem localSchemeModuleOpen_eq (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (V : (j ''ᵁ W).toScheme.Opens) :
    j ''ᵁ
        (W.overEquivalence.symm.functor.obj
          ((j.isoImage W).inv.opensFunctor.obj V)).left =
      ((j ''ᵁ W).overEquivalence.symm.functor.obj V).left := by
  rw [overEquivalence_inverse_obj_left,
    overEquivalence_inverse_obj_left]
  calc
    j ''ᵁ (W.ι ''ᵁ ((j.isoImage W).inv ''ᵁ V)) =
        (((j.isoImage W).inv ≫ W.ι) ≫ j) ''ᵁ V := by
      rw [Scheme.Hom.comp_image, Scheme.Hom.comp_image]
    _ = (j ''ᵁ W).ι ''ᵁ V := by
      have hcomp : ((j.isoImage W).inv ≫ W.ι) ≫ j =
          (j ''ᵁ W).ι := by simp
      apply TopologicalSpace.Opens.ext
      change Set.image
          (fun x ↦ ((((j.isoImage W).inv ≫ W.ι) ≫ j) x)) V =
        Set.image (fun x ↦ (j ''ᵁ W).ι x) V
      rw [hcomp]

noncomputable abbrev localSchemeModuleSourceOverW (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens)
    (V : (j ''ᵁ W).toScheme.Opens) : Over W :=
  W.overEquivalence.symm.functor.obj
    ((j.isoImage W).inv.opensFunctor.obj V)

noncomputable abbrev localSchemeModuleSourceOver (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (V : (j ''ᵁ W).toScheme.Opens) : Over (j ''ᵁ W) :=
  imageOver j W (localSchemeModuleSourceOverW j W V)

abbrev localSchemeModuleTargetOver (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (V : (j ''ᵁ W).toScheme.Opens) : Over (j ''ᵁ W) :=
  (j ''ᵁ W).overEquivalence.symm.functor.obj V

noncomputable def localSchemeModuleOverIso (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens) (V : (j ''ᵁ W).toScheme.Opens) :
    localSchemeModuleSourceOver j W V ≅
      localSchemeModuleTargetOver j W V :=
  Over.isoMk (eqToIso (localSchemeModuleOpen_eq j W V)) (by subsingleton)

theorem localSchemeModuleOverIso_hom_left (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens) (V : (j ''ᵁ W).toScheme.Opens) :
    (localSchemeModuleOverIso j W V).hom.left =
      eqToHom (localSchemeModuleOpen_eq j W V) :=
  rfl

theorem localSchemeModuleOpen_eq_one (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (V : (j ''ᵁ W).toScheme.Opens) :
    (((j.isoImage W).inv ≫ W.ι) ≫ j) ''ᵁ V =
      (j ''ᵁ W).ι ''ᵁ V := by
  apply TopologicalSpace.Opens.ext
  change Set.image
      (fun x ↦ ((((j.isoImage W).inv ≫ W.ι) ≫ j) x)) V =
    Set.image (fun x ↦ (j ''ᵁ W).ι x) V
  rw [localSchemeModule_morphism_eq]

theorem localSchemeModuleOpen_eq_two (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (V : (j ''ᵁ W).toScheme.Opens) :
    j ''ᵁ (((j.isoImage W).inv ≫ W.ι) ''ᵁ V) =
      (j ''ᵁ W).ι ''ᵁ V := by
  calc
    j ''ᵁ (((j.isoImage W).inv ≫ W.ι) ''ᵁ V) =
        (((j.isoImage W).inv ≫ W.ι) ≫ j) ''ᵁ V :=
      (Scheme.Hom.comp_image
        ((j.isoImage W).inv ≫ W.ι) j V).symm
    _ = (j ''ᵁ W).ι ''ᵁ V :=
      localSchemeModuleOpen_eq_one j W V

theorem localSchemeModuleCongr_app_apply (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (V : Opposite (j ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (j ''ᵁ W)).functor.obj
      (M.over (j ''ᵁ W))).val.obj V) :
    (((restrictFunctorCongr
      (localSchemeModule_morphism_eq j W)).inv.app M).val.app V) x =
      M.presheaf.map
        (eqToHom (localSchemeModuleOpen_eq_one j W V.unop)).op x := by
  exact ConcreteCategory.congr_hom
    (restrictFunctorCongr_inv_app_app
      (U := V.unop) (localSchemeModule_morphism_eq j W) M) x

theorem localSchemeModuleCompU_component (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (V : Opposite (j ''ᵁ W).toScheme.Opens)
    (x : ((restrictFunctor
      (((j.isoImage W).inv ≫ W.ι) ≫ j)).obj M).val.obj V) :
    (((restrictFunctorComp
      ((j.isoImage W).inv ≫ W.ι) j).hom.app M).val.app V) x =
      M.presheaf.map
        (eqToHom (Scheme.Hom.comp_image
          ((j.isoImage W).inv ≫ W.ι) j V.unop).symm).op x := by
  exact ConcreteCategory.congr_hom
    (restrictFunctorComp_hom_app_app
      (U := V.unop) ((j.isoImage W).inv ≫ W.ι) j M) x

theorem localSchemeModuleCompU_app_apply (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (V : Opposite (j ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (j ''ᵁ W)).functor.obj
      (M.over (j ''ᵁ W))).val.obj V) :
    (((restrictFunctorComp
      ((j.isoImage W).inv ≫ W.ι) j).hom.app M).val.app V)
        (M.presheaf.map
          (eqToHom (localSchemeModuleOpen_eq_one j W V.unop)).op x) =
      M.presheaf.map
        (eqToHom (localSchemeModuleOpen_eq_two j W V.unop)).op x := by
  let a := M.presheaf.map
    (eqToHom (localSchemeModuleOpen_eq_one j W V.unop)).op x
  have h := localSchemeModuleCompU_component M j W V a
  refine h.trans ?_
  dsimp only [a]
  rw [← Functor.map_comp_apply, ← op_comp]
  rfl

theorem localSchemeModuleOpen_eq_three_step (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens)
    (V : (j ''ᵁ W).toScheme.Opens) :
    j ''ᵁ (W.ι ''ᵁ ((j.isoImage W).inv ''ᵁ V)) =
      j ''ᵁ (((j.isoImage W).inv ≫ W.ι) ''ᵁ V) :=
  congrArg (fun T : X.Opens ↦ j ''ᵁ T)
    (Scheme.Hom.comp_image (j.isoImage W).inv W.ι V).symm

theorem localSchemeModuleOpen_map_apply (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens)
    (V : (j ''ᵁ W).toScheme.Opens)
    (x : Γ(Y, (j ''ᵁ W).ι ''ᵁ V)) :
    Y.presheaf.map (eqToHom (localSchemeModuleOpen_eq j W V)).op x =
      Y.presheaf.map
        (eqToHom (localSchemeModuleOpen_eq_three_step j W V)).op
        (Y.presheaf.map
          (eqToHom (Scheme.Hom.comp_image
            ((j.isoImage W).inv ≫ W.ι) j V).symm).op
          (Y.presheaf.map
            (eqToHom (localSchemeModuleOpen_eq_one j W V)).op x)) := by
  rw [← Functor.map_comp_apply, ← op_comp,
    ← Functor.map_comp_apply, ← op_comp]
  rfl

theorem localSchemeModuleCompW_component (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (V : Opposite (j ''ᵁ W).toScheme.Opens)
    (x : ((restrictFunctor ((j.isoImage W).inv ≫ W.ι)).obj
      ((restrictFunctor j).obj M)).val.obj V) :
    (((restrictFunctorComp (j.isoImage W).inv W.ι).hom.app
      ((restrictFunctor j).obj M)).val.app V) x =
      ((restrictFunctor j).obj M).presheaf.map
        (eqToHom (Scheme.Hom.comp_image
          (j.isoImage W).inv W.ι V.unop).symm).op x := by
  exact ConcreteCategory.congr_hom
    (restrictFunctorComp_hom_app_app
      (U := V.unop) (j.isoImage W).inv W.ι
        ((restrictFunctor j).obj M)) x

theorem localSchemeModuleCompW_map_apply (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (V : Opposite (j ''ᵁ W).toScheme.Opens)
    (x : ((restrictFunctor ((j.isoImage W).inv ≫ W.ι)).obj
      ((restrictFunctor j).obj M)).val.obj V) :
    ((restrictFunctor j).obj M).presheaf.map
        (eqToHom (Scheme.Hom.comp_image
          (j.isoImage W).inv W.ι V.unop).symm).op x =
      M.presheaf.map
        (eqToHom (localSchemeModuleOpen_eq_three_step j W V.unop)).op x := by
  rfl

noncomputable def localSchemeModuleStageTwoValue (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (V : Opposite (j ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (j ''ᵁ W)).functor.obj
      (M.over (j ''ᵁ W))).val.obj V) :
    ((restrictFunctor ((j.isoImage W).inv ≫ W.ι)).obj
      ((restrictFunctor j).obj M)).val.obj V :=
  M.presheaf.map
    (eqToHom (localSchemeModuleOpen_eq_two j W V.unop)).op x

theorem localSchemeModuleCompW_app_apply (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (V : Opposite (j ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (j ''ᵁ W)).functor.obj
      (M.over (j ''ᵁ W))).val.obj V) :
    (((restrictFunctorComp (j.isoImage W).inv W.ι).hom.app
      ((restrictFunctor j).obj M)).val.app V)
        (localSchemeModuleStageTwoValue M j W V x) =
      (M.over (j ''ᵁ W)).val.map
        (localSchemeModuleOverIso j W V.unop).hom.op x := by
  let a := localSchemeModuleStageTwoValue M j W V x
  have hc := localSchemeModuleCompW_component M j W V a
  have hm := localSchemeModuleCompW_map_apply M j W V a
  refine hc.trans (hm.trans ?_)
  dsimp only [a, localSchemeModuleStageTwoValue]
  rw [← Functor.map_comp_apply, ← op_comp]
  rfl

noncomputable def localSchemeModuleTransition (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :=
  (restrictFunctorCongr (localSchemeModule_morphism_eq j W)).inv.app M ≫
    (restrictFunctorComp ((j.isoImage W).inv ≫ W.ι) j).hom.app M ≫
      (restrictFunctorComp (j.isoImage W).inv W.ι).hom.app
        ((restrictFunctor j).obj M)

theorem localSchemeModuleTransition_app_apply (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (V : Opposite (j ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (j ''ᵁ W)).functor.obj
      (M.over (j ''ᵁ W))).val.obj V) :
    (localSchemeModuleTransition M j W).val.app V x =
      (M.over (j ''ᵁ W)).val.map
        (localSchemeModuleOverIso j W V.unop).hom.op x := by
  dsimp only [localSchemeModuleTransition]
  erw [sheafOfModules_comp_app_apply]
  erw [sheafOfModules_comp_app_apply]
  let f1 := fun z ↦
    (((restrictFunctorComp (j.isoImage W).inv W.ι).hom.app
      ((restrictFunctor j).obj M)).val.app V)
      ((((restrictFunctorComp
        ((j.isoImage W).inv ≫ W.ι) j).hom.app M).val.app V) z)
  have h1 := localSchemeModuleCongr_app_apply M j W V x
  refine (congrArg f1 h1).trans ?_
  let f2 := fun z ↦
    (((restrictFunctorComp (j.isoImage W).inv W.ι).hom.app
      ((restrictFunctor j).obj M)).val.app V) z
  have h2 := localSchemeModuleCompU_app_apply M j W V x
  refine (congrArg f2 h2).trans ?_
  exact localSchemeModuleCompW_app_apply M j W V x

theorem localSchemeModuleTransition_raw_app_apply (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (V : Opposite (j ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (j ''ᵁ W)).functor.obj
      (M.over (j ''ᵁ W))).val.obj V) :
    (((restrictFunctorComp (j.isoImage W).inv W.ι).hom.app
      ((restrictFunctor j).obj M)).val.app V
      (((restrictFunctorComp
        ((j.isoImage W).inv ≫ W.ι) j).hom.app M).val.app V
        (((restrictFunctorCongr
          (localSchemeModule_morphism_eq j W)).inv.app M).val.app V x))) =
      (M.over (j ''ᵁ W)).val.map
        (localSchemeModuleOverIso j W V.unop).hom.op x := by
  change (localSchemeModuleTransition M j W).val.app V x = _
  exact localSchemeModuleTransition_app_apply M j W V x

theorem localSchemeUnitTransition_app_apply (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens)
    (V : (j ''ᵁ W).toScheme.Opens)
    (x : (_root_.SheafOfModules.unit
      (Y.ringCatSheaf.over (j ''ᵁ W))).val.obj
        (op (localSchemeModuleTargetOver j W V))) :
    ((j.isoImage W).inv.appIso V).hom
        ((j.appIso (localSchemeModuleSourceOverW j W V).left).hom
          ((_root_.SheafOfModules.unit
            (Y.ringCatSheaf.over (j ''ᵁ W))).val.map
              (localSchemeModuleOverIso j W V).hom.op x)) = x := by
  change ((j.isoImage W).inv.appIso V).hom
      ((j.appIso (localSchemeModuleSourceOverW j W V).left).hom
        (Y.presheaf.map
          (localSchemeModuleOverIso j W V).hom.left.op x)) = x
  have hmap := localSchemeModuleOpen_map_apply j W V x
  have hmap' :
      Y.presheaf.map (localSchemeModuleOverIso j W V).hom.left.op x =
        Y.presheaf.map
          (eqToHom (localSchemeModuleOpen_eq_three_step j W V)).op
          (Y.presheaf.map
            (eqToHom (Scheme.Hom.comp_image
              ((j.isoImage W).inv ≫ W.ι) j V).symm).op
          (Y.presheaf.map
              (eqToHom (localSchemeModuleOpen_eq_one j W V)).op x)) := by
    rw [localSchemeModuleOverIso_hom_left]
    exact hmap
  refine (congrArg (fun z ↦
    ((j.isoImage W).inv.appIso V).hom
      ((j.appIso (localSchemeModuleSourceOverW j W V).left).hom z)) hmap').trans ?_
  let x0 := Y.presheaf.map
    (eqToHom (localSchemeModuleOpen_eq_one j W V)).op x
  let x1 := Y.presheaf.map
    (eqToHom (Scheme.Hom.comp_image
      ((j.isoImage W).inv ≫ W.ι) j V).symm).op x0
  let z := Y.presheaf.map
    (eqToHom (localSchemeModuleOpen_eq_three_step j W V)).op x1
  let y1 := (j.appIso (((j.isoImage W).inv ≫ W.ι) ''ᵁ V)).hom x1
  change ((j.isoImage W).inv.appIso V).hom
      ((j.appIso (localSchemeModuleSourceOverW j W V).left).hom z) = x
  let uMap := X.presheaf.map
    (eqToHom (Scheme.Hom.comp_image
      (j.isoImage W).inv W.ι V).symm).op y1
  have hj :
      (j.appIso (localSchemeModuleSourceOverW j W V).left).hom z = uMap := by
    change (j.appIso (W.ι ''ᵁ ((j.isoImage W).inv ''ᵁ V))).hom
      (Y.presheaf.map
        (eqToHom (localSchemeModuleOpen_eq_three_step j W V)).op x1) =
      X.presheaf.map
        (eqToHom (Scheme.Hom.comp_image
          (j.isoImage W).inv W.ι V).symm).op y1
    have hnat := ConcreteCategory.congr_hom
      (j.appIso_hom_naturality
        (eqToHom (Scheme.Hom.comp_image
          (j.isoImage W).inv W.ι V).symm).op) x1
    have hm :
        j.opensFunctor.map
            ((eqToHom (Scheme.Hom.comp_image
              (j.isoImage W).inv W.ι V).symm).op.unop) =
          eqToHom (localSchemeModuleOpen_eq_three_step j W V) :=
      Subsingleton.elim _ _
    rw [hm] at hnat
    simpa only [z, y1, uMap, CategoryTheory.comp_apply] using hnat
  have hab := comp_appIso_hom_apply
    (j.isoImage W).inv W.ι V y1
  have hab' :
      (((j.isoImage W).inv ≫ W.ι).appIso V).hom y1 =
        ((j.isoImage W).inv.appIso V).hom
          ((j.appIso (localSchemeModuleSourceOverW j W V).left).hom z) := by
    refine hab.trans ?_
    rw [Scheme.Opens.ι_appIso]
    exact congrArg (fun t ↦ ((j.isoImage W).inv.appIso V).hom t) hj.symm
  have hfull := comp_appIso_hom_apply
    ((j.isoImage W).inv ≫ W.ι) j V x0
  have hfull' :
      (((((j.isoImage W).inv ≫ W.ι) ≫ j).appIso V).hom x0) =
        (((j.isoImage W).inv ≫ W.ι).appIso V).hom y1 := by
    simpa only [x1, y1] using hfull
  refine hab'.symm.trans (hfull'.symm.trans ?_)
  have hcongr := appIso_congr_apply
    (((j.isoImage W).inv ≫ W.ι) ≫ j)
    (j ''ᵁ W).ι (localSchemeModule_morphism_eq j W) V
    (localSchemeModuleOpen_eq_one j W V) x
  have hlast : ((j ''ᵁ W).ι.appIso V).hom x = x := by
    rw [Scheme.Opens.ι_appIso]
    rfl
  exact hcongr.trans hlast

noncomputable def localModuleIso (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens) :
    (localEquiv j W).functor.obj (((restrictFunctor j).obj M).over W) ≅
      M.over (j ''ᵁ W) :=
  (overEquiv (j ''ᵁ W)).fullyFaithfulFunctor.preimageIso
    ((overEquiv (j ''ᵁ W)).counitIso.app
        ((restrictFunctor (j.isoImage W).inv).obj
          ((overEquiv W).functor.obj (((restrictFunctor j).obj M).over W))) ≪≫
      localSchemeModuleIso M j W)

noncomputable def localSchemeUnitIso (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :
    (restrictFunctor (j.isoImage W).inv).obj
        ((overEquiv W).functor.obj
          (_root_.SheafOfModules.unit (X.ringCatSheaf.over W))) ≅
      (overEquiv (j ''ᵁ W)).functor.obj
        (_root_.SheafOfModules.unit
          (Y.ringCatSheaf.over (j ''ᵁ W))) :=
  restrictUnitIso (j.isoImage W).inv

theorem localSchemeUnitIso_hom_app_apply (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens)
    (V : Opposite (j ''ᵁ W).toScheme.Opens)
    (x : ((restrictFunctor (j.isoImage W).inv).obj
      ((overEquiv W).functor.obj
        (_root_.SheafOfModules.unit
          (X.ringCatSheaf.over W)))).val.obj V) :
    (localSchemeUnitIso j W).hom.val.app V x =
      ((j.isoImage W).inv.appIso V.unop).hom x := by
  rfl

noncomputable def localUnitIso (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :
    (localEquiv j W).functor.obj
        (_root_.SheafOfModules.unit (X.ringCatSheaf.over W)) ≅
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (j ''ᵁ W)) :=
  (overEquiv (j ''ᵁ W)).fullyFaithfulFunctor.preimageIso
    ((overEquiv (j ''ᵁ W)).counitIso.app
        ((restrictFunctor (j.isoImage W).inv).obj
          ((overEquiv W).functor.obj
            (_root_.SheafOfModules.unit (X.ringCatSheaf.over W)))) ≪≫
      localSchemeUnitIso j W)

noncomputable def localDualSectionsEquiv (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens) :
    ((((restrictFunctor j).obj M).over W ⟶
        _root_.SheafOfModules.unit (X.ringCatSheaf.over W))) ≃
      (M.over (j ''ᵁ W) ⟶
        _root_.SheafOfModules.unit
          (Y.ringCatSheaf.over (j ''ᵁ W))) :=
  (localEquiv j W).fullyFaithfulFunctor.homEquiv.trans
    (Iso.homCongr (localModuleIso M j W) (localUnitIso j W))

theorem localSchemeDualRestrict_restrict_app_apply (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (alpha : M.over (j ''ᵁ W) ⟶
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (j ''ᵁ W)))
    (V : Opposite (j ''ᵁ W).toScheme.Opens)
    (y : ((restrictFunctor (j.isoImage W).inv).obj
      ((overEquiv W).functor.obj
        (((restrictFunctor j).obj M).over W))).val.obj V) :
    (localSchemeUnitIso j W).hom.val.app V
        (((restrictFunctor (j.isoImage W).inv).map
          ((overEquiv W).functor.map
            (localDualRestrict M j W alpha))).val.app V y) =
      (localSchemeUnitIso j W).hom.val.app V
        (((overEquiv W).functor.map
          (localDualRestrict M j W alpha)).val.app
            ((j.isoImage W).inv.opensFunctor.op.obj V) y) := by
  exact congrArg (fun z ↦ (localSchemeUnitIso j W).hom.val.app V z)
    (restrictFunctor_map_app_apply (j.isoImage W).inv
      ((overEquiv W).functor.map (localDualRestrict M j W alpha)) V y)

theorem localSchemeDualRestrict_value (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens)
    (alpha : M.over (j ''ᵁ W) ⟶
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (j ''ᵁ W)))
    (V : Opposite (j ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (j ''ᵁ W)).functor.obj
      (M.over (j ''ᵁ W))).val.obj V) :
    (localSchemeUnitIso j W).hom.val.app V
        (((overEquiv W).functor.map
          (localDualRestrict M j W alpha)).val.app
            ((j.isoImage W).inv.opensFunctor.op.obj V)
          (((restrictFunctorComp (j.isoImage W).inv W.ι).hom.app
            ((restrictFunctor j).obj M)).val.app V
            (((restrictFunctorComp
              ((j.isoImage W).inv ≫ W.ι) j).hom.app M).val.app V
              (((restrictFunctorCongr
                (localSchemeModule_morphism_eq j W)).inv.app M).val.app V x)))) =
      ((overEquiv (j ''ᵁ W)).functor.map alpha).val.app V x := by
  let y :=
    (((restrictFunctorComp (j.isoImage W).inv W.ι).hom.app
      ((restrictFunctor j).obj M)).val.app V
      (((restrictFunctorComp
        ((j.isoImage W).inv ≫ W.ι) j).hom.app M).val.app V
        (((restrictFunctorCongr
          (localSchemeModule_morphism_eq j W)).inv.app M).val.app V x)))
  let Z := (j.isoImage W).inv.opensFunctor.op.obj V
  let k := fun z ↦ (localSchemeUnitIso j W).hom.val.app V z
  have hl := overEquiv_map_app_apply W
    (localDualRestrict M j W alpha) Z y
  have hr := overEquiv_map_app_apply (j ''ᵁ W) alpha V x
  change k (((overEquiv W).functor.map
    (localDualRestrict M j W alpha)).val.app Z y) = _
  calc
    k (((overEquiv W).functor.map
        (localDualRestrict M j W alpha)).val.app Z y) =
      k ((localDualRestrict M j W alpha).val.app
        (op (W.overEquivalence.symm.functor.obj Z.unop)) y) :=
      congrArg k hl
    _ = ((overEquiv (j ''ᵁ W)).functor.map alpha).val.app V x :=
      by
        rw [hr]
        let Q := op (W.overEquivalence.symm.functor.obj Z.unop)
        have hu := localSchemeUnitIso_hom_app_apply j W V
          ((localDualRestrict M j W alpha).val.app Q y)
        have hd := localDualRestrict_app_apply M j W alpha Q y
        refine hu.trans ?_
        refine (congrArg (fun z ↦
          ((j.isoImage W).inv.appIso V.unop).hom z) hd).trans ?_
        let i := localSchemeModuleOverIso j W V.unop
        have hy := localSchemeModuleTransition_raw_app_apply M j W V x
        have ha := PresheafOfModules.naturality_apply alpha.val i.hom.op x
        have hyAlpha := congrArg
          (fun z ↦ alpha.val.app
            (op (localSchemeModuleSourceOver j W V.unop)) z) hy
        have hAlpha := hyAlpha.trans ha
        let f := fun z ↦
          ((j.isoImage W).inv.appIso V.unop).hom
            ((j.appIso Q.unop.left).hom z)
        refine (congrArg f hAlpha).trans ?_
        exact localSchemeUnitTransition_app_apply j W V.unop _

theorem localSchemeDualRestrict_raw (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens)
    (alpha : M.over (j ''ᵁ W) ⟶
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (j ''ᵁ W)))
    (V : Opposite (j ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (j ''ᵁ W)).functor.obj
      (M.over (j ''ᵁ W))).val.obj V) :
    (localSchemeUnitIso j W).hom.val.app V
        (((restrictFunctor (j.isoImage W).inv).map
          ((overEquiv W).functor.map
            (localDualRestrict M j W alpha))).val.app V
          ((localSchemeModuleIsoOverFunctor M j W).inv.val.app V
            (((restrictFunctorComp (j.isoImage W).inv W.ι).hom.app
              ((restrictFunctor j).obj M)).val.app V
              (((restrictFunctorComp
                ((j.isoImage W).inv ≫ W.ι) j).hom.app M).val.app V
                (((restrictFunctorCongr
                  (localSchemeModule_morphism_eq j W)).inv.app M).val.app V x))))) =
      ((overEquiv (j ''ᵁ W)).functor.map alpha).val.app V x := by
  let y :=
    (((restrictFunctorComp (j.isoImage W).inv W.ι).hom.app
      ((restrictFunctor j).obj M)).val.app V
      (((restrictFunctorComp
        ((j.isoImage W).inv ≫ W.ι) j).hom.app M).val.app V
        (((restrictFunctorCongr
          (localSchemeModule_morphism_eq j W)).inv.app M).val.app V x)))
  let k := fun z ↦
    (localSchemeUnitIso j W).hom.val.app V
      (((restrictFunctor (j.isoImage W).inv).map
        ((overEquiv W).functor.map
          (localDualRestrict M j W alpha))).val.app V z)
  have h0 := localSchemeModuleIsoOverFunctor_inv_app_apply M j W V y
  calc
    _ = k y := congrArg k h0
    _ = (localSchemeUnitIso j W).hom.val.app V
        (((overEquiv W).functor.map
          (localDualRestrict M j W alpha)).val.app
            ((j.isoImage W).inv.opensFunctor.op.obj V) y) :=
      localSchemeDualRestrict_restrict_app_apply M j W alpha V y
    _ = ((overEquiv (j ''ᵁ W)).functor.map alpha).val.app V x :=
      localSchemeDualRestrict_value M j W alpha V x

theorem localSchemeDualRestrict (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens)
    (alpha : M.over (j ''ᵁ W) ⟶
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (j ''ᵁ W))) :
    (localSchemeModuleIso M j W).inv ≫
        (restrictFunctor (j.isoImage W).inv).map
          ((overEquiv W).functor.map (localDualRestrict M j W alpha)) ≫
      (localSchemeUnitIso j W).hom =
        (overEquiv (j ''ᵁ W)).functor.map alpha := by
  apply (_root_.SheafOfModules.forget
    (j ''ᵁ W).toScheme.ringCatSheaf).map_injective
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((localSchemeUnitIso j W).hom.val.app V)
      (((restrictFunctor (j.isoImage W).inv).map
        ((overEquiv W).functor.map (localDualRestrict M j W alpha))).val.app V
          ((localSchemeModuleIso M j W).inv.val.app V x)) =
    ((overEquiv (j ''ᵁ W)).functor.map alpha).val.app V x
  dsimp only [localSchemeModuleIso]
  rw [localSchemeModuleIsoStage5_inv]
  erw [sheafOfModules_comp_app_apply]
  rw [localSchemeModuleIsoStage4_inv]
  erw [sheafOfModules_comp_app_apply]
  rw [localSchemeModuleIsoStage3_inv]
  erw [sheafOfModules_comp_app_apply]
  rw [localSchemeModuleIsoStage2_inv]
  erw [sheafOfModules_comp_app_apply]
  have hx0 := localSchemeModuleIsoOverImage_inv_app_apply M j W V x
  let k0 := fun y ↦
    (localSchemeUnitIso j W).hom.val.app V
      (((restrictFunctor (j.isoImage W).inv).map
        ((overEquiv W).functor.map (localDualRestrict M j W alpha))).val.app V
          ((localSchemeModuleIsoOverFunctor M j W).inv.val.app V
            ((localSchemeModuleIsoCompW M j W).inv.val.app V
              ((localSchemeModuleIsoCompU M j W).inv.val.app V
                ((localSchemeModuleIsoCongr M j W).inv.val.app V y)))))
  change k0 ((localSchemeModuleIsoOverImage M j W).inv.val.app V x) = _
  calc
    k0 ((localSchemeModuleIsoOverImage M j W).inv.val.app V x) = k0 x :=
      congrArg k0 hx0
    _ = ((overEquiv (j ''ᵁ W)).functor.map alpha).val.app V x :=
      localSchemeDualRestrict_raw M j W alpha V x

theorem localDualSectionsEquiv_localDualRestrict (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens)
    (alpha : M.over (j ''ᵁ W) ⟶
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (j ''ᵁ W))) :
    localDualSectionsEquiv M j W (localDualRestrict M j W alpha) = alpha := by
  change (localModuleIso M j W).inv ≫
      (localEquiv j W).functor.map (localDualRestrict M j W alpha) ≫
        (localUnitIso j W).hom = alpha
  apply (overEquiv (j ''ᵁ W)).functor.map_injective
  simp only [Functor.map_comp, localModuleIso, localUnitIso,
    Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.preimageIso_inv,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.trans_inv]
  let E := overEquiv (j ''ᵁ W)
  let A := (restrictFunctor (j.isoImage W).inv).obj
    ((overEquiv W).functor.obj (((restrictFunctor j).obj M).over W))
  let O := (restrictFunctor (j.isoImage W).inv).obj
    ((overEquiv W).functor.obj
      (_root_.SheafOfModules.unit (X.ringCatSheaf.over W)))
  let q : A ⟶ O :=
    (restrictFunctor (j.isoImage W).inv).map
      ((overEquiv W).functor.map (localDualRestrict M j W alpha))
  change ((localSchemeModuleIso M j W).inv ≫ (E.counitIso.app A).inv) ≫
      E.functor.map (E.inverse.map q) ≫ (E.counitIso.app O).hom ≫
        (localSchemeUnitIso j W).hom = E.functor.map alpha
  have hmid : (E.counitIso.app A).inv ≫
      E.functor.map (E.inverse.map q) ≫ (E.counitIso.app O).hom = q := by
    simpa only [Functor.id_obj] using
      equivalence_counitInv_map_inverse_comp_counit E q
  calc
    ((localSchemeModuleIso M j W).inv ≫ (E.counitIso.app A).inv) ≫
          E.functor.map (E.inverse.map q) ≫ (E.counitIso.app O).hom ≫
            (localSchemeUnitIso j W).hom =
        (localSchemeModuleIso M j W).inv ≫
          (((E.counitIso.app A).inv ≫ E.functor.map (E.inverse.map q) ≫
            (E.counitIso.app O).hom) ≫ (localSchemeUnitIso j W).hom) := by
      simp only [Category.assoc]
    _ = (localSchemeModuleIso M j W).inv ≫
        (q ≫ (localSchemeUnitIso j W).hom) :=
      congrArg (fun k ↦ (localSchemeModuleIso M j W).inv ≫
        (k ≫ (localSchemeUnitIso j W).hom)) hmid
    _ = E.functor.map alpha := localSchemeDualRestrict M j W alpha

theorem localDualRestrict_bijective (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : X.Opens) : Function.Bijective (localDualRestrict M j W) := by
  constructor
  · intro alpha beta h
    have h' := congrArg (localDualSectionsEquiv M j W) h
    simpa only [localDualSectionsEquiv_localDualRestrict] using h'
  · intro beta
    refine ⟨localDualSectionsEquiv M j W beta, ?_⟩
    apply (localDualSectionsEquiv M j W).injective
    rw [localDualSectionsEquiv_localDualRestrict]

noncomputable def dualRestrictComponentIso (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : Opposite X.Opens) :
    ((restrictFunctor j).obj (dualObj M)).val.obj W ≅
      (dualObj ((restrictFunctor j).obj M)).val.obj W :=
  (LinearEquiv.ofBijective
    ((dualRestrictPresheafHom M j).app W).hom
    (localDualRestrict_bijective M j W.unop)).toModuleIso

theorem dualRestrictComponentIso_hom (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : Opposite X.Opens) :
    (dualRestrictComponentIso M j W).hom =
      (dualRestrictPresheafHom M j).app W := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

noncomputable def dualRestrictPresheafIso (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j] :
    ((restrictFunctor j).obj (dualObj M)).val ≅
      (dualObj ((restrictFunctor j).obj M)).val :=
  PresheafOfModules.isoMk
    (dualRestrictComponentIso M j)
    (fun {_ _} f ↦ by
      rw [dualRestrictComponentIso_hom, dualRestrictComponentIso_hom]
      exact (dualRestrictPresheafHom M j).naturality f)

/-- Restriction along an open immersion commutes with the sheaf dual. -/
noncomputable def dualRestrictIso (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j] :
    (restrictFunctor j).obj (dualObj M) ≅
      dualObj ((restrictFunctor j).obj M) :=
  (_root_.SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
    (dualRestrictPresheafIso M j)

end AlgebraicGeometry.Scheme.Modules
