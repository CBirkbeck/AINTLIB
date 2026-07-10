import ModularCurves.Picard.Dual

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u v₁ v₂ u₁ u₂

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

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

def imageOverFunctor (U : X.Opens) (W : U.toScheme.Opens) :
    Over W ⥤ Over (U.ι ''ᵁ W) :=
  Over.post U.ι.opensFunctor

abbrev imageOver (U : X.Opens) (W : U.toScheme.Opens) (Z : Over W) :
    Over (U.ι ''ᵁ W) :=
  (imageOverFunctor U W).obj Z

example (M : X.Modules) (U : X.Opens) (W : U.toScheme.Opens)
    (Z : Opposite (Over W))
    (x : (((restrictFunctor U.ι).obj M).over W).val.obj Z) :
    (M.over (U.ι ''ᵁ W)).val.obj (op (imageOver U W Z.unop)) :=
  x

noncomputable example (U : X.Opens) (W : U.toScheme.Opens) (Z : Opposite (Over W))
    (x : (_root_.SheafOfModules.unit
      (X.ringCatSheaf.over (U.ι ''ᵁ W))).val.obj
        (op (imageOver U W Z.unop))) :
    (_root_.SheafOfModules.unit (U.toScheme.ringCatSheaf.over W)).val.obj Z :=
  (U.ι.appIso Z.unop.left).hom x

noncomputable def localDualRestrictApp (M : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens)
    (alpha : M.over (U.ι ''ᵁ W) ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over (U.ι ''ᵁ W)))
    (Z : Opposite (Over W)) :
    (((restrictFunctor U.ι).obj M).over W).val.presheaf.obj Z ⟶
      (_root_.SheafOfModules.unit
        (U.toScheme.ringCatSheaf.over W)).val.presheaf.obj Z :=
  AddCommGrpCat.ofHom
    { toFun := fun x ↦ (U.ι.appIso Z.unop.left).hom
        (alpha.val.app (op (imageOver U W Z.unop)) x)
      map_zero' := by
        calc
          (U.ι.appIso Z.unop.left).hom
              (alpha.val.app (op (imageOver U W Z.unop)) 0) =
            (U.ι.appIso Z.unop.left).hom 0 :=
              congrArg _ (alpha.val.app
                (op (imageOver U W Z.unop))).hom.map_zero
          _ = 0 := (U.ι.appIso Z.unop.left).hom.hom.map_zero
      map_add' := by
        intro x y
        calc
          (U.ι.appIso Z.unop.left).hom
              (alpha.val.app (op (imageOver U W Z.unop)) (x + y)) =
            (U.ι.appIso Z.unop.left).hom
              (alpha.val.app (op (imageOver U W Z.unop)) x +
                alpha.val.app (op (imageOver U W Z.unop)) y) :=
              congrArg _ ((alpha.val.app
                (op (imageOver U W Z.unop))).hom.map_add x y)
          _ = (U.ι.appIso Z.unop.left).hom
                (alpha.val.app (op (imageOver U W Z.unop)) x) +
              (U.ι.appIso Z.unop.left).hom
                (alpha.val.app (op (imageOver U W Z.unop)) y) :=
            (U.ι.appIso Z.unop.left).hom.hom.map_add _ _ }

theorem localDualRestrictApp_naturality (M : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens)
    (alpha : M.over (U.ι ''ᵁ W) ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over (U.ι ''ᵁ W)))
    {Z Z' : Opposite (Over W)} (f : Z ⟶ Z') :
    (((restrictFunctor U.ι).obj M).over W).val.presheaf.map f ≫
        localDualRestrictApp M U W alpha Z' =
      localDualRestrictApp M U W alpha Z ≫
        (_root_.SheafOfModules.unit
          (U.toScheme.ringCatSheaf.over W)).val.presheaf.map f := by
  ext x
  change (U.ι.appIso Z'.unop.left).hom
      (alpha.val.app (op (imageOver U W Z'.unop))
        (((M.restrict U.ι).over W).val.map f x)) =
    ((_root_.SheafOfModules.unit
      (U.toScheme.ringCatSheaf.over W)).val.map f)
      ((U.ι.appIso Z.unop.left).hom
        (alpha.val.app (op (imageOver U W Z.unop)) x))
  have hsource :
      ((M.restrict U.ι).over W).val.map f x =
        (M.over (U.ι ''ᵁ W)).val.map
          ((imageOverFunctor U W).op.map f) x := rfl
  have halpha := CategoryTheory.congr_fun
    (alpha.val.naturality ((imageOverFunctor U W).op.map f)) x
  have happ := CategoryTheory.congr_fun
    (U.ι.appIso_hom_naturality f.unop.left.op)
    (alpha.val.app (op (imageOver U W Z.unop)) x)
  calc
    (U.ι.appIso Z'.unop.left).hom
        (alpha.val.app (op (imageOver U W Z'.unop))
          (((M.restrict U.ι).over W).val.map f x)) =
      (U.ι.appIso Z'.unop.left).hom
        (alpha.val.app (op (imageOver U W Z'.unop))
          ((M.over (U.ι ''ᵁ W)).val.map
            ((imageOverFunctor U W).op.map f) x)) :=
      congrArg (fun y ↦ (U.ι.appIso Z'.unop.left).hom
        (alpha.val.app (op (imageOver U W Z'.unop)) y)) hsource
    _ = (U.ι.appIso Z'.unop.left).hom
        ((_root_.SheafOfModules.unit
          (X.ringCatSheaf.over (U.ι ''ᵁ W))).val.map
            ((imageOverFunctor U W).op.map f)
              (alpha.val.app (op (imageOver U W Z.unop)) x)) := congrArg _ halpha
    _ = ((_root_.SheafOfModules.unit
        (U.toScheme.ringCatSheaf.over W)).val.map f)
          ((U.ι.appIso Z.unop.left).hom
            (alpha.val.app (op (imageOver U W Z.unop)) x)) := happ

theorem localDualRestrictApp_smul (M : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens)
    (alpha : M.over (U.ι ''ᵁ W) ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over (U.ι ''ᵁ W)))
    (Z : Opposite (Over W))
    (r : (U.toScheme.ringCatSheaf.over W).obj.obj Z)
    (x : (((restrictFunctor U.ι).obj M).over W).val.obj Z) :
    localDualRestrictApp M U W alpha Z (r • x) =
      r • localDualRestrictApp M U W alpha Z x := by
  let rU : Γ(U.toScheme, Z.unop.left) := r
  let rX : (X.ringCatSheaf.over (U.ι ''ᵁ W)).obj.obj
      (op (imageOver U W Z.unop)) :=
    (U.ι.appIso Z.unop.left).inv rU
  let xX : (M.over (U.ι ''ᵁ W)).val.obj
      (op (imageOver U W Z.unop)) := x
  let yX : (X.ringCatSheaf.over (U.ι ''ᵁ W)).obj.obj
      (op (imageOver U W Z.unop)) :=
    alpha.val.app (op (imageOver U W Z.unop)) xX
  change (U.ι.appIso Z.unop.left).hom
      (alpha.val.app (op (imageOver U W Z.unop)) (rX • xX)) =
    rU • (U.ι.appIso Z.unop.left).hom
      yX
  calc
    (U.ι.appIso Z.unop.left).hom
        (alpha.val.app (op (imageOver U W Z.unop)) (rX • xX)) =
      (U.ι.appIso Z.unop.left).hom
        (rX • yX) :=
      congrArg _ ((alpha.val.app
        (op (imageOver U W Z.unop))).hom.map_smul rX xX)
    _ = rU • (U.ι.appIso Z.unop.left).hom yX := by
      change (U.ι.appIso Z.unop.left).hom
          (rX * yX) =
        rU * (U.ι.appIso Z.unop.left).hom yX
      calc
        (U.ι.appIso Z.unop.left).hom (rX * yX) =
            (U.ι.appIso Z.unop.left).hom rX *
              (U.ι.appIso Z.unop.left).hom yX :=
          (U.ι.appIso Z.unop.left).hom.hom.map_mul rX yX
        _ = rU * (U.ι.appIso Z.unop.left).hom yX :=
          congrArg (fun a ↦ a * (U.ι.appIso Z.unop.left).hom yX)
            (Iso.inv_hom_id_apply (U.ι.appIso Z.unop.left) rU)

noncomputable def localDualRestrict (M : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens)
    (alpha : M.over (U.ι ''ᵁ W) ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over (U.ι ''ᵁ W))) :
    ((restrictFunctor U.ι).obj M).over W ⟶
      _root_.SheafOfModules.unit (U.toScheme.ringCatSheaf.over W) where
  val := PresheafOfModules.homMk
    { app := localDualRestrictApp M U W alpha
      naturality := by
        intro Z Z' f
        exact localDualRestrictApp_naturality M U W alpha f }
    (localDualRestrictApp_smul M U W alpha)

theorem localDualRestrict_app_apply (M : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens)
    (alpha : M.over (U.ι ''ᵁ W) ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over (U.ι ''ᵁ W)))
    (Z : Opposite (Over W))
    (x : (((restrictFunctor U.ι).obj M).over W).val.obj Z) :
    (localDualRestrict M U W alpha).val.app Z x =
      (U.ι.appIso Z.unop.left).hom
        (alpha.val.app (op (imageOver U W Z.unop)) x) :=
  rfl

theorem localDualRestrict_dualRestrict (M : X.Modules) (U : X.Opens)
    {V W : Opposite U.toScheme.Opens} (f : V ⟶ W)
    (alpha : M.over (U.ι ''ᵁ V.unop) ⟶
      _root_.SheafOfModules.unit
        (X.ringCatSheaf.over (U.ι ''ᵁ V.unop))) :
    localDualRestrict M U W.unop
        (ModularCurves.SheafOfModules.dualRestrict X.ringCatSheaf M
          (U.ι.opensFunctor.op.map f) alpha) =
      ModularCurves.SheafOfModules.dualRestrict U.toScheme.ringCatSheaf
        ((restrictFunctor U.ι).obj M) f
          (localDualRestrict M U V.unop alpha) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem localDualRestrict_add (M : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens)
    (alpha beta : M.over (U.ι ''ᵁ W) ⟶
      _root_.SheafOfModules.unit
        (X.ringCatSheaf.over (U.ι ''ᵁ W))) :
    localDualRestrict M U W (alpha + beta) =
      localDualRestrict M U W alpha + localDualRestrict M U W beta := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (U.ι.appIso Z.unop.left).hom
      ((alpha + beta).val.app (op (imageOver U W Z.unop)) x) =
    (U.ι.appIso Z.unop.left).hom
        (alpha.val.app (op (imageOver U W Z.unop)) x) +
      (U.ι.appIso Z.unop.left).hom
        (beta.val.app (op (imageOver U W Z.unop)) x)
  calc
    (U.ι.appIso Z.unop.left).hom
        ((alpha + beta).val.app (op (imageOver U W Z.unop)) x) =
      (U.ι.appIso Z.unop.left).hom
        (alpha.val.app (op (imageOver U W Z.unop)) x +
          beta.val.app (op (imageOver U W Z.unop)) x) := rfl
    _ = (U.ι.appIso Z.unop.left).hom
          (alpha.val.app (op (imageOver U W Z.unop)) x) +
        (U.ι.appIso Z.unop.left).hom
          (beta.val.app (op (imageOver U W Z.unop)) x) :=
      (U.ι.appIso Z.unop.left).hom.hom.map_add _ _

theorem localDualRestrict_smul (M : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens) (r : Γ(U.toScheme, W))
    (alpha : M.over (U.ι ''ᵁ W) ⟶
      _root_.SheafOfModules.unit
        (X.ringCatSheaf.over (U.ι ''ᵁ W))) :
    letI : Module (Γ(X, U.ι ''ᵁ W))
        (M.over (U.ι ''ᵁ W) ⟶
          _root_.SheafOfModules.unit
            (X.ringCatSheaf.over (U.ι ''ᵁ W))) :=
      ModularCurves.SheafOfModules.dualSectionsModule
        X.ringCatSheaf M (U.ι ''ᵁ W)
    letI : Module (Γ(U.toScheme, W))
        (((restrictFunctor U.ι).obj M).over W ⟶
          _root_.SheafOfModules.unit
            (U.toScheme.ringCatSheaf.over W)) :=
      ModularCurves.SheafOfModules.dualSectionsModule
        U.toScheme.ringCatSheaf ((restrictFunctor U.ι).obj M) W
    localDualRestrict M U W ((U.ι.appIso W).inv r • alpha) =
      r • localDualRestrict M U W alpha := by
  letI : Module (Γ(X, U.ι ''ᵁ W))
      (M.over (U.ι ''ᵁ W) ⟶
        _root_.SheafOfModules.unit
          (X.ringCatSheaf.over (U.ι ''ᵁ W))) :=
    ModularCurves.SheafOfModules.dualSectionsModule
      X.ringCatSheaf M (U.ι ''ᵁ W)
  letI : Module (Γ(U.toScheme, W))
      (((restrictFunctor U.ι).obj M).over W ⟶
        _root_.SheafOfModules.unit
          (U.toScheme.ringCatSheaf.over W)) :=
    ModularCurves.SheafOfModules.dualSectionsModule
      U.toScheme.ringCatSheaf ((restrictFunctor U.ι).obj M) W
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let rX : Γ(X, U.ι ''ᵁ W) := (U.ι.appIso W).inv r
  let yX : Γ(X, U.ι ''ᵁ Z.unop.left) :=
    alpha.val.app (op (imageOver U W Z.unop)) x
  let sX : Γ(X, U.ι ''ᵁ Z.unop.left) :=
    X.presheaf.map (U.ι.opensFunctor.map Z.unop.hom).op rX
  let sU : Γ(U.toScheme, Z.unop.left) :=
    U.toScheme.presheaf.map Z.unop.hom.op r
  change (U.ι.appIso Z.unop.left).hom (yX * sX) =
    (U.ι.appIso Z.unop.left).hom yX * sU
  have hs : (U.ι.appIso Z.unop.left).hom sX = sU := by
    have hnat := CategoryTheory.congr_fun
      (U.ι.appIso_hom_naturality Z.unop.hom.op) rX
    have hnat' :
        (U.ι.appIso Z.unop.left).hom sX =
          U.toScheme.presheaf.map Z.unop.hom.op
            ((U.ι.appIso W).hom rX) := by
      simpa only [sX, CommRingCat.comp_apply, Quiver.Hom.unop_op] using hnat
    have hr : (U.ι.appIso W).hom rX = r :=
      Iso.inv_hom_id_apply (U.ι.appIso W) r
    exact hnat'.trans (congrArg
      (U.toScheme.presheaf.map Z.unop.hom.op) hr)
  calc
    (U.ι.appIso Z.unop.left).hom (yX * sX) =
        (U.ι.appIso Z.unop.left).hom yX *
          (U.ι.appIso Z.unop.left).hom sX :=
      (U.ι.appIso Z.unop.left).hom.hom.map_mul yX sX
    _ = (U.ι.appIso Z.unop.left).hom yX * sU :=
      congrArg ((U.ι.appIso Z.unop.left).hom yX * ·) hs

noncomputable def dualRestrictPresheafHom (M : X.Modules) (U : X.Opens) :
    ((restrictFunctor U.ι).obj (dualObj M)).val ⟶
      (dualObj ((restrictFunctor U.ι).obj M)).val where
  app W :=
    ModuleCat.homMk
      (AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (localDualRestrict M U W.unop)
        (localDualRestrict_add M U W.unop)))
      (by
        intro r
        ext alpha
        exact (localDualRestrict_smul M U W.unop r alpha).symm)
  naturality := by
    intro V W f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro alpha
    change localDualRestrict M U W.unop
        (ModularCurves.SheafOfModules.dualRestrict X.ringCatSheaf M
          (U.ι.opensFunctor.op.map f) alpha) =
      ModularCurves.SheafOfModules.dualRestrict U.toScheme.ringCatSheaf
        ((restrictFunctor U.ι).obj M) f
          (localDualRestrict M U V.unop alpha)
    exact localDualRestrict_dualRestrict M U f alpha

noncomputable def dualRestrictHom (M : X.Modules) (U : X.Opens) :
    (restrictFunctor U.ι).obj (dualObj M) ⟶
      dualObj ((restrictFunctor U.ι).obj M) :=
  ⟨dualRestrictPresheafHom M U⟩

noncomputable def restrictIsoHomInvCongr {X Y : Scheme.{u}} (e : X ≅ Y) :
    restrictFunctor (𝟙 X) ≅ restrictFunctor (e.hom ≫ e.inv) :=
  restrictFunctorCongr e.hom_inv_id.symm

noncomputable def restrictIsoInvHomCongr {X Y : Scheme.{u}} (e : X ≅ Y) :
    restrictFunctor (e.inv ≫ e.hom) ≅ restrictFunctor (𝟙 Y) :=
  restrictFunctorCongr e.inv_hom_id

noncomputable def restrictIsoEquiv {X Y : Scheme.{u}} (e : X ≅ Y) :
    X.Modules ≌ Y.Modules := by
  let F := restrictFunctor e.inv
  let G := restrictFunctor e.hom
  let eta : 𝟭 X.Modules ≅ F ⋙ G :=
    (restrictFunctorId (X := X)).symm ≪≫
      restrictIsoHomInvCongr e ≪≫
      restrictFunctorComp e.hom e.inv
  let epsilon : G ⋙ F ≅ 𝟭 Y.Modules :=
    (restrictFunctorComp e.inv e.hom).symm ≪≫
      restrictIsoInvHomCongr e ≪≫
      restrictFunctorId (X := Y)
  letI : F.IsEquivalence := Functor.IsEquivalence.mk' G eta epsilon
  exact F.asEquivalence

noncomputable def localEquiv (U : X.Opens) (W : U.toScheme.Opens) :
    _root_.SheafOfModules (U.toScheme.ringCatSheaf.over W) ≌
      _root_.SheafOfModules (X.ringCatSheaf.over (U.ι ''ᵁ W)) :=
  (overEquiv W).trans
    (restrictIsoEquiv (U.ι.isoImage W)) |>.trans
      (overEquiv (U.ι ''ᵁ W)).symm

noncomputable def localSchemeModuleIsoOverFunctor (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens) :=
  (restrictFunctor (U.ι.isoImage W).inv).mapIso
    ((overFunctorEquiv W).app ((restrictFunctor U.ι).obj M))

noncomputable def localSchemeModuleIsoCompW (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens) :=
  ((restrictFunctorComp (U.ι.isoImage W).inv W.ι).app
    ((restrictFunctor U.ι).obj M)).symm

noncomputable def localSchemeModuleIsoCompU (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens) :=
  ((restrictFunctorComp ((U.ι.isoImage W).inv ≫ W.ι) U.ι).app M).symm

theorem localSchemeModule_morphism_eq (U : X.Opens)
    (W : U.toScheme.Opens) :
    ((U.ι.isoImage W).inv ≫ W.ι) ≫ U.ι = (U.ι ''ᵁ W).ι := by
  simp

noncomputable def localSchemeModuleIsoCongr (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens) :=
  (restrictFunctorCongr (localSchemeModule_morphism_eq U W)).app M

noncomputable def localSchemeModuleIsoOverImage (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens) :=
  ((overFunctorEquiv (U.ι ''ᵁ W)).app M).symm

theorem localSchemeModuleIsoOverImage_inv_app_apply (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens)
    (V : Opposite (U.ι ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (U.ι ''ᵁ W)).functor.obj
      (M.over (U.ι ''ᵁ W))).val.obj V) :
    (localSchemeModuleIsoOverImage M U W).inv.val.app V x = x := by
  exact overFunctorEquiv_hom_app_apply (U.ι ''ᵁ W) M V x

theorem localSchemeModuleIsoOverFunctor_inv_app_apply (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens)
    (V : Opposite (U.ι ''ᵁ W).toScheme.Opens)
    (x : ((restrictFunctor (U.ι.isoImage W).inv).obj
      ((restrictFunctor W.ι).obj
        ((restrictFunctor U.ι).obj M))).val.obj V) :
    (localSchemeModuleIsoOverFunctor M U W).inv.val.app V x = x := by
  dsimp only [localSchemeModuleIsoOverFunctor, Functor.mapIso_inv]
  erw [restrictFunctor_map_app_apply]
  exact overFunctorEquiv_inv_app_apply W ((restrictFunctor U.ι).obj M)
    ((U.ι.isoImage W).inv.opensFunctor.op.obj V) x

noncomputable def localSchemeModuleIsoStage2 (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens) :=
  localSchemeModuleIsoOverFunctor M U W ≪≫
    localSchemeModuleIsoCompW M U W

theorem localSchemeModuleIsoStage2_inv (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens) :
    (localSchemeModuleIsoStage2 M U W).inv =
      (localSchemeModuleIsoCompW M U W).inv ≫
        (localSchemeModuleIsoOverFunctor M U W).inv :=
  rfl

noncomputable def localSchemeModuleIsoStage3 (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens) :=
  localSchemeModuleIsoStage2 M U W ≪≫
    localSchemeModuleIsoCompU M U W

theorem localSchemeModuleIsoStage3_inv (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens) :
    (localSchemeModuleIsoStage3 M U W).inv =
      (localSchemeModuleIsoCompU M U W).inv ≫
        (localSchemeModuleIsoStage2 M U W).inv :=
  rfl

noncomputable def localSchemeModuleIsoStage4 (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens) :=
  localSchemeModuleIsoStage3 M U W ≪≫
    localSchemeModuleIsoCongr M U W

theorem localSchemeModuleIsoStage4_inv (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens) :
    (localSchemeModuleIsoStage4 M U W).inv =
      (localSchemeModuleIsoCongr M U W).inv ≫
        (localSchemeModuleIsoStage3 M U W).inv :=
  rfl

noncomputable def localSchemeModuleIsoStage5 (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens) :=
  localSchemeModuleIsoStage4 M U W ≪≫
    localSchemeModuleIsoOverImage M U W

theorem localSchemeModuleIsoStage5_inv (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens) :
    (localSchemeModuleIsoStage5 M U W).inv =
      (localSchemeModuleIsoOverImage M U W).inv ≫
        (localSchemeModuleIsoStage4 M U W).inv :=
  rfl

noncomputable def localSchemeModuleIso (M : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens) :
    (restrictFunctor (U.ι.isoImage W).inv).obj
        ((overEquiv W).functor.obj (((restrictFunctor U.ι).obj M).over W)) ≅
      (overEquiv (U.ι ''ᵁ W)).functor.obj (M.over (U.ι ''ᵁ W)) :=
  localSchemeModuleIsoStage5 M U W

theorem overEquivalence_inverse_obj_left (T : X.Opens)
    (V : T.toScheme.Opens) :
    (T.overEquivalence.symm.functor.obj V).left = T.ι ''ᵁ V :=
  rfl

theorem localSchemeModuleOpen_eq (U : X.Opens) (W : U.toScheme.Opens)
    (V : (U.ι ''ᵁ W).toScheme.Opens) :
    U.ι ''ᵁ
        (W.overEquivalence.symm.functor.obj
          ((U.ι.isoImage W).inv.opensFunctor.obj V)).left =
      ((U.ι ''ᵁ W).overEquivalence.symm.functor.obj V).left := by
  rw [overEquivalence_inverse_obj_left,
    overEquivalence_inverse_obj_left]
  calc
    U.ι ''ᵁ (W.ι ''ᵁ ((U.ι.isoImage W).inv ''ᵁ V)) =
        (((U.ι.isoImage W).inv ≫ W.ι) ≫ U.ι) ''ᵁ V := by
      rw [Scheme.Hom.comp_image, Scheme.Hom.comp_image]
    _ = (U.ι ''ᵁ W).ι ''ᵁ V := by
      have hcomp : ((U.ι.isoImage W).inv ≫ W.ι) ≫ U.ι =
          (U.ι ''ᵁ W).ι := by simp
      apply TopologicalSpace.Opens.ext
      change Set.image
          (fun x ↦ ((((U.ι.isoImage W).inv ≫ W.ι) ≫ U.ι) x)) V =
        Set.image (fun x ↦ (U.ι ''ᵁ W).ι x) V
      rw [hcomp]

noncomputable abbrev localSchemeModuleSourceOverW (U : X.Opens)
    (W : U.toScheme.Opens)
    (V : (U.ι ''ᵁ W).toScheme.Opens) : Over W :=
  W.overEquivalence.symm.functor.obj
    ((U.ι.isoImage W).inv.opensFunctor.obj V)

noncomputable abbrev localSchemeModuleSourceOver (U : X.Opens) (W : U.toScheme.Opens)
    (V : (U.ι ''ᵁ W).toScheme.Opens) : Over (U.ι ''ᵁ W) :=
  imageOver U W (localSchemeModuleSourceOverW U W V)

abbrev localSchemeModuleTargetOver (U : X.Opens) (W : U.toScheme.Opens)
    (V : (U.ι ''ᵁ W).toScheme.Opens) : Over (U.ι ''ᵁ W) :=
  (U.ι ''ᵁ W).overEquivalence.symm.functor.obj V

noncomputable def localSchemeModuleOverIso (U : X.Opens)
    (W : U.toScheme.Opens) (V : (U.ι ''ᵁ W).toScheme.Opens) :
    localSchemeModuleSourceOver U W V ≅
      localSchemeModuleTargetOver U W V :=
  Over.isoMk (eqToIso (localSchemeModuleOpen_eq U W V)) (by subsingleton)

theorem localSchemeModuleOverIso_hom_left (U : X.Opens)
    (W : U.toScheme.Opens) (V : (U.ι ''ᵁ W).toScheme.Opens) :
    (localSchemeModuleOverIso U W V).hom.left =
      eqToHom (localSchemeModuleOpen_eq U W V) :=
  rfl

theorem localSchemeModuleOpen_eq_one (U : X.Opens) (W : U.toScheme.Opens)
    (V : (U.ι ''ᵁ W).toScheme.Opens) :
    (((U.ι.isoImage W).inv ≫ W.ι) ≫ U.ι) ''ᵁ V =
      (U.ι ''ᵁ W).ι ''ᵁ V := by
  apply TopologicalSpace.Opens.ext
  change Set.image
      (fun x ↦ ((((U.ι.isoImage W).inv ≫ W.ι) ≫ U.ι) x)) V =
    Set.image (fun x ↦ (U.ι ''ᵁ W).ι x) V
  rw [localSchemeModule_morphism_eq]

theorem localSchemeModuleOpen_eq_two (U : X.Opens) (W : U.toScheme.Opens)
    (V : (U.ι ''ᵁ W).toScheme.Opens) :
    U.ι ''ᵁ (((U.ι.isoImage W).inv ≫ W.ι) ''ᵁ V) =
      (U.ι ''ᵁ W).ι ''ᵁ V := by
  calc
    U.ι ''ᵁ (((U.ι.isoImage W).inv ≫ W.ι) ''ᵁ V) =
        (((U.ι.isoImage W).inv ≫ W.ι) ≫ U.ι) ''ᵁ V :=
      (Scheme.Hom.comp_image
        ((U.ι.isoImage W).inv ≫ W.ι) U.ι V).symm
    _ = (U.ι ''ᵁ W).ι ''ᵁ V :=
      localSchemeModuleOpen_eq_one U W V

theorem localSchemeModuleCongr_app_apply (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens)
    (V : Opposite (U.ι ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (U.ι ''ᵁ W)).functor.obj
      (M.over (U.ι ''ᵁ W))).val.obj V) :
    (((restrictFunctorCongr
      (localSchemeModule_morphism_eq U W)).inv.app M).val.app V) x =
      M.presheaf.map
        (eqToHom (localSchemeModuleOpen_eq_one U W V.unop)).op x := by
  exact ConcreteCategory.congr_hom
    (restrictFunctorCongr_inv_app_app
      (U := V.unop) (localSchemeModule_morphism_eq U W) M) x

theorem localSchemeModuleCompU_component (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens)
    (V : Opposite (U.ι ''ᵁ W).toScheme.Opens)
    (x : ((restrictFunctor
      (((U.ι.isoImage W).inv ≫ W.ι) ≫ U.ι)).obj M).val.obj V) :
    (((restrictFunctorComp
      ((U.ι.isoImage W).inv ≫ W.ι) U.ι).hom.app M).val.app V) x =
      M.presheaf.map
        (eqToHom (Scheme.Hom.comp_image
          ((U.ι.isoImage W).inv ≫ W.ι) U.ι V.unop).symm).op x := by
  exact ConcreteCategory.congr_hom
    (restrictFunctorComp_hom_app_app
      (U := V.unop) ((U.ι.isoImage W).inv ≫ W.ι) U.ι M) x

theorem localSchemeModuleCompU_app_apply (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens)
    (V : Opposite (U.ι ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (U.ι ''ᵁ W)).functor.obj
      (M.over (U.ι ''ᵁ W))).val.obj V) :
    (((restrictFunctorComp
      ((U.ι.isoImage W).inv ≫ W.ι) U.ι).hom.app M).val.app V)
        (M.presheaf.map
          (eqToHom (localSchemeModuleOpen_eq_one U W V.unop)).op x) =
      M.presheaf.map
        (eqToHom (localSchemeModuleOpen_eq_two U W V.unop)).op x := by
  let a := M.presheaf.map
    (eqToHom (localSchemeModuleOpen_eq_one U W V.unop)).op x
  have h := localSchemeModuleCompU_component M U W V a
  refine h.trans ?_
  dsimp only [a]
  rw [← Functor.map_comp_apply, ← op_comp]
  rfl

theorem localSchemeModuleOpen_eq_three_step (U : X.Opens)
    (W : U.toScheme.Opens)
    (V : (U.ι ''ᵁ W).toScheme.Opens) :
    U.ι ''ᵁ (W.ι ''ᵁ ((U.ι.isoImage W).inv ''ᵁ V)) =
      U.ι ''ᵁ (((U.ι.isoImage W).inv ≫ W.ι) ''ᵁ V) :=
  congrArg (fun T : U.toScheme.Opens ↦ U.ι ''ᵁ T)
    (Scheme.Hom.comp_image (U.ι.isoImage W).inv W.ι V).symm

theorem localSchemeModuleOpen_map_apply (U : X.Opens)
    (W : U.toScheme.Opens)
    (V : (U.ι ''ᵁ W).toScheme.Opens)
    (x : Γ(X, (U.ι ''ᵁ W).ι ''ᵁ V)) :
    X.presheaf.map (eqToHom (localSchemeModuleOpen_eq U W V)).op x =
      X.presheaf.map
        (eqToHom (localSchemeModuleOpen_eq_three_step U W V)).op
        (X.presheaf.map
          (eqToHom (Scheme.Hom.comp_image
            ((U.ι.isoImage W).inv ≫ W.ι) U.ι V).symm).op
          (X.presheaf.map
            (eqToHom (localSchemeModuleOpen_eq_one U W V)).op x)) := by
  rw [← Functor.map_comp_apply, ← op_comp,
    ← Functor.map_comp_apply, ← op_comp]
  rfl

theorem localSchemeModuleCompW_component (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens)
    (V : Opposite (U.ι ''ᵁ W).toScheme.Opens)
    (x : ((restrictFunctor ((U.ι.isoImage W).inv ≫ W.ι)).obj
      ((restrictFunctor U.ι).obj M)).val.obj V) :
    (((restrictFunctorComp (U.ι.isoImage W).inv W.ι).hom.app
      ((restrictFunctor U.ι).obj M)).val.app V) x =
      ((restrictFunctor U.ι).obj M).presheaf.map
        (eqToHom (Scheme.Hom.comp_image
          (U.ι.isoImage W).inv W.ι V.unop).symm).op x := by
  exact ConcreteCategory.congr_hom
    (restrictFunctorComp_hom_app_app
      (U := V.unop) (U.ι.isoImage W).inv W.ι
        ((restrictFunctor U.ι).obj M)) x

theorem localSchemeModuleCompW_map_apply (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens)
    (V : Opposite (U.ι ''ᵁ W).toScheme.Opens)
    (x : ((restrictFunctor ((U.ι.isoImage W).inv ≫ W.ι)).obj
      ((restrictFunctor U.ι).obj M)).val.obj V) :
    ((restrictFunctor U.ι).obj M).presheaf.map
        (eqToHom (Scheme.Hom.comp_image
          (U.ι.isoImage W).inv W.ι V.unop).symm).op x =
      M.presheaf.map
        (eqToHom (localSchemeModuleOpen_eq_three_step U W V.unop)).op x := by
  rfl

noncomputable def localSchemeModuleStageTwoValue (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens)
    (V : Opposite (U.ι ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (U.ι ''ᵁ W)).functor.obj
      (M.over (U.ι ''ᵁ W))).val.obj V) :
    ((restrictFunctor ((U.ι.isoImage W).inv ≫ W.ι)).obj
      ((restrictFunctor U.ι).obj M)).val.obj V :=
  M.presheaf.map
    (eqToHom (localSchemeModuleOpen_eq_two U W V.unop)).op x

theorem localSchemeModuleCompW_app_apply (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens)
    (V : Opposite (U.ι ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (U.ι ''ᵁ W)).functor.obj
      (M.over (U.ι ''ᵁ W))).val.obj V) :
    (((restrictFunctorComp (U.ι.isoImage W).inv W.ι).hom.app
      ((restrictFunctor U.ι).obj M)).val.app V)
        (localSchemeModuleStageTwoValue M U W V x) =
      (M.over (U.ι ''ᵁ W)).val.map
        (localSchemeModuleOverIso U W V.unop).hom.op x := by
  let a := localSchemeModuleStageTwoValue M U W V x
  have hc := localSchemeModuleCompW_component M U W V a
  have hm := localSchemeModuleCompW_map_apply M U W V a
  refine hc.trans (hm.trans ?_)
  dsimp only [a, localSchemeModuleStageTwoValue]
  rw [← Functor.map_comp_apply, ← op_comp]
  rfl

noncomputable def localSchemeModuleTransition (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens) :=
  (restrictFunctorCongr (localSchemeModule_morphism_eq U W)).inv.app M ≫
    (restrictFunctorComp ((U.ι.isoImage W).inv ≫ W.ι) U.ι).hom.app M ≫
      (restrictFunctorComp (U.ι.isoImage W).inv W.ι).hom.app
        ((restrictFunctor U.ι).obj M)

theorem localSchemeModuleTransition_app_apply (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens)
    (V : Opposite (U.ι ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (U.ι ''ᵁ W)).functor.obj
      (M.over (U.ι ''ᵁ W))).val.obj V) :
    (localSchemeModuleTransition M U W).val.app V x =
      (M.over (U.ι ''ᵁ W)).val.map
        (localSchemeModuleOverIso U W V.unop).hom.op x := by
  dsimp only [localSchemeModuleTransition]
  erw [sheafOfModules_comp_app_apply]
  erw [sheafOfModules_comp_app_apply]
  let f1 := fun z ↦
    (((restrictFunctorComp (U.ι.isoImage W).inv W.ι).hom.app
      ((restrictFunctor U.ι).obj M)).val.app V)
      ((((restrictFunctorComp
        ((U.ι.isoImage W).inv ≫ W.ι) U.ι).hom.app M).val.app V) z)
  have h1 := localSchemeModuleCongr_app_apply M U W V x
  refine (congrArg f1 h1).trans ?_
  let f2 := fun z ↦
    (((restrictFunctorComp (U.ι.isoImage W).inv W.ι).hom.app
      ((restrictFunctor U.ι).obj M)).val.app V) z
  have h2 := localSchemeModuleCompU_app_apply M U W V x
  refine (congrArg f2 h2).trans ?_
  exact localSchemeModuleCompW_app_apply M U W V x

theorem localSchemeModuleTransition_raw_app_apply (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens)
    (V : Opposite (U.ι ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (U.ι ''ᵁ W)).functor.obj
      (M.over (U.ι ''ᵁ W))).val.obj V) :
    (((restrictFunctorComp (U.ι.isoImage W).inv W.ι).hom.app
      ((restrictFunctor U.ι).obj M)).val.app V
      (((restrictFunctorComp
        ((U.ι.isoImage W).inv ≫ W.ι) U.ι).hom.app M).val.app V
        (((restrictFunctorCongr
          (localSchemeModule_morphism_eq U W)).inv.app M).val.app V x))) =
      (M.over (U.ι ''ᵁ W)).val.map
        (localSchemeModuleOverIso U W V.unop).hom.op x := by
  change (localSchemeModuleTransition M U W).val.app V x = _
  exact localSchemeModuleTransition_app_apply M U W V x

theorem localSchemeUnitTransition_app_apply (U : X.Opens)
    (W : U.toScheme.Opens)
    (V : (U.ι ''ᵁ W).toScheme.Opens)
    (x : (_root_.SheafOfModules.unit
      (X.ringCatSheaf.over (U.ι ''ᵁ W))).val.obj
        (op (localSchemeModuleTargetOver U W V))) :
    ((U.ι.isoImage W).inv.appIso V).hom
        ((U.ι.appIso (localSchemeModuleSourceOverW U W V).left).hom
          ((_root_.SheafOfModules.unit
            (X.ringCatSheaf.over (U.ι ''ᵁ W))).val.map
              (localSchemeModuleOverIso U W V).hom.op x)) = x := by
  change ((U.ι.isoImage W).inv.appIso V).hom
      ((U.ι.appIso (localSchemeModuleSourceOverW U W V).left).hom
        (X.presheaf.map
          (localSchemeModuleOverIso U W V).hom.left.op x)) = x
  have hmap := localSchemeModuleOpen_map_apply U W V x
  have hmap' :
      X.presheaf.map (localSchemeModuleOverIso U W V).hom.left.op x =
        X.presheaf.map
          (eqToHom (localSchemeModuleOpen_eq_three_step U W V)).op
          (X.presheaf.map
            (eqToHom (Scheme.Hom.comp_image
              ((U.ι.isoImage W).inv ≫ W.ι) U.ι V).symm).op
          (X.presheaf.map
              (eqToHom (localSchemeModuleOpen_eq_one U W V)).op x)) := by
    rw [localSchemeModuleOverIso_hom_left]
    exact hmap
  refine (congrArg (fun z ↦
    ((U.ι.isoImage W).inv.appIso V).hom
      ((U.ι.appIso (localSchemeModuleSourceOverW U W V).left).hom z)) hmap').trans ?_
  let x0 := X.presheaf.map
    (eqToHom (localSchemeModuleOpen_eq_one U W V)).op x
  let x1 := X.presheaf.map
    (eqToHom (Scheme.Hom.comp_image
      ((U.ι.isoImage W).inv ≫ W.ι) U.ι V).symm).op x0
  have hab := comp_appIso_hom_apply
    (U.ι.isoImage W).inv W.ι V x1
  have hfull := comp_appIso_hom_apply
    ((U.ι.isoImage W).inv ≫ W.ι) U.ι V x0
  let z := X.presheaf.map
    (eqToHom (localSchemeModuleOpen_eq_three_step U W V)).op x1
  change ((U.ι.isoImage W).inv.appIso V).hom
      ((U.ι.appIso (localSchemeModuleSourceOverW U W V).left).hom z) = x
  have hUfinal :
      (U.ι.appIso (localSchemeModuleSourceOverW U W V).left).hom z = z := by
    rw [Scheme.Opens.ι_appIso]
    rfl
  refine (congrArg (fun t ↦
    ((U.ι.isoImage W).inv.appIso V).hom t) hUfinal).trans ?_
  let uMap := U.toScheme.presheaf.map
    (eqToHom (Scheme.Hom.comp_image
      (U.ι.isoImage W).inv W.ι V).symm).op x1
  have huMap : uMap = z := by rfl
  have hW : (W.ι.appIso ((U.ι.isoImage W).inv ''ᵁ V)).hom uMap = z := by
    rw [Scheme.Opens.ι_appIso]
    exact huMap
  have hab' :
      (((U.ι.isoImage W).inv ≫ W.ι).appIso V).hom x1 =
        ((U.ι.isoImage W).inv.appIso V).hom z :=
    hab.trans (congrArg (fun t ↦
      ((U.ι.isoImage W).inv.appIso V).hom t) hW)
  have hU :
      (U.ι.appIso (((U.ι.isoImage W).inv ≫ W.ι) ''ᵁ V)).hom
          (X.presheaf.map
            (eqToHom (Scheme.Hom.comp_image
              ((U.ι.isoImage W).inv ≫ W.ι) U.ι V).symm).op x0) = x1 := by
    rw [Scheme.Opens.ι_appIso]
    rfl
  have hfull' :
      (((((U.ι.isoImage W).inv ≫ W.ι) ≫ U.ι).appIso V).hom x0) =
        (((U.ι.isoImage W).inv ≫ W.ι).appIso V).hom x1 :=
    hfull.trans (congrArg (fun t ↦
      (((U.ι.isoImage W).inv ≫ W.ι).appIso V).hom t) hU)
  refine hab'.symm.trans (hfull'.symm.trans ?_)
  have hcongr := appIso_congr_apply
    (((U.ι.isoImage W).inv ≫ W.ι) ≫ U.ι)
    (U.ι ''ᵁ W).ι (localSchemeModule_morphism_eq U W) V
    (localSchemeModuleOpen_eq_one U W V) x
  have hlast : ((U.ι ''ᵁ W).ι.appIso V).hom x = x := by
    rw [Scheme.Opens.ι_appIso]
    rfl
  exact hcongr.trans hlast

noncomputable def localModuleIso (M : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens) :
    (localEquiv U W).functor.obj (((restrictFunctor U.ι).obj M).over W) ≅
      M.over (U.ι ''ᵁ W) :=
  (overEquiv (U.ι ''ᵁ W)).fullyFaithfulFunctor.preimageIso
    ((overEquiv (U.ι ''ᵁ W)).counitIso.app
        ((restrictFunctor (U.ι.isoImage W).inv).obj
          ((overEquiv W).functor.obj (((restrictFunctor U.ι).obj M).over W))) ≪≫
      localSchemeModuleIso M U W)

noncomputable def localSchemeUnitIso (U : X.Opens) (W : U.toScheme.Opens) :
    (restrictFunctor (U.ι.isoImage W).inv).obj
        ((overEquiv W).functor.obj
          (_root_.SheafOfModules.unit (U.toScheme.ringCatSheaf.over W))) ≅
      (overEquiv (U.ι ''ᵁ W)).functor.obj
        (_root_.SheafOfModules.unit
          (X.ringCatSheaf.over (U.ι ''ᵁ W))) :=
  restrictUnitIso (U.ι.isoImage W).inv

theorem localSchemeUnitIso_hom_app_apply (U : X.Opens)
    (W : U.toScheme.Opens)
    (V : Opposite (U.ι ''ᵁ W).toScheme.Opens)
    (x : ((restrictFunctor (U.ι.isoImage W).inv).obj
      ((overEquiv W).functor.obj
        (_root_.SheafOfModules.unit
          (U.toScheme.ringCatSheaf.over W)))).val.obj V) :
    (localSchemeUnitIso U W).hom.val.app V x =
      ((U.ι.isoImage W).inv.appIso V.unop).hom x := by
  rfl

noncomputable def localUnitIso (U : X.Opens) (W : U.toScheme.Opens) :
    (localEquiv U W).functor.obj
        (_root_.SheafOfModules.unit (U.toScheme.ringCatSheaf.over W)) ≅
      _root_.SheafOfModules.unit
        (X.ringCatSheaf.over (U.ι ''ᵁ W)) :=
  (overEquiv (U.ι ''ᵁ W)).fullyFaithfulFunctor.preimageIso
    ((overEquiv (U.ι ''ᵁ W)).counitIso.app
        ((restrictFunctor (U.ι.isoImage W).inv).obj
          ((overEquiv W).functor.obj
            (_root_.SheafOfModules.unit (U.toScheme.ringCatSheaf.over W)))) ≪≫
      localSchemeUnitIso U W)

noncomputable def localDualSectionsEquiv (M : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens) :
    ((((restrictFunctor U.ι).obj M).over W ⟶
        _root_.SheafOfModules.unit (U.toScheme.ringCatSheaf.over W))) ≃
      (M.over (U.ι ''ᵁ W) ⟶
        _root_.SheafOfModules.unit
          (X.ringCatSheaf.over (U.ι ''ᵁ W))) :=
  (localEquiv U W).fullyFaithfulFunctor.homEquiv.trans
    (Iso.homCongr (localModuleIso M U W) (localUnitIso U W))

theorem localSchemeDualRestrict_restrict_app_apply (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens)
    (alpha : M.over (U.ι ''ᵁ W) ⟶
      _root_.SheafOfModules.unit
        (X.ringCatSheaf.over (U.ι ''ᵁ W)))
    (V : Opposite (U.ι ''ᵁ W).toScheme.Opens)
    (y : ((restrictFunctor (U.ι.isoImage W).inv).obj
      ((overEquiv W).functor.obj
        (((restrictFunctor U.ι).obj M).over W))).val.obj V) :
    (localSchemeUnitIso U W).hom.val.app V
        (((restrictFunctor (U.ι.isoImage W).inv).map
          ((overEquiv W).functor.map
            (localDualRestrict M U W alpha))).val.app V y) =
      (localSchemeUnitIso U W).hom.val.app V
        (((overEquiv W).functor.map
          (localDualRestrict M U W alpha)).val.app
            ((U.ι.isoImage W).inv.opensFunctor.op.obj V) y) := by
  exact congrArg (fun z ↦ (localSchemeUnitIso U W).hom.val.app V z)
    (restrictFunctor_map_app_apply (U.ι.isoImage W).inv
      ((overEquiv W).functor.map (localDualRestrict M U W alpha)) V y)

theorem localSchemeDualRestrict_value (M : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens)
    (alpha : M.over (U.ι ''ᵁ W) ⟶
      _root_.SheafOfModules.unit
        (X.ringCatSheaf.over (U.ι ''ᵁ W)))
    (V : Opposite (U.ι ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (U.ι ''ᵁ W)).functor.obj
      (M.over (U.ι ''ᵁ W))).val.obj V) :
    (localSchemeUnitIso U W).hom.val.app V
        (((overEquiv W).functor.map
          (localDualRestrict M U W alpha)).val.app
            ((U.ι.isoImage W).inv.opensFunctor.op.obj V)
          (((restrictFunctorComp (U.ι.isoImage W).inv W.ι).hom.app
            ((restrictFunctor U.ι).obj M)).val.app V
            (((restrictFunctorComp
              ((U.ι.isoImage W).inv ≫ W.ι) U.ι).hom.app M).val.app V
              (((restrictFunctorCongr
                (localSchemeModule_morphism_eq U W)).inv.app M).val.app V x)))) =
      ((overEquiv (U.ι ''ᵁ W)).functor.map alpha).val.app V x := by
  let y :=
    (((restrictFunctorComp (U.ι.isoImage W).inv W.ι).hom.app
      ((restrictFunctor U.ι).obj M)).val.app V
      (((restrictFunctorComp
        ((U.ι.isoImage W).inv ≫ W.ι) U.ι).hom.app M).val.app V
        (((restrictFunctorCongr
          (localSchemeModule_morphism_eq U W)).inv.app M).val.app V x)))
  let Z := (U.ι.isoImage W).inv.opensFunctor.op.obj V
  let k := fun z ↦ (localSchemeUnitIso U W).hom.val.app V z
  have hl := overEquiv_map_app_apply W
    (localDualRestrict M U W alpha) Z y
  have hr := overEquiv_map_app_apply (U.ι ''ᵁ W) alpha V x
  change k (((overEquiv W).functor.map
    (localDualRestrict M U W alpha)).val.app Z y) = _
  calc
    k (((overEquiv W).functor.map
        (localDualRestrict M U W alpha)).val.app Z y) =
      k ((localDualRestrict M U W alpha).val.app
        (op (W.overEquivalence.symm.functor.obj Z.unop)) y) :=
      congrArg k hl
    _ = ((overEquiv (U.ι ''ᵁ W)).functor.map alpha).val.app V x :=
      by
        rw [hr]
        let Q := op (W.overEquivalence.symm.functor.obj Z.unop)
        have hu := localSchemeUnitIso_hom_app_apply U W V
          ((localDualRestrict M U W alpha).val.app Q y)
        have hd := localDualRestrict_app_apply M U W alpha Q y
        refine hu.trans ?_
        refine (congrArg (fun z ↦
          ((U.ι.isoImage W).inv.appIso V.unop).hom z) hd).trans ?_
        let i := localSchemeModuleOverIso U W V.unop
        have hy := localSchemeModuleTransition_raw_app_apply M U W V x
        have ha := PresheafOfModules.naturality_apply alpha.val i.hom.op x
        have hyAlpha := congrArg
          (fun z ↦ alpha.val.app
            (op (localSchemeModuleSourceOver U W V.unop)) z) hy
        have hAlpha := hyAlpha.trans ha
        let f := fun z ↦
          ((U.ι.isoImage W).inv.appIso V.unop).hom
            ((U.ι.appIso Q.unop.left).hom z)
        refine (congrArg f hAlpha).trans ?_
        exact localSchemeUnitTransition_app_apply U W V.unop _

theorem localSchemeDualRestrict_raw (M : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens)
    (alpha : M.over (U.ι ''ᵁ W) ⟶
      _root_.SheafOfModules.unit
        (X.ringCatSheaf.over (U.ι ''ᵁ W)))
    (V : Opposite (U.ι ''ᵁ W).toScheme.Opens)
    (x : ((overEquiv (U.ι ''ᵁ W)).functor.obj
      (M.over (U.ι ''ᵁ W))).val.obj V) :
    (localSchemeUnitIso U W).hom.val.app V
        (((restrictFunctor (U.ι.isoImage W).inv).map
          ((overEquiv W).functor.map
            (localDualRestrict M U W alpha))).val.app V
          ((localSchemeModuleIsoOverFunctor M U W).inv.val.app V
            (((restrictFunctorComp (U.ι.isoImage W).inv W.ι).hom.app
              ((restrictFunctor U.ι).obj M)).val.app V
              (((restrictFunctorComp
                ((U.ι.isoImage W).inv ≫ W.ι) U.ι).hom.app M).val.app V
                (((restrictFunctorCongr
                  (localSchemeModule_morphism_eq U W)).inv.app M).val.app V x))))) =
      ((overEquiv (U.ι ''ᵁ W)).functor.map alpha).val.app V x := by
  let y :=
    (((restrictFunctorComp (U.ι.isoImage W).inv W.ι).hom.app
      ((restrictFunctor U.ι).obj M)).val.app V
      (((restrictFunctorComp
        ((U.ι.isoImage W).inv ≫ W.ι) U.ι).hom.app M).val.app V
        (((restrictFunctorCongr
          (localSchemeModule_morphism_eq U W)).inv.app M).val.app V x)))
  let k := fun z ↦
    (localSchemeUnitIso U W).hom.val.app V
      (((restrictFunctor (U.ι.isoImage W).inv).map
        ((overEquiv W).functor.map
          (localDualRestrict M U W alpha))).val.app V z)
  have h0 := localSchemeModuleIsoOverFunctor_inv_app_apply M U W V y
  calc
    _ = k y := congrArg k h0
    _ = (localSchemeUnitIso U W).hom.val.app V
        (((overEquiv W).functor.map
          (localDualRestrict M U W alpha)).val.app
            ((U.ι.isoImage W).inv.opensFunctor.op.obj V) y) :=
      localSchemeDualRestrict_restrict_app_apply M U W alpha V y
    _ = ((overEquiv (U.ι ''ᵁ W)).functor.map alpha).val.app V x :=
      localSchemeDualRestrict_value M U W alpha V x

theorem localSchemeDualRestrict (M : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens)
    (alpha : M.over (U.ι ''ᵁ W) ⟶
      _root_.SheafOfModules.unit
        (X.ringCatSheaf.over (U.ι ''ᵁ W))) :
    (localSchemeModuleIso M U W).inv ≫
        (restrictFunctor (U.ι.isoImage W).inv).map
          ((overEquiv W).functor.map (localDualRestrict M U W alpha)) ≫
      (localSchemeUnitIso U W).hom =
        (overEquiv (U.ι ''ᵁ W)).functor.map alpha := by
  apply (_root_.SheafOfModules.forget
    (U.ι ''ᵁ W).toScheme.ringCatSheaf).map_injective
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((localSchemeUnitIso U W).hom.val.app V)
      (((restrictFunctor (U.ι.isoImage W).inv).map
        ((overEquiv W).functor.map (localDualRestrict M U W alpha))).val.app V
          ((localSchemeModuleIso M U W).inv.val.app V x)) =
    ((overEquiv (U.ι ''ᵁ W)).functor.map alpha).val.app V x
  dsimp only [localSchemeModuleIso]
  rw [localSchemeModuleIsoStage5_inv]
  erw [sheafOfModules_comp_app_apply]
  rw [localSchemeModuleIsoStage4_inv]
  erw [sheafOfModules_comp_app_apply]
  rw [localSchemeModuleIsoStage3_inv]
  erw [sheafOfModules_comp_app_apply]
  rw [localSchemeModuleIsoStage2_inv]
  erw [sheafOfModules_comp_app_apply]
  have hx0 := localSchemeModuleIsoOverImage_inv_app_apply M U W V x
  let k0 := fun y ↦
    (localSchemeUnitIso U W).hom.val.app V
      (((restrictFunctor (U.ι.isoImage W).inv).map
        ((overEquiv W).functor.map (localDualRestrict M U W alpha))).val.app V
          ((localSchemeModuleIsoOverFunctor M U W).inv.val.app V
            ((localSchemeModuleIsoCompW M U W).inv.val.app V
              ((localSchemeModuleIsoCompU M U W).inv.val.app V
                ((localSchemeModuleIsoCongr M U W).inv.val.app V y)))))
  change k0 ((localSchemeModuleIsoOverImage M U W).inv.val.app V x) = _
  calc
    k0 ((localSchemeModuleIsoOverImage M U W).inv.val.app V x) = k0 x :=
      congrArg k0 hx0
    _ = ((overEquiv (U.ι ''ᵁ W)).functor.map alpha).val.app V x :=
      localSchemeDualRestrict_raw M U W alpha V x

theorem localDualSectionsEquiv_localDualRestrict (M : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens)
    (alpha : M.over (U.ι ''ᵁ W) ⟶
      _root_.SheafOfModules.unit
        (X.ringCatSheaf.over (U.ι ''ᵁ W))) :
    localDualSectionsEquiv M U W (localDualRestrict M U W alpha) = alpha := by
  change (localModuleIso M U W).inv ≫
      (localEquiv U W).functor.map (localDualRestrict M U W alpha) ≫
        (localUnitIso U W).hom = alpha
  apply (overEquiv (U.ι ''ᵁ W)).functor.map_injective
  simp only [Functor.map_comp, localModuleIso, localUnitIso,
    Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.preimageIso_inv,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.trans_inv]
  let E := overEquiv (U.ι ''ᵁ W)
  let A := (restrictFunctor (U.ι.isoImage W).inv).obj
    ((overEquiv W).functor.obj (((restrictFunctor U.ι).obj M).over W))
  let O := (restrictFunctor (U.ι.isoImage W).inv).obj
    ((overEquiv W).functor.obj
      (_root_.SheafOfModules.unit (U.toScheme.ringCatSheaf.over W)))
  let q : A ⟶ O :=
    (restrictFunctor (U.ι.isoImage W).inv).map
      ((overEquiv W).functor.map (localDualRestrict M U W alpha))
  change ((localSchemeModuleIso M U W).inv ≫ (E.counitIso.app A).inv) ≫
      E.functor.map (E.inverse.map q) ≫ (E.counitIso.app O).hom ≫
        (localSchemeUnitIso U W).hom = E.functor.map alpha
  have hmid : (E.counitIso.app A).inv ≫
      E.functor.map (E.inverse.map q) ≫ (E.counitIso.app O).hom = q := by
    simpa only [Functor.id_obj] using
      equivalence_counitInv_map_inverse_comp_counit E q
  calc
    ((localSchemeModuleIso M U W).inv ≫ (E.counitIso.app A).inv) ≫
          E.functor.map (E.inverse.map q) ≫ (E.counitIso.app O).hom ≫
            (localSchemeUnitIso U W).hom =
        (localSchemeModuleIso M U W).inv ≫
          (((E.counitIso.app A).inv ≫ E.functor.map (E.inverse.map q) ≫
            (E.counitIso.app O).hom) ≫ (localSchemeUnitIso U W).hom) := by
      simp only [Category.assoc]
    _ = (localSchemeModuleIso M U W).inv ≫
        (q ≫ (localSchemeUnitIso U W).hom) :=
      congrArg (fun k ↦ (localSchemeModuleIso M U W).inv ≫
        (k ≫ (localSchemeUnitIso U W).hom)) hmid
    _ = E.functor.map alpha := localSchemeDualRestrict M U W alpha

theorem localDualRestrict_bijective (M : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens) : Function.Bijective (localDualRestrict M U W) := by
  constructor
  · intro alpha beta h
    have h' := congrArg (localDualSectionsEquiv M U W) h
    simpa only [localDualSectionsEquiv_localDualRestrict] using h'
  · intro beta
    refine ⟨localDualSectionsEquiv M U W beta, ?_⟩
    apply (localDualSectionsEquiv M U W).injective
    rw [localDualSectionsEquiv_localDualRestrict]

noncomputable def dualRestrictComponentIso (M : X.Modules) (U : X.Opens)
    (W : Opposite U.toScheme.Opens) :
    ((restrictFunctor U.ι).obj (dualObj M)).val.obj W ≅
      (dualObj ((restrictFunctor U.ι).obj M)).val.obj W :=
  (LinearEquiv.ofBijective
    ((dualRestrictPresheafHom M U).app W).hom
    (localDualRestrict_bijective M U W.unop)).toModuleIso

theorem dualRestrictComponentIso_hom (M : X.Modules) (U : X.Opens)
    (W : Opposite U.toScheme.Opens) :
    (dualRestrictComponentIso M U W).hom =
      (dualRestrictPresheafHom M U).app W := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

noncomputable def dualRestrictPresheafIso (M : X.Modules) (U : X.Opens) :
    ((restrictFunctor U.ι).obj (dualObj M)).val ≅
      (dualObj ((restrictFunctor U.ι).obj M)).val :=
  PresheafOfModules.isoMk
    (dualRestrictComponentIso M U)
    (fun {_ _} f ↦ by
      rw [dualRestrictComponentIso_hom, dualRestrictComponentIso_hom]
      exact (dualRestrictPresheafHom M U).naturality f)

/-- Restriction along an open immersion commutes with the sheaf dual. -/
noncomputable def dualRestrictIso (M : X.Modules) (U : X.Opens) :
    (restrictFunctor U.ι).obj (dualObj M) ≅
      dualObj ((restrictFunctor U.ι).obj M) :=
  (_root_.SheafOfModules.fullyFaithfulForget U.toScheme.ringCatSheaf).preimageIso
    (dualRestrictPresheafIso M U)

end AlgebraicGeometry.Scheme.Modules
