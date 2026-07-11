import ModularCurves.Picard.DualRestrict
import ModularCurves.Picard.UnitPullback

/-!
# Pullback of dual modules

This file constructs the canonical comparison from the pullback of a module dual to the
dual of its pullback.  For invertible modules the comparison is an isomorphism.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

/-- Transport an ambient module restriction from the over-site presentation to the
corresponding open subscheme. -/
noncomputable def overRestrictModuleIso (M : X.Modules) {U V : X.Opens}
    (i : V ⟶ U) :
    (overEquiv V).functor.obj (M.over V) ≅
      (restrictFunctor (X.homOfLE (leOfHom i))).obj
        ((overEquiv U).functor.obj (M.over U)) :=
  (overEquiv V).functor.mapIso
      (((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).app M).symm) ≪≫
    (overMapCompOverEquiv i).app (M.over U)

/-- Transport the restriction of the local structure module from an open subscheme
back to its over-site presentation. -/
noncomputable def overRestrictUnitIso {U V : X.Opens} (i : V ⟶ U) :
    (restrictFunctor (X.homOfLE (leOfHom i))).obj
        ((overEquiv U).functor.obj
          (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))) ≅
      (overEquiv V).functor.obj
        (_root_.SheafOfModules.unit (X.ringCatSheaf.over V)) :=
  ((overMapCompOverEquiv i).app
      (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))).symm ≪≫
    (overEquiv V).functor.mapIso
      (_root_.SheafOfModules.overMapUnitIso i)

/-- Restriction of a local functional, expressed after transporting both over-sites to
their open subschemes. -/
theorem overEquiv_map_dualRestrict (M : X.Modules) {U V : X.Opens}
    (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (overEquiv V).functor.map
        (ModularCurves.SheafOfModules.dualRestrict X.ringCatSheaf M i.op α) =
      (overRestrictModuleIso M i).hom ≫
        (restrictFunctor (X.homOfLE (leOfHom i))).map
          ((overEquiv U).functor.map α) ≫
        (overRestrictUnitIso i).hom := by
  let E := overMapCompOverEquiv i
  have hmid : E.hom.app (M.over U) ≫
        (restrictFunctor (X.homOfLE (leOfHom i))).map
          ((overEquiv U).functor.map α) ≫
        E.inv.app (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)) =
      (overEquiv V).functor.map
        ((_root_.SheafOfModules.overMap X.ringCatSheaf i).map α) := by
    let F := _root_.SheafOfModules.overMap X.ringCatSheaf i ⋙
      (overEquiv V).functor
    let G := (overEquiv U).functor ⋙
      restrictFunctor (X.homOfLE (leOfHom i))
    let O := _root_.SheafOfModules.unit (X.ringCatSheaf.over U)
    let p := F.map α
    change E.hom.app (M.over U) ≫ G.map α ≫ E.inv.app O = p
    have hnat : p ≫ E.hom.app O = E.hom.app (M.over U) ≫ G.map α :=
      E.hom.naturality α
    calc
      E.hom.app (M.over U) ≫ G.map α ≫ E.inv.app O =
          (E.hom.app (M.over U) ≫ G.map α) ≫ E.inv.app O :=
        (Category.assoc _ _ _).symm
      _ = (p ≫ E.hom.app O) ≫ E.inv.app O :=
        congrArg (fun r ↦ r ≫ E.inv.app O) hnat.symm
      _ = p ≫ (E.hom.app O ≫ E.inv.app O) :=
        Category.assoc _ _ _
      _ = p ≫ 𝟙 (F.obj O) :=
        congrArg (fun r ↦ p ≫ r) (E.hom_inv_id_app O)
      _ = p :=
        Category.comp_id _
  simp only [ModularCurves.SheafOfModules.dualRestrict,
    overRestrictModuleIso, overRestrictUnitIso, Functor.map_comp,
    Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, Quiver.Hom.unop_op]
  let a := (overEquiv V).functor.map
    ((_root_.SheafOfModules.overFunctorMap X.ringCatSheaf i).inv.app M)
  let b := (overEquiv V).functor.map
    (_root_.SheafOfModules.overMapUnitIso i).hom
  change a ≫ (overEquiv V).functor.map
        ((_root_.SheafOfModules.overMap X.ringCatSheaf i).map α) ≫ b =
    a ≫ (E.hom.app (M.over U) ≫
      (restrictFunctor (X.homOfLE (leOfHom i))).map
        ((overEquiv U).functor.map α) ≫
      E.inv.app (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))) ≫ b
  calc
    a ≫ (overEquiv V).functor.map
          ((_root_.SheafOfModules.overMap X.ringCatSheaf i).map α) ≫ b =
        a ≫ (E.hom.app (M.over U) ≫
          (restrictFunctor (X.homOfLE (leOfHom i))).map
            ((overEquiv U).functor.map α) ≫
          E.inv.app
            (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))) ≫ b :=
      (congrArg (fun q ↦ a ≫ q ≫ b) hmid).symm
    _ = a ≫ E.hom.app (M.over U) ≫
        (restrictFunctor (X.homOfLE (leOfHom i))).map
          ((overEquiv U).functor.map α) ≫
        E.inv.app (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)) ≫ b := by
      simp only [Category.assoc]

/-- Pulling back after restriction to a smaller target open agrees with restricting
after pullback to the inverse-image open. -/
noncomputable def openPullbackRestrictIso (f : Y ⟶ X) {U V : X.Opens}
    (i : V ⟶ U) :
    restrictFunctor (X.homOfLE (leOfHom i)) ⋙ pullback (f ∣_ V) ≅
      pullback (f ∣_ U) ⋙
        restrictFunctor
          (Y.homOfLE (f.preimage_mono (leOfHom i))) :=
  Functor.isoWhiskerRight
      (restrictFunctorIsoPullback (X.homOfLE (leOfHom i)))
      (pullback (f ∣_ V)) ≪≫
    pullbackComp (f ∣_ V) (X.homOfLE (leOfHom i)) ≪≫
    pullbackCongr (morphismRestrict_homOfLE f V U (leOfHom i)) ≪≫
    (pullbackComp
      (Y.homOfLE (f.preimage_mono (leOfHom i))) (f ∣_ U)).symm ≪≫
    Functor.isoWhiskerLeft (pullback (f ∣_ U))
      (restrictFunctorIsoPullback
        (Y.homOfLE (f.preimage_mono (leOfHom i)))).symm

theorem overEquiv_map_add (U : X.Opens)
    {A B : _root_.SheafOfModules (X.ringCatSheaf.over U)} (p q : A ⟶ B) :
    (overEquiv U).functor.map (p + q) =
      (overEquiv U).functor.map p + (overEquiv U).functor.map q := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- A section on an ambient open, transported to the top open of its open subscheme. -/
noncomputable def openTopSection (U : X.Opens) (r : Γ(X, U)) :
    Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
  (U.ι.appIso ⊤).hom
    (X.presheaf.map (eqToHom U.ι_image_top).op r)

theorem sheafOfModulesEquivOverUnit_hom_app_apply (U : X.Opens)
    (V : Opposite U.toScheme.Opens)
    (x : ((overEquiv U).functor.obj
      (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))).val.obj V) :
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom.val.app V x = x := by
  rfl

theorem openTopSection_restrict (U : X.Opens) (V : U.toScheme.Opens) (r : Γ(X, U)) :
    (U.ι.appIso V).hom
        (X.presheaf.map (homOfLE (U.ι_image_le V)).op r) =
      U.toScheme.presheaf.map
        (homOfLE (le_top : V ≤ (⊤ : U.toScheme.Opens))).op
        (openTopSection U r) := by
  let i : Opposite.op (⊤ : U.toScheme.Opens) ⟶ Opposite.op V :=
    (homOfLE (le_top : V ≤ (⊤ : U.toScheme.Opens))).op
  have hmaps :
      X.presheaf.map (homOfLE (U.ι_image_le V)).op =
        X.presheaf.map (eqToHom U.ι_image_top).op ≫
          X.presheaf.map (U.ι.opensFunctor.map i.unop).op := by
    rw [← X.presheaf.map_comp]
    exact X.presheaf.congr_map (Subsingleton.elim _ _)
  rw [openTopSection, hmaps]
  have h := congrArg (fun q ↦ q.hom
      (X.presheaf.map (eqToHom U.ι_image_top).op r))
    (U.ι.appIso_hom_naturality i)
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using h

theorem overEquiv_unitScalarEnd (U : X.Opens) (r : Γ(X, U)) :
    (overEquiv U).functor.map
          (ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) ≫
        (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom =
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom ≫
        ModularCurves.unitEndomorphismOfTopSection (openTopSection U r) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  repeat' erw [sheafOfModules_comp_app_apply]
  rw [overEquiv_map_app_apply]
  rw [ModularCurves.SheafOfModules.overUnitScalarEnd_app_apply]
  erw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
  repeat' erw [sheafOfModulesEquivOverUnit_hom_app_apply (X := X) U V]
  congr 1
  change X.presheaf.map (homOfLE (U.ι_image_le V.unop)).op r =
    U.toScheme.presheaf.map
      (homOfLE (le_top : V.unop ≤ (⊤ : U.toScheme.Opens))).op
      (openTopSection U r)
  have h := openTopSection_restrict U V.unop r
  rw [Scheme.Opens.ι_appIso] at h
  exact h

theorem openTopSection_morphismRestrict (f : Y ⟶ X) (U : X.Opens) (r : Γ(X, U)) :
    openTopSection (f ⁻¹ᵁ U) ((f.app U).hom r) =
      (f ∣_ U).appTop.hom (openTopSection U r) := by
  rw [openTopSection, openTopSection, morphismRestrict_appTop]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_hom]
  change Y.presheaf.map (eqToHom (f ⁻¹ᵁ U).ι_image_top).op
      ((f.app U).hom r) =
    Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op
      ((f.app (U.ι ''ᵁ ⊤)).hom
        (X.presheaf.map (eqToHom U.ι_image_top).op r))
  let i : Opposite.op U ⟶ Opposite.op (U.ι ''ᵁ ⊤) :=
    (eqToHom U.ι_image_top).op
  have h := congrArg (fun q ↦ q.hom r) (f.naturality i)
  have hmap :
      Y.presheaf.map (eqToHom (f ⁻¹ᵁ U).ι_image_top).op =
        Y.presheaf.map (((TopologicalSpace.Opens.map f.base).map i.unop).op) ≫
          Y.presheaf.map
            (eqToHom (image_morphismRestrict_preimage f U ⊤)).op := by
    rw [← Y.presheaf.map_comp]
    exact Y.presheaf.congr_map (Subsingleton.elim _ _)
  rw [hmap]
  exact congrArg
    (fun x ↦ Y.presheaf.map
      (eqToHom (image_morphismRestrict_preimage f U ⊤)).op x) h.symm

/-- Pulling a module restricted to an open back along the restricted morphism agrees
with restricting the pullback module to the inverse-image open. -/
noncomputable def localPullbackModuleIso (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    (pullback (f ∣_ U)).obj ((overEquiv U).functor.obj (M.over U)) ≅
      (overEquiv (f ⁻¹ᵁ U)).functor.obj (((pullback f).obj M).over (f ⁻¹ᵁ U)) :=
  (pullback (f ∣_ U)).mapIso ((overFunctorEquiv U).app M) ≪≫
    (pullback (f ∣_ U)).mapIso ((restrictFunctorIsoPullback U.ι).app M) ≪≫
    (pullbackComp (f ∣_ U) U.ι).app M ≪≫
    (pullbackCongr (morphismRestrict_ι f U)).app M ≪≫
    ((pullbackComp (f ⁻¹ᵁ U).ι f).app M).symm ≪≫
    ((restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app ((pullback f).obj M)).symm ≪≫
    ((overFunctorEquiv (f ⁻¹ᵁ U)).app ((pullback f).obj M)).symm

/-- Pulling the local structure module back along a restricted morphism gives the local
structure module on the inverse-image open. -/
noncomputable def localPullbackUnitIso (f : Y ⟶ X) (U : X.Opens) :
    (pullback (f ∣_ U)).obj
        ((overEquiv U).functor.obj
          (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))) ≅
      (overEquiv (f ⁻¹ᵁ U)).functor.obj
        (_root_.SheafOfModules.unit (Y.ringCatSheaf.over (f ⁻¹ᵁ U))) :=
  (pullback (f ∣_ U)).mapIso (U.sheafOfModulesEquivOverUnit X.ringCatSheaf) ≪≫
    pullbackUnitIso (f ∣_ U) ≪≫
    ((f ⁻¹ᵁ U).sheafOfModulesEquivOverUnit Y.ringCatSheaf).symm

theorem pullbackUnitIso_scalar {A B : Scheme.{u}} (g : A ⟶ B)
    (r : Γ(B, (⊤ : B.Opens))) :
    (pullback g).map (ModularCurves.unitEndomorphismOfTopSection r) ≫
        (pullbackUnitIso g).hom =
      (pullbackUnitIso g).hom ≫
        ModularCurves.unitEndomorphismOfTopSection (g.appTop.hom r) := by
  have h := congrArg (fun q ↦ (pullbackUnitIso g).hom ≫ q)
    (ModularCurves.pullback_unitEndomorphismOfTopSection g r)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h

theorem overEquiv_unitScalarEnd_inv (U : X.Opens) (r : Γ(X, U)) :
    ModularCurves.unitEndomorphismOfTopSection (openTopSection U r) ≫
        (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).inv =
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).inv ≫
        (overEquiv U).functor.map
          (ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) := by
  let e := U.sheafOfModulesEquivOverUnit X.ringCatSheaf
  let a := (overEquiv U).functor.map
    (ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r)
  let b := ModularCurves.unitEndomorphismOfTopSection (openTopSection U r)
  have h : a ≫ e.hom = e.hom ≫ b := overEquiv_unitScalarEnd U r
  change b ≫ e.inv = e.inv ≫ a
  apply (Iso.comp_inv_eq e).2
  exact (e.inv_hom_id_assoc b).symm.trans
    ((congrArg (fun q ↦ e.inv ≫ q) h.symm).trans
      (Category.assoc _ _ _).symm)

theorem localPullbackUnitIso_scalar (f : Y ⟶ X) (U : X.Opens) (r : Γ(X, U)) :
    (pullback (f ∣_ U)).map
          ((overEquiv U).functor.map
            (ModularCurves.SheafOfModules.overUnitScalarEnd
              X.ringCatSheaf U r)) ≫
        (localPullbackUnitIso f U).hom =
      (localPullbackUnitIso f U).hom ≫
        (overEquiv (f ⁻¹ᵁ U)).functor.map
          (ModularCurves.SheafOfModules.overUnitScalarEnd Y.ringCatSheaf
            (f ⁻¹ᵁ U) ((f.app U).hom r)) := by
  let g := f ∣_ U
  let eU := U.sheafOfModulesEquivOverUnit X.ringCatSheaf
  let eV := (f ⁻¹ᵁ U).sheafOfModulesEquivOverUnit Y.ringCatSheaf
  let a := (overEquiv U).functor.map
    (ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r)
  let b := (overEquiv (f ⁻¹ᵁ U)).functor.map
    (ModularCurves.SheafOfModules.overUnitScalarEnd Y.ringCatSheaf
      (f ⁻¹ᵁ U) ((f.app U).hom r))
  have hU : (pullback g).map a ≫ (pullback g).map eU.hom =
      (pullback g).map eU.hom ≫
        (pullback g).map
          (ModularCurves.unitEndomorphismOfTopSection (openTopSection U r)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (pullback g).map (overEquiv_unitScalarEnd U r)
  have hpb : (pullback g).map
        (ModularCurves.unitEndomorphismOfTopSection (openTopSection U r)) ≫
      (pullbackUnitIso g).hom =
        (pullbackUnitIso g).hom ≫
          ModularCurves.unitEndomorphismOfTopSection
            (openTopSection (f ⁻¹ᵁ U) ((f.app U).hom r)) := by
    rw [pullbackUnitIso_scalar, ← openTopSection_morphismRestrict]
  have hV : ModularCurves.unitEndomorphismOfTopSection
        (openTopSection (f ⁻¹ᵁ U) ((f.app U).hom r)) ≫ eV.inv =
      eV.inv ≫ b :=
    overEquiv_unitScalarEnd_inv (f ⁻¹ᵁ U) ((f.app U).hom r)
  change (pullback g).map a ≫
      ((pullback g).map eU.hom ≫ (pullbackUnitIso g).hom ≫ eV.inv) =
    (pullback g).map eU.hom ≫ (pullbackUnitIso g).hom ≫ eV.inv ≫ b
  rw [← Category.assoc, hU]
  let pU := (pullback g).map eU.hom
  let pO := (pullback g).map
    (ModularCurves.unitEndomorphismOfTopSection (openTopSection U r))
  let e := (pullbackUnitIso g).hom
  let qO := ModularCurves.unitEndomorphismOfTopSection
    (openTopSection (f ⁻¹ᵁ U) ((f.app U).hom r))
  change (pU ≫ pO) ≫ e ≫ eV.inv = pU ≫ e ≫ eV.inv ≫ b
  calc
    (pU ≫ pO) ≫ e ≫ eV.inv =
        pU ≫ ((pO ≫ e) ≫ eV.inv) := by
      simp only [Category.assoc]
    _ = pU ≫ ((e ≫ qO) ≫ eV.inv) :=
      congrArg (fun q ↦ pU ≫ (q ≫ eV.inv)) hpb
    _ = pU ≫ (e ≫ (qO ≫ eV.inv)) := by
      simp only [Category.assoc]
    _ = pU ≫ (e ≫ (eV.inv ≫ b)) :=
      congrArg (fun q ↦ pU ≫ (e ≫ q)) hV
    _ = pU ≫ e ≫ eV.inv ≫ b := rfl

/-- Pull a local functional back along the morphism restricted to its domain open. -/
noncomputable def localDualPullback (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (α : M.over U ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ((pullback f).obj M).over (f ⁻¹ᵁ U) ⟶
      _root_.SheafOfModules.unit (Y.ringCatSheaf.over (f ⁻¹ᵁ U)) :=
  (overEquiv (f ⁻¹ᵁ U)).fullyFaithfulFunctor.preimage
    ((localPullbackModuleIso f M U).inv ≫
      (pullback (f ∣_ U)).map ((overEquiv U).functor.map α) ≫
      (localPullbackUnitIso f U).hom)

theorem localDualPullback_add (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (α β : M.over U ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    localDualPullback f M U (α + β) =
      localDualPullback f M U α + localDualPullback f M U β := by
  apply (overEquiv (f ⁻¹ᵁ U)).functor.map_injective
  rw [overEquiv_map_add]
  simp only [localDualPullback, Functor.FullyFaithful.map_preimage]
  rw [overEquiv_map_add, Functor.map_add, Preadditive.add_comp,
    Preadditive.comp_add]

theorem localDualPullback_smul (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (r : Γ(X, U))
    (α : M.over U ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    letI : Module (Γ(X, U))
        (M.over U ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :=
      ModularCurves.SheafOfModules.dualSectionsModule X.ringCatSheaf M U
    letI : Module (Γ(Y, f ⁻¹ᵁ U))
        (((pullback f).obj M).over (f ⁻¹ᵁ U) ⟶
          _root_.SheafOfModules.unit (Y.ringCatSheaf.over (f ⁻¹ᵁ U))) :=
      ModularCurves.SheafOfModules.dualSectionsModule Y.ringCatSheaf
        ((pullback f).obj M) (f ⁻¹ᵁ U)
    localDualPullback f M U (r • α) =
      (f.app U).hom r • localDualPullback f M U α := by
  letI : Module (Γ(X, U))
      (M.over U ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    ModularCurves.SheafOfModules.dualSectionsModule X.ringCatSheaf M U
  letI : Module (Γ(Y, f ⁻¹ᵁ U))
      (((pullback f).obj M).over (f ⁻¹ᵁ U) ⟶
        _root_.SheafOfModules.unit (Y.ringCatSheaf.over (f ⁻¹ᵁ U))) :=
    ModularCurves.SheafOfModules.dualSectionsModule Y.ringCatSheaf
      ((pullback f).obj M) (f ⁻¹ᵁ U)
  rw [show r • α = α ≫
    ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r from rfl]
  rw [show (f.app U).hom r • localDualPullback f M U α =
    localDualPullback f M U α ≫
      ModularCurves.SheafOfModules.overUnitScalarEnd Y.ringCatSheaf
        (f ⁻¹ᵁ U) ((f.app U).hom r) from rfl]
  apply (overEquiv (f ⁻¹ᵁ U)).functor.map_injective
  rw [Functor.map_comp]
  simp only [localDualPullback, Functor.FullyFaithful.map_preimage]
  rw [Functor.map_comp, Functor.map_comp]
  rw [Category.assoc, localPullbackUnitIso_scalar]
  rfl

end AlgebraicGeometry.Scheme.Modules
