import ModularCurves.Picard.DualPullback.LocalTrivialization

/-!
# Inverse local trivializations for pulled dual modules

The inverse source trivialization sends `1` to the canonical pulled dual section, allowing
the local dual-pullback map to be recognized as an isomorphism.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

theorem dualToPushforwardHomD_app_applyT
    (f : Y ⟶ X) (M : X.Modules) (U : Opposite X.Opens)
    (alpha : M.over U.unop ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U.unop)) :
    ((dualToPushforwardHomD f M).val.app U) alpha =
      localDualPullback f M U.unop alpha := by
  rfl

theorem dualIsoObj_hom_app_applyT {M N : X.Modules} (e : M ≅ N)
    (U : Opposite X.Opens)
    (alpha : N.over U.unop ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U.unop)) :
    ((dualIsoObj e).hom.val.app U) alpha =
      ModularCurves.SheafOfModules.dualPrecomp
        X.ringCatSheaf e.hom U.unop alpha := by
  rfl

theorem restrictAdjunction_unit_dual_app_applyT
    (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (U : Y.Opens)
    (alpha : M.over U ⟶
      _root_.SheafOfModules.unit (Y.ringCatSheaf.over U)) :
    (((restrictAdjunction j).unit.app (dualObj M)).val.app (.op U)) alpha =
      ModularCurves.SheafOfModules.dualRestrict Y.ringCatSheaf M
        (homOfLE (j.image_preimage_le U)).op alpha := by
  change (((restrictAdjunction j).unit.app
      (dualObj M)).val.app (.op U)) alpha =
    ((dualObj M).val.map (homOfLE (j.image_preimage_le U)).op) alpha
  have hunit := restrictAdjunction_unit_app_app
    (f := j) (dualObj M) U
  exact congrArg (fun q ↦ q.hom alpha) hunit

theorem dualRestrictIso_hom_app_applyT
    (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : Opposite X.Opens)
    (alpha : (M.over (j ''ᵁ W.unop) ⟶
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (j ''ᵁ W.unop)))) :
    ((dualRestrictIso M j).hom.val.app W) alpha =
      localDualRestrict M j W.unop alpha := by
  rfl

theorem dualRestrictIso_inv_app_applyT
    (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : Opposite X.Opens)
    (beta : (((restrictFunctor j).obj M).over W.unop ⟶
      _root_.SheafOfModules.unit
        (X.ringCatSheaf.over W.unop))) :
    ((dualRestrictIso M j).inv.val.app W) beta =
      localDualSectionsEquiv M j W.unop beta := by
  apply (localDualRestrict_bijective M j W.unop).1
  have hcomp := congrArg (fun q ↦ q.val.app W)
    (dualRestrictIso M j).inv_hom_id
  have h := ConcreteCategory.congr_hom hcomp beta
  change ((dualRestrictIso M j).hom.val.app W)
      (((dualRestrictIso M j).inv.val.app W) beta) = beta at h
  rw [dualRestrictIso_hom_app_applyT] at h
  have hsections : localDualRestrict M j W.unop
      (localDualSectionsEquiv M j W.unop beta) = beta := by
    apply (localDualSectionsEquiv M j W.unop).injective
    rw [localDualSectionsEquiv_localDualRestrict]
  exact h.trans hsections.symm

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite



namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

theorem dualPullbackHom_unit_appT (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens)
    (alpha : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (dualPullbackHomD f M).val.app (.op (f ⁻¹ᵁ U))
        (((pullbackPushforwardAdjunction f).unit.app (dualObj M)).val.app
          (.op U) alpha) =
      localDualPullback f M U alpha := by
  have h := pullbackAdjunction_homEquiv_dualPullbackHomD f M
  rw [Adjunction.homEquiv_unit] at h
  have happ := congrArg (fun q ↦ q.val.app (.op U) alpha) h
  erw [sheafOfModules_comp_app_apply] at happ
  change (dualPullbackHomD f M).val.app (.op (f ⁻¹ᵁ U))
      (((pullbackPushforwardAdjunction f).unit.app (dualObj M)).val.app
        (.op U) alpha) =
    (dualToPushforwardHomD f M).val.app (.op U) alpha at happ
  rw [dualToPushforwardHomD_app_applyT] at happ
  exact happ

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite



namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

theorem sheafIso_inv_app_eq_of_hom_app_eqT
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {A B : _root_.SheafOfModules R}
    (p : A ≅ B) (Z : Opposite C) (x : A.val.obj Z) (y : B.val.obj Z)
    (h : p.hom.val.app Z x = y) :
    p.inv.val.app Z y = x := by
  have hleft := congrArg (fun z ↦ p.inv.val.app Z z) h.symm
  have hcomp := congrArg (fun q ↦ q.val.app Z) p.hom_inv_id
  have hright := ConcreteCategory.congr_hom hcomp x
  erw [sheafOfModules_comp_app_apply] at hright
  exact hleft.trans hright

theorem localSheafIso_inv_one_of_hom_eq_oneT
    (V : Y.Opens)
    {A : _root_.SheafOfModules (Y.ringCatSheaf.over V)}
    (p : A ≅ _root_.SheafOfModules.unit (Y.ringCatSheaf.over V))
    (x : A.val.obj (.op (Over.mk (𝟙 V))))
    (h : p.hom.val.app (.op (Over.mk (𝟙 V))) x =
      (show (Y.ringCatSheaf.over V).obj.obj
        (.op (Over.mk (𝟙 V))) from 1)) :
    p.inv.val.app (.op (Over.mk (𝟙 V)))
        (show (Y.ringCatSheaf.over V).obj.obj
          (.op (Over.mk (𝟙 V))) from 1) = x := by
  exact sheafIso_inv_app_eq_of_hom_app_eqT
    (C := Over V) (R := Y.ringCatSheaf.over V) p
      (.op (Over.mk (𝟙 V))) x
        (show (Y.ringCatSheaf.over V).obj.obj
          (.op (Over.mk (𝟙 V))) from 1) h

theorem localPullbackTrivialization_inv_one_coreT (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (d : (dualObj M).over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (p : ((pullback f).obj (dualObj M)).over (f ⁻¹ᵁ U) ≅
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (f ⁻¹ᵁ U)))
    (hd : d.hom.val.app (.op (Over.mk (𝟙 U))) e.hom =
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1))
    (hp : (overEquiv (f ⁻¹ᵁ U)).functor.map p.hom =
      (localPullbackModuleIso f (dualObj M) U).inv ≫
        (pullback (f ∣_ U)).map
          ((overEquiv U).functor.map d.hom) ≫
        (localPullbackUnitIso f U).hom) :
    p.inv.val.app (.op (Over.mk (𝟙 (f ⁻¹ᵁ U))))
        (show (Y.ringCatSheaf.over (f ⁻¹ᵁ U)).obj.obj
          (.op (Over.mk (𝟙 (f ⁻¹ᵁ U)))) from 1) =
      ((pullbackPushforwardAdjunction f).unit.app (dualObj M)).val.app
        (.op U) e.hom := by
  apply localSheafIso_inv_one_of_hom_eq_oneT (f ⁻¹ᵁ U) p
  exact localPullbackTrivialization_hom_unit_coreT f M U e d p hd hp

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

theorem localPullbackTrivialization_inv_oneT (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    let d := ModularCurves.SheafOfModules.dualOverIsoOfIso
      X.ringCatSheaf M U e
    let p := localPullbackTrivializationT f (dualObj M) U d
    p.inv.val.app (.op (Over.mk (𝟙 (f ⁻¹ᵁ U))))
        (show (Y.ringCatSheaf.over (f ⁻¹ᵁ U)).obj.obj
          (.op (Over.mk (𝟙 (f ⁻¹ᵁ U)))) from 1) =
      ((pullbackPushforwardAdjunction f).unit.app (dualObj M)).val.app
        (.op U) e.hom := by
  dsimp only
  let d := ModularCurves.SheafOfModules.dualOverIsoOfIso
    X.ringCatSheaf M U e
  let p := localPullbackTrivializationT f (dualObj M) U d
  let V := f ⁻¹ᵁ U
  let T : Over V := Over.mk (𝟙 V)
  let oneV : (Y.ringCatSheaf.over V).obj.obj (.op T) := 1
  let xg := ((pullbackPushforwardAdjunction f).unit.app
    (dualObj M)).val.app (.op U) e.hom
  change p.inv.val.app (.op T) oneV = xg
  have hd := dualOverIsoOfIso_hom_terminal_apply_trivializationT M U e
  have hp : (overEquiv V).functor.map p.hom =
      (localPullbackModuleIso f (dualObj M) U).inv ≫
        (pullback (f ∣_ U)).map
          ((overEquiv U).functor.map d.hom) ≫
        (localPullbackUnitIso f U).hom := by
    dsimp only [p, localPullbackTrivializationT]
    simp only [Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage, Iso.trans_hom,
      Functor.mapIso_hom]
    rfl
  exact localPullbackTrivialization_inv_one_coreT f M U e d p hd hp

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite



namespace AlgebraicGeometry.Scheme.Modules

theorem sheaf_three_comp_app_eqT
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    {A B D E : _root_.SheafOfModules R}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (U : Opposite C) (x : A.val.obj U)
    (y : B.val.obj U) (z : D.val.obj U) (w : E.val.obj U)
    (ha : a.val.app U x = y) (hb : b.val.app U y = z)
    (hc : c.val.app U z = w) :
    (a ≫ b ≫ c).val.app U x = w := by
  change c.val.app U (b.val.app U (a.val.app U x)) = w
  rw [ha, hb, hc]

theorem unitEnd_eq_id_of_terminal_oneT
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [∀ U, IsMulCommutative (R.obj.obj U)] (U : C)
    (q : End (_root_.SheafOfModules.unit (R.over U)))
    (h : q.val.app (.op (Over.mk (𝟙 U)))
        (show (R.over U).obj.obj (.op (Over.mk (𝟙 U))) from 1) =
      (show (R.over U).obj.obj (.op (Over.mk (𝟙 U))) from 1)) :
    q = 𝟙 _ := by
  apply (ModularCurves.SheafOfModules.dualUnitSectionsEquiv R U).injective
  rw [ModularCurves.SheafOfModules.dualUnitSectionsEquiv_apply]
  rw [ModularCurves.SheafOfModules.dualUnitSectionsEquiv_apply]
  change q.val.app (.op (Over.mk (𝟙 U)))
      (show (R.over U).obj.obj (.op (Over.mk (𝟙 U))) from 1) =
    (show (R.over U).obj.obj (.op (Over.mk (𝟙 U))) from 1)
  exact h

theorem isIso_of_local_trivializations_terminal_oneT
    {Y : Scheme.{u}} (V : Y.Opens)
    {A B : _root_.SheafOfModules (Y.ringCatSheaf.over V)}
    (pS : A ≅ _root_.SheafOfModules.unit (Y.ringCatSheaf.over V))
    (pT : B ≅ _root_.SheafOfModules.unit (Y.ringCatSheaf.over V))
    (m : A ⟶ B)
    (x : A.val.obj (.op (Over.mk (𝟙 V))))
    (y : B.val.obj (.op (Over.mk (𝟙 V))))
    (hs : pS.inv.val.app (.op (Over.mk (𝟙 V)))
        (show (Y.ringCatSheaf.over V).obj.obj
          (.op (Over.mk (𝟙 V))) from 1) = x)
    (hm : m.val.app (.op (Over.mk (𝟙 V))) x = y)
    (ht : pT.hom.val.app (.op (Over.mk (𝟙 V))) y =
      (show (Y.ringCatSheaf.over V).obj.obj
        (.op (Over.mk (𝟙 V))) from 1))
    [∀ U, IsMulCommutative (Y.ringCatSheaf.obj.obj U)] :
    IsIso m := by
  let T : Over V := Over.mk (𝟙 V)
  let oneV : (Y.ringCatSheaf.over V).obj.obj (.op T) := 1
  have hvalue : (pS.inv ≫ m ≫ pT.hom).val.app (.op T) oneV = oneV :=
    sheaf_three_comp_app_eqT pS.inv m pT.hom (.op T)
      oneV x y oneV hs hm ht
  have hconj : pS.inv ≫ m ≫ pT.hom = 𝟙 _ :=
    unitEnd_eq_id_of_terminal_oneT Y.ringCatSheaf V
      (pS.inv ≫ m ≫ pT.hom) hvalue
  haveI hconjIso : IsIso (pS.inv ≫ m ≫ pT.hom) := by
    rw [hconj]
    infer_instance
  haveI hleft : IsIso (pS.inv ≫ m) :=
    (isIso_comp_right_iff (pS.inv ≫ m) pT.hom).mp hconjIso
  exact (isIso_comp_left_iff pS.inv m).mp hleft

end AlgebraicGeometry.Scheme.Modules
