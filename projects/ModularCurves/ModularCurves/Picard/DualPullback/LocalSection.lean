import ModularCurves.Picard.DualPullback.OpenUnit

/-!
# Local pullback of canonical sections

Transport canonical sections through local pullback, the terminal over-object, and the
pullback unit.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

theorem localPullbackModuleIso_pulledSectionT (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens) (x : M.val.obj (.op U)) :
    let W := U.ι ⁻¹ᵁ U
    let g := f ∣_ U
    let VY := f ⁻¹ᵁ U
    let ZY := VY.ι ⁻¹ᵁ VY
    let hpre : ZY = g ⁻¹ᵁ W := by
      change (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
        (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U)
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
      exact congrArg (fun q : VY.toScheme ⟶ X ↦ q ⁻¹ᵁ U)
        (morphismRestrict_ι f U).symm
    let A := (overEquiv U).functor.obj (M.over U)
    let a := ((pullbackPushforwardAdjunction g).unit.app A).val.app (.op W)
      (localModuleSection M U W x)
    (localPullbackModuleIso f M U).hom.val.app (.op ZY)
        (((pullback g).obj A).presheaf.map (eqToHom hpre).op a) =
      localModuleSection ((pullback f).obj M) VY ZY
        (((pullbackPushforwardAdjunction f).unit.app M).val.app (.op U) x) := by
  dsimp only
  let W := U.ι ⁻¹ᵁ U
  let g := f ∣_ U
  let VY := f ⁻¹ᵁ U
  let ZY := VY.ι ⁻¹ᵁ VY
  let hpre : ZY = g ⁻¹ᵁ W := by
    change (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
      (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
    exact congrArg (fun q : VY.toScheme ⟶ X ↦ q ⁻¹ᵁ U)
      (morphismRestrict_ι f U).symm
  let A := (overEquiv U).functor.obj (M.over U)
  let B := (restrictFunctor U.ι).obj M
  let q := ((overFunctorEquiv U).app M).hom
  let a := ((pullbackPushforwardAdjunction g).unit.app A).val.app (.op W)
    (localModuleSection M U W x)
  let b := ((pullbackPushforwardAdjunction g).unit.app B).val.app (.op W)
    (((restrictAdjunction U.ι).unit.app M).val.app (.op U) x)
  let s := ((pullback g).obj A).presheaf.map (eqToHom hpre).op a
  let e := localPullbackRestrictIso f M U
  let xg := ((pullbackPushforwardAdjunction f).unit.app M).val.app (.op U) x
  have hiso := congrArg
    (fun p ↦ p.val.app (.op ZY) s)
      (localPullbackModuleIso_hom_eqS f M U)
  have hiso' :
      (localPullbackModuleIso f M U).hom.val.app (.op ZY) s =
        ((overFunctorEquiv VY).app ((pullback f).obj M)).inv.val.app (.op ZY)
          (e.hom.val.app (.op ZY)
            (((pullback g).map q).val.app (.op ZY) s)) := by
    calc
      _ = (((pullback g).map q ≫ e.hom ≫
            ((overFunctorEquiv VY).app ((pullback f).obj M)).inv).val.app
              (.op ZY)) s := hiso
      _ = _ := by
        erw [three_comp_app_applyT]
  have hpb := localPullbackUnit_overFunctorT f M U x
  change ((pullback g).map q).val.app (.op (g ⁻¹ᵁ W)) a = b at hpb
  have hnat := PresheafOfModules.naturality_apply
    ((pullback g).map q).val (eqToHom hpre).op a
  have hfirst : ((pullback g).map q).val.app (.op ZY) s =
      ((pullback g).obj B).presheaf.map (eqToHom hpre).op b := by
    change ((pullback g).map q).val.app (.op ZY)
        (((pullback g).obj A).presheaf.map (eqToHom hpre).op a) = _
    calc
      _ = ((pullback g).obj B).presheaf.map (eqToHom hpre).op
          (((pullback g).map q).val.app (.op (g ⁻¹ᵁ W)) a) := hnat
      _ = _ := congrArg
        (fun z ↦ ((pullback g).obj B).presheaf.map
          (eqToHom hpre).op z) hpb
  have hcore := localPullbackRestrictIso_unit_appT f M U x
  change e.hom.val.app (.op ZY)
      (((pullback g).obj B).presheaf.map (eqToHom hpre).op b) =
    ((restrictAdjunction VY.ι).unit.app ((pullback f).obj M)).val.app
      (.op VY) xg at hcore
  have htarget := overFunctorEquiv_inv_restrictUnitT
    ((pullback f).obj M) VY xg
  change ((overFunctorEquiv VY).app ((pullback f).obj M)).inv.val.app
      (.op ZY)
        (((restrictAdjunction VY.ι).unit.app ((pullback f).obj M)).val.app
          (.op VY) xg) =
    localModuleSection ((pullback f).obj M) VY ZY xg at htarget
  rw [hiso', hfirst, hcore, htarget]

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite



namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable def preimageSelfOverIsoT (U : X.Opens) :
    U.overEquivalence.symm.functor.obj (U.ι ⁻¹ᵁ U) ≅
      Over.mk (𝟙 U) :=
  Over.isoMk (eqToIso (by
    change U.ι ''ᵁ (U.ι ⁻¹ᵁ U) = U
    rw [U.ι_preimage_self, U.ι_image_top]))

theorem overMap_terminal_localModuleSectionT (M : X.Modules)
    (U : X.Opens) (x : M.val.obj (.op U)) :
    let Z := U.ι ⁻¹ᵁ U
    let Q := U.overEquivalence.symm.functor.obj Z
    let k : Q ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from Q
    (M.over U).val.map k.op x = localModuleSection M U Z x := by
  dsimp only
  let Z := U.ι ⁻¹ᵁ U
  let Q := U.overEquivalence.symm.functor.obj Z
  let k : Q ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from Q
  let y : ((overEquiv U).functor.obj (M.over U)).val.obj (.op Z) :=
    (M.over U).val.map k.op x
  change y = localModuleSection M U Z x
  let e := (overFunctorEquiv U).app M
  have himage : e.hom.val.app (.op Z) y =
      e.hom.val.app (.op Z) (localModuleSection M U Z x) := by
    rw [overFunctorEquiv_hom_localModuleSection_preimageT]
    change M.val.map k.left.op x =
      M.val.map (homOfLE (U.ι.image_preimage_le U)).op x
    exact M.val.congr_map_apply (Subsingleton.elim _ _) x
  have hback := congrArg (fun z ↦ e.inv.val.app (.op Z) z) himage
  exact (iso_hom_inv_app_applyT e (.op Z) y).symm.trans
    (hback.trans (iso_hom_inv_app_applyT e (.op Z)
      (localModuleSection M U Z x)))

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite



namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

theorem overEquiv_map_localModuleSectionT (M : X.Modules)
    (U : X.Opens)
    (p : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : M.val.obj (.op U)) :
    let Z := U.ι ⁻¹ᵁ U
    let Q := U.overEquivalence.symm.functor.obj Z
    let k : Q ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from Q
    ((overEquiv U).functor.map p).val.app (.op Z)
        (localModuleSection M U Z x) =
      (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)).val.map k.op
        (p.val.app (.op (Over.mk (𝟙 U))) x) := by
  dsimp only
  let Z := U.ι ⁻¹ᵁ U
  let Q := U.overEquivalence.symm.functor.obj Z
  let k : Q ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from Q
  have hsource := overMap_terminal_localModuleSectionT M U x
  change (M.over U).val.map k.op x = localModuleSection M U Z x at hsource
  have happ := overEquiv_map_app_apply U p (.op Z)
    (localModuleSection M U Z x)
  change ((overEquiv U).functor.map p).val.app (.op Z)
      (localModuleSection M U Z x) =
    p.val.app (.op Q) (localModuleSection M U Z x) at happ
  have hnat := PresheafOfModules.naturality_apply p.val k.op x
  rw [happ, ← hsource, hnat]

theorem terminal_apply_eq_of_overEquivT (M : X.Modules)
    (U : X.Opens)
    (p : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : M.val.obj (.op U))
    (y : (X.ringCatSheaf.over U).obj.obj
      (.op (Over.mk (𝟙 U))))
    (h :
      let Z := U.ι ⁻¹ᵁ U
      let Q := U.overEquivalence.symm.functor.obj Z
      let k : Q ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from Q
      ((overEquiv U).functor.map p).val.app (.op Z)
          (localModuleSection M U Z x) =
        (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)).val.map
          k.op y) :
    p.val.app (.op (Over.mk (𝟙 U))) x = y := by
  dsimp only at h
  let Z := U.ι ⁻¹ᵁ U
  let Q := U.overEquivalence.symm.functor.obj Z
  let T : Over U := Over.mk (𝟙 U)
  let k : Q ⟶ T := Over.mkIdTerminal.from Q
  have hsource := overMap_terminal_localModuleSectionT M U x
  change (M.over U).val.map k.op x = localModuleSection M U Z x at hsource
  have happ := overEquiv_map_app_apply U p (.op Z)
    (localModuleSection M U Z x)
  change ((overEquiv U).functor.map p).val.app (.op Z)
      (localModuleSection M U Z x) =
    p.val.app (.op Q) (localModuleSection M U Z x) at happ
  have hnat := PresheafOfModules.naturality_apply p.val k.op x
  have hrestricted :
      (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)).val.map k.op
          (p.val.app (.op T) x) =
        (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)).val.map k.op y := by
    have hnat' := hnat
    rw [hsource, ← happ, h] at hnat'
    exact hnat'.symm
  let e := preimageSelfOverIsoT U
  have hk : k = e.hom := by
    exact CostructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)
  rw [hk] at hrestricted
  change (X.ringCatSheaf.over U).obj.map e.hom.op
      (p.val.app (.op T) x) =
    (X.ringCatSheaf.over U).obj.map e.hom.op y at hrestricted
  change (show (X.ringCatSheaf.over U).obj.obj (.op T) from
    p.val.app (.op T) x) = y
  dsimp only [T] at hrestricted ⊢
  have hback := congrArg
    (fun z ↦ (X.ringCatSheaf.over U).obj.map e.inv.op z) hrestricted
  have hx : (X.ringCatSheaf.over U).obj.map e.inv.op
      ((X.ringCatSheaf.over U).obj.map e.hom.op
        (p.val.app (.op (Over.mk (𝟙 U))) x)) =
      p.val.app (.op (Over.mk (𝟙 U))) x := by
    simpa only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.op_hom,
      Iso.op_inv] using Iso.hom_inv_id_apply
        ((X.ringCatSheaf.over U).obj.mapIso e.op)
        (p.val.app (.op (Over.mk (𝟙 U))) x)
  have hy : (X.ringCatSheaf.over U).obj.map e.inv.op
      ((X.ringCatSheaf.over U).obj.map e.hom.op y) = y := by
    simpa only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.op_hom,
      Iso.op_inv] using Iso.hom_inv_id_apply
        ((X.ringCatSheaf.over U).obj.mapIso e.op) y
  exact Eq.trans hx.symm (Eq.trans hback hy)

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite



namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

theorem pullbackUnit_map_appT (f : Y ⟶ X) {M N : X.Modules}
    (q : M ⟶ N) (U : X.Opens) (x : M.val.obj (.op U)) :
    ((pullback f).map q).val.app (.op (f ⁻¹ᵁ U))
        (((pullbackPushforwardAdjunction f).unit.app M).val.app (.op U) x) =
      ((pullbackPushforwardAdjunction f).unit.app N).val.app (.op U)
        (q.val.app (.op U) x) := by
  have hnat := (pullbackPushforwardAdjunction f).unit.naturality q
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_map] at hnat
  have happ := congrArg (fun r ↦ r.val.app (.op U) x) hnat
  conv_lhs at happ => erw [sheafOfModules_comp_app_apply]
  conv_rhs at happ => erw [sheafOfModules_comp_app_apply]
  exact happ.symm

theorem pullbackUnit_map_transportT (f : Y ⟶ X) {M N : X.Modules}
    (q : M ⟶ N) (U : X.Opens) (V : Y.Opens)
    (hV : V = f ⁻¹ᵁ U) (x : M.val.obj (.op U)) :
    ((pullback f).map q).val.app (.op V)
        (((pullback f).obj M).presheaf.map (eqToHom hV).op
          (((pullbackPushforwardAdjunction f).unit.app M).val.app (.op U) x)) =
      ((pullback f).obj N).presheaf.map (eqToHom hV).op
        (((pullbackPushforwardAdjunction f).unit.app N).val.app (.op U)
          (q.val.app (.op U) x)) := by
  have hnat := PresheafOfModules.naturality_apply
    ((pullback f).map q).val (eqToHom hV).op
      (((pullbackPushforwardAdjunction f).unit.app M).val.app (.op U) x)
  have hunit := pullbackUnit_map_appT f q U x
  calc
    _ = ((pullback f).obj N).presheaf.map (eqToHom hV).op
        (((pullback f).map q).val.app (.op (f ⁻¹ᵁ U))
          (((pullbackPushforwardAdjunction f).unit.app M).val.app
            (.op U) x)) := hnat
    _ = _ := congrArg
      (fun z ↦ ((pullback f).obj N).presheaf.map (eqToHom hV).op z) hunit

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite



namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

theorem pullbackUnitIso_hom_unit_oneT (f : Y ⟶ X) :
    (pullbackUnitIso f).hom.val.app (.op (f ⁻¹ᵁ (⊤ : X.Opens)))
        (((pullbackPushforwardAdjunction f).unit.app (unitObj X)).val.app
          (.op (⊤ : X.Opens))
            (show X.presheaf.obj (.op (⊤ : X.Opens)) from 1)) =
      (show Y.presheaf.obj (.op (f ⁻¹ᵁ (⊤ : X.Opens))) from 1) := by
  have hunit := pullback_unit_unit_app_top_apply_oneT f
  have h := congrArg (fun z ↦
    (pullbackUnitIso f).hom.val.app (.op (f ⁻¹ᵁ (⊤ : X.Opens))) z) hunit
  have hcancel :
      (pullbackUnitIso f).hom.val.app (.op (f ⁻¹ᵁ (⊤ : X.Opens)))
          ((pullbackUnitIso f).inv.val.app
            (.op (f ⁻¹ᵁ (⊤ : X.Opens)))
              ((f.app (⊤ : X.Opens)).hom
                (show X.presheaf.obj (.op (⊤ : X.Opens)) from 1))) =
        (f.app (⊤ : X.Opens)).hom
          (show X.presheaf.obj (.op (⊤ : X.Opens)) from 1) :=
    iso_inv_hom_app_applyT (pullbackUnitIso f)
      (.op (f ⁻¹ᵁ (⊤ : X.Opens))) _
  have hfinal := Eq.trans h hcancel
  simpa only [map_one] using hfinal

theorem pullbackUnit_one_transport_topT (f : Y ⟶ X)
    (U : X.Opens) (V : Y.Opens) (hU : U = ⊤)
    (hV : V = f ⁻¹ᵁ U) :
    ((pullback f).obj (unitObj X)).presheaf.map (eqToHom hV).op
        (((pullbackPushforwardAdjunction f).unit.app (unitObj X)).val.app
          (.op U) (show X.presheaf.obj (.op U) from 1)) =
      ((pullback f).obj (unitObj X)).presheaf.map
        (eqToHom (hV.trans (congrArg (fun W ↦ f ⁻¹ᵁ W) hU))).op
          (((pullbackPushforwardAdjunction f).unit.app (unitObj X)).val.app
            (.op ⊤) (show X.presheaf.obj (.op ⊤) from 1)) := by
  subst U
  rfl

end AlgebraicGeometry.Scheme.Modules
