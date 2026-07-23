import ModularCurves.Picard.DualPullback.Iso

/-!
# Naturality of dual pullback on the unit module

This file proves that the dual-pullback comparison respects the canonical self-duality of the
structure sheaf. The proof reduces the comparison to the section `1` on the terminal open and
then computes it through the existing local pullback trivialization.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

private theorem overEquiv_map_id_localUnitSectionT
    (U : X.Opens) :
    let W := U.ι ⁻¹ᵁ U
    let Q := U.overEquivalence.symm.functor.obj W
    let k : Q ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from Q
    ((overEquiv U).functor.map
        (𝟙 ((unitObj X).over U))).val.app (.op W)
          (localModuleSection (unitObj X) U W
            (show X.presheaf.obj (.op U) from 1)) =
      (_root_.SheafOfModules.unit
        (X.ringCatSheaf.over U)).val.map k.op
          (show (X.ringCatSheaf.over U).obj.obj
            (.op (Over.mk (𝟙 U))) from 1) := by
  dsimp only
  let W := U.ι ⁻¹ᵁ U
  let Q := U.overEquivalence.symm.functor.obj W
  let k : Q ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from Q
  let oneU : X.presheaf.obj (.op U) := 1
  have h := overEquiv_map_localModuleSectionT (unitObj X) U
    (𝟙 ((unitObj X).over U)) oneU
  change ((overEquiv U).functor.map
      (𝟙 ((unitObj X).over U))).val.app (.op W)
        (localModuleSection (unitObj X) U W oneU) =
    (_root_.SheafOfModules.unit
      (X.ringCatSheaf.over U)).val.map k.op
        ((𝟙 ((unitObj X).over U) :
          (unitObj X).over U ⟶ (unitObj X).over U).val.app
            (.op (Over.mk (𝟙 U))) oneU) at h
  have hid :
      ((𝟙 ((unitObj X).over U) :
        (unitObj X).over U ⟶ (unitObj X).over U).val.app
          (.op (Over.mk (𝟙 U))) oneU) =
        (show (X.ringCatSheaf.over U).obj.obj
          (.op (Over.mk (𝟙 U))) from 1) := by
    rfl
  rw [hid] at h
  exact h


private theorem localUnitMiddle_pulledOneT
    (f : Y ⟶ X) (U : X.Opens) :
    let W := U.ι ⁻¹ᵁ U
    let g := f ∣_ U
    let V := f ⁻¹ᵁ U
    let Z := V.ι ⁻¹ᵁ V
    let hpre : Z = g ⁻¹ᵁ W := by
      change (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
        (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U)
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
      exact congrArg (fun q : V.toScheme ⟶ X ↦ q ⁻¹ᵁ U)
        (morphismRestrict_ι f U).symm
    let QX := U.overEquivalence.symm.functor.obj W
    let kX : QX ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from QX
    let M := unitObj X
    let N := (pullback f).obj M
    let oneX : X.presheaf.obj (.op U) := 1
    let xg := ((pullbackPushforwardAdjunction f).unit.app M).val.app
      (.op U) oneX
    let O := (overEquiv U).functor.obj
      (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    let q := (overEquiv U).functor.map (𝟙 (M.over U))
    let r := (_root_.SheafOfModules.unit
      (X.ringCatSheaf.over U)).val.map kX.op
        (show (X.ringCatSheaf.over U).obj.obj
          (.op (Over.mk (𝟙 U))) from 1)
    let t := ((pullback g).obj O).presheaf.map (eqToHom hpre).op
      (((pullbackPushforwardAdjunction g).unit.app O).val.app (.op W) r)
    ((pullback g).map q).val.app (.op Z)
        ((localPullbackModuleIso f M U).inv.val.app (.op Z)
          (localModuleSection N V Z xg)) = t := by
  dsimp only
  let W := U.ι ⁻¹ᵁ U
  let g := f ∣_ U
  let V := f ⁻¹ᵁ U
  let Z := V.ι ⁻¹ᵁ V
  let hpre : Z = g ⁻¹ᵁ W := by
    change (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
      (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
    exact congrArg (fun q : V.toScheme ⟶ X ↦ q ⁻¹ᵁ U)
      (morphismRestrict_ι f U).symm
  let QX := U.overEquivalence.symm.functor.obj W
  let kX : QX ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from QX
  let M := unitObj X
  let N := (pullback f).obj M
  let oneX : X.presheaf.obj (.op U) := 1
  let xg := ((pullbackPushforwardAdjunction f).unit.app M).val.app
    (.op U) oneX
  let A := (overEquiv U).functor.obj (M.over U)
  let O := (overEquiv U).functor.obj
    (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))
  let q := (overEquiv U).functor.map (𝟙 (M.over U))
  let sourceLocal := localModuleSection M U W oneX
  let sourcePulled := ((pullback g).obj A).presheaf.map
    (eqToHom hpre).op
      (((pullbackPushforwardAdjunction g).unit.app A).val.app
        (.op W) sourceLocal)
  let r := (_root_.SheafOfModules.unit
    (X.ringCatSheaf.over U)).val.map kX.op
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1)
  let t := ((pullback g).obj O).presheaf.map (eqToHom hpre).op
    (((pullbackPushforwardAdjunction g).unit.app O).val.app (.op W) r)
  have hinv := localPullbackModuleIso_inv_pulledSectionT f M U oneX
  change (localPullbackModuleIso f M U).inv.val.app (.op Z)
      (localModuleSection N V Z xg) = sourcePulled at hinv
  have hqr := overEquiv_map_id_localUnitSectionT U
  change q.val.app (.op W) sourceLocal = r at hqr
  have hpull := pullbackUnit_map_transportT g q W Z hpre sourceLocal
  change ((pullback g).map q).val.app (.op Z) sourcePulled =
    ((pullback g).obj O).presheaf.map (eqToHom hpre).op
      (((pullbackPushforwardAdjunction g).unit.app O).val.app (.op W)
        (q.val.app (.op W) sourceLocal)) at hpull
  rw [hinv, hpull, hqr]


private theorem localUnitTail_pulledOneT
    (f : Y ⟶ X) (U : X.Opens) :
    let W := U.ι ⁻¹ᵁ U
    let g := f ∣_ U
    let V := f ⁻¹ᵁ U
    let Z := V.ι ⁻¹ᵁ V
    let hpre : Z = g ⁻¹ᵁ W := by
      change (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
        (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U)
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
      exact congrArg (fun q : V.toScheme ⟶ X ↦ q ⁻¹ᵁ U)
        (morphismRestrict_ι f U).symm
    let QX := U.overEquivalence.symm.functor.obj W
    let kX : QX ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from QX
    let QY := V.overEquivalence.symm.functor.obj Z
    let kY : QY ⟶ Over.mk (𝟙 V) := Over.mkIdTerminal.from QY
    let O := (overEquiv U).functor.obj
      (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    let r := (_root_.SheafOfModules.unit
      (X.ringCatSheaf.over U)).val.map kX.op
        (show (X.ringCatSheaf.over U).obj.obj
          (.op (Over.mk (𝟙 U))) from 1)
    let t := ((pullback g).obj O).presheaf.map (eqToHom hpre).op
      (((pullbackPushforwardAdjunction g).unit.app O).val.app (.op W) r)
    (localPullbackUnitIso f U).hom.val.app (.op Z) t =
      (_root_.SheafOfModules.unit
        (Y.ringCatSheaf.over V)).val.map kY.op
          (show (Y.ringCatSheaf.over V).obj.obj
            (.op (Over.mk (𝟙 V))) from 1) := by
  dsimp only
  let W := U.ι ⁻¹ᵁ U
  let g := f ∣_ U
  let V := f ⁻¹ᵁ U
  let Z := V.ι ⁻¹ᵁ V
  let hpre : Z = g ⁻¹ᵁ W := by
    change (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
      (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
    exact congrArg (fun q : V.toScheme ⟶ X ↦ q ⁻¹ᵁ U)
      (morphismRestrict_ι f U).symm
  let QX := U.overEquivalence.symm.functor.obj W
  let kX : QX ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from QX
  let QY := V.overEquivalence.symm.functor.obj Z
  let kY : QY ⟶ Over.mk (𝟙 V) := Over.mkIdTerminal.from QY
  let O := (overEquiv U).functor.obj
    (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))
  let r := (_root_.SheafOfModules.unit
    (X.ringCatSheaf.over U)).val.map kX.op
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1)
  let t := ((pullback g).obj O).presheaf.map (eqToHom hpre).op
    (((pullbackPushforwardAdjunction g).unit.app O).val.app (.op W) r)
  let oneLocal := (_root_.SheafOfModules.unit
    (Y.ringCatSheaf.over V)).val.map kY.op
      (show (Y.ringCatSheaf.over V).obj.obj
        (.op (Over.mk (𝟙 V))) from 1)
  have ht := localOverUnit_pulled_one_eqT f U
  change t = ((pullback g).obj (unitObj U.toScheme)).presheaf.map
      (eqToHom hpre).op
        (((pullbackPushforwardAdjunction g).unit.app
          (unitObj U.toScheme)).val.app (.op W)
            (show U.toScheme.presheaf.obj (.op W) from 1)) at ht
  have hunit := localPullbackUnitIso_hom_pulled_oneT f U
  change (localPullbackUnitIso f U).hom.val.app (.op Z)
      (((pullback g).obj (unitObj U.toScheme)).presheaf.map
        (eqToHom hpre).op
          (((pullbackPushforwardAdjunction g).unit.app
            (unitObj U.toScheme)).val.app (.op W)
              (show U.toScheme.presheaf.obj (.op W) from 1))) =
    oneLocal at hunit
  have htApplied : (localPullbackUnitIso f U).hom.val.app (.op Z) t =
      (localPullbackUnitIso f U).hom.val.app (.op Z)
        (((pullback g).obj (unitObj U.toScheme)).presheaf.map
          (eqToHom hpre).op
            (((pullbackPushforwardAdjunction g).unit.app
              (unitObj U.toScheme)).val.app (.op W)
                (show U.toScheme.presheaf.obj (.op W) from 1))) :=
    congrArg (fun z ↦
      (localPullbackUnitIso f U).hom.val.app (.op Z) z) ht
  exact htApplied.trans hunit


private theorem localPullbackTrivialization_unit_hom_pulled_one_coreT
    (f : Y ⟶ X)
    (p : ((pullback f).obj (unitObj X)).over
        (f ⁻¹ᵁ (⊤ : X.Opens)) ≅
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (f ⁻¹ᵁ (⊤ : X.Opens))))
    (hp : (overEquiv (f ⁻¹ᵁ (⊤ : X.Opens))).functor.map p.hom =
      (localPullbackModuleIso f (unitObj X) (⊤ : X.Opens)).inv ≫
        (pullback (f ∣_ (⊤ : X.Opens))).map
          ((overEquiv (⊤ : X.Opens)).functor.map
            (𝟙 ((unitObj X).over (⊤ : X.Opens)))) ≫
        (localPullbackUnitIso f (⊤ : X.Opens)).hom) :
    p.hom.val.app
        (.op (Over.mk (𝟙 (f ⁻¹ᵁ (⊤ : X.Opens)))))
          (((pullbackPushforwardAdjunction f).unit.app (unitObj X)).val.app
            (.op (⊤ : X.Opens))
              (show X.presheaf.obj (.op (⊤ : X.Opens)) from 1)) =
      (show (Y.ringCatSheaf.over (f ⁻¹ᵁ (⊤ : X.Opens))).obj.obj
        (.op (Over.mk (𝟙 (f ⁻¹ᵁ (⊤ : X.Opens))))) from 1) := by
  let U := (⊤ : X.Opens)
  let V := f ⁻¹ᵁ U
  let M := unitObj X
  let N := (pullback f).obj M
  let oneX : X.presheaf.obj (.op U) := 1
  let xg := ((pullbackPushforwardAdjunction f).unit.app M).val.app
    (.op U) oneX
  refine terminal_apply_eq_of_overEquivT (X := Y) N V p.hom xg
    (show (Y.ringCatSheaf.over V).obj.obj
      (.op (Over.mk (𝟙 V))) from 1) ?_
  let W := U.ι ⁻¹ᵁ U
  let g := f ∣_ U
  let Z := V.ι ⁻¹ᵁ V
  let hpre : Z = g ⁻¹ᵁ W := by
    change (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
      (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
    exact congrArg (fun q : V.toScheme ⟶ X ↦ q ⁻¹ᵁ U)
      (morphismRestrict_ι f U).symm
  let QX := U.overEquivalence.symm.functor.obj W
  let kX : QX ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from QX
  let QY := V.overEquivalence.symm.functor.obj Z
  let kY : QY ⟶ Over.mk (𝟙 V) := Over.mkIdTerminal.from QY
  let O := (overEquiv U).functor.obj
    (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))
  let q := (overEquiv U).functor.map (𝟙 (M.over U))
  let a := (localPullbackModuleIso f M U).inv
  let b := (pullback g).map q
  let c := (localPullbackUnitIso f U).hom
  let F := (overEquiv V).functor.map p.hom
  let xLocal := localModuleSection N V Z xg
  let r := (_root_.SheafOfModules.unit
    (X.ringCatSheaf.over U)).val.map kX.op
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1)
  let t := ((pullback g).obj O).presheaf.map (eqToHom hpre).op
    (((pullbackPushforwardAdjunction g).unit.app O).val.app (.op W) r)
  let oneLocal := (_root_.SheafOfModules.unit
    (Y.ringCatSheaf.over V)).val.map kY.op
      (show (Y.ringCatSheaf.over V).obj.obj
        (.op (Over.mk (𝟙 V))) from 1)
  change F = a ≫ b ≫ c at hp
  have hmiddle := localUnitMiddle_pulledOneT f U
  change b.val.app (.op Z) (a.val.app (.op Z) xLocal) = t at hmiddle
  have htail := localUnitTail_pulledOneT f U
  change c.val.app (.op Z) t = oneLocal at htail
  exact app_eq_of_eq_three_compT F a b c hp (.op Z) xLocal t
    oneLocal hmiddle htail

private theorem localPullbackTrivialization_unit_hom_pulled_oneT
    (f : Y ⟶ X) :
    (localPullbackTrivializationT f (unitObj X) (⊤ : X.Opens)
      (Iso.refl _)).hom.val.app
        (.op (Over.mk (𝟙 (f ⁻¹ᵁ (⊤ : X.Opens)))))
          (((pullbackPushforwardAdjunction f).unit.app (unitObj X)).val.app
            (.op (⊤ : X.Opens))
              (show X.presheaf.obj (.op (⊤ : X.Opens)) from 1)) =
      (show (Y.ringCatSheaf.over (f ⁻¹ᵁ (⊤ : X.Opens))).obj.obj
        (.op (Over.mk (𝟙 (f ⁻¹ᵁ (⊤ : X.Opens))))) from 1) := by
  let p := localPullbackTrivializationT f (unitObj X)
    (⊤ : X.Opens) (Iso.refl _)
  apply localPullbackTrivialization_unit_hom_pulled_one_coreT f p
  dsimp only [p, localPullbackTrivializationT]
  simp only [Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom,
    Functor.mapIso_hom]
  rfl


private theorem pullbackUnitIso_inv_over_terminal_oneT (f : Y ⟶ X) :
    ((pullbackUnitIso f).inv.over (f ⁻¹ᵁ (⊤ : X.Opens))).val.app
        (.op (Over.mk (𝟙 (f ⁻¹ᵁ (⊤ : X.Opens)))))
          (show (Y.ringCatSheaf.over (f ⁻¹ᵁ (⊤ : X.Opens))).obj.obj
            (.op (Over.mk (𝟙 (f ⁻¹ᵁ (⊤ : X.Opens))))) from 1) =
      ((pullbackPushforwardAdjunction f).unit.app (unitObj X)).val.app
        (.op (⊤ : X.Opens))
          (show X.presheaf.obj (.op (⊤ : X.Opens)) from 1) := by
  let V := f ⁻¹ᵁ (⊤ : X.Opens)
  change (pullbackUnitIso f).inv.val.app (.op V)
      (show Y.presheaf.obj (.op V) from 1) = _
  rw [pullback_unit_unit_app_top_apply_oneT]
  rw [map_one]

private theorem pullbackUnitIso_inv_over_localTrivialization_terminal_oneT
    (f : Y ⟶ X) :
    (localPullbackTrivializationT f (unitObj X) (⊤ : X.Opens)
      (Iso.refl _)).hom.val.app
      (.op (Over.mk (𝟙 (f ⁻¹ᵁ (⊤ : X.Opens)))))
        (((pullbackUnitIso f).inv.over
          (f ⁻¹ᵁ (⊤ : X.Opens))).val.app
            (.op (Over.mk (𝟙 (f ⁻¹ᵁ (⊤ : X.Opens)))))
              (show (Y.ringCatSheaf.over
                (f ⁻¹ᵁ (⊤ : X.Opens))).obj.obj
                  (.op (Over.mk
                    (𝟙 (f ⁻¹ᵁ (⊤ : X.Opens))))) from 1)) =
      (show (Y.ringCatSheaf.over (f ⁻¹ᵁ (⊤ : X.Opens))).obj.obj
        (.op (Over.mk (𝟙 (f ⁻¹ᵁ (⊤ : X.Opens))))) from 1) := by
  have hunit := pullbackUnitIso_inv_over_terminal_oneT f
  have htriv := localPullbackTrivialization_unit_hom_pulled_oneT f
  have hunitApplied := congrArg (fun z ↦
    (localPullbackTrivializationT f (unitObj X) (⊤ : X.Opens)
      (Iso.refl _)).hom.val.app
        (.op (Over.mk (𝟙 (f ⁻¹ᵁ (⊤ : X.Opens))))) z) hunit
  exact hunitApplied.trans htriv

private theorem unitEnd_comp_eq_id_of_terminal_oneT
    (V : Y.Opens)
    {M : _root_.SheafOfModules (Y.ringCatSheaf.over V)}
    (a : _root_.SheafOfModules.unit (Y.ringCatSheaf.over V) ⟶ M)
    (b : M ⟶
      _root_.SheafOfModules.unit (Y.ringCatSheaf.over V))
    (h : b.val.app (.op (Over.mk (𝟙 V)))
        (a.val.app (.op (Over.mk (𝟙 V)))
          (show (Y.ringCatSheaf.over V).obj.obj
            (.op (Over.mk (𝟙 V))) from 1)) =
      (show (Y.ringCatSheaf.over V).obj.obj
        (.op (Over.mk (𝟙 V))) from 1)) :
    a ≫ b = 𝟙 _ := by
  apply unitEnd_eq_id_of_terminal_oneT Y.ringCatSheaf V
  erw [sheafOfModules_comp_app_apply]
  exact h

private theorem pullbackUnitIso_inv_over_comp_coreT
    (f : Y ⟶ X)
    (p : ((pullback f).obj (unitObj X)).over
        (f ⁻¹ᵁ (⊤ : X.Opens)) ≅
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (f ⁻¹ᵁ (⊤ : X.Opens))))
    (h : p.hom.val.app
        (.op (Over.mk (𝟙 (f ⁻¹ᵁ (⊤ : X.Opens)))))
          (((pullbackUnitIso f).inv.over
            (f ⁻¹ᵁ (⊤ : X.Opens))).val.app
              (.op (Over.mk (𝟙 (f ⁻¹ᵁ (⊤ : X.Opens)))))
                (show (Y.ringCatSheaf.over
                  (f ⁻¹ᵁ (⊤ : X.Opens))).obj.obj
                    (.op (Over.mk
                      (𝟙 (f ⁻¹ᵁ (⊤ : X.Opens))))) from 1)) =
        (show (Y.ringCatSheaf.over
          (f ⁻¹ᵁ (⊤ : X.Opens))).obj.obj
            (.op (Over.mk (𝟙 (f ⁻¹ᵁ (⊤ : X.Opens))))) from 1)) :
    (pullbackUnitIso f).inv.over (f ⁻¹ᵁ (⊤ : X.Opens)) ≫
        p.hom =
      𝟙 _ := by
  exact unitEnd_comp_eq_id_of_terminal_oneT
    (f ⁻¹ᵁ (⊤ : X.Opens))
      ((pullbackUnitIso f).inv.over (f ⁻¹ᵁ (⊤ : X.Opens)))
      p.hom h

private theorem pullbackUnitIso_inv_over_comp_localTrivializationT
    (f : Y ⟶ X) :
    (pullbackUnitIso f).inv.over (f ⁻¹ᵁ (⊤ : X.Opens)) ≫
        (localPullbackTrivializationT f (unitObj X) ⊤
          (Iso.refl _)).hom =
      𝟙 _ := by
  let p := localPullbackTrivializationT f (unitObj X)
    (⊤ : X.Opens) (Iso.refl _)
  apply pullbackUnitIso_inv_over_comp_coreT f p
  exact pullbackUnitIso_inv_over_localTrivialization_terminal_oneT f


private theorem dualUnitObjIso_inv_app_oneT (U : X.Opens) :
    (dualUnitObjIso (X := X)).inv.val.app (.op U)
        (show X.presheaf.obj (.op U) from 1) =
      𝟙 (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)) := by
  change (ModularCurves.SheafOfModules.dualUnitLinearEquiv
    X.ringCatSheaf U).symm 1 = _
  change ModularCurves.SheafOfModules.overUnitScalarEnd
    X.ringCatSheaf U 1 = _
  exact map_one (ModularCurves.SheafOfModules.overUnitScalarEndRingHom
    X.ringCatSheaf U)

private theorem unit_hom_ext_top_one {M : X.Modules}
    {p q : unitObj X ⟶ M}
    (h : p.app ⊤ (show X.presheaf.obj (.op ⊤) from 1) =
      q.app ⊤ (show X.presheaf.obj (.op ⊤) from 1)) : p = q := by
  apply M.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  let i : (.op (⊤ : X.Opens)) ⟶ U :=
    (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op
  rw [← PresheafOfModules.sections_property (M.unitHomEquiv p) i]
  rw [← PresheafOfModules.sections_property (M.unitHomEquiv q) i]
  congr 1

theorem dualPullbackHom_unit_naturality (f : Y ⟶ X) :
    (pullback f).map (dualUnitObjIso (X := X)).inv ≫
        dualPullbackHom f (unitObj X) ≫
        dualMapObj (pullbackUnitIso f).inv =
      (pullbackUnitIso f).hom ≫ (dualUnitObjIso (X := Y)).inv := by
  apply (cancel_epi (pullbackUnitIso f).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply unit_hom_ext_top_one
  change (((pullbackUnitIso f).inv ≫
      (pullback f).map (dualUnitObjIso (X := X)).inv ≫
      dualPullbackHom f (unitObj X) ≫
      dualMapObj (pullbackUnitIso f).inv).val.app (.op ⊤))
        (show Y.presheaf.obj (.op ⊤) from 1) =
    ((dualUnitObjIso (X := Y)).inv.val.app (.op ⊤)
      (show Y.presheaf.obj (.op ⊤) from 1))
  erw [sheafOfModules_comp_app_apply]
  erw [sheafOfModules_comp_app_apply]
  erw [sheafOfModules_comp_app_apply]
  let V := f ⁻¹ᵁ (⊤ : X.Opens)
  let oneX : X.presheaf.obj (.op (⊤ : X.Opens)) := 1
  let oneY : Y.presheaf.obj (.op V) := 1
  let alpha : (unitObj X).over (⊤ : X.Opens) ⟶
      _root_.SheafOfModules.unit
        (X.ringCatSheaf.over (⊤ : X.Opens)) := 𝟙 _
  let p := localPullbackTrivializationT f (unitObj X)
    (⊤ : X.Opens) (Iso.refl _)
  have hunit : (pullbackUnitIso f).inv.val.app (.op V) oneY =
      ((pullbackPushforwardAdjunction f).unit.app (unitObj X)).val.app
        (.op (⊤ : X.Opens)) oneX := by
    dsimp only [V, oneX, oneY]
    exact pullbackUnitIso_inv_over_terminal_oneT f
  have hdualX : (dualUnitObjIso (X := X)).inv.val.app
      (.op (⊤ : X.Opens)) oneX = alpha := by
    dsimp only [oneX, alpha]
    exact dualUnitObjIso_inv_app_oneT (X := X) (⊤ : X.Opens)
  have hpull := pullbackUnit_map_appT f
    (dualUnitObjIso (X := X)).inv (⊤ : X.Opens) oneX
  have hstageOne :
      ((pullback f).map (dualUnitObjIso (X := X)).inv).val.app (.op V)
          ((pullbackUnitIso f).inv.val.app (.op V) oneY) =
        ((pullbackPushforwardAdjunction f).unit.app
          (dualObj (unitObj X))).val.app (.op (⊤ : X.Opens)) alpha := by
    have hunitApplied := congrArg (fun z ↦
      ((pullback f).map (dualUnitObjIso (X := X)).inv).val.app
        (.op V) z) hunit
    have hdualApplied := congrArg (fun z ↦
      ((pullbackPushforwardAdjunction f).unit.app
        (dualObj (unitObj X))).val.app (.op (⊤ : X.Opens)) z) hdualX
    exact hunitApplied.trans (hpull.trans hdualApplied)
  have hdual := dualPullbackHom_unit_appT f (unitObj X)
    (⊤ : X.Opens) alpha
  have hlocal := localDualPullback_trivialization_homT f
    (unitObj X) (⊤ : X.Opens) (Iso.refl _)
  have hp : localDualPullback f (unitObj X) (⊤ : X.Opens) alpha =
      p.hom := by
    dsimp only [alpha, p]
    exact hlocal
  have hstageTwo :
      (dualPullbackHom f (unitObj X)).val.app (.op V)
          (((pullback f).map
            (dualUnitObjIso (X := X)).inv).val.app (.op V)
              ((pullbackUnitIso f).inv.val.app (.op V) oneY)) =
        p.hom := by
    have hstageOneApplied := congrArg (fun z ↦
      (dualPullbackHom f (unitObj X)).val.app (.op V) z) hstageOne
    exact hstageOneApplied.trans (hdual.trans hp)
  have hcomp := pullbackUnitIso_inv_over_comp_localTrivializationT f
  have hmap : (dualMapObj (pullbackUnitIso f).inv).val.app (.op V)
      p.hom = 𝟙 _ := by
    change (pullbackUnitIso f).inv.over V ≫ p.hom = 𝟙 _
    dsimp only [V, p]
    exact hcomp
  have hdualY : (dualUnitObjIso (X := Y)).inv.val.app (.op V) oneY =
      𝟙 _ := by
    dsimp only [V, oneY]
    exact dualUnitObjIso_inv_app_oneT (X := Y) V
  have hstageTwoApplied := congrArg (fun z ↦
    (dualMapObj (pullbackUnitIso f).inv).val.app (.op V) z) hstageTwo
  exact hstageTwoApplied.trans (hmap.trans hdualY.symm)

end AlgebraicGeometry.Scheme.Modules
