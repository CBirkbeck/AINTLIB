/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.DualPullback.LocalTrivializationInv

/-!
# Pulled local trivializations on a distinguished section, module-generically

The `LocalTrivialization`/`LocalTrivializationInv` chain computes the inverse of a pulled
local trivialization on `1` for the **dual module** with its distinguished section `e.hom`.
This file replays the chain for an **arbitrary module `A`** equipped with an over-site
trivialization `t : A.over U ≅ unit` and an arbitrary section `x` normalised by `t`
(`t.hom x = 1`): the pulled trivialization's inverse sends `1` to the image of `x` under the
pullback–pushforward adjunction unit (`localPullbackTrivialization_inv_one_ofSection`).
Consumed by `RelPicLocal.glueSectionA_compat`, where `A := N` on the base of the family and
the adjunction-unit form makes restriction to overlaps a naturality statement.
-/

universe u v

open AlgebraicGeometry CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

theorem localMiddle_pulledSection_ofSection (f : Y ⟶ X)
    (A : X.Modules) (U : X.Opens)
    (t : A.over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : A.val.obj (.op U))
    (hx : t.hom.val.app (.op (Over.mk (𝟙 U))) x =
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1)) :
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
    let QX := U.overEquivalence.symm.functor.obj W
    let kX : QX ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from QX
    let N := (pullback f).obj A
    let xg := ((pullbackPushforwardAdjunction f).unit.app
      A).val.app (.op U) x
    let O := (overEquiv U).functor.obj
      (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    let q := (overEquiv U).functor.map t.hom
    let r := (_root_.SheafOfModules.unit
      (X.ringCatSheaf.over U)).val.map kX.op
        (show (X.ringCatSheaf.over U).obj.obj
          (.op (Over.mk (𝟙 U))) from 1)
    let s := ((pullback g).obj O).presheaf.map (eqToHom hpre).op
      (((pullbackPushforwardAdjunction g).unit.app O).val.app (.op W) r)
    ((pullback g).map q).val.app (.op ZY)
        ((localPullbackModuleIso f A U).inv.val.app (.op ZY)
          (localModuleSection N VY ZY xg)) = s := by
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
  let QX := U.overEquivalence.symm.functor.obj W
  let kX : QX ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from QX
  let N := (pullback f).obj A
  let xg := ((pullbackPushforwardAdjunction f).unit.app
    A).val.app (.op U) x
  let O := (overEquiv U).functor.obj
    (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))
  let q := (overEquiv U).functor.map t.hom
  let r := (_root_.SheafOfModules.unit
    (X.ringCatSheaf.over U)).val.map kX.op
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1)
  have hinv := localPullbackModuleIso_inv_pulledSectionT f A U x
  change (localPullbackModuleIso f A U).inv.val.app
      (.op ZY) (localModuleSection N VY ZY xg) =
    ((pullback g).obj ((overEquiv U).functor.obj (A.over U))).presheaf.map
      (eqToHom hpre).op
        (((pullbackPushforwardAdjunction g).unit.app
          ((overEquiv U).functor.obj (A.over U))).val.app
            (.op W) (localModuleSection A U W x)) at hinv
  have hq := overEquiv_map_localModuleSectionT A U t.hom x
  change q.val.app (.op W) (localModuleSection A U W x) =
    (_root_.SheafOfModules.unit
      (X.ringCatSheaf.over U)).val.map kX.op
        (t.hom.val.app (.op (Over.mk (𝟙 U))) x) at hq
  have hqr : q.val.app (.op W)
      (localModuleSection A U W x) = r := by
    rw [hq, hx]
  have hpull := pullbackUnit_map_transportT g q W ZY hpre
    (localModuleSection A U W x)
  change ((pullback g).map q).val.app (.op ZY)
      (((pullback g).obj ((overEquiv U).functor.obj (A.over U))).presheaf.map
        (eqToHom hpre).op
          (((pullbackPushforwardAdjunction g).unit.app
            ((overEquiv U).functor.obj (A.over U))).val.app
              (.op W) (localModuleSection A U W x))) =
    ((pullback g).obj O).presheaf.map (eqToHom hpre).op
      (((pullbackPushforwardAdjunction g).unit.app O).val.app (.op W)
        (q.val.app (.op W)
          (localModuleSection A U W x))) at hpull
  rw [hinv, hpull, hqr]

theorem localTrivialization_overEquiv_pulledSection_ofSection
    (f : Y ⟶ X) (A : X.Modules) (U : X.Opens)
    (t : A.over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : A.val.obj (.op U))
    (p : ((pullback f).obj A).over (f ⁻¹ᵁ U) ≅
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (f ⁻¹ᵁ U)))
    (hx : t.hom.val.app (.op (Over.mk (𝟙 U))) x =
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1))
    (hp : (overEquiv (f ⁻¹ᵁ U)).functor.map p.hom =
      (localPullbackModuleIso f A U).inv ≫
        (pullback (f ∣_ U)).map
          ((overEquiv U).functor.map t.hom) ≫
        (localPullbackUnitIso f U).hom) :
    let VY := f ⁻¹ᵁ U
    let ZY := VY.ι ⁻¹ᵁ VY
    let QY := VY.overEquivalence.symm.functor.obj ZY
    let kY : QY ⟶ Over.mk (𝟙 VY) := Over.mkIdTerminal.from QY
    let N := (pullback f).obj A
    let xg := ((pullbackPushforwardAdjunction f).unit.app
      A).val.app (.op U) x
    ((overEquiv VY).functor.map p.hom).val.app (.op ZY)
        (localModuleSection N VY ZY xg) =
      (_root_.SheafOfModules.unit
        (Y.ringCatSheaf.over VY)).val.map kY.op
          (show (Y.ringCatSheaf.over VY).obj.obj
            (.op (Over.mk (𝟙 VY))) from 1) := by
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
  let QX := U.overEquivalence.symm.functor.obj W
  let kX : QX ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from QX
  let QY := VY.overEquivalence.symm.functor.obj ZY
  let kY : QY ⟶ Over.mk (𝟙 VY) := Over.mkIdTerminal.from QY
  let N := (pullback f).obj A
  let xg := ((pullbackPushforwardAdjunction f).unit.app
    A).val.app (.op U) x
  let O := (overEquiv U).functor.obj
    (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))
  let q := (overEquiv U).functor.map t.hom
  let r := (_root_.SheafOfModules.unit
    (X.ringCatSheaf.over U)).val.map kX.op
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1)
  let s := ((pullback g).obj O).presheaf.map (eqToHom hpre).op
    (((pullbackPushforwardAdjunction g).unit.app O).val.app (.op W) r)
  have hmiddle := localMiddle_pulledSection_ofSection f A U t x hx
  change ((pullback g).map q).val.app (.op ZY)
      ((localPullbackModuleIso f A U).inv.val.app (.op ZY)
        (localModuleSection N VY ZY xg)) = s at hmiddle
  have ht := localOverUnit_pulled_one_eqT f U
  change s = ((pullback g).obj (unitObj U.toScheme)).presheaf.map
      (eqToHom hpre).op
        (((pullbackPushforwardAdjunction g).unit.app
          (unitObj U.toScheme)).val.app (.op W)
            (show U.toScheme.presheaf.obj (.op W) from 1)) at ht
  have hunit := localPullbackUnitIso_hom_pulled_oneT f U
  change (localPullbackUnitIso f U).hom.val.app (.op ZY)
      (((pullback g).obj (unitObj U.toScheme)).presheaf.map
        (eqToHom hpre).op
          (((pullbackPushforwardAdjunction g).unit.app
            (unitObj U.toScheme)).val.app (.op W)
              (show U.toScheme.presheaf.obj (.op W) from 1))) =
    (_root_.SheafOfModules.unit
      (Y.ringCatSheaf.over VY)).val.map kY.op
        (show (Y.ringCatSheaf.over VY).obj.obj
          (.op (Over.mk (𝟙 VY))) from 1) at hunit
  let F := (overEquiv VY).functor.map p.hom
  let a := (localPullbackModuleIso f A U).inv
  let b := (pullback g).map q
  let c := (localPullbackUnitIso f U).hom
  let y := localModuleSection N VY ZY xg
  let w := (_root_.SheafOfModules.unit
    (Y.ringCatSheaf.over VY)).val.map kY.op
      (show (Y.ringCatSheaf.over VY).obj.obj
        (.op (Over.mk (𝟙 VY))) from 1)
  have htail : c.val.app (.op ZY) s = w := by
    have htApplied : c.val.app (.op ZY) s =
        c.val.app (.op ZY)
          (((pullback g).obj (unitObj U.toScheme)).presheaf.map
            (eqToHom hpre).op
              (((pullbackPushforwardAdjunction g).unit.app
                (unitObj U.toScheme)).val.app (.op W)
                  (show U.toScheme.presheaf.obj (.op W) from 1))) :=
      congrArg (fun z ↦ c.val.app (.op ZY) z) ht
    exact Eq.trans htApplied hunit
  exact app_eq_of_eq_three_compT F a b c hp (.op ZY) y s w hmiddle htail

theorem localPullbackTrivialization_hom_unit_ofSection (f : Y ⟶ X)
    (A : X.Modules) (U : X.Opens)
    (t : A.over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : A.val.obj (.op U))
    (p : ((pullback f).obj A).over (f ⁻¹ᵁ U) ≅
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (f ⁻¹ᵁ U)))
    (hx : t.hom.val.app (.op (Over.mk (𝟙 U))) x =
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1))
    (hp : (overEquiv (f ⁻¹ᵁ U)).functor.map p.hom =
      (localPullbackModuleIso f A U).inv ≫
        (pullback (f ∣_ U)).map
          ((overEquiv U).functor.map t.hom) ≫
        (localPullbackUnitIso f U).hom) :
    p.hom.val.app (.op (Over.mk (𝟙 (f ⁻¹ᵁ U))))
        (((pullbackPushforwardAdjunction f).unit.app A).val.app
          (.op U) x) =
      (show (Y.ringCatSheaf.over (f ⁻¹ᵁ U)).obj.obj
        (.op (Over.mk (𝟙 (f ⁻¹ᵁ U)))) from 1) := by
  let VY := f ⁻¹ᵁ U
  let N := (pullback f).obj A
  let xg := ((pullbackPushforwardAdjunction f).unit.app
    A).val.app (.op U) x
  refine terminal_apply_eq_of_overEquivT (X := Y) N VY p.hom xg
    (show (Y.ringCatSheaf.over VY).obj.obj
      (.op (Over.mk (𝟙 VY))) from 1) ?_
  exact localTrivialization_overEquiv_pulledSection_ofSection
    f A U t x p hx hp

/-- **Adjunction-unit form of the pulled trivialization on `1`.** For an over-site
trivialization `t : A.over U ≅ unit` and a section `x` with `t.hom x = 1`, any pulled
trivialization `p` whose `overEquiv`-image is the canonical chain sends `1` back to the image
of `x` under the pullback–pushforward adjunction unit. -/
theorem localPullbackTrivialization_inv_one_ofSection (f : Y ⟶ X)
    (A : X.Modules) (U : X.Opens)
    (t : A.over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : A.val.obj (.op U))
    (p : ((pullback f).obj A).over (f ⁻¹ᵁ U) ≅
      _root_.SheafOfModules.unit
        (Y.ringCatSheaf.over (f ⁻¹ᵁ U)))
    (hx : t.hom.val.app (.op (Over.mk (𝟙 U))) x =
      (show (X.ringCatSheaf.over U).obj.obj
        (.op (Over.mk (𝟙 U))) from 1))
    (hp : (overEquiv (f ⁻¹ᵁ U)).functor.map p.hom =
      (localPullbackModuleIso f A U).inv ≫
        (pullback (f ∣_ U)).map
          ((overEquiv U).functor.map t.hom) ≫
        (localPullbackUnitIso f U).hom) :
    p.inv.val.app (.op (Over.mk (𝟙 (f ⁻¹ᵁ U))))
        (show (Y.ringCatSheaf.over (f ⁻¹ᵁ U)).obj.obj
          (.op (Over.mk (𝟙 (f ⁻¹ᵁ U)))) from 1) =
      ((pullbackPushforwardAdjunction f).unit.app A).val.app
        (.op U) x := by
  apply localSheafIso_inv_one_of_hom_eq_oneT (f ⁻¹ᵁ U) p
  exact localPullbackTrivialization_hom_unit_ofSection f A U t x p hx hp

end AlgebraicGeometry.Scheme.Modules
