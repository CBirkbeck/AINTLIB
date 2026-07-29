/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafPointedIso
import ModularCurves.ForMathlib.SchemeModulePullbackIteratedBaseChange

/-!
# Iterated base change of pole-sheaf models

This file transports a pointed pole-sheaf model through a second base change
and expresses the result on the direct pullback family.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace ModularCurves

/-- A section of a once-base-changed family, after one further base change and
transport through the canonical pullback associator. -/
noncomputable def sectionIteratedBaseChangeDirect
    {Y S T U : Scheme.{u}} (π : Y ⟶ S) (t : T ⟶ S)
    (zT : T ⟶ pullback π t) (hzT : zT ≫ pullback.snd π t = 𝟙 T)
    (u : U ⟶ T) : U ⟶ pullback π (u ≫ t) :=
  sectionBaseChange zT hzT u ≫
    (pullbackLeftPullbackSndIso π t u).hom

/-- The transported direct section is a section of the direct base change. -/
@[reassoc]
theorem sectionIteratedBaseChangeDirect_snd
    {Y S T U : Scheme.{u}} (π : Y ⟶ S) (t : T ⟶ S)
    (zT : T ⟶ pullback π t) (hzT : zT ≫ pullback.snd π t = 𝟙 T)
    (u : U ⟶ T) :
    sectionIteratedBaseChangeDirect π t zT hzT u ≫
      pullback.snd π (u ≫ t) = 𝟙 U := by
  rw [sectionIteratedBaseChangeDirect, Category.assoc,
    pullbackLeftPullbackSndIso_hom_snd, sectionBaseChange_snd]

/-- Transporting the direct section back through the associator recovers the
iterated base-change section. -/
@[reassoc]
theorem sectionIteratedBaseChangeDirect_assoc_inv
    {Y S T U : Scheme.{u}} (π : Y ⟶ S) (t : T ⟶ S)
    (zT : T ⟶ pullback π t) (hzT : zT ≫ pullback.snd π t = 𝟙 T)
    (u : U ⟶ T) :
    sectionIteratedBaseChangeDirect π t zT hzT u ≫
      (pullbackLeftPullbackSndIso π t u).inv =
        sectionBaseChange zT hzT u := by
  rw [sectionIteratedBaseChangeDirect, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- A pole-sheaf model after one base change induces a pole-sheaf model on
every direct further base change. -/
noncomputable def sectionPoleSheafPowerDirectBaseChangeIso
    {Y S T U : Scheme.{u}} {π : Y ⟶ S} [IsSeparated π]
    (t : T ⟶ S) (zT : T ⟶ pullback π t)
    (hzT : zT ≫ pullback.snd π t = 𝟙 T)
    (hsmT : SmoothOfRelativeDimension 1 (pullback.snd π t))
    (M : Y.Modules) {n : ℕ}
    (e : (Scheme.Modules.pullback (pullback.fst π t)).obj M ≅
      sectionPoleSheafPower (pullback.snd π t) zT hzT n)
    (u : U ⟶ T) :
    (Scheme.Modules.pullback (pullback.fst π (u ≫ t))).obj M ≅
      sectionPoleSheafPower (pullback.snd π (u ≫ t))
        (sectionIteratedBaseChangeDirect π t zT hzT u)
        (sectionIteratedBaseChangeDirect_snd π t zT hzT u) n := by
  let eAssoc := pullbackLeftPullbackSndIso π t u
  let zU := sectionBaseChange zT hzT u
  let hzU := sectionBaseChange_snd zT hzT u
  let zD := sectionIteratedBaseChangeDirect π t zT hzT u
  let hzD := sectionIteratedBaseChangeDirect_snd π t zT hzT u
  let hsmU : SmoothOfRelativeDimension 1
      (pullback.snd (pullback.snd π t) u) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback (pullback.snd π t) u) hsmT
  let eIter := Scheme.Modules.pullbackIteratedBaseChangeIso π t u M
  let eModel :=
    (Scheme.Modules.pullback eAssoc.inv).mapIso
      ((Scheme.Modules.pullback
        (pullback.fst (pullback.snd π t) u)).mapIso e)
  let ePole := (Scheme.Modules.pullback eAssoc.inv).mapIso
    (sectionPoleSheafPowerBaseChangeIso hsmT zT hzT u n)
  let ePointed := sectionPoleSheafPowerPointedIso
    zD hzD zU hzU hsmU eAssoc.symm
      (sectionIteratedBaseChangeDirect_assoc_inv π t zT hzT u) n
  exact eIter ≪≫ eModel ≪≫ ePole ≪≫ ePointed

end ModularCurves
