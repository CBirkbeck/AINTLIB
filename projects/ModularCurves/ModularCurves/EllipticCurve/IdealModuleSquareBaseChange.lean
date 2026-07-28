/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.PoleSheaf

/-!
# Base change of ideal modules along a commutative square

This file constructs the canonical map from the pullback of the ideal module of a
morphism to the ideal module of a morphism in a commutative square. It also gives
an affine criterion proving that map is an isomorphism when matching
nonzerodivisor generators cut out the two ideals.
-/

open AlgebraicGeometry CategoryTheory Limits SheafOfModules

universe u

namespace ModularCurves

noncomputable section

private noncomputable def idealModuleSquareBaseChangeArrow
    {A A' X Y : Scheme.{u}} (f : A ⟶ Y) (_f' : A' ⟶ X)
    (g : X ⟶ Y) :
    idealModule f ⟶
      (Scheme.Modules.pushforward g).obj (Scheme.Modules.unitObj X) :=
  idealModuleToUnit f ≫
    SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom

private theorem idealModuleSquareBaseChangeArrow_condition
    {A A' X Y : Scheme.{u}} (f : A ⟶ Y) (f' : A' ⟶ X)
    (g : X ⟶ Y) (t : A' ⟶ A) (h : f' ≫ g = t ≫ f) :
    idealModuleSquareBaseChangeArrow f f' g ≫
      (Scheme.Modules.pushforward g).map
        (SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom) = 0 := by
  let u := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have hkernel := kernel.condition u
  apply (cancel_mono
    ((Scheme.Modules.pushforwardComp f' g).hom.app
      (Scheme.Modules.unitObj A'))).1
  change _ = (0 : idealModule f ⟶
    (Scheme.Modules.pushforward (f' ≫ g)).obj (Scheme.Modules.unitObj A'))
  change idealModuleToUnit f ≫
    (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward g).map
        (SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom) ≫
      (Scheme.Modules.pushforwardComp f' g).hom.app
        (Scheme.Modules.unitObj A')) = 0
  erw [← unitToPushforwardObjUnit_comp f' g]
  rw [h]
  rw [unitToPushforwardObjUnit_comp t f]
  erw [← Category.assoc, hkernel]
  exact zero_comp

/-- Before adjunction, the ideal-module comparison attached to a commutative
square. -/
noncomputable def idealModuleToPushforwardSquareBaseChangeRaw
    {A A' X Y : Scheme.{u}} (f : A ⟶ Y) (f' : A' ⟶ X)
    (g : X ⟶ Y) (t : A' ⟶ A) (h : f' ≫ g = t ≫ f) :
    idealModule f ⟶
      (Scheme.Modules.pushforward g).obj (idealModule f') :=
  kernel.lift _ (idealModuleSquareBaseChangeArrow f f' g)
      (idealModuleSquareBaseChangeArrow_condition f f' g t h) ≫
    (PreservesKernel.iso (Scheme.Modules.pushforward g)
      (SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom)).inv

private theorem kernelLiftPreservedIdealModule_comp
    {A' X Y : Scheme.{u}} (f' : A' ⟶ X) (g : X ⟶ Y)
    {W : Y.Modules}
    (a : W ⟶ (Scheme.Modules.pushforward g).obj (Scheme.Modules.unitObj X))
    (ha : a ≫ (Scheme.Modules.pushforward g).map
      (SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom) = 0) :
    (kernel.lift ((Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom)) a ha ≫
        (PreservesKernel.iso (Scheme.Modules.pushforward g)
          (SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom)).inv) ≫
      (Scheme.Modules.pushforward g).map
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          f'.toRingCatSheafHom)) = a := by
  let u' := SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom
  have hi := PreservesKernel.iso_inv_ι (Scheme.Modules.pushforward g) u'
  rw [Category.assoc]
  erw [hi]
  exact kernel.lift_ι ((Scheme.Modules.pushforward g).map u') a ha

/-- The adjunction-side ideal-module comparison attached to a commutative
square. -/
noncomputable def idealModuleToPushforwardSquareBaseChange
    {A A' X Y : Scheme.{u}} (f : A ⟶ Y) (f' : A' ⟶ X)
    (g : X ⟶ Y) (t : A' ⟶ A) (h : f' ≫ g = t ≫ f) :
    idealModule f ⟶
      (Scheme.Modules.pushforward g).obj (idealModule f') :=
  idealModuleToPushforwardSquareBaseChangeRaw f f' g t h

/-- The canonical morphism from the pullback of an ideal module to the ideal
module in a commutative square. -/
noncomputable def idealModuleSquareBaseChangeHom
    {A A' X Y : Scheme.{u}} (f : A ⟶ Y) (f' : A' ⟶ X)
    (g : X ⟶ Y) (t : A' ⟶ A) (h : f' ≫ g = t ≫ f) :
    (Scheme.Modules.pullback g).obj (idealModule f) ⟶ idealModule f' :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
    (idealModuleToPushforwardSquareBaseChange f f' g t h)

@[reassoc]
theorem idealModuleToPushforwardSquareBaseChangeRaw_comp_toUnit
    {A A' X Y : Scheme.{u}} (f : A ⟶ Y) (f' : A' ⟶ X)
    (g : X ⟶ Y) (t : A' ⟶ A) (h : f' ≫ g = t ≫ f) :
    idealModuleToPushforwardSquareBaseChangeRaw f f' g t h ≫
        (Scheme.Modules.pushforward g).map
          (kernel.ι (unitToPushforwardObjUnit f'.toRingCatSheafHom)) =
      kernel.ι (unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        unitToPushforwardObjUnit g.toRingCatSheafHom := by
  exact kernelLiftPreservedIdealModule_comp f' g
    (idealModuleSquareBaseChangeArrow f f' g)
    (idealModuleSquareBaseChangeArrow_condition f f' g t h)

@[reassoc]
theorem idealModuleToPushforwardSquareBaseChange_comp_toUnit
    {A A' X Y : Scheme.{u}} (f : A ⟶ Y) (f' : A' ⟶ X)
    (g : X ⟶ Y) (t : A' ⟶ A) (h : f' ≫ g = t ≫ f) :
    idealModuleToPushforwardSquareBaseChange f f' g t h ≫
        (Scheme.Modules.pushforward g).map (idealModuleToUnit f') =
      idealModuleToUnit f ≫
        unitToPushforwardObjUnit g.toRingCatSheafHom := by
  exact idealModuleToPushforwardSquareBaseChangeRaw_comp_toUnit
    f f' g t h

@[reassoc]
theorem idealModuleSquareBaseChangeHom_comp_toUnit
    {A A' X Y : Scheme.{u}} (f : A ⟶ Y) (f' : A' ⟶ X)
    (g : X ⟶ Y) (t : A' ⟶ A) (h : f' ≫ g = t ≫ f) :
    idealModuleSquareBaseChangeHom f f' g t h ≫ idealModuleToUnit f' =
      (Scheme.Modules.pullback g).map (idealModuleToUnit f) ≫
        (Scheme.Modules.pullbackUnitIso g).hom := by
  letI : (SheafOfModules.pushforward
      g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  let adj : Scheme.Modules.pullback g ⊣ Scheme.Modules.pushforward g :=
    Scheme.Modules.pullbackPushforwardAdjunction g
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  rw [show (adj.homEquiv _ _)
      (idealModuleSquareBaseChangeHom f f' g t h) =
      idealModuleToPushforwardSquareBaseChange f f' g t h by
    exact Equiv.apply_symm_apply _ _]
  rw [idealModuleToPushforwardSquareBaseChange_comp_toUnit]
  rw [Adjunction.homEquiv_naturality_left]
  erw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    g.toRingCatSheafHom]
  rfl

/-- On affine charts where the source and target ideals have matching
nonzerodivisor generators, the square base-change map is an isomorphism. -/
theorem idealModuleSquareBaseChangeHom_isIso_on_affine
    {A A' X Y : Scheme.{u}} (f : A ⟶ Y) (f' : A' ⟶ X)
    (g : X ⟶ Y) (t : A' ⟶ A) (h : f' ≫ g = t ≫ f)
    [QuasiCompact f] [QuasiCompact f']
    (U : X.affineOpens) (V : Y.affineOpens)
    (hUV : U.1 ≤ g ⁻¹ᵁ V.1)
    (r : Γ(Y, V.1)) (hr : r ∈ f.ker.ideal V)
    (hspan : f.ker.ideal V = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, V.1))
    (hspan' : f'.ker.ideal U =
      Ideal.span {affinePullbackSection g U V hUV r})
    (hnzd' : affinePullbackSection g U V hUV r ∈
      nonZeroDivisors Γ(X, U.1)) :
    IsIso ((Scheme.Modules.pullback U.1.ι).map
      (idealModuleSquareBaseChangeHom f f' g t h)) := by
  let r' := affinePullbackSection g U V hUV r
  let eS := pullbackLocalIdealGeneratorIso f g U V hUV r hr hspan hnzd
  have hr' : r' ∈ f'.ker.ideal U := by
    rw [hspan']
    exact Ideal.mem_span_singleton_self r'
  let eT := localIdealGeneratorPullbackIso f' U r' hr' hspan' hnzd'
  have hbase : (Scheme.Modules.pullback U.1.ι).map
        (idealModuleSquareBaseChangeHom f f' g t h) ≫
        pulledIdealModuleToUnit f' U.1.ι =
      (Scheme.Modules.pullback U.1.ι).map
          (pulledIdealModuleToUnit f g) ≫
        (Scheme.Modules.pullbackUnitIso U.1.ι).hom := by
    dsimp only [pulledIdealModuleToUnit]
    rw [← (Scheme.Modules.pullback U.1.ι).map_comp_assoc]
    rw [idealModuleSquareBaseChangeHom_comp_toUnit]
  have hm : eS.hom ≫
      (Scheme.Modules.pullback U.1.ι).map
        (idealModuleSquareBaseChangeHom f f' g t h) = eT.hom := by
    letI : Mono (pulledIdealModuleToUnit f' U.1.ι) :=
      pulledIdealModuleToUnit_mono_of_isOpenImmersion f' U.1.ι
    apply (cancel_mono (pulledIdealModuleToUnit f' U.1.ι)).1
    calc
      (eS.hom ≫ (Scheme.Modules.pullback U.1.ι).map
          (idealModuleSquareBaseChangeHom f f' g t h)) ≫
          pulledIdealModuleToUnit f' U.1.ι =
        eS.hom ≫ (Scheme.Modules.pullback U.1.ι).map
          (pulledIdealModuleToUnit f g) ≫
          (Scheme.Modules.pullbackUnitIso U.1.ι).hom := by
            rw [Category.assoc, hbase]
      _ = unitEndomorphismOfTopSection
          ((g.resLE V.1 U.1 hUV).appTop.hom
            (affineOpenTopSection V r)) :=
        pullbackLocalIdealGeneratorIso_hom_comp_toUnit
          f g U V hUV r hr hspan hnzd
      _ = unitEndomorphismOfTopSection (affineOpenTopSection U r') := by
        rw [affineOpenTopSection_affinePullbackSection]
      _ = eT.hom ≫ pulledIdealModuleToUnit f' U.1.ι :=
        (localIdealGeneratorPullbackIso_hom_comp_pulledIdealModuleToUnit
          f' U r' hr' hspan' hnzd').symm
  have hmap : (Scheme.Modules.pullback U.1.ι).map
      (idealModuleSquareBaseChangeHom f f' g t h) =
      eS.inv ≫ eT.hom := by
    apply (cancel_epi eS.hom).1
    calc
      eS.hom ≫ (Scheme.Modules.pullback U.1.ι).map
          (idealModuleSquareBaseChangeHom f f' g t h) = eT.hom := hm
      _ = eS.hom ≫ (eS.inv ≫ eT.hom) := by
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [hmap]
  infer_instance

end

end ModularCurves
