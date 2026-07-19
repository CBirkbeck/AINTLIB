/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.CartierDivisor
import ModularCurves.Picard.Dual
import ModularCurves.Picard.DualPullback.Iso
import ModularCurves.Picard.DualRestrict
import ModularCurves.Picard.Pic
import ModularCurves.Picard.UnitPullback
import ModularCurves.ForMathlib.PullbackCompMonoidal
import ModularCurves.ForMathlib.FlatNonZeroDivisor
import ModularCurves.ForMathlib.PullbackTensorGeneral
import ModularCurves.ForMathlib.PullbackTensorMonoidal
import ModularCurves.ForMathlib.PullbackUnitMonoidal
import ModularCurves.Picard.DualPullback.TrivializationRestriction
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Pole sheaves attached to a section

This file begins the converse direction of the fibrewise/local Weierstrass comparison.
It packages the ideal of a section as an actual sheaf of modules, rather than only as
`Scheme.IdealSheafData`.  The local-principal theorem in `CartierDivisor.lean` will then
identify this kernel sheaf locally with the structure sheaf.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory SheafOfModules
  TopologicalSpace

universe v u

set_option backward.isDefEq.respectTransparency false in
local instance (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)) := by
  change (PresheafOfModules.sheafification
      (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
        X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj)).IsLocalization
    (PresheafOfModules.sheafificationW
      (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
        X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj))
  infer_instance

local instance (X : Scheme.{u}) :
    (PresheafOfModules.sheafificationW
      (𝟙 X.ringCatSheaf.obj)).IsMonoidal := by
  change (PresheafOfModules.sheafificationW
    (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
      X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj)).IsMonoidal
  infer_instance

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

namespace ModularCurves

/-- Base change of a section along a morphism of bases. -/
noncomputable def sectionBaseChange {C S T : Scheme.{u}} {π : C ⟶ S}
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    T ⟶ pullback π t :=
  pullback.lift (t ≫ z) (𝟙 T)
    (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp])

@[simp]
theorem sectionBaseChange_fst {C S T : Scheme.{u}} {π : C ⟶ S}
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    sectionBaseChange z hz t ≫ pullback.fst π t = t ≫ z :=
  pullback.lift_fst _ _ _

@[simp]
theorem sectionBaseChange_snd {C S T : Scheme.{u}} {π : C ⟶ S}
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    sectionBaseChange z hz t ≫ pullback.snd π t = 𝟙 T :=
  pullback.lift_snd _ _ _

/-- The divisor cut out by a section commutes with arbitrary base change. -/
theorem RelEffCartierDiv.sectionDivisor_baseChange
    {C S T : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    (sectionDivisor π z hz).baseChange t =
      sectionDivisor (pullback.snd π t) (sectionBaseChange z hz t)
        (sectionBaseChange_snd z hz t) := by
  apply RelEffCartierDiv.ext
  rw [RelEffCartierDiv.baseChange_ideal]
  change (Scheme.Hom.ker z).comap (pullback.fst π t) =
    (sectionBaseChange z hz t).ker
  exact (RelEffCartierDiv.ker_sectionBaseChange z hz t).symm

/-- Multiplication by a nonzerodivisor identifies a ring with the principal ideal it
generates.  Unlike `LinearEquiv.toSpanNonzeroSingleton`, this does not require the
ambient ring to be a domain. -/
noncomputable def principalIdealEquiv {R : Type*} [CommRing R]
    (r : R) (hr : r ∈ nonZeroDivisors R) :
    R ≃ₗ[R] (Ideal.span {r} : Ideal R) :=
  (LinearEquiv.ofInjective (LinearMap.toSpanSingleton R R r)
      (by
        rw [← LinearMap.ker_eq_bot]
        exact LinearMap.ker_toSpanSingleton_eq_bot_iff.mpr
          (mem_nonZeroDivisors_iff_right.mp hr))).trans
    (LinearEquiv.ofEq _ _ (LinearMap.range_toSpanSingleton r))

@[simp]
theorem principalIdealEquiv_apply {R : Type*} [CommRing R]
    (r : R) (hr : r ∈ nonZeroDivisors R) (a : R) :
    principalIdealEquiv r hr a =
      (⟨a * r, Ideal.mul_mem_left _ a (Ideal.mem_span_singleton_self r)⟩ :
        Ideal.span {r}) :=
  rfl

/-- The structure-sheaf morphism for a composite is the composite of the two
structure-sheaf morphisms, after identifying iterated pushforward with pushforward
along the composite. -/
theorem unitToPushforwardObjUnit_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app (Scheme.Modules.unitObj X) := by
  apply SheafOfModules.hom_ext
  ext U
  rfl

@[simp]
private theorem ofEq_coe {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] (P Q : Submodule R M) (h : P = Q) (x : P) :
    (((LinearEquiv.ofEq P Q h) x : Q) : M) = x := by
  subst Q
  rfl

/-- The raw sheaf-of-modules kernel defining the ideal of a morphism. -/
noncomputable def idealModuleRaw {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SheafOfModules Y.ringCatSheaf :=
  kernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)

/-- The ideal module of a morphism: the kernel of
`O_Y -> f_* O_X` in the abelian category of sheaves of `O_Y`-modules. -/
noncomputable def idealModule {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.Modules :=
  idealModuleRaw f

/-- The ideal module is canonically a submodule of the structure sheaf. -/
noncomputable def idealModuleToUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    idealModule f ⟶ Scheme.Modules.unitObj Y :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)

set_option backward.isDefEq.respectTransparency false in
/-- Before adjunction, the base-change comparison for a section ideal is the map
from the original kernel to the pushforward of the base-changed kernel. -/
noncomputable def idealModuleToPushforwardBaseChangeRaw
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    idealModuleRaw z ⟶
      (Scheme.Modules.pushforward (pullback.fst π t)).obj
        (idealModuleRaw (sectionBaseChange z hz t)) := by
  let z' := sectionBaseChange z hz t
  let g := pullback.fst π t
  let u := SheafOfModules.unitToPushforwardObjUnit z.toRingCatSheafHom
  let u' := SheafOfModules.unitToPushforwardObjUnit z'.toRingCatSheafHom
  let a : idealModuleRaw z ⟶
      (Scheme.Modules.pushforward g).obj (Scheme.Modules.unitObj (pullback π t)) :=
    kernel.ι u ≫
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom
  have hkernel := kernel.condition u
  have ha : a ≫ (Scheme.Modules.pushforward g).map u' = 0 := by
    apply (cancel_mono
      ((Scheme.Modules.pushforwardComp z' g).hom.app (Scheme.Modules.unitObj T))).1
    change _ = (0 : idealModuleRaw z ⟶
      (Scheme.Modules.pushforward (z' ≫ g)).obj (Scheme.Modules.unitObj T))
    change kernel.ι u ≫
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit z'.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp z' g).hom.app (Scheme.Modules.unitObj T)) = 0
    erw [← unitToPushforwardObjUnit_comp z' g]
    rw [show z' ≫ g = t ≫ z by exact sectionBaseChange_fst z hz t]
    rw [unitToPushforwardObjUnit_comp t z]
    erw [← Category.assoc, hkernel]
    exact zero_comp
  exact kernel.lift _ a ha ≫
    (PreservesKernel.iso (Scheme.Modules.pushforward g) u').inv

/-- The adjunction-side map underlying base change of a section ideal. -/
noncomputable def idealModuleToPushforwardBaseChange
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    idealModule z ⟶
      (Scheme.Modules.pushforward (pullback.fst π t)).obj
        (idealModule (sectionBaseChange z hz t)) :=
  idealModuleToPushforwardBaseChangeRaw z hz t

/-- The canonical morphism from the pullback of a section ideal to the ideal of the
base-changed section. -/
noncomputable def idealModuleBaseChangeHom
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    (Scheme.Modules.pullback (pullback.fst π t)).obj (idealModule z) ⟶
      idealModule (sectionBaseChange z hz t) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.fst π t)).homEquiv _ _).symm
    (idealModuleToPushforwardBaseChange z hz t)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem idealModuleToPushforwardBaseChangeRaw_comp_toUnit
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    idealModuleToPushforwardBaseChangeRaw z hz t ≫
        (Scheme.Modules.pushforward (pullback.fst π t)).map
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (sectionBaseChange z hz t).toRingCatSheafHom)) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit z.toRingCatSheafHom) ≫
        SheafOfModules.unitToPushforwardObjUnit
        (pullback.fst π t).toRingCatSheafHom := by
  dsimp only [idealModuleToPushforwardBaseChangeRaw]
  rw [Category.assoc, PreservesKernel.iso_inv_ι]
  rw [kernel.lift_ι]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem idealModuleToPushforwardBaseChange_comp_toUnit
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    idealModuleToPushforwardBaseChange z hz t ≫
        (Scheme.Modules.pushforward (pullback.fst π t)).map
          (idealModuleToUnit (sectionBaseChange z hz t)) =
      idealModuleToUnit z ≫ SheafOfModules.unitToPushforwardObjUnit
        (pullback.fst π t).toRingCatSheafHom := by
  change idealModuleToPushforwardBaseChangeRaw z hz t ≫
      (Scheme.Modules.pushforward (pullback.fst π t)).map
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (sectionBaseChange z hz t).toRingCatSheafHom)) =
    kernel.ι (SheafOfModules.unitToPushforwardObjUnit z.toRingCatSheafHom) ≫
      SheafOfModules.unitToPushforwardObjUnit
        (pullback.fst π t).toRingCatSheafHom
  exact idealModuleToPushforwardBaseChangeRaw_comp_toUnit z hz t

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem idealModuleBaseChangeHom_comp_toUnit
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    idealModuleBaseChangeHom z hz t ≫
        idealModuleToUnit (sectionBaseChange z hz t) =
      (Scheme.Modules.pullback (pullback.fst π t)).map (idealModuleToUnit z) ≫
        SheafOfModules.pullbackObjUnitToUnit
          (pullback.fst π t).toRingCatSheafHom := by
  let g := pullback.fst π t
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  rw [show (adj.homEquiv _ _)
      (idealModuleBaseChangeHom z hz t) =
      idealModuleToPushforwardBaseChange z hz t by
    exact Equiv.apply_symm_apply _ _]
  rw [idealModuleToPushforwardBaseChange_comp_toUnit]
  rw [Adjunction.homEquiv_naturality_left]
  erw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]

/-- On an affine open, `idealModule f` is the module attached to the affine ideal
recorded by `f.ker`. -/
noncomputable def idealModuleAppIdealIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (U : Y.affineOpens) :
    (SheafOfModules.evaluation Y.ringCatSheaf (.op U.1)).obj (idealModule f) ≅
      ModuleCat.of Γ(Y, U.1) (f.ker.ideal U) := by
  refine (PreservesKernel.iso (SheafOfModules.evaluation Y.ringCatSheaf (.op U.1))
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).trans
    ((ModuleCat.kernelIsoKer _).trans ?_)
  exact (LinearEquiv.ofEq _ _ (by rw [Scheme.Hom.ker_apply]; rfl)).toModuleIso

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem idealModuleAppIdealIso_coe {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (U : Y.affineOpens) (x : Γ(idealModule f, U.1)) :
    ((idealModuleAppIdealIso f U).hom x : Γ(Y, U.1)) =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).val.app
        (.op U.1) x := by
  change (((idealModuleAppIdealIso f U).hom ≫
    ModuleCat.ofHom (f.ker.ideal U).subtype) x) = _
  simp only [idealModuleAppIdealIso, idealModule, idealModuleRaw, Iso.trans_hom,
    ConcreteCategory.comp_apply, LinearEquiv.toModuleIso_hom]
  let F := SheafOfModules.evaluation Y.ringCatSheaf (.op U.1)
  let g := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have hker : (F.map g).hom.ker = f.ker.ideal U := by
    rw [Scheme.Hom.ker_apply]
    rfl
  change ((LinearEquiv.ofEq _ _ hker)
    ((ModuleCat.kernelIsoKer (F.map g)).hom ((PreservesKernel.iso F g).hom x))).1 = _
  rw [ofEq_coe]
  change (ModuleCat.ofHom (F.map g).hom.ker.subtype)
    (((PreservesKernel.iso F g).hom ≫ (ModuleCat.kernelIsoKer (F.map g)).hom) x) = _
  rw [← ConcreteCategory.comp_apply]
  rw [Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype]
  rw [PreservesKernel.iso_hom, kernelComparison_comp_ι]
  rfl

/-- The restricted ideal module maps to the restricted structure sheaf. -/
noncomputable def restrictIdealModuleToUnit {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion g] :
    (Scheme.Modules.restrictFunctor g).obj (idealModule f) ⟶
      Scheme.Modules.unitObj Y' :=
  (Scheme.Modules.restrictFunctor g).map (idealModuleToUnit f) ≫
    (Scheme.Modules.restrictUnitIso g).hom

set_option backward.isDefEq.respectTransparency false in
/-- If the kernel ideal of `f'` is the pullback of the kernel ideal of `f`, then
the restricted ideal module maps into the ideal module of `f'`. -/
theorem restrictIdealModuleToUnit_comp_zero {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion g] (f' : X' ⟶ Y')
    [QuasiCompact f] [QuasiCompact f']
    (hker : f'.ker = f.ker.comap g) :
    restrictIdealModuleToUnit f g ≫
      SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom = 0 := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  have hbasis : Opens.IsBasis
      (Set.range (fun U : Y'.affineOpens => U.1)) := by
    simpa only [Subtype.range_val] using Y'.isBasis_affineOpens
  apply TopCat.Sheaf.hom_ext (B := fun U : Y'.affineOpens => U.1)
    ((PresheafOfModules.toPresheaf _).obj
      ((Scheme.Modules.restrictFunctor g).obj (idealModule f)).val)
    ((SheafOfModules.toSheaf Y'.ringCatSheaf).obj
      ((Scheme.Modules.pushforward f').obj (Scheme.Modules.unitObj X')))
    hbasis
  intro U
  ext x
  change f'.app U.1 _ = 0
  rw [← RingHom.mem_ker]
  rw [← Scheme.Hom.ker_apply f' U]
  rw [hker, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  rw [Ideal.mem_comap]
  change (g.appIso U.1).inv
    ((g.appIso U.1).hom
      ((idealModuleToUnit f).val.app (.op (g ''ᵁ U.1)) x)) ∈ _
  rw [Iso.hom_inv_id_apply]
  have hx := (idealModuleAppIdealIso f
    ⟨g ''ᵁ U.1, U.2.image_of_isOpenImmersion g⟩).hom x |>.property
  rw [idealModuleAppIdealIso_coe] at hx
  exact hx

/-- The canonical map from a restricted ideal module to the ideal module having
the pulled-back kernel ideal. -/
noncomputable def restrictIdealModuleHom {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion g] (f' : X' ⟶ Y')
    [QuasiCompact f] [QuasiCompact f']
    (hker : f'.ker = f.ker.comap g) :
    (Scheme.Modules.restrictFunctor g).obj (idealModule f) ⟶ idealModule f' := by
  change (Scheme.Modules.restrictFunctor g).obj (idealModule f) ⟶
    kernel (SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom)
  exact kernel.lift _ (restrictIdealModuleToUnit f g)
    (restrictIdealModuleToUnit_comp_zero f g f' hker)

@[reassoc]
theorem restrictIdealModuleHom_comp_toUnit {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion g] (f' : X' ⟶ Y')
    [QuasiCompact f] [QuasiCompact f']
    (hker : f'.ker = f.ker.comap g) :
    restrictIdealModuleHom f g f' hker ≫ idealModuleToUnit f' =
      restrictIdealModuleToUnit f g := by
  apply kernel.lift_ι

theorem restrictIdealModuleHom_app_toUnit {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion g] (f' : X' ⟶ Y')
    [QuasiCompact f] [QuasiCompact f']
    (hker : f'.ker = f.ker.comap g) (U : Y'.affineOpens)
    (x : Γ(idealModule f, g ''ᵁ U.1)) :
    (idealModuleToUnit f').val.app (.op U.1)
        ((restrictIdealModuleHom f g f' hker).val.app (.op U.1) x) =
      (g.appIso U.1).hom ((idealModuleToUnit f).val.app (.op (g ''ᵁ U.1)) x) := by
  have h := congrArg (fun q => q.val.app (.op U.1))
    (restrictIdealModuleHom_comp_toUnit f g f' hker)
  exact congr($(h) x)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical ideal-module map is bijective on every affine open. -/
theorem restrictIdealModuleHom_app_bijective {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion g] (f' : X' ⟶ Y')
    [QuasiCompact f] [QuasiCompact f']
    (hker : f'.ker = f.ker.comap g) (U : Y'.affineOpens) :
    Function.Bijective
      ((restrictIdealModuleHom f g f' hker).val.app (.op U.1)) := by
  let V : Y.affineOpens :=
    ⟨g ''ᵁ U.1, U.2.image_of_isOpenImmersion g⟩
  constructor
  · intro x y hxy
    have hxy' := congrArg
      (fun q => (idealModuleToUnit f').val.app (.op U.1) q) hxy
    rw [restrictIdealModuleHom_app_toUnit, restrictIdealModuleHom_app_toUnit] at hxy'
    have hxy'' := (ConcreteCategory.bijective_of_isIso (g.appIso U.1).hom).1 hxy'
    apply (ConcreteCategory.bijective_of_isIso (idealModuleAppIdealIso f V).hom).1
    apply Subtype.ext
    change ((idealModuleAppIdealIso f V).hom x).1 =
      ((idealModuleAppIdealIso f V).hom y).1
    rw [idealModuleAppIdealIso_coe, idealModuleAppIdealIso_coe]
    exact hxy''
  · intro y
    let r' : Γ(Y', U.1) := (idealModuleToUnit f').val.app (.op U.1) y
    have hr' : r' ∈ f'.ker.ideal U := by
      have hy := ((idealModuleAppIdealIso f' U).hom y).property
      rw [idealModuleAppIdealIso_coe] at hy
      exact hy
    have hr : (g.appIso U.1).inv r' ∈ f.ker.ideal V := by
      rw [hker, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
        Ideal.mem_comap] at hr'
      exact hr'
    let x : Γ(idealModule f, g ''ᵁ U.1) :=
      (idealModuleAppIdealIso f V).inv ⟨(g.appIso U.1).inv r', hr⟩
    refine ⟨x, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (idealModuleAppIdealIso f' U).hom).1
    apply Subtype.ext
    rw [idealModuleAppIdealIso_coe, idealModuleAppIdealIso_coe]
    change (idealModuleToUnit f').val.app (.op U.1)
        ((restrictIdealModuleHom f g f' hker).val.app (.op U.1) x) =
      (idealModuleToUnit f').val.app (.op U.1) y
    rw [restrictIdealModuleHom_app_toUnit]
    have hx := congrArg Subtype.val
      (Iso.inv_hom_id_apply (idealModuleAppIdealIso f V)
        ⟨(g.appIso U.1).inv r', hr⟩)
    rw [idealModuleAppIdealIso_coe] at hx
    have hx' : (idealModuleToUnit f).val.app (.op (g ''ᵁ U.1)) x =
        (g.appIso U.1).inv r' := by
      change (kernel.ι
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).val.app
            (.op V.1)
          ((idealModuleAppIdealIso f V).inv
            ⟨(g.appIso U.1).inv r', hr⟩) = _
      exact hx
    change (g.appIso U.1).hom
      ((idealModuleToUnit f).val.app (.op (g ''ᵁ U.1)) x) = r'
    rw [hx', Iso.inv_hom_id_apply]

/-- Restriction along an open immersion commutes with formation of a quasi-compact
morphism's ideal module when the kernel ideal pulls back. -/
noncomputable def restrictIdealModuleIso {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion g] (f' : X' ⟶ Y')
    [QuasiCompact f] [QuasiCompact f']
    (hker : f'.ker = f.ker.comap g) :
    (Scheme.Modules.restrictFunctor g).obj (idealModule f) ≅ idealModule f' := by
  let e := restrictIdealModuleHom f g f' hker
  have hbasis : Opens.IsBasis
      (Set.range (fun U : Y'.affineOpens => U.1)) := by
    simpa only [Subtype.range_val] using Y'.isBasis_affineOpens
  haveI heSheaf : IsIso ((SheafOfModules.toSheaf Y'.ringCatSheaf).map e) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis
      (B := fun U : Y'.affineOpens => U.1)
      (φ := (SheafOfModules.toSheaf Y'.ringCatSheaf).map e) hbasis
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    exact restrictIdealModuleHom_app_bijective f g f' hker U
  let es := asIso ((SheafOfModules.toSheaf Y'.ringCatSheaf).map e)
  apply (SheafOfModules.fullyFaithfulForget Y'.ringCatSheaf).preimageIso
  refine PresheafOfModules.isoMk (fun U => by
    let eU := ((sheafToPresheaf (Opens.grothendieckTopology Y')
      AddCommGrpCat).mapIso es).app U
    exact ModuleCat.isoMk
      eU
      (ModuleCat.smul_naturality (e.val.app U))) (fun {U V} i => ?_)
  ext x
  exact congr($(e.val.naturality i) x)

/-- Restricting a principal ideal generated by a nonzerodivisor to an affine basic
open preserves both properties. -/
theorem ideal_basicOpen_span_nzd {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (U : Y.affineOpens) (r : Γ(Y, U.1))
    (hspan : I.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, U.1)) (t : Γ(Y, U.1)) :
    I.ideal (Y.affineBasicOpen t) =
        Ideal.span {(Y.presheaf.map (homOfLE (Y.basicOpen_le t)).op) r} ∧
      (Y.presheaf.map (homOfLE (Y.basicOpen_le t)).op) r ∈
        nonZeroDivisors Γ(Y, (Y.affineBasicOpen t).1) := by
  letI : Algebra Γ(Y, U.1) Γ(Y, (Y.affineBasicOpen t).1) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le t)).op).hom.toAlgebra
  letI : IsLocalization (Submonoid.powers t) Γ(Y, (Y.affineBasicOpen t).1) :=
    U.2.isLocalization_basicOpen t
  constructor
  · rw [← I.map_ideal_basicOpen U t, hspan, Ideal.map_span, Set.image_singleton]
  · exact IsLocalization.map_nonZeroDivisors_le (Submonoid.powers t)
      Γ(Y, (Y.affineBasicOpen t).1) ⟨r, hnzd, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The element of the kernel sheaf corresponding to an element of the affine kernel
ideal. -/
noncomputable def localIdealElement {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (U : Y.affineOpens) (r : Γ(Y, U.1)) (hr : r ∈ f.ker.ideal U) :
    Γ(idealModule f, U.1) :=
  (idealModuleAppIdealIso f U).inv ⟨r, hr⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem idealModuleAppIdealIso_hom_localIdealElement {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] (U : Y.affineOpens) (r : Γ(Y, U.1))
    (hr : r ∈ f.ker.ideal U) :
    (idealModuleAppIdealIso f U).hom (localIdealElement f U r hr) = ⟨r, hr⟩ := by
  simp [localIdealElement]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Under the affine kernel identification, restricting `localIdealElement` to an
affine subopen restricts its underlying ring element. -/
theorem idealModuleAppIdealIso_coe_map_localIdealElement {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] (U V : Y.affineOpens) (hVU : V ≤ U)
    (r : Γ(Y, U.1)) (hr : r ∈ f.ker.ideal U) :
    ((idealModuleAppIdealIso f V).hom
        ((idealModule f).presheaf.map (homOfLE hVU).op
          (localIdealElement f U r hr))).1 =
      Y.presheaf.map (homOfLE hVU).op r := by
  rw [idealModuleAppIdealIso_coe]
  let g := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let i : Opposite.op U.1 ⟶ Opposite.op V.1 :=
    (homOfLE (show V.1 ≤ U.1 from hVU)).op
  change (kernel.ι g).val.app (.op V.1)
    ((idealModule f).val.map i (localIdealElement f U r hr)) = _
  have hnat := congr($((kernel.ι g).val.naturality i).hom
    (localIdealElement f U r hr))
  have hnat' :
      (kernel.ι g).val.app (.op V.1)
          ((idealModule f).val.map i (localIdealElement f U r hr)) =
        (SheafOfModules.unit Y.ringCatSheaf).val.map i
          ((kernel.ι g).val.app (.op U.1) (localIdealElement f U r hr)) := by
    simpa only [idealModule, idealModuleRaw, ModuleCat.hom_comp,
      LinearMap.coe_comp, Function.comp_apply, ModuleCat.restrictScalars.map_apply] using hnat
  rw [hnat']
  change Y.presheaf.map i
    ((kernel.ι g).val.app (.op U.1) (localIdealElement f U r hr)) = _
  rw [← idealModuleAppIdealIso_coe f U]
  rw [idealModuleAppIdealIso_hom_localIdealElement]
  change Y.presheaf.map i r = _
  congr

/-- A generator of the affine ideal gives a global section of the restriction of
`idealModule f` to that affine open. -/
noncomputable def localIdealGenerator {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (U : Y.affineOpens) (r : Γ(Y, U.1)) (hr : r ∈ f.ker.ideal U) :
    Γ((idealModule f).restrict U.1.ι, (⊤ : U.1.toScheme.Opens)) :=
  ((idealModule f).restrictAppIso U.1.ι (⊤ : U.1.toScheme.Opens)).inv
    ((idealModule f).presheaf.map (eqToHom U.1.ι_image_top).op
      (localIdealElement f U r hr))

/-- Multiplication by a chosen local generator, viewed as a morphism from the
structure sheaf to the restricted ideal module. -/
noncomputable def localIdealGeneratorHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (U : Y.affineOpens) (r : Γ(Y, U.1)) (hr : r ∈ f.ker.ideal U) :
    Scheme.Modules.unitObj U.1.toScheme ⟶ (idealModule f).restrict U.1.ι :=
  ((idealModule f).restrict U.1.ι).unitHomEquiv.symm
    (moduleSectionsOfTop _ (localIdealGenerator f U r hr))

@[simp]
theorem localIdealGeneratorHom_app_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (U : Y.affineOpens) (r : Γ(Y, U.1)) (hr : r ∈ f.ker.ideal U)
    (W : U.1.toScheme.Opens) (a : Γ(U.1.toScheme, W)) :
    (localIdealGeneratorHom f U r hr).val.app (.op W) a =
      a • ((idealModule f).restrict U.1.ι).presheaf.map
        (homOfLE (le_top : W ≤ (⊤ : U.1.toScheme.Opens))).op
        (localIdealGenerator f U r hr) := by
  rfl

@[simp]
theorem restrictAppIso_hom_localIdealGenerator {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (U : Y.affineOpens) (r : Γ(Y, U.1)) (hr : r ∈ f.ker.ideal U) :
    ((idealModule f).restrictAppIso U.1.ι (⊤ : U.1.toScheme.Opens)).hom
        (localIdealGenerator f U r hr) =
      (idealModule f).presheaf.map (eqToHom U.1.ι_image_top).op
        (localIdealElement f U r hr) := by
  simp [localIdealGenerator]

/-- The basic open of an affine chart corresponding to a section of the chart's
coordinate ring. -/
noncomputable def chartBasicOpen {Y : Scheme.{u}} (U : Y.affineOpens)
    (t : Γ(Y, U.1)) : U.1.toScheme.Opens :=
  U.1.toScheme.basicOpen (U.1.topIso.inv t)

/-- The image in the ambient scheme of `chartBasicOpen`, with its affine-open
structure retained definitionally. -/
noncomputable def chartBasicOpenImage {Y : Scheme.{u}} (U : Y.affineOpens)
    (t : Γ(Y, U.1)) : Y.affineOpens :=
  ⟨U.1.ι ''ᵁ chartBasicOpen U t, by
    rw [chartBasicOpen, U.1.ι_image_basicOpen_topIso_inv]
    exact (Y.affineBasicOpen t).2⟩

@[simp]
theorem chartBasicOpenImage_eq_affineBasicOpen {Y : Scheme.{u}}
    (U : Y.affineOpens) (t : Γ(Y, U.1)) :
    chartBasicOpenImage U t = Y.affineBasicOpen t := by
  apply Subtype.ext
  exact U.1.ι_image_basicOpen_topIso_inv t

theorem chartBasicOpenImage_le {Y : Scheme.{u}} (U : Y.affineOpens)
    (t : Γ(Y, U.1)) : chartBasicOpenImage U t ≤ U := by
  rw [chartBasicOpenImage_eq_affineBasicOpen]
  exact Y.affineBasicOpen_le t

theorem isBasis_chartBasicOpen {Y : Scheme.{u}} (U : Y.affineOpens) :
    Opens.IsBasis (Set.range (chartBasicOpen U)) := by
  rw [show Set.range (chartBasicOpen U) =
      Set.range (U.1.toScheme.basicOpen :
        Γ(U.1.toScheme, ⊤) → U.1.toScheme.Opens) by
    ext W
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨U.1.topIso.inv t, rfl⟩
    · rintro ⟨t, rfl⟩
      refine ⟨U.1.topIso.hom t, ?_⟩
      change U.1.toScheme.basicOpen (U.1.topIso.inv (U.1.topIso.hom t)) = _
      rw [Iso.hom_inv_id_apply]]
  exact isBasis_basicOpen U.1.toScheme

/-- A chart-basic affine refinement of an ambient open neighborhood. -/
theorem exists_chartBasicOpenImage_le_of_mem
    {Y : Scheme.{u}} (W : Y.affineOpens) (O : Y.Opens) (x : Y)
    (hxW : x ∈ W.1) (hxO : x ∈ O) :
    ∃ a : Γ(Y, W.1), x ∈ (chartBasicOpenImage W a).1 ∧
      (chartBasicOpenImage W a).1 ≤ O := by
  let xW : W.1 := ⟨x, hxW⟩
  have hxpre : xW ∈ W.1.ι ⁻¹ᵁ O := hxO
  obtain ⟨_, ⟨a, rfl⟩, hxa, hle⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_chartBasicOpen W) hxpre
  refine ⟨a, ?_, ?_⟩
  · change x ∈ W.1.ι ''ᵁ chartBasicOpen W a
    exact ⟨xW, hxa, rfl⟩
  · intro y hy
    change y ∈ W.1.ι ''ᵁ chartBasicOpen W a at hy
    obtain ⟨yW, hyW, rfl⟩ := hy
    exact hle hyW

theorem ideal_chartBasicOpenImage_span_nzd {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (U : Y.affineOpens) (r : Γ(Y, U.1))
    (hspan : I.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, U.1)) (t : Γ(Y, U.1)) :
    I.ideal (chartBasicOpenImage U t) =
        Ideal.span {Y.presheaf.map (homOfLE (chartBasicOpenImage_le U t)).op r} ∧
      Y.presheaf.map (homOfLE (chartBasicOpenImage_le U t)).op r ∈
        nonZeroDivisors Γ(Y, (chartBasicOpenImage U t).1) := by
  constructor
  · rw [← I.map_ideal (chartBasicOpenImage_le U t), hspan,
      Ideal.map_span, Set.image_singleton]
    congr 2
  · convert (ideal_basicOpen_span_nzd I U r hspan hnzd t).2 using 1
    let p : {V : Y.affineOpens // V ≤ U} :=
      ⟨chartBasicOpenImage U t, chartBasicOpenImage_le U t⟩
    let q : {V : Y.affineOpens // V ≤ U} :=
      ⟨Y.affineBasicOpen t, Y.affineBasicOpen_le t⟩
    have hpq : p = q := by
      apply Subtype.ext
      exact chartBasicOpenImage_eq_affineBasicOpen U t
    refine (congrArg (fun V : {V : Y.affineOpens // V ≤ U} ↦
      Y.presheaf.map (homOfLE V.2).op r ∈
        nonZeroDivisors Γ(Y, V.1.1)) hpq).to_iff.trans ?_
    have hmap : Y.presheaf.map (homOfLE q.2).op r =
        Y.presheaf.map (homOfLE (Y.basicOpen_le t)).op r := by
      exact congr($(Y.presheaf.congr_map (Subsingleton.elim _ _)).hom r)
    dsimp only [q] at hmap ⊢
    cases hmap
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- On a chart basic open, the local generator morphism is multiplication by the
restricted affine generator, after the canonical affine kernel identification. -/
theorem localIdealGeneratorHom_chartBasicOpen_formula {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] (U : Y.affineOpens) (r : Γ(Y, U.1))
    (hr : r ∈ f.ker.ideal U) (t : Γ(Y, U.1))
    (a : Γ(U.1.toScheme, chartBasicOpen U t)) :
    ((idealModuleAppIdealIso f (chartBasicOpenImage U t)).hom
      (((idealModule f).restrictAppIso U.1.ι (chartBasicOpen U t)).hom
        ((localIdealGeneratorHom f U r hr).val.app (.op (chartBasicOpen U t)) a))).1 =
      (U.1.ι.appIso (chartBasicOpen U t)).inv a *
        Y.presheaf.map (homOfLE (chartBasicOpenImage_le U t)).op r := by
  rw [localIdealGeneratorHom_app_apply]
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
  rw [map_smul]
  change (show Γ(Y, (chartBasicOpenImage U t).1) from
      (U.1.ι.appIso (chartBasicOpen U t)).inv a) *
      (((idealModuleAppIdealIso f (chartBasicOpenImage U t)).hom
        (((idealModule f).restrictAppIso U.1.ι (chartBasicOpen U t)).hom
          (((idealModule f).restrict U.1.ι).presheaf.map
            (homOfLE (le_top : chartBasicOpen U t ≤
              (⊤ : U.1.toScheme.Opens))).op
            (localIdealGenerator f U r hr)))).1 :
        Γ(Y, (chartBasicOpenImage U t).1)) = _
  congr 1
  rw [Scheme.Modules.map_restrictAppIso_hom_apply]
  rw [restrictAppIso_hom_localIdealGenerator]
  convert idealModuleAppIdealIso_coe_map_localIdealElement f U
    (chartBasicOpenImage U t) (chartBasicOpenImage_le U t) r hr using 1
  · congr 2
    rw [← ConcreteCategory.comp_apply, ← (idealModule f).presheaf.map_comp]
    exact congr($((idealModule f).presheaf.congr_map
      (Subsingleton.elim _ _)).hom (localIdealElement f U r hr))
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- A Cartier generator makes the local ideal-generator morphism bijective on every
basic open of its affine chart. -/
theorem localIdealGeneratorHom_chartBasicOpen_bijective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] (U : Y.affineOpens) (r : Γ(Y, U.1))
    (hr : r ∈ f.ker.ideal U) (hspan : f.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, U.1)) (t : Γ(Y, U.1)) :
    Function.Bijective ((localIdealGeneratorHom f U r hr).val.app
      (.op (chartBasicOpen U t))) := by
  let W := chartBasicOpen U t
  let V := chartBasicOpenImage U t
  let eR := U.1.ι.appIso W
  let eM := (idealModule f).restrictAppIso U.1.ι W
  let eI := idealModuleAppIdealIso f V
  let rt := Y.presheaf.map (homOfLE (chartBasicOpenImage_le U t)).op r
  have hp := ideal_chartBasicOpenImage_span_nzd f.ker U r hspan hnzd t
  constructor
  · intro a b hab
    have hout := congr_arg (fun y ↦ ((eI.hom (eM.hom y)).1)) hab
    have hmul : eR.inv a * rt = eR.inv b * rt := by
      dsimp only [eR, eM, eI, rt, W, V] at hout ⊢
      rw [localIdealGeneratorHom_chartBasicOpen_formula,
        localIdealGeneratorHom_chartBasicOpen_formula] at hout
      exact hout
    have hcoeff := (mul_cancel_right_mem_nonZeroDivisors hp.2).mp hmul
    exact (ConcreteCategory.bijective_of_isIso eR.inv).1 hcoeff
  · intro y
    let yI := eI.hom (eM.hom y)
    have hyspan : yI.1 ∈ Ideal.span {rt} := by
      rw [← hp.1]
      exact yI.2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hyspan
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso eR.inv).2 c
    refine ⟨a, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso eM.hom).1
    apply (ConcreteCategory.bijective_of_isIso eI.hom).1
    apply Subtype.ext
    rw [localIdealGeneratorHom_chartBasicOpen_formula]
    rw [ha]
    exact hc

/-- A principal nonzerodivisor chart trivializes the corresponding restricted ideal
module. -/
theorem isIso_localIdealGeneratorHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (U : Y.affineOpens) (r : Γ(Y, U.1))
    (hr : r ∈ f.ker.ideal U) (hspan : f.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, U.1)) :
    IsIso (localIdealGeneratorHom f U r hr) := by
  letI hreflect : (SheafOfModules.toSheaf.{u}
      U.1.toScheme.ringCatSheaf).ReflectsIsomorphisms :=
    PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
  haveI hmap : IsIso ((SheafOfModules.toSheaf.{u} U.1.toScheme.ringCatSheaf).map
      (localIdealGeneratorHom f U r hr)) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (isBasis_chartBasicOpen U)
    intro t
    rw [ConcreteCategory.isIso_iff_bijective]
    exact localIdealGeneratorHom_chartBasicOpen_bijective f U r hr hspan hnzd t
  exact @Functor.ReflectsIsomorphisms.reflects _ _ _ _
    (SheafOfModules.toSheaf.{u} U.1.toScheme.ringCatSheaf) hreflect _ _
    (localIdealGeneratorHom f U r hr) hmap

/-- The explicit trivialization of the kernel ideal module on a principal
nonzerodivisor chart. -/
noncomputable def localIdealGeneratorIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (U : Y.affineOpens) (r : Γ(Y, U.1))
    (hr : r ∈ f.ker.ideal U) (hspan : f.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, U.1)) :
    Scheme.Modules.unitObj U.1.toScheme ≅ (idealModule f).restrict U.1.ι := by
  letI := isIso_localIdealGeneratorHom f U r hr hspan hnzd
  exact asIso (localIdealGeneratorHom f U r hr)

/-- A kernel ideal which is affine-locally principal on a nonzerodivisor is an
invertible sheaf of modules. -/
theorem idealModule_isInvertible_of_locallyPrincipal {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f]
    (hlocal : ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧ ∃ r : Γ(Y, U.1),
      f.ker.ideal U = Ideal.span {r} ∧
        r ∈ nonZeroDivisors Γ(Y, U.1)) :
    Scheme.Modules.IsInvertible (idealModule f) := by
  choose U hyU r hspan hnzd using hlocal
  refine ⟨Y, fun y => (U y).1, ?_, fun y => ?_⟩
  · rw [eq_top_iff]
    exact fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y⟩
  · have hr : r y ∈ f.ker.ideal (U y) := by
      rw [hspan y]
      exact Ideal.mem_span_singleton_self (r y)
    exact ⟨Scheme.Modules.pullbackIsoOfRestrictIso (idealModule f) (U y).1
      (localIdealGeneratorIso f (U y) (r y) hr (hspan y) (hnzd y)).symm⟩

/-- A section on an ambient open, transported to the top open of its open subscheme. -/
noncomputable def affineOpenTopSection {Y : Scheme.{u}} (U : Y.affineOpens)
    (r : Γ(Y, U.1)) : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
  (U.1.ι.appIso ⊤).hom
    (Y.presheaf.map (eqToHom U.1.ι_image_top).op r)

/-- A top-open section of an open subscheme, transported back to the corresponding
ambient open. -/
noncomputable def affineOpenAmbientSection {Y : Scheme.{u}} (U : Y.affineOpens)
    (r : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))) : Γ(Y, U.1) :=
  Y.presheaf.map (homOfLE U.1.ι_image_top.ge).op
    ((U.1.ι.appIso ⊤).inv r)

@[simp]
theorem affineOpenAmbientSection_add {Y : Scheme.{u}} (U : Y.affineOpens)
    (r s : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))) :
    affineOpenAmbientSection U (r + s) =
      affineOpenAmbientSection U r + affineOpenAmbientSection U s := by
  unfold affineOpenAmbientSection
  rw [map_add, map_add]

@[simp]
theorem affineOpenAmbientSection_mul {Y : Scheme.{u}} (U : Y.affineOpens)
    (r s : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))) :
    affineOpenAmbientSection U (r * s) =
      affineOpenAmbientSection U r * affineOpenAmbientSection U s := by
  unfold affineOpenAmbientSection
  rw [map_mul, map_mul]

@[simp]
theorem affineOpenAmbientSection_zero {Y : Scheme.{u}} (U : Y.affineOpens) :
    affineOpenAmbientSection U 0 = 0 := by
  unfold affineOpenAmbientSection
  rw [map_zero, map_zero]

@[simp]
theorem affineOpenTopSection_ambientSection {Y : Scheme.{u}}
    (U : Y.affineOpens) (r : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))) :
    affineOpenTopSection U (affineOpenAmbientSection U r) = r := by
  rw [affineOpenTopSection, affineOpenAmbientSection]
  change (U.1.ι.appIso ⊤).hom
      ((Y.presheaf.map (homOfLE U.1.ι_image_top.ge).op ≫
        Y.presheaf.map (eqToHom U.1.ι_image_top).op)
          ((U.1.ι.appIso ⊤).inv r)) = r
  have hmap : Y.presheaf.map
      (homOfLE U.1.ι_image_top.ge).op ≫
        Y.presheaf.map (eqToHom U.1.ι_image_top).op =
      𝟙 _ := by
    rw [← Y.presheaf.map_comp]
    simp
  rw [hmap]
  change (U.1.ι.appIso ⊤).hom ((U.1.ι.appIso ⊤).inv r) = r
  exact Iso.inv_hom_id_apply _ r

@[simp]
theorem affineOpenAmbientSection_topSection {Y : Scheme.{u}}
    (U : Y.affineOpens) (r : Γ(Y, U.1)) :
    affineOpenAmbientSection U (affineOpenTopSection U r) = r := by
  rw [affineOpenAmbientSection, affineOpenTopSection]
  rw [Iso.hom_inv_id_apply]
  change (Y.presheaf.map (eqToHom U.1.ι_image_top).op ≫
    Y.presheaf.map (homOfLE U.1.ι_image_top.ge).op) r = r
  rw [← Y.presheaf.map_comp]
  simp

private noncomputable def affineOpenSectionsIso
    {Y : Scheme.{u}} (U : Y.affineOpens) :
    Γ(Y, U.1) ≅ Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
  Y.presheaf.mapIso (eqToIso U.1.ι_image_top).op ≪≫ U.1.ι.appIso ⊤

/-- The ambient affine section obtained by pulling a chart section through a
restricted morphism. -/
noncomputable def affinePullbackSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (r : Γ(Y, V.1)) : Γ(X, U.1) :=
  affineOpenAmbientSection U
    ((f.resLE V.1 U.1 hUV).appTop.hom (affineOpenTopSection V r))

@[simp]
theorem affineOpenTopSection_affinePullbackSection
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (r : Γ(Y, V.1)) :
    affineOpenTopSection U (affinePullbackSection f U V hUV r) =
      (f.resLE V.1 U.1 hUV).appTop.hom (affineOpenTopSection V r) := by
  simp [affinePullbackSection]

/-- Pulling a nonzerodivisor through a flat morphism preserves the
nonzerodivisor condition on affine charts. -/
theorem affinePullbackSection_mem_nonZeroDivisors
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (U : X.affineOpens) (V : Y.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) {r : Γ(Y, V.1)}
    (hr : r ∈ nonZeroDivisors Γ(Y, V.1)) :
    affinePullbackSection f U V hUV r ∈
      nonZeroDivisors Γ(X, U.1) := by
  haveI : IsAffine U.1.toScheme := U.2
  haveI : IsAffine V.1.toScheme := V.2
  have hrTop : affineOpenTopSection V r ∈
      nonZeroDivisors Γ(V.1.toScheme, (⊤ : V.1.toScheme.Opens)) := by
    change (affineOpenSectionsIso V).commRingCatIsoToRingEquiv r ∈
      nonZeroDivisors Γ(V.1.toScheme, (⊤ : V.1.toScheme.Opens))
    rw [← MulEquivClass.map_nonZeroDivisors
      (affineOpenSectionsIso V).commRingCatIsoToRingEquiv]
    exact ⟨r, hr, rfl⟩
  have hrPullback := RingHom.Flat.map_mem_nonZeroDivisors
    (f.resLE V.1 U.1 hUV).flat_appTop hrTop
  change (affineOpenSectionsIso U).symm.commRingCatIsoToRingEquiv
      ((f.resLE V.1 U.1 hUV).appTop.hom
        (affineOpenTopSection V r)) ∈ nonZeroDivisors Γ(X, U.1)
  rw [← MulEquivClass.map_nonZeroDivisors
    (affineOpenSectionsIso U).symm.commRingCatIsoToRingEquiv]
  exact ⟨_, hrPullback, rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem localIdealGeneratorHom_comp_restrictIdealModuleToUnit
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.affineOpens) (r : Γ(Y, U.1)) (hr : r ∈ f.ker.ideal U) :
    localIdealGeneratorHom f U r hr ≫ restrictIdealModuleToUnit f U.1.ι =
      unitEndomorphismOfTopSection (affineOpenTopSection U r) := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  apply TopCat.Sheaf.hom_ext (B := fun t => chartBasicOpen U t)
    ((PresheafOfModules.toPresheaf _).obj
      (Scheme.Modules.unitObj U.1.toScheme).val)
    ((SheafOfModules.toSheaf U.1.toScheme.ringCatSheaf).obj
      (Scheme.Modules.unitObj U.1.toScheme))
    (isBasis_chartBasicOpen U)
  intro t
  ext x
  let W := chartBasicOpen U t
  let V := chartBasicOpenImage U t
  let a : Γ(U.1.toScheme, W) := x
  change (localIdealGeneratorHom f U r hr ≫
      restrictIdealModuleToUnit f U.1.ι).val.app (.op W) a =
    (unitEndomorphismOfTopSection (affineOpenTopSection U r)).val.app (.op W) a
  rw [unitEndomorphismOfTopSection_app_apply]
  change (U.1.ι.appIso W).hom
      ((idealModuleToUnit f).val.app (.op (U.1.ι ''ᵁ W))
        ((localIdealGeneratorHom f U r hr).val.app (.op W) a)) =
    a * U.1.toScheme.presheaf.map
      (homOfLE (le_top : W ≤ (⊤ : U.1.toScheme.Opens))).op
      (affineOpenTopSection U r)
  dsimp only [W, V]
  change (U.1.ι.appIso (chartBasicOpen U t)).hom
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).val.app
        (.op (chartBasicOpenImage U t).1)
        ((localIdealGeneratorHom f U r hr).val.app
          (.op (chartBasicOpen U t)) a)) = _
  rw [← idealModuleAppIdealIso_coe f V]
  change (U.1.ι.appIso (chartBasicOpen U t)).hom
      (((idealModuleAppIdealIso f (chartBasicOpenImage U t)).hom
        (((idealModule f).restrictAppIso U.1.ι (chartBasicOpen U t)).hom
          ((localIdealGeneratorHom f U r hr).val.app
            (.op (chartBasicOpen U t)) a))).1) = _
  rw [localIdealGeneratorHom_chartBasicOpen_formula]
  rw [map_mul, Iso.inv_hom_id_apply]
  congr 1
  let i : Opposite.op (⊤ : U.1.toScheme.Opens) ⟶
      Opposite.op (chartBasicOpen U t) :=
    (homOfLE (le_top : chartBasicOpen U t ≤ (⊤ : U.1.toScheme.Opens))).op
  have hmaps :
      Y.presheaf.map (homOfLE (chartBasicOpenImage_le U t)).op =
        Y.presheaf.map (eqToHom U.1.ι_image_top).op ≫
          Y.presheaf.map (U.1.ι.opensFunctor.map i.unop).op := by
    rw [← Y.presheaf.map_comp]
    exact Y.presheaf.congr_map (Subsingleton.elim _ _)
  rw [affineOpenTopSection]
  calc
    (U.1.ι.appIso (chartBasicOpen U t)).hom
        (Y.presheaf.map (homOfLE (chartBasicOpenImage_le U t)).op r) =
      (U.1.ι.appIso (chartBasicOpen U t)).hom
        ((Y.presheaf.map (eqToHom U.1.ι_image_top).op ≫
          Y.presheaf.map (U.1.ι.opensFunctor.map i.unop).op) r) := by
      rw [hmaps]
    _ = U.1.toScheme.presheaf.map i
        ((U.1.ι.appIso ⊤).hom
          (Y.presheaf.map (eqToHom U.1.ι_image_top).op r)) := by
      have h := congrArg (fun q => q.hom
          (Y.presheaf.map (eqToHom U.1.ι_image_top).op r))
        (U.1.ι.appIso_hom_naturality i)
      simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using h

/-- Affine-chart formula for an arbitrary scheme-theoretic inverse image of an ideal. -/
theorem ideal_comap_affineOpens_nested {X Y : Scheme.{u}}
    (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    let eU : ↑Γ(X, U.1.ι ''ᵁ ⊤) ≃+* ↑Γ(U.1.toScheme, ⊤) :=
      (U.1.ι.appIso ⊤).commRingCatIsoToRingEquiv
    let eV : ↑Γ(Y, V.1.ι ''ᵁ ⊤) ≃+* ↑Γ(V.1.toScheme, ⊤) :=
      (V.1.ι.appIso ⊤).commRingCatIsoToRingEquiv
    (I.comap f).ideal U =
      ((((I.ideal ⟨V.1.ι ''ᵁ ⊤,
          (isAffineOpen_top _).image_of_isOpenImmersion _⟩).map
        eV.toRingHom).map
          ((f.resLE V.1 U.1 hUV).appTop).hom).map
            eU.symm.toRingHom).map
              (X.presheaf.map (homOfLE U.1.ι_image_top.ge).op).hom := by
  classical
  haveI : IsAffine U.1.toScheme := U.2
  haveI : IsAffine V.1.toScheme := V.2
  let eU : ↑Γ(X, U.1.ι ''ᵁ ⊤) ≃+* ↑Γ(U.1.toScheme, ⊤) :=
    (U.1.ι.appIso ⊤).commRingCatIsoToRingEquiv
  let eV : ↑Γ(Y, V.1.ι ''ᵁ ⊤) ≃+* ↑Γ(V.1.toScheme, ⊤) :=
    (V.1.ι.appIso ⊤).commRingCatIsoToRingEquiv
  have hBV : ((I.comap V.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ :
        Ideal ↑Γ(V.1.toScheme, ⊤)) =
      (I.ideal ⟨V.1.ι ''ᵁ ⊤,
        (isAffineOpen_top _).image_of_isOpenImmersion _⟩).map eV.toRingHom :=
    (Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I V.1.ι
      ⟨⊤, isAffineOpen_top _⟩).trans (Ideal.comap_symm eV)
  have hT := Scheme.IdealSheafData.comap_comap_ι_ideal_top
    I f U V hUV
  rw [hBV] at hT
  have hB : ((I.comap f).ideal ⟨U.1.ι ''ᵁ ⊤,
        (isAffineOpen_top _).image_of_isOpenImmersion _⟩ :
        Ideal ↑Γ(X, U.1.ι ''ᵁ ⊤)) =
      (((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ :
          Ideal ↑Γ(U.1.toScheme, ⊤)).map eU.symm.toRingHom := by
    have h1 : (((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ :
          Ideal ↑Γ(U.1.toScheme, ⊤)) =
        ((I.comap f).ideal ⟨U.1.ι ''ᵁ ⊤,
          (isAffineOpen_top _).image_of_isOpenImmersion _⟩).map eU.toRingHom :=
      (Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion
        (I.comap f) U.1.ι ⟨⊤, isAffineOpen_top _⟩).trans
          (Ideal.comap_symm eU)
    have h2 := congrArg (Ideal.map eU.symm.toRingHom) h1
    exact (h2.trans (Ideal.map_of_equiv eU)).symm
  have hA : ((I.comap f).ideal U : Ideal ↑Γ(X, U.1)) =
      ((I.comap f).ideal ⟨U.1.ι ''ᵁ ⊤,
        (isAffineOpen_top _).image_of_isOpenImmersion _⟩).map
          (X.presheaf.map (homOfLE U.1.ι_image_top.ge).op).hom :=
    (Scheme.IdealSheafData.map_ideal (I.comap f) U.1.ι_image_top.ge).symm
  rw [hA, hB, hT]

/-- Transporting a principal ideal to the image of the top open transports its
generator through the canonical ring equivalence. -/
theorem ideal_imageTop_span {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (V : Y.affineOpens) (r : Γ(Y, V.1))
    (hspan : I.ideal V = Ideal.span {r}) :
    I.ideal ⟨V.1.ι ''ᵁ ⊤,
        (isAffineOpen_top _).image_of_isOpenImmersion _⟩ =
      Ideal.span {Y.presheaf.map (eqToHom V.1.ι_image_top).op r} := by
  let e : ↑Γ(Y, V.1) ≃+* ↑Γ(Y, V.1.ι ''ᵁ ⊤) :=
    (Y.presheaf.mapIso (eqToIso V.1.ι_image_top).op).commRingCatIsoToRingEquiv
  have hV : I.ideal V =
      (I.ideal ⟨V.1.ι ''ᵁ ⊤,
        (isAffineOpen_top _).image_of_isOpenImmersion _⟩).map
          e.symm.toRingHom := by
    exact (Scheme.IdealSheafData.map_ideal I V.1.ι_image_top.ge).symm
  have h2 := congrArg (Ideal.map e.toRingHom) hV
  rw [hspan, Ideal.map_span, Set.image_singleton] at h2
  have hc : ((I.ideal ⟨V.1.ι ''ᵁ ⊤,
        (isAffineOpen_top _).image_of_isOpenImmersion _⟩).map
      e.symm.toRingHom).map e.toRingHom =
      I.ideal ⟨V.1.ι ''ᵁ ⊤,
        (isAffineOpen_top _).image_of_isOpenImmersion _⟩ := by
    simpa using Ideal.map_of_equiv e.symm
  rw [hc] at h2
  change I.ideal ⟨V.1.ι ''ᵁ ⊤,
      (isAffineOpen_top _).image_of_isOpenImmersion _⟩ =
    Ideal.span {e.toRingHom r}
  exact h2.symm

/-- A principal ideal pulls back on affine charts to the principal ideal generated
by the explicitly transported section. -/
theorem ideal_comap_affineOpens_span {X Y : Scheme.{u}}
    (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (r : Γ(Y, V.1))
    (hspan : I.ideal V = Ideal.span {r}) :
    (I.comap f).ideal U =
      Ideal.span {affinePullbackSection f U V hUV r} := by
  rw [ideal_comap_affineOpens_nested I f U V hUV]
  rw [ideal_imageTop_span I V r hspan]
  simp only [Ideal.map_span, Set.image_singleton]
  rfl

/-- If two principal ideals agree and one generator is a nonzerodivisor, then so is
the other generator. -/
theorem mem_nonZeroDivisors_of_span_eq_span {R : Type*} [CommRing R]
    {a b : R} (h : Ideal.span {a} = Ideal.span {b})
    (hb : b ∈ nonZeroDivisors R) : a ∈ nonZeroDivisors R := by
  have ha : a ∈ Ideal.span {b} := by
    rw [← h]
    exact Ideal.mem_span_singleton_self a
  have hb' : b ∈ Ideal.span {a} := by
    rw [h]
    exact Ideal.mem_span_singleton_self b
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hb'
  have hdc : d * c = 1 :=
    (mul_cancel_right_mem_nonZeroDivisors hb).mp (by
      calc
        (d * c) * b = d * (c * b) := mul_assoc _ _ _
        _ = d * a := by rw [hc]
        _ = b := hd
        _ = 1 * b := (one_mul b).symm)
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  have hxcb : (x * c) * b = 0 * b := by
    rw [zero_mul, mul_assoc, hc, hx]
  have hxc : x * c = 0 :=
    (mul_cancel_right_mem_nonZeroDivisors hb).mp hxcb
  calc
    x = x * 1 := (mul_one x).symm
    _ = x * (d * c) := by rw [hdc]
    _ = (x * c) * d := by ac_rfl
    _ = 0 := by rw [hxc, zero_mul]

/-- The ideal module inclusion is a monomorphism. -/
theorem idealModuleToUnit_mono {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mono (idealModuleToUnit f) := by
  change Mono (kernel.ι
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
  infer_instance

theorem restrictIdealModuleToUnit_mono {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (j : Y' ⟶ Y) [IsOpenImmersion j] :
    Mono (restrictIdealModuleToUnit f j) := by
  apply (SheafOfModules.forget Y'.ringCatSheaf).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro W x y hxy
  have hxy' := (ConcreteCategory.bijective_of_isIso (j.appIso W.unop).hom).1 hxy
  let F := SheafOfModules.evaluation Y.ringCatSheaf (.op (j ''ᵁ W.unop))
  let u := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  change (F.map (kernel.ι u)) x = (F.map (kernel.ι u)) y at hxy'
  haveI : Mono (F.map (kernel.ι u)) := inferInstance
  exact (ModuleCat.mono_iff_injective (F.map (kernel.ι u))).mp inferInstance hxy'

/-- The local Cartier-generator trivialization, expressed using module pullback
rather than open restriction. -/
noncomputable def localIdealGeneratorPullbackIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] (U : Y.affineOpens)
    (r : Γ(Y, U.1)) (hr : r ∈ f.ker.ideal U)
    (hspan : f.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, U.1)) :
    Scheme.Modules.unitObj U.1.toScheme ≅
      (Scheme.Modules.pullback U.1.ι).obj (idealModule f) :=
  localIdealGeneratorIso f U r hr hspan hnzd ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.1.ι).app (idealModule f)

/-- Pulling a Cartier-generator trivialization through a morphism gives a
trivialization of the pulled ideal module on an affine source chart. -/
noncomputable def pullbackLocalIdealGeneratorIso
    {A X Y : Scheme.{u}} (k : A ⟶ Y) [QuasiCompact k] (g : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ g ⁻¹ᵁ V.1)
    (r : Γ(Y, V.1)) (hr : r ∈ k.ker.ideal V)
    (hspan : k.ker.ideal V = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, V.1)) :
    Scheme.Modules.unitObj U.1.toScheme ≅
      (Scheme.Modules.pullback U.1.ι).obj
        ((Scheme.Modules.pullback g).obj (idealModule k)) :=
  let q := g.resLE V.1 U.1 hUV
  (Scheme.Modules.pullbackUnitIso q).symm ≪≫
    (Scheme.Modules.pullback q).mapIso
      (localIdealGeneratorPullbackIso k V r hr hspan hnzd) ≪≫
    (Scheme.Modules.pullbackComp q V.1.ι).app (idealModule k) ≪≫
    (Scheme.Modules.pullbackCongr (g.resLE_comp_ι hUV)).app (idealModule k) ≪≫
    ((Scheme.Modules.pullbackComp U.1.ι g).app (idealModule k)).symm

/-- The inclusion of an ideal module after restricting to an affine open, written
in pullback coordinates. -/
noncomputable def pullbackIdealModuleToUnit {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.affineOpens) :
    (Scheme.Modules.pullback U.1.ι).obj (idealModule f) ⟶
      Scheme.Modules.unitObj U.1.toScheme :=
  (Scheme.Modules.restrictFunctorIsoPullback U.1.ι).inv.app (idealModule f) ≫
    restrictIdealModuleToUnit f U.1.ι

theorem pullbackIdealModuleToUnit_mono {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.affineOpens) :
    Mono (pullbackIdealModuleToUnit f U) := by
  dsimp only [pullbackIdealModuleToUnit]
  letI : Mono (restrictIdealModuleToUnit f U.1.ι) :=
    restrictIdealModuleToUnit_mono f U.1.ι
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem localIdealGeneratorPullbackIso_hom_comp_toUnit
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.affineOpens) (r : Γ(Y, U.1)) (hr : r ∈ f.ker.ideal U)
    (hspan : f.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, U.1)) :
    (localIdealGeneratorPullbackIso f U r hr hspan hnzd).hom ≫
        pullbackIdealModuleToUnit f U =
      unitEndomorphismOfTopSection (affineOpenTopSection U r) := by
  dsimp only [localIdealGeneratorPullbackIso, pullbackIdealModuleToUnit]
  simp only [Iso.trans_hom]
  rw [Category.assoc]
  erw [Iso.hom_inv_id_assoc]
  change localIdealGeneratorHom f U r hr ≫
      restrictIdealModuleToUnit f U.1.ι = _
  exact localIdealGeneratorHom_comp_restrictIdealModuleToUnit f U r hr

/-- The pulled ideal inclusion followed by the canonical structure-sheaf
identification. -/
noncomputable def pulledIdealModuleToUnit {A X Y : Scheme.{u}}
    (k : A ⟶ Y) (g : X ⟶ Y) :
    (Scheme.Modules.pullback g).obj (idealModule k) ⟶
      Scheme.Modules.unitObj X :=
  (Scheme.Modules.pullback g).map (idealModuleToUnit k) ≫
    (Scheme.Modules.pullbackUnitIso g).hom

/-- The canonical pulled ideal inclusion remains a monomorphism along an open immersion. -/
theorem pulledIdealModuleToUnit_mono_of_isOpenImmersion
    {A X Y : Scheme.{u}} (k : A ⟶ Y) (g : X ⟶ Y)
    [IsOpenImmersion g] : Mono (pulledIdealModuleToUnit k g) := by
  haveI hrestrictToUnit : Mono (restrictIdealModuleToUnit k g) :=
    restrictIdealModuleToUnit_mono k g
  haveI hrestrict : Mono
      ((Scheme.Modules.restrictFunctor g).map (idealModuleToUnit k)) := by
    exact mono_of_mono_fac (h := restrictIdealModuleToUnit k g) rfl
  let e := Scheme.Modules.restrictFunctorIsoPullback g
  haveI hpullbackComp : Mono
      (e.hom.app (idealModule k) ≫
        (Scheme.Modules.pullback g).map (idealModuleToUnit k)) := by
    rw [← e.hom.naturality (idealModuleToUnit k)]
    infer_instance
  haveI hpullback : Mono
      ((Scheme.Modules.pullback g).map (idealModuleToUnit k)) :=
    (mono_comp_iff_of_isIso _ _).mp hpullbackComp
  dsimp only [pulledIdealModuleToUnit]
  infer_instance


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem pullbackUnitIso_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((Scheme.Modules.pullbackComp f g).app (Scheme.Modules.unitObj Z)).hom ≫
        (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom =
      (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫
        (Scheme.Modules.pullbackUnitIso f).hom := by
  let α := (Scheme.Modules.pullbackComp f g).app (Scheme.Modules.unitObj Z)
  let adjf := Scheme.Modules.pullbackPushforwardAdjunction f
  let adjg := Scheme.Modules.pullbackPushforwardAdjunction g
  let adjc := adjg.comp adjf
  let adjd := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let τ := Scheme.Modules.pushforwardComp f g
  have hconj : CategoryTheory.conjugateEquiv adjc adjd
      (Scheme.Modules.pullbackComp f g).inv = τ.hom :=
    Scheme.Modules.conjugateEquiv_pullbackComp_inv f g
  have hconjIso : CategoryTheory.conjugateIsoEquiv adjc adjd
      (Scheme.Modules.pullbackComp f g).symm =
      Scheme.Modules.pushforwardComp f g := by
    apply Iso.ext
    exact hconj
  have hconj' : CategoryTheory.conjugateEquiv adjd adjc
      (Scheme.Modules.pullbackComp f g).hom =
      (Scheme.Modules.pushforwardComp f g).inv := by
    have h := congrArg Iso.inv hconjIso
    exact h
  have hf : (adjf.homEquiv _ _)
      (Scheme.Modules.pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
    erw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  have hg : (adjg.homEquiv _ _)
      (Scheme.Modules.pullbackUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
    erw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  have hfg : (adjd.homEquiv _ _)
      (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom := by
    erw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  have hfgUnit : adjd.unit.app (Scheme.Modules.unitObj Z) ≫
      (Scheme.Modules.pushforward (f ≫ g)).map
        (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom := by
    simpa only [Adjunction.homEquiv_unit] using hfg
  apply (adjc.homEquiv _ _).injective
  have hleft : (adjc.homEquiv _ _)
      (α.hom ≫ (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom) =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom ≫
        τ.inv.app (Scheme.Modules.unitObj X) := by
    dsimp only [α]
    rw [Adjunction.homEquiv_unit, Functor.map_comp]
    erw [← Category.assoc,
      ← CategoryTheory.unit_conjugateEquiv adjd adjc
        (Scheme.Modules.pullbackComp f g).hom (Scheme.Modules.unitObj Z)]
    rw [Category.assoc]
    erw [← (CategoryTheory.conjugateEquiv adjd adjc
      (Scheme.Modules.pullbackComp f g).hom).naturality]
    rw [hconj']
    rw [← Category.assoc, hfgUnit]
  have hright : (adjc.homEquiv _ _)
      ((Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫
        (Scheme.Modules.pullbackUnitIso f).hom) =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
    change (adjg.homEquiv _ _)
      ((adjf.homEquiv _ _)
        ((Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫
          (Scheme.Modules.pullbackUnitIso f).hom)) = _
    rw [Adjunction.homEquiv_naturality_left, hf]
    rw [Adjunction.homEquiv_naturality_right, hg]
  rw [hleft, hright, unitToPushforwardObjUnit_comp]
  dsimp only [τ]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  let q := SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
    (Scheme.Modules.pushforward g).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
  change q ≫ 𝟙 _ = q
  exact Category.comp_id q

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem restrictAdjunction_homEquiv_restrictUnitIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    ((Scheme.Modules.restrictAdjunction f).homEquiv _ _)
        (Scheme.Modules.restrictUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  rw [Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  ext U
  change (((Scheme.Modules.restrictAdjunction f).unit.app
      (Scheme.Modules.unitObj Y)).val.app U ≫
        (((Scheme.Modules.pushforward f).map
          (Scheme.Modules.restrictUnitIso f).hom).val.app U))
      (show Γ(Y, U.unop) from 1) = _
  rw [ConcreteCategory.comp_apply]
  dsimp only [Scheme.Modules.restrictAdjunction]
  erw [SheafOfModules.pushforwardPushforwardAdj_unit_app_val_app]
  change (f.appIso (f ⁻¹ᵁ U.unop)).hom
      (Y.presheaf.map _ (1 : Γ(Y, U.unop))) =
    (f.app U.unop).hom 1
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem restrictFunctorIsoPullback_inv_comp_restrictUnitIso
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
  rw [restrictAdjunction_homEquiv_restrictUnitIso]
  rw [Adjunction.homEquiv_naturality_right]
  have he := CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app
    adjr adjp (Scheme.Modules.unitObj Y)
  change (adjr.homEquiv _ _) e.hom =
    adjp.unit.app (Scheme.Modules.unitObj Y) at he
  erw [he]
  have hp : adjp.unit.app (Scheme.Modules.unitObj Y) ≫
      (Scheme.Modules.pushforward f).map
        (Scheme.Modules.pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
    have hp0 : (adjp.homEquiv _ _)
        (Scheme.Modules.pullbackUnitIso f).hom =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
      erw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
    simpa only [Adjunction.homEquiv_unit] using hp0
  exact hp.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem pullbackIdealModuleToUnit_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.affineOpens) :
    pullbackIdealModuleToUnit f U =
      pulledIdealModuleToUnit f U.1.ι := by
  dsimp only [pullbackIdealModuleToUnit, pulledIdealModuleToUnit,
    restrictIdealModuleToUnit]
  rw [← (Scheme.Modules.restrictFunctorIsoPullback U.1.ι).inv.naturality_assoc
    (idealModuleToUnit f)]
  rw [restrictFunctorIsoPullback_inv_comp_restrictUnitIso]

theorem pullbackUnitIso_congr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) :
    ((Scheme.Modules.pullbackCongr h).app (Scheme.Modules.unitObj Y)).hom ≫
        (Scheme.Modules.pullbackUnitIso g).hom =
      (Scheme.Modules.pullbackUnitIso f).hom := by
  subst g
  simp [Scheme.Modules.pullbackCongr]

theorem localIdealGeneratorPullbackIso_hom_comp_pulledIdealModuleToUnit
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.affineOpens) (r : Γ(Y, U.1)) (hr : r ∈ f.ker.ideal U)
    (hspan : f.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, U.1)) :
    (localIdealGeneratorPullbackIso f U r hr hspan hnzd).hom ≫
        pulledIdealModuleToUnit f U.1.ι =
      unitEndomorphismOfTopSection (affineOpenTopSection U r) := by
  rw [← pullbackIdealModuleToUnit_eq]
  exact localIdealGeneratorPullbackIso_hom_comp_toUnit
    f U r hr hspan hnzd

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
theorem pullbackLocalIdealGeneratorIso_hom_comp_toUnit
    {A X Y : Scheme.{u}} (k : A ⟶ Y) [QuasiCompact k] (g : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ g ⁻¹ᵁ V.1)
    (r : Γ(Y, V.1)) (hr : r ∈ k.ker.ideal V)
    (hspan : k.ker.ideal V = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, V.1)) :
    (pullbackLocalIdealGeneratorIso k g U V hUV r hr hspan hnzd).hom ≫
        (Scheme.Modules.pullback U.1.ι).map (pulledIdealModuleToUnit k g) ≫
        (Scheme.Modules.pullbackUnitIso U.1.ι).hom =
      unitEndomorphismOfTopSection
        ((g.resLE V.1 U.1 hUV).appTop.hom (affineOpenTopSection V r)) := by
  let q := g.resLE V.1 U.1 hUV
  let α := Scheme.Modules.pullbackComp U.1.ι g
  let β := Scheme.Modules.pullbackComp q V.1.ι
  let γ := Scheme.Modules.pullbackCongr (g.resLE_comp_ι hUV)
  have hαunit : α.inv.app (Scheme.Modules.unitObj Y) ≫
      (Scheme.Modules.pullback U.1.ι).map
        (Scheme.Modules.pullbackUnitIso g).hom ≫
      (Scheme.Modules.pullbackUnitIso U.1.ι).hom =
      (Scheme.Modules.pullbackUnitIso (U.1.ι ≫ g)).hom := by
    rw [← pullbackUnitIso_comp U.1.ι g]
    exact Iso.inv_hom_id_assoc (α.app (Scheme.Modules.unitObj Y)) _
  have hγunit : γ.hom.app (Scheme.Modules.unitObj Y) ≫
      (Scheme.Modules.pullbackUnitIso (U.1.ι ≫ g)).hom =
      (Scheme.Modules.pullbackUnitIso (q ≫ V.1.ι)).hom := by
    exact pullbackUnitIso_congr (g.resLE_comp_ι hUV)
  have hβunit : β.hom.app (Scheme.Modules.unitObj Y) ≫
      (Scheme.Modules.pullbackUnitIso (q ≫ V.1.ι)).hom =
      (Scheme.Modules.pullback q).map
          (Scheme.Modules.pullbackUnitIso V.1.ι).hom ≫
        (Scheme.Modules.pullbackUnitIso q).hom := by
    exact pullbackUnitIso_comp q V.1.ι
  let eV := localIdealGeneratorPullbackIso k V r hr hspan hnzd
  have hlocalBase : eV.hom ≫
      (Scheme.Modules.pullback V.1.ι).map (idealModuleToUnit k) ≫
        (Scheme.Modules.pullbackUnitIso V.1.ι).hom =
      unitEndomorphismOfTopSection (affineOpenTopSection V r) := by
    change eV.hom ≫ pulledIdealModuleToUnit k V.1.ι = _
    exact localIdealGeneratorPullbackIso_hom_comp_pulledIdealModuleToUnit
      k V r hr hspan hnzd
  have hlocal : ((Scheme.Modules.pullback q).mapIso eV).hom ≫
      (Scheme.Modules.pullback V.1.ι ⋙ Scheme.Modules.pullback q).map
        (idealModuleToUnit k) ≫
      (Scheme.Modules.pullback q).map
        (Scheme.Modules.pullbackUnitIso V.1.ι).hom =
      (Scheme.Modules.pullback q).map
        (unitEndomorphismOfTopSection (affineOpenTopSection V r)) := by
    change (Scheme.Modules.pullback q).map eV.hom ≫
      (Scheme.Modules.pullback q).map
        ((Scheme.Modules.pullback V.1.ι).map (idealModuleToUnit k)) ≫
      (Scheme.Modules.pullback q).map
        (Scheme.Modules.pullbackUnitIso V.1.ι).hom = _
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun a => (Scheme.Modules.pullback q).map a) hlocalBase
  have hlocalFull : (Scheme.Modules.pullbackUnitIso q).inv ≫
      ((Scheme.Modules.pullback q).mapIso eV).hom ≫
      (Scheme.Modules.pullback V.1.ι ⋙ Scheme.Modules.pullback q).map
        (idealModuleToUnit k) ≫
      (Scheme.Modules.pullback q).map
        (Scheme.Modules.pullbackUnitIso V.1.ι).hom ≫
      (Scheme.Modules.pullbackUnitIso q).hom =
      (Scheme.Modules.pullbackUnitIso q).inv ≫
        (Scheme.Modules.pullback q).map
          (unitEndomorphismOfTopSection (affineOpenTopSection V r)) ≫
        (Scheme.Modules.pullbackUnitIso q).hom := by
    simpa only [Category.assoc] using congrArg
      (fun a => (Scheme.Modules.pullbackUnitIso q).inv ≫ a ≫
        (Scheme.Modules.pullbackUnitIso q).hom) hlocal
  dsimp only [pullbackLocalIdealGeneratorIso, pulledIdealModuleToUnit]
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
  rw [show (Scheme.Modules.pullback U.1.ι).map
      ((Scheme.Modules.pullback g).map (idealModuleToUnit k)) =
    (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback U.1.ι).map
      (idealModuleToUnit k) by rfl]
  erw [← (Scheme.Modules.pullbackComp U.1.ι g).inv.naturality_assoc
    (idealModuleToUnit k)]
  erw [← (Scheme.Modules.pullbackCongr
    (g.resLE_comp_ι hUV)).hom.naturality_assoc (idealModuleToUnit k)]
  erw [← (Scheme.Modules.pullbackComp q V.1.ι).hom.naturality_assoc
    (idealModuleToUnit k)]
  rw [hαunit, hγunit, hβunit]
  change (Scheme.Modules.pullbackUnitIso q).inv ≫
      ((Scheme.Modules.pullback q).mapIso eV).hom ≫
      (Scheme.Modules.pullback V.1.ι ⋙ Scheme.Modules.pullback q).map
        (idealModuleToUnit k) ≫
      (Scheme.Modules.pullback q).map
        (Scheme.Modules.pullbackUnitIso V.1.ι).hom ≫
      (Scheme.Modules.pullbackUnitIso q).hom = _
  rw [hlocalFull]
  exact pullback_unitEndomorphismOfTopSection q (affineOpenTopSection V r)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- On affine Cartier charts, the canonical section-ideal base-change map is an
isomorphism. -/
theorem idealModuleBaseChangeHom_isIso_on_affine
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S)
    [QuasiCompact z] [QuasiCompact (sectionBaseChange z hz t)]
    (U : (pullback π t).affineOpens) (V : C.affineOpens)
    (hUV : U.1 ≤ pullback.fst π t ⁻¹ᵁ V.1)
    (r : Γ(C, V.1)) (hr : r ∈ z.ker.ideal V)
    (hspan : z.ker.ideal V = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, V.1))
    (hspan' : (sectionBaseChange z hz t).ker.ideal U =
      Ideal.span {affinePullbackSection (pullback.fst π t) U V hUV r})
    (hnzd' : affinePullbackSection (pullback.fst π t) U V hUV r ∈
      nonZeroDivisors Γ(pullback π t, U.1)) :
    IsIso ((Scheme.Modules.pullback U.1.ι).map
      (idealModuleBaseChangeHom z hz t)) := by
  let g := pullback.fst π t
  let z' := sectionBaseChange z hz t
  let r' := affinePullbackSection g U V hUV r
  let eS := pullbackLocalIdealGeneratorIso z g U V hUV r hr hspan hnzd
  have hr' : r' ∈ z'.ker.ideal U := by
    rw [hspan']
    exact Ideal.mem_span_singleton_self r'
  let eT := localIdealGeneratorPullbackIso z' U r' hr' hspan' hnzd'
  have hbase : (Scheme.Modules.pullback U.1.ι).map
        (idealModuleBaseChangeHom z hz t) ≫
        pulledIdealModuleToUnit z' U.1.ι =
      (Scheme.Modules.pullback U.1.ι).map
          (pulledIdealModuleToUnit z g) ≫
        (Scheme.Modules.pullbackUnitIso U.1.ι).hom := by
    dsimp only [pulledIdealModuleToUnit]
    rw [← (Scheme.Modules.pullback U.1.ι).map_comp_assoc]
    rw [idealModuleBaseChangeHom_comp_toUnit]
    rfl
  have hm : eS.hom ≫
      (Scheme.Modules.pullback U.1.ι).map (idealModuleBaseChangeHom z hz t) =
      eT.hom := by
    letI : Mono (pulledIdealModuleToUnit z' U.1.ι) :=
      pulledIdealModuleToUnit_mono_of_isOpenImmersion z' U.1.ι
    apply (cancel_mono (pulledIdealModuleToUnit z' U.1.ι)).1
    calc
      (eS.hom ≫ (Scheme.Modules.pullback U.1.ι).map
          (idealModuleBaseChangeHom z hz t)) ≫
          pulledIdealModuleToUnit z' U.1.ι =
        eS.hom ≫ (Scheme.Modules.pullback U.1.ι).map
          (pulledIdealModuleToUnit z g) ≫
          (Scheme.Modules.pullbackUnitIso U.1.ι).hom := by
            rw [Category.assoc, hbase]
      _ = unitEndomorphismOfTopSection
          ((g.resLE V.1 U.1 hUV).appTop.hom
            (affineOpenTopSection V r)) :=
        pullbackLocalIdealGeneratorIso_hom_comp_toUnit
          z g U V hUV r hr hspan hnzd
      _ = unitEndomorphismOfTopSection (affineOpenTopSection U r') := by
        rw [affineOpenTopSection_affinePullbackSection]
      _ = eT.hom ≫ pulledIdealModuleToUnit z' U.1.ι :=
        (localIdealGeneratorPullbackIso_hom_comp_pulledIdealModuleToUnit
          z' U r' hr' hspan' hnzd').symm
  have hmap : (Scheme.Modules.pullback U.1.ι).map
      (idealModuleBaseChangeHom z hz t) = eS.inv ≫ eT.hom := by
    apply (cancel_epi eS.hom).1
    calc
      eS.hom ≫ (Scheme.Modules.pullback U.1.ι).map
          (idealModuleBaseChangeHom z hz t) = eT.hom := hm
      _ = eS.hom ≫ (eS.inv ≫ eT.hom) := by
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [hmap]
  infer_instance

/-- A module morphism which is an isomorphism after restriction to an open
neighborhood induces an isomorphism on the corresponding ambient stalk. -/
theorem isIso_stalkFunctor_map_of_isIso_pullback_opens
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (x : U)
    [IsIso ((Scheme.Modules.pullback U.ι).map f)] :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x.1).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom) := by
  let e := Scheme.Modules.restrictFunctorIsoPullback U.ι
  have hnat : (Scheme.Modules.restrictFunctor U.ι).map f ≫ e.hom.app N =
      e.hom.app M ≫ (Scheme.Modules.pullback U.ι).map f :=
    e.hom.naturality f
  haveI hrestrictComp : IsIso
      ((Scheme.Modules.restrictFunctor U.ι).map f ≫ e.hom.app N) := by
    rw [hnat]
    infer_instance
  haveI hrestrict : IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) :=
    (isIso_comp_right_iff _ _).mp hrestrictComp
  let eStalk := Scheme.Modules.restrictStalkNatIso U.ι x
  apply (NatIso.isIso_map_iff eStalk f).mp
  change IsIso ((TopCat.Presheaf.stalkFunctor.{u, u + 1}
      AddCommGrpCat.{u} _).map
    ((Scheme.Modules.toPresheaf.{u} _).map
      ((Scheme.Modules.restrictFunctor U.ι).map f)))
  infer_instance

/-- A section of a separated morphism is a closed immersion. -/
theorem isClosedImmersion_section {C S : Scheme.{u}} {π : C ⟶ S}
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) : IsClosedImmersion z := by
  have hcomp : IsClosedImmersion (z ≫ π) := by
    rw [hz]
    infer_instance
  exact IsClosedImmersion.of_comp z π

/-- The ideal sheaf of a section, as an actual sheaf of modules. -/
noncomputable def sectionIdealModule {C S : Scheme.{u}} (π : C ⟶ S)
    [IsSeparated π] (z : S ⟶ C) (_hz : z ≫ π = 𝟙 S) : C.Modules := by
  letI : IsClosedImmersion z := isClosedImmersion_section z _hz
  letI : QuasiCompact z := inferInstance
  exact idealModule z

set_option backward.isDefEq.respectTransparency false in
/-- The zero-section ideal commutes with restriction to an open subscheme of the base. -/
noncomputable def sectionIdealModuleRestrictIso
    {C S T : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) [IsOpenImmersion t] :
    (Scheme.Modules.restrictFunctor (pullback.fst π t)).obj
        (sectionIdealModule π z hz) ≅
      sectionIdealModule (pullback.snd π t) (sectionBaseChange z hz t)
        (sectionBaseChange_snd z hz t) := by
  letI : IsOpenImmersion (pullback.fst π t) :=
    MorphismProperty.pullback_fst π t inferInstance
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  letI : IsSeparated (pullback.snd π t) :=
    inferInstance
  letI : IsClosedImmersion (sectionBaseChange z hz t) :=
    isClosedImmersion_section (sectionBaseChange z hz t) (sectionBaseChange_snd z hz t)
  letI : QuasiCompact (sectionBaseChange z hz t) := inferInstance
  change (Scheme.Modules.restrictFunctor (pullback.fst π t)).obj (idealModule z) ≅
    idealModule (sectionBaseChange z hz t)
  exact restrictIdealModuleIso z (pullback.fst π t) (sectionBaseChange z hz t)
    (RelEffCartierDiv.ker_sectionBaseChange z hz t)

/-- The ideal sheaf of a section of a smooth separated relative curve is invertible. -/
theorem sectionIdealModule_isInvertible {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) :
    Scheme.Modules.IsInvertible (sectionIdealModule π z hz) := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  change Scheme.Modules.IsInvertible (idealModule z)
  exact idealModule_isInvertible_of_locallyPrincipal z
    (RelEffCartierDiv.sectionDivisor_isOfficial hsm z hz).locallyPrincipal

set_option backward.isDefEq.respectTransparency false in
/-- The ideal module of the zero section commutes with arbitrary base change. -/
theorem idealModuleBaseChangeHom_isIso
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    IsIso (idealModuleBaseChangeHom z hz t) := by
  let g := pullback.fst π t
  let z' := sectionBaseChange z hz t
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  letI : IsSeparated (pullback.snd π t) :=
    inferInstance
  letI : IsClosedImmersion z' :=
    isClosedImmersion_section z' (sectionBaseChange_snd z hz t)
  letI : QuasiCompact z' := inferInstance
  have hsm' : SmoothOfRelativeDimension 1 (pullback.snd π t) := by
    have : MorphismProperty.IsStableUnderBaseChange
        (@SmoothOfRelativeDimension 1) :=
      AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange 1
    exact MorphismProperty.pullback_snd π t hsm
  let F := SheafOfModules.toSheaf (pullback π t).ringCatSheaf
  letI hreflect : F.ReflectsIsomorphisms :=
    PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
  haveI hstalk : ∀ x : (pullback π t : Scheme.{u}),
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (F.map (idealModuleBaseChangeHom z hz t)).hom) := by
    intro x
    obtain ⟨V, hgV, r, hspan, hnzd⟩ :=
      (RelEffCartierDiv.sectionDivisor_isOfficial hsm z hz).locallyPrincipal (g x)
    change z.ker.ideal V = Ideal.span {r} at hspan
    obtain ⟨W, hxW, s, hspanS, hnzdS⟩ :=
      (RelEffCartierDiv.sectionDivisor_isOfficial hsm' z'
        (sectionBaseChange_snd z hz t)).locallyPrincipal x
    change z'.ker.ideal W = Ideal.span {s} at hspanS
    obtain ⟨a, hxU, hUV⟩ := exists_chartBasicOpenImage_le_of_mem W
      (g ⁻¹ᵁ V.1) x hxW hgV
    let U := chartBasicOpenImage W a
    let r' := affinePullbackSection g U V hUV r
    have hr : r ∈ z.ker.ideal V := by
      rw [hspan]
      exact Ideal.mem_span_singleton_self r
    have hspan' : z'.ker.ideal U = Ideal.span {r'} := by
      have hker : z'.ker = z.ker.comap g := by
        dsimp only [z', g]
        exact RelEffCartierDiv.ker_sectionBaseChange z hz t
      rw [hker]
      exact ideal_comap_affineOpens_span z.ker g U V hUV r hspan
    have hsdata := ideal_chartBasicOpenImage_span_nzd
      z'.ker W s hspanS hnzdS a
    have hnzd' : r' ∈ nonZeroDivisors Γ(pullback π t, U.1) := by
      apply mem_nonZeroDivisors_of_span_eq_span
        (hspan'.symm.trans hsdata.1)
      exact hsdata.2
    letI hlocal : IsIso ((Scheme.Modules.pullback U.1.ι).map
        (idealModuleBaseChangeHom z hz t)) :=
      idealModuleBaseChangeHom_isIso_on_affine z hz t U V hUV r hr
        hspan hnzd hspan' hnzd'
    let xU : U.1 := ⟨x, hxU⟩
    change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat xU.1).map
      ((SheafOfModules.toSheaf (pullback π t).ringCatSheaf).map
        (idealModuleBaseChangeHom z hz t)).hom)
    exact isIso_stalkFunctor_map_of_isIso_pullback_opens
      (idealModuleBaseChangeHom z hz t) U.1 xU
  haveI hmap : IsIso (F.map (idealModuleBaseChangeHom z hz t)) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
      (F.map (idealModuleBaseChangeHom z hz t))
  exact @Functor.ReflectsIsomorphisms.reflects _ _ _ _ F hreflect _ _
    (idealModuleBaseChangeHom z hz t) hmap

set_option backward.isDefEq.respectTransparency false in
/-- The canonical arbitrary-base-change isomorphism for the zero-section ideal. -/
noncomputable def sectionIdealModuleBaseChangeIso
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    (Scheme.Modules.pullback (pullback.fst π t)).obj
        (sectionIdealModule π z hz) ≅
      sectionIdealModule (pullback.snd π t) (sectionBaseChange z hz t)
        (sectionBaseChange_snd z hz t) := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  letI : IsSeparated (pullback.snd π t) :=
    inferInstance
  letI : IsClosedImmersion (sectionBaseChange z hz t) :=
    isClosedImmersion_section (sectionBaseChange z hz t)
      (sectionBaseChange_snd z hz t)
  letI : QuasiCompact (sectionBaseChange z hz t) := inferInstance
  letI : IsIso (idealModuleBaseChangeHom z hz t) :=
    idealModuleBaseChangeHom_isIso hsm z hz t
  change (Scheme.Modules.pullback (pullback.fst π t)).obj (idealModule z) ≅
    idealModule (sectionBaseChange z hz t)
  exact asIso (idealModuleBaseChangeHom z hz t)

/-- The sheaf `𝒪_C([0])`: the dual of the ideal sheaf of the zero section. -/
noncomputable def sectionPoleSheaf {C S : Scheme.{u}} (π : C ⟶ S)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) : C.Modules :=
  Scheme.Modules.dualObj (sectionIdealModule π z hz)

/-- The pole sheaf of a section commutes with restriction along an open
immersion of the base. -/
noncomputable def sectionPoleSheafRestrictIso
    {C S T : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) [IsOpenImmersion t] :
    (Scheme.Modules.restrictFunctor (pullback.fst π t)).obj
        (sectionPoleSheaf π z hz) ≅
      sectionPoleSheaf (pullback.snd π t) (sectionBaseChange z hz t)
        (sectionBaseChange_snd z hz t) := by
  letI : IsOpenImmersion (pullback.fst π t) :=
    MorphismProperty.pullback_fst π t inferInstance
  letI : IsSeparated (pullback.snd π t) :=
    inferInstance
  exact Scheme.Modules.dualRestrictIso
      (sectionIdealModule π z hz) (pullback.fst π t) ≪≫
    (Scheme.Modules.dualIsoObj
      (sectionIdealModuleRestrictIso z hz t)).symm

/-- The simple-pole sheaf of a smooth separated relative curve commutes with
arbitrary base change. -/
noncomputable def sectionPoleSheafBaseChangeIso
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    (Scheme.Modules.pullback (pullback.fst π t)).obj
        (sectionPoleSheaf π z hz) ≅
      sectionPoleSheaf (pullback.snd π t) (sectionBaseChange z hz t)
        (sectionBaseChange_snd z hz t) := by
  letI : IsSeparated (pullback.snd π t) :=
    inferInstance
  exact Scheme.Modules.dualPullbackIsoOfIsInvertible
      (pullback.fst π t) (sectionIdealModule π z hz)
      (sectionIdealModule_isInvertible hsm z hz) ≪≫
    (Scheme.Modules.dualIsoObj
      (sectionIdealModuleBaseChangeIso hsm z hz t)).symm

/-- The inclusion of the zero-section ideal into the structure sheaf. -/
noncomputable def sectionIdealToUnit {C S : Scheme.{u}} (π : C ⟶ S)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) :
    sectionIdealModule π z hz ⟶ Scheme.Modules.unitObj C := by
  change idealModule z ⟶ Scheme.Modules.unitObj C
  exact idealModuleToUnit z

/-- The canonical inclusion `𝒪_C → 𝒪_C([0])`, obtained by dualizing the
zero-section ideal inclusion. -/
noncomputable def sectionPoleUnitHom {C S : Scheme.{u}} (π : C ⟶ S)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) :
    Scheme.Modules.unitObj C ⟶ sectionPoleSheaf π z hz :=
  (Scheme.Modules.dualUnitObjIso (X := C)).inv ≫
    Scheme.Modules.dualMapObj (sectionIdealToUnit π z hz)

/-- The pole sheaf `𝒪_C(n[0])`, formed as the `n`-fold sheafified tensor power of
`𝒪_C([0])`. -/
noncomputable def sectionPoleSheafPower {C S : Scheme.{u}} (π : C ⟶ S)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) : ℕ → C.Modules
  | 0 => 𝟙_ C.Modules
  | n + 1 => sectionPoleSheafPower π z hz n ⊗ sectionPoleSheaf π z hz

/-- Every nonnegative tensor power of the pole sheaf commutes with arbitrary
base change. -/
noncomputable def sectionPoleSheafPowerBaseChangeIso
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    ∀ n : ℕ,
      (Scheme.Modules.pullback (pullback.fst π t)).obj
          (sectionPoleSheafPower π z hz n) ≅
        sectionPoleSheafPower (pullback.snd π t)
          (sectionBaseChange z hz t) (sectionBaseChange_snd z hz t) n
  | 0 => by
      letI : IsSeparated (pullback.snd π t) :=
        inferInstance
      letI : (Scheme.Modules.pullback (pullback.fst π t)).Monoidal :=
        Scheme.Modules.pullbackMonoidal (pullback.fst π t)
      exact (Functor.Monoidal.εIso
        (Scheme.Modules.pullback (pullback.fst π t))).symm
  | n + 1 => by
      letI : IsSeparated (pullback.snd π t) :=
        inferInstance
      letI : (Scheme.Modules.pullback (pullback.fst π t)).Monoidal :=
        Scheme.Modules.pullbackMonoidal (pullback.fst π t)
      exact (Functor.Monoidal.μIso
          (Scheme.Modules.pullback (pullback.fst π t))
          (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz)).symm ≪≫
        (sectionPoleSheafPowerBaseChangeIso hsm z hz t n ⊗ᵢ
          sectionPoleSheafBaseChangeIso hsm z hz t)

/-- Every tensor power of the pole sheaf commutes with restriction along an
open immersion of the base. -/
noncomputable def sectionPoleSheafPowerRestrictIso
    {C S T : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) [IsOpenImmersion t] :
    ∀ n : ℕ,
      (Scheme.Modules.restrictFunctor (pullback.fst π t)).obj
          (sectionPoleSheafPower π z hz n) ≅
        sectionPoleSheafPower (pullback.snd π t)
          (sectionBaseChange z hz t) (sectionBaseChange_snd z hz t) n
  | 0 => by
      letI : IsOpenImmersion (pullback.fst π t) :=
        MorphismProperty.pullback_fst π t inferInstance
      letI : (Scheme.Modules.pullback (pullback.fst π t)).Monoidal :=
        Scheme.Modules.pullbackMonoidal (pullback.fst π t)
      letI : (Scheme.Modules.restrictFunctor (pullback.fst π t)).Monoidal :=
        Functor.Monoidal.transport
          (Scheme.Modules.restrictFunctorIsoPullback (pullback.fst π t)).symm
      exact (Functor.Monoidal.εIso
        (Scheme.Modules.restrictFunctor (pullback.fst π t))).symm
  | n + 1 => by
      letI : IsOpenImmersion (pullback.fst π t) :=
        MorphismProperty.pullback_fst π t inferInstance
      letI : IsSeparated (pullback.snd π t) :=
        inferInstance
      letI : (Scheme.Modules.pullback (pullback.fst π t)).Monoidal :=
        Scheme.Modules.pullbackMonoidal (pullback.fst π t)
      letI : (Scheme.Modules.restrictFunctor (pullback.fst π t)).Monoidal :=
        Functor.Monoidal.transport
          (Scheme.Modules.restrictFunctorIsoPullback (pullback.fst π t)).symm
      exact (Functor.Monoidal.μIso
          (Scheme.Modules.restrictFunctor (pullback.fst π t))
          (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz)).symm ≪≫
        (sectionPoleSheafPowerRestrictIso z hz t n ⊗ᵢ
          sectionPoleSheafRestrictIso z hz t)

/-- The localized monoidal unit is the structure sheaf. -/
noncomputable def monoidalUnitObjIso (X : Scheme.{u}) :
    𝟙_ X.Modules ≅ Scheme.Modules.unitObj X :=
  Scheme.Modules.sheafifyValIso (Scheme.Modules.unitObj X)

/-- The explicit structure module is the monoidal unit, so its tensor square is
canonically the structure module again. -/
private noncomputable def unitObjTensorIso (X : Scheme.{u}) :
    Scheme.Modules.unitObj X ⊗ Scheme.Modules.unitObj X ≅
      Scheme.Modules.unitObj X :=
  ((monoidalUnitObjIso X).symm ⊗ᵢ (monoidalUnitObjIso X).symm) ≪≫
    λ_ (𝟙_ X.Modules) ≪≫ monoidalUnitObjIso X

/-- The canonical multiplication on the explicit structure module is associative. -/
private theorem unitObjTensorIso_hom_assoc (X : Scheme.{u}) :
    (α_ (Scheme.Modules.unitObj X) (Scheme.Modules.unitObj X)
          (Scheme.Modules.unitObj X)).inv ≫
        ((unitObjTensorIso X).hom ⊗ₘ 𝟙 (Scheme.Modules.unitObj X)) ≫
          (unitObjTensorIso X).hom =
      (𝟙 (Scheme.Modules.unitObj X) ⊗ₘ (unitObjTensorIso X).hom) ≫
        (unitObjTensorIso X).hom := by
  letI : MonObj (Scheme.Modules.unitObj X) :=
    MonObj.ofIso (monoidalUnitObjIso X)
  change (α_ (Scheme.Modules.unitObj X) (Scheme.Modules.unitObj X)
        (Scheme.Modules.unitObj X)).inv ≫
      (MonObj.mul ⊗ₘ 𝟙 (Scheme.Modules.unitObj X)) ≫ MonObj.mul =
    (𝟙 (Scheme.Modules.unitObj X) ⊗ₘ MonObj.mul) ≫ MonObj.mul
  simpa only [tensorHom_id, id_tensorHom] using
    (MonObj.mul_assoc_flip (Scheme.Modules.unitObj X)).symm

/-- Associativity of a multiplication propagates through three morphisms into
its underlying object. -/
private theorem tensorMulHom_assoc
    {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {A B C X : D} (a : A ⟶ X) (b : B ⟶ X) (c : C ⟶ X)
    (mul : X ⊗ X ⟶ X)
    (hassoc :
      (α_ X X X).inv ≫ (mul ⊗ₘ 𝟙 X) ≫ mul =
        (𝟙 X ⊗ₘ mul) ≫ mul) :
    (α_ A B C).inv ≫ (((a ⊗ₘ b) ≫ mul) ⊗ₘ c) ≫ mul =
      (a ⊗ₘ ((b ⊗ₘ c) ≫ mul)) ≫ mul := by
  calc
    _ = (α_ A B C).inv ≫
        (((a ⊗ₘ b) ⊗ₘ c) ≫ (mul ⊗ₘ 𝟙 X)) ≫ mul := by
      simp only [tensorHom_comp_tensorHom, Category.comp_id]
    _ = ((a ⊗ₘ (b ⊗ₘ c)) ≫ (α_ X X X).inv) ≫
        (mul ⊗ₘ 𝟙 X) ≫ mul := by
      rw [associator_inv_naturality]
      simp only [Category.assoc]
    _ = (a ⊗ₘ (b ⊗ₘ c)) ≫ (𝟙 X ⊗ₘ mul) ≫ mul := by
      simp only [Category.assoc, hassoc]
    _ = _ := by
      rw [← Category.assoc]
      rw [tensorHom_comp_tensorHom]
      rw [Category.comp_id]

/-- Conjugating the tensor of two endomorphisms through an identification with the
monoidal unit gives their composite. -/
private theorem tensorUnitIso_hom_naturality
    {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {X : D} (e : 𝟙_ D ≅ X) (f g : X ⟶ X) :
    (f ⊗ₘ g) ≫ (e.inv ⊗ₘ e.inv) ≫ (λ_ (𝟙_ D)).hom ≫ e.hom =
      (e.inv ⊗ₘ e.inv) ≫ (λ_ (𝟙_ D)).hom ≫ e.hom ≫ f ≫ g := by
  let a : 𝟙_ D ⟶ 𝟙_ D := e.hom ≫ f ≫ e.inv
  let b : 𝟙_ D ⟶ 𝟙_ D := e.hom ≫ g ≫ e.inv
  have hf : f ≫ e.inv = e.inv ≫ a := by
    simp [a]
  have hg : g ≫ e.inv = e.inv ≫ b := by
    simp [b]
  have hab : (a ⊗ₘ b) ≫ (λ_ (𝟙_ D)).hom =
      (λ_ (𝟙_ D)).hom ≫ a ≫ b := by
    rw [tensorHom_def, Category.assoc, leftUnitor_naturality]
    rw [unitors_equal, ← Category.assoc, rightUnitor_naturality]
    rw [Category.assoc]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  rw [hf, hg, ← tensorHom_comp_tensorHom]
  rw [Category.assoc]
  rw [← Category.assoc (a ⊗ₘ b) (λ_ (𝟙_ D)).hom e.hom, hab]
  simp [a, b, Category.assoc]

/-- The tensor-square identification induced by `e : 𝟙 ≅ X` is compatible
with a morphism into `X`. -/
private theorem tensorUnitIso_hom_naturality_left
    {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {X Y : D} (e : 𝟙_ D ≅ X) (f : Y ⟶ X) :
    (f ⊗ₘ e.hom) ≫ (e.inv ⊗ₘ e.inv) ≫
        (λ_ (𝟙_ D)).hom ≫ e.hom =
      (ρ_ Y).hom ≫ f := by
  rw [← Category.assoc (f ⊗ₘ e.hom) (e.inv ⊗ₘ e.inv)]
  rw [tensorHom_comp_tensorHom]
  rw [e.hom_inv_id]
  rw [unitors_equal]
  have h := rightUnitor_naturality (f ≫ e.inv)
  calc
    _ = ((f ≫ e.inv ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ (𝟙_ D)).hom) ≫ e.hom :=
      (Category.assoc _ _ _).symm
    _ = (((f ≫ e.inv) ▷ 𝟙_ D) ≫ (ρ_ (𝟙_ D)).hom) ≫ e.hom := by
      rw [tensorHom_id]
    _ = ((ρ_ Y).hom ≫ (f ≫ e.inv)) ≫ e.hom :=
      congrArg (fun k ↦ k ≫ e.hom) h
    _ = _ := by simp

/-- Under `𝒪_X ⊗ 𝒪_X ≅ 𝒪_X`, tensoring multiplication by `r` and by `s`
is multiplication by `r * s`. -/
private theorem unitObjTensorIso_hom_comp_scalars (X : Scheme.{u})
    (r s : Γ(X, (⊤ : X.Opens))) :
    (unitEndomorphismOfTopSection r ⊗ₘ
        unitEndomorphismOfTopSection s) ≫ (unitObjTensorIso X).hom =
      (unitObjTensorIso X).hom ≫ unitEndomorphismOfTopSection (r * s) := by
  change (unitEndomorphismOfTopSection r ⊗ₘ
      unitEndomorphismOfTopSection s) ≫
      ((monoidalUnitObjIso X).inv ⊗ₘ (monoidalUnitObjIso X).inv) ≫
        (λ_ (𝟙_ X.Modules)).hom ≫ (monoidalUnitObjIso X).hom =
    ((monoidalUnitObjIso X).inv ⊗ₘ (monoidalUnitObjIso X).inv) ≫
      (λ_ (𝟙_ X.Modules)).hom ≫ (monoidalUnitObjIso X).hom ≫
        unitEndomorphismOfTopSection (r * s)
  calc
    _ = ((monoidalUnitObjIso X).inv ⊗ₘ (monoidalUnitObjIso X).inv) ≫
        (λ_ (𝟙_ X.Modules)).hom ≫ (monoidalUnitObjIso X).hom ≫
          unitEndomorphismOfTopSection r ≫ unitEndomorphismOfTopSection s :=
      tensorUnitIso_hom_naturality (monoidalUnitObjIso X) _ _
    _ = _ := by rw [unitEndomorphismOfTopSection_comp]

/-- The localized coherent tensor agrees with the explicit sheafified tensor used by
the cover-local invertibility API. -/
noncomputable def monoidalTensorObjIso {X : Scheme.{u}} (M N : X.Modules) :
    M ⊗ N ≅ Scheme.Modules.tensorObj M N :=
  ((Scheme.Modules.sheafifyValIso M).symm ⊗ᵢ
      (Scheme.Modules.sheafifyValIso N).symm) ≪≫
    Localization.Monoidal.μ
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _) M.val N.val

/-- Restriction along an open immersion preserves the localized monoidal unit. -/
private noncomputable def restrictMonoidalUnitIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules := by
  letI : (Scheme.Modules.pullback f).Monoidal :=
    Scheme.Modules.pullbackMonoidal f
  exact (Scheme.Modules.restrictFunctorIsoPullback f).app (𝟙_ Y.Modules) ≪≫
    (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).symm

/-- Restriction along an open immersion preserves the localized tensor product. -/
private noncomputable def restrictMonoidalTensorIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.Modules) :
    (Scheme.Modules.restrictFunctor f).obj (M ⊗ N) ≅
      (Scheme.Modules.restrictFunctor f).obj M ⊗
        (Scheme.Modules.restrictFunctor f).obj N := by
  letI : (Scheme.Modules.pullback f).Monoidal :=
    Scheme.Modules.pullbackMonoidal f
  exact (Scheme.Modules.restrictFunctorIsoPullback f).app (M ⊗ N) ≪≫
    (Functor.Monoidal.μIso (Scheme.Modules.pullback f) M N).symm ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback f).symm.app M ⊗ᵢ
      (Scheme.Modules.restrictFunctorIsoPullback f).symm.app N)

/-- A trivialization of the simple-pole sheaf on an open induces compatible
trivializations of all of its tensor powers on that open. -/
noncomputable def sectionPoleSheafPowerTrivialization
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.Opens)
    (e : (sectionPoleSheaf π z hz).restrict U.ι ≅
      Scheme.Modules.unitObj U.toScheme) :
    ∀ n : ℕ,
      (sectionPoleSheafPower π z hz n).restrict U.ι ≅
        Scheme.Modules.unitObj U.toScheme
  | 0 => restrictMonoidalUnitIso U.ι ≪≫ monoidalUnitObjIso U.toScheme
  | n + 1 =>
      restrictMonoidalTensorIso U.ι
          (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz) ≪≫
        (sectionPoleSheafPowerTrivialization z hz U e n ⊗ᵢ e) ≪≫
        unitObjTensorIso U.toScheme

/-- Transporting the index of a pole-sheaf power is compatible with its local
trivialization. -/
private theorem sectionPoleSheafPowerTrivialization_eqToHom
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.Opens)
    (e : (sectionPoleSheaf π z hz).restrict U.ι ≅
      Scheme.Modules.unitObj U.toScheme) {a b : ℕ} (h : a = b) :
    (Scheme.Modules.restrictFunctor U.ι).map
          (eqToHom (congrArg (sectionPoleSheafPower π z hz) h)) ≫
        (sectionPoleSheafPowerTrivialization z hz U e b).hom =
      (sectionPoleSheafPowerTrivialization z hz U e a).hom := by
  cases h
  simp

/-- The morphism underlying the successor power trivialization. -/
private theorem sectionPoleSheafPowerTrivialization_succ_hom
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.Opens)
    (e : (sectionPoleSheaf π z hz).restrict U.ι ≅
      Scheme.Modules.unitObj U.toScheme) (n : ℕ) :
    (sectionPoleSheafPowerTrivialization z hz U e (n + 1)).hom =
      (restrictMonoidalTensorIso U.ι
          (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz)).hom ≫
        ((sectionPoleSheafPowerTrivialization z hz U e n).hom ⊗ₘ e.hom) ≫
          (unitObjTensorIso U.toScheme).hom :=
  rfl

/-- A scalar transition between simple-pole trivializations raises to its `n`th
power on the induced trivializations of `𝒪(n[0])`. -/
theorem sectionPoleSheafPowerTrivialization_hom_eq_comp_scalar
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.Opens)
    (e g : (sectionPoleSheaf π z hz).restrict U.ι ≅
      Scheme.Modules.unitObj U.toScheme)
    (r : Γ(U.toScheme, (⊤ : U.toScheme.Opens)))
    (h : e.hom = g.hom ≫ unitEndomorphismOfTopSection r) :
    ∀ n : ℕ,
      (sectionPoleSheafPowerTrivialization z hz U e n).hom =
        (sectionPoleSheafPowerTrivialization z hz U g n).hom ≫
          unitEndomorphismOfTopSection (r ^ n)
  | 0 => by
      rw [pow_zero, unitEndomorphismOfTopSection_one, Category.comp_id]
      rfl
  | n + 1 => by
      have hn := sectionPoleSheafPowerTrivialization_hom_eq_comp_scalar
        z hz U e g r h n
      have htensor₀ :
          (sectionPoleSheafPowerTrivialization z hz U e n).hom ⊗ₘ e.hom =
            ((sectionPoleSheafPowerTrivialization z hz U g n).hom ≫
                unitEndomorphismOfTopSection (r ^ n)) ⊗ₘ
              (g.hom ≫ unitEndomorphismOfTopSection r) :=
        congrArg₂ (fun a b ↦ a ⊗ₘ b) hn h
      have htensor :
          (sectionPoleSheafPowerTrivialization z hz U e n).hom ⊗ₘ e.hom =
            ((sectionPoleSheafPowerTrivialization z hz U g n).hom ⊗ₘ g.hom) ≫
              (unitEndomorphismOfTopSection (r ^ n) ⊗ₘ
                unitEndomorphismOfTopSection r) :=
        htensor₀.trans
          (MonoidalCategory.tensorHom_comp_tensorHom
            (sectionPoleSheafPowerTrivialization z hz U g n).hom g.hom
            (unitEndomorphismOfTopSection (r ^ n))
            (unitEndomorphismOfTopSection r)).symm
      have heSucc :
          sectionPoleSheafPowerTrivialization z hz U e (n + 1) =
            restrictMonoidalTensorIso U.ι
                (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz) ≪≫
              (sectionPoleSheafPowerTrivialization z hz U e n ⊗ᵢ e) ≪≫
              unitObjTensorIso U.toScheme := rfl
      have hgSucc :
          sectionPoleSheafPowerTrivialization z hz U g (n + 1) =
            restrictMonoidalTensorIso U.ι
                (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz) ≪≫
              (sectionPoleSheafPowerTrivialization z hz U g n ⊗ᵢ g) ≪≫
              unitObjTensorIso U.toScheme := rfl
      have hcomp :
          (restrictMonoidalTensorIso U.ι
                (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz) ≪≫
              (sectionPoleSheafPowerTrivialization z hz U e n ⊗ᵢ e) ≪≫
              unitObjTensorIso U.toScheme).hom =
            (restrictMonoidalTensorIso U.ι
                  (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz) ≪≫
                (sectionPoleSheafPowerTrivialization z hz U g n ⊗ᵢ g) ≪≫
                unitObjTensorIso U.toScheme).hom ≫
              unitEndomorphismOfTopSection (r ^ (n + 1)) := by
        simp only [Iso.trans_hom, MonoidalCategory.tensorIso_hom]
        rw [htensor]
        simp only [Category.assoc]
        rw [unitObjTensorIso_hom_comp_scalars]
        rw [pow_succ]
      rw [← heSucc, ← hgSucc] at hcomp
      exact hcomp

section PolePowerRestriction

noncomputable local instance {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Monoidal :=
  Scheme.Modules.pullbackMonoidal f

/-- The tensor-power trivialization formed directly in the pullback functor. -/
private noncomputable def sectionPoleSheafPowerPullbackTrivialization
    {C S T : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (f : T ⟶ C)
    (e : (Scheme.Modules.pullback f).obj (sectionPoleSheaf π z hz) ≅
      Scheme.Modules.unitObj T) :
    ∀ n : ℕ,
      (Scheme.Modules.pullback f).obj (sectionPoleSheafPower π z hz n) ≅
        Scheme.Modules.unitObj T
  | 0 =>
      (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).symm ≪≫
        monoidalUnitObjIso T
  | n + 1 =>
      (Functor.Monoidal.μIso (Scheme.Modules.pullback f)
        (sectionPoleSheafPower π z hz n)
        (sectionPoleSheaf π z hz)).symm ≪≫
      (sectionPoleSheafPowerPullbackTrivialization z hz f e n ⊗ᵢ e) ≪≫
      unitObjTensorIso T

/-- The restriction-functor pole-power trivialization agrees with its direct
pullback-functor presentation. -/
private theorem sectionPoleSheafPowerTrivialization_eq_pullback
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.Opens)
    (e : (sectionPoleSheaf π z hz).restrict U.ι ≅
      Scheme.Modules.unitObj U.toScheme) :
    ∀ n : ℕ,
      sectionPoleSheafPowerTrivialization z hz U e n =
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).app
            (sectionPoleSheafPower π z hz n) ≪≫
          sectionPoleSheafPowerPullbackTrivialization z hz U.ι
            ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app
                (sectionPoleSheaf π z hz) ≪≫ e) n
  | 0 => by
      rfl
  | n + 1 => by
      apply Iso.ext
      simp only [sectionPoleSheafPowerTrivialization,
        sectionPoleSheafPowerPullbackTrivialization, Iso.trans_hom,
        MonoidalCategory.tensorIso_hom]
      rw [sectionPoleSheafPowerTrivialization_eq_pullback z hz U e n]
      change
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app
              (sectionPoleSheafPower π z hz n ⊗ sectionPoleSheaf π z hz) ≫
            Functor.OplaxMonoidal.δ (Scheme.Modules.pullback U.ι)
              (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz) ≫
            ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app
                (sectionPoleSheafPower π z hz n) ⊗ₘ
              (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app
                (sectionPoleSheaf π z hz))) ≫
          (((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app
                  (sectionPoleSheafPower π z hz n) ≫
                (sectionPoleSheafPowerPullbackTrivialization z hz U.ι
                  ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app
                    (sectionPoleSheaf π z hz) ≪≫ e) n).hom) ⊗ₘ e.hom) ≫
          (unitObjTensorIso U.toScheme).hom =
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app
              (sectionPoleSheafPower π z hz n ⊗ sectionPoleSheaf π z hz) ≫
            Functor.OplaxMonoidal.δ (Scheme.Modules.pullback U.ι)
              (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz) ≫
            (((sectionPoleSheafPowerPullbackTrivialization z hz U.ι
                  ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app
                    (sectionPoleSheaf π z hz) ≪≫ e) n).hom) ⊗ₘ
              ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app
                (sectionPoleSheaf π z hz) ≫ e.hom)) ≫
          (unitObjTensorIso U.toScheme).hom
      simp only [Category.assoc]
      slice_lhs 3 4 => rw [MonoidalCategory.tensorHom_comp_tensorHom]
      simp

/-- The direct pullback tensor-power trivialization with values in the monoidal
unit. -/
private noncomputable def sectionPoleSheafPowerPullbackMonoidalTrivialization
    {C S T : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (f : T ⟶ C)
    (e : (Scheme.Modules.pullback f).obj (sectionPoleSheaf π z hz) ≅
      𝟙_ T.Modules) :
    ∀ n : ℕ,
      (Scheme.Modules.pullback f).obj (sectionPoleSheafPower π z hz n) ≅
        𝟙_ T.Modules
  | 0 => (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).symm
  | n + 1 =>
      (Functor.Monoidal.μIso (Scheme.Modules.pullback f)
        (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz)).symm ≪≫
      (sectionPoleSheafPowerPullbackMonoidalTrivialization z hz f e n ⊗ᵢ e) ≪≫
      λ_ (𝟙_ T.Modules)

/-- The induced simple-pole trivialization for a composite monoidal pullback. -/
private noncomputable def sectionPoleSheafPowerCompMonoidalTrivialization
    {C S T U : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (f : T ⟶ C) (g : U ⟶ T) (h : U ⟶ C)
    (α : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback h)
    (e : (Scheme.Modules.pullback f).obj (sectionPoleSheaf π z hz) ≅
      𝟙_ T.Modules) :
    (Scheme.Modules.pullback h).obj (sectionPoleSheaf π z hz) ≅
      𝟙_ U.Modules :=
  (α.app (sectionPoleSheaf π z hz)).symm ≪≫
    (Scheme.Modules.pullback g).mapIso e ≪≫
      (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).symm

/-- Monoidal pullback composition commutes with the recursively induced
tensor-power trivializations. -/
private theorem sectionPoleSheafPowerPullbackMonoidalTrivialization_comp
    {C S T U : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (f : T ⟶ C) (g : U ⟶ T) (h : U ⟶ C)
    (α : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback h) [α.hom.IsMonoidal]
    (e : (Scheme.Modules.pullback f).obj (sectionPoleSheaf π z hz) ≅
      𝟙_ T.Modules) :
    ∀ n : ℕ,
      sectionPoleSheafPowerPullbackMonoidalTrivialization z hz h
          (sectionPoleSheafPowerCompMonoidalTrivialization
            z hz f g h α e) n =
        (α.app (sectionPoleSheafPower π z hz n)).symm ≪≫
          (Scheme.Modules.pullback g).mapIso
            (sectionPoleSheafPowerPullbackMonoidalTrivialization
              z hz f e n) ≪≫
          (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).symm
  | 0 => by
      apply Iso.ext
      simp only [sectionPoleSheafPowerPullbackMonoidalTrivialization,
        sectionPoleSheafPower, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom]
      have hunit := NatTrans.IsMonoidal.unit (τ := α.hom)
      rw [Functor.LaxMonoidal.comp_ε] at hunit
      simp only [Category.assoc] at hunit
      change (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).hom ≫
          (Scheme.Modules.pullback g).map
              (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).hom ≫
            α.hom.app (𝟙_ C.Modules) =
        (Functor.Monoidal.εIso (Scheme.Modules.pullback h)).hom at hunit
      apply (cancel_epi
        (Functor.Monoidal.εIso (Scheme.Modules.pullback h)).hom).1
      rw [Iso.hom_inv_id]
      rw [← hunit]
      simp only [Category.assoc]
      slice_rhs 3 4 => erw [(α.app (𝟙_ C.Modules)).hom_inv_id]
      erw [Category.id_comp]
      slice_rhs 2 3 => erw [Functor.Monoidal.map_ε_η]
      simp
  | n + 1 => by
      apply Iso.ext
      simp only [sectionPoleSheafPowerPullbackMonoidalTrivialization,
        sectionPoleSheafPower, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom, MonoidalCategory.tensorIso_hom]
      rw [sectionPoleSheafPowerPullbackMonoidalTrivialization_comp
        z hz f g h α e n]
      have htensor := NatTrans.IsMonoidal.tensor (τ := α.hom)
        (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz)
      change (Functor.Monoidal.μIso
          (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g)
          (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz)).hom ≫
            (α.app (sectionPoleSheafPower π z hz n ⊗
              sectionPoleSheaf π z hz)).hom =
        ((α.app (sectionPoleSheafPower π z hz n)).hom ⊗ₘ
            (α.app (sectionPoleSheaf π z hz)).hom) ≫
          (Functor.Monoidal.μIso (Scheme.Modules.pullback h)
            (sectionPoleSheafPower π z hz n)
              (sectionPoleSheaf π z hz)).hom at htensor
      have hhom_delta :
          (α.app (sectionPoleSheafPower π z hz n ⊗
              sectionPoleSheaf π z hz)).hom ≫
              Functor.OplaxMonoidal.δ (Scheme.Modules.pullback h)
                (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz) =
            Functor.OplaxMonoidal.δ
                (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g)
                (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz) ≫
              ((α.app (sectionPoleSheafPower π z hz n)).hom ⊗ₘ
                (α.app (sectionPoleSheaf π z hz)).hom) := by
        apply (cancel_epi (Functor.Monoidal.μIso
          (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g)
          (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz)).hom).1
        slice_lhs 1 2 => rw [htensor]
        slice_lhs 2 3 => erw [Functor.Monoidal.μ_δ]
        slice_rhs 1 2 => erw [Functor.Monoidal.μ_δ]
        simp
      have hinv_delta :
          (α.app (sectionPoleSheafPower π z hz n ⊗
              sectionPoleSheaf π z hz)).inv ≫
              Functor.OplaxMonoidal.δ
                (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g)
                (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz) =
            Functor.OplaxMonoidal.δ (Scheme.Modules.pullback h)
                (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz) ≫
              ((α.app (sectionPoleSheafPower π z hz n)).inv ⊗ₘ
                (α.app (sectionPoleSheaf π z hz)).inv) := by
        apply (cancel_epi (α.app (sectionPoleSheafPower π z hz n ⊗
          sectionPoleSheaf π z hz)).hom).1
        slice_lhs 1 2 => erw [(α.app (sectionPoleSheafPower π z hz n ⊗
          sectionPoleSheaf π z hz)).hom_inv_id]
        rw [Category.id_comp]
        slice_rhs 1 2 => rw [hhom_delta]
        slice_rhs 2 3 => erw [MonoidalCategory.tensorHom_comp_tensorHom]
        simp
      let p :=
        (sectionPoleSheafPowerPullbackMonoidalTrivialization z hz f e n).hom
      let q := e.hom
      let etaG := Functor.OplaxMonoidal.η (Scheme.Modules.pullback g)
      have hunit_tensor :
          Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g)
              (𝟙_ T.Modules) (𝟙_ T.Modules) ≫
              (etaG ⊗ₘ etaG) ≫ (λ_ (𝟙_ U.Modules)).hom =
            (Scheme.Modules.pullback g).map (λ_ (𝟙_ T.Modules)).hom ≫
              etaG := by
        dsimp only [etaG]
        rw [tensorHom_def]
        simp only [Category.assoc]
        rw [MonoidalCategory.leftUnitor_naturality]
        rw [Functor.OplaxMonoidal.left_unitality_hom_assoc]
      have hchain :
          (((α.app (sectionPoleSheafPower π z hz n)).inv ≫
                (Scheme.Modules.pullback g).map p ≫ etaG) ⊗ₘ
              ((α.app (sectionPoleSheaf π z hz)).inv ≫
                (Scheme.Modules.pullback g).map q ≫ etaG)) =
            ((α.app (sectionPoleSheafPower π z hz n)).inv ⊗ₘ
              (α.app (sectionPoleSheaf π z hz)).inv) ≫
              ((Scheme.Modules.pullback g).map p ⊗ₘ
                (Scheme.Modules.pullback g).map q) ≫ (etaG ⊗ₘ etaG) := by
        rw [MonoidalCategory.tensorHom_comp_tensorHom]
        rw [MonoidalCategory.tensorHom_comp_tensorHom]
      change
        Functor.OplaxMonoidal.δ (Scheme.Modules.pullback h)
              (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz) ≫
              (((α.app (sectionPoleSheafPower π z hz n)).inv ≫
                  (Scheme.Modules.pullback g).map p ≫ etaG) ⊗ₘ
                ((α.app (sectionPoleSheaf π z hz)).inv ≫
                  (Scheme.Modules.pullback g).map q ≫ etaG)) ≫
              (λ_ (𝟙_ U.Modules)).hom =
          (α.app (sectionPoleSheafPower π z hz n ⊗
              sectionPoleSheaf π z hz)).inv ≫
            (Scheme.Modules.pullback g).map
              (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f)
                (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz) ≫
              (p ⊗ₘ q) ≫ (λ_ (𝟙_ T.Modules)).hom) ≫ etaG
      rw [hchain]
      simp only [Category.assoc]
      slice_lhs 1 2 => rw [← hinv_delta]
      rw [Functor.OplaxMonoidal.comp_δ]
      slice_lhs 3 4 => erw [Functor.OplaxMonoidal.δ_natural]
      slice_lhs 4 6 => rw [hunit_tensor]
      simp only [Functor.map_comp]
      erw [Category.assoc]
      erw [Category.assoc]

/-- Converting the monoidal-unit pullback trivialization to the structure sheaf
recovers the direct pullback trivialization. -/
private theorem sectionPoleSheafPowerPullbackTrivialization_eq_monoidal
    {C S T : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (f : T ⟶ C)
    (e : (Scheme.Modules.pullback f).obj (sectionPoleSheaf π z hz) ≅
      Scheme.Modules.unitObj T) :
    ∀ n : ℕ,
      sectionPoleSheafPowerPullbackTrivialization z hz f e n =
        sectionPoleSheafPowerPullbackMonoidalTrivialization z hz f
            (e ≪≫ (monoidalUnitObjIso T).symm) n ≪≫
          monoidalUnitObjIso T
  | 0 => rfl
  | n + 1 => by
      apply Iso.ext
      have hstructSucc :
          sectionPoleSheafPowerPullbackTrivialization z hz f e (n + 1) =
            (Functor.Monoidal.μIso (Scheme.Modules.pullback f)
                (sectionPoleSheafPower π z hz n)
                (sectionPoleSheaf π z hz)).symm ≪≫
              (sectionPoleSheafPowerPullbackTrivialization z hz f e n ⊗ᵢ e) ≪≫
              unitObjTensorIso T := rfl
      have hmonoidalSucc :
          sectionPoleSheafPowerPullbackMonoidalTrivialization z hz f
              (e ≪≫ (monoidalUnitObjIso T).symm) (n + 1) =
            (Functor.Monoidal.μIso (Scheme.Modules.pullback f)
                (sectionPoleSheafPower π z hz n)
                (sectionPoleSheaf π z hz)).symm ≪≫
              (sectionPoleSheafPowerPullbackMonoidalTrivialization z hz f
                  (e ≪≫ (monoidalUnitObjIso T).symm) n ⊗ᵢ
                (e ≪≫ (monoidalUnitObjIso T).symm)) ≪≫
              λ_ (𝟙_ T.Modules) := rfl
      rw [hstructSucc, hmonoidalSucc]
      simp only [Iso.trans_hom, Iso.symm_hom,
        MonoidalCategory.tensorIso_hom, unitObjTensorIso]
      rw [sectionPoleSheafPowerPullbackTrivialization_eq_monoidal
        z hz f e n]
      simp only [Iso.trans_hom, Category.assoc]
      have htensor :
          (((sectionPoleSheafPowerPullbackMonoidalTrivialization z hz f
                (e ≪≫ (monoidalUnitObjIso T).symm) n).hom ≫
              (monoidalUnitObjIso T).hom) ⊗ₘ e.hom) ≫
              ((monoidalUnitObjIso T).inv ⊗ₘ
                (monoidalUnitObjIso T).inv) =
            (sectionPoleSheafPowerPullbackMonoidalTrivialization z hz f
                (e ≪≫ (monoidalUnitObjIso T).symm) n).hom ⊗ₘ
              (e.hom ≫ (monoidalUnitObjIso T).inv) := by
        rw [MonoidalCategory.tensorHom_comp_tensorHom]
        simp
      change
        (Functor.Monoidal.μIso (Scheme.Modules.pullback f)
              (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz)).inv ≫
            ((((sectionPoleSheafPowerPullbackMonoidalTrivialization z hz f
                    (e ≪≫ (monoidalUnitObjIso T).symm) n).hom ≫
                  (monoidalUnitObjIso T).hom) ⊗ₘ e.hom) ≫
              ((monoidalUnitObjIso T).inv ⊗ₘ
                (monoidalUnitObjIso T).inv)) ≫
            (λ_ (𝟙_ T.Modules)).hom ≫ (monoidalUnitObjIso T).hom =
          (Functor.Monoidal.μIso (Scheme.Modules.pullback f)
              (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz)).inv ≫
            ((sectionPoleSheafPowerPullbackMonoidalTrivialization z hz f
                  (e ≪≫ (monoidalUnitObjIso T).symm) n).hom ⊗ₘ
                (e.hom ≫ (monoidalUnitObjIso T).inv)) ≫
            (λ_ (𝟙_ T.Modules)).hom ≫ (monoidalUnitObjIso T).hom
      rw [htensor]

/-- The structure-sheaf trivialization induced along a composite pullback. -/
private noncomputable def sectionPoleSheafPowerCompPullbackTrivialization
    {C S T U : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (f : T ⟶ C) (g : U ⟶ T) (h : U ⟶ C)
    (α : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback h)
    (e : (Scheme.Modules.pullback f).obj (sectionPoleSheaf π z hz) ≅
      Scheme.Modules.unitObj T) :
    (Scheme.Modules.pullback h).obj (sectionPoleSheaf π z hz) ≅
      Scheme.Modules.unitObj U :=
  (α.app (sectionPoleSheaf π z hz)).symm ≪≫
    (Scheme.Modules.pullback g).mapIso e ≪≫
      Scheme.Modules.pullbackUnitIso g

/-- Pullback composition commutes with pole-power trivializations valued in the
structure sheaf. -/
private theorem sectionPoleSheafPowerPullbackTrivialization_comp
    {C S T U : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (f : T ⟶ C) (g : U ⟶ T) (h : U ⟶ C)
    (α : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback h) [α.hom.IsMonoidal]
    (e : (Scheme.Modules.pullback f).obj (sectionPoleSheaf π z hz) ≅
      Scheme.Modules.unitObj T) :
    ∀ n : ℕ,
      sectionPoleSheafPowerPullbackTrivialization z hz h
          (sectionPoleSheafPowerCompPullbackTrivialization
            z hz f g h α e) n =
        (α.app (sectionPoleSheafPower π z hz n)).symm ≪≫
          (Scheme.Modules.pullback g).mapIso
            (sectionPoleSheafPowerPullbackTrivialization z hz f e n) ≪≫
          Scheme.Modules.pullbackUnitIso g := by
  intro n
  let uT := monoidalUnitObjIso T
  let uU := monoidalUnitObjIso U
  let e₀ := e ≪≫ uT.symm
  let eComp := sectionPoleSheafPowerCompPullbackTrivialization
    z hz f g h α e
  let eComp₀ := sectionPoleSheafPowerCompMonoidalTrivialization
    z hz f g h α e₀
  have hunit := Scheme.Modules.pullback_monoidalUnitObjIso g
  change (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).symm ≪≫ uU =
      (Scheme.Modules.pullback g).mapIso uT ≪≫
        Scheme.Modules.pullbackUnitIso g at hunit
  have hunitHom := congrArg Iso.hom hunit
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at hunitHom
  change (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv ≫ uU.hom =
    ((Scheme.Modules.pullback g).mapIso uT).hom ≫
      (Scheme.Modules.pullbackUnitIso g).hom at hunitHom
  have hunitInv :
      Scheme.Modules.pullbackUnitIso g ≪≫ uU.symm =
        ((Scheme.Modules.pullback g).mapIso uT).symm ≪≫
          (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).symm := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom]
    calc
      (Scheme.Modules.pullbackUnitIso g).hom ≫ uU.inv =
          ((Scheme.Modules.pullback g).mapIso uT).inv ≫
            (((Scheme.Modules.pullback g).mapIso uT).hom ≫
              (Scheme.Modules.pullbackUnitIso g).hom) ≫ uU.inv := by simp
      _ = ((Scheme.Modules.pullback g).mapIso uT).inv ≫
          (((Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv ≫
            uU.hom) ≫ uU.inv) := by rw [hunitHom]
      _ = ((Scheme.Modules.pullback g).mapIso uT).inv ≫
          (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv := by simp
  have hsimple : eComp ≪≫ uU.symm = eComp₀ := by
    apply Iso.ext
    simp only [eComp, eComp₀, e₀,
      sectionPoleSheafPowerCompPullbackTrivialization,
      sectionPoleSheafPowerCompMonoidalTrivialization,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
    rw [← Category.assoc]
    rw [show (Scheme.Modules.pullbackUnitIso g).hom ≫ uU.inv =
        ((Scheme.Modules.pullback g).mapIso uT).inv ≫
          (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv by
      exact congrArg Iso.hom hunitInv]
    change (α.app (sectionPoleSheaf π z hz)).inv ≫
        (Scheme.Modules.pullback g).map e.hom ≫
          (Scheme.Modules.pullback g).map uT.inv ≫
            (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv =
      (α.app (sectionPoleSheaf π z hz)).inv ≫
        (Scheme.Modules.pullback g).map (e.hom ≫ uT.inv) ≫
          (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv
    have hmapComp :=
      ((Scheme.Modules.pullback g).map_comp e.hom uT.inv).symm
    calc
      (α.app (sectionPoleSheaf π z hz)).inv ≫
            (Scheme.Modules.pullback g).map e.hom ≫
            (Scheme.Modules.pullback g).map uT.inv ≫
            (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv =
          (α.app (sectionPoleSheaf π z hz)).inv ≫
            ((Scheme.Modules.pullback g).map e.hom ≫
            (Scheme.Modules.pullback g).map uT.inv) ≫
            (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv := by
            simp only [Category.assoc]
      _ = (α.app (sectionPoleSheaf π z hz)).inv ≫
            ((Scheme.Modules.pullback g).map (e.hom ≫ uT.inv) ≫
              (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv) :=
        congrArg (fun q => (α.app (sectionPoleSheaf π z hz)).inv ≫
          (q ≫ (Functor.Monoidal.εIso
            (Scheme.Modules.pullback g)).inv)) hmapComp
      _ = _ := rfl
  rw [sectionPoleSheafPowerPullbackTrivialization_eq_monoidal
    z hz h eComp n]
  rw [hsimple]
  rw [sectionPoleSheafPowerPullbackMonoidalTrivialization_comp
    z hz f g h α e₀ n]
  rw [CategoryTheory.Iso.trans_assoc]
  rw [CategoryTheory.Iso.trans_assoc]
  rw [hunit]
  have hmap :
      (Scheme.Modules.pullback g).mapIso
          (sectionPoleSheafPowerPullbackMonoidalTrivialization
            z hz f e₀ n) ≪≫
        (Scheme.Modules.pullback g).mapIso uT =
      (Scheme.Modules.pullback g).mapIso
        (sectionPoleSheafPowerPullbackTrivialization z hz f e n) := by
    rw [← (Scheme.Modules.pullback g).mapIso_trans]
    rw [← sectionPoleSheafPowerPullbackTrivialization_eq_monoidal
      z hz f e n]
  have hmap' := congrArg
    (fun q => q ≪≫ Scheme.Modules.pullbackUnitIso g) hmap
  rw [CategoryTheory.Iso.trans_assoc] at hmap'
  have hmap'' := congrArg
    (fun q => (α.app (sectionPoleSheafPower π z hz n)).symm ≪≫ q) hmap'
  exact hmap''

private theorem pullbackCongr_inv_isMonoidal
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g) :
    (Scheme.Modules.pullbackCongr hfg).inv.IsMonoidal := by
  subst g
  change NatTrans.IsMonoidal (𝟙 (Scheme.Modules.pullback f))
  infer_instance

/-- Restricting a pole-power trivialization to a smaller open agrees with the
power trivialization induced by the restricted simple-pole trivialization. -/
theorem sectionPoleSheafPowerTrivialization_restrictOpen
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    {U V : C.Opens} (hVU : V ≤ U)
    (e : (sectionPoleSheaf π z hz).restrict U.ι ≅
      Scheme.Modules.unitObj U.toScheme) :
    ∀ n : ℕ,
      Scheme.Modules.restrictOpenTrivialization hVU
          (sectionPoleSheafPowerTrivialization z hz U e n) =
        sectionPoleSheafPowerTrivialization z hz V
          (Scheme.Modules.restrictOpenTrivialization hVU e) n := by
  intro n
  let j := C.homOfLE hVU
  let α : Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback j ≅
      Scheme.Modules.pullback V.ι :=
    Scheme.Modules.pullbackComp j U.ι ≪≫
      (Scheme.Modules.pullbackCongr (C.homOfLE_ι hVU).symm).symm
  let eU := (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app
    (sectionPoleSheaf π z hz) ≪≫ e
  let eV := (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm.app
      (sectionPoleSheaf π z hz) ≪≫
    Scheme.Modules.restrictOpenTrivialization hVU e
  let eComp := sectionPoleSheafPowerCompPullbackTrivialization
    z hz U.ι j V.ι α eU
  letI hcomp : (Scheme.Modules.pullbackComp j U.ι).hom.IsMonoidal :=
    Scheme.Modules.pullbackComp_hom_isMonoidal j U.ι
  letI hcongr :
      (Scheme.Modules.pullbackCongr
        (C.homOfLE_ι hVU).symm).inv.IsMonoidal :=
    pullbackCongr_inv_isMonoidal (C.homOfLE_ι hVU).symm
  letI halpha : α.hom.IsMonoidal := by
    change NatTrans.IsMonoidal
      ((Scheme.Modules.pullbackComp j U.ι).hom ≫
        (Scheme.Modules.pullbackCongr (C.homOfLE_ι hVU).symm).inv)
    exact NatTrans.IsMonoidal.comp _ _
  have heV : eV = eComp := by
    dsimp only [eV]
    rw [Scheme.Modules.restrictOpenTrivialization_eq_pullback hVU e]
    apply Iso.ext
    simp only [eComp,
      sectionPoleSheafPowerCompPullbackTrivialization,
      Scheme.Modules.restrictOpenTrivializationPullback,
      Scheme.Modules.restrictTrivialization, eU, α, j,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp
  rw [sectionPoleSheafPowerTrivialization_eq_pullback
    z hz V (Scheme.Modules.restrictOpenTrivialization hVU e) n]
  change _ = (Scheme.Modules.restrictFunctorIsoPullback V.ι).app
      (sectionPoleSheafPower π z hz n) ≪≫
        sectionPoleSheafPowerPullbackTrivialization z hz V.ι eV n
  rw [heV]
  rw [sectionPoleSheafPowerPullbackTrivialization_comp
    z hz U.ι j V.ι α eU n]
  rw [Scheme.Modules.restrictOpenTrivialization_eq_pullback hVU
    (sectionPoleSheafPowerTrivialization z hz U e n)]
  simp only [Scheme.Modules.restrictOpenTrivializationPullback,
    Scheme.Modules.restrictTrivialization]
  rw [sectionPoleSheafPowerTrivialization_eq_pullback z hz U e n]
  simp only [eU, α, j]
  let rInv := (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app
    (sectionPoleSheafPower π z hz n)
  let rHom := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app
    (sectionPoleSheafPower π z hz n)
  let q := sectionPoleSheafPowerPullbackTrivialization z hz U.ι
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app
      (sectionPoleSheaf π z hz) ≪≫ e) n
  have hinside : rInv ≪≫ rHom ≪≫ q = q := by
    dsimp only [rInv, rHom]
    apply Iso.ext
    simp
  have hmapInside := congrArg
    (fun k => (Scheme.Modules.pullback j).mapIso k) hinside
  dsimp only [rInv, rHom, q] at hmapInside
  have halphaApp :
      (α.app (sectionPoleSheafPower π z hz n)).symm =
        (Scheme.Modules.pullbackCongr
            (C.homOfLE_ι hVU).symm).app
              (sectionPoleSheafPower π z hz n) ≪≫
          ((Scheme.Modules.pullbackComp j U.ι).app
            (sectionPoleSheafPower π z hz n)).symm := by
    rfl
  rw [halphaApp]
  have hfull := congrArg
    (fun k => (Scheme.Modules.restrictFunctorIsoPullback V.ι).app
        (sectionPoleSheafPower π z hz n) ≪≫
      (Scheme.Modules.pullbackCongr
          (C.homOfLE_ι hVU).symm).app
            (sectionPoleSheafPower π z hz n) ≪≫
      ((Scheme.Modules.pullbackComp j U.ι).app
          (sectionPoleSheafPower π z hz n)).symm ≪≫ k ≪≫
      Scheme.Modules.pullbackUnitIso j) hmapInside
  simpa only [j, CategoryTheory.Iso.trans_assoc] using hfull

end PolePowerRestriction

/-- A global module section, restricted to the top open of an affine open
subscheme. -/
noncomputable def localTrivializationRestriction {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens) (m : Γ(M, (⊤ : X.Opens))) :
    Γ(M.restrict U.1.ι, (⊤ : U.1.toScheme.Opens)) :=
  (M.restrictAppIso U.1.ι (⊤ : U.1.toScheme.Opens)).inv
    (M.presheaf.map (eqToHom U.1.ι_image_top).op
      (M.presheaf.map (homOfLE le_top).op m))

@[simp]
theorem localTrivializationRestriction_add {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens) (m n : Γ(M, (⊤ : X.Opens))) :
    localTrivializationRestriction M U (m + n) =
      localTrivializationRestriction M U m +
        localTrivializationRestriction M U n := by
  simp [localTrivializationRestriction, map_add]

@[simp]
theorem localTrivializationRestriction_zero {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens) : localTrivializationRestriction M U 0 = 0 := by
  simp [localTrivializationRestriction, map_zero]

/-- Restricting a global section commutes with a morphism of scheme modules. -/
theorem localTrivializationRestriction_map
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (U : X.affineOpens) (m : Γ(M, (⊤ : X.Opens))) :
    localTrivializationRestriction N U (f.val.app (.op ⊤) m) =
      ((Scheme.Modules.restrictFunctor U.1.ι).map f).val.app (.op ⊤)
        (localTrivializationRestriction M U m) := by
  unfold localTrivializationRestriction
  have htop := PresheafOfModules.naturality_apply f.val
    (homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op m
  have himage := PresheafOfModules.naturality_apply f.val
    (eqToHom U.1.ι_image_top).op
      (M.presheaf.map
        (homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op m)
  erw [← htop, ← himage]
  rfl

/-- A restricted section, expressed in the trivial unit module. -/
noncomputable def localTrivializationTopSection {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme)
    (m : Γ(M, (⊤ : X.Opens))) :
    Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
  e.hom.val.app (.op ⊤) (localTrivializationRestriction M U m)

@[simp]
theorem localTrivializationTopSection_add {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme)
    (m n : Γ(M, (⊤ : X.Opens))) :
    localTrivializationTopSection M U e (m + n) =
      localTrivializationTopSection M U e m +
        localTrivializationTopSection M U e n := by
  unfold localTrivializationTopSection
  rw [localTrivializationRestriction_add]
  exact (e.hom.val.app (.op ⊤)).hom.map_add _ _

@[simp]
theorem localTrivializationTopSection_zero {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme) :
    localTrivializationTopSection M U e 0 = 0 := by
  unfold localTrivializationTopSection
  rw [localTrivializationRestriction_zero]
  exact (e.hom.val.app (.op ⊤)).hom.map_zero

/-- The coefficient of a global module section in a chosen trivialization on an
affine open. -/
noncomputable def localTrivializationCoefficient {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme)
    (m : Γ(M, (⊤ : X.Opens))) : Γ(X, U.1) :=
  affineOpenAmbientSection U (localTrivializationTopSection M U e m)

@[simp]
theorem localTrivializationCoefficient_add {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme)
    (m n : Γ(M, (⊤ : X.Opens))) :
    localTrivializationCoefficient M U e (m + n) =
      localTrivializationCoefficient M U e m +
        localTrivializationCoefficient M U e n := by
  unfold localTrivializationCoefficient
  rw [localTrivializationTopSection_add, affineOpenAmbientSection_add]

@[simp]
theorem localTrivializationCoefficient_zero {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme) :
    localTrivializationCoefficient M U e 0 = 0 := by
  unfold localTrivializationCoefficient
  rw [localTrivializationTopSection_zero, affineOpenAmbientSection_zero]

/-- A ring section, viewed as a module section through an over-site
trivialization. -/
noncomputable def overTrivializationSection {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U)) : Γ(M, U) :=
  e.inv.val.app (.op (Over.mk (𝟙 U))) r

/-- The coefficient of the module section constructed through a trivialization
is the original ring section. -/
theorem overTrivializationSection_coefficient {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U)) :
    e.hom.val.app (.op (Over.mk (𝟙 U)))
        (overTrivializationSection M U e r) = r := by
  have hcomp := congrArg (fun q => q.val.app (.op (Over.mk (𝟙 U))))
    e.inv_hom_id
  exact ConcreteCategory.congr_hom hcomp r

@[simp]
theorem overTrivializationSection_add {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r s : Γ(X, U)) :
    overTrivializationSection M U e (r + s) =
      overTrivializationSection M U e r + overTrivializationSection M U e s := by
  exact (e.inv.val.app (.op (Over.mk (𝟙 U)))).hom.map_add r s

@[simp]
theorem overTrivializationSection_zero {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    overTrivializationSection M U e 0 = 0 := by
  exact (e.inv.val.app (.op (Over.mk (𝟙 U)))).hom.map_zero

/-- Constructing a section through a trivialization commutes with restriction
to a smaller open and the induced trivialization. -/
theorem overTrivializationSection_restrict {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (hVU : V ≤ U)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U)) :
    M.presheaf.map (homOfLE hVU).op (overTrivializationSection M U e r) =
      overTrivializationSection M V
        (SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
          (Over.mk (homOfLE hVU)))
        (X.presheaf.map (homOfLE hVU).op r) := by
  unfold overTrivializationSection
  let VU : Over U := Over.mk (homOfLE hVU)
  let k : VU ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from VU
  have hnat := PresheafOfModules.naturality_apply e.inv.val k.op r
  change M.presheaf.map (homOfLE hVU).op
      (e.inv.val.app (.op (Over.mk (𝟙 U))) r) =
    e.inv.val.app (.op ((Over.map VU.hom).obj (Over.mk (𝟙 V))))
      (X.presheaf.map (homOfLE hVU).op r)
  change M.presheaf.map (Over.mkIdTerminal.from VU).left.op
      (e.inv.val.app (.op (Over.mk (𝟙 U))) r) =
    e.inv.val.app (.op VU)
      (X.presheaf.map (Over.mkIdTerminal.from VU).left.op r)
  exact hnat.symm

/-- Ring sections satisfying the scalar transition equation define the same
module section through the corresponding trivializations. -/
theorem overTrivializationSection_eq_of_transition
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r a b : Γ(X, U))
    (h : e.hom = g.hom ≫
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r)
    (hab : a = b * r) :
    overTrivializationSection M U e a =
      overTrivializationSection M U g b := by
  have hright : e.hom.val.app (.op (Over.mk (𝟙 U)))
      (overTrivializationSection M U g b) = b * r := by
    have happ := congrArg
      (fun q => q.val.app (.op (Over.mk (𝟙 U)))) h
    have hx := ConcreteCategory.congr_hom happ
      (overTrivializationSection M U g b)
    change e.hom.val.app (.op (Over.mk (𝟙 U)))
        (g.inv.val.app (.op (Over.mk (𝟙 U))) b) =
      (SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r).val.app
        (.op (Over.mk (𝟙 U)))
        (g.hom.val.app (.op (Over.mk (𝟙 U)))
          (g.inv.val.app (.op (Over.mk (𝟙 U))) b)) at hx
    have hg : g.hom.val.app (.op (Over.mk (𝟙 U)))
        (g.inv.val.app (.op (Over.mk (𝟙 U))) b) = b := by
      have hcomp := congrArg
        (fun q => q.val.app (.op (Over.mk (𝟙 U)))) g.inv_hom_id
      exact ConcreteCategory.congr_hom hcomp b
    rw [hg] at hx
    erw [ModularCurves.SheafOfModules.overUnitScalarEnd_app_apply
      X.ringCatSheaf U r (.op (Over.mk (𝟙 U))) b] at hx
    change e.hom.val.app (.op (Over.mk (𝟙 U)))
        (overTrivializationSection M U g b) =
      b * X.presheaf.map (𝟙 (.op U)) r at hx
    rw [X.presheaf.map_id, ConcreteCategory.id_apply] at hx
    exact hx
  have heq : e.hom.val.app (.op (Over.mk (𝟙 U)))
      (overTrivializationSection M U e a) =
      e.hom.val.app (.op (Over.mk (𝟙 U)))
        (overTrivializationSection M U g b) := by
    rw [overTrivializationSection_coefficient, hright, hab]
  have heq' := congrArg
    (fun x => e.inv.val.app (.op (Over.mk (𝟙 U))) x) heq
  have hcancel (x : (M.over U).val.obj (.op (Over.mk (𝟙 U)))) :
      e.inv.val.app (.op (Over.mk (𝟙 U)))
          (e.hom.val.app (.op (Over.mk (𝟙 U))) x) = x := by
    have hcomp := congrArg
      (fun q => q.val.app (.op (Over.mk (𝟙 U)))) e.hom_inv_id
    have hx := ConcreteCategory.congr_hom hcomp x
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply] at hx
    exact hx
  change (show (M.over U).val.obj (.op (Over.mk (𝟙 U))) from
      overTrivializationSection M U e a) =
    (show (M.over U).val.obj (.op (Over.mk (𝟙 U))) from
      overTrivializationSection M U g b)
  exact (hcancel (overTrivializationSection M U e a)).symm.trans
    (heq'.trans (hcancel (overTrivializationSection M U g b)))

/-- The coefficient of a global section in a trivialization on the over-site of an
open subset. -/
noncomputable def overTrivializationCoefficient {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (m : Γ(M, (⊤ : X.Opens))) : Γ(X, U) :=
  e.hom.val.app (.op (Over.mk (𝟙 U)))
    (M.presheaf.map (homOfLE le_top).op m)

/-- Equality of coefficients in an over-site trivialization detects equality
of the corresponding restricted module sections. -/
theorem restrict_eq_of_overTrivializationCoefficient_eq
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (m n : Γ(M, (⊤ : X.Opens)))
    (h : overTrivializationCoefficient M U e m =
      overTrivializationCoefficient M U e n) :
    M.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op m =
      M.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op n := by
  let T : Over U := Over.mk (𝟙 U)
  let mU := M.presheaf.map
    (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op m
  let nU := M.presheaf.map
    (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op n
  change e.hom.val.app (.op T) mU = e.hom.val.app (.op T) nU at h
  have h' := congrArg (fun x => e.inv.val.app (.op T) x) h
  have hcancel (x : (M.over U).val.obj (.op T)) :
      e.inv.val.app (.op T) (e.hom.val.app (.op T) x) = x := by
    have hcomp := congrArg (fun q => q.val.app (.op T)) e.hom_inv_id
    have hx := ConcreteCategory.congr_hom hcomp x
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply] at hx
    exact hx
  change (show (M.over U).val.obj (.op T) from mU) =
    (show (M.over U).val.obj (.op T) from nU)
  exact (hcancel mU).symm.trans (h'.trans (hcancel nU))

/-- Expressing a scalar multiple in an over-site trivialization restricts the
scalar and multiplies the coefficient. -/
theorem overTrivializationCoefficient_smul {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (a : Γ(X, (⊤ : X.Opens))) (m : Γ(M, (⊤ : X.Opens))) :
    overTrivializationCoefficient M U e (a • m) =
      X.presheaf.map (homOfLE le_top).op a *
        overTrivializationCoefficient M U e m := by
  unfold overTrivializationCoefficient
  rw [M.map_smul]
  let T : Over U := Over.mk (𝟙 U)
  let c : (X.ringCatSheaf.over U).obj.obj (.op T) :=
    X.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op a
  let x : (M.over U).val.obj (.op T) :=
    M.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op m
  have h := (e.hom.val.app (.op T)).hom.map_smul c x
  change (show (X.ringCatSheaf.over U).obj.obj (.op T) from
      e.hom.val.app (.op T) (c • x)) =
    c * (show (X.ringCatSheaf.over U).obj.obj (.op T) from
      e.hom.val.app (.op T) x) at h
  exact h

/-- Coefficients in a restricted over-site trivialization are restrictions of the
original coefficients. -/
theorem overTrivializationCoefficient_restrict {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (hVU : V ≤ U)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (m : Γ(M, (⊤ : X.Opens))) :
    overTrivializationCoefficient M V
        (SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
          (Over.mk (homOfLE hVU))) m =
      X.presheaf.map (homOfLE hVU).op
        (overTrivializationCoefficient M U e m) := by
  unfold overTrivializationCoefficient
  unfold SheafOfModules.restrictOverTrivialization
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  let VU : Over U := Over.mk (homOfLE hVU)
  change e.hom.val.app (.op VU)
      (M.presheaf.map (homOfLE (le_top : V ≤ (⊤ : X.Opens))).op m) =
    X.presheaf.map (homOfLE hVU).op
      (e.hom.val.app (.op (Over.mk (𝟙 U)))
        (M.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op m))
  let k : VU ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from VU
  let mU := M.presheaf.map
    (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op m
  have hnat := PresheafOfModules.naturality_apply e.hom.val k.op mU
  change e.hom.val.app (.op VU)
      ((M.over U).val.map k.op mU) =
    (X.ringCatSheaf.over U).obj.map k.op
      (e.hom.val.app (.op (Over.mk (𝟙 U))) mU) at hnat
  dsimp only [k] at hnat
  change e.hom.val.app (.op VU)
      (M.presheaf.map (Over.mkIdTerminal.from VU).left.op mU) =
    X.presheaf.map (Over.mkIdTerminal.from VU).left.op
      (e.hom.val.app (.op (Over.mk (𝟙 U))) mU) at hnat
  rw [Over.mkIdTerminal_from_left] at hnat
  change e.hom.val.app (.op VU)
      (M.presheaf.map (homOfLE hVU).op mU) =
    X.presheaf.map (homOfLE hVU).op
      (e.hom.val.app (.op (Over.mk (𝟙 U))) mU) at hnat
  rw [← M.presheaf.map_comp_apply] at hnat
  exact hnat

/-- Coefficients transform by the same scalar as their over-site
trivializations. -/
theorem overTrivializationCoefficient_eq_mul_of_transition
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U))
    (h : e.hom = g.hom ≫
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r)
    (m : Γ(M, (⊤ : X.Opens))) :
    overTrivializationCoefficient M U e m =
      overTrivializationCoefficient M U g m * r := by
  unfold overTrivializationCoefficient
  rw [h]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  erw [ModularCurves.SheafOfModules.overUnitScalarEnd_app_apply
    X.ringCatSheaf U r (.op (Over.mk (𝟙 U)))
    (g.hom.val.app (.op (Over.mk (𝟙 U)))
      (M.presheaf.map (homOfLE le_top).op m))]
  change _ * X.presheaf.map (𝟙 (.op U)) r = _ * r
  rw [X.presheaf.map_id]
  rw [ConcreteCategory.id_apply]

/-- An over-site trivialization gives the corresponding trivialization on the open
subscheme. -/
noncomputable def restrictTrivializationOfOverIso
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme :=
  (Scheme.Modules.overFunctorEquiv U).symm.app M ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
      U.sheafOfModulesEquivOverUnit X.ringCatSheaf

/-- Passing from over-site trivializations to open-subscheme trivializations
preserves scalar transitions. -/
theorem restrictTrivializationOfOverIso_hom_eq_comp_scalar
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U))
    (h : e.hom = g.hom ≫
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) :
    (restrictTrivializationOfOverIso M U e).hom =
      (restrictTrivializationOfOverIso M U g).hom ≫
        unitEndomorphismOfTopSection (Scheme.Modules.openTopSection U r) := by
  unfold restrictTrivializationOfOverIso
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  let F := Scheme.Modules.overFunctorEquiv U
  let G := (Scheme.Modules.overEquiv U).functor
  let C₀ := (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom
  let q := SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r
  let d := unitEndomorphismOfTopSection (Scheme.Modules.openTopSection U r)
  change F.inv.app M ≫ G.map e.hom ≫ C₀ =
    (F.inv.app M ≫ G.map g.hom ≫ C₀) ≫ d
  have hs : G.map q ≫ C₀ = C₀ ≫ d := by
    exact Scheme.Modules.overEquiv_unitScalarEnd U r
  have hmap : G.map e.hom = G.map g.hom ≫ G.map q := by
    rw [h, Functor.map_comp]
  have h₁ : F.inv.app M ≫ G.map e.hom ≫ C₀ =
      F.inv.app M ≫ (G.map g.hom ≫ G.map q) ≫ C₀ :=
    congrArg (fun k ↦ F.inv.app M ≫ k ≫ C₀) hmap
  have h₂ : F.inv.app M ≫ (G.map g.hom ≫ G.map q) ≫ C₀ =
      F.inv.app M ≫ G.map g.hom ≫ (G.map q ≫ C₀) :=
    congrArg (fun k ↦ F.inv.app M ≫ k)
      (Category.assoc (G.map g.hom) (G.map q) C₀)
  have h₃ : F.inv.app M ≫ G.map g.hom ≫ (G.map q ≫ C₀) =
      F.inv.app M ≫ G.map g.hom ≫ (C₀ ≫ d) :=
    congrArg (fun k ↦ F.inv.app M ≫ G.map g.hom ≫ k) hs
  have h₄ : F.inv.app M ≫ G.map g.hom ≫ (C₀ ≫ d) =
      (F.inv.app M ≫ G.map g.hom ≫ C₀) ≫ d := by
    have hinner : G.map g.hom ≫ (C₀ ≫ d) =
        (G.map g.hom ≫ C₀) ≫ d :=
      (Category.assoc _ _ _).symm
    have hprefix := congrArg (fun k ↦ F.inv.app M ≫ k) hinner
    exact hprefix.trans (Category.assoc _ _ _).symm
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- A scalar coordinate for a morphism between over-site trivializations gives
the same scalar coordinate after restricting to the open subscheme. -/
theorem restrictFunctor_map_comp_restrictTrivializationOfOverIso_hom_eq_comp_scalar
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U))
    (h : f.over U ≫ eN.hom = eM.hom ≫
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) :
    (Scheme.Modules.restrictFunctor U.ι).map f ≫
        (restrictTrivializationOfOverIso N U eN).hom =
      (restrictTrivializationOfOverIso M U eM).hom ≫
        unitEndomorphismOfTopSection (Scheme.Modules.openTopSection U r) := by
  let G := (Scheme.Modules.overEquiv U).functor
  let F := Scheme.Modules.overFunctorEquiv U
  let C := U.sheafOfModulesEquivOverUnit X.ringCatSheaf
  let q := (Scheme.Modules.restrictFunctor U.ι).map f
  let s := SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r
  let d := unitEndomorphismOfTopSection (Scheme.Modules.openTopSection U r)
  change q ≫ (F.inv.app N ≫ G.map eN.hom ≫ C.hom) =
    (F.inv.app M ≫ G.map eM.hom ≫ C.hom) ≫ d
  have hnat : q ≫ F.inv.app N = F.inv.app M ≫ G.map (f.over U) :=
    F.inv.naturality f
  have hmap : G.map (f.over U) ≫ G.map eN.hom =
      G.map eM.hom ≫ G.map s := by
    rw [← G.map_comp, ← G.map_comp, h]
  have hscalar : G.map s ≫ C.hom = C.hom ≫ d :=
    Scheme.Modules.overEquiv_unitScalarEnd U r
  rw [← Category.assoc q (F.inv.app N) (G.map eN.hom ≫ C.hom)]
  rw [← Category.assoc (q ≫ F.inv.app N) (G.map eN.hom) C.hom]
  rw [hnat]
  rw [Category.assoc (F.inv.app M) (G.map (f.over U)) (G.map eN.hom)]
  rw [hmap]
  rw [← Category.assoc (F.inv.app M) (G.map eM.hom) (G.map s)]
  rw [Category.assoc (F.inv.app M ≫ G.map eM.hom) (G.map s) C.hom]
  rw [hscalar]
  exact congrArg (fun k ↦ k ≫ d)
    (Category.assoc (F.inv.app M) (G.map eM.hom) C.hom)

/-- Passing from open-subscheme trivializations back to over-site
trivializations preserves scalar transitions. -/
theorem overTrivializationOfRestrictIso_hom_eq_comp_scalar
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e g : M.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme)
    (r : Γ(X, U))
    (h : e.hom = g.hom ≫
      unitEndomorphismOfTopSection (Scheme.Modules.openTopSection U r)) :
    (Scheme.Modules.overTrivializationOfRestrictIso M U e).hom =
      (Scheme.Modules.overTrivializationOfRestrictIso M U g).hom ≫
        SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r := by
  let G := (Scheme.Modules.overEquiv U).functor
  let F := Scheme.Modules.overFunctorEquiv U
  let C := U.sheafOfModulesEquivOverUnit X.ringCatSheaf
  let q := SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r
  let d := unitEndomorphismOfTopSection (Scheme.Modules.openTopSection U r)
  apply G.map_injective
  change G.map (Scheme.Modules.overTrivializationOfRestrictIso M U e).hom =
    G.map ((Scheme.Modules.overTrivializationOfRestrictIso M U g).hom ≫ q)
  rw [Functor.map_comp]
  simp only [Scheme.Modules.overTrivializationOfRestrictIso,
    Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom]
  change (F.hom.app M ≫ e.hom ≫ C.inv) =
    (F.hom.app M ≫ g.hom ≫ C.inv) ≫ G.map q
  rw [h]
  have hs := Scheme.Modules.overEquiv_unitScalarEnd U r
  change G.map q ≫ C.hom = C.hom ≫ d at hs
  have hsC := congrArg (fun k ↦ k ≫ C.inv) hs
  have hsC' : G.map q = (C.hom ≫ d) ≫ C.inv := by
    have hcancel : G.map q = (G.map q ≫ C.hom) ≫ C.inv := by
      have h₁ : G.map q = G.map q ≫ 𝟙 _ := (Category.comp_id _).symm
      have h₂ : G.map q ≫ 𝟙 _ = G.map q ≫ (C.hom ≫ C.inv) :=
        congrArg (fun k ↦ G.map q ≫ k) C.hom_inv_id.symm
      have h₃ : G.map q ≫ (C.hom ≫ C.inv) =
          (G.map q ≫ C.hom) ≫ C.inv :=
        (Category.assoc _ _ _).symm
      exact h₁.trans (h₂.trans h₃)
    exact hcancel.trans hsC
  let A := F.hom.app M ≫ g.hom
  change A ≫ d ≫ C.inv = A ≫ C.inv ≫ G.map q
  rw [hsC']
  have hconj : C.inv ≫ ((C.hom ≫ d) ≫ C.inv) = d ≫ C.inv := by
    have h₁ : C.inv ≫ ((C.hom ≫ d) ≫ C.inv) =
        (C.inv ≫ (C.hom ≫ d)) ≫ C.inv :=
      (Category.assoc _ _ _).symm
    have h₂ : (C.inv ≫ (C.hom ≫ d)) ≫ C.inv =
        ((C.inv ≫ C.hom) ≫ d) ≫ C.inv :=
      congrArg (fun k ↦ k ≫ C.inv) (Category.assoc _ _ _).symm
    have h₃ : ((C.inv ≫ C.hom) ≫ d) ≫ C.inv =
        ((𝟙 _) ≫ d) ≫ C.inv :=
      congrArg (fun k ↦ (k ≫ d) ≫ C.inv) C.inv_hom_id
    have h₄ : ((𝟙 _) ≫ d) ≫ C.inv = d ≫ C.inv := by
      rw [Category.id_comp]
    exact h₁.trans (h₂.trans (h₃.trans h₄))
  exact (congrArg (fun k ↦ A ≫ k) hconj).symm

/-- Converting an over-site trivialization to the open subscheme and back
recovers the original trivialization. -/
theorem overTrivializationOfRestrictTrivializationOfOverIso
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Scheme.Modules.overTrivializationOfRestrictIso M U
        (restrictTrivializationOfOverIso M U e) = e := by
  apply Iso.ext
  let G := (Scheme.Modules.overEquiv U).functor
  apply G.map_injective
  simp only [Scheme.Modules.overTrivializationOfRestrictIso,
    restrictTrivializationOfOverIso,
    Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom,
    Functor.mapIso_hom]
  let F := Scheme.Modules.overFunctorEquiv U
  let C := U.sheafOfModulesEquivOverUnit X.ringCatSheaf
  change F.hom.app M ≫ F.inv.app M ≫ G.map e.hom ≫ C.hom ≫ C.inv =
    G.map e.hom
  have hF := F.hom_inv_id_app_assoc M
    (G.map e.hom ≫ C.hom ≫ C.inv)
  have hC₁ : G.map e.hom ≫ (C.hom ≫ C.inv) =
      G.map e.hom ≫ 𝟙 _ :=
    congrArg (fun k ↦ G.map e.hom ≫ k) C.hom_inv_id
  have hC₂ : G.map e.hom ≫ 𝟙 _ = G.map e.hom := Category.comp_id _
  exact hF.trans (hC₁.trans hC₂)

/-- Converting an open-subscheme trivialization to the over-site and back
recovers the original trivialization. -/
theorem restrictTrivializationOfOverTrivializationOfRestrictIso
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme) :
    restrictTrivializationOfOverIso M U
        (Scheme.Modules.overTrivializationOfRestrictIso M U e) = e := by
  apply Scheme.Modules.overTrivializationOfRestrictIso_injective
  exact overTrivializationOfRestrictTrivializationOfOverIso M U
    (Scheme.Modules.overTrivializationOfRestrictIso M U e)

private theorem restrictTrivializationOfOverIso_hom_top_apply
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : ((M.restrict U.ι).val.obj (.op (⊤ : U.toScheme.Opens)))) :
    (restrictTrivializationOfOverIso M U e).hom.val.app (.op ⊤) x =
      e.hom.val.app
        (.op (U.overEquivalence.symm.functor.obj (⊤ : U.toScheme.Opens)))
        (((Scheme.Modules.overFunctorEquiv U).inv.app M).val.app (.op ⊤) x) := by
  unfold restrictTrivializationOfOverIso
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]

private theorem affineOpenTopSection_eq_overMap_terminal
    {X : Scheme.{u}} (U : X.affineOpens) (r : Γ(X, U.1)) :
    let V := U.1.overEquivalence.symm.functor.obj
      (⊤ : U.1.toScheme.Opens)
    let k : V ⟶ Over.mk (𝟙 U.1) := Over.mkIdTerminal.from V
    affineOpenTopSection U r =
      (X.ringCatSheaf.over U.1).obj.map k.op r := by
  dsimp only
  unfold affineOpenTopSection
  rw [U.1.ι_appIso]
  change X.presheaf.map (eqToHom U.1.ι_image_top).op r =
    X.presheaf.map
      (Over.mkIdTerminal.from
        (U.1.overEquivalence.symm.functor.obj
          (⊤ : U.1.toScheme.Opens))).left.op r
  congr 2
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

private theorem localTrivializationRestriction_eq_overMap_terminal
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (m : Γ(M, (⊤ : X.Opens))) :
    let V := U.1.overEquivalence.symm.functor.obj
      (⊤ : U.1.toScheme.Opens)
    let k : V ⟶ Over.mk (𝟙 U.1) := Over.mkIdTerminal.from V
    ((Scheme.Modules.overFunctorEquiv U.1).inv.app M).val.app (.op ⊤)
        (localTrivializationRestriction M U m) =
      (M.over U.1).val.map k.op
        (M.presheaf.map (homOfLE le_top).op m) := by
  dsimp only
  erw [Scheme.Modules.overFunctorEquiv_inv_app_apply U.1 M (.op ⊤)
    (localTrivializationRestriction M U m)]
  unfold localTrivializationRestriction
  change M.presheaf.map (eqToHom U.1.ι_image_top).op
      (M.presheaf.map (homOfLE le_top).op m) =
    M.presheaf.map
      (Over.mkIdTerminal.from
        (U.1.overEquivalence.symm.functor.obj
          (⊤ : U.1.toScheme.Opens))).left.op
      (M.presheaf.map (homOfLE le_top).op m)
  congr 2
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

private theorem overTrivializationCoefficient_eq_local_of_overIso
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (e : M.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (m : Γ(M, (⊤ : X.Opens))) :
    overTrivializationCoefficient M U.1 e m =
      localTrivializationCoefficient M U
        (restrictTrivializationOfOverIso M U.1 e) m := by
  rw [← affineOpenAmbientSection_topSection U
    (overTrivializationCoefficient M U.1 e m)]
  unfold localTrivializationCoefficient
  congr 1
  unfold localTrivializationTopSection overTrivializationCoefficient
  erw [restrictTrivializationOfOverIso_hom_top_apply M U.1 e
    (localTrivializationRestriction M U m)]
  rw [localTrivializationRestriction_eq_overMap_terminal]
  erw [affineOpenTopSection_eq_overMap_terminal U
    (e.hom.val.app (.op (Over.mk (𝟙 U.1)))
      (M.presheaf.map (homOfLE le_top).op m))]
  let V := U.1.overEquivalence.symm.functor.obj
    (⊤ : U.1.toScheme.Opens)
  let k : V ⟶ Over.mk (𝟙 U.1) := Over.mkIdTerminal.from V
  let mU := M.presheaf.map
    (homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op m
  have hnat := PresheafOfModules.naturality_apply e.hom.val k.op mU
  exact hnat.symm

/-- The over-site coefficient associated to an affine-open trivialization is the
same as the coefficient obtained directly on the open subscheme. -/
theorem overTrivializationCoefficient_overTrivializationOfRestrictIso
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme)
    (m : Γ(M, (⊤ : X.Opens))) :
    overTrivializationCoefficient M U.1
        (Scheme.Modules.overTrivializationOfRestrictIso M U.1 e) m =
      localTrivializationCoefficient M U e m := by
  calc
    overTrivializationCoefficient M U.1
        (Scheme.Modules.overTrivializationOfRestrictIso M U.1 e) m =
      localTrivializationCoefficient M U
        (restrictTrivializationOfOverIso M U.1
          (Scheme.Modules.overTrivializationOfRestrictIso M U.1 e)) m :=
      overTrivializationCoefficient_eq_local_of_overIso M U _ m
    _ = localTrivializationCoefficient M U e m := by
      rw [restrictTrivializationOfOverTrivializationOfRestrictIso]

/-- Equality of coefficients in an affine-open trivialization detects equality
of the corresponding restricted module sections. -/
theorem restrict_eq_of_localTrivializationCoefficient_eq
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme)
    (m n : Γ(M, (⊤ : X.Opens)))
    (h : localTrivializationCoefficient M U e m =
      localTrivializationCoefficient M U e n) :
    M.presheaf.map (homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op m =
      M.presheaf.map (homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op n := by
  apply restrict_eq_of_overTrivializationCoefficient_eq M U.1
    (Scheme.Modules.overTrivializationOfRestrictIso M U.1 e)
  rwa [overTrivializationCoefficient_overTrivializationOfRestrictIso,
    overTrivializationCoefficient_overTrivializationOfRestrictIso]

/-- Expressing a scalar multiple in an affine-open trivialization restricts
the scalar and multiplies the coefficient. -/
theorem localTrivializationCoefficient_smul {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme)
    (a : Γ(X, (⊤ : X.Opens))) (m : Γ(M, (⊤ : X.Opens))) :
    localTrivializationCoefficient M U e (a • m) =
      X.presheaf.map (homOfLE le_top).op a *
        localTrivializationCoefficient M U e m := by
  rw [← overTrivializationCoefficient_overTrivializationOfRestrictIso,
    ← overTrivializationCoefficient_overTrivializationOfRestrictIso]
  exact overTrivializationCoefficient_smul M U.1 _ a m

/-- Restricting a coefficient computed in an affine-open trivialization agrees
with computing it in the induced over-site trivialization. -/
theorem localTrivializationCoefficient_restrict
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    {V : X.Opens} (hVU : V ≤ U.1)
    (e : M.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme)
    (m : Γ(M, (⊤ : X.Opens))) :
    overTrivializationCoefficient M V
        (Scheme.Modules.overTrivializationOfRestrictIso M V
          (Scheme.Modules.restrictOpenTrivialization hVU e)) m =
      X.presheaf.map (homOfLE hVU).op
        (localTrivializationCoefficient M U e m) := by
  rw [Scheme.Modules.overTrivializationOfRestrictOpenTrivialization]
  rw [overTrivializationCoefficient_restrict]
  rw [overTrivializationCoefficient_overTrivializationOfRestrictIso]

/-- An equation expressing an ideal generator in an over-site trivialization
restricts to the corresponding equation for the restricted generator. -/
theorem restrictOverTrivialization_inv_comp_over
    {X : Scheme.{u}} {M : X.Modules}
    (i : M ⟶ Scheme.Modules.unitObj X) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U))
    (h : e.inv ≫ i.over U =
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r)
    {V : X.Opens} (hVU : V ≤ U) :
    let j : Over U := Over.mk (homOfLE hVU)
    let eV := SheafOfModules.restrictOverTrivialization
      X.ringCatSheaf M U e j
    eV.inv ≫ i.over V =
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf V
        (X.presheaf.map (homOfLE hVU).op r) := by
  dsimp only
  let j : Over U := Over.mk (homOfLE hVU)
  let eV := SheafOfModules.restrictOverTrivialization
    X.ringCatSheaf M U e j
  change eV.inv ≫ i.over V =
    SheafOfModules.overUnitScalarEnd X.ringCatSheaf V
      (X.presheaf.map (homOfLE hVU).op r)
  apply SheafOfModules.hom_ext
  ext Z
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  have heV : eV.inv.val.app Z
      (show (X.ringCatSheaf.over V).obj.obj Z from 1) =
        e.inv.val.app (.op ((Over.map j.hom).obj Z.unop))
          (show (X.ringCatSheaf.over V).obj.obj Z from 1) :=
    ModularCurves.SheafOfModules.restrictOverTrivialization_inv_app_apply
      X.ringCatSheaf M U e j Z
        (show (X.ringCatSheaf.over V).obj.obj Z from 1)
  rw [heV]
  have happ := congrArg (fun q ↦ q.val.app
    (.op ((Over.map j.hom).obj Z.unop))) h
  have hx := ConcreteCategory.congr_hom happ
    (show (X.ringCatSheaf.over U).obj.obj
      (.op ((Over.map j.hom).obj Z.unop)) from 1)
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hx
  change i.val.app (.op Z.unop.left)
      (e.inv.val.app (.op ((Over.map j.hom).obj Z.unop))
        (show (X.ringCatSheaf.over U).obj.obj
          (.op ((Over.map j.hom).obj Z.unop)) from 1)) =
    (1 : X.presheaf.obj (.op Z.unop.left)) *
      X.presheaf.map Z.unop.hom.op
        (X.presheaf.map (homOfLE hVU).op r)
  change i.val.app (.op ((Over.map j.hom).obj Z.unop).left)
      (e.inv.val.app (.op ((Over.map j.hom).obj Z.unop))
        (show (X.ringCatSheaf.over U).obj.obj
          (.op ((Over.map j.hom).obj Z.unop)) from 1)) =
    (1 : X.presheaf.obj (.op ((Over.map j.hom).obj Z.unop).left)) *
      X.presheaf.map ((Over.map j.hom).obj Z.unop).hom.op r at hx
  have hmap : X.presheaf.map Z.unop.hom.op
      (X.presheaf.map (homOfLE hVU).op r) =
    X.presheaf.map ((Over.map j.hom).obj Z.unop).hom.op r := by
    have hc := congrArg (fun φ ↦ CommRingCat.Hom.hom φ r)
      ((X.presheaf.map_comp (homOfLE hVU).op Z.unop.hom.op).symm)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hc
    refine hc.trans ?_
    exact congrArg (fun ψ ↦ (CommRingCat.Hom.hom (X.presheaf.map ψ)) r)
      (Subsingleton.elim _ _)
  rw [hmap]
  exact hx

section

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

/-- If two trivializations differ by multiplication by `s`, then their dual
coordinates differ by multiplication by `s` in the opposite direction. -/
theorem dualTrivializationLinearEquiv_eq_mul_of_transition
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(X, U))
    (h : g.hom = e.hom ≫
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s)
    (alpha : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (show Γ(X, U) from
      SheafOfModules.dualTrivializationLinearEquiv X.ringCatSheaf M U e alpha) =
      s * (show Γ(X, U) from
        SheafOfModules.dualTrivializationLinearEquiv
          X.ringCatSheaf M U g alpha) := by
  let T : Over U := Over.mk (𝟙 U)
  let oneU : (X.ringCatSheaf.over U).obj.obj (.op T) := 1
  let sU : (X.ringCatSheaf.over U).obj.obj (.op T) := s
  change (show (X.ringCatSheaf.over U).obj.obj (.op T) from
      alpha.val.app (.op T) (e.inv.val.app (.op T) oneU)) =
    sU * (show (X.ringCatSheaf.over U).obj.obj (.op T) from
      alpha.val.app (.op T) (g.inv.val.app (.op T) oneU))
  have he_one : e.hom.val.app (.op T) (e.inv.val.app (.op T) oneU) = oneU := by
    have hcomp := congrArg (fun q ↦ q.val.app (.op T)) e.inv_hom_id
    have happ := ConcreteCategory.congr_hom hcomp oneU
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply] at happ
    exact happ
  have hge : g.hom.val.app (.op T) (e.inv.val.app (.op T) oneU) = sU := by
    rw [h]
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    rw [he_one]
    erw [ModularCurves.SheafOfModules.overUnitScalarEnd_app_apply
      X.ringCatSheaf U s (.op T) oneU]
    change (1 : Γ(X, U)) * X.presheaf.map (𝟙 (.op U)) s = s
    rw [X.presheaf.map_id]
    simp
  have hg_cancel (x : (M.over U).val.obj (.op T)) :
      g.inv.val.app (.op T) (g.hom.val.app (.op T) x) = x := by
    have hcomp := congrArg (fun q ↦ q.val.app (.op T)) g.hom_inv_id
    have happ := ConcreteCategory.congr_hom hcomp x
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply] at happ
    exact happ
  have hgen : e.inv.val.app (.op T) oneU =
      sU • g.inv.val.app (.op T) oneU := by
    calc
      e.inv.val.app (.op T) oneU =
          g.inv.val.app (.op T)
            (g.hom.val.app (.op T) (e.inv.val.app (.op T) oneU)) :=
        (hg_cancel (e.inv.val.app (.op T) oneU)).symm
      _ = g.inv.val.app (.op T) sU :=
        congrArg (fun x ↦ g.inv.val.app (.op T) x) hge
      _ = g.inv.val.app (.op T) (sU • oneU) := by
        congr 1
        change s = s * 1
        rw [mul_one]
      _ = sU • g.inv.val.app (.op T) oneU :=
        (g.inv.val.app (.op T)).hom.map_smul sU oneU
  rw [hgen, (alpha.val.app (.op T)).hom.map_smul]
  rfl

/-- Dualization reverses a scalar transition between trivializations. -/
theorem dualOverIsoOfIso_hom_eq_comp_scalar
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(X, U))
    (h : g.hom = e.hom ≫
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s) :
    (SheafOfModules.dualOverIsoOfIso X.ringCatSheaf M U e).hom =
      (SheafOfModules.dualOverIsoOfIso X.ringCatSheaf M U g).hom ≫
        SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s := by
  apply SheafOfModules.hom_ext
  ext V alpha
  let eV := SheafOfModules.restrictOverTrivialization
    X.ringCatSheaf M U e V.unop
  let gV := SheafOfModules.restrictOverTrivialization
    X.ringCatSheaf M U g V.unop
  let sV : X.ringCatSheaf.obj.obj (.op V.unop.left) :=
    X.presheaf.map V.unop.hom.op s
  have hV : gV.hom = eV.hom ≫
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf V.unop.left sV := by
    have hV' := restrictOverTrivialization_hom_eq_comp_scalar
      M (leOfHom V.unop.hom) e g s h
    convert hV' using 1
    all_goals rfl
  have hcoord := dualTrivializationLinearEquiv_eq_mul_of_transition
    M V.unop.left eV gV sV hV alpha
  change SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M V.unop.left eV alpha = _
  change SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M V.unop.left eV alpha =
    (SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s).val.app V
      ((SheafOfModules.dualOverIsoOfIso
        X.ringCatSheaf M U g).hom.val.app V alpha)
  erw [ModularCurves.SheafOfModules.overUnitScalarEnd_app_apply
    X.ringCatSheaf U s V
      ((SheafOfModules.dualOverIsoOfIso
        X.ringCatSheaf M U g).hom.val.app V alpha)]
  have hg : (SheafOfModules.dualOverIsoOfIso
      X.ringCatSheaf M U g).hom.val.app V alpha =
    SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M V.unop.left gV alpha := by
    rfl
  rw [hg]
  change SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M V.unop.left eV alpha =
    SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M V.unop.left gV alpha * sV
  change SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M V.unop.left eV alpha =
    sV * SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M V.unop.left gV alpha at hcoord
  exact hcoord.trans (mul_comm' sV
    (SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M V.unop.left gV alpha))

/-- The over-site trivialization induced by a principal generator identifies the
inclusion of the ideal module with multiplication by that generator. -/
theorem localIdealGeneratorOverTrivialization_inv_comp
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.affineOpens) (r : Γ(Y, U.1)) (hr : r ∈ f.ker.ideal U)
    (hspan : f.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, U.1)) :
    let eGen := localIdealGeneratorIso f U r hr hspan hnzd
    let eOver := Scheme.Modules.overTrivializationOfRestrictIso
      (idealModule f) U.1 eGen.symm
    eOver.inv ≫ (idealModuleToUnit f).over U.1 =
      SheafOfModules.overUnitScalarEnd Y.ringCatSheaf U.1 r := by
  dsimp only
  let eGen := localIdealGeneratorIso f U r hr hspan hnzd
  let eOver := Scheme.Modules.overTrivializationOfRestrictIso
    (idealModule f) U.1 eGen.symm
  change eOver.inv ≫ (idealModuleToUnit f).over U.1 =
    SheafOfModules.overUnitScalarEnd Y.ringCatSheaf U.1 r
  let G := (Scheme.Modules.overEquiv U.1).functor
  let F := Scheme.Modules.overFunctorEquiv U.1
  let C := (U.1.sheafOfModulesEquivOverUnit Y.ringCatSheaf).hom
  let A := G.map eOver.inv
  let B := G.map ((idealModuleToUnit f).over U.1)
  let D := G.map
    (SheafOfModules.overUnitScalarEnd Y.ringCatSheaf U.1 r)
  apply G.map_injective
  change A ≫ B = D
  apply (cancel_mono C).1
  change (A ≫ B) ≫ C = D ≫ C
  have hscalar := Scheme.Modules.overEquiv_unitScalarEnd (X := Y) U.1 r
  change D ≫ C = C ≫
    unitEndomorphismOfTopSection (Scheme.Modules.openTopSection U.1 r) at hscalar
  rw [hscalar]
  let FI := F.app (idealModule f)
  let FO := F.app (Scheme.Modules.unitObj Y)
  have hC : FO.hom ≫ (Scheme.Modules.restrictUnitIso U.1.ι).hom = C := by
    dsimp only [FO, F, C]
    rw [Scheme.Modules.overFunctorEquiv_unitP]
    change (Scheme.Modules.restrictUnitIso U.1.ι).inv ≫
      (Scheme.Modules.restrictUnitIso U.1.ι).hom = 𝟙 _
    exact (Scheme.Modules.restrictUnitIso U.1.ι).inv_hom_id
  have hnat := F.hom.naturality (idealModuleToUnit f)
  let q := (Scheme.Modules.restrictFunctor U.1.ι).map (idealModuleToUnit f)
  let eO := (Scheme.Modules.restrictUnitIso U.1.ι).hom
  let H := restrictIdealModuleToUnit f U.1.ι
  change B ≫ FO.hom = FI.hom ≫ q at hnat
  have hBC : B ≫ C = FI.hom ≫ H := by
    change B ≫ C = FI.hom ≫ (q ≫ eO)
    rw [← hC]
    have hnatComp := congrArg (fun p ↦ p ≫ eO) hnat
    have hleft : B ≫ (FO.hom ≫ eO) = (B ≫ FO.hom) ≫ eO :=
      (Category.assoc _ _ _).symm
    have hright : (FI.hom ≫ q) ≫ eO = FI.hom ≫ (q ≫ eO) :=
      Category.assoc _ _ _
    exact hleft.trans (hnatComp.trans hright)
  have hA : A = C ≫ eGen.hom ≫ FI.inv := by
    dsimp only [A, eOver, Scheme.Modules.overTrivializationOfRestrictIso]
    simp only [Functor.FullyFaithful.preimageIso_inv,
      Functor.FullyFaithful.map_preimage, Iso.trans_inv]
    rfl
  have h₀ : (A ≫ B) ≫ C = A ≫ (B ≫ C) := Category.assoc _ _ _
  have h₁ : A ≫ (B ≫ C) =
      (C ≫ eGen.hom ≫ FI.inv) ≫ (FI.hom ≫ H) :=
    congrArg₂ (fun p q ↦ p ≫ q) hA hBC
  have hcanc : FI.inv ≫ FI.hom ≫ H = H := FI.inv_hom_id_assoc H
  have hprefix := congrArg (fun p ↦ C ≫ eGen.hom ≫ p) hcanc
  have h₂ : (C ≫ eGen.hom ≫ FI.inv) ≫ (FI.hom ≫ H) =
      C ≫ eGen.hom ≫ H := by
    have houter :=
      Category.assoc C (eGen.hom ≫ FI.inv) (FI.hom ≫ H)
    have hinner :=
      Category.assoc eGen.hom FI.inv (FI.hom ≫ H)
    have hwhisk := congrArg (fun p ↦ C ≫ p) hinner
    exact houter.trans (hwhisk.trans hprefix)
  have hbase := localIdealGeneratorHom_comp_restrictIdealModuleToUnit
    f U r hr
  change eGen.hom ≫ H =
    unitEndomorphismOfTopSection
      (Scheme.Modules.openTopSection U.1 r) at hbase
  have h₃ : C ≫ eGen.hom ≫ H =
      C ≫ unitEndomorphismOfTopSection
        (Scheme.Modules.openTopSection U.1 r) :=
    congrArg (fun p ↦ C ≫ p) hbase
  exact h₀.trans (h₁.trans (h₂.trans h₃))

private theorem sheafOfModules_mono_of_mono_over_iSup_eq_top
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} (U : ι → Opens X) (hU : iSup U = ⊤)
    (hf : ∀ i, Mono (f.over (U i))) : Mono f := by
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro V x y hxy
  apply TopCat.Sheaf.eq_of_locally_eq'
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
      (fun i ↦ V.unop ⊓ U i) V.unop
      (fun _ ↦ homOfLE inf_le_left)
  · intro p hp
    have hpU : p ∈ iSup U := by
      rw [hU]
      trivial
    obtain ⟨i, hpi⟩ := Opens.mem_iSup.mp hpU
    exact Opens.mem_iSup.mpr ⟨i, hp, hpi⟩
  · intro i
    let W : Over (U i) := Over.mk
      (homOfLE (inf_le_right : V.unop ⊓ U i ≤ U i))
    haveI : Mono (f.over (U i)) := hf i
    let g := (SheafOfModules.forget (X.ringCatSheaf.over (U i))).map
      (f.over (U i))
    haveI : Mono g := Functor.map_mono _ _
    apply PresheafOfModules.injective_of_mono g (.op W)
    have hx := PresheafOfModules.naturality_apply f.val
      (homOfLE (inf_le_left : V.unop ⊓ U i ≤ V.unop)).op x
    have hy := PresheafOfModules.naturality_apply f.val
      (homOfLE (inf_le_left : V.unop ⊓ U i ≤ V.unop)).op y
    exact hx.trans ((congrArg (fun q ↦ N.val.map
      (homOfLE (inf_le_left : V.unop ⊓ U i ≤ V.unop)).op q) hxy).trans hy.symm)

private theorem sheafOfModules_mono_over
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M N : SheafOfModules R}
    (f : M ⟶ N) (hf : Mono f) (U : C) : Mono (f.over U) := by
  letI := hf
  apply (SheafOfModules.forget (R.over U)).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro V
  haveI : Mono ((SheafOfModules.forget R).map f) :=
    Functor.map_mono (SheafOfModules.forget R) f
  exact PresheafOfModules.injective_of_mono
    ((SheafOfModules.forget R).map f) (.op V.unop.left)

private theorem localIdealGeneratorScalar_mono
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.affineOpens) (r : Γ(Y, U.1)) (hr : r ∈ f.ker.ideal U)
    (hspan : f.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, U.1)) :
    Mono (SheafOfModules.overUnitScalarEnd Y.ringCatSheaf U.1 r) := by
  let eGen := localIdealGeneratorIso f U r hr hspan hnzd
  let eOver := Scheme.Modules.overTrivializationOfRestrictIso
    (idealModule f) U.1 eGen.symm
  have hmono : Mono ((idealModuleToUnit f).over U.1) :=
    sheafOfModules_mono_over (idealModuleToUnit f)
      (idealModuleToUnit_mono f) U.1
  have hcomp : Mono (eOver.inv ≫ (idealModuleToUnit f).over U.1) :=
    @mono_comp _ _ _ _ _ eOver.inv inferInstance
      ((idealModuleToUnit f).over U.1) hmono
  rw [← localIdealGeneratorOverTrivialization_inv_comp
    f U r hr hspan hnzd]
  exact hcomp

private theorem dualMap_over_comp_dualOverIsoOfIso_hom_eq_scalar
    {X : Scheme.{u}} {M : X.Modules}
    (i : M ⟶ Scheme.Modules.unitObj X) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U))
    (h : e.inv ≫ i.over U =
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) :
    (((Scheme.Modules.dualUnitObjIso (X := X)).inv ≫
      Scheme.Modules.dualMapObj i).over U) ≫
        (SheafOfModules.dualOverIsoOfIso
          X.ringCatSheaf M U e).hom =
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r := by
  apply (SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U).injective
  have hr : (SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U)
      (SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) = r := by
    change (SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U)
      ((SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U).symm r) = r
    exact (SheafOfModules.dualUnitSectionsEquiv
      X.ringCatSheaf U).apply_symm_apply r
  rw [hr]
  change
    (Hom.over ((Scheme.Modules.dualUnitObjIso (X := X)).inv ≫
        Scheme.Modules.dualMapObj i) U ≫
      (SheafOfModules.dualOverIsoOfIso
        X.ringCatSheaf M U e).hom).val.app (.op (Over.mk (𝟙 U)))
          (show (X.ringCatSheaf.over U).obj.obj
            (.op (Over.mk (𝟙 U))) from 1) = r
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  change SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M U e
        (SheafOfModules.dualPrecomp X.ringCatSheaf i U
          ((SheafOfModules.dualUnitLinearEquiv
            X.ringCatSheaf U).symm 1)) = r
  change SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
      (e.inv ≫ (i.over U ≫
        (SheafOfModules.dualUnitLinearEquiv
          X.ringCatSheaf U).symm 1)) = r
  let alpha := (SheafOfModules.dualUnitLinearEquiv
    X.ringCatSheaf U).symm 1
  have hcomp : (e.inv ≫ i.over U) ≫ alpha =
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r ≫ alpha :=
    congrArg (fun q ↦ q ≫ alpha) h
  have halpha : alpha = 𝟙 _ := by
    change SheafOfModules.overUnitScalarEnd X.ringCatSheaf U 1 = 𝟙 _
    exact (SheafOfModules.overUnitScalarEndRingHom
      X.ringCatSheaf U).map_one
  change SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
      (e.inv ≫ (i.over U ≫ alpha)) = r
  have h₁ : SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
      (e.inv ≫ (i.over U ≫ alpha)) =
      SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
        ((e.inv ≫ i.over U) ≫ alpha) :=
    congrArg _ (Category.assoc _ _ _).symm
  have h₂ : SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
      ((e.inv ≫ i.over U) ≫ alpha) =
      SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
        (SheafOfModules.overUnitScalarEnd
          X.ringCatSheaf U r ≫ alpha) := congrArg _ hcomp
  have h₃ : SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
      (SheafOfModules.overUnitScalarEnd
        X.ringCatSheaf U r ≫ alpha) = r := by
    rw [halpha, Category.comp_id]
    change (SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U)
      (SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) = r
    exact hr
  exact h₁.trans (h₂.trans h₃)

/-- On a Cartier-generator chart, the canonical map from the structure sheaf to the
simple-pole sheaf is multiplication by the generator under the induced dual
trivialization. -/
theorem sectionPoleUnitHom_over_comp_dualGeneratorTrivialization
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) :
    letI : IsClosedImmersion z := isClosedImmersion_section z hz
    letI : QuasiCompact z := inferInstance
    let eGen := localIdealGeneratorIso z U r hr hspan hnzd
    let eIdeal := Scheme.Modules.overTrivializationOfRestrictIso
      (sectionIdealModule π z hz) U.1 eGen.symm
    ((sectionPoleUnitHom π z hz).over U.1) ≫
        (SheafOfModules.dualOverIsoOfIso
          C.ringCatSheaf (sectionIdealModule π z hz) U.1 eIdeal).hom =
      SheafOfModules.overUnitScalarEnd C.ringCatSheaf U.1 r := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  dsimp only
  exact dualMap_over_comp_dualOverIsoOfIso_hom_eq_scalar
    (sectionIdealToUnit π z hz) U.1 _ r
      (localIdealGeneratorOverTrivialization_inv_comp
        z U r hr hspan hnzd)

private theorem sectionPoleUnitHom_over_mono_of_generator
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) :
    Mono ((sectionPoleUnitHom π z hz).over U.1) := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  let eGen := localIdealGeneratorIso z U r hr hspan hnzd
  let eOver := Scheme.Modules.overTrivializationOfRestrictIso
    (idealModule z) U.1 eGen.symm
  have hscalar : Mono
      (SheafOfModules.overUnitScalarEnd C.ringCatSheaf U.1 r) :=
    localIdealGeneratorScalar_mono z U r hr hspan hnzd
  have hcoord := dualMap_over_comp_dualOverIsoOfIso_hom_eq_scalar
    (idealModuleToUnit z) U.1 eOver r
      (localIdealGeneratorOverTrivialization_inv_comp
        z U r hr hspan hnzd)
  change Mono ((((Scheme.Modules.dualUnitObjIso (X := C)).inv ≫
    Scheme.Modules.dualMapObj (idealModuleToUnit z)).over U.1))
  let q := (((Scheme.Modules.dualUnitObjIso (X := C)).inv ≫
    Scheme.Modules.dualMapObj (idealModuleToUnit z)).over U.1)
  let d := (SheafOfModules.dualOverIsoOfIso
    C.ringCatSheaf (idealModule z) U.1 eOver).hom
  have hqd : Mono (q ≫ d) := by
    rw [hcoord]
    exact hscalar
  letI := hqd
  exact mono_of_mono q d

/-- The canonical inclusion `𝒪_C → 𝒪_C([0])` is a monomorphism. -/
theorem sectionPoleUnitHom_mono
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) :
    Mono (sectionPoleUnitHom π z hz) := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  choose U hxU r hspan hnzd using fun x ↦
    (RelEffCartierDiv.sectionDivisor_isOfficial hsm z hz).locallyPrincipal x
  have hU : iSup (fun x ↦ (U x).1) = ⊤ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      exact Opens.mem_iSup.mpr ⟨x, hxU x⟩
  apply sheafOfModules_mono_of_mono_over_iSup_eq_top
    (sectionPoleUnitHom π z hz) (fun x ↦ (U x).1) hU
  intro x
  have hspanx := hspan x
  change z.ker.ideal (U x) = Ideal.span {r x} at hspanx
  have hr : r x ∈ z.ker.ideal (U x) := by
    rw [hspanx]
    exact Ideal.mem_span_singleton_self (r x)
  exact sectionPoleUnitHom_over_mono_of_generator z hz
    (U x) (r x) hr hspanx (hnzd x)

end

/-- The restriction of `O([0])` to a residue fibre is the pole sheaf of the induced
marked point on that fibre. -/
noncomputable def sectionPoleSheafFiberIso
    {E S : Scheme.{u}} {π : E ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) (s : S) :
    letI : IsSeparated (π.fiberToSpecResidueField s) :=
      by
        change IsSeparated (pullback.snd π (S.fromSpecResidueField s))
        infer_instance
    (Scheme.Modules.pullback (π.fiberι s)).obj (sectionPoleSheaf π z hz) ≅
      sectionPoleSheaf (π.fiberToSpecResidueField s)
        (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) :=
  sectionPoleSheafBaseChangeIso hsm z hz (S.fromSpecResidueField s)

/-- The restriction of `O(n[0])` to a residue fibre is the corresponding tensor power
of the pole sheaf of the induced marked point. -/
noncomputable def sectionPoleSheafPowerFiberIso
    {E S : Scheme.{u}} {π : E ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) (s : S) (n : ℕ) :
    letI : IsSeparated (π.fiberToSpecResidueField s) :=
      by
        change IsSeparated (pullback.snd π (S.fromSpecResidueField s))
        infer_instance
    (Scheme.Modules.pullback (π.fiberι s)).obj
          (sectionPoleSheafPower π z hz n) ≅
        sectionPoleSheafPower (π.fiberToSpecResidueField s)
          (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) n :=
  sectionPoleSheafPowerBaseChangeIso hsm z hz
    (S.fromSpecResidueField s) n

/-- Cover-local invertibility is invariant under isomorphism. -/
private theorem isInvertible_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (e : N ≅ M) :
    Scheme.Modules.IsInvertible N := by
  obtain ⟨ι, U, hU, htriv⟩ := hM
  refine ⟨ι, U, hU, fun i => ?_⟩
  obtain ⟨eM⟩ := htriv i
  exact ⟨(Scheme.Modules.pullback (U i).ι).mapIso e ≪≫ eM⟩

@[simp]
theorem sectionPoleSheafPower_zero {C S : Scheme.{u}} (π : C ⟶ S)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) :
    sectionPoleSheafPower π z hz 0 = 𝟙_ C.Modules :=
  rfl

@[simp]
theorem sectionPoleSheafPower_succ {C S : Scheme.{u}} (π : C ⟶ S)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ) :
    sectionPoleSheafPower π z hz (n + 1) =
      sectionPoleSheafPower π z hz n ⊗ sectionPoleSheaf π z hz :=
  rfl

/-- The first pole power is the simple-pole sheaf. -/
noncomputable def sectionPoleSheafPowerOneIso {C S : Scheme.{u}} (π : C ⟶ S)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) :
    sectionPoleSheafPower π z hz 1 ≅ sectionPoleSheaf π z hz :=
  λ_ (sectionPoleSheaf π z hz)

/-- The canonical filtration map `𝒪_C(n[0]) → 𝒪_C((n+1)[0])`. -/
noncomputable def sectionPoleSheafSuccHom {C S : Scheme.{u}} (π : C ⟶ S)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ) :
    sectionPoleSheafPower π z hz n ⟶ sectionPoleSheafPower π z hz (n + 1) :=
  (ρ_ (sectionPoleSheafPower π z hz n)).inv ≫
    (𝟙 _ ⊗ₘ ((monoidalUnitObjIso C).hom ≫ sectionPoleUnitHom π z hz))

section

local instance (X : Scheme.{u}) :
    ∀ V, IsMulCommutative (X.ringCatSheaf.obj.obj V) :=
  fun V ↦ by
    change IsMulCommutative (X.presheaf.obj V)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

/-- On a Cartier-generator chart, every consecutive pole-filtration map is
multiplication by the same generator under the compatible power
trivializations. -/
theorem sectionPoleSheafSuccHom_restrict_comp_generatorTrivialization
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ) :
    letI : IsClosedImmersion z := isClosedImmersion_section z hz
    letI : QuasiCompact z := inferInstance
    let eGen := localIdealGeneratorIso z U r hr hspan hnzd
    let eIdeal := Scheme.Modules.overTrivializationOfRestrictIso
      (sectionIdealModule π z hz) U.1 eGen.symm
    let ePoleOver := SheafOfModules.dualOverIsoOfIso
      C.ringCatSheaf (sectionIdealModule π z hz) U.1 eIdeal
    let ePole := restrictTrivializationOfOverIso
      (sectionPoleSheaf π z hz) U.1 ePoleOver
    (Scheme.Modules.restrictFunctor U.1.ι).map
          (sectionPoleSheafSuccHom π z hz n) ≫
        (sectionPoleSheafPowerTrivialization z hz U.1 ePole (n + 1)).hom =
      (sectionPoleSheafPowerTrivialization z hz U.1 ePole n).hom ≫
        unitEndomorphismOfTopSection
          (Scheme.Modules.openTopSection U.1 r) := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  let eGen := localIdealGeneratorIso z U r hr hspan hnzd
  let eIdeal := Scheme.Modules.overTrivializationOfRestrictIso
    (sectionIdealModule π z hz) U.1 eGen.symm
  let ePoleOver := SheafOfModules.dualOverIsoOfIso
    C.ringCatSheaf (sectionIdealModule π z hz) U.1 eIdeal
  let ePole := restrictTrivializationOfOverIso
    (sectionPoleSheaf π z hz) U.1 ePoleOver
  let F := Scheme.Modules.restrictFunctor U.1.ι
  letI : (Scheme.Modules.pullback U.1.ι).Monoidal :=
    Scheme.Modules.pullbackMonoidal U.1.ι
  letI : F.Monoidal := Functor.Monoidal.transport
    (Scheme.Modules.restrictFunctorIsoPullback U.1.ι).symm
  let d := unitEndomorphismOfTopSection
    (Scheme.Modules.openTopSection U.1 r)
  let eUnitOver :
      (Scheme.Modules.unitObj C).over U.1 ≅
        SheafOfModules.unit (C.ringCatSheaf.over U.1) := Iso.refl _
  let eUnit := restrictTrivializationOfOverIso
    (Scheme.Modules.unitObj C) U.1 eUnitOver
  have hsimpleOver :
      (sectionPoleUnitHom π z hz).over U.1 ≫ ePoleOver.hom =
        SheafOfModules.overUnitScalarEnd C.ringCatSheaf U.1 r :=
    by
      simpa only [ePoleOver, eIdeal, eGen] using
        sectionPoleUnitHom_over_comp_dualGeneratorTrivialization
          z hz U r hr hspan hnzd
  have hsimple :
      F.map (sectionPoleUnitHom π z hz) ≫ ePole.hom =
        eUnit.hom ≫ d := by
    apply restrictFunctor_map_comp_restrictTrivializationOfOverIso_hom_eq_comp_scalar
      (sectionPoleUnitHom π z hz) U.1 eUnitOver ePoleOver r
    exact hsimpleOver.trans (by
      dsimp only [eUnitOver, Iso.refl_hom]
      exact (Category.id_comp _).symm)
  let g : 𝟙_ C.Modules ⟶ sectionPoleSheaf π z hz :=
    (monoidalUnitObjIso C).hom ≫ sectionPoleUnitHom π z hz
  let eZero : F.obj (𝟙_ C.Modules) ≅ Scheme.Modules.unitObj U.1.toScheme :=
    sectionPoleSheafPowerTrivialization z hz U.1 ePole 0
  have hzero : F.map (monoidalUnitObjIso C).hom ≫ eUnit.hom = eZero.hom := by
    let R := Scheme.Modules.restrictFunctorIsoPullback U.1.ι
    let G := Scheme.Modules.pullback U.1.ι
    let q : F.obj (Scheme.Modules.unitObj C) ⟶
        Scheme.Modules.unitObj U.1.toScheme :=
      (Scheme.Modules.restrictUnitIso U.1.ι).hom
    let p : G.obj (Scheme.Modules.unitObj C) ⟶
        Scheme.Modules.unitObj U.1.toScheme :=
      (Scheme.Modules.pullbackUnitIso U.1.ι).hom
    have heUnit : eUnit.hom = q := by
      have hfirst :
          ((Scheme.Modules.overFunctorEquiv U.1).symm.app
            (Scheme.Modules.unitObj C)).hom = q := by
        change ((Scheme.Modules.overFunctorEquiv U.1).app
          (Scheme.Modules.unitObj C)).inv =
            (Scheme.Modules.restrictUnitIso U.1.ι).hom
        rw [Scheme.Modules.overFunctorEquiv_unitP]
        rfl
      let H := (Scheme.Modules.overEquiv U.1).functor
      let A := (Scheme.Modules.unitObj C).over U.1
      let a := ((Scheme.Modules.overFunctorEquiv U.1).symm.app
        (Scheme.Modules.unitObj C)).hom
      change a ≫ H.map (𝟙 A) ≫ 𝟙 (H.obj A) = q
      have hmap : H.map (𝟙 A) = 𝟙 (H.obj A) := H.map_id A
      have hreplace :
          a ≫ H.map (𝟙 A) ≫ 𝟙 (H.obj A) =
            a ≫ 𝟙 (H.obj A) ≫ 𝟙 (H.obj A) :=
        congrArg (fun k ↦ a ≫ k ≫ 𝟙 (H.obj A)) hmap
      have hremove : a ≫ 𝟙 (H.obj A) ≫ 𝟙 (H.obj A) = a := by
        rw [Category.comp_id]
        exact Category.comp_id a
      exact hreplace.trans (hremove.trans hfirst)
    have hpull :
        (Functor.Monoidal.εIso G).inv ≫ (monoidalUnitObjIso U.1.toScheme).hom =
          G.map (monoidalUnitObjIso C).hom ≫ p := by
      have h := congrArg Iso.hom
        (Scheme.Modules.pullback_monoidalUnitObjIso U.1.ι)
      change (Functor.Monoidal.εIso G).inv ≫
          (monoidalUnitObjIso U.1.toScheme).hom =
        G.map (monoidalUnitObjIso C).hom ≫ p at h
      exact h
    have hrestrict :
        R.hom.app (Scheme.Modules.unitObj C) ≫ p = q := by
      have h := restrictFunctorIsoPullback_inv_comp_restrictUnitIso U.1.ι
      let eR := R.app (Scheme.Modules.unitObj C)
      have h' : eR.inv ≫ q = p := h
      calc
        eR.hom ≫ p = eR.hom ≫ (eR.inv ≫ q) :=
          congrArg (fun k ↦ eR.hom ≫ k) h'.symm
        _ = (eR.hom ≫ eR.inv) ≫ q := (Category.assoc _ _ _).symm
        _ = 𝟙 _ ≫ q := congrArg (fun k ↦ k ≫ q) eR.hom_inv_id
        _ = q := Category.id_comp q
    have hnat := R.hom.naturality (monoidalUnitObjIso C).hom
    change F.map (monoidalUnitObjIso C).hom ≫ eUnit.hom =
      R.hom.app (𝟙_ C.Modules) ≫
        (Functor.Monoidal.εIso G).inv ≫
          (monoidalUnitObjIso U.1.toScheme).hom
    rw [heUnit]
    rw [hpull]
    rw [← Category.assoc]
    rw [← hnat]
    rw [Category.assoc]
    rw [hrestrict]
  have hg : F.map g ≫ ePole.hom = eZero.hom ≫ d := by
    dsimp only [g]
    rw [F.map_comp]
    rw [Category.assoc]
    rw [hsimple]
    rw [← Category.assoc]
    exact congrArg (fun k ↦ k ≫ d) hzero
  let P := sectionPoleSheafPower π z hz n
  let eP := sectionPoleSheafPowerTrivialization z hz U.1 ePole n
  have htensor :
      (𝟙 (F.obj P) ⊗ₘ F.map g) ≫ (eP.hom ⊗ₘ ePole.hom) =
        (eP.hom ⊗ₘ eZero.hom) ≫ (𝟙 _ ⊗ₘ d) := by
    calc
      _ = (𝟙 (F.obj P) ≫ eP.hom) ⊗ₘ
          (F.map g ≫ ePole.hom) :=
        tensorHom_comp_tensorHom (𝟙 (F.obj P)) (F.map g)
          eP.hom ePole.hom
      _ = eP.hom ⊗ₘ (eZero.hom ≫ d) := by
        rw [Category.id_comp, hg]
      _ = (eP.hom ⊗ₘ eZero.hom) ≫
          (𝟙 (Scheme.Modules.unitObj U.1.toScheme) ⊗ₘ d) :=
        (tensorHom_comp_tensorHom eP.hom eZero.hom
          (𝟙 (Scheme.Modules.unitObj U.1.toScheme)) d).symm
  have hsource :
      (ρ_ (F.obj P)).inv ≫ (F.obj P ◁ Functor.LaxMonoidal.ε F) ≫
          (eP.hom ⊗ₘ eZero.hom) ≫ (unitObjTensorIso U.1.toScheme).hom =
        eP.hom := by
    let eU := monoidalUnitObjIso U.1.toScheme
    have heZero : eZero.hom =
        Functor.OplaxMonoidal.η F ≫ eU.hom := by
      rfl
    have hfirst :
        (F.obj P ◁ Functor.LaxMonoidal.ε F) ≫
            (eP.hom ⊗ₘ eZero.hom) =
          eP.hom ⊗ₘ eU.hom := by
      rw [heZero]
      rw [← id_tensorHom]
      rw [tensorHom_comp_tensorHom]
      rw [Category.id_comp]
      rw [← Category.assoc]
      rw [Functor.Monoidal.ε_η]
      rw [Category.id_comp]
    have hsecond :
        (eP.hom ⊗ₘ eU.hom) ≫ (unitObjTensorIso U.1.toScheme).hom =
          (ρ_ (F.obj P)).hom ≫ eP.hom := by
      simpa only [eU, P, F, unitObjTensorIso, Iso.trans_hom,
        MonoidalCategory.tensorIso_hom, Iso.symm_hom] using
        tensorUnitIso_hom_naturality_left eU eP.hom
    have htail :
        (F.obj P ◁ Functor.LaxMonoidal.ε F) ≫
            (eP.hom ⊗ₘ eZero.hom) ≫ (unitObjTensorIso U.1.toScheme).hom =
          (ρ_ (F.obj P)).hom ≫ eP.hom := by
      calc
        _ = ((F.obj P ◁ Functor.LaxMonoidal.ε F) ≫
              (eP.hom ⊗ₘ eZero.hom)) ≫
                (unitObjTensorIso U.1.toScheme).hom :=
          (Category.assoc _ _ _).symm
        _ = (eP.hom ⊗ₘ eU.hom) ≫
              (unitObjTensorIso U.1.toScheme).hom :=
          congrArg (fun k ↦ k ≫ (unitObjTensorIso U.1.toScheme).hom) hfirst
        _ = _ := hsecond
    rw [htail]
    simp
  change F.map ((ρ_ P).inv ≫ (𝟙 P ⊗ₘ g)) ≫
      (restrictMonoidalTensorIso U.1.ι P (sectionPoleSheaf π z hz)).hom ≫
      (eP.hom ⊗ₘ ePole.hom) ≫ (unitObjTensorIso U.1.toScheme).hom =
    eP.hom ≫ d
  rw [F.map_comp]
  rw [Functor.Monoidal.map_rightUnitor_inv]
  rw [Functor.Monoidal.map_tensor]
  rw [F.map_id]
  change
    ((ρ_ (F.obj P)).inv ≫ (F.obj P ◁ Functor.LaxMonoidal.ε F) ≫
        Functor.LaxMonoidal.μ F P (𝟙_ C.Modules)) ≫
      (Functor.OplaxMonoidal.δ F P (𝟙_ C.Modules) ≫
        (𝟙 (F.obj P) ⊗ₘ F.map g) ≫
        Functor.LaxMonoidal.μ F P (sectionPoleSheaf π z hz)) ≫
      Functor.OplaxMonoidal.δ F P (sectionPoleSheaf π z hz) ≫
      (eP.hom ⊗ₘ ePole.hom) ≫ (unitObjTensorIso U.1.toScheme).hom =
    eP.hom ≫ d
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [← Category.assoc
    (𝟙 (F.obj P) ⊗ₘ F.map g) (eP.hom ⊗ₘ ePole.hom)]
  rw [htensor]
  have hunitD :
      (𝟙 (Scheme.Modules.unitObj U.1.toScheme) ⊗ₘ d) ≫
          (unitObjTensorIso U.1.toScheme).hom =
        (unitObjTensorIso U.1.toScheme).hom ≫ d := by
    simpa only [unitObjTensorIso, Iso.trans_hom,
      MonoidalCategory.tensorIso_hom, Iso.symm_hom, Category.id_comp,
      Category.assoc] using
      tensorUnitIso_hom_naturality (monoidalUnitObjIso U.1.toScheme)
        (𝟙 (Scheme.Modules.unitObj U.1.toScheme)) d
  rw [Category.assoc (eP.hom ⊗ₘ eZero.hom)
    (𝟙 (Scheme.Modules.unitObj U.1.toScheme) ⊗ₘ d)
    (unitObjTensorIso U.1.toScheme).hom]
  rw [hunitD]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ d) hsource

/-- On a Cartier-generator chart, passing to the next pole power multiplies
the local coefficient by the generator. -/
theorem localTrivializationCoefficient_sectionPoleSheafSuccHom
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ)
    (x : Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens))) :
    letI : IsClosedImmersion z := isClosedImmersion_section z hz
    letI : QuasiCompact z := inferInstance
    let eGen := localIdealGeneratorIso z U r hr hspan hnzd
    let eIdeal := Scheme.Modules.overTrivializationOfRestrictIso
      (sectionIdealModule π z hz) U.1 eGen.symm
    let ePoleOver := SheafOfModules.dualOverIsoOfIso
      C.ringCatSheaf (sectionIdealModule π z hz) U.1 eIdeal
    let ePole := restrictTrivializationOfOverIso
      (sectionPoleSheaf π z hz) U.1 ePoleOver
    localTrivializationCoefficient
        (sectionPoleSheafPower π z hz (n + 1)) U
        (sectionPoleSheafPowerTrivialization z hz U.1 ePole (n + 1))
        ((sectionPoleSheafSuccHom π z hz n).val.app (.op ⊤) x) =
      localTrivializationCoefficient
          (sectionPoleSheafPower π z hz n) U
          (sectionPoleSheafPowerTrivialization z hz U.1 ePole n) x * r := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  let eGen := localIdealGeneratorIso z U r hr hspan hnzd
  let eIdeal := Scheme.Modules.overTrivializationOfRestrictIso
    (sectionIdealModule π z hz) U.1 eGen.symm
  let ePoleOver := SheafOfModules.dualOverIsoOfIso
    C.ringCatSheaf (sectionIdealModule π z hz) U.1 eIdeal
  let ePole := restrictTrivializationOfOverIso
    (sectionPoleSheaf π z hz) U.1 ePoleOver
  let P := sectionPoleSheafPower π z hz n
  let Q := sectionPoleSheafPower π z hz (n + 1)
  let eP := sectionPoleSheafPowerTrivialization z hz U.1 ePole n
  let eQ := sectionPoleSheafPowerTrivialization z hz U.1 ePole (n + 1)
  have htransition :
      (Scheme.Modules.restrictFunctor U.1.ι).map
            (sectionPoleSheafSuccHom π z hz n) ≫ eQ.hom =
        eP.hom ≫ unitEndomorphismOfTopSection
          (Scheme.Modules.openTopSection U.1 r) := by
    simpa only [eQ, eP, ePole, ePoleOver, eIdeal, eGen] using
      sectionPoleSheafSuccHom_restrict_comp_generatorTrivialization
        z hz U r hr hspan hnzd n
  have htransitionTop := congrArg
    (fun k ↦ k.val.app (.op (⊤ : U.1.toScheme.Opens))) htransition
  have htransitionApply := ConcreteCategory.congr_hom htransitionTop
    (localTrivializationRestriction P U x)
  conv_lhs at htransitionApply =>
    erw [Scheme.Modules.sheafOfModules_comp_app_apply]
  conv_rhs at htransitionApply =>
    erw [Scheme.Modules.sheafOfModules_comp_app_apply]
  have htop :
      localTrivializationTopSection Q U eQ
          ((sectionPoleSheafSuccHom π z hz n).val.app (.op ⊤) x) =
        localTrivializationTopSection P U eP x *
          Scheme.Modules.openTopSection U.1 r := by
    unfold localTrivializationTopSection
    erw [localTrivializationRestriction_map]
    rw [htransitionApply]
    let a : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
      eP.hom.val.app (.op (⊤ : U.1.toScheme.Opens))
        (localTrivializationRestriction P U x)
    have hunit := unitEndomorphismOfTopSection_app_apply
      (X := U.1.toScheme) (Scheme.Modules.openTopSection U.1 r)
      (⊤ : U.1.toScheme.Opens) a
    have hrestrict :
        U.1.toScheme.presheaf.map
            (homOfLE (le_top : (⊤ : U.1.toScheme.Opens) ≤ ⊤)).op
              (Scheme.Modules.openTopSection U.1 r) =
          Scheme.Modules.openTopSection U.1 r := by
      rw [Subsingleton.elim
        (homOfLE (le_top : (⊤ : U.1.toScheme.Opens) ≤ ⊤)).op (𝟙 _)]
      have hmap := U.1.toScheme.presheaf.map_id
        (.op (⊤ : U.1.toScheme.Opens))
      have happ := ConcreteCategory.congr_hom hmap
        (Scheme.Modules.openTopSection U.1 r)
      exact happ.trans (by rfl)
    exact hunit.trans (by rw [hrestrict])
  change
    localTrivializationCoefficient Q U eQ
        ((sectionPoleSheafSuccHom π z hz n).val.app (.op ⊤) x) =
      localTrivializationCoefficient P U eP x * r
  unfold localTrivializationCoefficient
  rw [htop, affineOpenAmbientSection_mul]
  congr 1
  change affineOpenAmbientSection U (affineOpenTopSection U r) = r
  exact affineOpenAmbientSection_topSection U r

end

private theorem mono_id_tensorHom_of_iso_unit
    {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {M X Y : D} (e : M ≅ 𝟙_ D) (f : X ⟶ Y) [Mono f] :
    Mono (𝟙 M ⊗ₘ f) := by
  let eX : M ⊗ X ≅ X := whiskerRightIso e X ≪≫ λ_ X
  let eY : M ⊗ Y ≅ Y := whiskerRightIso e Y ≪≫ λ_ Y
  have h : (𝟙 M ⊗ₘ f) ≫ eY.hom = eX.hom ≫ f := by
    dsimp only [eX, eY]
    simp only [Iso.trans_hom, whiskerRightIso_hom, Category.assoc]
    rw [id_tensorHom]
    rw [← Category.assoc, whisker_exchange]
    rw [Category.assoc, leftUnitor_naturality]
  haveI : Mono (eX.hom ≫ f) := mono_comp _ _
  haveI : Mono ((𝟙 M ⊗ₘ f) ≫ eY.hom) := h ▸ inferInstance
  exact mono_of_mono (𝟙 M ⊗ₘ f) eY.hom

private theorem map_id_tensorHom_mono_of_iso_unit
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {M X Y : C}
    (e : F.obj M ≅ 𝟙_ D) (f : X ⟶ Y) (hf : Mono (F.map f)) :
    Mono (F.map (𝟙 M ⊗ₘ f)) := by
  letI : Mono (F.map f) := hf
  haveI : Mono (𝟙 (F.obj M) ⊗ₘ F.map f) :=
    mono_id_tensorHom_of_iso_unit e (F.map f)
  rw [Functor.Monoidal.map_tensor, F.map_id]
  infer_instance

private theorem restrictFunctor_map_mono
    {X : Scheme.{u}} {M N : X.Modules} (U : X.Opens)
    (f : M ⟶ N) (hf : Mono f) :
    Mono ((Scheme.Modules.restrictFunctor U.ι).map f) := by
  let F := (Scheme.Modules.overEquiv U).functor
  let e := Scheme.Modules.overFunctorEquiv U
  haveI : Mono (f.over U) := sheafOfModules_mono_over f hf U
  haveI : Mono (F.map (f.over U)) := Functor.map_mono F (f.over U)
  have hnat := e.hom.naturality f
  have hnat' : F.map (f.over U) ≫ (e.app N).hom =
      (e.app M).hom ≫ (Scheme.Modules.restrictFunctor U.ι).map f := by
    exact hnat
  have hmap : (Scheme.Modules.restrictFunctor U.ι).map f =
      (e.app M).inv ≫ F.map (f.over U) ≫ (e.app N).hom := by
    calc
      _ = (e.app M).inv ≫ ((e.app M).hom ≫
          (Scheme.Modules.restrictFunctor U.ι).map f) := by simp
      _ = (e.app M).inv ≫ (F.map (f.over U) ≫ (e.app N).hom) := by
        exact congrArg (fun q ↦ (e.app M).inv ≫ q) hnat'.symm
      _ = _ := Category.assoc _ _ _
  rw [hmap]
  infer_instance

private theorem sheafOfModules_mono_over_of_restrict_mono
    {X : Scheme.{u}} {M N : X.Modules} (U : X.Opens)
    (f : M ⟶ N) (hf : Mono ((Scheme.Modules.restrictFunctor U.ι).map f)) :
    Mono (f.over U) := by
  let F := (Scheme.Modules.overEquiv U).functor
  let e := Scheme.Modules.overFunctorEquiv U
  have hnat := e.hom.naturality f
  have hnat' : F.map (f.over U) ≫ (e.app N).hom =
      (e.app M).hom ≫ (Scheme.Modules.restrictFunctor U.ι).map f := by
    exact hnat
  letI : Mono ((Scheme.Modules.restrictFunctor U.ι).map f) := hf
  haveI : Mono ((e.app M).hom ≫
      (Scheme.Modules.restrictFunctor U.ι).map f) := mono_comp _ _
  have hleft : Mono (F.map (f.over U) ≫ (e.app N).hom) := by
    rw [hnat']
    infer_instance
  letI := hleft
  haveI : Mono (F.map (f.over U)) := mono_of_mono _ (e.app N).hom
  exact F.mono_of_mono_map
    (show Mono (F.map (f.over U)) from inferInstance)

private theorem sectionPoleSheafSuccHom_over_mono_of_trivialization
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ) (U : C.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj
      (sectionPoleSheafPower π z hz n) ≅ Scheme.Modules.unitObj U.toScheme) :
    Mono ((sectionPoleSheafSuccHom π z hz n).over U) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let eR : F.obj (sectionPoleSheafPower π z hz n) ≅
      Scheme.Modules.unitObj U.toScheme :=
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app
      (sectionPoleSheafPower π z hz n) ≪≫ e
  let eM : F.obj (sectionPoleSheafPower π z hz n) ≅ 𝟙_ U.toScheme.Modules :=
    eR ≪≫ (monoidalUnitObjIso U.toScheme).symm
  let f : 𝟙_ C.Modules ⟶ sectionPoleSheaf π z hz :=
    (monoidalUnitObjIso C).hom ≫ sectionPoleUnitHom π z hz
  have hf : Mono f := by
    dsimp only [f]
    letI : Mono (sectionPoleUnitHom π z hz) :=
      sectionPoleUnitHom_mono hsm z hz
    infer_instance
  have hfR : Mono (F.map f) := restrictFunctor_map_mono U f hf
  letI : (Scheme.Modules.pullback U.ι).Monoidal :=
    Scheme.Modules.pullbackMonoidal U.ι
  letI : F.Monoidal := Functor.Monoidal.transport
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
  have htensor : Mono (F.map (𝟙 (sectionPoleSheafPower π z hz n) ⊗ₘ f)) :=
    map_id_tensorHom_mono_of_iso_unit F eM f hfR
  have hsucc : Mono (F.map (sectionPoleSheafSuccHom π z hz n)) := by
    change Mono (F.map ((ρ_ (sectionPoleSheafPower π z hz n)).inv ≫
      (𝟙 (sectionPoleSheafPower π z hz n) ⊗ₘ f)))
    rw [F.map_comp]
    letI := htensor
    infer_instance
  exact sheafOfModules_mono_over_of_restrict_mono U
    (sectionPoleSheafSuccHom π z hz n) hsucc

/-- The composite filtration map `𝒪_C(n[0]) → 𝒪_C((n+k)[0])`. -/
noncomputable def sectionPoleSheafAddHom {C S : Scheme.{u}} (π : C ⟶ S)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ) :
    ∀ k : ℕ, sectionPoleSheafPower π z hz n ⟶
      sectionPoleSheafPower π z hz (n + k)
  | 0 => eqToHom (by rw [Nat.add_zero])
  | k + 1 => sectionPoleSheafAddHom π z hz n k ≫
      sectionPoleSheafSuccHom π z hz (n + k) ≫
      eqToHom (congrArg (sectionPoleSheafPower π z hz) (by omega))

/-- The pole-filtration map associated to an inequality `n ≤ m`. -/
noncomputable def sectionPoleSheafLEHom {C S : Scheme.{u}} (π : C ⟶ S)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    {n m : ℕ} (h : n ≤ m) :
    sectionPoleSheafPower π z hz n ⟶ sectionPoleSheafPower π z hz m :=
  sectionPoleSheafAddHom π z hz n (m - n) ≫
    eqToHom (congrArg (sectionPoleSheafPower π z hz) (Nat.add_sub_of_le h))

/-- Multiplication of pole sheaves:
`𝒪_C(m[0]) ⊗ 𝒪_C(n[0]) → 𝒪_C((m+n)[0])`. -/
noncomputable def sectionPoleSheafMulHom {C S : Scheme.{u}} (π : C ⟶ S)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (m : ℕ) :
    ∀ n : ℕ, sectionPoleSheafPower π z hz m ⊗
        sectionPoleSheafPower π z hz n ⟶
      sectionPoleSheafPower π z hz (m + n)
  | 0 => (ρ_ (sectionPoleSheafPower π z hz m)).hom ≫
      eqToHom (congrArg (sectionPoleSheafPower π z hz) (by omega))
  | n + 1 => (α_ (sectionPoleSheafPower π z hz m)
        (sectionPoleSheafPower π z hz n) (sectionPoleSheaf π z hz)).inv ≫
      (sectionPoleSheafMulHom π z hz m n ⊗ₘ 𝟙 _) ≫
      eqToHom ((sectionPoleSheafPower_succ π z hz (m + n)).symm.trans
        (congrArg (sectionPoleSheafPower π z hz) (by omega)))

/-- The source trivialization for multiplication of two pole-sheaf powers. -/
noncomputable def sectionPoleSheafPowerMulTrivialization
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.Opens)
    (e : (sectionPoleSheaf π z hz).restrict U.ι ≅
      Scheme.Modules.unitObj U.toScheme) (m n : ℕ) :
    (sectionPoleSheafPower π z hz m ⊗
        sectionPoleSheafPower π z hz n).restrict U.ι ≅
      Scheme.Modules.unitObj U.toScheme :=
  restrictMonoidalTensorIso U.ι
      (sectionPoleSheafPower π z hz m)
      (sectionPoleSheafPower π z hz n) ≪≫
    (sectionPoleSheafPowerTrivialization z hz U e m ⊗ᵢ
      sectionPoleSheafPowerTrivialization z hz U e n) ≪≫
    unitObjTensorIso U.toScheme

/-- The morphism underlying the source trivialization for pole multiplication. -/
private theorem sectionPoleSheafPowerMulTrivialization_hom
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.Opens)
    (e : (sectionPoleSheaf π z hz).restrict U.ι ≅
      Scheme.Modules.unitObj U.toScheme) (m n : ℕ) :
    (sectionPoleSheafPowerMulTrivialization z hz U e m n).hom =
      (restrictMonoidalTensorIso U.ι
          (sectionPoleSheafPower π z hz m)
          (sectionPoleSheafPower π z hz n)).hom ≫
        ((sectionPoleSheafPowerTrivialization z hz U e m).hom ⊗ₘ
          (sectionPoleSheafPowerTrivialization z hz U e n).hom) ≫
            (unitObjTensorIso U.toScheme).hom :=
  rfl

private theorem poleTensor_five_comp_of_three_eq
    {D : Type u} [Category.{v} D]
    {A₀ A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ : D}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂}
    {c : A₀ ⟶ B₁} {d : B₁ ⟶ A₂}
    {e : A₂ ⟶ A₃} {f : A₃ ⟶ A₄}
    {g : B₁ ⟶ B₂} {h : B₂ ⟶ A₄}
    {i : A₄ ⟶ A₅} {j : B₂ ⟶ B₃}
    {k : B₃ ⟶ A₅}
    (h₁ : a ≫ b = c ≫ d) (h₂ : d ≫ e ≫ f = g ≫ h)
    (h₃ : h ≫ i = j ≫ k) :
    a ≫ b ≫ e ≫ f ≫ i = c ≫ g ≫ j ≫ k := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

private theorem poleTensor_nested_four_comp_of_tail_head_last
    {D : Type u} [Category.{v} D]
    {A₀ A₁ A₂ A₃ A₄ B₁ C₁ : D}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂}
    {c : A₂ ⟶ A₃} {d : A₃ ⟶ A₄}
    {e : A₂ ⟶ B₁} {f : B₁ ⟶ A₄}
    {g : A₀ ⟶ C₁} {h : C₁ ⟶ B₁}
    {i : C₁ ⟶ A₄}
    (htail : c ≫ d = e ≫ f)
    (hhead : a ≫ b ≫ e = g ≫ h) (hlast : h ≫ f = i) :
    (a ≫ (b ≫ c)) ≫ d = g ≫ i := by
  calc
    (a ≫ (b ≫ c)) ≫ d = a ≫ ((b ≫ c) ≫ d) :=
      Category.assoc _ _ _
    _ = a ≫ (b ≫ (c ≫ d)) := congrArg
      (fun q ↦ a ≫ q) (Category.assoc _ _ _)
    _ = a ≫ (b ≫ (e ≫ f)) := congrArg
      (fun q ↦ a ≫ (b ≫ q)) htail
    _ = a ≫ ((b ≫ e) ≫ f) := congrArg
      (fun q ↦ a ≫ q) (Category.assoc _ _ _).symm
    _ = (a ≫ (b ≫ e)) ≫ f := (Category.assoc _ _ _).symm
    _ = (g ≫ h) ≫ f := congrArg (fun q ↦ q ≫ f) hhead
    _ = g ≫ (h ≫ f) := Category.assoc _ _ _
    _ = g ≫ i := congrArg (fun q ↦ g ≫ q) hlast

private noncomputable def poleTensorTopSection
    {X : Scheme.{u}} (M N : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) (y : Γ(N, (⊤ : X.Opens))) :
    Γ(M ⊗ N, (⊤ : X.Opens)) :=
  (monoidalTensorObjIso M N).inv.val.app (.op (⊤ : X.Opens))
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app (M.val ⊗ N.val)).app
      (.op (⊤ : X.Opens)) (x ⊗ₜ y))

private noncomputable def poleTopSectionHom
    {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) : Scheme.Modules.unitObj X ⟶ M :=
  M.unitHomEquiv.symm (moduleSectionsOfTop M x)

private theorem poleTopSectionHom_app_top_apply_one
    {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) :
    (poleTopSectionHom M x).val.app (.op ⊤)
      (show X.presheaf.obj (.op ⊤) from 1) = x := by
  change (M.unitHomEquiv (poleTopSectionHom M x)).val (.op ⊤) = x
  let s := moduleSectionsOfTop M x
  have he : M.unitHomEquiv (poleTopSectionHom M x) = s :=
    Equiv.apply_symm_apply M.unitHomEquiv s
  have hv := congrArg (fun t ↦ t.val (.op (⊤ : X.Opens))) he
  rw [hv]
  change M.val.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op x = x
  simp
  rfl

private theorem poleTopSectionHom_app_apply
    {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) (W : X.Opens) (a : Γ(X, W)) :
    (poleTopSectionHom M x).val.app (.op W) a =
      a • M.presheaf.map
        (homOfLE (le_top : W ≤ (⊤ : X.Opens))).op x := by
  rfl

private theorem poleUnitObj_hom_ext_top
    {X : Scheme.{u}} {M : X.Modules}
    {f g : Scheme.Modules.unitObj X ⟶ M}
    (h : f.val.app (.op ⊤) (show X.presheaf.obj (.op ⊤) from 1) =
      g.val.app (.op ⊤) (show X.presheaf.obj (.op ⊤) from 1)) :
    f = g := by
  apply SheafOfModules.hom_ext
  ext V
  let i := (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
  have hf := PresheafOfModules.naturality_apply f.val i
    (show X.presheaf.obj (.op ⊤) from 1)
  have hg := PresheafOfModules.naturality_apply g.val i
    (show X.presheaf.obj (.op ⊤) from 1)
  change f.val.app V
      (X.presheaf.map i (show X.presheaf.obj (.op ⊤) from 1)) =
      M.presheaf.map i
        (f.val.app (.op ⊤) (show X.presheaf.obj (.op ⊤) from 1)) at hf
  change g.val.app V
      (X.presheaf.map i (show X.presheaf.obj (.op ⊤) from 1)) =
      M.presheaf.map i
        (g.val.app (.op ⊤) (show X.presheaf.obj (.op ⊤) from 1)) at hg
  rw [map_one] at hf hg
  exact hf.trans ((congrArg (fun q ↦ M.presheaf.map i q) h).trans hg.symm)

private theorem poleTopSectionHom_localTrivializationRestriction
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (x : Γ(M, (⊤ : X.Opens))) :
    poleTopSectionHom ((Scheme.Modules.restrictFunctor U.1.ι).obj M)
        (localTrivializationRestriction M U x) =
      (Scheme.Modules.restrictUnitIso U.1.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.1.ι).map
          (poleTopSectionHom M x) := by
  apply poleUnitObj_hom_ext_top
  rw [poleTopSectionHom_app_top_apply_one]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  erw [Scheme.Modules.restrictUnitIso_inv_app_applyP]
  rw [map_one]
  unfold localTrivializationRestriction
  let s : Γ(M, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) :=
    M.presheaf.map (eqToHom U.1.ι_image_top).op
      (M.presheaf.map
        (homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op x)
  have hrestrict :
      (M.restrictAppIso U.1.ι (⊤ : U.1.toScheme.Opens)).inv s = s :=
    rfl
  have hmapApply :
      ((Scheme.Modules.restrictFunctor U.1.ι).map
          (poleTopSectionHom M x)).val.app (.op ⊤)
            (show X.presheaf.obj
              (.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))) from 1) =
        (poleTopSectionHom M x).val.app
          (.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
            (show X.presheaf.obj
              (.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))) from 1) :=
    rfl
  have hs : s =
      (poleTopSectionHom M x).val.app
        (.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
          (show X.presheaf.obj
            (.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))) from 1) := by
    dsimp only [s]
    rw [poleTopSectionHom_app_apply, one_smul]
    change M.presheaf.map (eqToHom U.1.ι_image_top).op
        (M.presheaf.map
          (homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op x) =
      M.presheaf.map
        (homOfLE (le_top : U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) ≤
          (⊤ : X.Opens))).op x
    rw [← M.presheaf.map_comp_apply]
    rw [Subsingleton.elim
      ((homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op ≫
        (eqToHom U.1.ι_image_top).op)
      (homOfLE (le_top : U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) ≤
        (⊤ : X.Opens))).op]
  exact hrestrict.trans (hs.trans hmapApply.symm)

private theorem monoidalTensorObjIso_inv_natural
    {X : Scheme.{u}} {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') :
    (PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map (f.val ⊗ₘ g.val) ≫
        (monoidalTensorObjIso M' N').inv =
      (monoidalTensorObjIso M N).inv ≫ (f ⊗ₘ g) := by
  letI : (PresheafOfModules.sheafificationW
      (𝟙 X.ringCatSheaf.obj)).IsMonoidal :=
    @PresheafOfModules.instSheafificationW_isMonoidal_commRingSheaf
      _ _ _ _ _ X.sheaf.obj X.ringCatSheaf.property
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let F : X.PresheafOfModules ⥤ X.Modules :=
    Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)
  letI : F.Monoidal := by
    change (Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)).Monoidal
    infer_instance
  let sh (A : X.PresheafOfModules) : X.Modules := L.obj A
  let δ (A B : X.PresheafOfModules) : sh (A ⊗ B) ⟶ sh A ⊗ sh B :=
    Functor.OplaxMonoidal.δ F A B
  let ε (A : X.Modules) : sh A.val ⟶ A :=
    (Scheme.Modules.sheafifyValIso A).hom
  have hIso (A B : X.Modules) :
      (monoidalTensorObjIso A B).inv =
        δ A.val B.val ≫ (ε A ⊗ₘ ε B) := by
    rfl
  have hδ :
      L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val =
        δ M.val N.val ≫ (L.map f.val ⊗ₘ L.map g.val) :=
    (Functor.OplaxMonoidal.δ_natural F f.val g.val).symm
  have hεf : L.map f.val ≫ ε M' = ε M ≫ f :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.naturality f
  have hεg : L.map g.val ≫ ε N' = ε N ≫ g :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.naturality g
  let e' : (sh M'.val ⊗ sh N'.val) ⟶ (M' ⊗ N') :=
    ε M' ⊗ₘ ε N'
  let e₀ : (sh M.val ⊗ sh N.val) ⟶ (M ⊗ N) :=
    ε M ⊗ₘ ε N
  let lfg : (sh M.val ⊗ sh N.val) ⟶ (sh M'.val ⊗ sh N'.val) :=
    L.map f.val ⊗ₘ L.map g.val
  let fg : (M ⊗ N) ⟶ (M' ⊗ N') := f ⊗ₘ g
  change L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val =
    δ M.val N.val ≫ lfg at hδ
  have hTensorComp : lfg ≫ e' = e₀ ≫ fg := by
    let c₁ : (sh M.val ⊗ sh N.val) ⟶ (M' ⊗ N') :=
      (L.map f.val ≫ ε M') ⊗ₘ (L.map g.val ≫ ε N')
    let c₀ : (sh M.val ⊗ sh N.val) ⟶ (M' ⊗ N') :=
      (ε M ≫ f) ⊗ₘ (ε N ≫ g)
    have hleft : lfg ≫ e' = c₁ := by
      dsimp only [lfg, e', c₁]
      exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
    have hmiddle : c₁ = c₀ := by
      dsimp only [c₁, c₀]
      exact congrArg₂
        (fun (a : sh M.val ⟶ M') (b : sh N.val ⟶ N') ↦ a ⊗ₘ b)
        hεf hεg
    have hright : e₀ ≫ fg = c₀ := by
      dsimp only [e₀, fg, c₀]
      exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
    exact hleft.trans (hmiddle.trans hright.symm)
  rw [hIso M' N', hIso M N]
  change L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val ≫ e' =
    δ M.val N.val ≫ e₀ ≫ fg
  have h₁ :
      L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val ≫ e' =
        (L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val) ≫ e' :=
    (Category.assoc _ _ _).symm
  have h₂ :
      (L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val) ≫ e' =
        (δ M.val N.val ≫ lfg) ≫ e' :=
    congrArg (fun k ↦ k ≫ e') hδ
  have h₃ :
      (δ M.val N.val ≫ lfg) ≫ e' =
        δ M.val N.val ≫ (lfg ≫ e') :=
    Category.assoc _ _ _
  have h₄ :
      δ M.val N.val ≫ (lfg ≫ e') =
        δ M.val N.val ≫ (e₀ ≫ fg) :=
    congrArg (fun k ↦ δ M.val N.val ≫ k) hTensorComp
  have h₅ :
      δ M.val N.val ≫ (e₀ ≫ fg) =
        δ M.val N.val ≫ e₀ ≫ fg :=
    (Category.assoc _ _ _).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

private theorem poleTensorTopSection_map
    {X : Scheme.{u}} {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N')
    (x : Γ(M, (⊤ : X.Opens))) (y : Γ(N, (⊤ : X.Opens))) :
    (f ⊗ₘ g).val.app (.op ⊤) (poleTensorTopSection M N x y) =
      poleTensorTopSection M' N'
        (f.val.app (.op ⊤) x) (g.val.app (.op ⊤) y) := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let t : (M.val ⊗ N.val).obj (.op ⊤) := x ⊗ₜ y
  let t' : (M'.val ⊗ N'.val).obj (.op ⊤) :=
    f.val.app (.op ⊤) x ⊗ₜ g.val.app (.op ⊤) y
  let q := adj.unit.app (M.val ⊗ N.val)
  let q' := adj.unit.app (M'.val ⊗ N'.val)
  let a := q.app (.op ⊤) t
  let a' := q'.app (.op ⊤) t'
  have ht : (f.val ⊗ₘ g.val).app (.op ⊤) t = t' := by
    rfl
  have hunit := adj.unit_naturality (f.val ⊗ₘ g.val)
  change adj.unit.app (M.val ⊗ N.val) ≫
      (L.map (f.val ⊗ₘ g.val)).val =
    (f.val ⊗ₘ g.val) ≫ adj.unit.app (M'.val ⊗ N'.val) at hunit
  have hunitTop := congrArg (fun k ↦ k.app (.op (⊤ : X.Opens))) hunit
  have hunitApply := ConcreteCategory.congr_hom hunitTop t
  conv_lhs at hunitApply =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  conv_rhs at hunitApply =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have hLa : (L.map (f.val ⊗ₘ g.val)).val.app (.op ⊤) a = a' := by
    dsimp only [a, a', q, q']
    have hright := congrArg
      (fun b ↦ (adj.unit.app (M'.val ⊗ N'.val)).app (.op ⊤) b) ht
    exact hunitApply.trans hright
  have hk := monoidalTensorObjIso_inv_natural f g
  have hkTop := congrArg (fun k ↦ k.val.app (.op (⊤ : X.Opens))) hk
  have hkApply := ConcreteCategory.congr_hom hkTop a
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at hkApply
  change (f ⊗ₘ g).val.app (.op ⊤)
      ((monoidalTensorObjIso M N).inv.val.app (.op ⊤) a) =
    (monoidalTensorObjIso M' N').inv.val.app (.op ⊤) a'
  exact hkApply.symm.trans
    (congrArg
      (fun b ↦ (monoidalTensorObjIso M' N').inv.val.app (.op ⊤) b) hLa)

private theorem monoidalTensorObjIso_unit_comp_unitObjTensorIso
    (X : Scheme.{u}) :
    (monoidalTensorObjIso (Scheme.Modules.unitObj X)
          (Scheme.Modules.unitObj X)).inv ≫
        (unitObjTensorIso X).hom =
      (PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map
          (λ_ (Scheme.Modules.unitObj X).val).hom ≫
        (Scheme.Modules.sheafifyValIso
          (Scheme.Modules.unitObj X)).hom := by
  letI : (PresheafOfModules.sheafificationW
      (𝟙 X.ringCatSheaf.obj)).IsMonoidal :=
    @PresheafOfModules.instSheafificationW_isMonoidal_commRingSheaf
      _ _ _ _ _ X.sheaf.obj X.ringCatSheaf.property
  let F : X.PresheafOfModules ⥤ X.Modules :=
    Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)
  letI : F.Monoidal := by
    change (Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)).Monoidal
    infer_instance
  let c := monoidalUnitObjIso X
  have hcc :
      (c.hom ⊗ₘ c.hom) ≫ (c.inv ⊗ₘ c.inv) =
        𝟙 _ := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [c.hom_inv_id]
    rw [MonoidalCategory.tensorHom_id]
    rw [MonoidalCategory.id_whiskerRight]
  let t := (λ_ (𝟙_ X.Modules)).hom ≫ c.hom
  have hcct :
      (c.hom ⊗ₘ c.hom) ≫ (c.inv ⊗ₘ c.inv) ≫ t = t := by
    rw [← Category.assoc, hcc, Category.id_comp]
  have hcancel :
      (monoidalTensorObjIso (Scheme.Modules.unitObj X)
            (Scheme.Modules.unitObj X)).inv ≫
          (unitObjTensorIso X).hom =
        Functor.OplaxMonoidal.δ F
            (Scheme.Modules.unitObj X).val
            (Scheme.Modules.unitObj X).val ≫
          (λ_ (𝟙_ X.Modules)).hom ≫ c.hom := by
    change
      (Localization.Monoidal.μ
          (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
          (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
          (Iso.refl _) (Scheme.Modules.unitObj X).val
            (Scheme.Modules.unitObj X).val).inv ≫
        (c.hom ⊗ₘ c.hom) ≫
        (c.inv ⊗ₘ c.inv) ≫
        (λ_ (𝟙_ X.Modules)).hom ≫ c.hom =
      Functor.OplaxMonoidal.δ F
          (Scheme.Modules.unitObj X).val
          (Scheme.Modules.unitObj X).val ≫
        (λ_ (𝟙_ X.Modules)).hom ≫ c.hom
    let d :=
      (Localization.Monoidal.μ
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
        (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
        (Iso.refl _) (Scheme.Modules.unitObj X).val
          (Scheme.Modules.unitObj X).val).inv
    change d ≫ (c.hom ⊗ₘ c.hom) ≫ (c.inv ⊗ₘ c.inv) ≫ t = d ≫ t
    exact congrArg (fun k ↦ d ≫ k) hcct
  rw [hcancel]
  change
    Functor.OplaxMonoidal.δ F (𝟙_ X.PresheafOfModules)
          (𝟙_ X.PresheafOfModules) ≫
        (λ_ (F.obj (𝟙_ X.PresheafOfModules))).hom ≫ c.hom =
      F.map (λ_ (𝟙_ X.PresheafOfModules)).hom ≫ c.hom
  have heta : Functor.OplaxMonoidal.η F = 𝟙 _ := by
    rfl
  have hid :
      𝟙 (F.obj (𝟙_ X.PresheafOfModules)) ▷
          F.obj (𝟙_ X.PresheafOfModules) = 𝟙 _ :=
    MonoidalCategory.id_whiskerRight _ _
  have hunit := Functor.OplaxMonoidal.left_unitality_hom_assoc F
    (𝟙_ X.PresheafOfModules) c.hom
  rw [heta] at hunit
  let s := (λ_ (F.obj (𝟙_ X.PresheafOfModules))).hom ≫ c.hom
  have hidt :
      (𝟙 (F.obj (𝟙_ X.PresheafOfModules)) ▷
          F.obj (𝟙_ X.PresheafOfModules)) ≫ s = s :=
    (congrArg (fun k ↦ k ≫ s) hid).trans (Category.id_comp s)
  have hpre := congrArg
    (fun k ↦ Functor.OplaxMonoidal.δ F (𝟙_ X.PresheafOfModules)
      (𝟙_ X.PresheafOfModules) ≫ k) hidt
  exact hpre.symm.trans hunit

private theorem unitObjTensorIso_hom_poleTensorTopSection (X : Scheme.{u})
    (a b : Γ(X, (⊤ : X.Opens))) :
    (unitObjTensorIso X).hom.val.app (.op (⊤ : X.Opens))
      (poleTensorTopSection _ _
        (show Γ(Scheme.Modules.unitObj X, (⊤ : X.Opens)) from a)
        (show Γ(Scheme.Modules.unitObj X, (⊤ : X.Opens)) from b)) =
      a * b := by
  let A := Scheme.Modules.unitObj X
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let c := monoidalUnitObjIso X
  let q₀ : (A.val ⊗ A.val).obj (.op (⊤ : X.Opens)) :=
    (show Γ(A, (⊤ : X.Opens)) from a) ⊗ₜ
      (show Γ(A, (⊤ : X.Opens)) from b)
  let uq := (adj.unit.app (A.val ⊗ A.val)).app
    (.op (⊤ : X.Opens)) q₀
  have hmor := monoidalTensorObjIso_unit_comp_unitObjTensorIso X
  have hmorTop := congrArg
    (fun k ↦ k.val.app (.op (⊤ : X.Opens))) hmor
  have hmorApply := ConcreteCategory.congr_hom hmorTop uq
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hmorApply
  change (unitObjTensorIso X).hom.val.app (.op (⊤ : X.Opens))
      ((monoidalTensorObjIso A A).inv.val.app (.op (⊤ : X.Opens)) uq) = _
  rw [hmorApply]
  let f := (λ_ A.val).hom
  have hnat := adj.unit_naturality f
  have htri := adj.right_triangle_components A
  change adj.unit.app (A.val ⊗ A.val) ≫ (L.map f).val =
    f ≫ adj.unit.app A.val at hnat
  change adj.unit.app A.val ≫ c.hom.val = 𝟙 A.val at htri
  have hpresheaf :
      adj.unit.app (A.val ⊗ A.val) ≫ (L.map f).val ≫ c.hom.val = f := by
    have hnatp :
        (adj.unit.app (A.val ⊗ A.val) ≫ (L.map f).val) ≫ c.hom.val =
          (f ≫ adj.unit.app A.val) ≫ c.hom.val :=
      congrArg (fun k ↦ k ≫ c.hom.val) hnat
    have htrip : f ≫ (adj.unit.app A.val ≫ c.hom.val) = f ≫ 𝟙 A.val :=
      congrArg (fun k ↦ f ≫ k) htri
    exact (Category.assoc _ _ _).symm |>.trans <|
      hnatp.trans <| (Category.assoc _ _ _).trans <|
        htrip.trans (Category.comp_id f)
  have hpresheafTop := congrArg
    (fun k ↦ k.app (.op (⊤ : X.Opens))) hpresheaf
  have hpresheafApply := ConcreteCategory.congr_hom hpresheafTop q₀
  erw [PresheafOfModules.comp_app, ModuleCat.comp_apply,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at hpresheafApply
  have hleft : ((λ_ A.val).hom.app (.op (⊤ : X.Opens))) q₀ = a * b := by
    have happ := PresheafOfModules.leftUnitor_hom_app A.val
      (.op (⊤ : X.Opens))
    have heval := ConcreteCategory.congr_hom happ q₀
    have hmodule :
        ((λ_ (ModuleCat.of (X.sheaf.obj.obj (.op (⊤ : X.Opens)))
          (X.sheaf.obj.obj (.op (⊤ : X.Opens))))).hom)
            (a ⊗ₜ b) = a • b :=
      ModuleCat.MonoidalCategory.leftUnitor_hom_apply
        (R := X.sheaf.obj.obj (.op (⊤ : X.Opens)))
        (M := ModuleCat.of (X.sheaf.obj.obj (.op (⊤ : X.Opens)))
          (X.sheaf.obj.obj (.op (⊤ : X.Opens))))
        (show X.sheaf.obj.obj (.op (⊤ : X.Opens)) from a)
        (show X.sheaf.obj.obj (.op (⊤ : X.Opens)) from b)
    have hsmul : a • b = a * b := by
      rfl
    exact heval.trans (hmodule.trans hsmul)
  dsimp only [uq]
  exact hpresheafApply.trans hleft

private theorem unitObjTensorIso_inv_apply_one (X : Scheme.{u}) :
    (unitObjTensorIso X).inv.val.app (.op ⊤)
        (show X.presheaf.obj (.op ⊤) from 1) =
      poleTensorTopSection
        (Scheme.Modules.unitObj X) (Scheme.Modules.unitObj X)
        (show Γ(Scheme.Modules.unitObj X, (⊤ : X.Opens)) from
          (show X.presheaf.obj (.op ⊤) from 1))
        (show Γ(Scheme.Modules.unitObj X, (⊤ : X.Opens)) from
          (show X.presheaf.obj (.op ⊤) from 1)) := by
  let e := unitObjTensorIso X
  let q := poleTensorTopSection
    (Scheme.Modules.unitObj X) (Scheme.Modules.unitObj X)
    (show Γ(Scheme.Modules.unitObj X, (⊤ : X.Opens)) from
      (show X.presheaf.obj (.op ⊤) from 1))
    (show Γ(Scheme.Modules.unitObj X, (⊤ : X.Opens)) from
      (show X.presheaf.obj (.op ⊤) from 1))
  have hmul : e.hom.val.app (.op ⊤) q =
      (show X.presheaf.obj (.op ⊤) from 1) := by
    dsimp only [e, q]
    simpa only [one_mul] using
      unitObjTensorIso_hom_poleTensorTopSection X
        (show Γ(X, (⊤ : X.Opens)) from 1)
        (show Γ(X, (⊤ : X.Opens)) from 1)
  have hcomp := congrArg (fun k ↦ k.val.app (.op (⊤ : X.Opens)))
    e.hom_inv_id
  have hcompApply := ConcreteCategory.congr_hom hcomp q
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hcompApply
  have hcancel := congrArg (fun a ↦ e.inv.val.app (.op ⊤) a) hmul
  exact hcancel.symm.trans hcompApply

private theorem poleTopSectionHom_tensorTopSection
    {X : Scheme.{u}} (M N : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) (y : Γ(N, (⊤ : X.Opens))) :
    poleTopSectionHom (M ⊗ N) (poleTensorTopSection M N x y) =
      (unitObjTensorIso X).inv ≫
        (poleTopSectionHom M x ⊗ₘ poleTopSectionHom N y) := by
  apply poleUnitObj_hom_ext_top
  rw [poleTopSectionHom_app_top_apply_one]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [unitObjTensorIso_inv_apply_one]
  rw [poleTensorTopSection_map]
  exact congrArg₂ (fun a b ↦ poleTensorTopSection M N a b)
    (poleTopSectionHom_app_top_apply_one M x).symm
    (poleTopSectionHom_app_top_apply_one N y).symm

private theorem poleTopSectionHom_comp
    {X : Scheme.{u}} {M N : X.Modules} (x : Γ(M, (⊤ : X.Opens)))
    (f : M ⟶ N) :
    poleTopSectionHom M x ≫ f =
      poleTopSectionHom N (f.val.app (.op ⊤) x) := by
  apply poleUnitObj_hom_ext_top
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  calc
    f.val.app (.op ⊤)
        ((poleTopSectionHom M x).val.app (.op ⊤)
          (show X.presheaf.obj (.op ⊤) from 1)) =
      f.val.app (.op ⊤) x := congrArg
        (fun q ↦ f.val.app (.op ⊤) q)
        (poleTopSectionHom_app_top_apply_one M x)
    _ = (poleTopSectionHom N (f.val.app (.op ⊤) x)).val.app (.op ⊤)
        (show X.presheaf.obj (.op ⊤) from 1) :=
      (poleTopSectionHom_app_top_apply_one N
        (f.val.app (.op ⊤) x)).symm

private theorem poleTensor_restrict_monoidalUnitObjIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    let F := Scheme.Modules.restrictFunctor f
    letI : (Scheme.Modules.pullback f).Monoidal :=
      Scheme.Modules.pullbackMonoidal f
    letI : F.Monoidal := Functor.Monoidal.transport
      (Scheme.Modules.restrictFunctorIsoPullback f).symm
    F.map (monoidalUnitObjIso Y).hom ≫
        (Scheme.Modules.restrictUnitIso f).hom =
      Functor.OplaxMonoidal.η F ≫ (monoidalUnitObjIso X).hom := by
  let F := Scheme.Modules.restrictFunctor f
  let G := Scheme.Modules.pullback f
  letI : G.Monoidal := Scheme.Modules.pullbackMonoidal f
  letI : F.Monoidal := Functor.Monoidal.transport
    (Scheme.Modules.restrictFunctorIsoPullback f).symm
  let R := Scheme.Modules.restrictFunctorIsoPullback f
  let q : F.obj (Scheme.Modules.unitObj Y) ⟶ Scheme.Modules.unitObj X :=
    (Scheme.Modules.restrictUnitIso f).hom
  let p : G.obj (Scheme.Modules.unitObj Y) ⟶ Scheme.Modules.unitObj X :=
    (Scheme.Modules.pullbackUnitIso f).hom
  have hpull :
      (Functor.Monoidal.εIso G).inv ≫ (monoidalUnitObjIso X).hom =
        G.map (monoidalUnitObjIso Y).hom ≫ p := by
    have h := congrArg Iso.hom
      (Scheme.Modules.pullback_monoidalUnitObjIso f)
    change (Functor.Monoidal.εIso G).inv ≫
        (monoidalUnitObjIso X).hom =
      G.map (monoidalUnitObjIso Y).hom ≫ p at h
    exact h
  have hrestrict :
      R.hom.app (Scheme.Modules.unitObj Y) ≫ p = q := by
    have h := restrictFunctorIsoPullback_inv_comp_restrictUnitIso f
    let eR := R.app (Scheme.Modules.unitObj Y)
    have h' : eR.inv ≫ q = p := h
    calc
      eR.hom ≫ p = eR.hom ≫ (eR.inv ≫ q) :=
        congrArg (fun k ↦ eR.hom ≫ k) h'.symm
      _ = (eR.hom ≫ eR.inv) ≫ q := (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ q := congrArg (fun k ↦ k ≫ q) eR.hom_inv_id
      _ = q := Category.id_comp q
  have hnat := R.hom.naturality (monoidalUnitObjIso Y).hom
  change F.map (monoidalUnitObjIso Y).hom ≫ q =
    R.hom.app (𝟙_ Y.Modules) ≫
      (Functor.Monoidal.εIso G).inv ≫ (monoidalUnitObjIso X).hom
  rw [hpull]
  rw [← Category.assoc]
  rw [← hnat]
  rw [Category.assoc]
  rw [hrestrict]

private theorem poleTensor_restrict_monoidalUnitObjIso_inv
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    let F := Scheme.Modules.restrictFunctor f
    letI : (Scheme.Modules.pullback f).Monoidal :=
      Scheme.Modules.pullbackMonoidal f
    letI : F.Monoidal := Functor.Monoidal.transport
      (Scheme.Modules.restrictFunctorIsoPullback f).symm
    (Scheme.Modules.restrictUnitIso f).inv ≫
        F.map (monoidalUnitObjIso Y).inv =
      (monoidalUnitObjIso X).inv ≫ Functor.LaxMonoidal.ε F := by
  let F := Scheme.Modules.restrictFunctor f
  letI : (Scheme.Modules.pullback f).Monoidal :=
    Scheme.Modules.pullbackMonoidal f
  letI : F.Monoidal := Functor.Monoidal.transport
    (Scheme.Modules.restrictFunctorIsoPullback f).symm
  let cY := monoidalUnitObjIso Y
  let cX := monoidalUnitObjIso X
  let r := Scheme.Modules.restrictUnitIso f
  have h := poleTensor_restrict_monoidalUnitObjIso f
  change F.map cY.hom ≫ r.hom =
    Functor.OplaxMonoidal.η F ≫ cX.hom at h
  let eL := F.mapIso cY ≪≫ r
  let eR := (Functor.Monoidal.εIso F).symm ≪≫ cX
  have he : eL = eR := Iso.ext h
  have hinv := congrArg Iso.inv he
  change r.inv ≫ F.map cY.inv =
    cX.inv ≫ Functor.LaxMonoidal.ε F at hinv
  exact hinv

private theorem poleTensor_restrict_unitObjTensorIso_inv
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    let F := Scheme.Modules.restrictFunctor f
    letI : (Scheme.Modules.pullback f).Monoidal :=
      Scheme.Modules.pullbackMonoidal f
    letI : F.Monoidal := Functor.Monoidal.transport
      (Scheme.Modules.restrictFunctorIsoPullback f).symm
    (Scheme.Modules.restrictUnitIso f).inv ≫
        F.map (unitObjTensorIso Y).inv ≫
          (restrictMonoidalTensorIso f
            (Scheme.Modules.unitObj Y) (Scheme.Modules.unitObj Y)).hom =
      (unitObjTensorIso X).inv ≫
        ((Scheme.Modules.restrictUnitIso f).inv ⊗ₘ
          (Scheme.Modules.restrictUnitIso f).inv) := by
  let F := Scheme.Modules.restrictFunctor f
  letI : (Scheme.Modules.pullback f).Monoidal :=
    Scheme.Modules.pullbackMonoidal f
  letI : F.Monoidal := Functor.Monoidal.transport
    (Scheme.Modules.restrictFunctorIsoPullback f).symm
  let cY := monoidalUnitObjIso Y
  let cX := monoidalUnitObjIso X
  let r := Scheme.Modules.restrictUnitIso f
  have hunit := poleTensor_restrict_monoidalUnitObjIso_inv f
  change r.inv ≫ F.map cY.inv =
    cX.inv ≫ Functor.LaxMonoidal.ε F at hunit
  have hunitForward := poleTensor_restrict_monoidalUnitObjIso f
  change F.map cY.hom ≫ r.hom =
    Functor.OplaxMonoidal.η F ≫ cX.hom at hunitForward
  have hunitHom :
      cX.hom ≫ r.inv =
        Functor.LaxMonoidal.ε F ≫ F.map cY.hom := by
    refine (r.comp_inv_eq).2 ?_
    have h₁ :
        (Functor.LaxMonoidal.ε F ≫ F.map cY.hom) ≫ r.hom =
          Functor.LaxMonoidal.ε F ≫ (F.map cY.hom ≫ r.hom) :=
      Category.assoc _ _ _
    have h₂ :
        Functor.LaxMonoidal.ε F ≫ (F.map cY.hom ≫ r.hom) =
          Functor.LaxMonoidal.ε F ≫
            (Functor.OplaxMonoidal.η F ≫ cX.hom) := congrArg
      (fun k : F.obj (𝟙_ Y.Modules) ⟶
          Scheme.Modules.unitObj X ↦
        Functor.LaxMonoidal.ε F ≫ k)
      hunitForward
    have h₃ :
        Functor.LaxMonoidal.ε F ≫
            (Functor.OplaxMonoidal.η F ≫ cX.hom) =
          (Functor.LaxMonoidal.ε F ≫
            Functor.OplaxMonoidal.η F) ≫ cX.hom :=
      (Category.assoc _ _ _).symm
    have h₄ :
        (Functor.LaxMonoidal.ε F ≫
            Functor.OplaxMonoidal.η F) ≫ cX.hom = cX.hom :=
      (congrArg (fun k ↦ k ≫ cX.hom)
        (Functor.Monoidal.ε_η F)).trans (Category.id_comp cX.hom)
    exact (h₁.trans (h₂.trans (h₃.trans h₄))).symm
  have hepsilonTensor :
      Functor.LaxMonoidal.ε F ≫
          (λ_ (F.obj (𝟙_ Y.Modules))).inv ≫
            (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules)) =
        (λ_ (𝟙_ X.Modules)).inv ≫
          (Functor.LaxMonoidal.ε F ⊗ₘ
            Functor.LaxMonoidal.ε F) := by
    calc
      _ = ((λ_ (𝟙_ X.Modules)).inv ≫
          (𝟙_ X.Modules ◁ Functor.LaxMonoidal.ε F)) ≫
            (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules)) :=
        congrArg
          (fun k ↦ k ≫
            (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules)))
          (leftUnitor_inv_naturality (Functor.LaxMonoidal.ε F))
      _ = (λ_ (𝟙_ X.Modules)).inv ≫
          ((𝟙_ X.Modules ◁ Functor.LaxMonoidal.ε F) ≫
            (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules))) :=
        Category.assoc _ _ _
      _ = _ := congrArg
        (fun k ↦ (λ_ (𝟙_ X.Modules)).inv ≫ k)
        (MonoidalCategory.tensorHom_def'
          (Functor.LaxMonoidal.ε F)
          (Functor.LaxMonoidal.ε F)).symm
  have htensorUnit :
      (Functor.LaxMonoidal.ε F ⊗ₘ Functor.LaxMonoidal.ε F) ≫
          (F.map cY.hom ⊗ₘ F.map cY.hom) =
        (cX.hom ⊗ₘ cX.hom) ≫ (r.inv ⊗ₘ r.inv) := by
    have h₁ := tensorHom_comp_tensorHom
      (Functor.LaxMonoidal.ε F) (Functor.LaxMonoidal.ε F)
      (F.map cY.hom) (F.map cY.hom)
    have h₂ :
        (Functor.LaxMonoidal.ε F ≫ F.map cY.hom) ⊗ₘ
            (Functor.LaxMonoidal.ε F ≫ F.map cY.hom) =
          (cX.hom ≫ r.inv) ⊗ₘ (cX.hom ≫ r.inv) := congrArg
      (fun k : 𝟙_ X.Modules ⟶
          F.obj (Scheme.Modules.unitObj Y) ↦ k ⊗ₘ k)
      hunitHom.symm
    have h₃ := tensorHom_comp_tensorHom
      cX.hom cX.hom r.inv r.inv
    exact h₁.trans (h₂.trans h₃.symm)
  have hcore := poleTensor_five_comp_of_three_eq
    hunit hepsilonTensor htensorUnit
  change r.inv ≫
      F.map (cY.inv ≫ (λ_ (𝟙_ Y.Modules)).inv ≫
        (cY.hom ⊗ₘ cY.hom)) ≫
        Functor.OplaxMonoidal.δ F
          (Scheme.Modules.unitObj Y) (Scheme.Modules.unitObj Y) =
    (cX.inv ≫ (λ_ (𝟙_ X.Modules)).inv ≫
      (cX.hom ⊗ₘ cX.hom)) ≫ (r.inv ⊗ₘ r.inv)
  have hmap :
      F.map (cY.inv ≫ (λ_ (𝟙_ Y.Modules)).inv ≫
          (cY.hom ⊗ₘ cY.hom)) =
        F.map cY.inv ≫ F.map (λ_ (𝟙_ Y.Modules)).inv ≫
          F.map (cY.hom ⊗ₘ cY.hom) := by
    calc
      _ = F.map cY.inv ≫
          F.map ((λ_ (𝟙_ Y.Modules)).inv ≫
            (cY.hom ⊗ₘ cY.hom)) :=
        F.map_comp cY.inv
          ((λ_ (𝟙_ Y.Modules)).inv ≫ (cY.hom ⊗ₘ cY.hom))
      _ = _ := congrArg (fun k ↦ F.map cY.inv ≫ k)
        (F.map_comp (λ_ (𝟙_ Y.Modules)).inv
          (cY.hom ⊗ₘ cY.hom))
  have hmapUnitor :
      F.map (λ_ (𝟙_ Y.Modules)).inv =
        (λ_ (F.obj (𝟙_ Y.Modules))).inv ≫
          (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules)) ≫
            Functor.LaxMonoidal.μ F (𝟙_ Y.Modules) (𝟙_ Y.Modules) :=
    Functor.Monoidal.map_leftUnitor_inv F (𝟙_ Y.Modules)
  have hmapTensor :
      F.map (cY.hom ⊗ₘ cY.hom) =
        Functor.OplaxMonoidal.δ F (𝟙_ Y.Modules) (𝟙_ Y.Modules) ≫
          (F.map cY.hom ⊗ₘ F.map cY.hom) ≫
            Functor.LaxMonoidal.μ F
              (Scheme.Modules.unitObj Y) (Scheme.Modules.unitObj Y) :=
    Functor.Monoidal.map_tensor F cY.hom cY.hom
  have hmapExpanded :
      F.map (cY.inv ≫ (λ_ (𝟙_ Y.Modules)).inv ≫
          (cY.hom ⊗ₘ cY.hom)) =
        F.map cY.inv ≫
          ((λ_ (F.obj (𝟙_ Y.Modules))).inv ≫
            (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules)) ≫
              Functor.LaxMonoidal.μ F
                (𝟙_ Y.Modules) (𝟙_ Y.Modules)) ≫
          (Functor.OplaxMonoidal.δ F
              (𝟙_ Y.Modules) (𝟙_ Y.Modules) ≫
            (F.map cY.hom ⊗ₘ F.map cY.hom) ≫
              Functor.LaxMonoidal.μ F
                (Scheme.Modules.unitObj Y)
                (Scheme.Modules.unitObj Y)) := by
    calc
      _ = F.map cY.inv ≫ F.map (λ_ (𝟙_ Y.Modules)).inv ≫
          F.map (cY.hom ⊗ₘ cY.hom) := hmap
      _ = F.map cY.inv ≫
          ((λ_ (F.obj (𝟙_ Y.Modules))).inv ≫
            (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules)) ≫
              Functor.LaxMonoidal.μ F
                (𝟙_ Y.Modules) (𝟙_ Y.Modules)) ≫
          F.map (cY.hom ⊗ₘ cY.hom) := congrArg
        (fun k ↦ F.map cY.inv ≫ k ≫ F.map (cY.hom ⊗ₘ cY.hom))
        hmapUnitor
      _ = _ := congrArg
        (fun k ↦ F.map cY.inv ≫
          ((λ_ (F.obj (𝟙_ Y.Modules))).inv ≫
            (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules)) ≫
              Functor.LaxMonoidal.μ F
                (𝟙_ Y.Modules) (𝟙_ Y.Modules)) ≫ k)
        hmapTensor
  calc
    _ = r.inv ≫
        (F.map cY.inv ≫
          ((λ_ (F.obj (𝟙_ Y.Modules))).inv ≫
            (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules)) ≫
              Functor.LaxMonoidal.μ F
                (𝟙_ Y.Modules) (𝟙_ Y.Modules)) ≫
          (Functor.OplaxMonoidal.δ F
              (𝟙_ Y.Modules) (𝟙_ Y.Modules) ≫
            (F.map cY.hom ⊗ₘ F.map cY.hom) ≫
              Functor.LaxMonoidal.μ F
                (Scheme.Modules.unitObj Y)
                (Scheme.Modules.unitObj Y))) ≫
          Functor.OplaxMonoidal.δ F
            (Scheme.Modules.unitObj Y)
            (Scheme.Modules.unitObj Y) := congrArg
      (fun k ↦ r.inv ≫ k ≫
        Functor.OplaxMonoidal.δ F
          (Scheme.Modules.unitObj Y)
          (Scheme.Modules.unitObj Y)) hmapExpanded
    _ = _ := by
      simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc,
        Functor.Monoidal.μ_δ, Category.comp_id]
      exact hcore

private theorem poleTensor_restrict_localTrivializationRestriction
    {X : Scheme.{u}} (M N : X.Modules) (U : X.affineOpens)
    (x : Γ(M, (⊤ : X.Opens))) (y : Γ(N, (⊤ : X.Opens))) :
    (restrictMonoidalTensorIso U.1.ι M N).hom.val.app (.op ⊤)
        (localTrivializationRestriction (M ⊗ N) U
          (poleTensorTopSection M N x y)) =
      poleTensorTopSection
        ((Scheme.Modules.restrictFunctor U.1.ι).obj M)
        ((Scheme.Modules.restrictFunctor U.1.ι).obj N)
        (localTrivializationRestriction M U x)
        (localTrivializationRestriction N U y) := by
  let F := Scheme.Modules.restrictFunctor U.1.ι
  letI : (Scheme.Modules.pullback U.1.ι).Monoidal :=
    Scheme.Modules.pullbackMonoidal U.1.ι
  letI : F.Monoidal := Functor.Monoidal.transport
    (Scheme.Modules.restrictFunctorIsoPullback U.1.ι).symm
  let r := Scheme.Modules.restrictUnitIso U.1.ι
  let uX := unitObjTensorIso X
  let uU := unitObjTensorIso U.1.toScheme
  let d := restrictMonoidalTensorIso U.1.ι M N
  let dUnit := restrictMonoidalTensorIso U.1.ι
    (Scheme.Modules.unitObj X) (Scheme.Modules.unitObj X)
  let hx := poleTopSectionHom M x
  let hy := poleTopSectionHom N y
  let q := poleTensorTopSection M N x y
  let xU := localTrivializationRestriction M U x
  let yU := localTrivializationRestriction N U y
  let qU := localTrivializationRestriction (M ⊗ N) U q
  let tU := poleTensorTopSection (F.obj M) (F.obj N) xU yU
  have hcomp := poleTopSectionHom_comp qU d.hom
  change poleTopSectionHom (F.obj (M ⊗ N)) qU ≫ d.hom =
    poleTopSectionHom (F.obj M ⊗ F.obj N)
      (d.hom.val.app (.op ⊤) qU) at hcomp
  have hrestrict :=
    poleTopSectionHom_localTrivializationRestriction (M ⊗ N) U q
  change poleTopSectionHom (F.obj (M ⊗ N)) qU =
    r.inv ≫ F.map (poleTopSectionHom (M ⊗ N) q) at hrestrict
  have hglobal := poleTopSectionHom_tensorTopSection M N x y
  change poleTopSectionHom (M ⊗ N) q =
    uX.inv ≫ (hx ⊗ₘ hy) at hglobal
  have hmapGlobal := congrArg F.map hglobal
  have hmapComp := F.map_comp uX.inv (hx ⊗ₘ hy)
  have hmapGlobalExpanded :
      F.map (poleTopSectionHom (M ⊗ N) q) =
        F.map uX.inv ≫ F.map (hx ⊗ₘ hy) :=
    hmapGlobal.trans hmapComp
  have hnatural := (Functor.OplaxMonoidal.δ_natural F hx hy).symm
  change F.map (hx ⊗ₘ hy) ≫ d.hom =
    dUnit.hom ≫ (F.map hx ⊗ₘ F.map hy) at hnatural
  have hunit := poleTensor_restrict_unitObjTensorIso_inv U.1.ι
  change r.inv ≫ F.map uX.inv ≫ dUnit.hom =
    uU.inv ≫ (r.inv ⊗ₘ r.inv) at hunit
  have htensor := tensorHom_comp_tensorHom
    r.inv r.inv (F.map hx) (F.map hy)
  have hrestrictX :=
    poleTopSectionHom_localTrivializationRestriction M U x
  change poleTopSectionHom (F.obj M) xU =
    r.inv ≫ F.map hx at hrestrictX
  have hrestrictY :=
    poleTopSectionHom_localTrivializationRestriction N U y
  change poleTopSectionHom (F.obj N) yU =
    r.inv ≫ F.map hy at hrestrictY
  have hlocal := poleTopSectionHom_tensorTopSection
    (F.obj M) (F.obj N) xU yU
  change poleTopSectionHom (F.obj M ⊗ F.obj N) tU =
    uU.inv ≫
      (poleTopSectionHom (F.obj M) xU ⊗ₘ
        poleTopSectionHom (F.obj N) yU) at hlocal
  have hmiddle := poleTensor_nested_four_comp_of_tail_head_last
    hnatural hunit htensor
  change (r.inv ≫
      (F.map uX.inv ≫ F.map (hx ⊗ₘ hy))) ≫ d.hom =
    uU.inv ≫
      ((r.inv ≫ F.map hx) ⊗ₘ (r.inv ≫ F.map hy)) at hmiddle
  have hhom :
      poleTopSectionHom (F.obj M ⊗ F.obj N) (d.hom.val.app (.op ⊤) qU) =
        poleTopSectionHom (F.obj M ⊗ F.obj N) tU := by
    have hchain :
        poleTopSectionHom (F.obj (M ⊗ N)) qU ≫ d.hom =
          poleTopSectionHom (F.obj M ⊗ F.obj N) tU := by
      have hstart :
          poleTopSectionHom (F.obj (M ⊗ N)) qU ≫ d.hom =
            (r.inv ≫ F.map (poleTopSectionHom (M ⊗ N) q)) ≫
              d.hom :=
        congrArg (fun k ↦ k ≫ d.hom) hrestrict
      have hglobalStep :
          (r.inv ≫ F.map (poleTopSectionHom (M ⊗ N) q)) ≫
              d.hom =
            (r.inv ≫ (F.map uX.inv ≫ F.map (hx ⊗ₘ hy))) ≫
              d.hom :=
        congrArg (fun k ↦ (r.inv ≫ k) ≫ d.hom) hmapGlobalExpanded
      have hrestricted :
          uU.inv ≫ ((r.inv ≫ F.map hx) ⊗ₘ
              (r.inv ≫ F.map hy)) =
            uU.inv ≫
              (poleTopSectionHom (F.obj M) xU ⊗ₘ
                poleTopSectionHom (F.obj N) yU) :=
        congrArg (fun k ↦ uU.inv ≫ k)
          (congrArg₂ (fun a b ↦ a ⊗ₘ b)
            hrestrictX.symm hrestrictY.symm)
      exact hstart.trans (hglobalStep.trans
        (hmiddle.trans (hrestricted.trans hlocal.symm)))
    exact hcomp.symm.trans hchain
  have happ := congrArg
    (fun k ↦ k.val.app (.op (⊤ : U.1.toScheme.Opens))
      (show U.1.toScheme.presheaf.obj (.op ⊤) from 1)) hhom
  exact (poleTopSectionHom_app_top_apply_one (F.obj M ⊗ F.obj N)
    (d.hom.val.app (.op ⊤) qU)).symm.trans
      (happ.trans (poleTopSectionHom_app_top_apply_one
        (F.obj M ⊗ F.obj N) tU))

/-- The local source coordinate of a canonical pure tensor of pole sections is
the product of the two local power coordinates. -/
theorem
    sectionPoleSheafPowerMulTrivialization_localTrivializationRestriction_tmul
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.affineOpens)
    (e : (sectionPoleSheaf π z hz).restrict U.1.ι ≅
      Scheme.Modules.unitObj U.1.toScheme) (m n : ℕ)
    (x : Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)))
    (y : Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens))) :
    (sectionPoleSheafPowerMulTrivialization z hz U.1 e m n).hom.val.app
        (.op ⊤)
        (localTrivializationRestriction
          (sectionPoleSheafPower π z hz m ⊗
            sectionPoleSheafPower π z hz n) U
          ((monoidalTensorObjIso
              (sectionPoleSheafPower π z hz m)
              (sectionPoleSheafPower π z hz n)).inv.val.app (.op ⊤)
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 C.ringCatSheaf.obj)).unit.app
                ((sectionPoleSheafPower π z hz m).val ⊗
                  (sectionPoleSheafPower π z hz n).val)).app (.op ⊤)
              (x ⊗ₜ y)))) =
      (show Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) from
        (sectionPoleSheafPowerTrivialization z hz U.1 e m).hom.val.app
          (.op ⊤)
          (localTrivializationRestriction
            (sectionPoleSheafPower π z hz m) U x)) *
        (show Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) from
          (sectionPoleSheafPowerTrivialization z hz U.1 e n).hom.val.app
            (.op ⊤)
            (localTrivializationRestriction
              (sectionPoleSheafPower π z hz n) U y)) := by
  let P := sectionPoleSheafPower π z hz m
  let Q := sectionPoleSheafPower π z hz n
  change
    (unitObjTensorIso U.1.toScheme).hom.val.app (.op ⊤)
      (((sectionPoleSheafPowerTrivialization z hz U.1 e m).hom ⊗ₘ
          (sectionPoleSheafPowerTrivialization z hz U.1 e n).hom).val.app
        (.op ⊤)
        ((restrictMonoidalTensorIso U.1.ι P Q).hom.val.app (.op ⊤)
          (localTrivializationRestriction (P ⊗ Q) U
            (poleTensorTopSection P Q x y)))) = _
  have hrestrict := poleTensor_restrict_localTrivializationRestriction
    P Q U x y
  rw [hrestrict, poleTensorTopSection_map]
  exact unitObjTensorIso_hom_poleTensorTopSection U.1.toScheme
    ((sectionPoleSheafPowerTrivialization z hz U.1 e m).hom.val.app
      (.op ⊤) (localTrivializationRestriction P U x))
    ((sectionPoleSheafPowerTrivialization z hz U.1 e n).hom.val.app
      (.op ⊤) (localTrivializationRestriction Q U y))

/-- Under the compatible tensor-power trivializations, multiplication of pole
sheaves restricts to multiplication of two copies of the structure sheaf. -/
theorem sectionPoleSheafMulHom_restrict_comp_powerTrivialization
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.Opens)
    (e : (sectionPoleSheaf π z hz).restrict U.ι ≅
      Scheme.Modules.unitObj U.toScheme) (m n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).map
          (sectionPoleSheafMulHom π z hz m n) ≫
        (sectionPoleSheafPowerTrivialization z hz U e (m + n)).hom =
      (sectionPoleSheafPowerMulTrivialization z hz U e m n).hom := by
  induction n with
  | zero =>
      let F := Scheme.Modules.restrictFunctor U.ι
      letI : (Scheme.Modules.pullback U.ι).Monoidal :=
        Scheme.Modules.pullbackMonoidal U.ι
      letI : F.Monoidal := Functor.Monoidal.transport
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
      let P := sectionPoleSheafPower π z hz m
      let eP := sectionPoleSheafPowerTrivialization z hz U e m
      let eU := monoidalUnitObjIso U.toScheme
      have hTensor :
          (restrictMonoidalTensorIso U.ι P (𝟙_ C.Modules)).hom =
            Functor.OplaxMonoidal.δ F P (𝟙_ C.Modules) := rfl
      have hUnit :
          (restrictMonoidalUnitIso U.ι).hom =
            Functor.OplaxMonoidal.η F := rfl
      have hUnitTensor :
          (eP.hom ⊗ₘ eU.hom) ≫ (unitObjTensorIso U.toScheme).hom =
            (ρ_ (F.obj P)).hom ≫ eP.hom := by
        simpa only [unitObjTensorIso, Iso.trans_hom,
          MonoidalCategory.tensorIso_hom, Iso.symm_hom] using
          tensorUnitIso_hom_naturality_left eU eP.hom
      change F.map (ρ_ P).hom ≫ eP.hom =
        (restrictMonoidalTensorIso U.ι P (𝟙_ C.Modules)).hom ≫
          (eP.hom ⊗ₘ ((restrictMonoidalUnitIso U.ι).hom ≫ eU.hom)) ≫
            (unitObjTensorIso U.toScheme).hom
      rw [hTensor, hUnit]
      rw [Functor.Monoidal.map_rightUnitor]
      calc
        _ = Functor.OplaxMonoidal.δ F P (𝟙_ C.Modules) ≫
            (F.obj P ◁ Functor.OplaxMonoidal.η F) ≫
              ((ρ_ (F.obj P)).hom ≫ eP.hom) := by
          simp only [Category.assoc]
        _ = Functor.OplaxMonoidal.δ F P (𝟙_ C.Modules) ≫
            (F.obj P ◁ Functor.OplaxMonoidal.η F) ≫
              ((eP.hom ⊗ₘ eU.hom) ≫
                (unitObjTensorIso U.toScheme).hom) := by
          exact congrArg
            (fun k => Functor.OplaxMonoidal.δ F P (𝟙_ C.Modules) ≫
              (F.obj P ◁ Functor.OplaxMonoidal.η F) ≫ k)
            hUnitTensor.symm
        _ = Functor.OplaxMonoidal.δ F P (𝟙_ C.Modules) ≫
            ((F.obj P ◁ Functor.OplaxMonoidal.η F) ≫
              (eP.hom ⊗ₘ eU.hom)) ≫
                (unitObjTensorIso U.toScheme).hom := by
          simp only [Category.assoc]
        _ = Functor.OplaxMonoidal.δ F P (𝟙_ C.Modules) ≫
            (eP.hom ⊗ₘ
              (Functor.OplaxMonoidal.η F ≫ eU.hom)) ≫
                (unitObjTensorIso U.toScheme).hom := by
          rw [← id_tensorHom]
          rw [tensorHom_comp_tensorHom]
          rw [Category.id_comp]
  | succ n hn =>
      let F := Scheme.Modules.restrictFunctor U.ι
      letI : (Scheme.Modules.pullback U.ι).Monoidal :=
        Scheme.Modules.pullbackMonoidal U.ι
      letI : F.Monoidal := Functor.Monoidal.transport
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
      have hTensor (A B : C.Modules) :
          (restrictMonoidalTensorIso U.ι A B).hom =
            Functor.OplaxMonoidal.δ
              (Scheme.Modules.restrictFunctor U.ι) A B := rfl
      have hadd : (m + n) + 1 = m + (n + 1) := by omega
      have htransport :
          F.map (eqToHom
              ((sectionPoleSheafPower_succ π z hz (m + n)).symm.trans
                (congrArg (sectionPoleSheafPower π z hz) hadd))) ≫
              (sectionPoleSheafPowerTrivialization z hz U e
                (m + (n + 1))).hom =
            (sectionPoleSheafPowerTrivialization z hz U e
              ((m + n) + 1)).hom := by
        rw [Subsingleton.elim
          ((sectionPoleSheafPower_succ π z hz (m + n)).symm.trans
            (congrArg (sectionPoleSheafPower π z hz) hadd))
          (congrArg (sectionPoleSheafPower π z hz) hadd)]
        exact sectionPoleSheafPowerTrivialization_eqToHom z hz U e hadd
      rw [sectionPoleSheafMulHom]
      simp only [sectionPoleSheafPower_succ]
      rw [Functor.map_comp, Functor.map_comp]
      simp only [Category.assoc]
      rw [htransport]
      rw [sectionPoleSheafPowerTrivialization_succ_hom]
      rw [sectionPoleSheafPowerMulTrivialization_hom]
      rw [sectionPoleSheafPowerTrivialization_succ_hom]
      rw [Functor.Monoidal.map_associator_inv]
      rw [Functor.Monoidal.map_tensor]
      rw [hTensor, hTensor, hTensor]
      simp only [sectionPoleSheafPower_succ]
      simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
      have hmapId :
          (Scheme.Modules.restrictFunctor U.ι).map
              (𝟙 (sectionPoleSheaf π z hz)) =
            𝟙 ((Scheme.Modules.restrictFunctor U.ι).obj
              (sectionPoleSheaf π z hz)) :=
        (Scheme.Modules.restrictFunctor U.ι).map_id _
      have hmulTensor :
          ((Scheme.Modules.restrictFunctor U.ι).map
                (sectionPoleSheafMulHom π z hz m n) ⊗ₘ
              (Scheme.Modules.restrictFunctor U.ι).map
                (𝟙 (sectionPoleSheaf π z hz))) ≫
              ((sectionPoleSheafPowerTrivialization z hz U e (m + n)).hom ⊗ₘ
                e.hom) =
            ((Functor.OplaxMonoidal.δ
                  (Scheme.Modules.restrictFunctor U.ι)
                  (sectionPoleSheafPower π z hz m)
                  (sectionPoleSheafPower π z hz n) ≫
                ((sectionPoleSheafPowerTrivialization z hz U e m).hom ⊗ₘ
                  (sectionPoleSheafPowerTrivialization z hz U e n).hom) ≫
                    (unitObjTensorIso U.toScheme).hom) ⊗ₘ e.hom) := by
        rw [hmapId]
        rw [tensorHom_comp_tensorHom]
        simp only [Category.id_comp]
        rw [hn]
        rw [sectionPoleSheafPowerMulTrivialization_hom]
        rw [hTensor]
      rw [← Category.assoc
        ((Scheme.Modules.restrictFunctor U.ι).map
            (sectionPoleSheafMulHom π z hz m n) ⊗ₘ
          (Scheme.Modules.restrictFunctor U.ι).map
            (𝟙 (sectionPoleSheaf π z hz)))
        ((sectionPoleSheafPowerTrivialization z hz U e (m + n)).hom ⊗ₘ
          e.hom)
        (unitObjTensorIso U.toScheme).hom]
      rw [hmulTensor]
      have hcancel :
          (Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor U.ι)
                (sectionPoleSheafPower π z hz m)
                (sectionPoleSheafPower π z hz n) ▷
              (Scheme.Modules.restrictFunctor U.ι).obj
                (sectionPoleSheaf π z hz)) ≫
              ((Functor.OplaxMonoidal.δ
                    (Scheme.Modules.restrictFunctor U.ι)
                    (sectionPoleSheafPower π z hz m)
                    (sectionPoleSheafPower π z hz n) ≫
                  ((sectionPoleSheafPowerTrivialization z hz U e m).hom ⊗ₘ
                    (sectionPoleSheafPowerTrivialization z hz U e n).hom) ≫
                      (unitObjTensorIso U.toScheme).hom) ⊗ₘ e.hom) =
            (((sectionPoleSheafPowerTrivialization z hz U e m).hom ⊗ₘ
                (sectionPoleSheafPowerTrivialization z hz U e n).hom) ≫
                  (unitObjTensorIso U.toScheme).hom) ⊗ₘ e.hom := by
        rw [← Category.id_comp e.hom]
        rw [← tensorHom_comp_tensorHom]
        simp only [tensorHom_id,
          Functor.Monoidal.whiskerRight_μ_δ_assoc]
        rw [Category.id_comp]
      rw [← Category.assoc
        (Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor U.ι)
            (sectionPoleSheafPower π z hz m)
            (sectionPoleSheafPower π z hz n) ▷
          (Scheme.Modules.restrictFunctor U.ι).obj
            (sectionPoleSheaf π z hz))
        ((Functor.OplaxMonoidal.δ (Scheme.Modules.restrictFunctor U.ι)
              (sectionPoleSheafPower π z hz m)
              (sectionPoleSheafPower π z hz n) ≫
            ((sectionPoleSheafPowerTrivialization z hz U e m).hom ⊗ₘ
              (sectionPoleSheafPowerTrivialization z hz U e n).hom) ≫
                (unitObjTensorIso U.toScheme).hom) ⊗ₘ e.hom)
        (unitObjTensorIso U.toScheme).hom]
      rw [hcancel]
      have hright :
          (sectionPoleSheafPowerTrivialization z hz U e m).hom ⊗ₘ
              (Functor.OplaxMonoidal.δ (Scheme.Modules.restrictFunctor U.ι)
                  (sectionPoleSheafPower π z hz n)
                  (sectionPoleSheaf π z hz) ≫
                ((sectionPoleSheafPowerTrivialization z hz U e n).hom ⊗ₘ
                  e.hom) ≫ (unitObjTensorIso U.toScheme).hom) =
            ((Scheme.Modules.restrictFunctor U.ι).obj
                (sectionPoleSheafPower π z hz m) ◁
              Functor.OplaxMonoidal.δ (Scheme.Modules.restrictFunctor U.ι)
                (sectionPoleSheafPower π z hz n)
                (sectionPoleSheaf π z hz)) ≫
              ((sectionPoleSheafPowerTrivialization z hz U e m).hom ⊗ₘ
                (((sectionPoleSheafPowerTrivialization z hz U e n).hom ⊗ₘ
                  e.hom) ≫ (unitObjTensorIso U.toScheme).hom)) := by
        rw [← id_tensorHom]
        rw [tensorHom_comp_tensorHom]
        rw [Category.id_comp]
      rw [hright]
      rw [tensorMulHom_assoc
        (sectionPoleSheafPowerTrivialization z hz U e m).hom
        (sectionPoleSheafPowerTrivialization z hz U e n).hom e.hom
        (unitObjTensorIso U.toScheme).hom
        (unitObjTensorIso_hom_assoc U.toScheme)]
      simp only [Category.assoc]

/-- The simple-pole sheaf along a section of a smooth separated relative curve is
invertible. -/
theorem sectionPoleSheaf_isInvertible {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) :
    Scheme.Modules.IsInvertible (sectionPoleSheaf π z hz) :=
  (sectionIdealModule_isInvertible hsm z hz).dual

/-- Every nonnegative tensor power `𝒪_C(n[0])` of the pole sheaf is invertible. -/
theorem sectionPoleSheafPower_isInvertible {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ) :
    Scheme.Modules.IsInvertible (sectionPoleSheafPower π z hz n) := by
  induction n with
  | zero =>
      exact isInvertible_of_iso Scheme.Modules.isInvertible_unit
        (monoidalUnitObjIso C)
  | succ n ih =>
      exact isInvertible_of_iso
        (ih.tensorObj (sectionPoleSheaf_isInvertible hsm z hz))
        (monoidalTensorObjIso _ _)

/-- Each successive inclusion `𝒪_C(n[0]) → 𝒪_C((n+1)[0])` is a monomorphism. -/
theorem sectionPoleSheafSuccHom_mono
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ) :
    Mono (sectionPoleSheafSuccHom π z hz n) := by
  obtain ⟨ι, U, hU, htriv⟩ :=
    sectionPoleSheafPower_isInvertible hsm z hz n
  apply sheafOfModules_mono_of_mono_over_iSup_eq_top
    (sectionPoleSheafSuccHom π z hz n) U hU
  intro i
  obtain ⟨e⟩ := htriv i
  exact sectionPoleSheafSuccHom_over_mono_of_trivialization
    hsm z hz n (U i) e

/-- Every finite composite in the pole filtration is a monomorphism. -/
theorem sectionPoleSheafAddHom_mono
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ) :
    ∀ k : ℕ, Mono (sectionPoleSheafAddHom π z hz n k)
  | 0 => by
      dsimp only [sectionPoleSheafAddHom]
      infer_instance
  | k + 1 => by
      letI : Mono (sectionPoleSheafAddHom π z hz n k) :=
        sectionPoleSheafAddHom_mono hsm z hz n k
      letI : Mono (sectionPoleSheafSuccHom π z hz (n + k)) :=
        sectionPoleSheafSuccHom_mono hsm z hz (n + k)
      dsimp only [sectionPoleSheafAddHom]
      infer_instance

/-- For `n ≤ m`, the canonical pole-filtration map
`𝒪_C(n[0]) → 𝒪_C(m[0])` is a monomorphism. -/
theorem sectionPoleSheafLEHom_mono
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    {n m : ℕ} (h : n ≤ m) :
    Mono (sectionPoleSheafLEHom π z hz h) := by
  letI : Mono (sectionPoleSheafAddHom π z hz n (m - n)) :=
    sectionPoleSheafAddHom_mono hsm z hz n (m - n)
  dsimp only [sectionPoleSheafLEHom]
  infer_instance

end ModularCurves
