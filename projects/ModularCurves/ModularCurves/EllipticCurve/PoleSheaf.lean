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
import ModularCurves.ForMathlib.PullbackTensorGeneral
import ModularCurves.ForMathlib.PullbackTensorMonoidal
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

universe u

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
    MorphismProperty.pullback_snd π t inferInstance
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
    MorphismProperty.pullback_snd π t inferInstance
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
    MorphismProperty.pullback_snd π t inferInstance
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
    MorphismProperty.pullback_snd π t inferInstance
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
    MorphismProperty.pullback_snd π t inferInstance
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
        MorphismProperty.pullback_snd π t inferInstance
      letI : (Scheme.Modules.pullback (pullback.fst π t)).Monoidal :=
        Scheme.Modules.pullbackMonoidal (pullback.fst π t)
      exact (Functor.Monoidal.εIso
        (Scheme.Modules.pullback (pullback.fst π t))).symm
  | n + 1 => by
      letI : IsSeparated (pullback.snd π t) :=
        MorphismProperty.pullback_snd π t inferInstance
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
        MorphismProperty.pullback_snd π t inferInstance
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
private noncomputable def monoidalUnitObjIso (X : Scheme.{u}) :
    𝟙_ X.Modules ≅ Scheme.Modules.unitObj X :=
  Scheme.Modules.sheafifyValIso (Scheme.Modules.unitObj X)

/-- The localized coherent tensor agrees with the explicit sheafified tensor used by
the cover-local invertibility API. -/
private noncomputable def monoidalTensorObjIso {X : Scheme.{u}} (M N : X.Modules) :
    M ⊗ N ≅ Scheme.Modules.tensorObj M N :=
  ((Scheme.Modules.sheafifyValIso M).symm ⊗ᵢ
      (Scheme.Modules.sheafifyValIso N).symm) ≪≫
    Localization.Monoidal.μ
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _) M.val N.val

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

end ModularCurves
