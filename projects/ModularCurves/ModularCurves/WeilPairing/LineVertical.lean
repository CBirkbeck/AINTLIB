/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.IdealModule

/-!
# The line and the vertical as rank-one kernels ([GAP-A-4])

The chord-and-tangent sections of the Weil-pairing construction (GME 2.6.4 Chain C):
the line `ℓ` through `[P] + [Q]` inside `H⁰(𝒪(3[0]))` and the vertical `v` through
`[R]` inside `H⁰(𝒪(2[0]))`, each cut out as the kernel of the global-sections
restriction to the divisor, each of rank one — the generator-up-to-unit that produces
the norm `N`.

This file starts with the ambient-module inclusion of an ideal module
(`idealModuleInclusion`), the mono that seeds every restriction cokernel downstream.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {C : Scheme.{u}} (J : C.IdealSheafData)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of the ideal module of `J` into the structure sheaf: componentwise
the subtype inclusion of `idealSections`. -/
noncomputable def idealModuleInclusion : idealModule J ⟶ unitObj C where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun m => (m.1 : Γ(C, U.unop))
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      naturality := fun {U V} i => by
        refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
        rfl }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem idealModuleInclusion_app_apply (U : (TopologicalSpace.Opens ↥C)ᵒᵖ)
    (m : idealSections J U) :
    (idealModuleInclusion J).val.app U m = (m.1 : Γ(C, U.unop)) :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : Mono (idealModuleInclusion J) := by
  constructor
  intro Z g h hgh
  ext U m
  have hval := congrArg (fun (q : Z ⟶ unitObj C) => q.val.app (op U) m) hgh
  have hg : (idealModuleInclusion J).val.app (op U) (g.val.app (op U) m) =
      (idealModuleInclusion J).val.app (op U) (h.val.app (op U) m) := hval
  exact Subtype.ext hg

section Twist

variable (L : C.Modules)

local instance (C : Scheme.{u}) :
    ∀ U, IsMulCommutative (C.ringCatSheaf.obj.obj U) :=
  fun U => by
    change IsMulCommutative (C.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b => mul_comm a b

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The presheaf-level action of the ideal module on any module — the whiskered
subtype inclusion followed by the left unitor. All naturality is the monoidal
structure's. -/
noncomputable def idealActionPre :
    ((idealModule J).val ⊗ L.val :
      _root_.PresheafOfModules (C.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ⟶
      L.val :=
  MonoidalCategory.whiskerRight (idealModuleInclusion J).val L.val ≫
    (λ_ L.val).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The divisor twist map**: the sheafified action `I(J) ⊗ L ⟶ L`, the mono whose
cokernel is the restriction of `L` to the subscheme of `J`. Transpose of
`idealActionPre` through the sheafification adjunction (the `ev` idiom). -/
noncomputable def divisorTwistHom : tensorObj (idealModule J) L ⟶ L :=
  (PresheafOfModules.sheafificationAdjunction
    (CategoryStruct.id C.ringCatSheaf.obj)).homEquiv
      ((idealModule J).val ⊗ L.val) L |>.symm (idealActionPre J L)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem idealActionPre_app_tmul (U : (TopologicalSpace.Opens ↥C)ᵒᵖ)
    (m : idealSections J U) (l : L.val.obj U) :
    (idealActionPre J L).app U
        (m ⊗ₜ[(C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U] l) =
      (show ((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U) from m.1) • l :=
  rfl

end Twist

end AlgebraicGeometry.Scheme.Modules
