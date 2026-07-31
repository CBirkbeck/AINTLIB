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

open CategoryTheory AlgebraicGeometry Opposite

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

end AlgebraicGeometry.Scheme.Modules
