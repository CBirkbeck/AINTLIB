/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# Base-linear Cech complexes of scheme modules

This file retains the module structure over the global functions on the base
in the native Cech complex of a scheme module.
-/

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite
  TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Sections of a scheme module, regarded functorially as modules over the
global functions on the base. -/
noncomputable def baseModulePresheaf {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) :
    X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(S, (⊤ : S.Opens)) :=
  (PresheafOfModules.forgetToPresheafModuleCat
      (op (⊤ : X.Opens)) (initialOpOfTerminal isTerminalTop)).obj M.1 ⋙
    ModuleCat.restrictScalars π.appTop.hom

@[simp]
theorem baseModulePresheaf_obj_coe {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) (V : X.Opensᵒᵖ) :
    ((baseModulePresheaf π M).obj V : Type u) = M.presheaf.obj V :=
  rfl

@[simp]
theorem baseModulePresheaf_map_apply {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {V W : X.Opensᵒᵖ} (f : V ⟶ W)
    (x : M.presheaf.obj V) :
    ((baseModulePresheaf π M).map f).hom x = M.presheaf.map f x :=
  rfl

/-- The Cech complex of a scheme module, retaining its module structure over
the global functions on the base. -/
noncomputable def baseCechComplex {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) ℕ :=
  (cechComplexFunctor U).obj (baseModulePresheaf π M)

end

end AlgebraicGeometry.Scheme.Modules
