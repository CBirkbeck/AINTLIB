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

/-- Base-linear sections on an ambient open are naturally identified with
top sections of the module restricted to that open. -/
noncomputable def baseModulePresheafRestrictIso
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) (U : X.Opens) :
    (baseModulePresheaf f M).obj (op U) ≅
      (ModuleCat.restrictScalars (U.ι ≫ f).appTop.hom).obj
        (ModuleCat.of Γ(U.toScheme, (⊤ : U.toScheme.Opens))
          Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens))) := by
  let eAdd := M.presheaf.mapIso (eqToIso U.ι_image_top).op ≪≫
    (M.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).symm
  refine ModuleCat.isoMk eAdd ?_
  intro r
  ext (x : Γ(M, U))
  change
    (U.ι ≫ f).appTop.hom r •
        (M.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).inv
          (M.presheaf.map (eqToHom U.ι_image_top).op x) =
      (M.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).inv
        (M.presheaf.map (eqToHom U.ι_image_top).op
          (((X.presheaf.map
            ((initialOpOfTerminal isTerminalTop).to (op U))).hom
              (f.appTop.hom r)) • x))
  rw [M.map_smul]
  rw [smul_restrictAppIso_inv_apply]
  congr 1
  rw [Scheme.Hom.comp_appTop]
  have hr : (U.ι.appIso (⊤ : U.toScheme.Opens)).hom
      (X.presheaf.map (eqToHom U.ι_image_top).op
        ((X.presheaf.map
          ((initialOpOfTerminal isTerminalTop).to (op U))).hom
            (f.appTop.hom r))) =
      U.topIso.inv
        ((X.presheaf.map
          ((initialOpOfTerminal isTerminalTop).to (op U))).hom
            (f.appTop.hom r)) := by
    rw [Scheme.Opens.topIso_inv]
    rw [Scheme.Opens.ι_appIso]
    rfl
  rw [hr]
  rw [Scheme.Opens.topIso_inv]
  rw [Scheme.Opens.ι_appTop]
  have hmap :
      X.presheaf.map
          (homOfLE (x := U.ι ''ᵁ (⊤ : U.toScheme.Opens)) le_top).op =
        X.presheaf.map
            ((initialOpOfTerminal isTerminalTop).to (op U)) ≫
          X.presheaf.map (eqToHom U.ι_image_top).op := by
    rw [← Functor.map_comp]
    congr
  rw [hmap]
  rfl

/-- The Cech complex of a scheme module, retaining its module structure over
the global functions on the base. -/
noncomputable def baseCechComplex {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) ℕ :=
  (cechComplexFunctor U).obj (baseModulePresheaf π M)

end

end AlgebraicGeometry.Scheme.Modules
