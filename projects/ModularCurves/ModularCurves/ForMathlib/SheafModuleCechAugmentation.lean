/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SheafModuleCechComplex

/-!
# Augmentation of module-valued sheaf Cech complexes

This file defines the canonical augmentation from a module-valued sheaf to its
sheaf-level Cech complex. The construction retains the coefficient-ring action.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable (F : Sheaf (ModuleCat.{u} R) X)
variable {ι : Type u} (U : ι → Opens X)

attribute [local instance] moduleCechSheafPreadditive

/-- The canonical augmentation from a module-valued sheaf to the degree-zero
term of its sheaf Cech complex. -/
noncomputable def moduleCechAugmentation :
    F ⟶ moduleCechTerm F U 0 :=
  Pi.lift fun i : Fin 1 → ι =>
    (toRestrict (ModuleCat R) (∏ᶜ fun k : Fin 1 => U (i k))).app F

private theorem moduleCechAugmentation_comp_coface_eq :
    moduleCechAugmentation F U ≫ moduleCechCoface F U 0 0 =
      moduleCechAugmentation F U ≫ moduleCechCoface F U 0 1 := by
  unfold moduleCechAugmentation moduleCechCoface moduleCechTerm
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, Pi.lift_π]
  rw [Category.assoc, Pi.lift_π]
  rw [← Category.assoc, Pi.lift_π]
  rw [← Category.assoc, Pi.lift_π]
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

/-- The module-valued Cech augmentation followed by the first differential is
zero. -/
theorem moduleCechAugmentation_comp :
    moduleCechAugmentation F U ≫ moduleCechDifferential F U 0 = 0 := by
  rw [moduleCechDifferential, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_zsmul, neg_one_zsmul]
  rw [Preadditive.comp_add, Preadditive.comp_neg,
    moduleCechAugmentation_comp_coface_eq F U]
  simp

/-- The augmentation and first differential of the module-valued sheaf Cech
complex. -/
noncomputable def moduleCechAugmentedShortComplex :
    ShortComplex (Sheaf (ModuleCat.{u} R) X) :=
  ShortComplex.mk (moduleCechAugmentation F U)
    (moduleCechDifferential F U 0)
    (moduleCechAugmentation_comp F U)

end TopCat.Sheaf
