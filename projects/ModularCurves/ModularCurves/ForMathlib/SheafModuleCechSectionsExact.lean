/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SheafCechSheafResolution
import ModularCurves.ForMathlib.SheafModuleCechSectionsDifferential
import ModularCurves.ForMathlib.SheafModuleCechTopExact

/-!
# Exactness of evaluated module-valued sheaf Cech complexes

After forgetting coefficients, the concrete section comparison identifies
the evaluated module-valued Cech augmentation and differential with their
additive counterparts. The sheaf condition therefore gives exactness in
degree zero and monicity of the evaluated augmentation.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable (F : Sheaf (ModuleCat.{u} R) X)
variable {ι : Type u} (U : ι → Opens X)

attribute [local instance] moduleCechSheafPreadditive

/-- The module-valued Cech augmentation restricts a section to every member
of the open family. -/
theorem moduleCechAugmentation_apply
    (W : Opens X) (x : F.obj.obj (op W))
    (i : Fin 1 → ι) :
    moduleCechTermSectionsLinearEquiv F U 0 W
        ((moduleCechAugmentation F U).hom.app (op W) x) i =
      F.obj.map (homOfLE (inf_le_left :
        (W ⊓ (∏ᶜ fun k : Fin 1 => U (i k))) ≤ W)).op x := by
  rw [moduleCechTermSectionsLinearEquiv_apply]
  have hcomponent :
      (Pi.π (moduleCechTermFactor F U 0) i).hom.app (op W)
          ((moduleCechAugmentation F U).hom.app (op W) x) =
        ((toRestrict (ModuleCat R)
          (∏ᶜ fun k : Fin 1 => U (i k))).app F).hom.app (op W) x := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.hom.app (op W))
        (Pi.lift_π (fun i : Fin 1 → ι =>
          (toRestrict (ModuleCat R)
            (∏ᶜ fun k : Fin 1 => U (i k))).app F) i)) x
  rw [hcomponent]
  change (F.obj.map _ ≫ F.obj.map _) x = F.obj.map _ x
  rw [← F.obj.map_comp]
  exact ConcreteCategory.congr_hom
    (congrArg F.obj.map (Subsingleton.elim _ _)) x

/-- Forgetting coefficients identifies sections of a native module-valued
Cech term with sections of the corresponding additive Cech term. -/
noncomputable def moduleCechTermSectionsAddEquiv
    (n : ℕ) (W : Opens X) :
    (moduleCechTerm F U n).obj.obj (op W) ≃+
      (cechTerm (moduleForgetSheaf F) U n).obj.obj (op W) :=
  (moduleCechTermSectionsLinearEquiv F U n W).toAddEquiv.trans
    (cechTermSectionsAddEquiv (moduleForgetSheaf F) U n W).symm

/-- The forgotten section comparison has the same tuple coordinates as the
linear section comparison. -/
theorem moduleCechTermSectionsAddEquiv_apply
    (n : ℕ) (W : Opens X)
    (x : (moduleCechTerm F U n).obj.obj (op W)) :
    cechTermSectionsAddEquiv (moduleForgetSheaf F) U n W
        (moduleCechTermSectionsAddEquiv F U n W x) =
      moduleCechTermSectionsLinearEquiv F U n W x := by
  exact (cechTermSectionsAddEquiv
    (moduleForgetSheaf F) U n W).apply_symm_apply _

/-- The forgotten section comparison commutes with the Cech augmentation. -/
theorem moduleCechTermSectionsAddEquiv_augmentation
    (W : Opens X) (x : F.obj.obj (op W)) :
    moduleCechTermSectionsAddEquiv F U 0 W
        ((moduleCechAugmentation F U).hom.app (op W) x) =
      (cechAugmentation (moduleForgetSheaf F) U).hom.app (op W) x := by
  apply (cechTermSectionsAddEquiv
    (moduleForgetSheaf F) U 0 W).injective
  funext i
  rw [cechAugmentation_apply (moduleForgetSheaf F) U W x i,
    moduleCechTermSectionsAddEquiv_apply,
    moduleCechAugmentation_apply]
  exact ConcreteCategory.congr_hom
    (congrArg F.obj.map (Subsingleton.elim _ _)) x

/-- The forgotten section comparison commutes with every Cech differential. -/
theorem moduleCechTermSectionsAddEquiv_differential
    (n : ℕ) (W : Opens X)
    (y : (moduleCechTerm F U n).obj.obj (op W)) :
    moduleCechTermSectionsAddEquiv F U (n + 1) W
        ((moduleCechDifferential F U n).hom.app (op W) y) =
      (cechDifferential (moduleForgetSheaf F) U n).hom.app (op W)
        (moduleCechTermSectionsAddEquiv F U n W y) := by
  apply (cechTermSectionsAddEquiv
    (moduleForgetSheaf F) U (n + 1) W).injective
  funext i
  rw [moduleCechTermSectionsAddEquiv_apply,
    cechDifferential_apply, moduleCechTermSectionsAddEquiv_apply,
    moduleCechDifferential_apply]
  apply Finset.sum_congr rfl
  intro k hk
  exact congrArg (fun z => (-1 : ℤ) ^ (k : ℕ) • z)
    (ConcreteCategory.congr_hom
      (congrArg F.obj.map (Subsingleton.elim _ _))
      (moduleCechTermSectionsLinearEquiv F U n W y
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)))

/-- The augmentation and first differential of the module-valued Cech
complex, evaluated on an arbitrary open. -/
noncomputable def moduleCechAugmentedShortComplexApp (W : Opens X) :
    ShortComplex (ModuleCat.{u} R) := by
  let f := (moduleCechAugmentation F U).hom.app (op W)
  let g := (moduleCechDifferential F U 0).hom.app (op W)
  refine ShortComplex.mk f g ?_
  exact congrArg (fun k => k.hom.app (op W))
    (moduleCechAugmentation_comp F U)

/-- The evaluated module-valued augmented Cech complex is exact in degree
zero for an open cover. -/
theorem moduleCechAugmentedShortComplexApp_exact
    (W : Opens X) (hU : ⨆ i, U i = ⊤) :
    (moduleCechAugmentedShortComplexApp F U W).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  change (moduleCechDifferential F U 0).hom.app (op W) y = 0 at hy
  have hy' :
      (cechDifferential (moduleForgetSheaf F) U 0).hom.app (op W)
          (moduleCechTermSectionsAddEquiv F U 0 W y) = 0 := by
    calc
      _ = moduleCechTermSectionsAddEquiv F U 1 W
          ((moduleCechDifferential F U 0).hom.app (op W) y) :=
        (moduleCechTermSectionsAddEquiv_differential F U 0 W y).symm
      _ = moduleCechTermSectionsAddEquiv F U 1 W 0 :=
        congrArg (moduleCechTermSectionsAddEquiv F U 1 W) hy
      _ = 0 := map_zero _
  obtain ⟨x, hx⟩ := TopCat.Sheaf.sections_exact_of_left_exact
    (U := W)
    (cechAugmentedShortComplex_exact (moduleForgetSheaf F) U hU)
    (cechAugmentation_mono (moduleForgetSheaf F) U hU)
    (moduleCechTermSectionsAddEquiv F U 0 W y) hy'
  refine ⟨x, (moduleCechTermSectionsAddEquiv F U 0 W).injective ?_⟩
  change moduleCechTermSectionsAddEquiv F U 0 W
      ((moduleCechAugmentation F U).hom.app (op W) x) =
    moduleCechTermSectionsAddEquiv F U 0 W y
  exact (moduleCechTermSectionsAddEquiv_augmentation F U W x).trans hx

/-- The evaluated module-valued Cech augmentation is monic for an open
cover. -/
theorem moduleCechAugmentation_app_mono
    (W : Opens X) (hU : ⨆ i, U i = ⊤) :
    Mono ((moduleCechAugmentation F U).hom.app (op W)) := by
  rw [ModuleCat.mono_iff_injective]
  intro x y hxy
  have hadd :
      (cechAugmentation (moduleForgetSheaf F) U).hom.app (op W) x =
        (cechAugmentation (moduleForgetSheaf F) U).hom.app (op W) y := by
    rw [← moduleCechTermSectionsAddEquiv_augmentation,
      ← moduleCechTermSectionsAddEquiv_augmentation]
    exact congrArg (moduleCechTermSectionsAddEquiv F U 0 W) hxy
  haveI : Mono (cechAugmentation (moduleForgetSheaf F) U) :=
    cechAugmentation_mono (moduleForgetSheaf F) U hU
  haveI : Mono (cechAugmentation (moduleForgetSheaf F) U).hom := by
    change Mono ((TopCat.Sheaf.forget AddCommGrpCat X).map
      (cechAugmentation (moduleForgetSheaf F) U))
    infer_instance
  haveI : Mono
      ((cechAugmentation (moduleForgetSheaf F) U).hom.app (op W)) := by
    infer_instance
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance hadd

end TopCat.Sheaf
