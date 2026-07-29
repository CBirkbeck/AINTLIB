/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.CategoryTheory.Sites.Limits
import ModularCurves.ForMathlib.SheafModuleCechTopExact

/-!
# Forgetting coefficients in sheaf-level Cech terms

Forgetting the module structure in a module-valued sheaf Cech term gives
the corresponding additive sheaf Cech term.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}

private abbrev moduleSheafForget :
    Sheaf (ModuleCat.{u} R) X ⥤ Sheaf AddCommGrpCat.{u} X :=
  sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

private theorem moduleSheafForget_preservesProduct (I : Type u) :
    PreservesLimitsOfShape (Discrete I)
      (moduleSheafForget (R := R) (X := X)) := by
  let G :=
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  have hcomp : PreservesLimitsOfShape (Discrete I)
      (moduleSheafForget (R := R) (X := X) ⋙ G) := by
    change PreservesLimitsOfShape (Discrete I)
      (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⋙
        (Functor.whiskeringRight _ _ _).obj
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))
    exact comp_preservesLimitsOfShape _ _
  have hreflect : ReflectsLimitsOfShape (Discrete I) G :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact @preservesLimitsOfShape_of_reflects_of_preserves
    _ _ _ _ _ _ _ _
    (moduleSheafForget (R := R) (X := X)) G hcomp hreflect

private noncomputable def moduleCechTermForgetDiagramIso
    (F : Sheaf (ModuleCat.{u} R) X)
    {ι : Type u} (U : ι → Opens X) (n : ℕ) :
    Discrete.functor (moduleCechTermFactor F U n) ⋙
        moduleSheafForget (R := R) (X := X) ≅
      Discrete.functor
        (cechTermFactor (moduleForgetSheaf F) U n) :=
  Discrete.natIso fun _ => Iso.refl _

/-- Forgetting the module structure in a module-valued sheaf Cech term gives
the corresponding additive sheaf Cech term. -/
noncomputable def moduleCechTermForgetIso
    (F : Sheaf (ModuleCat.{u} R) X)
    {ι : Type u} (U : ι → Opens X) (n : ℕ) :
    moduleForgetSheaf (moduleCechTerm F U n) ≅
      cechTerm (moduleForgetSheaf F) U n := by
  letI := moduleSheafForget_preservesProduct
    (R := R) (X := X) (Fin (n + 1) → ι)
  exact preservesLimitIso (moduleSheafForget (R := R) (X := X))
      (Discrete.functor (moduleCechTermFactor F U n)) ≪≫
    HasLimit.isoOfNatIso (moduleCechTermForgetDiagramIso F U n)

end TopCat.Sheaf
