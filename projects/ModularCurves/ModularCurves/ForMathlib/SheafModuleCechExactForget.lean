/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import ModularCurves.ForMathlib.SheafModuleCechTopExact

/-!
# Exactness after forgetting Cech-complex coefficients

Exactness of a module-valued Cech complex can be checked after forgetting
the module structure.
-/

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}

/-- A native module-valued Cech complex is exact in a degree exactly when
the native additive Cech complex of the forgotten sheaf is exact there. -/
theorem moduleCechComplex_exactAt_iff_forget
    (F : Sheaf (ModuleCat.{u} R) X) {ι : Type u} (U : ι → Opens X) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).ExactAt n ↔
      ((cechComplexFunctor U).obj (moduleForgetSheaf F).obj).ExactAt n := by
  constructor
  · intro h
    have hmap :
        (((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
          (.up ℕ)).obj ((cechComplexFunctor U).obj F.obj)).ExactAt n := by
      rw [HomologicalComplex.exactAt_iff]
      change ((((cechComplexFunctor U).obj F.obj).sc n).map
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).Exact
      exact (ShortComplex.exact_iff_exact_map_forget₂
        (S := ((cechComplexFunctor U).obj F.obj).sc n)).mp h
    exact hmap.of_iso (moduleCechComplexForgetIso F U)
  · intro h
    have hmap :
        (((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
          (.up ℕ)).obj ((cechComplexFunctor U).obj F.obj)).ExactAt n :=
      h.of_iso (moduleCechComplexForgetIso F U).symm
    rw [HomologicalComplex.exactAt_iff] at hmap ⊢
    exact (ShortComplex.exact_iff_exact_map_forget₂
      (S := ((cechComplexFunctor U).obj F.obj).sc n)).mpr hmap

end TopCat.Sheaf
