/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SheafModuleCechFixedFactorSections
import ModularCurves.ForMathlib.SchemeModuleCechAffineRestriction
import ModularCurves.ForMathlib.SheafModuleCechTwoCoverHomology

/-!
# Degree-one Cech comparison for finite affine covers

For quasicoherent coefficients on a separated scheme, the row and column
exactness assumptions in the two-cover comparison hold for finite affine
open covers. Consequently, finite generation of native Cech cohomology in
degree one transfers between any two such covers.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TopCat TopCat.Sheaf

/-- The module-valued Cech complex of a sheaf-level Cech term is exact in
degree one on a finite affine open cover. -/
theorem baseModuleCechTerm_cech_exactAt_one_of_affine_openCover
    {X S : Scheme.{u}} [X.IsSeparated]
    (π : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent]
    {ι κ : Type u} [Finite κ]
    (U : ι → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i))
    (V : κ → X.Opens) (hV : IsOpenCover V)
    (hVaff : ∀ i, IsAffineOpen (V i)) (q : ℕ) :
    ((cechComplexFunctor V).obj
      (moduleCechTerm (baseModuleTopSheaf π M) U q).obj).ExactAt 1 := by
  apply moduleCechTerm_cech_exactAt_one_of_factors
  intro i
  apply moduleCechFixedFactorNative_exactAt_one_of_app_exact
  exact moduleCechShortComplexApp_exact_of_affine_openCover
    π M V hV hVaff
    (∏ᶜ fun k : Fin (q + 1) => U (i k))
    (IsAffineOpen.cechIntersection U hUaff q i)

/-- Finite generation of native Cech cohomology in degree one transfers
between finite affine open covers. -/
theorem baseModuleCech_homology_one_module_finite_of_affine_openCovers
    {X S : Scheme.{u}} [X.IsSeparated]
    (π : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent]
    {ι κ : Type u} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (V : κ → X.Opens) (hV : IsOpenCover V)
    (hVaff : ∀ i, IsAffineOpen (V i))
    [Module.Finite Γ(S, (⊤ : S.Opens))
      (((cechComplexFunctor U).obj
        (baseModuleTopSheaf π M).obj).homology 1)] :
    Module.Finite Γ(S, (⊤ : S.Opens))
      (((cechComplexFunctor V).obj
        (baseModuleTopSheaf π M).obj).homology 1) := by
  apply moduleCechTwoCover_homology_one_module_finite
    (baseModuleTopSheaf π M) U V hU hV
  · exact baseModuleCechTerm_cech_exactAt_one_of_affine_openCover
      π M U hUaff V hV hVaff 0
  · intro i
    exact moduleCechShortComplexApp_exact_of_affine_openCover
      π M U hU hUaff
      (∏ᶜ fun k : Fin 1 => V (i k))
      (IsAffineOpen.cechIntersection V hVaff 0 i)

end AlgebraicGeometry.Scheme.Modules
