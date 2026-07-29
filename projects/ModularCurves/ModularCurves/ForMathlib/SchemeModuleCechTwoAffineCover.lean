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
every positive degree on a finite affine open cover. -/
theorem baseModuleCechTerm_cech_exactAt_succ_of_affine_openCover
    {X S : Scheme.{u}} [X.IsSeparated]
    (π : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent]
    {ι κ : Type u} [Finite κ]
    (U : ι → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i))
    (V : κ → X.Opens) (hV : IsOpenCover V)
    (hVaff : ∀ i, IsAffineOpen (V i)) (q n : ℕ) :
    ((cechComplexFunctor V).obj
      (moduleCechTerm
        (baseModuleTopSheaf π M) U q).obj).ExactAt (n + 1) := by
  apply moduleCechTerm_cech_exactAt_succ_of_factors
  intro i
  apply moduleCechFixedFactorNative_exactAt_succ_of_app_exact
  exact moduleCechShortComplexApp_exact_of_affine_openCover_succ
    π M V hV hVaff
    (∏ᶜ fun k : Fin (q + 1) => U (i k))
    (IsAffineOpen.cechIntersection U hUaff q i) n

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
      (moduleCechTerm
        (baseModuleTopSheaf π M) U q).obj).ExactAt 1 := by
  simpa using
    baseModuleCechTerm_cech_exactAt_succ_of_affine_openCover
      π M U hUaff V hV hVaff q 0

/-- Finite generation of native Cech cohomology in every positive degree
transfers between finite affine open covers. -/
theorem baseModuleCech_homology_succ_module_finite_of_affine_openCovers
    {X S : Scheme.{u}} [X.IsSeparated]
    (π : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent]
    {ι κ : Type u} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (V : κ → X.Opens) (hV : IsOpenCover V)
    (hVaff : ∀ i, IsAffineOpen (V i))
    (n : ℕ)
    [Module.Finite Γ(S, (⊤ : S.Opens))
      (((cechComplexFunctor U).obj
        (baseModuleTopSheaf π M).obj).homology (n + 1))] :
    Module.Finite Γ(S, (⊤ : S.Opens))
      (((cechComplexFunctor V).obj
        (baseModuleTopSheaf π M).obj).homology (n + 1)) := by
  apply Module.Finite.equiv
    (moduleCechTwoCoverHomologySuccIso
      (baseModuleTopSheaf π M) U V hU hV n
        (fun q p _ hp => by
          cases p with
          | zero => omega
          | succ p =>
              simpa only [Nat.succ_eq_add_one] using
                baseModuleCechTerm_cech_exactAt_succ_of_affine_openCover
                  π M U hUaff V hV hVaff q p)
        (fun q p _ hp => by
          cases p with
          | zero => omega
          | succ p =>
              simpa only [Nat.succ_eq_add_one] using
                baseModuleCechTerm_cech_exactAt_succ_of_affine_openCover
                  π M U hUaff V hV hVaff q p)
        (fun p q _ _ i =>
          moduleCechShortComplexApp_exact_of_affine_openCover_succ
            π M U hU hUaff
            (∏ᶜ fun k : Fin (p + 1) => V (i k))
            (IsAffineOpen.cechIntersection V hVaff p i) (q - 1))
        (fun p q _ _ i =>
          moduleCechShortComplexApp_exact_of_affine_openCover_succ
            π M U hU hUaff
            (∏ᶜ fun k : Fin (p + 1) => V (i k))
            (IsAffineOpen.cechIntersection V hVaff p i)
            (q - 1))).symm.toLinearEquiv

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
  simpa using
    baseModuleCech_homology_succ_module_finite_of_affine_openCovers
      π M U hU hUaff V hV hVaff 0

end AlgebraicGeometry.Scheme.Modules
