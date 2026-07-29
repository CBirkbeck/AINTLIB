import ModularCurves.ForMathlib.AcyclicAffineCechComparison
import ModularCurves.ForMathlib.SchemeModuleBaseCechHomology
import ModularCurves.ForMathlib.SchemeModuleCechRestrict

/-!
# Cech exactness after affine open restriction

Evaluation on an affine open of the module-valued Cech complex of a finite
affine cover is exact in degree one for quasicoherent coefficients.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TopCat TopCat.Sheaf

/-- If the restriction of a cover to an open is affine and the restricted
module has vanishing `H^(n+1)`, then the evaluated module-valued Cech short
complex is exact in degree `n+1`. -/
theorem moduleCechShortComplexApp_exact_of_restrict_subsingleton_H_succ
    {X S : Scheme.{u}} [X.IsSeparated]
    (π : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (W : X.Opens)
    (hUWaff : ∀ i, IsAffineOpen (W.ι ⁻¹ᵁ U i))
    (n : ℕ)
    (hH : Subsingleton (CategoryTheory.Sheaf.H
      (M.restrict W.ι).sheaf (n + 1))) :
    (moduleCechShortComplexApp
      (baseModuleTopSheaf π M) U n W).Exact := by
  let MW := M.restrict W.ι
  let UW : ι → W.toScheme.Opens := fun i => W.ι ⁻¹ᵁ U i
  letI : W.toScheme.IsSeparated := ⟨by
    rw [← terminal.comp_from W.ι]
    infer_instance⟩
  letI : MW.IsQuasicoherent := inferInstance
  have hUW : IsOpenCover UW :=
    W.ι.iSup_preimage_eq_top hU
  have hnative :
      ((cechComplexFunctor UW).obj MW.sheaf.obj).ExactAt (n + 1) :=
    cechComplex_exactAt_succ_of_affine_openCover
      MW UW hUW hUWaff n hH
  have hbase :
      (baseCechComplex (W.ι ≫ π) MW UW).ExactAt (n + 1) :=
    (baseCechComplex_exactAt_iff
      (W.ι ≫ π) MW UW (n + 1)).2 hnative
  exact
    (moduleCechShortComplexApp_exact_iff_baseCechComplex_restrict
      π M U W n).2 hbase

/-- If the restriction of a cover to an open is affine and the restricted
module has vanishing `H¹`, then the evaluated module-valued Cech short
complex is exact. -/
theorem moduleCechShortComplexApp_exact_of_restrict_subsingleton_H
    {X S : Scheme.{u}} [X.IsSeparated]
    (π : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (W : X.Opens)
    (hUWaff : ∀ i, IsAffineOpen (W.ι ⁻¹ᵁ U i))
    (hH : Subsingleton (CategoryTheory.Sheaf.H
      (M.restrict W.ι).sheaf 1)) :
    (moduleCechShortComplexApp
      (baseModuleTopSheaf π M) U 0 W).Exact :=
  moduleCechShortComplexApp_exact_of_restrict_subsingleton_H_succ
    π M U hU W hUWaff 0 hH

/-- For a finite affine cover, every positive-degree module-valued Cech short
complex evaluated on an affine open is exact. -/
theorem moduleCechShortComplexApp_exact_of_affine_openCover_succ
    {X S : Scheme.{u}} [X.IsSeparated]
    (π : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (W : X.Opens) (hWaff : IsAffineOpen W) (n : ℕ) :
    (moduleCechShortComplexApp
      (baseModuleTopSheaf π M) U n W).Exact := by
  let MW := M.restrict W.ι
  let UW : ι → W.toScheme.Opens := fun i => W.ι ⁻¹ᵁ U i
  letI : IsAffine W.toScheme := hWaff
  letI : MW.IsQuasicoherent := inferInstance
  have hUW : IsOpenCover UW :=
    W.ι.iSup_preimage_eq_top hU
  have hUWaff : ∀ i, IsAffineOpen (UW i) := by
    intro i
    apply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion W.ι).mp
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    exact hWaff.inf (hUaff i)
  have hnative :
      ((cechComplexFunctor UW).obj MW.sheaf.obj).ExactAt (n + 1) :=
    cechComplex_exactAt_succ_of_affine_openCover
      MW UW hUW hUWaff n (affine_subsingleton_H MW n)
  have hbase :
      (baseCechComplex (W.ι ≫ π) MW UW).ExactAt (n + 1) :=
    (baseCechComplex_exactAt_iff
      (W.ι ≫ π) MW UW (n + 1)).2 hnative
  exact
    (moduleCechShortComplexApp_exact_iff_baseCechComplex_restrict
      π M U W n).2 hbase

/-- For a finite affine cover, the module-valued Cech short complex evaluated
on an affine open is exact in degree one. -/
theorem moduleCechShortComplexApp_exact_of_affine_openCover
    {X S : Scheme.{u}} [X.IsSeparated]
    (π : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (W : X.Opens) (hWaff : IsAffineOpen W) :
    (moduleCechShortComplexApp
      (baseModuleTopSheaf π M) U 0 W).Exact :=
  moduleCechShortComplexApp_exact_of_affine_openCover_succ
    π M U hU hUaff W hWaff 0

end AlgebraicGeometry.Scheme.Modules
