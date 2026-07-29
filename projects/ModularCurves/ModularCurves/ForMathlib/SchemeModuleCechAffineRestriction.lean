import ModularCurves.ForMathlib.AcyclicAffineCechComparison
import ModularCurves.ForMathlib.SchemeModuleBaseCechHomology
import ModularCurves.ForMathlib.SchemeModuleCechRestrict

/-!
# Cech exactness after affine open restriction

Evaluation on an affine open of the module-valued Cech complex of a finite
affine cover is exact in degree one for quasicoherent coefficients.
-/

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TopCat TopCat.Sheaf

/-- For a finite affine cover, the module-valued Cech short complex evaluated
on an affine open is exact in degree one. -/
theorem moduleCechShortComplexApp_exact_of_affine_openCover
    {X S : Scheme.{u}} [X.IsSeparated]
    (π : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (W : X.Opens) (hWaff : IsAffineOpen W) :
    (moduleCechShortComplexApp (baseModuleTopSheaf π M) U 0 W).Exact := by
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
      ((cechComplexFunctor UW).obj MW.sheaf.obj).ExactAt 1 :=
    cechComplex_exactAt_succ_of_affine_openCover
      MW UW hUW hUWaff 0 (affine_subsingleton_H MW 0)
  have hbase :
      (baseCechComplex (W.ι ≫ π) MW UW).ExactAt 1 :=
    (baseCechComplex_exactAt_iff (W.ι ≫ π) MW UW 1).2 hnative
  exact
    (moduleCechShortComplexApp_exact_iff_baseCechComplex_restrict
      π M U W 0).2 hbase

end AlgebraicGeometry.Scheme.Modules
