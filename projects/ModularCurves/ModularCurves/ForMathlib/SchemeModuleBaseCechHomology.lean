import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import ModularCurves.ForMathlib.SchemeModuleBaseCech

/-!
# Homology of base-linear Cech complexes

Transport exactness through the comparison between the base-linear Cech
complex of a scheme module and the native additive Cech complex.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Exactness of the base-linear Cech complex can be checked after forgetting
to the native additive Cech complex. -/
theorem baseCechComplex_exactAt_iff
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (baseCechComplex π M U).ExactAt n ↔
      ((cechComplexFunctor U).obj M.sheaf.obj).ExactAt n := by
  constructor
  · intro h
    have hmap :
        (((baseModuleForget S).mapHomologicalComplex (.up ℕ)).obj
          (baseCechComplex π M U)).ExactAt n := by
      rw [HomologicalComplex.exactAt_iff]
      change (((baseCechComplex π M U).sc n).map
        (baseModuleForget S)).Exact
      exact (ShortComplex.exact_iff_exact_map_forget₂
        (S := (baseCechComplex π M U).sc n)).mp h
    exact hmap.of_iso (baseCechComplexForgetIso π M U)
  · intro h
    have hmap :
        (((baseModuleForget S).mapHomologicalComplex (.up ℕ)).obj
          (baseCechComplex π M U)).ExactAt n :=
      h.of_iso (baseCechComplexForgetIso π M U).symm
    rw [HomologicalComplex.exactAt_iff] at hmap ⊢
    exact (ShortComplex.exact_iff_exact_map_forget₂
      (S := (baseCechComplex π M U).sc n)).mpr hmap

/-- For a quasicoherent module on an affine open cover, degree-one exactness
of the base-linear Cech complex is equivalent to genuine `H¹` vanishing. -/
theorem baseCechComplex_exactAt_one_iff_subsingleton_H
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) :
    (baseCechComplex π M U).ExactAt 1 ↔
      Subsingleton (CategoryTheory.Sheaf.H M.sheaf 1) := by
  rw [baseCechComplex_exactAt_iff]
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let e := cechHomologyOneIso_of_affine_openCover M U hU hUaff
  constructor
  · intro h
    have h' : IsZero (AddCommGrpCat.of
        (CategoryTheory.Sheaf.H M.sheaf 1)) := IsZero.of_iso h e.symm
    simpa using AddCommGrpCat.subsingleton_of_isZero
      (G := AddCommGrpCat.of (CategoryTheory.Sheaf.H M.sheaf 1)) h'
  · intro h
    letI : Subsingleton (AddCommGrpCat.of
        (CategoryTheory.Sheaf.H M.sheaf 1)) := h
    have h' : IsZero (AddCommGrpCat.of
        (CategoryTheory.Sheaf.H M.sheaf 1)) :=
      AddCommGrpCat.isZero_of_subsingleton _
    exact IsZero.of_iso h' e

end

end AlgebraicGeometry.Scheme.Modules
