import ModularCurves.ForMathlib.SheafCechInjectiveComparison

/-!
# Cech comparison for affine covers

Specialize the degree-one injective-Cech comparison to quasicoherent modules on
affine open covers.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TopCat TopCat.Sheaf

/-- The native Cech complex of a quasicoherent module on an affine open cover
computes its genuine degree-one sheaf cohomology. -/
noncomputable def cechHomologyOneIso_of_affine_openCover
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    ((cechComplexFunctor U).obj M.sheaf.obj).homology 1 ≅
      AddCommGrpCat.of (CategoryTheory.Sheaf.H M.sheaf 1) := by
  apply cechHomologyOneIso_of_subsingleton_H U M.sheaf
  · simpa only [IsOpenCover] using hU
  · intro i
    simpa using restrict_subsingleton_H_of_isAffineOpen M (U i) (hUaff i) 0

end AlgebraicGeometry.Scheme.Modules
