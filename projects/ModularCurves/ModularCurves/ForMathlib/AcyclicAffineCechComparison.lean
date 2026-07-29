import ModularCurves.ForMathlib.SheafCechCochains
import ModularCurves.ForMathlib.SheafCechInjectiveComparison
import ModularCurves.ForMathlib.SheafCechRestrictionAcyclicComparison

/-!
# Cech comparison for affine covers

Specialize the injective-Cech comparison to quasicoherent modules on affine
open covers.
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
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) 1).obj M.sheaf := by
  apply cechHomologyOneIso_of_subsingleton_H U M.sheaf
  · simpa only [IsOpenCover] using hU
  · intro i
    simpa using restrict_subsingleton_H_of_isAffineOpen M (U i) (hUaff i) 0

/-- If global `H^(n+1)` vanishes for a quasicoherent module on a separated
scheme, its native Cech complex for a finite affine open cover is exact in
degree `n+1`. -/
theorem cechComplex_exactAt_succ_of_affine_openCover
    {X : Scheme.{u}} [X.IsSeparated] (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) (n : ℕ)
    (hM : Subsingleton (CategoryTheory.Sheaf.H M.sheaf (n + 1))) :
    ((cechComplexFunctor U).obj M.sheaf.obj).ExactAt (n + 1) := by
  apply cechComplex_exactAt_succ_of_subsingleton_restrict_H (U := U) M.sheaf
    (by simpa only [IsOpenCover] using hU)
  · intro p i q
    exact cechIntersection_subsingleton_H M U hUaff p i q
  · exact hM

end AlgebraicGeometry.Scheme.Modules
