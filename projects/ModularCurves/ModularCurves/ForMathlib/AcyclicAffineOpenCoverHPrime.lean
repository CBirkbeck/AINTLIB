import ModularCurves.ForMathlib.AcyclicAffineOpenCover
import ModularCurves.ForMathlib.SheafCohomologyOpen

/-!
# Cohomology-presheaf vanishing on affine opens

This file transfers ordinary affine-open vanishing for quasicoherent modules to the
cohomology-presheaf values used by the Mayer--Vietoris sequence.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TopCat TopCat.Sheaf

/-- A quasicoherent module has vanishing positive-degree cohomology-presheaf values
on an affine open. -/
theorem restrict_subsingleton_HPrime_of_isAffineOpen
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    Subsingleton ((toSiteSheaf M.sheaf).H' (n + 1) U) := by
  letI : Subsingleton (H
      ((TopCat.Sheaf.restrict AddCommGrpCat U.isOpenEmbedding).obj M.sheaf) (n + 1)) :=
    restrict_subsingleton_H_of_isAffineOpen M U hU n
  exact subsingleton_HPrime_succ_of_subsingleton_restrict_H M.sheaf U n

end AlgebraicGeometry.Scheme.Modules
