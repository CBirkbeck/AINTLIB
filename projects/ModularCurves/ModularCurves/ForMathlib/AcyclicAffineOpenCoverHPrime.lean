import ModularCurves.ForMathlib.AcyclicAffineOpenCover
import ModularCurves.ForMathlib.SheafCohomologyOpen
import ModularCurves.ForMathlib.SheafCohomologyMayerVietoris

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

/-- A quasicoherent module on a separated scheme covered by two affine opens has
vanishing cohomology in every degree at least two. -/
theorem subsingleton_H_add_two_of_two_affine_open_cover
    {X : Scheme.{u}} [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Subsingleton (H M.sheaf (n + 2)) := by
  have hIntersection : Subsingleton
      ((toSiteSheaf M.sheaf).H' (n + 1) (U ⊓ V)) :=
    restrict_subsingleton_HPrime_of_isAffineOpen M (U ⊓ V) (hU.inf hV) n
  have hU' : Subsingleton ((toSiteSheaf M.sheaf).H' (n + 2) U) := by
    simpa [Nat.add_assoc] using
      restrict_subsingleton_HPrime_of_isAffineOpen M U hU (n + 1)
  have hV' : Subsingleton ((toSiteSheaf M.sheaf).H' (n + 2) V) := by
    simpa [Nat.add_assoc] using
      restrict_subsingleton_HPrime_of_isAffineOpen M V hV (n + 1)
  simpa [Nat.add_assoc] using
    subsingleton_H_succ_of_mayerVietoris M.sheaf U V hUV (n + 1)
      hIntersection hU' hV'

end AlgebraicGeometry.Scheme.Modules
