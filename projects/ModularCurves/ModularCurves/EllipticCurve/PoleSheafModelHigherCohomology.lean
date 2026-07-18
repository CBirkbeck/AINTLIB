import ModularCurves.EllipticCurve.PoleSheafModelHOne
import ModularCurves.ForMathlib.AcyclicAffineOpenCoverHPrime

/-!
# Higher cohomology of pole sheaves on Weierstrass models

The canonical affine `Z`-chart and affine section neighborhood cover a projective
Weierstrass model. Mayer--Vietoris therefore gives vanishing above degree one for
every quasicoherent pole sheaf.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace ModularCurves

variable {K : Type u} [Field K]

/-- On an elliptic projective Weierstrass model, every pole sheaf has vanishing
cohomology in degrees at least two. -/
theorem sectionPoleSheafPower_projModel_subsingleton_H_add_two
    (W : WeierstrassCurve K) [W.IsElliptic] (n q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower (projModelπ W) (projModelZero W)
        (projModelZero_projModelπ W) n).sheaf (q + 2)) := by
  let M := sectionPoleSheafPower (projModelπ W) (projModelZero W)
    (projModelZero_projModelπ W) n
  let N := projModelSectionNeighborhood W
  let Z := projModelZChart W
  letI : M.IsQuasicoherent :=
    sectionPoleSheafPower_isQuasicoherent (projModel_smooth W)
      (projModelZero W) (projModelZero_projModelπ W) n
  exact AlgebraicGeometry.Scheme.Modules.subsingleton_H_add_two_of_two_affine_open_cover
    M N Z N.2 Z.2 (by
      rw [sup_comm]
      exact projModelZChart_sup_sectionNeighborhood_eq_top W) q

end ModularCurves
