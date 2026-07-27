import ModularCurves.EllipticCurve.PoleSheafAwaySections
import ModularCurves.EllipticCurve.PoleSheafModel

/-!
# The marked-point complement of a Weierstrass model

This file identifies the complement of the zero section in a projective Weierstrass model
with its standard affine `Z`-chart.
-/

open AlgebraicGeometry TopologicalSpace

universe u

namespace ModularCurves

noncomputable section

variable {R : Type u} [CommRing R]

/-- The complement of the zero section in a projective Weierstrass model is its affine
`Z`-chart. -/
theorem sectionAway_projModelZero_eq_zChart (W : WeierstrassCurve R) :
    sectionAway (projModelZero W) (projModelZero_projModelπ W) =
      (projModelZChart W : (projModel W).Opens) := by
  ext p
  change p ∉ Set.range ⇑(projModelZero W) ↔
    p ∈ (projModelZChart W : (projModel W).Opens)
  constructor
  · intro hp
    by_contra hpZ
    exact hp (mem_range_zero_of_not_mem_zChart hpZ)
  · intro hpZ hp
    exact not_mem_zChart_of_mem_range_zero hp hpZ

end

end ModularCurves
