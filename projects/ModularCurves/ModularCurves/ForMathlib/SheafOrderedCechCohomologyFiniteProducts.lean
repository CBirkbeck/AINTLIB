import ModularCurves.ForMathlib.SheafCohomologyFiniteProducts
import ModularCurves.ForMathlib.SheafOrderedCechSheafResolution

/-!
# Cohomology of ordered sheaf-level Cech terms

Finite ordered Cech terms inherit cohomology vanishing from their
restriction-pushforward factors.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

open AlgebraicGeometry.Scheme.Modules

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} [LinearOrder ι] (U : ι → Opens X)

/-- A finite ordered Cech term has vanishing cohomology in a degree whenever
all of its restriction-pushforward factors do. -/
theorem orderedCechTerm_subsingleton_H_of_factors [Finite ι]
    (n q : ℕ)
    (h : ∀ i : OrderedCechIndex ι n,
      Subsingleton (H (orderedCechTermFactor F U n i) q)) :
    Subsingleton (H (orderedCechTerm F U n) q) := by
  letI : Finite (OrderedCechIndex ι n) :=
    Finite.of_injective (fun i => i.1) Subtype.val_injective
  exact CategoryTheory.Sheaf.H.subsingleton_product_of_factors
    (orderedCechTermFactor F U n) q h

end TopCat.Sheaf
