import ModularCurves.ForMathlib.SheafCechAcyclicComparison
import ModularCurves.ForMathlib.SheafCechFlasqueTerms

/-!
# Exactness of Cech complexes of flasque sheaves

For a finite open cover, every positive cohomology group of every Cech term of
a flasque sheaf vanishes. The acyclic-cover comparison therefore makes its
native Cech complex exact in every positive degree.
-/

open CategoryTheory TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable {ι : Type u} (U : ι → Opens X)

/-- The native Cech complex of a flasque sheaf is exact in every positive
degree for a finite open cover. -/
theorem cechComplex_exactAt_succ_of_isFlasque [Finite ι]
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F]
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).ExactAt (n + 1) := by
  apply cechComplex_exactAt_succ_of_subsingleton_H F U hU
  · intro p q hq
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    exact cechTerm_subsingleton_H_of_isFlasque F U p r
  · exact IsFlasque.subsingleton_H n

end TopCat.Sheaf
