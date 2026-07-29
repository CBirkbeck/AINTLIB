import ModularCurves.ForMathlib.TotalComplexUpNatLowDegrees
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Decomposition of first-quadrant total-complex degrees

Express every degree of a first-quadrant total complex as the finite sum of its
bidegree projections and inclusions.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open scoped BigOperators

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))
variable [K.HasTotal (.up ℕ)]

/-- A degree of a first-quadrant total complex is the finite direct sum of the
bidegrees on the corresponding antidiagonal. -/
theorem totalUpNat_decomposition (n : ℕ) :
    ∑ qp ∈ Finset.antidiagonal n,
        K.πTotalUpNat qp.1 qp.2 n ≫
          K.ιTotalOrZero (.up ℕ) qp.1 qp.2 n =
      𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro q p h
  change q + p = n at h
  simp only [Preadditive.comp_sum]
  rw [Finset.sum_eq_single (q, p)]
  · rw [K.ιTotalOrZero_eq (.up ℕ) q p n h]
    simp
  · rintro ⟨q', p'⟩ hmem hne
    by_cases hq : q = q'
    · have hp : p ≠ p' := fun hp ↦ hne (Prod.ext hq.symm hp.symm)
      simp [hq, hp]
    · simp [hq]
  · intro hnot
    exact (hnot (Finset.mem_antidiagonal.mpr h)).elim

end HomologicalComplex₂
