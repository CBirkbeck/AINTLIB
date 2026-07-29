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

/-- The signed total differential formula, with inclusions extended by zero away
from the corresponding total degrees. -/
@[reassoc]
theorem ιTotalOrZero_d_upNat (q p n : ℕ) :
    K.ιTotalOrZero (.up ℕ) q p n ≫
        (K.total (.up ℕ)).d n (n + 1) =
      (K.d q (q + 1)).f p ≫
          K.ιTotalOrZero (.up ℕ) (q + 1) p (n + 1) +
        ((-1 : ℤˣ) ^ q) • ((K.X q).d p (p + 1) ≫
          K.ιTotalOrZero (.up ℕ) q (p + 1) (n + 1)) := by
  by_cases h : q + p = n
  · subst n
    rw [K.ιTotalOrZero_eq (.up ℕ) q p (q + p) rfl,
      K.ιTotalOrZero_eq (.up ℕ) (q + 1) p (q + p + 1)
        (by change q + 1 + p = q + p + 1; omega),
      K.ιTotalOrZero_eq (.up ℕ) q (p + 1) (q + p + 1)
        (by change q + (p + 1) = q + p + 1; omega)]
    exact K.ιTotal_d_upNat q p
  · have h₁ : q + 1 + p ≠ n + 1 := by omega
    have h₂ : q + (p + 1) ≠ n + 1 := by omega
    rw [K.ιTotalOrZero_eq_zero (.up ℕ) q p n h,
      K.ιTotalOrZero_eq_zero (.up ℕ) (q + 1) p (n + 1) h₁,
      K.ιTotalOrZero_eq_zero (.up ℕ) q (p + 1) (n + 1) h₂]
    simp

end HomologicalComplex₂
