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

/-- The total differential is the finite antidiagonal sum of its horizontal and
signed vertical bidegree components. -/
theorem total_d_upNat_decomposition (n : ℕ) :
    (K.total (.up ℕ)).d n (n + 1) =
      ∑ qp ∈ Finset.antidiagonal n,
        K.πTotalUpNat qp.1 qp.2 n ≫
          ((K.d qp.1 (qp.1 + 1)).f qp.2 ≫
              K.ιTotalOrZero (.up ℕ) (qp.1 + 1) qp.2 (n + 1) +
            ((-1 : ℤˣ) ^ qp.1) • ((K.X qp.1).d qp.2 (qp.2 + 1) ≫
              K.ιTotalOrZero (.up ℕ) qp.1 (qp.2 + 1) (n + 1))) := by
  calc
    _ = (𝟙 _ : (K.total (.up ℕ)).X n ⟶ _) ≫
        (K.total (.up ℕ)).d n (n + 1) := by simp
    _ = (∑ qp ∈ Finset.antidiagonal n,
          K.πTotalUpNat qp.1 qp.2 n ≫
            K.ιTotalOrZero (.up ℕ) qp.1 qp.2 n) ≫
        (K.total (.up ℕ)).d n (n + 1) := by
      rw [K.totalUpNat_decomposition n]
    _ = _ := by
      rw [Preadditive.sum_comp]
      apply Finset.sum_congr rfl
      intro qp hqp
      rw [Category.assoc, K.ιTotalOrZero_d_upNat]

/-- Projection of the total differential to one target bidegree is the sum of
the incoming horizontal and signed vertical differentials. -/
theorem total_d_πTotalUpNat (n q p : ℕ) (hqp : q + p = n + 1) :
    (K.total (.up ℕ)).d n (n + 1) ≫ K.πTotalUpNat q p (n + 1) =
      (if _hq : 0 < q then
          K.πTotalUpNat (q - 1) p n ≫ (K.d (q - 1) q).f p
        else 0) +
      ((-1 : ℤˣ) ^ q) •
        (if _hp : 0 < p then
          K.πTotalUpNat q (p - 1) n ≫ (K.X q).d (p - 1) p
        else 0) := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  change a + b = n at hab
  subst n
  by_cases ha : a + 1 = q
  · have hb : b = p := by omega
    subst q p
    by_cases hb0 : 0 < b
    · simp [hb0, Category.assoc, K.ιTotal_d_upNat_assoc]
    · simp [hb0, K.ιTotal_d_upNat_assoc]
  · by_cases hav : a = q
    · have hb : b + 1 = p := by omega
      subst q p
      by_cases ha0 : 0 < a
      · simp [ha0, Category.assoc, K.ιTotal_d_upNat_assoc]
      · simp [ha0, K.ιTotal_d_upNat_assoc]
    · by_cases hq : 0 < q
      · have haq : a ≠ q - 1 := by omega
        by_cases hp : 0 < p
        · have hbp : b ≠ p - 1 := by omega
          simp [ha, hav, hq, hp, haq, Category.assoc,
            K.ιTotal_d_upNat_assoc]
        · simp [ha, hav, hq, hp, haq, Category.assoc,
            K.ιTotal_d_upNat_assoc]
      · by_cases hp : 0 < p
        · have hbp : b ≠ p - 1 := by omega
          simp [ha, hav, hq, hp, Category.assoc,
            K.ιTotal_d_upNat_assoc]
        · omega

end HomologicalComplex₂
