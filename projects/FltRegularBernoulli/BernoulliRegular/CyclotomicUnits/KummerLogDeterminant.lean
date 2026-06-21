import BernoulliRegular.CyclotomicUnits.KummerLogFormalEvaluator
import BernoulliRegular.CyclotomicUnits.KummerLogLinearAlgebra
import BernoulliRegular.CyclotomicUnits.Vandermonde

/-!
# Kummer logarithm determinant

This file assembles the CU-11 coefficient congruence and the CU-12
Vandermonde determinant into Kummer's determinant criterion.  The determinant
is nonzero exactly when the Bernoulli numerator factors in the classical
range are nonzero modulo `p`.
-/

@[expose] public section

noncomputable section

open NumberField
open NumberField.IsCMField
open scoped BigOperators NumberField

namespace BernoulliRegular
namespace CyclotomicUnits

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

/-- The row scalar multiplying the finite-field Vandermonde matrix in the
concrete Kummer logarithm matrix. -/
def kummerLogDetRowFactor (j : Fin (kummerLogRank p)) : ZMod p :=
  squaredKummerLogUnitFactor p (kummerLogRowIndex (p := p) j) *
    bernoulliFactor p (kummerLogRowIndex (p := p) j)

/-- The concrete Kummer logarithm matrix factors as a diagonal matrix of row
Bernoulli factors times the finite-field Vandermonde matrix from CU-12. -/
theorem concreteKummerLogMatrix_eq_diagonal_mul_vandermonde
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p) :
    concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five =
      Matrix.diagonal (kummerLogDetRowFactor (p := p)) *
        vandermondeTeichmullerEvenSubOneMatrix (p := p) hp_three := by
  ext j a
  rw [Matrix.diagonal_mul]
  rw [kummerLogCoeff_congr (p := p) (K := K) hp_three hp_five j a]
  simp only [kummerLogDetRowFactor, vandermondeTeichmullerEvenSubOneMatrix,
    teichmullerEvenNode, kummerLogRowIndex_eq, Nat.cast_add, Nat.cast_ofNat]
  have hpow :
      ((((a : ℕ) : ZMod p) + 2) ^ 2) ^ ((j : ℕ) + 1) =
        (((a : ℕ) : ZMod p) + 2) ^ (2 * ((j : ℕ) + 1)) := by
    rw [pow_mul]
  rw [hpow]

/-- Determinant form of the Kummer logarithm matrix factorization. -/
theorem concreteKummerLogMatrix_det_eq_prod_rowFactor_mul_vandermonde_det
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p) :
    (concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five).det =
      (∏ j : Fin (kummerLogRank p), kummerLogDetRowFactor (p := p) j) *
        (vandermondeTeichmullerEvenSubOneMatrix (p := p) hp_three).det := by
  rw [concreteKummerLogMatrix_eq_diagonal_mul_vandermonde
      (p := p) (K := K) hp_three hp_five,
    Matrix.det_mul, Matrix.det_diagonal]

/-- The determinant is nonzero exactly when every row scalar is nonzero. -/
theorem concreteKummerLogMatrix_det_ne_zero_iff_forall_rowFactor_ne_zero
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p) :
    (concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five).det ≠ 0 ↔
      ∀ j : Fin (kummerLogRank p), kummerLogDetRowFactor (p := p) j ≠ 0 := by
  rw [concreteKummerLogMatrix_det_eq_prod_rowFactor_mul_vandermonde_det
      (p := p) (K := K) hp_three hp_five]
  constructor
  · intro h j hrow
    have hprod :
        (∏ j : Fin (kummerLogRank p), kummerLogDetRowFactor (p := p) j) = 0 :=
      Finset.prod_eq_zero_iff.mpr ⟨j, Finset.mem_univ j, hrow⟩
    exact h (by rw [hprod, zero_mul])
  · intro h
    exact mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr (by intro j _; exact h j))
      (vandermonde_teichmuller_even_sub_one_det_ne_zero (p := p) hp_three)

/-- The squared-family row factor is nonzero exactly when its Bernoulli factor
is nonzero; the extra Kummer logarithm unit is already known to be nonzero. -/
theorem kummerLogDetRowFactor_ne_zero_iff_bernoulliFactor_ne_zero
    (hp_five : 5 ≤ p) (j : Fin (kummerLogRank p)) :
    kummerLogDetRowFactor (p := p) j ≠ 0 ↔
      bernoulliFactor p (kummerLogRowIndex (p := p) j) ≠ 0 := by
  unfold kummerLogDetRowFactor
  constructor
  · intro h hB
    exact h (mul_eq_zero.mpr (Or.inr hB))
  · intro hB
    exact mul_ne_zero
      (squaredKummerLogUnitFactor_ne_zero (p := p) hp_five j) hB

/-- Kummer determinant nonvanishing reduced to the Bernoulli factors in each
matrix row. -/
theorem concreteKummerLogMatrix_det_ne_zero_iff_forall_bernoulliFactor_ne_zero
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p) :
    (concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five).det ≠ 0 ↔
      ∀ j : Fin (kummerLogRank p),
        bernoulliFactor p (kummerLogRowIndex (p := p) j) ≠ 0 := by
  rw [concreteKummerLogMatrix_det_ne_zero_iff_forall_rowFactor_ne_zero
      (p := p) (K := K) hp_three hp_five]
  constructor
  · intro h j
    exact (kummerLogDetRowFactor_ne_zero_iff_bernoulliFactor_ne_zero
      (p := p) hp_five j).mp (h j)
  · intro h j
    exact (kummerLogDetRowFactor_ne_zero_iff_bernoulliFactor_ne_zero
      (p := p) hp_five j).mpr (h j)

/-- In the Kummer range, reducing `B_(2j)/(2j)` modulo `p` is nonzero
exactly when the numerator of `B_(2j)` is not divisible by `p`. -/
theorem bernoulliFactor_ne_zero_iff_not_dvd_bernoulli_num
    {j : ℕ} (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    bernoulliFactor p j ≠ 0 ↔
      ¬ (p : ℤ) ∣ (_root_.bernoulli (2 * j)).num := by
  let B : ℚ := _root_.bernoulli (2 * j)
  let n : ℕ := 2 * j
  let q : ℚ := B / (n : ℚ)
  let D : ℕ := B.den * n
  have hn_pos : 0 < n := by
    dsimp [n]
    omega
  have hnQ_ne : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn_pos.ne'
  have hD_pos : 0 < D := by
    dsimp [D]
    exact Nat.mul_pos B.den_pos hn_pos
  have hD_int_ne : ((D : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast hD_pos.ne'
  have hqdf : q = Rat.divInt B.num ((D : ℕ) : ℤ) := by
    calc
      q = B / (n : ℚ) := rfl
      _ = ((B.num : ℚ) / (B.den : ℚ)) / (n : ℚ) := by
        rw [Rat.num_div_den]
      _ = (B.num : ℚ) / (D : ℚ) := by
        dsimp [D]
        field_simp [hnQ_ne]
        rw [Nat.cast_mul]
        ring
      _ = Rat.divInt B.num ((D : ℕ) : ℤ) := by
        rw [Rat.divInt_eq_div]
        norm_num
  obtain ⟨c, hcnum, hcden⟩ := Rat.num_den_mk hD_int_ne hqdf
  have hD_zmod_ne : ((D : ℕ) : ZMod p) ≠ 0 := by
    have hBden := bernoulli_den_zmod_ne_zero (p := p) (j := j) hj hjp
    have hn := two_mul_index_zmod_ne_zero (p := p) (j := j) hj hjp
    simpa [D, B, n, Nat.cast_mul] using mul_ne_zero hBden hn
  have hcden_zmod :
      ((D : ℕ) : ZMod p) = (c : ZMod p) * (q.den : ZMod p) := by
    have hcast := congrArg (fun z : ℤ ↦ (z : ZMod p)) hcden
    simpa [Int.cast_mul] using hcast
  have hc_zmod_ne : (c : ZMod p) ≠ 0 := fun hc_zero ↦
    hD_zmod_ne (by rw [hcden_zmod, hc_zero, zero_mul])
  have hqden_zmod_ne : ((q.den : ℕ) : ZMod p) ≠ 0 := fun hqden_zero ↦
    hD_zmod_ne (by rw [hcden_zmod, hqden_zero, mul_zero])
  have hcnum_zmod :
      ((B.num : ℤ) : ZMod p) = (c : ZMod p) * (q.num : ZMod p) := by
    have hcast := congrArg (fun z : ℤ ↦ (z : ZMod p)) hcnum
    simpa [Int.cast_mul] using hcast
  have hqnum_ne_iff_Bnum_ne :
      (q.num : ZMod p) ≠ 0 ↔ ((B.num : ℤ) : ZMod p) ≠ 0 := by
    constructor
    · intro hq hB
      have hmul : (c : ZMod p) * (q.num : ZMod p) = 0 := by
        simpa [hcnum_zmod] using hB
      exact hq ((mul_eq_zero.mp hmul).resolve_left hc_zmod_ne)
    · intro hB hq
      exact hB (by rw [hcnum_zmod, hq, mul_zero])
  have hred_ne_iff : ratReductionZMod p q ≠ 0 ↔ (q.num : ZMod p) ≠ 0 := by
    unfold ratReductionZMod
    rw [div_eq_mul_inv]
    constructor
    · intro h hq
      exact h (by rw [hq, zero_mul])
    · intro hq hzero
      rcases mul_eq_zero.mp hzero with hnum | hden_inv
      · exact hq hnum
      · exact (inv_ne_zero hqden_zmod_ne) hden_inv
  have hBnum_ne_iff :
      (((_root_.bernoulli (2 * j)).num : ℤ) : ZMod p) ≠ 0 ↔
        ¬ (p : ℤ) ∣ (_root_.bernoulli (2 * j)).num :=
    not_congr (CharP.intCast_eq_zero_iff (ZMod p) p
      ((_root_.bernoulli (2 * j)).num))
  simpa [bernoulliFactor, q, B, n] using
    hred_ne_iff.trans (hqnum_ne_iff_Bnum_ne.trans (by simpa [B] using hBnum_ne_iff))

omit [Fact p.Prime] in
/-- A natural number in the Kummer Bernoulli range is represented by a matrix
row index. -/
theorem exists_fin_kummerLogRowIndex_eq_of_mem_range
    {j : ℕ} (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    ∃ i : Fin (kummerLogRank p), kummerLogRowIndex (p := p) i = j := by
  have hj_le_rank : j ≤ kummerLogRank p := by
    rw [kummerLogRank]
    exact (Nat.le_div_iff_mul_le Nat.zero_lt_two).mpr (by omega)
  refine ⟨⟨j - 1, by omega⟩, ?_⟩
  simp [kummerLogRowIndex]
  omega

/-- CU-13: Kummer's logarithm determinant is nonzero exactly when all
Bernoulli numerators in the classical even range are prime to `p`. -/
theorem kummerLogMatrix_det_ne_zero_iff_bernoulli_nonzero
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p) :
    (concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five).det ≠ 0 ↔
      ∀ j : ℕ, 1 ≤ j → 2 * j ≤ p - 3 →
        ¬ (p : ℤ) ∣ (_root_.bernoulli (2 * j)).num := by
  rw [concreteKummerLogMatrix_det_ne_zero_iff_forall_bernoulliFactor_ne_zero
      (p := p) (K := K) hp_three hp_five]
  constructor
  · intro h j hj hjp
    obtain ⟨i, hi⟩ :=
      exists_fin_kummerLogRowIndex_eq_of_mem_range (p := p) hj hjp
    have hi' : (i : ℕ) + 1 = j := by
      simpa [kummerLogRowIndex] using hi
    exact (bernoulliFactor_ne_zero_iff_not_dvd_bernoulli_num
      (p := p) (j := j) hj hjp).mp (by simpa [hi'] using h i)
  · intro h i
    exact (bernoulliFactor_ne_zero_iff_not_dvd_bernoulli_num
      (p := p)
      (j := kummerLogRowIndex (p := p) i)
      (kummerLogRowIndex_one_le (p := p) i)
      (two_mul_kummerLogRowIndex_le_sub_three (p := p) i)).mpr
        (h (kummerLogRowIndex (p := p) i)
          (kummerLogRowIndex_one_le (p := p) i)
          (two_mul_kummerLogRowIndex_le_sub_three (p := p) i))

end CyclotomicUnits
end BernoulliRegular

end
