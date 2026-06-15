module

public import BernoulliRegular.CyclotomicUnits.Subgroup
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# The finite-field Vandermonde determinant for Kummer's logarithmic matrix

This file proves the pure finite-field determinant input for the
cyclotomic-unit route.  In the eventual `p`-adic calculation, the
Teichmüller lift of `a` reduces modulo `p` to `(a : ZMod p)`, so the
matrix proved non-singular here is the mod-`p` reduction of

```text
omega(a)^(2*j) - 1,     1 <= j <= (p - 3) / 2,  2 <= a <= (p - 1) / 2.
```
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace BernoulliRegular
namespace CyclotomicUnits

open Matrix Polynomial

variable (p : ℕ) [Fact p.Prime]

/-- The row/column size `r = (p - 3) / 2`. -/
abbrev kummerLogRank : ℕ :=
  (p - 3) / 2

/-- The column index `a = 2, ..., (p - 1) / 2`. -/
abbrev kummerLogColumnIndex (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) : ℕ :=
  CPlusGeneratorIndex (p := p) hp_three a

/-- The mod-`p` square of the Teichmüller representative attached to `a`. -/
def teichmullerEvenNode (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) : ZMod p :=
  (kummerLogColumnIndex (p := p) hp_three a : ZMod p) ^ 2

/-- The Kummer/Vandermonde matrix
`V_{j,a} = omega(a)^(2*(j+1)) - 1` over `ZMod p`. -/
def vandermondeTeichmullerEvenSubOneMatrix (hp_three : 3 ≤ p) :
    Matrix (Fin (kummerLogRank p)) (Fin (kummerLogRank p)) (ZMod p) :=
  fun j a => teichmullerEvenNode (p := p) hp_three a ^ ((j : ℕ) + 1) - 1

omit [Fact p.Prime] in
theorem kummerLogColumnIndex_two_le
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    2 ≤ kummerLogColumnIndex (p := p) hp_three a :=
  CPlusGeneratorIndex_two_le (p := p) hp_three a

theorem kummerLogColumnIndex_le_half
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogColumnIndex (p := p) hp_three a ≤ (p - 1) / 2 :=
  CPlusGeneratorIndex_le_half (p := p) hp_three a

theorem kummerLogColumnIndex_lt_p
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogColumnIndex (p := p) hp_three a < p := by
  have hle := kummerLogColumnIndex_le_half (p := p) hp_three a
  have hhalf : (p - 1) / 2 < p := by omega
  omega

omit [Fact p.Prime] in
theorem zmod_natCast_eq_of_lt {a b p : ℕ} (ha : a < p) (hb : b < p)
    (h : (a : ZMod p) = (b : ZMod p)) :
    a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact h

omit [Fact p.Prime] in
theorem zmod_natCast_ne_zero_of_pos_lt {a p : ℕ} (ha_pos : 0 < a) (ha_lt : a < p) :
    (a : ZMod p) ≠ 0 := by
  intro hzero
  rw [ZMod.natCast_eq_zero_iff] at hzero
  exact (not_le_of_gt ha_lt) (Nat.le_of_dvd ha_pos hzero)

theorem kummerLogColumnIndex_add_ne_zero
    (hp_three : 3 ≤ p) (a b : Fin (kummerLogRank p)) :
    ((kummerLogColumnIndex (p := p) hp_three a +
        kummerLogColumnIndex (p := p) hp_three b : ℕ) : ZMod p) ≠ 0 := by
  refine zmod_natCast_ne_zero_of_pos_lt ?_ ?_
  · have ha_two := kummerLogColumnIndex_two_le (p := p) hp_three a
    omega
  · have ha := kummerLogColumnIndex_le_half (p := p) hp_three a
    have hb := kummerLogColumnIndex_le_half (p := p) hp_three b
    have hdouble : 2 * ((p - 1) / 2) ≤ p - 1 := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (p - 1) 2
    omega

theorem teichmullerEvenNode_injective (hp_three : 3 ≤ p) :
    Function.Injective (teichmullerEvenNode (p := p) hp_three) := by
  intro a b hsq
  dsimp [teichmullerEvenNode] at hsq
  let A : ℕ := kummerLogColumnIndex (p := p) hp_three a
  let B : ℕ := kummerLogColumnIndex (p := p) hp_three b
  have hfactor : ((A : ZMod p) - (B : ZMod p)) * ((A : ZMod p) + (B : ZMod p)) = 0 := by
    calc
      ((A : ZMod p) - (B : ZMod p)) * ((A : ZMod p) + (B : ZMod p)) =
          (A : ZMod p) ^ 2 - (B : ZMod p) ^ 2 := by ring
      _ = 0 := by
        simpa [A, B] using sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hfactor with hsub | hadd
  · have hAB_zmod : (A : ZMod p) = (B : ZMod p) := sub_eq_zero.mp hsub
    have hAB : A = B :=
      zmod_natCast_eq_of_lt
        (kummerLogColumnIndex_lt_p (p := p) hp_three a)
        (kummerLogColumnIndex_lt_p (p := p) hp_three b)
        hAB_zmod
    apply Fin.ext
    dsimp [A, B, kummerLogColumnIndex, CPlusGeneratorIndex] at hAB
    omega
  · have hadd_nat :
        ((A + B : ℕ) : ZMod p) = 0 := by
      simpa [A, B, Nat.cast_add] using hadd
    exfalso
    exact (kummerLogColumnIndex_add_ne_zero (p := p) hp_three a b) hadd_nat

theorem teichmullerEvenNode_ne_one (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    teichmullerEvenNode (p := p) hp_three a ≠ 1 := by
  intro h
  dsimp [teichmullerEvenNode] at h
  let A : ℕ := kummerLogColumnIndex (p := p) hp_three a
  have hfactor : ((A : ZMod p) - 1) * ((A : ZMod p) + 1) = 0 := by
    calc
      ((A : ZMod p) - 1) * ((A : ZMod p) + 1) =
          (A : ZMod p) ^ 2 - 1 := by ring
      _ = 0 := by
        simpa [A] using sub_eq_zero.mpr h
  rcases mul_eq_zero.mp hfactor with hsub | hadd
  · have hA1_zmod : (A : ZMod p) = 1 := by simpa using sub_eq_zero.mp hsub
    have hA1 : A = 1 :=
      zmod_natCast_eq_of_lt
        (kummerLogColumnIndex_lt_p (p := p) hp_three a)
        (by omega)
        (by simpa using hA1_zmod)
    have hA_two := kummerLogColumnIndex_two_le (p := p) hp_three a
    omega
  · have hAp1 :
        ((A + 1 : ℕ) : ZMod p) = 0 := by
      simpa [A, Nat.cast_add] using hadd
    exact zmod_natCast_ne_zero_of_pos_lt
      (a := A + 1) (p := p)
      (by omega)
      (by
        have hA := kummerLogColumnIndex_le_half (p := p) hp_three a
        have hhalf : (p - 1) / 2 + 1 < p := by omega
        omega)
      hAp1

/-- The polynomial `1 + X + ... + X^j`. -/
def geomPolynomial (j : Fin (kummerLogRank p)) : (ZMod p)[X] :=
  ∑ i ∈ Finset.range ((j : ℕ) + 1), (X : (ZMod p)[X]) ^ i

theorem geomPolynomial_natDegree (j : Fin (kummerLogRank p)) :
    (geomPolynomial (p := p) j).natDegree = (j : ℕ) := by
  unfold geomPolynomial
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · refine Polynomial.natDegree_sum_le_of_forall_le
      (s := Finset.range ((j : ℕ) + 1))
      (n := (j : ℕ))
      (fun i => (X : (ZMod p)[X]) ^ i) ?_
    intro i hi
    exact (Polynomial.natDegree_X_pow_le i).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  · simp

theorem geomPolynomial_monic (j : Fin (kummerLogRank p)) :
    (geomPolynomial (p := p) j).Monic := by
  unfold geomPolynomial
  exact Polynomial.monic_geom_sum_X (R := ZMod p) (by omega)

theorem geomPolynomial_eval (hp_three : 3 ≤ p)
    (a j : Fin (kummerLogRank p)) :
    (geomPolynomial (p := p) j).eval (teichmullerEvenNode (p := p) hp_three a) =
      ∑ i ∈ Finset.range ((j : ℕ) + 1),
        teichmullerEvenNode (p := p) hp_three a ^ i := by
  simp [geomPolynomial]

/-- The geometric-sum evaluation matrix whose determinant is the ordinary
Vandermonde determinant at the nodes `a^2`. -/
def geomEvaluationMatrix (hp_three : 3 ≤ p) :
    Matrix (Fin (kummerLogRank p)) (Fin (kummerLogRank p)) (ZMod p) :=
  fun a j => (geomPolynomial (p := p) j).eval (teichmullerEvenNode (p := p) hp_three a)

theorem det_geomEvaluationMatrix_ne_zero (hp_three : 3 ≤ p) :
    (geomEvaluationMatrix (p := p) hp_three).det ≠ 0 := by
  have hdet :=
    Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (R := ZMod p)
      (v := teichmullerEvenNode (p := p) hp_three)
      (p := geomPolynomial (p := p))
      (h_deg := geomPolynomial_natDegree (p := p))
      (h_monic := geomPolynomial_monic (p := p))
  have hvand_ne :
      (Matrix.vandermonde (teichmullerEvenNode (p := p) hp_three)).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr
      (teichmullerEvenNode_injective (p := p) hp_three)
  simpa [geomEvaluationMatrix] using hdet ▸ hvand_ne

theorem transpose_vandermondeTeichmullerEvenSubOneMatrix_eq_diagonal_mul_geomEvaluationMatrix
    (hp_three : 3 ≤ p) :
    (vandermondeTeichmullerEvenSubOneMatrix (p := p) hp_three)ᵀ =
      Matrix.diagonal (fun a : Fin (kummerLogRank p) =>
        teichmullerEvenNode (p := p) hp_three a - 1) *
        geomEvaluationMatrix (p := p) hp_three := by
  ext a j
  simp [vandermondeTeichmullerEvenSubOneMatrix, geomEvaluationMatrix,
    geomPolynomial_eval, Matrix.diagonal_mul]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (geom_sum_mul (teichmullerEvenNode (p := p) hp_three a) ((j : ℕ) + 1)).symm

theorem vandermonde_teichmuller_even_sub_one_det_ne_zero
    (hp_three : 3 ≤ p) :
    (vandermondeTeichmullerEvenSubOneMatrix (p := p) hp_three).det ≠ 0 := by
  have htranspose :=
    congrArg Matrix.det
      (transpose_vandermondeTeichmullerEvenSubOneMatrix_eq_diagonal_mul_geomEvaluationMatrix
        (p := p) hp_three)
  rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_diagonal] at htranspose
  rw [htranspose]
  exact mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr
      (by
        intro a _
        exact sub_ne_zero.mpr (teichmullerEvenNode_ne_one (p := p) hp_three a)))
    (det_geomEvaluationMatrix_ne_zero (p := p) hp_three)

end CyclotomicUnits
end BernoulliRegular

end
