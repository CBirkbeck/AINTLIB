module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.SamePrimeLog.ArtinHasseExpCoordLogHomogeneous

@[expose] public section

noncomputable section

open scoped NumberField
open PowerSeries

namespace BernoulliRegular
namespace CyclotomicUnits
namespace PadicLogSetup
namespace DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance : CharZero (ValuedCompletion p K) :=
  algebraRat.charZero (ValuedCompletion p K)

noncomputable def samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
    (N d : ℕ) (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  ∑ a ∈ (Finset.Icc 1 d).attach,
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm (p := p) (K := K) N a.1 d x hx

theorem samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_eval_sum
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum (p := p) (K := K) N d x hx =
      ∑ a ∈ (Finset.Icc 1 d).attach,
        samePrimeNatDivEval (p := p) (K := K) N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
            (p := p) (K := K) N a.1 d x)
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
            have hden : a.1.factorization p * (p - 1) ≤ d :=
              samePrimeFiniteArtinHasse_den_exponent_le (p := p)
                (Nat.ne_zero_of_lt ha1) had
            simpa [samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator] using
              (Ideal.pow_le_pow_right hden
                (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator_mem_lambdaIdeal_pow
                  (p := p) (K := K) N a.1 d hx))) := by
  classical
  unfold samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
  refine Finset.sum_congr rfl ?_
  intro a _ha
  have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
  have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
  have han : a.1 ≠ 0 := Nat.ne_zero_of_lt ha1
  have hden : a.1.factorization p * (p - 1) ≤ d :=
    samePrimeFiniteArtinHasse_den_exponent_le (p := p) han had
  have hcoeff :
      ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ a.1).coeff d ∈
        (lambdaIdeal p K) ^ d :=
    samePrimeFiniteArtinHasseExpCoordPoly_pow_coeff_mem_lambdaIdeal_pow
      (p := p) (K := K) N hx a.1 d
  have hsign :
      (((-1 : ValuedIntegerRing p K) ^ (a.1 + 1)) *
          ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ a.1).coeff d) ∈
        (lambdaIdeal p K) ^ d :=
    samePrimeFiniteArtinHasseExpCoord_signed_pow_coeff_mem_lambdaIdeal_pow
      (p := p) (K := K) N a.1 d hx
  have hnum0 :
      samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
          (p := p) (K := K) N a.1 d x ∈
        (lambdaIdeal p K) ^ (a.1.factorization p * (p - 1) + 0) := by
    simpa [samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator] using
      (Ideal.pow_le_pow_right hden hsign)
  have hmk :
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          ((-1 : ValuedIntegerRing p K) ^ (a.1 + 1)) =
        ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (a.1 + 1)) := by
    simp
  rw [samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm_eq_signed_eval
    (p := p) (K := K) N a.1 d hx han had]
  rw [← hmk]
  rw [← samePrimeNatDivEvalAtDegree_mul_left (p := p) (K := K) han
    ((-1 : ValuedIntegerRing p K) ^ (a.1 + 1)) hcoeff hsign hden]
  rw [samePrimeNatDivEvalAtDegree_eq_samePrimeNatDivEval (p := p) (K := K)
    han hsign hden hnum0]
  exact samePrimeNatDivEval_eq_of_eq (p := p) (K := K) han
    (by simp [samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator]) hnum0 _

set_option linter.style.longLine false in
theorem samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_zero_of_factorial_weighted_sum_mem
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hclear :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          (((-1 : ValuedIntegerRing p K) ^ (n + 1)) *
            ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d)) ∈
        (lambdaIdeal p K) ^ (d.factorial.factorization p * (p - 1) + (N + 1))) :
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
        (p := p) (K := K) N d x hx = 0 := by
  classical
  let z : ℕ → ValuedIntegerRing p K := fun n ↦
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
      (p := p) (K := K) N n d x
  have hz0 : ∀ n ∈ Finset.Icc 1 d,
      z n ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + 0) := by
    intro n hnI
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    have hnd : n ≤ d := (Finset.mem_Icc.mp hnI).2
    have hden : n.factorization p * (p - 1) ≤ d :=
      samePrimeFiniteArtinHasse_den_exponent_le (p := p)
        (Nat.ne_zero_of_lt hn1) hnd
    simpa [z] using
      (Ideal.pow_le_pow_right hden
        (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator_mem_lambdaIdeal_pow
          (p := p) (K := K) N n d hx))
  have htransport :=
    samePrimeNatDivEval_Icc_sum_eq_zero_of_factorial_weighted_sum_mem_lambdaIdeal_pow
      (p := p) (K := K) (N := N) (d := d) (s := 0) (t := N + 1) z hz0
      (by simpa [z, samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator] using hclear)
      le_rfl
  calc
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
        (p := p) (K := K) N d x hx
        =
      ∑ a ∈ (Finset.Icc 1 d).attach,
        samePrimeNatDivEval (p := p) (K := K) N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (z a.1) (hz0 a.1 a.2) := by
        simpa [z] using
          samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_eval_sum
            (p := p) (K := K) N d hx
    _ = 0 := htransport

set_option linter.style.longLine false in
theorem samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_zero_of_not_pow
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hd : ¬ ∃ r : ℕ, d = p ^ r) :
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
        (p := p) (K := K) N d x hx = 0 :=
  samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_zero_of_factorial_weighted_sum_mem
    (p := p) (K := K) N d hx
    (by
      simpa [samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator] using
        samePrimeFiniteArtinHasseLogHomogeneousNumerator_factorial_weighted_sum_mem_lambdaIdeal_pow_of_not_pow
          (p := p) (K := K) N d hx hd)

theorem samePrimeFiniteLogTermCore_finiteArtinHasseExpCoord_eq_homogeneous_support_sum
    (N n : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) (hn : n ≠ 0) :
    samePrimeFiniteLogTermCore (p := p) (K := K) N n
        (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x)
        (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal (p := p) (K := K) N hx) =
      ∑ d ∈ ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).support,
        samePrimeFiniteArtinHasseExpCoordLogHomogeneousCore (p := p) (K := K) N n d x hx := by
  classical
  let P : Polynomial (ValuedIntegerRing p K) :=
    samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x
  let z : ValuedIntegerRing p K :=
    samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x
  let s : ℕ := samePrimeFiniteLogTermOrder (p := p) n
  have hz : z ∈ lambdaIdeal p K := by
    simpa [z] using samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal
      (p := p) (K := K) N hx
  have hpow_order : z ^ n ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
    simpa [z, s, factorization_mul_pred_add_samePrimeFiniteLogTermOrder
        (p := p) hn] using
      Ideal.pow_mem_pow hz n
  have hcoeff_order_of_mem :
      ∀ d ∈ (P ^ n).support,
        (P ^ n).coeff d ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
    intro d hd
    have hnd : n ≤ d := by
      simpa [P] using
        samePrimeFiniteArtinHasseExpCoordPoly_pow_le_of_mem_support
          (p := p) (K := K) N x hd
    have hcoeff : (P ^ n).coeff d ∈ (lambdaIdeal p K) ^ d := by
      simpa [P] using
        samePrimeFiniteArtinHasseExpCoordPoly_pow_coeff_mem_lambdaIdeal_pow
          (p := p) (K := K) N hx n d
    have hle : (lambdaIdeal p K) ^ d ≤
        (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
      rw [factorization_mul_pred_add_samePrimeFiniteLogTermOrder (p := p) hn]
      exact Ideal.pow_le_pow_right hnd
    exact hle hcoeff
  have hcoeff_order :
      ∀ d, (P ^ n).coeff d ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
    intro d
    by_cases hd : d ∈ (P ^ n).support
    · exact hcoeff_order_of_mem d hd
    · have hzero : (P ^ n).coeff d = 0 := by
        simpa [Polynomial.mem_support_iff] using hd
      rw [hzero]
      exact zero_mem _
  have heval :
      (P ^ n).eval 1 = ∑ d ∈ (P ^ n).support, (P ^ n).coeff d := by
    rw [Polynomial.eval_eq_sum]
    simp [Polynomial.sum]
  have hsum_eq : z ^ n = ∑ d ∈ (P ^ n).support, (P ^ n).coeff d := by
    calc
      z ^ n = ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x).eval 1) ^ n := by
        rw [samePrimeFiniteArtinHasseExpCoordPoly_eval_one]
      _ = (P ^ n).eval 1 := by
        simp [P, Polynomial.eval_pow]
      _ = ∑ d ∈ (P ^ n).support, (P ^ n).coeff d := heval
  have hsum_order :
      (∑ d ∈ (P ^ n).support, (P ^ n).coeff d) ∈
        (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
    rw [← hsum_eq]
    exact hpow_order
  calc
    samePrimeFiniteLogTermCore (p := p) (K := K) N n
        (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x)
        (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal (p := p) (K := K) N hx)
        =
      samePrimeNatDivEval (p := p) (K := K) N n s hn (z ^ n) hpow_order := by
        rw [samePrimeFiniteLogTermCore_eq_samePrimeNatDivEvalAtDegree
          (p := p) (K := K) hn hz]
        rw [samePrimeNatDivEvalAtDegree_eq_samePrimeNatDivEval
          (p := p) (K := K) hn (Ideal.pow_mem_pow hz n)
          (by
            have h := Nat.factorization_mul_pred_le_pred
              (ell := p) (n := n) (Fact.out : Nat.Prime p) hn
            omega)
          hpow_order]
    _ =
      samePrimeNatDivEval (p := p) (K := K) N n s hn
        (∑ d ∈ (P ^ n).support, (P ^ n).coeff d) hsum_order :=
        samePrimeNatDivEval_eq_of_eq (p := p) (K := K) hn
          hsum_eq hpow_order hsum_order
    _ =
      ∑ d ∈ (P ^ n).support,
        samePrimeNatDivEval (p := p) (K := K) N n s hn ((P ^ n).coeff d)
          (hcoeff_order d) := by
        rw [samePrimeNatDivEval_sum (p := p) (K := K) hn (P ^ n).support
          (fun d ↦ (P ^ n).coeff d) hcoeff_order hsum_order]
    _ =
      ∑ d ∈ (P ^ n).support,
        samePrimeFiniteArtinHasseExpCoordLogHomogeneousCore (p := p) (K := K) N n d x hx := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        have hnd : n ≤ d := by
          simpa [P] using
            samePrimeFiniteArtinHasseExpCoordPoly_pow_le_of_mem_support
              (p := p) (K := K) N x hd
        have hden : n.factorization p * (p - 1) ≤ d :=
          samePrimeFiniteArtinHasse_den_exponent_le (p := p) hn hnd
        have hcoeff : (P ^ n).coeff d ∈ (lambdaIdeal p K) ^ d := by
          simpa [P] using
            samePrimeFiniteArtinHasseExpCoordPoly_pow_coeff_mem_lambdaIdeal_pow
              (p := p) (K := K) N hx n d
        rw [samePrimeFiniteArtinHasseExpCoordLogHomogeneousCore, dif_neg hn, dif_pos hnd]
        exact (samePrimeNatDivEvalAtDegree_eq_samePrimeNatDivEval
          (p := p) (K := K) hn hcoeff hden (hcoeff_order d)).symm

theorem samePrimeFiniteLogTerm_finiteArtinHasseExpCoord_eq_homogeneous_support_sum
    (N n : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) (hn : n ≠ 0) :
    samePrimeFiniteLogTerm (p := p) (K := K) N n
        (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x)
        (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal (p := p) (K := K) N hx) =
      ∑ d ∈ ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).support,
        samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm (p := p) (K := K) N n d x hx := by
  rw [samePrimeFiniteLogTerm,
    samePrimeFiniteLogTermCore_finiteArtinHasseExpCoord_eq_homogeneous_support_sum
      (p := p) (K := K) N n hx hn,
    Finset.mul_sum]
  simp [samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm]

/-- Forced lambda-adic order of the `r`-th Artin--Hasse logarithm term
`x^(p^r) / p^r` for `x` in the lambda ideal. -/
def samePrimeArtinHasseLogTermOrder (r : ℕ) : ℕ :=
  p ^ r - r * (p - 1)

private theorem nat_mul_le_pow_self_of_two_le {a r : ℕ} (ha : 2 ≤ a) :
    r * a ≤ a ^ r := by
  cases r with
  | zero =>
      simp
  | succ r =>
      have hs : r + 1 ≤ a ^ r := by
        have htwo : r + 1 ≤ 2 ^ r := Nat.succ_le_of_lt r.lt_two_pow_self
        exact htwo.trans (Nat.pow_le_pow_left ha r)
      have hmul := Nat.mul_le_mul_right a hs
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul

theorem samePrimeArtinHasseLog_den_le (r : ℕ) :
    r * (p - 1) ≤ p ^ r := by
  have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hmul := nat_mul_le_pow_self_of_two_le (a := p) (r := r) hp_two
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hpred : p - 1 ≤ p := Nat.sub_le p 1
  exact (Nat.mul_le_mul_left r hpred).trans hmul

theorem samePrimeArtinHasseLog_den_add_order (r : ℕ) :
    r * (p - 1) + samePrimeArtinHasseLogTermOrder (p := p) r = p ^ r := by
  simp [samePrimeArtinHasseLogTermOrder,
    Nat.add_sub_cancel' (samePrimeArtinHasseLog_den_le (p := p) r)]

theorem le_samePrimeArtinHasseLogTermOrder (r : ℕ) :
    r ≤ samePrimeArtinHasseLogTermOrder (p := p) r := by
  have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hmul := nat_mul_le_pow_self_of_two_le (a := p) (r := r) hp_two
  have hp_one : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
  have hadd : r + r * (p - 1) ≤ p ^ r := by
    calc
      r + r * (p - 1) = r * (1 + (p - 1)) := by
        rw [Nat.mul_add, mul_one]
      _ = r * p := by
        rw [Nat.add_comm 1 (p - 1), Nat.sub_add_cancel hp_one]
      _ ≤ p ^ r := hmul
  exact Nat.le_sub_of_add_le hadd

/-- The numerator data representing `x^(p^r) / p^r` in the same-prime
lambda-adic quotient. -/
theorem samePrimeArtinHasseLogTermData_exists (r : ℕ)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    ∃ y : ValuedIntegerRing p K,
      y ∈ (lambdaIdeal p K) ^ samePrimeArtinHasseLogTermOrder (p := p) r ∧
        (p : ValuedIntegerRing p K) ^ r * y = x ^ (p ^ r) := by
  have hxpow : x ^ (p ^ r) ∈
      (lambdaIdeal p K) ^
        (r * (p - 1) + samePrimeArtinHasseLogTermOrder (p := p) r) := by
    simpa [samePrimeArtinHasseLog_den_add_order (p := p) r] using
      Ideal.pow_mem_pow hx (p ^ r)
  exact exists_natCast_prime_pow_mul_eq_of_mem_lambdaIdeal_pow_mul_pred_add
    (p := p) (K := K) r (samePrimeArtinHasseLogTermOrder (p := p) r) hxpow

/-- Chosen numerator representing the same-prime Artin--Hasse logarithm term
`x^(p^r) / p^r`. -/
noncomputable def samePrimeArtinHasseLogTermNumerator (r : ℕ)
    (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K :=
  Classical.choose (samePrimeArtinHasseLogTermData_exists (p := p) (K := K) r hx)

theorem samePrimeArtinHasseLogTermNumerator_spec (r : ℕ)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeArtinHasseLogTermNumerator (p := p) (K := K) r x hx ∈
        (lambdaIdeal p K) ^ samePrimeArtinHasseLogTermOrder (p := p) r ∧
      (p : ValuedIntegerRing p K) ^ r *
          samePrimeArtinHasseLogTermNumerator (p := p) (K := K) r x hx =
        x ^ (p ^ r) :=
  Classical.choose_spec (samePrimeArtinHasseLogTermData_exists (p := p) (K := K) r hx)

/-- The `r`-th same-prime Artin--Hasse logarithm term in
`R / lambda^(N+1)`. -/
noncomputable def samePrimeFiniteArtinHasseLogTerm (N r : ℕ)
    (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
    (samePrimeArtinHasseLogTermNumerator (p := p) (K := K) r x hx)

private theorem quotientNatCastInv_one (N : ℕ) (h : Nat.Coprime 1 p) :
    quotientNatCastInv (p := p) (K := K) N 1 h = 1 :=
  quotientNatCastInv_eq_of_mul_right_eq_one
    (p := p) (K := K) (N := N) (m := 1) h (by simp)

theorem samePrimeNatDivEval_prime_pow_zero_eq_finiteArtinHasseLogTerm
    (N r : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hmem : x ^ (p ^ r) ∈
      (lambdaIdeal p K) ^ ((p ^ r).factorization p * (p - 1) + 0)) :
    samePrimeNatDivEval (p := p) (K := K) N (p ^ r) 0
        (pow_ne_zero r (Fact.out : Nat.Prime p).ne_zero) (x ^ (p ^ r)) hmem =
      samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx := by
  let y : ValuedIntegerRing p K :=
    samePrimeArtinHasseLogTermNumerator (p := p) (K := K) r x hx
  have hfac : (p ^ r).factorization p = r :=
    Nat.factorization_pow_self (Fact.out : Nat.Prime p)
  have hy :
      (p : ValuedIntegerRing p K) ^ (p ^ r).factorization p * y =
        x ^ (p ^ r) := by
    rw [hfac]
    simpa [y] using
      (samePrimeArtinHasseLogTermNumerator_spec (p := p) (K := K) r hx).2
  rw [samePrimeFiniteArtinHasseLogTerm]
  rw [samePrimeNatDivEval_eq_of_spec (p := p) (K := K)
    (N := N) (n := p ^ r) (s := 0)
    (pow_ne_zero r (Fact.out : Nat.Prime p).ne_zero) hmem hy]
  have hord : ordCompl[p] (p ^ r) = 1 :=
    Nat.ordCompl_self_pow (Fact.out : Nat.Prime p)
  have hinv :
      quotientNatCastInv (p := p) (K := K) N (ordCompl[p] (p ^ r))
          (samePrimeFiniteLog_ordCompl_coprime (p := p)
            (pow_ne_zero r (Fact.out : Nat.Prime p).ne_zero)) = 1 := by
    refine quotientNatCastInv_eq_of_mul_right_eq_one
      (p := p) (K := K) (N := N) (m := ordCompl[p] (p ^ r))
      (samePrimeFiniteLog_ordCompl_coprime (p := p)
        (pow_ne_zero r (Fact.out : Nat.Prime p).ne_zero)) ?_
    rw [hord]
    simp
  rw [hinv, mul_one]

/-- Multiplying the same-prime Artin--Hasse term by `p^r` recovers
`x^(p^r)` in the finite quotient. -/
theorem samePrimeFiniteArtinHasseLogTerm_natCast_prime_pow_mul_eq_mk
    (N r : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        ((p : ValuedIntegerRing p K) ^ r) *
      samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx =
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) (x ^ (p ^ r)) := by
  rw [samePrimeFiniteArtinHasseLogTerm, ← map_mul,
    (samePrimeArtinHasseLogTermNumerator_spec (p := p) (K := K) r hx).2]

theorem samePrimeFiniteArtinHasseLogTerm_mem_map_lambdaIdeal_pow
    (N r : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx ∈
      Ideal.map (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
        ((lambdaIdeal p K) ^ samePrimeArtinHasseLogTermOrder (p := p) r) :=
  Ideal.mem_map_of_mem (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
    (samePrimeArtinHasseLogTermNumerator_spec (p := p) (K := K) r hx).1

theorem samePrimeFiniteArtinHasseLogTerm_eq_zero_of_succ_le
    {N r : ℕ} {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (horder : N + 1 ≤ samePrimeArtinHasseLogTermOrder (p := p) r) :
    samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx = 0 := by
  rw [samePrimeFiniteArtinHasseLogTerm]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.pow_le_pow_right horder
      (samePrimeArtinHasseLogTermNumerator_spec (p := p) (K := K) r hx).1)

theorem samePrimeFiniteArtinHasseLogTerm_eq_zero_of_succ_le_index
    {N r : ℕ} {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hr : N + 1 ≤ r) :
    samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx = 0 :=
  samePrimeFiniteArtinHasseLogTerm_eq_zero_of_succ_le (p := p) (K := K) hx
    (hr.trans (le_samePrimeArtinHasseLogTermOrder (p := p) r))

set_option linter.style.longLine false in
/-- The attached `samePrimeNatDivEval`-sum of a pointwise difference `num - target`
splits as the difference of the two attached eval-sums, using additivity of
`samePrimeNatDivEval` on the shared membership level. -/
private theorem samePrimeNatDivEval_attach_sum_sub_eq
    (N d : ℕ) (num target : ℕ → ValuedIntegerRing p K)
    (hnum0 : ∀ a : {n // n ∈ Finset.Icc 1 d},
      num a.1 ∈ (lambdaIdeal p K) ^ (a.1.factorization p * (p - 1) + 0))
    (htarget0 : ∀ a : {n // n ∈ Finset.Icc 1 d},
      target a.1 ∈ (lambdaIdeal p K) ^ (a.1.factorization p * (p - 1) + 0))
    (hz0 : ∀ n ∈ Finset.Icc 1 d,
      (num n - target n) ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + 0)) :
    (∑ a ∈ (Finset.Icc 1 d).attach,
      samePrimeNatDivEval (p := p) (K := K) N a.1 0
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (num a.1 - target a.1) (hz0 a.1 a.2))
      =
    (∑ a ∈ (Finset.Icc 1 d).attach,
      samePrimeNatDivEval (p := p) (K := K) N a.1 0
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (num a.1) (hnum0 a)) -
    (∑ a ∈ (Finset.Icc 1 d).attach,
      samePrimeNatDivEval (p := p) (K := K) N a.1 0
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (target a.1) (htarget0 a)) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro a _ha
  have han : a.1 ≠ 0 := by
    have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
    exact Nat.ne_zero_of_lt ha1
  have hneg : -target a.1 ∈
      (lambdaIdeal p K) ^ (a.1.factorization p * (p - 1) + 0) :=
    ((lambdaIdeal p K) ^ (a.1.factorization p * (p - 1) + 0)).neg_mem (htarget0 a)
  have hz_add : num a.1 - target a.1 = num a.1 + -target a.1 := by
    rw [sub_eq_add_neg]
  have hz_add_mem :
      num a.1 + -target a.1 ∈
        (lambdaIdeal p K) ^ (a.1.factorization p * (p - 1) + 0) := by
    simpa [← hz_add] using hz0 a.1 a.2
  have hadd :
      samePrimeNatDivEval (p := p) (K := K) N a.1 0 han
          (num a.1 + -target a.1) hz_add_mem =
        samePrimeNatDivEval (p := p) (K := K) N a.1 0 han
            (num a.1) (hnum0 a) +
          samePrimeNatDivEval (p := p) (K := K) N a.1 0 han
            (-target a.1) hneg :=
    samePrimeNatDivEval_add (p := p) (K := K) (N := N)
      (n := a.1) (s := 0) han (hnum0 a) hneg hz_add_mem
  calc
    samePrimeNatDivEval (p := p) (K := K) N a.1 0 han
        (num a.1 - target a.1) (hz0 a.1 a.2)
        =
      samePrimeNatDivEval (p := p) (K := K) N a.1 0 han
        (num a.1 + -target a.1) hz_add_mem :=
        samePrimeNatDivEval_eq_of_eq (p := p) (K := K) han hz_add
          (hz0 a.1 a.2) hz_add_mem
    _ =
      samePrimeNatDivEval (p := p) (K := K) N a.1 0 han
          (num a.1) (hnum0 a) +
        samePrimeNatDivEval (p := p) (K := K) N a.1 0 han
          (-target a.1) hneg := hadd
    _ =
      samePrimeNatDivEval (p := p) (K := K) N a.1 0 han
          (num a.1) (hnum0 a) -
        samePrimeNatDivEval (p := p) (K := K) N a.1 0 han
          (target a.1) (htarget0 a) := by
        rw [samePrimeNatDivEval_neg (p := p) (K := K) han (htarget0 a) hneg]
        ring

set_option linter.style.longLine false in
/-- The attached `samePrimeNatDivEval`-sum of the indicator `target` supported at
`n = p ^ r` (value `x ^ (p ^ r)`) collapses to the single nonzero term and equals
the same-prime finite Artin--Hasse log term. -/
private theorem samePrimeNatDivEval_attach_sum_target_eq_finiteArtinHasseLogTerm
    (N r : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (htarget0 : ∀ a : {n // n ∈ Finset.Icc 1 (p ^ r)},
      (if a.1 = p ^ r then x ^ (p ^ r) else 0) ∈
        (lambdaIdeal p K) ^ (a.1.factorization p * (p - 1) + 0)) :
    (∑ a ∈ (Finset.Icc 1 (p ^ r)).attach,
      samePrimeNatDivEval (p := p) (K := K) N a.1 0
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (if a.1 = p ^ r then x ^ (p ^ r) else 0) (htarget0 a)) =
      samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx := by
  have hd_ne : p ^ r ≠ 0 := pow_ne_zero r (Fact.out : Nat.Prime p).ne_zero
  have hxd : x ^ (p ^ r) ∈ (lambdaIdeal p K) ^ (p ^ r) := Ideal.pow_mem_pow hx (p ^ r)
  let a0 : {n // n ∈ Finset.Icc 1 (p ^ r)} := ⟨p ^ r, Finset.mem_Icc.mpr ⟨by
    have hdpos : 0 < p ^ r := Nat.pos_of_ne_zero hd_ne
    exact Nat.succ_le_of_lt hdpos, le_rfl⟩⟩
  let targetEval : {n // n ∈ Finset.Icc 1 (p ^ r)} →
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) := fun a ↦
    samePrimeNatDivEval (p := p) (K := K) N a.1 0
      (by
        have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
        exact Nat.ne_zero_of_lt ha1)
      (if a.1 = p ^ r then x ^ (p ^ r) else 0) (htarget0 a)
  change (∑ a ∈ (Finset.Icc 1 (p ^ r)).attach, targetEval a) =
    samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx
  calc
    (∑ a ∈ (Finset.Icc 1 (p ^ r)).attach, targetEval a) = targetEval a0 := by
      refine Finset.sum_eq_single (s := (Finset.Icc 1 (p ^ r)).attach)
        (a := a0) (f := targetEval) ?zero ?not_mem
      · intro a _ha hne
        dsimp [targetEval]
        have han : a.1 ≠ 0 := by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1
        have ha_ne : a.1 ≠ p ^ r := fun ha ↦
          hne (Subtype.ext ha)
        have htarget_zero : (if a.1 = p ^ r then x ^ (p ^ r) else 0) = 0 := by
          simp [ha_ne]
        have hzero :
            (0 : ValuedIntegerRing p K) ∈
              (lambdaIdeal p K) ^ (a.1.factorization p * (p - 1) + 0) :=
          zero_mem _
        calc
          samePrimeNatDivEval (p := p) (K := K) N a.1 0
              (by
                have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
                exact Nat.ne_zero_of_lt ha1)
              (if a.1 = p ^ r then x ^ (p ^ r) else 0) (htarget0 a)
              =
            samePrimeNatDivEval (p := p) (K := K) N a.1 0 han 0 hzero :=
              samePrimeNatDivEval_eq_of_eq (p := p) (K := K) han
                htarget_zero (htarget0 a) hzero
          _ = 0 :=
              samePrimeNatDivEval_zero (p := p) (K := K)
                (N := N) (n := a.1) (s := 0) han hzero
      · intro ha0
        simp [a0] at ha0
    _ = samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx := by
      dsimp [targetEval]
      have hden : (p ^ r).factorization p * (p - 1) ≤ p ^ r :=
        samePrimeFiniteArtinHasse_den_exponent_le (p := p) hd_ne le_rfl
      have htarget0_d :
          x ^ (p ^ r) ∈
            (lambdaIdeal p K) ^ ((p ^ r).factorization p * (p - 1) + 0) :=
        Ideal.pow_le_pow_right hden hxd
      calc
        samePrimeNatDivEval (p := p) (K := K) N a0.1 0
            (by
              have ha1 : 1 ≤ a0.1 := (Finset.mem_Icc.mp a0.2).1
              exact Nat.ne_zero_of_lt ha1)
            (if a0.1 = p ^ r then x ^ (p ^ r) else 0) (htarget0 a0)
            =
          samePrimeNatDivEval (p := p) (K := K) N (p ^ r) 0 hd_ne
            (x ^ (p ^ r)) htarget0_d :=
            samePrimeNatDivEval_eq_of_eq (p := p) (K := K) hd_ne
              (by simp [a0]) (htarget0 a0) htarget0_d
        _ =
          samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx :=
            samePrimeNatDivEval_prime_pow_zero_eq_finiteArtinHasseLogTerm
              (p := p) (K := K) N r hx htarget0_d

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in
-- This is the same-prime port of the homogeneous `p^r` slice comparison; it
-- expands three attached finite sums and transports finite-log additivity.
theorem samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_logTerm_of_factorial_weighted_sub_pow_mem
    (N r : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hclear :
      (∑ n ∈ Finset.Icc 1 (p ^ r),
        (((p ^ r).factorial / n : ℕ) : ValuedIntegerRing p K) *
          (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) N n (p ^ r) x -
            if n = p ^ r then x ^ (p ^ r) else 0)) ∈
        (lambdaIdeal p K) ^ ((p ^ r).factorial.factorization p * (p - 1) + (N + 1))) :
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
        (p := p) (K := K) N (p ^ r) x hx =
      samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx := by
  classical
  let d : ℕ := p ^ r
  let num : ℕ → ValuedIntegerRing p K := fun n ↦
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
      (p := p) (K := K) N n d x
  let target : ℕ → ValuedIntegerRing p K := fun n ↦ if n = d then x ^ d else 0
  let z : ℕ → ValuedIntegerRing p K := fun n ↦ num n - target n
  have hd_ne : d ≠ 0 := pow_ne_zero r (Fact.out : Nat.Prime p).ne_zero
  have hxd : x ^ d ∈ (lambdaIdeal p K) ^ d := Ideal.pow_mem_pow hx d
  have hz0 : ∀ n ∈ Finset.Icc 1 d,
      z n ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + 0) := by
    intro n hnI
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    have hnd : n ≤ d := (Finset.mem_Icc.mp hnI).2
    have hden : n.factorization p * (p - 1) ≤ d :=
      samePrimeFiniteArtinHasse_den_exponent_le (p := p)
        (Nat.ne_zero_of_lt hn1) hnd
    have hnum_d : num n ∈ (lambdaIdeal p K) ^ d := by
      simpa [num] using
        samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator_mem_lambdaIdeal_pow
          (p := p) (K := K) N n d hx
    have htarget_d : target n ∈ (lambdaIdeal p K) ^ d := by
      by_cases hn : n = d
      · simp [target, hn, hxd]
      · simp [target, hn]
    have hz_d : z n ∈ (lambdaIdeal p K) ^ d := by
      simpa [z, sub_eq_add_neg] using
        ((lambdaIdeal p K) ^ d).add_mem hnum_d
          (((lambdaIdeal p K) ^ d).neg_mem htarget_d)
    simpa using Ideal.pow_le_pow_right hden hz_d
  have htransport :
      (∑ a ∈ (Finset.Icc 1 d).attach,
        samePrimeNatDivEval (p := p) (K := K) N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (z a.1) (hz0 a.1 a.2)) = 0 :=
    samePrimeNatDivEval_Icc_sum_eq_zero_of_factorial_weighted_sum_mem_lambdaIdeal_pow
      (p := p) (K := K) (N := N) (d := d) (s := 0) (t := N + 1) z hz0
      (by simpa [d, z, num, target] using hclear) le_rfl
  have hnum0 : ∀ a : {n // n ∈ Finset.Icc 1 d},
      num a.1 ∈ (lambdaIdeal p K) ^ (a.1.factorization p * (p - 1) + 0) := by
    intro a
    have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
    have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
    have hden : a.1.factorization p * (p - 1) ≤ d :=
      samePrimeFiniteArtinHasse_den_exponent_le (p := p)
        (Nat.ne_zero_of_lt ha1) had
    simpa [num] using
      Ideal.pow_le_pow_right hden
        (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator_mem_lambdaIdeal_pow
          (p := p) (K := K) N a.1 d hx)
  have htarget0 : ∀ a : {n // n ∈ Finset.Icc 1 d},
      target a.1 ∈ (lambdaIdeal p K) ^ (a.1.factorization p * (p - 1) + 0) := by
    intro a
    by_cases ha : a.1 = d
    · have hden : a.1.factorization p * (p - 1) ≤ d := by
        simpa [ha] using
          samePrimeFiniteArtinHasse_den_exponent_le (p := p) hd_ne le_rfl
      simpa [target, ha] using Ideal.pow_le_pow_right hden hxd
    · simp [target, ha]
  have heval_sub :
      (∑ a ∈ (Finset.Icc 1 d).attach,
        samePrimeNatDivEval (p := p) (K := K) N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (z a.1) (hz0 a.1 a.2))
        =
      (∑ a ∈ (Finset.Icc 1 d).attach,
        samePrimeNatDivEval (p := p) (K := K) N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (num a.1) (hnum0 a)) -
      (∑ a ∈ (Finset.Icc 1 d).attach,
        samePrimeNatDivEval (p := p) (K := K) N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (target a.1) (htarget0 a)) :=
    samePrimeNatDivEval_attach_sum_sub_eq (p := p) (K := K) N d num target
      hnum0 htarget0 hz0
  have htarget_sum :
      (∑ a ∈ (Finset.Icc 1 d).attach,
        samePrimeNatDivEval (p := p) (K := K) N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (target a.1) (htarget0 a)) =
        samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx :=
    samePrimeNatDivEval_attach_sum_target_eq_finiteArtinHasseLogTerm
      (p := p) (K := K) N r hx htarget0
  have hdegree :
      samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
          (p := p) (K := K) N d x hx =
      (∑ a ∈ (Finset.Icc 1 d).attach,
        samePrimeNatDivEval (p := p) (K := K) N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (num a.1) (hnum0 a)) := by
    simpa [num] using
      samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_eval_sum
        (p := p) (K := K) N d hx
  rw [← sub_eq_zero]
  calc
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
          (p := p) (K := K) N d x hx -
        samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx
        =
      (∑ a ∈ (Finset.Icc 1 d).attach,
        samePrimeNatDivEval (p := p) (K := K) N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (num a.1) (hnum0 a)) -
      (∑ a ∈ (Finset.Icc 1 d).attach,
        samePrimeNatDivEval (p := p) (K := K) N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (target a.1) (htarget0 a)) := by
        rw [hdegree, htarget_sum]
    _ =
      ∑ a ∈ (Finset.Icc 1 d).attach,
        samePrimeNatDivEval (p := p) (K := K) N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (z a.1) (hz0 a.1 a.2) := by
        rw [heval_sub]
    _ = 0 := htransport

set_option linter.style.longLine false in
theorem samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_logTerm
    (N r : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
        (p := p) (K := K) N (p ^ r) x hx =
      samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx :=
  samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_logTerm_of_factorial_weighted_sub_pow_mem
    (p := p) (K := K) N r hx
    (by
      simpa [samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator] using
        samePrimeFiniteArtinHasseLogHomogeneousNumerator_factorial_weighted_sub_pow_mem_lambdaIdeal_pow
          (p := p) (K := K) N r hx)


end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular

end
