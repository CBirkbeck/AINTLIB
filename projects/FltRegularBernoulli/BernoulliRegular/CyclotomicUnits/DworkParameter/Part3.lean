module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.Part2

/-!
# The same-prime finite logarithm and its additivity

This file defines the ordinary finite logarithm `samePrimeFiniteLog` on principal units
`1 + x` with `x` in the lambda ideal, valued in the truncation
`ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)`, and develops the bookkeeping needed
for its additivity over products.

## Main definitions

* `samePrimeFiniteLog`: the truncated finite logarithm of `1 + x`.
* `samePrimeFiniteLogLocalizedPolynomial`: the same value re-expressed through the
  degree-indexed localized evaluator.
* `samePrimeFiniteLogProductHomogeneousGrid`: the homogeneous grid used to compare the
  logarithm of a product against the sum of the logarithms.

## Main results

* `samePrimeFiniteLog_eq_samePrimeFiniteLogLocalizedPolynomial`: the two presentations agree.
* `samePrimeFiniteLog_eq_of_sub_mem`: the logarithm depends only on `x` modulo
  `(lambdaIdeal p K) ^ (N + 1)`.
* `samePrimeFiniteLogAdditivity_degree_sum_eq_zero`: the product-versus-sum discrepancy
  vanishes degree by degree, the key input to additivity.
-/

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

theorem samePrimeFiniteLogTerm_eq_zero_of_cutoff_le {N n : ℕ}
    (hn : samePrimeFiniteLogCutoff (p := p) N ≤ n)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLogTerm (p := p) (K := K) N n x hx = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp
  rcases (Ideal.mem_map_iff_of_surjective
      (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
      Ideal.Quotient.mk_surjective).1
      (samePrimeFiniteLogTerm_mem_map_lambdaIdeal_pow
        (p := p) (K := K) hn0 hx) with
    ⟨y, hy, hyq⟩
  rw [← hyq, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_le_pow_right
    (succ_le_samePrimeFiniteLogTermOrder_of_cutoff_le (p := p) hn) hy

/-- The ordinary finite logarithm on `1 + x`, for `x` in the lambda ideal. -/
noncomputable def samePrimeFiniteLog (N : ℕ)
    (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  ∑ n ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
    samePrimeFiniteLogTerm (p := p) (K := K) N n x hx

theorem samePrimeFiniteLog_eq_of_eq {N : ℕ}
    {x y : ValuedIntegerRing p K} (hxy : x = y)
    (hx : x ∈ lambdaIdeal p K) (hy : y ∈ lambdaIdeal p K) :
    samePrimeFiniteLog (p := p) (K := K) N x hx =
      samePrimeFiniteLog (p := p) (K := K) N y hy := by
  subst y
  rfl

theorem pow_sub_pow_mem_lambdaIdeal_pow_add {N n : ℕ} (hn : n ≠ 0)
    {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K)
    (hxy : x - y ∈ (lambdaIdeal p K) ^ (N + 1)) :
    x ^ n - y ^ n ∈ (lambdaIdeal p K) ^ (N + n) := by
  classical
  let g : ValuedIntegerRing p K :=
    ∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)
  have hg : g ∈ (lambdaIdeal p K) ^ (n - 1) := by
    refine Ideal.sum_mem _ ?_
    intro i hi
    have hix : x ^ i ∈ (lambdaIdeal p K) ^ i := Ideal.pow_mem_pow hx i
    have hiy : y ^ (n - 1 - i) ∈ (lambdaIdeal p K) ^ (n - 1 - i) :=
      Ideal.pow_mem_pow hy (n - 1 - i)
    have hmul : x ^ i * y ^ (n - 1 - i) ∈
        (lambdaIdeal p K) ^ i * (lambdaIdeal p K) ^ (n - 1 - i) :=
      Ideal.mul_mem_mul hix hiy
    rw [← pow_add] at hmul
    have hidx : i + (n - 1 - i) = n - 1 := by
      have hi_lt : i < n := Finset.mem_range.mp hi
      lia
    simpa [hidx] using hmul
  have hprod : (x - y) * g ∈ (lambdaIdeal p K) ^ (N + n) := by
    have hmul : (x - y) * g ∈
        (lambdaIdeal p K) ^ (N + 1) * (lambdaIdeal p K) ^ (n - 1) :=
      Ideal.mul_mem_mul hxy hg
    rw [← pow_add] at hmul
    have hidx : (N + 1) + (n - 1) = N + n := by lia
    simpa [hidx] using hmul
  have hgeom : (x - y) * g = x ^ n - y ^ n := by
    change (x - y) *
        (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) = x ^ n - y ^ n
    rw [mul_comm]
    exact geom_sum₂_mul x y n
  simpa [g, hgeom] using hprod

theorem samePrimeFiniteLogTermCore_eq_of_sub_mem {N n : ℕ} (hn : n ≠ 0)
    {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K)
    (hxy : x - y ∈ (lambdaIdeal p K) ^ (N + 1)) :
    samePrimeFiniteLogTermCore (p := p) (K := K) N n x hx =
      samePrimeFiniteLogTermCore (p := p) (K := K) N n y hy := by
  let den : ℕ := n.factorization p * (p - 1)
  let s : ℕ := samePrimeFiniteLogTermOrder (p := p) n
  have hxpow : x ^ n ∈ (lambdaIdeal p K) ^ (den + s) := by
    simpa [den, s, factorization_mul_pred_add_samePrimeFiniteLogTermOrder
        (p := p) hn] using
      Ideal.pow_mem_pow hx n
  have hypow : y ^ n ∈ (lambdaIdeal p K) ^ (den + s) := by
    simpa [den, s, factorization_mul_pred_add_samePrimeFiniteLogTermOrder
        (p := p) hn] using
      Ideal.pow_mem_pow hy n
  have hdiff_s : x ^ n - y ^ n ∈ (lambdaIdeal p K) ^ (den + s) :=
    ((lambdaIdeal p K) ^ (den + s)).sub_mem hxpow hypow
  have hpowdiff : x ^ n - y ^ n ∈ (lambdaIdeal p K) ^ (N + n) :=
    pow_sub_pow_mem_lambdaIdeal_pow_add (p := p) (K := K) hn hx hy hxy
  have hdiff_big : x ^ n - y ^ n ∈ (lambdaIdeal p K) ^ (den + (N + 1)) := by
    have horder : 1 ≤ s := by
      simpa [s] using one_le_samePrimeFiniteLogTermOrder (p := p) hn
    have hle : den + (N + 1) ≤ N + n := by
      have hsum : den + s = n := by
        simpa [den, s] using
          factorization_mul_pred_add_samePrimeFiniteLogTermOrder (p := p) hn
      lia
    exact Ideal.pow_le_pow_right hle hpowdiff
  have hsub_eval :
      samePrimeNatDivEval (p := p) (K := K) N n s hn
          (x ^ n - y ^ n) hdiff_s =
        samePrimeNatDivEval (p := p) (K := K) N n s hn (x ^ n) hxpow -
          samePrimeNatDivEval (p := p) (K := K) N n s hn (y ^ n) hypow := by
    have hneg : -y ^ n ∈ (lambdaIdeal p K) ^ (den + s) :=
      ((lambdaIdeal p K) ^ (den + s)).neg_mem hypow
    have hsum_s : x ^ n + -y ^ n ∈ (lambdaIdeal p K) ^ (den + s) := by
      simpa [sub_eq_add_neg] using hdiff_s
    have hadd := samePrimeNatDivEval_add (p := p) (K := K) (N := N)
      (n := n) (s := s) hn hxpow hneg hsum_s
    rw [samePrimeNatDivEval_neg (p := p) (K := K) (N := N)
      (n := n) (s := s) hn hypow hneg] at hadd
    simpa [sub_eq_add_neg] using hadd
  have hzero_s :
      samePrimeNatDivEval (p := p) (K := K) N n s hn
          (x ^ n - y ^ n) hdiff_s = 0 := by
    rw [samePrimeNatDivEval_eq_of_mem (p := p) (K := K) (N := N)
      (n := n) (s := s) (t := N + 1) hn hdiff_s hdiff_big]
    exact samePrimeNatDivEval_eq_zero_of_succ_le (p := p) (K := K)
      (N := N) (n := n) (s := N + 1) hn hdiff_big le_rfl
  rw [samePrimeFiniteLogTermCore_eq_samePrimeNatDivEval (p := p) (K := K) hn hx,
    samePrimeFiniteLogTermCore_eq_samePrimeNatDivEval (p := p) (K := K) hn hy]
  exact sub_eq_zero.mp (by rw [← hsub_eval, hzero_s])

theorem samePrimeFiniteLogTerm_eq_of_sub_mem {N n : ℕ}
    {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K)
    (hxy : x - y ∈ (lambdaIdeal p K) ^ (N + 1)) :
    samePrimeFiniteLogTerm (p := p) (K := K) N n x hx =
      samePrimeFiniteLogTerm (p := p) (K := K) N n y hy := by
  by_cases hn : n = 0
  · subst n
    simp
  simp [samePrimeFiniteLogTerm,
    samePrimeFiniteLogTermCore_eq_of_sub_mem (p := p) (K := K) hn hx hy hxy]

theorem samePrimeFiniteLog_eq_of_sub_mem {N : ℕ}
    {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K)
    (hxy : x - y ∈ (lambdaIdeal p K) ^ (N + 1)) :
    samePrimeFiniteLog (p := p) (K := K) N x hx =
      samePrimeFiniteLog (p := p) (K := K) N y hy := by
  classical
  unfold samePrimeFiniteLog
  exact Finset.sum_congr rfl fun n _hn =>
    samePrimeFiniteLogTerm_eq_of_sub_mem (p := p) (K := K) hx hy hxy

/-- The ordinary finite logarithm re-expressed through the degree-indexed
localized evaluator.  This form is used by the homogeneous additivity proof. -/
noncomputable def samePrimeFiniteLogLocalizedTerm (N n : ℕ)
    (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  if hn : n = 0 then 0 else
    ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
      samePrimeNatDivEvalAtDegree (p := p) (K := K) N n n hn
        (x ^ n) (Ideal.pow_mem_pow hx n)
        (by
          have h := Nat.factorization_mul_pred_le_pred
            (ell := p) (n := n) (Fact.out : Nat.Prime p) hn
          lia)

noncomputable def samePrimeFiniteLogLocalizedPolynomial (N : ℕ)
    (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  ∑ n ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
    samePrimeFiniteLogLocalizedTerm (p := p) (K := K) N n x hx

theorem samePrimeFiniteLogTerm_eq_localizedTerm (N n : ℕ)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLogTerm (p := p) (K := K) N n x hx =
      samePrimeFiniteLogLocalizedTerm (p := p) (K := K) N n x hx := by
  by_cases hn : n = 0
  · subst n
    simp [samePrimeFiniteLogLocalizedTerm]
  rw [samePrimeFiniteLogTerm, samePrimeFiniteLogLocalizedTerm, dif_neg hn,
    samePrimeFiniteLogTermCore_eq_samePrimeNatDivEvalAtDegree
      (p := p) (K := K) hn hx]

theorem samePrimeFiniteLog_eq_samePrimeFiniteLogLocalizedPolynomial (N : ℕ)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLog (p := p) (K := K) N x hx =
      samePrimeFiniteLogLocalizedPolynomial (p := p) (K := K) N x hx := by
  classical
  unfold samePrimeFiniteLog samePrimeFiniteLogLocalizedPolynomial
  exact Finset.sum_congr rfl fun n _hn =>
    samePrimeFiniteLogTerm_eq_localizedTerm (p := p) (K := K) N n hx

@[simp]
theorem samePrimeFiniteLog_arg_zero (N : ℕ) :
    samePrimeFiniteLog (p := p) (K := K) N 0
        (zero_mem (lambdaIdeal p K)) = 0 := by
  classical
  unfold samePrimeFiniteLog
  exact Finset.sum_eq_zero fun n _hn =>
    samePrimeFiniteLogTerm_arg_zero (p := p) (K := K) N n

/-- Principal-unit product coordinate:
`(1 + x) * (1 + y) - 1 = x + y + x*y`. -/
def samePrimeFiniteLogProductCoord
    (x y : ValuedIntegerRing p K) : ValuedIntegerRing p K :=
  x + y + x * y

theorem samePrimeFiniteLogProductCoord_mem_lambdaIdeal
    {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K) :
    samePrimeFiniteLogProductCoord (p := p) (K := K) x y ∈ lambdaIdeal p K := by
  have hxy : x * y ∈ lambdaIdeal p K :=
    (lambdaIdeal p K).mul_mem_right y hx
  exact (lambdaIdeal p K).add_mem ((lambdaIdeal p K).add_mem hx hy) hxy

/-- Homogeneous bookkeeping polynomial for `x + y + x*y`, where `x` and `y`
have degree `1` and `x*y` has degree `2`. -/
def samePrimeFiniteLogProductArgPoly
    (x y : ValuedIntegerRing p K) : Polynomial (ValuedIntegerRing p K) :=
  Polynomial.monomial 1 (x + y) + Polynomial.monomial 2 (x * y)

theorem samePrimeFiniteLogProductArgPoly_eval_one
    (x y : ValuedIntegerRing p K) :
    (samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y).eval 1 =
      samePrimeFiniteLogProductCoord (p := p) (K := K) x y := by
  simp [samePrimeFiniteLogProductArgPoly, samePrimeFiniteLogProductCoord,
    Polynomial.eval_monomial]

theorem samePrimeFiniteLogProductArgPoly_pow_eval_one
    (n : ℕ) (x y : ValuedIntegerRing p K) :
    ((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).eval 1 =
      (samePrimeFiniteLogProductCoord (p := p) (K := K) x y) ^ n := by
  simp [samePrimeFiniteLogProductArgPoly_eval_one, Polynomial.eval_pow]

theorem samePrimeFiniteLogProductArgPoly_coeff_mem_lambdaIdeal_pow
    {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K) (d : ℕ) :
    (samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y).coeff d ∈
      (lambdaIdeal p K) ^ d := by
  by_cases h1 : d = 1
  · subst d
    simpa [samePrimeFiniteLogProductArgPoly, Polynomial.coeff_monomial] using
      (lambdaIdeal p K).add_mem hx hy
  by_cases h2 : d = 2
  · subst d
    have hxy : x * y ∈ (lambdaIdeal p K) ^ 2 := by
      have hmul : x * y ∈ lambdaIdeal p K * lambdaIdeal p K :=
        Ideal.mul_mem_mul hx hy
      simpa [pow_two] using hmul
    simpa [samePrimeFiniteLogProductArgPoly, Polynomial.coeff_monomial] using hxy
  have hne1 : 1 ≠ d := fun h => h1 h.symm
  have hne2 : 2 ≠ d := fun h => h2 h.symm
  simp [samePrimeFiniteLogProductArgPoly, Polynomial.coeff_monomial, hne1, hne2]

theorem samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
    {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K) (n d : ℕ) :
    ((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d ∈
      (lambdaIdeal p K) ^ d := by
  induction n generalizing d with
  | zero =>
      by_cases hd : d = 0
      · subst d
        simp
      · simp [Polynomial.coeff_one, hd]
  | succ n ih =>
      rw [pow_succ, Polynomial.coeff_mul]
      refine Ideal.sum_mem _ ?_
      intro a ha
      have hsum : a.1 + a.2 = d := by
        simpa using (Finset.mem_antidiagonal.mp ha)
      have hleft :
          ((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff a.1 ∈
            (lambdaIdeal p K) ^ a.1 :=
        ih a.1
      have hright :
          (samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y).coeff a.2 ∈
            (lambdaIdeal p K) ^ a.2 :=
        samePrimeFiniteLogProductArgPoly_coeff_mem_lambdaIdeal_pow
          (p := p) (K := K) hx hy a.2
      have hmul :
          ((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff a.1 *
              (samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y).coeff a.2 ∈
            (lambdaIdeal p K) ^ (a.1 + a.2) := by
        simpa [pow_add] using Ideal.mul_mem_mul hleft hright
      simpa [hsum] using hmul

theorem coeff_pow_coe_eq_zero_of_lt_of_constantCoeff_eq_zero
    {A : Type*} [CommRing A] (P : Polynomial A) (hP0 : P.coeff 0 = 0)
    {n d : ℕ} (hdn : d < n) :
    PowerSeries.coeff d ((P : PowerSeries A) ^ n) = 0 := by
  have hconst : PowerSeries.constantCoeff (P : PowerSeries A) = 0 := by
    simpa [Polynomial.constantCoeff_coe] using hP0
  have hle : (n : ℕ∞) ≤ ((P : PowerSeries A) ^ n).order :=
    PowerSeries.le_order_pow_of_constantCoeff_eq_zero n hconst
  exact PowerSeries.coeff_of_lt_order d ((ENat.coe_lt_coe.mpr hdn).trans_le hle)

theorem coeff_subst_log_coe_eq_sum_Icc
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (P : Polynomial A) (hP0 : P.coeff 0 = 0) (d : ℕ) :
    PowerSeries.coeff d (PowerSeries.subst (P : PowerSeries A) (PowerSeries.log A)) =
      ∑ n ∈ Finset.Icc 1 d,
        algebraMap ℚ A (((-1 : ℚ) ^ (n + 1)) / n) *
          PowerSeries.coeff d ((P : PowerSeries A) ^ n) := by
  classical
  have hconst : PowerSeries.constantCoeff (P : PowerSeries A) = 0 := by
    simpa [Polynomial.constantCoeff_coe] using hP0
  have hsubst : PowerSeries.HasSubst (P : PowerSeries A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hconst
  rw [PowerSeries.coeff_subst' hsubst, finsum_eq_sum_of_support_subset]
  · refine Finset.sum_congr rfl ?_
    intro n hn
    have hn0 : n ≠ 0 := by
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact Nat.ne_zero_of_lt hn1
    simp [PowerSeries.coeff_log, hn0, smul_eq_mul]
  · rw [Function.support_subset_iff]
    intro n hnmem
    by_contra hnI
    by_cases hn0 : n = 0
    · subst n
      simp at hnmem
    · have hdn : d < n := by
        by_contra hdn
        have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
        have hnd : n ≤ d := by lia
        exact hnI (Finset.mem_Icc.mpr ⟨hn1, hnd⟩)
      have hcoeff := coeff_pow_coe_eq_zero_of_lt_of_constantCoeff_eq_zero P hP0 hdn
      simp [hcoeff] at hnmem

theorem coeff_coe_map_pow {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (P : Polynomial A) (n d : ℕ) :
    PowerSeries.coeff d (((P.map f : Polynomial B) : PowerSeries B) ^ n) =
      f (((P ^ n).coeff d)) := by
  rw [← Polynomial.coe_pow, Polynomial.coeff_coe, ← Polynomial.map_pow, Polynomial.coeff_map]

def samePrimeFormalProductArgPoly
    (x y : ValuedCompletion p K) : Polynomial (ValuedCompletion p K) :=
  Polynomial.X * Polynomial.C x + Polynomial.X * Polynomial.C y +
    Polynomial.X ^ 2 * Polynomial.C (x * y)

theorem samePrimeFormalProductArgPoly_coe (x y : ValuedCompletion p K) :
    ((samePrimeFormalProductArgPoly (p := p) (K := K) x y :
      Polynomial (ValuedCompletion p K)) : PowerSeries (ValuedCompletion p K)) =
      PowerSeries.X * PowerSeries.C x +
        PowerSeries.X * PowerSeries.C y +
        PowerSeries.X ^ 2 * PowerSeries.C (x * y) := by
  simp [samePrimeFormalProductArgPoly]
  ring_nf

theorem samePrimeFiniteLogProductArgPoly_map_eq_formal
    (x y : ValuedIntegerRing p K) :
    (samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y).map
        (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K)) =
      samePrimeFormalProductArgPoly (p := p) (K := K)
        (x : ValuedCompletion p K) (y : ValuedCompletion p K) := by
  simp [samePrimeFiniteLogProductArgPoly, samePrimeFormalProductArgPoly,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  ring_nf

theorem samePrimeFiniteLogProductArgPoly_coe_eq_formal
    (x y : ValuedIntegerRing p K) :
    ((((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y).map
        (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K)) :
          Polynomial (ValuedCompletion p K)) : PowerSeries (ValuedCompletion p K))) =
      PowerSeries.X * PowerSeries.C (x : ValuedCompletion p K) +
        PowerSeries.X * PowerSeries.C (y : ValuedCompletion p K) +
        PowerSeries.X ^ 2 * PowerSeries.C
          ((x * y : ValuedIntegerRing p K) : ValuedCompletion p K) := by
  rw [samePrimeFiniteLogProductArgPoly_map_eq_formal]
  exact samePrimeFormalProductArgPoly_coe (p := p) (K := K)
    (x : ValuedCompletion p K) (y : ValuedCompletion p K)

def samePrimeFiniteLogAdditivityNumerator
    (x y : ValuedIntegerRing p K) (d n : ℕ) : ValuedIntegerRing p K :=
  ((-1 : ValuedIntegerRing p K) ^ (n + 1)) *
    (((((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d +
      -(((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x 0) ^ n).coeff d)) +
      -(((samePrimeFiniteLogProductArgPoly (p := p) (K := K) y 0) ^ n).coeff d)))

theorem samePrimeFiniteLogAdditivityNumerator_mem_lambdaIdeal_pow
    {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K) (d n : ℕ) :
    samePrimeFiniteLogAdditivityNumerator (p := p) (K := K) x y d n ∈
      (lambdaIdeal p K) ^ d := by
  have hprod :
      ((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d ∈
        (lambdaIdeal p K) ^ d :=
    samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
      (p := p) (K := K) hx hy n d
  have hxlin :
      ((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x 0) ^ n).coeff d ∈
        (lambdaIdeal p K) ^ d :=
    samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
      (p := p) (K := K) hx (zero_mem (lambdaIdeal p K)) n d
  have hylin :
      ((samePrimeFiniteLogProductArgPoly (p := p) (K := K) y 0) ^ n).coeff d ∈
        (lambdaIdeal p K) ^ d :=
    samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
      (p := p) (K := K) hy (zero_mem (lambdaIdeal p K)) n d
  exact Ideal.mul_mem_left _ _
    (((lambdaIdeal p K) ^ d).add_mem
      (((lambdaIdeal p K) ^ d).add_mem hprod (((lambdaIdeal p K) ^ d).neg_mem hxlin))
      (((lambdaIdeal p K) ^ d).neg_mem hylin))

theorem samePrimeFiniteLogProductArgPoly_coeff_zero
    (x y : ValuedIntegerRing p K) :
    (samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y).coeff 0 = 0 := by
  simp [samePrimeFiniteLogProductArgPoly, Polynomial.coeff_monomial]

theorem samePrimeFiniteLogProductArgPoly_map_coeff_zero
    (x y : ValuedIntegerRing p K) :
    ((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y).map
        (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))).coeff 0 = 0 := by
  simp [Polynomial.coeff_map, samePrimeFiniteLogProductArgPoly_coeff_zero]

theorem samePrimeFiniteLogProductArgPoly_pow_coeff_eq_zero_of_lt
    (x y : ValuedIntegerRing p K) {n d : ℕ} (hdn : d < n) :
    ((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d = 0 := by
  have h :=
    coeff_pow_coe_eq_zero_of_lt_of_constantCoeff_eq_zero
      (samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y)
      (samePrimeFiniteLogProductArgPoly_coeff_zero (p := p) (K := K) x y) hdn
  simpa [← Polynomial.coe_pow, Polynomial.coeff_coe] using h

theorem samePrimeFiniteLogAdditivity_rational_sum_eq_zero
    (x y : ValuedIntegerRing p K) (d : ℕ) :
    (∑ n ∈ Finset.Icc 1 d,
      algebraMap ℚ (ValuedCompletion p K) (((-1 : ℚ) ^ (n + 1)) / n) *
        (((algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
            (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d) -
          (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
            (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x 0) ^ n).coeff d)) -
          (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
            (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) y 0) ^ n).coeff d))) = 0 := by
  classical
  let Pxy : Polynomial (ValuedCompletion p K) :=
    (samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y).map
      (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
  let Px : Polynomial (ValuedCompletion p K) :=
    (samePrimeFiniteLogProductArgPoly (p := p) (K := K) x 0).map
      (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
  let Py : Polynomial (ValuedCompletion p K) :=
    (samePrimeFiniteLogProductArgPoly (p := p) (K := K) y 0).map
      (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
  have hxyarg :
      (Pxy : PowerSeries (ValuedCompletion p K)) =
        PowerSeries.X * PowerSeries.C (x : ValuedCompletion p K) +
          PowerSeries.X * PowerSeries.C (y : ValuedCompletion p K) +
          PowerSeries.X ^ 2 *
            PowerSeries.C ((x : ValuedCompletion p K) * (y : ValuedCompletion p K)) := by
    simpa [Pxy, map_mul] using
      samePrimeFiniteLogProductArgPoly_coe_eq_formal (p := p) (K := K) x y
  have hxarg :
      (Px : PowerSeries (ValuedCompletion p K)) =
        PowerSeries.X * PowerSeries.C (x : ValuedCompletion p K) := by
    simpa [Px] using
      samePrimeFiniteLogProductArgPoly_coe_eq_formal (p := p) (K := K) x
        (0 : ValuedIntegerRing p K)
  have hyarg :
      (Py : PowerSeries (ValuedCompletion p K)) =
        PowerSeries.X * PowerSeries.C (y : ValuedCompletion p K) := by
    simpa [Py] using
      samePrimeFiniteLogProductArgPoly_coe_eq_formal (p := p) (K := K) y
        (0 : ValuedIntegerRing p K)
  have hformal :=
    Furtwaengler.FiniteLogFormal.coeff_log_subst_add_add_mul_scaled
      (A := ValuedCompletion p K) (x : ValuedCompletion p K) (y : ValuedCompletion p K) d
  rw [← hxyarg, ← hxarg, ← hyarg] at hformal
  have hPxy0 : Pxy.coeff 0 = 0 := by
    simpa [Pxy] using samePrimeFiniteLogProductArgPoly_map_coeff_zero (p := p) (K := K) x y
  have hPx0 : Px.coeff 0 = 0 := by
    simpa [Px] using
      samePrimeFiniteLogProductArgPoly_map_coeff_zero (p := p) (K := K) x
        (0 : ValuedIntegerRing p K)
  have hPy0 : Py.coeff 0 = 0 := by
    simpa [Py] using
      samePrimeFiniteLogProductArgPoly_map_coeff_zero (p := p) (K := K) y
        (0 : ValuedIntegerRing p K)
  rw [coeff_subst_log_coe_eq_sum_Icc Pxy hPxy0 d,
    coeff_subst_log_coe_eq_sum_Icc Px hPx0 d,
    coeff_subst_log_coe_eq_sum_Icc Py hPy0 d] at hformal
  simp only [Pxy, Px, Py, coeff_coe_map_pow] at hformal
  calc
    (∑ n ∈ Finset.Icc 1 d,
      algebraMap ℚ (ValuedCompletion p K) (((-1 : ℚ) ^ (n + 1)) / n) *
        (((algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
            (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d) -
          (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
            (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x 0) ^ n).coeff d)) -
          (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
            (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) y 0) ^ n).coeff d)))
        =
      (∑ n ∈ Finset.Icc 1 d,
        algebraMap ℚ (ValuedCompletion p K) (((-1 : ℚ) ^ (n + 1)) / n) *
          (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
            (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d)) -
        (∑ n ∈ Finset.Icc 1 d,
          algebraMap ℚ (ValuedCompletion p K) (((-1 : ℚ) ^ (n + 1)) / n) *
            (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
              (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x 0) ^ n).coeff d)) -
        (∑ n ∈ Finset.Icc 1 d,
          algebraMap ℚ (ValuedCompletion p K) (((-1 : ℚ) ^ (n + 1)) / n) *
            (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
              (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) y 0) ^ n).coeff d)) := by
        simp [Finset.sum_sub_distrib, mul_sub]
    _ = 0 := by
        rw [hformal]
        ring

theorem samePrimeFiniteLogAdditivity_factorial_weighted_sum_eq_zero
    (x y : ValuedIntegerRing p K) (d : ℕ) :
    (∑ n ∈ Finset.Icc 1 d,
      ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
        samePrimeFiniteLogAdditivityNumerator (p := p) (K := K) x y d n) = 0 := by
  classical
  apply Subtype.ext
  change (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteLogAdditivityNumerator (p := p) (K := K) x y d n) =
    (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K)) 0
  rw [map_zero]
  have hrat := samePrimeFiniteLogAdditivity_rational_sum_eq_zero (p := p) (K := K) x y d
  calc
    (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
            samePrimeFiniteLogAdditivityNumerator (p := p) (K := K) x y d n)
        =
      ∑ n ∈ Finset.Icc 1 d,
        ((d.factorial : ValuedCompletion p K) *
          (algebraMap ℚ (ValuedCompletion p K) (((-1 : ℚ) ^ (n + 1)) / n) *
            (((algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
                (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d) -
              (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
                (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x 0) ^ n).coeff d)) -
              (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
                (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) y 0) ^ n).coeff d)))) := by
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnd : n ≤ d := (Finset.mem_Icc.mp hn).2
        have hdiv :
            ((d.factorial / n : ℕ) : ValuedCompletion p K) =
              (d.factorial : ValuedCompletion p K) / (n : ValuedCompletion p K) :=
          Nat.cast_div_charZero (K := ValuedCompletion p K)
            (Nat.dvd_factorial (Nat.pos_of_ne_zero (Nat.ne_zero_of_lt hn1)) hnd)
        have hn0 : (n : ValuedCompletion p K) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hn1)
        simp [samePrimeFiniteLogAdditivityNumerator, hdiv]
        field_simp [hn0]
        ring
    _ =
      (d.factorial : ValuedCompletion p K) *
        (∑ n ∈ Finset.Icc 1 d,
          algebraMap ℚ (ValuedCompletion p K) (((-1 : ℚ) ^ (n + 1)) / n) *
            (((algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
                (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d) -
              (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
                (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x 0) ^ n).coeff d)) -
              (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K))
                (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) y 0) ^ n).coeff d))) := by
        rw [Finset.mul_sum]
    _ = 0 := by
        rw [hrat, mul_zero]

theorem samePrimeFiniteLogAdditivity_den_exponent_le {n d : ℕ}
    (hn : n ≠ 0) (hnd : n ≤ d) :
    n.factorization p * (p - 1) ≤ d := by
  have h := Nat.factorization_mul_pred_le_pred
    (ell := p) (n := n) (Fact.out : Nat.Prime p) hn
  lia

theorem samePrimeFiniteLogAdditivity_degree_sum_eq_zero (N d : ℕ)
    {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K) :
    (∑ a ∈ (Finset.Icc 1 d).attach,
      samePrimeNatDivEvalAtDegree (p := p) (K := K) N a.1 d
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (samePrimeFiniteLogAdditivityNumerator (p := p) (K := K) x y d a.1)
        (samePrimeFiniteLogAdditivityNumerator_mem_lambdaIdeal_pow
          (p := p) (K := K) hx hy d a.1)
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
          exact samePrimeFiniteLogAdditivity_den_exponent_le (p := p)
            (Nat.ne_zero_of_lt ha1) had)) = 0 := by
  classical
  let z : ℕ → ValuedIntegerRing p K :=
    fun n => samePrimeFiniteLogAdditivityNumerator (p := p) (K := K) x y d n
  have hz0 : ∀ n ∈ Finset.Icc 1 d,
      z n ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + 0) := by
    intro n hnI
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    have hnd : n ≤ d := (Finset.mem_Icc.mp hnI).2
    have hden : n.factorization p * (p - 1) ≤ d :=
      samePrimeFiniteLogAdditivity_den_exponent_le (p := p)
        (Nat.ne_zero_of_lt hn1) hnd
    simpa using
      (Ideal.pow_le_pow_right hden
        (samePrimeFiniteLogAdditivityNumerator_mem_lambdaIdeal_pow
          (p := p) (K := K) hx hy d n))
  have htransport :=
    samePrimeNatDivEval_Icc_sum_eq_zero_of_factorial_weighted_sum_eq_zero
      (p := p) (K := K) (N := N) (d := d) (s := 0) z hz0
      (by
        simpa [z] using
          (samePrimeFiniteLogAdditivity_factorial_weighted_sum_eq_zero
            (p := p) (K := K) x y d))
  calc
    (∑ a ∈ (Finset.Icc 1 d).attach,
      samePrimeNatDivEvalAtDegree (p := p) (K := K) N a.1 d
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (samePrimeFiniteLogAdditivityNumerator (p := p) (K := K) x y d a.1)
        (samePrimeFiniteLogAdditivityNumerator_mem_lambdaIdeal_pow
          (p := p) (K := K) hx hy d a.1)
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
          exact samePrimeFiniteLogAdditivity_den_exponent_le (p := p)
            (Nat.ne_zero_of_lt ha1) had))
        =
      ∑ a ∈ (Finset.Icc 1 d).attach,
        samePrimeNatDivEval (p := p) (K := K) N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (z a.1) (hz0 a.1 a.2) := by
        refine Finset.sum_congr rfl ?_
        intro a _ha
        dsimp [z]
        exact samePrimeNatDivEvalAtDegree_eq_samePrimeNatDivEval
          (p := p) (K := K)
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (samePrimeFiniteLogAdditivityNumerator_mem_lambdaIdeal_pow
            (p := p) (K := K) hx hy d a.1)
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
            exact samePrimeFiniteLogAdditivity_den_exponent_le (p := p)
              (Nat.ne_zero_of_lt ha1) had)
          (hz0 a.1 a.2)
    _ = 0 := htransport

theorem samePrimeFiniteLogAdditivity_term_eq (N d n : ℕ) (hn : n ≠ 0)
    (hnd : n ≤ d) {x y : ValuedIntegerRing p K}
    (hx : x ∈ lambdaIdeal p K) (hy : y ∈ lambdaIdeal p K) :
    samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
        (samePrimeFiniteLogAdditivityNumerator (p := p) (K := K) x y d n)
        (samePrimeFiniteLogAdditivityNumerator_mem_lambdaIdeal_pow
          (p := p) (K := K) hx hy d n)
        (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
      =
    ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
        samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
          (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d)
          (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
            (p := p) (K := K) hx hy n d)
          (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd) -
      ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
        samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
          (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x 0) ^ n).coeff d)
          (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
            (p := p) (K := K) hx (zero_mem (lambdaIdeal p K)) n d)
          (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd) -
      ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
        samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
          (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) y 0) ^ n).coeff d)
          (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
            (p := p) (K := K) hy (zero_mem (lambdaIdeal p K)) n d)
          (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd) := by
  let zxy : ValuedIntegerRing p K :=
    ((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d
  let zx : ValuedIntegerRing p K :=
    ((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x 0) ^ n).coeff d
  let zy : ValuedIntegerRing p K :=
    ((samePrimeFiniteLogProductArgPoly (p := p) (K := K) y 0) ^ n).coeff d
  let sgn : ValuedIntegerRing p K := (-1 : ValuedIntegerRing p K) ^ (n + 1)
  let hden : n.factorization p * (p - 1) ≤ d :=
    samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd
  have hzxy : zxy ∈ (lambdaIdeal p K) ^ d :=
    samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
      (p := p) (K := K) hx hy n d
  have hzx : zx ∈ (lambdaIdeal p K) ^ d :=
    samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
      (p := p) (K := K) hx (zero_mem (lambdaIdeal p K)) n d
  have hzy : zy ∈ (lambdaIdeal p K) ^ d :=
    samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
      (p := p) (K := K) hy (zero_mem (lambdaIdeal p K)) n d
  have hsubx : zxy + -zx ∈ (lambdaIdeal p K) ^ d :=
    ((lambdaIdeal p K) ^ d).add_mem hzxy (((lambdaIdeal p K) ^ d).neg_mem hzx)
  have hsubxy : (zxy + -zx) + -zy ∈ (lambdaIdeal p K) ^ d :=
    ((lambdaIdeal p K) ^ d).add_mem hsubx (((lambdaIdeal p K) ^ d).neg_mem hzy)
  have hs_sub : sgn * ((zxy + -zx) + -zy) ∈ (lambdaIdeal p K) ^ d :=
    Ideal.mul_mem_left _ sgn hsubxy
  have hnum :
      samePrimeFiniteLogAdditivityNumerator (p := p) (K := K) x y d n =
        sgn * ((zxy + -zx) + -zy) := by
    rfl
  have hmk_s :
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) sgn =
        ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) := by
    simp [sgn]
  calc
    samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
        (samePrimeFiniteLogAdditivityNumerator (p := p) (K := K) x y d n)
        (samePrimeFiniteLogAdditivityNumerator_mem_lambdaIdeal_pow
          (p := p) (K := K) hx hy d n)
        (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
        =
      samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
        (sgn * ((zxy + -zx) + -zy)) hs_sub hden := by
        cases hnum
        rfl
    _ =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) sgn *
        samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
          ((zxy + -zx) + -zy) hsubxy hden :=
        samePrimeNatDivEvalAtDegree_mul_left (p := p) (K := K)
          hn sgn hsubxy hs_sub hden
    _ =
      ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
        (samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn zxy hzxy hden -
          samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn zx hzx hden -
          samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn zy hzy hden) := by
        rw [hmk_s,
          samePrimeNatDivEvalAtDegree_add (p := p) (K := K) hn
            hsubx (((lambdaIdeal p K) ^ d).neg_mem hzy) hsubxy hden,
          samePrimeNatDivEvalAtDegree_add (p := p) (K := K) hn
            hzxy (((lambdaIdeal p K) ^ d).neg_mem hzx) hsubx hden,
          samePrimeNatDivEvalAtDegree_neg (p := p) (K := K) hn
            hzx (((lambdaIdeal p K) ^ d).neg_mem hzx) hden,
          samePrimeNatDivEvalAtDegree_neg (p := p) (K := K) hn
            hzy (((lambdaIdeal p K) ^ d).neg_mem hzy) hden]
        ring
    _ = _ := by
        ring

noncomputable def samePrimeFiniteLogProductHomogeneousGrid (N : ℕ)
    (x y : ValuedIntegerRing p K)
    (hx : x ∈ lambdaIdeal p K) (hy : y ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  ∑ n ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
    if hn : n = 0 then 0 else
      ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
        ∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
          if hnd : n ≤ d then
            samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
              (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d)
              (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
                (p := p) (K := K) hx hy n d)
              (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
          else 0

theorem samePrimeFiniteLogProductHomogeneousGrid_eq_degree_sum (N : ℕ)
    {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K) :
    samePrimeFiniteLogProductHomogeneousGrid (p := p) (K := K) N x y hx hy =
      ∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
        ∑ n ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
          if hn : n = 0 then 0 else
            ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
              (if hnd : n ≤ d then
                samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
                  (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d)
                  (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
                    (p := p) (K := K) hx hy n d)
                  (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
              else 0) := by
  classical
  calc
    samePrimeFiniteLogProductHomogeneousGrid (p := p) (K := K) N x y hx hy
        =
      ∑ n ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
        ∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
          if hn : n = 0 then 0 else
            ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
              (if hnd : n ≤ d then
                samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
                  (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d)
                  (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
                    (p := p) (K := K) hx hy n d)
                  (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
              else 0) := by
        refine Finset.sum_congr rfl ?_
        intro n _hnC
        by_cases hn0 : n = 0
        · simp [hn0]
        · simp [hn0, Finset.mul_sum]
    _ =
      ∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
        ∑ n ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
          if hn : n = 0 then 0 else
            ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
              (if hnd : n ≤ d then
                samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
                  (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d)
                  (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
                    (p := p) (K := K) hx hy n d)
                  (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
              else 0) := by
        rw [Finset.sum_comm]

end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular

end
