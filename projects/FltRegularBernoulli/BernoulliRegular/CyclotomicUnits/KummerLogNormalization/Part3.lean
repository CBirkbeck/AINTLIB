import BernoulliRegular.CyclotomicUnits.KummerLogNormalization.Part2

@[expose] public section

noncomputable section

open NumberField
open NumberField.IsCMField
open IsCyclotomicExtension
open BernoulliRegular.Reflection.Local
open scoped BigOperators NumberField

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

set_option linter.style.longLine false in
omit [NumberField.IsCMField K] in
theorem quotient_mk_samePrimeFiniteArtinHasseNormalizedLogHomogeneousNumerator_factorial_weighted_sum_eq_formal
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeQuotientMap (p := p) (K := K) N
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
            samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
              (p := p) (K := K) N n d x) =
      samePrimeQuotientMap (p := p) (K := K) N (x ^ d) *
        (samePrimeRIntegralRatToQuotient (p := p) (K := K) N
          (∑ n ∈ Finset.Icc 1 d,
            rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n)) := by
  classical
  let q : ValuedIntegerRing p K →+*
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    samePrimeQuotientMap (p := p) (K := K) N
  let φ : Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+*
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    samePrimeRIntegralRatToQuotient (p := p) (K := K) N
  let xbar_d : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    q (x ^ d)
  have hterm : ∀ n ∈ Finset.Icc 1 d,
      q (((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x) =
        xbar_d *
          φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) := by
    intro n _hn
    have hqcoeff :
        q (((samePrimeFiniteArtinHasseNormalizedCoordPoly
              (p := p) (K := K) N x) ^ n).coeff d) =
          (PowerSeries.coeff
            (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
            ((samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries
              (p := p) (K := K) N x) ^ n) := by
      change Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          (((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x) ^ n).coeff d) =
        (PowerSeries.coeff
          (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
          ((samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries
            (p := p) (K := K) N x) ^ n)
      exact quotient_mk_samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_eq
        (p := p) (K := K) N n d hx
    calc
      q (((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x)
          =
        ((d.factorial / n : ℕ) :
            ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
          ((-1 :
            ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
            (PowerSeries.coeff
              (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
              ((samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries
                (p := p) (K := K) N x) ^ n) := by
          simp only [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator,
            map_mul, map_natCast, map_pow]
          rw [hqcoeff]
          simp only [map_neg, map_one]
          ring_nf
      _ =
        xbar_d *
          φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) := by
          have hformal :
              φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) =
                ((d.factorial / n : ℕ) :
                    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
                  ((-1 :
                    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
                    (PowerSeries.coeff
                      (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
                      ((PowerSeries.map q
                        (integralArtinHasseNormalizedExpMinusOneSeries p K - 1)) ^ n) :=
            samePrime_rIntegralRatToQuotient_normalizedFactorialWeightedLogCoeff
              (p := p) (K := K) N d n
          rw [coeff_samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries_pow
            (p := p) (K := K) N n d x]
          let a : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
            ((d.factorial / n : ℕ) :
              ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1))
          let b : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
            ((-1 :
              ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1))
          let c : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
            (PowerSeries.coeff
              (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
              ((PowerSeries.map q
                (integralArtinHasseNormalizedExpMinusOneSeries p K - 1)) ^ n)
          let z : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) := q (x ^ d)
          have hformal' :
              φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) =
                a * b * c :=
            hformal
          change a * b * (z * c) =
            xbar_d *
              φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n)
          rw [hformal']
          ring
  calc
    q (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
            samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
              (p := p) (K := K) N n d x)
        =
      ∑ n ∈ Finset.Icc 1 d,
        q (((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x) := by
        rw [map_sum]
    _ =
      ∑ n ∈ Finset.Icc 1 d,
        xbar_d *
          φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        exact hterm n hn
    _ =
      xbar_d *
        ∑ n ∈ Finset.Icc 1 d,
          φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) :=
        (Finset.mul_sum (s := Finset.Icc 1 d)
          (f := fun n ↦ φ
            (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n))
          xbar_d).symm
    _ =
      q (x ^ d) *
        φ (∑ n ∈ Finset.Icc 1 d,
          rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) := by
        have hmapsum :
            (∑ n ∈ Finset.Icc 1 d,
              φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n)) =
              φ (∑ n ∈ Finset.Icc 1 d,
                rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) :=
          (map_sum φ
            (fun n ↦ rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n)
            (Finset.Icc 1 d)).symm
        rw [hmapsum]

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (n d : ℕ) :
    ((samePrimeFiniteArtinHasseNormalizedCoordPoly
        (p := p) (K := K) N x) ^ n).coeff d ∈
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
          ((samePrimeFiniteArtinHasseNormalizedCoordPoly
              (p := p) (K := K) N x) ^ n).coeff a.1 ∈
            (lambdaIdeal p K) ^ a.1 :=
        ih a.1
      have hright :
          (samePrimeFiniteArtinHasseNormalizedCoordPoly
              (p := p) (K := K) N x).coeff a.2 ∈
            (lambdaIdeal p K) ^ a.2 :=
        samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_mem_lambdaIdeal_pow
          (p := p) (K := K) N hx a.2
      have hmul :
          ((samePrimeFiniteArtinHasseNormalizedCoordPoly
                (p := p) (K := K) N x) ^ n).coeff a.1 *
              (samePrimeFiniteArtinHasseNormalizedCoordPoly
                (p := p) (K := K) N x).coeff a.2 ∈
            (lambdaIdeal p K) ^ (a.1 + a.2) := by
        simpa [pow_add] using Ideal.mul_mem_mul hleft hright
      simpa [hsum] using hmul

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator_mem_lambdaIdeal_pow
    (N n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
        (p := p) (K := K) N n d x ∈
      (lambdaIdeal p K) ^ d :=
  Ideal.mul_mem_left _ _
    (samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
      (p := p) (K := K) N hx n d)

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_sub_coeff_mem_lambdaIdeal_pow
    (N M d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hNM : N ≤ M) :
    (samePrimeFiniteArtinHasseNormalizedCoordPoly
        (p := p) (K := K) N x).coeff d -
        (samePrimeFiniteArtinHasseNormalizedCoordPoly
          (p := p) (K := K) M x).coeff d ∈
      (lambdaIdeal p K) ^ (if d ≤ N then N + 1 + d else d) := by
  by_cases hdN : d ≤ N
  · rw [if_pos hdN]
    by_cases hd0 : d = 0
    · subst d
      simp [samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_zero]
    · have hdM : d ≤ M := hdN.trans hNM
      rw [samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_eq_of_pos_le
          (p := p) (K := K) N d x hd0 hdN,
        samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_eq_of_pos_le
          (p := p) (K := K) M d x hd0 hdM, sub_self]
      exact zero_mem _
  · rw [if_neg hdN]
    have hNmem :
        (samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x).coeff d ∈
          (lambdaIdeal p K) ^ d :=
      samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_mem_lambdaIdeal_pow
        (p := p) (K := K) N hx d
    have hMmem :
        (samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) M x).coeff d ∈
          (lambdaIdeal p K) ^ d :=
      samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_mem_lambdaIdeal_pow
        (p := p) (K := K) M hx d
    exact ((lambdaIdeal p K) ^ d).sub_mem hNmem hMmem

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_sub_coeff_mem_lambdaIdeal_pow
    (N M n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hNM : N ≤ M) :
    ((samePrimeFiniteArtinHasseNormalizedCoordPoly
        (p := p) (K := K) N x) ^ n).coeff d -
        ((samePrimeFiniteArtinHasseNormalizedCoordPoly
          (p := p) (K := K) M x) ^ n).coeff d ∈
      (lambdaIdeal p K) ^ (if d < N + n then N + 1 + d else d) := by
  classical
  induction n generalizing d with
  | zero =>
      simp
  | succ n ih =>
      let PN : Polynomial (ValuedIntegerRing p K) :=
        samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N x
      let PM : Polynomial (ValuedIntegerRing p K) :=
        samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) M x
      rw [pow_succ, pow_succ, Polynomial.coeff_mul, Polynomial.coeff_mul,
        ← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ ?_
      intro a ha
      have hsum : a.1 + a.2 = d := by
        simpa using Finset.mem_antidiagonal.mp ha
      by_cases ha2z : a.2 = 0
      · simp [ha2z, samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_zero]
      · have hPN₂ : PN.coeff a.2 ∈ (lambdaIdeal p K) ^ a.2 := by
          simpa [PN] using
            samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_mem_lambdaIdeal_pow
              (p := p) (K := K) N hx a.2
        have hPMpow₁ :
            (PM ^ n).coeff a.1 ∈ (lambdaIdeal p K) ^ a.1 := by
          simpa [PM] using
            samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
              (p := p) (K := K) M hx n a.1
        have hdiff₁ :
            (PN ^ n).coeff a.1 - (PM ^ n).coeff a.1 ∈
              (lambdaIdeal p K) ^
                (if a.1 < N + n then N + 1 + a.1 else a.1) := by
          simpa [PN, PM] using ih a.1
        have hmul₁ :
            ((PN ^ n).coeff a.1 - (PM ^ n).coeff a.1) * PN.coeff a.2 ∈
              (lambdaIdeal p K) ^
                ((if a.1 < N + n then N + 1 + a.1 else a.1) + a.2) := by
          simpa [pow_add] using Ideal.mul_mem_mul hdiff₁ hPN₂
        have hterm₁ :
            ((PN ^ n).coeff a.1 - (PM ^ n).coeff a.1) * PN.coeff a.2 ∈
              (lambdaIdeal p K) ^ (if d < N + (n + 1) then N + 1 + d else d) := by
          refine Ideal.pow_le_pow_right ?_ hmul₁
          by_cases hdsmall : d < N + (n + 1)
          · have ha1small : a.1 < N + n := by omega
            rw [if_pos hdsmall, if_pos ha1small]
            omega
          · rw [if_neg hdsmall]
            by_cases ha1small : a.1 < N + n
            · rw [if_pos ha1small]
              omega
            · rw [if_neg ha1small]
              omega
        have hterm₂ :
            (PM ^ n).coeff a.1 * (PN.coeff a.2 - PM.coeff a.2) ∈
              (lambdaIdeal p K) ^ (if d < N + (n + 1) then N + 1 + d else d) := by
          by_cases ha1lt : a.1 < n
          · have hzero : (PM ^ n).coeff a.1 = 0 := by
              have h :=
                coeff_pow_coe_eq_zero_of_lt_of_constantCoeff_eq_zero PM
                  (by
                    simpa [PM] using
                      samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_zero
                        (p := p) (K := K) M x)
                  ha1lt
              simpa [← Polynomial.coe_pow, Polynomial.coeff_coe] using h
            rw [hzero, zero_mul]
            exact zero_mem _
          · have hna1 : n ≤ a.1 := Nat.le_of_not_gt ha1lt
            have hdiff₂ :
                PN.coeff a.2 - PM.coeff a.2 ∈
                  (lambdaIdeal p K) ^ (if a.2 ≤ N then N + 1 + a.2 else a.2) := by
              simpa [PN, PM] using
                samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_sub_coeff_mem_lambdaIdeal_pow
                  (p := p) (K := K) N M a.2 hx hNM
            have hmul₂ :
                (PM ^ n).coeff a.1 * (PN.coeff a.2 - PM.coeff a.2) ∈
                  (lambdaIdeal p K) ^
                    (a.1 + (if a.2 ≤ N then N + 1 + a.2 else a.2)) := by
              simpa [pow_add] using Ideal.mul_mem_mul hPMpow₁ hdiff₂
            refine Ideal.pow_le_pow_right ?_ hmul₂
            by_cases hdsmall : d < N + (n + 1)
            · have ha2N : a.2 ≤ N := by omega
              rw [if_pos hdsmall, if_pos ha2N]
              omega
            · rw [if_neg hdsmall]
              by_cases ha2N : a.2 ≤ N
              · rw [if_pos ha2N]
                omega
              · rw [if_neg ha2N]
                omega
        rw [show
            (PN ^ n).coeff a.1 * PN.coeff a.2 -
                (PM ^ n).coeff a.1 * PM.coeff a.2 =
              ((PN ^ n).coeff a.1 - (PM ^ n).coeff a.1) * PN.coeff a.2 +
                (PM ^ n).coeff a.1 * (PN.coeff a.2 - PM.coeff a.2) by ring]
        exact ((lambdaIdeal p K) ^
          (if d < N + (n + 1) then N + 1 + d else d)).add_mem hterm₁ hterm₂

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_eq_zero_of_lt
    (N : ℕ) (x : ValuedIntegerRing p K) {n d : ℕ} (hdn : d < n) :
    ((samePrimeFiniteArtinHasseNormalizedCoordPoly
        (p := p) (K := K) N x) ^ n).coeff d = 0 := by
  have h :=
    coeff_pow_coe_eq_zero_of_lt_of_constantCoeff_eq_zero
      (samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N x)
      (samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_zero
        (p := p) (K := K) N x) hdn
  simpa [← Polynomial.coe_pow, Polynomial.coeff_coe] using h

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_le_of_mem_support
    (N : ℕ) (x : ValuedIntegerRing p K) {n d : ℕ}
    (hd : d ∈ ((samePrimeFiniteArtinHasseNormalizedCoordPoly
        (p := p) (K := K) N x) ^ n).support) :
    n ≤ d := by
  by_contra hnd
  have hdn : d < n := Nat.lt_of_not_ge hnd
  have hcoeff :
      ((samePrimeFiniteArtinHasseNormalizedCoordPoly
          (p := p) (K := K) N x) ^ n).coeff d = 0 :=
    samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_eq_zero_of_lt
      (p := p) (K := K) N x hdn
  exact (Polynomial.mem_support_iff.mp hd) hcoeff

omit [NumberField.IsCMField K] in
/-- Unsigned homogeneous finite-log term attached to the degree-`d`
coefficient of the `n`-th power of the normalized Artin-Hasse coordinate. -/
noncomputable def samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore
    (N n d : ℕ) (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  if hn : n = 0 then 0 else
    if hnd : n ≤ d then
      samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
        (((samePrimeFiniteArtinHasseNormalizedCoordPoly
          (p := p) (K := K) N x) ^ n).coeff d)
        (samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
          (p := p) (K := K) N hx n d)
        (samePrimeFiniteArtinHasse_den_exponent_le (p := p) hn hnd)
    else 0

omit [NumberField.IsCMField K] in
/-- Signed homogeneous finite-log term attached to the degree-`d`
coefficient of the `n`-th power of the normalized Artin-Hasse coordinate. -/
noncomputable def samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
    (N n d : ℕ) (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore
      (p := p) (K := K) N n d x hx

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm_eq_signed_eval
    (N n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hn : n ≠ 0) (hnd : n ≤ d) :
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
        (p := p) (K := K) N n d x hx =
      ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
        samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
          (((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x) ^ n).coeff d)
          (samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
            (p := p) (K := K) N hx n d)
          (samePrimeFiniteArtinHasse_den_exponent_le (p := p) hn hnd) := by
  simp [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm,
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore, hn, hnd]

omit [NumberField.IsCMField K] in
noncomputable def samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
    (N d : ℕ) (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  ∑ a ∈ (Finset.Icc 1 d).attach,
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
      (p := p) (K := K) N a.1 d x hx

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_eval_sum
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
        (p := p) (K := K) N d x hx =
      ∑ a ∈ (Finset.Icc 1 d).attach,
        samePrimeNatDivEval (p := p) (K := K) N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) N a.1 d x)
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
            have hden : a.1.factorization p * (p - 1) ≤ d :=
              samePrimeFiniteArtinHasse_den_exponent_le (p := p)
                (Nat.ne_zero_of_lt ha1) had
            simpa [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator] using
              Ideal.pow_le_pow_right hden
                (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator_mem_lambdaIdeal_pow
                  (p := p) (K := K) N a.1 d hx)) := by
  classical
  unfold samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
  refine Finset.sum_congr rfl ?_
  intro a _ha
  have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
  have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
  have han : a.1 ≠ 0 := Nat.ne_zero_of_lt ha1
  have hden : a.1.factorization p * (p - 1) ≤ d :=
    samePrimeFiniteArtinHasse_den_exponent_le (p := p) han had
  have hcoeff :
      ((samePrimeFiniteArtinHasseNormalizedCoordPoly
          (p := p) (K := K) N x) ^ a.1).coeff d ∈
        (lambdaIdeal p K) ^ d :=
    samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
      (p := p) (K := K) N hx a.1 d
  have hsign :
      (((-1 : ValuedIntegerRing p K) ^ (a.1 + 1)) *
          ((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x) ^ a.1).coeff d) ∈
        (lambdaIdeal p K) ^ d :=
    Ideal.mul_mem_left _ _ hcoeff
  have hnum0 :
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
          (p := p) (K := K) N a.1 d x ∈
        (lambdaIdeal p K) ^ (a.1.factorization p * (p - 1) + 0) := by
    simpa [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator] using
      Ideal.pow_le_pow_right hden hsign
  have hmk :
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          ((-1 : ValuedIntegerRing p K) ^ (a.1 + 1)) =
        ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^
          (a.1 + 1)) := by
    simp
  rw [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm_eq_signed_eval
    (p := p) (K := K) N a.1 d hx han had, ← hmk,
    ← samePrimeNatDivEvalAtDegree_mul_left (p := p) (K := K) han
      ((-1 : ValuedIntegerRing p K) ^ (a.1 + 1)) hcoeff hsign hden,
    samePrimeNatDivEvalAtDegree_eq_samePrimeNatDivEval (p := p) (K := K)
      han hsign hden hnum0]
  exact samePrimeNatDivEval_eq_of_eq (p := p) (K := K) han
    (by simp [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator])
    hnum0 _

set_option linter.style.longLine false in
omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_zero_of_factorial_weighted_sum_mem
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hclear :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x) ∈
        (lambdaIdeal p K) ^
          (d.factorial.factorization p * (p - 1) + (N + 1))) :
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
        (p := p) (K := K) N d x hx = 0 := by
  classical
  let z : ℕ → ValuedIntegerRing p K := fun n ↦
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
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
      Ideal.pow_le_pow_right hden
        (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator_mem_lambdaIdeal_pow
          (p := p) (K := K) N n d hx)
  have htransport :=
    samePrimeNatDivEval_Icc_sum_eq_zero_of_factorial_weighted_sum_mem_lambdaIdeal_pow
      (p := p) (K := K) (N := N) (d := d) (s := 0) (t := N + 1) z hz0
      (by
        simpa [z] using hclear)
      le_rfl
  calc
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
        (p := p) (K := K) N d x hx
        =
      ∑ a ∈ (Finset.Icc 1 d).attach,
        samePrimeNatDivEval (p := p) (K := K) N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (z a.1) (hz0 a.1 a.2) := by
        simpa [z] using
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_eval_sum
            (p := p) (K := K) N d hx
    _ = 0 := htransport

set_option linter.style.longLine false in
omit [NumberField.IsCMField K] in
/-- Multiplying a normalized homogeneous finite-log degree slice by `d!`
clears the same-prime denominators and gives the factorial-weighted numerator
sum in the finite quotient. -/
theorem natCast_factorial_mul_samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    ((d.factorial : ℕ) :
        ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
        (p := p) (K := K) N d x hx =
    samePrimeQuotientMap (p := p) (K := K) N
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x) := by
  classical
  let A : Type _ := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)
  let q : ValuedIntegerRing p K →+* A :=
    samePrimeQuotientMap (p := p) (K := K) N
  let z : ℕ → ValuedIntegerRing p K := fun n ↦
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
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
      Ideal.pow_le_pow_right hden
        (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator_mem_lambdaIdeal_pow
          (p := p) (K := K) N n d hx)
  have hdegree :
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
          (p := p) (K := K) N d x hx =
        ∑ a ∈ (Finset.Icc 1 d).attach,
          samePrimeNatDivEval (p := p) (K := K) N a.1 0
            (by
              have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
              exact Nat.ne_zero_of_lt ha1)
            (z a.1) (hz0 a.1 a.2) := by
    simpa [z] using
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_eval_sum
        (p := p) (K := K) N d hx
  rw [hdegree, Finset.mul_sum]
  calc
    ∑ a ∈ (Finset.Icc 1 d).attach,
        ((d.factorial : ℕ) : A) *
          samePrimeNatDivEval (p := p) (K := K) N a.1 0
            (by
              have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
              exact Nat.ne_zero_of_lt ha1)
            (z a.1) (hz0 a.1 a.2)
        =
      ∑ a ∈ (Finset.Icc 1 d).attach,
        q (((d.factorial / a.1 : ℕ) : ValuedIntegerRing p K) * z a.1) := by
        refine Finset.sum_congr rfl ?_
        intro a _ha
        have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
        have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
        have han : a.1 ≠ 0 := Nat.ne_zero_of_lt ha1
        have hdiv : a.1 ∣ d.factorial :=
          Nat.dvd_factorial (Nat.pos_of_ne_zero han) had
        have hfac : (d.factorial / a.1) * a.1 = d.factorial :=
          Nat.div_mul_cancel hdiv
        have hnat :
            ((d.factorial : ℕ) : A) =
              ((d.factorial / a.1 : ℕ) : A) * ((a.1 : ℕ) : A) := by
          rw [← Nat.cast_mul, hfac]
        have hnatdiv :
            ((a.1 : ℕ) : A) *
                samePrimeNatDivEval (p := p) (K := K) N a.1 0 han
                  (z a.1) (hz0 a.1 a.2) =
              q (z a.1) := by
          simpa [q, A, samePrimeQuotientMap] using
            samePrimeNatDivEval_natCast_mul_eq_mk
              (p := p) (K := K) (N := N) (n := a.1) (s := 0) han
              (z := z a.1) (hz0 a.1 a.2)
        calc
          ((d.factorial : ℕ) : A) *
              samePrimeNatDivEval (p := p) (K := K) N a.1 0 han
                (z a.1) (hz0 a.1 a.2)
              =
            ((d.factorial / a.1 : ℕ) : A) *
              (((a.1 : ℕ) : A) *
                samePrimeNatDivEval (p := p) (K := K) N a.1 0 han
                  (z a.1) (hz0 a.1 a.2)) := by
              rw [hnat]
              ring
          _ =
            ((d.factorial / a.1 : ℕ) : A) * q (z a.1) := by
              rw [hnatdiv]
          _ =
            q (((d.factorial / a.1 : ℕ) : ValuedIntegerRing p K) * z a.1) := by
              change q (((d.factorial / a.1 : ℕ) : ValuedIntegerRing p K)) *
                  q (z a.1) =
                q (((d.factorial / a.1 : ℕ) : ValuedIntegerRing p K) * z a.1)
              rw [map_mul]
    _ =
      samePrimeQuotientMap (p := p) (K := K) N
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) * z n) := by
        rw [map_sum]
        simpa [q] using
          (Finset.sum_attach (s := Finset.Icc 1 d)
            (f := fun n : ℕ ↦
              q (((d.factorial / n : ℕ) : ValuedIntegerRing p K) * z n)))

set_option linter.style.longLine false in
omit [NumberField.IsCMField K] in
/-- Factorial-cleared normalized homogeneous degree slice, expressed through
the formal normalized Artin-Hasse logarithm coefficient. -/
theorem natCast_factorial_mul_samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_formal
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    ((d.factorial : ℕ) :
        ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
        (p := p) (K := K) N d x hx =
    samePrimeQuotientMap (p := p) (K := K) N (x ^ d) *
      samePrimeRIntegralRatToQuotient (p := p) (K := K) N
        (∑ n ∈ Finset.Icc 1 d,
          rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) := by
  rw [natCast_factorial_mul_samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq
    (p := p) (K := K) N d hx]
  exact quotient_mk_samePrimeFiniteArtinHasseNormalizedLogHomogeneousNumerator_factorial_weighted_sum_eq_formal
    (p := p) (K := K) N d hx

set_option linter.style.longLine false in
omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedLogHomogeneousNumerator_factorial_weighted_sub_precision_mem_lambdaIdeal_pow
    (N M n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hNM : N ≤ M) (hn1 : 1 ≤ n) (hnd : n ≤ d) :
    (((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
        (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x -
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) M n d x)) ∈
      (lambdaIdeal p K) ^ (d.factorial.factorization p * (p - 1) + (N + 1)) := by
  classical
  let s : ℕ := n.factorization p * (p - 1)
  let u : ℕ := if d < N + n then N + 1 + d else d
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn1
  have hs_le_pred : s ≤ n - 1 := by
    simpa [s] using
      Nat.factorization_mul_pred_le_pred
        (ell := p) (n := n) (Fact.out : Nat.Prime p) hn0
  have hs_le_d : s ≤ d := by omega
  have hu : N + 1 + s ≤ u := by
    by_cases hdsmall : d < N + n
    · dsimp [u]
      rw [if_pos hdsmall]
      omega
    · dsimp [u]
      rw [if_neg hdsmall]
      omega
  have hpowdiff :
      ((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x) ^ n).coeff d -
          ((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) M x) ^ n).coeff d ∈
        (lambdaIdeal p K) ^ u := by
    simpa [u] using
      samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_sub_coeff_mem_lambdaIdeal_pow
        (p := p) (K := K) N M n d hx hNM
  have hnumdiff :
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
          (p := p) (K := K) N n d x -
        samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
          (p := p) (K := K) M n d x ∈
        (lambdaIdeal p K) ^ u := by
    have hmul :
        ((-1 : ValuedIntegerRing p K) ^ (n + 1)) *
            (((samePrimeFiniteArtinHasseNormalizedCoordPoly
                  (p := p) (K := K) N x) ^ n).coeff d -
              ((samePrimeFiniteArtinHasseNormalizedCoordPoly
                  (p := p) (K := K) M x) ^ n).coeff d) ∈
          (lambdaIdeal p K) ^ u :=
      Ideal.mul_mem_left _ _ hpowdiff
    simpa [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator,
      sub_eq_add_neg, mul_add, mul_neg] using hmul
  have hweighted :
      (((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
              (p := p) (K := K) N n d x -
            samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
              (p := p) (K := K) M n d x)) ∈
        (lambdaIdeal p K) ^ ((d.factorial / n).factorization p * (p - 1) + u) :=
    natCast_mul_mem_lambdaIdeal_pow_factorization_mul_pred_add
      (p := p) (K := K) (c := d.factorial / n) hnumdiff
  have hdiv : n ∣ d.factorial :=
    Nat.dvd_factorial (Nat.pos_of_ne_zero hn0) hnd
  have hmul_div : d.factorial / n * n = d.factorial := Nat.div_mul_cancel hdiv
  have hdiv_ne : d.factorial / n ≠ 0 := by
    intro hzero
    have hfac0 : d.factorial = 0 := by
      simpa [hzero] using hmul_div.symm
    exact Nat.factorial_ne_zero d hfac0
  have hfac :
      d.factorial.factorization p =
        (d.factorial / n).factorization p + n.factorization p := by
    have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p)
      (Nat.factorization_mul hdiv_ne hn0)
    simpa [hmul_div] using h
  have htarget :
      d.factorial.factorization p * (p - 1) + (N + 1) ≤
        (d.factorial / n).factorization p * (p - 1) + u := by
    rw [hfac, Nat.add_mul]
    omega
  exact Ideal.pow_le_pow_right htarget hweighted

set_option linter.style.longLine false in
omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedLogHomogeneousNumerator_factorial_weighted_sub_highPrecision_mem_lambdaIdeal_pow
    (N n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hn1 : 1 ≤ n) (hnd : n ≤ d) :
    (((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
        (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x -
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K)
            (N + d.factorial.factorization p * (p - 1)) n d x)) ∈
      (lambdaIdeal p K) ^ (d.factorial.factorization p * (p - 1) + (N + 1)) :=
  samePrimeFiniteArtinHasseNormalizedLogHomogeneousNumerator_factorial_weighted_sub_precision_mem_lambdaIdeal_pow
    (p := p) (K := K) N (N + d.factorial.factorization p * (p - 1)) n d hx
    (Nat.le_add_right N (d.factorial.factorization p * (p - 1))) hn1 hnd

set_option linter.style.longLine false in
omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedLogHomogeneousNumerator_factorial_weighted_sum_mem_lambdaIdeal_pow_of_coeff_log_eq_zero
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hcoeff :
      (PowerSeries.coeff (R := ℚ) d)
          (PowerSeries.logOf (rationalArtinHasseNormalizedExpMinusOneSeries p)) = 0) :
    (∑ n ∈ Finset.Icc 1 d,
      ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
        samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
          (p := p) (K := K) N n d x) ∈
      (lambdaIdeal p K) ^ (d.factorial.factorization p * (p - 1) + (N + 1)) := by
  classical
  let D : ℕ := d.factorial.factorization p * (p - 1)
  let M : ℕ := D + N
  let I : Ideal (ValuedIntegerRing p K) := (lambdaIdeal p K) ^ (D + (N + 1))
  have hNM : N ≤ M := by omega
  have hdiff :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
              (p := p) (K := K) N n d x -
            samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
              (p := p) (K := K) M n d x)) ∈ I := by
    refine Ideal.sum_mem _ ?_
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnd : n ≤ d := (Finset.mem_Icc.mp hn).2
    simpa [I, D] using
      samePrimeFiniteArtinHasseNormalizedLogHomogeneousNumerator_factorial_weighted_sub_precision_mem_lambdaIdeal_pow
        (p := p) (K := K) N M n d hx hNM hn1 hnd
  have hsumM_M :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) M n d x) ∈
        (lambdaIdeal p K) ^ (M + 1) := by
    have hsource_zero :
        (∑ n ∈ Finset.Icc 1 d,
          rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) = 0 := by
      apply Subtype.ext
      have hcoe :=
        coe_sum_rationalArtinHasseNormalizedFactorialWeightedLogCoeff
          (p := p) d
      simpa [hcoeff] using hcoe
    have hq :=
      quotient_mk_samePrimeFiniteArtinHasseNormalizedLogHomogeneousNumerator_factorial_weighted_sum_eq_formal
        (p := p) (K := K) M d hx
    rw [hsource_zero, map_zero, mul_zero] at hq
    have hq_zero :
        samePrimeQuotientMap (p := p) (K := K) M
          (∑ n ∈ Finset.Icc 1 d,
            ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
              samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
                (p := p) (K := K) M n d x) = 0 := by
      simpa using hq
    change Ideal.Quotient.mk ((lambdaIdeal p K) ^ (M + 1))
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
            samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
              (p := p) (K := K) M n d x) = 0 at hq_zero
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq_zero
  have hsumM : (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) M n d x) ∈ I := by
    simpa [I, M, D, Nat.add_assoc] using hsumM_M
  have hsplit :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x) =
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
              (p := p) (K := K) N n d x -
            samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
              (p := p) (K := K) M n d x)) +
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
            (p := p) (K := K) M n d x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    ring
  rw [hsplit]
  exact I.add_mem hdiff hsumM

set_option linter.style.longLine false in
omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_zero_of_coeff_log_eq_zero
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hcoeff :
      (PowerSeries.coeff (R := ℚ) d)
          (PowerSeries.logOf (rationalArtinHasseNormalizedExpMinusOneSeries p)) = 0) :
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
        (p := p) (K := K) N d x hx = 0 :=
  samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_zero_of_factorial_weighted_sum_mem
    (p := p) (K := K) N d hx
    (samePrimeFiniteArtinHasseNormalizedLogHomogeneousNumerator_factorial_weighted_sum_mem_lambdaIdeal_pow_of_coeff_log_eq_zero
      (p := p) (K := K) N d hx hcoeff)

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm_eq_zero_of_not_mem_support
    (N n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hd : d ∉ ((samePrimeFiniteArtinHasseNormalizedCoordPoly
      (p := p) (K := K) N x) ^ n).support) :
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
      (p := p) (K := K) N n d x hx = 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm,
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore]
  by_cases hnd : n ≤ d
  · have hcoeff_zero :
        ((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x) ^ n).coeff d = 0 := by
      simpa [Polynomial.mem_support_iff] using hd
    have hcoeff :
        ((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x) ^ n).coeff d ∈
          (lambdaIdeal p K) ^ d :=
      samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
        (p := p) (K := K) N hx n d
    have hden : n.factorization p * (p - 1) ≤ d :=
      samePrimeFiniteArtinHasse_den_exponent_le (p := p) hn hnd
    have heval_zero :
        samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
            (((samePrimeFiniteArtinHasseNormalizedCoordPoly
              (p := p) (K := K) N x) ^ n).coeff d)
            hcoeff hden = 0 := by
      rw [samePrimeNatDivEvalAtDegree]
      let s : ℕ := d - n.factorization p * (p - 1)
      have hcoeff_s :
          ((samePrimeFiniteArtinHasseNormalizedCoordPoly
              (p := p) (K := K) N x) ^ n).coeff d ∈
            (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
        simpa [s, Nat.add_sub_of_le hden] using hcoeff
      have hzero_s :
          (0 : ValuedIntegerRing p K) ∈
            (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) :=
        zero_mem _
      change samePrimeNatDivEval (p := p) (K := K) N n s hn
          (((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x) ^ n).coeff d)
          hcoeff_s = 0
      calc
        samePrimeNatDivEval (p := p) (K := K) N n s hn
            (((samePrimeFiniteArtinHasseNormalizedCoordPoly
              (p := p) (K := K) N x) ^ n).coeff d)
            hcoeff_s
            = samePrimeNatDivEval (p := p) (K := K) N n s hn 0 hzero_s :=
                samePrimeNatDivEval_eq_of_eq (p := p) (K := K) hn
                  hcoeff_zero hcoeff_s hzero_s
        _ = 0 := samePrimeNatDivEval_zero (p := p) (K := K) hn hzero_s
    rw [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm_eq_signed_eval
      (p := p) (K := K) N n d hx hn hnd, heval_zero]
    simp
  · simp [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm,
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore, hn, hnd]

end CyclotomicUnits

end BernoulliRegular

end
