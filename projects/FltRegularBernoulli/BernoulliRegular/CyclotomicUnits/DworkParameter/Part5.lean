module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.Part4

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

/-- Unsigned homogeneous finite-log term attached to the degree-`d`
coefficient of `(E_N(x)-1)^n`. -/
noncomputable def samePrimeFiniteArtinHasseExpCoordLogHomogeneousCore
    (N n d : ℕ) (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  if hn : n = 0 then 0 else
    if hnd : n ≤ d then
      samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
        (((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d)
        (samePrimeFiniteArtinHasseExpCoordPoly_pow_coeff_mem_lambdaIdeal_pow
          (p := p) (K := K) N hx n d)
        (samePrimeFiniteArtinHasse_den_exponent_le (p := p) hn hnd)
    else 0

/-- Signed homogeneous finite-log term attached to the degree-`d`
coefficient of `(E_N(x)-1)^n`. -/
noncomputable def samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm
    (N n d : ℕ) (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousCore (p := p) (K := K) N n d x hx

theorem samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm_eq_signed_eval
    (N n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hn : n ≠ 0) (hnd : n ≤ d) :
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm (p := p) (K := K) N n d x hx =
      ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
        samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
          (((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d)
          (samePrimeFiniteArtinHasseExpCoordPoly_pow_coeff_mem_lambdaIdeal_pow
            (p := p) (K := K) N hx n d)
          (samePrimeFiniteArtinHasse_den_exponent_le (p := p) hn hnd) := by
  simp [samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm,
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousCore, hn, hnd]

/-- Quotient power series represented by the homogeneous Artin--Hasse
coordinate polynomial. -/
def samePrimeFiniteArtinHasseExpCoordQuotientSeries
    (N : ℕ) (x : ValuedIntegerRing p K) :
    PowerSeries (ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) :=
  PowerSeries.rescale
    (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) x)
    (PowerSeries.map (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
      (integralExpMinusOneSeries p K))

theorem samePrimeFiniteArtinHasseExpCoordPoly_map_eq_quotientSeries
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    (((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x).map
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))) :
          Polynomial (ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1))) :
        PowerSeries (ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1))) =
      samePrimeFiniteArtinHasseExpCoordQuotientSeries (p := p) (K := K) N x := by
  classical
  let q : ValuedIntegerRing p K →+*
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
  ext d
  rw [Polynomial.coeff_coe, Polynomial.coeff_map]
  rw [samePrimeFiniteArtinHasseExpCoordQuotientSeries, PowerSeries.coeff_rescale,
    PowerSeries.coeff_map]
  by_cases hd0 : d = 0
  · subst d
    have hcoeff0 :
        (PowerSeries.coeff (R := ValuedIntegerRing p K) 0)
            (integralExpMinusOneSeries p K) = 0 := by
      ext
      simp [integralExpMinusOneSeries, rIntegralRatToValuedInteger,
        rIntegralRatToValuedCompletion, FormalDwork.expMinusOneSeries]
    rw [samePrimeFiniteArtinHasseExpCoordPoly_coeff_zero, hcoeff0, map_zero]
    simp
  · by_cases hdN : d ≤ N
    · have hpoly :=
        samePrimeFiniteArtinHasseExpCoordPoly_coeff_eq_of_pos_le
          (p := p) (K := K) N d x hd0 hdN
      have hcoeff :
          (PowerSeries.coeff (R := ValuedIntegerRing p K) d)
              (integralExpMinusOneSeries p K) =
            (PowerSeries.coeff (R := ValuedIntegerRing p K) d)
              (integralExpSeries p K) := by
        rw [integralExpMinusOneSeries_eq]
        simp [hd0]
      rw [hpoly, hcoeff]
      rw [map_mul, map_pow]
      ring
    · have hdlt : N < d := Nat.lt_of_not_ge hdN
      have hpoly :
          (samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x).coeff d = 0 :=
        samePrimeFiniteArtinHasseExpCoordPoly_coeff_eq_zero_of_lt
          (p := p) (K := K) N d x hdlt
      have hle : N + 1 ≤ d := Nat.succ_le_of_lt hdlt
      have hxpow : x ^ d ∈ (lambdaIdeal p K) ^ (N + 1) :=
        Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hx d)
      have hxzero : q (x ^ d) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hxpow
      have hpowmap : (q x) ^ d = q (x ^ d) := (map_pow q x d).symm
      rw [hpoly, map_zero]
      rw [hpowmap, hxzero, zero_mul]

theorem quotient_mk_samePrimeFiniteArtinHasseExpCoordPoly_pow_coeff_eq
    (N n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d) =
      (PowerSeries.coeff
        (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
        ((samePrimeFiniteArtinHasseExpCoordQuotientSeries (p := p) (K := K) N x) ^ n) := by
  let A : Type _ := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)
  let q : ValuedIntegerRing p K →+*
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
  let P : Polynomial (ValuedIntegerRing p K) :=
    samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x
  have hseries :
      ((P.map q : Polynomial A) : PowerSeries A) =
        samePrimeFiniteArtinHasseExpCoordQuotientSeries (p := p) (K := K) N x := by
    simpa [P, q, A] using
      samePrimeFiniteArtinHasseExpCoordPoly_map_eq_quotientSeries
        (p := p) (K := K) N hx
  calc
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) ((P ^ n).coeff d)
        =
      (P.map q ^ n).coeff d := by
        rw [← Polynomial.map_pow, Polynomial.coeff_map]
    _ =
      (PowerSeries.coeff (R := A) d) (((P.map q : Polynomial A) : PowerSeries A) ^ n) := by
        rw [← Polynomial.coe_pow, Polynomial.coeff_coe]
    _ =
      (PowerSeries.coeff (R := A) d)
        ((samePrimeFiniteArtinHasseExpCoordQuotientSeries (p := p) (K := K) N x) ^ n) := by
        rw [hseries]

theorem coeff_samePrimeFiniteArtinHasseExpCoordQuotientSeries_pow
    (N n d : ℕ) (x : ValuedIntegerRing p K) :
    (PowerSeries.coeff
        (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
        ((samePrimeFiniteArtinHasseExpCoordQuotientSeries (p := p) (K := K) N x) ^ n) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) (x ^ d) *
        (PowerSeries.coeff
          (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
          ((PowerSeries.map (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
            (integralExpMinusOneSeries p K)) ^ n) := by
  let A : Type _ := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)
  let q : ValuedIntegerRing p K →+*
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
  let xbar : A := q x
  let EpsMinus : PowerSeries A := PowerSeries.map q (integralExpMinusOneSeries p K)
  calc
    (PowerSeries.coeff (R := A) d)
        ((samePrimeFiniteArtinHasseExpCoordQuotientSeries (p := p) (K := K) N x) ^ n)
        =
      (PowerSeries.coeff (R := A) d) ((PowerSeries.rescale xbar EpsMinus) ^ n) := by
        rfl
    _ =
      (PowerSeries.coeff (R := A) d) (PowerSeries.rescale xbar (EpsMinus ^ n)) := by
        rw [(map_pow (PowerSeries.rescale xbar) EpsMinus n).symm]
    _ =
      xbar ^ d * (PowerSeries.coeff (R := A) d) (EpsMinus ^ n) := by
        rw [PowerSeries.coeff_rescale]
    _ =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) (x ^ d) *
        (PowerSeries.coeff (R := A) d)
          ((PowerSeries.map (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
            (integralExpMinusOneSeries p K)) ^ n) := by
        simp [xbar, q, A, EpsMinus]

theorem samePrimeFiniteArtinHasseExpCoord_signed_pow_coeff_mem_lambdaIdeal_pow
    (N n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    ((-1 : ValuedIntegerRing p K) ^ (n + 1)) *
        ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d ∈
      (lambdaIdeal p K) ^ d :=
  Ideal.mul_mem_left _ _
    (samePrimeFiniteArtinHasseExpCoordPoly_pow_coeff_mem_lambdaIdeal_pow
      (p := p) (K := K) N hx n d)

def samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
    (N n d : ℕ) (x : ValuedIntegerRing p K) : ValuedIntegerRing p K :=
  ((-1 : ValuedIntegerRing p K) ^ (n + 1)) *
    ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d

theorem samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator_mem_lambdaIdeal_pow
    (N n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator (p := p) (K := K) N n d x ∈
      (lambdaIdeal p K) ^ d :=
  samePrimeFiniteArtinHasseExpCoord_signed_pow_coeff_mem_lambdaIdeal_pow
    (p := p) (K := K) N n d hx

def samePrimeQuotientMap (N : ℕ) :
    ValuedIntegerRing p K →+*
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))

def samePrimeRIntegralRatToQuotient (N : ℕ) :
    Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+*
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  (samePrimeQuotientMap (p := p) (K := K) N).comp
    (rIntegralRatToValuedInteger p K)

private theorem mul_mul_mul_rotate_eq_of_eq_of_eq {R : Type*} [CommSemigroup R]
    {a b c z z' y : R} (hz : z = z') (hy : y = a * b * c) :
    a * b * (z * c) = z' * y := by
  subst z'
  rw [hy]
  ac_rfl

theorem samePrime_rIntegralRatToQuotient_factorialWeightedLogCoeff
    (N d n : ℕ) :
    samePrimeRIntegralRatToQuotient (p := p) (K := K) N
        (Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff p d n) =
      ((d.factorial / n : ℕ) :
          ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
        ((-1 :
          ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
          (PowerSeries.coeff
            (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
            ((PowerSeries.map (samePrimeQuotientMap (p := p) (K := K) N)
                (integralExpMinusOneSeries p K)) ^ n) := by
  let q : ValuedIntegerRing p K →+*
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    samePrimeQuotientMap (p := p) (K := K) N
  let φ : Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+*
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    samePrimeRIntegralRatToQuotient (p := p) (K := K) N
  let hE : Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (Furtwaengler.artinHasseExpSeries p) :=
    fun m => Furtwaengler.artinHasseExpSeries_coeff_isRIntegral p m
  let hA : Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (Furtwaengler.artinHasseExpSeries p - 1) :=
    hE.sub (Furtwaengler.DieudonneDwork.IsRIntegralPS.one p)
  have hAps :
      hA.mapTo φ =
        PowerSeries.map q (integralExpMinusOneSeries p K) := by
    let hM : Furtwaengler.DieudonneDwork.IsRIntegralPS p
        (FormalDwork.expMinusOneSeries p) :=
      FormalDwork.expMinusOneSeries_isPIntegral p
    calc
      hA.mapTo φ = hM.mapTo φ :=
        Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_eq_of_eq
          φ hA hM (by
            simp [FormalDwork.expMinusOneSeries,
              Furtwaengler.artinHasseExpMinusOneSeries])
      _ = PowerSeries.map q (hM.mapTo (rIntegralRatToValuedInteger p K)) :=
        (Furtwaengler.DieudonneDwork.IsRIntegralPS.map_mapTo
          (rIntegralRatToValuedInteger p K) q hM).symm
      _ = PowerSeries.map q (integralExpMinusOneSeries p K) := by
        rfl
  have hcoeff :
      φ (⟨(PowerSeries.coeff (R := ℚ) d)
            ((Furtwaengler.artinHasseExpSeries p - 1) ^ n),
          hA.pow n d⟩ :
          Furtwaengler.DieudonneDwork.rIntegralRatSubring p) =
        (PowerSeries.coeff
          (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
          ((PowerSeries.map q (integralExpMinusOneSeries p K)) ^ n) := by
    calc
      φ (⟨(PowerSeries.coeff (R := ℚ) d)
            ((Furtwaengler.artinHasseExpSeries p - 1) ^ n),
          hA.pow n d⟩ :
          Furtwaengler.DieudonneDwork.rIntegralRatSubring p)
          =
        (PowerSeries.coeff
          (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
          ((hA.pow n).mapTo φ) := by
          rw [Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_mapTo]
      _ =
        (PowerSeries.coeff
          (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
          ((hA.mapTo φ) ^ n) := by
          rw [Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_pow]
      _ =
        (PowerSeries.coeff
          (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
          ((PowerSeries.map q (integralExpMinusOneSeries p K)) ^ n) := by
          rw [hAps]
  calc
    φ (Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff p d n)
        =
      ((d.factorial / n : ℕ) :
          ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
          ((-1 :
            ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
          φ (⟨(PowerSeries.coeff (R := ℚ) d)
              ((Furtwaengler.artinHasseExpSeries p - 1) ^ n),
            hA.pow n d⟩ :
            Furtwaengler.DieudonneDwork.rIntegralRatSubring p) := by
        simp [Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff,
          map_mul, map_pow]
    _ =
      ((d.factorial / n : ℕ) :
          ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
        ((-1 :
          ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
          (PowerSeries.coeff
            (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
            ((PowerSeries.map q (integralExpMinusOneSeries p K)) ^ n) :=
        congrArg (fun y =>
          ((d.factorial / n : ℕ) :
              ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
            ((-1 :
              ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) * y)
          hcoeff

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in
-- The quotient-sum comparison is elaboration-heavy because the target expands
-- finite sums, quotient maps, and power-series coefficients at the same time.
theorem quotient_mk_samePrimeFiniteArtinHasseLogHomogeneousNumerator_factorial_weighted_sum_eq_formal
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeQuotientMap (p := p) (K := K) N
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
            samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) N n d x) =
      samePrimeQuotientMap (p := p) (K := K) N (x ^ d) *
        (samePrimeRIntegralRatToQuotient (p := p) (K := K) N
          (∑ n ∈ Finset.Icc 1 d,
            Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff p d n)) := by
  classical
  let q : ValuedIntegerRing p K →+*
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    samePrimeQuotientMap (p := p) (K := K) N
  let φ : Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+*
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    samePrimeRIntegralRatToQuotient (p := p) (K := K) N
  let xbar_d : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) := q (x ^ d)
  have hterm : ∀ n ∈ Finset.Icc 1 d,
      q (((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x) =
        xbar_d *
          φ (Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff p d n) := by
    intro n _hn
    have hqcoeff :
        q (((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d) =
          (PowerSeries.coeff
            (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
            ((samePrimeFiniteArtinHasseExpCoordQuotientSeries
              (p := p) (K := K) N x) ^ n) := by
      change Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          (((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d) =
        (PowerSeries.coeff
          (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
          ((samePrimeFiniteArtinHasseExpCoordQuotientSeries
            (p := p) (K := K) N x) ^ n)
      exact quotient_mk_samePrimeFiniteArtinHasseExpCoordPoly_pow_coeff_eq
        (p := p) (K := K) N n d hx
    calc
        q (((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x)
          =
        ((d.factorial / n : ℕ) :
            ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
          ((-1 :
            ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
            (PowerSeries.coeff
              (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
              ((samePrimeFiniteArtinHasseExpCoordQuotientSeries
                (p := p) (K := K) N x) ^ n) := by
          simp only [samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator,
            map_mul, map_natCast, map_pow]
          rw [hqcoeff]
          simp only [map_neg, map_one]
          ring_nf
      _ =
        xbar_d *
          φ (Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff p d n) := by
          have hformal :
              φ (Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff p d n) =
                ((d.factorial / n : ℕ) :
                    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
                  ((-1 :
                    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
                    (PowerSeries.coeff
                      (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
                      ((PowerSeries.map q (integralExpMinusOneSeries p K)) ^ n) :=
            samePrime_rIntegralRatToQuotient_factorialWeightedLogCoeff
              (p := p) (K := K) N d n
          rw [coeff_samePrimeFiniteArtinHasseExpCoordQuotientSeries_pow
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
              ((PowerSeries.map q (integralExpMinusOneSeries p K)) ^ n)
          let z : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) := q (x ^ d)
          have hformal' :
              φ (Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff p d n) =
                a * b * c :=
            hformal
          change a * b * (z * c) =
            xbar_d *
              φ (Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff p d n)
          exact mul_mul_mul_rotate_eq_of_eq_of_eq
            (a := a) (b := b) (c := c) (z := z) (z' := xbar_d)
            (y := φ (Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff p d n))
            rfl hformal'
  calc
    q (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
            samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) N n d x)
        =
      ∑ n ∈ Finset.Icc 1 d,
        q (((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x) := by
        rw [map_sum]
    _ =
      ∑ n ∈ Finset.Icc 1 d,
        xbar_d *
          φ (Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff p d n) := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        exact hterm n hn
    _ =
      xbar_d *
        ∑ n ∈ Finset.Icc 1 d,
          φ (Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff p d n) :=
        (Finset.mul_sum (s := Finset.Icc 1 d)
          (f := fun n => φ
            (Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff p d n))
          xbar_d).symm
    _ =
      q (x ^ d) *
        φ (∑ n ∈ Finset.Icc 1 d,
          Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff p d n) := by
        have hmapsum :
            (∑ n ∈ Finset.Icc 1 d,
              φ (Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff p d n)) =
              φ (∑ n ∈ Finset.Icc 1 d,
                Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff p d n) :=
          (map_sum φ
            (fun n =>
              Furtwaengler.FiniteArtinHasseFormal.factorialWeightedLogCoeff p d n)
            (Finset.Icc 1 d)).symm
        rw [hmapsum]

set_option linter.style.longLine false in
theorem samePrimeFiniteArtinHasseLogHomogeneousNumerator_factorial_weighted_sub_precision_mem_lambdaIdeal_pow
    (N M n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hNM : N ≤ M) (hn1 : 1 ≤ n) (hnd : n ≤ d) :
    (((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
        (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x -
          samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
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
      ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d -
          ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) M x) ^ n).coeff d ∈
        (lambdaIdeal p K) ^ u := by
    simpa [u] using
      samePrimeFiniteArtinHasseExpCoordPoly_pow_coeff_sub_coeff_mem_lambdaIdeal_pow
        (p := p) (K := K) N M n d hx hNM
  have hnumdiff :
      samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
          (p := p) (K := K) N n d x -
        samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
          (p := p) (K := K) M n d x ∈
        (lambdaIdeal p K) ^ u := by
    have hmul :
        ((-1 : ValuedIntegerRing p K) ^ (n + 1)) *
            (((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d -
              ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) M x) ^ n).coeff d) ∈
          (lambdaIdeal p K) ^ u :=
      Ideal.mul_mem_left _ _ hpowdiff
    simpa [samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator,
      sub_eq_add_neg, mul_add, mul_neg] using hmul
  have hweighted :
      (((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) N n d x -
            samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
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
    have h := congrArg (fun f : ℕ →₀ ℕ => f p)
      (Nat.factorization_mul hdiv_ne hn0)
    simpa [hmul_div] using h
  have htarget :
      d.factorial.factorization p * (p - 1) + (N + 1) ≤
        (d.factorial / n).factorization p * (p - 1) + u := by
    rw [hfac, Nat.add_mul]
    omega
  exact Ideal.pow_le_pow_right htarget hweighted

set_option linter.style.longLine false in
theorem samePrimeFiniteArtinHasseLogHomogeneousNumerator_factorial_weighted_sub_highPrecision_mem_lambdaIdeal_pow
    (N n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hn1 : 1 ≤ n) (hnd : n ≤ d) :
    (((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
        (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x -
          samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
            (p := p) (K := K)
            (N + d.factorial.factorization p * (p - 1)) n d x)) ∈
      (lambdaIdeal p K) ^ (d.factorial.factorization p * (p - 1) + (N + 1)) :=
  samePrimeFiniteArtinHasseLogHomogeneousNumerator_factorial_weighted_sub_precision_mem_lambdaIdeal_pow
    (p := p) (K := K) N (N + d.factorial.factorization p * (p - 1)) n d hx
    (Nat.le_add_right N (d.factorial.factorization p * (p - 1))) hn1 hnd

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in
-- The proof compares two expanded quotient sums after rewriting a formal
-- coefficient sum to zero, so elaboration needs the same local bump.
theorem samePrimeFiniteArtinHasseLogHomogeneousNumerator_factorial_weighted_sum_mem_lambdaIdeal_pow_of_not_pow
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hd : ¬ ∃ r : ℕ, d = p ^ r) :
    (∑ n ∈ Finset.Icc 1 d,
      ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
        samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
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
          (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) N n d x -
            samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) M n d x)) ∈ I := by
    refine Ideal.sum_mem _ ?_
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnd : n ≤ d := (Finset.mem_Icc.mp hn).2
    simpa [I, D] using
      samePrimeFiniteArtinHasseLogHomogeneousNumerator_factorial_weighted_sub_precision_mem_lambdaIdeal_pow
        (p := p) (K := K) N M n d hx hNM hn1 hnd
  have hsumM_M :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
            (p := p) (K := K) M n d x) ∈
        (lambdaIdeal p K) ^ (M + 1) := by
    have hq :=
      quotient_mk_samePrimeFiniteArtinHasseLogHomogeneousNumerator_factorial_weighted_sum_eq_formal
        (p := p) (K := K) M d hx
    rw [Furtwaengler.FiniteArtinHasseFormal.sum_factorialWeightedLogCoeff_eq_zero_of_not_pow
      p d hd] at hq
    rw [map_zero, mul_zero] at hq
    have hq_zero :
        samePrimeQuotientMap (p := p) (K := K) M
          (∑ n ∈ Finset.Icc 1 d,
            ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
              samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
                (p := p) (K := K) M n d x) = 0 := by
      simpa using hq
    change Ideal.Quotient.mk ((lambdaIdeal p K) ^ (M + 1))
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
            samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) M n d x) = 0 at hq_zero
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq_zero
  have hsumM : (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
            (p := p) (K := K) M n d x) ∈ I := by
    simpa [I, M, D, Nat.add_assoc] using hsumM_M
  have hsplit :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
            (p := p) (K := K) N n d x) =
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) N n d x -
            samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) M n d x)) +
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
            (p := p) (K := K) M n d x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    ring
  rw [hsplit]
  exact I.add_mem hdiff hsumM

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in
-- The power-degree slice repeats the quotient-sum comparison after replacing
-- the formal coefficient sum by its single surviving monomial.
theorem samePrimeFiniteArtinHasseLogHomogeneousNumerator_factorial_weighted_sub_pow_mem_lambdaIdeal_pow
    (N r : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    (∑ n ∈ Finset.Icc 1 (p ^ r),
      (((p ^ r).factorial / n : ℕ) : ValuedIntegerRing p K) *
        (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
            (p := p) (K := K) N n (p ^ r) x -
          if n = p ^ r then x ^ (p ^ r) else 0)) ∈
      (lambdaIdeal p K) ^ ((p ^ r).factorial.factorization p * (p - 1) + (N + 1)) := by
  classical
  let d : ℕ := p ^ r
  let D : ℕ := d.factorial.factorization p * (p - 1)
  let M : ℕ := D + N
  let I : Ideal (ValuedIntegerRing p K) := (lambdaIdeal p K) ^ (D + (N + 1))
  let target : ℕ → ValuedIntegerRing p K := fun n => if n = d then x ^ d else 0
  have hd_ne : d ≠ 0 := pow_ne_zero r (Fact.out : Nat.Prime p).ne_zero
  have hd_mem : d ∈ Finset.Icc 1 d :=
    Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd_ne), le_rfl⟩
  have hNM : N ≤ M := by omega
  have hdiff :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) N n d x -
            samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) M n d x)) ∈ I := by
    refine Ideal.sum_mem _ ?_
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnd : n ≤ d := (Finset.mem_Icc.mp hn).2
    simpa [I, D] using
      samePrimeFiniteArtinHasseLogHomogeneousNumerator_factorial_weighted_sub_precision_mem_lambdaIdeal_pow
        (p := p) (K := K) N M n d hx hNM hn1 hnd
  have hsumM_eq :
      samePrimeQuotientMap (p := p) (K := K) M
          (∑ n ∈ Finset.Icc 1 d,
            ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
              samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
                (p := p) (K := K) M n d x) =
        samePrimeQuotientMap (p := p) (K := K) M
          (((d.factorial / d : ℕ) : ValuedIntegerRing p K) * x ^ d) := by
    have hq :=
      quotient_mk_samePrimeFiniteArtinHasseLogHomogeneousNumerator_factorial_weighted_sum_eq_formal
        (p := p) (K := K) M d hx
    rw [show d = p ^ r from rfl] at hq
    rw [Furtwaengler.FiniteArtinHasseFormal.sum_factorialWeightedLogCoeff_eq_factorial_div_pow
      p r] at hq
    simpa [d, samePrimeQuotientMap, samePrimeRIntegralRatToQuotient, map_mul,
      mul_comm, mul_left_comm, mul_assoc] using hq
  have htarget_sum :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) * target n) =
        ((d.factorial / d : ℕ) : ValuedIntegerRing p K) * x ^ d := by
    calc
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) * target n)
          =
        ((d.factorial / d : ℕ) : ValuedIntegerRing p K) * target d := by
          refine Finset.sum_eq_single (s := Finset.Icc 1 d) (a := d)
            (f := fun n =>
              ((d.factorial / n : ℕ) : ValuedIntegerRing p K) * target n)
            ?main ?not_mem
          · intro n hn hne
            have hne' : n ≠ d := fun h =>
              hne h
            simp [target, hne']
          · intro hd_not
            exact False.elim (hd_not hd_mem)
      _ = ((d.factorial / d : ℕ) : ValuedIntegerRing p K) * x ^ d := by
          simp [target]
  have hsumM_sub_M :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) M n d x - target n)) ∈
        (lambdaIdeal p K) ^ (M + 1) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk ((lambdaIdeal p K) ^ (M + 1))
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
            (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
                (p := p) (K := K) M n d x - target n)) = 0
    have hsplit :
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
            (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
                (p := p) (K := K) M n d x - target n)) =
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
            samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) M n d x) -
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) * target n) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro n _hn
      ring
    rw [hsplit, map_sub]
    change samePrimeQuotientMap (p := p) (K := K) M
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
            samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) M n d x) -
      samePrimeQuotientMap (p := p) (K := K) M
        (∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) * target n) = 0
    rw [hsumM_eq, htarget_sum]
    simp
  have hsumM_sub : (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) M n d x - target n)) ∈ I := by
    simpa [I, M, D, Nat.add_assoc] using hsumM_sub_M
  have hsplit :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) N n d x - target n)) =
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) N n d x -
            samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) M n d x)) +
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) M n d x - target n)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    ring
  have hmain : (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : ValuedIntegerRing p K) *
          (samePrimeFiniteArtinHasseExpCoordLogHomogeneousNumerator
              (p := p) (K := K) N n d x - target n)) ∈ I := by
    rw [hsplit]
    exact I.add_mem hdiff hsumM_sub
  simpa [d, I, D, target] using hmain


end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular

end
