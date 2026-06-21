import BernoulliRegular.CyclotomicUnits.KummerLogNormalization.Part1

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

omit [NumberField.IsCMField K] in
/-- Image in the level-`N + 1` quotient of the rational normalized factorial-weighted log
coefficient, as a signed factorial-weighted coefficient of the mapped Artin-Hasse series. -/
theorem samePrime_rIntegralRatToQuotient_normalizedFactorialWeightedLogCoeff
    (N d n : ℕ) :
    samePrimeRIntegralRatToQuotient (p := p) (K := K) N
        (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) =
      ((d.factorial / n : ℕ) :
          ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
        ((-1 :
          ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
          (PowerSeries.coeff
            (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
            ((PowerSeries.map (samePrimeQuotientMap (p := p) (K := K) N)
                (integralArtinHasseNormalizedExpMinusOneSeries p K - 1)) ^ n) := by
  let q : ValuedIntegerRing p K →+*
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    samePrimeQuotientMap (p := p) (K := K) N
  let φ : Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+*
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    samePrimeRIntegralRatToQuotient (p := p) (K := K) N
  let hA : Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (rationalArtinHasseNormalizedExpMinusOneSeries p - 1) :=
    rationalArtinHasseNormalizedExpMinusOneSeries_sub_one_isPIntegral (p := p)
  let hN : Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (rationalArtinHasseNormalizedExpMinusOneSeries p) :=
    rationalArtinHasseNormalizedExpMinusOneSeries_isPIntegral (p := p)
  have hAps :
      hA.mapTo φ =
        PowerSeries.map q
          (integralArtinHasseNormalizedExpMinusOneSeries p K - 1) := by
    have hsub :
        hA.mapTo φ = hN.mapTo φ - 1 := by
      simpa [hA, hN] using
        Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_sub
          φ hN (Furtwaengler.DieudonneDwork.IsRIntegralPS.one p)
    have hNmap :
        hN.mapTo φ =
          PowerSeries.map q
            (integralArtinHasseNormalizedExpMinusOneSeries p K) := by
      calc
        hN.mapTo φ =
            PowerSeries.map q
              (hN.mapTo (rIntegralRatToValuedInteger p K)) := by
              simpa [hN, φ, q, samePrimeRIntegralRatToQuotient,
                samePrimeQuotientMap] using
                (Furtwaengler.DieudonneDwork.IsRIntegralPS.map_mapTo
                  (rIntegralRatToValuedInteger p K) q hN).symm
        _ =
            PowerSeries.map q
              (integralArtinHasseNormalizedExpMinusOneSeries p K) := by
              rw [rationalArtinHasseNormalizedExpMinusOneSeries_mapTo_valued
                (p := p) (K := K)]
    calc
      hA.mapTo φ = hN.mapTo φ - 1 := hsub
      _ =
          PowerSeries.map q
              (integralArtinHasseNormalizedExpMinusOneSeries p K) - 1 := by
          rw [hNmap]
      _ =
          PowerSeries.map q
            (integralArtinHasseNormalizedExpMinusOneSeries p K - 1) := by
          rw [map_sub, map_one]
  have hcoeff :
      φ (⟨(PowerSeries.coeff (R := ℚ) d)
            ((rationalArtinHasseNormalizedExpMinusOneSeries p - 1) ^ n),
          hA.pow n d⟩ :
          Furtwaengler.DieudonneDwork.rIntegralRatSubring p) =
        (PowerSeries.coeff
          (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
          ((PowerSeries.map q
            (integralArtinHasseNormalizedExpMinusOneSeries p K - 1)) ^ n) := by
    calc
      φ (⟨(PowerSeries.coeff (R := ℚ) d)
            ((rationalArtinHasseNormalizedExpMinusOneSeries p - 1) ^ n),
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
          ((PowerSeries.map q
            (integralArtinHasseNormalizedExpMinusOneSeries p K - 1)) ^ n) := by
          rw [hAps]
  calc
    φ (rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n)
        =
      ((d.factorial / n : ℕ) :
          ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
        ((-1 :
          ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
          φ (⟨(PowerSeries.coeff (R := ℚ) d)
              ((rationalArtinHasseNormalizedExpMinusOneSeries p - 1) ^ n),
            hA.pow n d⟩ :
            Furtwaengler.DieudonneDwork.rIntegralRatSubring p) := by
        simp [rationalArtinHasseNormalizedFactorialWeightedLogCoeff,
          φ, map_mul, map_pow]
    _ =
      ((d.factorial / n : ℕ) :
          ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
        ((-1 :
          ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
          (PowerSeries.coeff
            (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
            ((PowerSeries.map q
              (integralArtinHasseNormalizedExpMinusOneSeries p K - 1)) ^ n) :=
        congrArg (fun y ↦
          ((d.factorial / n : ℕ) :
              ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) *
            ((-1 :
              ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) * y)
          hcoeff

omit [NumberField.IsCMField K] in
@[simp]
theorem integralArtinHasseNormalizedExpMinusOneSeries_coeff (n : ℕ) :
    (PowerSeries.coeff (R := ValuedIntegerRing p K) n)
        (integralArtinHasseNormalizedExpMinusOneSeries p K) =
      (PowerSeries.coeff (R := ValuedIntegerRing p K) (n + 1))
        (integralExpMinusOneSeries p K) := by
  simp [integralArtinHasseNormalizedExpMinusOneSeries]

omit [NumberField.IsCMField K] in
@[simp]
theorem integralArtinHasseNormalizedExpMinusOneSeries_constantCoeff :
    PowerSeries.constantCoeff
        (integralArtinHasseNormalizedExpMinusOneSeries p K) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    integralArtinHasseNormalizedExpMinusOneSeries_coeff, integralExpMinusOneSeries,
    Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_mapTo]
  have hsub :
      (⟨(PowerSeries.coeff (R := ℚ) 1)
          (PadicLogSetup.FormalDwork.expMinusOneSeries p),
        PadicLogSetup.FormalDwork.expMinusOneSeries_isPIntegral p 1⟩ :
          Furtwaengler.DieudonneDwork.rIntegralRatSubring p) = 1 := by
    ext
    simp
  rw [hsub]
  exact map_one (rIntegralRatToValuedInteger p K)

omit [NumberField.IsCMField K] in
@[simp]
theorem integralArtinHasseNormalizedExpMinusOneSeries_map_valuedIntegerCyclotomicEquiv
    (a : CyclotomicUnitDelta p) :
    PowerSeries.map
        (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (integralArtinHasseNormalizedExpMinusOneSeries p K) =
      integralArtinHasseNormalizedExpMinusOneSeries p K := by
  ext n
  rw [PowerSeries.coeff_map, integralArtinHasseNormalizedExpMinusOneSeries_coeff,
    integralExpMinusOneSeries, Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_mapTo]
  exact congrArg Subtype.val
    (Conjugation.valuedIntegerCyclotomicEquiv_rIntegralRatToValuedInteger
    (p := p) (K := K) a
    ⟨(PowerSeries.coeff (R := ℚ) (n + 1))
      (PadicLogSetup.FormalDwork.expMinusOneSeries p),
      PadicLogSetup.FormalDwork.expMinusOneSeries_isPIntegral p (n + 1)⟩)

omit [NumberField.IsCMField K] in
/-- Formal normalized-factor identity for the integral Artin-Hasse series. -/
theorem integralExpMinusOneSeries_eq_X_mul_normalized :
    integralExpMinusOneSeries p K =
      PowerSeries.X *
        integralArtinHasseNormalizedExpMinusOneSeries p K := by
  have hconst : PowerSeries.constantCoeff (integralExpMinusOneSeries p K) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, integralExpMinusOneSeries,
      Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_mapTo]
    have hsub :
        (⟨(PowerSeries.coeff (R := ℚ) 0)
            (PadicLogSetup.FormalDwork.expMinusOneSeries p),
          PadicLogSetup.FormalDwork.expMinusOneSeries_isPIntegral p 0⟩ :
            Furtwaengler.DieudonneDwork.rIntegralRatSubring p) = 0 := by
      ext
      simp
    rw [hsub]
    exact map_zero (rIntegralRatToValuedInteger p K)
  calc
    integralExpMinusOneSeries p K =
        integralExpMinusOneSeries p K -
          PowerSeries.C (PowerSeries.constantCoeff (integralExpMinusOneSeries p K)) := by
          rw [hconst]
          simp
    _ = PowerSeries.X *
          integralArtinHasseNormalizedExpMinusOneSeries p K := by
          simpa [integralArtinHasseNormalizedExpMinusOneSeries] using
            (PowerSeries.sub_const_eq_X_mul_shift (integralExpMinusOneSeries p K))

omit [NumberField.IsCMField K] in
theorem evalIntegralPowerSeriesMod_X_mul
    (F : PowerSeries (ValuedIntegerRing p K))
    {x : DworkCompleteIntegerRing p K}
    (hx : AdicCompletion.evalₐ (lambdaIdeal p K) 1 x = 0)
    (N : ℕ) :
    evalIntegralPowerSeriesMod p K (PowerSeries.X * F) x N =
      AdicCompletion.evalₐ (lambdaIdeal p K) N x *
        evalIntegralPowerSeriesMod p K F x N := by
  classical
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let A : Type _ := R ⧸ I ^ N
  let q : R →+* A := Ideal.Quotient.mk (I ^ N)
  let xN : A := AdicCompletion.evalₐ I N x
  let G : PowerSeries A := PowerSeries.map q F
  have hmap : PowerSeries.map q (PowerSeries.X * F) = PowerSeries.X * G := by
    simp [G]
  change
    (PowerSeries.trunc N (PowerSeries.map q (PowerSeries.X * F))).eval₂
        (RingHom.id A) xN =
      xN * (PowerSeries.trunc N G).eval₂ (RingHom.id A) xN
  rw [hmap]
  cases N with
  | zero =>
      exact
        (quotient_pow_zero_eq_zero (p := p) (K := K) I _).trans
          (quotient_pow_zero_eq_zero (p := p) (K := K) I _).symm
  | succ N =>
      have hxNil : xN ^ (N + 1) = 0 :=
        evalₐ_pow_eq_zero_of_evalₐ_one_eq_zero
          (p := p) (K := K) hx (N + 1)
      rw [Furtwaengler.powerSeries_trunc_eval₂_mul_of_pow_succ_eq_zero
        xN N hxNil PowerSeries.X G]
      cases N with
      | zero =>
          have hxN : xN = 0 := by
            simpa [xN, I] using hx
          simp [hxN]
      | succ N =>
          rw [PowerSeries.trunc_X]
          simp

omit [NumberField.IsCMField K] in
theorem evalIntegralPowerSeries_X_mul
    (F : PowerSeries (ValuedIntegerRing p K))
    {x : DworkCompleteIntegerRing p K}
    (hx : AdicCompletion.evalₐ (lambdaIdeal p K) 1 x = 0) :
    evalIntegralPowerSeries p K (PowerSeries.X * F) x hx =
      x * evalIntegralPowerSeries p K F x hx := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [evalIntegralPowerSeries_evalₐ, map_mul, evalIntegralPowerSeries_evalₐ]
  exact evalIntegralPowerSeriesMod_X_mul (p := p) (K := K) F hx N

omit [NumberField.IsCMField K] in
theorem evalIntegralPowerSeries_expMinusOne_eq_exp_sub_one
    {x : DworkCompleteIntegerRing p K}
    (hx : AdicCompletion.evalₐ (lambdaIdeal p K) 1 x = 0) :
    evalIntegralPowerSeries p K (integralExpMinusOneSeries p K) x hx =
      evalIntegralPowerSeries p K (integralExpSeries p K) x hx - 1 := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [evalIntegralPowerSeries_evalₐ, map_sub, evalIntegralPowerSeries_evalₐ,
    map_one,
    PadicLogSetup.DworkParameter.Conjugation.evalIntegralPowerSeriesMod_expMinusOne_eq_exp_sub_one]

omit [NumberField.IsCMField K] in
/-- Completed evaluation of the normalized Artin-Hasse numerator. -/
noncomputable def artinHasseNormalizedExpMinusOneEval
    (x : DworkCompleteIntegerRing p K)
    (hx : AdicCompletion.evalₐ (lambdaIdeal p K) 1 x = 0) :
    DworkCompleteIntegerRing p K :=
  evalIntegralPowerSeries p K
    (integralArtinHasseNormalizedExpMinusOneSeries p K) x hx

omit [NumberField.IsCMField K] in
/-- In the complete Dwork ring, `E_p(x)-1 = x * A_p(x)` for the normalized
Artin-Hasse factor `A_p(T) = (E_p(T)-1)/T`. -/
theorem artinHasseExp_eval_sub_one_eq_mul_normalized
    {x : DworkCompleteIntegerRing p K}
    (hx : AdicCompletion.evalₐ (lambdaIdeal p K) 1 x = 0) :
    evalIntegralPowerSeries p K (integralExpSeries p K) x hx - 1 =
      x * artinHasseNormalizedExpMinusOneEval p K x hx := by
  rw [← evalIntegralPowerSeries_expMinusOne_eq_exp_sub_one (p := p) (K := K) hx,
    integralExpMinusOneSeries_eq_X_mul_normalized]
  exact evalIntegralPowerSeries_X_mul (p := p) (K := K)
    (integralArtinHasseNormalizedExpMinusOneSeries p K) hx

omit [NumberField.IsCMField K] in
/-- Truncated finite value of the normalized Artin-Hasse factor
`(E_p(T)-1)/T`. -/
def samePrimeFiniteArtinHasseNormalized
    (N : ℕ) (x : ValuedIntegerRing p K) : ValuedIntegerRing p K :=
  (PowerSeries.trunc (N + 1)
      (integralArtinHasseNormalizedExpMinusOneSeries p K)).eval₂
    (RingHom.id (ValuedIntegerRing p K)) x

omit [NumberField.IsCMField K] in
/-- Principal-unit coordinate of the truncated normalized Artin-Hasse factor. -/
def samePrimeFiniteArtinHasseNormalizedCoord
    (N : ℕ) (x : ValuedIntegerRing p K) : ValuedIntegerRing p K :=
  samePrimeFiniteArtinHasseNormalized (p := p) (K := K) N x - 1

omit [NumberField.IsCMField K] in
/-- Truncated normalized Artin-Hasse factor at the Dwork-parameter
approximant. -/
noncomputable def dworkParameterNormalizedApprox (N : ℕ) :
    ValuedIntegerRing p K :=
  samePrimeFiniteArtinHasseNormalized (p := p) (K := K) N
    (dworkParameterApprox p K (N + 1))

omit [NumberField.IsCMField K] in
/-- Truncated normalized Artin-Hasse factor at the scaled Dwork-parameter
approximant. -/
noncomputable def scaledDworkParameterNormalizedApprox
    (a : ZMod p) (N : ℕ) : ValuedIntegerRing p K :=
  samePrimeFiniteArtinHasseNormalized (p := p) (K := K) N
    (scaledDworkParameterApprox p K a (N + 1))

omit [NumberField.IsCMField K] in
/-- Principal-unit coordinate of `dworkParameterNormalizedApprox`. -/
noncomputable def dworkParameterNormalizedCoordApprox (N : ℕ) :
    ValuedIntegerRing p K :=
  dworkParameterNormalizedApprox (p := p) (K := K) N - 1

omit [NumberField.IsCMField K] in
/-- Principal-unit coordinate of `scaledDworkParameterNormalizedApprox`. -/
noncomputable def scaledDworkParameterNormalizedCoordApprox
    (a : ZMod p) (N : ℕ) : ValuedIntegerRing p K :=
  scaledDworkParameterNormalizedApprox (p := p) (K := K) a N - 1

omit [NumberField.IsCMField K] in
theorem dworkParameterNormalizedCoordApprox_eq
    (N : ℕ) :
    dworkParameterNormalizedCoordApprox (p := p) (K := K) N =
      samePrimeFiniteArtinHasseNormalizedCoord (p := p) (K := K) N
        (dworkParameterApprox p K (N + 1)) :=
  rfl

omit [NumberField.IsCMField K] in
theorem scaledDworkParameterNormalizedCoordApprox_eq
    (a : ZMod p) (N : ℕ) :
    scaledDworkParameterNormalizedCoordApprox (p := p) (K := K) a N =
      samePrimeFiniteArtinHasseNormalizedCoord (p := p) (K := K) N
        (scaledDworkParameterApprox p K a (N + 1)) :=
  rfl

omit [NumberField.IsCMField K] in
theorem quotient_mk_dworkParameterNormalizedApprox_eq_evalIntegralPowerSeriesMod
    (N : ℕ) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (dworkParameterNormalizedApprox (p := p) (K := K) N) =
      evalIntegralPowerSeriesMod p K
        (integralArtinHasseNormalizedExpMinusOneSeries p K)
        (dworkParameter p K) (N + 1) := by
  classical
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let q : R →+* R ⧸ I ^ (N + 1) := Ideal.Quotient.mk (I ^ (N + 1))
  change
    q ((PowerSeries.trunc (N + 1)
        (integralArtinHasseNormalizedExpMinusOneSeries p K)).eval₂
        (RingHom.id R) (dworkParameterApprox p K (N + 1))) =
      (PowerSeries.trunc (N + 1)
          (PowerSeries.map q
            (integralArtinHasseNormalizedExpMinusOneSeries p K))).eval₂
        (RingHom.id (R ⧸ I ^ (N + 1)))
        (AdicCompletion.evalₐ I (N + 1) (dworkParameter p K))
  rw [dworkParameter_evalₐ, PowerSeries.eval₂_trunc_eq_sum_range, map_sum,
    PowerSeries.eval₂_trunc_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simp [q, I, map_pow]

omit [NumberField.IsCMField K] in
theorem quotient_mk_scaledDworkParameterNormalizedApprox_eq_evalIntegralPowerSeriesMod
    (a : ZMod p) (N : ℕ) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (scaledDworkParameterNormalizedApprox (p := p) (K := K) a N) =
      evalIntegralPowerSeriesMod p K
        (integralArtinHasseNormalizedExpMinusOneSeries p K)
        (scaledDworkParameter p K a) (N + 1) := by
  classical
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let q : R →+* R ⧸ I ^ (N + 1) := Ideal.Quotient.mk (I ^ (N + 1))
  change
    q ((PowerSeries.trunc (N + 1)
        (integralArtinHasseNormalizedExpMinusOneSeries p K)).eval₂
        (RingHom.id R) (scaledDworkParameterApprox p K a (N + 1))) =
      (PowerSeries.trunc (N + 1)
          (PowerSeries.map q
            (integralArtinHasseNormalizedExpMinusOneSeries p K))).eval₂
        (RingHom.id (R ⧸ I ^ (N + 1)))
        (AdicCompletion.evalₐ I (N + 1) (scaledDworkParameter p K a))
  rw [scaledDworkParameter_evalₐ, PowerSeries.eval₂_trunc_eq_sum_range, map_sum,
    PowerSeries.eval₂_trunc_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simp [q, I, map_pow]

omit [NumberField.IsCMField K] in
theorem evalₐ_artinHasseNormalized_dworkParameter_eq_mk_normalizedApprox
    (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) (N + 1)
        (artinHasseNormalizedExpMinusOneEval p K
          (dworkParameter p K)
          (dworkParameter_evalₐ_one (p := p) (K := K))) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (dworkParameterNormalizedApprox (p := p) (K := K) N) := by
  rw [artinHasseNormalizedExpMinusOneEval, evalIntegralPowerSeries_evalₐ]
  exact (quotient_mk_dworkParameterNormalizedApprox_eq_evalIntegralPowerSeriesMod
    (p := p) (K := K) N).symm

omit [NumberField.IsCMField K] in
theorem evalₐ_artinHasseNormalized_scaledDworkParameter_eq_mk_normalizedApprox
    (a : ZMod p) (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) (N + 1)
        (artinHasseNormalizedExpMinusOneEval p K
          (scaledDworkParameter p K a)
          (scaledDworkParameter_evalₐ_one (p := p) (K := K) a)) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (scaledDworkParameterNormalizedApprox (p := p) (K := K) a N) := by
  rw [artinHasseNormalizedExpMinusOneEval, evalIntegralPowerSeries_evalₐ]
  exact (quotient_mk_scaledDworkParameterNormalizedApprox_eq_evalIntegralPowerSeriesMod
    (p := p) (K := K) a N).symm

omit [NumberField.IsCMField K] in
@[simp] theorem samePrimeFiniteArtinHasseNormalizedCoord_add_one
    (N : ℕ) (x : ValuedIntegerRing p K) :
    samePrimeFiniteArtinHasseNormalizedCoord (p := p) (K := K) N x + 1 =
      samePrimeFiniteArtinHasseNormalized (p := p) (K := K) N x := by
  simp [samePrimeFiniteArtinHasseNormalizedCoord]

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoord_eq_positive_sum
    (N : ℕ) (x : ValuedIntegerRing p K) :
    samePrimeFiniteArtinHasseNormalizedCoord (p := p) (K := K) N x =
      ∑ n ∈ Finset.range N,
        (PowerSeries.coeff (R := ValuedIntegerRing p K) (n + 1))
            (integralArtinHasseNormalizedExpMinusOneSeries p K) *
          x ^ (n + 1) := by
  rw [samePrimeFiniteArtinHasseNormalizedCoord, samePrimeFiniteArtinHasseNormalized,
    PowerSeries.eval₂_trunc_eq_sum_range, Finset.sum_range_succ']
  have hcoeff0 :
      (PowerSeries.coeff (R := ValuedIntegerRing p K) 0)
          (integralArtinHasseNormalizedExpMinusOneSeries p K) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      integralArtinHasseNormalizedExpMinusOneSeries_constantCoeff]
  simp [hcoeff0]

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoord_mem_lambdaIdeal
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseNormalizedCoord (p := p) (K := K) N x ∈
      lambdaIdeal p K := by
  classical
  rw [samePrimeFiniteArtinHasseNormalizedCoord_eq_positive_sum]
  refine Ideal.sum_mem _ ?_
  intro n _hn
  have hpow : x ^ (n + 1) ∈ lambdaIdeal p K :=
    Ideal.pow_le_self (Nat.succ_ne_zero n)
      (Ideal.pow_mem_pow hx (n + 1))
  exact (lambdaIdeal p K).mul_mem_left _ hpow

omit [NumberField.IsCMField K] in
theorem dworkParameterNormalizedCoordApprox_mem_lambdaIdeal
    (N : ℕ) :
    dworkParameterNormalizedCoordApprox (p := p) (K := K) N ∈ lambdaIdeal p K := by
  simpa [dworkParameterNormalizedCoordApprox_eq] using
    samePrimeFiniteArtinHasseNormalizedCoord_mem_lambdaIdeal
      (p := p) (K := K) N
      (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1))

omit [NumberField.IsCMField K] in
theorem scaledDworkParameterNormalizedCoordApprox_mem_lambdaIdeal
    (a : ZMod p) (N : ℕ) :
    scaledDworkParameterNormalizedCoordApprox (p := p) (K := K) a N ∈
      lambdaIdeal p K := by
  simpa [scaledDworkParameterNormalizedCoordApprox_eq] using
    samePrimeFiniteArtinHasseNormalizedCoord_mem_lambdaIdeal
      (p := p) (K := K) N
      (scaledDworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) a (N + 1))

omit [NumberField.IsCMField K] in
/-- Homogeneous bookkeeping polynomial for the normalized Artin-Hasse
principal-unit coordinate. -/
def samePrimeFiniteArtinHasseNormalizedCoordPoly
    (N : ℕ) (x : ValuedIntegerRing p K) :
    Polynomial (ValuedIntegerRing p K) :=
  ∑ n ∈ Finset.range N,
    Polynomial.monomial (n + 1)
      ((PowerSeries.coeff (R := ValuedIntegerRing p K) (n + 1))
        (integralArtinHasseNormalizedExpMinusOneSeries p K) * x ^ (n + 1))

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_eval_one
    (N : ℕ) (x : ValuedIntegerRing p K) :
    (samePrimeFiniteArtinHasseNormalizedCoordPoly
        (p := p) (K := K) N x).eval 1 =
      samePrimeFiniteArtinHasseNormalizedCoord
        (p := p) (K := K) N x := by
  rw [samePrimeFiniteArtinHasseNormalizedCoord_eq_positive_sum]
  simp [samePrimeFiniteArtinHasseNormalizedCoordPoly, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_mem_lambdaIdeal_pow
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) (d : ℕ) :
    (samePrimeFiniteArtinHasseNormalizedCoordPoly
        (p := p) (K := K) N x).coeff d ∈
      (lambdaIdeal p K) ^ d := by
  classical
  rw [samePrimeFiniteArtinHasseNormalizedCoordPoly, Polynomial.finsetSum_coeff]
  refine Ideal.sum_mem _ ?_
  intro n _hn
  by_cases hnd : n + 1 = d
  · subst d
    simpa [Polynomial.coeff_monomial] using
      (((lambdaIdeal p K) ^ (n + 1)).mul_mem_left _
        (Ideal.pow_mem_pow hx (n + 1)))
  · simp [Polynomial.coeff_monomial, hnd]

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_zero
    (N : ℕ) (x : ValuedIntegerRing p K) :
    (samePrimeFiniteArtinHasseNormalizedCoordPoly
        (p := p) (K := K) N x).coeff 0 = 0 := by
  classical
  simp [samePrimeFiniteArtinHasseNormalizedCoordPoly, Polynomial.coeff_monomial]

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_eq_of_pos_le
    (N d : ℕ) (x : ValuedIntegerRing p K) (hd0 : d ≠ 0) (hdN : d ≤ N) :
    (samePrimeFiniteArtinHasseNormalizedCoordPoly
        (p := p) (K := K) N x).coeff d =
      (PowerSeries.coeff (R := ValuedIntegerRing p K) d)
        (integralArtinHasseNormalizedExpMinusOneSeries p K) * x ^ d := by
  classical
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hdmem : d - 1 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  rw [samePrimeFiniteArtinHasseNormalizedCoordPoly, Polynomial.finsetSum_coeff]
  calc
    (∑ n ∈ Finset.range N,
        (Polynomial.monomial (n + 1)
          ((PowerSeries.coeff (R := ValuedIntegerRing p K) (n + 1))
            (integralArtinHasseNormalizedExpMinusOneSeries p K) *
              x ^ (n + 1))).coeff d)
        =
      (Polynomial.monomial ((d - 1) + 1)
          ((PowerSeries.coeff (R := ValuedIntegerRing p K) ((d - 1) + 1))
            (integralArtinHasseNormalizedExpMinusOneSeries p K) *
              x ^ ((d - 1) + 1))).coeff d := by
        refine Finset.sum_eq_single (d - 1) ?_ ?_
        · intro b hb hbne
          have hbne' : b + 1 ≠ d := by
            intro hbd
            apply hbne
            omega
          simp [Polynomial.coeff_monomial, hbne']
        · intro hnot
          exact False.elim (hnot hdmem)
    _ =
      (PowerSeries.coeff (R := ValuedIntegerRing p K) d)
        (integralArtinHasseNormalizedExpMinusOneSeries p K) * x ^ d := by
        have hdsub : (d - 1) + 1 = d := Nat.sub_add_cancel hdpos
        simp [hdsub]

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_eq_zero_of_lt
    (N d : ℕ) (x : ValuedIntegerRing p K) (hdN : N < d) :
    (samePrimeFiniteArtinHasseNormalizedCoordPoly
        (p := p) (K := K) N x).coeff d = 0 := by
  classical
  rw [samePrimeFiniteArtinHasseNormalizedCoordPoly, Polynomial.finsetSum_coeff]
  exact Finset.sum_eq_zero fun n hn ↦
    by
      have hnlt : n < N := Finset.mem_range.mp hn
      have hne : n + 1 ≠ d := by omega
      simp [Polynomial.coeff_monomial, hne]

omit [NumberField.IsCMField K] in
/-- Dummy-variable quotient series whose `T^d` coefficient is the image of
the degree-`d` homogeneous part of `A_p(x) - 1`. -/
def samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries
    (N : ℕ) (x : ValuedIntegerRing p K) :
    PowerSeries (ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) :=
  PowerSeries.rescale
    (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) x)
    (PowerSeries.map (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
      (integralArtinHasseNormalizedExpMinusOneSeries p K - 1))

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_map_eq_quotientSeries
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    ((samePrimeFiniteArtinHasseNormalizedCoordPoly
        (p := p) (K := K) N x).map
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))) :
      PowerSeries (ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1))) =
    samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries
      (p := p) (K := K) N x := by
  classical
  let A : Type _ := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)
  let q : ValuedIntegerRing p K →+* A :=
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
  ext d
  rw [Polynomial.coeff_coe, Polynomial.coeff_map,
    samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries, PowerSeries.coeff_rescale,
    PowerSeries.coeff_map]
  by_cases hd0 : d = 0
  · subst d
    have hcoeff0 :
        (PowerSeries.coeff (R := ValuedIntegerRing p K) 0)
            (integralArtinHasseNormalizedExpMinusOneSeries p K - 1) = 0 := by
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        integralArtinHasseNormalizedExpMinusOneSeries_constantCoeff]
    rw [samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_zero, hcoeff0, map_zero]
    simp
  · by_cases hdN : d ≤ N
    · have hpoly :=
        samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_eq_of_pos_le
          (p := p) (K := K) N d x hd0 hdN
      have hcoeff_sub :
          (PowerSeries.coeff (R := ValuedIntegerRing p K) d)
              (integralArtinHasseNormalizedExpMinusOneSeries p K - 1) =
            (PowerSeries.coeff (R := ValuedIntegerRing p K) d)
              (integralArtinHasseNormalizedExpMinusOneSeries p K) := by
        simp [hd0]
      rw [hpoly, hcoeff_sub, map_mul, map_pow]
      ring
    · have hdNlt : N < d := Nat.lt_of_not_ge hdN
      have hpoly :=
        samePrimeFiniteArtinHasseNormalizedCoordPoly_coeff_eq_zero_of_lt
          (p := p) (K := K) N d x hdNlt
      have hle : N + 1 ≤ d := Nat.succ_le_of_lt hdNlt
      have hxpow : x ^ d ∈ (lambdaIdeal p K) ^ (N + 1) :=
        Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hx d)
      have hxzero : q (x ^ d) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hxpow
      have hpowmap : (q x) ^ d = q (x ^ d) := (map_pow q x d).symm
      rw [hpoly, map_zero, hpowmap, hxzero, zero_mul]

omit [NumberField.IsCMField K] in
theorem quotient_mk_samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_eq
    (N n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (((samePrimeFiniteArtinHasseNormalizedCoordPoly
          (p := p) (K := K) N x) ^ n).coeff d) =
      (PowerSeries.coeff
        (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
        ((samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries
          (p := p) (K := K) N x) ^ n) := by
  let A : Type _ := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)
  let q : ValuedIntegerRing p K →+* A :=
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
  let P : Polynomial (ValuedIntegerRing p K) :=
    samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N x
  have hseries :
      ((P.map q : Polynomial A) : PowerSeries A) =
        samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries
          (p := p) (K := K) N x := by
    simpa [P, q, A] using
      samePrimeFiniteArtinHasseNormalizedCoordPoly_map_eq_quotientSeries
        (p := p) (K := K) N hx
  calc
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) ((P ^ n).coeff d)
        =
      (P.map q ^ n).coeff d := by
        rw [← Polynomial.map_pow, Polynomial.coeff_map]
    _ =
      (PowerSeries.coeff (R := A) d)
          (((P.map q : Polynomial A) : PowerSeries A) ^ n) := by
        rw [← Polynomial.coe_pow, Polynomial.coeff_coe]
    _ =
      (PowerSeries.coeff (R := A) d)
        ((samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries
          (p := p) (K := K) N x) ^ n) := by
        rw [hseries]

omit [NumberField.IsCMField K] in
theorem coeff_samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries_pow
    (N n d : ℕ) (x : ValuedIntegerRing p K) :
    (PowerSeries.coeff
        (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
        ((samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries
          (p := p) (K := K) N x) ^ n) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) (x ^ d) *
        (PowerSeries.coeff
          (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
          ((PowerSeries.map (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
            (integralArtinHasseNormalizedExpMinusOneSeries p K - 1)) ^ n) := by
  let A : Type _ := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)
  let q : ValuedIntegerRing p K →+* A :=
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
  let xbar : A := q x
  let F : PowerSeries A :=
    PowerSeries.map q (integralArtinHasseNormalizedExpMinusOneSeries p K - 1)
  calc
    (PowerSeries.coeff (R := A) d)
        ((samePrimeFiniteArtinHasseNormalizedCoordQuotientSeries
          (p := p) (K := K) N x) ^ n)
        =
      (PowerSeries.coeff (R := A) d) ((PowerSeries.rescale xbar F) ^ n) := by
        rfl
    _ =
      (PowerSeries.coeff (R := A) d) (PowerSeries.rescale xbar (F ^ n)) := by
        rw [(map_pow (PowerSeries.rescale xbar) F n).symm]
    _ =
      xbar ^ d * (PowerSeries.coeff (R := A) d) (F ^ n) := by
        rw [PowerSeries.coeff_rescale]
    _ =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) (x ^ d) *
        (PowerSeries.coeff
          (R := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) d)
          ((PowerSeries.map (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
            (integralArtinHasseNormalizedExpMinusOneSeries p K - 1)) ^ n) := by
        simp [xbar, q, A, F]

omit [NumberField.IsCMField K] in
/-- Signed numerator of the normalized homogeneous logarithm term, before the
same-prime division by `n`. -/
def samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousNumerator
    (N n d : ℕ) (x : ValuedIntegerRing p K) : ValuedIntegerRing p K :=
  ((-1 : ValuedIntegerRing p K) ^ (n + 1)) *
    ((samePrimeFiniteArtinHasseNormalizedCoordPoly
      (p := p) (K := K) N x) ^ n).coeff d

end CyclotomicUnits

end BernoulliRegular

end
