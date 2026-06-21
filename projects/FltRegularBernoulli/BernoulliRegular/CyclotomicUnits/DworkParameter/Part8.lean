module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.Part7

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

/-- The Cauchy sequence of inverse-series truncations defining
`G_p(lambda)` in the `lambda`-adic completion. -/
def dworkParameterCauchySeq :
    AdicCompletion.AdicCauchySequence (lambdaIdeal p K) (ValuedIntegerRing p K) where
  val N := dworkParameterApprox p K N
  property := by
    intro M N hMN
    exact dworkParameterApprox_smodEq (p := p) (K := K) hMN

/-- The corrected Dwork parameter `G_p(lambda)` as an element of the
`lambda`-adic completion of the valuation integer ring. -/
def dworkParameter : DworkCompleteIntegerRing p K :=
  AdicCompletion.mkₐ (lambdaIdeal p K) (dworkParameterCauchySeq p K)

@[simp]
theorem dworkParameter_evalₐ (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N (dworkParameter p K) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
        (dworkParameterApprox p K N) := by
  simp [dworkParameter, dworkParameterCauchySeq]

theorem dworkParameter_evalₐ_one :
    AdicCompletion.evalₐ (lambdaIdeal p K) 1 (dworkParameter p K) = 0 := by
  rw [dworkParameter_evalₐ]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simpa using dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) 1

/-- The corrected parameter is congruent to `lambda` modulo `lambda^2`. -/
theorem dworkParameter_evalₐ_two :
    AdicCompletion.evalₐ (lambdaIdeal p K) 2 (dworkParameter p K) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ 2)
        (valuedCyclotomicLambdaInteger p K) := by
  rw [dworkParameter_evalₐ, dworkParameterApprox_two]

theorem dworkParameter_sub_lambda_mem_sq :
    AdicCompletion.evalₐ (lambdaIdeal p K) 2
        (dworkParameter p K -
          AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
            (valuedCyclotomicLambdaInteger p K)) = 0 := by
  rw [map_sub, dworkParameter_evalₐ_two, AdicCompletion.evalₐ_of, sub_self]

theorem dworkParameter_sub_dworkCompleteLambda_mem_sq :
    dworkParameter p K - dworkCompleteLambda p K ∈
      (dworkCompleteLambdaIdeal p K) ^ 2 :=
  dworkComplete_mem_lambdaIdeal_pow_of_evalₐ_eq_zero
    (p := p) (K := K) (by
      change AdicCompletion.evalₐ (lambdaIdeal p K) 2
          (dworkParameter p K -
            AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
              (valuedCyclotomicLambdaInteger p K)) = 0
      exact dworkParameter_sub_lambda_mem_sq (p := p) (K := K))

theorem dworkParameter_eq_dworkCompleteLambda_mul_unit :
    ∃ u : (DworkCompleteIntegerRing p K)ˣ,
      dworkParameter p K = dworkCompleteLambda p K * (u : DworkCompleteIntegerRing p K) := by
  let S : Type _ := DworkCompleteIntegerRing p K
  let lam : S := dworkCompleteLambda p K
  have hmem : dworkParameter p K - lam ∈
      Ideal.span ({lam} : Set S) ^ 2 := by
    simpa [lam, dworkCompleteLambdaIdeal_eq_span (p := p) (K := K)] using
      dworkParameter_sub_dworkCompleteLambda_mem_sq (p := p) (K := K)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
  rcases hmem with ⟨a, ha⟩
  have hlam_mem : lam ∈ dworkCompleteLambdaIdeal p K := by
    rw [dworkCompleteLambdaIdeal_eq_span (p := p) (K := K)]
    exact Ideal.mem_span_singleton_self lam
  have ha_lam_mem : a * lam ∈ dworkCompleteLambdaIdeal p K :=
    (dworkCompleteLambdaIdeal p K).mul_mem_left a hlam_mem
  have hunit : IsUnit (1 + a * lam) :=
    isUnit_one_add_of_mem_dworkCompleteLambdaIdeal
      (p := p) (K := K) ha_lam_mem
  refine ⟨hunit.unit, ?_⟩
  have hunit_val : (hunit.unit : S) = 1 + a * lam := hunit.unit_spec
  calc
    dworkParameter p K = lam + (dworkParameter p K - lam) := by abel
    _ = lam + a * lam ^ 2 := by rw [← ha]
    _ = lam * (1 + a * lam) := by ring
    _ = lam * (hunit.unit : S) := by rw [hunit_val]

theorem dworkCompleteLambda_mul_eq_zero
    {x : DworkCompleteIntegerRing p K}
    (hx : dworkCompleteLambda p K * x = 0) :
    x = 0 := by
  have hx_smul : valuedCyclotomicLambdaInteger p K • x = 0 := by
    rw [Algebra.smul_def, AdicCompletion.algebraMap_apply]
    exact hx
  exact dworkComplete_smul_eq_zero_of_ne_zero
    (p := p) (K := K)
    (valuedCyclotomicLambdaInteger_ne_zero (p := p) (K := K)) hx_smul

theorem dworkParameter_mul_eq_zero
    {x : DworkCompleteIntegerRing p K}
    (hx : dworkParameter p K * x = 0) :
    x = 0 := by
  rcases dworkParameter_eq_dworkCompleteLambda_mul_unit (p := p) (K := K)
    with ⟨u, hu⟩
  have hux : (u : DworkCompleteIntegerRing p K) * x = 0 := by
    apply dworkCompleteLambda_mul_eq_zero (p := p) (K := K)
    simpa [hu, mul_assoc] using hx
  have hcancel := congrArg (fun y : DworkCompleteIntegerRing p K ↦
      ((↑u⁻¹ : DworkCompleteIntegerRing p K) * y)) hux
  simpa [mul_assoc] using hcancel

theorem quotient_mk_dworkParameterApprox_eq_trunc_eval (N : ℕ) :
    let A : Type _ := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N
    let φ : ValuedIntegerRing p K →+* A :=
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
    let Ips : PowerSeries A := PowerSeries.map φ (integralInverseSeries p K)
    let lambdabar : A :=
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ N) (valuedCyclotomicLambdaInteger p K)
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ N) (dworkParameterApprox p K N) =
      (PowerSeries.trunc N Ips).eval₂ (RingHom.id A) lambdabar := by
  classical
  dsimp only
  rw [dworkParameterApprox_eq_sum_range]
  rw [map_sum]
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simp [map_pow]

@[simp]
theorem valuedCyclotomicZetaInteger_eq_one_add_lambda :
    valuedCyclotomicZetaInteger p K =
      1 + valuedCyclotomicLambdaInteger p K := by
  ext
  simp [valuedCyclotomicZetaInteger, valuedCyclotomicLambdaInteger,
    Furtwaengler.KummerArtinHasse.lambdaValuedZetaInteger,
    Furtwaengler.KummerArtinHasse.lambdaValuedPiInteger, map_sub]

@[simp]
theorem valuedCyclotomicZetaInteger_pow_eq_one :
    valuedCyclotomicZetaInteger p K ^ p = 1 := by
  ext
  change valuedCyclotomicZeta p K ^ p = 1
  rw [valuedCyclotomicZeta_pow_eq_one]

/-- The valuation-side integer corresponding to the conjugate
`zeta_p⁻¹ - 1 = zeta_p^(p-1) - 1`. -/
def valuedCyclotomicConjugateLambdaInteger : ValuedIntegerRing p K :=
  valuedCyclotomicZetaInteger p K ^ (p - 1) - 1

/-- Denominator-cleared form of `zeta_p⁻¹ - 1 = -lambda / (1 + lambda)` in
the valuation integer ring. -/
theorem valuedCyclotomicConjugateLambdaInteger_mul_one_add_lambda :
    valuedCyclotomicConjugateLambdaInteger p K *
        (1 + valuedCyclotomicLambdaInteger p K) =
      -valuedCyclotomicLambdaInteger p K := by
  let ζ : ValuedIntegerRing p K := valuedCyclotomicZetaInteger p K
  let lam : ValuedIntegerRing p K := valuedCyclotomicLambdaInteger p K
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hp_succ : p - 1 + 1 = p :=
    Nat.sub_one_add_one (Nat.ne_of_gt hp_pos)
  have hζpow : ζ ^ (p - 1) * ζ = 1 := by
    rw [← pow_succ, hp_succ]
    exact valuedCyclotomicZetaInteger_pow_eq_one (p := p) (K := K)
  have hzetalam : ζ = 1 + lam := by
    change valuedCyclotomicZetaInteger p K =
      1 + valuedCyclotomicLambdaInteger p K
    exact valuedCyclotomicZetaInteger_eq_one_add_lambda (p := p) (K := K)
  calc
    valuedCyclotomicConjugateLambdaInteger p K *
        (1 + valuedCyclotomicLambdaInteger p K) =
        (ζ ^ (p - 1) - 1) * ζ := by
          change (ζ ^ (p - 1) - 1) * (1 + lam) =
            (ζ ^ (p - 1) - 1) * ζ
          rw [← hzetalam]
    _ = ζ ^ (p - 1) * ζ - ζ := by
          ring
    _ = 1 - ζ := by
          rw [hζpow]
    _ = -lam := by
          rw [hzetalam]
          ring
    _ = -valuedCyclotomicLambdaInteger p K := rfl

/-- The completed image of the conjugate lambda parameter
`zeta_p⁻¹ - 1`. -/
def dworkCompleteConjugateLambda : DworkCompleteIntegerRing p K :=
  AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
    (valuedCyclotomicConjugateLambdaInteger p K)

/-- Denominator-cleared conjugation formula for the completed lambda
parameter. -/
theorem dworkCompleteConjugateLambda_mul_one_add_lambda :
    dworkCompleteConjugateLambda p K * (1 + dworkCompleteLambda p K) =
      -dworkCompleteLambda p K := by
  let R : Type _ := ValuedIntegerRing p K
  let S : Type _ := DworkCompleteIntegerRing p K
  let φ : R →+* S := algebraMap R S
  have h := congrArg φ
    (valuedCyclotomicConjugateLambdaInteger_mul_one_add_lambda
      (p := p) (K := K))
  rw [map_mul, map_add, map_one, map_neg] at h
  exact h

/-- The same-prime conjugate lambda coordinate is still lambda-adically small. -/
theorem valuedCyclotomicConjugateLambdaInteger_mem_lambdaIdeal :
    valuedCyclotomicConjugateLambdaInteger p K ∈ lambdaIdeal p K := by
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let ζ : R := valuedCyclotomicZetaInteger p K
  have hζ_sub_one : ζ - 1 ∈ I := by
    have hζ : ζ = 1 + valuedCyclotomicLambdaInteger p K := by
      change valuedCyclotomicZetaInteger p K =
        1 + valuedCyclotomicLambdaInteger p K
      exact valuedCyclotomicZetaInteger_eq_one_add_lambda (p := p) (K := K)
    rw [hζ]
    simp [I, valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K)]
  simpa [valuedCyclotomicConjugateLambdaInteger, ζ, I] using
    Furtwaengler.pow_sub_one_mem_of_sub_one_mem ζ (p - 1) hζ_sub_one

@[simp]
theorem dworkCompleteConjugateLambda_evalₐ (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N
        (dworkCompleteConjugateLambda p K) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
        (valuedCyclotomicConjugateLambdaInteger p K) := by
  simp [dworkCompleteConjugateLambda]

theorem dworkCompleteConjugateLambda_evalₐ_one :
    AdicCompletion.evalₐ (lambdaIdeal p K) 1
        (dworkCompleteConjugateLambda p K) = 0 := by
  rw [dworkCompleteConjugateLambda_evalₐ]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (by
    simpa using valuedCyclotomicConjugateLambdaInteger_mem_lambdaIdeal
      (p := p) (K := K))

/-- The inverse-series parameter obtained by evaluating `G_p` at the conjugate
lambda coordinate `zeta_p⁻¹ - 1`.  The remaining CU-09d bridge is to identify
this element with the image of `dworkParameter` under an honest completed
complex-conjugation automorphism. -/
def dworkConjugateParameter : DworkCompleteIntegerRing p K :=
  evalIntegralPowerSeries p K (integralInverseSeries p K)
    (dworkCompleteConjugateLambda p K)
    (dworkCompleteConjugateLambda_evalₐ_one (p := p) (K := K))

@[simp]
theorem dworkConjugateParameter_evalₐ (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N
        (dworkConjugateParameter p K) =
      evalIntegralPowerSeriesMod p K (integralInverseSeries p K)
        (dworkCompleteConjugateLambda p K) N := by
  simp [dworkConjugateParameter]

theorem neg_pow_eq_zero_of_pow_eq_zero {A : Type*} [Ring A] {a : A} {n : ℕ}
    (h : a ^ n = 0) : (-a) ^ n = 0 := by
  rw [neg_pow, h, mul_zero]

theorem powerSeries_trunc_eval₂_one_add_X_of_pow_succ_eq_zero
    {A : Type*} [CommRing A] (a : A) (N : ℕ) (ha : a ^ (N + 1) = 0) :
    (PowerSeries.trunc (N + 1) (1 + (PowerSeries.X : PowerSeries A))).eval₂
        (RingHom.id A) a = 1 + a := by
  cases N with
  | zero =>
      have ha0 : a = 0 := by
        simpa using ha
      have htrunc :
          PowerSeries.trunc 1 (1 + (PowerSeries.X : PowerSeries A)) =
            (1 : Polynomial A) := by
        calc
          PowerSeries.trunc 1 (1 + (PowerSeries.X : PowerSeries A)) =
              PowerSeries.trunc 1 (1 : PowerSeries A) +
                PowerSeries.trunc 1 (PowerSeries.X : PowerSeries A) :=
              LinearMap.map_add (PowerSeries.trunc (R := A) 1)
                (1 : PowerSeries A) (PowerSeries.X : PowerSeries A)
          _ = (1 : Polynomial A) := by
              rw [PowerSeries.trunc_one 0, PowerSeries.trunc_one_X, add_zero]
      rw [ha0, htrunc]
      simp
  | succ N =>
      change
        (PowerSeries.trunc (N + 2) (1 + (PowerSeries.X : PowerSeries A))).eval₂
            (RingHom.id A) a = 1 + a
      have htrunc :
          PowerSeries.trunc (N + 2) (1 + (PowerSeries.X : PowerSeries A)) =
            (1 : Polynomial A) + Polynomial.X := by
        calc
          PowerSeries.trunc (N + 2) (1 + (PowerSeries.X : PowerSeries A)) =
              PowerSeries.trunc (N + 2) (1 : PowerSeries A) +
                PowerSeries.trunc (N + 2) (PowerSeries.X : PowerSeries A) :=
              LinearMap.map_add (PowerSeries.trunc (R := A) (N + 2))
                (1 : PowerSeries A) (PowerSeries.X : PowerSeries A)
          _ = (1 : Polynomial A) + Polynomial.X := by
              rw [PowerSeries.trunc_one (N + 1), PowerSeries.trunc_X N]
      rw [htrunc]
      simp

theorem powerSeries_trunc_eval₂_neg_X_of_pow_succ_eq_zero
    {A : Type*} [CommRing A] (a : A) (N : ℕ) (ha : a ^ (N + 1) = 0) :
    (PowerSeries.trunc (N + 1) (-(PowerSeries.X : PowerSeries A))).eval₂
        (RingHom.id A) a = -a := by
  cases N with
  | zero =>
      have htrunc :
          PowerSeries.trunc 1 (-(PowerSeries.X : PowerSeries A)) = 0 := by
        calc
          PowerSeries.trunc 1 (-(PowerSeries.X : PowerSeries A)) =
              -PowerSeries.trunc 1 (PowerSeries.X : PowerSeries A) :=
              LinearMap.map_neg (PowerSeries.trunc (R := A) 1)
                (PowerSeries.X : PowerSeries A)
          _ = 0 := by
              rw [PowerSeries.trunc_one_X, neg_zero]
      have ha0 : a = 0 := by
        simpa using ha
      rw [ha0, htrunc]
      simp
  | succ N =>
      change
        (PowerSeries.trunc (N + 2) (-(PowerSeries.X : PowerSeries A))).eval₂
            (RingHom.id A) a = -a
      have htrunc :
          PowerSeries.trunc (N + 2) (-(PowerSeries.X : PowerSeries A)) =
            -(Polynomial.X : Polynomial A) := by
        calc
          PowerSeries.trunc (N + 2) (-(PowerSeries.X : PowerSeries A)) =
              -PowerSeries.trunc (N + 2) (PowerSeries.X : PowerSeries A) :=
              LinearMap.map_neg (PowerSeries.trunc (R := A) (N + 2))
                (PowerSeries.X : PowerSeries A)
          _ = -(Polynomial.X : Polynomial A) := by
              rw [PowerSeries.trunc_X N]
      rw [htrunc]
      simp

theorem quotient_pow_zero_eq_zero (I : Ideal (ValuedIntegerRing p K))
    (x : ValuedIntegerRing p K ⧸ I ^ 0) : x = 0 := by
  refine Quotient.inductionOn' x ?_
  intro r
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simp)

set_option maxHeartbeats 1000000 in
-- The quotient-local power-series comparison unfolds several adic quotient aliases.
theorem evalIntegralPowerSeriesMod_expMinusOne_neg_dworkParameter_eq_conjugateLambda
    (hp_two : 2 < p) (N : ℕ) :
    evalIntegralPowerSeriesMod p K (integralExpMinusOneSeries p K)
        (-(dworkParameter p K)) N =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
        (valuedCyclotomicConjugateLambdaInteger p K) := by
  classical
  cases N with
  | zero =>
      trans 0
      · exact quotient_pow_zero_eq_zero (p := p) (K := K) (lambdaIdeal p K) _
      · symm
        exact quotient_pow_zero_eq_zero (p := p) (K := K) (lambdaIdeal p K) _
  | succ M =>
      let I : Ideal (ValuedIntegerRing p K) := lambdaIdeal p K
      let A : Type _ := ValuedIntegerRing p K ⧸ I ^ (M + 1)
      letI : CommRing A := by
        dsimp [A]
        infer_instance
      letI : SeminormedCommRing A := by
        dsimp [A]
        infer_instance
      let q : ValuedIntegerRing p K →+* A := Ideal.Quotient.mk (I ^ (M + 1))
      let φ : Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+* A :=
        q.comp (rIntegralRatToValuedInteger p K)
      let G : PowerSeries A := (FormalDwork.inverseSeries_isPIntegral p).mapTo φ
      let H : PowerSeries A := (FormalDwork.expMinusOneSeries_isPIntegral p).mapTo φ
      let lambdabar : A := q (valuedCyclotomicLambdaInteger p K)
      let cbar : A := q (valuedCyclotomicConjugateLambdaInteger p K)
      let gamma : A :=
        (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A) lambdabar
      have hG_eq :
          PowerSeries.map q (integralInverseSeries p K) = G := by
        simp [G, φ, integralInverseSeries,
          Furtwaengler.DieudonneDwork.IsRIntegralPS.map_mapTo]
      have hH_eq :
          PowerSeries.map q (integralExpMinusOneSeries p K) = H := by
        simp [H, φ, integralExpMinusOneSeries,
          Furtwaengler.DieudonneDwork.IsRIntegralPS.map_mapTo]
      have hgamma_eval :
          AdicCompletion.evalₐ I (M + 1) (dworkParameter p K) = gamma := by
        calc
          AdicCompletion.evalₐ I (M + 1) (dworkParameter p K) =
              Ideal.Quotient.mk (I ^ (M + 1))
                (dworkParameterApprox p K (M + 1)) := by
                change
                  AdicCompletion.evalₐ (lambdaIdeal p K) (M + 1)
                      (dworkParameter p K) =
                    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (M + 1))
                      (dworkParameterApprox p K (M + 1))
                rw [dworkParameter_evalₐ]
          _ = gamma := by
                show Ideal.Quotient.mk (I ^ (M + 1))
                    (dworkParameterApprox p K (M + 1)) =
                  (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A) lambdabar
                rw [← hG_eq]
                exact quotient_mk_dworkParameterApprox_eq_trunc_eval
                  (p := p) (K := K) (M + 1)
      have hlambdaNil : lambdabar ^ (M + 1) = 0 := by
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact valuedCyclotomicLambdaInteger_pow_mem_lambdaIdeal_pow
          (p := p) (K := K) (M + 1)
      have hgammaNil : gamma ^ (M + 1) = 0 := by
        rw [← hgamma_eval]
        exact evalₐ_pow_eq_zero_of_evalₐ_one_eq_zero
          (p := p) (K := K) (dworkParameter_evalₐ_one (p := p) (K := K)) (M + 1)
      have hnegGammaNil : (-gamma) ^ (M + 1) = 0 :=
        neg_pow_eq_zero_of_pow_eq_zero hgammaNil
      have hG0 : PowerSeries.constantCoeff G = 0 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        rw [Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_mapTo]
        have hcoeff0 :
            (PowerSeries.coeff (R := ℚ) 0) (FormalDwork.inverseSeries p) = 0 := by
          rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
          exact FormalDwork.inverseSeries_constantCoeff p
        have hsubzero :
            (⟨(PowerSeries.coeff (R := ℚ) 0) (FormalDwork.inverseSeries p),
                FormalDwork.inverseSeries_isPIntegral p 0⟩ :
              Furtwaengler.DieudonneDwork.rIntegralRatSubring p) = 0 := by
          ext
          exact hcoeff0
        rw [hsubzero]
        exact map_zero φ
      have hH0 : PowerSeries.constantCoeff H = 0 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        rw [Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_mapTo]
        have hcoeff0 :
            (PowerSeries.coeff (R := ℚ) 0) (FormalDwork.expMinusOneSeries p) = 0 := by
          rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
          exact FormalDwork.expMinusOneSeries_constantCoeff p
        have hsubzero :
            (⟨(PowerSeries.coeff (R := ℚ) 0) (FormalDwork.expMinusOneSeries p),
                FormalDwork.expMinusOneSeries_isPIntegral p 0⟩ :
              Furtwaengler.DieudonneDwork.rIntegralRatSubring p) = 0 := by
          ext
          exact hcoeff0
        rw [hsubzero]
        exact map_zero φ
      have hNegEval :
          (PowerSeries.trunc (M + 1) (-G)).eval₂ (RingHom.id A) lambdabar =
            -gamma := by
        simp [gamma]
      have hNegG0 : PowerSeries.constantCoeff (-G) = 0 := by
        simp [hG0]
      have hNegEvalNil :
          ((PowerSeries.trunc (M + 1) (-G)).eval₂ (RingHom.id A) lambdabar) ^
              (M + 1) = 0 := by
        rw [hNegEval]
        exact hnegGammaNil
      have hcomp :
          (PowerSeries.trunc (M + 1) (PowerSeries.subst (-G) H)).eval₂
              (RingHom.id A) lambdabar =
            (PowerSeries.trunc (M + 1) H).eval₂ (RingHom.id A) (-gamma) := by
        have h := powerSeries_trunc_eval₂_subst_of_pow_succ_eq_zero
          (a := lambdabar) (N := M) hlambdaNil
          (G := -G) hNegG0 hNegEvalNil H
        calc
          (PowerSeries.trunc (M + 1) (PowerSeries.subst (-G) H)).eval₂
              (RingHom.id A) lambdabar =
            (PowerSeries.trunc (M + 1) H).eval₂ (RingHom.id A)
              ((PowerSeries.trunc (M + 1) (-G)).eval₂ (RingHom.id A) lambdabar) := h
          _ = (PowerSeries.trunc (M + 1) H).eval₂ (RingHom.id A) (-gamma) := by
            rw [hNegEval]
      have hOneXEval :
          (PowerSeries.trunc (M + 1) (1 + (PowerSeries.X : PowerSeries A))).eval₂
              (RingHom.id A) lambdabar = 1 + lambdabar :=
        powerSeries_trunc_eval₂_one_add_X_of_pow_succ_eq_zero lambdabar M hlambdaNil
      have hNegXEval :
          (PowerSeries.trunc (M + 1) (-(PowerSeries.X : PowerSeries A))).eval₂
              (RingHom.id A) lambdabar = -lambdabar :=
        powerSeries_trunc_eval₂_neg_X_of_pow_succ_eq_zero lambdabar M hlambdaNil
      have hseries :
          PowerSeries.subst (-G) H * (1 + (PowerSeries.X : PowerSeries A)) =
            -(PowerSeries.X : PowerSeries A) :=
        FormalDwork.expMinusOneSeries_mapTo_subst_neg_inverse_mul_one_add_X_eq_neg_X
          (p := p) φ hp_two
      have hevalSeries := congrArg
        (fun S : PowerSeries A ↦
          (PowerSeries.trunc (M + 1) S).eval₂ (RingHom.id A) lambdabar)
        hseries
      have hHmul :
          ((PowerSeries.trunc (M + 1) H).eval₂ (RingHom.id A) (-gamma)) *
              (1 + lambdabar) = -lambdabar := by
        change
          (PowerSeries.trunc (M + 1)
              (PowerSeries.subst (-G) H * (1 + (PowerSeries.X : PowerSeries A)))).eval₂
                (RingHom.id A) lambdabar =
            (PowerSeries.trunc (M + 1) (-(PowerSeries.X : PowerSeries A))).eval₂
                (RingHom.id A) lambdabar at hevalSeries
        have hmulEval :=
          Furtwaengler.powerSeries_trunc_eval₂_mul_of_pow_succ_eq_zero
            lambdabar M hlambdaNil (PowerSeries.subst (-G) H)
            (1 + (PowerSeries.X : PowerSeries A))
        calc
          ((PowerSeries.trunc (M + 1) H).eval₂ (RingHom.id A) (-gamma)) *
              (1 + lambdabar) =
            (PowerSeries.trunc (M + 1) (PowerSeries.subst (-G) H)).eval₂
                (RingHom.id A) lambdabar *
              (PowerSeries.trunc (M + 1) (1 + (PowerSeries.X : PowerSeries A))).eval₂
                (RingHom.id A) lambdabar := by
              rw [hcomp, hOneXEval]
          _ =
            (PowerSeries.trunc (M + 1)
              (PowerSeries.subst (-G) H * (1 + (PowerSeries.X : PowerSeries A)))).eval₂
                (RingHom.id A) lambdabar :=
              hmulEval.symm
          _ = (PowerSeries.trunc (M + 1) (-(PowerSeries.X : PowerSeries A))).eval₂
                (RingHom.id A) lambdabar := hevalSeries
          _ = -lambdabar := hNegXEval
      have hcMul : cbar * (1 + lambdabar) = -lambdabar := by
        change
          q (valuedCyclotomicConjugateLambdaInteger p K) *
              (1 + q (valuedCyclotomicLambdaInteger p K)) =
            -q (valuedCyclotomicLambdaInteger p K)
        have h := congrArg q
          (valuedCyclotomicConjugateLambdaInteger_mul_one_add_lambda
            (p := p) (K := K))
        change
          q (valuedCyclotomicConjugateLambdaInteger p K *
              (1 + valuedCyclotomicLambdaInteger p K)) =
            q (-(valuedCyclotomicLambdaInteger p K)) at h
        simpa only [map_mul, map_add, map_one, map_neg] using h
      have hUnit : IsUnit (1 + lambdabar) := by
        have hpow : (1 + lambdabar) ^ p = 1 := by
          have h := congrArg q
            (valuedCyclotomicZetaInteger_pow_eq_one (p := p) (K := K))
          change q ((valuedCyclotomicZetaInteger p K) ^ p) = q 1 at h
          rw [map_pow, map_one] at h
          have hzeta :
              q (valuedCyclotomicZetaInteger p K) = 1 + lambdabar := by
            rw [valuedCyclotomicZetaInteger_eq_one_add_lambda, map_add, map_one]
          rw [hzeta] at h
          exact h
        exact IsUnit.of_pow_eq_one hpow (Nat.ne_of_gt (Fact.out : Nat.Prime p).pos)
      have hHeq :
          (PowerSeries.trunc (M + 1) H).eval₂ (RingHom.id A) (-gamma) = cbar := by
        apply hUnit.mul_right_cancel
        calc
          ((PowerSeries.trunc (M + 1) H).eval₂ (RingHom.id A) (-gamma)) *
              (1 + lambdabar) = -lambdabar := hHmul
          _ = cbar * (1 + lambdabar) := hcMul.symm
      calc
        evalIntegralPowerSeriesMod p K (integralExpMinusOneSeries p K)
            (-(dworkParameter p K)) (M + 1)
            =
          (PowerSeries.trunc (M + 1) H).eval₂ (RingHom.id A) (-gamma) := by
            rw [evalIntegralPowerSeriesMod]
            change
              (PowerSeries.trunc (M + 1)
                (PowerSeries.map q (integralExpMinusOneSeries p K))).eval₂
                  (RingHom.id A)
                  (AdicCompletion.evalₐ I (M + 1) (-(dworkParameter p K))) =
                (PowerSeries.trunc (M + 1) H).eval₂ (RingHom.id A) (-gamma)
            rw [hH_eq, map_neg, hgamma_eval]
        _ = cbar := hHeq
        _ = Ideal.Quotient.mk ((lambdaIdeal p K) ^ (M + 1))
            (valuedCyclotomicConjugateLambdaInteger p K) := rfl

set_option maxHeartbeats 1000000 in
-- The completed sign theorem reuses the same finite quotient comparison data.
theorem dworkConjugateParameter_eq_neg_dworkParameter (hp_two : 2 < p) :
    dworkConjugateParameter p K = -dworkParameter p K := by
  classical
  apply AdicCompletion.ext_evalₐ
  intro N
  cases N with
  | zero =>
      trans 0
      · exact quotient_pow_zero_eq_zero (p := p) (K := K) (lambdaIdeal p K) _
      · symm
        exact quotient_pow_zero_eq_zero (p := p) (K := K) (lambdaIdeal p K) _
  | succ M =>
      let I : Ideal (ValuedIntegerRing p K) := lambdaIdeal p K
      let A : Type _ := ValuedIntegerRing p K ⧸ I ^ (M + 1)
      letI : CommRing A := by
        dsimp [A]
        infer_instance
      letI : SeminormedCommRing A := by
        dsimp [A]
        infer_instance
      let q : ValuedIntegerRing p K →+* A := Ideal.Quotient.mk (I ^ (M + 1))
      let φ : Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+* A :=
        q.comp (rIntegralRatToValuedInteger p K)
      let G : PowerSeries A := (FormalDwork.inverseSeries_isPIntegral p).mapTo φ
      let H : PowerSeries A := (FormalDwork.expMinusOneSeries_isPIntegral p).mapTo φ
      let lambdabar : A := q (valuedCyclotomicLambdaInteger p K)
      let cbar : A := q (valuedCyclotomicConjugateLambdaInteger p K)
      let gamma : A :=
        (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A) lambdabar
      have hG_eq :
          PowerSeries.map q (integralInverseSeries p K) = G := by
        simp [G, φ, integralInverseSeries,
          Furtwaengler.DieudonneDwork.IsRIntegralPS.map_mapTo]
      have hgamma_eval :
          AdicCompletion.evalₐ I (M + 1) (dworkParameter p K) = gamma := by
        calc
          AdicCompletion.evalₐ I (M + 1) (dworkParameter p K) =
              Ideal.Quotient.mk (I ^ (M + 1))
                (dworkParameterApprox p K (M + 1)) := by
                change
                  AdicCompletion.evalₐ (lambdaIdeal p K) (M + 1)
                      (dworkParameter p K) =
                    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (M + 1))
                      (dworkParameterApprox p K (M + 1))
                rw [dworkParameter_evalₐ]
          _ = gamma := by
                show Ideal.Quotient.mk (I ^ (M + 1))
                    (dworkParameterApprox p K (M + 1)) =
                  (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A) lambdabar
                rw [← hG_eq]
                exact quotient_mk_dworkParameterApprox_eq_trunc_eval
                  (p := p) (K := K) (M + 1)
      have hExpConj :
          (PowerSeries.trunc (M + 1) H).eval₂ (RingHom.id A) (-gamma) = cbar := by
        have hfinite :=
          evalIntegralPowerSeriesMod_expMinusOne_neg_dworkParameter_eq_conjugateLambda
            (p := p) (K := K) hp_two (M + 1)
        rw [evalIntegralPowerSeriesMod] at hfinite
        change
          (PowerSeries.trunc (M + 1)
            (PowerSeries.map q (integralExpMinusOneSeries p K))).eval₂
              (RingHom.id A)
              (AdicCompletion.evalₐ I (M + 1) (-(dworkParameter p K))) =
            cbar at hfinite
        have hH_eq :
            PowerSeries.map q (integralExpMinusOneSeries p K) = H := by
          simp [H, φ, integralExpMinusOneSeries,
            Furtwaengler.DieudonneDwork.IsRIntegralPS.map_mapTo]
        rw [hH_eq, map_neg, hgamma_eval] at hfinite
        exact hfinite
      have hlambdaNil : lambdabar ^ (M + 1) = 0 := by
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact valuedCyclotomicLambdaInteger_pow_mem_lambdaIdeal_pow
          (p := p) (K := K) (M + 1)
      have hcbarNil : cbar ^ (M + 1) = 0 := by
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_mem_pow
          (valuedCyclotomicConjugateLambdaInteger_mem_lambdaIdeal (p := p) (K := K))
          (M + 1)
      have hG0 : PowerSeries.constantCoeff G = 0 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        rw [Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_mapTo]
        have hcoeff0 :
            (PowerSeries.coeff (R := ℚ) 0) (FormalDwork.inverseSeries p) = 0 := by
          rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
          exact FormalDwork.inverseSeries_constantCoeff p
        have hsubzero :
            (⟨(PowerSeries.coeff (R := ℚ) 0) (FormalDwork.inverseSeries p),
                FormalDwork.inverseSeries_isPIntegral p 0⟩ :
              Furtwaengler.DieudonneDwork.rIntegralRatSubring p) = 0 := by
          ext
          exact hcoeff0
        rw [hsubzero]
        exact map_zero φ
      have hNegG0 : PowerSeries.constantCoeff (-G) = 0 := by
        simp [hG0]
      have hH0 : PowerSeries.constantCoeff H = 0 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        rw [Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_mapTo]
        have hcoeff0 :
            (PowerSeries.coeff (R := ℚ) 0) (FormalDwork.expMinusOneSeries p) = 0 := by
          rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
          exact FormalDwork.expMinusOneSeries_constantCoeff p
        have hsubzero :
            (⟨(PowerSeries.coeff (R := ℚ) 0) (FormalDwork.expMinusOneSeries p),
                FormalDwork.expMinusOneSeries_isPIntegral p 0⟩ :
              Furtwaengler.DieudonneDwork.rIntegralRatSubring p) = 0 := by
          ext
          exact hcoeff0
        rw [hsubzero]
        exact map_zero φ
      have hInner0 :
          PowerSeries.constantCoeff (PowerSeries.subst (-G) H) = 0 :=
        PowerSeries.constantCoeff_subst_eq_zero hNegG0 H hH0
      have hNegEval :
          (PowerSeries.trunc (M + 1) (-G)).eval₂ (RingHom.id A) lambdabar =
            -gamma := by
        simp [gamma]
      have hInnerEval :
          (PowerSeries.trunc (M + 1) (PowerSeries.subst (-G) H)).eval₂
              (RingHom.id A) lambdabar = cbar := by
        have hgammaNil : gamma ^ (M + 1) = 0 := by
          rw [← hgamma_eval]
          exact evalₐ_pow_eq_zero_of_evalₐ_one_eq_zero
            (p := p) (K := K) (dworkParameter_evalₐ_one (p := p) (K := K)) (M + 1)
        have hnegGammaNil : (-gamma) ^ (M + 1) = 0 :=
          neg_pow_eq_zero_of_pow_eq_zero hgammaNil
        have hNegEvalNil :
            ((PowerSeries.trunc (M + 1) (-G)).eval₂ (RingHom.id A) lambdabar) ^
                (M + 1) = 0 := by
          rw [hNegEval]
          exact hnegGammaNil
        have hcomp :
            (PowerSeries.trunc (M + 1) (PowerSeries.subst (-G) H)).eval₂
                (RingHom.id A) lambdabar =
              (PowerSeries.trunc (M + 1) H).eval₂ (RingHom.id A) (-gamma) := by
          have h := powerSeries_trunc_eval₂_subst_of_pow_succ_eq_zero
            (a := lambdabar) (N := M) hlambdaNil
            (G := -G) hNegG0 hNegEvalNil H
          calc
            (PowerSeries.trunc (M + 1) (PowerSeries.subst (-G) H)).eval₂
                (RingHom.id A) lambdabar =
              (PowerSeries.trunc (M + 1) H).eval₂ (RingHom.id A)
                ((PowerSeries.trunc (M + 1) (-G)).eval₂ (RingHom.id A) lambdabar) := h
            _ = (PowerSeries.trunc (M + 1) H).eval₂ (RingHom.id A) (-gamma) := by
              rw [hNegEval]
        rw [hcomp]
        exact hExpConj
      have hInnerEvalNil :
          ((PowerSeries.trunc (M + 1) (PowerSeries.subst (-G) H)).eval₂
              (RingHom.id A) lambdabar) ^ (M + 1) = 0 := by
        rw [hInnerEval]
        exact hcbarNil
      have hcompInv :
          (PowerSeries.trunc (M + 1)
              (PowerSeries.subst (PowerSeries.subst (-G) H) G)).eval₂
              (RingHom.id A) lambdabar =
            (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A) cbar := by
        have h := powerSeries_trunc_eval₂_subst_of_pow_succ_eq_zero
          (a := lambdabar) (N := M) hlambdaNil
          (G := PowerSeries.subst (-G) H) hInner0 hInnerEvalNil G
        calc
          (PowerSeries.trunc (M + 1)
              (PowerSeries.subst (PowerSeries.subst (-G) H) G)).eval₂
              (RingHom.id A) lambdabar =
            (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A)
              ((PowerSeries.trunc (M + 1) (PowerSeries.subst (-G) H)).eval₂
                (RingHom.id A) lambdabar) := h
          _ = (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A) cbar :=
            congrArg
              (fun x : A ↦ (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A) x)
              hInnerEval
      have hseriesInv :
          PowerSeries.subst (PowerSeries.subst (-G) H) G = -G :=
        FormalDwork.inverseSeries_mapTo_subst_expMinusOneSeries_subst_neg_inverse
          (p := p) φ
      have hevalInv := congrArg
        (fun S : PowerSeries A ↦
          (PowerSeries.trunc (M + 1) S).eval₂ (RingHom.id A) lambdabar)
        hseriesInv
      have hG_cbar :
          (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A) cbar = -gamma := by
        change
          (PowerSeries.trunc (M + 1)
              (PowerSeries.subst (PowerSeries.subst (-G) H) G)).eval₂
                (RingHom.id A) lambdabar =
            (PowerSeries.trunc (M + 1) (-G)).eval₂
                (RingHom.id A) lambdabar at hevalInv
        calc
          (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A) cbar =
            (PowerSeries.trunc (M + 1)
                (PowerSeries.subst (PowerSeries.subst (-G) H) G)).eval₂
                  (RingHom.id A) lambdabar := hcompInv.symm
          _ = (PowerSeries.trunc (M + 1) (-G)).eval₂
                  (RingHom.id A) lambdabar := hevalInv
          _ = -gamma := hNegEval
      calc
        AdicCompletion.evalₐ I (M + 1) (dworkConjugateParameter p K)
            = evalIntegralPowerSeriesMod p K (integralInverseSeries p K)
                (dworkCompleteConjugateLambda p K) (M + 1) :=
                dworkConjugateParameter_evalₐ (p := p) (K := K) (M + 1)
        _ = (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A) cbar := by
                change
                  (PowerSeries.trunc (M + 1)
                    (PowerSeries.map q (integralInverseSeries p K))).eval₂
                      (RingHom.id A)
                      (AdicCompletion.evalₐ (lambdaIdeal p K) (M + 1)
                        (dworkCompleteConjugateLambda p K)) =
                    (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A) cbar
                rw [dworkCompleteConjugateLambda_evalₐ]
                change
                  (PowerSeries.trunc (M + 1)
                    (PowerSeries.map q (integralInverseSeries p K))).eval₂
                      (RingHom.id A) cbar =
                    (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A) cbar
                rw [hG_eq]
        _ = -gamma := hG_cbar
        _ = AdicCompletion.evalₐ I (M + 1) (-(dworkParameter p K)) := by
                symm
                calc
                  AdicCompletion.evalₐ I (M + 1) (-(dworkParameter p K)) =
                      -AdicCompletion.evalₐ I (M + 1) (dworkParameter p K) :=
                      map_neg (AdicCompletion.evalₐ I (M + 1)) (dworkParameter p K)
                  _ = -gamma :=
                      congrArg Neg.neg hgamma_eval

end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular

end
