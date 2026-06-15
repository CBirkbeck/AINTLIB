module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.Part9

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

theorem dworkParameter_mul_pow_pred_add_p_mul_tailUnit_eq_zero
    (hp_two : 2 < p) :
    dworkParameter p K *
        (dworkParameter p K ^ (p - 1) +
          (p : DworkCompleteIntegerRing p K) *
            artinHasseTailUnit (p := p) (K := K) hp_two) = 0 := by
  apply AdicCompletion.ext_evalₐ
  intro n
  cases n with
  | zero =>
      exact quotient_pow_zero_eq_zero (p := p) (K := K) (lambdaIdeal p K) _
  | succ N =>
      cases N with
      | zero =>
          rw [map_mul, dworkParameter_evalₐ_one]
          simp
      | succ N =>
          have hfinite :=
            dworkParameterFinite_corrected_factor_eq_zero
              (p := p) (K := K) (N := N + 1) (Nat.succ_pos N)
          rw [map_mul, map_add, map_pow, map_mul, map_natCast,
            dworkParameter_evalₐ, artinHasseTailUnit_evalₐ_succ]
          exact hfinite

theorem dworkParameter_pow_pred_eq_neg_p_mul_tailUnit
    (hp_two : 2 < p) :
    dworkParameter p K ^ (p - 1) =
      -(p : DworkCompleteIntegerRing p K) *
        artinHasseTailUnit (p := p) (K := K) hp_two := by
  have hinside :
      dworkParameter p K ^ (p - 1) +
        (p : DworkCompleteIntegerRing p K) *
          artinHasseTailUnit (p := p) (K := K) hp_two = 0 :=
    dworkParameter_mul_eq_zero (p := p) (K := K)
      (dworkParameter_mul_pow_pred_add_p_mul_tailUnit_eq_zero
        (p := p) (K := K) hp_two)
  simpa [neg_mul] using eq_neg_of_add_eq_zero_left hinside

theorem dworkParameterExpApprox_smodEq
    {M N : ℕ} (hMN : M ≤ N) :
    dworkParameterExpApprox p K M ≡ dworkParameterExpApprox p K N
      [SMOD (lambdaIdeal p K) ^ M •
        (⊤ : Submodule (ValuedIntegerRing p K) (ValuedIntegerRing p K))] := by
  let I : Ideal (ValuedIntegerRing p K) := lambdaIdeal p K
  have hM :
      Ideal.Quotient.mk (I ^ M) (dworkParameterExpApprox p K M) =
        Ideal.Quotient.mk (I ^ M) (valuedCyclotomicZetaInteger p K) := by
    simpa [I] using
      quotient_mk_dworkParameterExpApprox_eq_zeta (p := p) (K := K) M
  have hNpow :
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
          (dworkParameterExpApprox p K N) =
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
          (valuedCyclotomicZetaInteger p K) :=
    quotient_mk_dworkParameterExpApprox_eq_zeta (p := p) (K := K) N
  have hN :
      Ideal.Quotient.mk (I ^ M) (dworkParameterExpApprox p K N) =
        Ideal.Quotient.mk (I ^ M) (valuedCyclotomicZetaInteger p K) := by
    have hfactor :=
      congrArg (Ideal.Quotient.factor (Ideal.pow_le_pow_right hMN)) hNpow
    simpa [I] using hfactor
  rw [SModEq.sub_mem]
  have hquot :
      Ideal.Quotient.mk (I ^ M) (dworkParameterExpApprox p K M) =
        Ideal.Quotient.mk (I ^ M) (dworkParameterExpApprox p K N) :=
    hM.trans hN.symm
  exact (mem_ideal_smul_top_iff_self (I ^ M)).mpr
    (Ideal.Quotient.eq.mp hquot)

/-- The Cauchy sequence of finite Artin-Hasse exponential approximants at
`G_p(lambda)`. -/
def dworkParameterExpCauchySeq :
    AdicCompletion.AdicCauchySequence (lambdaIdeal p K) (ValuedIntegerRing p K) where
  val N := dworkParameterExpApprox p K N
  property := by
    intro M N hMN
    exact dworkParameterExpApprox_smodEq (p := p) (K := K) hMN

/-- The specialized completed Artin-Hasse evaluation `E_p(G_p(lambda))`,
defined as the limit of finite truncation evaluations. -/
def dworkParameterExp : DworkCompleteIntegerRing p K :=
  AdicCompletion.mkₐ (lambdaIdeal p K) (dworkParameterExpCauchySeq p K)

@[simp]
theorem dworkParameterExp_evalₐ (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N (dworkParameterExp p K) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
        (dworkParameterExpApprox p K N) := by
  simp [dworkParameterExp, dworkParameterExpCauchySeq]

theorem dworkParameterExp_eq_zeta :
    dworkParameterExp p K =
      AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
        (valuedCyclotomicZetaInteger p K) := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [dworkParameterExp_evalₐ]
  rw [AdicCompletion.evalₐ_of]
  exact quotient_mk_dworkParameterExpApprox_eq_zeta (p := p) (K := K) N

theorem evalIntegralPowerSeriesMod_exp_dworkParameter (N : ℕ) :
    evalIntegralPowerSeriesMod p K (integralExpSeries p K) (dworkParameter p K) N =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
        (valuedCyclotomicZetaInteger p K) := by
  calc
    evalIntegralPowerSeriesMod p K (integralExpSeries p K) (dworkParameter p K) N =
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
          (dworkParameterExpApprox p K N) := by
      rw [evalIntegralPowerSeriesMod]
      rw [dworkParameter_evalₐ]
      exact (quotient_mk_dworkParameterExpApprox_eq_trunc_eval
        (p := p) (K := K) N).symm
    _ = Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
        (valuedCyclotomicZetaInteger p K) :=
      quotient_mk_dworkParameterExpApprox_eq_zeta (p := p) (K := K) N

theorem dworkParameter_eval_exp :
    evalIntegralPowerSeries p K (integralExpSeries p K) (dworkParameter p K)
        (dworkParameter_evalₐ_one (p := p) (K := K)) =
      AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
        (valuedCyclotomicZetaInteger p K) := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [evalIntegralPowerSeries_evalₐ]
  rw [AdicCompletion.evalₐ_of]
  exact evalIntegralPowerSeriesMod_exp_dworkParameter (p := p) (K := K) N

/-- Uniqueness of the completed inverse-series construction: a completed
element with the same finite coordinates as `G_p(lambda)` is the constructed
Dwork parameter. -/
theorem dworkParameter_unique
    {x : DworkCompleteIntegerRing p K}
    (hx :
      ∀ N,
        AdicCompletion.evalₐ (lambdaIdeal p K) N x =
          (PowerSeries.trunc N
            (PowerSeries.map
              (Ideal.Quotient.mk ((lambdaIdeal p K) ^ N))
              (integralInverseSeries p K))).eval₂
            (RingHom.id
              (ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N))
            (Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
              (valuedCyclotomicLambdaInteger p K))) :
    x = dworkParameter p K := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [hx N, dworkParameter_evalₐ]
  exact (quotient_mk_dworkParameterApprox_eq_trunc_eval
    (p := p) (K := K) N).symm


end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular

end
