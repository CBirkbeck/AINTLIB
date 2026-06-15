module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.Part18

@[expose] public section

noncomputable section

/-!
# The corrected Dwork parameter

This wrapper imports the split implementation of the completed Dwork parameter.
-/

namespace BernoulliRegular
namespace CyclotomicUnits
namespace PadicLogSetup
namespace DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- Final CU-09 assembly theorem for the completed corrected Dwork parameter.

This theorem records the concrete endpoint names needed downstream: the
inverse-series coordinate construction, the Artin--Hasse evaluation at
`varpi`, the lambda congruences, conjugation, uniformizer/ramification data,
the `Z_p[varpi]` and fixed-even-power descriptions, the corrected
Eisenstein equation, and the Teichmuller-scaled Artin--Hasse rewrite. -/
theorem finalAssembly (hp_two : 2 < p) :
    (∀ N,
      AdicCompletion.evalₐ (lambdaIdeal p K) N (dworkParameter p K) =
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
          (dworkParameterApprox p K N)) ∧
    evalIntegralPowerSeries p K (integralExpSeries p K) (dworkParameter p K)
        (dworkParameter_evalₐ_one (p := p) (K := K)) =
      AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
        (valuedCyclotomicZetaInteger p K) ∧
    dworkParameter p K - dworkCompleteLambda p K ∈
      (dworkCompleteLambdaIdeal p K) ^ 2 ∧
    Conjugation.dworkCompleteComplexConj (p := p) K (dworkParameter p K) =
      -dworkParameter p K ∧
    dworkParameterIdeal p K = dworkCompleteLambdaIdeal p K ∧
    Ideal.span ({(p : DworkCompleteIntegerRing p K)} :
        Set (DworkCompleteIntegerRing p K)) =
      (dworkParameterIdeal p K) ^ (p - 1) ∧
    (∀ {x : DworkCompleteIntegerRing p K}, dworkParameter p K * x = 0 → x = 0) ∧
    dworkCompleteLambda p K - dworkParameter p K ∈
      (dworkParameterIdeal p K) ^ 2 ∧
    dworkParameterAdjoin p K = ⊤ ∧
    dworkFixedSubalgebra p K = dworkEvenParameterAdjoin p K ∧
    (∀ i : Fin (p - 1),
      dworkParameterPowerBasis p K i = dworkParameter p K ^ (i : ℕ)) ∧
    (∀ i : dworkEvenPowerIndex p,
      (dworkFixedEvenPowerBasis (p := p) (K := K) hp_two i :
        DworkCompleteIntegerRing p K) =
        dworkParameter p K ^ ((i.1 : Fin (p - 1)) : ℕ)) ∧
    dworkParameter p K ^ (p - 1) =
      -(p : DworkCompleteIntegerRing p K) *
        artinHasseTailUnit (p := p) (K := K) hp_two ∧
    (∀ a : ZMod p,
      artinHasseExp_eval_scaledDworkParameter p K a =
        AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
          (valuedCyclotomicZetaInteger p K ^ a.val)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact dworkParameter_evalₐ (p := p) (K := K)
  · exact dworkParameter_eval_exp (p := p) (K := K)
  · exact dworkParameter_sub_dworkCompleteLambda_mem_sq (p := p) (K := K)
  · exact Conjugation.dworkCompleteComplexConj_dworkParameter_eq_neg
      (p := p) (K := K) hp_two
  · exact dworkParameterIdeal_eq_dworkCompleteLambdaIdeal (p := p) (K := K)
  · exact span_natCast_prime_dworkComplete_eq_parameterIdeal_pow_pred
      (p := p) (K := K)
  · exact dworkParameter_regular (p := p) (K := K)
  · exact dworkCompleteLambda_sub_dworkParameter_mem_parameterIdeal_sq
      (p := p) (K := K)
  · exact dworkParameterAdjoin_eq_top (p := p) (K := K)
  · exact (dworkEvenParameterAdjoin_eq_fixed (p := p) (K := K) hp_two).symm
  · exact dworkParameterPowerBasis_apply (p := p) (K := K)
  · intro i
    simpa using congrArg Subtype.val
      (dworkFixedEvenPowerBasis_apply (p := p) (K := K) hp_two i)
  · exact dworkParameter_pow_pred_eq_neg_p_mul_tailUnit
      (p := p) (K := K) hp_two
  · exact artinHasseExp_eval_scaledDworkParameter_eq_zeta_pow
      (p := p) (K := K)

end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular
