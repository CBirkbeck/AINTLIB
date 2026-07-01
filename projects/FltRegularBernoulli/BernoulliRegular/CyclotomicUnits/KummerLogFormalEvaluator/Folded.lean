import BernoulliRegular.CyclotomicUnits.KummerLogFormalEvaluator.Representatives

/-!
# Folded same-prime finite logarithm representatives

This file contains the folded same-prime finite-log representatives and the
normalized quotient bridge.
-/

@[expose] public section

noncomputable section

open BernoulliRegular.Reflection.Local
open scoped BigOperators

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
/-- The cyclotomic action transports the unscaled normalized Artin-Hasse
finite coordinate to the scaled coordinate in the matching finite quotient. -/
theorem quotient_mk_valuedIntegerCyclotomicEquiv_dworkParameterNormalizedCoordApprox
    (a : CyclotomicUnitDelta p) (N : ℕ) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a
          (dworkParameterNormalizedCoordApprox (p := p) (K := K) N)) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (scaledDworkParameterNormalizedCoordApprox
          (p := p) (K := K) (a : ZMod p) N) := by
  let I : Ideal (ValuedIntegerRing p K) := lambdaIdeal p K
  let e : ValuedIntegerRing p K ≃+* ValuedIntegerRing p K :=
    Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a
  have hnormalized :
      Ideal.quotientMap (I ^ (N + 1)) (e : ValuedIntegerRing p K →+* ValuedIntegerRing p K)
          (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e
            (Conjugation.lambdaIdeal_map_valuedIntegerCyclotomicEquiv
              (p := p) (K := K) a) (N + 1))
          (Ideal.Quotient.mk (I ^ (N + 1))
            (dworkParameterNormalizedApprox (p := p) (K := K) N)) =
        Ideal.Quotient.mk (I ^ (N + 1))
          (scaledDworkParameterNormalizedApprox
            (p := p) (K := K) (a : ZMod p) N) := by
    have h :=
      Conjugation.quotientMap_evalIntegralPowerSeriesMod_cyclotomic
        (p := p) (K := K) a
        (integralArtinHasseNormalizedExpMinusOneSeries p K)
        (integralArtinHasseNormalizedExpMinusOneSeries_map_valuedIntegerCyclotomicEquiv
          (p := p) (K := K) a)
        (dworkParameter p K) (N + 1)
    rw [Conjugation.dworkCompleteCyclotomicEquiv_dworkParameter,
      ← quotient_mk_dworkParameterNormalizedApprox_eq_evalIntegralPowerSeriesMod
        (p := p) (K := K) N,
      ← quotient_mk_scaledDworkParameterNormalizedApprox_eq_evalIntegralPowerSeriesMod
        (p := p) (K := K) (a : ZMod p) N] at h
    simpa [I, e] using h
  have hcoord := congrArg (fun z ↦
      z - (1 : ValuedIntegerRing p K ⧸ I ^ (N + 1))) hnormalized
  simpa [I, e, dworkParameterNormalizedCoordApprox,
    scaledDworkParameterNormalizedCoordApprox, map_sub] using hcoord

omit [NumberField.IsCMField K] in
/-- The unscaled normalized Artin-Hasse finite logarithm at the Dwork
parameter approximant, at the Kummer precision. -/
noncomputable def dworkParameterNormalizedFiniteLogApprox :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1) :=
  Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
      p - 1 ≤ (p - 2) + 1)
    (samePrimeFiniteLog (p := p) (K := K) (p - 2)
      (dworkParameterNormalizedCoordApprox (p := p) (K := K) (p - 2))
      (dworkParameterNormalizedCoordApprox_mem_lambdaIdeal
        (p := p) (K := K) (p - 2)))

omit [NumberField.IsCMField K] in
/-- The scaled normalized Artin-Hasse finite logarithm at the Dwork parameter
approximant, at the Kummer precision. -/
noncomputable def scaledDworkParameterNormalizedFiniteLogApprox
    (a : ZMod p) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1) :=
  Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
      p - 1 ≤ (p - 2) + 1)
    (samePrimeFiniteLog (p := p) (K := K) (p - 2)
      (scaledDworkParameterNormalizedCoordApprox
        (p := p) (K := K) a (p - 2))
      (scaledDworkParameterNormalizedCoordApprox_mem_lambdaIdeal
        (p := p) (K := K) a (p - 2)))

omit [NumberField.IsCMField K] in
/-- The folded same-prime finite logarithm at precision `lambda^(p - 1)`.

This is the finite quotient representative
`sum_{1 <= n <= p - 1} logTerm_n(x) + logTerm_p(x)`.  The final summand is
the same-prime folded `x^p / p` contribution; it is intentionally kept in the
existing finite-log term API rather than divided by `p` in the quotient. -/
noncomputable def samePrimeFoldedFiniteLogPowPred
    (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ ((p - 2) + 1) :=
  (∑ n ∈ Finset.Icc 1 (p - 1),
    samePrimeFiniteLogTerm (p := p) (K := K) (p - 2) n x hx) +
  samePrimeFiniteLogTerm (p := p) (K := K) (p - 2) p x hx

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteLog_eq_samePrimeFoldedFiniteLogPowPred
    (hp_three : 3 ≤ p)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLog (p := p) (K := K) (p - 2) x hx =
      samePrimeFoldedFiniteLogPowPred (p := p) (K := K) x hx :=
  samePrimeFiniteLog_eq_sum_Icc_add_p_term_pow_pred
    (p := p) (K := K) hp_three hx

omit [NumberField.IsCMField K] in
/-- Folded finite-log representative for the unscaled normalized
Artin-Hasse factor at the Dwork parameter. -/
noncomputable def dworkParameterNormalizedFoldedFiniteLogApprox :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ ((p - 2) + 1) :=
  samePrimeFoldedFiniteLogPowPred
    (p := p) (K := K)
    (dworkParameterNormalizedCoordApprox (p := p) (K := K) (p - 2))
    (dworkParameterNormalizedCoordApprox_mem_lambdaIdeal
      (p := p) (K := K) (p - 2))

omit [NumberField.IsCMField K] in
/-- Folded finite-log representative for the scaled normalized
Artin-Hasse factor at `omega(a) * varpi`. -/
noncomputable def scaledDworkParameterNormalizedFoldedFiniteLogApprox
    (a : ZMod p) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ ((p - 2) + 1) :=
  samePrimeFoldedFiniteLogPowPred
    (p := p) (K := K)
    (scaledDworkParameterNormalizedCoordApprox
      (p := p) (K := K) a (p - 2))
    (scaledDworkParameterNormalizedCoordApprox_mem_lambdaIdeal
      (p := p) (K := K) a (p - 2))

omit [NumberField.IsCMField K] in
/-- The specialized folded representative for the normalized Kummer quotient:
the folded unscaled normalized logarithm minus the folded scaled normalized
logarithm. -/
noncomputable def kummerLogDworkArtinHasseSpecializedFoldedFiniteLog
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ ((p - 2) + 1) :=
  dworkParameterNormalizedFoldedFiniteLogApprox (p := p) (K := K) -
    scaledDworkParameterNormalizedFoldedFiniteLogApprox
      (p := p) (K := K)
      (kummerLogColumnIndex (p := p) hp_three a : ZMod p)

omit [NumberField.IsCMField K] in
/-- CU-11f2b2c3: the Dwork Artin-Hasse specialized finite logarithm is
represented by the folded same-prime expression. -/
theorem kummerLogDworkArtinHasseSpecializedFiniteLog_eq_folded
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogDworkArtinHasseSpecializedFiniteLog
        (p := p) (K := K) hp_three a =
      kummerLogDworkArtinHasseSpecializedFoldedFiniteLog
        (p := p) (K := K) hp_three a := by
  rw [kummerLogDworkArtinHasseSpecializedFiniteLog_eq_normalizedApprox_logs
      (p := p) (K := K) hp_three a,
    samePrimeFiniteLog_eq_samePrimeFoldedFiniteLogPowPred
      (p := p) (K := K) hp_three
      (dworkParameterNormalizedCoordApprox_mem_lambdaIdeal
        (p := p) (K := K) (p - 2)),
    samePrimeFiniteLog_eq_samePrimeFoldedFiniteLogPowPred
      (p := p) (K := K) hp_three
      (scaledDworkParameterNormalizedCoordApprox_mem_lambdaIdeal
        (p := p) (K := K)
        (kummerLogColumnIndex (p := p) hp_three a : ZMod p) (p - 2))]
  rfl

omit [NumberField.IsCMField K] in
/-- The folded representative after reducing to the `p - 1` quotient used by
Dwork-coordinate coefficients. -/
theorem kummerLogDworkArtinHasseSpecializedFiniteLog_factorPow_eq_folded
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
        p - 1 ≤ (p - 2) + 1)
      (kummerLogDworkArtinHasseSpecializedFiniteLog
        (p := p) (K := K) hp_three a) =
    Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
        p - 1 ≤ (p - 2) + 1)
      (kummerLogDworkArtinHasseSpecializedFoldedFiniteLog
        (p := p) (K := K) hp_three a) := by
  rw [kummerLogDworkArtinHasseSpecializedFiniteLog_eq_folded
    (p := p) (K := K) hp_three a]

omit [NumberField.IsCMField K] in
/-- The scaled normalized Artin-Hasse finite logarithm is the cyclotomic image
of the unscaled normalized finite logarithm at the Kummer precision. -/
theorem samePrimeFiniteLog_scaledNormalizedCoordApprox_eq_quotientMap
    (a : CyclotomicUnitDelta p) :
    samePrimeFiniteLog (p := p) (K := K) (p - 2)
        (scaledDworkParameterNormalizedCoordApprox
          (p := p) (K := K) (a : ZMod p) (p - 2))
        (scaledDworkParameterNormalizedCoordApprox_mem_lambdaIdeal
          (p := p) (K := K) (a : ZMod p) (p - 2)) =
      Ideal.quotientMap ((lambdaIdeal p K) ^ ((p - 2) + 1))
        (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a)
          (Conjugation.lambdaIdeal_map_valuedIntegerCyclotomicEquiv
            (p := p) (K := K) a) ((p - 2) + 1))
        (samePrimeFiniteLog (p := p) (K := K) (p - 2)
          (dworkParameterNormalizedCoordApprox (p := p) (K := K) (p - 2))
          (dworkParameterNormalizedCoordApprox_mem_lambdaIdeal
            (p := p) (K := K) (p - 2))) := by
  let e : ValuedIntegerRing p K ≃+* ValuedIntegerRing p K :=
    Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a
  let x : ValuedIntegerRing p K :=
    dworkParameterNormalizedCoordApprox (p := p) (K := K) (p - 2)
  let y : ValuedIntegerRing p K :=
    scaledDworkParameterNormalizedCoordApprox
      (p := p) (K := K) (a : ZMod p) (p - 2)
  have hx : x ∈ lambdaIdeal p K := by
    simpa [x] using
      dworkParameterNormalizedCoordApprox_mem_lambdaIdeal
        (p := p) (K := K) (p - 2)
  have hy : y ∈ lambdaIdeal p K := by
    simpa [y] using
      scaledDworkParameterNormalizedCoordApprox_mem_lambdaIdeal
        (p := p) (K := K) (a : ZMod p) (p - 2)
  have hex : e x ∈ lambdaIdeal p K := by
    simpa [e, x] using
      Conjugation.valuedIntegerCyclotomicEquiv_mem_lambdaIdeal
        (p := p) (K := K) a hx
  have hsub : e x - y ∈ (lambdaIdeal p K) ^ ((p - 2) + 1) := by
    have hq :=
      quotient_mk_valuedIntegerCyclotomicEquiv_dworkParameterNormalizedCoordApprox
        (p := p) (K := K) a (p - 2)
    simpa [e, x, y] using Ideal.Quotient.eq.mp hq
  have hlog :
      samePrimeFiniteLog (p := p) (K := K) (p - 2) (e x) hex =
        samePrimeFiniteLog (p := p) (K := K) (p - 2) y hy :=
    samePrimeFiniteLog_eq_of_sub_mem (p := p) (K := K) hex hy hsub
  have hmap :=
    Conjugation.samePrimeFiniteLog_quotientMap_cyclotomic
      (p := p) (K := K) (N := p - 2) a hx
  simpa [e, x, y] using hlog.symm.trans hmap.symm

omit [NumberField.IsCMField K] in
/-- Factoring a cyclotomic quotient map to lower lambda-adic precision commutes
with first factoring the source quotient. -/
theorem quotientMap_valuedIntegerCyclotomicEquiv_factorPow
    {M N : ℕ} (hMN : M ≤ N) (a : CyclotomicUnitDelta p)
    (x : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) hMN
        (Ideal.quotientMap ((lambdaIdeal p K) ^ N)
          (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a :
            ValuedIntegerRing p K →+* ValuedIntegerRing p K)
          (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
            (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a)
            (Conjugation.lambdaIdeal_map_valuedIntegerCyclotomicEquiv
              (p := p) (K := K) a) N)
          x) =
      Ideal.quotientMap ((lambdaIdeal p K) ^ M)
        (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a)
          (Conjugation.lambdaIdeal_map_valuedIntegerCyclotomicEquiv
            (p := p) (K := K) a) M)
        (Ideal.Quotient.factorPow (lambdaIdeal p K) hMN x) := by
  refine Quotient.inductionOn' x ?_
  intro x
  rfl

set_option maxHeartbeats 2000000 in
-- The statement contains the p-level lambda quotient and two finite-log
-- approximants; elaborating the quotient type needs a local heartbeat bump.
omit [NumberField.IsCMField K] in
/-- Coordinate form of
`samePrimeFiniteLog_scaledNormalizedCoordApprox_eq_quotientMap`. -/
theorem valuedLambdaQuotientDworkCoeffModP_scaledNormalizedFiniteLog_eq_smul
    (a : CyclotomicUnitDelta p) (i : Fin (p - 1)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (scaledDworkParameterNormalizedFiniteLogApprox
          (p := p) (K := K) (a : ZMod p)) =
      (a : ZMod p) ^ (i : ℕ) *
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
          (dworkParameterNormalizedFiniteLogApprox (p := p) (K := K)) := by
  unfold scaledDworkParameterNormalizedFiniteLogApprox
  rw [samePrimeFiniteLog_scaledNormalizedCoordApprox_eq_quotientMap
      (p := p) (K := K) a,
    quotientMap_valuedIntegerCyclotomicEquiv_factorPow
      (p := p) (K := K) (M := p - 1) (N := (p - 2) + 1)
      (by omega) a]
  have hcoord :=
    valuedLambdaQuotientDworkCoeffModP_quotientMap_cyclotomic
      (p := p) (K := K) a i
      (dworkParameterNormalizedFiniteLogApprox (p := p) (K := K))
  simpa [dworkParameterNormalizedFiniteLogApprox,
    scaledDworkParameterNormalizedFiniteLogApprox] using hcoord

omit [NumberField.IsCMField K] in
/-- CU-11f2b2c reduced to the unscaled normalized Artin-Hasse finite-log
coordinate.  The scaled denominator contributes by the cyclotomic action,
hence the factor `1 - c^i`. -/
theorem valuedLambdaQuotientDworkCoeffModP_specializedFiniteLog_eq_one_sub_pow_mul_unscaled
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (i : Fin (p - 1)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
            p - 1 ≤ (p - 2) + 1)
          (kummerLogDworkArtinHasseSpecializedFiniteLog
            (p := p) (K := K) hp_three a)) =
      (1 - (kummerLogColumnIndex (p := p) hp_three a : ZMod p) ^ (i : ℕ)) *
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
          (dworkParameterNormalizedFiniteLogApprox (p := p) (K := K)) := by
  let δ : CyclotomicUnitDelta p := kummerLogColumnDelta (p := p) hp_three a
  rw [kummerLogDworkArtinHasseSpecializedFiniteLog_factorPow_eq_normalizedApprox_logs
      (p := p) (K := K) hp_three a,
    valuedLambdaQuotientDworkCoeffModP_sub]
  change
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (dworkParameterNormalizedFiniteLogApprox (p := p) (K := K)) -
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (scaledDworkParameterNormalizedFiniteLogApprox
          (p := p) (K := K)
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p)) =
    (1 - (kummerLogColumnIndex (p := p) hp_three a : ZMod p) ^ (i : ℕ)) *
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (dworkParameterNormalizedFiniteLogApprox (p := p) (K := K))
  rw [show (kummerLogColumnIndex (p := p) hp_three a : ZMod p) =
        (δ : ZMod p) by rfl,
    valuedLambdaQuotientDworkCoeffModP_scaledNormalizedFiniteLog_eq_smul
      (p := p) (K := K) δ i]
  ring

omit [NumberField.IsCMField K] in
/-- Dwork-specialized normalized quotient identity, with the denominator
cleared.

This is the completed-ring analogue of the formal identity
`formalKummerQuotientUnit_mul_scaled_eq_normalized`: after specializing
`X` to the Kummer-column Teichmüller lift and `T` to the Dwork parameter,
the normalized quotient unit is `kummerLogDworkArtinHasseNormalizedQuotientArg
+ 1`. -/
theorem kummerLogDworkArtinHasseNormalizedQuotientUnit_mul_scaled_eq_normalized
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogDworkArtinHasseNormalizedQuotientArg
        (p := p) (K := K) hp_three a + 1) *
      (artinHasseExp_eval_scaledDworkParameter p K
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p) - 1) =
    algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K)
        (rationalPadicTeichmuller p
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p)) *
      (artinHasseExp_eval_scaledDworkParameter p K 1 - 1) := by
  let S : Type _ := DworkCompleteIntegerRing p K
  let R₀ : Type := RationalPadicIntegerRing p
  let c : S :=
    algebraMap R₀ S
      (rationalPadicTeichmuller p
        (kummerLogColumnIndex (p := p) hp_three a : ZMod p))
  let u : Sˣ :=
    kummerLogDworkArtinHasseQuotientDenUnit
      (p := p) (K := K) hp_three a
  have harg :
      kummerLogDworkArtinHasseNormalizedQuotientArg
          (p := p) (K := K) hp_three a + 1 =
        c * ((u⁻¹ : Sˣ) : S) := by
    simp [kummerLogDworkArtinHasseNormalizedQuotientArg, c, u, S, R₀]
  have hden :
      (u : S) * (artinHasseExp_eval_scaledDworkParameter p K 1 - 1) =
        artinHasseExp_eval_scaledDworkParameter p K
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p) - 1 := by
    simpa [u, S] using
      kummerLogDworkArtinHasseQuotientDenUnit_mul_exp_sub_one
        (p := p) (K := K) hp_three a
  calc
    (kummerLogDworkArtinHasseNormalizedQuotientArg
          (p := p) (K := K) hp_three a + 1) *
        (artinHasseExp_eval_scaledDworkParameter p K
            (kummerLogColumnIndex (p := p) hp_three a : ZMod p) - 1)
        = (c * ((u⁻¹ : Sˣ) : S)) *
            ((u : S) *
              (artinHasseExp_eval_scaledDworkParameter p K 1 - 1)) := by
          rw [harg, hden]
    _ = c * ((((u⁻¹ : Sˣ) : S) * (u : S)) *
          (artinHasseExp_eval_scaledDworkParameter p K 1 - 1)) := by
          ring
    _ = c * (artinHasseExp_eval_scaledDworkParameter p K 1 - 1) := by
          simp

omit [NumberField.IsCMField K] in
/-- Finite quotient form of
`kummerLogDworkArtinHasseNormalizedQuotientUnit_mul_scaled_eq_normalized`,
at the Kummer mod-`p` level. -/
theorem kummerLogDworkArtinHasseNormalizedQuotientUnit_evalₐ_mul_scaled_eq_normalized
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
        (kummerLogDworkArtinHasseNormalizedQuotientArg
          (p := p) (K := K) hp_three a + 1) *
      AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
        (artinHasseExp_eval_scaledDworkParameter p K
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p) - 1) =
    AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
        (algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K)
          (rationalPadicTeichmuller p
            (kummerLogColumnIndex (p := p) hp_three a : ZMod p))) *
      AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
        (artinHasseExp_eval_scaledDworkParameter p K 1 - 1) := by
  have h :=
    congrArg (AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1))
        (kummerLogDworkArtinHasseNormalizedQuotientUnit_mul_scaled_eq_normalized
        (p := p) (K := K) hp_three a)
  simpa [map_mul] using h

end CyclotomicUnits
end BernoulliRegular

end
