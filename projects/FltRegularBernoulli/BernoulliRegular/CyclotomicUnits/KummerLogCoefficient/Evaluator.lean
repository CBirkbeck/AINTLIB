import BernoulliRegular.CyclotomicUnits.KummerLogCoefficient.Coordinates

/-!
# Specialized finite-log coefficient evaluators

This file contains the final coefficient extraction API for specialized Dwork
Artin-Hasse finite logarithms.
-/

@[expose] public section

noncomputable section

open NumberField
open NumberField.IsCMField
open BernoulliRegular.Reflection.Local
open scoped BigOperators NumberField

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
theorem dworkParameterPowerLinearMap_of_polynomial_eval₂
    (P : Polynomial (RationalPadicIntegerRing p)) (hdeg : P.natDegree < p - 1) :
    Polynomial.eval₂
        (algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K))
        (dworkParameter p K) P =
      dworkParameterPowerLinearMap p K
        (fun i : Fin (p - 1) => P.coeff (i : ℕ)) := by
  rw [Polynomial.eval₂_eq_sum_range'
    (f := algebraMap (RationalPadicIntegerRing p)
      (DworkCompleteIntegerRing p K))
    (p := P) hdeg (x := dworkParameter p K)]
  rw [dworkParameterPowerLinearMap_apply]
  exact (Fin.sum_univ_eq_sum_range
    (fun i : ℕ =>
      algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K)
          (P.coeff i) *
        dworkParameter p K ^ i) (p - 1)).symm

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModP_mk_polynomial_eval₂_of_natDegree_lt
    (i : Fin (p - 1)) (P : Polynomial (RationalPadicIntegerRing p))
    (hdeg : P.natDegree < p - 1) :
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
          (Polynomial.eval₂
            (algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K))
            (dworkParameter p K) P)) =
      rationalPadicIntegerToZMod p (P.coeff (i : ℕ)) := by
  rw [dworkParameterPowerLinearMap_of_polynomial_eval₂
    (p := p) (K := K) P hdeg]
  rw [dworkParameterQuotientCoeffModP_mk_powerLinearMap]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModP_evalₐ_polynomial_eval₂_of_natDegree_lt
    (i : Fin (p - 1)) (P : Polynomial (RationalPadicIntegerRing p))
    (hdeg : P.natDegree < p - 1) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
          (Polynomial.eval₂
            (algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K))
            (dworkParameter p K) P)) =
      rationalPadicIntegerToZMod p (P.coeff (i : ℕ)) := by
  rw [dworkParameterPowerLinearMap_of_polynomial_eval₂
    (p := p) (K := K) P hdeg]
  rw [valuedLambdaQuotientDworkCoeffModP_evalₐ_powerLinearMap]

omit [NumberField.IsCMField K] in
/-- The cyclotomic action multiplies the `i`-th Dwork power-basis coordinate
by the corresponding residue power. -/
theorem dworkParameterPowerBasis_repr_dworkCompleteCyclotomicEquiv_toZMod
    (a : CyclotomicUnitDelta p) (x : DworkCompleteIntegerRing p K)
    (i : Fin (p - 1)) :
    rationalPadicIntegerToZMod p
        ((dworkParameterPowerBasis p K).repr
          (Conjugation.dworkCompleteCyclotomicEquiv (p := p) K a x) i) =
      (a : ZMod p) ^ (i : ℕ) *
        rationalPadicIntegerToZMod p
          ((dworkParameterPowerBasis p K).repr x i) := by
  classical
  let c : Fin (p - 1) → RationalPadicIntegerRing p :=
    (dworkParameterPowerBasis p K).repr x
  have hx : dworkParameterPowerLinearMap p K c = x := by
    simpa [c] using
      KummerLogTrace.dworkParameterPowerLinearMap_repr
        (p := p) (K := K) x
  have haction :
      Conjugation.dworkCompleteCyclotomicEquiv (p := p) K a x =
        dworkParameterPowerLinearMap p K
          (fun i : Fin (p - 1) =>
            rationalPadicTeichmuller p (a : ZMod p) ^ (i : ℕ) * c i) := by
    rw [← hx]
    exact Conjugation.dworkCompleteCyclotomicEquiv_powerLinearMap
      (p := p) (K := K) a c
  have hcoeff :
      (dworkParameterPowerBasis p K).repr
          (Conjugation.dworkCompleteCyclotomicEquiv (p := p) K a x) i =
        rationalPadicTeichmuller p (a : ZMod p) ^ (i : ℕ) * c i := by
    have hrepr :=
      congrFun
        (dworkParameterPowerBasis_repr_powerLinearMap
          (p := p) (K := K)
          (fun i : Fin (p - 1) =>
            rationalPadicTeichmuller p (a : ZMod p) ^ (i : ℕ) * c i)) i
    rw [haction]
    simpa using hrepr
  rw [hcoeff, map_mul, map_pow, rationalPadicIntegerToZMod_teichmuller]

omit [NumberField.IsCMField K] in
/-- The completed cyclotomic action is compatible with the valued-integer
algebra map into the Dwork completion. -/
theorem dworkCompleteCyclotomicEquiv_algebraMap_valuedInteger
    (a : CyclotomicUnitDelta p) (x : ValuedIntegerRing p K) :
    Conjugation.dworkCompleteCyclotomicEquiv (p := p) K a
        (algebraMap (ValuedIntegerRing p K)
          (DworkCompleteIntegerRing p K) x) =
      algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)
        (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a x) := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [Conjugation.evalₐ_dworkCompleteCyclotomicEquiv]
  simp [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]

omit [NumberField.IsCMField K] in
/-- Coordinate action on the valued `lambda^(p - 1)` quotient. -/
theorem valuedLambdaQuotientDworkCoeffModP_quotientMap_cyclotomic
    (a : CyclotomicUnitDelta p) (i : Fin (p - 1))
    (x : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (Ideal.quotientMap ((lambdaIdeal p K) ^ (p - 1))
          (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a :
            ValuedIntegerRing p K →+* ValuedIntegerRing p K)
          (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
            (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K a)
            (Conjugation.lambdaIdeal_map_valuedIntegerCyclotomicEquiv
              (p := p) (K := K) a) (p - 1)) x) =
      (a : ZMod p) ^ (i : ℕ) *
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i x := by
  refine Quotient.inductionOn' x ?_
  intro x
  have hcoord :=
    dworkParameterPowerBasis_repr_dworkCompleteCyclotomicEquiv_toZMod
      (p := p) (K := K) a
      (algebraMap (ValuedIntegerRing p K)
        (DworkCompleteIntegerRing p K) x) i
  rw [dworkCompleteCyclotomicEquiv_algebraMap_valuedInteger
    (p := p) (K := K) a x] at hcoord
  rw [show (Quotient.mk'' x : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) =
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1)) x from rfl,
    Ideal.quotientMap_mk, valuedLambdaQuotientDworkCoeffModP_mk,
    valuedLambdaQuotientDworkCoeffModP_mk]
  exact hcoord

omit [NumberField.IsCMField K] in
/-- The finite Dwork Artin-Hasse specialization coefficient selected by a
Kummer matrix row. -/
noncomputable def kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) : ZMod p :=
  valuedLambdaQuotientDworkCoeffModP (p := p) (K := K)
    (kummerLogEvenPowerIndex (p := p) hp_five j).1
    (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
        p - 1 ≤ (p - 2) + 1)
      (kummerLogDworkArtinHasseSpecializedFiniteLog
        (p := p) (K := K) hp_three a))

omit [NumberField.IsCMField K] in
theorem kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
        (p := p) (K := K) hp_three hp_five j a =
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K)
        (kummerLogEvenPowerIndex (p := p) hp_five j).1
        (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
            p - 1 ≤ (p - 2) + 1)
          (kummerLogDworkArtinHasseSpecializedFiniteLog
            (p := p) (K := K) hp_three a)) :=
  rfl

omit [NumberField.IsCMField K] in
theorem kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_of_evalₐ_eq
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) (x : DworkCompleteIntegerRing p K)
    (hx :
      Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
          p - 1 ≤ (p - 2) + 1)
        (kummerLogDworkArtinHasseSpecializedFiniteLog
          (p := p) (K := K) hp_three a) =
        AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1) x) :
    kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
        (p := p) (K := K) hp_three hp_five j a =
      rationalPadicIntegerToZMod p
        ((dworkParameterPowerBasis p K).repr x
          (kummerLogEvenPowerIndex (p := p) hp_five j).1) := by
  rw [kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq, hx,
    valuedLambdaQuotientDworkCoeffModP_evalₐ]

omit [NumberField.IsCMField K] in
theorem kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_of_evalₐ_powerLinearMap
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p))
    (c : Fin (p - 1) → RationalPadicIntegerRing p)
    (hc_eval :
      Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
          p - 1 ≤ (p - 2) + 1)
        (kummerLogDworkArtinHasseSpecializedFiniteLog
          (p := p) (K := K) hp_three a) =
        AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
          (dworkParameterPowerLinearMap p K c))
    (hc_coeff :
      rationalPadicIntegerToZMod p
          (c (kummerLogEvenPowerIndex (p := p) hp_five j).1) =
        Polynomial.eval
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
          (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j))) :
    kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
        (p := p) (K := K) hp_three hp_five j a =
      Polynomial.eval
        (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
        (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j)) := by
  rw [kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_of_evalₐ_eq
    (p := p) (K := K) hp_three hp_five j a
    (dworkParameterPowerLinearMap p K c) hc_eval,
    dworkParameterPowerBasis_repr_powerLinearMap, hc_coeff]

omit [NumberField.IsCMField K] in
theorem kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_of_evalₐ_polynomial_eval₂
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p))
    (P : Polynomial (RationalPadicIntegerRing p))
    (hdeg : P.natDegree < p - 1)
    (h_eval :
      Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
          p - 1 ≤ (p - 2) + 1)
        (kummerLogDworkArtinHasseSpecializedFiniteLog
          (p := p) (K := K) hp_three a) =
        AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
          (Polynomial.eval₂
            (algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K))
            (dworkParameter p K) P))
    (h_coeff :
      rationalPadicIntegerToZMod p
          (P.coeff ((kummerLogEvenPowerIndex (p := p) hp_five j).1 : ℕ)) =
        Polynomial.eval
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
          (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j))) :
    kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
        (p := p) (K := K) hp_three hp_five j a =
      Polynomial.eval
        (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
        (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j)) := by
  rw [kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq,
    h_eval,
    valuedLambdaQuotientDworkCoeffModP_evalₐ_polynomial_eval₂_of_natDegree_lt
      (p := p) (K := K)
      (kummerLogEvenPowerIndex (p := p) hp_five j).1 P hdeg,
    h_coeff]

omit [NumberField.IsCMField K] in
/-- Once the finite Artin-Hasse specialization coefficient has been identified
with the formal `ZMod p[X]` coefficient, it rewrites to the assembled Kummer
right-hand side from CU-11e. -/
theorem kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_congrRhs_of_eq_formal
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p))
    (hformal :
      kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
          (p := p) (K := K) hp_three hp_five j a =
        Polynomial.eval
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
          (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j))) :
    kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
        (p := p) (K := K) hp_three hp_five j a =
      kummerLogCoeffCongrRhs (p := p) hp_three j a := by
  rw [hformal, formalKummerLogCoeff_congr (p := p) hp_three hp_five j a]

omit [NumberField.IsCMField K] in
theorem kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_formal_iff_eq_congrRhs
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
        (p := p) (K := K) hp_three hp_five j a =
        Polynomial.eval
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
          (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j)) ↔
      kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
        (p := p) (K := K) hp_three hp_five j a =
        kummerLogCoeffCongrRhs (p := p) hp_three j a := by
  rw [formalKummerLogCoeff_congr (p := p) hp_three hp_five j a]

end CyclotomicUnits
end BernoulliRegular

end
