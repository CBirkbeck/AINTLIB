import BernoulliRegular.CyclotomicUnits.KummerLogFormalEvaluator.Homogeneous

/-!
# Final Kummer logarithm evaluator coefficient bridge

This file contains the final coefficient-level handoff theorems for the split formal evaluator.
-/

@[expose] public section

noncomputable section

open NumberField
open NumberField.IsCMField
open BernoulliRegular.Reflection.Local
open scoped BigOperators NumberField PowerSeries

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
/-- Homogeneous-degree expansion of the unscaled normalized finite-log
coefficient at the Dwork parameter. -/
theorem normalizedFiniteLogApprox_evenCoeff_eq_homogeneousDegreeSums
    (hp_five : 5 ≤ p) (j : Fin (kummerLogRank p)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K)
        (kummerLogEvenPowerIndex (p := p) hp_five j).1
        (dworkParameterNormalizedFiniteLogApprox (p := p) (K := K)) =
      ∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) (p - 2)),
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K)
          (kummerLogEvenPowerIndex (p := p) hp_five j).1
          (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
              p - 1 ≤ (p - 2) + 1)
            (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
              (p := p) (K := K) (p - 2) d
              (dworkParameterApprox p K ((p - 2) + 1))
              (dworkParameterApprox_mem_lambdaIdeal
                (p := p) (K := K) ((p - 2) + 1)))) := by
  unfold dworkParameterNormalizedFiniteLogApprox
  simp only [dworkParameterNormalizedCoordApprox_eq]
  exact valuedLambdaQuotientDworkCoeffModP_factorPow_samePrimeFiniteLog_normalizedCoord
    (p := p) (K := K) (kummerLogEvenPowerIndex (p := p) hp_five j).1
    (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) ((p - 2) + 1))

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- Low normalized Artin-Hasse logarithm coefficients agree with the ordinary
normalized exponential coefficients, hence with the Bernoulli formula. -/
theorem coeff_logOf_rationalArtinHasseNormalizedExpMinusOneSeries_eq_bernoulli
    {j : ℕ} (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    (PowerSeries.coeff (R := ℚ) (2 * j))
        (PowerSeries.logOf (rationalArtinHasseNormalizedExpMinusOneSeries p)) =
      (_root_.bernoulli (2 * j) : ℚ) /
        (((2 * j : ℕ) : ℚ) * (Nat.factorial (2 * j) : ℚ)) := by
  have hlow :
      ∀ k, k ≤ 2 * j →
        (PowerSeries.coeff (R := ℚ) k)
            (rationalArtinHasseNormalizedExpMinusOneSeries p) =
          (PowerSeries.coeff (R := ℚ) k) formalExpNormalizedMinusOne := by
    intro k hk
    have hklt : k + 1 < p := by omega
    rw [rationalArtinHasseNormalizedExpMinusOneSeries_coeff,
      formalExpNormalizedMinusOne_coeff]
    have hAH :
        (PowerSeries.coeff (R := ℚ) (k + 1))
            (PadicLogSetup.FormalDwork.expMinusOneSeries p) =
          (PowerSeries.coeff (R := ℚ) (k + 1)) (PowerSeries.exp ℚ) := by
      simp [PadicLogSetup.FormalDwork.expMinusOneSeries,
        Furtwaengler.artinHasseExpMinusOneSeries,
        Furtwaengler.artinHasseExpSeries_coeff_eq_inv_factorial_of_lt p hklt]
    rw [hAH]
  calc
    (PowerSeries.coeff (R := ℚ) (2 * j))
        (PowerSeries.logOf (rationalArtinHasseNormalizedExpMinusOneSeries p))
        =
      (PowerSeries.coeff (R := ℚ) (2 * j))
        (PowerSeries.logOf formalExpNormalizedMinusOne) :=
        coeff_logOf_eq_of_coeff_eq_le
          (rationalArtinHasseNormalizedExpMinusOneSeries_constantCoeff (p := p))
          formalExpNormalizedMinusOne_constantCoeff hlow
    _ =
      (_root_.bernoulli (2 * j) : ℚ) /
        (((2 * j : ℕ) : ℚ) * (Nat.factorial (2 * j) : ℚ)) :=
        coeff_logOf_formalExpNormalizedMinusOne_eq_bernoulli
          (by omega : 1 < 2 * j)

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- The reduced factorial-cleared normalized Artin-Hasse coefficient in an
even Kummer row is the Bernoulli factor used by the formal target. -/
theorem rIntegralToZMod_sum_rationalArtinHasseNormalizedFactorialWeightedLogCoeff_even
    {j : ℕ} (hj : 1 ≤ j) (hjp : 2 * j ≤ p - 3) :
    Furtwaengler.DieudonneDwork.rIntegralToZMod p
        (∑ n ∈ Finset.Icc 1 (2 * j),
          rationalArtinHasseNormalizedFactorialWeightedLogCoeff p (2 * j) n) =
      bernoulliFactor p j := by
  classical
  let S : Furtwaengler.DieudonneDwork.rIntegralRatSubring p :=
    ∑ n ∈ Finset.Icc 1 (2 * j),
      rationalArtinHasseNormalizedFactorialWeightedLogCoeff p (2 * j) n
  let q : ℚ := (_root_.bernoulli (2 * j) : ℚ) / (2 * j : ℚ)
  have hcoeff :
      (PowerSeries.coeff (R := ℚ) (2 * j))
          (PowerSeries.logOf (rationalArtinHasseNormalizedExpMinusOneSeries p)) =
        (_root_.bernoulli (2 * j) : ℚ) /
          (((2 * j : ℕ) : ℚ) * (Nat.factorial (2 * j) : ℚ)) :=
    coeff_logOf_rationalArtinHasseNormalizedExpMinusOneSeries_eq_bernoulli
      (p := p) hj hjp
  have hS : (S : ℚ) = q := by
    have hcoe :=
      coe_sum_rationalArtinHasseNormalizedFactorialWeightedLogCoeff
        (p := p) (2 * j)
    have hfac_ne : (Nat.factorial (2 * j) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * j)
    have hd_ne : ((2 * j : ℕ) : ℚ) ≠ 0 := by
      have hd : 2 * j ≠ 0 := by omega
      exact_mod_cast hd
    calc
      (S : ℚ) =
          (Nat.factorial (2 * j) : ℚ) *
            (PowerSeries.coeff (R := ℚ) (2 * j))
              (PowerSeries.logOf
                (rationalArtinHasseNormalizedExpMinusOneSeries p)) := by
          simpa [S] using hcoe
      _ = (Nat.factorial (2 * j) : ℚ) *
            ((_root_.bernoulli (2 * j) : ℚ) /
              (((2 * j : ℕ) : ℚ) * (Nat.factorial (2 * j) : ℚ))) := by
          rw [hcoeff]
      _ = q := by
          dsimp [q]
          field_simp [hfac_ne, hd_ne]
          ring_nf
          norm_num [Nat.cast_mul]
          ring
  have hres :
      ((S : ℚ).num : ZMod p) * ((S : ℚ).den : ZMod p)⁻¹ =
        (q.num : ZMod p) * (q.den : ZMod p)⁻¹ :=
    congrArg (fun r : ℚ => (r.num : ZMod p) * (r.den : ZMod p)⁻¹) hS
  rw [Furtwaengler.DieudonneDwork.rIntegralToZMod_apply]
  change ((S : ℚ).num : ZMod p) * ((S : ℚ).den : ZMod p)⁻¹ =
    bernoulliFactor p j
  rw [hres]
  simp [bernoulliFactor, ratReductionZMod, q, div_eq_mul_inv]

omit [NumberField.IsCMField K] in
/-- On even rows the same-prime finite log may be computed from the ordinary
terms and then regrouped by normalized homogeneous degree below `p - 1`. -/
theorem normalizedFiniteLogApprox_evenCoeff_eq_lowHomogeneousDegreeSums
    (hp_five : 5 ≤ p) (j : Fin (kummerLogRank p)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K)
        (kummerLogEvenPowerIndex (p := p) hp_five j).1
        (dworkParameterNormalizedFiniteLogApprox (p := p) (K := K)) =
      ∑ d ∈ Finset.range (p - 1),
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K)
          (kummerLogEvenPowerIndex (p := p) hp_five j).1
          (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
              p - 1 ≤ (p - 2) + 1)
            (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
              (p := p) (K := K) (p - 2) d
              (dworkParameterApprox p K ((p - 2) + 1))
              (dworkParameterApprox_mem_lambdaIdeal
                (p := p) (K := K) ((p - 2) + 1)))) := by
  classical
  let x : ValuedIntegerRing p K :=
    dworkParameterApprox p K ((p - 2) + 1)
  let hx : x ∈ lambdaIdeal p K :=
    dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) ((p - 2) + 1)
  let i : Fin (p - 1) := (kummerLogEvenPowerIndex (p := p) hp_five j).1
  let hle : p - 1 ≤ (p - 2) + 1 := by omega
  let term : ℕ → ℕ → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ ((p - 2) + 1) :=
    fun n d =>
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
        (p := p) (K := K) (p - 2) n d x hx
  rw [normalizedFiniteLogApprox_evenCoeff_eq_ordinaryTerms
    (p := p) (K := K) hp_five j]
  simp only [dworkParameterNormalizedCoordApprox_eq]
  change
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.factorPow (lambdaIdeal p K) hle
          (∑ n ∈ Finset.Icc 1 (p - 1),
            samePrimeFiniteLogTerm (p := p) (K := K) (p - 2) n
              (samePrimeFiniteArtinHasseNormalizedCoord
                (p := p) (K := K) (p - 2) x)
              (samePrimeFiniteArtinHasseNormalizedCoord_mem_lambdaIdeal
                (p := p) (K := K) (p - 2) hx))) =
      ∑ d ∈ Finset.range (p - 1),
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
          (Ideal.Quotient.factorPow (lambdaIdeal p K) hle
            (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
              (p := p) (K := K) (p - 2) d x hx))
  rw [map_sum]
  rw [valuedLambdaQuotientDworkCoeffModP_sum]
  calc
    ∑ n ∈ Finset.Icc 1 (p - 1),
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
          (Ideal.Quotient.factorPow (lambdaIdeal p K) hle
            (samePrimeFiniteLogTerm (p := p) (K := K) (p - 2) n
              (samePrimeFiniteArtinHasseNormalizedCoord
                (p := p) (K := K) (p - 2) x)
              (samePrimeFiniteArtinHasseNormalizedCoord_mem_lambdaIdeal
                (p := p) (K := K) (p - 2) hx)))
        =
      ∑ n ∈ Finset.Icc 1 (p - 1),
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
          (Ideal.Quotient.factorPow (lambdaIdeal p K) hle
            (∑ d ∈ Finset.range (p - 1), term n d)) := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        have hnlt : n < p := by
          have hnpred : n ≤ p - 1 := (Finset.mem_Icc.mp hn).2
          omega
        rw [samePrimeFiniteLogTerm_normalizedArtinHasseCoord_eq_homogeneous_quotient_sum_of_lt_prime
          (p := p) (K := K) (N := p - 2) (n := n) hx hnlt]
        simp [term, show p - 2 + 1 = p - 1 by omega]
    _ =
      ∑ n ∈ Finset.Icc 1 (p - 1),
        ∑ d ∈ Finset.range (p - 1),
          valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
            (Ideal.Quotient.factorPow (lambdaIdeal p K) hle (term n d)) := by
        refine Finset.sum_congr rfl ?_
        intro n _hn
        rw [map_sum]
        exact valuedLambdaQuotientDworkCoeffModP_sum (p := p) (K := K) i
          (Finset.range (p - 1))
          (fun d => Ideal.Quotient.factorPow (lambdaIdeal p K) hle (term n d))
    _ =
      ∑ d ∈ Finset.range (p - 1),
        ∑ n ∈ Finset.Icc 1 (p - 1),
          valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
            (Ideal.Quotient.factorPow (lambdaIdeal p K) hle (term n d)) := by
        rw [Finset.sum_comm]
    _ =
      ∑ d ∈ Finset.range (p - 1),
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
          (Ideal.Quotient.factorPow (lambdaIdeal p K) hle
            (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
              (p := p) (K := K) (p - 2) d x hx)) := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        have hdlt : d < p - 1 := Finset.mem_range.mp hd
        have hI_subset : Finset.Icc 1 d ⊆ Finset.Icc 1 (p - 1) := fun n hn =>
          Finset.mem_Icc.mpr
            ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans (Nat.le_of_lt hdlt)⟩
        have hsum :
            ∑ n ∈ Finset.Icc 1 d,
                valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
                  (Ideal.Quotient.factorPow (lambdaIdeal p K) hle (term n d)) =
              ∑ n ∈ Finset.Icc 1 (p - 1),
                valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
                  (Ideal.Quotient.factorPow (lambdaIdeal p K) hle (term n d)) := by
          refine Finset.sum_subset hI_subset ?_
          intro n hn_big hn_small
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn_big).1
          have hnd_not : ¬ n ≤ d := fun hnd =>
            hn_small (Finset.mem_Icc.mpr ⟨hn1, hnd⟩)
          have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn1
          have hterm_zero : term n d = 0 := by
            simp [term, samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm,
              samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore, hn0,
              hnd_not]
          rw [hterm_zero]
          change valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
              (0 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) = 0
          have hzero := valuedLambdaQuotientDworkCoeffModP_add
            (p := p) (K := K) i
            (0 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) 0
          simpa using hzero
        rw [← hsum]
        rw [← valuedLambdaQuotientDworkCoeffModP_sum]
        rw [← map_sum]
        rw [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_sum_Icc
          (p := p) (K := K) (N := p - 2) (d := d) hx]

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in
-- The proof first unfolds the same-prime finite logarithm to ordinary
-- homogeneous slices, then collapses the Dwork coordinate sum to one degree.
omit [NumberField.IsCMField K] in
/-- CU-11f2b2c4 source theorem: the unscaled normalized finite-log coefficient
on an even Kummer row is the formal Bernoulli coefficient. -/
theorem valuedLambdaQuotientDworkCoeffModP_unscaledNormalizedFiniteLog_even_eq_formal
    (hp_five : 5 ≤ p) (j : Fin (kummerLogRank p)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K)
        (kummerLogEvenPowerIndex (p := p) hp_five j).1
        (dworkParameterNormalizedFiniteLogApprox (p := p) (K := K)) =
      -kummerLogUnitFactor p (kummerLogRowIndex (p := p) j) *
        bernoulliFactor p (kummerLogRowIndex (p := p) j) := by
  classical
  let i : Fin (p - 1) := (kummerLogEvenPowerIndex (p := p) hp_five j).1
  let e : ℕ := (i : ℕ)
  have heq : e = 2 * kummerLogRowIndex (p := p) j := by
    rfl
  have he_lt : e < p - 1 := by
    have hle := two_mul_kummerLogRowIndex_le_sub_three (p := p) j
    omega
  rw [normalizedFiniteLogApprox_evenCoeff_eq_lowHomogeneousDegreeSums
    (p := p) (K := K) hp_five j]
  rw [Finset.sum_eq_single e]
  · rw [
      valuedLambdaQuotientDworkCoeffModP_factorPow_normalizedHomogeneousDegreeSum_dworkParameterApprox_of_lt
        (p := p) (K := K) i he_lt]
    have hsingle :
        rationalPadicIntegerToZMod p
          (((Pi.single (⟨e, he_lt⟩ : Fin (p - 1))
            (1 : RationalPadicIntegerRing p) :
              Fin (p - 1) → RationalPadicIntegerRing p) i)) = 1 := by
      have hfin : (⟨e, he_lt⟩ : Fin (p - 1)) = i := by
        ext
        rfl
      rw [hfin, Pi.single_eq_same]
      simp
    rw [hsingle, mul_one]
    have hred :
        Furtwaengler.DieudonneDwork.rIntegralToZMod p
            (∑ n ∈ Finset.Icc 1 e,
              rationalArtinHasseNormalizedFactorialWeightedLogCoeff p e n) =
          bernoulliFactor p (kummerLogRowIndex (p := p) j) := by
      rw [heq]
      exact
        rIntegralToZMod_sum_rationalArtinHasseNormalizedFactorialWeightedLogCoeff_even
          (p := p)
          (j := kummerLogRowIndex (p := p) j)
          (kummerLogRowIndex_one_le (p := p) j)
          (two_mul_kummerLogRowIndex_le_sub_three (p := p) j)
    rw [hred]
    rw [heq]
    simp [kummerLogUnitFactor]
  · intro d hd hde
    have hdlt : d < p - 1 := Finset.mem_range.mp hd
    rw [
      valuedLambdaQuotientDworkCoeffModP_factorPow_normalizedHomogeneousDegreeSum_dworkParameterApprox_of_lt
        (p := p) (K := K) i hdlt]
    have hne_fin : (⟨d, hdlt⟩ : Fin (p - 1)) ≠ i := by
      intro h
      apply hde
      dsimp [e]
      exact congrArg Fin.val h
    rw [Pi.single_eq_of_ne hne_fin.symm]
    simp
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr he_lt))

omit [NumberField.IsCMField K] in
/-- CU-11f2b2c4, folded-coordinate form: the finite specialized coefficient
can be read from the folded representative. -/
theorem kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_folded
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
        (p := p) (K := K) hp_three hp_five j a =
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K)
        (kummerLogEvenPowerIndex (p := p) hp_five j).1
        (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
            p - 1 ≤ (p - 2) + 1)
          (kummerLogDworkArtinHasseSpecializedFoldedFiniteLog
            (p := p) (K := K) hp_three a)) := by
  rw [kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq]
  rw [← kummerLogDworkArtinHasseSpecializedFiniteLog_factorPow_eq_folded
    (p := p) (K := K) hp_three a]

omit [NumberField.IsCMField K] in
/-- Even-row folded coefficient reduced to the unscaled normalized finite-log
coordinate.  This is the coordinate-first C4 bridge; the remaining source
calculation is the unscaled even-row normalized Artin-Hasse coefficient. -/
theorem kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_one_sub_pow_mul_unscaled
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
        (p := p) (K := K) hp_three hp_five j a =
      (1 -
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p) ^
            ((kummerLogEvenPowerIndex (p := p) hp_five j).1 : ℕ)) *
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K)
          (kummerLogEvenPowerIndex (p := p) hp_five j).1
          (dworkParameterNormalizedFiniteLogApprox (p := p) (K := K)) := by
  rw [kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq]
  exact valuedLambdaQuotientDworkCoeffModP_specializedFiniteLog_eq_one_sub_pow_mul_unscaled
    (p := p) (K := K) hp_three a
    (kummerLogEvenPowerIndex (p := p) hp_five j).1

omit [NumberField.IsCMField K] in
/-- Once the unscaled even-row normalized finite-log coefficient is known,
the specialized folded coefficient is the formal Kummer coefficient. -/
theorem kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_formal_of_unscaled
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p))
    (hunscaled :
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K)
          (kummerLogEvenPowerIndex (p := p) hp_five j).1
          (dworkParameterNormalizedFiniteLogApprox (p := p) (K := K)) =
        -kummerLogUnitFactor p (kummerLogRowIndex (p := p) j) *
          bernoulliFactor p (kummerLogRowIndex (p := p) j)) :
    kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
        (p := p) (K := K) hp_three hp_five j a =
      Polynomial.eval
        (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
        (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j)) := by
  rw [kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_one_sub_pow_mul_unscaled
    (p := p) (K := K) hp_three hp_five j a]
  rw [hunscaled]
  rw [formalKummerLogCoeffModP_eval]
  rw [kummerLogEvenPowerIndex_val]
  rw [show 2 * ((j : ℕ) + 1) = kummerLogRowIndex (p := p) j * 2 by
    simp [kummerLogRowIndex]
    omega]
  ring

omit [NumberField.IsCMField K] in
/-- CU-11f2b2c4 endpoint: the specialized finite Artin-Hasse logarithm
coefficient agrees with the formal Kummer coefficient on every even row. -/
theorem kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_formal
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
        (p := p) (K := K) hp_three hp_five j a =
      Polynomial.eval
        (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
        (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j)) :=
  kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_formal_of_unscaled
    (p := p) (K := K) hp_three hp_five j a
    (valuedLambdaQuotientDworkCoeffModP_unscaledNormalizedFiniteLog_even_eq_formal
      (p := p) (K := K) hp_five j)

omit [NumberField.IsCMField K] in
/-- CU-11f2b3 endpoint: the folded finite same-prime evaluator gives the
formal Kummer coefficient after specialization at the column residue. -/
theorem kummerLogFormalEvaluator_coeff_eq
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
        (p := p) (K := K) hp_three hp_five j a =
      Polynomial.eval
        (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
        (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j)) :=
  kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_formal
    (p := p) (K := K) hp_three hp_five j a

omit [NumberField.IsCMField K] in
/-- CU-11f2b3 endpoint rewritten to the assembled Kummer congruence right-hand
side.  This is the form intended for the concrete matrix-entry theorem. -/
theorem kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_congrRhs
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
        (p := p) (K := K) hp_three hp_five j a =
      kummerLogCoeffCongrRhs (p := p) hp_three j a :=
  kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_congrRhs_of_eq_formal
    (p := p) (K := K) hp_three hp_five j a
    (kummerLogFormalEvaluator_coeff_eq
      (p := p) (K := K) hp_three hp_five j a)

/-- The concrete squared-family matrix entry is twice the normalized finite-log
coefficient.  This is the coordinate form of the already-proved identity
`concreteKummerLogVector = 2 • specializedFiniteLog` modulo `λ^(p - 1)`. -/
theorem concreteKummerLogMatrix_eq_two_mul_specializedFiniteLogCoeffModP
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five j a =
      (2 : ZMod p) *
        kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
          (p := p) (K := K) hp_three hp_five j a := by
  let i : Fin (p - 1) := (kummerLogEvenPowerIndex (p := p) hp_five j).1
  let z : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1) :=
    Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
        p - 1 ≤ (p - 2) + 1)
      (kummerLogDworkArtinHasseSpecializedFiniteLog
        (p := p) (K := K) hp_three a)
  have hmatrix :
      concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five j a =
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
          (AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
            (concreteKummerLogVector (p := p) (K := K) hp_three a :
              DworkCompleteIntegerRing p K)) := by
    have hrepr :=
      dworkFixedEvenPowerBasis_repr_eq_powerBasis_repr
        (p := p) (K := K) (by omega : 2 < p)
        (concreteKummerLogVector (p := p) (K := K) hp_three a)
        (kummerLogEvenPowerIndex (p := p) hp_five j)
    rw [concreteKummerLogMatrix_apply, concreteKummerLogCoeff_eq]
    rw [valuedLambdaQuotientDworkCoeffModP_evalₐ]
    simpa [i, concreteKummerLogVector] using
      congrArg (rationalPadicIntegerToZMod p) hrepr
  have hvec :=
    concreteKummerLogVector_evalₐ_pow_pred_eq_two_nsmul_dworkArtinHasseSpecializedFiniteLog
      (p := p) (K := K) hp_three a
  let hle : p - 1 ≤ (p - 2) + 1 := by omega
  have hvec_factor :=
    congrArg (Ideal.Quotient.factorPow (lambdaIdeal p K) hle) hvec
  have hvec' :
      AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
          (concreteKummerLogVector (p := p) (K := K) hp_three a :
            DworkCompleteIntegerRing p K) = 2 • z := by
    rw [factor_evalₐ_eq_evalₐ (p := p) (K := K) hle, map_nsmul] at hvec_factor
    exact hvec_factor
  calc
    concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five j a
        = valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
            (AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
              (concreteKummerLogVector (p := p) (K := K) hp_three a :
                DworkCompleteIntegerRing p K)) := hmatrix
    _ = valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i (2 • z) := by
          rw [hvec']
    _ = (2 : ZMod p) *
        kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP
          (p := p) (K := K) hp_three hp_five j a := by
          have htwo :
              valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i (2 • z) =
                (2 : ZMod p) *
                  valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i z := by
            rw [show (2 • z : ValuedIntegerRing p K ⧸
                (lambdaIdeal p K) ^ (p - 1)) =
                  (2 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) * z by
                norm_num]
            simpa using
              valuedLambdaQuotientDworkCoeffModP_natCast_mul
                (p := p) (K := K) i 2 z
          rw [htwo]
          rfl

/-- CU-11f3: the concrete logarithm matrix entries satisfy the Kummer
congruence in the squared-family normalization. -/
theorem concreteKummerLogMatrix_eq_squaredKummerLogCoeffCongrRhs
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five j a =
      squaredKummerLogCoeffCongrRhs (p := p) hp_three j a := by
  rw [concreteKummerLogMatrix_eq_two_mul_specializedFiniteLogCoeffModP
      (p := p) (K := K) hp_three hp_five j a,
    kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_congrRhs
      (p := p) (K := K) hp_three hp_five j a,
    squaredKummerLogCoeffCongrRhs_eq_two_mul]

/-- The concrete squared-family matrix entry is exactly `2` times the
normalized-family Kummer congruence right-hand side. -/
theorem concreteKummerLogMatrix_eq_two_mul_kummerLogCoeffCongrRhs
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five j a =
      (2 : ZMod p) * kummerLogCoeffCongrRhs (p := p) hp_three j a := by
  rw [concreteKummerLogMatrix_eq_squaredKummerLogCoeffCongrRhs
      (p := p) (K := K) hp_three hp_five j a,
    squaredKummerLogCoeffCongrRhs_eq_two_mul]

/-- Final concrete squared-family entry API, with the squared unit factor
displayed explicitly. -/
theorem concreteSquaredKummerLogMatrixEntry_congr
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five j a =
      squaredKummerLogUnitFactor p (kummerLogRowIndex (p := p) j) *
        bernoulliFactor p (kummerLogRowIndex (p := p) j) *
          ((kummerLogColumnIndex (p := p) hp_three a : ZMod p) ^
            (2 * kummerLogRowIndex (p := p) j) - 1) := by
  rw [concreteKummerLogMatrix_eq_squaredKummerLogCoeffCongrRhs
      (p := p) (K := K) hp_three hp_five j a]
  rfl

/-- CU-11 endpoint: the concrete Kummer logarithm coefficient congruence.

The unit factor is the squared-family unit
`squaredKummerLogUnitFactor = 2 * kummerLogUnitFactor`, which is nonzero by
`squaredKummerLogUnitFactor_ne_zero`. -/
theorem kummerLogCoeff_congr
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five j a =
      squaredKummerLogUnitFactor p (kummerLogRowIndex (p := p) j) *
        bernoulliFactor p (kummerLogRowIndex (p := p) j) *
          ((kummerLogColumnIndex (p := p) hp_three a : ZMod p) ^
            (2 * kummerLogRowIndex (p := p) j) - 1) :=
  concreteSquaredKummerLogMatrixEntry_congr
    (p := p) (K := K) hp_three hp_five j a

/-- Matrix-level form of the concrete squared-family Kummer congruence. -/
theorem concreteKummerLogMatrix_eq_squaredKummerLogCoeffCongrRhs_matrix
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p) :
    concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five =
      fun j a => squaredKummerLogCoeffCongrRhs (p := p) hp_three j a := by
  ext j a
  exact concreteKummerLogMatrix_eq_squaredKummerLogCoeffCongrRhs
    (p := p) (K := K) hp_three hp_five j a

end CyclotomicUnits
end BernoulliRegular

end
