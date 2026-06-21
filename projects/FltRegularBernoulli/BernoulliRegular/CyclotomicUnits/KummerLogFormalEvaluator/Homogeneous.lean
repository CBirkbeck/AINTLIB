import BernoulliRegular.CyclotomicUnits.KummerLogFormalEvaluator.Folded

/-!
# Homogeneous finite-log coordinates

This file contains homogeneous-coordinate expansions and folded correction
coordinate lemmas for the finite Kummer logarithm evaluator.
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
/-- Coordinate form of the homogeneous expansion for the finite logarithm of
the normalized Artin-Hasse factor, at the `p - 1` quotient used by the Kummer
matrix entries. -/
theorem valuedLambdaQuotientDworkCoeffModP_factorPow_samePrimeFiniteLog_normalizedCoord
    (i : Fin (p - 1)) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
            p - 1 ≤ (p - 2) + 1)
          (samePrimeFiniteLog (p := p) (K := K) (p - 2)
            (samePrimeFiniteArtinHasseNormalizedCoord
              (p := p) (K := K) (p - 2) x)
            (samePrimeFiniteArtinHasseNormalizedCoord_mem_lambdaIdeal
              (p := p) (K := K) (p - 2) hx))) =
      ∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) (p - 2)),
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
          (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
              p - 1 ≤ (p - 2) + 1)
            (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
              (p := p) (K := K) (p - 2) d x hx)) := by
  classical
  rw [samePrimeFiniteLog_normalizedArtinHasseCoord_eq_homogeneous_degree_sum_range
    (p := p) (K := K) (N := p - 2) hx]
  rw [map_sum]
  exact valuedLambdaQuotientDworkCoeffModP_sum (p := p) (K := K) i
    (Finset.range (samePrimeFiniteLogCutoff (p := p) (p - 2)))
    (fun d ↦
      Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
          p - 1 ≤ (p - 2) + 1)
        (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
          (p := p) (K := K) (p - 2) d x hx))

omit [NumberField.IsCMField K] in
/-- The CU-11f2b2c finite-log coordinate after reducing to homogeneous
normalized Artin-Hasse degree sums. -/
theorem valuedLambdaQuotientDworkCoeffModP_specializedFiniteLog_eq_degreeSums_sub
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (i : Fin (p - 1)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
            p - 1 ≤ (p - 2) + 1)
          (kummerLogDworkArtinHasseSpecializedFiniteLog
            (p := p) (K := K) hp_three a)) =
      (∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) (p - 2)),
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
          (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
              p - 1 ≤ (p - 2) + 1)
            (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
              (p := p) (K := K) (p - 2) d
              (dworkParameterApprox p K ((p - 2) + 1))
              (dworkParameterApprox_mem_lambdaIdeal
                (p := p) (K := K) ((p - 2) + 1))))) -
      (∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) (p - 2)),
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
          (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
              p - 1 ≤ (p - 2) + 1)
            (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
              (p := p) (K := K) (p - 2) d
              (scaledDworkParameterApprox p K
                (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
                ((p - 2) + 1))
              (scaledDworkParameterApprox_mem_lambdaIdeal
                (p := p) (K := K)
                (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
                ((p - 2) + 1))))) := by
  classical
  rw [kummerLogDworkArtinHasseSpecializedFiniteLog_factorPow_eq_normalizedApprox_logs
    (p := p) (K := K) hp_three a]
  rw [valuedLambdaQuotientDworkCoeffModP_sub]
  simp only [dworkParameterNormalizedCoordApprox_eq,
    scaledDworkParameterNormalizedCoordApprox_eq]
  rw [valuedLambdaQuotientDworkCoeffModP_factorPow_samePrimeFiniteLog_normalizedCoord
    (p := p) (K := K) i
    (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) ((p - 2) + 1))]
  rw [valuedLambdaQuotientDworkCoeffModP_factorPow_samePrimeFiniteLog_normalizedCoord
    (p := p) (K := K) i
    (scaledDworkParameterApprox_mem_lambdaIdeal
      (p := p) (K := K)
      (kummerLogColumnIndex (p := p) hp_three a : ZMod p) ((p - 2) + 1))]

/-- The concrete Kummer-column fixedness forces the linear Dwork coordinate of
the specialized normalized Artin-Hasse finite logarithm to vanish.

This is a useful guardrail for CU-11f2b2c: a quotient representative for the
specialized finite log modulo `varpi^(p - 1)` cannot contain a nonzero linear
term.  The proof uses the already-proved concrete-column identity
`eval = 2 • specializedFiniteLog` and odd-coordinate vanishing in the fixed
Dwork subalgebra; it does not cancel any `varpi` in the finite quotient. -/
theorem valuedLambdaQuotientDworkCoeffModP_specializedFiniteLog_linear_eq_zero
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (a : Fin (kummerLogRank p)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K)
      (⟨1, by omega⟩ : Fin (p - 1))
      (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
          p - 1 ≤ (p - 2) + 1)
        (kummerLogDworkArtinHasseSpecializedFiniteLog
          (p := p) (K := K) hp_three a)) = 0 := by
  let i : Fin (p - 1) := ⟨1, by omega⟩
  let z : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1) :=
    Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
      p - 1 ≤ (p - 2) + 1)
      (kummerLogDworkArtinHasseSpecializedFiniteLog
        (p := p) (K := K) hp_three a)
  have hvec0 :
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
          (concreteKummerLogVector (p := p) (K := K) hp_three a :
            DworkCompleteIntegerRing p K)) = 0 := by
    rw [valuedLambdaQuotientDworkCoeffModP_evalₐ]
    let x : DworkCompleteIntegerRing p K :=
      (concreteKummerLogVector (p := p) (K := K) hp_three a :
        DworkCompleteIntegerRing p K)
    let coeffs : Fin (p - 1) → RationalPadicIntegerRing p :=
      (dworkParameterPowerBasis p K).repr x
    have hx_repr : dworkParameterPowerLinearMap p K coeffs = x := by
      simpa [coeffs, x] using KummerLogTrace.dworkParameterPowerLinearMap_repr
        (p := p) (K := K) x
    have hfixed : Conjugation.dworkCompleteComplexConj (p := p) K x = x := by
      simpa [x, concreteKummerLogVector, kummerLogFixedColumn] using
        kummerLogCompletedColumn_complexConj (p := p) (K := K) hp_three a
    have hfixed_coeffs :
        Conjugation.dworkCompleteComplexConj (p := p) K
            (dworkParameterPowerLinearMap p K coeffs) =
          dworkParameterPowerLinearMap p K coeffs := by
      simpa [hx_repr] using hfixed
    have hodd : Odd (i : ℕ) := by
      dsimp [i]
      exact Nat.odd_iff.mpr rfl
    have hcoeff : coeffs i = 0 :=
      dworkParameterPowerLinearMap_odd_coeff_eq_zero_of_fixed
        (p := p) (K := K) (by omega : 2 < p) hfixed_coeffs i hodd
    change rationalPadicIntegerToZMod p (coeffs i) = 0
    rw [hcoeff, map_zero]
  have hvec :=
    concreteKummerLogVector_evalₐ_pow_pred_eq_two_nsmul_dworkArtinHasseSpecializedFiniteLog
      (p := p) (K := K) hp_three a
  let hle : p - 1 ≤ (p - 2) + 1 := by omega
  have hvec_factor := congrArg (Ideal.Quotient.factorPow (lambdaIdeal p K) hle) hvec
  have hvec' :
      AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
          (concreteKummerLogVector (p := p) (K := K) hp_three a :
            DworkCompleteIntegerRing p K) = 2 • z := by
    rw [factor_evalₐ_eq_evalₐ (p := p) (K := K) hle, map_nsmul] at hvec_factor
    exact hvec_factor
  have hcoeff_vec :=
    congrArg (valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i) hvec'
  rw [hvec0] at hcoeff_vec
  have hz2 :
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i (2 • z) =
        (2 : ZMod p) * valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i z := by
    rw [show (2 • z : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) =
        z + z by ring]
    rw [valuedLambdaQuotientDworkCoeffModP_add]
    ring
  rw [hz2] at hcoeff_vec
  have htwo_ne : (2 : ZMod p) ≠ 0 :=
    two_zmod_ne_zero_of_five_le (p := p) hp_five
  exact (mul_eq_zero.mp hcoeff_vec.symm).resolve_left htwo_ne

/-- The folded representative has zero linear Dwork coordinate after
specialization.  This packages the corrected folded representative with the
existing fixedness guardrail for the finite specialized logarithm. -/
theorem valuedLambdaQuotientDworkCoeffModP_specializedFoldedFiniteLog_linear_eq_zero
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (a : Fin (kummerLogRank p)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K)
      (⟨1, by omega⟩ : Fin (p - 1))
      (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
          p - 1 ≤ (p - 2) + 1)
        (kummerLogDworkArtinHasseSpecializedFoldedFiniteLog
          (p := p) (K := K) hp_three a)) = 0 := by
  rw [← kummerLogDworkArtinHasseSpecializedFiniteLog_factorPow_eq_folded
    (p := p) (K := K) hp_three a]
  exact valuedLambdaQuotientDworkCoeffModP_specializedFiniteLog_linear_eq_zero
    (p := p) (K := K) hp_three hp_five a

set_option maxHeartbeats 1200000 in
-- The proof unfolds a quotient coordinate through the Dwork power basis and
-- a ramification congruence; elaborating the completion coercions is slow.
omit [NumberField.IsCMField K] in
/-- The integral ramification-unit representative of the folded `n = p`
finite-log term has zero even Kummer coordinates once the divided argument
has a rational-padic residue lift.

This is the coordinate form of the strengthened ramification congruence
`dworkRamificationCorrection_sub_linear_mem_parameterIdeal_pow_pred`: modulo
`varpi^(p - 1)` the correction is a scalar multiple of `varpi`, hence it is
invisible in every even row. -/
theorem dworkRamificationCorrection_evenCoeff_eq_zero_of_sub_residue
    (hp_five : 5 ≤ p) (j : Fin (kummerLogRank p))
    (c : RationalPadicIntegerRing p) {Z : DworkCompleteIntegerRing p K}
    (hZ :
      Z - algebraMap (RationalPadicIntegerRing p)
          (DworkCompleteIntegerRing p K) c ∈
        dworkParameterIdeal p K) :
    dworkParameterQuotientCoeffModP (p := p) (K := K)
        (kummerLogEvenPowerIndex (p := p) hp_five j).1
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
          (dworkRamificationUnit (p := p) (K := K) (by omega : 2 < p) *
            dworkParameter p K * Z ^ p)) = 0 := by
  let S : Type _ := DworkCompleteIntegerRing p K
  let R₀ : Type := RationalPadicIntegerRing p
  let i : Fin (p - 1) := (kummerLogEvenPowerIndex (p := p) hp_five j).1
  let y : S :=
    algebraMap R₀ S (-(c ^ p)) * dworkParameter p K
  have hmem :
      dworkRamificationUnit (p := p) (K := K) (by omega : 2 < p) *
            dworkParameter p K * Z ^ p - y ∈
        (dworkParameterIdeal p K) ^ (p - 1) := by
    have h :=
      dworkRamificationCorrection_sub_linear_mem_parameterIdeal_pow_pred
        (p := p) (K := K) (by omega : 2 < p)
        (Z := Z) (z0 := algebraMap R₀ S c) hZ
    simpa [y, S, R₀, map_pow] using h
  have hcoord :=
    dworkParameterPowerBasis_coeff_zmod_eq_of_sub_mem_parameterIdeal_pow_pred
      (p := p) (K := K) hmem i
  change
    rationalPadicIntegerToZMod p
        ((dworkParameterPowerBasis p K).repr
          (dworkRamificationUnit (p := p) (K := K) (by omega : 2 < p) *
            dworkParameter p K * Z ^ p) i) = 0
  rw [hcoord]
  have hy :
      rationalPadicIntegerToZMod p
        ((dworkParameterPowerBasis p K).repr y i) = 0 := by
    change dworkParameterQuotientCoeffModP (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1)) y) = 0
    have hne : (i : ℕ) ≠ 1 := by
      dsimp [i]
      omega
    have hne_fin : i ≠ (⟨1, by omega⟩ : Fin (p - 1)) := fun h ↦
      hne (congrArg Fin.val h)
    rw [show y =
        algebraMap R₀ S (-(c ^ p)) * dworkParameter p K ^ 1 by
          simp [y, S, R₀]]
    rw [dworkParameterQuotientCoeffModP_mk_algebraMap_mul_pow_of_lt
      (p := p) (K := K) i (-(c ^ p)) (by omega : 1 < p - 1)]
    rw [Pi.single_eq_of_ne hne_fin]
    simp
  exact hy

set_option maxHeartbeats 800000 in
-- The `n = p` finite-log term is compared with the ramification correction
-- by identifying their `p`-multiples in the complete Dwork ring and then
-- cancelling `p` there, not in the finite quotient.
omit [NumberField.IsCMField K] in
/-- The actual folded `n = p` same-prime finite-log term has the same Dwork
coordinate as the integral ramification correction `epsilon * varpi * Z^p`,
provided the argument maps to `varpi * Z` in the complete Dwork ring. -/
theorem valuedLambdaQuotientDworkCoeffModP_samePrimeFiniteLogTerm_p_eq_ramificationCorrection
    (hp_five : 5 ≤ p) (i : Fin (p - 1))
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    {Z : DworkCompleteIntegerRing p K}
    (hZ :
      algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) x =
        dworkParameter p K * Z) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
            p - 1 ≤ (p - 2) + 1)
          (samePrimeFiniteLogTerm (p := p) (K := K) (p - 2) p x hx)) =
      dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
          (dworkRamificationUnit (p := p) (K := K) (by omega : 2 < p) *
            dworkParameter p K * Z ^ p)) := by
  let R : Type _ := ValuedIntegerRing p K
  let S : Type _ := DworkCompleteIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let q : R →+* R ⧸ I ^ (p - 1) := Ideal.Quotient.mk (I ^ (p - 1))
  let y : R := samePrimeFiniteLogTermNumerator (p := p) (K := K) p x hx
  let corr : S :=
    dworkRamificationUnit (p := p) (K := K) (by omega : 2 < p) *
      dworkParameter p K * Z ^ p
  have hp_ne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hord : ordCompl[p] p = 1 := by
    rw [Nat.Prime.factorization_self (Fact.out : Nat.Prime p)]
    rw [pow_one]
    exact Nat.div_self (Fact.out : Nat.Prime p).pos
  have hmk_ord :
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ ((p - 2) + 1))
          ((ordCompl[p] p : ℕ) : R) =
        (1 : R ⧸ I ^ ((p - 2) + 1)) := by
    rw [hord]
    simp [I]
  have hinv_ord :
      quotientNatCastInv (p := p) (K := K) (p - 2) (ordCompl[p] p)
          (samePrimeFiniteLog_ordCompl_coprime (p := p) hp_ne) =
        (1 : R ⧸ I ^ ((p - 2) + 1)) := by
    have h :=
      quotientNatCastInv_spec_right (p := p) (K := K)
        (N := p - 2) (m := ordCompl[p] p)
        (hm := samePrimeFiniteLog_ordCompl_coprime (p := p) hp_ne)
    rw [hmk_ord] at h
    simpa using h
  have hcore :
      samePrimeFiniteLogTermCore (p := p) (K := K) (p - 2) p x hx =
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ ((p - 2) + 1)) y := by
    rw [samePrimeFiniteLogTermCore, dif_neg hp_ne]
    change
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ ((p - 2) + 1)) y *
          quotientNatCastInv (p := p) (K := K) (p - 2) (ordCompl[p] p)
            (samePrimeFiniteLog_ordCompl_coprime (p := p) hp_ne) =
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ ((p - 2) + 1)) y
    rw [hinv_ord]
    simp
  have hsign :
      ((-1 : R ⧸ I ^ ((p - 2) + 1)) ^ (p + 1)) = 1 := by
    rcases (Fact.out : Nat.Prime p).odd_of_ne_two (by omega : p ≠ 2) with ⟨k, hk⟩
    have hp1 : p + 1 = 2 * (k + 1) := by omega
    rw [hp1, pow_mul]
    have hsq : ((-1 : R ⧸ I ^ ((p - 2) + 1)) ^ 2) = 1 := by ring
    rw [hsq]
    simp
  have hterm :
      samePrimeFiniteLogTerm (p := p) (K := K) (p - 2) p x hx =
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ ((p - 2) + 1)) y := by
    rw [samePrimeFiniteLogTerm, hcore, hsign, one_mul]
  have hy_mul :
      (p : S) * algebraMap R S y =
        (algebraMap R S x) ^ p := by
    have hy :=
      samePrimeFiniteLogTermNumerator_mul_spec
        (p := p) (K := K) (n := p) hp_ne hx
    have hy' := congrArg (algebraMap R S) hy
    simpa [R, S, y, map_mul, map_pow,
      Nat.Prime.factorization_self (Fact.out : Nat.Prime p)] using hy'
  have hcorr_mul :
      (p : S) * corr = (algebraMap R S x) ^ p := by
    have hcorr :=
      natCast_prime_mul_dworkRamificationCorrection_of_eq
        (p := p) (K := K) (by omega : 2 < p)
        (Y := algebraMap R S x) (Z := Z) hZ
    simpa [R, S, corr] using hcorr
  have hmap_y : algebraMap R S y = corr := by
    have hsub :
        (p : S) * (algebraMap R S y - corr) = 0 := by
      calc
        (p : S) * (algebraMap R S y - corr) =
            (p : S) * algebraMap R S y - (p : S) * corr := by ring
        _ = (algebraMap R S x) ^ p - (algebraMap R S x) ^ p := by
              rw [hy_mul, hcorr_mul]
        _ = 0 := by ring
    exact sub_eq_zero.mp
      (natCast_prime_dworkComplete_regular
        (p := p) (K := K) (by omega : 2 < p) hsub)
  have hterm_pred :
      Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
          p - 1 ≤ (p - 2) + 1)
        (samePrimeFiniteLogTerm (p := p) (K := K) (p - 2) p x hx) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1)) y := by
    rw [hterm]
    rfl
  rw [hterm_pred]
  rw [valuedLambdaQuotientDworkCoeffModP_mk,
    dworkParameterQuotientCoeffModP_mk]
  rw [hmap_y]

set_option maxHeartbeats 1000000 in
-- The statement contains a same-prime term at precision `p - 2` coerced to
-- the Kummer quotient; elaborating those quotient powers is expensive.
omit [NumberField.IsCMField K] in
/-- The folded `n = p` same-prime finite-log term has zero even Kummer
coordinate for every lambda-adic argument.  The argument is factored by the
complete Dwork parameter, and the resulting factor is reduced only modulo the
Dwork parameter using the residue-lift theorem. -/
theorem valuedLambdaQuotientDworkCoeffModP_samePrimeFiniteLogTerm_p_even_eq_zero
    (hp_five : 5 ≤ p) (j : Fin (kummerLogRank p))
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K)
        (kummerLogEvenPowerIndex (p := p) hp_five j).1
        (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
            p - 1 ≤ (p - 2) + 1)
          (samePrimeFiniteLogTerm (p := p) (K := K) (p - 2) p x hx)) = 0 := by
  let R : Type _ := ValuedIntegerRing p K
  let S : Type _ := DworkCompleteIntegerRing p K
  let xD : S := algebraMap R S x
  have hxD_lam : xD ∈ dworkCompleteLambdaIdeal p K :=
    Ideal.mem_map_of_mem (algebraMap R S) hx
  have hxD_param : xD ∈ dworkParameterIdeal p K := by
    simpa [xD, dworkParameterIdeal_eq_dworkCompleteLambdaIdeal
      (p := p) (K := K)] using hxD_lam
  have hxD_span : xD ∈ Ideal.span ({dworkParameter p K} : Set S) := by
    simpa [dworkParameterIdeal, S] using hxD_param
  rcases Ideal.mem_span_singleton'.mp hxD_span with ⟨Z, hZraw⟩
  have hZ : xD = dworkParameter p K * Z := by
    calc
      xD = Z * dworkParameter p K := hZraw.symm
      _ = dworkParameter p K * Z := by ring
  rw [valuedLambdaQuotientDworkCoeffModP_samePrimeFiniteLogTerm_p_eq_ramificationCorrection
    (p := p) (K := K) hp_five
    (kummerLogEvenPowerIndex (p := p) hp_five j).1 hx hZ]
  rcases dworkComplete_residue_lift_rationalPadicInteger (p := p) (K := K) Z with
    ⟨c, hc⟩
  exact dworkRamificationCorrection_evenCoeff_eq_zero_of_sub_residue
    (p := p) (K := K) hp_five j c hc

omit [NumberField.IsCMField K] in
/-- On even Kummer rows, the unscaled normalized finite logarithm is computed
by the ordinary same-prime terms `1 <= n <= p - 1`; the folded `n = p`
correction has zero even coordinate. -/
theorem normalizedFiniteLogApprox_evenCoeff_eq_ordinaryTerms
    (hp_five : 5 ≤ p) (j : Fin (kummerLogRank p)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K)
        (kummerLogEvenPowerIndex (p := p) hp_five j).1
        (dworkParameterNormalizedFiniteLogApprox (p := p) (K := K)) =
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K)
        (kummerLogEvenPowerIndex (p := p) hp_five j).1
        (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
            p - 1 ≤ (p - 2) + 1)
          (∑ n ∈ Finset.Icc 1 (p - 1),
            samePrimeFiniteLogTerm (p := p) (K := K) (p - 2) n
              (dworkParameterNormalizedCoordApprox (p := p) (K := K) (p - 2))
              (dworkParameterNormalizedCoordApprox_mem_lambdaIdeal
                (p := p) (K := K) (p - 2)))) := by
  let x : ValuedIntegerRing p K :=
    dworkParameterNormalizedCoordApprox (p := p) (K := K) (p - 2)
  let hx : x ∈ lambdaIdeal p K :=
    dworkParameterNormalizedCoordApprox_mem_lambdaIdeal
      (p := p) (K := K) (p - 2)
  let hle : p - 1 ≤ (p - 2) + 1 := by omega
  let i : Fin (p - 1) := (kummerLogEvenPowerIndex (p := p) hp_five j).1
  have hlog :
      samePrimeFiniteLog (p := p) (K := K) (p - 2) x hx =
        (∑ n ∈ Finset.Icc 1 (p - 1),
          samePrimeFiniteLogTerm (p := p) (K := K) (p - 2) n x hx) +
        samePrimeFiniteLogTerm (p := p) (K := K) (p - 2) p x hx :=
    samePrimeFiniteLog_eq_sum_Icc_add_p_term_pow_pred
      (p := p) (K := K) (by omega : 3 ≤ p) hx
  have hpterm :
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
          (Ideal.Quotient.factorPow (lambdaIdeal p K) hle
            (samePrimeFiniteLogTerm (p := p) (K := K) (p - 2) p x hx)) = 0 :=
    valuedLambdaQuotientDworkCoeffModP_samePrimeFiniteLogTerm_p_even_eq_zero
      (p := p) (K := K) hp_five j hx
  unfold dworkParameterNormalizedFiniteLogApprox
  change
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.factorPow (lambdaIdeal p K) hle
          (samePrimeFiniteLog (p := p) (K := K) (p - 2) x hx)) =
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.factorPow (lambdaIdeal p K) hle
          (∑ n ∈ Finset.Icc 1 (p - 1),
            samePrimeFiniteLogTerm (p := p) (K := K) (p - 2) n x hx))
  rw [hlog]
  rw [map_add]
  rw [valuedLambdaQuotientDworkCoeffModP_add]
  rw [hpterm]
  simp

set_option linter.style.longLine false in
omit [NumberField.IsCMField K] in
/-- For ordinary same-prime logarithm terms `n < p`, no same-prime
denominator folding occurs.  Hence a homogeneous piece of lambda-degree
`>= N + 1` is already zero in the `lambda^(N + 1)` quotient. -/
theorem samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm_eq_zero_of_quotient_le_of_lt_prime
    {N n d : ℕ} {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hnlt : n < p) (hd : N + 1 ≤ d) :
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
      (p := p) (K := K) N n d x hx = 0 := by
  by_cases hn : n = 0
  · subst n
    simp [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm,
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore]
  by_cases hnd : n ≤ d
  · rw [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm_eq_signed_eval
      (p := p) (K := K) N n d hx hn hnd]
    have hfac : n.factorization p = 0 :=
      Nat.factorization_eq_zero_of_lt hnlt
    have heval :
        samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
          (((samePrimeFiniteArtinHasseNormalizedCoordPoly
            (p := p) (K := K) N x) ^ n).coeff d)
          (samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_mem_lambdaIdeal_pow
            (p := p) (K := K) N hx n d)
          (samePrimeFiniteArtinHasse_den_exponent_le (p := p) hn hnd) = 0 := by
      rw [samePrimeNatDivEvalAtDegree]
      exact samePrimeNatDivEval_eq_zero_of_succ_le
        (p := p) (K := K) hn _ (by simpa [hfac] using hd)
    rw [heval, mul_zero]
  · simp [samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm,
      samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousCore, hn, hnd]

set_option linter.style.longLine false in
omit [NumberField.IsCMField K] in
/-- An ordinary logarithm term `n < p` for the normalized Artin-Hasse
coordinate only needs homogeneous degrees below the quotient precision. -/
theorem samePrimeFiniteLogTerm_normalizedArtinHasseCoord_eq_homogeneous_quotient_sum_of_lt_prime
    (N n : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hnlt : n < p) :
    samePrimeFiniteLogTerm (p := p) (K := K) N n
        (samePrimeFiniteArtinHasseNormalizedCoord (p := p) (K := K) N x)
        (samePrimeFiniteArtinHasseNormalizedCoord_mem_lambdaIdeal
          (p := p) (K := K) N hx) =
      ∑ d ∈ Finset.range (N + 1),
        samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
          (p := p) (K := K) N n d x hx := by
  classical
  rw [samePrimeFiniteLogTerm_normalizedArtinHasseCoord_eq_homogeneous_cutoff_sum
    (p := p) (K := K) N n hx]
  let C : ℕ := samePrimeFiniteLogCutoff (p := p) N
  let f : ℕ → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) := fun d ↦
    samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm
      (p := p) (K := K) N n d x hx
  have hprec_le_cut : N + 1 ≤ C := by
    dsimp [C, samePrimeFiniteLogCutoff]
    exact Nat.le_mul_of_pos_left (N + 1) (Fact.out : Nat.Prime p).pos
  have hsubset : Finset.range (N + 1) ⊆ Finset.range C := fun d hd ↦
    Finset.mem_range.mpr ((Finset.mem_range.mp hd).trans_le hprec_le_cut)
  exact (Finset.sum_subset hsubset (by
    intro d _hdC hdSmall
    have hd : N + 1 ≤ d :=
      Nat.le_of_not_gt (by
        intro hlt
        exact hdSmall (Finset.mem_range.mpr hlt))
    exact samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousTerm_eq_zero_of_quotient_le_of_lt_prime
      (p := p) (K := K) hx hnlt hd)).symm

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in
-- The proof pushes the factorial-cleared homogeneous identity through
-- quotient maps and Dwork-coordinate extraction; elaboration is above the
-- default heartbeat budget.
omit [NumberField.IsCMField K] in
/-- Coordinate of one low normalized homogeneous degree slice at the Dwork
parameter approximant.  The bound `d < p - 1` makes `d!` invertible modulo
`p`, so the factorial-cleared source theorem can be read in `ZMod p`
coordinates. -/
theorem valuedLambdaQuotientDworkCoeffModP_factorPow_normalizedHomogeneousDegreeSum_dworkParameterApprox_of_lt
    (i : Fin (p - 1)) {d : ℕ} (hd : d < p - 1) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.factorPow (lambdaIdeal p K) (by omega :
            p - 1 ≤ (p - 2) + 1)
          (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
            (p := p) (K := K) (p - 2) d
            (dworkParameterApprox p K ((p - 2) + 1))
            (dworkParameterApprox_mem_lambdaIdeal
              (p := p) (K := K) ((p - 2) + 1)))) =
      (((d.factorial : ℕ) : ZMod p)⁻¹ *
        Furtwaengler.DieudonneDwork.rIntegralToZMod p
          (∑ n ∈ Finset.Icc 1 d,
            rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n)) *
        rationalPadicIntegerToZMod p
          (((Pi.single (⟨d, hd⟩ : Fin (p - 1))
            (1 : RationalPadicIntegerRing p) :
              Fin (p - 1) → RationalPadicIntegerRing p) i)) := by
  classical
  let hle : p - 1 ≤ (p - 2) + 1 := by omega
  let x : ValuedIntegerRing p K :=
    dworkParameterApprox p K ((p - 2) + 1)
  let hx : x ∈ lambdaIdeal p K :=
    dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) ((p - 2) + 1)
  let S : Furtwaengler.DieudonneDwork.rIntegralRatSubring p :=
    ∑ n ∈ Finset.Icc 1 d,
      rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n
  let b : ZMod p :=
    rationalPadicIntegerToZMod p
      (((Pi.single (⟨d, hd⟩ : Fin (p - 1))
        (1 : RationalPadicIntegerRing p) :
          Fin (p - 1) → RationalPadicIntegerRing p) i))
  have hfac_ne : (((d.factorial : ℕ) : ZMod p)) ≠ 0 := by
    intro hzero
    have hp_dvd : p ∣ d.factorial :=
      (ZMod.natCast_eq_zero_iff d.factorial p).mp hzero
    have hlt : d < p := by omega
    exact Nat.not_lt.mpr
      ((Nat.Prime.dvd_factorial (Fact.out : Nat.Prime p)).mp hp_dvd) hlt
  have hsource :=
    natCast_factorial_mul_samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum_eq_formal
      (p := p) (K := K) (N := p - 2) (d := d) hx
  have hsource_factor :=
    congrArg (Ideal.Quotient.factorPow (lambdaIdeal p K) hle) hsource
  have hsource_coord :=
    congrArg (valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i)
      hsource_factor
  have hright :
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.factorPow (lambdaIdeal p K) hle
          (samePrimeQuotientMap (p := p) (K := K) (p - 2) (x ^ d) *
            samePrimeRIntegralRatToQuotient (p := p) (K := K) (p - 2) S)) =
        Furtwaengler.DieudonneDwork.rIntegralToZMod p S * b := by
    have hparam : (p - 2) + 1 = p - 1 := by
      have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
      omega
    have hxpow :
        x ^ d =
          dworkParameterApprox p K (p - 1) ^ d := by
      dsimp [x]
      rw [hparam]
    have hquot :
        Ideal.Quotient.factorPow (lambdaIdeal p K) hle
          (samePrimeQuotientMap (p := p) (K := K) (p - 2) (x ^ d) *
            samePrimeRIntegralRatToQuotient (p := p) (K := K) (p - 2) S) =
          Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1))
            (rIntegralRatToValuedInteger p K S *
              dworkParameterApprox p K (p - 1) ^ d) := by
      change Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1))
          (x ^ d * rIntegralRatToValuedInteger p K S) =
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1))
          (rIntegralRatToValuedInteger p K S *
            dworkParameterApprox p K (p - 1) ^ d)
      rw [hxpow]
      ring_nf
    rw [hquot]
    exact
      valuedLambdaQuotientDworkCoeffModP_mk_rIntegralRat_mul_dworkParameterApprox_pow_of_lt
        (p := p) (K := K) i S hd
  have hmul :
      ((d.factorial : ℕ) : ZMod p) *
          valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
            (Ideal.Quotient.factorPow (lambdaIdeal p K) hle
              (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
                (p := p) (K := K) (p - 2) d x hx)) =
        Furtwaengler.DieudonneDwork.rIntegralToZMod p S * b := by
    have hleft :
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
            (Ideal.Quotient.factorPow (lambdaIdeal p K) hle
              (((d.factorial : ℕ) :
                  ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ ((p - 2) + 1)) *
                samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
                  (p := p) (K := K) (p - 2) d x hx)) =
          ((d.factorial : ℕ) : ZMod p) *
            valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
              (Ideal.Quotient.factorPow (lambdaIdeal p K) hle
                (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
                  (p := p) (K := K) (p - 2) d x hx)) := by
      simpa [map_mul] using
        valuedLambdaQuotientDworkCoeffModP_natCast_mul
          (p := p) (K := K) i d.factorial
          (Ideal.Quotient.factorPow (lambdaIdeal p K) hle
            (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
              (p := p) (K := K) (p - 2) d x hx))
    rw [hleft] at hsource_coord
    rw [hright] at hsource_coord
    simpa [S] using hsource_coord
  apply (isUnit_iff_ne_zero.mpr hfac_ne).mul_left_cancel
  calc
    ((d.factorial : ℕ) : ZMod p) *
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
          (Ideal.Quotient.factorPow (lambdaIdeal p K) hle
            (samePrimeFiniteArtinHasseNormalizedCoordLogHomogeneousDegreeSum
              (p := p) (K := K) (p - 2) d x hx))
        = Furtwaengler.DieudonneDwork.rIntegralToZMod p S * b := hmul
    _ =
        ((d.factorial : ℕ) : ZMod p) *
          ((((d.factorial : ℕ) : ZMod p)⁻¹ *
            Furtwaengler.DieudonneDwork.rIntegralToZMod p S) * b) := by
        calc
          Furtwaengler.DieudonneDwork.rIntegralToZMod p S * b =
              (((d.factorial : ℕ) : ZMod p) *
                ((d.factorial : ℕ) : ZMod p)⁻¹) *
                  (Furtwaengler.DieudonneDwork.rIntegralToZMod p S * b) := by
                rw [mul_inv_cancel₀ hfac_ne, one_mul]
          _ =
              ((d.factorial : ℕ) : ZMod p) *
                ((((d.factorial : ℕ) : ZMod p)⁻¹ *
                  Furtwaengler.DieudonneDwork.rIntegralToZMod p S) * b) := by
                ring

end CyclotomicUnits
end BernoulliRegular

end
