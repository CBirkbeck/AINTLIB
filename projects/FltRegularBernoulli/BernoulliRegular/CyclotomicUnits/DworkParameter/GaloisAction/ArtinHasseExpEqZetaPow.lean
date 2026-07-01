module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.GaloisAction.TeichmullerScaledParameter

@[expose] public section

noncomputable section

/-!
# Scaled Dwork parameter, exact Artin--Hasse value

This file finishes CU-09g3b: the principal-unit logarithm-kernel uniqueness
step identifying the completed Artin--Hasse value at a Teichmuller multiple of
the Dwork parameter with the corresponding power of the cyclotomic root.
-/

namespace BernoulliRegular
namespace CyclotomicUnits
namespace PadicLogSetup
namespace DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation "R" => ValuedIntegerRing p K
local notation "I" => lambdaIdeal p K

/-- Finite Artin--Hasse exponential representative for the scaled Dwork
parameter in precision `N + 1`. -/
noncomputable def scaledDworkParameterExpApprox (a : ZMod p) (N : ℕ) : R :=
  samePrimeFiniteArtinHasseExp (p := p) (K := K) N
    (scaledDworkParameterApprox p K a (N + 1))

theorem quotient_mk_scaledDworkParameterExpApprox_eq_evalIntegralPowerSeriesMod
    (a : ZMod p) (N : ℕ) :
    Ideal.Quotient.mk (I ^ (N + 1))
        (scaledDworkParameterExpApprox p K a N) =
      evalIntegralPowerSeriesMod p K (integralExpSeries p K)
        (scaledDworkParameter p K a) (N + 1) := by
  let q : R →+* R ⧸ I ^ (N + 1) := Ideal.Quotient.mk (I ^ (N + 1))
  change
    q ((PowerSeries.trunc (N + 1) (integralExpSeries p K)).eval₂
        (RingHom.id R) (scaledDworkParameterApprox p K a (N + 1))) =
      (PowerSeries.trunc (N + 1) (PowerSeries.map q (integralExpSeries p K))).eval₂
        (RingHom.id (R ⧸ I ^ (N + 1)))
        (AdicCompletion.evalₐ I (N + 1) (scaledDworkParameter p K a))
  rw [scaledDworkParameter_evalₐ, PowerSeries.eval₂_trunc_eq_sum_range, map_sum,
    PowerSeries.eval₂_trunc_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simp [q, map_pow]

theorem scaledDworkParameterExpApprox_smodEq
    (a : ZMod p) {M N : ℕ} (hMN : M ≤ N) :
    scaledDworkParameterExpApprox p K a M -
        scaledDworkParameterExpApprox p K a N ∈ I ^ (M + 1) := by
  have hM :
      Ideal.Quotient.mk (I ^ (M + 1))
          (scaledDworkParameterExpApprox p K a M) =
        evalIntegralPowerSeriesMod p K (integralExpSeries p K)
          (scaledDworkParameter p K a) (M + 1) := by
    simpa using
      quotient_mk_scaledDworkParameterExpApprox_eq_evalIntegralPowerSeriesMod
        (p := p) (K := K) a M
  have hNpow :
      Ideal.Quotient.mk (I ^ (N + 1))
          (scaledDworkParameterExpApprox p K a N) =
        evalIntegralPowerSeriesMod p K (integralExpSeries p K)
          (scaledDworkParameter p K a) (N + 1) := by
    simpa using
      quotient_mk_scaledDworkParameterExpApprox_eq_evalIntegralPowerSeriesMod
        (p := p) (K := K) a N
  have hfactor := congrArg
    (Ideal.Quotient.factorPow I (Nat.succ_le_succ hMN)) hNpow
  have hN :
      Ideal.Quotient.mk (I ^ (M + 1))
          (scaledDworkParameterExpApprox p K a N) =
        evalIntegralPowerSeriesMod p K (integralExpSeries p K)
          (scaledDworkParameter p K a) (M + 1) := by
    simpa [Ideal.Quotient.factorPow] using
      hfactor.trans
        (evalIntegralPowerSeriesMod_factor_eq (p := p) (K := K)
          (F := integralExpSeries p K)
          (x := scaledDworkParameter p K a)
          (scaledDworkParameter_evalₐ_one (p := p) (K := K) a)
          (Nat.succ_le_succ hMN))
  exact Ideal.Quotient.eq.mp (hM.trans hN.symm)

theorem samePrimeFiniteLog_scaledDworkParameterExpCoord_eq_zero
    (a : ZMod p) (N : ℕ) :
    samePrimeFiniteLog (p := p) (K := K) N
        (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N
          (scaledDworkParameterApprox p K a (N + 1)))
        (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal
          (p := p) (K := K) N
          (scaledDworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) a (N + 1))) =
      0 := by
  rw [samePrimeFiniteLog_finiteArtinHasseExpCoord_eq_finiteArtinHasseLog
    (p := p) (K := K) N
    (scaledDworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) a (N + 1))]
  exact scaledDworkParameterFiniteArtinHasseLog_eq_zero (p := p) (K := K) a N

theorem zetaPowSubOne_mem_lambdaIdeal (a : ZMod p) :
    valuedCyclotomicZetaInteger p K ^ a.val - 1 ∈ I := by
  have hsq :
      valuedCyclotomicZetaInteger p K ^ a.val - 1 -
          (a.val : R) * valuedCyclotomicLambdaInteger p K ∈ I ^ 2 :=
    valuedCyclotomicZetaInteger_pow_sub_one_sub_natCast_mul_lambda_mem_sq
      (p := p) (K := K) a
  have hlin :
      (a.val : R) * valuedCyclotomicLambdaInteger p K ∈ I :=
    (lambdaIdeal p K).mul_mem_left _
      (valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K))
  have hsqI :
      valuedCyclotomicZetaInteger p K ^ a.val - 1 -
          (a.val : R) * valuedCyclotomicLambdaInteger p K ∈ I :=
    Ideal.pow_le_self (by decide : 2 ≠ 0) hsq
  have hsum : (valuedCyclotomicZetaInteger p K ^ a.val - 1 -
          (a.val : R) * valuedCyclotomicLambdaInteger p K) +
        (a.val : R) * valuedCyclotomicLambdaInteger p K ∈ I :=
    (lambdaIdeal p K).add_mem hsqI hlin
  convert hsum using 1
  ring

theorem samePrimeFiniteLog_zetaPowSubOne_eq_zero
    (a : ZMod p) (N : ℕ) :
    samePrimeFiniteLog (p := p) (K := K) N
        (valuedCyclotomicZetaInteger p K ^ a.val - 1)
        (zetaPowSubOne_mem_lambdaIdeal (p := p) (K := K) a) = 0 := by
  let lam : R := valuedCyclotomicLambdaInteger p K
  have hcoord :
      samePrimeFiniteLogPowCoord (p := p) (K := K) a.val lam =
        valuedCyclotomicZetaInteger p K ^ a.val - 1 := by
    rw [samePrimeFiniteLogPowCoord, ← valuedCyclotomicZetaInteger_eq_one_add_lambda
      (p := p) (K := K)]
  have hpow :=
    samePrimeFiniteLog_powCoord (p := p) (K := K) N a.val
      (valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K))
  have hloglam :
      samePrimeFiniteLog (p := p) (K := K) N lam
          (valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K)) = 0 := by
    rw [← dworkParameterFiniteArtinHasseLog_eq_samePrimeFiniteLog_lambda
      (p := p) (K := K) N]
    exact dworkParameterFiniteArtinHasseLog_eq_zero (p := p) (K := K) N
  rw [← samePrimeFiniteLog_eq_of_eq (p := p) (K := K) hcoord
    (samePrimeFiniteLogPowCoord_mem_lambdaIdeal (p := p) (K := K)
      (valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K)) a.val)
    (zetaPowSubOne_mem_lambdaIdeal (p := p) (K := K) a)]
  rw [hpow, hloglam, nsmul_zero]

theorem dworkComplete_evalₐ_eq_zero_of_mem_lambdaIdeal_pow
    {N : ℕ} {x : DworkCompleteIntegerRing p K}
    (hx : x ∈ (dworkCompleteLambdaIdeal p K) ^ N) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N x = 0 := by
  let S : Type _ := DworkCompleteIntegerRing p K
  have hxmap :
      x ∈ ((lambdaIdeal p K) ^ N).map (algebraMap R S) := by
    simpa [S, dworkCompleteLambdaIdeal, Ideal.map_pow] using hx
  have hle :
      ((lambdaIdeal p K) ^ N).map (algebraMap R S) ≤
        RingHom.ker (AdicCompletion.evalₐ (lambdaIdeal p K) N) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    change AdicCompletion.evalₐ (lambdaIdeal p K) N
        (algebraMap R S y) = 0
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hy
  exact hle hxmap

theorem zetaPow_pow_prime_eq_one (a : ZMod p) :
    (valuedCyclotomicZetaInteger p K ^ a.val) ^ p = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul,
    valuedCyclotomicZetaInteger_pow_eq_one (p := p) (K := K), one_pow]

theorem zetaPow_mul_zetaPow_pred_eq_one (a : ZMod p) :
    valuedCyclotomicZetaInteger p K ^ a.val *
        (valuedCyclotomicZetaInteger p K ^ a.val) ^ (p - 1) = 1 := by
  rw [mul_pow_sub_one (Fact.out : Nat.Prime p).ne_zero,
    zetaPow_pow_prime_eq_one (p := p) (K := K) a]

theorem scaledDworkParameterExpApprox_sub_zetaPow_mem_sq
    (a : ZMod p) :
    scaledDworkParameterExpApprox p K a 1 -
        valuedCyclotomicZetaInteger p K ^ a.val ∈ I ^ 2 := by
  let z : R := valuedCyclotomicZetaInteger p K ^ a.val
  have hcomp :
      artinHasseExp_eval_scaledDworkParameter p K a -
          AdicCompletion.of (lambdaIdeal p K) R z ∈
        (dworkCompleteLambdaIdeal p K) ^ 2 := by
    simpa [z] using
      artinHasseExp_eval_scaledDworkParameter_sub_zeta_pow_mem_sq
        (p := p) (K := K) a
  have hzero :
      AdicCompletion.evalₐ (lambdaIdeal p K) 2
          (artinHasseExp_eval_scaledDworkParameter p K a -
            AdicCompletion.of (lambdaIdeal p K) R z) = 0 :=
    dworkComplete_evalₐ_eq_zero_of_mem_lambdaIdeal_pow (p := p) (K := K) hcomp
  rw [map_sub, artinHasseExp_eval_scaledDworkParameter_evalₐ,
    ← quotient_mk_scaledDworkParameterExpApprox_eq_evalIntegralPowerSeriesMod
      (p := p) (K := K) a 1,
    AdicCompletion.evalₐ_of] at hzero
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

theorem samePrimeFiniteLog_scaledDworkParameterExpApprox_sub_one_eq_zero
    (a : ZMod p) (N : ℕ) :
    samePrimeFiniteLog (p := p) (K := K) N
        (scaledDworkParameterExpApprox p K a N - 1)
        (by
          simpa [scaledDworkParameterExpApprox, samePrimeFiniteArtinHasseExpCoord] using
            samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal
              (p := p) (K := K) N
              (scaledDworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) a (N + 1))) =
      0 := by
  simpa [scaledDworkParameterExpApprox, samePrimeFiniteArtinHasseExpCoord] using
    samePrimeFiniteLog_scaledDworkParameterExpCoord_eq_zero
      (p := p) (K := K) a N

theorem scaledDworkParameterExpApprox_sub_zetaPow_mem_step
    (a : ZMod p) {N : ℕ} (hN : 1 ≤ N)
    (hprev :
      scaledDworkParameterExpApprox p K a N -
          valuedCyclotomicZetaInteger p K ^ a.val ∈ I ^ (N + 1)) :
    scaledDworkParameterExpApprox p K a (N + 1) -
        valuedCyclotomicZetaInteger p K ^ a.val ∈ I ^ (N + 2) := by
  let z : R := valuedCyclotomicZetaInteger p K ^ a.val
  let E : R := scaledDworkParameterExpApprox p K a (N + 1)
  let x : R := z - 1
  let w : R := z ^ (p - 1) * (E - z)
  have hcompat :
      scaledDworkParameterExpApprox p K a N -
          scaledDworkParameterExpApprox p K a (N + 1) ∈ I ^ (N + 1) :=
    scaledDworkParameterExpApprox_smodEq (p := p) (K := K) a (Nat.le_succ N)
  have hEprev : E - z ∈ I ^ (N + 1) := by
    have hneg :
        scaledDworkParameterExpApprox p K a (N + 1) -
            scaledDworkParameterExpApprox p K a N ∈ I ^ (N + 1) := by
      simpa [sub_eq_add_neg, add_comm] using
        (I ^ (N + 1)).neg_mem hcompat
    have hsum : (scaledDworkParameterExpApprox p K a (N + 1) -
            scaledDworkParameterExpApprox p K a N) +
          (scaledDworkParameterExpApprox p K a N - z) ∈ I ^ (N + 1) :=
      (I ^ (N + 1)).add_mem hneg (by simpa [z] using hprev)
    simpa [E, z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
  have hwPow : w ∈ I ^ (N + 1) :=
    (I ^ (N + 1)).mul_mem_left (z ^ (p - 1)) hEprev
  have hwI : w ∈ I :=
    Ideal.pow_le_self (Nat.ne_of_gt (Nat.succ_pos N)) hwPow
  have hx : x ∈ I := by
    simpa [x, z] using zetaPowSubOne_mem_lambdaIdeal (p := p) (K := K) a
  have hEarg : E - 1 ∈ I := by
    simpa [E, scaledDworkParameterExpApprox, samePrimeFiniteArtinHasseExpCoord] using
      samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal
        (p := p) (K := K) (N + 1)
        (scaledDworkParameterApprox_mem_lambdaIdeal
          (p := p) (K := K) a (N + 2))
  have hzw : z * w = E - z := by
    dsimp [w]
    rw [← mul_assoc, zetaPow_mul_zetaPow_pred_eq_one (p := p) (K := K) a,
      one_mul]
  have hprod :
      samePrimeFiniteLogProductCoord (p := p) (K := K) x w = E - 1 := by
    dsimp [samePrimeFiniteLogProductCoord, x]
    calc
      z - 1 + w + (z - 1) * w = z - 1 + z * w := by ring
      _ = z - 1 + (E - z) := by rw [hzw]
      _ = E - 1 := by ring
  have hlogE :
      samePrimeFiniteLog (p := p) (K := K) (N + 1) (E - 1) hEarg = 0 := by
    simpa [E] using
      samePrimeFiniteLog_scaledDworkParameterExpApprox_sub_one_eq_zero
        (p := p) (K := K) a (N + 1)
  have hlogProd :
      samePrimeFiniteLog (p := p) (K := K) (N + 1)
          (samePrimeFiniteLogProductCoord (p := p) (K := K) x w)
          (samePrimeFiniteLogProductCoord_mem_lambdaIdeal (p := p) (K := K) hx hwI) = 0 := by
    rw [samePrimeFiniteLog_eq_of_eq (p := p) (K := K) hprod
      (samePrimeFiniteLogProductCoord_mem_lambdaIdeal (p := p) (K := K) hx hwI)
      hEarg]
    exact hlogE
  have hlogx :
      samePrimeFiniteLog (p := p) (K := K) (N + 1) x hx = 0 := by
    rw [samePrimeFiniteLog_eq_of_eq (p := p) (K := K) (by rfl)
      hx (zetaPowSubOne_mem_lambdaIdeal (p := p) (K := K) a)]
    exact samePrimeFiniteLog_zetaPowSubOne_eq_zero (p := p) (K := K) a (N + 1)
  have hlogw :
      samePrimeFiniteLog (p := p) (K := K) (N + 1) w hwI = 0 := by
    have hadd := samePrimeFiniteLog_add_add_mul (p := p) (K := K)
      (N + 1) hx hwI
    rw [hlogProd, hlogx, zero_add] at hadd
    exact hadd.symm
  have hm : 2 ≤ N + 1 := Nat.succ_le_succ hN
  have hmk :
      Ideal.Quotient.mk (I ^ ((N + 1) + 1)) w = 0 := by
    rw [← samePrimeFiniteLog_eq_mk_of_mem_pow_of_two_le
      (p := p) (K := K) hm hwPow]
    exact hlogw
  have hwNext : w ∈ I ^ (N + 2) := by
    simpa [Nat.add_assoc] using Ideal.Quotient.eq_zero_iff_mem.mp hmk
  have hfinal : z * w ∈ I ^ (N + 2) :=
    (I ^ (N + 2)).mul_mem_left z hwNext
  have hfinal' : E - z ∈ I ^ (N + 2) := by
    simpa [hzw] using hfinal
  simpa [E, z] using hfinal'

theorem scaledDworkParameterExpApprox_sub_zetaPow_mem_pow_succ
    (a : ZMod p) {N : ℕ} (hN : 1 ≤ N) :
    scaledDworkParameterExpApprox p K a N -
        valuedCyclotomicZetaInteger p K ^ a.val ∈ I ^ (N + 1) := by
  induction N using Nat.case_strong_induction_on with
  | hz =>
      cases hN
  | hi N ih =>
      by_cases hN0 : N = 0
      · subst N
        simpa using scaledDworkParameterExpApprox_sub_zetaPow_mem_sq
          (p := p) (K := K) a
      · have hpos : 1 ≤ N := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN0)
        exact scaledDworkParameterExpApprox_sub_zetaPow_mem_step
          (p := p) (K := K) a hpos (ih N le_rfl hpos)

theorem scaledDworkParameterExpApprox_zero_sub_zetaPow_mem
    (a : ZMod p) :
    scaledDworkParameterExpApprox p K a 0 -
        valuedCyclotomicZetaInteger p K ^ a.val ∈ I := by
  have hcompat :
      scaledDworkParameterExpApprox p K a 0 -
          scaledDworkParameterExpApprox p K a 1 ∈ I ^ (0 + 1) :=
    scaledDworkParameterExpApprox_smodEq (p := p) (K := K) a (by decide : 0 ≤ 1)
  have hbase :
      scaledDworkParameterExpApprox p K a 1 -
          valuedCyclotomicZetaInteger p K ^ a.val ∈ I ^ (0 + 1) :=
    Ideal.pow_le_pow_right (by decide : 1 ≤ 2)
      (scaledDworkParameterExpApprox_sub_zetaPow_mem_sq (p := p) (K := K) a)
  have hsum : (scaledDworkParameterExpApprox p K a 0 -
          scaledDworkParameterExpApprox p K a 1) +
        (scaledDworkParameterExpApprox p K a 1 -
          valuedCyclotomicZetaInteger p K ^ a.val) ∈ I ^ (0 + 1) :=
    (I ^ (0 + 1)).add_mem hcompat hbase
  simpa using hsum

theorem artinHasseExp_eval_scaledDworkParameter_eq_zeta_pow
    (a : ZMod p) :
    artinHasseExp_eval_scaledDworkParameter p K a =
      AdicCompletion.of (lambdaIdeal p K) R
        (valuedCyclotomicZetaInteger p K ^ a.val) := by
  apply AdicCompletion.ext_evalₐ
  intro N
  cases N with
  | zero =>
      -- The codomain `R ⧸ I ^ 0` is trivial, so both evaluations are `0`.
      exact (quotient_pow_zero_eq_zero (p := p) (K := K) (lambdaIdeal p K) _).trans
        (quotient_pow_zero_eq_zero (p := p) (K := K) (lambdaIdeal p K) _).symm
  | succ N =>
      rw [artinHasseExp_eval_scaledDworkParameter_evalₐ,
        ← quotient_mk_scaledDworkParameterExpApprox_eq_evalIntegralPowerSeriesMod
          (p := p) (K := K) a N,
        AdicCompletion.evalₐ_of]
      apply Ideal.Quotient.eq.mpr
      cases N with
      | zero =>
          simpa using scaledDworkParameterExpApprox_zero_sub_zetaPow_mem
            (p := p) (K := K) (a := a)
      | succ N =>
          exact scaledDworkParameterExpApprox_sub_zetaPow_mem_pow_succ
            (p := p) (K := K) a (by omega)

end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular
