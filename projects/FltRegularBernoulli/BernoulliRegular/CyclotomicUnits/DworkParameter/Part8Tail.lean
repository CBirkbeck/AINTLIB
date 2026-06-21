module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.Part8Conjugation

/-!
# The corrected Dwork parameter: vanishing of the finite Artin--Hasse logarithm

This file evaluates the integral Artin--Hasse exponential at the Dwork parameter modulo
powers of the principal `lambda`-ideal, identifies the resulting finite logarithm with the
same-prime finite logarithm of `lambda`, and assembles these compatible finite coordinates
into a completed element. It then shows that element — and hence every finite coordinate —
vanishes, which is the `p`-torsion input to the same-prime principal-unit argument.

## Main definitions

* `dworkParameterExpApprox`: the finite Artin--Hasse exponential approximants evaluated at
  the Dwork parameter approximants.
* `dworkParameterFiniteArtinHasseLogCoord`: the finite Artin--Hasse logarithm coordinates,
  packaged for adic-completion assembly.
* `artinHasseLog_eval_dworkParameter`: the completed Artin--Hasse logarithm of the Dwork
  parameter, assembled from its compatible finite quotient coordinates.

## Main results

* `dworkParameter_eval_exp_mod`: the finite-quotient form of `E_p(G_p(lambda)) = zeta_p`.
* `dworkParameterFiniteArtinHasseLog_eq_zero`: each finite Artin--Hasse logarithm of the
  Dwork parameter vanishes.
* `artinHasseLog_eval_dworkParameter_eq_zero`: the completed Artin--Hasse logarithm of the
  Dwork parameter is zero.
-/

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


/-- Principal-unit coordinate of a power, used by finite-log torsion
statements. -/
def samePrimeFiniteLogPowCoord (n : ℕ) (x : ValuedIntegerRing p K) :
    ValuedIntegerRing p K :=
  (1 + x) ^ n - 1

theorem samePrimeFiniteLogProductCoord_powCoord
    (n : ℕ) (x : ValuedIntegerRing p K) :
    samePrimeFiniteLogProductCoord (p := p) (K := K)
        (samePrimeFiniteLogPowCoord (p := p) (K := K) n x) x =
      samePrimeFiniteLogPowCoord (p := p) (K := K) (n + 1) x := by
  unfold samePrimeFiniteLogProductCoord samePrimeFiniteLogPowCoord
  rw [pow_succ]
  ring

theorem samePrimeFiniteLogPowCoord_mem_lambdaIdeal
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) (n : ℕ) :
    samePrimeFiniteLogPowCoord (p := p) (K := K) n x ∈ lambdaIdeal p K := by
  induction n with
  | zero =>
      simp [samePrimeFiniteLogPowCoord]
  | succ n ih =>
      have hprod :
          samePrimeFiniteLogProductCoord (p := p) (K := K)
              (samePrimeFiniteLogPowCoord (p := p) (K := K) n x) x ∈
            lambdaIdeal p K :=
        samePrimeFiniteLogProductCoord_mem_lambdaIdeal
          (p := p) (K := K) ih hx
      simpa [Nat.succ_eq_add_one, samePrimeFiniteLogProductCoord_powCoord]
        using hprod

theorem samePrimeFiniteLog_powCoord (N n : ℕ)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLog (p := p) (K := K) N
        (samePrimeFiniteLogPowCoord (p := p) (K := K) n x)
        (samePrimeFiniteLogPowCoord_mem_lambdaIdeal (p := p) (K := K) hx n) =
      n • samePrimeFiniteLog (p := p) (K := K) N x hx := by
  induction n with
  | zero =>
      simp [samePrimeFiniteLogPowCoord, samePrimeFiniteLog_arg_zero]
  | succ n ih =>
      have hpow_mem :
          samePrimeFiniteLogPowCoord (p := p) (K := K) n x ∈ lambdaIdeal p K :=
        samePrimeFiniteLogPowCoord_mem_lambdaIdeal (p := p) (K := K) hx n
      have hprod_mem :
          samePrimeFiniteLogProductCoord (p := p) (K := K)
              (samePrimeFiniteLogPowCoord (p := p) (K := K) n x) x ∈
            lambdaIdeal p K :=
        samePrimeFiniteLogProductCoord_mem_lambdaIdeal
          (p := p) (K := K) hpow_mem hx
      calc
        samePrimeFiniteLog (p := p) (K := K) N
            (samePrimeFiniteLogPowCoord (p := p) (K := K) (Nat.succ n) x)
            (samePrimeFiniteLogPowCoord_mem_lambdaIdeal (p := p) (K := K) hx (Nat.succ n))
            =
          samePrimeFiniteLog (p := p) (K := K) N
            (samePrimeFiniteLogProductCoord (p := p) (K := K)
              (samePrimeFiniteLogPowCoord (p := p) (K := K) n x) x)
            hprod_mem :=
            samePrimeFiniteLog_eq_of_eq (p := p) (K := K) (N := N)
              (by
                rw [Nat.succ_eq_add_one]
                exact (samePrimeFiniteLogProductCoord_powCoord
                  (p := p) (K := K) n x).symm)
              (samePrimeFiniteLogPowCoord_mem_lambdaIdeal (p := p) (K := K) hx (Nat.succ n))
              hprod_mem
        _ =
          samePrimeFiniteLog (p := p) (K := K) N
              (samePrimeFiniteLogPowCoord (p := p) (K := K) n x) hpow_mem +
            samePrimeFiniteLog (p := p) (K := K) N x hx :=
            samePrimeFiniteLog_add_add_mul (p := p) (K := K) N hpow_mem hx
        _ = n • samePrimeFiniteLog (p := p) (K := K) N x hx +
            samePrimeFiniteLog (p := p) (K := K) N x hx := by
            rw [ih]
        _ = Nat.succ n • samePrimeFiniteLog (p := p) (K := K) N x hx := by
            rw [Nat.succ_eq_add_one]
            ring

@[simp]
theorem samePrimeFiniteLogPowCoord_prime_lambda :
    samePrimeFiniteLogPowCoord (p := p) (K := K) p
        (valuedCyclotomicLambdaInteger p K) = 0 := by
  rw [samePrimeFiniteLogPowCoord, ← valuedCyclotomicZetaInteger_eq_one_add_lambda
    (p := p) (K := K), valuedCyclotomicZetaInteger_pow_eq_one]
  simp

theorem samePrimeFiniteLogPowCoord_prime_lambda_mem :
    samePrimeFiniteLogPowCoord (p := p) (K := K) p
        (valuedCyclotomicLambdaInteger p K) ∈ lambdaIdeal p K := by
  rw [samePrimeFiniteLogPowCoord_prime_lambda]
  exact zero_mem (lambdaIdeal p K)

theorem samePrimeFiniteLog_powCoord_prime_lambda_eq_zero (N : ℕ) :
    samePrimeFiniteLog (p := p) (K := K) N
        (samePrimeFiniteLogPowCoord (p := p) (K := K) p
          (valuedCyclotomicLambdaInteger p K))
        (samePrimeFiniteLogPowCoord_prime_lambda_mem (p := p) (K := K)) = 0 := by
  simp [samePrimeFiniteLogPowCoord_prime_lambda]

theorem samePrimeFiniteLog_lambda_p_nsmul_eq_zero (N : ℕ) :
    p • samePrimeFiniteLog (p := p) (K := K) N
        (valuedCyclotomicLambdaInteger p K)
        (valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K)) = 0 := by
  calc
    p • samePrimeFiniteLog (p := p) (K := K) N
        (valuedCyclotomicLambdaInteger p K)
        (valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K))
        =
      samePrimeFiniteLog (p := p) (K := K) N
        (samePrimeFiniteLogPowCoord (p := p) (K := K) p
          (valuedCyclotomicLambdaInteger p K))
        (samePrimeFiniteLogPowCoord_mem_lambdaIdeal (p := p) (K := K)
          (valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K)) p) :=
        (samePrimeFiniteLog_powCoord (p := p) (K := K) N p
          (valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K))).symm
    _ = 0 :=
        samePrimeFiniteLog_powCoord_prime_lambda_eq_zero (p := p) (K := K) N

theorem samePrimeFiniteLog_lambda_natCast_p_mul_eq_zero (N : ℕ) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) (p : ValuedIntegerRing p K) *
        samePrimeFiniteLog (p := p) (K := K) N
          (valuedCyclotomicLambdaInteger p K)
          (valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K)) = 0 := by
  have h := samePrimeFiniteLog_lambda_p_nsmul_eq_zero (p := p) (K := K) N
  rw [nsmul_eq_mul] at h
  rw [map_natCast]
  exact h

/-- Finite-quotient form of `E_p(G_p(lambda)) = zeta_p`.  This is the honest
statement currently available before introducing a general infinite
power-series evaluation API on the completed ring. -/
theorem dworkParameter_eval_exp_mod (N : ℕ) :
    let A : Type _ := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)
    let φ : ValuedIntegerRing p K →+* A :=
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
    let Eps : PowerSeries A := PowerSeries.map φ (integralExpSeries p K)
    (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (AdicCompletion.evalₐ (lambdaIdeal p K) (N + 1) (dworkParameter p K)) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (valuedCyclotomicZetaInteger p K) := by
  classical
  dsimp only
  let A : Type _ := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)
  let q : ValuedIntegerRing p K →+* A :=
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
  let φ : Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+* A :=
    q.comp (rIntegralRatToValuedInteger p K)
  let hE : Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (Furtwaengler.artinHasseExpSeries p) :=
    Furtwaengler.artinHasseExpSeries_coeff_isRIntegral p
  let hInv : Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (FormalDwork.inverseSeries p) :=
    FormalDwork.inverseSeries_isPIntegral p
  let Eps : PowerSeries A := hE.mapTo φ
  let Ips : PowerSeries A := hInv.mapTo φ
  let lambdabar : A := q (valuedCyclotomicLambdaInteger p K)
  let gammabar : A :=
    AdicCompletion.evalₐ (lambdaIdeal p K) (N + 1) (dworkParameter p K)
  have hlambdaNil : lambdabar ^ (N + 1) = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact valuedCyclotomicLambdaInteger_pow_mem_lambdaIdeal_pow
      (p := p) (K := K) (N + 1)
  have hgammaMk :
      gammabar =
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          (dworkParameterApprox p K (N + 1)) := by
    simp [gammabar]
  have hgammaEq :
      gammabar =
        (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) lambdabar := by
    calc
      gammabar =
          Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
            (dworkParameterApprox p K (N + 1)) := hgammaMk
      _ = (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) lambdabar := by
            simpa [A, q, φ, hInv, Ips, lambdabar, integralInverseSeries,
              Furtwaengler.DieudonneDwork.IsRIntegralPS.map_mapTo] using
              quotient_mk_dworkParameterApprox_eq_trunc_eval
                (p := p) (K := K) (N + 1)
  have hgammaMem :
      dworkParameterApprox p K (N + 1) ∈ lambdaIdeal p K :=
    dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1)
  have hgammaNil : gammabar ^ (N + 1) = 0 := by
    rw [hgammaMk, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hgammaMem (N + 1)
  have hSubInv :
      PowerSeries.subst (PowerSeries.C lambdabar) Ips = PowerSeries.C gammabar := by
    rw [Furtwaengler.powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero
      lambdabar N hlambdaNil Ips]
    rw [← hgammaEq]
  have hInv0 : PowerSeries.constantCoeff Ips = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_mapTo]
    have hcoeff0 :
        (PowerSeries.coeff (R := ℚ) 0) (FormalDwork.inverseSeries p) = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact FormalDwork.inverseSeries_constantCoeff p
    have hsubzero :
        (⟨(PowerSeries.coeff (R := ℚ) 0) (FormalDwork.inverseSeries p),
            hInv 0⟩ :
          Furtwaengler.DieudonneDwork.rIntegralRatSubring p) = 0 := by
      ext
      exact hcoeff0
    rw [hsubzero]
    exact map_zero φ
  have hIpsSubst : PowerSeries.HasSubst Ips :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hInv0
  have hClambdaSubst : PowerSeries.HasSubst (PowerSeries.C lambdabar : PowerSeries A) := by
    change IsNilpotent
      (PowerSeries.constantCoeff (PowerSeries.C lambdabar : PowerSeries A))
    rw [PowerSeries.constantCoeff_C]
    exact ⟨N + 1, hlambdaNil⟩
  have hseries :
      PowerSeries.subst Ips Eps = 1 + (PowerSeries.X : PowerSeries A) := by
    simpa [Eps, Ips, hE, hInv, FormalDwork.expSeries, φ]
      using FormalDwork.expSeries_mapTo_subst_inverse (p := p) φ
  have hcomp :
      PowerSeries.subst (PowerSeries.C gammabar) Eps =
        PowerSeries.C (1 + lambdabar) := by
    calc
      PowerSeries.subst (PowerSeries.C gammabar) Eps
          = PowerSeries.subst (PowerSeries.subst (PowerSeries.C lambdabar) Ips) Eps := by
              rw [hSubInv]
      _ = PowerSeries.subst (PowerSeries.C lambdabar) (PowerSeries.subst Ips Eps) := by
              rw [← PowerSeries.subst_comp_subst_apply hIpsSubst hClambdaSubst Eps]
      _ = PowerSeries.subst (PowerSeries.C lambdabar) (1 + (PowerSeries.X : PowerSeries A)) := by
              rw [hseries]
      _ = PowerSeries.C (1 + lambdabar) := by
              have hone :
                  PowerSeries.subst (PowerSeries.C lambdabar) (1 : PowerSeries A) = 1 := by
                simpa using
                  (PowerSeries.subst_C
                    (a := (PowerSeries.C lambdabar : PowerSeries A)) (r := (1 : A)))
              rw [PowerSeries.subst_add hClambdaSubst,
                PowerSeries.subst_X hClambdaSubst, hone]
              simp
  have hEval :
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) gammabar =
        1 + lambdabar := by
    have hsubst :=
      Furtwaengler.powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero
        gammabar N hgammaNil Eps
    apply PowerSeries.C_injective
    rw [← hsubst, hcomp]
  calc
    (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (AdicCompletion.evalₐ (lambdaIdeal p K) (N + 1) (dworkParameter p K))
        = 1 + lambdabar := by
            simpa [gammabar] using hEval
    _ = Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (valuedCyclotomicZetaInteger p K) := by
            simp [lambdabar, q, valuedCyclotomicZetaInteger_eq_one_add_lambda]

/-- The finite Artin-Hasse exponential approximants at the Dwork parameter
approximants. -/
def dworkParameterExpApprox (N : ℕ) : ValuedIntegerRing p K :=
  (PowerSeries.trunc N (integralExpSeries p K)).eval₂
    (RingHom.id (ValuedIntegerRing p K)) (dworkParameterApprox p K N)

theorem quotient_mk_dworkParameterExpApprox_eq_trunc_eval (N : ℕ) :
    let A : Type _ := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N
    let φ : ValuedIntegerRing p K →+* A :=
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
    let Eps : PowerSeries A := PowerSeries.map φ (integralExpSeries p K)
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
        (dworkParameterExpApprox p K N) =
      (PowerSeries.trunc N Eps).eval₂ (RingHom.id A)
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
          (dworkParameterApprox p K N)) := by
  classical
  dsimp only [dworkParameterExpApprox]
  rw [PowerSeries.eval₂_trunc_eq_sum_range, map_sum,
    PowerSeries.eval₂_trunc_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simp [map_pow]

theorem quotient_mk_dworkParameterExpApprox_eq_zeta (N : ℕ) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
        (dworkParameterExpApprox p K N) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
        (valuedCyclotomicZetaInteger p K) := by
  cases N with
  | zero =>
      apply Ideal.Quotient.eq.mpr
      simp
  | succ N =>
      calc
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
            (dworkParameterExpApprox p K (N + 1))
            =
          (PowerSeries.trunc (N + 1)
              (PowerSeries.map
                (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
                (integralExpSeries p K))).eval₂
            (RingHom.id
              (ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)))
            (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
              (dworkParameterApprox p K (N + 1))) :=
              quotient_mk_dworkParameterExpApprox_eq_trunc_eval
                (p := p) (K := K) (N + 1)
        _ = Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
            (valuedCyclotomicZetaInteger p K) := by
              simpa [dworkParameter_evalₐ] using
                dworkParameter_eval_exp_mod (p := p) (K := K) N

@[simp]
theorem samePrimeFiniteArtinHasseExp_dworkParameterApprox
    (N : ℕ) :
    samePrimeFiniteArtinHasseExp (p := p) (K := K) N
        (dworkParameterApprox p K (N + 1)) =
      dworkParameterExpApprox p K (N + 1) := by
  rfl

theorem quotient_mk_samePrimeFiniteArtinHasseExpCoord_dworkParameterApprox_eq_lambda
    (N : ℕ) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N
          (dworkParameterApprox p K (N + 1))) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (valuedCyclotomicLambdaInteger p K) := by
  rw [samePrimeFiniteArtinHasseExpCoord, map_sub,
    samePrimeFiniteArtinHasseExp_dworkParameterApprox,
    quotient_mk_dworkParameterExpApprox_eq_zeta]
  simp [valuedCyclotomicZetaInteger_eq_one_add_lambda]

theorem samePrimeFiniteArtinHasseExpCoord_dworkParameterApprox_sub_lambda_mem
    (N : ℕ) :
    samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N
        (dworkParameterApprox p K (N + 1)) -
      valuedCyclotomicLambdaInteger p K ∈
        (lambdaIdeal p K) ^ (N + 1) :=
  Ideal.Quotient.eq.mp
    (quotient_mk_samePrimeFiniteArtinHasseExpCoord_dworkParameterApprox_eq_lambda
      (p := p) (K := K) N)

theorem samePrimeFiniteLog_finiteArtinHasseExpCoord_dworkParameterApprox_eq_lambda
    (N : ℕ) :
    samePrimeFiniteLog (p := p) (K := K) N
        (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N
          (dworkParameterApprox p K (N + 1)))
        (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal
          (p := p) (K := K) N
          (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1))) =
      samePrimeFiniteLog (p := p) (K := K) N
        (valuedCyclotomicLambdaInteger p K)
        (valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K)) :=
  samePrimeFiniteLog_eq_of_sub_mem (p := p) (K := K)
    (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal
      (p := p) (K := K) N
      (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1)))
    (valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K))
    (samePrimeFiniteArtinHasseExpCoord_dworkParameterApprox_sub_lambda_mem
      (p := p) (K := K) N)

theorem dworkParameterFiniteArtinHasseLog_eq_samePrimeFiniteLog_lambda
    (N : ℕ) :
    dworkParameterFiniteArtinHasseLog (p := p) (K := K) N =
      samePrimeFiniteLog (p := p) (K := K) N
        (valuedCyclotomicLambdaInteger p K)
        (valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K)) := by
  calc
    dworkParameterFiniteArtinHasseLog (p := p) (K := K) N =
        samePrimeFiniteArtinHasseLog (p := p) (K := K) N
          (dworkParameterApprox p K (N + 1))
          (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1)) := rfl
    _ =
        samePrimeFiniteLog (p := p) (K := K) N
          (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N
            (dworkParameterApprox p K (N + 1)))
          (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal
            (p := p) (K := K) N
            (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1))) :=
        (samePrimeFiniteLog_finiteArtinHasseExpCoord_eq_finiteArtinHasseLog
          (p := p) (K := K) N
          (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1))).symm
    _ =
        samePrimeFiniteLog (p := p) (K := K) N
          (valuedCyclotomicLambdaInteger p K)
          (valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K)) :=
        samePrimeFiniteLog_finiteArtinHasseExpCoord_dworkParameterApprox_eq_lambda
          (p := p) (K := K) N

theorem dworkParameterFiniteArtinHasseLog_p_nsmul_eq_zero (N : ℕ) :
    p • dworkParameterFiniteArtinHasseLog (p := p) (K := K) N = 0 := by
  rw [dworkParameterFiniteArtinHasseLog_eq_samePrimeFiniteLog_lambda
    (p := p) (K := K) N]
  exact samePrimeFiniteLog_lambda_p_nsmul_eq_zero (p := p) (K := K) N

theorem dworkParameterFiniteArtinHasseLog_natCast_p_mul_eq_zero (N : ℕ) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) (p : ValuedIntegerRing p K) *
        dworkParameterFiniteArtinHasseLog (p := p) (K := K) N = 0 := by
  rw [dworkParameterFiniteArtinHasseLog_eq_samePrimeFiniteLog_lambda
    (p := p) (K := K) N]
  exact samePrimeFiniteLog_lambda_natCast_p_mul_eq_zero (p := p) (K := K) N

theorem quotientNatCastInv_factorPow {M N m : ℕ} (hMN : M ≤ N)
    (hm : Nat.Coprime m p) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (quotientNatCastInv (p := p) (K := K) N m hm) =
      quotientNatCastInv (p := p) (K := K) M m hm := by
  symm
  refine quotientNatCastInv_eq_of_mul_right_eq_one
    (p := p) (K := K) (N := M) (m := m) hm ?_
  have hspec :=
    congrArg
      (Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN))
      (quotientNatCastInv_spec_right (p := p) (K := K) N m hm)
  simpa [Ideal.Quotient.factorPow] using hspec

theorem samePrimeNatDivEval_factorPow {M N n s : ℕ} (hMN : M ≤ N)
    (hn : n ≠ 0) {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s)) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (samePrimeNatDivEval (p := p) (K := K) N n s hn z hz) =
      samePrimeNatDivEval (p := p) (K := K) M n s hn z hz := by
  rw [samePrimeNatDivEval, samePrimeNatDivEval, map_mul,
    quotientNatCastInv_factorPow (p := p) (K := K) hMN]
  rfl

theorem samePrimeFiniteLogTermCore_factorPow {M N n : ℕ} (hMN : M ≤ N)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (samePrimeFiniteLogTermCore (p := p) (K := K) N n x hx) =
      samePrimeFiniteLogTermCore (p := p) (K := K) M n x hx := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [samePrimeFiniteLogTermCore_eq_samePrimeNatDivEval (p := p) (K := K) hn hx,
    samePrimeFiniteLogTermCore_eq_samePrimeNatDivEval (p := p) (K := K) hn hx]
  exact samePrimeNatDivEval_factorPow (p := p) (K := K) hMN hn _

theorem samePrimeFiniteLogTerm_factorPow {M N n : ℕ} (hMN : M ≤ N)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (samePrimeFiniteLogTerm (p := p) (K := K) N n x hx) =
      samePrimeFiniteLogTerm (p := p) (K := K) M n x hx := by
  rw [samePrimeFiniteLogTerm, samePrimeFiniteLogTerm, map_mul, map_pow,
    samePrimeFiniteLogTermCore_factorPow (p := p) (K := K) hMN hx]
  rfl

theorem samePrimeFiniteLog_factorPow {M N : ℕ} (hMN : M ≤ N)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (samePrimeFiniteLog (p := p) (K := K) N x hx) =
      samePrimeFiniteLog (p := p) (K := K) M x hx := by
  classical
  let cutoffM : ℕ := samePrimeFiniteLogCutoff (p := p) M
  let cutoffN : ℕ := samePrimeFiniteLogCutoff (p := p) N
  let termN : ℕ → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (M + 1) := fun n =>
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
      (samePrimeFiniteLogTerm (p := p) (K := K) N n x hx)
  let termM : ℕ → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (M + 1) := fun n =>
    samePrimeFiniteLogTerm (p := p) (K := K) M n x hx
  have hcut : cutoffM ≤ cutoffN := by
    dsimp [cutoffM, cutoffN, samePrimeFiniteLogCutoff]
    exact Nat.mul_le_mul_left p (Nat.succ_le_succ hMN)
  have hmap :
      Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
          (samePrimeFiniteLog (p := p) (K := K) N x hx) =
        ∑ n ∈ Finset.range cutoffN, termN n := by
    rw [samePrimeFiniteLog, map_sum]
  have htail :
      ∀ n ∈ Finset.range cutoffN, n ∉ Finset.range cutoffM → termN n = 0 := by
    intro n _hnN hnM
    have hMn : cutoffM ≤ n := Nat.le_of_not_gt (by simpa [cutoffM] using hnM)
    change Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (samePrimeFiniteLogTerm (p := p) (K := K) N n x hx) = 0
    rw [samePrimeFiniteLogTerm_factorPow (p := p) (K := K) hMN hx]
    exact samePrimeFiniteLogTerm_eq_zero_of_cutoff_le (p := p) (K := K) hMn hx
  have hrestrict :
      ∑ n ∈ Finset.range cutoffN, termN n =
        ∑ n ∈ Finset.range cutoffM, termN n :=
    (Finset.sum_subset (Finset.range_mono hcut) htail).symm
  have hterms :
      ∑ n ∈ Finset.range cutoffM, termN n =
        ∑ n ∈ Finset.range cutoffM, termM n := by
    refine Finset.sum_congr rfl ?_
    intro n _hn
    exact samePrimeFiniteLogTerm_factorPow (p := p) (K := K) hMN hx
  calc
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (samePrimeFiniteLog (p := p) (K := K) N x hx)
        = ∑ n ∈ Finset.range cutoffN, termN n := hmap
    _ = ∑ n ∈ Finset.range cutoffM, termN n := hrestrict
    _ = ∑ n ∈ Finset.range cutoffM, termM n := hterms
    _ = samePrimeFiniteLog (p := p) (K := K) M x hx := by
        simp [samePrimeFiniteLog, cutoffM, termM]

theorem dworkParameterFiniteArtinHasseLog_factorPow {M N : ℕ} (hMN : M ≤ N) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (dworkParameterFiniteArtinHasseLog (p := p) (K := K) N) =
      dworkParameterFiniteArtinHasseLog (p := p) (K := K) M := by
  rw [dworkParameterFiniteArtinHasseLog_eq_samePrimeFiniteLog_lambda
      (p := p) (K := K) N,
    dworkParameterFiniteArtinHasseLog_eq_samePrimeFiniteLog_lambda
      (p := p) (K := K) M]
  exact samePrimeFiniteLog_factorPow (p := p) (K := K) hMN
    (valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K))

noncomputable def dworkParameterFiniteArtinHasseLogCoord (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N :=
  match N with
  | 0 => 0
  | N + 1 => dworkParameterFiniteArtinHasseLog (p := p) (K := K) N

@[simp]
theorem dworkParameterFiniteArtinHasseLogCoord_zero :
    dworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) 0 = 0 := rfl

@[simp]
theorem dworkParameterFiniteArtinHasseLogCoord_succ (N : ℕ) :
    dworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) (N + 1) =
      dworkParameterFiniteArtinHasseLog (p := p) (K := K) N := rfl

theorem dworkParameterFiniteArtinHasseLogCoord_factorPow
    {M N : ℕ} (hMN : M ≤ N) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) hMN
        (dworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) N) =
      dworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) M := by
  cases M with
  | zero =>
      exact quotient_pow_zero_eq_zero (p := p) (K := K)
        (lambdaIdeal p K)
        (Ideal.Quotient.factorPow (lambdaIdeal p K) hMN
          (dworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) N))
  | succ M =>
      cases N with
      | zero =>
          exact False.elim (Nat.not_succ_le_zero M hMN)
      | succ N =>
          have hMN' : M ≤ N := Nat.succ_le_succ_iff.mp hMN
          simpa using
            dworkParameterFiniteArtinHasseLog_factorPow (p := p) (K := K) hMN'

/-- The completed Artin--Hasse logarithm of the Dwork parameter, assembled
from its compatible finite quotient coordinates. -/
noncomputable def artinHasseLog_eval_dworkParameter :
    DworkCompleteIntegerRing p K :=
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  ⟨fun N =>
      (Ideal.quotientEquivAlgOfEq R (by
        ext y
        simp : (I ^ N • ⊤ : Ideal R) = I ^ N)).symm
        (dworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) N),
    by
      intro M N hMN
      let hEqM : (I ^ M • ⊤ : Ideal R) = I ^ M := by
        ext y
        simp
      let hEqN : (I ^ N • ⊤ : Ideal R) = I ^ N := by
        ext y
        simp
      apply (Ideal.quotientEquivAlgOfEq R hEqM).injective
      calc
        (Ideal.quotientEquivAlgOfEq R hEqM)
            (AdicCompletion.transitionMap I R hMN
              ((Ideal.quotientEquivAlgOfEq R hEqN).symm
                (dworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) N)))
            =
          Ideal.Quotient.factorPow I hMN
            (dworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) N) := by
            refine Quotient.inductionOn'
              (dworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) N) ?_
            intro r
            rfl
        _ = dworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) M :=
            dworkParameterFiniteArtinHasseLogCoord_factorPow
              (p := p) (K := K) hMN
        _ = (Ideal.quotientEquivAlgOfEq R hEqM)
            ((Ideal.quotientEquivAlgOfEq R hEqM).symm
              (dworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) M)) := by
            refine Quotient.inductionOn'
              (dworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) M) ?_
            intro r
            rfl
      ⟩

@[simp]
theorem artinHasseLog_eval_dworkParameter_evalₐ (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N
        (artinHasseLog_eval_dworkParameter p K) =
      dworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) N := by
  unfold artinHasseLog_eval_dworkParameter
  let hEq :
      ((lambdaIdeal p K) ^ N • ⊤ : Ideal (ValuedIntegerRing p K)) =
        (lambdaIdeal p K) ^ N := by
    ext y
    simp
  change
    (Ideal.quotientEquivAlgOfEq (ValuedIntegerRing p K) hEq)
      ((Ideal.quotientEquivAlgOfEq (ValuedIntegerRing p K) hEq).symm
        (dworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) N)) =
      dworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) N
  refine Quotient.inductionOn'
    (dworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) N) ?_
  intro r
  rfl

@[simp]
theorem artinHasseLog_eval_dworkParameter_evalₐ_succ (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) (N + 1)
        (artinHasseLog_eval_dworkParameter p K) =
      dworkParameterFiniteArtinHasseLog (p := p) (K := K) N := by
  simp

theorem artinHasseLog_eval_dworkParameter_eq_zero :
    artinHasseLog_eval_dworkParameter p K = 0 := by
  apply dworkComplete_eq_zero_of_evalₐ_natCast_p_nsmul_eq_zero
    (p := p) (K := K)
  intro N
  cases N with
  | zero =>
      simp
  | succ N =>
      rw [artinHasseLog_eval_dworkParameter_evalₐ_succ]
      exact dworkParameterFiniteArtinHasseLog_p_nsmul_eq_zero (p := p) (K := K) N

theorem dworkParameterFiniteArtinHasseLog_eq_zero (N : ℕ) :
    dworkParameterFiniteArtinHasseLog (p := p) (K := K) N = 0 := by
  have h :=
    congrArg (AdicCompletion.evalₐ (lambdaIdeal p K) (N + 1))
      (artinHasseLog_eval_dworkParameter_eq_zero (p := p) (K := K))
  simpa using h


end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular

end
