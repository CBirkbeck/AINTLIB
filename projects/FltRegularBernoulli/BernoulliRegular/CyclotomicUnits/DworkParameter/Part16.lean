module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.Part15
public import BernoulliRegular.Characters

@[expose] public section

noncomputable section

open scoped NumberField Topology

namespace BernoulliRegular
namespace CyclotomicUnits
namespace PadicLogSetup
namespace DworkParameter

open Furtwaengler.KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- First-order expansion of `(1 + x)^k` modulo one higher ideal power. -/
theorem one_add_pow_sub_one_sub_natCast_mul_mem_pow_succ
    {R : Type*} [CommRing R] (I : Ideal R)
    {n : ℕ} (hn : 1 ≤ n) {x : R} (hx : x ∈ I ^ n) (k : ℕ) :
    (1 + x) ^ k - 1 - (k : R) * x ∈ I ^ (n + 1) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hleft :
          ((1 + x) ^ k - 1 - (k : R) * x) * (1 + x) ∈ I ^ (n + 1) :=
        Ideal.mul_mem_right (1 + x) (I ^ (n + 1)) ih
      have hxx : x * x ∈ I ^ (n + 1) := by
        have hx2 : x * x ∈ I ^ n * I ^ n := Ideal.mul_mem_mul hx hx
        have hx2' : x * x ∈ I ^ (n + n) := by
          simpa [pow_add] using hx2
        exact Ideal.pow_le_pow_right (by omega : n + 1 ≤ n + n) hx2'
      have hright : (k : R) * (x * x) ∈ I ^ (n + 1) :=
        Ideal.mul_mem_left (I ^ (n + 1)) (k : R) hxx
      have hsum :
          ((1 + x) ^ k - 1 - (k : R) * x) * (1 + x) +
              (k : R) * (x * x) ∈ I ^ (n + 1) :=
        Ideal.add_mem _ hleft hright
      convert hsum using 1
      rw [pow_succ, Nat.cast_succ]
      ring

/-- The p-adic integers indexed by a bundled prime, with the `Fact` instance
supplied by the bundle. -/
abbrev padicIntOfPrime (q : Nat.Primes) : Type :=
  @PadicInt q.1 ⟨q.2⟩

/-- The concrete `ℤ_p` model used on the Dwork side is the integer subring of
the rational `(p)`-adic completion.  Mathlib's `ℤ_[p]` is canonically
equivalent to it. -/
noncomputable def padicIntToRationalPadicIntegerRingEquiv :
    ℤ_[lambdaPadicPrime p] ≃+* RationalPadicIntegerRing p := by
  refine (RingEquiv.cast
      (R := padicIntOfPrime)
      (primesEquiv_lambdaRationalHeightOneSpectrum (p := p)).symm).trans ?_
  let R₀ : Type := RationalPadicIntegerRing p
  letI : Algebra ℤ R₀ := Ring.toIntAlgebra R₀
  let e : R₀ ≃A[ℤ]
      padicIntOfPrime
        (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)
          (lambdaRationalHeightOneSpectrum p)) :=
    Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv
      (lambdaRationalHeightOneSpectrum p)
  exact
    { toFun := fun x ↦ e.symm x
      invFun := fun x ↦ e x
      left_inv := fun x ↦ e.apply_symm_apply x
      right_inv := fun x ↦ e.symm_apply_apply x
      map_mul' := fun x y ↦ e.symm.map_mul x y
      map_add' := fun x y ↦ e.symm.map_add x y }

/-- The Teichmüller lift in the rational completed integer coefficient ring
selected for the Dwork parameter. -/
noncomputable def rationalPadicTeichmuller (a : ZMod p) :
    RationalPadicIntegerRing p :=
  padicIntToRationalPadicIntegerRingEquiv (p := p)
    (BernoulliRegular.teichmuller p a)

@[simp]
theorem rationalPadicTeichmuller_zero :
    rationalPadicTeichmuller p 0 = 0 := by
  simp [rationalPadicTeichmuller]

@[simp]
theorem rationalPadicTeichmuller_one :
    rationalPadicTeichmuller p 1 = 1 := by
  simp [rationalPadicTeichmuller]

@[simp]
theorem rationalPadicTeichmuller_mul (a b : ZMod p) :
    rationalPadicTeichmuller p (a * b) =
      rationalPadicTeichmuller p a * rationalPadicTeichmuller p b := by
  simp [rationalPadicTeichmuller]

theorem rationalPadicTeichmuller_pow_sub_one
    {a : ZMod p} (ha : a ≠ 0) :
    rationalPadicTeichmuller p a ^ (p - 1) = 1 := by
  change
    padicIntToRationalPadicIntegerRingEquiv (p := p)
        (BernoulliRegular.teichmuller p a) ^ (p - 1) = 1
  rw [← map_pow, BernoulliRegular.teichmuller_pow_sub_one (p := p) ha, map_one]

theorem rationalPadicTeichmuller_pow_prime (a : ZMod p) :
    rationalPadicTeichmuller p a ^ p =
      rationalPadicTeichmuller p a := by
  change
    padicIntToRationalPadicIntegerRingEquiv (p := p)
        (BernoulliRegular.teichmuller p a) ^ p =
      padicIntToRationalPadicIntegerRingEquiv (p := p)
        (BernoulliRegular.teichmuller p a)
  rw [← map_pow, BernoulliRegular.teichmuller_pow_card (p := p) a]

theorem rationalPadicTeichmuller_isUnit
    {a : ZMod p} (ha : a ≠ 0) :
    IsUnit (rationalPadicTeichmuller p a) :=
  (BernoulliRegular.isUnit_teichmuller (p := p) ha).map
    (padicIntToRationalPadicIntegerRingEquiv (p := p)).toRingHom

@[simp]
theorem rationalPadicTeichmuller_eq_zero_iff {a : ZMod p} :
    rationalPadicTeichmuller p a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hpre :
        BernoulliRegular.teichmuller p a = 0 := by
      have h' := congrArg
        (padicIntToRationalPadicIntegerRingEquiv (p := p)).symm h
      simpa [rationalPadicTeichmuller] using h'
    simpa using (BernoulliRegular.teichmuller_eq_zero_iff (p := p)).mp hpre
  · intro h
    simp [h]

/-- The residue map on the rational completed integer coefficient ring,
transported from mathlib's `PadicInt.toZMod`. -/
noncomputable def rationalPadicIntegerToZMod :
    RationalPadicIntegerRing p →+* ZMod p :=
  (PadicInt.toZMod (p := p)).comp
    (padicIntToRationalPadicIntegerRingEquiv (p := p)).symm.toRingHom

@[simp]
theorem rationalPadicIntegerToZMod_teichmuller (a : ZMod p) :
    rationalPadicIntegerToZMod p (rationalPadicTeichmuller p a) = a := by
  change PadicInt.toZMod
      ((padicIntToRationalPadicIntegerRingEquiv (p := p)).symm
        ((padicIntToRationalPadicIntegerRingEquiv (p := p))
          (BernoulliRegular.teichmuller p a))) = a
  rw [RingEquiv.symm_apply_apply]
  exact BernoulliRegular.toZMod_teichmuller (p := p) a

@[simp]
theorem rationalPadicIntegerToZMod_natCast (n : ℕ) :
    rationalPadicIntegerToZMod p (n : RationalPadicIntegerRing p) =
      (n : ZMod p) := by
  change PadicInt.toZMod
      ((padicIntToRationalPadicIntegerRingEquiv (p := p)).symm
        (n : RationalPadicIntegerRing p)) = (n : ZMod p)
  have hmap :
      (padicIntToRationalPadicIntegerRingEquiv (p := p)) (n : ℤ_[p]) =
        (n : RationalPadicIntegerRing p) := by
    simp [padicIntToRationalPadicIntegerRingEquiv]
  rw [← hmap, RingEquiv.symm_apply_apply]
  simp

theorem rationalPadicIntegerToZMod_eq_zero_iff_mem_primeIdeal
    (x : RationalPadicIntegerRing p) :
    rationalPadicIntegerToZMod p x = 0 ↔ x ∈ rationalPadicPrimeIdeal p := by
  let e := padicIntToRationalPadicIntegerRingEquiv (p := p)
  change PadicInt.toZMod (e.symm x) = 0 ↔
    x ∈ rationalPadicPrimeIdeal p
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
  change e.symm x ∈ IsLocalRing.maximalIdeal ℤ_[p] ↔
    x ∈ rationalPadicPrimeIdeal p
  rw [rationalPadicPrimeIdeal_eq_maximalIdeal (p := p)]
  constructor
  · intro hx
    rw [IsLocalRing.mem_maximalIdeal] at hx
    rw [IsLocalRing.mem_maximalIdeal]
    intro hxunit
    have hpre : IsUnit (e.symm x) := by
      simpa using hxunit.map e.symm.toRingHom
    exact hx hpre
  · intro hx
    rw [IsLocalRing.mem_maximalIdeal] at hx ⊢
    intro hunit
    have hxunit : IsUnit x := by
      simpa using hunit.map e.toRingHom
    exact hx hxunit

theorem rationalPadicTeichmuller_sub_natCast_val_mem_primeIdeal
    (a : ZMod p) :
    rationalPadicTeichmuller p a - (a.val : RationalPadicIntegerRing p) ∈
      rationalPadicPrimeIdeal p := by
  rw [← rationalPadicIntegerToZMod_eq_zero_iff_mem_primeIdeal (p := p)]
  rw [map_sub, rationalPadicIntegerToZMod_teichmuller,
    rationalPadicIntegerToZMod_natCast]
  exact sub_eq_zero.mpr (ZMod.natCast_zmod_val a).symm

/-- The scaled Dwork parameter `omega(a) * varpi`.  The coefficient is the
Teichmüller lift in the rational completed integer ring. -/
noncomputable def scaledDworkParameter (a : ZMod p) :
    DworkCompleteIntegerRing p K :=
  algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K)
      (rationalPadicTeichmuller p a) *
    dworkParameter p K

@[simp]
theorem scaledDworkParameter_zero :
    scaledDworkParameter p K 0 = 0 := by
  simp [scaledDworkParameter]

@[simp]
theorem scaledDworkParameter_one :
    scaledDworkParameter p K 1 = dworkParameter p K := by
  simp [scaledDworkParameter]

theorem scaledDworkParameter_evalₐ_one (a : ZMod p) :
    AdicCompletion.evalₐ (lambdaIdeal p K) 1
        (scaledDworkParameter p K a) = 0 := by
  rw [scaledDworkParameter, map_mul, dworkParameter_evalₐ_one, mul_zero]

set_option maxHeartbeats 800000 in
-- This congruence transports ideals through the rational and Dwork completions;
-- the higher limit keeps the nested completion abbreviations from timing out.
theorem scaledDworkParameter_sub_natCast_mul_lambda_mem_sq
    (a : ZMod p) :
    scaledDworkParameter p K a -
        algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K)
          (a.val : RationalPadicIntegerRing p) *
          dworkCompleteLambda p K ∈
      (dworkCompleteLambdaIdeal p K) ^ 2 := by
  let S : Type _ := DworkCompleteIntegerRing p K
  let I : Ideal S := dworkCompleteLambdaIdeal p K
  let omegaR : RationalPadicIntegerRing p := rationalPadicTeichmuller p a
  let avalR : RationalPadicIntegerRing p := (a.val : RationalPadicIntegerRing p)
  let omegaS : S := algebraMap (RationalPadicIntegerRing p) S omegaR
  let avalS : S := algebraMap (RationalPadicIntegerRing p) S avalR
  let varpi : S := dworkParameter p K
  let lambda : S := dworkCompleteLambda p K
  have hvarpi :
      varpi - lambda ∈ I ^ 2 := by
    simpa [varpi, lambda, I] using
      dworkParameter_sub_dworkCompleteLambda_mem_sq (p := p) (K := K)
  have hterm1 : omegaS * (varpi - lambda) ∈ I ^ 2 :=
    (I ^ 2).mul_mem_left omegaS hvarpi
  have hcoeffPrime :
      omegaR - avalR ∈ rationalPadicPrimeIdeal p := by
    simpa [omegaR, avalR] using
      rationalPadicTeichmuller_sub_natCast_val_mem_primeIdeal (p := p) a
  have hcoeffParamPow :
      algebraMap (RationalPadicIntegerRing p) S (omegaR - avalR) ∈
        (dworkParameterIdeal p K) ^ (1 * (p - 1)) :=
    algebraMap_mem_dworkParameterIdeal_pow_mul_pred_of_mem_rationalPadicPrimeIdeal_pow
        (p := p) (K := K) (q := 1)
        (by simpa [pow_one] using hcoeffPrime)
  have hp_pred_pos : 0 < p - 1 :=
    Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
  have hcoeffParam :
      algebraMap (RationalPadicIntegerRing p) S (omegaR - avalR) ∈
        dworkParameterIdeal p K := by
    have htmp :
        algebraMap (RationalPadicIntegerRing p) S (omegaR - avalR) ∈
          (dworkParameterIdeal p K) ^ (p - 1) := by
      simpa [one_mul] using hcoeffParamPow
    exact Ideal.pow_le_self (Nat.ne_of_gt hp_pred_pos) htmp
  have hcoeffI :
      algebraMap (RationalPadicIntegerRing p) S (omegaR - avalR) ∈ I := by
    simpa [I, dworkParameterIdeal_eq_dworkCompleteLambdaIdeal (p := p) (K := K)]
      using hcoeffParam
  have hlambdaI : lambda ∈ I := by
    change dworkCompleteLambda p K ∈ dworkCompleteLambdaIdeal p K
    rw [dworkCompleteLambdaIdeal_eq_span (p := p) (K := K)]
    exact Ideal.mem_span_singleton_self lambda
  have hterm2 :
      algebraMap (RationalPadicIntegerRing p) S (omegaR - avalR) *
          lambda ∈ I ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul hcoeffI hlambdaI
  have hdecomp :
      scaledDworkParameter p K a - avalS * lambda =
        omegaS * (varpi - lambda) +
          algebraMap (RationalPadicIntegerRing p) S (omegaR - avalR) * lambda := by
    change
      algebraMap (RationalPadicIntegerRing p) S omegaR * varpi -
          algebraMap (RationalPadicIntegerRing p) S avalR * lambda =
        algebraMap (RationalPadicIntegerRing p) S omegaR * (varpi - lambda) +
          algebraMap (RationalPadicIntegerRing p) S (omegaR - avalR) * lambda
    rw [map_sub]
    rw [mul_sub, sub_mul]
    abel
  rw [hdecomp]
  exact (I ^ 2).add_mem hterm1 hterm2

theorem valuedCyclotomicZetaInteger_pow_sub_one_sub_natCast_mul_lambda_mem_sq
    (a : ZMod p) :
    valuedCyclotomicZetaInteger p K ^ a.val - 1 -
        (a.val : ValuedIntegerRing p K) *
          valuedCyclotomicLambdaInteger p K ∈
      (lambdaIdeal p K) ^ 2 := by
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let lam : R := valuedCyclotomicLambdaInteger p K
  have hlam : lam ∈ I ^ 1 := by
    simp [I, lam, pow_one,
      valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K)]
  have h :=
    one_add_pow_sub_one_sub_natCast_mul_mem_pow_succ
      (I := I) (n := 1) (by decide : 1 ≤ 1) (x := lam) hlam a.val
  simpa [R, I, lam, valuedCyclotomicZetaInteger_eq_one_add_lambda
    (p := p) (K := K)] using h

theorem algebraMap_rationalPadicInteger_natCast_dworkComplete (n : ℕ) :
    algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K)
        (n : RationalPadicIntegerRing p) =
      algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)
        (n : ValuedIntegerRing p K) := by
  rw [algebraMap_rationalPadicInteger_dworkComplete_apply]
  congr 1
  apply Subtype.ext
  simp

theorem samePrimeFiniteLog_higher_term_order
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    m + 1 ≤ n * m - n.factorization p * (p - 1) := by
  let den : ℕ := n.factorization p * (p - 1)
  have hn_ne : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hden_le_pred : den ≤ n - 1 := by
    simpa [den, Nat.mul_comm] using
      Nat.factorization_mul_pred_le_pred (ell := p) (n := n)
        (Fact.out : Nat.Prime p) hn_ne
  have htarget : m + 1 + den ≤ n * m := by
    have hZden' : (den : ℤ) ≤ (n - 1 : ℕ) := by
      exact_mod_cast hden_le_pred
    have hZden : (den : ℤ) ≤ (n : ℤ) - 1 := by
      have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
      have hsub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
        omega
      simpa [hsub] using hZden'
    have hZm : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
    have hZn : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    have hnonneg : (0 : ℤ) ≤ ((n : ℤ) - 2) * ((m : ℤ) - 1) :=
      mul_nonneg (by omega) (by omega)
    have htargetZ : (m : ℤ) + 1 + den ≤ (n : ℤ) * (m : ℤ) := by
      nlinarith
    exact_mod_cast htargetZ
  exact Nat.le_sub_of_add_le htarget

theorem quotientNatCastInv_one' (N : ℕ) :
    quotientNatCastInv (p := p) (K := K) N 1 (Nat.coprime_one_left p) = 1 := by
  refine quotientNatCastInv_eq_of_mul_right_eq_one
    (p := p) (K := K) (N := N) (m := 1) (hm := Nat.coprime_one_left p) ?_
  simp

theorem samePrimeFiniteLogTerm_one_eq_mk
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLogTerm (p := p) (K := K) N 1 x hx =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) x := by
  rw [samePrimeFiniteLogTerm, samePrimeFiniteLogTermCore_eq_samePrimeNatDivEval
    (p := p) (K := K) (by decide : (1 : ℕ) ≠ 0) hx]
  have hz :
      x ^ 1 ∈
        (lambdaIdeal p K) ^
          ((1 : ℕ).factorization p * (p - 1) + samePrimeFiniteLogTermOrder (p := p) 1) := by
    have horder : samePrimeFiniteLogTermOrder (p := p) 1 = 1 := by
      simp [samePrimeFiniteLogTermOrder]
    simpa [factorization_mul_pred_add_samePrimeFiniteLogTermOrder
        (p := p) (by decide : (1 : ℕ) ≠ 0), horder] using
      Ideal.pow_mem_pow hx 1
  rw [samePrimeNatDivEval_eq_of_spec (p := p) (K := K)
    (N := N) (n := 1) (s := samePrimeFiniteLogTermOrder (p := p) 1)
    (by decide : (1 : ℕ) ≠ 0)
    hz
    (y := x)]
  · simp [quotientNatCastInv_one' (p := p) (K := K)]
  · simp

theorem samePrimeFiniteLogTerm_eq_zero_of_mem_pow_of_two_le
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {x : ValuedIntegerRing p K} (hx : x ∈ (lambdaIdeal p K) ^ m) :
    samePrimeFiniteLogTerm (p := p) (K := K) m n x
        (Ideal.pow_le_self (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hm)) hx) =
      0 := by
  let s : ℕ := n * m - n.factorization p * (p - 1)
  have hn_ne : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hxI : x ∈ lambdaIdeal p K :=
    Ideal.pow_le_self (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hm)) hx
  have hxpow_s :
      x ^ n ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
    have hxpow : x ^ n ∈ ((lambdaIdeal p K) ^ m) ^ n := Ideal.pow_mem_pow hx n
    have hxpow_nm : x ^ n ∈ (lambdaIdeal p K) ^ (m * n) := by
      simpa [pow_mul] using hxpow
    have hden_le : n.factorization p * (p - 1) ≤ n * m := by
      have hle := Nat.factorization_mul_pred_le_pred
        (ell := p) (n := n) (Fact.out : Nat.Prime p) hn_ne
      have hn_pred_le_nm : n - 1 ≤ n * m :=
        (Nat.sub_le n 1).trans (Nat.le_mul_of_pos_right n
          (lt_of_lt_of_le (by decide : 0 < 2) hm))
      have hle' : n.factorization p * (p - 1) ≤ n - 1 := by
        simpa [Nat.mul_comm] using hle
      exact hle'.trans hn_pred_le_nm
    have hs : n.factorization p * (p - 1) + s = n * m := by
      dsimp [s]
      exact Nat.add_sub_of_le hden_le
    have hs' : n.factorization p * (p - 1) + s = m * n := by
      simpa [Nat.mul_comm] using hs
    simpa [hs'] using hxpow_nm
  have htermCore :
      samePrimeFiniteLogTermCore (p := p) (K := K) m n x hxI =
        samePrimeNatDivEval (p := p) (K := K) m n s hn_ne (x ^ n) hxpow_s := by
    rw [samePrimeFiniteLogTermCore_eq_samePrimeNatDivEvalAtDegree
      (p := p) (K := K) hn_ne hxI]
    exact samePrimeNatDivEvalAtDegree_eq_samePrimeNatDivEval
      (p := p) (K := K) hn_ne (Ideal.pow_mem_pow hxI n)
      (by
        have h := Nat.factorization_mul_pred_le_pred
          (ell := p) (n := n) (Fact.out : Nat.Prime p) hn_ne
        omega)
      hxpow_s
  rw [samePrimeFiniteLogTerm, htermCore]
  rw [samePrimeNatDivEval_eq_zero_of_succ_le (p := p) (K := K)
    hn_ne hxpow_s (samePrimeFiniteLog_higher_term_order (p := p) hm hn)]
  simp

theorem samePrimeFiniteLog_eq_mk_of_mem_pow_of_two_le
    {m : ℕ} (hm : 2 ≤ m)
    {x : ValuedIntegerRing p K} (hx : x ∈ (lambdaIdeal p K) ^ m) :
    samePrimeFiniteLog (p := p) (K := K) m x
        (Ideal.pow_le_self (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hm)) hx) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (m + 1)) x := by
  classical
  let hxI : x ∈ lambdaIdeal p K :=
    Ideal.pow_le_self (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hm)) hx
  unfold samePrimeFiniteLog
  rw [Finset.sum_eq_single 1]
  · exact samePrimeFiniteLogTerm_one_eq_mk (p := p) (K := K) m hxI
  · intro n hn_range hn_ne_one
    by_cases hn0 : n = 0
    · subst n
      simp
    have hn2 : 2 ≤ n := by omega
    exact samePrimeFiniteLogTerm_eq_zero_of_mem_pow_of_two_le
      (p := p) (K := K) hm hn2 hx
  · intro hnot
    exfalso
    have hcut : 1 < samePrimeFiniteLogCutoff (p := p) m := by
      calc
        1 < p := (Fact.out : Nat.Prime p).one_lt
        _ ≤ p * (m + 1) := Nat.le_mul_of_pos_right p (Nat.succ_pos m)
    exact hnot (by simpa [samePrimeFiniteLogCutoff] using hcut)

/-- Above the same-prime folded index `p`, every ordinary logarithm term has
lambda-order at least `p - 1`. -/
theorem pred_le_samePrimeFiniteLogTermOrder_of_prime_lt
    (hp_three : 3 ≤ p) {n : ℕ} (hn : p < n) :
    p - 1 ≤ samePrimeFiniteLogTermOrder (p := p) n := by
  let v : ℕ := n.factorization p
  have hn0 : n ≠ 0 := by omega
  by_cases hv0 : v = 0
  · have hle : p - 1 ≤ n := by omega
    simpa [samePrimeFiniteLogTermOrder, v, hv0] using hle
  by_cases hv1 : v = 1
  · have hvpos : 1 ≤ n.factorization p := by
      simp [v, hv1]
    have hpdvd : p ∣ n := by
      simpa [pow_one] using
        ((Fact.out : Nat.Prime p).pow_dvd_iff_le_factorization hn0).2 hvpos
    rcases hpdvd with ⟨k, hk⟩
    have hk_gt_one : 1 < k := by
      have hmul : p * 1 < p * k := by
        simpa [one_mul, hk] using hn
      exact Nat.lt_of_mul_lt_mul_left hmul
    have hk_two : 2 ≤ k := Nat.succ_le_of_lt hk_gt_one
    have hn_two_p : 2 * p ≤ n := by
      rw [hk]
      nlinarith [Nat.mul_le_mul_left p hk_two]
    have hle : p - 1 ≤ n - (p - 1) * n.factorization p := by
      rw [show n.factorization p = 1 by simpa [v] using hv1]
      omega
    simpa [samePrimeFiniteLogTermOrder] using hle
  · have hv_two : 2 ≤ n.factorization p := by
      have hvpos : 0 < v := Nat.pos_of_ne_zero hv0
      have hvne_one : v ≠ 1 := hv1
      omega
    have hp2_dvd : p ^ 2 ∣ n :=
      ((Fact.out : Nat.Prime p).pow_dvd_iff_le_factorization hn0).2 hv_two
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    have hp2_le : p ^ 2 ≤ n := Nat.le_of_dvd hn_pos hp2_dvd
    have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
    have hp_le_div : p ≤ n / p := by
      rw [Nat.le_div_iff_mul_le hp_pos]
      simpa [pow_two] using hp2_le
    have hden :=
      Nat.pred_mul_factorization_add_div_le (ell := p) (n := n)
        (Fact.out : Nat.Prime p)
    have hden' :
        n / p + (p - 1) * n.factorization p ≤ n := by
      simpa [add_comm] using hden
    have hdiv_le_sub :
        n / p ≤ n - (p - 1) * n.factorization p :=
      Nat.le_sub_of_add_le hden'
    have hle : p - 1 ≤ n - (p - 1) * n.factorization p :=
      (by omega : p - 1 ≤ n / p).trans hdiv_le_sub
    simpa [samePrimeFiniteLogTermOrder] using hle

/-- At precision `lambda^(p - 1)`, the ordinary logarithm terms after the
unique same-prime folded term `n = p` vanish. -/
theorem samePrimeFiniteLogTerm_pow_pred_eq_zero_of_prime_lt
    (hp_three : 3 ≤ p) {n : ℕ} (hn : p < n)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLogTerm (p := p) (K := K) (p - 2) n x hx = 0 := by
  rcases (Ideal.mem_map_iff_of_surjective
      (Ideal.Quotient.mk ((lambdaIdeal p K) ^ ((p - 2) + 1)))
      Ideal.Quotient.mk_surjective).1
      (samePrimeFiniteLogTerm_mem_map_lambdaIdeal_pow
        (p := p) (K := K) (by omega : n ≠ 0) hx) with
    ⟨y, hy, hyq⟩
  rw [← hyq, Ideal.Quotient.eq_zero_iff_mem]
  have horder :
      (p - 2) + 1 ≤ samePrimeFiniteLogTermOrder (p := p) n := by
    have hpred := pred_le_samePrimeFiniteLogTermOrder_of_prime_lt
      (p := p) hp_three hn
    omega
  exact Ideal.pow_le_pow_right horder hy

/-- Folded same-prime finite-log expansion at precision `lambda^(p - 1)`.

The finite logarithm is the ordinary unit-denominator part through `n = p - 1`
plus the single surviving same-prime term `n = p`.  The latter is the API-level
representative of `x^p / p`; its integral ramification-unit rewrite is a
separate step. -/
theorem samePrimeFiniteLog_eq_sum_Icc_add_p_term_pow_pred
    (hp_three : 3 ≤ p)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLog (p := p) (K := K) (p - 2) x hx =
      (∑ n ∈ Finset.Icc 1 (p - 1),
        samePrimeFiniteLogTerm (p := p) (K := K) (p - 2) n x hx) +
      samePrimeFiniteLogTerm (p := p) (K := K) (p - 2) p x hx := by
  classical
  let N : ℕ := p - 2
  let C : ℕ := samePrimeFiniteLogCutoff (p := p) N
  let f : ℕ → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    fun n ↦ samePrimeFiniteLogTerm (p := p) (K := K) N n x hx
  have hcut : p + 1 ≤ C := by
    have htwo : 2 ≤ N + 1 := by
      dsimp [N]
      omega
    have hp1_le_2p : p + 1 ≤ p * 2 := by
      omega
    exact hp1_le_2p.trans (by
      dsimp [C, samePrimeFiniteLogCutoff]
      exact Nat.mul_le_mul_left p htwo)
  have htail :
      ∀ n ∈ Finset.range C, n ∉ Finset.range (p + 1) → f n = 0 := by
    intro n _hnC hn_range
    have hp_lt_n : p < n := by
      have hnot : ¬ n < p + 1 := by
        simpa using hn_range
      omega
    exact samePrimeFiniteLogTerm_pow_pred_eq_zero_of_prime_lt
      (p := p) (K := K) hp_three hp_lt_n hx
  have hrestrict :
      (∑ n ∈ Finset.range C, f n) =
        ∑ n ∈ Finset.range (p + 1), f n :=
    (Finset.sum_subset (Finset.range_mono hcut) htail).symm
  have hrange :
      Finset.range (p + 1) =
        insert 0 (insert p (Finset.Icc 1 (p - 1))) := by
    ext n
    simp
    omega
  have h0not : 0 ∉ insert p (Finset.Icc 1 (p - 1)) := by
    simp
    omega
  have hpnot : p ∉ Finset.Icc 1 (p - 1) := by
    simp
    omega
  unfold samePrimeFiniteLog
  change (∑ n ∈ Finset.range C, f n) =
    (∑ n ∈ Finset.Icc 1 (p - 1), f n) + f p
  rw [hrestrict, hrange]
  rw [Finset.sum_insert h0not, Finset.sum_insert hpnot]
  simp [f, samePrimeFiniteLogTerm_zero, add_comm]

/-- The Teichmüller coefficient transported all the way to the lambda-valued
integer ring. -/
noncomputable def rationalPadicTeichmullerValued (a : ZMod p) :
    ValuedIntegerRing p K :=
  rationalPadicIntegerToValuedInteger (p := p) (K := K)
    (rationalPadicTeichmuller p a)

@[simp]
theorem rationalPadicTeichmullerValued_zero :
    rationalPadicTeichmullerValued p K 0 = 0 := by
  simp [rationalPadicTeichmullerValued]

@[simp]
theorem rationalPadicTeichmullerValued_one :
    rationalPadicTeichmullerValued p K 1 = 1 := by
  simp [rationalPadicTeichmullerValued]

@[simp]
theorem rationalPadicTeichmullerValued_mul (a b : ZMod p) :
    rationalPadicTeichmullerValued p K (a * b) =
      rationalPadicTeichmullerValued p K a *
        rationalPadicTeichmullerValued p K b := by
  simp [rationalPadicTeichmullerValued]

theorem rationalPadicTeichmullerValued_pow_prime (a : ZMod p) :
    rationalPadicTeichmullerValued p K a ^ p =
      rationalPadicTeichmullerValued p K a := by
  rw [rationalPadicTeichmullerValued, ← map_pow,
    rationalPadicTeichmuller_pow_prime]

theorem rationalPadicTeichmullerValued_pow_prime_pow (a : ZMod p) (r : ℕ) :
    rationalPadicTeichmullerValued p K a ^ (p ^ r) =
      rationalPadicTeichmullerValued p K a := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      rw [Nat.pow_succ, pow_mul, ih,
        rationalPadicTeichmullerValued_pow_prime]

/-- Finite integral approximants to the scaled Dwork parameter
`omega(a) * G_p(lambda)`. -/
noncomputable def scaledDworkParameterApprox (a : ZMod p) (N : ℕ) :
    ValuedIntegerRing p K :=
  rationalPadicTeichmullerValued p K a * dworkParameterApprox p K N

theorem scaledDworkParameterApprox_mem_lambdaIdeal (a : ZMod p) (N : ℕ) :
    scaledDworkParameterApprox p K a N ∈ lambdaIdeal p K :=
  (lambdaIdeal p K).mul_mem_left
    (rationalPadicTeichmullerValued p K a)
    (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) N)

theorem scaledDworkParameter_evalₐ (a : ZMod p) (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N (scaledDworkParameter p K a) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
        (scaledDworkParameterApprox p K a N) := by
  rw [scaledDworkParameter, map_mul, dworkParameter_evalₐ]
  simp [scaledDworkParameterApprox, rationalPadicTeichmullerValued,
    algebraMap_rationalPadicInteger_dworkComplete_apply]

theorem samePrimeFiniteArtinHasseLogTerm_teichmuller_mul
    (N r : ℕ) (a : ZMod p) {x : ValuedIntegerRing p K}
    (hx : x ∈ lambdaIdeal p K)
    (hcx :
      rationalPadicTeichmullerValued p K a * x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r
        (rationalPadicTeichmullerValued p K a * x) hcx =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          (rationalPadicTeichmullerValued p K a) *
        samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx := by
  let c : ValuedIntegerRing p K := rationalPadicTeichmullerValued p K a
  let n : ℕ := p ^ r
  have hn : n ≠ 0 := pow_ne_zero r (Fact.out : Nat.Prime p).ne_zero
  have hfac : n.factorization p = r := by
    simpa [n] using
      (Nat.factorization_pow_self (p := p) (n := r) (Fact.out : Nat.Prime p))
  have hpowx :
      x ^ n ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + 0) := by
    have hpow : x ^ n ∈ (lambdaIdeal p K) ^ n :=
      Ideal.pow_mem_pow hx n
    have hden : r * (p - 1) ≤ p ^ r :=
      samePrimeArtinHasseLog_den_le (p := p) r
    have htarget : n.factorization p * (p - 1) + 0 ≤ n := by
      rw [hfac]
      simpa [n] using hden
    exact Ideal.pow_le_pow_right
      htarget hpow
  have hpowcx :
      (c * x) ^ n ∈
        (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + 0) := by
    have hpow : (c * x) ^ n ∈ (lambdaIdeal p K) ^ n :=
      Ideal.pow_mem_pow hcx n
    have hden : r * (p - 1) ≤ p ^ r :=
      samePrimeArtinHasseLog_den_le (p := p) r
    have htarget : n.factorization p * (p - 1) + 0 ≤ n := by
      rw [hfac]
      simpa [n] using hden
    exact Ideal.pow_le_pow_right
      htarget hpow
  have hcpow : c ^ n = c := by
    simpa [c, n] using
      rationalPadicTeichmullerValued_pow_prime_pow (p := p) (K := K) a r
  have hpow_eq : (c * x) ^ n = c * x ^ n := by
    rw [mul_pow, hcpow]
  have hcxpow :
      c * x ^ n ∈
        (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + 0) := by
    simpa [hpow_eq] using hpowcx
  calc
    samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r
        (rationalPadicTeichmullerValued p K a * x) hcx
        =
      samePrimeNatDivEval (p := p) (K := K) N n 0 hn
        ((c * x) ^ n) hpowcx := by
          symm
          simpa [c, n] using
            samePrimeNatDivEval_prime_pow_zero_eq_finiteArtinHasseLogTerm
              (p := p) (K := K) N r hcx hpowcx
    _ =
      samePrimeNatDivEval (p := p) (K := K) N n 0 hn
        (c * x ^ n) hcxpow :=
          samePrimeNatDivEval_eq_of_eq (p := p) (K := K) hn
            hpow_eq hpowcx hcxpow
    _ =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) c *
        samePrimeNatDivEval (p := p) (K := K) N n 0 hn
          (x ^ n) hpowx :=
          samePrimeNatDivEval_mul_left (p := p) (K := K) hn
            c hpowx hcxpow
    _ =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          (rationalPadicTeichmullerValued p K a) *
        samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx := by
          rw [← samePrimeNatDivEval_prime_pow_zero_eq_finiteArtinHasseLogTerm
            (p := p) (K := K) N r hx hpowx]

theorem samePrimeFiniteArtinHasseLog_teichmuller_mul
    (N : ℕ) (a : ZMod p) {x : ValuedIntegerRing p K}
    (hx : x ∈ lambdaIdeal p K)
    (hcx :
      rationalPadicTeichmullerValued p K a * x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseLog (p := p) (K := K) N
        (rationalPadicTeichmullerValued p K a * x) hcx =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          (rationalPadicTeichmullerValued p K a) *
        samePrimeFiniteArtinHasseLog (p := p) (K := K) N x hx := by
  classical
  rw [samePrimeFiniteArtinHasseLog, samePrimeFiniteArtinHasseLog, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  exact samePrimeFiniteArtinHasseLogTerm_teichmuller_mul
    (p := p) (K := K) N r a hx hcx

/-- The finite same-prime Artin-Hasse logarithm at the scaled Dwork
approximant. -/
noncomputable def scaledDworkParameterFiniteArtinHasseLog
    (a : ZMod p) (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  samePrimeFiniteArtinHasseLog (p := p) (K := K) N
    (scaledDworkParameterApprox p K a (N + 1))
    (scaledDworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) a (N + 1))

theorem scaledDworkParameterFiniteArtinHasseLog_eq_teichmuller_mul
    (a : ZMod p) (N : ℕ) :
    scaledDworkParameterFiniteArtinHasseLog (p := p) (K := K) a N =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          (rationalPadicTeichmullerValued p K a) *
        dworkParameterFiniteArtinHasseLog (p := p) (K := K) N := by
  rw [scaledDworkParameterFiniteArtinHasseLog,
    dworkParameterFiniteArtinHasseLog]
  exact samePrimeFiniteArtinHasseLog_teichmuller_mul
    (p := p) (K := K) N a
    (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1))
    (scaledDworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) a (N + 1))

theorem scaledDworkParameterFiniteArtinHasseLog_eq_zero
    (a : ZMod p) (N : ℕ) :
    scaledDworkParameterFiniteArtinHasseLog (p := p) (K := K) a N = 0 := by
  rw [scaledDworkParameterFiniteArtinHasseLog_eq_teichmuller_mul,
    dworkParameterFiniteArtinHasseLog_eq_zero, mul_zero]

noncomputable def scaledDworkParameterFiniteArtinHasseLogCoord
    (a : ZMod p) (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N :=
  match N with
  | 0 => 0
  | N + 1 => scaledDworkParameterFiniteArtinHasseLog (p := p) (K := K) a N

@[simp]
theorem scaledDworkParameterFiniteArtinHasseLogCoord_zero (a : ZMod p) :
    scaledDworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) a 0 = 0 := rfl

@[simp]
theorem scaledDworkParameterFiniteArtinHasseLogCoord_succ
    (a : ZMod p) (N : ℕ) :
    scaledDworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) a (N + 1) =
      scaledDworkParameterFiniteArtinHasseLog (p := p) (K := K) a N := rfl

theorem scaledDworkParameterFiniteArtinHasseLogCoord_eq_zero
    (a : ZMod p) (N : ℕ) :
    scaledDworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) a N = 0 := by
  cases N with
  | zero =>
      simp
  | succ N =>
      simp [scaledDworkParameterFiniteArtinHasseLog_eq_zero]

/-- The completed Artin-Hasse logarithm at `omega(a) * varpi`, expressed
through the already constructed completed log at `varpi`. -/
noncomputable def artinHasseLog_eval_scaledDworkParameter (a : ZMod p) :
    DworkCompleteIntegerRing p K :=
  algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K)
      (rationalPadicTeichmuller p a) *
    artinHasseLog_eval_dworkParameter p K

@[simp]
theorem artinHasseLog_eval_scaledDworkParameter_evalₐ_succ
    (a : ZMod p) (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) (N + 1)
        (artinHasseLog_eval_scaledDworkParameter p K a) =
      scaledDworkParameterFiniteArtinHasseLog (p := p) (K := K) a N := by
  rw [artinHasseLog_eval_scaledDworkParameter, map_mul,
    artinHasseLog_eval_dworkParameter_evalₐ_succ,
    scaledDworkParameterFiniteArtinHasseLog_eq_teichmuller_mul]
  simp [rationalPadicTeichmullerValued,
    algebraMap_rationalPadicInteger_dworkComplete_apply]

@[simp]
theorem artinHasseLog_eval_scaledDworkParameter_evalₐ
    (a : ZMod p) (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N
        (artinHasseLog_eval_scaledDworkParameter p K a) =
      scaledDworkParameterFiniteArtinHasseLogCoord (p := p) (K := K) a N := by
  cases N with
  | zero =>
      exact quotient_pow_zero_eq_zero (p := p) (K := K) (lambdaIdeal p K)
        (AdicCompletion.evalₐ (lambdaIdeal p K) 0
          (artinHasseLog_eval_scaledDworkParameter p K a))
  | succ N =>
      simp

theorem artinHasseLog_eval_scaledDworkParameter_eq_zero (a : ZMod p) :
    artinHasseLog_eval_scaledDworkParameter p K a = 0 := by
  rw [artinHasseLog_eval_scaledDworkParameter,
    artinHasseLog_eval_dworkParameter_eq_zero, mul_zero]

/-- Completed Artin-Hasse exponential at the scaled Dwork parameter.  CU-09g3
will identify this element with `zeta_p^a`. -/
noncomputable def artinHasseExp_eval_scaledDworkParameter (a : ZMod p) :
    DworkCompleteIntegerRing p K :=
  evalIntegralPowerSeries p K (integralExpSeries p K)
    (scaledDworkParameter p K a)
    (scaledDworkParameter_evalₐ_one (p := p) (K := K) a)

@[simp]
theorem artinHasseExp_eval_scaledDworkParameter_evalₐ
    (a : ZMod p) (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N
        (artinHasseExp_eval_scaledDworkParameter p K a) =
      evalIntegralPowerSeriesMod p K (integralExpSeries p K)
        (scaledDworkParameter p K a) N := by
  simp [artinHasseExp_eval_scaledDworkParameter]

theorem evalIntegralPowerSeriesMod_exp_scaledDworkParameter_two
    (a : ZMod p) :
    evalIntegralPowerSeriesMod p K (integralExpSeries p K)
        (scaledDworkParameter p K a) 2 =
      1 + AdicCompletion.evalₐ (lambdaIdeal p K) 2
        (scaledDworkParameter p K a) := by
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let A : Type _ := R ⧸ I ^ 2
  let q : R →+* A := Ideal.Quotient.mk (I ^ 2)
  let xbar : A := AdicCompletion.evalₐ I 2 (scaledDworkParameter p K a)
  change
    (PowerSeries.trunc 2 (PowerSeries.map q (integralExpSeries p K))).eval₂
        (RingHom.id A) xbar =
      1 + xbar
  rw [PowerSeries.trunc_map, integralExpSeries_trunc_two,
    ← PowerSeries.trunc_map]
  simp

theorem artinHasseExp_eval_scaledDworkParameter_sub_one_sub_scaled_mem_sq
    (a : ZMod p) :
    artinHasseExp_eval_scaledDworkParameter p K a - 1 -
        scaledDworkParameter p K a ∈
      (dworkCompleteLambdaIdeal p K) ^ 2 := by
  apply dworkComplete_mem_lambdaIdeal_pow_of_evalₐ_eq_zero
    (p := p) (K := K) (n := 2)
  rw [map_sub, map_sub, map_one,
    artinHasseExp_eval_scaledDworkParameter_evalₐ,
    evalIntegralPowerSeriesMod_exp_scaledDworkParameter_two]
  ring

theorem artinHasseExp_eval_scaledDworkParameter_sub_one_sub_natCast_mul_lambda_mem_sq
    (a : ZMod p) :
    artinHasseExp_eval_scaledDworkParameter p K a - 1 -
        algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K)
          (a.val : RationalPadicIntegerRing p) *
          dworkCompleteLambda p K ∈
      (dworkCompleteLambdaIdeal p K) ^ 2 := by
  let S : Type _ := DworkCompleteIntegerRing p K
  let I : Ideal S := dworkCompleteLambdaIdeal p K
  let y : S := artinHasseExp_eval_scaledDworkParameter p K a
  let x : S := scaledDworkParameter p K a
  let z : S :=
    algebraMap (RationalPadicIntegerRing p) S
      (a.val : RationalPadicIntegerRing p) *
      dworkCompleteLambda p K
  have hyx : y - 1 - x ∈ I ^ 2 := by
    simpa [S, I, y, x] using
      artinHasseExp_eval_scaledDworkParameter_sub_one_sub_scaled_mem_sq
        (p := p) (K := K) a
  have hxz : x - z ∈ I ^ 2 := by
    simpa [S, I, x, z] using
      scaledDworkParameter_sub_natCast_mul_lambda_mem_sq (p := p) (K := K) a
  have hsum : (y - 1 - x) + (x - z) ∈ I ^ 2 := (I ^ 2).add_mem hyx hxz
  convert hsum using 1
  ring

theorem adicCompletion_of_zeta_pow_sub_one_sub_natCast_mul_lambda_mem_sq
    (a : ZMod p) :
    AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
        (valuedCyclotomicZetaInteger p K ^ a.val) - 1 -
        algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K)
          (a.val : RationalPadicIntegerRing p) *
          dworkCompleteLambda p K ∈
      (dworkCompleteLambdaIdeal p K) ^ 2 := by
  let R : Type _ := ValuedIntegerRing p K
  let S : Type _ := DworkCompleteIntegerRing p K
  let I : Ideal S := dworkCompleteLambdaIdeal p K
  let hz : R := valuedCyclotomicZetaInteger p K ^ a.val
  let lam : R := valuedCyclotomicLambdaInteger p K
  have hvalued :
      hz - 1 - (a.val : R) * lam ∈ (lambdaIdeal p K) ^ 2 := by
    simpa [R, hz, lam] using
      valuedCyclotomicZetaInteger_pow_sub_one_sub_natCast_mul_lambda_mem_sq
        (p := p) (K := K) a
  have hmap :
      algebraMap R S (hz - 1 - (a.val : R) * lam) ∈ I ^ 2 := by
    have hraw :
        algebraMap R S (hz - 1 - (a.val : R) * lam) ∈
          ((lambdaIdeal p K) ^ 2).map (algebraMap R S) :=
      Ideal.mem_map_of_mem (algebraMap R S) hvalued
    simpa [S, I, dworkCompleteLambdaIdeal, Ideal.map_pow] using hraw
  convert hmap using 1
  rw [algebraMap_rationalPadicInteger_natCast_dworkComplete (p := p) (K := K)]
  change
    algebraMap R S hz - 1 - algebraMap R S (a.val : R) *
        algebraMap R S lam =
      algebraMap R S (hz - 1 - (a.val : R) * lam)
  simp [map_sub, map_mul]

theorem artinHasseExp_eval_scaledDworkParameter_sub_zeta_pow_mem_sq
    (a : ZMod p) :
    artinHasseExp_eval_scaledDworkParameter p K a -
        AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
          (valuedCyclotomicZetaInteger p K ^ a.val) ∈
      (dworkCompleteLambdaIdeal p K) ^ 2 := by
  let S : Type _ := DworkCompleteIntegerRing p K
  let I : Ideal S := dworkCompleteLambdaIdeal p K
  let y : S := artinHasseExp_eval_scaledDworkParameter p K a
  let z : S :=
    AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
      (valuedCyclotomicZetaInteger p K ^ a.val)
  let lin : S :=
    algebraMap (RationalPadicIntegerRing p) S
      (a.val : RationalPadicIntegerRing p) *
      dworkCompleteLambda p K
  have hy :
      y - 1 - lin ∈ I ^ 2 := by
    simpa [S, I, y, lin] using
      artinHasseExp_eval_scaledDworkParameter_sub_one_sub_natCast_mul_lambda_mem_sq
        (p := p) (K := K) a
  have hz :
      z - 1 - lin ∈ I ^ 2 := by
    simpa [S, I, z, lin] using
      adicCompletion_of_zeta_pow_sub_one_sub_natCast_mul_lambda_mem_sq
        (p := p) (K := K) a
  have hdiff : (y - 1 - lin) - (z - 1 - lin) ∈ I ^ 2 := (I ^ 2).sub_mem hy hz
  convert hdiff using 1
  ring

end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular
