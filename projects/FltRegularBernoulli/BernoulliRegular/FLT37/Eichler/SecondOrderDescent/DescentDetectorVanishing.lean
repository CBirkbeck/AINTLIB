import BernoulliRegular.FLT37.Eichler.SecondOrderDescent.KummerLogDetectorModSq

/-!
# The second-order descent detector vanishes

This file proves the detector-vanishing half of Washington Proposition 8.12 at `i = 32` and
`p = 37`. For a unit `u` in the maximal real subfield whose image is congruent to an integer
modulo `37 ^ 2`, the mod-`37 ^ 2` `varpi ^ 32` Dwork detector of its descent logarithm vanishes.

The completed-log argument is `X ^ 36 - 1`, where `X = EPlus_valuedLocalImage u`. The proof uses
the decomposition

`X ^ 36 - 1 = (X ^ 36 - c ^ 36) + (c ^ 36 - 1)`.

The first summand lies in the 72nd power of the lambda ideal, while the second is a rational
constant and therefore contributes only to the zeroth Dwork coordinate. A high-precision
same-prime logarithm lemma identifies the logarithm with its argument at level 72.

## Main results

* `samePrimeFiniteLog_eq_mk_of_mem_pow_high_level` identifies a same-prime logarithm with its
  argument when the requested precision is at most twice the known lambda-adic order.
* `caseIICor823SecondOrder_argCoeffModSq_eq_zero` proves that the relevant coordinate of the
  completed-log argument vanishes.
* `caseIICor823SecondOrder_detector_descent_eq_zero` proves that the descent detector vanishes.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Sections 8.4 and 9.2.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- If `x` lies in the `m`th power of the lambda ideal, then every logarithm term of degree at
least two vanishes at any precision bounded by `2 * m`. -/
theorem samePrimeFiniteLogTerm_eq_zero_of_mem_pow_high_level
    {N m n : ℕ} (hp : 3 ≤ p) (hm : 2 ≤ m) (hn : 2 ≤ n) (hN : N + 1 ≤ 2 * m)
    {x : ValuedIntegerRing p K} (hx : x ∈ (lambdaIdeal p K) ^ m)
    (hxI : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLogTerm (p := p) (K := K) N n x hxI = 0 := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hfactorization : n.factorization p * (p - 1) ≤ n - 1 := by
    simpa [Nat.mul_comm] using
      Nat.factorization_mul_pred_le_pred (ell := p) (n := n)
        (Fact.out : Nat.Prime p) hn_ne
  set s : ℕ := n * m - n.factorization p * (p - 1) with hs
  have hxpow_s :
      x ^ n ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
    have hxpow : x ^ n ∈ ((lambdaIdeal p K) ^ m) ^ n := Ideal.pow_mem_pow hx n
    have hxpow_nm : x ^ n ∈ (lambdaIdeal p K) ^ (m * n) := by
      simpa [pow_mul] using hxpow
    have hden_le : n.factorization p * (p - 1) ≤ n * m := by
      exact hfactorization.trans ((Nat.sub_le n 1).trans
        (Nat.le_mul_of_pos_right n (lt_of_lt_of_le (by decide : 0 < 2) hm)))
    have hsum : n.factorization p * (p - 1) + s = n * m := by
      rw [hs]
      omega
    have hsum' : n.factorization p * (p - 1) + s = m * n := by
      rw [hsum]
      ring
    simpa [hsum'] using hxpow_nm
  have hdeg : n.factorization p * (p - 1) ≤ n :=
    hfactorization.trans (Nat.sub_le n 1)
  have htermCore :
      samePrimeFiniteLogTermCore (p := p) (K := K) N n x hxI =
        samePrimeNatDivEval (p := p) (K := K) N n s hn_ne (x ^ n) hxpow_s := by
    rw [samePrimeFiniteLogTermCore_eq_samePrimeNatDivEvalAtDegree
      (p := p) (K := K) hn_ne hxI]
    exact samePrimeNatDivEvalAtDegree_eq_samePrimeNatDivEval
      (p := p) (K := K) hn_ne (Ideal.pow_mem_pow hxI n) hdeg hxpow_s
  rw [samePrimeFiniteLogTerm, htermCore]
  have hNs : N + 1 ≤ s := by
    rw [hs]
    have hge : 2 * m + n.factorization p * (p - 1) ≤ n * m := by
      rcases Nat.lt_or_ge n 3 with hn3 | hn3
      ·
        have hn2 : n = 2 := by omega
        subst n
        have hv0 : (2 : ℕ).factorization p = 0 := by
          rw [Nat.factorization_eq_zero_iff]
          exact Or.inr (Or.inl (fun hdvd ↦ by
            have hp_le_two := Nat.le_of_dvd (by norm_num) hdvd
            omega))
        rw [hv0]
        omega
      ·
        have hprod : (n - 2) * 2 ≤ (n - 2) * m := Nat.mul_le_mul_left _ hm
        have hexp : n * m = 2 * m + (n - 2) * m := by
          conv_lhs => rw [show n = 2 + (n - 2) by omega]
          rw [add_mul]
        omega
    omega
  rw [samePrimeNatDivEval_eq_zero_of_succ_le (p := p) (K := K) hn_ne hxpow_s hNs]
  rw [mul_zero]

/-- A same-prime logarithm agrees with its argument when all terms of degree at least two vanish
at the requested precision. -/
theorem samePrimeFiniteLog_eq_mk_of_mem_pow_high_level
    {N m : ℕ} (hp : 3 ≤ p) (hm : 2 ≤ m) (hN : N + 1 ≤ 2 * m)
    {x : ValuedIntegerRing p K} (hx : x ∈ (lambdaIdeal p K) ^ m)
    (hxI : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLog (p := p) (K := K) N x hxI =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) x := by
  classical
  simp only [samePrimeFiniteLog]
  rw [Finset.sum_eq_single 1]
  · exact samePrimeFiniteLogTerm_one_eq_mk (p := p) (K := K) N hxI
  · intro n _hn_range hn_ne_one
    by_cases hn0 : n = 0
    · subst n
      exact samePrimeFiniteLogTerm_zero (p := p) (K := K) N x hxI
    · exact samePrimeFiniteLogTerm_eq_zero_of_mem_pow_high_level
        (p := p) (K := K) hp hm (by omega) hN hx hxI
  · intro hnot
    exfalso
    have hcut : 1 < samePrimeFiniteLogCutoff (p := p) N := by
      calc
        1 < p := (Fact.out : Nat.Prime p).one_lt
        _ ≤ p * (N + 1) := Nat.le_mul_of_pos_right p (Nat.succ_pos N)
    exact hnot (by simpa [samePrimeFiniteLogCutoff] using hcut)

/-- The mod-`p²` `varpi^k` Dwork coordinate of a rational-integer constant `c` vanishes at every
positive index `k` (`(k : ℕ) ≠ 0`): the constant maps to the `varpi^0` coordinate only. -/
theorem valuedLambdaQuotientDworkCoeffModSq_mk_intCast_eq_zero
    (k : Fin (p - 1)) (hk : (k : ℕ) ≠ 0) (c : ℤ) :
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) k
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (2 * (p - 1)))
          (c : ValuedIntegerRing p K)) = 0 := by
  classical
  rw [valuedLambdaQuotientDworkCoeffModSq_mk]
  set c' : RationalPadicIntegerRing p :=
    (c : RationalPadicIntegerRing p) with hc'
  have hzero_idx : (0 : ℕ) < p - 1 := by
    have hp_two := (Fact.out : Nat.Prime p).two_le
    omega
  have hsingle :
      algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)
          (c : ValuedIntegerRing p K) =
        dworkParameterPowerLinearMap p K
          (Pi.single (⟨0, hzero_idx⟩ : Fin (p - 1)) c') := by
    rw [dworkParameterPowerLinearMap_single_coeff]
    simp only [pow_zero, mul_one]
    rw [hc', map_intCast, map_intCast]
  rw [hsingle, dworkParameterPowerBasis_repr_powerLinearMap]
  rw [Pi.single_eq_of_ne (fun hcontra ↦ hk (by rw [hcontra]))]
  rw [map_zero]

/-- The mod-`p²` `varpi^k` Dwork coordinate of an element in the `2 * (p - 1)`st power of the
lambda ideal vanishes. -/
theorem valuedLambdaQuotientDworkCoeffModSq_mk_eq_zero_of_mem_pow
    (k : Fin (p - 1)) {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (2 * (p - 1))) :
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) k
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (2 * (p - 1))) z) = 0 := by
  rw [show Ideal.Quotient.mk ((lambdaIdeal p K) ^ (2 * (p - 1))) z =
      (0 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hz]
  exact valuedLambdaQuotientDworkCoeffModSq_zero (p := p) (K := K) k

end BernoulliRegular.CyclotomicUnits

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-- The `varpi ^ 32` mod-`37 ^ 2` Dwork coordinate of the descent-log argument vanishes. The
nonconstant part of `X ^ 36 - 1` lies in the 72nd power of the lambda ideal, and its remaining
part is a rational constant. -/
theorem caseIICor823SecondOrder_argCoeffModSq_eq_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ)
    (hc : ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ))))
    (k : Fin (37 - 1)) (hk : (k : ℕ) = 32) :
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ) k
        (Ideal.Quotient.mk ((lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (2 * (37 - 1)))
          ((EPlus_valuedLocalImage (p := 37) (K := CyclotomicField 37 ℚ) u :
              ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 - 1)) = 0 := by
  letI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set x : ValuedIntegerRing 37 (CyclotomicField 37 ℚ) :=
    (EPlus_valuedLocalImage (p := 37) (K := CyclotomicField 37 ℚ) u :
      ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) with hx
  have hsplit : x ^ 36 - 1 =
      (x ^ 36 - (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36) +
        ((c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 - 1) := by ring
  rw [hsplit, map_add, valuedLambdaQuotientDworkCoeffModSq_add]
  have hmem72 :
      x ^ 36 - (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 ∈
        (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (2 * (37 - 1)) := by
    have h := caseIICor823_localImage_pow36_sub_intCast_pow36_mem_lambdaIdeal_pow72 u c hc
    rw [hx]
    generalize (EPlus_valuedLocalImage (p := 37) (K := CyclotomicField 37 ℚ) u :
        ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 -
        (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 = z at h ⊢
    convert h using 2
  have hnonconstant :
      valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ) k
      (Ideal.Quotient.mk ((lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (2 * (37 - 1)))
        (x ^ 36 - (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36)) = 0 := by
    set_option maxRecDepth 4000 in
      exact valuedLambdaQuotientDworkCoeffModSq_mk_eq_zero_of_mem_pow
        (p := 37) (K := CyclotomicField 37 ℚ) k hmem72
  have hconstant :
      valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ) k
      (Ideal.Quotient.mk ((lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (2 * (37 - 1)))
        ((c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 - 1)) = 0 := by
    rw [show ((c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 - 1) =
        (((c ^ 36 - 1 : ℤ) : ValuedIntegerRing 37 (CyclotomicField 37 ℚ))) by
          push_cast
          ring]
    exact valuedLambdaQuotientDworkCoeffModSq_mk_intCast_eq_zero
      (p := 37) (K := CyclotomicField 37 ℚ) k (by rw [hk]; decide) (c ^ 36 - 1)
  rw [hnonconstant, hconstant, add_zero]

/-- The mod-`37 ^ 2` `varpi ^ 32` Dwork coefficient of the descent logarithm at precision 72. -/
def caseIICor823DescentDetectorSq
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) : ZMod (37 ^ 2) :=
  valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
    (⟨32, by norm_num⟩ : Fin (37 - 1))
    (AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (2 * (37 - 1))
      (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
        (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u)))

/-- The mod-`37 ^ 2` `varpi ^ 32` detector of the descent logarithm vanishes when the unit image is
congruent to a rational integer modulo `37 ^ 2`. -/
theorem caseIICor823SecondOrder_detector_descent_eq_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ)
    (hc : ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ)))) :
    caseIICor823DescentDetectorSq u = 0 := by
  letI : Fact (Nat.Prime 37) := ⟨by decide⟩
  simp only [caseIICor823DescentDetectorSq]
  set k : Fin (37 - 1) := ⟨32, by norm_num⟩
  have hk : (k : ℕ) = 32 := rfl
  have hc1 : (37 : 𝓞 (CyclotomicField 37 ℚ)) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ))) :=
    dvd_trans (dvd_pow_self (37 : 𝓞 (CyclotomicField 37 ℚ)) (by norm_num)) hc
  set w : completedLogDomain (p := 37) (K := CyclotomicField 37 ℚ) :=
    EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u with hw
  have harg_eq : completedLogArg (p := 37) (K := CyclotomicField 37 ℚ) w =
      (EPlus_valuedLocalImage (p := 37) (K := CyclotomicField 37 ℚ) u :
        ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 - 1 := by
    rw [hw, completedLogArg, EPlus_completedLogDomainPowPred_coe]
  have harg_mem : completedLogArg (p := 37) (K := CyclotomicField 37 ℚ) w ∈
      (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ 36 := by
    have hval := caseIILeadingExponent_completedLogArg_mem_lambdaIdeal_pow_pred u c hc1
    revert hval
    simp only [CompletedLogArgHighValuation37]
    rw [hw]
    generalize completedLogArg (p := 37) (K := CyclotomicField 37 ℚ)
      (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u) = z
    intro hval
    convert hval using 2
  have hdetector :
      AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (2 * (37 - 1))
        (completedLog (p := 37) (K := CyclotomicField 37 ℚ) w) =
      Ideal.Quotient.mk ((lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (2 * (37 - 1)))
        (completedLogArg (p := 37) (K := CyclotomicField 37 ℚ) w) := by
    rw [completedLog_evalₐ]
    rw [show (2 * (37 - 1)) = 71 + 1 from rfl]
    rw [show completedLogCoord (p := 37) (K := CyclotomicField 37 ℚ) w (71 + 1) =
        AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (71 + 1)
          (completedLog (p := 37) (K := CyclotomicField 37 ℚ) w) from
      (completedLog_evalₐ (p := 37) (K := CyclotomicField 37 ℚ) w (71 + 1)).symm]
    rw [completedLog_evalₐ_succ]
    set_option maxRecDepth 4000 in
      rw [samePrimeFiniteLog_eq_mk_of_mem_pow_high_level
        (p := 37) (K := CyclotomicField 37 ℚ) (m := 36) (N := 71)
        (by norm_num) (by norm_num) (by norm_num) harg_mem
        (completedLogArg_mem (p := 37) (K := CyclotomicField 37 ℚ) w)]
  rw [hdetector, harg_eq]
  exact caseIICor823SecondOrder_argCoeffModSq_eq_zero u c hc k hk

end BernoulliRegular.FLT37.Eichler

end
