import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.LambdaExponentCollapseToOmega32

/-!
# Washington Exercise 8.11 for `p = 37`

This file packages the leading-`λ`-exponent bridge used to discharge
`LeadingExponentEigenCollapse37`.

## Main definitions

* `CompletedLogVanishingThroughLevel36_37`: the completed logarithm vanishes through
  `λ`-level `36`.
* `LeadingExponentBridge37`: the local logarithm bridge to regular eigencomponents.

## Main results

* `leadingExponentEigenCollapse37_of_bridge`: `LeadingExponentEigenCollapse37` from the valuation
  half and bridge.
* `leadingExponentEigenCollapse37_proven`: the same conclusion under the named structural inputs.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.2 Lemma 9.9,
  Exercises 8.10/8.11, Corollary 8.15, Theorem 8.16.
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-- For `2 ≤ N` and `y ∈ λ ^ (N + 1)`, the level-`N` same-prime finite logarithm vanishes. -/
theorem caseIIEx811_samePrimeFiniteLog_eq_zero_of_two_le_of_mem_pow_succ
    {N : ℕ} (hN : 2 ≤ N)
    {y : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)}
    (hy : y ∈ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (N + 1))
    (hy' : y ∈ lambdaIdeal 37 (CyclotomicField 37 ℚ)) :
    samePrimeFiniteLog (p := 37) (K := CyclotomicField 37 ℚ) N y hy' = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hyN : y ∈ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ N :=
    Ideal.pow_le_pow_right (Nat.le_succ N) hy
  have heq :=
    samePrimeFiniteLog_eq_mk_of_mem_pow_of_two_le
      (p := 37) (K := CyclotomicField 37 ℚ) (m := N) hN hyN
  rw [samePrimeFiniteLog_eq_of_eq (p := 37) (K := CyclotomicField 37 ℚ) (N := N) rfl hy'
    (Ideal.pow_le_self (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hN)) hyN), heq,
    Ideal.Quotient.eq_zero_iff_mem]
  exact hy

/-- For `2 ≤ n` and `y ∈ λ ^ 2`, the `n`-th level-`1` same-prime finite-log term vanishes. -/
theorem caseIIEx811_samePrimeFiniteLogTerm_level_one_eq_zero
    {n : ℕ} (hn : 2 ≤ n)
    {y : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)}
    (hy2 : y ∈ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ 2)
    (hy' : y ∈ lambdaIdeal 37 (CyclotomicField 37 ℚ)) :
    samePrimeFiniteLogTerm (p := 37) (K := CyclotomicField 37 ℚ) 1 n y hy' = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set v : ℕ := n.factorization 37 with hv
  set s : ℕ := n * 2 - v * (37 - 1) with hs
  have hn_ne : n ≠ 0 := by omega
  have hxpow_s : y ^ n ∈ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (v * (37 - 1) + s) := by
    have hxpow : y ^ n ∈ ((lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ 2) ^ n :=
      Ideal.pow_mem_pow hy2 n
    have hxpow_nm : y ^ n ∈ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (2 * n) := by
      simpa [pow_mul] using hxpow
    have hden_le : v * (37 - 1) ≤ n * 2 := by
      have hle := Nat.factorization_mul_pred_le_pred (ell := 37) (n := n) (by decide) hn_ne
      have : v * (37 - 1) ≤ n - 1 := by simpa [hv, Nat.mul_comm] using hle
      omega
    have hsum : v * (37 - 1) + s = 2 * n := by
      rw [hs]
      omega
    simpa [hsum] using hxpow_nm
  have htermCore :
      samePrimeFiniteLogTermCore (p := 37) (K := CyclotomicField 37 ℚ) 1 n y hy' =
        samePrimeNatDivEval (p := 37) (K := CyclotomicField 37 ℚ) 1 n s hn_ne (y ^ n)
          hxpow_s := by
    have hdeg : n.factorization 37 * (37 - 1) ≤ n := by
      have h := Nat.factorization_mul_pred_le_pred (ell := 37) (n := n) (by decide) hn_ne
      omega
    rw [samePrimeFiniteLogTermCore_eq_samePrimeNatDivEvalAtDegree
      (p := 37) (K := CyclotomicField 37 ℚ) hn_ne hy']
    exact samePrimeNatDivEvalAtDegree_eq_samePrimeNatDivEval
      (p := 37) (K := CyclotomicField 37 ℚ) hn_ne (Ideal.pow_mem_pow hy' n) hdeg hxpow_s
  rw [samePrimeFiniteLogTerm, htermCore]
  rw [samePrimeNatDivEval_eq_zero_of_succ_le (p := 37) (K := CyclotomicField 37 ℚ) hn_ne hxpow_s
    (by
    rw [hs]
    have hle := Nat.factorization_mul_pred_le_pred (ell := 37) (n := n) (by decide) hn_ne
    have hv_pred : v * (37 - 1) ≤ n - 1 := by simpa [hv, Nat.mul_comm] using hle
    omega)]
  simp

/-- For `y ∈ λ ^ 2`, the level-`1` same-prime finite logarithm vanishes. -/
theorem caseIIEx811_samePrimeFiniteLog_level_one_eq_zero
    {y : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)}
    (hy2 : y ∈ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ 2)
    (hy' : y ∈ lambdaIdeal 37 (CyclotomicField 37 ℚ)) :
    samePrimeFiniteLog (p := 37) (K := CyclotomicField 37 ℚ) 1 y hy' = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  unfold samePrimeFiniteLog
  rw [Finset.sum_eq_single 1]
  · rw [samePrimeFiniteLogTerm_one_eq_mk (p := 37) (K := CyclotomicField 37 ℚ) 1 hy',
      Ideal.Quotient.eq_zero_iff_mem]
    exact hy2
  · intro n _hn_range hn_ne_one
    by_cases hn0 : n = 0
    · subst n
      simp
    · exact caseIIEx811_samePrimeFiniteLogTerm_level_one_eq_zero (n := n) (by omega) hy2 hy'
  · intro hnot
    refine absurd (Finset.mem_range.mpr ?_) hnot
    show 1 < samePrimeFiniteLogCutoff (p := 37) 1
    calc 1 < 37 := by norm_num
      _ ≤ 37 * (1 + 1) := by norm_num

/-- For `M ≤ 35` and `y ∈ λ ^ 36`, the level-`M` same-prime finite logarithm vanishes. -/
theorem caseIIEx811_samePrimeFiniteLog_eq_zero_of_le_of_mem_pow36
    {M : ℕ} (hM : M ≤ 35)
    {y : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)}
    (hy36 : y ∈ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ 36)
    (hy' : y ∈ lambdaIdeal 37 (CyclotomicField 37 ℚ)) :
    samePrimeFiniteLog (p := 37) (K := CyclotomicField 37 ℚ) M y hy' = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  rcases Nat.lt_or_ge M 1 with hM0 | hM1
  ·
    have : M = 0 := by omega
    subst this
    exact samePrimeFiniteLog_level_zero (p := 37) (K := CyclotomicField 37 ℚ) hy'
  · rcases Nat.lt_or_ge M 2 with hM1' | hM2
    ·
      have : M = 1 := by omega
      subst this
      exact caseIIEx811_samePrimeFiniteLog_level_one_eq_zero
        (Ideal.pow_le_pow_right (by norm_num) hy36) hy'
    ·
      exact caseIIEx811_samePrimeFiniteLog_eq_zero_of_two_le_of_mem_pow_succ
        (N := M) hM2 (Ideal.pow_le_pow_right (by omega) hy36) hy'

/-- The completed logarithm of a unit satisfying `CompletedLogArgHighValuation37` vanishes through
`λ`-level `36`. -/
def CompletedLogVanishingThroughLevel36_37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ),
    CompletedLogArgHighValuation37 u →
    ∀ N : ℕ, N ≤ 36 →
      AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
            (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u)) = 0

/-- The local logarithm bridge from level-`36` vanishing to regular eigencomponent vanishing. -/
def LeadingExponentBridge37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ),
    (∀ N : ℕ, N ≤ 36 →
      AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
            (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u)) = 0) →
    ∀ j : Fin 18, j ≠ 15 →
      caseIIResidueProvenance_decomp
        (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u)) j = 0

/-- `LeadingExponentEigenCollapse37` follows from the valuation half and bridge. -/
theorem leadingExponentEigenCollapse37_of_bridge
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hVan : CompletedLogVanishingThroughLevel36_37)
    (hBridge : LeadingExponentBridge37) :
    LeadingExponentEigenCollapse37 := fun u hu j hj ↦
  hBridge u (hVan u hu) j hj

/-- `LeadingExponentEigenCollapse37` under the named valuation and bridge inputs. -/
theorem leadingExponentEigenCollapse37_proven
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hVan : CompletedLogVanishingThroughLevel36_37)
    (hBridge : LeadingExponentBridge37) :
    LeadingExponentEigenCollapse37 :=
  leadingExponentEigenCollapse37_of_bridge hVan hBridge

end BernoulliRegular.FLT37.Eichler

end
