import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.LeadingExponentBridge

/-!
# Washington Exercise 8.11 for `p = 37`

This file proves the completed-log valuation half needed for the leading-exponent collapse and
packages `LeadingExponentEigenCollapse37` as a reduction to the single remaining bridge
`LeadingExponentBridge37`.

References: Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Lemma 9.9 and Exercises
8.10/8.11.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits

/-- The completed-log valuation half of Washington Exercise 8.11 for `p = 37`. -/
theorem completedLogVanishingThroughLevel36_37_proven
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    CompletedLogVanishingThroughLevel36_37 := by
  intro u hu N hN
  revert hu
  unfold CompletedLogArgHighValuation37
  rcases N with _ | M
  ·
    intro _hu
    rw [completedLog_evalₐ]
    rfl
  ·
    rw [completedLog_evalₐ_succ]
    generalize EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u = W
    intro hu
    refine caseIIEx811_samePrimeFiniteLog_eq_zero_of_le_of_mem_pow36
      (M := M) (y := completedLogArg (p := 37) (K := CyclotomicField 37 ℚ) W) (by omega) ?_
      (completedLogArg_mem (p := 37) (K := CyclotomicField 37 ℚ) W)
    convert hu using 2

/-- `LeadingExponentEigenCollapse37` from the single Galois-equivariant bridge. -/
theorem leadingExponentEigenCollapse37_of_bridge'
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hBridge : LeadingExponentBridge37) :
    LeadingExponentEigenCollapse37 :=
  leadingExponentEigenCollapse37_of_bridge completedLogVanishingThroughLevel36_37_proven hBridge

end BernoulliRegular.FLT37.Eichler

end
