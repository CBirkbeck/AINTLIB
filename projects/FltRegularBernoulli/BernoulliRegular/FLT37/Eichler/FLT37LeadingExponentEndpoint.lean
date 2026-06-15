import BernoulliRegular.FLT37.Eichler.CaseIILeadingExponent
import BernoulliRegular.FLT37.Eichler.FLT37CaseIWired

/-!
# FLT for `p = 37`, reduced to the three precise Case-II leaves (the Thm-9.4 leading-exponent route)

This module composes the proven chains into a single top-level statement of Fermat's Last Theorem at
`p = 37`, exposing **exactly** the remaining mathematical content as three precisely-named leaves plus
the user-owned second-order Bernoulli input.  Case I is fully discharged (`fltCaseI_thirtyseven`),
`¬ 37 ∣ h⁺` is proven (`Sinnott.flt37_not_dvd_hPlus`), and the entire Case-II descent engine —
realness (unconditional), the rational-mod-`37` congruence (`caseII_quotient_sub_intCast_mem_37`), the
automatic eigencomponent decomposition, the membership-free eigenspace collapse, the analytic
`SinnottIndexFormula 37`, the `Δ`-action eigenvalue, the half-range Vandermonde collapse, and the
high-`λ`-valuation local reduction — is proven.

It imports only; it does **not** modify any existing file.

## The three remaining Case-II leaves

`fermatLastTheoremFor_thirtyseven_of_leadingExponent` derives `FermatLastTheoremFor 37` from:

* `caseII_realDescent : CaseIIRealIdealDescent37` — **Case-II II1**, the single-quotient ideal descent
  `𝔞(η)/𝔞₀` descends from an ideal of `𝓞 K⁺` (Washington §9.1 `B_a` handled by Lemma 9.2 / Hilbert 90
  under `37 ∤ h⁺`).  Not supplied by the σ-stable *pair* producer (`caseII_sigmaPairAnchoredSource_proven`
  realises the conjugate-pair `𝔞(η)𝔞(η⁻¹)`, whose `𝔭`-valuations double).

* `hCollapse : LeadingExponentEigenCollapse37` — **Case-II II2, regular indices**, Washington Lemma 9.9's
  regular-index collapse in eigencomponent form (Exercise 8.11, the Galois-graded leading-`λ`-coefficient
  computation): high `λ`-valuation of the descent unit's completed log forces the regular eigencomponents
  (`i ≠ 32`, `37 ∤ B_i`, leading `λ`-exponent `i/2 < 18`) to vanish.  Its analytic input — the rational-mod-`37`
  congruence `⟹` `λ`-valuation `≥ 36` — is **proven**
  (`caseIILeadingExponent_completedLogArg_mem_lambdaIdeal_pow_pred`).  Second-order-condition-free.

* `h_localPow : Lemma98LocalPower37` — **Case-II II2, irregular index**, Washington Lemma 9.8's
  single-index mod-`𝔩` Kummer congruence (the descent unit is a `37`-th power mod `𝔩 = 149`), feeding the
  `residueInd₃₂` collapse for the surviving `i = 32` eigencomponent.

* `noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32` — the user-owned second-order Bernoulli
  input (`37³ ∤ B_{32·37}`), carried (Kellner Prop 2.7), **not** a leaf to discharge.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–§9.2 (Theorems 9.4/9.5,
  Lemmas 9.8/9.9), Exercises 8.10/8.11, Corollaries 8.15/8.23.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-- **Fermat's Last Theorem for `37`, reduced to the three Case-II leaves** (proven, axiom-clean given
the three named inputs + the carried second-order Bernoulli Prop).

Composes:
* Case I — `fltCaseI_thirtyseven` (proven, unconditional), wired by `fermatLastTheoremFor_thirtyseven_of_caseII`;
* Case-II II2 — Assumption II (`WashingtonCaseIIExactQuotientUnitPower37Source`) from the regular-index
  collapse `LeadingExponentEigenCollapse37` (via `descentUnit_omega32Membership_of_leadingExponent` and
  `caseIIOmega32_assumptionII_of_membership_localPower`) together with the irregular-index local power
  `Lemma98LocalPower37`;
* Case-II II1 — the single-quotient ideal descent `CaseIIRealIdealDescent37`.

`¬ 37 ∣ h⁺` is supplied internally by the proven `Sinnott.flt37_not_dvd_hPlus`.  All other Case-II
content (realness, the rational-mod-`37` congruence, the eigencomponent decomposition, the eigenspace
collapse, `SinnottIndexFormula 37`, the `Δ`-eigenvalue, the high-`λ`-valuation local reduction) is
proven.  This is the cleanest current statement of the remaining FLT-`37` content. -/
theorem fermatLastTheoremFor_thirtyseven_of_leadingExponent
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_realDescent : FLT37.LehmerVandiver.CaseII.CaseIIRealIdealDescent37)
    (hCollapse : LeadingExponentEigenCollapse37)
    (h_localPow : Lemma98LocalPower37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_caseII
    caseII_realDescent
    (caseIIOmega32_assumptionII_of_membership_localPower
      (descentUnit_omega32Membership_of_leadingExponent hCollapse) h_localPow)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
