import BernoulliRegular.FLT37.Eichler.CaseII.RootClass.RootClassConjugateFixed
import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.LambdaExponentCollapseToOmega32

/-!
# Fermat's Last Theorem for `p = 37`, reduced to the four genuine (non-vacuous) Case-II residuals

This module composes the proven chains into the single cleanest statement of FLT for `p = 37`,
exposing **exactly** the remaining mathematical content as four precisely-named, **genuinely-true,
non-vacuous** leaves over real data, plus the user-owned second-order Bernoulli input.

Everything else is proven and axiom-clean:
* **Case I** — `fltCaseI_thirtyseven` (Eichler argument), unconditional;
* `¬ 37 ∣ h⁺` — `Sinnott.flt37_not_dvd_hPlus` (Vandiver for 37);
* the **realness** of the descent unit `ε₁/ε₂` (`caseIISigmaAntiDescent_quotient_unitsMap`);
* the rational-mod-`37` congruence (`caseII_quotient_sub_intCast_mem_37`);
* the `c = 1` collapse over real data (`caseII_anchored_class_eq_one_of_pthPower`, from Lemma-9.2
  conj-fixedness `σc = c` + the proven anti-fixedness `c·σc = 1` + `c³⁷ = 1`);
* the automatic eigencomponent decomposition, the membership-free eigenspace collapse,
  `SinnottIndexFormula 37`, the `Δ`-action eigenvalue, the high-`λ`-valuation local reduction
  (`caseIILeadingExponent_completedLogArg_mem_lambdaIdeal_pow_pred`);
* the `RealCaseIIData37` producer at the base (`exists_realCaseIIData37_of_caseII_int_solution`).

It imports only; it does **not** modify any existing file.

## The four genuine residuals

`fermatLastTheoremFor_thirtyseven_of_genuineResiduals` derives `FermatLastTheoremFor 37` from:

1. `caseII_classConjFixed : CaseIIRootClassConjFixed37` — **Case-II II1**, Washington Lemma 9.2:
   the root class is conjugation-fixed, `[𝔞(η)] = [𝔞(η⁻¹)]` over real data (the genuinely-true,
   non-vacuous form — the `-ζ^a` twist lives at the unit/ideal level, so this is NOT the
   provably-false `CaseIIRootRatioPthPower37`).  Reduces to the corrected anti-fixed primary radical
   being a `37`-th power (Hilbert 94 / Kummer, under `37 ∤ h⁺`).

2. `caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37` — **Case-II descent**, the
   single-root Washington descent construction yields a *real* datum at `m' < m` (reality preserved
   through the norm-form / Vandermonde reassembly), so the descent iterates and `c = 1` applies at
   every level.

3. `caseII_leadingExp : LeadingExponentEigenCollapse37` — **Case-II II2 (regular indices)**,
   Washington Lemma 9.9's regular-index collapse (the leading-`λ`-exponent / Exercise-8.11 content):
   high `λ`-valuation of the descent unit's completed log forces the regular eigencomponents to
   vanish, putting the descent unit's class in the `ω³²`-eigenspace.  Second-order-condition-free.

4. `caseII_localPow : Lemma98LocalPower37` — **Case-II II2 (irregular index)**, Washington Lemma
   9.8's single-index mod-`𝔩` Kummer congruence for the surviving `i = 32` eigencomponent.

plus `noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32` — the carried second-order
Bernoulli input (Kellner Prop 2.7, `37³ ∤ B_{32·37}`), **not** a leaf to discharge.

Residuals 3+4 produce **Assumption II** (`WashingtonCaseIIExactQuotientUnitPower37Source`) via
`caseIIOmega32_assumptionII_of_membership_localPower ∘ descentUnit_omega32Membership_of_leadingExponent`;
residuals 1+2 then drive the `c = 1` real-data descent to the Case-II contradiction.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–§9.2 (Theorems 9.4/9.5,
  Lemmas 9.1/9.2/9.8/9.9), Exercises 8.10/8.11, Corollaries 8.15/8.23.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-- **Fermat's Last Theorem for `37`, reduced to the four genuine non-vacuous Case-II residuals**
(proven, axiom-clean given the four named inputs + the carried second-order Bernoulli Prop).

This is the cleanest current statement of the remaining FLT-`37` content.  Case I is the proven
unconditional Eichler first case; `¬ 37 ∣ h⁺` is proven; the entire Case-II engine (realness,
rational-mod-`37`, the `c = 1` real-data collapse, the eigenspace/Vandermonde machinery, the
high-`λ`-valuation reduction, the `RealCaseIIData37` base producer) is proven.  What remains is the
four genuine, non-vacuous residuals over real data:

* `CaseIIRootClassConjFixed37` (Lemma 9.2 root-class conj-fixedness);
* `CaseIIRealSingleRootDescentPreservesReality37` (reality-preserving single-root descent);
* `LeadingExponentEigenCollapse37` (Lemma 9.9 regular-index collapse, Assumption II);
* `Lemma98LocalPower37` (Lemma 9.8 single-index local power, Assumption II).

Composes `fermatLastTheoremFor_thirtyseven_of_rootClassConjFixed` (residuals 1+2, the II1 real-data
descent) with Assumption II produced from residuals 3+4
(`caseIIOmega32_assumptionII_of_membership_localPower ∘
descentUnit_omega32Membership_of_leadingExponent`). -/
theorem fermatLastTheoremFor_thirtyseven_of_genuineResiduals
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_leadingExp : LeadingExponentEigenCollapse37)
    (caseII_localPow : Lemma98LocalPower37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_rootClassConjFixed
    caseII_classConjFixed
    caseII_realDescent
    (caseIIOmega32_assumptionII_of_membership_localPower
      (descentUnit_omega32Membership_of_leadingExponent caseII_leadingExp) caseII_localPow)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
