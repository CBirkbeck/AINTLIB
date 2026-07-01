import BernoulliRegular.FLT37.Final
import BernoulliRegular.UnitQuotient.Washington83UnitForward
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.BridgeAssembly
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Unconditional
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.RealGeneratorBridge
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.ProductDescent

/-!
# Vandiver's conjecture for `37` (plus-side), proven

`Washington83UnitForward.lean` proves `flt37_not_dvd_hPlus : ¬ 37 ∣ h⁺(ℚ(ζ₃₇))` unconditionally
(axiom-clean) via the Washington §8.3 unit-side route: the eigenspace/index forward bridge
(Theorem 8.14), the class-form Theorem 8.16, the proven real-local certificate at the irregular
index `32`, and the computed first-order Bernoulli table.  This file packages that as
`Vandiver37PlusCoprime` — the regularity input consumed by the FLT37 Case-I/II decomposition.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.3.
-/

@[expose] public section

open NumberField

namespace BernoulliRegular.FLT37

variable [Fact (Nat.Prime 37)] [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **Vandiver's conjecture for `37` (plus-side): `37` is coprime to `h⁺(ℚ(ζ₃₇))`.**
Immediate from the unconditional `flt37_not_dvd_hPlus`. -/
theorem vandiver37PlusCoprime_proven : Vandiver37PlusCoprime :=
  vandiver37PlusCoprime_iff_not_dvd_hPlus.mpr Sinnott.flt37_not_dvd_hPlus

/-- **The σ-stable Case-II II1 source is UNCONDITIONAL.** The reviewer's (2026-05-27-3)
option-B replacement for the unsatisfiable raw-quotient `CaseIIRealIdealDescent37`: the
σ-stable pair-product anchored real-generator source `CaseIISigmaPairAnchoredSource37` is
discharged outright from the proven `Sinnott.flt37_not_dvd_hPlus` (= `37 ∤ h⁺`, i.e. the
`37`-coprimality of `Cl(𝓞 K⁺)`). This closes the **producer** half of the σ-stable Case-II II1
target: for every real Case-II datum the adjacent conjugate-paired real generators with the
σ-stable cross identity exist, with no remaining hypothesis. The only remaining Case-II open
content is the Washington 9.4 **consumer** (the pair-product descent step). `Type`-valued
because the source produces the generator *data*. -/
noncomputable def caseII_sigmaPairAnchoredSource_proven :
    FLT37.LehmerVandiver.CaseII.CaseIISigmaPairAnchoredSource37 :=
  FLT37.LehmerVandiver.CaseII.caseII_sigma_pair_anchored_source_of_VC
    ((by decide : Nat.Prime 37).coprime_iff_not_dvd.mpr Sinnott.flt37_not_dvd_hPlus)

/-- **Fermat's Last Theorem for `37`, with the `¬ 37 ∣ h⁺` lynchpin discharged.** The shared
Vandiver input to the Case-I/Case-II decomposition is now the proven `flt37_not_dvd_hPlus`, so
`FermatLastTheoremFor 37` reduces to exactly the Case-I class-equality discharge, the Case-II
bridge, and the (user-owned) second-order irregularity input. -/
theorem fermatLastTheoremFor_thirtyseven_of_caseI_caseII_noSO
    (caseI_classEq : FLT37.LehmerVandiver.CaseI.CaseIClassEqDischarge 37 (CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_not_dvd_hPlus Sinnott.flt37_not_dvd_hPlus
    caseI_classEq noSecondOrderIrregular caseII

/-- **FLT37 via the AK5a / Washington-9.4-descent route, with `¬ 37 ∣ h⁺` discharged.** This
is the reviewer's preferred Case-I/II decomposition (`AK5a_PrincipalMinusIdeals` + the Case-II
descent step), now with the `Vandiver37PlusCoprime` input supplied by the proven
`vandiver37PlusCoprime_proven` — so the class-side Kučera/Thaine + Herbrand/Ribet derivation of
`¬ 37 ∣ h⁺` is no longer needed on this path. Remaining inputs are exactly the Case-I AK5a
principal-minus theorem, the Case-II descent step, and the user-owned second-order data. -/
theorem fermatLastTheoremFor_thirtyseven_of_AK5a_caseIIDescent_noSecondOrder
    (caseI_AK5a :
      FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
        (p := 37) (K := CyclotomicField 37 ℚ))
    (caseII_step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        FLT37.LehmerVandiver.CaseII.CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (FLT37.LehmerVandiver.CaseII.CaseIIData37 (CyclotomicField 37 ℚ) m'))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_vandiver37_AK5a_caseIIDescent_noSecondOrder
    vandiver37PlusCoprime_proven caseI_AK5a caseII_step noSecondOrderIrregular

/-- **FLT37 from Case-I AK5a, the Case-II II1 real-ideal descent, the Case-II II2
exact quotient-unit power, and the (user-owned) second-order input** — with `¬ 37 ∣ h⁺`
discharged by the proven `Sinnott.flt37_not_dvd_hPlus`.

The Case-II II1 input is now the concrete real-ideal descent `CaseIIRealIdealDescent37`
(that each anchored quotient `𝔞(η)/𝔞₀` descends from an ideal of `𝓞 K⁺`): the proven
`¬ 37 ∣ h⁺` turns it into the Washington adjacent fixed-generator source via
`washingtonCaseIIAdjacentFixedGenerators37Source_of_realIdealDescent`, then feeds the
Washington 9.4 descent step. -/
theorem fermatLastTheoremFor_thirtyseven_of_AK5a_realIdealDescent_exactUnit_noSecondOrder
    (caseI_AK5a :
      FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals
        (p := 37) (K := CyclotomicField 37 ℚ))
    (caseII_realDescent : FLT37.LehmerVandiver.CaseII.CaseIIRealIdealDescent37)
    (caseII_exactUnit :
      FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_AK5a_caseIIDescent_noSecondOrder
    caseI_AK5a
    (fun hV hSO {_m} D ↦
      FLT37.LehmerVandiver.CaseII.caseII_descent_step_under_vandiver37
        (FLT37.LehmerVandiver.CaseII.washingtonCaseIIAdjacentFixedGenerators37Source_of_realIdealDescent
          Sinnott.flt37_not_dvd_hPlus caseII_realDescent)
        caseII_exactUnit hV hSO D)
    noSecondOrderIrregular

/-- **FLT37 from the source-faithful Case-I/Case-II inputs, with `¬ 37 ∣ h⁺` banked
everywhere.** The remaining mathematical inputs are exactly:

* `caseI_LK` (`CaseIAntiKummerLKUnramified`): the σ-anti Kummer extension is unramified
  for each Case-I FLT37 datum;
* `caseII_realDescent` (`CaseIIRealIdealDescent37`): each Case-II anchored quotient
  `𝔞(η)/𝔞₀` descends from an ideal of `𝓞 K⁺`;
* `caseII_exactUnit` (`WashingtonCaseIIExactQuotientUnitPower37Source`): the Case-II
  descent-equation quotient unit is a `37`th power;
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`): the user-owned
  second-order Bernoulli input.

`¬ 37 ∣ h⁺` (Vandiver-37) is discharged by the proven `Sinnott.flt37_not_dvd_hPlus`
on **both** the Case-I principalisation (via
`AK5a_PrincipalMinusIdeals_of_CaseIAntiKummerLKUnramified_and_not_dvd_hPlus`) and the
Case-II II1 real-generator construction. -/
theorem fermatLastTheoremFor_thirtyseven_of_caseIUnramified_realIdealDescent_exactUnit_noSecondOrder
    (caseI_LK : FLT37.LehmerVandiver.CaseI.CaseIAntiKummerLKUnramified)
    (caseII_realDescent : FLT37.LehmerVandiver.CaseII.CaseIIRealIdealDescent37)
    (caseII_exactUnit :
      FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_AK5a_realIdealDescent_exactUnit_noSecondOrder
    (FLT37.LehmerVandiver.CaseI.AK5a_PrincipalMinusIdeals_of_CaseIAntiKummerLKUnramified_and_not_dvd_hPlus
      Sinnott.flt37_not_dvd_hPlus caseI_LK)
    caseII_realDescent caseII_exactUnit noSecondOrderIrregular

end BernoulliRegular.FLT37

end
