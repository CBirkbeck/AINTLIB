import BernoulliRegular.FLT37.Eichler.CaseIClose
import BernoulliRegular.FLT37.VandiverProven

/-!
# Wiring the proven first case of FLT for `p = 37` into the top-level chain

The first case of Fermat's Last Theorem for the exponent `37` is now **proved
unconditionally** (axiom-clean) in `FLT37/Eichler/CaseIClose.lean` via the
Eichler argument:

```text
BernoulliRegular.FLT37.Eichler.fltCaseI_thirtyseven :
  ∀ x y z : ℤ, ¬ (37:ℤ) ∣ x → ¬ (37:ℤ) ∣ y → ¬ (37:ℤ) ∣ z →
    x ^ 37 + y ^ 37 = z ^ 37 → False
```

This module connects that proof to the LV-route top-level assembly
`fermatLastTheoremFor_thirtyseven_of_remaining` so that `FermatLastTheoremFor 37`
rests on **only the Case-II descent inputs** — Case I is fully discharged and
carries no remaining hypothesis.

## Case-I input form discharged

The LV-route consumes Case I as a `CaseIBridge 37 K` (see
`FLT37/LehmerVandiver/CaseI/Main.lean`). Its single field is

```text
no_caseI_solution :
  ¬ (37:ℕ) ∣ hPlus K → ∀ ⦃a b c : ℤ⦄, ¬ (37:ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 ≠ c ^ 37
```

i.e. the *raw first-case statement* (no `a^p + b^p ≠ c^p` solution when
`37 ∤ abc`), gated behind a `¬ 37 ∣ h⁺` hypothesis that the LV-route's Vandiver
1934 fill would have used. The Eichler proof needs **no** `¬ 37 ∣ h⁺` input, so
`caseIBridge_thirtyseven_eichler` ignores that hypothesis and fills the field
directly from `fltCaseI_thirtyseven`.

## Resulting top-level dependency

`fermatLastTheoremFor_thirtyseven_of_caseII` below derives
`FermatLastTheoremFor 37` from exactly:

* `caseII_realDescent : CaseIIRealIdealDescent37` — each Case-II anchored
  quotient `𝔞(η)/𝔞₀` descends from an ideal of `𝓞 K⁺` (Case-II II1);
* `caseII_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source` — the
  Case-II descent-equation quotient unit is a `37`th power (Case-II II2);
* `noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32` — the user-owned
  second-order Bernoulli input (`37³ ∤ B_{32·37}`).

`¬ 37 ∣ h⁺` is supplied internally by the proven `Sinnott.flt37_not_dvd_hPlus`,
both for the Cor 8.19 bridge and the Case-II real-generator construction. The
real-local certificate is the proven
`flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete`.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

/-- **The LV-route Case-I bridge for `37`, filled by the proven Eichler first
case.** The `¬ 37 ∣ h⁺` hypothesis of `CaseIBridge.no_caseI_solution` is *not
used*: `fltCaseI_thirtyseven` proves the first case of FLT for `37`
unconditionally, so the bridge's content is discharged with no class-number
input. The three single-prime non-divisibilities are extracted from
`¬ (37:ℤ) ∣ a * b * c` via primality of `37`. -/
def caseIBridge_thirtyseven_eichler :
    BernoulliRegular.CaseIBridge 37 (CyclotomicField 37 ℚ) where
  no_caseI_solution := fun _hPlus a b c hcaseI heq => by
    have hp37 : Prime (37 : ℤ) := by rw [Int.prime_iff_natAbs_prime]; norm_num
    have hx : ¬ (37 : ℤ) ∣ a := fun h =>
      hcaseI ((h.mul_right b).mul_right c)
    have hy : ¬ (37 : ℤ) ∣ b := fun h =>
      hcaseI ((h.mul_left a).mul_right c)
    have hz : ¬ (37 : ℤ) ∣ c := fun h =>
      hcaseI (h.mul_left (a * b))
    exact fltCaseI_thirtyseven a b c hx hy hz heq

/-- **Fermat's Last Theorem for `37`, conditional only on the Case-II descent
inputs.**

Case I is discharged unconditionally by the Eichler first-case proof
`fltCaseI_thirtyseven` (no `¬ 37 ∣ h⁺` hypothesis remains on the Case-I side).
`¬ 37 ∣ h⁺` is supplied internally by the proven `Sinnott.flt37_not_dvd_hPlus`
for the Cor 8.19 bridge and the Case-II real-generator construction.

Remaining mathematical inputs (Case II only):

* `caseII_realDescent` (`CaseIIRealIdealDescent37`): Case-II II1, each anchored
  quotient `𝔞(η)/𝔞₀` descends from an ideal of `𝓞 K⁺`;
* `caseII_exactUnit` (`WashingtonCaseIIExactQuotientUnitPower37Source`): Case-II
  II2, the descent-equation quotient unit is a `37`th power;
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`): the user-owned
  second-order Bernoulli input. -/
theorem fermatLastTheoremFor_thirtyseven_of_caseII
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_realDescent : FLT37.LehmerVandiver.CaseII.CaseIIRealIdealDescent37)
    (caseII_exactUnit :
      FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero 37 := ⟨by decide⟩
  -- Case II: assemble the public Case-II bridge from the real-ideal descent +
  -- exact quotient-unit-power inputs, exactly as the source-faithful endpoint
  -- in `VandiverProven.lean`, with `¬ 37 ∣ h⁺` discharged by the proven
  -- `Sinnott.flt37_not_dvd_hPlus`.
  have caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 := by
    open FLT37.LehmerVandiver.CaseII in
    exact caseIIBridge_thirtyseven_of_descent_step
      (fun hV hSO {_m} D =>
        caseII_descent_step_under_vandiver37
          (washingtonCaseIIAdjacentFixedGenerators37Source_of_realIdealDescent
            Sinnott.flt37_not_dvd_hPlus caseII_realDescent)
          caseII_exactUnit hV hSO D)
  -- Final assembly via the LV-route, with the Case-I bridge filled by the
  -- proven Eichler first case and `cor8_19` filled trivially from `37 ∤ h⁺`.
  exact fermatLastTheoremFor_thirtyseven_of_remaining
    (cor8_19Bridge_of_not_dvd_hPlus 37 (CyclotomicField 37 ℚ)
      Sinnott.flt37_not_dvd_hPlus)
    caseIBridge_thirtyseven_eichler
    noSecondOrderIrregular
    caseII

end BernoulliRegular.FLT37.Eichler

end
