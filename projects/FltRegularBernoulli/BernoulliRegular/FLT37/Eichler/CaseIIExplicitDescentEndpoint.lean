import BernoulliRegular.FLT37.VandiverProven
import BernoulliRegular.FLT37.Eichler.CaseIIExplicitDescent

/-!
# FLT37 endpoint with the membership-free Case-II descent-unit input

This file composes the membership-free Case-II reduction of
`CaseIIExplicitDescent.lean` with the FLT37 capstone of `VandiverProven.lean`, giving a top-level
`FermatLastTheoremFor 37` endpoint whose Case-II descent-unit input is the **bare residue
equations** (Washington Lemma 9.8 / 9.9, `caseIISigmaAntiDescent_residueEqns`) together with the
single-index local power (`Lemma98LocalPower37`) — **with neither the cyclotomic-membership conjunct
`w ∈ C⁺` nor the analytic `SinnottIndexFormula 37`**.

It imports only; it does **not** modify any existing file.

## Why this is the cleaner endpoint

The existing endpoint
`fermatLastTheoremFor_thirtyseven_of_caseIUnramified_realIdealDescent_exactUnit_noSecondOrder`
(`VandiverProven.lean`) takes Assumption II
(`WashingtonCaseIIExactQuotientUnitPower37Source`) as a black-box input.  The standard route to
Assumption II ran through `Cor815RealDescentData37` / the reduced provenance Props, all of which
carry the cyclotomic membership `w ∈ C⁺` of the descent unit (Washington §9.1's explicit `η_a`
identification) **and** Sinnott's index formula.  `CaseIIExplicitDescent.lean` proves that the
membership is redundant: the K-side single-index expansion needs only the eigenspace collapse
`Cor815EigenCollapseAt`, which follows membership-free from the residue equations via the Case-I
real-`p`-th-root descent.  This file threads that membership-free Assumption II into the capstone.

## What this file proves (real, axiom-clean Lean)

* `fermatLastTheoremFor_thirtyseven_of_caseIUnramified_realIdealDescent_residueEqns_noSecondOrder` —
  `FermatLastTheoremFor 37` from
  - `caseI_LK` (`CaseIAntiKummerLKUnramified`) — the Case-I σ-anti Kummer unramifiedness;
  - `caseII_realDescent` (`CaseIIRealIdealDescent37`) — the Case-II II1 ideal descent;
  - `caseII_residueEqns` (`caseIISigmaAntiDescent_residueEqns`) — Washington Lemma 9.8 / 9.9's
    half-range residue equations on the canonical descent unit (replacing Assumption II, **without**
    cyclotomic membership or Sinnott);
  - `caseII_localPow` (`Lemma98LocalPower37`) — Washington Lemma 9.8's single-index mod-`𝔩` Kummer
    congruence; and
  - `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`) — the user-owned second-order
    Bernoulli input.

  `¬ 37 ∣ h⁺` is discharged everywhere by the proven `Sinnott.flt37_not_dvd_hPlus`; the descent
  unit's **realness** is the unconditional `CaseIISigmaAntiDescent` result.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–§9.2 (Theorem 9.4), Lemma
  9.8 / 9.9, Corollary 8.15.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII in
/-- **FLT37 with the membership-free Case-II descent-unit input** (proven, axiom-clean).

`FermatLastTheoremFor 37` from the Case-I unramifiedness, the Case-II II1 ideal descent, the bare
Case-II **residue equations** + single-index local power (in place of Assumption II — **no**
cyclotomic membership `w ∈ C⁺`, **no** `SinnottIndexFormula 37`), and the user-owned second-order
input.

Assumption II (`WashingtonCaseIIExactQuotientUnitPower37Source`) is produced internally by
`caseIIExplicitDescent_assumptionII_of_residueEqns` (the descent unit's realness is the
unconditional `CaseIISigmaAntiDescent` result; its eigenspace collapse follows membership-free from
the residue equations), then fed to
`fermatLastTheoremFor_thirtyseven_of_caseIUnramified_realIdealDescent_exactUnit_noSecondOrder`. -/
theorem fermatLastTheoremFor_thirtyseven_of_caseIUnramified_realIdealDescent_residueEqns_noSO
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseI_LK : FLT37.LehmerVandiver.CaseI.CaseIAntiKummerLKUnramified)
    (caseII_realDescent : FLT37.LehmerVandiver.CaseII.CaseIIRealIdealDescent37)
    (caseII_residueEqns : caseIISigmaAntiDescent_residueEqns)
    (caseII_localPow : Lemma98LocalPower37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_caseIUnramified_realIdealDescent_exactUnit_noSecondOrder
    caseI_LK caseII_realDescent
    (caseIIExplicitDescent_assumptionII_of_residueEqns caseII_residueEqns caseII_localPow)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
