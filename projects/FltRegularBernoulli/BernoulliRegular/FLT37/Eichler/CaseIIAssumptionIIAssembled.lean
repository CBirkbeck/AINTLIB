import BernoulliRegular.FLT37.Eichler.Reduction.FLT37PostII1Reduction
import BernoulliRegular.FLT37.Eichler.CaseIIEx811EigenVandermonde

/-!
# [FLT37-CASEII] Assumption II assembled over the genuine descent data, with **R3 PROVEN**

This file performs the post-R3 consolidation of the Case-II descent for Fermat's Last Theorem at
`p = 37`.  Washington Lemma 9.9's regular-index collapse (R3,
`LeadingExponentEigenCollapse37`) is now a **proven theorem**, so the descent unit's ω³²-eigenspace
membership (`DescentUnitOmega32Membership37`) is proven, and **Assumption II**
(`WashingtonCaseIIExactQuotientUnitPower37Source`) is reduced to the remaining Lemma-9.8 content
(R4) alone.

It imports only — it does **not** modify any existing file.

## What R3 being proven banks (reuse — do not re-derive)

* **R3 closed.**  `caseII_leadingExponentEigenCollapse37_proven : LeadingExponentEigenCollapse37`
  (the `r3_proven` of the task) is `leadingExponentEigenCollapse37_of_eigenVandermonde` applied to
  the proven Exercise-8.11 eigen↔Vandermonde compatibility `caseIIEx811EigenVandermonde37_proven`.

* **R3 membership half proven.**  `caseII_descentUnitOmega32Membership37_proven :
  DescentUnitOmega32Membership37` is `descentUnit_omega32Membership_of_leadingExponent` at the
  proven R3.  This is Washington Lemma 9.9's regular-index collapse over the **unit**-realness of
  `ε₁/ε₂` (available over *bare* `CaseIIData37` via `caseIISigmaAntiDescent_quotient_unitsMap`), so
  it needs no `RealCaseIIData37` datum.

## Assumption II, reduced to R4 alone (the membership half discharged by the proven R3)

`caseIIOmega32_assumptionII_of_localPower` produces Assumption II from the single Lemma-9.8 local
power `Lemma98LocalPower37` (R4), with the regular-index collapse (R3) supplied internally.
`caseIIOmega32_assumptionII_of_section91Ident_dvdZ` produces it from the genuine §9.1 residue
identification `CaseIISection91DescentUnitIdentification37` (R4(i)) and the `ℓ ∣ z` datum
`CaseIILehmerVandiverDvdZ37` (R4(ii)), routing the local power through the **proven** §9.1 producer
(`caseII_localPower_of_dvd_z`, never Assumption II).

## The consolidated FLT37 endpoint

`fermatLastTheoremFor_thirtyseven_of_caseII_postR3` derives `FermatLastTheoremFor 37` from
**R2 + R4(i) + R4(ii) + carried Kellner** — Case I (Eichler), `¬ 37 ∣ h⁺` (Vandiver for 37), the
Case-II II1 (Washington Lemma 9.2, `caseIIRootClassConjFixed37_proven`), and now **R3** (Washington
Lemma 9.9 regular indices) are all proven and supplied internally.  This is
`fermatLastTheoremFor_thirtyseven_of_caseII_postII1` with its R3 hypothesis discharged.

## The bare-vs-real resolution (honest, soundness-first)

The bare `Lemma98LocalPower37` (over *free* units `ε₁, ε₂, ε₃`) is **false** as universally
quantified (logged B2 `CASEII-LEMMA98-LOCALPOWER`: over free units `ε₁/ε₂` need not be a `37`-th
power mod `lv149`; the descent never feeds free units — `exists_solution_of_etaZeroSpanSingletons`
constructs `ε₁/ε₂` as a producer ratio of root-ideal generators).  Hence it is **not** discharged
from the proven real-data R4 (`caseII_real_localPower_section91` is the local power of the
*producer-constructed* `δ` over `RealCaseIIData37`, not of a free `ε₁/ε₂`).  The genuine path is
the real-data route: the §9.1 residue identification `CaseIISection91DescentUnitIdentification37`
(R4(i)) identifies the abstract `ε₁/ε₂` with the producer `δ` mod `lv149`, under the genuine
`ℓ ∣ z` datum (R4(ii)).

These two named residuals R4(i)/R4(ii) are **kept as explicit hypotheses** here; this file does
**not** attempt to prove the false bare local power, and does **not** launder the R4(ii) `ℓ ∣ z`
datum (logged B2 `R4-ellz`: also over-general on the free-unit telescope — the genuine `ℓ ∣ z`
lives at the integer base of the descent and propagates through the reality-preserving R2
construction, not over a free abstract `CaseIIData37`).  So the endpoint
`fermatLastTheoremFor_thirtyseven_of_caseII_postR3` is a **conditional** theorem on
R2 + R4(i) + R4(ii) + carried Kellner — exactly the residual set of
`fermatLastTheoremFor_thirtyseven_of_caseII_postII1` minus the now-proven R3.  Consequently this
consolidation banks R3 (removing it from the residual set); Assumption II is **not** fully proven
here — see the file-level report.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–§9.2 (Theorem 9.5, Lemmas
  9.7/9.8/9.9), Exercises 8.10/8.11, Corollary 8.15.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-! ## 1. R3 (Washington Lemma 9.9 regular-index collapse) is PROVEN -/

/-- **R3 closed: the leading-exponent eigencomponent collapse holds** (proven, axiom-clean).

`LeadingExponentEigenCollapse37` — Washington Lemma 9.9's regular-index collapse for `p = 37` (the
Galois-graded leading-`λ`-coefficient computation of Exercise 8.11) — is the composition
`leadingExponentEigenCollapse37_of_eigenVandermonde caseIIEx811EigenVandermonde37_proven`.  This is
the `r3_proven` of the consolidation: with the proven eigen↔Vandermonde compatibility, the
matrix-kernel collapse forces every regular eigencoordinate of the descent unit's mod-`37` free part
to vanish. -/
theorem caseII_leadingExponentEigenCollapse37_proven
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    LeadingExponentEigenCollapse37 :=
  leadingExponentEigenCollapse37_of_eigenVandermonde caseIIEx811EigenVandermonde37_proven

/-- **R3 membership half proven: the descent unit lies in the ω³²-eigenspace** (axiom-clean).

`DescentUnitOmega32Membership37` — for a real unit `u` whose `K`-image is `≡` a rational integer
mod `37`, the mod-`37` free-part class `realUnitToFreePartModP u` lands in the irregular
`ω³²`-eigenspace — follows from the proven R3 via
`descentUnit_omega32Membership_of_leadingExponent`.  The realness input is the **unit**-realness of
`ε₁/ε₂`, available over *bare* `CaseIIData37`, so this needs no `RealCaseIIData37` datum. -/
theorem caseII_descentUnitOmega32Membership37_proven
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    DescentUnitOmega32Membership37 :=
  descentUnit_omega32Membership_of_leadingExponent caseII_leadingExponentEigenCollapse37_proven

/-! ## 2. Assumption II from R4 alone (R3 membership half supplied by the proven collapse) -/

/-- **Assumption II from the Lemma-9.8 local power alone** (proven, axiom-clean — R3 supplied
internally).

`WashingtonCaseIIExactQuotientUnitPower37Source` (Assumption II: the descent unit `ε₁/ε₂` is a
`37`-th power) follows from the single remaining R4 input `Lemma98LocalPower37` (Washington Lemma
9.8's single-index mod-`𝔩` Kummer congruence), with Washington Lemma 9.9's regular-index collapse
(R3) discharged by the proven `caseII_descentUnitOmega32Membership37_proven`.

This is `caseIIOmega32_assumptionII_of_membership_localPower` with its first (membership) hypothesis
proven, isolating the remaining Case-II II2 content to the Lemma-9.8 local power.  NB the bare
`Lemma98LocalPower37` is over-general (false on the free-unit telescope, B2
`CASEII-LEMMA98-LOCALPOWER`); the **sound** consumer is
`caseIIOmega32_assumptionII_of_section91Ident_dvdZ` below, which obtains it from the genuine
R4(i)+R4(ii) via the proven §9.1 producer.  This lemma is the intermediate that bridges the two. -/
theorem caseIIOmega32_assumptionII_of_localPower
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_localPow : Lemma98LocalPower37) :
    WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIIOmega32_assumptionII_of_membership_localPower
    caseII_descentUnitOmega32Membership37_proven h_localPow

/-- **Assumption II from the §9.1 identification + the `ℓ ∣ z` datum** (proven, axiom-clean — R3
supplied internally, local power routed through the proven §9.1 producer).

`WashingtonCaseIIExactQuotientUnitPower37Source` from the two **sound** genuine R4 residuals:

* `caseII_section91Ident : CaseIISection91DescentUnitIdentification37` — R4(i), the §9.1 residue
  identification `ε₁/ε₂ ≡ δ (mod lv149)` of the abstract descent unit with the proven producer unit
  `δ` (Washington Lemma 9.8's `η_a ≡ ω ρ_a^{-37}` opening, which uses `ℓ ∣ z`);
* `caseII_dvdZ : CaseIILehmerVandiverDvdZ37` — R4(ii), the genuine `ℓ ∣ z` datum (Washington Lemma
  9.7, non-vacuous: `149 ≡ 1 (mod 37)` and `149 < 37² − 37`).

The Lemma-9.8 local power `Lemma98LocalPower37` is obtained from these via
`caseII_localPower_of_dvd_z` (the §9.1 producer `δ` is a `37`-th power mod `lv149` **by
construction**, so the identification transports the property to `ε₁/ε₂` — never through Assumption
II) and `lemma98LocalPower37_of_strict`.  The regular-index collapse (R3) is the proven
`caseII_descentUnitOmega32Membership37_proven`.  No false bare local power is used. -/
theorem caseIIOmega32_assumptionII_of_section91Ident_dvdZ
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_section91Ident : CaseIISection91DescentUnitIdentification37)
    (caseII_dvdZ : CaseIILehmerVandiverDvdZ37) :
    WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIIOmega32_assumptionII_of_localPower
    (lemma98LocalPower37_of_strict
      (caseII_localPower_of_dvd_z caseII_section91Ident) caseII_dvdZ)

/-! ## 3. The consolidated FLT37 endpoint: R2 + R4(i) + R4(ii) + carried Kellner -/

/-- **Fermat's Last Theorem for `37`, with R3 (and II1, Case I, `¬ 37 ∣ h⁺`) all proven**
(proven, axiom-clean given the remaining named inputs + the carried second-order Bernoulli Prop).

`FermatLastTheoremFor 37` from the genuine remaining Case-II residuals:

* `caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37` — **R2**, the
  reality-preserving single-root descent (produces the next `RealCaseIIData37` at `m' < m`);
* `caseII_section91Ident : CaseIISection91DescentUnitIdentification37` — **R4(i)**, the §9.1
  Lemma-9.8-opening residue identification `ε₁/ε₂ ≡ δ (mod 𝔩)`;
* `caseII_lehmerVandiverDvdZ : CaseIILehmerVandiverDvdZ37` — **R4(ii)**, the genuine `ℓ ∣ z` datum
  (Washington Lemma 9.7);
* `noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32` — the carried second-order Bernoulli
  input (Kellner Prop 2.7), **not** a leaf to discharge.

Everything else is proven and supplied internally: Case I (Eichler, `fltCaseI_thirtyseven`),
`¬ 37 ∣ h⁺` (`Sinnott.flt37_not_dvd_hPlus`), the Case-II II1 (Washington Lemma 9.2,
`caseIIRootClassConjFixed37_proven`), and now **R3** (Washington Lemma 9.9 regular indices,
`caseII_leadingExponentEigenCollapse37_proven`).  This is
`fermatLastTheoremFor_thirtyseven_of_caseII_postII1` with its R3 hypothesis discharged — the post-R3
consolidation of the Case-II descent. -/
theorem fermatLastTheoremFor_thirtyseven_of_caseII_postR3
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_section91Ident : CaseIISection91DescentUnitIdentification37)
    (caseII_lehmerVandiverDvdZ : CaseIILehmerVandiverDvdZ37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_caseII_postII1
    caseII_realDescent
    caseII_leadingExponentEigenCollapse37_proven
    caseII_section91Ident
    caseII_lehmerVandiverDvdZ
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
