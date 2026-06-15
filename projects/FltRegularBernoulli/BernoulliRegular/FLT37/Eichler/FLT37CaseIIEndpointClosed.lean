import BernoulliRegular.FLT37.Eichler.CaseIIRootClassConjFixedClosed
import BernoulliRegular.FLT37.Eichler.CaseIILocalPowerStrict

/-!
# FLT for `p = 37` with the Case-II II1 residual discharged

Washington Lemma 9.2 (the Case-II II1 conjugation-fixedness `[𝔞(η)] = [𝔞(η⁻¹)]`) is now a proven
theorem, `caseIIRootClassConjFixed37_proven` (both halves of the ideal-theoretic Lemma 9.1 — the
at-`37` primary half and the away-from-`37` tame-Kummer half — are proven, and the non-unit
generalization of flt-regular's `KummersLemma.isUnramified` is closed).  Feeding it into the
cleanest endpoint `fermatLastTheoremFor_thirtyseven_of_genuineResiduals_section91Identification`
**discharges the II1 hypothesis**, so FLT for `37` rests on a strictly smaller residual set.

It imports only; it does **not** modify any existing file.

## Remaining residuals after II1 is discharged

`fermatLastTheoremFor_thirtyseven_of_caseII_postII1` derives `FermatLastTheoremFor 37` from:

* `caseII_realDescent` (`CaseIIRealSingleRootDescentPreservesReality37`) — **R2**, the
  reality-preserving single-root descent (the symmetric-Vandermonde reassembly landing the next
  datum in `RealCaseIIData37` at `m' < m`);
* `caseII_leadingExp` (`LeadingExponentEigenCollapse37`) — **R3**, the leading-`λ`-exponent
  local→global eigencomponent collapse (regular indices, Ex. 8.10/8.11);
* `caseII_section91Ident` (`CaseIISection91DescentUnitIdentification37`) — **R4(i)**, the §9.1
  Lemma-9.8-opening residue identification `ε₁/ε₂ ≡ δ (mod 𝔩)`;
* `caseII_lehmerVandiverDvdZ` (`CaseIILehmerVandiverDvdZ37`) — **R4(ii)**, the genuine `ℓ ∣ z`
  datum (Washington Lemma 9.7, `ℓ = 149 < 37²−37`);
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`) — the carried second-order Bernoulli
  input.

Everything else — Case I (Eichler), `37 ∤ h⁺`, the realness of `ε₁/ε₂`, the rational-mod-`37`
congruence, the eigenspace/Vandermonde apparatus, `SinnottIndexFormula 37`, the `Δ`-eigenvalue, the
local-power discharge through the §9.1 producer, the `RealCaseIIData37` base producer, **and now the
entire Case-II II1 (Washington Lemma 9.2)** — is proven.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-- **FLT for `37`, with the Case-II II1 residual discharged** (proven, axiom-clean given the four
remaining named inputs + the carried second-order Bernoulli Prop).

Composes the proven II1 `caseIIRootClassConjFixed37_proven` (Washington Lemma 9.2) into
`fermatLastTheoremFor_thirtyseven_of_genuineResiduals_section91Identification`, removing the II1
hypothesis.  FLT-`37` now rests on: R2 (reality descent), R3 (leading-exponent collapse), R4 (the
§9.1 identification + the `ℓ ∣ z` datum), and the carried second-order condition. -/
theorem fermatLastTheoremFor_thirtyseven_of_caseII_postII1
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_leadingExp : LeadingExponentEigenCollapse37)
    (caseII_section91Ident : CaseIISection91DescentUnitIdentification37)
    (caseII_lehmerVandiverDvdZ : CaseIILehmerVandiverDvdZ37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_genuineResiduals_section91Identification
    caseIIRootClassConjFixed37_proven
    caseII_realDescent
    caseII_leadingExp
    caseII_section91Ident
    caseII_lehmerVandiverDvdZ
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
