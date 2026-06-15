import BernoulliRegular.FLT37.Eichler.CaseIIKummerAt37Proof
import BernoulliRegular.FLT37.Eichler.CaseIIKummerAway37Proof
import BernoulliRegular.FLT37.Eichler.CaseIIIdealKummerUnramifiedProof

/-!
# Closing the Case-II II1 residual: Washington Lemma 9.2 (`[𝔞(η)] = [𝔞(η⁻¹)]`) is unconditional

Both halves of the ideal-theoretic Washington Lemma 9.1 are now proven:

* `caseIIKummerUnramifiedAt37_proven` — the at-`37` half (primary radical ⟹ unramified at the prime
  above `37`), via the non-unit generalization of flt-regular's `KummersLemma.isUnramified`
  (`NonUnitKummer.isUnramifiedAt_local`) plus the integralization of the field radical; and
* `caseIIKummerUnramifiedAway37_proven` — the away-from-`37` (tame Kummer) half, via the local-DVR
  `p`-th-power-unit argument.

Composing them through `caseIIIdealKummerUnramified37_of_halves` discharges the ideal-theoretic
Lemma 9.1 `CaseIIIdealKummerUnramified37` UNCONDITIONALLY; and through
`caseIIRootClassConjFixed37_of_idealKummer` this discharges the Case-II II1 residual
`CaseIIRootClassConjFixed37` (`[𝔞(η)] = [𝔞(η⁻¹)]`, Washington Lemma 9.2) — and hence the `c = 1`
real-data collapse — with **no remaining hypothesis** beyond the proven `37 ∤ h⁺`.

The circularity that previously blocked this (the unit-form input being equivalent to the class
equality) is broken: the corrected radical's primarity is the *unconditional*
`caseII_correctedRadical_primary_witness`, and its ideal-`37`-th-power structure the *unconditional*
`caseII_correctedRadical_fractionalIdeal_eq`; the Kummer unramifiedness is then the genuine local
content, proven here for the non-unit radical.

It imports only; it does **not** modify any existing file.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

/-- **The ideal-theoretic Washington Lemma 9.1, unconditional** (proven, axiom-clean).

Both local halves are proven: `caseIIKummerUnramifiedAt37_proven` (primarity ⟹ unramified at the
prime above `37`) and `caseIIKummerUnramifiedAway37_proven` (tame Kummer unramifiedness away from
`37`).  Their composition through `caseIIIdealKummerUnramified37_of_halves` is the full ideal-form
Lemma 9.1 with no hypothesis. -/
theorem caseIIIdealKummerUnramified37_proven
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    CaseIIIdealKummerUnramified37 :=
  caseIIIdealKummerUnramified37_of_halves
    caseIIKummerUnramifiedAway37_proven
    caseIIKummerUnramifiedAt37_proven

/-- **Washington Lemma 9.2 for `p = 37`, unconditional** (proven, axiom-clean): the Case-II root
class is conjugation-fixed, `[𝔞(η)] = [𝔞(η⁻¹)]`, over every real Case-II datum.

This **discharges the Case-II II1 residual** `CaseIIRootClassConjFixed37`: it is no longer a
hypothesis but a theorem, obtained from the unconditional ideal-form Lemma 9.1
(`caseIIIdealKummerUnramified37_proven`) via `caseIIRootClassConjFixed37_of_idealKummer`.  Together
with the proven `c·σc = 1` and `c³⁷ = 1`, the anchored class collapses to `c = 1` over real data. -/
theorem caseIIRootClassConjFixed37_proven
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    CaseIIRootClassConjFixed37 :=
  caseIIRootClassConjFixed37_of_idealKummer caseIIIdealKummerUnramified37_proven

end BernoulliRegular.FLT37.Eichler

end
