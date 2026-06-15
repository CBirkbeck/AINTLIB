import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Thaine.Bridge
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealBundle

/-!
# T-FLT37-FINAL: parametric assembly via the Thaine pivot

`fermatLastTheoremFor_thirtyseven_of_thaine` — the final assembly
theorem, parametric on the four Thaine-pivot inputs:

* `id : ClassGroupComponentIdentification 37 (CyclotomicField 37 ℚ)`
* `thaine : ThaineSingleCharDischarge 37 K id 32`
* `reflection : ReflectionOtherDischarge 37 K id 32`
* (existing `CaseIBridge`, `NoSecondOrderIrregularPair 37 32`,
  `CaseIIBridge 37 K 32`)

→ `FermatLastTheoremFor 37`.

The local certificate (`realLocalCert`) is filled by the previously-shipped
`flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete` (in `RealBundle.lean`).

Conceptually: the Cor 8.19 bridge is now decomposed into the eigenspace
identification + Thaine annihilator + reflection (the post-2026-05-06
expert-review pivot route), and assembled via T-PIVOT-1-REFINE
(`cor8_19Bridge_of_componentTrivialities`).

## References

* T-THAINE-6 (`Bridge.lean`) — Thaine + Reflection assembly.
* T-PIVOT-1-REFINE (`UnitClassBridge.lean`) — the content-bearing
  Cor8_19 constructor.
* `BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealBundle` —
  the existing `fermatLastTheoremFor_thirtyseven_of_remaining`.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

/-- **`fermatLastTheoremFor_thirtyseven_of_thaine`** — final FLT37 assembly
via the Thaine pivot route. Given the eigenspace identification + Thaine
single-character discharge + Reflection-other discharge + the existing
Case I/II bridges + numerical second-order check, FLT at exponent 37 holds.

This is the LV-route's final assembly under the 2026-05-06 expert-review
pivot from Sinnott's regulator computation to Thaine's annihilator
theorem. Compared to `fermatLastTheoremFor_thirtyseven_of_remaining`, the
Cor8_19 bridge input is replaced by the more granular triple
`(id, thaine, reflection)` whose `thaine` field carries the substantive
Thaine annihilator content. -/
theorem fermatLastTheoremFor_thirtyseven_of_thaine
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (id : ClassGroupComponentIdentification 37 (CyclotomicField 37 ℚ))
    (thaine : ThaineSingleCharDischarge 37 (CyclotomicField 37 ℚ) id 32)
    (reflection : ReflectionOtherDischarge 37 (CyclotomicField 37 ℚ) id 32)
    (caseI : CaseIBridge 37 (CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_remaining
    (cor8_19Bridge_of_thaineAndReflection (p := 37) (K := CyclotomicField 37 ℚ)
      id thaine reflection)
    caseI noSecondOrderIrregular caseII

end BernoulliRegular

end
