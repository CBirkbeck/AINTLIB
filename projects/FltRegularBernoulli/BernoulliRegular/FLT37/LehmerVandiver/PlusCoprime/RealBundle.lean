import BernoulliRegular.FLT37.LehmerVandiver.Final
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealClosure

/-!
# LV005-real bundle assembly

This file ships a convenience constructor for `FLT37BridgeBundle` that
pre-fills the `realLocalCert` field via the just-shipped axiom-clean
theorem `flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete`,
reducing FLT37 to the four remaining bundle fields:

* `cor8_19` (Sinnott / Washington Cor 8.19, real form)
* `caseI` (Vandiver 1934)
* `noSecondOrderIrregular` (`37³ ∤ B_{32·37}`)
* `caseII` (Washington Theorem 9.4)

`fermatLastTheoremFor_thirtyseven_of_remaining`: clean one-shot
interface — `FermatLastTheoremFor 37` from the four remaining fields.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

/-- **FLT37 bundle from remaining fields.** Construct
`FLT37BridgeBundle` from the four follow-up bridges, with
`realLocalCert` filled by `flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete`. -/
def FLT37BridgeBundle.ofRemaining
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI : CaseIBridge 37 (CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FLT37BridgeBundle where
  realLocalCert :=
    FLT37.flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete
  cor8_19 := cor8_19
  caseI := caseI
  noSecondOrderIrregular := noSecondOrderIrregular
  caseII := caseII

/-- **FLT37 from remaining bridges**: with `realLocalCert` shipped, FLT37
follows from the four remaining bridge fields. -/
theorem fermatLastTheoremFor_thirtyseven_of_remaining
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI : CaseIBridge 37 (CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_bundle
    (FLT37BridgeBundle.ofRemaining cor8_19 caseI noSecondOrderIrregular caseII)

end BernoulliRegular

end
