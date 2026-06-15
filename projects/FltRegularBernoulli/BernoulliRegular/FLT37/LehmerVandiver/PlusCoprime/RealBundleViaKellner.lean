import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealBundle
import BernoulliRegular.BernoulliFast.KellnerSecondOrder
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.BridgeAssembly

/-!
# Bundle assembly via parametric Kellner Prop 2.7

Per the 2026-05-07 reviewer followup (patch 2), provide a bundle
constructor that takes the parametric Kellner Prop 2.7 hypothesis
`KellnerProp27_thirtyseven_thirtytwo` instead of the raw
`NoSecondOrderIrregularPair 37 32`. This makes the Kellner pathway —
avoiding direct computation of `B_{1184}` — directly usable from
`FermatLastTheoremFor 37` callers.

The discharge `noSecondOrderIrregularPair_thirtyseven_thirtytwo_of_kellner`
(in `BernoulliFast/KellnerSecondOrder.lean`) bridges the parametric
Kellner to the existing `NoSecondOrderIrregularPair 37 32` predicate,
so this constructor just feeds through.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

/-- **FLT37 bundle from remaining fields, with Kellner**: identical to
`FLT37BridgeBundle.ofRemaining` but takes `KellnerProp27_thirtyseven_thirtytwo`
in place of `NoSecondOrderIrregularPair 37 32`. -/
def FLT37BridgeBundle.ofRemainingViaKellner
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI : CaseIBridge 37 (CyclotomicField 37 ℚ))
    (kellner : KellnerProp27_thirtyseven_thirtytwo)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FLT37BridgeBundle :=
  FLT37BridgeBundle.ofRemaining cor8_19 caseI
    (noSecondOrderIrregularPair_thirtyseven_thirtytwo_of_kellner kellner)
    caseII

/-- **FLT37 via Kellner**: with `realLocalCert` shipped, `FermatLastTheoremFor 37`
follows from the four remaining bridge fields, where the second-order
non-irregularity is supplied via the parametric Kellner Prop 2.7
specialised to `(37, 32)`. -/
theorem fermatLastTheoremFor_thirtyseven_of_remainingViaKellner
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI : CaseIBridge 37 (CyclotomicField 37 ℚ))
    (kellner : KellnerProp27_thirtyseven_thirtytwo)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_bundle
    (FLT37BridgeBundle.ofRemainingViaKellner cor8_19 caseI kellner caseII)

/-- **FLT37 from three bridges**: with `realLocalCert` and the FLT37
second-order Bernoulli target both supplied internally, `FermatLastTheoremFor 37` follows from
the three remaining bridge fields:

* `cor8_19` : Cor 8.19 contrapositive (`cert ⟹ ¬p∣h⁺`),
* `caseI` : Vandiver 1934 Theorem 1 case-I bridge,
* `caseII` : Washington Theorem 9.4 case-II bridge.

The second-order non-irregularity input is supplied via the named parametric
Kellner Prop 2.7 hypothesis `KellnerProp27_thirtyseven_thirtytwo` (sorry-free;
the substantive `B_1184` Iwasawa computation is the explicit boundary). -/
theorem fermatLastTheoremFor_thirtyseven_of_threeRemaining
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI : CaseIBridge 37 (CyclotomicField 37 ℚ))
    (kellner : KellnerProp27_thirtyseven_thirtytwo)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_remaining cor8_19 caseI
    (noSecondOrderIrregularPair_thirtyseven_thirtytwo_of_kellner kellner) caseII

/-- **FLT37 from `¬p∣h⁺` + caseI-classEq + caseII** (alternative form).
Replaces `Cor8_19Bridge` with the direct `¬ 37 ∣ hPlus(K_37)` and uses
the smaller `CaseIClassEqDischarge` instead of full `CaseIBridge`.
The Kellner Prop 2.7 input is supplied via the named parametric hypothesis. -/
theorem fermatLastTheoremFor_thirtyseven_of_notDvdHPlus_and_two
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_not_dvd_hPlus : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (caseI_classEq :
      FLT37.LehmerVandiver.CaseI.CaseIClassEqDischarge 37 (CyclotomicField 37 ℚ))
    (kellner : KellnerProp27_thirtyseven_thirtytwo)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_not_dvd_hPlus
    h_not_dvd_hPlus caseI_classEq
    (noSecondOrderIrregularPair_thirtyseven_thirtytwo_of_kellner kellner)
    caseII

/-- **FLT37 from Cor8_19 + Stage2 + caseII**: maximally-reduced form
using the smallest case-I hypothesis (`Stage2KummerRatioK`, the Kummer
ratio statement) instead of the larger `CaseIBridge` or
`CaseIClassEqDischarge`. The Kellner Prop 2.7 input is supplied via the
named parametric hypothesis `KellnerProp27_thirtyseven_thirtytwo`. -/
theorem fermatLastTheoremFor_thirtyseven_of_cor8_19_stage2_caseII
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (stage2 : FLT37.LehmerVandiver.CaseI.Stage2KummerRatioK 37
      (CyclotomicField 37 ℚ))
    (kellner : KellnerProp27_thirtyseven_thirtytwo)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_stage2 cor8_19 stage2
    (noSecondOrderIrregularPair_thirtyseven_thirtytwo_of_kellner kellner) caseII

end BernoulliRegular

end
