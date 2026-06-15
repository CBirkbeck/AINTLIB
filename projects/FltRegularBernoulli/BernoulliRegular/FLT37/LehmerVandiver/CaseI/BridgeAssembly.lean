import BernoulliRegular.FLT37.LehmerVandiver.CaseI.Bridge
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.Stage2Interface
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.ADivPrincipal
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Cor8_19Forward
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealBundle

/-!
# LV010-D Final assembly: FLT37 reduced to four parametric inputs

Composes LV010-D (`caseIBridge_of_classEqDischarge`) with the existing
`fermatLastTheoremFor_thirtyseven_of_remaining`, producing a clean
parametric statement for FLT37.

The remaining four parametric inputs:
- `cor8_19 : Cor8_19Bridge 37 K 32` (Sinnott's index formula)
- `caseI_classEq : CaseIClassEqDischarge 37 K` (Stages 1+2: primary
  + Kummer's lemma adapted)
- `noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32`
  (`37³ ∤ B_{1184}`, user-handled via `bernoulli_decide`)
- `caseII : CaseIIBridge 37 K 32` (Washington Theorem 9.4)

Once any one of these is closed, FLT37 reduces to the remaining three.
With all four closed, FLT37 is unconditional with axiom budget
`[propext, Classical.choice, Quot.sound]` only.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

/-- **FLT37 from four parametric inputs (LV010-D form).** Replaces the
existing `fermatLastTheoremFor_thirtyseven_of_remaining`'s `caseI`
field with the parametric `caseIBridge_of_classEqDischarge`, exposing
the class-equality input directly.

This is the "shipping shape" of the LV-route: FLT37 is derivable
unconditionally from
- Sinnott's index formula (cor8_19 bridge),
- The Vandiver class-equality discharge (Stages 1+2),
- The second-order Bernoulli condition (Kellner / `bernoulli_decide`),
- Washington's case-II argument (caseII bridge). -/
theorem fermatLastTheoremFor_thirtyseven_of_classEqDischarge
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (caseI_classEq :
      FLT37.LehmerVandiver.CaseI.CaseIClassEqDischarge 37 (CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_remaining
    cor8_19
    (FLT37.LehmerVandiver.CaseI.caseIBridge_of_classEqDischarge
      (by decide : (37 : ℕ) ≠ 2) caseI_classEq)
    noSecondOrderIrregular
    caseII

/-- **FLT37 from Stage 2 + three other inputs.** Variant that takes
Stage 2 (the Kummer ratio Prop) directly, composing
`caseIClassEqDischarge_of_stage2` to discharge the class equality.

Stage 1 is shipped (regularity-free, in
`PrimaryNormalization.lean`); Stage 2 is the substantive Kummer's
lemma adaptation (Hilbert 90 / 92 / 94 descent). -/
theorem fermatLastTheoremFor_thirtyseven_of_stage2
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (stage2 : FLT37.LehmerVandiver.CaseI.Stage2KummerRatioK 37
      (CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_classEqDischarge
    cor8_19
    (FLT37.LehmerVandiver.CaseI.caseIClassEqDischarge_of_stage2 stage2)
    noSecondOrderIrregular
    caseII

/-- **FLT37 from all five "axiom-like" discharges.** Maximal parametric
form: takes Stage 2 + AdaptedKummersLemma + CaseIIPrincipalDischarge as
the deep CFT inputs, plus Cor8_19Bridge (Sinnott) and the Bernoulli
condition.

This is the cleanest possible "shipping shape" of FLT37 via the
LV-route: every regularity-using piece in the original flt-regular
proof has been replaced by an explicit parametric Prop predicate. -/
theorem fermatLastTheoremFor_thirtyseven_of_all_discharges
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (stage2 : FLT37.LehmerVandiver.CaseI.Stage2KummerRatioK 37
      (CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32)
    (caseII_principal :
      FLT37.LehmerVandiver.CaseII.CaseIIPrincipalDischarge 37
        (CyclotomicField 37 ℚ))
    (caseII_kummer :
      FLT37.LehmerVandiver.CaseII.AdaptedKummersLemma 37
        (CyclotomicField 37 ℚ)) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_stage2
    cor8_19
    stage2
    noSecondOrderIrregular
    (FLT37.LehmerVandiver.CaseII.caseIIBridge_of_discharges
      (by decide : (37 : ℕ) ≠ 2) 32 caseII_principal caseII_kummer)

/-- **FLT37 from ¬p ∣ h⁺ + 4 other discharges.** Variant that takes
`¬ 37 ∣ h⁺(K_37)` directly (instead of via `Cor8_19Bridge`), using
the trivial `cor8_19Bridge_of_not_dvd_hPlus` constructor.

Useful when `¬ p ∣ h⁺` is established by other means (numerical
verification, regularity, etc.) without needing Sinnott's index
formula. -/
theorem fermatLastTheoremFor_thirtyseven_of_not_dvd_hPlus
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_not_dvd_hPlus : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (caseI_classEq :
      FLT37.LehmerVandiver.CaseI.CaseIClassEqDischarge 37 (CyclotomicField 37 ℚ))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_classEqDischarge
    (cor8_19Bridge_of_not_dvd_hPlus 37 (CyclotomicField 37 ℚ) h_not_dvd_hPlus)
    caseI_classEq
    noSecondOrderIrregular
    caseII

end BernoulliRegular

end
