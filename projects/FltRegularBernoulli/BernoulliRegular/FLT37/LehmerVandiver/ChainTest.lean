import BernoulliRegular.FLT37.LehmerVandiver.CaseI.Bridge
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.BridgeAssembly
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.ADivPrincipal
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.NoSecondOrderHelper
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.SpecificDischarge
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Cor8_19Forward

/-!
# LV-route chain compositionality tests

Sanity-check theorems verifying that the parametric LV-route chain
composes correctly. Each `example` exercises a specific composition
path:

1. Regular-prime path: from `p.Coprime |Cl(K)|` (regularity), all
   discharges hold, so the chain composes to give `CaseIBridge` and
   `CaseIIBridge` directly.

2. Parametric path: from explicit `Stage2KummerRatioK` etc. discharges,
   the chain composes to give `FermatLastTheoremFor 37`.

These are smoke tests — no new mathematical content, just compositional
correctness verification.
-/

@[expose] public section

open NumberField

namespace BernoulliRegular

/-- **Smoke test: regular-prime caseI bridge.** Under regularity, the
LV010-D parametric chain composes to give `CaseIBridge`. -/
example {p : ℕ} [hpri : Fact p.Prime] (hp_odd : p ≠ 2)
    [NumberField.IsCMField (CyclotomicField p ℚ)]
    [Fintype (ClassGroup (𝓞 (CyclotomicField p ℚ)))]
    (hreg : p.Coprime <|
      Fintype.card <| ClassGroup (𝓞 (CyclotomicField p ℚ))) :
    CaseIBridge p (CyclotomicField p ℚ) :=
  FLT37.LehmerVandiver.CaseI.caseIBridge_of_regular hp_odd hreg

/-- **Smoke test: regular-prime caseII bridge.** Same for caseII. -/
example {p : ℕ} [hpri : Fact p.Prime] (hp_odd : p ≠ 2) (i : ℕ)
    [NumberField.IsCMField (CyclotomicField p ℚ)]
    [Fintype (ClassGroup (𝓞 (CyclotomicField p ℚ)))]
    (hreg : p.Coprime <|
      Fintype.card <| ClassGroup (𝓞 (CyclotomicField p ℚ))) :
    CaseIIBridge p (CyclotomicField p ℚ) i :=
  FLT37.LehmerVandiver.CaseII.caseIIBridge_of_regular hp_odd i hreg

/-- **Smoke test: full FLT37 from 5 parametric inputs.** Verifies the
top-level reduction theorem is callable with the right input types. -/
example
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
  fermatLastTheoremFor_thirtyseven_of_all_discharges
    cor8_19 stage2 noSecondOrderIrregular caseII_principal caseII_kummer

/-- **Smoke test: cor8_19 trivial constructor.** Direct bridge from
known `¬ p ∣ h⁺`. -/
example {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {i : ℕ}
    (h : ¬ (p : ℕ) ∣ hPlus K) :
    Cor8_19Bridge p K i :=
  cor8_19Bridge_of_not_dvd_hPlus p K h

/-- **Smoke test: full FLT-via-regular compatibility.** Under
regularity (a vacuous hypothesis for 37, since 37 is irregular), the
parametric chain composes to give FLT37. This is a compositional
sanity check, not a substantive result. -/
example
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    [Fintype (ClassGroup (𝓞 (CyclotomicField 37 ℚ)))]
    (hreg : (37 : ℕ).Coprime <|
      Fintype.card <| ClassGroup (𝓞 (CyclotomicField 37 ℚ)))
    (h_not_dvd_hPlus : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (noSO : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_remaining
    (cor8_19Bridge_of_not_dvd_hPlus 37 (CyclotomicField 37 ℚ) h_not_dvd_hPlus)
    (FLT37.LehmerVandiver.CaseI.caseIBridge_of_regular
      (by decide : (37 : ℕ) ≠ 2) hreg)
    noSO
    (FLT37.LehmerVandiver.CaseII.caseIIBridge_of_regular
      (by decide : (37 : ℕ) ≠ 2) 32 hreg)

/-- **Smoke test: cor8_19 from regularity.** Under regularity,
`cor8_19Bridge_of_regular` discharges Cor 8.19 directly (no separate
`h_not_dvd_hPlus` hypothesis needed — it's derived from regularity
via `hPlus_dvd_h`). -/
example {p : ℕ} [hpri : Fact p.Prime] (hp_odd : p ≠ 2)
    [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
    [NumberField.IsCMField (CyclotomicField p ℚ)]
    [Fintype (ClassGroup (𝓞 (CyclotomicField p ℚ)))]
    (hreg : p.Coprime <|
      Fintype.card <| ClassGroup (𝓞 (CyclotomicField p ℚ))) {i : ℕ} :
    Cor8_19Bridge p (CyclotomicField p ℚ) i :=
  cor8_19Bridge_of_regular p (CyclotomicField p ℚ) hp_odd hreg

/-- **Smoke test: minimal-input variant.** Use direct `¬ p ∣ h⁺`
instead of `Cor8_19Bridge`. -/
example
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_not_dvd_hPlus : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (caseI_classEq :
      FLT37.LehmerVandiver.CaseI.CaseIClassEqDischarge 37
        (CyclotomicField 37 ℚ))
    (noSO : NoSecondOrderIrregularPair 37 32)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_not_dvd_hPlus
    h_not_dvd_hPlus caseI_classEq noSO caseII

/-- **Smoke test: NoSecondOrderIrregularPair from explicit
non-divisibility.** -/
example (h : ¬ (37 : ℤ) ^ 3 ∣ (bernoulli (32 * 37)).num) :
    NoSecondOrderIrregularPair 37 32 :=
  NoSecondOrderIrregularPair.of_not_dvd_bernoulli_num h

end BernoulliRegular

end
