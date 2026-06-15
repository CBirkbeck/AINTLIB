import BernoulliRegular.FLT37.Eichler.CaseIIFreeContentDatum
import BernoulliRegular.FLT37.Eichler.CaseIIFactorDescent

/-!
# [FLT37-CASEII-R2] FLT37 Case-II via the **free-content** factor-count descent

This file composes the free-content factor-count descent (`CaseIIFreeContentDatum.lean`) into the
FLT37 Case-II bridge and the top-level FLT37 endpoint, on the **content-free** frame that resolves
the doubled-measure obstruction.

## What this closes (the structural frame of R2)

The chain of residuals `CaseIIWashingtonAnchorSquareDatum37` / `CaseIIRealAnchorDatumAssembly37` /
`CaseIIFactorDescentStep37` is all keyed to producing a **`RealCaseIIData37`** whose Fermat variable
is anchor-supported.  The proven `caseII_realCaseIIData37_lambda_content_mul_p` shows that frame
forces `(ζ−1)`-content `≡ 0 (mod 37)`, which is **incompatible** with Washington's conjugate-norm
descent equation `ω₁³⁷ + θ₁³⁷ = δ·λ^{2m−37}·ξ₁³⁷` (content `2m − 37 ≢ 0 mod 37`).  This is the
documented reason those residuals are undischargeable *as stated* (b2 verdict, 2026-05-31).

The free-content frame removes that obstruction: `no_realCaseIIData37_of_freeContentDescent`
(`CaseIIFreeContentDatum.lean`) closes the whole Case-II descent from the **single** content-free
descent step `FreeContentCaseIIDescentStep37`, whose conclusion is a free-content datum at an
**arbitrary** content `n'`, so Washington's doubled-measure equation fits natively.  Everything else
— the embedding `RealCaseIIData37 ↪ FreeContentCaseIIData37`, the corrected-radical machinery, the
primarity `(ζ−1)² ∣ α−1`, the terminal first-layer contradiction `caseIIFreeFirstLayer_false`, and
the well-founded factor-count descent — is **proven** in `CaseIIFreeContentDatum.lean`.

## What this file proves

* `caseIIBridge_thirtyseven_of_freeContentDescent` — `CaseIIBridge 37 K 32` from
  `FreeContentCaseIIDescentStep37` (the integer Case-II solution → `RealCaseIIData37` via the proven
  producer, then `no_realCaseIIData37_of_freeContentDescent`).
* `fermatLastTheoremFor_thirtyseven_of_freeContentDescent` — `FermatLastTheoremFor 37` from
  `FreeContentCaseIIDescentStep37` + Assumption-II-free path: Case I (Eichler), `¬37∣h⁺` (Sinnott),
  II1 (Lemma 9.2), and the carried Kellner input are all proven/wired.  This is the FLT37 endpoint
  on the **content-free** Case-II route — the single remaining Case-II residual is the content-free
  `FreeContentCaseIIDescentStep37`, *not* a content-obstructed `RealCaseIIData37` packaging.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–§9.2 (Theorem 9.4),
  pp. 171–173.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **The Case-II bridge via the free-content factor-count descent.**

`CaseIIBridge 37 K 32` from the single content-free descent step `FreeContentCaseIIDescentStep37`.
The integer Case-II solution becomes a real datum via the proven producer
`exists_realCaseIIData37_of_caseII_int_solution`; `no_realCaseIIData37_of_freeContentDescent` (the
well-founded factor-count descent in the **content-free** frame) then closes it.  Mirrors
`caseIIBridge_thirtyseven_of_factorDescent`, but the descent runs in the free-content frame, so the
producer's doubled-measure output is no longer obstructed by the `RealCaseIIData37` λ-content
constraint. -/
theorem caseIIBridge_thirtyseven_of_freeContentDescent
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (h_step : FreeContentCaseIIDescentStep37) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  refine ⟨?_⟩
  intro _hV _hSO a b c hprod hgcd hcase hEq
  exact no_realCaseIIData37_of_freeContentDescent h_step
    (exists_realCaseIIData37_of_caseII_int_solution hprod hgcd hcase hEq)

/-- **Fermat's Last Theorem for `37`, via the free-content factor-count descent.**

`FermatLastTheoremFor 37` from the single content-free descent step
`FreeContentCaseIIDescentStep37` and the carried second-order input `NoSecondOrderIrregularPair
37 32`.  Case I is the unconditional Eichler bridge (`caseIBridge_thirtyseven_eichler`); `¬37∣h⁺` is
the proven `Sinnott.flt37_not_dvd_hPlus`; the Cor-8.19 bridge is built from it.  The Case-II bridge
is `caseIIBridge_thirtyseven_of_freeContentDescent`.

This is the FLT37 endpoint on the **content-free** Case-II route: the single remaining Case-II
content is `FreeContentCaseIIDescentStep37` (the conjugate-norm reassembly producing the next
free-content datum), which — unlike every prior `RealCaseIIData37`-keyed residual — is **not**
obstructed by the doubled-measure λ-content mismatch. -/
theorem fermatLastTheoremFor_thirtyseven_of_freeContentDescent
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (h_step : FreeContentCaseIIDescentStep37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero 37 := ⟨by decide⟩
  exact fermatLastTheoremFor_thirtyseven_of_remaining
    (cor8_19Bridge_of_not_dvd_hPlus 37 (CyclotomicField 37 ℚ) Sinnott.flt37_not_dvd_hPlus)
    caseIBridge_thirtyseven_eichler
    noSecondOrderIrregular
    (caseIIBridge_thirtyseven_of_freeContentDescent h_step)

end BernoulliRegular.FLT37.Eichler

end

end
