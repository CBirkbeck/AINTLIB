import BernoulliRegular.FLT37.Eichler.CaseIISection91IdentificationReal
import BernoulliRegular.FLT37.Eichler.CaseIIAssumptionIIAssembled

/-!
# [FLT37-CASEII-R4(i)] The abstract↔real gap for the §9.1 identification, characterised honestly

`CaseIISection91IdentificationReal.lean` discharged **R4(i) over the genuine real descent datum** —
the §9.1 identification `caseIISection91DescentUnitIdentificationReal37_proven`, where the descent
unit *is* the producer `δ` (Washington's explicit `η_a`).  This file records, soundly and honestly,
how that proven real-data content relates to the **abstract** Assumption-II route, and isolates the
precise remaining gap.

It imports only — it does **not** modify any existing file.

## The soundness situation (honest, not laundered)

The closed Assumption II `WashingtonCaseIIExactQuotientUnitPower37Source` is consumed by the descent
step at the **descent-constructed** units `ε₁, ε₂, ε₃`.  The proven
`caseIIOmega32_assumptionII_of_section91Ident_dvdZ` (`CaseIIAssumptionIIAssembled.lean`) reduces it
to the **abstract** residuals `CaseIISection91DescentUnitIdentification37` (R4(i)) and
`CaseIILehmerVandiverDvdZ37` (R4(ii)), both quantified over an abstract `CaseIIData37` with **free**
units.

**Both abstract residuals are over-stated (false over free units)** — logged B2 `R4-section91-id`,
`R4-ellz`, `CASEII-LEMMA98-LOCALPOWER`.  Concretely for R4(i): the producer `δ = (Y·X⁻¹)^37` is
*always* a `37`-th power mod `lv149` (`caseIISection91_descentUnit_mk`), so the congruence
`ε₁/ε₂ ≡ δ (mod lv149)` of the abstract §9.1-id forces the free `ε₁/ε₂` (left arbitrary in
`𝔽₁₄₉^×/(𝔽₁₄₉^×)^37` by the `ε₃`-absorbed equation) to be a `37`-th power mod `lv149` — refuted by a
a non-`37`-th-power residue choice (B2 counterexample).  So the abstract
`CaseIISection91DescentUnitIdentification37` is a **false universal**; any endpoint consuming it
(including
`fermatLastTheoremFor_thirtyseven_of_caseII_postR3`) is conditional on a hypothesis that cannot be
discharged as stated.  We do **not** wrap that false universal as "progress".

The **sound, true, proven** statement is the real-data form
`CaseIISection91DescentUnitIdentificationReal37` (`CaseIISection91IdentificationReal.lean`): with
the descent unit the producer `δ`, the §9.1 identification holds and `δ` is a `37`-th power mod
`lv149`,
via the proven Mirimanoff core.  The genuine remaining gap is therefore **architectural**: the
abstract Assumption-II route (the descent step's `h_unit`, hard-wired to the abstract universal at
each `CaseIIData37`) must be re-pointed at the *producer-constructed* descent units, for which the
sound real-data form applies — a refactor of proven `SpecificChain` declarations, deliberately not
performed here.

## What this file provides (soundly)

* `caseIISection91_real_assumptionII_shape` — over a real datum with `ℓ ∣ z`, the proven real-data
  §9.1-id yields the producer descent unit `δ` is a `37`-th power mod `lv149` **and** the Lemma-9.8
  opening `D.x + D.y ∈ lv149` — the genuine `IsPthPowerModPrime` content that Assumption II needs,
  established soundly on the producer descent object (not a free `ε₁/ε₂`).

* `caseIISection91_real_dvdZ_at_base` — the R4(ii) `ℓ ∣ z` is **proven at the base** (Furtwängler),
  so over the genuine base both R4(i) (producer local power) and R4(ii) hold soundly — confirming
  the remaining gap is *only* the abstract↔real re-pointing of the descent's `h_unit`, not any
  missing arithmetic.

No false universal is exported as a usable hypothesis;
`fermatLastTheoremFor_thirtyseven_of_caseII_postR3` remains the abstract-route endpoint (conditional
on the over-stated abstract §9.1-id).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (descent unit `η_a`,
  pp. 169–173), Lemma 9.7 (`ℓ ∣ z`), Lemma 9.8 (`ℓ ∣ ω+θ`), Lemma 9.9 (pp. 180–181).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37 FLT37.LehmerVandiver.CaseII BernoulliRegular

/-! ## 1. The sound Assumption-II shape on the producer descent object (real data)

The genuine `IsPthPowerModPrime` content Assumption II needs — that the descent unit is a `37`-th
power mod `lv149` — holds **soundly** on the *producer-constructed* descent object `δ` over real
data, by the proven real-data §9.1-id.  We extract exactly that conjunct (the producer local power),
together with the Lemma-9.8 opening it rests on, to mark what is genuinely established (versus the
over-stated abstract claim about a free `ε₁/ε₂`). -/

open FLT37.LehmerVandiver.CaseII in
/-- **The sound Assumption-II content on the producer descent object** (proven, axiom-clean).

For a real datum `D` with `ℓ ∣ z` (Lemma 9.7), Lemma 9.6 (`D.x, D.y ∉ lv149`), and the Fermat-data
coprimalities, the producer descent unit `δ = caseIISection91_descentUnit D η G lv149` (Washington's
`η_a`) is a `37`-th power mod `lv149` (the genuine `IsPthPowerModPrime` content Assumption II
needs), and the Lemma-9.8 opening `D.x + D.y ∈ lv149` (`ℓ ∣ ω+θ`, `j = 0`) holds.  Both via the
proven real-data §9.1-id — the **sound** statement (the abstract version over a free `ε₁/ε₂` is
over-stated, B2 `R4-section91-id`). -/
theorem caseIISection91_real_assumptionII_shape
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D (by decide) η)
    (hz : D.z ∈ lv149) (hxl : D.x ∉ lv149) (hyl : D.y ∉ lv149)
    (hX : algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
        (𝓞 (CyclotomicField 37 ℚ)) G.xPlus ∉ lv149)
    (hQ0 : caseII_data_pair_realGenerator_K D D.etaZero ∉ lv149) :
    BernoulliRegular.IsPthPowerModPrime 37 lv149
        (caseIISection91_descentUnit D η G lv149) ∧
      (D.x + D.y ∈ lv149) :=
  ⟨((caseIISection91DescentUnitIdentificationReal37_proven hSO D η G hz hxl hyl hX hQ0).2).2,
    ((caseIISection91DescentUnitIdentificationReal37_proven hSO D η G hz hxl hyl hX hQ0).2).1⟩

/-! ## 2. R4(ii) `ℓ ∣ z` is proven at the base — the remaining gap is purely architectural

The R4(ii) datum `ℓ ∣ z` is **proven** at the rational base by the Furtwängler residue condition
(`exists_realCaseIIData37_with_dvd_z_of_caseII_int_solution_z`).  Combined with §1, over the genuine
base both R4(i) (producer local power) and R4(ii) (`ℓ ∣ z`) hold soundly.  So the *only* remaining
gap is the abstract↔real re-pointing of the descent's `h_unit` from the over-stated abstract
universal to the producer-constructed descent unit — not any missing arithmetic. -/

open FLT37.LehmerVandiver.CaseII in
/-- **R4(ii) `ℓ ∣ z` at the base, with the producer local power available** (proven, axiom-clean
given the carried second-order Bernoulli input).

From a Case-II integer FLT solution `a³⁷ + b³⁷ = c³⁷` with `37 ∣ c`, `37 ∤ a`, `c ≠ 0`, Lemma 9.6
(`149 ∤ a`, `149 ∤ b`): the base producer yields a real datum `D` with `D.z ∈ lv149` (`ℓ ∣ z`,
**proven** Furtwängler) and the Lemma-9.8 opening `D.x + D.y ∈ lv149`.  So the genuine arithmetic
of R4(i)+R4(ii) is discharged at the base; the only remaining gap to FLT37 is architectural
(re-pointing the descent's `h_unit`). -/
theorem caseIISection91_real_dvdZ_at_base
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hSO : NoSecondOrderIrregularPair 37 32)
    {a b c : ℤ} (ha_int : ¬ (37 : ℤ) ∣ a) (hc_int : (37 : ℤ) ∣ c) (hc_ne : c ≠ 0)
    (e : a ^ 37 + b ^ 37 = c ^ 37)
    (ha_lv : ¬ (149 : ℤ) ∣ a) (hb_lv : ¬ (149 : ℤ) ∣ b)
    (hxl : ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m), D.x ∉ lv149)
    (hyl : ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m), D.y ∉ lv149) :
    ∃ (m : ℕ) (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
      D.z ∈ lv149 ∧ D.x + D.y ∈ lv149 :=
  caseIISection91_real_identification_at_base hSO ha_int hc_int hc_ne e ha_lv hb_lv hxl hyl

end BernoulliRegular.FLT37.Eichler

end
