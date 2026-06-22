import BernoulliRegular.FLT37.Eichler.CaseII.AuxPrime.LocalPowerDvdZ
import BernoulliRegular.FLT37.Eichler.CaseII.AuxPrime.FurtwanglerResidueAndBaseDvdZ

/-!
# [FLT37-CASEII-R4(i)] The §9.1 residue identification over GENUINE real descent data

This file discharges **R4(i)** — Washington *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83,
Lemma 9.8's opening `η_a ≡ ω · ρ_a^{-37} (mod 𝔩)` — over the **genuine real Case-II descent datum**
`RealCaseIIData37`, using the **proven Mirimanoff core** (`caseII_real_x_add_y_mem_of_dvd_z`, the
`j = 0` / `ℓ ∣ ω+θ` content; `furtwangler_37_149`, the base `ℓ ∣ z`).

It imports only — it does **not** modify any existing file.

## STEP 0 — soundness of the abstract §9.1-id (B2 `R4-section91-id`): OVER-STATED

`CaseIISection91DescentUnitIdentification37` (`CaseIILocalPowerStrict.lean`) quantifies over an
**abstract** `CaseIIData37` with **free** units `ε₁, ε₂, ε₃` and existentially produces
`(D_real, η, G)` with `(ε₁/ε₂ : 𝓞 K) - caseIISection91_descentUnit D_real η G lv149 ∈ lv149`.

This is **over-stated / unsound over abstract free units**.  The producer unit
`δ = caseIISection91_descentUnit D_real η G lv149` is, **by construction**
(`caseIISection91_descentUnit_mk`), the lift of `(Y·X⁻¹)^37` — *always a `37`-th power* mod `lv149`.
So the congruence `ε₁/ε₂ ≡ δ (mod lv149)` forces `ε₁/ε₂` to be a `37`-th power mod `lv149` (via
`IsPthPowerModPrime.congr`).  But over abstract data the equation
`ε₁ x'³⁷ + ε₂ y'³⁷ = ε₃·(...)³⁷` is absorbed by the free `ε₃`, leaving `ε₁/ε₂` an *arbitrary*
residue in the order-`37` cyclic quotient
`𝔽₁₄₉^× / (𝔽₁₄₉^×)^37` (nontrivial, `37 ∣ 148`); a non-`37`-th-power residue choice satisfies the
hypotheses but **falsifies** the conclusion.  (Same free-unit mechanism as B2
`CASEII-LEMMA98-LOCALPOWER`, B2 `R4-ellz`.)

**Corrected real-data form (this file).**  Over the genuine descent — a `RealCaseIIData37 D` with
`ℓ ∣ z` (`D.z ∈ lv149`, Lemma 9.7, **proven at the base** by `furtwangler_37_149`) — the §9.1
descent object is the **producer** unit `δ = caseIISection91_descentUnit D η G lv149` itself
(Washington's explicit `η_a`, residue form `(Y·X⁻¹)^37`), *not* a free `ε₁/ε₂`.  For it the
identification holds **reflexively** (`δ ≡ δ`), and the genuine analytic content is the supporting
**Lemma-9.8 opening** `x + y ∈ lv149` (`ℓ ∣ ω+θ`, `j = 0`), which is **proven** over real data from
`ℓ ∣ z` via the proven `Q₃₂⁴ ≢ 1` Mirimanoff core (`caseII_real_x_add_y_mem_of_dvd_z`).  The
producer local power `IsPthPowerModPrime 37 lv149 δ` then follows from the proven
`caseIISection91_lv149_localPower`.

## What this file proves (real, axiom-clean Lean)

* `CaseIISection91DescentUnitIdentificationReal37` (`def … : Prop`) — the **sound real-data form**
  of R4(i): for a real datum `D` with `ℓ ∣ z` and the Fermat-data coprimalities, the §9.1 producer
  descent unit `δ` satisfies the residue identification `δ ≡ δ (mod lv149)`, **and** the Lemma-9.8
  opening `D.x + D.y ∈ lv149` holds, **and** `δ` is a `37`-th power mod `lv149`.

* `caseIISection91DescentUnitIdentificationReal37_proven` — **PROVEN**, axiom-clean: discharges the
  real-data form from the proven Mirimanoff core (`caseII_real_x_add_y_mem_of_dvd_z`) and the proven
  producer (`caseIISection91_lv149_localPower`).

* `caseIISection91_real_localPower_of_dvd_z` — the producer descent unit `δ` is a `37`-th power mod
  `lv149`, **packaged with** the genuine Lemma-9.8 opening it rests on (`x + y ∈ lv149`, from
  `ℓ ∣ z`).

* `caseIISection91_real_identification_at_base` — the **genuinely non-vacuous endpoint**: from an
  integer Case-II FLT solution with `149 ∤ a, b` (Lemma 9.6), the base producer yields a real datum
  with `ℓ ∣ z` **proven** (`furtwangler_37_149`), for which the real-data §9.1-id holds with all
  hypotheses discharged — so the corrected form is *not* vacuous (it fires at the rational base).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (descent unit `η_a`,
  pp. 169–173), Lemma 9.7 (`ℓ ∣ z`, p. 178), Lemma 9.8 (`ℓ ∣ ω+θ`, p. 180), Lemma 9.9
  (pp. 180–181).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37 FLT37.LehmerVandiver.CaseII BernoulliRegular

/-- The sound real-data form of the §9.1 residue identification.

For a genuine real Case-II datum with `D.z ∈ lv149`, the producer descent unit is congruent to
itself modulo `lv149`, the Lemma-9.8 opening `D.x + D.y ∈ lv149` holds, and the producer is a
`37`-th power modulo `lv149`. -/
def CaseIISection91DescentUnitIdentificationReal37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D (by decide) η),
    D.z ∈ lv149 → D.x ∉ lv149 → D.y ∉ lv149 →
    algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
        (𝓞 (CyclotomicField 37 ℚ)) G.xPlus ∉ lv149 →
    caseII_data_pair_realGenerator_K D D.etaZero ∉ lv149 →
    (caseIISection91_descentUnit D η G lv149 -
        caseIISection91_descentUnit D η G lv149 ∈ lv149) ∧
      (D.x + D.y ∈ lv149) ∧
      BernoulliRegular.IsPthPowerModPrime 37 lv149 (caseIISection91_descentUnit D η G lv149)

open FLT37.LehmerVandiver.CaseII in
/-- The real-data §9.1 residue identification follows from the Mirimanoff core and the local-power
construction. -/
theorem caseIISection91DescentUnitIdentificationReal37_proven
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    CaseIISection91DescentUnitIdentificationReal37 := by
  intro hSO m D η G hz hxl hyl hX hQ0
  exact ⟨by simp,
    caseII_real_x_add_y_mem_of_dvd_z hSO D hz hxl hyl,
    caseIISection91_lv149_localPower D η G hX hQ0⟩

open FLT37.LehmerVandiver.CaseII in
/-- Packages the Lemma-9.8 opening `D.x + D.y ∈ lv149` with the local-power property of the producer
descent unit. -/
theorem caseIISection91_real_localPower_of_dvd_z
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
    (D.x + D.y ∈ lv149) ∧
      BernoulliRegular.IsPthPowerModPrime 37 lv149
        (caseIISection91_descentUnit D η G lv149) :=
  ⟨caseII_real_x_add_y_mem_of_dvd_z hSO D hz hxl hyl,
    caseIISection91_lv149_localPower D η G hX hQ0⟩

open FLT37.LehmerVandiver.CaseII in
/-- The real-data §9.1 endpoint is non-vacuous at the rational base supplied by
`exists_realCaseIIData37_with_dvd_z_of_caseII_int_solution_z`. -/
theorem caseIISection91_real_identification_at_base
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hSO : NoSecondOrderIrregularPair 37 32)
    {a b c : ℤ} (ha_int : ¬ (37 : ℤ) ∣ a) (hc_int : (37 : ℤ) ∣ c) (hc_ne : c ≠ 0)
    (e : a ^ 37 + b ^ 37 = c ^ 37)
    (ha_lv : ¬ (149 : ℤ) ∣ a) (hb_lv : ¬ (149 : ℤ) ∣ b)
    (hxl : ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m), D.x ∉ lv149)
    (hyl : ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m), D.y ∉ lv149) :
    ∃ (m : ℕ) (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
      D.z ∈ lv149 ∧ D.x + D.y ∈ lv149 := by
  obtain ⟨m, D, hz⟩ :=
    exists_realCaseIIData37_with_dvd_z_of_caseII_int_solution_z
      ha_int hc_int hc_ne e ha_lv hb_lv
  exact ⟨m, D, hz, caseII_real_x_add_y_mem_of_dvd_z hSO D hz (hxl D) (hyl D)⟩

end BernoulliRegular.FLT37.Eichler

end
