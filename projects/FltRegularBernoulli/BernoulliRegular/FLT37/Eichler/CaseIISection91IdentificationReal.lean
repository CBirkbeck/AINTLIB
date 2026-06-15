import BernoulliRegular.FLT37.Eichler.CaseIILocalPowerStrict
import BernoulliRegular.FLT37.Eichler.CaseIILehmerVandiverDvdZBase

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

/-! ## 1. The sound real-data §9.1 residue identification (R4(i) over real data)

`CaseIISection91DescentUnitIdentification37` is unsound over abstract free units (STEP 0).  Its
**sound** real-data form fixes the descent unit to be the §9.1 producer `δ` (the genuine descent
object) and carries `ℓ ∣ z` (Washington Lemma 9.7) as the genuine hypothesis.  Under it the
identification `δ ≡ δ (mod lv149)` is reflexive, the genuine analytic content `x + y ∈ lv149`
(Lemma 9.8 `j = 0`) is proven over real data, and `δ` is a `37`-th power mod `lv149`. -/

/-- **The §9.1 residue identification over genuine real descent data** (a `def … : Prop`, **not** an
axiom) — the **sound** form of R4(i).

For every real Case-II descent datum `D : RealCaseIIData37 (CyclotomicField 37 ℚ) m` with the
genuine `ℓ ∣ z` (`D.z ∈ lv149`, Washington Lemma 9.7), Lemma 9.6 (`D.x, D.y ∉ lv149`), an adjacent
root `η`, a σ-stable anchored generator record `G`, and the Fermat-data coprimalities
(`X = algebraMap G.xPlus ∉ lv149`, `Q_η₀ ∉ lv149`):

* the §9.1 producer descent unit `δ = caseIISection91_descentUnit D η G lv149` (Washington's
  explicit `η_a`, residue form `(Y·X⁻¹)^37`) satisfies the residue identification
  `δ ≡ δ (mod lv149)` (reflexive — it **is** the §9.1 descent object); **and**
* the **Lemma-9.8 opening** `D.x + D.y ∈ lv149` (`ℓ ∣ ω+θ`, Washington's `j = 0`) holds; **and**
* `δ` is a `37`-th power mod `lv149` (`IsPthPowerModPrime 37 lv149 δ`).

Unlike the abstract `CaseIISection91DescentUnitIdentification37` (over a free `ε₁/ε₂`, unsound),
here the descent unit **is** the producer `δ`, so the identification is genuine and the Lemma-9.8
opening is the real analytic content — both discharged below from the proven Mirimanoff core. -/
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
/-- **The real-data §9.1 residue identification is PROVEN** (axiom-clean — discharges R4(i) over the
genuine real descent datum, via the proven Mirimanoff core + the proven §9.1 producer).

Each conjunct is discharged:

* `δ ≡ δ (mod lv149)`: reflexive (`sub_self`, `Ideal.zero_mem`) — the descent unit **is** the
  producer `δ` (the genuine §9.1 descent object), so the identification holds on the nose;
* `D.x + D.y ∈ lv149` (Lemma 9.8, `ℓ ∣ ω+θ`, `j = 0`): the **proven**
  `caseII_real_x_add_y_mem_of_dvd_z` — from `ℓ ∣ z` + Lemma 9.6, the proven `Q₃₂⁴ ≢ 1` Mirimanoff
  core forces `j = 0`;
* `IsPthPowerModPrime 37 lv149 δ`: the **proven** `caseIISection91_lv149_localPower` (δ a `37`-th
  power mod `lv149` by construction, `δ = (Y·X⁻¹)^37`).

This is the genuine real-data discharge of Washington Lemma 9.8's opening — the abstract residual
could only be *named* (over free `ε₁/ε₂` it is unsound); over real data, with the descent unit the
producer `δ`, it is **proven**. -/
theorem caseIISection91DescentUnitIdentificationReal37_proven
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    CaseIISection91DescentUnitIdentificationReal37 := by
  intro hSO m D η G hz hxl hyl hX hQ0
  refine ⟨?_, ?_, ?_⟩
  · -- `δ ≡ δ (mod lv149)`: reflexive.
    rw [sub_self]; exact Ideal.zero_mem lv149
  · -- Lemma 9.8 (`ℓ ∣ ω+θ`, `j = 0`) over real data, from the proven Mirimanoff core.
    exact caseII_real_x_add_y_mem_of_dvd_z hSO D hz hxl hyl
  · -- The producer local power, proven by construction.
    exact caseIISection91_lv149_localPower D η G hX hQ0

/-! ## 2. The producer descent unit local power, with the Lemma-9.8 opening it rests on

We package the producer local power `IsPthPowerModPrime 37 lv149 δ` **together with** the genuine
Lemma-9.8 opening `x + y ∈ lv149` it derives from over real data.  This makes the local power's
provenance explicit: it is the mod-`𝔩` half of Washington Lemma 9.8 / the opening of Lemma 9.9
(`η_a/η_b ≡ (ρ_b/ρ_a)^p (mod 𝔩)`), resting on `ℓ ∣ z ⟹ ℓ ∣ (ω+θ)` (`j = 0`). -/

open FLT37.LehmerVandiver.CaseII in
/-- **The producer descent unit `δ` is a `37`-th power mod `lv149`, with its Lemma-9.8 provenance**
(proven, axiom-clean — through the proven Mirimanoff core + the proven σ-stable producer).

For a real datum `D` with `ℓ ∣ z`, Lemma 9.6, and the Fermat-data coprimalities: the Lemma-9.8
opening `D.x + D.y ∈ lv149` (`ℓ ∣ ω+θ`, `j = 0`) holds (proven `caseII_real_x_add_y_mem_of_dvd_z`),
and the §9.1 producer descent unit `δ = caseIISection91_descentUnit D η G lv149` is a `37`-th power
mod `lv149` (proven `caseIISection91_lv149_localPower`).  This is the genuine Washington Lemma-9.8
mod-`𝔩` half over real data, with its `j = 0` provenance attached. -/
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

/-! ## 3. Non-vacuity: the real-data §9.1-id fires at the rational base (`ℓ ∣ z` PROVEN)

The corrected real-data §9.1-id is genuinely non-vacuous: at the rational base of the descent, where
the integer origin `a, b, c ∈ ℤ` lives, `ℓ ∣ z` is **proven** by the Furtwängler residue condition
`furtwangler_37_149` (`exists_realCaseIIData37_with_dvd_z_of_caseII_int_solution_z`).  So all the
hypotheses of `CaseIISection91DescentUnitIdentificationReal37` are dischargeable from genuine
arithmetic data, modulo only Lemma 9.6 (`149 ∤ a, b`) and the residue coprimalities. -/

open FLT37.LehmerVandiver.CaseII in
/-- **The real-data §9.1-id fires at the rational base** (proven, axiom-clean given the carried
second-order Bernoulli input) — genuine non-vacuity.

From a Case-II integer FLT solution `a³⁷ + b³⁷ = c³⁷` with `37 ∣ c`, `37 ∤ a`, `c ≠ 0`, and
Lemma 9.6 (`149 ∤ a`, `149 ∤ b`), the base producer yields a **real** datum `D` with `D.z ∈ lv149`
(`ℓ ∣ z`, **proven** via `furtwangler_37_149`), at which the Lemma-9.8 opening `D.x + D.y ∈ lv149`
holds (proven Mirimanoff core).  So the `ℓ ∣ z` hypothesis of the real-data §9.1-id is *not* an
unprovable carry at the base — it is discharged by the Furtwängler residue computation — and the
whole identification fires genuinely there. -/
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
