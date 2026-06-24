import BernoulliRegular.FLT37.Eichler.CaseII.Section91.DescentUnitResidueIdentification

/-!
# [FLT37-CASEII-R4(i)] The producer-`δ` real-data §9.1 form is VACUOUS in the `ℓ ∣ z` regime

This file records, with a **machine-checked, axiom-clean proof**, the precise obstruction to closing
R2 by "re-pointing" the Case-II descent step's abstract Assumption-II hypothesis
(`WashingtonCaseIIExactQuotientUnitPower37Source`) at the proven real-data §9.1 form
(`caseIISection91DescentUnitIdentificationReal37_proven`).

## The claim under scrutiny (logged for honesty)

The proven real-data form `caseIISection91DescentUnitIdentificationReal37_proven`
(`CaseIISection91IdentificationReal.lean`) is **true** — but it is true **vacuously** in exactly the
regime where the descent needs it.  Concretely its hypotheses include both:

* `hz  : D.z ∈ lv149` — Washington Lemma 9.7 (`ℓ ∣ z`), the genuine descent regime; **and**
* `hQ0 : caseII_data_pair_realGenerator_K D D.etaZero ∉ lv149` — `Q_η₀ = (x+y)² ∉ lv149`, the
  coprimality the **producer** descent unit `δ = (Y·X⁻¹)^37` needs for its local power
  (`caseIISection91_lv149_localPower`, which requires `Q_η₀ ∉ 𝔩` to cancel the residue).

But over real data, **Washington Lemma 9.8** (`caseII_real_x_add_y_mem_of_dvd_z`, PROVEN) shows
`D.z ∈ lv149` together with Lemma 9.6 (`ℓ ∤ x`, `ℓ ∤ y`) forces `D.x + D.y ∈ lv149`, hence
`Q_η₀ = (x+y)² ∈ lv149` — **contradicting** `hQ0`.

So `hz ∧ hQ0` is **jointly unsatisfiable** over real data (given Lemma 9.6): the producer-`δ`
real-data form fires only when `Q_η₀ ∉ lv149`, i.e. when `ℓ ∤ z`, which is **never** the descent
regime.  The producer balanced identity `X³⁷·Q_η·U = Y³⁷·Q_η₀` (the source of `δ`) **degenerates
mod `lv149`** precisely when `Q_η₀ ∈ lv149` (its RHS `Y³⁷·Q_η₀ ≡ 0`), so the cancellation that makes
`δ` a `37`-th power mod `lv149` is unavailable in the `ℓ ∣ z` regime.

## Consequence for the "architectural re-pointing"

Re-pointing the descent step's `h_unit` at the producer-`δ` real-data form therefore does **not**
close R2: in the regime where the descent applies it (`ℓ ∣ z`, the only regime where the descent
unit must be a `37`-th power), the real-data form's hypotheses are contradictory, so it supplies
**no** usable content.  The genuine §9.1 identification — connecting the descent's combinatorial
`ε₁/ε₂` to a `37`-th-power producer unit mod `lv149` **under `ℓ ∣ z`** — requires Washington's
actual §9.1 `η_a` construction at a factor `𝔩 ∣ (ω + ζ^j θ)` that does **not** degenerate, the
Lemma 9.8 / 9.9 content (the all-conjugate `∏_i (ω + ζⁱθ) ≡ 0 (mod 𝔩)` argument).  This is **not**
mere wiring; it is the substantive open arithmetic of R2.

This file imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (descent unit `η_a`,
  pp. 169–173), Lemma 9.6 (`ℓ ∤ a, b`), Lemma 9.7 (`ℓ ∣ z`), Lemma 9.8 (`ℓ ∣ ω+θ`), Lemma 9.9.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-- **The producer-`δ` real-data §9.1 form's hypotheses are jointly unsatisfiable in the `ℓ ∣ z`
regime** (proven, axiom-clean — the precise obstruction to the architectural re-pointing).

For a real Case-II datum `D` with `D.z ∈ lv149` (Washington Lemma 9.7, the descent regime) and
Lemma 9.6 (`D.x ∉ lv149`, `D.y ∉ lv149`), the coprimality
`caseII_data_pair_realGenerator_K D D.etaZero ∉ lv149` (i.e. `Q_η₀ = (x+y)² ∉ lv149`) **cannot
hold**:

* Lemma 9.8 (`caseII_real_x_add_y_mem_of_dvd_z`, PROVEN) gives `D.x + D.y ∈ lv149`;
* hence `Q_η₀ = (D.x + D.y)² ∈ lv149` (`lv149` absorbs products), contradicting `hQ0`.

`caseIISection91DescentUnitIdentificationReal37_proven` (and `caseIISection91_lv149_localPower`)
require exactly this `hQ0`, so they fire **only** when `Q_η₀ ∉ lv149`, i.e. `ℓ ∤ z` — never the
descent regime.  This is why re-pointing the descent step's `h_unit` at the producer-`δ` real-data
form does **not** close R2: it has no usable content where the descent needs it. -/
theorem caseIISection91_real_form_vacuous_in_dvdZ_regime
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hz : D.z ∈ lv149) (hxl : D.x ∉ lv149) (hyl : D.y ∉ lv149)
    (hQ0 : caseII_data_pair_realGenerator_K D D.etaZero ∉ lv149) :
    False := by
  -- Washington Lemma 9.8 over real data: `x + y ∈ lv149`.
  have hxy : D.x + D.y ∈ lv149 := caseII_real_x_add_y_mem_of_dvd_z hSO D hz hxl hyl
  -- `Q_η₀ = (x + y)²`.
  have hQ0eq : caseII_data_pair_realGenerator_K D D.etaZero = (D.x + D.y) ^ 2 :=
    caseII_data_pair_realGenerator_K_at_etaZero_eq_sq D (by decide)
  -- `(x + y)² ∈ lv149`, contradicting `hQ0`.
  exact hQ0 (by rw [hQ0eq, sq]; exact Ideal.mul_mem_left lv149 _ hxy)

end BernoulliRegular.FLT37.Eichler

end
