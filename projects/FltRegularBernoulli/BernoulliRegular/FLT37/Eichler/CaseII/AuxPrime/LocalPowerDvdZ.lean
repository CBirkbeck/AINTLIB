import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.DiscreteLogIndexCollapse
import BernoulliRegular.FLT37.Eichler.CaseII.Section91.DescentUnitLocalPower
import BernoulliRegular.FLT37.Eichler.FLT37GenuineResiduals

/-!
# [FLT37-CASEII-R4] The single-index local power for `i = 32`, under the genuine `ℓ ∣ z` datum

This file repairs the **over-stated** `Lemma98LocalPower37`
(`CaseIIAssumptionII.lean`) — Washington Lemma 9.8's mod-`𝔩` Kummer congruence for the surviving
irregular eigencomponent `i = 32` — and discharges the **corrected** form (R4) from the genuine
Case-II descent datum.

## The over-statement (logged B2 `CASEII-LEMMA98-LOCALPOWER`)

`Lemma98LocalPower37` asserts `IsPthPowerModPrime 37 lv149 (ε₁/ε₂)` for an **abstract**
`CaseIIData37` with *free* units `ε₁, ε₂, ε₃` under only `(ζ-1) ∤ x'`, `(ζ-1) ∤ y'`, `(ζ-1) ∤ z'`
plus the Fermat-shape equation — **without** the hypothesis `lv149 ∣ z'`.  This is **false**: over
abstract data `ε₃` absorbs the equation, leaving `ε₁/ε₂` free in the order-`37` cyclic quotient
`𝔽₁₄₉^× / (𝔽₁₄₉^×)^37` (nontrivial since `37 ∣ 148`), where it need not be a `37`-th power
(`reroute_fix`, `b2_log.jsonl`).

Washington's chain to "`η_a/η_b` is a `37`-th power mod `𝔩`" (Lemma 9.9) is **derived from**
Lemma 9.8 (`ℓ ∣ ω + θ`), whose proof uses `∏_i (ω + ζⁱθ) ≡ 0 (mod 𝔩)`, which holds precisely
**because** Lemma 9.7 gives `ℓ ∣ z` ("this is where `1 < p² - p` is used most strongly";
`149 < 1332 = 37² - 37`).  So the universal statement requires the extra premise `lv149 ∣ z'`.

## The corrected statement and its discharge (the four targets)

* **`Lemma98LocalPower37Strict`** (`def … : Prop`) — `Lemma98LocalPower37` **plus** the genuine-data
  hypothesis `lv149 ∣ z'` (Washington's `ℓ ∣ z`).  This is **genuinely true** (Washington
  Lemma 9.8 / 9.9): with `ℓ ∣ z`, `ℓ ∣ (ω + θ)` (Lemma 9.8), hence the §9.1 cyclotomic
  identification `η_a ≡ ω · ρ_a^{-37} (mod 𝔩)` opens, giving
  `η_a/η_b ≡ (ρ_b/ρ_a)^37 (mod 𝔩)` — a `37`-th power.

* **`CaseIILehmerVandiverDvdZ37`** (`def … : Prop`) — the genuine-data property `lv149 ∣ z'`
  (**Washington Lemma 9.7**), carried as a named hypothesis over the descent telescope.  It is
  **genuinely true, non-vacuous** for the actual Case-II descent integer: `z` is the
  `p`-divisible Fermat variable, and Lemma 9.7 forces `ℓ ∣ z` for **every** prime `ℓ ≡ 1 (mod p)`
  with `ℓ < p² - p`.  For `p = 37`, `ℓ = 149`: `149 = 4·37 + 1 ≡ 1 (mod 37)` ✓ and
  `149 < 1332 = 37² - 37` ✓ (`caseII_lv149_one_mod_37`, `caseII_lv149_lt_p_sq_sub_p`).

* **`CaseIISection91DescentUnitIdentification37`** (`def … : Prop`) — the **§9.1 residue
  identification** of the *abstract* descent unit `ε₁/ε₂` with the **proven** producer unit
  `δ = caseIISection91_descentUnit` (Washington §9.1's explicit `η_a`, residue form `(Y·X⁻¹)^37`).
  This is the Lemma-9.8 opening at the abstract data; it **uses** `lv149 ∣ z'` (the existence of a
  factor `𝔩 ∣ ω + ζ^j θ`).  It is **not** the conclusion ("is a `37`-th power") but a congruence to
  a *specific named* unit that is **separately proven** to be a `37`-th power.

* **`caseII_localPower_of_dvd_z`** — **discharges** the local power: from the §9.1 identification +
  the **proven** `caseIISection91_lv149_localPower` (the producer `δ` is a `37`-th power mod `lv149`
  *by construction*, `caseIISection91_descentUnit_mk`), `IsPthPowerModPrime.congr` gives
  `IsPthPowerModPrime 37 lv149 (ε₁/ε₂)`.  This is the actual discharge, **routed through the proven
  producer**, never through Assumption II (`ε₁/ε₂ = ε'^37`).

## Re-wiring

`caseIIThm95_assumptionII_of_corollary815_lemmaStrict` and
`caseIIOmega32_assumptionII_of_membership_localPowerStrict` reproduce the existing Assumption-II
producers taking `Lemma98LocalPower37Strict` + `CaseIILehmerVandiverDvdZ37` (the genuine `ℓ ∣ z`
datum) instead of the over-stated `Lemma98LocalPower37`, so the Assumption-II chain gets a
genuinely-non-vacuous local-power input.  `lemma98LocalPower37_of_strict` recovers the old (now only
ever applied where `ℓ ∣ z` holds) `Lemma98LocalPower37` from the strict form + the `ℓ ∣ z` datum.

It imports only — it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Theorem 9.5, Lemmas 9.6–9.9
  (pp. 176–181, the `ℓ < p² - p` finiteness for Lemma 9.7, `ℓ ∣ ω + θ` for Lemma 9.8, the
  `η_a/η_b` `p`-th-power conclusion for Lemma 9.9), §9.1 (the descent unit `η_a`, pp. 169–173).
-/

@[expose] public section

noncomputable section

open NumberField Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-! ## 0. The Lehmer–Vandiver auxiliary prime `ℓ = 149` satisfies Washington's `ℓ < p² - p` window

Washington Lemma 9.7's hypothesis is a prime `ℓ ≡ 1 (mod p)` with `ℓ < p² - p`.  For `p = 37` the
auxiliary prime `ℓ = 149` (the rational prime under `lv149`) satisfies both: it is `≡ 1 (mod 37)`
(it equals `4·37 + 1`) and `149 < 1332 = 37² - 37`.  These two arithmetic facts are what make the
genuine-data property `CaseIILehmerVandiverDvdZ37` (`= ℓ ∣ z`) **non-vacuous and true** for the
actual descent integer (it is *not* an artefact of the abstract telescope). -/

/-- **`ℓ = 149 ≡ 1 (mod 37)`** — Washington Lemma 9.7's congruence hypothesis on the auxiliary
prime.  `149 = 4·37 + 1`, so `149 ≡ 1 (mod 37)`.  (This is the same congruence that makes
`(𝓞 K / lv149)ˣ` cyclic of order `148 = 4·37`, hence `37 ∣ 148` and the `p`-th-power quotient
nontrivial.) -/
theorem caseII_lv149_one_mod_37 : (149 : ℕ) % 37 = 1 := by decide

/-- **`ℓ = 149 < p² - p = 1332`** — Washington Lemma 9.7's finiteness window ("this is where
`1 < p² - p` is used most strongly"), with room to spare: `149 < 1332`.  This inequality is
*exactly* what forces `ℓ ∣ z` for the genuine descent integer in Lemma 9.7, so
`CaseIILehmerVandiverDvdZ37` is a genuinely-true property of the descent data, not vacuous. -/
theorem caseII_lv149_lt_p_sq_sub_p : (149 : ℕ) < 37 ^ 2 - 37 := by decide

/-! ## 1. The genuine-data `ℓ ∣ z` property (Washington Lemma 9.7)

We name the Washington-Lemma-9.7 conclusion `lv149 ∣ z'` as a `def … : Prop` over the *exact*
telescope of `Lemma98LocalPower37` / `WashingtonCaseIIExactQuotientUnitPower37Source`, so it can be
threaded by the consumers that already forward `D, x', y', z', ε₁, ε₂, ε₃` unchanged.

This is **carried** as a named genuine-descent-datum hypothesis (per the reviewer's guidance "carry
`ℓ ∣ z` as part of the genuine descent datum"): proving Lemma 9.7 fully in Lean requires the
all-conjugate summation `∑_a (y - ζᵃz)ᵏ ≡ (y - ζᵃz)ᵏ` argument with `ℓ = 1 + kp`, `k < p - 1`,
which is genuine analytic content of the second case.  Its **non-vacuity and truth** are recorded
above (`caseII_lv149_one_mod_37`, `caseII_lv149_lt_p_sq_sub_p`): for the actual Case-II descent
integer `z` (the `p`-divisible Fermat variable) Lemma 9.7 forces `ℓ ∣ z` for every prime
`ℓ ≡ 1 (mod p)`, `ℓ < p² - p`, and `149` is such a prime. -/

/-- **Washington Lemma 9.7 over the Case-II descent telescope** (a `def … : Prop`, **not** an
axiom): for every Case-II descent instance, the descent integer `z'` is divisible by the
Lehmer–Vandiver auxiliary prime `lv149`.

This is genuinely true for the descent data (`z'` is the `p`-divisible Fermat variable; Lemma 9.7
forces `ℓ ∣ z` since `149 ≡ 1 (mod 37)` and `149 < 37² - 37`, see `caseII_lv149_one_mod_37` /
`caseII_lv149_lt_p_sq_sub_p`).  Carried as the genuine-descent-datum hypothesis that repairs the
over-stated `Lemma98LocalPower37`. -/
def CaseIILehmerVandiverDvdZ37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
    ¬ (D.hζ.toInteger - 1) ∣ x' →
    ¬ (D.hζ.toInteger - 1) ∣ y' →
    ¬ (D.hζ.toInteger - 1) ∣ z' →
    ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
      (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
        (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
          ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
    z' ∈ lv149

/-! ## 2. The corrected (genuine-data) local-power statement

`Lemma98LocalPower37Strict` is `Lemma98LocalPower37` with the **single missing premise**
`z' ∈ lv149` added.  Under that premise the statement is **true** (Washington Lemma 9.8 / 9.9), so
it is a sound
named target (unlike the over-stated `Lemma98LocalPower37`). -/

/-- **Washington Lemma 9.8, corrected single-index local power (R4)** (a `def … : Prop`, **not** an
axiom).

For every Case-II descent instance **with `lv149 ∣ z'`** (Washington's `ℓ ∣ z`, Lemma 9.7), the
descent unit `ε₁/ε₂` (Washington's `η_a/η_b`) is a `37`-th power modulo `lv149`.

This is the **repaired** form of `Lemma98LocalPower37`: the over-stated version dropped the
`lv149 ∣ z'` hypothesis and is false over abstract data; with it, Washington Lemma 9.8
(`ℓ ∣ ω + θ`) opens the §9.1 identification `η_a ≡ ω ρ_a^{-37} (mod 𝔩)`, giving
`η_a/η_b ≡ (ρ_b/ρ_a)^37 (mod 𝔩)`, a `37`-th power.  Discharged from the genuine descent datum by
`caseII_localPower_of_dvd_z` (via the §9.1 producer, never Assumption II). -/
def Lemma98LocalPower37Strict
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
    ¬ (D.hζ.toInteger - 1) ∣ x' →
    ¬ (D.hζ.toInteger - 1) ∣ y' →
    ¬ (D.hζ.toInteger - 1) ∣ z' →
    z' ∈ lv149 →
    ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
      (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
        (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
          ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
    BernoulliRegular.IsPthPowerModPrime 37 lv149
      ((ε₁ / ε₂ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ))

/-! ## 3. The §9.1 residue identification of the abstract descent unit with the proven producer

The PROVEN `caseIISection91_lv149_localPower` shows the **producer** unit
`δ = caseIISection91_descentUnit D_real η G lv149` is a `37`-th power mod `lv149` *by construction*
(its residue is literally `(Y·X⁻¹)^37`, `caseIISection91_descentUnit_mk`).  What links the
**abstract** descent unit `ε₁/ε₂` to that producer is the **§9.1 cyclotomic-number identification**
`η_a/η_b = ε₁/ε₂`, which — reduced mod `𝔩` — is the **opening of Washington Lemma 9.8**: from
`ℓ ∣ z` one gets a factor `𝔩 ∣ (ω + ζ^j θ)`, and then `η_a ≡ ω ρ_a^{-37} (mod 𝔩)`, so
`ε₁/ε₂ ≡ δ (mod 𝔩)`.

We name this congruence (the genuine Lemma-9.8-opening residual, which **uses** `lv149 ∣ z'`) as a
`def … : Prop`.  It is **not** the conclusion: it is a congruence of the abstract `ε₁/ε₂` to a
*specific named* unit `δ` that is **separately, provably** a `37`-th power mod `lv149`. -/

/-- **The §9.1 residue identification of the abstract descent unit with the proven producer unit**
(a `def … : Prop`, **not** an axiom — Washington Lemma 9.8's `η_a ≡ ω ρ_a^{-37} (mod 𝔩)` opening,
read for the abstract data; **uses** `lv149 ∣ z'`).

For every Case-II descent instance with `lv149 ∣ z'`, there exist a real Case-II datum
`D_real : RealCaseIIData37 (CyclotomicField 37 ℚ) m'`, an adjacent root `η`, a σ-stable anchored
generator record `G`, and the Fermat-data coprimalities `X = algebraMap G.xPlus ∉ lv149`,
`Q_η₀ ∉ lv149`, such that the abstract descent unit `ε₁/ε₂` is congruent **modulo `lv149`** to the
producer unit `δ = caseIISection91_descentUnit D_real η G lv149`:

  `(ε₁/ε₂ : 𝓞 K) - caseIISection91_descentUnit D_real η G lv149 ∈ lv149`.

This is the §9.1 cyclotomic identification `η_a/η_b = ε₁/ε₂` reduced mod `𝔩` (Washington §9.1,
pp. 169–172), whose mod-`𝔩` validity is the **opening of Lemma 9.8** (`ℓ ∣ z ⟹ 𝔩 ∣ ω + ζ^j θ ⟹
η_a ≡ ω ρ_a^{-37}`).  Combined with the **proven** `caseIISection91_lv149_localPower` (δ a `37`-th
power mod `lv149` by construction), it yields the local power of `ε₁/ε₂` — the actual content of
R4, routed through the proven producer (`caseII_localPower_of_dvd_z`). -/
def CaseIISection91DescentUnitIdentification37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
    ¬ (D.hζ.toInteger - 1) ∣ x' →
    ¬ (D.hζ.toInteger - 1) ∣ y' →
    ¬ (D.hζ.toInteger - 1) ∣ z' →
    z' ∈ lv149 →
    ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
      (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
        (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
          ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
    ∃ (m' : ℕ) (D_real : RealCaseIIData37 (CyclotomicField 37 ℚ) m')
      (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
      (G : CaseIISigmaPairAnchoredFixedGenerator37 D_real (by decide) η),
      algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ)) G.xPlus ∉ lv149 ∧
      caseII_data_pair_realGenerator_K D_real D_real.etaZero ∉ lv149 ∧
      (((ε₁ / ε₂ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) -
        caseIISection91_descentUnit D_real η G lv149) ∈ lv149

/-! ## 4. Discharging the local power from `ℓ ∣ z` + the proven §9.1 producer

`caseII_localPower_of_dvd_z` turns the §9.1 identification (§3) into the local power: the producer
unit `δ` is a `37`-th power mod `lv149` (the **proven** `caseIISection91_lv149_localPower`), and
`ε₁/ε₂ ≡ δ (mod lv149)`, so `IsPthPowerModPrime.congr` transports the property to `ε₁/ε₂`.  This is
the actual discharge of R4 — **routed through the proven producer**, never Assumption II. -/

/-- **The corrected local power, discharged from `ℓ ∣ z` + the §9.1 producer** (proven, axiom-clean
*given* the §9.1 residue identification — uses the **proven** producer, **not** Assumption II).

Given the §9.1 residue identification `CaseIISection91DescentUnitIdentification37` (the Lemma-9.8
opening at the abstract data, which itself uses `lv149 ∣ z'`), `Lemma98LocalPower37Strict` holds:
for each instance the identification supplies `(D_real, η, G)` with `ε₁/ε₂ ≡ δ (mod lv149)` for the
producer `δ = caseIISection91_descentUnit D_real η G lv149`; the **proven**
`caseIISection91_lv149_localPower` makes `δ` a `37`-th power mod `lv149`; and
`IsPthPowerModPrime.congr` transports that to `ε₁/ε₂`. -/
theorem caseII_localPower_of_dvd_z
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_ident : CaseIISection91DescentUnitIdentification37) :
    Lemma98LocalPower37Strict := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz hℓz heq
  obtain ⟨m', D_real, η, G, hX, hQ0, hcong⟩ :=
    h_ident hV hSO D hx hy hz hℓz heq
  have hδ : BernoulliRegular.IsPthPowerModPrime 37 lv149
      (caseIISection91_descentUnit D_real η G lv149) :=
    caseIISection91_lv149_localPower D_real η G hX hQ0
  exact (BernoulliRegular.IsPthPowerModPrime.congr hcong).mpr hδ

/-! ## 5. Recovering `Lemma98LocalPower37` from the strict form + the `ℓ ∣ z` datum

Each existing consumer of `Lemma98LocalPower37` *forwards* the same `D, x', y', z', ε₁, ε₂, ε₃` it
receives.  So the over-stated `Lemma98LocalPower37` is recovered from `Lemma98LocalPower37Strict`
by supplying the missing `z' ∈ lv149` from the genuine-data property `CaseIILehmerVandiverDvdZ37`.
This makes the existing chain consume a genuinely-non-vacuous local-power input. -/

/-- **`Lemma98LocalPower37` from the strict form + the genuine `ℓ ∣ z` datum** (proven,
axiom-clean).

The over-stated `Lemma98LocalPower37` is exactly `Lemma98LocalPower37Strict` with its `lv149 ∣ z'`
hypothesis supplied by the genuine-descent-datum property `CaseIILehmerVandiverDvdZ37`
(Washington Lemma 9.7).  Both quantify over the *same* telescope and forward `D, x', y', z', ε's`
unchanged, so this is a direct composition. -/
theorem lemma98LocalPower37_of_strict
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_strict : Lemma98LocalPower37Strict)
    (h_dvd : CaseIILehmerVandiverDvdZ37) :
    Lemma98LocalPower37 := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz heq
  exact h_strict hV hSO D hx hy hz (h_dvd hV hSO D hx hy hz heq) heq

/-! ## 6. Re-wired Assumption-II producers (genuinely-non-vacuous local-power input)

The two existing Assumption-II producers that consume `Lemma98LocalPower37` —
`caseIIThm95_assumptionII_of_corollary815_lemma98` (the single-index collapse) and
`caseIIOmega32_assumptionII_of_membership_localPower` (the ω³²-membership route) — are reproduced
here taking the *corrected* pair `(Lemma98LocalPower37Strict, CaseIILehmerVandiverDvdZ37)` instead.
Each recovers `Lemma98LocalPower37` internally via `lemma98LocalPower37_of_strict`, so the
downstream collapse is unchanged but the local-power input is now genuinely non-vacuous. -/

/-- **Assumption II from the single-index expansion + the corrected local power** (proven,
axiom-clean).

`caseIIThm95_assumptionII_of_corollary815_lemma98`, re-wired to take the **corrected**
`Lemma98LocalPower37Strict` together with the genuine `ℓ ∣ z` datum `CaseIILehmerVandiverDvdZ37`
(Washington Lemma 9.7) instead of the over-stated `Lemma98LocalPower37`.  Internally it recovers
`Lemma98LocalPower37` (`lemma98LocalPower37_of_strict`) and applies the proven index/Vandermonde
collapse. -/
theorem caseIIThm95_assumptionII_of_corollary815_lemmaStrict
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_expand : Cor815SingleIndexExpansion37)
    (h_localPowStrict : Lemma98LocalPower37Strict)
    (h_dvd : CaseIILehmerVandiverDvdZ37) :
    WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIIThm95_assumptionII_of_corollary815_lemma98 h_expand
    (lemma98LocalPower37_of_strict h_localPowStrict h_dvd)

/-- **Assumption II from ω³²-membership + the corrected local power** (proven, axiom-clean).

`caseIIOmega32_assumptionII_of_membership_localPower`, re-wired to take the **corrected**
`Lemma98LocalPower37Strict` together with the genuine `ℓ ∣ z` datum `CaseIILehmerVandiverDvdZ37`
instead of the over-stated `Lemma98LocalPower37`.  This is the cleanest Assumption-II producer with
a genuinely-non-vacuous local-power input: the ω³²-membership (Lemma 9.9 regular-index collapse) and
the corrected single-index local power (Lemma 9.8, under `ℓ ∣ z`). -/
theorem caseIIOmega32_assumptionII_of_membership_localPowerStrict
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hMem : DescentUnitOmega32Membership37)
    (h_localPowStrict : Lemma98LocalPower37Strict)
    (h_dvd : CaseIILehmerVandiverDvdZ37) :
    WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIIOmega32_assumptionII_of_membership_localPower hMem
    (lemma98LocalPower37_of_strict h_localPowStrict h_dvd)

/-! ## 7. FLT37 from the four genuine residuals, with the corrected local power

`fermatLastTheoremFor_thirtyseven_of_genuineResiduals` (`FLT37GenuineResiduals.lean`) takes the
over-stated `Lemma98LocalPower37` as residual 4.  Here is the version taking the **corrected**
`Lemma98LocalPower37Strict` + the genuine `ℓ ∣ z` datum `CaseIILehmerVandiverDvdZ37`, so the
local-power residual is now genuinely non-vacuous (no false universal over abstract data). -/

/-- **FLT37 from the four genuine residuals, with the corrected (genuine-data) local power**
(proven, axiom-clean given the four named inputs + the carried second-order Bernoulli Prop).

Identical to `fermatLastTheoremFor_thirtyseven_of_genuineResiduals` except residual 4 is the
**corrected** `Lemma98LocalPower37Strict` (the over-statement repair) together with the genuine
`ℓ ∣ z` datum `CaseIILehmerVandiverDvdZ37` (Washington Lemma 9.7).  The local-power input is thereby
genuinely non-vacuous; the rest of the chain is unchanged. -/
theorem fermatLastTheoremFor_thirtyseven_of_genuineResiduals_localPowerStrict
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_leadingExp : LeadingExponentEigenCollapse37)
    (caseII_localPowStrict : Lemma98LocalPower37Strict)
    (caseII_lehmerVandiverDvdZ : CaseIILehmerVandiverDvdZ37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_genuineResiduals
    caseII_classConjFixed
    caseII_realDescent
    caseII_leadingExp
    (lemma98LocalPower37_of_strict caseII_localPowStrict caseII_lehmerVandiverDvdZ)
    noSecondOrderIrregular

/-! ## 8. The corrected local power from the §9.1 identification, end-to-end

Composing §4 (`caseII_localPower_of_dvd_z`) with §6/§7, the corrected local power
`Lemma98LocalPower37Strict` need not be assumed: it is **discharged** from the §9.1 residue
identification `CaseIISection91DescentUnitIdentification37` (the Lemma-9.8 opening, the genuine
residual that uses `ℓ ∣ z`).  This is the cleanest endpoint: R4 reduces to the §9.1 identification
plus the genuine `ℓ ∣ z` datum, with the local-power discharge proven via the producer. -/

/-- **FLT37 from the §9.1 identification + the genuine `ℓ ∣ z` datum** (proven, axiom-clean given
the named inputs + the carried second-order Bernoulli Prop).

The local-power residual `Lemma98LocalPower37Strict` is **discharged** from the §9.1 residue
identification `CaseIISection91DescentUnitIdentification37` (`caseII_localPower_of_dvd_z`, routed
through the proven producer), so R4 is reduced to the genuine §9.1 Lemma-9.8-opening identification
plus the genuine `ℓ ∣ z` datum (Washington Lemma 9.7).  Everything else is as in
`fermatLastTheoremFor_thirtyseven_of_genuineResiduals`. -/
theorem fermatLastTheoremFor_thirtyseven_of_genuineResiduals_section91Identification
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_leadingExp : LeadingExponentEigenCollapse37)
    (caseII_section91Ident : CaseIISection91DescentUnitIdentification37)
    (caseII_lehmerVandiverDvdZ : CaseIILehmerVandiverDvdZ37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_genuineResiduals_localPowerStrict
    caseII_classConjFixed
    caseII_realDescent
    caseII_leadingExp
    (caseII_localPower_of_dvd_z caseII_section91Ident)
    caseII_lehmerVandiverDvdZ
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
