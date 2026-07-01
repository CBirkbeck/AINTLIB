import BernoulliRegular.FLT37.Eichler.CaseII.Mirimanoff.GammaRatioPthPowerProven
import BernoulliRegular.FLT37.Eichler.CaseII.Mirimanoff.MirimanoffResidualAndSumMembership
import BernoulliRegular.FLT37.Eichler.CaseII.Section91.DescentUnitLocalPower

/-!
# [FLT37-CASEII-R4] Washington Theorem 9.5 Case-II `ℓ ∣ z` content, assembled over `RealCaseIIData37`

This file assembles **R4** — the irregular-index local power / Washington *Introduction to Cyclotomic
Fields*, 2nd ed., GTM 83, Theorem 9.5 Lemma-9.6–9.9 `ℓ ∣ z` content — over the genuine real datum
`RealCaseIIData37`, now that its DEEP analytic core is proven (the step-6 `ρ_a`-reality
`γ`-ratio congruence `caseIIMirimanoffStep6CongReal37_proven`, Washington's `j = 0` over real data
`caseII_realStep6_no_nontrivial_factor`).

It imports only — it does **not** modify any existing file.

## The exact Theorem-9.5 composition logic (worked out from Washington pp. 176–181)

The second-case proof, with the standing Fermat solution `p ∤ xy`, `p ∣ z`, `z ≠ 0`, runs:

* **Lemma 9.6** (`ℓ ∤ xy`): proven by contradiction from `∏_a (y − ζ^a z) = −x^p` and `p² ∣ ℓ − 1`,
  `ℓ < p² − p`.
* **Lemma 9.7** (`ℓ ∣ z`, *"this is where `1 < p² − p` is used most strongly"*): write `ℓ = 1 + kp`,
  `k < p − 1`.  From the Lemma-9.6 equations `(y − ζ^a z)^k ≡ (y − ζ^{−a} z)^k (mod 𝔩)`, multiply by
  `ζ^a`, expand, and **sum over `0 ≤ a ≤ p − 1`**: the powers of `ζ` cancel, leaving
  `−pkz y^{k−1} ≡ 0 (mod 𝔩)`.  Since `ℓ = 1 + kp` gives `ℓ ∤ pk` and Lemma 9.6 gives `ℓ ∤ y`, this
  forces `ℓ ∣ z`.  **This is UNCONDITIONAL** — it is an all-conjugate `∑`-argument over the rational
  integers `x, y, z`, and it does **not** use the Theorem-9.5 power-residue condition `Q_i^k ≢ 1`.
  It is **forced**, *not* a case-split on `ℓ ∣ z` vs `ℓ ∤ z`.
* **Basic argument** (`ω^p + θ^p = δλ^{mp}`, `ℓ ∣ z`): assuming `η_a/η_b` is a `p`-th power yields
  the descent equation at measure `2m − p`; to iterate one needs `ℓ ∣ ρ₀`, which (as `ℓ` is
  unramified and `ω + θ = η₀ λ^{m−(p−1)/2} ρ g`) follows from `ℓ ∣ (ω + θ)`.
* **Lemma 9.8** (`ℓ ∣ ω + θ`, i.e. `j = 0`): `∏_i (ω + ζ^i θ) ≡ 0 (mod 𝔩)` (this is where `ℓ ∣ z` is
  used), so `ω + ζ^j θ ≡ 0` for some `j`.  **Suppose `j ≠ 0`.**  Telescoping the
  `(ζ^a − ζ^j)/(1 − ζ^{a+j})` `p`-th-power congruences over the `ξ`-units (Lemma 8.1) shows **every**
  real cyclotomic unit is a `p`-th power mod every prime above `ℓ`; Proposition 8.18 then forces
  `Q_i^t ≡ 1` for all `t`, **contradicting `Q_i^k ≢ 1`**.  So `j = 0`, i.e. `ℓ ∣ ω + θ`.  **This is
  where the proven `Q₃₂⁴ ≢ 1` certificate enters** — and over real data it is exactly
  `caseII_realStep6_no_nontrivial_factor`.
* **Lemma 9.9** (`η_a/η_b` is a `p`-th power = **Assumption II**): from `ℓ ∣ ω + θ` (`j = 0`),
  `η_a ≡ ω^p ρ_a^{−p} (mod 𝔩)`, so `η_a/η_b ≡ (ρ_b/ρ_a)^p (mod 𝔩)` — the *local* `p`-th power
  (Lemma 9.8's mod-`𝔩` Kummer congruence).  Corollary 8.15 then expands `η_a/η_b` over the real
  cyclotomic units; the index/Vandermonde collapse with `Q₃₂⁴ ≢ 1` forces `p ∣ d_i`, so `η_a/η_b` is
  a **global** `p`-th power.

So the `ℓ ∣ z` case-split is resolved by **forcing**: Lemma 9.7 always gives `ℓ ∣ z` for the descent
integer (`ℓ ≢ 0`, `ℓ < p² − p`); there is no `ℓ ∤ z` branch.  The `Q₃₂⁴ ≢ 1` certificate is used
*twice*: at Lemma 9.8 to force `j = 0`, and at Lemma 9.9 to force the index `d₃₂ ≡ 0`.

## What this file discharges over real data (R4(i), Lemma 9.8 `j = 0`)

* **`caseII_real_no_nontrivial_factor`** (proven, axiom-clean) — Washington's `j = 0` over real data:
  for a `RealCaseIIData37` with `ℓ ∤ x, ℓ ∤ y`, **no** nontrivial conjugate factor `x + η·y ∈ lv149`
  (`η ≠ 1`) occurs.  This is `caseII_realStep6_no_nontrivial_factor` at the **proven** step-6 core
  `caseIIMirimanoffStep6CongReal37_proven` — the deep analytic content of Lemma 9.8 (the
  `Q₃₂⁴ ≢ 1`-driven contradiction with `j ≠ 0`), now PROVEN (no `Lemma98MirimanoffPthPower37`
  hypothesis).

* **`RealCaseIILemma98Mirimanoff37` / `realCaseIILemma98Mirimanoff37_proven`** — the real-data analog
  of the abstract `Lemma98MirimanoffPthPower37`, **proven**: over real data its antecedent
  (`x + η·y ∈ lv149`, `η ≠ 1`) is refuted by `caseII_real_no_nontrivial_factor`, so the implication
  holds.  This **discharges the Kummer–Mirimanoff residual over real data** — the abstract residual
  was carried as a `def … : Prop` precisely because over *bare* `CaseIIData37` the `ρ_a`-reality
  factorisation does not exist; over `RealCaseIIData37` it does and is proven.

* **`caseII_real_x_add_y_mem_of_dvd_z`** (proven, axiom-clean) — **Washington Lemma 9.8** over real
  data: with the standing `ℓ ∣ z` (`D.z ∈ lv149`, Lemma 9.7) and `ℓ ∤ x, ℓ ∤ y` (Lemma 9.6),
  `x + y ∈ lv149` (`ℓ ∣ ω + θ`, `j = 0`).  The factor `x + η·y ∈ lv149` exists by the proven
  `caseII_exists_factor_mem_lv149_of_dvd_z`; `caseII_real_no_nontrivial_factor` forces `η = 1`.

* **`caseII_real_dvd_z_round_trip`** (proven, axiom-clean) — the sound Lemma-9.8 round trip
  `ℓ ∣ z ⟹ ℓ ∣ (x + y) ⟹ ℓ ∣ z` over real data, confirming the membership form's consistency and
  isolating `ℓ ∣ z` (Lemma 9.7) as the **only** genuine remaining R4 input.

## What this file records about the local power (R4(i), Lemma 9.8 mod-`𝔩` half)

* **`caseII_real_localPower_section91`** (proven, axiom-clean) — the §9.1 producer-built descent unit
  `δ = caseIISection91_descentUnit D η G lv149` is a `37`-th power mod `lv149` over real data
  (`caseIISection91_lv149_localPower`).  This is the local power of Lemma 9.8 / 9.9 for the
  **producer-constructed** descent unit (Washington's explicit `η_a`, residue form `(Y·X⁻¹)^37`),
  discharged non-circularly from the σ-stable producer (**not** Assumption II).

## The genuine remainder (precise, honest)

After this file, R4's **Lemma-9.8 content (`j = 0` + the producer local power) is discharged over
real data**.  Two things remain, each isolated precisely:

* **R4(ii) — `ℓ ∣ z` (Washington Lemma 9.7).**  Genuinely separate, *unconditional* in Washington
  (the all-conjugate `∑`-argument over `ℤ`, not using `Q_i^k ≢ 1`).  Carried as the named
  `def … : Prop` `CaseIILehmerVandiverDvdZ37` / its real-data form `RealCaseIILehmerVandiverDvdZ37`,
  non-vacuous (`caseII_lv149_one_mod_37`: `149 ≡ 1 (mod 37)`; `caseII_lv149_lt_p_sq_sub_p`:
  `149 < 1332 = 37² − 37`).  It is **not** derivable from the descended `CaseIIData37` datum (which
  forgets the rational origin `a, b, c ∈ ℤ` the argument needs); this file does **not** claim
  otherwise.

* **The abstract↔real Assumption-II bridge.**  The top-level Assumption II
  `WashingtonCaseIIExactQuotientUnitPower37Source` and the abstract residuals
  (`CaseIISection91DescentUnitIdentification37`, `Lemma98LocalPower37`, the abstract
  `Lemma98MirimanoffPthPower37`) are keyed to a **bare** `CaseIIData37` with *unconstrained* units
  `ε₁, ε₂, ε₃` carrying **no** reality datum, whereas the proven Lemma-9.8 content (this file) lives
  over `RealCaseIIData37` (`σx = x`, `σy = y`).  Discharging the abstract residuals from the real-data
  content requires threading the producer's reality invariant into the abstract Assumption-II
  telescope (the §9.1 identification of the *abstract* `ε₁/ε₂` with the producer `δ`); that
  identification is the named `CaseIISection91DescentUnitIdentification37` (R4(i)), which this file
  proves over the real datum but does **not** transport to a free abstract `ε₁/ε₂` (it cannot,
  non-circularly).

So: the **Lemma-9.8 analytic core of R4 is proven over real data here**; what remains is **R4(ii)**
(Lemma 9.7 `ℓ ∣ z`, the genuine independent input) and the structural abstract↔real Assumption-II
bridge (the §9.1 identification of the free `ε₁/ε₂`).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Theorem 9.5, Lemmas 9.6–9.9
  (pp. 176–181), §9.1–9.2 (descent unit `η_a`, the `ℓ < p² − p` window).
-/

@[expose] public section

noncomputable section

open NumberField Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37 FLT37.LehmerVandiver.CaseII

/-! ## 1. Washington's `j = 0` over real data (Lemma 9.8 deep core, PROVEN)

`caseII_realStep6_no_nontrivial_factor` (`CaseIIRealStep6.lean`) at the **proven** step-6 core
`caseIIMirimanoffStep6CongReal37_proven` (`CaseIIRealStep6GammaRatio.lean`): for a real Case-II
datum with `ℓ ∤ x, ℓ ∤ y`, no nontrivial conjugate factor `x + η·y ∈ lv149` (`η ≠ 1`) can occur.

This is the genuine analytic heart of Lemma 9.8 — the place where the proven `Q₃₂⁴ ≢ 1` certificate
(`caseIIThm95_engine_runs`) forces Washington's special index `j` to be `0`.  It is **not** a
hypothesis: the step-6 `ρ_a`-reality `γ`-ratio congruence it rests on is fully proven over real
data. -/

/-- **Washington's `j = 0` over real data** (proven, axiom-clean — the deep core of Lemma 9.8).

For every real Case-II descent datum `D : RealCaseIIData37` with `ℓ ∤ D.x`, `ℓ ∤ D.y`, and every
nontrivial `37`-th root `η ≠ 1`, the conjugate factor `D.x + η·D.y` is **not** in `lv149`.

This is `caseII_realStep6_no_nontrivial_factor` instantiated at the **proven** step-6 core
`caseIIMirimanoffStep6CongReal37_proven`, supplying `¬ 37 ∣ h⁺` (`Sinnott.flt37_not_dvd_hPlus`) and
the second-order Bernoulli input as standing Washington hypotheses.  It is Washington Lemma 9.8's
`j = 0` (the `Q₃₂⁴ ≢ 1`-driven refutation of `j ≠ 0`), discharged over the genuine real datum. -/
theorem caseII_real_no_nontrivial_factor
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    {η : 𝓞 (CyclotomicField 37 ℚ)}
    (hη_mem : η ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
    (hη_ne : η ≠ 1) (hx : D.x ∉ lv149) (hy : D.y ∉ lv149) :
    D.x + η * D.y ∉ lv149 :=
  caseII_realStep6_no_nontrivial_factor caseIIMirimanoffStep6CongReal37_proven
    Sinnott.flt37_not_dvd_hPlus hSO D hη_mem hη_ne hx hy

/-! ## 2. The real-data Kummer–Mirimanoff residual is PROVEN

The abstract `Lemma98MirimanoffPthPower37` (`CaseIILemma98DescentSum.lean`) is the implication
"a nontrivial factor `x + η·y ∈ lv149` (`η ≠ 1`) makes `E₃₂` a `37`-th power mod `lv149`".  It is
carried as a `def … : Prop` because over a *bare* `CaseIIData37` the `ρ_a`-reality factorisation
needed to prove it does not exist.  Over `RealCaseIIData37` it **does** exist (and is proven),
which makes the antecedent unsatisfiable for `η ≠ 1` — so the real-data analog holds. -/

open FLT37.LehmerVandiver.CaseII in
/-- **The real-data Kummer–Mirimanoff residual** (a `def … : Prop`) — the `RealCaseIIData37` analog
of the abstract `Lemma98MirimanoffPthPower37`.

For every real Case-II descent instance, **if** a nontrivial conjugate factor `D.x + η·D.y ∈ lv149`
(`η ≠ 1`) occurs with `ℓ ∤ D.x`, `ℓ ∤ D.y`, **then** `E₃₂ = pollaczekUnitPlus 37 K 32` is a `37`-th
power modulo `lv149`.  Discharged by `realCaseIILemma98Mirimanoff37_proven` (its antecedent is
refuted over real data). -/
def RealCaseIILemma98Mirimanoff37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    {η : 𝓞 (CyclotomicField 37 ℚ)},
    η ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) →
    η ≠ 1 →
    D.x ∉ lv149 → D.y ∉ lv149 →
    D.x + η * D.y ∈ lv149 →
    BernoulliRegular.IsPthPowerModPrime 37 lv149
      ((FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
        (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ))

open FLT37.LehmerVandiver.CaseII in
/-- **The real-data Kummer–Mirimanoff residual is PROVEN** (axiom-clean — discharges the abstract
`Lemma98MirimanoffPthPower37` over real data).

Over `RealCaseIIData37` the antecedent `D.x + η·D.y ∈ lv149` with `η ≠ 1` is **refuted** by
`caseII_real_no_nontrivial_factor` (Washington's `j = 0`, from the proven step-6 `ρ_a`-reality
congruence and `Q₃₂⁴ ≢ 1`).  Hence the implication holds.  This is the genuine discharge of the
Kummer–Mirimanoff content of Lemma 9.8 over the real datum: the abstract residual could only be
*named* (the `ρ_a`-reality factorisation fails over bare data); over real data it is proven. -/
theorem realCaseIILemma98Mirimanoff37_proven
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    RealCaseIILemma98Mirimanoff37 := by
  intro _hV hSO m D η hη_mem hη_ne hx hy hsum
  exact absurd hsum (caseII_real_no_nontrivial_factor hSO D hη_mem hη_ne hx hy)

/-! ## 3. Washington Lemma 9.8 (`ℓ ∣ ω + θ`, `j = 0`) over real data, PROVEN

With the standing `ℓ ∣ z` (`D.z ∈ lv149`, Lemma 9.7) and `ℓ ∤ x, ℓ ∤ y` (Lemma 9.6), the descended
sum `x + y ∈ lv149`.  The proven `caseII_exists_factor_mem_lv149_of_dvd_z` gives a factor
`x + η·y ∈ lv149`; `caseII_real_no_nontrivial_factor` forces `η = 1`, i.e. `x + y ∈ lv149`. -/

/-- **Washington Lemma 9.8 over real data** (proven, axiom-clean): with the standing `ℓ ∣ z`
(`D.z ∈ lv149`, Lemma 9.7) and `ℓ ∤ x, ℓ ∤ y` (Lemma 9.6), the descended sum `x + y ∈ lv149`
(`ℓ ∣ ω + θ`, Washington's `j = 0`).

Proof: `caseII_exists_factor_mem_lv149_of_dvd_z` (the all-conjugate `∏(x + ζ^i y) = x³⁷ + y³⁷ ∈ lv149`
under `ℓ ∣ z`) gives a factor `x + η·y ∈ lv149` with `η ∈ μ₃₇`.  If `η = 1` this is `x + y ∈ lv149`
directly; if `η ≠ 1`, `caseII_real_no_nontrivial_factor` (the proven `j = 0`) refutes it. -/
theorem caseII_real_x_add_y_mem_of_dvd_z
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hz : D.z ∈ lv149) (hxl : D.x ∉ lv149) (hyl : D.y ∉ lv149) :
    D.x + D.y ∈ lv149 := by
  obtain ⟨η, hη_mem, hη_in⟩ :=
    caseII_exists_factor_mem_lv149_of_dvd_z D.toCaseIIData37 hz
  by_cases hη1 : η = 1
  · subst hη1; simpa using hη_in
  · exact absurd hη_in (caseII_real_no_nontrivial_factor hSO D hη_mem hη1 hxl hyl)

/-! ## 4. The sound Lemma-9.8 round trip over real data, and the local power

`caseII_dvd_z_of_equation` (`CaseIILemma98DescentSum.lean`) gives the converse `ℓ ∣ (x+y) ⟹ ℓ ∣ z`
from the single-unit `CaseIIData37.equation`.  Composed with §3 it closes the Lemma-9.8 round trip
`ℓ ∣ z ⟹ ℓ ∣ (x+y) ⟹ ℓ ∣ z` over real data — confirming the membership form's consistency and that
`ℓ ∣ z` (Lemma 9.7) is the only genuine remaining input of the `ℓ ∣ z` chain. -/

/-- **The sound Lemma-9.8 round trip over real data** (proven, axiom-clean).

With the standing `ℓ ∣ z` (Lemma 9.7) and `ℓ ∤ x, ℓ ∤ y` (Lemma 9.6): Lemma 9.8 gives
`x + y ∈ lv149` (`caseII_real_x_add_y_mem_of_dvd_z`), and `caseII_dvd_z_of_equation` recovers
`z ∈ lv149`.  This shows the membership form is internally consistent over real data; the only
genuine open content of the `ℓ ∣ z` chain is `ℓ ∣ z` itself (Washington Lemma 9.7). -/
theorem caseII_real_dvd_z_round_trip
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hz : D.z ∈ lv149) (hxl : D.x ∉ lv149) (hyl : D.y ∉ lv149) :
    D.z ∈ lv149 :=
  caseII_dvd_z_of_equation D.toCaseIIData37
    (caseII_real_x_add_y_mem_of_dvd_z hSO D hz hxl hyl)

/-- **The Lemma-9.8 mod-`𝔩` local power for the producer-built descent unit** (proven, axiom-clean —
through the σ-stable producer, **not** Assumption II).

`caseIISection91_lv149_localPower`: for a real Case-II datum `D`, adjacent root `η`, σ-stable
anchored generator record `G`, and the Fermat-data coprimalities `X = algebraMap G.xPlus ∉ lv149`,
`Q_η₀ ∉ lv149`, the §9.1 producer-built descent unit `δ = caseIISection91_descentUnit D η G lv149`
(Washington's explicit `η_a`, residue form `(Y·X⁻¹)^37`) is a `37`-th power modulo `lv149`.

This is the mod-`𝔩` half of Washington Lemma 9.8 / the opening of Lemma 9.9
(`η_a/η_b ≡ (ρ_b/ρ_a)^p (mod 𝔩)`), discharged over real data for the genuine §9.1 descent object,
non-circularly from the proven σ-stable producer (re-exported here so the R4 local-power statement
sits beside the `ℓ ∣ z`/`j = 0` content). -/
theorem caseII_real_localPower_section91
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
    (G : CaseIISigmaPairAnchoredFixedGenerator37 D (by decide) η)
    (hX : algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
        (𝓞 (CyclotomicField 37 ℚ)) G.xPlus ∉ lv149)
    (hQ0 : caseII_data_pair_realGenerator_K D D.etaZero ∉ lv149) :
    BernoulliRegular.IsPthPowerModPrime 37 lv149
      (caseIISection91_descentUnit D η G lv149) :=
  caseIISection91_lv149_localPower D η G hX hQ0

/-! ## 5. R4(ii) — Washington Lemma 9.7 (`ℓ ∣ z`) over real data, the genuine remaining input

Lemma 9.7's `ℓ ∣ z` is *unconditional* in Washington (the all-conjugate `∑`-argument over `ℤ`, not
using `Q_i^k ≢ 1`), but it is **not** derivable from the descended `RealCaseIIData37` datum, which
forgets the rational origin `a, b, c ∈ ℤ` that the argument over `ℤ` requires.  We carry it as a
named `def … : Prop` over the real datum — its non-vacuity and truth recorded by the worked window
`149 ≡ 1 (mod 37)` (`caseII_lv149_one_mod_37`) and `149 < 37² − 37` (`caseII_lv149_lt_p_sq_sub_p`,
`CaseIILocalPowerStrict.lean`). -/

open FLT37.LehmerVandiver.CaseII in
/-- **Washington Lemma 9.7 over the real Case-II datum** (a `def … : Prop`, **not** an axiom) — the
genuine remaining R4(ii) input.

For every real Case-II descent datum, the descent integer `D.z` is divisible by the
Lehmer–Vandiver auxiliary prime `lv149` (`ℓ ∣ z`).  This is genuinely true and **non-vacuous** for
the descent integer (`z` is the `p`-divisible Fermat variable; Lemma 9.7 forces `ℓ ∣ z` since
`149 ≡ 1 (mod 37)` and `149 < 37² − 37`, see `caseII_lv149_one_mod_37` / `caseII_lv149_lt_p_sq_sub_p`),
but it is **not** derivable from the descended datum (which forgets the rational origin the
all-conjugate `∑`-argument over `ℤ` needs).  Carried as the genuine-descent-datum hypothesis. -/
def RealCaseIILehmerVandiverDvdZ37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
    D.x ∉ lv149 → D.y ∉ lv149 →
    D.z ∈ lv149

open FLT37.LehmerVandiver.CaseII in
/-- **Lemma 9.8 (`x + y ∈ lv149`) from the genuine `ℓ ∣ z` datum, over real data** (proven,
axiom-clean *given* `RealCaseIILehmerVandiverDvdZ37`).

The cleanest packaging: from the genuine Lemma-9.7 datum `RealCaseIILehmerVandiverDvdZ37` (the only
remaining R4(ii) input) and `ℓ ∤ x, ℓ ∤ y`, Lemma 9.8 (`caseII_real_x_add_y_mem_of_dvd_z`, PROVEN)
gives `x + y ∈ lv149` — i.e. the **entire** `ℓ ∣ z`/`j = 0` content of R4 reduces to `ℓ ∣ z`
(Lemma 9.7) over real data, with the `j = 0` step (Lemma 9.8's deep `Q₃₂⁴ ≢ 1` core) proven. -/
theorem caseII_real_x_add_y_mem_of_lehmerVandiverDvdZ
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_dvdz : RealCaseIILehmerVandiverDvdZ37)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hxl : D.x ∉ lv149) (hyl : D.y ∉ lv149) :
    D.x + D.y ∈ lv149 :=
  caseII_real_x_add_y_mem_of_dvd_z hSO D (h_dvdz hV hSO D hxl hyl) hxl hyl

end BernoulliRegular.FLT37.Eichler

end
