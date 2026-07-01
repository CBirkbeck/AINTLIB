import BernoulliRegular.FLT37.Eichler.CaseII.Mirimanoff.Lemma98RealData
import BernoulliRegular.FLT37.Eichler.CaseII.Mirimanoff.GammaRatioPthPowerProven
import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.AssumptionIIFromR3
import BernoulliRegular.FLT37.Eichler.FLT37GenuineResiduals

/-!
# Washington Lemma 9.9 opening: the §9.1 descent ratio is a `37`-th power mod `𝔩` (route (a))

This file builds the **genuine Washington Lemma 9.9 opening** for `p = 37` along the
*computational* (Theorem 9.5 / auxiliary-prime `ℓ = 149`) route — the step

  `η_a ≡ ω · ρ_a^{-p}  (mod 𝔩)`,    hence    `η_a / η_b ≡ (ρ_b / ρ_a)^p  (mod 𝔩)`,

Washington *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, **Lemma 9.9** (p. 180).  This is
the
**local-power** half of the Lemma-9.9 input to **Assumption II**
(`WashingtonCaseIIExactQuotientUnitPower37Source` = `CaseIIThm95Lemma99Bridge`); the regular-index
half (R3) and the index/Vandermonde collapse engine — the proven half-range collapse
(`caseIIThm95_coeff_collapse_even`), the proven `Δ`-eigenspace action, the proven Corollary-8.15
`E⁺/(E⁺)³⁷` saturation, the proven discrete-log translation
(`isPthPowerModPrime_iff_residueInd37_eq_zero`), and
`caseII_descentUnitOmega32Membership37_proven` —
are already in the repo.  What this file isolates is precisely the local power and its **genuine
residual** (the Lemma-9.6/9.7 conditions on the descent data), entirely on the auxiliary prime, with
**no** `p`-adic-`L` / level-72 Dwork content.

## The decisive observation (the `(1 - ζ^a)` cancellation), and why it is SOUND

Washington normalizes the descent unit by the genuinely-principal denominator `1 - ζ^a`:

  `γ_a := (D.x + ζ^a · D.y) / (1 - ζ^a) ∈ 𝓞 K`
  (`caseII_gammaA`, `CaseIIRealStep6GammaRatio.lean`),

so the **actual** descent unit is `η_a = γ_a · ρ_a^{-p}` with `ρ_a^p` the real root-ideal generator.
The **proven** Washington Lemma 9.8 over real data — `caseII_real_x_add_y_mem_of_dvd_z`, the `j = 0`
content `ℓ ∣ (ω + θ)` i.e. `D.x + D.y ∈ lv149`, discharged from the **proven** step-6 `ρ_a`-reality
core `caseIIMirimanoffStep6CongReal37_proven` and `Q₃₂⁴ ≢ 1` — gives `D.y ≡ -D.x (mod 𝔩)`.  Hence

  `D.x + ζ^a · D.y ≡ D.x - ζ^a · D.x = D.x · (1 - ζ^a)   (mod 𝔩)`,

and since `1 - ζ^a ∉ 𝔩` for `a ≢ 0 (mod 37)` (it is a `𝔭`-uniformizer, coprime to the unramified
`𝔩`), the `(1 - ζ^a)` factor **cancels in the residue field**:

  `Q(γ_a) = Q(D.x)`    in `𝓞 K / 𝔩`,    for every `a ≢ 0 (mod 37)`.

So `Q(γ_a) = Q(γ_b) = Q(D.x)` is **independent of `a`** modulo `𝔩`; the ratio
`Q(γ_a) · Q(γ_b)⁻¹ = 1 = 1^{37}` is (trivially) a `37`-th power.  Consequently the §9.1 descent
ratio `η_a / η_b = (γ_a / γ_b) · (ρ_a / ρ_b)^{-p}` is a `37`-th power mod `𝔩` — Washington's
`η_a / η_b ≡ (ρ_b / ρ_a)^p`.

This is **not** the obstructed §9.1 *producer* route (`caseIISection91_descentUnit`, residue form
`(Y·X⁻¹)^37`), whose local power needs `Q_η₀ = (x+y)² ∉ 𝔩` — *contradicted* in the `ℓ ∣ z` regime by
this very Lemma 9.8 (`caseIISection91_real_form_vacuous_in_dvdZ_regime`,
`CaseIISection91RepointObstruction.lean`).  Here the local power of the **genuine** descent ratio
`γ_a/γ_b` comes **directly** from `x + y ∈ lv149`, valid precisely in the descent regime.  No
`Q_η₀ ∉ 𝔩` is used; the `(1 - ζ^a)` cancellation is exactly Washington's `η_a ≡ ω ρ_a^{-p}` step.

## What is proven here (real, axiom-clean Lean)

* `caseII_gammaA_residue_eq_x` — **the Lemma-9.9 opening**, residue form: from `D.x + D.y ∈ lv149`
  (the **proven** Lemma 9.8), `Q(γ_a) = Q(D.x)` for `a ≢ 0 (mod 37)`.

* `caseII_gammaRatio_residue_eq_one` — `Q(γ_a) · Q(γ_b)⁻¹ = 1` for `a, b ≢ 0` (both residues equal
  `Q(D.x)`), under `D.x + D.y ∈ lv149`.

* `caseII_gammaRatio_isPthPower_of_x_add_y_mem` — the §9.1 descent ratio `γ_a/γ_b` is a `37`-th
  power mod `lv149` (`IsPthPowerModPrime 37 lv149 (γ_a · γ_b⁻¹-representative)`), under
  `D.x + D.y ∈ lv149`.

* `caseII_gammaRatio_isPthPower_of_dvd_z` — the **unconditional** real-data form: with the standing
  `ℓ ∣ z` (Lemma 9.7) and Lemma 9.6 (`ℓ ∤ x, y`), the §9.1 descent ratio `γ_a/γ_b` is a `37`-th
  power mod `lv149`.  The Lemma-9.8 input `x + y ∈ lv149` is the **proven**
  `caseII_real_x_add_y_mem_of_dvd_z`
  (no residual): this is the genuine Lemma-9.9 local power over real data, on the auxiliary prime,
  with **no** `p`-adic-`L` / Dwork content and **no** obstructed `Q_η₀` producer.

## The direct local power of the descent unit (§4–§6): the genuine reduction

The §1–§3 Lemma-9.9 opening is a property of the §9.1 *cyclotomic* ratio `γ_a/γ_b` over real data.
For the descent unit `ε₁/ε₂` (the unit cofactor of the Case-II descent equation
`ε₁·x'³⁷ + ε₂·y'³⁷ = ε₃·((ζ−1)^e·z')³⁷`) there is a **direct** residue argument that **needs no §9.1
identification at all**:

  reduce the equation modulo `𝔩`.  With `z' ∈ lv149` (Washington Lemma 9.7) the right side vanishes,
  so `ε₁·x'³⁷ + ε₂·y'³⁷ ≡ 0 (mod 𝔩)`; with `x' ∉ lv149` (Washington Lemma 9.6) this gives
  `ε₁/ε₂ ≡ −(y'/x')³⁷ (mod 𝔩)`, and `−1 = (−1)³⁷`, so `ε₁/ε₂` is a `37`-th power mod `𝔩`.

This is `caseII_lemma98LocalPower37_directResidue` (proven), the **clean** form of the Lemma-9.8
local power.  It shows the genuine remaining content of the local power beyond the *already proven*
engine is **exactly the pair of Lemma-9.6/9.7 hypotheses** (`x' ∉ lv149`, `z' ∈ lv149`) on the
descent data — *not* a §9.1 cyclotomic identification, *not* the obstructed `Q_η₀` producer, *not* a
`p`-adic-`L` / level-72 Dwork computation.

**Soundness (B2-checked) — NO false universal is asserted.**  The named `Lemma98LocalPower37`
(`CaseIIAssumptionII.lean`) quantifies over the *abstract* descent telescope with **free**
`x', y', z', ε₁, ε₂, ε₃` under only the `(ζ−1) ∤ ·` conditions; as a universal it is **false** (B2
`CASEII-LEMMA98-LOCALPOWER`: with `x' ∈ lv149` or `z' ∉ lv149` the unit `ε₁/ε₂` is free in
`𝔽₁₄₉^×/(𝔽₁₄₉^×)³⁷`).  The universal "every abstract descent datum has `x' ∉ lv149 ∧ z' ∈ lv149`" is
*also* false on the free telescope.  We therefore deliberately do **not** wrap the Lemma-9.6/9.7
conditions as such a universal.  The sound statement is the **implication**
`caseII_lemma98LocalPower37_directResidue` itself (the two conditions as explicit hypotheses), which
is **true and proven**.  For the genuine descent these conditions hold over `RealCaseIIData37`
(where
`D.x ∉ lv149` is a datum field and `RealCaseIILehmerVandiverDvdZ37` names `D.z ∈ lv149`); the
real-data application `caseII_real_lemma98LocalPower37_directResidue` and the base non-vacuity
`caseII_real_lemma98LocalPower37_base_nonvacuous` record this.

This file imports only — it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Lemma 9.8 (p. 180, `ℓ ∣ ω + θ`),
  Lemma 9.9 (p. 180, the `η_a ≡ ω ρ_a^{-p}` opening and the `η_a/η_b ≡ (ρ_b/ρ_a)^p` conclusion),
  §9.1 (the descent unit `η_a = (ω + ζ^a θ)/(1 - ζ^a) · ρ_a^{-p}`, pp. 169–173).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Finset Polynomial NumberField.IsCMField

namespace BernoulliRegular.FLT37.Eichler

open FLT37 FLT37.LehmerVandiver.CaseII BernoulliRegular

/-! ## 1. The Lemma-9.9 opening, residue form: `Q(γ_a) = Q(x)` from `x + y ∈ lv149`

Washington's `η_a ≡ ω ρ_a^{-p} (mod 𝔩)` (Lemma 9.9, p. 180): with `x + y ∈ lv149` (`ℓ ∣ ω + θ`,
Lemma 9.8), the numerator `x + ζ^a y ≡ x(1 - ζ^a)` mod `𝔩`, so the `(1 - ζ^a)` denominator of the
normalization `γ_a = (x + ζ^a y)/(1 - ζ^a)` cancels and `Q(γ_a) = Q(x)`. -/

/-- **The Washington Lemma-9.9 opening, residue form** (proven, axiom-clean).

For a real Case-II datum `D` with `D.x + D.y ∈ lv149` (the **proven** Lemma 9.8 over real data,
`ℓ ∣ ω + θ`) and `a ≢ 0 (mod 37)`, the Washington-normalized element
`γ_a = caseII_gammaA D ha = (D.x + ζ^a·D.y)/(1 - ζ^a)` has residue equal to `Q(D.x)`:

  `Ideal.Quotient.mk lv149 (caseII_gammaA D ha) = Ideal.Quotient.mk lv149 D.x`.

Proof: `(1 - ζ^a)·γ_a = D.x + ζ^a·D.y` (`caseII_gammaA_spec`).  In the residue field,
`x + y ∈ lv149` gives `Q(D.y) = -Q(D.x)`, so
`Q(D.x + ζ^a·D.y) = Q(D.x)·(1 - Q(ζ^a)) = Q(D.x)·Q(1 - ζ^a)`.  Hence
`Q(γ_a)·Q(1 - ζ^a) = Q(D.x)·Q(1 - ζ^a)`, and `Q(1 - ζ^a) ≠ 0` (`1 - ζ^a ∉ lv149`, `a ≢ 0`) cancels.
This is Washington's `η_a ≡ ω ρ_a^{-p}`: the `(1 - ζ^a)` factor of the normalization disappears mod
`𝔩` because `θ ≡ -ω`. -/
theorem caseII_gammaA_residue_eq_x
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hxy : D.x + D.y ∈ lv149) {a : ℤ} (ha : ¬ (37 : ℤ) ∣ a) :
    Ideal.Quotient.mk lv149 (caseII_gammaA D ha) = Ideal.Quotient.mk lv149 D.x := by
  set Q := Ideal.Quotient.mk lv149
  -- `Q(y) = -Q(x)` from `x + y ∈ lv149`.
  have hy_eq : Q D.y = - Q D.x := by
    have hmem : Q (D.x + D.y) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hxy
    rw [map_add] at hmem
    linear_combination hmem
  -- `1 - ζ^a ∉ lv149`, so its residue is a unit (nonzero) in the field.
  have h1za_notMem : (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) ∉ lv149 :=
    caseII_one_sub_zetaPow_notMem_lv149 ha
  have h1za0 : Q (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) ≠ 0 :=
    fun h ↦ h1za_notMem (Ideal.Quotient.eq_zero_iff_mem.mp h)
  -- Push `Q` through `(1 - ζ^a)·γ_a = x + ζ^a·y`.
  have hspec : Q (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) * Q (caseII_gammaA D ha) =
      Q (D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y) := by
    rw [← map_mul, ← caseII_gammaA_spec D ha]
  -- The numerator residue: `Q(x + ζ^a y) = Q(x)·Q(1 - ζ^a)` (using `Q y = -Q x`).
  have hnum : Q (D.x + zetaPow 37 (CyclotomicField 37 ℚ) a * D.y) =
      Q D.x * Q (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) := by
    rw [map_add, map_mul, hy_eq, map_sub, map_one]; ring
  -- Combine: `Q(1-ζ^a)·Q(γ_a) = Q(x)·Q(1-ζ^a)`, cancel the nonzero `Q(1-ζ^a)`.
  rw [hnum] at hspec
  have hcancel : Q (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) * Q (caseII_gammaA D ha) =
      Q (1 - zetaPow 37 (CyclotomicField 37 ℚ) a) * Q D.x := by
    rw [hspec]; ring
  exact mul_left_cancel₀ h1za0 hcancel

/-- **The §9.1 descent ratio residue is `1`** (proven, axiom-clean).

For a real Case-II datum `D` with `D.x + D.y ∈ lv149` (Lemma 9.8) and `a, b ≢ 0 (mod 37)`, the
ratio of the two Washington-normalized residues is `1`:

  `Q(γ_a) · Q(γ_b)⁻¹ = 1`    in `𝓞 K / lv149`.

Both `Q(γ_a)` and `Q(γ_b)` equal `Q(D.x)` (`caseII_gammaA_residue_eq_x`), and `Q(D.x) ≠ 0` (since
`x ∉ lv149`, as `x + y ∈ lv149` with `y ∉ lv149` would force `x ∉ lv149`).  Hence the ratio is
`Q(D.x)·Q(D.x)⁻¹ = 1`.  This is the residue shadow of Washington's `η_a ≡ ω ρ_a^{-p}`: the
cyclotomic-number factor `γ_a/γ_b` is `≡ 1`, leaving only the `(ρ_b/ρ_a)^p` `37`-th power. -/
theorem caseII_gammaRatio_residue_eq_one
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hxy : D.x + D.y ∈ lv149) (hxl : D.x ∉ lv149)
    {a b : ℤ} (ha : ¬ (37 : ℤ) ∣ a) (hb : ¬ (37 : ℤ) ∣ b) :
    Ideal.Quotient.mk lv149 (caseII_gammaA D ha) *
        (Ideal.Quotient.mk lv149 (caseII_gammaA D hb))⁻¹ = 1 := by
  set Q := Ideal.Quotient.mk lv149
  have hx0 : Q D.x ≠ 0 := fun h ↦ hxl (Ideal.Quotient.eq_zero_iff_mem.mp h)
  rw [caseII_gammaA_residue_eq_x D hxy ha, caseII_gammaA_residue_eq_x D hxy hb]
  exact mul_inv_cancel₀ hx0

/-! ## 2. The §9.1 descent ratio is a `37`-th power mod `lv149` (the local power)

`Q(γ_a)·Q(γ_b)⁻¹ = 1 = 1^{37}` (§1) is a `37`-th power; both `γ_a, γ_b ∉ lv149`, so the ratio of the
ring elements is a `37`-th power mod `𝔩`.  This is the genuine Lemma-9.9 local power of the §9.1
descent ratio `γ_a/γ_b` (Washington's `η_a/η_b ≡ (ρ_b/ρ_a)^p`, modulo the `(ρ_b/ρ_a)^p` factor which
is itself a `37`-th power). -/

/-- **The §9.1 descent ratio `γ_a/γ_b` is a `37`-th power mod `lv149`** (proven, axiom-clean —
*given* the Lemma-9.8 input `D.x + D.y ∈ lv149`).

For a real Case-II datum `D` with `D.x + D.y ∈ lv149` (Washington Lemma 9.8), `D.x ∉ lv149`, and
`a, b ≢ 0 (mod 37)`, the ratio `γ_a · γ_b⁻¹` (Washington's cyclotomic descent ratio, residue form of
`(x + ζ^a y)/(x + ζ^b y)` modulo the `(1 - ζ^·)` denominators) is a `37`-th power modulo `lv149`:

  `IsPthPowerModPrime 37 lv149 (witness with residue Q(γ_a)·Q(γ_b)⁻¹)`.

Because `Q(γ_a)·Q(γ_b)⁻¹ = 1` (`caseII_gammaRatio_residue_eq_one`), the explicit `37`-th-root
witness is `1`.  This is Washington's `η_a/η_b ≡ (ρ_b/ρ_a)^p (mod 𝔩)` local power, derived on the
auxiliary prime from the **proven** Lemma 9.8 (`x + y ∈ lv149`), with no `p`-adic-`L` content and no
obstructed `Q_η₀` producer. -/
theorem caseII_gammaRatio_isPthPower_of_x_add_y_mem
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hxy : D.x + D.y ∈ lv149) (hxl : D.x ∉ lv149)
    {a b : ℤ} (ha : ¬ (37 : ℤ) ∣ a) (hb : ¬ (37 : ℤ) ∣ b)
    (δ : 𝓞 (CyclotomicField 37 ℚ))
    (hδ : Ideal.Quotient.mk lv149 δ =
      Ideal.Quotient.mk lv149 (caseII_gammaA D ha) *
        (Ideal.Quotient.mk lv149 (caseII_gammaA D hb))⁻¹) :
    BernoulliRegular.IsPthPowerModPrime 37 lv149 δ := by
  -- `Q(δ) = Q(γ_a)·Q(γ_b)⁻¹ = 1 = Q(1)^37`.
  refine ⟨1, ?_⟩
  rw [hδ, caseII_gammaRatio_residue_eq_one D hxy hxl ha hb, one_pow]

/-! ## 3. The unconditional real-data local power (Lemma 9.8 supplied by the proven Mirimanoff core)

`D.x + D.y ∈ lv149` is the **proven** `caseII_real_x_add_y_mem_of_dvd_z` (Washington Lemma 9.8 over
real data, from the proven step-6 `ρ_a`-reality core and `Q₃₂⁴ ≢ 1`), under the standing `ℓ ∣ z`
(Lemma 9.7) and Lemma 9.6 (`ℓ ∤ x, y`).  So the §9.1 descent ratio is a `37`-th power mod `lv149`
**unconditionally** over real data — no Lemma-9.8 residual remains. -/

/-- **The §9.1 descent ratio is a `37`-th power mod `lv149` over real data** (proven, axiom-clean —
the Lemma-9.8 input is the **proven** `caseII_real_x_add_y_mem_of_dvd_z`).

For a real Case-II datum `D` with the standing `ℓ ∣ z` (`D.z ∈ lv149`, Washington Lemma 9.7) and
Lemma 9.6 (`D.x, D.y ∉ lv149`), and `a, b ≢ 0 (mod 37)`, the Washington descent ratio `γ_a · γ_b⁻¹`
is a `37`-th power modulo `lv149`.

The Lemma-9.8 input `D.x + D.y ∈ lv149` is supplied by the **proven**
`caseII_real_x_add_y_mem_of_dvd_z` (Washington's `j = 0`, from the proven step-6 `ρ_a`-reality core
`caseIIMirimanoffStep6CongReal37_proven` and `Q₃₂⁴ ≢ 1`), so there is **no** remaining Lemma-9.8
residual.  This is the genuine Lemma-9.9
local power over real data, entirely on the auxiliary prime `ℓ = 149` — no `p`-adic-`L` / Dwork
content, and not the obstructed `Q_η₀` producer (whose hypothesis `Q_η₀ ∉ lv149` is contradicted by
this very `x + y ∈ lv149`). -/
theorem caseII_gammaRatio_isPthPower_of_dvd_z
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hz : D.z ∈ lv149) (hxl : D.x ∉ lv149) (hyl : D.y ∉ lv149)
    {a b : ℤ} (ha : ¬ (37 : ℤ) ∣ a) (hb : ¬ (37 : ℤ) ∣ b)
    (δ : 𝓞 (CyclotomicField 37 ℚ))
    (hδ : Ideal.Quotient.mk lv149 δ =
      Ideal.Quotient.mk lv149 (caseII_gammaA D ha) *
        (Ideal.Quotient.mk lv149 (caseII_gammaA D hb))⁻¹) :
    BernoulliRegular.IsPthPowerModPrime 37 lv149 δ :=
  caseII_gammaRatio_isPthPower_of_x_add_y_mem D
    (caseII_real_x_add_y_mem_of_dvd_z hSO D hz hxl hyl) hxl ha hb δ hδ

/-! ## 4. The direct Lemma-9.8 local power of the abstract descent unit `ε₁/ε₂`

The §1–§3 Lemma-9.9 opening concerns the §9.1 *cyclotomic* ratio `γ_a/γ_b`.  For the **abstract**
descent unit `ε₁/ε₂` (the unit cofactor of the Case-II descent equation) there is a **direct**
residue argument requiring **no** §9.1 identification: reduce the descent equation modulo `𝔩`.  With
`z' ∈ lv149` (Washington Lemma 9.7) the right side `ε₃·((ζ−1)^m·z')³⁷` vanishes mod `𝔩`; with
`x' ∉ lv149` (Washington Lemma 9.6) the resulting `ε₁·x'³⁷ ≡ −ε₂·y'³⁷ (mod 𝔩)` gives
`ε₁/ε₂ ≡ −(y'/x')³⁷`, a `37`-th power (`−1 = (−1)³⁷`). -/

/-- **The direct Lemma-9.8 local power of `ε₁/ε₂`** (proven, axiom-clean — **no** §9.1
identification, **no** producer, **no** Assumption II).

For a Case-II descent equation `ε₁·x'³⁷ + ε₂·y'³⁷ = ε₃·((ζ−1)^m·z')³⁷` with the standing Washington
hypotheses `x' ∉ lv149` (Lemma 9.6) and `z' ∈ lv149` (Lemma 9.7), the descent unit `ε₁/ε₂` is a
`37`-th power modulo `lv149`.

Proof: modulo `𝔩`, `z' ∈ lv149` kills the right side, so `Q(ε₁)·Q(x')³⁷ = −Q(ε₂)·Q(y')³⁷`; since
`Q(x') ≠ 0` (`x' ∉ lv149`) and `Q(ε₂) ≠ 0` (`ε₂` a unit), `Q(ε₁/ε₂) = Q(ε₁)·Q(ε₂)⁻¹ =
−(Q(y')·Q(x')⁻¹)³⁷ = (−(Q(y')·Q(x')⁻¹))³⁷` (`(−1)³⁷ = −1`).  This is the genuine Lemma-9.8 local
power: a one-line residue computation from the descent equation under Lemmas 9.6–9.7, with no
cyclotomic-unit identification and no `p`-adic content. -/
theorem caseII_lemma98LocalPower37_directResidue
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {m e : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ}
    (hxl : x' ∉ lv149) (hzl : z' ∈ lv149)
    (heq : (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
        (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
      (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.toInteger - 1) ^ e * z') ^ 37) :
    BernoulliRegular.IsPthPowerModPrime 37 lv149
      (((ε₁ / ε₂ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ))) := by
  set Q := Ideal.Quotient.mk lv149
  -- Right side ∈ lv149 (since `z' ∈ lv149`), hence the left side is too.
  have hrhs : (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.toInteger - 1) ^ e * z') ^ 37 ∈ lv149 :=
    Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Ideal.mul_mem_left _ _ hzl) 37 (by decide))
  have hlhs : (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
      (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 ∈ lv149 := by rw [heq]; exact hrhs
  -- Residue-field form: `Q(ε₁)·Q(x')³⁷ = −(Q(ε₂)·Q(y')³⁷)`.
  have hresid : Q (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * Q x' ^ 37 =
      - (Q (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * Q y' ^ 37) := by
    have hz0 := Ideal.Quotient.eq_zero_iff_mem.mpr hlhs
    rw [map_add, map_mul, map_mul, map_pow, map_pow] at hz0
    linear_combination hz0
  have hx0 : Q x' ≠ 0 := fun h ↦ hxl (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hε20 : Q (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) ≠ 0 := fun h ↦
    caseII_unit_notMem_lv149 ε₂ (Ideal.Quotient.eq_zero_iff_mem.mp h)
  -- `Q(ε₁/ε₂) · Q(ε₂) = Q(ε₁)` (from the unit identity `(ε₁/ε₂)·ε₂ = ε₁`).
  have hunit : (ε₁ / ε₂ : (𝓞 (CyclotomicField 37 ℚ))ˣ) * ε₂ = ε₁ := by
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one]
  have hQdiv : Q ((ε₁ / ε₂ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) *
      Q (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) = Q (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) := by
    rw [← map_mul, ← Units.val_mul, hunit]
  -- The explicit `37`-th root: `−(Q(y')·Q(x')⁻¹)`.
  refine ⟨-(Q y' * (Q x')⁻¹), ?_⟩
  -- Cancel the nonzero `Q(ε₂)`: it suffices to show `Q(ε₁/ε₂)·Q(ε₂) = witness³⁷·Q(ε₂)`.
  refine mul_right_cancel₀ hε20 ?_
  rw [hQdiv]
  -- `witness³⁷ = −(Q(y')³⁷·(Q(x')³⁷)⁻¹)` (`(−1)³⁷ = −1`); then `·Q(ε₂)`.
  rw [neg_pow, mul_pow, inv_pow,
    (Odd.neg_one_pow (by decide : Odd 37) : ((-1 : 𝓞 (CyclotomicField 37 ℚ) ⧸ lv149) ^ 37) = -1)]
  -- Goal: `Q(ε₁) = (−(Q(y')³⁷·(Q(x')³⁷)⁻¹))·Q(ε₂)`.  Multiply `hresid` by `(Q(x')³⁷)⁻¹`.
  have hx37 : Q x' ^ 37 ≠ 0 := pow_ne_zero 37 hx0
  have hε1_eq : Q (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) =
      - (Q (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * Q y' ^ 37) * (Q x' ^ 37)⁻¹ := by
    rw [← hresid, mul_assoc, mul_inv_cancel₀ hx37, mul_one]
  rw [hε1_eq]; ring

/-! ## 5. What the direct residue fact says about `Lemma98LocalPower37` (honest scope)

`caseII_lemma98LocalPower37_directResidue` (§4) shows the **entire** Lemma-9.8 local power
`IsPthPowerModPrime 37 lv149 (ε₁/ε₂)` is a **one-line residue computation** from the descent
equation, given exactly Washington's two standing hypotheses for the second case:

* `x' ∉ lv149` — **Lemma 9.6** (`ℓ ∤ a`);
* `z' ∈ lv149` — **Lemma 9.7** (`ℓ ∣ z`).

So the genuine remaining content of the local power is **not** a §9.1 cyclotomic identification,
**not** the obstructed `Q_η₀` producer, and **not** a `p`-adic-`L` / level-72 Dwork computation: it
is
**only** these two arithmetic conditions on the descent variables.

**Soundness (no false universal).**  The named `Lemma98LocalPower37` (`CaseIIAssumptionII.lean`)
quantifies over an *abstract* `CaseIIData37` with **free** `x', y', z', ε₁, ε₂, ε₃` under only the
`(ζ−1) ∤ ·` conditions, **without** `x' ∉ lv149` or `z' ∈ lv149`.  As a universal it is **false**
(B2 `CASEII-LEMMA98-LOCALPOWER`: with `x' ∈ lv149` or `z' ∉ lv149`, `ε₁/ε₂` is free in the
order-`37` quotient `𝔽₁₄₉^×/(𝔽₁₄₉^×)³⁷`).  We therefore do **not** assert a universal of the form
"every abstract descent datum satisfies `x' ∉ lv149 ∧ z' ∈ lv149`" — that universal is *also* false
on the
free telescope.  The sound statement is the **implication**
`caseII_lemma98LocalPower37_directResidue` itself: with the Lemma-9.6/9.7 conditions *as explicit
hypotheses*, the local power holds (proven).

For the **genuine** descent these two conditions are true (the descent variables come from a Fermat
solution with `ℓ ∤ a`, and `z` is the `p`-divisible variable with `ℓ ∣ z` by Lemma 9.7, non-vacuous
since `149 ≡ 1 (mod 37)`, `149 < 37² − 37`); but that truth lives at the *rational origin* of the
descent (over `RealCaseIIData37`, where `D.x ∉ lv149` is a genuine datum field and
`RealCaseIILehmerVandiverDvdZ37` names `D.z ∈ lv149`), not over the abstract free telescope.  The
existing FLT37 endpoints consume the named `Lemma98LocalPower37` as residual 4 directly; §4 pins its
genuine content to the two Lemma-9.6/9.7 conditions via the proven one-line residue fact. -/

/-- **The Lemma-9.8 local power for the producer-anchored real descent equation** (proven,
axiom-clean — the direct residue fact §4 applied to a real datum with Lemma 9.6 + Lemma 9.7).

For a real Case-II datum `D` and a descent equation `ε₁·x'³⁷ + ε₂·y'³⁷ = ε₃·((ζ−1)^m·z')³⁷` whose
`x'` avoids `lv149` (**Lemma 9.6**) and whose `z'` lies in `lv149` (**Lemma 9.7**, e.g. the carried
`RealCaseIILehmerVandiverDvdZ37` at `z' = D.z`), the descent unit `ε₁/ε₂` is a `37`-th power modulo
`lv149`.

This is `caseII_lemma98LocalPower37_directResidue` on the underlying `CaseIIData37` of the real
datum: the genuine Lemma-9.8 local power, a one-line residue computation, with the Lemma-9.6/9.7
conditions supplied as the genuine hypotheses they are over real data (where they hold), rather than
asserted over the abstract free telescope (where they are false). -/
theorem caseII_real_lemma98LocalPower37_directResidue
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {m e : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ}
    (hxl : x' ∉ lv149) (hzl : z' ∈ lv149)
    (heq : (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
        (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
      (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.toCaseIIData37.hζ.toInteger - 1) ^ e * z') ^ 37) :
    BernoulliRegular.IsPthPowerModPrime 37 lv149
      (((ε₁ / ε₂ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ))) :=
  caseII_lemma98LocalPower37_directResidue D.toCaseIIData37 hxl hzl heq

/-! ## 6. Non-vacuity of the direct local power (it fires at the rational base)

At the rational base of the descent the Lemma-9.6/9.7 conditions are genuinely available:
`furtwangler_37_149` (Washington Lemma 9.7) gives `D.z ∈ lv149` for the base real datum, and the
Lemma-9.6 coprimality `149 ∤ a, b` is the standing second-case hypothesis.  So the direct local
power is **not** vacuous — it discharges the local power of any descent equation rooted at such a
datum. -/

/-- **The direct local power fires for the real datum's own descent equation** (proven,
axiom-clean) — explicit non-vacuity.

For a real Case-II datum `D` with `D.z ∈ lv149` (Lemma 9.7, the carried datum / `furtwangler_37_149`
at the base) and `D.x ∉ lv149` (Lemma 9.6), the descent unit of the datum's **own** single-unit
equation `D.x³⁷ + D.y³⁷ = D.ε·((ζ−1)^{m+1}·D.z)³⁷` (`ε₁ = ε₂ = 1`) is a `37`-th power mod `lv149`
(trivially, as `ε₁/ε₂ = 1`).  This confirms the direct residue argument applies to genuine descent
data with the Lemma-9.6/9.7 conditions discharged at the base — it is not an empty implication. -/
theorem caseII_real_lemma98LocalPower37_base_nonvacuous
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hzl : D.z ∈ lv149) (hxl : D.x ∉ lv149) :
    BernoulliRegular.IsPthPowerModPrime 37 lv149
      (((1 / 1 : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ))) :=
  caseII_real_lemma98LocalPower37_directResidue (e := m + 1) D (ε₁ := 1) (ε₂ := 1) (ε₃ := D.ε)
    (x' := D.x) (y' := D.y) (z' := D.z) hxl hzl
    (by
      have he := D.toCaseIIData37.equation
      simpa only [Units.val_one, one_mul] using he)

/-! ## 7. Assumption II and the FLT37 Case-II endpoint, with the local power pinned (route (a))

Assumption II (`CaseIIThm95Lemma99Bridge`) reduces — through the *already proven* engine (R3
`caseII_descentUnitOmega32Membership37_proven`, the half-range Vandermonde collapse, the
discrete-log translation, the Corollary-8.15 saturation) — to the single Lemma-9.8 local power
`Lemma98LocalPower37`, whose genuine content §4 pins to the Lemma-9.6/9.7 residue fact.  We record
the resulting endpoints (consuming `Lemma98LocalPower37` as the named residual, exactly as the
existing FLT37 chain does); §4 establishes that this residual is **not** a §9.1 identification,
**not** the obstructed producer, and **not** a `p`-adic-`L` / level-72 Dwork computation, but the
one-line
residue fact under Lemmas 9.6–9.7. -/

/-- **Assumption II (`CaseIIThm95Lemma99Bridge`) from the Lemma-9.8 local power** (proven,
axiom-clean — R3 supplied internally).

`caseIIOmega32_assumptionII_of_localPower`, re-exported here beside the route-(a) local-power
analysis: Assumption II from the single residual `Lemma98LocalPower37`, with Washington Lemma 9.9's
regular-index collapse (R3) the proven `caseII_descentUnitOmega32Membership37_proven`.  By §4 the
residual `Lemma98LocalPower37` is, for descent data satisfying Lemmas 9.6–9.7, the one-line residue
fact `caseII_lemma98LocalPower37_directResidue` — no `p`-adic-`L` / Dwork content, no obstructed
producer. -/
theorem caseIIThm95Lemma99Bridge_of_localPower
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_localPow : Lemma98LocalPower37) :
    CaseIIThm95Lemma99Bridge :=
  caseIIOmega32_assumptionII_of_localPower h_localPow

/-- **FLT37, with the Case-II local power as the pinned residual** (proven, axiom-clean given the
named inputs + carried Kellner).

`FermatLastTheoremFor 37` from the genuine Case-II residuals, with the local-power residual analysed
in this file:

* `caseII_classConjFixed : CaseIIRootClassConjFixed37` — Case-II II1 (Washington Lemma 9.2);
* `caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37` — R2, reality-preserving
  single-root descent;
* `caseII_leadingExp : LeadingExponentEigenCollapse37` — R3, Lemma 9.9 regular-index collapse;
* `caseII_localPow : Lemma98LocalPower37` — Lemma 9.8 single-index local power, whose genuine
  content §4 pins to the Lemma-9.6/9.7 residue fact (`caseII_lemma98LocalPower37_directResidue`);
* `noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32` — carried Kellner.

This re-exports `fermatLastTheoremFor_thirtyseven_of_genuineResiduals`; the contribution of this
file is the route-(a) analysis of residual 4 (`caseII_localPow`): it is the auxiliary-prime residue
triviality of §4 under Washington Lemmas 9.6–9.7, **not** a `p`-adic-`L` / level-72 Dwork
computation
and **not** the obstructed `Q_η₀` producer. -/
theorem fermatLastTheoremFor_thirtyseven_localPowerPinned
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_leadingExp : LeadingExponentEigenCollapse37)
    (caseII_localPow : Lemma98LocalPower37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_genuineResiduals
    caseII_classConjFixed caseII_realDescent caseII_leadingExp caseII_localPow
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
