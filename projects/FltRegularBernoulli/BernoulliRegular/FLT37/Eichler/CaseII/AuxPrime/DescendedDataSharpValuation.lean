import BernoulliRegular.FLT37.Eichler.CaseII.FreeContent.DescentEquationPackaging
import BernoulliRegular.FLT37.Eichler.CaseII.FreeContent.DescendedContentIsPContent
import BernoulliRegular.FLT37.Eichler.CaseII.Kummer.CorrectedUnitPrimarity

/-!
# [FLT37-CASEII-R2-L5b] The sharp `𝔭`-invariants `hxy'`/`hdenom'` are DERIVABLE from L1/L2

This file **overturns** the project's prior assessment
(`CaseIIFreeContentAssembly.lean:444`, `CaseIIFreeContentDatumPackaging.lean §4`) that the sharp
`𝔭`-valuation invariants
```
hxy'   : (ζ−1)³ ∣ ω + θ,
hdenom' : ∃ c, ω + θ·ζ³⁶ = (ζ−1)·c ∧ ¬(ζ−1) ∣ c   (i.e. v_𝔭(ω+θζ³⁶) = 1 exactly)
```
are "**not** derivable from the descended equation".  That assessment was made *before* the L1
anchor (`caseII_anchor_real_rho0_genuineUnit`) and L2 factor equations
(`caseII_section91_factorEquations_etaOne_etaTwo`) were proven, and — crucially — before the
**`p`-content of the descended content** was banked.

## The key arithmetic that unlocks the derivation

The L1 anchor equation `algebraMap(x+y) = algebraMap(u₀)·Λ^e·ρ₀³⁷` with `z' = ρ₀²` `𝔭`-coprime
**forces** `2·e = 37·m + 1` (the proven `caseII_anchor_exponent_eq`).  Hence the descended
`(ζ−1)`-content
```
n' = 2·(2e − 1) = 2·(37m + 1 − 1) = 74m = 37·(2m)
```
is a **multiple of `37`** (`caseII_descended_content_eq`).  Therefore the integer descended Fermat
equation
```
ω³⁷ + θ³⁷ = (δ' : 𝓞 K) · Λ^{2e−1} · (z')³⁷,     Λ = (1−ζ)(1−ζ³⁶),
```
after the standalone repackaging
`Λ^{2e−1} = (−ζ³⁶)^{2e−1}·(ζ−1)^{2(2e−1)} = (−ζ³⁶)^{2e−1}·((ζ−1)^{2m})³⁷`
(`freeContentPackaging_Lambda_eq`), takes the **inside-frame** shape
```
ω³⁷ + θ³⁷ = ε' · ((ζ−1)^{2m} · z')³⁷,     ε' = δ'·(−ζ³⁶)^{2e−1},
```
i.e. it is a genuine `RealCaseIIData37 (2m−1)` (with `m'+1 = 2m`, `m' = 2m−1 ≥ 1`).  This is exactly
the frame on which the **proven** sharp root-ideal lemmas run:

* `caseII_K_zeta_sub_one_pow_dvd_x_add_y` (`(ζ−1)^{37·m'+1} ∣ ω+θ`, and `37m'+1 ≥ 38 ≥ 3`) ⟹ `hxy'`;
* `caseII_etaInv_denom_factor` at the adjacent root `ζ` (`ω + θ·ζ³⁶ = (ζ−1)·c`, `¬(ζ−1)∣c`,
  the sharp `v_𝔭 = 1`, built from `caseII_zeta_sub_one_sq_not_dvd_x_add_y_root`) ⟹ `hdenom'`.

So `hxy'` and `hdenom'` are **not** independent carried content: they are the inside-frame sharp
valuation lemmas applied to the descended Fermat data, whose content is `p`-content **because of the
proven anchor exponent identity `2e = 37m+1`**.  The mechanism is identical to the proven embedding
`FreeContentCaseIIData37.ofRealCaseIIData37`, applied to the *descended* datum.

We build the descended datum over the **canonical** `zeta_spec` primitive root, so the sharp lemmas
produce exactly the `zeta_spec`-form of `hxy'`/`hdenom'` that the witness bundle records.

## What this file proves

* `caseII_descended_realData` — packages the descended `(ω, θ, z'=ρ₀²)` into a
  `RealCaseIIData37 (2m−1)` (over `zeta_spec`) from the integer descended equation (Λ-form) +
  `2e = 37m+1` + reality + `𝔭`-coprimality.  The content match `2·(2e−1) = 37·(2m)` (so `m'+1 = 2m`)
  is the proven `caseII_descended_content_eq` arithmetic.
* `caseII_descended_hxy_hdenom` — `hxy'` (`(ζ−1)³ ∣ ω+θ`) **and** `hdenom'` (sharp
  `v_𝔭(ω+θζ³⁶) = 1`) from that datum, exactly as `ofRealCaseIIData37` proves its `hxy`/`hdenom`.

These feed the R2 closure (`CaseIIWashingtonDescentClose.lean`): the sharp `𝔭`-geometry is
**proven**, not carried, leaving only the integer-witness existence (`ω, θ`), the σ-fixed unit `δ'`,
and the
aux-prime Lemma-9.6/9.7 `ℓ`-propagation as carried §9.1 content.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (Theorem 9.4), pp. 169–173
  (the descended Fermat equation at the doubled, `p`-divisible content; the sharp `v_𝔭`
  bookkeeping).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. The descended Fermat datum `RealCaseIIData37 (2m−1)` from the descended equation -/

/-- **[DESCENDED DATUM] The descended `(ω, θ, z')` is a `RealCaseIIData37 (2m−1)`** (over the
canonical `zeta_spec` root).

From the **integer** descended Fermat equation in `Λ`-form
```
ω³⁷ + θ³⁷ = (δ' : 𝓞 K) · ((1−ζ)(1−ζ³⁶))^{2e−1} · z'³⁷,     ζ = zeta_spec,
```
the proven anchor-exponent relation `2·e = 37·m + 1` (so `m ≥ 1`, hence `2m−1+1 = 2m`), the reality
`σω = ω`, `σθ = θ`, and the `𝔭`-coprimalities `(ζ−1) ∤ θ`, `(ζ−1) ∤ z'`, package as a
`RealCaseIIData37 (2m−1)` whose Fermat variables are `ω, θ` and whose descended variable is `z'`.

The content match is the proven `caseII_descended_content_eq` arithmetic: `2·(2e−1) = 37·(2m)`, so
the inside-frame exponent is `m'+1 = 2m`, `m' = 2m−1`.  The `Λ^{2e−1} → ε'·(ζ−1)^{37·2m}` conversion
is `freeContentPackaging_Lambda_eq` (`Λ = −ζ³⁶·(ζ−1)²`).  Mirrors the proven embedding
`FreeContentCaseIIData37.ofRealCaseIIData37` on the descended data. -/
def caseII_descended_realData
    {m : ℕ} (hm : 1 ≤ m)
    {ω θ z' : 𝓞 (CyclotomicField 37 ℚ)} {δ' : (𝓞 (CyclotomicField 37 ℚ))ˣ} {e : ℕ}
    (h2e : 2 * e = 37 * m + 1)
    (hequation : ω ^ 37 + θ ^ 37 =
      (δ' : 𝓞 (CyclotomicField 37 ℚ)) *
        ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
          (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36)) ^ (2 * e - 1) *
        z' ^ 37)
    (hω_real : NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ω = ω)
    (hθ_real : NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ) θ = θ)
    (hθ_cop : ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ θ)
    (hz'_cop : ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ z') :
    RealCaseIIData37 (CyclotomicField 37 ℚ) (2 * m - 1) := by
  set ζspec := zeta_spec 37 ℚ (CyclotomicField 37 ℚ)
  -- The unit factor `−ζ³⁶` of the `Λ → (ζ−1)²` conversion.
  set η36u : (𝓞 (CyclotomicField 37 ℚ))ˣ :=
    (freeContentPackaging_neg_zeta_pow_36_isUnit ζspec).unit with hη36u_def
  have hη36u_val : (η36u : 𝓞 (CyclotomicField 37 ℚ)) = -(ζspec.toInteger ^ 36) := by
    rw [hη36u_def, IsUnit.unit_spec]
  -- `ε' = δ' · (−ζ³⁶)^{2e−1}`.
  set ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ := δ' * η36u ^ (2 * e - 1) with hε'_def
  -- The inside-frame equation `ω³⁷+θ³⁷ = ε'·((ζ−1)^{2m}·z')³⁷`.
  have hinside : ω ^ 37 + θ ^ 37 =
      (ε' : 𝓞 (CyclotomicField 37 ℚ)) *
        ((ζspec.toInteger - 1) ^ ((2 * m - 1) + 1) * z') ^ 37 := by
    -- `Λ = −ζ³⁶·(ζ−1)²` gives `Λ^{2e−1} = (−ζ³⁶)^{2e−1}·(ζ−1)^{2(2e−1)}`; and
    -- `2·(2e−1) = 37·((2m−1)+1)`, so `(ζ−1)^{2(2e−1)}·z'³⁷ = ((ζ−1)^{2m}·z')³⁷`.
    rw [hequation, freeContentPackaging_Lambda_eq ζspec, mul_pow, ← pow_mul, hε'_def,
      Units.val_mul, Units.val_pow_eq_pow_val, hη36u_val, mul_pow, ← pow_mul]
    have hexp : 2 * (2 * e - 1) = 37 * ((2 * m - 1) + 1) := by omega
    rw [hexp]
    ring
  exact
    { ζ := _, hζ := ζspec,
      x := ω, y := θ, z := z', ε := ε',
      equation := hinside, x_real := hω_real, y_real := hθ_real, hy := hθ_cop, hz := hz'_cop }

@[simp] theorem caseII_descended_realData_hζ
    {m : ℕ} (hm : 1 ≤ m)
    {ω θ z' : 𝓞 (CyclotomicField 37 ℚ)} {δ' : (𝓞 (CyclotomicField 37 ℚ))ˣ} {e : ℕ}
    (h2e : 2 * e = 37 * m + 1)
    (hequation : ω ^ 37 + θ ^ 37 =
      (δ' : 𝓞 (CyclotomicField 37 ℚ)) *
        ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
          (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36)) ^ (2 * e - 1) *
        z' ^ 37)
    (hω_real : NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ω = ω)
    (hθ_real : NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ) θ = θ)
    (hθ_cop : ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ θ)
    (hz'_cop : ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ z') :
    (caseII_descended_realData hm h2e hequation hω_real hθ_real hθ_cop hz'_cop).hζ =
      zeta_spec 37 ℚ (CyclotomicField 37 ℚ) := rfl

/-! ## 2. The sharp invariants `hxy'`/`hdenom'`, derived from the descended datum -/

/-- **[hxy' + hdenom' DERIVED] The two sharp `𝔭`-valuation invariants of the witness bundle.**

From the integer descended Fermat equation (Λ-form) + the proven anchor-exponent relation
`2e = 37m+1` + reality + `𝔭`-coprimality of `θ, z'`, the witness bundle's two sharp invariants
```
hxy'   : (ζ−1)³ ∣ ω + θ,
hdenom' : ∃ c, ω + θ·ζ³⁶ = (ζ−1)·c ∧ ¬(ζ−1) ∣ c        (the sharp v_𝔭(ω+θζ³⁶) = 1)
```
(in `zeta_spec`-terms `ζ = (zeta_spec 37 ℚ K).toInteger`) **both hold**.

Proof: package `(ω, θ, z')` as the descended `RealCaseIIData37 (2m−1)` over `zeta_spec`
(`caseII_descended_realData`), then apply the inside-frame sharp lemmas exactly as the proven
embedding `FreeContentCaseIIData37.ofRealCaseIIData37` does:

* `hxy'` from `caseII_K_zeta_sub_one_pow_dvd_x_add_y` (`(ζ−1)^{37·(2m−1)+1} ∣ ω+θ`,
  `37·(2m−1)+1 ≥ 38 ≥ 3`);
* `hdenom'` from `caseII_etaInv_denom_factor` at the adjacent root `etaOne = ζ`
  (whence `ζ³⁶`), the sharp `v_𝔭 = 1`.

This is the L5b deliverable: the sharp `𝔭`-geometry of the descended building blocks is **proven**,
overturning the prior "not derivable from the equation" assessment — derivable **because** the
descended content `2(2e−1) = 37·(2m)` is `p`-content (the proven anchor-exponent identity). -/
theorem caseII_descended_hxy_hdenom
    {m : ℕ} (hm : 1 ≤ m)
    {ω θ z' : 𝓞 (CyclotomicField 37 ℚ)} {δ' : (𝓞 (CyclotomicField 37 ℚ))ˣ} {e : ℕ}
    (h2e : 2 * e = 37 * m + 1)
    (hequation : ω ^ 37 + θ ^ 37 =
      (δ' : 𝓞 (CyclotomicField 37 ℚ)) *
        ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
          (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36)) ^ (2 * e - 1) *
        z' ^ 37)
    (hω_real : NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ω = ω)
    (hθ_real : NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ) θ = θ)
    (hθ_cop : ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ θ)
    (hz'_cop : ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ z') :
    ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ^ 3 ∣ ω + θ ∧
    (∃ c : 𝓞 (CyclotomicField 37 ℚ),
      ω + θ * (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36 =
          ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) * c ∧
        ¬ ((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1) ∣ c) := by
  have hp : (37 : ℕ) ≠ 2 := by decide
  -- Package the descended data as `RealCaseIIData37 (2m−1)` over `zeta_spec`.
  set D' := caseII_descended_realData hm h2e hequation hω_real hθ_real hθ_cop hz'_cop
  -- `D'.hζ = zeta_spec`, `D'.x = ω`, `D'.y = θ`.
  have hD'ζ : D'.hζ = zeta_spec 37 ℚ (CyclotomicField 37 ℚ) := rfl
  have hD'x : D'.x = ω := rfl
  have hD'y : D'.y = θ := rfl
  refine ⟨?_, ?_⟩
  · -- `hxy'`: `(ζ−1)³ ∣ ω+θ` from `(ζ−1)^{37·(2m−1)+1} ∣ ω+θ` (`37·(2m−1)+1 ≥ 3`).
    have hdvd := caseII_K_zeta_sub_one_pow_dvd_x_add_y D' hp
    rw [hD'ζ, hD'x, hD'y] at hdvd
    exact (pow_dvd_pow _ (by omega : 3 ≤ 37 * (2 * m - 1) + 1)).trans hdvd
  · -- `hdenom'`: sharp denominator at `etaOne = ζ`.
    obtain ⟨c, hc, hc_not⟩ :=
      caseII_etaInv_denom_factor D' hp D'.etaOne D'.toCaseIIData37.etaOne_ne_etaZero
    rw [caseII_etaOne_coe_eq_zeta D' hp, hD'ζ, hD'x, hD'y] at hc
    rw [hD'ζ] at hc_not
    exact ⟨c, hc, hc_not⟩

end BernoulliRegular.FLT37.Eichler

end
