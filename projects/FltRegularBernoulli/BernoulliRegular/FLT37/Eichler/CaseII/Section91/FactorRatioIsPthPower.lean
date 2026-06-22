import BernoulliRegular.FLT37.Eichler.CaseII.Kummer.RootClassConjFixedUnconditional
import BernoulliRegular.FLT37.Eichler.CaseII.Section91.SquaredFormToFactorEquation

/-!
# [FLT37-CASEII-R2] Washington §9.1 squared form: the *quotient* half (Lemma 9.2, unconditional)

This file builds the **quotient half** of Washington's squared form (GTM 83, 2nd ed., p. 170): the
ratio of the adjacent factor `X = (x+yη)/(1-η)` to its conjugate `X̄ = (x+yη³⁶)/(1-η³⁶)` is a clean
`37`-th power,

  `X / X̄ = β³⁷`,    `β ∈ K`,

**unconditionally** (no residual): it is Washington Lemma 9.2 (`ᾱ = α⁻¹`, primary, unramified ⟹ `α`
a `p`-th power), which the project has **proven** end-to-end via the ideal-form Lemma 9.1
(`caseIIRootClassConjFixed37_proven` / `caseIIIdealKummerUnramified37_proven`) and Hilbert 94
(`flt37_antiFixed_radical_isPthPower`, `Sinnott.flt37_not_dvd_hPlus`).

The clean (unit-free) `37`-th power is exactly Washington's `α = α₁^p`, **because** the project's
proven corrected-radical-is-a-`p`-th-power uses the *specific* Washington correction unit
`u₀ = -η = -ζ^a` (`caseII_correctionUnit`), and the `−ζ^a` twist of the numerator ratio
`(x+yη)/(x+yη³⁶) = (-η)·β³⁷` is cancelled by the `(1-η³⁶)/(1-η) = -η⁻¹` ratio:
```
X/X̄ = (x+yη)/(x+yη³⁶) · (1-η³⁶)/(1-η) = (-η)·β³⁷ · (-η⁻¹) = β³⁷.
```

This is the genuinely-unconditional analytic core (Lemma 9.2) of the §9.1 squared form.  Combined
with the *product* half `X·X̄ = η'·γ³⁷` (the B₀-style real-generator argument, remaining content),
the squared form `X² = η'·(βγ)³⁷` with **real** unit `η'` follows, feeding
`washington_factor_of_squared_pair` (`CaseIISection91FactorExtraction.lean`) to produce the factor
equations.

## What this file proves (real, axiom-clean Lean — no `sorry`, no `axiom`)

* `caseII_correctedRadical_neg_eta_isPthPower` — the proven Lemma 9.2 in clean form: the corrected
  radical `α = (-η)⁻¹·(x+yη)/(x+yη³⁶)` is a `37`-th power `β³⁷` (unconditionally, via the proven
  ideal-form Lemma 9.1 + Hilbert 94), handling both the generic (`α² ≠ 1`) and degenerate (`α² = 1`)
  cases.

* `caseII_section91_rootRatioK_eq_neg_eta_mul_pthPower` — the numerator-ratio form
  `(x+yη)/(x+yη³⁶) = (-η)·β³⁷`.

* `caseII_section91_factorRatio_isPthPower` — **the quotient half** `X/X̄ = β³⁷` (clean, unit-free).

These are over `K = CyclotomicField 37 ℚ` (where Lemma 9.2 is proven) and an adjacent root `η ≠ η₀`.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1, pp. 169–171 (Lemma 9.2,
  the squared form).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension NumberField.IsCMField Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-! ## 1. The proven Lemma 9.2 in clean form: the corrected radical is a `37`-th power -/

/-- **[LEMMA 9.2, CLEAN] The corrected radical is a `37`-th power** (proven, axiom-clean).

For a real Case-II datum `D` and adjacent root `η ≠ η₀`, the corrected radical
`α = caseII_correctedRadical D η (-η) = (-η)⁻¹·(x+yη)/(x+yη³⁶)` is a `37`-th power `β³⁷` for some
`β ∈ K`.

Proof: the corrected radical is anti-fixed (`caseII_correctedRadical_complexConj` with the proven
`caseII_correctionUnit_anti`).  If `α² = 1` then `α = ±1` and `α = α³⁷` (37 odd), so `β = α`.
Otherwise `flt37_antiFixed_radical_isPthPower` (Hilbert 94, `¬ 37 ∣ h⁺` = `Sinnott`)
applies, with the unramifiedness supplied by the **proven** `caseIIIdealKummerUnramified37_proven`
through `caseII_correctedRadicalUnramified37_of_idealKummer` (whose `u₀` is exactly
`caseII_correctionUnit η = -η`). -/
theorem caseII_correctedRadical_neg_eta_isPthPower
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
    (hη : η ≠ D.etaZero) :
    ∃ β : CyclotomicField 37 ℚ,
      β ^ 37 = caseII_correctedRadical D η (caseII_correctionUnit η) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set α := caseII_correctedRadical D η (caseII_correctionUnit η) with hα_def
  have hα_ne : α ≠ 0 :=
    caseII_correctedRadical_ne_zero D (by decide : (37 : ℕ) ≠ 2) η (caseII_correctionUnit η)
  -- Anti-fixedness of the corrected radical (from the proven `caseII_correctionUnit_anti`).
  have hα_anti : NumberField.IsCMField.complexConj (CyclotomicField 37 ℚ) α = α⁻¹ :=
    caseII_correctedRadical_complexConj D (by decide : (37 : ℕ) ≠ 2) η (caseII_correctionUnit η)
      (caseII_correctionUnit_anti η)
  by_cases hsq : α ^ 2 = 1
  · -- `α = ±1`; `α = α³⁷` (37 odd).
    have hpm : α = 1 ∨ α = -1 := by
      have hfac : (α - 1) * (α + 1) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp hfac with h1 | h1
      · exact Or.inl (by linear_combination h1)
      · exact Or.inr (by linear_combination h1)
    refine ⟨α, ?_⟩
    rcases hpm with h1 | h1
    · rw [h1, one_pow]
    · rw [h1]; norm_num
  · -- `α² ≠ 1`: the proven ideal-form Lemma 9.1 unramifiedness (at the explicit correction unit
    -- `-η`, via the two unconditional witnesses) + Hilbert 94.
    -- Primarity witness (unconditional, at `caseII_correctionUnit η`).
    have h_prim := caseII_correctedRadical_primary_witness D (by decide : (37 : ℕ) ≠ 2) η hη
    obtain ⟨N, c, hc_not, hc_eq⟩ := h_prim
    -- Ideal `37`-th-power structure (unconditional, at `caseII_correctionUnit η`).
    have h_ideal_struct := caseII_correctedRadical_fractionalIdeal_eq D
      (by decide : (37 : ℕ) ≠ 2) η
    -- The proven ideal-form Lemma 9.1, applied to our `α`.
    have h_unram : Algebra.Unramified (𝓞 (CyclotomicField 37 ℚ))
        (𝓞 (FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift (p := 37)
          (CyclotomicField 37 ℚ) α hα_ne)) :=
      caseIIIdealKummerUnramified37_proven α hα_ne
        ⟨D.ζ, D.hζ, N, c, hc_not, hc_eq⟩
        ⟨_, h_ideal_struct⟩
    exact flt37_antiFixed_radical_isPthPower (K := CyclotomicField 37 ℚ)
      Sinnott.flt37_not_dvd_hPlus hα_ne hα_anti hsq h_unram

/-! ## 2. The numerator-ratio form and the clean quotient `X/X̄ = β³⁷` -/

/-- **The numerator-ratio form** `(x+yη)/(x+yη³⁶) = (-η)·β³⁷` (Lemma 9.2, undoing the correction).

From `caseII_correctedRadical_neg_eta_isPthPower` (`α = (-η)⁻¹·α₀ = β³⁷`), multiply by `-η`:
`α₀ = caseII_rootRatioK D η = (x+yη)/(x+yη³⁶) = (-η)·β³⁷` in `K`. -/
theorem caseII_section91_rootRatioK_eq_neg_eta_mul_pthPower
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
    (hη : η ≠ D.etaZero) :
    ∃ β : CyclotomicField 37 ℚ,
      caseII_rootRatioK D η =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (-(η : 𝓞 _)) * β ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  obtain ⟨β, hβ⟩ := caseII_correctedRadical_neg_eta_isPthPower D η hη
  refine ⟨β, ?_⟩
  -- `α = (algebraMap (-η))⁻¹ · α₀ = β³⁷`, so `α₀ = algebraMap(-η) · β³⁷`.
  -- `algebraMap(-η) ≠ 0` since `-η = caseII_correctionUnit η` is a unit.
  have hu_ne : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
      (-(η : 𝓞 (CyclotomicField 37 ℚ))) ≠ 0 := by
    rw [show (-(η : 𝓞 (CyclotomicField 37 ℚ))) = (caseII_correctionUnit η : 𝓞 _) from
      (caseII_correctionUnit_val η).symm, Ne,
      map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
    exact (caseII_correctionUnit η).ne_zero
  -- `α = (algebraMap(-η))⁻¹ · α₀` (definitional, using `caseII_correctionUnit η = -η`).
  have hαdef : caseII_correctedRadical D η (caseII_correctionUnit η) =
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
        (-(η : 𝓞 _)))⁻¹ * caseII_rootRatioK D η := by
    rw [caseII_correctedRadical, caseII_correctionUnit_val]
  rw [hαdef] at hβ
  -- `(algebraMap(-η))⁻¹·α₀ = β³⁷` ⟹ `α₀ = algebraMap(-η)·β³⁷`.
  field_simp at hβ
  linear_combination -hβ

/-- **[QUOTIENT HALF] The factor ratio is a clean `37`-th power** `X/X̄ = β³⁷` (Washington p. 170).

For the adjacent factor `X = (x+yη)/(1-η)` and its conjugate `X̄ = (x+yη³⁶)/(1-η³⁶)`, the ratio is a
unit-free `37`-th power:
```
X / X̄ = β³⁷,   β ∈ K.
```
Proof: `X/X̄ = α₀ · (1-η³⁶)/(1-η)` and `(1-η³⁶)/(1-η) = -η⁻¹` (from `η³⁶ = η⁻¹`); with
`α₀ = (-η)·β³⁷` (`caseII_section91_rootRatioK_eq_neg_eta_mul_pthPower`), the `(-η)·(-η⁻¹)=1` cancels
and `X/X̄ = β³⁷`.  This is the unconditional Lemma 9.2 quotient half of the squared form. -/
theorem caseII_section91_factorRatio_isPthPower
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
    (hη : η ≠ D.etaZero) :
    ∃ β : CyclotomicField 37 ℚ,
      (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y * (η : 𝓞 _)) /
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            (1 - (η : 𝓞 _))) /
        (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            (D.x + D.y * ((η : 𝓞 _) ^ 36)) /
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            (1 - (η : 𝓞 _) ^ 36)) = β ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set K := CyclotomicField 37 ℚ with hK
  obtain ⟨β₀, hβ⟩ := caseII_section91_rootRatioK_eq_neg_eta_mul_pthPower D η hη
  refine ⟨β₀, ?_⟩
  have h37 : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
  -- nonzero numerators of `α₀`.
  have hnum_ne := caseII_algebraMap_x_add_y_eta_ne_zero D (by decide : (37 : ℕ) ≠ 2) η
  have hden_ne := caseII_algebraMap_x_add_y_etaInv_ne_zero D (by decide : (37 : ℕ) ≠ 2) η
  -- `η = 1` is excluded (`η ≠ η₀ = 1`).
  have hη1 : (η : 𝓞 K) ≠ 1 := by
    intro h1
    refine absurd hη (not_not.mpr (Subtype.ext ?_))
    rw [caseII_etaZero_eq_one D (by decide : (37 : ℕ) ≠ 2)]; exact h1
  -- `algebraMap(1-η) ≠ 0`.
  have h1η_ne : algebraMap (𝓞 K) K (1 - (η : 𝓞 K)) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
    intro h0; exact hη1 (by linear_combination -h0)
  -- `algebraMap(1-η³⁶) ≠ 0`.
  have h1η36_ne : algebraMap (𝓞 K) K (1 - (η : 𝓞 K) ^ 36) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
    intro h0
    have hη36 : (η : 𝓞 K) ^ 36 = 1 := by linear_combination -h0
    -- `η³⁷ = η³⁶·η`, so `1 = 1·η = η`, giving `η = 1`.
    apply hη1
    have hps : (η : 𝓞 K) ^ 37 = (η : 𝓞 K) ^ 36 * (η : 𝓞 K) := pow_succ _ _
    rw [h37, hη36, one_mul] at hps
    exact hps.symm
  -- `η·η³⁶ = 1` (the key root-of-unity relation).
  have hηη : (η : 𝓞 K) * (η : 𝓞 K) ^ 36 = 1 := by rw [mul_comm, ← pow_succ]; exact h37
  -- `(1-η³⁶) = -η³⁶·(1-η)` (at the `𝓞 K` level, mapped to `K`).
  have h_denom_id : algebraMap (𝓞 K) K (1 - (η : 𝓞 K) ^ 36) =
      algebraMap (𝓞 K) K (-((η : 𝓞 K) ^ 36)) * algebraMap (𝓞 K) K (1 - (η : 𝓞 K)) := by
    rw [← map_mul]
    exact congrArg (algebraMap (𝓞 K) K) (by linear_combination -hηη)
  -- `algebraMap(-η)·algebraMap(-η³⁶) = 1`.
  have h_unit_prod : algebraMap (𝓞 K) K (-(η : 𝓞 K)) *
      algebraMap (𝓞 K) K (-((η : 𝓞 K) ^ 36)) = 1 := by
    rw [← map_mul]
    exact (congrArg (algebraMap (𝓞 K) K) (by rw [neg_mul_neg]; linear_combination hηη)).trans
      (map_one _)
  -- `caseII_rootRatioK D η = N/D` (definitional unfold).
  have hα₀ : caseII_rootRatioK D η =
      algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K)) /
        algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K) ^ 36) := rfl
  rw [hα₀] at hβ
  -- nonzero facts.
  have hnumK_ne : algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K)) ≠ 0 := hnum_ne
  have hdenK_ne : algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K) ^ 36) ≠ 0 := hden_ne
  -- Clear all denominators; the goal is then a polynomial identity using `hβ`, `h_unit_prod`.
  rw [h_denom_id, div_div_div_eq]
  rw [div_eq_iff (mul_ne_zero h1η_ne hdenK_ne)]
  -- `hβ` cleared: `nη = uη·β³⁷·dη`.
  rw [div_eq_iff hdenK_ne] at hβ
  -- close by ring-with-hypotheses: coeff `(vη·e1)` for `hβ`, `(β³⁷·dη·e1)` for `h_unit_prod`.
  linear_combination
    (algebraMap (𝓞 K) K (-((η : 𝓞 K) ^ 36)) * algebraMap (𝓞 K) K (1 - (η : 𝓞 K))) * hβ +
    (β₀ ^ 37 * algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K) ^ 36) *
      algebraMap (𝓞 K) K (1 - (η : 𝓞 K))) * h_unit_prod

end BernoulliRegular.FLT37.Eichler

end

end
