import BernoulliRegular.FLT37.Eichler.CaseII.Section91.ConjNormReassembly

/-!
# [FLT37-CASEII-R2] The integer-level descended equation (Section §9.1 output, lifted to `𝓞 K`)

This file lifts the **field-level** descended Fermat equation produced by
`washington_section91_descended_equation` (`CaseIISection91ConjNormReassembly.lean`) to an
**integer-level** equation in `𝓞 K`, in exactly the hypothesis-shape consumed by the packaging
lemma `freeContentCaseIIData37_of_descended_equation`
(`CaseIIFreeContentDatumPackaging.lean`).  It is the field→integer bridge that, composed with the
packaging lemma, gives

  *factor equations + anchor + Assumption II + integer-witness data ⟹ `∃ FreeContentCaseIIData37`* .

## Why two files (the pre-existing `washington_theta_real` name clash)

A single Lean file cannot import **both** `CaseIISection91ConjNormReassembly` (the proven
reassembly, needed for `washington_section91_descended_equation`) **and** `CaseIIFreeContentDatum`
(the target datum type, needed for `FreeContentCaseIIData37`): their import closures each define a
theorem named `BernoulliRegular.FLT37.Eichler.washington_theta_real` — Section §9.1's
`σ(-ρ_bσρ_b) = …` (`CaseIISection91ConjNormReassembly`, line 86) and the conjugate-paired-generators
reality lemma (`CaseIIConjugatePairedGenerators`, line 98, transitively pulled by
`CaseIIFreeContentDatum → CaseIIConjNormFactorDrop → CaseIIAnchorSquareDatum`).  Lean rejects two
imported modules defining the same fully-qualified name.  **Both** declarations pre-exist this work
(both files are unmodified); resolving the clash needs renaming one of them, i.e. editing an
existing file, which is out of scope here.

So the bridge is split: this file (Section §9.1 closure only) produces the **integer descended
equation** from the field one, and `freeContentCaseIIData37_of_descended_equation` (datum closure
only) packages that exact equation into the datum.  Composing them is a one-line application once
the name clash is resolved.

## What this file proves

`washington_section91_integer_descended_equation` — from the Section §9.1
factor/anchor/Assumption-II hypotheses **and** integer witnesses `ω, θ, z' : 𝓞 K` for the field
building blocks `u²ρ_aσρ_a`, `-ρ_bσρ_b`, `ρ_0²` and an integer unit witness `δ'` for the σ-fixed
field unit, the
**integer** descended equation
```
ω³⁷ + θ³⁷ = (δ' : 𝓞 K) · ((1-ζ)(1-ζ³⁶))^{2e-1} · z'³⁷
```
holds (`Λ = (1-ζ)(1-ζ³⁶)` as an element of `𝓞 K`).  The field equation descends by injectivity of
`algebraMap (𝓞 K) K`.  This is precisely the `hequation` hypothesis of
`freeContentCaseIIData37_of_descended_equation`.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1, pp. 179–180.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension NumberField.IsCMField

namespace BernoulliRegular.FLT37.Eichler

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-- **[SECTION-91-INTEGER-DESCENT] The integer-level descended equation.**

From the Section §9.1 factor/anchor/Assumption-II data (the hypotheses of
`washington_section91_descended_equation`, with the two roots `ηA, ηB` the field images of integer
`37`-th roots), **plus** integer witnesses
* `ω : 𝓞 K` with `algebraMap ω = u²·ρ_a·σρ_a`,
* `θ : 𝓞 K` with `algebraMap θ = -ρ_b·σρ_b`,
* `z' : 𝓞 K` with `algebraMap z' = ρ_0²`,
* `δ' : (𝓞 K)ˣ` with `algebraMap δ' = (δ:K)` for the σ-fixed field unit `δ` Section §9.1 produces,

the integer descended Fermat equation
```
ω³⁷ + θ³⁷ = (δ' : 𝓞 K) · ((1-ζ)(1-ζ³⁶))^{2e-1} · z'³⁷
```
holds in `𝓞 K`.  This is exactly the `hequation` input of
`freeContentCaseIIData37_of_descended_equation` (with `ζ` the primitive root `hζ.toInteger`; note
`Λ = (1-ζ)(1-ζ³⁶)` and `1-ζ³⁶ = 1-ζ⁻¹`).

Proof: take the field descended equation from `washington_section91_descended_equation`; since the
σ-fixed field unit it produces is `algebraMap δ'`, both sides are `algebraMap` of the claimed
integer expressions, so injectivity of `algebraMap (𝓞 K) K` descends the equation. -/
theorem washington_section91_integer_descended_equation
    {x y ρa ρb ρ0 : K} {ηa ηb η0 u : Kˣ} {ηA ηB : 𝓞 K}
    {Λa Λb Λ : Kˣ} {e : ℕ}
    (he : 1 ≤ e)
    (hA : ηA ^ 37 = 1) (hB : ηB ^ 37 = 1)
    (hA1 : ηA ≠ 1) (hB1 : ηB ≠ 1) (hAB : ηA ≠ ηB) (hABp : ηA * ηB ≠ 1)
    (hΛa : (Λa : K) = algebraMap (𝓞 K) K ((1 - ηA) * (1 - ηA ^ 36)))
    (hΛb : (Λb : K) = algebraMap (𝓞 K) K ((1 - ηB) * (1 - ηB ^ 36)))
    (hΛ : (Λ : K) = algebraMap (𝓞 K) K
      ((1 - (zeta_spec 37 ℚ K).toInteger) * (1 - (zeta_spec 37 ℚ K).toInteger ^ 36)))
    (hfa_pos : x + algebraMap (𝓞 K) K ηA * y =
      (1 - algebraMap (𝓞 K) K ηA) * (ηa : K) * ρa ^ 37)
    (hfa_neg : x + algebraMap (𝓞 K) K (ηA ^ 36) * y =
      (1 - algebraMap (𝓞 K) K (ηA ^ 36)) * (ηa : K) * (complexConj K ρa) ^ 37)
    (hfb_pos : x + algebraMap (𝓞 K) K ηB * y =
      (1 - algebraMap (𝓞 K) K ηB) * (ηb : K) * ρb ^ 37)
    (hfb_neg : x + algebraMap (𝓞 K) K (ηB ^ 36) * y =
      (1 - algebraMap (𝓞 K) K (ηB ^ 36)) * (ηb : K) * (complexConj K ρb) ^ 37)
    (hanchor : x + y = (η0 : K) * (Λ : K) ^ e * ρ0 ^ 37)
    (hII : (ηa : Kˣ) = u ^ 37 * ηb)
    (hη0real : complexConj K (η0 : K) = (η0 : K))
    (hηbreal : complexConj K (ηb : K) = (ηb : K))
    -- integer witnesses for the building blocks and the σ-fixed field unit:
    {ω θ z' : 𝓞 K} {δ' : (𝓞 K)ˣ}
    (hω : algebraMap (𝓞 K) K ω = (u : K) ^ 2 * (ρa * complexConj K ρa))
    (hθ : algebraMap (𝓞 K) K θ = -(ρb * complexConj K ρb))
    (hz' : algebraMap (𝓞 K) K z' = ρ0 ^ 2)
    (hδ' : ∀ δ : Kˣ, complexConj K (δ : K) = (δ : K) →
      ((u : K) ^ 2 * (ρa * complexConj K ρa)) ^ 37 +
          (-(ρb * complexConj K ρb)) ^ 37 =
        (δ : K) * (Λ : K) ^ (2 * e - 1) * (ρ0 ^ 2) ^ 37 →
      (δ : K) = algebraMap (𝓞 K) K (δ' : 𝓞 K)) :
    ω ^ 37 + θ ^ 37 =
      (δ' : 𝓞 K) *
        ((1 - (zeta_spec 37 ℚ K).toInteger) * (1 - (zeta_spec 37 ℚ K).toInteger ^ 36)) ^ (2 * e - 1) *
        z' ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- Section §9.1: the field descended equation, with a σ-fixed field unit `δ`.
  obtain ⟨δ, hδ_real, hδ_eq⟩ :=
    washington_section91_descended_equation he hA hB hA1 hB1 hAB hABp hΛa hΛb hΛ
      hfa_pos hfa_neg hfb_pos hfb_neg hanchor hII hη0real hηbreal
  -- The field unit descends to `algebraMap δ'`.
  have hδ_coe : (δ : K) = algebraMap (𝓞 K) K (δ' : 𝓞 K) := hδ' δ hδ_real hδ_eq
  -- Descend the field equation to `𝓞 K` by injectivity.
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  -- LHS image: `algebraMap (ω³⁷ + θ³⁷) = (u²ρ_aσρ_a)³⁷ + (-ρ_bσρ_b)³⁷`.
  rw [map_add, map_pow, map_pow, hω, hθ]
  -- RHS image: `algebraMap (δ'·Λ_int^{2e-1}·z'³⁷) = (δ:K)·(Λ:K)^{2e-1}·(ρ_0²)³⁷`.
  rw [map_mul, map_mul, map_pow, map_pow, hz', ← hΛ, ← hδ_coe]
  exact hδ_eq

end BernoulliRegular.FLT37.Eichler

end

end
