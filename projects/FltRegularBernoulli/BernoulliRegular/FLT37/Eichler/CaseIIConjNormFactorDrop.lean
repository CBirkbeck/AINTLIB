import BernoulliRegular.FLT37.Eichler.CaseIIAnchorSquareDatum

/-!
# [FLT37-CASEII-R2] The conjugate-norm strict factor drop (Washington Thm 9.4, `ξ₁ = ρ₀σρ₀`)

This file establishes, **soundly and with no residual**, the genuine factor-count content of
Washington *Cyclotomic Fields* (2nd ed., GTM 83) §9.1 Theorem 9.4: the conjugate-norm new
variable `ξ₁ = ρ₀·σρ₀` has **strictly fewer distinct prime ideal factors** than the Fermat
variable `z` of a real Case-II datum, in the **non-terminal** regime (some adjacent `Bₐ ≠ (1)`,
`a ≥ 1`).

## What is proved (composing two PROVEN halves into a result the repo did not have)

`caseII_conjNorm_factorCount_strict` :  for a real Case-II datum `D` whose adjacent corrected
radical at `η = D.etaOne = ζ` is **not** a unit (the non-terminal hypothesis), there is a
**real**, `𝔭`-coprime `ξ₁ : 𝓞 K` with
```
ringOfIntegersComplexConj K ξ₁ = ξ₁   ∧   ¬ (ζ−1) ∣ ξ₁   ∧
(normalizedFactors (Ideal.span {ξ₁})).toFinset.card  <  caseIIZFactorCount D.toCaseIIData37 .
```
That is, Washington's `ξ₁ = ρ₀σρ₀` *is* an explicit real element whose distinct-prime count is
strictly below that of `z`.  The two proven halves are:

* `caseII_anchorPow_conjNorm_real_span` (`CaseIIAnchorSquareDatum.lean`) — the conjugate norm
  `ξ₁ = ρ₀·σρ₀` of a generator `ρ₀` of the principal anchor power `𝔞₀^{k'}` is real, `𝔭`-coprime,
  and `(ξ₁) = 𝔞₀^{2k'}`;
* `caseIIZFactorCount_strict_of_anchor_supported` (`CaseIIFactorDescentAnchor.lean`) — **any**
  `z'` whose prime support lies in that of the `𝔭`-free anchor `𝔞₀` has strictly fewer distinct
  prime factors than `z` under the non-terminal hypothesis (the dropped prime is a factor of a
  nontrivial non-anchor `𝔞(η₁)`, coprime to `𝔞₀`).

The bridge between them is the proven support arithmetic
`caseII_anchorSupported_of_span_eq_anchorPow` (`(ξ₁) = 𝔞₀^{2k'}` ⟹ `support(ξ₁) ⊆ support(𝔞₀)`).

## Why this is the sound form of Washington's descent (no measure mismatch)

`caseIIZFactorCount_strict_of_anchor_supported` consumes only the **ideal-theoretic** support of
`ξ₁`; it does **not** require `ξ₁` to head a fresh `RealCaseIIData37`.  This is the crucial point.
The conjugate-norm equation exhibiting `ξ₁` as a Fermat variable sits at the **doubled**
`λ`-measure `λ^{2m−p}` (Washington p. 172), whose `(ζ−1)`-content `2m−37 ≢ 0 (mod 37)` is
**incompatible** with the `RealCaseIIData37` content `37·(m'+1)` (the proven certificate
`caseII_realCaseIIData37_lambda_content_mul_p`).  So the factor drop must be — and here **is** —
phrased on `ξ₁` *as an element/ideal*, never as a re-packaged datum at the wrong measure.

## The remaining open content (isolated precisely, at the correct measure)

The well-founded descent `no_realCaseIIData37_of_factorDescent` (`CaseIIFactorDescent.lean`) is
keyed to the minimal achieved `caseIIZFactorCount` **over `RealCaseIIData37`**.  Turning the strict
drop on the *element* `ξ₁` into a contradiction with that minimality requires `ξ₁` to be the Fermat
variable of a Case-II datum *in the minimised pool* — i.e. Washington's
`ω₁^p + θ₁^p = δ·λ^{2m−p}·ξ₁^p` must be realised as a datum.  At the doubled measure this is **not**
a `RealCaseIIData37`; it is a Case-II datum at a *free* `λ`-content `n = 2m−p` (not `≡ 0 (mod p)`),
whose root-ideal factorisation `𝔞η^p = 𝔠η` does **not** hold (`span{ω₁^p+θ₁^p} = 𝔭^n·(ξ₁)^p` is not
a perfect `p`-th power for `n ≢ 0 (mod p)`).  This is the genuine remaining R2 content: a
**free-content Case-II datum** (generalising flt-regular's `InductionStep`, where the anchor `B₀`
absorbs the `n mod p` excess) on which the minimality is run, the producer's doubled-measure
equation fits natively, and the proven terminal first-layer (content-agnostic) and **this** strict
drop both fire.  It is *not* the measure-mismatched `CaseIIRealAnchorDatumIdeal37` (which forces the
doubled-measure variable into the `37·(m'+1)`-content frame and is undischargeable as stated).

This file imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–§9.2 (Theorem 9.4),
  pp. 171–173 (the conjugate-norm new variable `ξ₁ = ρ₀σρ₀`, `(ξ₁) = B₀²`, with strictly fewer
  distinct prime factors than `z`; the doubled measure `λ^{2m−p}`).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **[FLT37-CASEII-CONJ-NORM-FACTOR-DROP] Washington's `ξ₁ = ρ₀σρ₀` has strictly fewer distinct
prime factors than `z`** (GTM 83 Theorem 9.4, p. 172), in the non-terminal regime.

For a real Case-II datum `D` whose adjacent corrected radical
`α = (-η)⁻¹·(x+yη)/(x+yη⁻¹)` at `η = D.etaOne = ζ` is **not** a unit of `𝓞 K` (the non-terminal
condition `𝔞(η)/𝔞(η⁻¹) ≠ (1)`, i.e. some `Bₐ ≠ (1)`, `a ≥ 1`), there is a **real**, `𝔭`-coprime
element `ξ₁ : 𝓞 K` — the conjugate norm `ρ₀·σρ₀` of a generator `ρ₀` of a principal power of the
`𝔭`-free anchor `𝔞₀ = aEtaZeroDvdPPow` — whose principal ideal `(ξ₁)` has **strictly fewer**
distinct prime factors than the Fermat variable `(D.z)`:  `count (ξ₁) < caseIIZFactorCount D`.

Construction (all proven): `caseII_anchorPow_conjNorm_real_span` gives `ξ₁ = ρ₀σρ₀` real,
`𝔭`-coprime, with `(ξ₁) = 𝔞₀^{2k'}` (`k' ≥ 1`); `caseII_anchorSupported_of_span_eq_anchorPow`
turns the anchor-power ideal into the support inclusion `support(ξ₁) ⊆ support(𝔞₀)`; and
`caseIIZFactorCount_strict_of_anchor_supported` delivers the strict drop from anchor support plus
the non-terminal hypothesis (the dropped prime divides a nontrivial non-anchor `𝔞(η₁)`, coprime to
the anchor).

This is the sound, residual-free factor-count content of Washington's descent: the strict drop is
on `ξ₁` *as an element/ideal*, never as a re-packaged datum, so the doubled-measure obstruction
(`2m − 37 ≢ 0 (mod 37)`, incompatible with the `RealCaseIIData37` content `37·(m'+1)`) does not
arise. -/
theorem caseII_conjNorm_factorCount_strict
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hnonterm : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical D D.etaOne (caseII_correctionUnit D.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) :
    ∃ ξ₁ : 𝓞 (CyclotomicField 37 ℚ),
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ξ₁ = ξ₁ ∧
      ¬ (D.hζ.toInteger - 1) ∣ ξ₁ ∧
      (normalizedFactors (Ideal.span ({ξ₁} : Set (𝓞 (CyclotomicField 37 ℚ))))).toFinset.card <
        caseIIZFactorCount D.toCaseIIData37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- Washington's `ξ₁ = ρ₀σρ₀`: real, `𝔭`-coprime, `(ξ₁) = 𝔞₀^{2k'}` (`k' ≥ 1`).  PROVEN.
  obtain ⟨ξ₁, k, hk, hξ_real, hξ_p, hξ_span⟩ := caseII_anchorPow_conjNorm_real_span D
  -- `(ξ₁) = 𝔞₀^k` ⟹ `support(ξ₁) ⊆ support(𝔞₀)`.  PROVEN support arithmetic.
  have hsupp := caseII_anchorSupported_of_span_eq_anchorPow D hk hξ_span
  -- anchor support + non-terminal ⟹ strict factor drop.  PROVEN.
  refine ⟨ξ₁, hξ_real, hξ_p, ?_⟩
  exact caseIIZFactorCount_strict_of_anchor_supported D (by decide : (37 : ℕ) ≠ 2) hnonterm hsupp

/-- **Non-vacuity of the non-terminal regime.**  The hypothesis of
`caseII_conjNorm_factorCount_strict` is the genuine descent regime, not vacuously excluded: the
*complementary* (unit) branch — the corrected radical at `η = ζ` being a unit — is the proven
first-layer contradiction `caseIIFirstLayer_false` (`False`).  So the non-terminal branch is
exactly the regime in which no first-layer collapse occurs, and the strict drop is the live
content. -/
theorem caseII_conjNorm_factorCount_strict_nonvacuous
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    (∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical D D.etaOne (caseII_correctionUnit D.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) → False :=
  fun ⟨αU, hαU⟩ ↦ caseIIFirstLayer_false D αU hαU

end BernoulliRegular.FLT37.Eichler

end

end
