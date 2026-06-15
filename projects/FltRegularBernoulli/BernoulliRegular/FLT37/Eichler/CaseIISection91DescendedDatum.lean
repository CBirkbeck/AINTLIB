import BernoulliRegular.FLT37.Eichler.CaseIISection91IntegerDescent
import BernoulliRegular.FLT37.Eichler.CaseIIFreeContentDatumPackaging

/-!
# [FLT37-CASEII-R2] The descended free-content datum from the factor equations (capstone)

This file composes the two proven halves of Washington's §9.1 conjugate-norm descent into a single
lemma: **from the factor equations of `x, y` (at two distinct indices `a, b`), the anchor equation,
Assumption II, and the descent invariants, the descended Washington datum `(ω, θ, ρ₀²)` IS a
`FreeContentCaseIIData37`.**  Concretely it chains

* `washington_section91_integer_descended_equation` (`CaseIISection91IntegerDescent.lean`) — the
  proven reassembly **algebra** lifted to `𝓞 K`: factor eqns + anchor + Assumption II + integer
  witnesses ⟹ the integer descended equation `ω³⁷ + θ³⁷ = δ'·((1−ζ)(1−ζ³⁶))^{2e−1}·z'³⁷`; and
* `freeContentCaseIIData37_of_descended_equation` (`CaseIIFreeContentDatumPackaging.lean`) — the
  proven **packaging**: the integer descended equation + reality + `𝔭`-coprimality + the two datum
  invariants (`hxy'`, `hdenom'`) ⟹ `∃ n' (D' : FreeContentCaseIIData37 K n'), D'.z = z'`.

The result `freeContentCaseIIData37_of_factorEquations` reduces the FLT37 Case-II descent step
**exactly** to the **factor-equation extraction** (Washington Lemma 9.1/9.2: producing the
conjugate-paired `37`-th-root generators `ρ_a, ρ_b, ρ_0` and the real units `η_a, η_b, η_0` from
the root-ideal
principalization), the integer witnesses, and the descent invariants `hxy'`/`hdenom'` (structure
fields, established by the construction — not derivable from the equation, by design).

The `λ`-content of the descended datum is `n' = 2·(2e−1)`, **even** (`λ = (1−ζ)(1−ζ³⁶)` is the real
prime, `v_𝔭 = 2`): the previously-suspected "content-parity obstruction" is **spurious** (it
conflated the real-`λ` exponent `2e−1` with the `(ζ−1)`-valuation `2(2e−1)`).

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1, pp. 179–180.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension NumberField.IsCMField

namespace BernoulliRegular.FLT37.Eichler

open FLT37 BernoulliRegular

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-- **[FLT37-CASEII-DESCENDED-DATUM] The descended Washington datum is a free-content datum.**

From the factor equations at two distinct indices `a, b` (with `ηA = ζ^a`, `ηB = ζ^b`,
`a ≢ ±b mod 37`), the squared-anchor equation, **Assumption II** (`η_a = u³⁷·η_b`), integer
witnesses `ω, θ, z'` for the conjugate-norm building blocks `u²ρ_aσρ_a`, `−ρ_bσρ_b`, `ρ₀²`, and
the descent
invariants (reality of `ω, θ`; `𝔭`-coprimality of `θ, z'`; `(ζ−1)³ ∣ ω+θ`; the sharp adjacent
denominator `hdenom'`), there is a free-content Case-II datum `D'` at content `n' = 2(2e−1)` whose
Fermat variable `D'.z` is exactly `z'` (`= ρ₀²`, Washington's `ξ₁`).

This is the composition of the proven reassembly **algebra**
(`washington_section91_integer_descended_equation`) with the proven **packaging**
(`freeContentCaseIIData37_of_descended_equation`).  It reduces the whole Case-II descent step to the
factor-equation extraction (Washington Lemma 9.1/9.2). -/
theorem freeContentCaseIIData37_of_factorEquations
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
    {ω θ z' : 𝓞 K} {δ' : (𝓞 K)ˣ}
    (hω : algebraMap (𝓞 K) K ω = (u : K) ^ 2 * (ρa * complexConj K ρa))
    (hθ : algebraMap (𝓞 K) K θ = -(ρb * complexConj K ρb))
    (hz' : algebraMap (𝓞 K) K z' = ρ0 ^ 2)
    (hδ' : ∀ δ : Kˣ, complexConj K (δ : K) = (δ : K) →
      ((u : K) ^ 2 * (ρa * complexConj K ρa)) ^ 37 +
          (-(ρb * complexConj K ρb)) ^ 37 =
        (δ : K) * (Λ : K) ^ (2 * e - 1) * (ρ0 ^ 2) ^ 37 →
      (δ : K) = algebraMap (𝓞 K) K (δ' : 𝓞 K))
    (hω_real : NumberField.IsCMField.ringOfIntegersComplexConj K ω = ω)
    (hθ_real : NumberField.IsCMField.ringOfIntegersComplexConj K θ = θ)
    (hθ_cop : ¬ (zeta_spec 37 ℚ K).toInteger - 1 ∣ θ)
    (hz'_cop : ¬ (zeta_spec 37 ℚ K).toInteger - 1 ∣ z')
    (hxy' : ((zeta_spec 37 ℚ K).toInteger - 1) ^ 3 ∣ ω + θ)
    (hdenom' : ∃ c : 𝓞 K,
      ω + θ * (zeta_spec 37 ℚ K).toInteger ^ 36 = ((zeta_spec 37 ℚ K).toInteger - 1) * c ∧
        ¬ ((zeta_spec 37 ℚ K).toInteger - 1) ∣ c) :
    ∃ (n' : ℕ) (D' : FreeContentCaseIIData37 K n'), D'.z = z' :=
  freeContentCaseIIData37_of_descended_equation (zeta_spec 37 ℚ K) he
    (washington_section91_integer_descended_equation he hA hB hA1 hB1 hAB hABp hΛa hΛb hΛ
      hfa_pos hfa_neg hfb_pos hfb_neg hanchor hII hη0real hηbreal hω hθ hz' hδ')
    hω_real hθ_real hθ_cop hz'_cop hxy' hdenom'

end BernoulliRegular.FLT37.Eichler

end

end
