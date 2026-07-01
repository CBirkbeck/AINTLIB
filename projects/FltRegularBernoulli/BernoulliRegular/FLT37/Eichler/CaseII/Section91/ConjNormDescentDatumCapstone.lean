import BernoulliRegular.FLT37.Eichler.CaseII.Section91.DescendedEquationIntegerLift
import BernoulliRegular.FLT37.Eichler.CaseII.FreeContent.DescentEquationPackaging

/-!
# Descended free-content datum from the factor equations

This file composes the two proven halves of Washington's §9.1 conjugate-norm
descent into a single lemma. From the factor equations of `x, y` at two
distinct indices, the anchor equation, Assumption II, and the descent
invariants, the descended Washington datum `(ω, θ, ρ₀²)` is a
`FreeContentCaseIIData37`.

The main result chains:

* `washington_section91_integer_descended_equation`: the reassembly algebra
  lifted to `𝓞 K`.
* `freeContentCaseIIData37_of_descended_equation`: the packaging step from the
  descended equation, reality, coprimality, and datum invariants.

The descended datum has even lambda-content `n' = 2 * (2 * e - 1)`. This
separates the real-prime exponent from the `(ζ - 1)`-valuation `2 * (2 * e - 1)`.

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

/-- The descended Washington datum obtained from the factor equations is a
free-content Case-II datum.

The result packages the factor equations, the squared-anchor equation,
Assumption II, integer witnesses for the conjugate-norm building blocks, and
the descent invariants into a datum `D'` with Fermat variable `D'.z = z'`. -/
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
