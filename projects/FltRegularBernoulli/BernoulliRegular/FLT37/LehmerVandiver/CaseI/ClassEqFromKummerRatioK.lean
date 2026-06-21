import BernoulliRegular.FLT37.LehmerVandiver.CaseI.ClassEqFromConjEquation


/-!
# LV010-class-eq-1e: Class equality from K-level Kummer ratio

K-level wrapper: given `α / σ(α) = β^p` in `K^×` (the natural form
of Stage 2's Kummer's lemma output), clear denominators to obtain
`α · δ^p = σ(α) · γ^p` in `𝓞 K` (with γ, δ ∈ 𝓞 K, δ ≠ 0), then
apply `caseI_class_eq_complexConj_of_conj_kummer_eq` to derive
`[σ𝔞] = [𝔞]`.

This bridges Stage 2's natural K-level statement to LV010-A's
class-equality input.

## References

* `caseI_class_eq_complexConj_of_conj_kummer_eq` (LV010-class-eq-1d).
* `IsFractionRing.div_surjective` from mathlib for clearing denominators.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseI

/-- **K-level Kummer ratio implies integral conjugate equation.**
Given `β ∈ K^×`, write `β = algebraMap (𝓞 K) K γ / algebraMap (𝓞 K) K δ`
for some γ ∈ 𝓞 K and δ ∈ (𝓞 K)^* (using `IsFractionRing` of 𝓞 K).

For our purpose: from `α / σ(α) = β^p` in K with α, σα ∈ (𝓞 K)^*,
derive an integral identity `α · δ^p = σ(α) · γ^p`. -/
theorem exists_integral_kummer_ratio_of_K
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
    {α : 𝓞 K} (_hα : α ≠ 0)
    (hσα : ringOfIntegersComplexConj K α ≠ 0)
    {β : K} (hβ : β ≠ 0)
    (h_kummer :
      (algebraMap (𝓞 K) K α) / (algebraMap (𝓞 K) K (ringOfIntegersComplexConj K α))
        = β ^ p) :
    ∃ (γ δ : 𝓞 K), γ ≠ 0 ∧ δ ≠ 0 ∧
      α * δ ^ p = ringOfIntegersComplexConj K α * γ ^ p := by
  -- Write `β = algebraMap γ / algebraMap δ` with `γ ∈ 𝓞 K`, `δ ∈ (𝓞 K)⁰`,
  -- then cross-multiply `α / σα = β ^ p` and lift to `𝓞 K` by injectivity.
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  obtain ⟨⟨γ, δ⟩, hγδ⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) β
  have hδ_ne : (δ : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero δ.2
  have hγ_ne : γ ≠ 0 := by
    intro hγ_eq
    apply hβ
    rw [hγ_eq, map_zero] at hγδ
    exact (mul_eq_zero.mp hγδ).resolve_right (hinj.ne hδ_ne)
  refine ⟨γ, δ, hγ_ne, hδ_ne, hinj ?_⟩
  push_cast
  rw [div_eq_iff (hinj.ne hσα)] at h_kummer
  have h_β_δ_pow : β ^ p * algebraMap (𝓞 K) K (δ : 𝓞 K) ^ p =
      algebraMap (𝓞 K) K γ ^ p := by rw [← mul_pow, hγδ]
  linear_combination (algebraMap (𝓞 K) K (δ : 𝓞 K)) ^ p * h_kummer +
    algebraMap (𝓞 K) K (ringOfIntegersComplexConj K α) * h_β_δ_pow

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
