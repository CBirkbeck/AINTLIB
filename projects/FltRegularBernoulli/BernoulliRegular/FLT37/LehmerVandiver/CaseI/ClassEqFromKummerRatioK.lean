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

set_option backward.isDefEq.respectTransparency false in
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
  -- Use IsFractionRing to write β = algebraMap γ' / algebraMap δ' for
  -- some γ' ∈ 𝓞 K and δ' ∈ (𝓞 K)⁰ (= nonZeroDivisors of 𝓞 K).
  obtain ⟨⟨γ, δ⟩, hγδ⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) β
  -- hγδ : β * algebraMap _ _ δ.val = algebraMap _ _ γ
  have hδ_ne : (δ : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero δ.2
  -- From β = γ/δ at the K level, raising to p-th power: β^p = γ^p/δ^p.
  -- Combined with h_kummer: α/σα = γ^p/δ^p in K.
  -- Cross-multiply: α · δ^p = σα · γ^p in K, hence in 𝓞 K (both sides integral).
  have hγ_ne : γ ≠ 0 := by
    intro hγ_eq
    apply hβ
    -- hγδ : β * algebraMap δ = algebraMap γ. With γ = 0, get β · alg(δ) = 0.
    rw [hγ_eq, map_zero] at hγδ
    have hδ_K_ne : algebraMap (𝓞 K) K (δ : 𝓞 K) ≠ 0 :=
      (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hδ_ne
    exact (mul_eq_zero.mp hγδ).resolve_right hδ_K_ne
  refine ⟨γ, δ, hγ_ne, hδ_ne, ?_⟩
  -- Goal: α · δ^p = σα · γ^p in 𝓞 K.
  -- Strategy: prove in K (using h_kummer + hγδ), lift via injectivity.
  apply (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  push_cast
  -- Now in K: h_kummer is α/σα = β^p; hγδ is β · δ = γ.
  -- Goal in K: α · δ^p = σα · γ^p.
  have hσα_K : algebraMap (𝓞 K) K (ringOfIntegersComplexConj K α) ≠ 0 :=
    (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hσα
  rw [div_eq_iff hσα_K] at h_kummer
  have hδ_K : algebraMap (𝓞 K) K (δ : 𝓞 K) ≠ 0 :=
    (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hδ_ne
  have h_β_δ_pow : β ^ p * algebraMap (𝓞 K) K (δ : 𝓞 K) ^ p =
      algebraMap (𝓞 K) K γ ^ p := by
    rw [← mul_pow]
    have : β * algebraMap (𝓞 K) K (δ : 𝓞 K) = algebraMap (𝓞 K) K γ := hγδ
    rw [this]
  -- linear_combination: δ^p · h_kummer + σα · h_β_δ_pow gives
  --   α · δ^p - σα · γ^p ≡ 0 (mod the trivial parts).
  linear_combination (algebraMap (𝓞 K) K (δ : 𝓞 K)) ^ p * h_kummer +
    algebraMap (𝓞 K) K (ringOfIntegersComplexConj K α) * h_β_δ_pow

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
