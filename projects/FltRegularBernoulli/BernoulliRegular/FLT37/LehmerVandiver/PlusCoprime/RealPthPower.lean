import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# T-PIVOT-2: Real-unit-side `p`-th-power equivalence

For an odd prime `p` and a unit `u ∈ (𝓞 K⁺)ˣ` of the maximal-real-subfield ring of
integers, the image of `u` in `(𝓞 K)ˣ` is a `p`-th power **iff** `u` is itself a
`p`-th power in `(𝓞 K⁺)ˣ`.

## Proof idea (reverse direction, the substantial one)

Given `α^p = alg u` in `(𝓞 K)ˣ`. Since `alg u ∈ realUnits K`, the obstruction
`ζ := unitsMulComplexConjInv K α = α · σ(α)⁻¹ ∈ torsion K` satisfies `ζ^p = 1`.

For odd `p`, the squaring map on the `p`-torsion subgroup `μ_p ⊂ torsion K` is
bijective: `η := ζ^((p+1)/2)` satisfies `η^2 = ζ` (because `ζ^p = 1`), and
`η^p = ζ^{p(p+1)/2} = (ζ^p)^{(p+1)/2} = 1`.

Setting `β_K := α · (η : (𝓞 K)ˣ)⁻¹`:
* `β_K^p = α^p · η^{-p} = α^p`, so `β_K^p = alg u`.
* `unitsMulComplexConjInv K β_K = ζ · (η^2)⁻¹ = ζ · ζ⁻¹ = 1`,
  so `β_K ∈ realUnits K`.

Hence `β_K = alg β` for some `β ∈ (𝓞 K⁺)ˣ`. By injectivity of the algebra map,
`β^p = u`.

## References

* [Reviewer reply, 2026-05-06] Caution 1: explicit lemma, not implicit coercion.
* `Mathlib.NumberTheory.NumberField.CMField` — `unitsMulComplexConjInv`,
  `realUnits`, `unitsMulComplexConjInv_ker`, `unitsMulComplexConjInv_apply_torsion`.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

namespace FLT37

universe u

variable (p : ℕ) [hp : Fact p.Prime]
variable {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

/-- The algebra-map embedding from the maximal real subfield's units. -/
private noncomputable abbrev algReal :
    (𝓞 (NumberField.maximalRealSubfield K))ˣ →* (𝓞 K)ˣ :=
  Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom

omit [NumberField K] [IsCMField K] in
/-- The algebra map `(𝓞 K⁺) → (𝓞 K)` is injective. -/
private theorem algebraMap_injective :
    Function.Injective (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :=
  FaithfulSMul.algebraMap_injective _ _

omit [NumberField K] [IsCMField K] in
/-- `algReal` is injective. -/
private theorem algReal_injective :
    Function.Injective (algReal (K := K)) := by
  intro a b h
  exact Units.ext <| algebraMap_injective (congrArg Units.val h)

omit [IsCyclotomicExtension {p} ℚ K] in
/-- For odd prime `p`, the embedding `(𝓞 K⁺)ˣ → (𝓞 K)ˣ` reflects `p`-th-power-ness:
a unit of `(𝓞 K⁺)ˣ` becomes a `p`-th power in `(𝓞 K)ˣ` iff it is already a `p`-th
power in `(𝓞 K⁺)ˣ`. -/
theorem isPthPower_image_iff (hp_odd : p ≠ 2) (u : (𝓞 (NumberField.maximalRealSubfield K))ˣ) :
    (∃ α : (𝓞 K)ˣ, algReal u = α ^ p) ↔
      ∃ β : (𝓞 (NumberField.maximalRealSubfield K))ˣ, u = β ^ p := by
  refine ⟨?_, fun ⟨β, hβ⟩ ↦ ⟨algReal β, by rw [hβ, map_pow]⟩⟩
  rintro ⟨α, hα⟩
  -- algReal u ∈ realUnits K (definition).
  have h_alg_in_real : algReal u ∈ NumberField.IsCMField.realUnits K := by
    rw [NumberField.IsCMField.mem_realUnits_iff]
    exact ⟨u, rfl⟩
  -- ζ := unitsMulComplexConjInv K α has ζ^p = 1.
  set ζ : NumberField.Units.torsion K := NumberField.IsCMField.unitsMulComplexConjInv K α
    with hζ_def
  have h_ζ_pow : ζ ^ p = 1 := by
    have h1 : ζ ^ p = NumberField.IsCMField.unitsMulComplexConjInv K (α ^ p) := by
      rw [hζ_def, ← map_pow]
    have h2 : NumberField.IsCMField.unitsMulComplexConjInv K (algReal u) = 1 := by
      have h_ker : algReal u ∈ (NumberField.IsCMField.unitsMulComplexConjInv K).ker := by
        rw [NumberField.IsCMField.unitsMulComplexConjInv_ker]
        exact h_alg_in_real
      rwa [MonoidHom.mem_ker] at h_ker
    rw [h1, ← hα]
    exact h2
  -- η := ζ^((p+1)/2). For p odd, η^2 = ζ and η^p = 1.
  set η : NumberField.Units.torsion K := ζ ^ ((p + 1) / 2) with hη_def
  have h_p_form : (p + 1) / 2 * 2 = p + 1 := by
    rcases hp.out.odd_of_ne_two hp_odd with ⟨n, hn⟩; omega
  have h_η_sq : η ^ 2 = ζ := by
    rw [hη_def, ← pow_mul, h_p_form, pow_succ, h_ζ_pow, one_mul]
  have h_η_p : η ^ p = 1 := by
    rw [hη_def, ← pow_mul, mul_comm, pow_mul, h_ζ_pow, one_pow]
  -- β_K := α · (η : (𝓞 K)ˣ)⁻¹ in (𝓞 K)ˣ.
  set β_K : (𝓞 K)ˣ := α * ((η : (𝓞 K)ˣ))⁻¹ with hβ_K_def
  -- β_K^p = α^p, since (η : (𝓞 K)ˣ)^p = 1.
  have h_η_unit_pow : ((η : (𝓞 K)ˣ)) ^ p = 1 := by
    have : ((η ^ p : NumberField.Units.torsion K) : (𝓞 K)ˣ) =
        ((1 : NumberField.Units.torsion K) : (𝓞 K)ˣ) :=
      congrArg (·) (congrArg Subtype.val h_η_p)
    simpa using this
  have h_β_K_pow : β_K ^ p = α ^ p := by
    rw [hβ_K_def, mul_pow]
    rw [show ((η : (𝓞 K)ˣ))⁻¹ ^ p = (((η : (𝓞 K)ˣ)) ^ p)⁻¹ from (inv_pow _ _).symm]
    rw [h_η_unit_pow, inv_one, mul_one]
  -- β_K ∈ realUnits since unitsMulComplexConjInv K β_K = 1.
  have h_β_K_real : β_K ∈ NumberField.IsCMField.realUnits K := by
    rw [← NumberField.IsCMField.unitsMulComplexConjInv_ker, MonoidHom.mem_ker]
    rw [hβ_K_def, map_mul, map_inv]
    -- unitsMulComplexConjInv K (η : (𝓞 K)ˣ) = η ^ 2 (apply torsion lemma)
    have h_torsion : NumberField.IsCMField.unitsMulComplexConjInv K ((η : (𝓞 K)ˣ)) = η ^ 2 :=
      NumberField.IsCMField.unitsMulComplexConjInv_apply_torsion (K := K) η
    rw [h_torsion, h_η_sq]
    exact mul_inv_cancel ζ
  -- Pull β_K back to (𝓞 K⁺)ˣ.
  rw [NumberField.IsCMField.mem_realUnits_iff] at h_β_K_real
  obtain ⟨β, hβ⟩ := h_β_K_real
  refine ⟨β, ?_⟩
  -- algReal β = β_K, so algReal (β^p) = β_K^p = α^p = algReal u, hence β^p = u.
  have h_alg_β : algReal β = β_K := by
    apply Units.ext
    simpa using hβ
  have h_alg_β_p : algReal (β ^ p) = algReal u := by
    rw [map_pow, h_alg_β, h_β_K_pow, ← hα]
  exact (algReal_injective h_alg_β_p).symm

end FLT37

end BernoulliRegular

end
