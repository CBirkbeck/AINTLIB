module

public import BernoulliRegular.Reflection.SingularKummer.LocalizationKernel

/-!
# Local `p`-th powers at `λ`

This file contains only the local-primary condition used by the one-sided
Kummer reciprocity target.  The condition is expressed in the same concrete
completed lambda-local quotient used by the singular-pair localization kernel:
the lambda valuation is divisible by `p`, and the normalized local-unit class
maps trivially to completed principal units modulo `p`-th powers.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

open Reflection.SingularKummer
open Reflection.SingularKummer.SingularPair

/-- Exact local `p`-th-power condition in the valued completion of `K` at
`λ = ζ_p - 1`, for field elements, stated through the concrete completed
principal-unit quotient used by the singular Kummer localization map. -/
def IsLambdaLocalPthPowerField (x : K) : Prop :=
  ∃ hx : x ≠ 0,
    (p : ℤ) ∣
      localUniformizerExponent (R := 𝓞 K) (K := K)
        (cyclotomicLambdaHeightOne (p := p) K) (Units.mk0 x hx) ∧
    cyclotomicLocalUnitPowerQuotientToCompletedPrincipalUnitModP p K
        (fieldUnitToLocalUnitPowerQuotient (R := 𝓞 K) (K := K)
          (cyclotomicLambdaHeightOne (p := p) K) p (Units.mk0 x hx)) = 1

/-- Exact local `p`-th-power condition in the valued completion of `K` at
`λ = ζ_p - 1`, for integral elements. -/
def IsLambdaLocalPthPower (α : 𝓞 K) : Prop :=
  IsLambdaLocalPthPowerField (p := p) (K := K) (algebraMap (𝓞 K) K α)

/-- A field element satisfying the local unit `p`-th-power condition is
nonzero. -/
theorem IsLambdaLocalPthPowerField.ne_zero {x : K}
    (hx : IsLambdaLocalPthPowerField (p := p) (K := K) x) : x ≠ 0 :=
  hx.choose

/-- An integral element satisfying the local unit `p`-th-power condition is
nonzero. -/
theorem IsLambdaLocalPthPower.ne_zero {α : 𝓞 K}
    (hα : IsLambdaLocalPthPower (p := p) (K := K) α) : α ≠ 0 := fun hα_zero =>
  IsLambdaLocalPthPowerField.ne_zero (p := p) (K := K) hα
    (by simp [hα_zero])

/-- A global `p`-th power is a local `p`-th power at `λ`. -/
theorem IsLambdaLocalPthPowerField.of_pow {x : K} (hx : x ≠ 0) :
    IsLambdaLocalPthPowerField (p := p) (K := K) (x ^ p) := by
  let v := cyclotomicLambdaHeightOne (p := p) K
  let xu : Kˣ := Units.mk0 x hx
  have hxpow_ne : x ^ p ≠ 0 := pow_ne_zero p hx
  let xpu : Kˣ := Units.mk0 (x ^ p) hxpow_ne
  have hxpu : xpu = xu ^ p := by
    ext
    rfl
  refine ⟨hxpow_ne, ?_, ?_⟩
  · change (p : ℤ) ∣ localUniformizerExponent (R := 𝓞 K) (K := K) v xpu
    refine ⟨localUniformizerExponent (R := 𝓞 K) (K := K) v xu, ?_⟩
    rw [hxpu]
    rw [localUniformizerExponent_eq_count_toPrincipalIdeal]
    rw [localUniformizerExponent_eq_count_toPrincipalIdeal]
    rw [map_pow, Units.val_pow_eq_pow_val, FractionalIdeal.count_pow]
  · change cyclotomicLocalUnitPowerQuotientToCompletedPrincipalUnitModP p K
        (fieldUnitToLocalUnitPowerQuotient (R := 𝓞 K) (K := K) v p xpu) = 1
    rw [hxpu]
    have hfield :
        fieldUnitToLocalUnitPowerQuotient (R := 𝓞 K) (K := K) v p (xu ^ p) = 1 :=
      fieldUnitToLocalUnitPowerQuotient_pow_eq_one (R := 𝓞 K) (K := K) v p xu
    rw [hfield]
    simp

/-- An integral global `p`-th power is a local `p`-th power at `λ`. -/
theorem IsLambdaLocalPthPower.of_pow {β : 𝓞 K} (hβ : β ≠ 0) :
    IsLambdaLocalPthPower (p := p) (K := K) (β ^ p) := by
  have hβK : algebraMap (𝓞 K) K β ≠ 0 :=
    (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hβ
  simpa [IsLambdaLocalPthPower, map_pow] using
    IsLambdaLocalPthPowerField.of_pow
      (p := p) (K := K) hβK

/-- `1` is a local `p`-th power at `λ`. -/
theorem IsLambdaLocalPthPower.one :
    IsLambdaLocalPthPower (p := p) (K := K) (1 : 𝓞 K) := by
  simpa using IsLambdaLocalPthPower.of_pow
    (p := p) (K := K) (β := (1 : 𝓞 K)) one_ne_zero

/-- A completed-localization-kernel singular pair supplies the local-primary
condition for the integral numerator represented by its generator. -/
theorem IsLambdaLocalPthPower.of_singularPair_completedLocalization_eq_zero
    {η : 𝓞 K} {s : SingularPair (𝓞 K) K p}
    (hη_ne : η ≠ 0)
    (hη_generator : algebraMap (𝓞 K) K η = (generator s : K))
    (hs_loc :
      singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K
        (Additive.ofMul
          (QuotientGroup.mk s :
            SingularGroup (R := 𝓞 K) (K := K) p)) = 0) :
    IsLambdaLocalPthPower (p := p) (K := K) η := by
  let v := cyclotomicLambdaHeightOne (p := p) K
  have hηK_ne : algebraMap (𝓞 K) K η ≠ 0 :=
    (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hη_ne
  let ηu : Kˣ := Units.mk0 (algebraMap (𝓞 K) K η) hηK_ne
  have hηu_generator : ηu = generator s := by
    ext
    exact hη_generator
  refine ⟨hηK_ne, ?_, ?_⟩
  · change (p : ℤ) ∣ localUniformizerExponent (R := 𝓞 K) (K := K) v ηu
    rw [hηu_generator]
    exact localUniformizerExponent_generator_dvd
      (R := 𝓞 K) (K := K) v p s
  · have hmul :
        singularGroupLocalizationToCompletedPrincipalUnits (p := p) K
          (QuotientGroup.mk s :
            SingularGroup (R := 𝓞 K) (K := K) p) = 1 := by
      apply Additive.ofMul.injective
      change Additive.ofMul
          (singularGroupLocalizationToCompletedPrincipalUnits (p := p) K
            (QuotientGroup.mk s :
              SingularGroup (R := 𝓞 K) (K := K) p)) = 0
      simpa [singularGroupLocalizationToCompletedPrincipalUnitsLinear] using hs_loc
    change cyclotomicLocalUnitPowerQuotientToCompletedPrincipalUnitModP p K
        (fieldUnitToLocalUnitPowerQuotient (R := 𝓞 K) (K := K) v p ηu) = 1
    rw [hηu_generator]
    simpa [singularGroupLocalizationToCompletedPrincipalUnits,
      singularGroupLocalizationToCyclotomicLocalUnits, v] using hmul

end Furtwaengler

end BernoulliRegular
