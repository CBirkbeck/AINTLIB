import BernoulliRegular.FLT37.LehmerVandiver.CaseI.IdealPowCancel
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.ClassEqFromKummerRatio

/-!
# LV010-class-eq-1c: Class equality from integral Kummer ratio

Given the IDEAL-LEVEL identity `(𝔞·(γ))^p = (σ𝔞·(δ))^p` (the integral
form derived from `α / σα = (γ/δ)^p` after multiplying by `σα^{p-1} ·
δ^p`), we use `Ideal.pow_left_inj_of_ne_zero` to conclude
`𝔞 · (γ) = σ𝔞 · (δ)`, hence `[𝔞] = [σ𝔞]` in `Cl(K)` (since principal
ideals have trivial class).

This is the IDEAL-level cancellation chain. Combined with stage 2's
output (Kummer's lemma adapted), it gives the class-equality input
that LV010-A consumes.

## References

* `Ideal.pow_left_inj_of_ne_zero` (LV010-class-eq-1b).
* `caseI_class_eq_complexConj_of_class_ratio_eq_one` (LV010-class-eq-1).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseI

/-- **Class equality from ideal-level Kummer cancellation.** Given:
- `𝔞, σ𝔞 : Ideal (𝓞 K)`, both nonzero
- `γ, δ : 𝓞 K`, both nonzero
- `(𝔞·(γ))^p = (σ𝔞·(δ))^p`

derive `[σ𝔞] = [𝔞]` in `Cl(𝓞 K)`. -/
theorem caseI_class_eq_of_ideal_pow_factored
    {p : ℕ} [Fact p.Prime] (hp_pos : 0 < p) {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
    {𝔞 𝔞' : Ideal (𝓞 K)} (h𝔞_nz : 𝔞 ≠ ⊥) (h𝔞'_nz : 𝔞' ≠ ⊥)
    {γ δ : 𝓞 K} (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (h_pow_eq : (𝔞 * Ideal.span ({γ} : Set _)) ^ p =
      (𝔞' * Ideal.span ({δ} : Set _)) ^ p) :
    ClassGroup.mk0
        (⟨𝔞', mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞'_nz⟩
          : nonZeroDivisors (Ideal (𝓞 K))) =
      ClassGroup.mk0
        (⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩
          : nonZeroDivisors (Ideal (𝓞 K))) := by
  have hγ_ne : Ideal.span ({γ} : Set (𝓞 K)) ≠ ⊥ :=
    mt Ideal.span_singleton_eq_bot.mp hγ
  have hδ_ne : Ideal.span ({δ} : Set (𝓞 K)) ≠ ⊥ :=
    mt Ideal.span_singleton_eq_bot.mp hδ
  -- Cancel the `p`-th power on the ideal identity, then read off the class
  -- equality via `mk0_eq_mk0_iff`: the principal factors `(δ)`, `(γ)` are the
  -- witnesses certifying `[σ𝔞] = [𝔞]`.
  have h_canceled : 𝔞 * Ideal.span ({γ} : Set (𝓞 K)) =
      𝔞' * Ideal.span ({δ} : Set (𝓞 K)) :=
    Ideal.pow_left_inj_of_ne_zero (n := p) (Nat.pos_iff_ne_zero.mp hp_pos)
      (mul_ne_zero h𝔞_nz hγ_ne) (mul_ne_zero h𝔞'_nz hδ_ne) h_pow_eq
  refine ClassGroup.mk0_eq_mk0_iff.mpr ⟨δ, γ, hδ, hγ, ?_⟩
  rw [mul_comm (Ideal.span ({δ} : Set (𝓞 K))), ← h_canceled, mul_comm]

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
