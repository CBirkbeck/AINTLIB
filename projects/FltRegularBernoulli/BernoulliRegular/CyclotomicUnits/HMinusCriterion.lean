module

public import BernoulliRegular.HMinusCriterion

/-!
# Minus class-number criterion for the cyclotomic-unit route

This file records the `h⁻`/Bernoulli-numerator API in the direction used by the
cyclotomic-unit proof of weak reflection.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

/-- Contrapositive form of `p_dvd_hMinus_iff_p_dvd_some_bernoulli`.

For the concrete model `CyclotomicField p ℚ`, use this theorem with
`K := CyclotomicField p ℚ` after installing the CM-field instance from
`isCMField_of_cyclotomic`. The divisibility statements already have the
needed casts: `hMinus` uses `(p : ℕ)`, while Bernoulli numerators use
`(p : ℤ)`.
-/
theorem bernoulli_nonzero_of_not_dvd_hMinus
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K] (hp_odd : p ≠ 2)
    (hminus : ¬ (p : ℕ) ∣ hMinus K) :
    ∀ k, 1 ≤ k → 2 * k ≤ p - 3 →
      ¬ (p : ℤ) ∣ (bernoulli (2 * k)).num := fun k hk hk_range hnum =>
  hminus <|
    (p_dvd_hMinus_iff_p_dvd_some_bernoulli (p := p) (K := K) hp_odd).2
      ⟨k, hk, hk_range, hnum⟩

end BernoulliRegular

end
