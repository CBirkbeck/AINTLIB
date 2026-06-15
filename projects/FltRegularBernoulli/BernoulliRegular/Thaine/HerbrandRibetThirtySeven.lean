import BernoulliRegular.BernoulliFast.Tactic
import Mathlib.NumberTheory.Bernoulli

/-!
# Herbrand-Ribet small-Bernoulli data for `p = 37`

For `p = 37`, irregular at index 32 (i.e., 37 ∣ B_{32}), the
Herbrand-Ribet theorem says: 37 ∣ (bernoulli k).num iff the
ω^{p-k}-eigencomponent of `Cl(K)⁻ ⊗ ℤ/37ℤ` is non-trivial.

To use this for the `ReflectionOtherDischarge` instance at `p = 37, i = 32`,
we need the negative direction at non-irregular indices: for even k in
`{2, 4, …, 34} \ {32}`, `37 ∤ (bernoulli k).num`. Combined with the
already-shipped `thirtyseven_dvd_bernoulli_thirtytwo_num` (37 ∣ B_{32}), this
characterises the irregular index uniquely.

These are small Bernoulli numbers (at most B_{34}), all within reach of
the `bernoulli_decide` tactic.

## References

* `BernoulliRegular.BernoulliFast.KellnerSecondOrder` —
  `thirtyseven_dvd_bernoulli_thirtytwo_num`.
* Pattern: `BernoulliRegular.BernoulliFast.TwentyThree.not_dvd_bernoulli_twentythree`.
-/

@[expose] public section

namespace BernoulliRegular

namespace Thaine

/-- **Herbrand-Ribet uniqueness for p = 37**: `37 ∤ (bernoulli (2k)).num`
for every `k` with `1 ≤ k`, `2k ≤ 34`, and `2k ≠ 32`. Combined with
`thirtyseven_dvd_bernoulli_thirtytwo_num` (37 ∣ B_{32}), this shows 32 is the
*unique* irregular index for 37 in the relevant range. -/
theorem not_dvd_bernoulli_thirtyseven_except_thirtytwo :
    ∀ k, 1 ≤ k → 2 * k ≤ 37 - 3 → 2 * k ≠ 32 →
      ¬ (37 : ℤ) ∣ (bernoulli (2 * k)).num := by
  intro k hk hk_range hk_ne
  have hk_upper : k ≤ 17 := by omega
  interval_cases k <;> first | (exact absurd rfl hk_ne) | bernoulli_decide

end Thaine

end BernoulliRegular
