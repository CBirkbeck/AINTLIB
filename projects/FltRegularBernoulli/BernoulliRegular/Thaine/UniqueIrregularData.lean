import BernoulliRegular.Thaine.HerbrandRibetThirtySeven
import BernoulliRegular.BernoulliFast.Tactic

/-!
# Unique-irregular-index data structure

A reusable structure packaging "the prime `p` is irregular at unique index
`i_irreg` in the Herbrand-Ribet range" — the Bernoulli-side input to the
`ReflectionOtherDischarge` of the Thaine pivot.

For `p = 37`, `i_irreg = 32` is the unique irregular index in
`{2, 4, …, 34}`, so an instance `UniqueIrregularData 37 32` exists.
-/

@[expose] public section

namespace BernoulliRegular

namespace Thaine

/-- **`UniqueIrregularData p i_irreg`** — the Herbrand-Ribet uniqueness
data: `p ∣ B_{i_irreg}` and `p ∤ B_k` for every other even `k` in the
reflection range `{2, 4, …, p − 3}`.

This is the parametric input to `ReflectionOtherDischarge`'s
substantive content: combined with the Spiegelungssatz (existing
project Reflection package), it gives `¬ id.componentNontrivial j` for
every `j ≠ i_irreg` in the relevant range. -/
structure UniqueIrregularData (p i_irreg : ℕ) : Prop where
  /-- `p ∣ B_{i_irreg}` (the irregularity condition). -/
  dvd_at_irreg : (p : ℤ) ∣ (bernoulli i_irreg).num
  /-- `p ∤ B_{2k}` for every `k` with `2k ≤ p − 3`, `2k ≠ i_irreg`. -/
  not_dvd_elsewhere :
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ p - 3 → 2 * k ≠ i_irreg →
      ¬ (p : ℤ) ∣ (bernoulli (2 * k)).num

namespace UniqueIrregularData

/-- **FLT37 instance**: 32 is the unique irregular index for 37. -/
theorem thirtyseven_thirtytwo : UniqueIrregularData 37 32 where
  dvd_at_irreg := by
    bernoulli_decide
    -- bernoulli 32 = −7709321041217/510; (.num) = −7709321041217 = 37 × (−208360028141).
    exact ⟨-208360028141, by decide⟩
  not_dvd_elsewhere :=
    BernoulliRegular.Thaine.not_dvd_bernoulli_thirtyseven_except_thirtytwo

end UniqueIrregularData

end Thaine

end BernoulliRegular
