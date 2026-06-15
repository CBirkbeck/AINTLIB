import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Thaine.Bridge
import BernoulliRegular.BernoulliFast.ValuesUpTo100

/-!
# T-PIVOT-5: `reflectionOtherComponents` — Spiegelung at non-irregular indices

The third of the four `FLT37UnitClassBridge` field discharges. For a prime
`p` with `UniqueIrregularIndex p i_irreg` (i.e., `i_irreg` is the only even
index in `{2, 4, …, p−3}` with `p ∣ B_{i_irreg}`):

  ∀ j : ℕ, j ≠ i_irreg → ClassGroupPlusComponentTrivial p K j.

By the Spiegelungssatz `[Wash97 §10.3 Theorem 10.10]`:
  rk_p Cl(K⁺)(ω^j) ≤ rk_p Cl(K)⁻(ω^{1−j}).

By Herbrand–Ribet `[Wash97 §6.3]`: the relevant minus component is controlled
by Bernoulli divisibility in the Herbrand range. Under
`UniqueIrregularIndex p i_irreg`, the only even Bernoulli index in that range
with `p ∣ B_i` is `i = i_irreg`, so `Cl(K)⁻(ω^{1−j})[p]` is trivial for
every `j ≠ 1 − i_irreg ≡ i_irreg` (mod p − 1) modulo the convention
identifying the "reflected" eigenspace with `ω^{i_irreg}` itself
(see Wash97 conventions).

For `p = 37`, `i_irreg = 32`: only the eigenspace at the reflected index
can be non-trivial; all others are p-trivial via Spiegelungssatz.

**Note (2026-05-06):** at this stage `ClassGroupPlusComponentTrivial` is
an opaque carrier Prop, so the discharge is structurally trivial. The
substantive Spiegelungssatz application is deferred to the future
refinement that makes the Prop content-bearing — at which point this
proof will need to invoke the project's existing reflection / T044
infrastructure together with the Herbrand–Ribet identification.

## References

* T-PIVOT-1 (`UnitClassBridge.lean`).
* `BernoulliRegular.Reflection.Final` — T044 / `ReflectionMinusNontrivialityBridge`.
* [Wash97] §10.3 (Spiegelungssatz, Theorem 10.10), §6.3 (Herbrand–Ribet).
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

/-- **T-PIVOT-5 implication**: under `UniqueIrregularIndex p i_irreg`,
every eigenspace of `Cl(K⁺) ⊗ ℤ_p` other than `ω^{i_irreg}` is trivial.

With the current opaque-Prop carrier this is structurally trivial; the
substantive content will appear when `ClassGroupPlusComponentTrivial`
is refined to a concrete eigenspace formulation, at which point the
proof will need to invoke the Spiegelungssatz + Herbrand–Ribet chain. -/
theorem classGroupPlusComponentTrivial_of_unique_irregular
    (i_irreg : ℕ) (_ : UniqueIrregularIndex p i_irreg) :
    ∀ j : ℕ, j ≠ i_irreg → ClassGroupPlusComponentTrivial p K j := by
  intro j _
  unfold ClassGroupPlusComponentTrivial
  intro _
  trivial

/-- **Small Bernoulli exclusion for `p = 37`.**

The unique-irregular-index certificate says that, in the Herbrand range,
`37` divides only `B_32`.  This reformulation accepts an arbitrary even
index `j` in the same range, instead of requiring it to be written as
`2 * k`. -/
theorem not_dvd_bernoulli_thirtyseven_of_even_ne_thirtytwo
    (h_unique : UniqueIrregularIndex 37 32) {j : ℕ}
    (hj_pos : 0 < j) (hj_le : j ≤ 37 - 3) (hj_even : Even j)
    (hj_ne : j ≠ 32) :
    ¬ (37 : ℤ) ∣ (bernoulli j).num := by
  rcases hj_even with ⟨k, rfl⟩
  simpa [two_mul] using
    UniqueIrregularIndex.not_dvd_elsewhere h_unique k (by omega)
      (by simpa [two_mul] using hj_le) (by simpa [two_mul] using hj_ne)

/-- **Bernoulli exclusion for all even reflection indices at `p = 37`.**

This folds the boundary component `j = 36` into the usual Herbrand range
exclusion.  In the interior range `j ≤ 34` it uses the unique-irregular-index
certificate; at the boundary it uses the cached exact value of `B_36`. -/
theorem not_dvd_bernoulli_thirtyseven_of_even_reflection_ne_thirtytwo
    (h_unique : UniqueIrregularIndex 37 32) {j : ℕ}
    (hj_index : IsReflectionComponentIndex 37 j) (hj_even : Even j)
    (hj_ne : j ≠ 32) :
    ¬ (37 : ℤ) ∣ (bernoulli j).num := by
  by_cases hj_boundary : j = 36
  · subst hj_boundary
    norm_num [BernoulliFast.bernoulli_36]
  · have hj_le : j ≤ 37 - 3 := by
      obtain ⟨k, hk⟩ := hj_even
      have hk_lt : k + k < 37 := by
        simpa [hk] using hj_index.2
      have hk_ne : k ≠ 18 := by
        intro hk_eq
        apply hj_boundary
        rw [hk, hk_eq]
      omega
    exact
      not_dvd_bernoulli_thirtyseven_of_even_ne_thirtytwo h_unique
        hj_index.1 hj_le hj_even hj_ne

/-- **Content-facing constructor for the FLT37 reflection-other discharge.**

This replaces the broad `ReflectionOtherDischarge` package by two explicit
source inputs:

* the boundary component `j = 36` is trivial;
* in the Herbrand range `j ≤ 34`, a non-trivial even component forces
  `37 ∣ B_j`.

Together with the proved small Bernoulli exclusion above, these inputs imply
that every even reflection component other than `32` is trivial. -/
theorem reflectionOtherDischarge_thirtyseven_of_boundary_and_herbrandRibet
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] [Fact (Nat.Prime 37)]
    (id : ClassGroupComponentIdentification 37 K)
    (h_boundary : ¬ id.componentNontrivial 36)
    (h_herbrand :
      ∀ j : ℕ, IsReflectionComponentIndex 37 j → Even j → j ≤ 37 - 3 →
        id.componentNontrivial j → (37 : ℤ) ∣ (bernoulli j).num) :
    ReflectionOtherDischarge 37 K id 32 where
  reflection_other := by
    intro j hj_index hj_even hj_ne h_component
    by_cases hj_boundary : j = 36
    · subst hj_boundary
      exact h_boundary h_component
    · have hj_le : j ≤ 37 - 3 := by
        obtain ⟨k, hk⟩ := hj_even
        have hk_lt : k + k < 37 := by
          simpa [hk] using hj_index.2
        have hk_ne : k ≠ 18 := by
          intro hk_eq
          apply hj_boundary
          rw [hk, hk_eq]
        omega
      exact
        (not_dvd_bernoulli_thirtyseven_of_even_ne_thirtytwo
          UniqueIrregularIndex.thirtyseven_thirtytwo hj_index.1 hj_le
          hj_even hj_ne)
          (h_herbrand j hj_index hj_even hj_le h_component)

/-- **Reflection-other discharge from a boundary-inclusive Herbrand bridge.**

If the Herbrand/Ribet input already covers every even reflection index
`0 < j < 37` (including the boundary index `36`), then the separate boundary
triviality input is unnecessary.  The purely arithmetic exclusion
`not_dvd_bernoulli_thirtyseven_of_even_reflection_ne_thirtytwo` handles both
the interior range and the boundary `B_36` case. -/
theorem reflectionOtherDischarge_thirtyseven_of_herbrandRibet_allEven
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] [Fact (Nat.Prime 37)]
    (id : ClassGroupComponentIdentification 37 K)
    (h_herbrand :
      ∀ j : ℕ, IsReflectionComponentIndex 37 j → Even j →
        id.componentNontrivial j → (37 : ℤ) ∣ (bernoulli j).num) :
    ReflectionOtherDischarge 37 K id 32 where
  reflection_other := by
    intro j hj_index hj_even hj_ne h_component
    exact
      (not_dvd_bernoulli_thirtyseven_of_even_reflection_ne_thirtytwo
        UniqueIrregularIndex.thirtyseven_thirtytwo hj_index hj_even hj_ne)
        (h_herbrand j hj_index hj_even h_component)

/-- **Corollary 8.19 bridge from Thaine plus boundary-inclusive Herbrand/Ribet.**

This is the refined Thaine assembly with the reflection side expressed as one
boundary-inclusive Herbrand/Ribet input instead of a separate `j = 36` boundary
proof and an interior Herbrand-range proof. -/
theorem cor8_19Bridge_thirtyseven_of_thaineAndHerbrandRibet_allEven
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] [Fact (Nat.Prime 37)]
    (id : ClassGroupComponentIdentification 37 K)
    (thaine : ThaineSingleCharDischarge 37 K id 32)
    (h_herbrand :
      ∀ j : ℕ, IsReflectionComponentIndex 37 j → Even j →
        id.componentNontrivial j → (37 : ℤ) ∣ (bernoulli j).num) :
    Cor8_19Bridge 37 K 32 :=
  cor8_19Bridge_of_thaineAndReflection (p := 37) (K := K) id thaine
    (reflectionOtherDischarge_thirtyseven_of_herbrandRibet_allEven id h_herbrand)

end BernoulliRegular

end
