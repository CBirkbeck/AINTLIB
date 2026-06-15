/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Bounded
import «Adic spaces».Presheaf

/-!
# Uniform and Stably Uniform Huber Pairs

We define **uniform** and **stably uniform** Huber pairs following §7 of
[Wedhorn, *Adic Spaces*].

## Main definitions

* `TopologicalRing.IsUniform A` : A topological ring `A` is uniform if the set `A°` of
  power-bounded elements is bounded (Definition 7.36 of Wedhorn).
* `TopologicalRing.IsStablyUniform A` : A Huber pair `(A, A⁺)` is stably uniform if for
  every rational localization `(A, A⁺) → (B, B⁺)`, the localization ring `B` (with the
  localization topology) is uniform (Definition 7.37 of Wedhorn).

## Main results

* `TopologicalRing.IsUniform.discrete` : Every discrete topological ring is uniform.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definitions 7.36, 7.37
-/

open TopologicalRing ValuationSpectrum

namespace TopologicalRing

universe u

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-! ### Uniform Huber pairs -/

/-- A topological ring `A` is **uniform** if the set `A°` of power-bounded elements is
bounded (Definition 7.36 of Wedhorn). -/
class IsUniform : Prop where
  /-- The set `A°` of power-bounded elements is bounded. -/
  isBounded_powerBounded : IsBounded (powerBoundedSubring A)

/-- A Huber pair `(A, A⁺)` is **stably uniform** if for every rational localization
`(A, A⁺) → (B, B⁺)`, the localization ring `B` (with the localization topology) is
uniform (Definition 7.37 of Wedhorn). -/
class IsStablyUniform [PlusSubring A] [IsHuberRing A] : Prop where
  /-- The presheaf value (= completion of the localization) is uniform for every
  rational localization datum `D`. -/
  presheafValue_isUniform :
    ∀ (D : RationalLocData A), IsBounded (powerBoundedSubring (presheafValue D))

/-! ### Discrete rings are uniform -/

/-- Every discrete topological ring is uniform (Definition 7.36 of Wedhorn).

In a discrete ring, every subset is bounded: for any neighbourhood `U` of `0`,
`U` itself witnesses that `S * U ⊆ U` since `0 ∈ S * U` and `U = Set.univ` in
the discrete topology. -/
instance IsUniform.discrete {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] : IsUniform A where
  isBounded_powerBounded := by
    intro U hU
    refine ⟨{0}, isOpen_discrete _ |>.mem_nhds rfl, ?_⟩
    rintro _ ⟨a, _, b, (hb : b = 0), rfl⟩
    simp only [hb, mul_zero]; exact mem_of_mem_nhds hU

end TopologicalRing
