/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.RepresentationTheory.Coinvariants

/-!
# Finiteness of coinvariants from a finite generating set of orbits

If a `k`-linear `G`-representation `ρ : Representation k G V` is such that the `G`-translates of a
*finite* set generate `V` over `k`, then its coinvariants `Representation.Coinvariants ρ` form a
finite `k`-module.

This is the elementary "orbit-collapse" finiteness step: the quotient map
`Representation.Coinvariants.mk` is surjective and identifies `ρ g v` with `v`
(`Representation.Coinvariants.mk_self_apply`), so the image of the (possibly infinite) orbit set
collapses onto the image of the finite generating set, which therefore spans the coinvariants.

## Main results

* `Representation.Coinvariants.finite_of_span_orbit_top`: if the span of the orbit of a finite set
  is all of `V`, then `Representation.Coinvariants ρ` is a finite `k`-module.
-/

namespace Representation.Coinvariants

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

/-- The image under the coinvariants quotient map of the orbit of a finite set `S` coincides with
the image of `S` itself, since `mk (ρ g s) = mk s`. -/
private lemma image_orbit_eq (ρ : Representation k G V) (S : Finset V) :
    (mk ρ) '' {v : V | ∃ g : G, ∃ s ∈ S, ρ g s = v} = (mk ρ) '' (↑S : Set V) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨g, s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, (mk_self_apply ρ g s).symm⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨ρ 1 s, ⟨1, s, hs, rfl⟩, mk_self_apply ρ 1 s⟩

/-- If the `G`-translates of a finite set `S` generate `V` over `k`, then the coinvariants
`Representation.Coinvariants ρ` form a finite `k`-module. -/
theorem finite_of_span_orbit_top
    (ρ : Representation k G V) (S : Finset V)
    (hS : Submodule.span k {v : V | ∃ g : G, ∃ s ∈ S, ρ g s = v} = ⊤) :
    Module.Finite k (Representation.Coinvariants ρ) := by
  rw [Module.finite_def]
  have h1 : (⊤ : Submodule k (Representation.Coinvariants ρ)) = Submodule.map (mk ρ) ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr (mk_surjective ρ)]
  rw [h1, ← hS, Submodule.map_span, image_orbit_eq]
  exact Submodule.fg_span (S.finite_toSet.image (mk ρ))

end Representation.Coinvariants
