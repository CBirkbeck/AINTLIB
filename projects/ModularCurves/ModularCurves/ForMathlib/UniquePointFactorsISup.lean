/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict

/-!
# A point from a one-point scheme factors through a member of a supremum of opens

A morphism from a one-point scheme to a supremum of open subschemes factors through one of
the members.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism from a one-point scheme to a supremum of open subschemes factors through one of
the members. -/
theorem exists_lift_iSup_of_unique {X Y : Scheme.{u}} [Unique Y] {ι : Type*} (U : ι → X.Opens)
    (g : Y ⟶ (⨆ i, U i).toScheme) :
    ∃ (i : ι) (h : Y ⟶ (U i).toScheme), h ≫ X.homOfLE (le_iSup U i) = g := by
  have hmem : (⨆ i, U i).ι.base (g.base default) ∈ (⨆ i, U i : X.Opens) := by
    change (⨆ i, U i).ι.base (g.base default) ∈ ((⨆ i, U i : X.Opens) : Set X)
    rw [← Scheme.Opens.range_ι]
    exact Set.mem_range_self _
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨i, IsOpenImmersion.lift (X.homOfLE (le_iSup U i)) g ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  simpa [Set.range_unique, ← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE] using hi

end AlgebraicGeometry
