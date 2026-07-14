/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict

/-!
# A point from a one-point scheme factors through a member of a supremum of opens

`exists_lift_iSup_of_unique`: a morphism `g : Y ⟶ (⨆ i, U i).toScheme` out of a scheme `Y`
with a single point (`[Unique Y]`) factors through one of the opens `U i`, via the inclusion
`X.homOfLE (le_iSup U i)`. The unique point of `Y` lies in some member of the cover, and the
member inclusion is an open immersion, so `IsOpenImmersion.lift` produces the factorisation.

Generic scheme statement (no elliptic-curve content); the `Spec K` case (`K` a field, whose
spectrum has a unique point) is the motivating application. Extracted from
`ModularCurves/EllipticCurve/AdditionSpecPoints.lean` as a ForMathlib candidate.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism from a one-point scheme `Y` (`[Unique Y]`) into an `iSup`-of-opens subscheme
factors through one of the members: the unique point of `Y` lies in some member, and the
member inclusion is an open immersion. -/
theorem exists_lift_iSup_of_unique {X Y : Scheme.{u}} [Unique Y] {ι : Type*}
    (U : ι → X.Opens) (g : Y ⟶ (⨆ i, U i).toScheme) :
    ∃ (i : ι) (h : Y ⟶ (U i).toScheme),
      h ≫ X.homOfLE (le_iSup U i) = g := by
  have hmem : (⨆ i, U i).ι.base (g.base default) ∈ (⨆ i, U i : X.Opens) := by
    have h1 : (⨆ i, U i).ι.base (g.base default) ∈ Set.range (⨆ i, U i).ι.base := ⟨_, rfl⟩
    rwa [Scheme.Opens.range_ι] at h1
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨i, IsOpenImmersion.lift (X.homOfLE (le_iSup U i)) g ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rw [Set.range_unique (f := g.base)]
  refine Set.singleton_subset_iff.mpr ?_
  have hor : (X.homOfLE (le_iSup U i)).opensRange =
      (⨆ j, U j).ι ⁻¹ᵁ (U i) := Scheme.opensRange_homOfLE _
  have : g.base default ∈ (X.homOfLE (le_iSup U i)).opensRange := by
    rw [hor]
    exact hi
  exact this

end AlgebraicGeometry
