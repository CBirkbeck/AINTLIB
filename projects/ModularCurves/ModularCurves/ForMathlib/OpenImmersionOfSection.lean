/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Open-immersion criterion via an image bound and a section (YFULL route γ, [YF-OI-CRIT])

A monomorphism `ι : Z ⟶ Y` (e.g. a closed immersion) whose set-theoretic image lands in
an open `U ⊆ Y` and which admits a section `s : U ⟶ Z` over that open
(`s ≫ ι = U.ι`) is an **open immersion** — indeed it is an isomorphism onto `U`.

This is the assembly shape of the `Y(N)` clopen leaf `isOpenImmersion_levelSpaceΓι`
(route γ): the full-level closed immersion `levelSpaceΓι` has image inside the clopen
"classifier-is-an-isomorphism" locus `U` (from `isClopen_finrank_eq`,
`FiniteLocallyFreeIsoLocus`), and over `U` the tautological full-level structure gives a
section back into `levelSpaceΓ` (`levelSpaceΓ_spec.mpr`). The two facts together upgrade
the closed immersion to an open immersion. A closed immersion with clopen image is *not*
automatically an open immersion (a non-reduced thickening of a clopen point is a
counterexample); the section is exactly the extra datum that rules this out.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- **[YF-OI-CRIT]** A monomorphism whose image lies in an open `U` and which has a
section over `U` is an open immersion (in fact an isomorphism onto `U`). -/
theorem isOpenImmersion_of_range_subset_of_section {Z Y : Scheme.{u}} (ι : Z ⟶ Y) [Mono ι]
    (U : Y.Opens) (hrange : Set.range ι.base ⊆ (U : Set Y))
    (s : (U : Scheme.{u}) ⟶ Z) (hs : s ≫ ι = U.ι) : IsOpenImmersion ι := by
  have hrange' : Set.range ι.base ⊆ Set.range U.ι.base := by
    rwa [Scheme.Opens.range_ι]
  -- the induced factorisation of `ι` through `U`
  let ι' : Z ⟶ (U : Scheme.{u}) := IsOpenImmersion.lift U.ι ι hrange'
  have hι' : ι' ≫ U.ι = ι := IsOpenImmersion.lift_fac _ _ _
  -- `s` and `ι'` are mutually inverse
  have hsι' : s ≫ ι' = 𝟙 (U : Scheme.{u}) := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, hι', hs, Category.id_comp]
  have hι's : ι' ≫ s = 𝟙 Z := by
    apply (cancel_mono ι).mp
    rw [Category.assoc, hs, hι', Category.id_comp]
  haveI : IsIso ι' := ⟨⟨s, hι's, hsι'⟩⟩
  rw [← hι']
  infer_instance

end AlgebraicGeometry
