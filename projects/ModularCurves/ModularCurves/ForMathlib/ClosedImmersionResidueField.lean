/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The residue-field map of a closed immersion is an isomorphism

For a closed immersion `f : X ⟶ Y`, the residue field at a point of `X` equals the residue field
at its image (`κ(f x) ≅ κ(x)`): the induced `residueFieldMap` is injective (a field homomorphism)
and surjective (closed immersions are surjective on stalks, and the residue maps are surjective).
This is the enabler for factoring `fromSpecResidueField` through a closed immersion, used in the
Y(N) `[YF-⊆]` distinctness argument.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry

instance isIso_residueFieldMap_of_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (x : X) : IsIso (f.residueFieldMap x) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  have hnat : ⇑(f.residueFieldMap x) ∘ ⇑(Y.residue (f.base x))
      = ⇑(X.residue x) ∘ ⇑(f.stalkMap x) := by
    have h := congrArg (fun m => ⇑(CommRingCat.Hom.hom m)) (Scheme.residue_residueFieldMap f x)
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp] using h
  have hs := (X.residue_surjective x).comp (f.stalkMap_surjective x)
  rw [← hnat] at hs
  exact hs.of_comp

end AlgebraicGeometry
