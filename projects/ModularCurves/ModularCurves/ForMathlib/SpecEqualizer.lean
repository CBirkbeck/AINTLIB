/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# `Spec` of an equalizer subalgebra is a cofork

Construction support for `T-G3d-infra` Piece 3 (`.mathlib-quality/decomposition-g3d-piece3.md`): the
affine-local model of the quotient `E/G`. For two `R`-algebra maps `f, g : B →ₐ[R] C`, the equalizer
subalgebra `eq(f, g) = {b : f b = g b}` gives, on `Spec`, a map `Spec B ⟶ Spec (eq f g)` that
**coequalizes** `Spec.map f, Spec.map g : Spec C ⇉ Spec B`. This is the affine coequalizer's cofork
leg; that it is the *colimit* cofork (universal) is the deeper finite-locally-free / Hopf-Galois
content (`Spec B` finite locally free over `Spec (eq f g)`), deferred.

The two ring maps model the two legs `act^#, pr_E^#` of the translation groupoid restricted to a
`G`-stable affine chart; `eq(act^#, pr_E^#) = B^{coG}` are the co-invariants.
-/

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

universe u

variable {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]

/-- The map `Spec B ⟶ Spec (eq f g)` induced by the equalizer inclusion `eq(f, g) ↪ B`. -/
noncomputable def specEqualizerπ (f g : B →ₐ[R] C) :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (AlgHom.equalizer f g)) :=
  Spec.map (CommRingCat.ofHom (AlgHom.equalizer f g).val.toRingHom)

/-- The equalizer inclusion coequalizes `f` and `g` at the ring level: `incl ≫ f = incl ≫ g`. -/
theorem equalizer_val_comp (f g : B →ₐ[R] C) :
    f.toRingHom.comp (AlgHom.equalizer f g).val.toRingHom
      = g.toRingHom.comp (AlgHom.equalizer f g).val.toRingHom :=
  RingHom.ext fun x => x.2

/-- **The affine coequalizer cofork.** `specEqualizerπ f g : Spec B ⟶ Spec (eq f g)` coequalizes the
two maps `Spec.map f, Spec.map g : Spec C ⇉ Spec B`. (Its universality — that `Spec (eq f g)` is the
colimit — is the deferred finite-locally-free content.) -/
theorem specMap_comp_specEqualizerπ (f g : B →ₐ[R] C) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ specEqualizerπ f g
      = Spec.map (CommRingCat.ofHom g.toRingHom) ≫ specEqualizerπ f g := by
  rw [specEqualizerπ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, equalizer_val_comp]

end AlgebraicGeometry
