/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import ModularCurves.ForMathlib.AwayCongr

/-!
# Naturality of `Proj.toSpecZero` under `Proj.map`

For a graded ring homomorphism `g : 𝒜 →+*ᵍ ℬ` (with the irrelevant-ideal hypothesis of
`Proj.map`), the structure morphism `Proj.toSpecZero` is natural: `Proj.map g` lies over
`Spec` of the degree-`0` restriction of `g`. In particular, when `g` fixes the degree-`0` part
(e.g. an `𝒜₀`-algebra endomorphism), `Proj.map g` is a morphism over `Spec (𝒜 0)`.

This is the scheme-level input for showing that a `Proj`-endomorphism induced by a graded
coordinate-ring endomorphism which is the identity in degree `0` — such as the negation of a
Weierstrass model — is a morphism over the base.

## Main definitions / results

* `gradedRingHomZero`: the degree-`0` part `𝒜 0 →+* ℬ 0` of a graded ring hom.
* `map_comp_toSpecZero`: `Proj.map g hf ≫ Proj.toSpecZero 𝒜 = Proj.toSpecZero ℬ ≫ Spec.map g₀`.

AINTLIB ModularCurves (T-W7.0b infrastructure); upstream candidate.
-/

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

namespace ModularCurves

universe u

variable {R A S B : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [CommRing B] [Algebra S B]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]
  {ℬ : ℕ → Submodule S B} [GradedAlgebra ℬ]

/-- The degree-`0` part of a graded ring homomorphism, as a ring homomorphism
`𝒜 0 →+* ℬ 0`. -/
def gradedRingHomZero (g : 𝒜 →+*ᵍ ℬ) : 𝒜 0 →+* ℬ 0 where
  toFun a := ⟨g a, g.map_mem a.2⟩
  map_one' := Subtype.ext (by simp [g.map_one])
  map_mul' a b := Subtype.ext (by simp [g.map_mul a b])
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[simp] lemma gradedRingHomZero_coe (g : 𝒜 →+*ᵍ ℬ) (a : 𝒜 0) :
    (gradedRingHomZero g a : B) = g a := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of `Proj.toSpecZero` under `Proj.map`.** For a graded ring hom
`g : 𝒜 →+*ᵍ ℬ`, the induced `Proj.map g` sits over `Spec` of the degree-`0` restriction. -/
theorem map_comp_toSpecZero (g : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    Proj.map g hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom (gradedRingHomZero g)) := by
  refine (Proj.mapAffineOpenCover g hf).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  rw [← Category.assoc, Proj.awayι_comp_map g hf s.1.2 s.2 s.2.2, Category.assoc,
    Proj.awayι_toSpecZero, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun a => awayMap_fromZeroRingHom g s.2 a

end ModularCurves
