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

/-- For a positive-degree homogeneous element, the map on global sections induced by
`Proj.awayι` is restriction to the basic open followed by the inverse of the canonical
homogeneous-localization presentation. -/
theorem Proj_awayι_appTop_ΓSpecIso (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {m : ℕ} (f : A) (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj.awayι 𝒜 f f_deg hm).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom =
    (Proj 𝒜).presheaf.map (homOfLE le_top).op ≫
      (Proj.basicOpenIsoAway 𝒜 f f_deg hm).inv := by
  rw [Iso.eq_comp_inv, Category.assoc]
  have hσ : (Proj.basicOpenIsoAway 𝒜 f f_deg hm).hom = Proj.awayToSection 𝒜 f := rfl
  rw [hσ]
  have hhomTop : (Proj.basicOpenToSpec 𝒜 f).appTop ≫
      (Proj.basicOpen 𝒜 f).topIso.hom =
      (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection 𝒜 f := by
    rw [show (Proj.basicOpenToSpec 𝒜 f).appTop =
      (Proj.basicOpenToSpec 𝒜 f).app ⊤ from rfl]
    rw [Proj.basicOpenToSpec_app_top, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [← hhomTop, ← Proj.basicOpenIsoSpec_inv_ι 𝒜 f f_deg hm,
    Scheme.Hom.comp_appTop, Category.assoc]
  rw [show Proj.basicOpenToSpec 𝒜 f =
    (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).hom from rfl]
  rw [← Category.assoc ((Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv.appTop)]
  rw [show (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv.appTop ≫
      (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).hom.appTop = 𝟙 _ from by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    simp]
  rw [Category.id_comp, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  refine ((Proj 𝒜).presheaf.map_comp _ _).symm.trans
    (congrArg ((Proj 𝒜).presheaf.map) ?_)
  exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)

/-- The composite from a coefficient ring to sections on a positive projective basic open,
then to its degree-zero homogeneous localization, is the canonical degree-zero map. -/
theorem Proj_structure_section_square (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (c : S →+* 𝒜 0) {m : ℕ} (f : A) (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
      (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom c)).appTop ≫
      (Proj 𝒜).presheaf.map (homOfLE le_top).op ≫
      (Proj.basicOpenIsoAway 𝒜 f f_deg hm).inv =
    CommRingCat.ofHom
      ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp c) := by
  have hbridge := Proj_awayι_appTop_ΓSpecIso 𝒜 f f_deg hm
  have hscheme :
      Proj.awayι 𝒜 f f_deg hm ≫
          (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom c)) =
        Spec.map (CommRingCat.ofHom
          ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp c)) := by
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
  have hΓ := congrArg Scheme.Hom.appTop hscheme
  rw [Scheme.Hom.comp_appTop] at hΓ
  calc
    (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
          (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom c)).appTop ≫
          (Proj 𝒜).presheaf.map (homOfLE le_top).op ≫
          (Proj.basicOpenIsoAway 𝒜 f f_deg hm).inv =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
          ((Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom c)).appTop ≫
            (Proj.awayι 𝒜 f f_deg hm).appTop) ≫
          (Scheme.ΓSpecIso
            (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom := by
      rw [← hbridge]
      simp only [Category.assoc]
    _ = (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
          (Spec.map (CommRingCat.ofHom
            ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp c))).appTop ≫
          (Scheme.ΓSpecIso
            (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom := by
      rw [hΓ]
    _ = _ := by
      rw [Scheme.ΓSpecIso_naturality, ← Category.assoc, Iso.inv_hom_id,
        Category.id_comp]

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
