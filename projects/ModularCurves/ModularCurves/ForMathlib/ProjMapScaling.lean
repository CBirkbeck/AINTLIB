/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# `Proj.map` of a degreewise rescaling is the identity

If a graded ring endomorphism `ρ : 𝒜 →+*ᵍ 𝒜` acts on each homogeneous piece by multiplication
by a fixed power of a unit — `ρ a = uᵈ · a` for `a ∈ 𝒜 d` — then the induced morphism
`Proj.map ρ : Proj 𝒜 ⟶ Proj 𝒜` is the identity. Geometrically, rescaling the homogeneous
coordinates by a unit does not move any point of the projective spectrum.

The whole mathematical content is a single `ring` identity on the affine charts: on a section
`a'/tᵏ` of the chart `D₊(t)` (with `t ∈ 𝒜 d`), `Away.map ρ t` produces `ρa'/(ρt)ᵏ =
(uᵏᵈ a')/(uᵏᵈ tᵏ)`, and the `u`-powers cancel because numerator and denominator share the
total degree `k·d`.

## Main results

* `Proj.map_degScaling_eq_id`: `ρ a = uᵈ · a` ⟹ `Proj.map ρ = 𝟙`.
* `Proj.map_negScaling_eq_id`: the `u = -1` special case, `ρ a = (-1)ᵈ · a` ⟹ `Proj.map ρ = 𝟙`.

The `-1` case is the one used to identify the point at infinity as a fixed point of negation on
a projective Weierstrass model (T-W7.0b, `negModelHom_zero`).

AINTLIB ModularCurves (T-W7.0b infrastructure); upstream candidate.
-/

universe u

open CategoryTheory AlgebraicGeometry HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry.Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

section rescale

variable (ρ : 𝒜 →+*ᵍ 𝒜) (u : Aˣ)
  (hscale : ∀ (d : ℕ) {a : A}, a ∈ 𝒜 d → ρ a = (u : A) ^ d * a)

include hscale

/-- Γ-level step: `Away.map ρ t` composed with `awayToSection` at `ρ t` equals `awayToSection`
at `t` composed with the restriction to `D₊(ρ t) ⊆ D₊(t)`. -/
lemma map_awayToSection_rescale {d : ℕ} {t : A} (ht : t ∈ 𝒜 d)
    (hle : Proj.basicOpen 𝒜 (ρ t) ≤ Proj.basicOpen 𝒜 t) :
    CommRingCat.ofHom (Away.map ρ t) ≫ awayToSection 𝒜 (ρ t) =
      awayToSection 𝒜 t ≫ (Proj 𝒜).presheaf.map (homOfLE hle).op := by
  ext a
  apply Subtype.ext
  ext ⟨pt, hpt⟩
  obtain ⟨k, a', ha, rfl⟩ := Away.mk_surjective 𝒜 ht a
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply, ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [Away.map_mk, Away.val_mk, Away.val_mk, Localization.mk_eq_mk', Localization.mk_eq_mk',
    IsLocalization.map_mk', IsLocalization.map_mk', ← Localization.mk_eq_mk',
    ← Localization.mk_eq_mk',
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, RingHom.id_apply]
  rw [hscale d ht, hscale (k • d) ha, mul_pow, smul_eq_mul]
  ring

/-- Spec-level step underlying `SpecMap_map_awayι_rescale`. -/
@[reassoc]
lemma basicOpenToSpec_SpecMap_map_rescale {d : ℕ} {t : A} (ht : t ∈ 𝒜 d)
    (hle : Proj.basicOpen 𝒜 (ρ t) ≤ Proj.basicOpen 𝒜 t) :
    basicOpenToSpec 𝒜 (ρ t) ≫ Spec.map (CommRingCat.ofHom (Away.map ρ t)) =
      (Proj 𝒜).homOfLE hle ≫ basicOpenToSpec 𝒜 t := by
  rw [basicOpenToSpec, Category.assoc, ← Spec.map_comp,
    map_awayToSection_rescale ρ u hscale ht hle, Spec.map_comp,
    Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]
  rfl

/-- On the chart `D₊(t)`, precomposing the inclusion `awayι 𝒜 t` by `Spec.map (Away.map ρ t)`
lands on the inclusion `awayι 𝒜 (ρ t)` — the rescaled chart is the same chart. -/
lemma SpecMap_map_awayι_rescale {d : ℕ} {t : A} (ht : t ∈ 𝒜 d) (hi : 0 < d)
    (hle : Proj.basicOpen 𝒜 (ρ t) ≤ Proj.basicOpen 𝒜 t) :
    Spec.map (CommRingCat.ofHom (Away.map ρ t)) ≫ awayι 𝒜 t ht hi =
      awayι 𝒜 (ρ t) (GradedRingHom.map_mem ρ ht) hi := by
  rw [awayι, awayι, Iso.eq_inv_comp, basicOpenIsoSpec_hom,
    basicOpenToSpec_SpecMap_map_rescale_assoc ρ u hscale ht hle,
    ← basicOpenIsoSpec_hom _ _ ht hi, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]

set_option backward.isDefEq.respectTransparency false in
/-- **Rescaling by a unit induces the identity on `Proj`.** If a graded endomorphism `ρ` acts
degreewise as `ρ a = uᵈ · a` for a unit `u`, then `Proj.map ρ = 𝟙`. -/
theorem map_degScaling_eq_id
    (hρ : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant 𝒜).map ρ) :
    Proj.map ρ hρ = 𝟙 (Proj 𝒜) := by
  refine (mapAffineOpenCover ρ hρ).openCover.hom_ext _ _ fun s ↦ ?_
  have hle : Proj.basicOpen 𝒜 (ρ (s.2 : A)) ≤ Proj.basicOpen 𝒜 (s.2 : A) :=
    basicOpen_mono 𝒜 _ _ ⟨(u : A) ^ (s.1 : ℕ), by rw [hscale _ s.2.2, mul_comm]⟩
  simp only [Scheme.AffineOpenCover.openCover_f, mapAffineOpenCover_f]
  rw [awayι_comp_map ρ hρ s.1.2 (s.2 : A) s.2.2, Category.comp_id]
  exact SpecMap_map_awayι_rescale ρ u hscale s.2.2 s.1.2 hle

end rescale

/-- **The `-1`-rescaling induces the identity on `Proj`.** If `ρ a = (-1)ᵈ · a` for `a ∈ 𝒜 d`,
then `Proj.map ρ = 𝟙`. This is the "negate all homogeneous coordinates" automorphism, which fixes
every point projectively. -/
theorem map_negScaling_eq_id (ρ : 𝒜 →+*ᵍ 𝒜)
    (hρ : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant 𝒜).map ρ)
    (hscale : ∀ (d : ℕ) {a : A}, a ∈ 𝒜 d → ρ a = (-1 : A) ^ d * a) :
    Proj.map ρ hρ = 𝟙 (Proj 𝒜) :=
  map_degScaling_eq_id ρ (-1) (fun d _ ha => by rw [hscale d ha]; simp) hρ

end AlgebraicGeometry.Proj
