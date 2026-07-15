/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.Moduli.WeierstrassAtlas

/-!
# The bundled Weierstrass atlas and the classifying map

**(T-W7 skeleton, lane P5 — `/develop --decompose` 2026-07-07.)** The bundled form of the
`LocallyWeierstrass` predicate — an indexed family of affine opens with Weierstrass curves
and pointed chart isomorphisms — extracted by choice, plus the classifying ring map
`ℤ[a₁,…,a₆][Δ⁻¹] →+* R` of an elliptic Weierstrass curve, exhibiting every chart as a base
change of the universal curve. Construction plumbing for the descent (`GroupLawDescent`).

Sources: reviewer round 1 §Q5 caveat 3 (bundle the atlas, don't construct against the
pointwise predicate); audit items 9/10; the localization universal property for the
classifying map.
-/

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve

universe u

namespace ModularCurves

/-- **(T-W7.1a′)** A bundled Weierstrass atlas for a geometric elliptic curve: indexed
affine opens covering `S`, per-index elliptic Weierstrass curves over the sections, and
pointed chart isomorphisms compatible with the structure morphism and the zero section —
the `Σ`-packaging of the `LocallyWeierstrass` predicate's per-point data. -/
structure WeierstrassAtlasData {S : Scheme.{u}} (G : EllipticCurveGeom S) where
  /-- The index type. -/
  ι : Type u
  /-- The affine opens of the atlas. -/
  U : ι → S.affineOpens
  /-- The opens cover `S`. -/
  covers : ∀ s : S, ∃ i, s ∈ (U i).1
  /-- The chart Weierstrass curves. -/
  W : ∀ i, WeierstrassCurve Γ(S, (U i).1)
  /-- Each chart curve is elliptic. -/
  elliptic : ∀ i, (W i).IsElliptic
  /-- The pointed chart isomorphisms. -/
  e : ∀ i, pullback G.π (U i).1.ι ≅ projModel (W i)
  /-- Chart isomorphisms respect the structure morphisms. -/
  compat_π : ∀ i, (e i).hom ≫ projModelπ (W i) =
    pullback.snd G.π (U i).1.ι ≫ (U i).2.isoSpec.hom
  /-- Chart isomorphisms respect the zero sections. -/
  compat_zero : ∀ i, ((U i).2.isoSpec.inv ≫ pullback.lift ((U i).1.ι ≫ G.zero) (𝟙 _)
      (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp])) ≫ (e i).hom =
    projModelZero (W i)

/-- **(T-W7.1a′-extract)** Every geometric elliptic curve admits a bundled atlas (choice from
the `localModel` field; index the atlas by the points of `S`). -/
noncomputable def EllipticCurveGeom.atlas {S : Scheme.{u}} (G : EllipticCurveGeom S) :
    WeierstrassAtlasData G where
  ι := S
  U s := (G.localModel s).choose
  covers s := ⟨s, (G.localModel s).choose_spec.choose⟩
  W s := (G.localModel s).choose_spec.choose_spec.choose
  elliptic s := (G.localModel s).choose_spec.choose_spec.choose_spec.1
  e s := (G.localModel s).choose_spec.choose_spec.choose_spec.2.choose
  compat_π s := (G.localModel s).choose_spec.choose_spec.choose_spec.2.choose_spec.1
  compat_zero s := (G.localModel s).choose_spec.choose_spec.choose_spec.2.choose_spec.2

/-- **(T-W7.1a-i, coefficients)** The coefficient ring map `MvPolynomial (Fin 5) ℤ →+* R` of a
Weierstrass curve `W` over `R`, sending the `i`-th coordinate `Xᵢ` to the coefficient `aᵢ`. This
is the pre-localization half of the classifying map. -/
noncomputable def classifyCoeffHom {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    MvPolynomial (Fin 5) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

/-- Specialising the universal Weierstrass curve along `classifyCoeffHom W` (`Xᵢ ↦ aᵢ`) recovers
`W` — the defining property of the coefficient map. -/
theorem universalWeierstrass_map_classifyCoeffHom {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) : universalWeierstrass.map (classifyCoeffHom W) = W := by
  ext <;>
    simp [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, universalWeierstrass, classifyCoeffHom,
      MvPolynomial.eval₂Hom_X']

/-- **(T-W7.1a-i)** The classifying ring map of an elliptic Weierstrass curve: the universal
coefficient ring maps to `R` by `Xᵢ ↦ aᵢ`, well-defined on the localization because `Δ` maps
to a unit. Source: `Localization.Away` universal property (`IsLocalization.Away.lift`). -/
noncomputable def classifyRingHom {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    [W.IsElliptic] : WeierstrassAtlasRing →+* R :=
  IsLocalization.Away.lift (g := classifyCoeffHom W) universalWeierstrass.Δ <| by
    have hΔ : classifyCoeffHom W universalWeierstrass.Δ = W.Δ := by
      rw [← map_Δ, universalWeierstrass_map_classifyCoeffHom]
    rw [hΔ]; exact W.isUnit_Δ

/-- **(T-W7.1a-ii)** The classifying map classifies: pushing the universal curve along it
recovers `W`. With `isPullback_projModelBaseChange` this exhibits `projModel W` as the base
change of the universal curve `E_U` along `Spec.map (classifyRingHom W)` — every chart of
every locally-Weierstrass family is a base change of `E_U`. -/
theorem universalWeierstrassLoc_map_classifyRingHom {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] :
    universalWeierstrassLoc.map (classifyRingHom W) = W := by
  have hcomp : (classifyRingHom W).comp
      (algebraMap (MvPolynomial (Fin 5) ℤ) WeierstrassAtlasRing) = classifyCoeffHom W := by
    simp only [classifyRingHom, IsLocalization.Away.lift_comp]
  rw [universalWeierstrassLoc, map_map, hcomp, universalWeierstrass_map_classifyCoeffHom]

end ModularCurves
