/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafNeighborhoodHOne
import ModularCurves.EllipticCurve.PoleSheafWeierstrassComparison
import ModularCurves.Moduli.EngineDescent

/-!
# Fibrewise elliptic families are locally Weierstrass (FLW-6)

The two final comparison theorems of the fibrewise-elliptic versus locally-Weierstrass
campaign (codex handover 2026-07-29 §3):

* `FibrewiseElliptic.locallyWeierstrass` — a smooth proper fibrewise elliptic family is
  Zariski-locally on the base a projective Weierstrass model;
* `locallyWeierstrass_iff_abstractConditions` — the definitional comparison.

Assembly: per point, the Cartier producer
(`exists_affineBaseChange_sectionCartierGenerator`) gives an affine `V ∋ s` with a
principal zero-section ideal on the `V`-restricted family; `[FLW-2b]`'s
`exists_mem_basicOpen_pointedIso_poleOneBasis` gives a basic open of `V` where the direct
stage family carries `H¹(𝒪([0])) = 0` and a normalized rank-one first-pole basis; the
Cartier data restricts to the basic open and crosses the pointed identification; the
`n = 1` comparison `sectionPoleSheafPower_locallyWeierstrass_of_CartierGenerator` then
produces the Weierstrass presentation, which `LocallyWeierstrass.of_iso_over` carries back
to the restricted family and pullback-composition carries up to the original base.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace ModularCurves

/-- **(chart lift)** A Weierstrass chart of the restriction of a pointed family to an
affine open lifts to a Weierstrass chart of the family itself. Tools per the board
`[FLW-6] chart-lift factorization`: `Scheme.Hom.isoImage` (+ `isoImage_hom_ι`),
`Scheme.Hom.appIso`, `IsAffineOpen.image_of_isOpenImmersion`, `WeierstrassCurve.map`
(elliptic instance), `projModelBaseChangeOf` + `isPullback_projModelBaseChangeOf`,
`isoSpec_appLE_bridge`, and the `IsPullback.of_iso`/`isoPullback` choreography of
`exists_pointedIso_direct_pullback`. -/
private theorem lw_point_of_baseChange_affineOpen
    {E S : Scheme.{u}} {π : E ⟶ S} {z : S ⟶ E} {hz : z ≫ π = 𝟙 S}
    (W : S.affineOpens) {s : S} (hs : s ∈ W.1)
    (hLW : LocallyWeierstrass (pullback.snd π W.1.ι)
      (sectionBaseChange z hz W.1.ι) (sectionBaseChange_snd z hz W.1.ι)) :
    ∃ (U : S.affineOpens) (_ : s ∈ U.1) (Wc : WeierstrassCurve Γ(S, U.1)),
      Wc.IsElliptic ∧
      ∃ e : pullback π U.1.ι ≅ projModel Wc,
        e.hom ≫ projModelπ Wc = pullback.snd π U.1.ι ≫ U.2.isoSpec.hom ∧
        (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ z) (𝟙 _)
            (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp])) ≫ e.hom =
          projModelZero Wc := by
  sorry

/-- **(FLW-6, affine case)** A smooth proper fibrewise elliptic family over an affine
base is locally Weierstrass. -/
theorem FibrewiseElliptic.locallyWeierstrass_of_isAffine
    {E S : Scheme.{u}} {π : E ⟶ S} {z : S ⟶ E} {hz : z ≫ π = 𝟙 S} [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π) (hproper : IsProper π)
    (h : FibrewiseElliptic π z hz) :
    LocallyWeierstrass π z hz := by
  sorry

/-- **(FLW final 1, handover §3)** A smooth proper fibrewise elliptic family is locally
Weierstrass. -/
theorem FibrewiseElliptic.locallyWeierstrass
    {E S : Scheme.{u}} {π : E ⟶ S} {z : S ⟶ E} {hz : z ≫ π = 𝟙 S}
    (hsm : SmoothOfRelativeDimension 1 π) (hproper : IsProper π)
    (h : FibrewiseElliptic π z hz) :
    LocallyWeierstrass π z hz := by
  intro s
  -- an affine open of the base around the point
  obtain ⟨_, ⟨V, hVaff, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s)
      (isOpen_univ (X := S))
  let Vaff : S.affineOpens := ⟨V, hVaff⟩
  haveI : IsAffine Vaff.1.toScheme := hVaff
  haveI : IsProper (pullback.snd π Vaff.1.ι) :=
    MorphismProperty.pullback_snd _ _ hproper
  have hsmV : SmoothOfRelativeDimension 1 (pullback.snd π Vaff.1.ι) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback π Vaff.1.ι) hsm
  have hV : FibrewiseElliptic (pullback.snd π Vaff.1.ι)
      (sectionBaseChange z hz Vaff.1.ι)
      (sectionBaseChange_snd z hz Vaff.1.ι) :=
    h.baseChange Vaff.1.ι
  exact lw_point_of_baseChange_affineOpen Vaff hsV
    (FibrewiseElliptic.locallyWeierstrass_of_isAffine hsmV inferInstance hV)

/-- **(FLW final 2, handover §3)** A pointed family is locally Weierstrass exactly when
it is smooth of relative dimension one, proper, and fibrewise elliptic. -/
theorem locallyWeierstrass_iff_abstractConditions
    {E S : Scheme.{u}} {π : E ⟶ S} {z : S ⟶ E} {hz : z ≫ π = 𝟙 S} :
    LocallyWeierstrass π z hz ↔
      SmoothOfRelativeDimension 1 π ∧ IsProper π ∧ FibrewiseElliptic π z hz := by
  constructor
  · intro hLW
    exact ⟨RouteA.smoothOfRelativeDimension_of_locallyWeierstrass hLW,
      RouteA.isProper_of_locallyWeierstrass hLW, hLW.fibrewiseElliptic⟩
  · rintro ⟨hsm, hproper, h⟩
    exact FibrewiseElliptic.locallyWeierstrass hsm hproper h

end ModularCurves
