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
  sorry

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
