/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.MuNBaseChange

/-!
# The torsion algebra under base change of the field (WP-D3c-2c)

`muNCarrierBaseChange` (`WeilPairing/MuNBaseChange.lean`) transported the `μ_N` side of the
field-change comparison by reducing it to the explicit `AdjoinRoot` model. `E[N]` has no such
model, so its transport has to come from the cartesian square itself
(`torsion_baseChange_isPullback`, `EllipticCurve/TorsionFibre.lean`).

This file supplies the affineness that makes that possible: the torsion scheme of an elliptic
curve over an affine base is affine, so `Scheme.isoSpec` applies to all three corners of the
square and `AlgebraicGeometry.pullbackSpecIso` can be read off.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-- **(WP-D3c-2c)** The `N`-torsion of an elliptic curve over an affine base is affine: its
structure morphism is finite (`torsionπ_isFinite`), hence affine. -/
instance isAffine_torsion [IsAffine S] : IsAffine (E.torsion N) :=
  haveI : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
  isAffine_of_isAffineHom (E.torsionπ N)

/-- **(WP-D3c-2c)** …and so is the torsion of a base change along a morphism from an affine
scheme, which is the other corner of `torsion_baseChange_isPullback`. -/
instance isAffine_torsion_baseChange {T : Scheme.{u}} [IsAffine T] (g : T ⟶ S) :
    IsAffine ((E.baseChange g).torsion N) :=
  haveI : IsFinite ((E.baseChange g).torsionπ N) := (E.baseChange g).torsionπ_isFinite N
  isAffine_of_isAffineHom ((E.baseChange g).torsionπ N)

end EllipticCurve

end ModularCurves
