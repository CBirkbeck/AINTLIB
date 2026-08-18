/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.SelfField

/-!
# U4 — vanishing over the universal torsion base

The universal `N`-torsion base `X_N := (modelEllipticCurve 𝕌).torsion N` is affine
(`torsionπ` is finite over the affine atlas), its section ring is `ℤ`-flat (the torsion
is flat over the `ℤ`-flat atlas ring), so sections inject into the `N`-inverted locus,
which is reduced; the diagonal pairing value is `1` at every residue field there by the
field leaf (`weilPairingEval_self_of_field'`), and a reduced ring embeds into the product
of its residue fields.

This file develops the pieces in order:
* [U4a] `X_N` is affine;
* [U4b] the `ℤ`-flatness of its ring;
* [U4c] `N` is a nonzerodivisor there;
* [U4d] the `N`-inverted ring is reduced;
* [U4e] pointwise vanishing at residue fields;
* [U4f] the conclusion.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace ModularCurves

namespace EllipticCurve

/-- **([U4a])** The universal `N`-torsion base is affine: `torsionπ` is finite, hence
affine, over the affine atlas `Spec 𝕌`. -/
instance isAffine_torsion_universal (N : ℕ) [NeZero N] :
    IsAffine ((modelEllipticCurve universalWeierstrassLocU.{u}).torsion N) := by
  haveI : IsFinite ((modelEllipticCurve universalWeierstrassLocU.{u}).torsionπ N) :=
    (modelEllipticCurve universalWeierstrassLocU.{u}).torsionπ_isFinite N
  exact isAffine_of_isAffineHom
    ((modelEllipticCurve universalWeierstrassLocU.{u}).torsionπ N)

/-- The section ring of the universal `N`-torsion base. -/
noncomputable abbrev universalTorsionRing (N : ℕ) : CommRingCat.{u} :=
  Γ((modelEllipticCurve universalWeierstrassLocU.{u}).torsion N, ⊤)

/-- **([U4b], ring level)** The section ring is flat over the atlas ring: `torsionπ` is
flat and both schemes are affine. -/
theorem flat_universalTorsionRing (N : ℕ) [NeZero N] :
    RingHom.Flat (((modelEllipticCurve universalWeierstrassLocU.{u}).torsionπ N).appTop).hom := by
  haveI : Flat ((modelEllipticCurve universalWeierstrassLocU.{u}).torsionπ N) :=
    (modelEllipticCurve universalWeierstrassLocU.{u}).torsionπ_flat N
  exact (HasRingHomProperty.iff_of_isAffine (P := @Flat) (Q := RingHom.Flat)).mp
    inferInstance

end EllipticCurve

end ModularCurves
