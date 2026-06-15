/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The nonsingular locus `E_ns` of a Weierstrass curve

For a (possibly singular) Weierstrass curve `E` over a field `F`, the **smooth part**
`E_ns` is the set of nonsingular points, together with the point at infinity.
Silverman defines this set and observes that the group law on `E` restricts to
make `E_ns` an abelian group (Silverman III.2, after Prop. III.2.2).

Mathlib's inductive type `WeierstrassCurve.Affine.Point` is, by construction,
exactly this set: it consists of the point at infinity together with the affine
points satisfying the Nonsingular predicate. Mathlib moreover provides the
abelian group structure on `W.Point` over any field `F` (see
`WeierstrassCurve.Affine.Point.instAddCommGroup`). So this file is a thin
wrapper that exposes the Silverman notation `E_ns := E.nonsingularLocus` and
transfers the group structure.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2
-/

namespace HasseWeil.EC

open WeierstrassCurve

variable {F : Type*} [Field F]

/-- The **nonsingular locus** `E_ns` of a Weierstrass curve `E` over a field `F`.

Mathlib's `E.toAffine.Point` is by construction the disjoint union of the unique
point at infinity and the nonsingular affine points, so the nonsingular locus is
the whole set.

Reference: Silverman III.2 (definition of `E_ns`). -/
def _root_.WeierstrassCurve.nonsingularLocus (E : WeierstrassCurve F) :
    Set E.toAffine.Point :=
  Set.univ

/-- The group law on `E.toAffine.Point` restricts to `E_ns`; equivalently, `E_ns`
inherits an abelian group structure, transferred along the equivalence
`E_ns ≃ E.toAffine.Point`.

Reference: Silverman III.2. -/
noncomputable instance (E : WeierstrassCurve F) :
    AddCommGroup E.nonsingularLocus :=
  (Equiv.Set.univ E.toAffine.Point).addCommGroup

end HasseWeil.EC
