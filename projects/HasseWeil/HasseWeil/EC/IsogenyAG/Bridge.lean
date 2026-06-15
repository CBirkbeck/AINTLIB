/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG.GroupHom

/-!
# `EC.Isogeny → HasseWeil.Isogeny` (Silverman III.4.8)

Now that the group-homomorphism property `EC.Isogeny.addHomProperty` (Silverman
III.4.8) is proven (`HasseWeil/EC/IsogenyAG/GroupHom.lean`), an `EC.Isogeny`
(carrying only a function-field pullback + basepoint witness) can be promoted to
a `HasseWeil.Isogeny` (= `Basic.Isogeny`, which carries the pullback **and** the
group homomorphism on points as bundled data). This bridge lets the
kernel/Galois/fixed-field machinery — all phrased for `Basic.Isogeny` — name
`ker φ`, `φ.degree`, and the translation covariance for an `EC.Isogeny φ`.

The promotion takes the `CoordHom` witness `cd` (needed for the point map),
over an algebraically closed base field; the module-finiteness of the
coordinate-ring extension (the standing finite-map hypothesis of Silverman
II.2/II.3, consumed by III.4.8) is supplied by `CurveMap.CoordHom.module_finite`.

## Main definitions

* `EC.Isogeny.toBasicIsogeny` — the promotion
  `EC.Isogeny W₁ W₂ → HasseWeil.Isogeny W₁ W₂`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4.8 (the group-hom property).
-/

open WeierstrassCurve

namespace HasseWeil.EC.Isogeny

open HasseWeil.Curves

variable {F : Type*} [Field F] [DecidableEq F]
variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic] [IsAlgClosed F]
variable [IsDedekindDomain (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
variable [IsDedekindDomain (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
variable [IsIntegrallyClosed (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
variable [IsIntegrallyClosed (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]

/-- **`EC.Isogeny → HasseWeil.Isogeny`** (Silverman III.4.8). An `EC.Isogeny φ`
(with a coordinate-ring witness `cd`, over an algebraically closed field)
yields a `HasseWeil.Isogeny`: the pullback is `φ`'s function-field pullback,
and the bundled `AddMonoidHom` on points is the one produced by Silverman
III.4.8 (`toAddMonoidHom'`).

This is the canonical faithful bridge from the pullback-only `EC.Isogeny` model
to the points-bearing `Basic.Isogeny` model, **without** a repo-wide migration:
the group-hom field is now a *theorem* (`addHomProperty`), not an axiom. -/
noncomputable def toBasicIsogeny (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom) :
    HasseWeil.Isogeny W₁ W₂ where
  pullback := φ.toCurveMap.pullback
  toAddMonoidHom := φ.toAddMonoidHom' cd

@[simp] theorem toBasicIsogeny_pullback (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom) :
    (φ.toBasicIsogeny cd).pullback = φ.toCurveMap.pullback := rfl

@[simp] theorem toBasicIsogeny_toAddMonoidHom (φ : Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom) :
    (φ.toBasicIsogeny cd).toAddMonoidHom = φ.toAddMonoidHom' cd := rfl

end HasseWeil.EC.Isogeny
