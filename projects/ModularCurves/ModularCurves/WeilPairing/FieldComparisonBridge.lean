/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PointsDictionary
import ModularCurves.EllipticCurve.ModelVariableChange
import ModularCurves.EllipticCurve.MulByHomDegree
import ModularCurves.ForMathlib.DominantFunctionField
import ModularCurves.GroupScheme.TranslationBySection
import HasseWeil.HasseBound.WeilPairing.PairingProps

/-!
# The scheme ↔ function-field bridge for the field-level comparison (AP-E4a-U5c)

T-C4's substrate, per the validated E4a plan (`decomposition-e4a-self.md`, U5 subcut):
to compare the KM pairing (`weilPairingEval` over `Spec K`) with HasseWeil's classical
pairing (`weilPairing`, defined by the translation characterisation
`τ_S g_T = e_ℓ(S,T) • g_T` in `W.toAffine.FunctionField`), the two languages meet at

* the **points dictionary** — `projModelPointsEquiv` (`EllipticCurve/PointsDictionary`),
  already pointed and chart-value-characterised;
* the **function-field dictionary** — `(projModel W).functionField ≃+* W.toAffine.FunctionField`
  (below): the `Z`-chart of the projective model is an affine open whose sections
  identify with the affine coordinate ring, and both sides are fraction fields
  (`functionField_isFractionRing_of_isAffineOpen` on the scheme side, the
  `FunctionField` instances on the HasseWeil side);
* the **translation bridge** — the scheme-level translation automorphism
  (`translateByPoint`) induces, through `Scheme.Hom.functionFieldMap`
  (`ForMathlib/DominantFunctionField`), precisely HasseWeil's
  `translateAlgEquivOfPoint` under the two dictionaries.

With these, U5b's glued rational function from the KM splitting satisfies HasseWeil's
characterising identity, `weilPairing_spec` pins the scalar, and `weilPairing_self`
closes the field leaf (U5d/U5e).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits HomogeneousIdeal
  CategoryTheory.MonoidalCategory

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ModularCurves

namespace EllipticCurve

section Bridge

variable {K : Type u} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic] [W.toAffine.IsElliptic]

/- **(U5c-1(ii)) — DISCHARGED BY REUSE.** `projModelFunctionFieldEquiv` already exists:
`EllipticCurve/MulByHomDegree.lean:85` (K4 (B)), the identical `coordRingToZSection` +
`functionField_isFractionRing_of_isAffineOpen` construction. The name clash that caught the
duplication is the workspace working as intended. That file also carries the `[N]`-precedent
for U5c-2: the L4-iii comparison `functionFieldMap [N] = mulByInt_pullbackAlgHom` mod
`projModelFunctionFieldEquiv`, with `functionFieldMap_germToFunctionField` computing the
chart-coordinate side — the translation bridge below mirrors that shape. -/

/- **(U5c-2, the translation bridge — the core comparison API)** The function-field
action of the scheme-level translation automorphism (`translateByIso` on the model
record, no base-change clothing) is HasseWeil's `translateAlgEquivOfPoint`, conjugated
through `projModelFunctionFieldEquiv`. The section `x` and the affine point `P'`
correspond under the points dictionary (`projModelPointsEquiv`), expressed through the
underlying morphism of `x`.

Convention check (recorded per the validation): whether the right-hand side is
`translateAlgEquivOfPoint W P'` or its inverse is pinned during the proof by computing
one coordinate on the `Z`-chart; the statement records the natural orientation.

Proof strategy (validated): both sides are ring maps out of `W.toAffine.FunctionField`
determined by their values on the coordinate generators; compute the left side's values
via the `KE`-valued `specPoints` machinery (`mulModelHom_specPoints` at `K := KE`
applied to the translated generic point) and match HasseWeil's slope formulas. -/
/- U5c-2 STATEMENT DRAFT (elaboration in progress — resume here):
theorem functionFieldMap_translateBy [IsIntegral (projModel W)]
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ (modelEllipticCurve W).asOver)
    (p : SpecPoints (projModel W) (projModelπ W) K)
    (hxp : x.left = p.1)
    (P' : W.toAffine.Point) (hP' : projModelPointsEquiv W K p = P'.baseChange K)
    [IsDominant ((GrpObj.translateByIso (E := (modelEllipticCurve W).asOver) x).hom.left)] :
    (projModelFunctionFieldEquiv W).toRingHom.comp
      (((GrpObj.translateByIso (E := (modelEllipticCurve W).asOver) x).hom.left).functionFieldMap.hom.comp
        (projModelFunctionFieldEquiv W).symm.toRingHom) =
      (translateAlgEquivOfPoint W P').toRingEquiv.toRingHom := by
  sorry


Elaboration fixes found so far: `translateByIso` is `ModularCurves.EllipticCurve.translateByIso`
(namespace EllipticCurve, E implicit from x's type — NOT GrpObj); `SpecPoints` needs
`[Algebra K K]` (present); the points-dictionary target is `(W.baseChange K).toAffine.Point`
while `translateAlgEquivOfPoint` wants `W.toAffine.Point` — the self-baseChange wrinkle.
DESIGN DECISION (no in-tree precedent — no consumer of projModelPointsEquiv has hit it):
quantify `P' : (W.baseChange K).toAffine.Point` and state the RHS at the curve
`W.baseChange K` (its `[IsElliptic]`-instances transport along `map`); a consuming
corollary collapses to `W` later via mathlib `WeierstrassCurve.map_id`. This keeps the
bridge statement dictionary-native. Then prove via the KE-valued specPoints strategy in
the docstring above.
FURTHER BRICK (found while elaborating): the wrinkle also hits the FunctionField slot —
`translateAlgEquivOfPoint (W.baseChange K) P'` acts on `(W.baseChange K).toAffine.FunctionField`,
not `W.toAffine.FunctionField`. Add the one-time brick
`functionFieldSelfBaseChangeEquiv : W.toAffine.FunctionField ≃+* (W.baseChange K).toAffine.FunctionField`
built from mathlib `WeierstrassCurve.Affine.CoordinateRing.map (RingHom.id K)`-functoriality
(Point.lean:184) + `IsLocalization.ringEquivOfRingEquiv` (same pattern as
`projModelFunctionFieldEquiv` above), and route the U5c-2 conjugation through it. -/

/-- **(U5c-2 brick)** The self-base-change collapse on function fields:
`W.baseChange K = W.map (algebraMap K K) = W.map (RingHom.id K) = W`, transported to the
function fields. Sealed as a named equiv so the U5c-2 conjugation never exposes the
cast. -/
noncomputable def functionFieldSelfBaseChangeEquiv :
    W.toAffine.FunctionField ≃+* (W.baseChange K).toAffine.FunctionField := by
  have h : W.baseChange K = W := by
    show W.map (algebraMap K K) = W
    rw [Algebra.algebraMap_self, WeierstrassCurve.map_id]
  rw [h]

/-- **(U5c-2)** The translation bridge: the function-field action of the scheme-level
translation automorphism equals HasseWeil's `translateAlgEquivOfPoint` (at the
self-base-changed curve, per the recorded design), conjugated through the two proven
dictionaries. Orientation to be convention-checked on one `Z`-chart coordinate during
the proof; proof strategy: both sides are determined on the coordinate generators —
compute the left side via the `KE`-valued specPoints machinery. -/
theorem functionFieldMap_translateBy [IsIntegral (projModel W)]
    [(W.baseChange K).toAffine.IsElliptic]
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ (modelEllipticCurve W).asOver)
    (p : SpecPoints (projModel W) (projModelπ W) K)
    (hxp : x.left = p.1)
    (P' : ((W.baseChange K).toAffine).Point)
    (hP' : projModelPointsEquiv W K p = P')
    (τ : projModel W ⟶ projModel W)
    (hτ : τ = (translateByIso (modelEllipticCurve W) x).hom.left)
    [IsDominant τ] :
    (functionFieldSelfBaseChangeEquiv W).symm.toRingHom.comp
      ((HasseWeil.translateAlgEquivOfPoint (W.baseChange K) P').toRingEquiv.toRingHom.comp
        (functionFieldSelfBaseChangeEquiv W).toRingHom) =
    (projModelFunctionFieldEquiv W).toRingHom.comp
      (τ.functionFieldMap.hom.comp
        (projModelFunctionFieldEquiv W).symm.toRingHom) := by
  sorry

end Bridge

end EllipticCurve

end ModularCurves
