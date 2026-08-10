/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PointsDictionary
import ModularCurves.ForMathlib.DominantFunctionField
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

open AlgebraicGeometry CategoryTheory Limits

namespace ModularCurves

section Bridge

variable {K : Type u} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic] [W.toAffine.IsElliptic]

/-- **(U5c-1(ii))** The function field of the projective model is the function field of
the affine Weierstrass curve: the `Z`-chart is an affine open with sections the affine
coordinate ring, and both sides are its fraction field. The integrality instance is an
argument (discharged at use sites by `isIntegral_projModel_u`, universe-polymorphic). -/
noncomputable def projModelFunctionFieldEquiv [IsIntegral (projModel W)] :
    (projModel W).functionField ≃+* W.toAffine.FunctionField := by sorry

/- **(U5c-2, the translation bridge — the largest missing API of the U5 leaf; statement
deferred until `projModelFunctionFieldEquiv` is proven, since it conjugates through it —
a bare-∃ form would be vacuous.)** Board-level spec (tickets.md §U5c-2): for a `K`-point
`P` of the model with dictionary image `P' : W.toAffine.Point`, the function-field map
induced by the scheme translation `translateByPoint` (through the `𝟙`-base-change
collapse iso and `Scheme.Hom.functionFieldMap`) equals `translateAlgEquivOfPoint W P'`
conjugated by `projModelFunctionFieldEquiv`. -/

end Bridge

end ModularCurves
