/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PointsDictionary
import ModularCurves.EllipticCurve.ModelVariableChange
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

open AlgebraicGeometry CategoryTheory Limits HomogeneousIdeal
  CategoryTheory.MonoidalCategory

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ModularCurves

section Bridge

variable {K : Type u} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic] [W.toAffine.IsElliptic]

/-- **(U5c-1(ii))** The function field of the projective model is the function field of
the affine Weierstrass curve: the `Z`-chart is an affine open with sections the affine
coordinate ring, and both sides are its fraction field. The integrality instance is an
argument (discharged at use sites by `isIntegral_projModel_u`, universe-polymorphic). -/
noncomputable def projModelFunctionFieldEquiv [IsIntegral (projModel W)] :
    (projModel W).functionField ≃+* W.toAffine.FunctionField := by
  have hf := mk_X_mem_quotientGrading_one W 2
  have hU : IsAffineOpen (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) := by
    rw [← Proj.opensRange_awayι (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) hf one_pos]
    exact isAffineOpen_opensRange _
  haveI hnt : Nontrivial Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) :=
    (coordRingToZSection W).symm.toEquiv.nontrivial
  haveI hne : Nonempty (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) := by
    by_contra h
    have hbot : (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) = ⊥ := by
      rw [← TopologicalSpace.Opens.not_nonempty_iff_eq_bot]
      exact fun hcon => h hcon.to_subtype
    refine (not_subsingleton_iff_nontrivial.mpr hnt) ?_
    rw [hbot]
    infer_instance
  haveI := functionField_isFractionRing_of_isAffineOpen (X := projModel W) _ hU
  exact (IsLocalization.ringEquivOfRingEquiv
    (M := nonZeroDivisors W.toAffine.CoordinateRing)
    (S := W.toAffine.FunctionField)
    (Q := (projModel W).functionField)
    (coordRingToZSection W)
    (MulEquivClass.map_nonZeroDivisors (coordRingToZSection W))).symm

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

end Bridge

end ModularCurves
