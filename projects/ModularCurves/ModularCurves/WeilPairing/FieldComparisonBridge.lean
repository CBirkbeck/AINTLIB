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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(U5c-2 sub-brick — the chart-constants identification)** The chart identification
`coordRingToZSection` carries the `K`-constant of the coordinate ring to the restriction
of the structure-pulled global constant. The `chartZAffineEquiv`-leg is an `≃ₐ[K]`
(`.commutes` free); the remaining legs are `algebraMap_gradeZero_comp_eq`
(WeierstrassModel:373) and the `awayι`/`toSpecZero` compatibility. -/
theorem coordRingToZSection_algebraMap (a : K) :
    coordRingToZSection W (algebraMap K W.toAffine.CoordinateRing a)
      = ((projModel W).presheaf.map (homOfLE le_top).op)
          ((projModelπ W).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) := by
  unfold coordRingToZSection
  simp only [RingEquiv.coe_trans, Function.comp_apply]
  have hA : (chartZRingEquiv W).symm ((algebraMap K W.toAffine.CoordinateRing) a)
      = (chartCoordEquiv W 2) (algebraMap K (MvPolynomial {j : Fin 3 // j ≠ 2} K ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux K 2 W.toProjective.polynomial}) a) := by
    show ((chartCoordEquiv W 2).symm.trans
      (chartZAffineEquiv W).toRingEquiv).symm _ = _
    rw [RingEquiv.symm_trans_apply]
    exact congrArg (chartCoordEquiv W 2) ((chartZAffineEquiv W).symm.commutes a)
  rw [hA]
  -- Leg C morphism algebra: the awayι-composite of the structure morphism is Spec of the
  -- zero-degree composite
  have hπ : Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos ≫ projModelπ W
      = Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
          (quotientGrading (projIdeal W))
          (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))) ≫
        Spec.map (CommRingCat.ofHom (algebraMapGradeZero (projIdeal W))) := by
    show _ ≫ (Proj.toSpecZero _ ≫ Spec.map _) = _
    rw [← Category.assoc, Proj.awayι_toSpecZero]
  -- S1: re-express the restriction through the awayι presentation
  have hres := (Iso.comp_inv_eq _).mp (Proj_awayι_appTop_ΓSpecIso
    (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
    (mk_X_mem_quotientGrading_one W 2) one_pos).symm
  rw [hres]
  -- S2: the constant's transport through the two Spec.map legs
  have helt : (Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).appTop.hom
      ((projModelπ W).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))
    = (Scheme.ΓSpecIso _).inv ((CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
        (quotientGrading (projIdeal W))
        (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))).hom
          ((CommRingCat.ofHom (algebraMapGradeZero (projIdeal W))).hom a)) := by
    have h0 := congrArg
      (fun m : Spec (CommRingCat.of (HomogeneousLocalization.Away
          (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) ⟶
        Spec (CommRingCat.of K) =>
        m.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) hπ
    refine h0.trans ?_
    have hn1 : (CommRingCat.Hom.hom (Scheme.Hom.app (Spec.map
          (CommRingCat.ofHom (algebraMapGradeZero (projIdeal W)))) ⊤))
          ((ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv) a)
        = (ConcreteCategory.hom (Scheme.ΓSpecIso
              (CommRingCat.of ↥((projIdeal W).quotientGrading 0))).inv)
            ((CommRingCat.ofHom (algebraMapGradeZero (projIdeal W))).hom a) :=
      (congrArg (fun m => CommRingCat.Hom.hom m a)
        (Scheme.ΓSpecIso_inv_naturality
          (CommRingCat.ofHom (algebraMapGradeZero (projIdeal W))))).symm
    have hn2 : (CommRingCat.Hom.hom (Scheme.Hom.app (Spec.map
          (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
            (quotientGrading (projIdeal W))
            (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))))) ⊤))
          ((ConcreteCategory.hom (Scheme.ΓSpecIso
              (CommRingCat.of ↥((projIdeal W).quotientGrading 0))).inv)
            ((CommRingCat.ofHom (algebraMapGradeZero (projIdeal W))).hom a))
        = (ConcreteCategory.hom (Scheme.ΓSpecIso _).inv)
            ((CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
              (quotientGrading (projIdeal W))
              (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))).hom
              ((CommRingCat.ofHom (algebraMapGradeZero (projIdeal W))).hom a)) :=
      (congrArg (fun m => CommRingCat.Hom.hom m
          ((CommRingCat.ofHom (algebraMapGradeZero (projIdeal W))).hom a))
        (Scheme.ΓSpecIso_inv_naturality
          (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
            (quotientGrading (projIdeal W))
            (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))))).symm
    exact (congrArg (CommRingCat.Hom.hom (Scheme.Hom.app (Spec.map
        (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
          (quotientGrading (projIdeal W))
          (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))))) ⊤))
      hn1).trans hn2
  sorry

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
    (P₀ : W.toAffine.Point)
    (hP₀ : P₀ = (show W.baseChange K = W by
      show W.map (algebraMap K K) = W
      rw [Algebra.algebraMap_self, WeierstrassCurve.map_id]) ▸ P')
    (τ : projModel W ⟶ projModel W)
    (hτ : τ = (translateByIso (modelEllipticCurve W) x).hom.left)
    [IsDominant τ] :
    (HasseWeil.translateAlgEquivOfPoint W P₀).toRingEquiv.toRingHom =
    (projModelFunctionFieldEquiv W).toRingHom.comp
      (τ.functionFieldMap.hom.comp
        (projModelFunctionFieldEquiv W).symm.toRingHom) := by
  -- PROOF SCAFFOLD (recorded; the two computations are the real content):
  -- 1. `IsFractionRing.ringHom_ext` (mathlib FractionRing.lean:355): two ring homs out of
  --    the fraction field `W.toAffine.FunctionField` agree iff they agree on
  --    `CoordinateRing`.
  -- 2. `CoordinateRing = AdjoinRoot (W-poly over K[X])`: reduce to the `x`- and
  --    `y`-generators (AdjoinRoot-ext + Polynomial-ext).
  -- 3. τ-side value on a generator: through `projModelFunctionFieldEquiv` the generator is
  --    the class of a `Z`-chart section; `functionFieldMap_germToFunctionField`
  --    (DominantFunctionField:95) computes `τ.functionFieldMap` on it as the class of
  --    `τ.app (chart-section)` — the translated chart coordinate, evaluated by the
  --    addition/translation spec-points machinery (`mulModelHom_specPoints`-genre at the
  --    generic point).
  -- 4. HasseWeil side on the generators: the slope-formula cases of
  --    `translateAlgEquivOfPoint` (TranslationOrd.lean:3290) — plus
  --    `mulByInt_pullbackAlgHom_x_gen` (MulByHomDegree:324) as the proven [n]-anchor
  --    exemplar.
  -- 5. Orientation/convention pinned at the first generator computation.
  refine IsFractionRing.ringHom_ext (A := W.toAffine.CoordinateRing) ?_
  intro c
  induction c using AdjoinRoot.induction_on with
  | _ f => ?_
  -- three anchors: the K-constants, the x-generator, the y-generator (the root)
  set L := ((HasseWeil.translateAlgEquivOfPoint W P₀).toRingEquiv.toRingHom).comp
    (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField) with hL
  set R := ((projModelFunctionFieldEquiv W).toRingHom.comp
    ((CommRingCat.Hom.hom (Scheme.Hom.functionFieldMap τ)).comp
      (projModelFunctionFieldEquiv W).symm.toRingHom)).comp
    (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField) with hR
  have hK : ∀ a : K, L ((AdjoinRoot.mk W.toAffine.polynomial) (Polynomial.C (Polynomial.C a)))
      = R ((AdjoinRoot.mk W.toAffine.polynomial) (Polynomial.C (Polynomial.C a))) := by
    intro a
    have ha : (AdjoinRoot.mk W.toAffine.polynomial) (Polynomial.C (Polynomial.C a))
        = algebraMap K W.toAffine.CoordinateRing a := rfl
    rw [ha]
    simp only [hL, hR, RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply K W.toAffine.CoordinateRing W.toAffine.FunctionField]
    rw [show ((HasseWeil.translateAlgEquivOfPoint W P₀).toRingEquiv.toRingHom)
        ((algebraMap K W.toAffine.FunctionField) a)
      = algebraMap K W.toAffine.FunctionField a from
        (HasseWeil.translateAlgEquivOfPoint W P₀).commutes a]
    -- the τ-invariance of the K-constant's function-field class (isolated brick:
    -- provable via functionFieldMap_comp at τ ≫ π = π once the chart-constants
    -- identification lands; see the board's U5c-2 entry)
    have hinv : (CommRingCat.Hom.hom (Scheme.Hom.functionFieldMap τ))
        ((projModelFunctionFieldEquiv W).symm.toRingHom
          ((algebraMap K W.toAffine.FunctionField) a)) =
      (projModelFunctionFieldEquiv W).symm.toRingHom
        ((algebraMap K W.toAffine.FunctionField) a) := by
      haveI hZaff : IsAffineOpen (zChart W) :=
        Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
      haveI : Nontrivial Γ(projModel W, zChart W) :=
        (coordRingToZSection W).toEquiv.symm.nontrivial
      haveI : Nonempty (zChart W : (projModel W).Opens) :=
        ⟨hZaff.isoSpec.inv.base (Classical.arbitrary _)⟩
      haveI : IsFractionRing Γ(projModel W, zChart W) (projModel W).functionField :=
        functionField_isFractionRing_of_isAffineOpen (projModel W) _ hZaff
      have h1 : (projModelFunctionFieldEquiv W).symm.toRingHom
          ((algebraMap K W.toAffine.FunctionField) a)
        = algebraMap Γ(projModel W, zChart W) ((projModel W).functionField)
            (coordRingToZSection W (algebraMap K W.toAffine.CoordinateRing a)) := by
        refine (RingEquiv.symm_apply_eq _).mpr ?_
        rw [projModelFunctionFieldEquiv_germ W
          (coordRingToZSection W (algebraMap K W.toAffine.CoordinateRing a)),
          RingEquiv.symm_apply_apply]
        exact (IsScalarTower.algebraMap_apply K W.toAffine.CoordinateRing
          W.toAffine.FunctionField a).symm
      rw [h1]
      sorry
    rw [hinv]
    exact (RingEquiv.apply_symm_apply _ _).symm
  have hx : L ((AdjoinRoot.mk W.toAffine.polynomial) (Polynomial.C Polynomial.X))
      = R ((AdjoinRoot.mk W.toAffine.polynomial) (Polynomial.C Polynomial.X)) := by
    sorry
  have hy : L ((AdjoinRoot.mk W.toAffine.polynomial) Polynomial.X)
      = R ((AdjoinRoot.mk W.toAffine.polynomial) Polynomial.X) := by
    sorry
  show L f = R f
  induction f using Polynomial.induction_on with
  | C q =>
      induction q using Polynomial.induction_on with
      | C a => exact hK a
      | add p₁ q₁ h₁ h₂ =>
          simpa only [map_add] using congrArg₂ (· + ·) h₁ h₂
      | monomial n a ih =>
          have h1 : (Polynomial.C (Polynomial.C a * Polynomial.X ^ (n + 1)) :
              Polynomial (Polynomial K)) =
              Polynomial.C (Polynomial.C a * Polynomial.X ^ n) *
                Polynomial.C Polynomial.X := by
            rw [← Polynomial.C_mul, mul_assoc, pow_succ]
          rw [h1, map_mul, map_mul, map_mul, ih, hx]
  | add p q hp hq =>
      simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | monomial n a ih =>
      have h1 : (Polynomial.C a * Polynomial.X ^ (n + 1) :
          Polynomial (Polynomial K)) =
          Polynomial.C a * Polynomial.X ^ n * Polynomial.X := by
        rw [mul_assoc, pow_succ]
      rw [h1, map_mul, map_mul, map_mul, ih, hy]

end Bridge

end EllipticCurve

end ModularCurves
