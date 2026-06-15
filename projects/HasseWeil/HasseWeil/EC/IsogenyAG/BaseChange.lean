/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.CoordHomFinite
import HasseWeil.EC.IsogenyAG.FrobeniusTwist
import HasseWeil.EC.IsogenyAG.RamificationInfty
import HasseWeil.Curves.OrdAtInftyBaseChange

/-!
# ISO-BC: base change of an `EC.Isogeny` along a field extension

For an isogeny `φ : E → E` over `K` carrying a coordinate-ring witness `cd`, and a
field extension `L/K` with `L` algebraically closed, this file constructs the
base-changed isogeny over `L` together with all the witnesses that the descent
engine `addHomProperty_descend_of_baseChange` (`GroupHomDescend.lean`) consumes:

* `EC.Isogeny.baseChangeIsogeny` — the base-changed isogeny
  `φ_L : E_L → E_L` over `L`, built with the **`EC.Isogeny.ofEquation`** builder
  (`FrobeniusTwist.lean`): its pullback sends the generators to the
  `functionFieldMap`-images of `φ^* x_gen`, `φ^* y_gen`, and the basepoint
  condition (`pullback_ordAtInfty_nonneg`) is *proven* by the `{1, y}`-parity
  route, not carried.  The three builder inputs are discharged as follows:
  - the `Equation` witness transports the `K`-level pullback of the generic
    equation along `functionFieldMap` (`Affine.Equation.map` twice, plus the
    curve identity `baseChange_map_functionFieldMap`);
  - the even-negative order at infinity comes from the `K`-level ramification
    formula `exists_pos_ramificationIdx_at_infinity` (`RamificationInfty.lean`,
    `ord_∞(φ^* x_gen) = e • (-2)`) transported along
    `ordAtInfty_functionFieldMap` (`OrdAtInftyBaseChange.lean`);
  - transcendence over `L` follows from the nonzero order at infinity: an
    element algebraic over the algebraically closed constant field `L` would be
    a constant, of order `0`.
* `EC.Isogeny.baseChangeCoordHom` — the base-changed coordinate-ring witness,
  packaging `CurveMap.CoordHom.baseChangeAlgHom` (`CurveMapBaseChange.lean`)
  with the `compat` field (an `AdjoinRoot.ringHom_ext` computation on the
  generators).
* `CurveMap.CoordHom.baseChange_module_finite` — transport of the standing
  `Module.Finite` witness along base change: `L[C]` is the `L`-span of the
  `coordRingMap`-image, `L`-scalars are `baseChangeAlgHom`-scalars, and
  `coordRingMap` is semilinear over `cd` by the naturality square
  `baseChangeAlgHom_coordRingMap`.
* `EC.Isogeny.baseChange_toPointMap_compat` — the point-map compatibility:
  `Affine.Point.map (algebraMap K L)` intertwines `φ.toPointMap cd` with
  `(φ_L).toPointMap (cd_L)`.  Reduces to evaluation naturality
  `evalAt_coordRingMap` (`P`-evaluation commutes with the coefficient map, via
  mathlib's `Polynomial.map_mapRingHom_evalEval`) plus the generator facts for
  `baseChangeAlgHom`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], I.2 (base change /
  "defined over `K`"), III.4.8.
-/

open WeierstrassCurve Polynomial

namespace HasseWeil.Curves

/-! ### Generator facts and the naturality square for `CoordHom.baseChangeAlgHom` -/

namespace CurveMap.CoordHom

variable {K : Type*} [Field K] {C₁ C₂ : SmoothPlaneCurve K} {φ : CurveMap C₁ C₂}
variable (cd : φ.CoordHom) (L : Type*) [Field L] [Algebra K L]

/-- `baseChangeAlgHom` sends the `Y`-generator (the `AdjoinRoot` root) of the
base-changed coordinate ring to the `coordRingMap`-image of the image of the
`K`-level root. -/
theorem baseChangeAlgHom_root :
    cd.baseChangeAlgHom L (AdjoinRoot.root (C₂.baseChange L).toAffine.polynomial) =
      C₁.coordRingMap L (cd.toAlgHom (AdjoinRoot.root C₂.toAffine.polynomial)) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- `baseChangeAlgHom` sends the `X`-generator of the base-changed coordinate
ring to the `coordRingMap`-image of the image of the `K`-level `X`-generator. -/
theorem baseChangeAlgHom_X :
    cd.baseChangeAlgHom L
        (algebraMap (Polynomial L) (C₂.baseChange L).CoordinateRing Polynomial.X) =
      C₁.coordRingMap L
        (cd.toAlgHom (algebraMap (Polynomial K) C₂.CoordinateRing Polynomial.X)) := by
  have h := AdjoinRoot.liftAlgHom_of (C₂.toAffine.baseChange L).toAffine.polynomial
    (cd.baseChangeInnerAlgHom L) (cd.baseChangeYImage L)
    (cd.baseChange_eval₂_zero L) Polynomial.X
  have h2 : cd.baseChangeInnerAlgHom L Polynomial.X = cd.baseChangeXImage L :=
    Polynomial.aeval_X _
  exact h.trans h2

/-- `coordRingMap` fixes the `X`-generator. -/
theorem _root_.HasseWeil.Curves.SmoothPlaneCurve.coordRingMap_X
    (C : SmoothPlaneCurve K) :
    C.coordRingMap L (algebraMap (Polynomial K) C.CoordinateRing Polynomial.X) =
      algebraMap (Polynomial L) (C.baseChange L).CoordinateRing Polynomial.X := by
  show WeierstrassCurve.Affine.CoordinateRing.map C.toAffine (algebraMap K L)
    (WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
      (Polynomial.C Polynomial.X)) = _
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk]
  rw [show ((Polynomial.C Polynomial.X : Polynomial (Polynomial K)).map
      (Polynomial.mapRingHom (algebraMap K L))) = Polynomial.C Polynomial.X by
    rw [Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_X]]
  rfl

/-- `coordRingMap` fixes the `Y`-generator (the `AdjoinRoot` root). -/
theorem _root_.HasseWeil.Curves.SmoothPlaneCurve.coordRingMap_root
    (C : SmoothPlaneCurve K) :
    C.coordRingMap L (AdjoinRoot.root C.toAffine.polynomial) =
      AdjoinRoot.root (C.baseChange L).toAffine.polynomial := by
  show WeierstrassCurve.Affine.CoordinateRing.map C.toAffine (algebraMap K L)
    (AdjoinRoot.root C.toAffine.polynomial) = _
  rw [← AdjoinRoot.mk_X, WeierstrassCurve.Affine.CoordinateRing.map_mk,
    Polynomial.map_X, AdjoinRoot.mk_X]
  rfl

/-- **The naturality square for the base-changed coordinate-ring hom**:
`baseChangeAlgHom ∘ coordRingMap = coordRingMap ∘ toAlgHom`.  By
`AdjoinRoot.ringHom_ext` it suffices to check the `K`-constants and the two
generators, where both sides are computed by `baseChangeAlgHom_X/root` and
`coordRingMap_X/root`. -/
theorem baseChangeAlgHom_coordRingMap (u : C₂.CoordinateRing) :
    cd.baseChangeAlgHom L (C₂.coordRingMap L u) =
      C₁.coordRingMap L (cd.toAlgHom u) := by
  have key : ((cd.baseChangeAlgHom L).toRingHom.comp (C₂.coordRingMap L)) =
      (C₁.coordRingMap L).comp cd.toAlgHom.toRingHom := by
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · -- agree on `of q` for `q : K[X]`
      refine Polynomial.ringHom_ext (fun a => ?_) ?_
      · -- constants from `K`
        show cd.baseChangeAlgHom L (C₂.coordRingMap L
            (algebraMap (Polynomial K) C₂.CoordinateRing (Polynomial.C a))) =
          C₁.coordRingMap L (cd.toAlgHom
            (algebraMap (Polynomial K) C₂.CoordinateRing (Polynomial.C a)))
        rw [show (algebraMap (Polynomial K) C₂.CoordinateRing) (Polynomial.C a) =
            algebraMap K C₂.CoordinateRing a from
          (IsScalarTower.algebraMap_apply K (Polynomial K) C₂.CoordinateRing a).symm]
        rw [SmoothPlaneCurve.coordRingMap_algebraMap_F C₂ L a, AlgHom.commutes,
          SmoothPlaneCurve.coordRingMap_algebraMap_F C₁ L a]
        rw [IsScalarTower.algebraMap_apply K L (C₂.baseChange L).CoordinateRing a]
        exact (cd.baseChangeAlgHom L).commutes (algebraMap K L a) |>.trans
          (IsScalarTower.algebraMap_apply K L (C₁.baseChange L).CoordinateRing a).symm
      · -- the `X` generator
        show cd.baseChangeAlgHom L (C₂.coordRingMap L
            (algebraMap (Polynomial K) C₂.CoordinateRing Polynomial.X)) =
          C₁.coordRingMap L (cd.toAlgHom
            (algebraMap (Polynomial K) C₂.CoordinateRing Polynomial.X))
        rw [SmoothPlaneCurve.coordRingMap_X]
        exact baseChangeAlgHom_X cd L
    · -- the root generator
      show cd.baseChangeAlgHom L (C₂.coordRingMap L
          (AdjoinRoot.root C₂.toAffine.polynomial)) =
        C₁.coordRingMap L (cd.toAlgHom (AdjoinRoot.root C₂.toAffine.polynomial))
      rw [SmoothPlaneCurve.coordRingMap_root]
      exact baseChangeAlgHom_root cd L
  exact RingHom.congr_fun key u

/-- **Base change preserves module-finiteness of a coordinate-ring witness**:
`L[C₁]` is a finite module over `L[C₂]` via `cd.baseChangeAlgHom L` (the
`K`-level finiteness input is supplied by `CoordHom.module_finite`).

The image of a `K`-level generating set under `coordRingMap` generates: every
element of `L[C₁]` is an `L`-combination of `coordRingMap`-images
(`fwdPinned_surjective`), `L`-scalars are `baseChangeAlgHom`-scalars (the
`AlgHom` fixes `L`), and `coordRingMap` is `cd → baseChangeAlgHom` semilinear by
the naturality square. -/
theorem baseChange_module_finite :
    @Module.Finite (C₂.baseChange L).CoordinateRing (C₁.baseChange L).CoordinateRing _ _
      (cd.baseChangeAlgHom L).toRingHom.toAlgebra.toModule := by
  have hfin : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _
      cd.toAlgebra.toModule := by
    exact cd.module_finite
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  letI algL : Algebra (C₂.baseChange L).CoordinateRing (C₁.baseChange L).CoordinateRing :=
    (cd.baseChangeAlgHom L).toRingHom.toAlgebra
  letI modL : Module (C₂.baseChange L).CoordinateRing (C₁.baseChange L).CoordinateRing :=
    algL.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR := hfin
  obtain ⟨S, hS⟩ := Module.finite_def.mp hfin'
  refine Module.finite_def.mpr ⟨S.image (C₁.coordRingMap L), ?_⟩
  rw [eq_top_iff]
  rintro w -
  -- Step 1: `coordRingMap`-images of `K`-level elements lie in the span.
  have key : ∀ u : C₁.CoordinateRing,
      C₁.coordRingMap L u ∈ Submodule.span (C₂.baseChange L).CoordinateRing
        ((S.image (C₁.coordRingMap L) : Finset (C₁.baseChange L).CoordinateRing) :
          Set (C₁.baseChange L).CoordinateRing) := by
    intro u
    have humem : u ∈ (⊤ : Submodule C₂.CoordinateRing C₁.CoordinateRing) :=
      Submodule.mem_top
    rw [← hS] at humem
    induction humem using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hx)))
    | zero =>
      rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ ihx ihy =>
      rw [map_add]; exact Submodule.add_mem _ ihx ihy
    | smul r x _ ihx =>
      have hsemi : C₁.coordRingMap L (r • x) =
          (C₂.coordRingMap L r) • (C₁.coordRingMap L x) := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        exact (baseChangeAlgHom_coordRingMap cd L r).symm
      rw [hsemi]
      exact Submodule.smul_mem _ _ ihx
  -- Step 2: every element of `L[C₁]` is an `L`-combination of images.
  obtain ⟨z, rfl⟩ := C₁.fwdPinned_surjective L w
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero]; exact Submodule.zero_mem _
  | tmul l u =>
    rw [C₁.fwdPinned_tmul L l u]
    have hsmul : l • C₁.coordRingMap L u =
        (algebraMap L (C₂.baseChange L).CoordinateRing l) • C₁.coordRingMap L u := by
      rw [Algebra.smul_def, Algebra.smul_def]
      congr 1
      exact ((cd.baseChangeAlgHom L).commutes l).symm
    rw [hsmul]
    exact Submodule.smul_mem _ _ (key u)
  | add x y ihx ihy =>
    rw [map_add]; exact Submodule.add_mem _ ihx ihy

end CurveMap.CoordHom

/-! ### Evaluation naturality through base change -/

namespace SmoothPlaneCurve

variable {K : Type*} [Field K] (C : SmoothPlaneCurve K)
variable (L : Type*) [Field L] [Algebra K L]

/-- **Evaluation naturality through base change**: evaluating the
`coordRingMap`-image of `u` at the included point recovers the `algebraMap`-image
of the evaluation of `u` at `P`.  Reduces to mathlib's
`Polynomial.map_mapRingHom_evalEval`. -/
theorem evalAt_coordRingMap (P : C.SmoothPoint) (u : C.CoordinateRing) :
    (C.baseChange L).evalAt (C.includePoint L P) (C.coordRingMap L u) =
      algebraMap K L (C.evalAt P u) := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective u
  rw [show C.coordRingMap L (WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine g) =
      WeierstrassCurve.Affine.CoordinateRing.mk (C.baseChange L).toAffine
        (g.map (Polynomial.mapRingHom (algebraMap K L))) from
    WeierstrassCurve.Affine.CoordinateRing.map_mk (algebraMap K L) g]
  rw [SmoothPlaneCurve.evalAt_mk, SmoothPlaneCurve.evalAt_mk,
    SmoothPlaneCurve.includePoint_x, SmoothPlaneCurve.includePoint_y]
  exact Polynomial.map_mapRingHom_evalEval (algebraMap K L) g P.x P.y

end SmoothPlaneCurve

end HasseWeil.Curves

/-! ### The base-changed isogeny via `ofEquation` -/

namespace HasseWeil.EC.Isogeny

open HasseWeil.Curves

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (φ : EC.Isogeny W.toAffine W.toAffine)
variable (L : Type*) [Field L] [Algebra K L] [DecidableEq L]

/-- The image in `L(E_L)` of the pullback `φ^* x_gen`, under the base-change
inclusion `functionFieldMap : K(E) → L(E_L)`.  This is the `x_gen`-image of the
base-changed isogeny. -/
noncomputable def baseChangeXgen : (W.baseChange L).toAffine.FunctionField :=
  (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L
    (φ.toCurveMap.pullback (x_gen W))

/-- The image in `L(E_L)` of the pullback `φ^* y_gen`. -/
noncomputable def baseChangeYgen : (W.baseChange L).toAffine.FunctionField :=
  (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L
    (φ.toCurveMap.pullback (y_gen W))

omit [DecidableEq K] in
/-- The pullback pair `(φ^* x_gen, φ^* y_gen)` satisfies the generic Weierstrass
equation: apply the `K`-algebra hom `φ^*` to `generic_equation` (the pullback
fixes the base-changed coefficients). -/
theorem pullback_generic_equation :
    (W_KE W).toAffine.Equation (φ.toCurveMap.pullback (x_gen W))
      (φ.toCurveMap.pullback (y_gen W)) := by
  have h := WeierstrassCurve.Affine.Equation.map
    (f := (φ.toCurveMap.pullback : W.toAffine.FunctionField →+* W.toAffine.FunctionField))
    (generic_equation W)
  rwa [show (W_KE W).toAffine.map
      (φ.toCurveMap.pullback : W.toAffine.FunctionField →+* W.toAffine.FunctionField) =
      W_KE W from by
    show (W.map _).map _ = W.map _
    rw [WeierstrassCurve.map_map, AlgHom.comp_algebraMap]] at h

omit [DecidableEq K] [DecidableEq L] [WeierstrassCurve.IsElliptic W.toAffine] in
/-- The two composites `K → K(E) → L(E_L)` and `K → L → L(E_L)` agree. -/
theorem functionFieldMap_comp_algebraMap :
    ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L).comp
        (algebraMap K W.toAffine.FunctionField) =
      (algebraMap L (W.baseChange L).toAffine.FunctionField).comp (algebraMap K L) := by
  refine RingHom.ext fun a => ?_
  show (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L
      (algebraMap K (⟨W.toAffine⟩ : SmoothPlaneCurve K).FunctionField a) =
    algebraMap L (W.baseChange L).toAffine.FunctionField (algebraMap K L a)
  rw [SmoothPlaneCurve.functionFieldMap_algebraMap_F (⟨W.toAffine⟩ : SmoothPlaneCurve K) L a]
  exact IsScalarTower.algebraMap_apply K L
    ((⟨W.toAffine⟩ : SmoothPlaneCurve K).baseChange L).FunctionField a

omit [DecidableEq K] [DecidableEq L] [WeierstrassCurve.IsElliptic W.toAffine] in
/-- **The base-change curve identity**: pushing `W_KE` along `functionFieldMap`
gives the base change of `W.baseChange L` to its own function field. -/
theorem baseChange_map_functionFieldMap :
    (W_KE W).toAffine.map ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L) =
      (W.baseChange L).map
        (algebraMap L (W.baseChange L).toAffine.FunctionField) := by
  show (W.map _).map _ = (W.map _).map _
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  exact congrArg W.map (functionFieldMap_comp_algebraMap W L)

omit [DecidableEq K] [DecidableEq L] in
/-- The base-changed generator images satisfy the Weierstrass equation of the
base-changed curve over `L(E_L)` — the `Equation` input of `ofEquation`. -/
theorem baseChange_generic_equation :
    ((W.baseChange L).map
        (algebraMap L (W.baseChange L).toAffine.FunctionField)).toAffine.Equation
      (baseChangeXgen W φ L) (baseChangeYgen W φ L) := by
  have h := WeierstrassCurve.Affine.Equation.map
    (f := ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L :
      W.toAffine.FunctionField →+*
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).baseChange L).FunctionField))
    (pullback_generic_equation W φ)
  exact (congrArg (fun V : WeierstrassCurve ((W.baseChange L).toAffine.FunctionField) =>
    V.toAffine.Equation (baseChangeXgen W φ L) (baseChangeYgen W φ L))
    (baseChange_map_functionFieldMap W L)).mp h

omit [DecidableEq L] in
/-- The base-changed `x_gen`-image is nonzero. -/
theorem baseChangeXgen_ne_zero : baseChangeXgen W φ L ≠ 0 := fun h0 =>
  φ.toCurveMap.pullback_ne_zero (x_gen_ne_zero W)
    ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap_injective L
      (h0.trans (map_zero _).symm))

private theorem nsmul_coe_neg_two (e : ℕ) :
    e • ((-2 : ℤ) : WithTop ℤ) = ((2 * (-(e : ℤ)) : ℤ) : WithTop ℤ) := by
  induction e with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ih, ← WithTop.coe_add]
    exact WithTop.coe_inj.mpr (by push_cast; ring)

omit [DecidableEq L] in
/-- **The even-negative order at infinity of the base-changed `x_gen`-image**:
`ord_∞(φ^* x_gen) = e • (-2)` over `K` by the ramification formula
(`exists_pos_ramificationIdx_at_infinity`, with `e = e_φ(O) ≥ 1`), and the order
transports along `functionFieldMap` (`ordAtInfty_functionFieldMap`). -/
theorem exists_ordAtInfty_baseChangeXgen :
    ∃ m : ℤ, m ≤ -1 ∧
      (W_smooth (W.baseChange L)).ordAtInfty (baseChangeXgen W φ L) =
        ((2 * m : ℤ) : WithTop ℤ) := by
  obtain ⟨e, he1, hform⟩ := exists_pos_ramificationIdx_at_infinity φ
  refine ⟨-(e : ℤ), by
    have h1 : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he1
    omega, ?_⟩
  -- the K-level order
  have hKord : (⟨W.toAffine⟩ : SmoothPlaneCurve K).ordAtInfty
      (φ.toCurveMap.pullback (x_gen W)) = ((2 * (-(e : ℤ)) : ℤ) : WithTop ℤ) := by
    have h := hform (x_gen W) (x_gen_ne_zero W)
    rw [show (⟨W.toAffine⟩ : SmoothPlaneCurve K).ordAtInfty (x_gen W) =
        ((-2 : ℤ) : WithTop ℤ) from ordAtInfty_x_gen W] at h
    rw [h]
    exact nsmul_coe_neg_two e
  -- transport along the base-change inclusion
  have hne : φ.toCurveMap.pullback (x_gen W) ≠ 0 :=
    φ.toCurveMap.pullback_ne_zero (x_gen_ne_zero W)
  have htrans := SmoothPlaneCurve.ordAtInfty_functionFieldMap
    (⟨W.toAffine⟩ : SmoothPlaneCurve K) L (φ.toCurveMap.pullback (x_gen W)) hne
  exact htrans.trans hKord

omit [DecidableEq L] in
/-- **Transcendence of the base-changed `x_gen`-image over `L`** (for `L`
algebraically closed): an element algebraic over the algebraically closed
constant field `L` would be a constant (degree-one minimal polynomial), of
order `0` at infinity — contradicting the even-negative order. -/
theorem baseChangeXgen_transcendental [IsAlgClosed L] :
    Transcendental L (baseChangeXgen W φ L) := by
  intro halg
  obtain ⟨m, hm, hord⟩ := exists_ordAtInfty_baseChangeXgen W φ L
  have hint : IsIntegral L (baseChangeXgen W φ L) := halg.isIntegral
  have hdeg : (minpoly L (baseChangeXgen W φ L)).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one L (baseChangeXgen W φ L) hdeg
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact baseChangeXgen_ne_zero W φ L hc.symm
  have h0 : (W_smooth (W.baseChange L)).ordAtInfty (baseChangeXgen W φ L) =
      ((0 : ℤ) : WithTop ℤ) := by
    rw [← hc]
    exact (W_smooth (W.baseChange L)).ordAtInfty_algebraMap_F_nonzero hc0
  rw [h0] at hord
  have : (0 : ℤ) = 2 * m := WithTop.coe_inj.mp hord
  omega

/-- **The base-changed isogeny** `φ_L : E_L → E_L` (ISO-BC item 1), for `L/K`
with `L` algebraically closed.  Built with the `ofEquation` builder: the
pullback sends `x_gen ↦ functionFieldMap (φ^* x_gen)`,
`y_gen ↦ functionFieldMap (φ^* y_gen)`, and the basepoint condition
`pullback_ordAtInfty_nonneg` is proven (the `{1, y}`-parity route), not
carried. -/
noncomputable def baseChangeIsogeny [IsAlgClosed L] :
    EC.Isogeny (W.baseChange L).toAffine (W.baseChange L).toAffine :=
  EC.Isogeny.ofEquation (W.baseChange L) (W.baseChange L)
    (baseChangeXgen W φ L) (baseChangeYgen W φ L)
    (baseChange_generic_equation W φ L)
    (baseChangeXgen_transcendental W φ L)
    (Classical.choose_spec (exists_ordAtInfty_baseChangeXgen W φ L)).1
    (Classical.choose_spec (exists_ordAtInfty_baseChangeXgen W φ L)).2

/-! ### The base-changed coordinate-ring witness -/

variable (cd : φ.toCurveMap.CoordHom)

omit [DecidableEq K] [DecidableEq L] in
/-- The coordinate-ring pullback of the base-changed isogeny is
`algebraMap ∘ baseChangeAlgHom`: both sides are ring homs out of the
`AdjoinRoot` presentation, agreeing on `L`-constants and on the two generators
(`ofEquationCoordAlgHom_x/_y` versus `baseChangeAlgHom_X/_root` +
`functionFieldMap_algebraMap` + `cd.compat`). -/
theorem ofEquationCoordRingHom_eq_algebraMap_comp_baseChangeAlgHom :
    ofEquationCoordRingHom (W.baseChange L) (W.baseChange L)
        (baseChangeXgen W φ L) (baseChangeYgen W φ L)
        (baseChange_generic_equation W φ L) =
      (algebraMap (W.baseChange L).toAffine.CoordinateRing
          (W.baseChange L).toAffine.FunctionField).comp
        (cd.baseChangeAlgHom L).toRingHom := by
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · -- agreement on `L[X]`
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · -- constants from `L`
      show ofEquationCoordRingHom (W.baseChange L) (W.baseChange L)
          (baseChangeXgen W φ L) (baseChangeYgen W φ L)
          (baseChange_generic_equation W φ L)
          (algebraMap L (W.baseChange L).toAffine.CoordinateRing a) =
        algebraMap (W.baseChange L).toAffine.CoordinateRing
          (W.baseChange L).toAffine.FunctionField
          (cd.baseChangeAlgHom L (algebraMap L (W.baseChange L).toAffine.CoordinateRing a))
      have hcomm : cd.baseChangeAlgHom L
          (algebraMap L (W.baseChange L).toAffine.CoordinateRing a) =
          algebraMap L (W.baseChange L).toAffine.CoordinateRing a :=
        (cd.baseChangeAlgHom L).commutes a
      rw [hcomm]
      exact ((ofEquationCoordAlgHom (W.baseChange L) (W.baseChange L)
          (baseChangeXgen W φ L) (baseChangeYgen W φ L)
          (baseChange_generic_equation W φ L)).commutes a).trans
        (IsScalarTower.algebraMap_apply L (W.baseChange L).toAffine.CoordinateRing
          (W.baseChange L).toAffine.FunctionField a)
    · -- the `X` generator
      show ofEquationCoordRingHom (W.baseChange L) (W.baseChange L)
          (baseChangeXgen W φ L) (baseChangeYgen W φ L)
          (baseChange_generic_equation W φ L)
          (algebraMap (Polynomial L) (W.baseChange L).toAffine.CoordinateRing Polynomial.X) =
        algebraMap (W.baseChange L).toAffine.CoordinateRing
          (W.baseChange L).toAffine.FunctionField
          (cd.baseChangeAlgHom L
            (algebraMap (Polynomial L) (W.baseChange L).toAffine.CoordinateRing Polynomial.X))
      have hLx : ofEquationCoordRingHom (W.baseChange L) (W.baseChange L)
          (baseChangeXgen W φ L) (baseChangeYgen W φ L)
          (baseChange_generic_equation W φ L)
          (algebraMap (Polynomial L) (W.baseChange L).toAffine.CoordinateRing Polynomial.X) =
          baseChangeXgen W φ L :=
        ofEquationCoordAlgHom_x (W.baseChange L) (W.baseChange L) (baseChangeXgen W φ L)
          (baseChangeYgen W φ L) (baseChange_generic_equation W φ L)
      have hRx : cd.baseChangeAlgHom L
          (algebraMap (Polynomial L) (W.baseChange L).toAffine.CoordinateRing Polynomial.X) =
          (⟨W.toAffine⟩ : SmoothPlaneCurve K).coordRingMap L
            (cd.toAlgHom (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) :=
        CurveMap.CoordHom.baseChangeAlgHom_X cd L
      rw [hLx, hRx]
      have h3 : algebraMap (W.baseChange L).toAffine.CoordinateRing
          (W.baseChange L).toAffine.FunctionField
          ((⟨W.toAffine⟩ : SmoothPlaneCurve K).coordRingMap L
            (cd.toAlgHom (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X))) =
          (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L
            (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
              (cd.toAlgHom (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X))) :=
        (SmoothPlaneCurve.functionFieldMap_algebraMap
          (⟨W.toAffine⟩ : SmoothPlaneCurve K) L _).symm
      rw [h3]
      have h4 : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (cd.toAlgHom (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) =
          φ.toCurveMap.pullback (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) :=
        (cd.compat _).symm
      rw [h4]
      rfl
  · -- the root generator
    show ofEquationCoordRingHom (W.baseChange L) (W.baseChange L)
        (baseChangeXgen W φ L) (baseChangeYgen W φ L)
        (baseChange_generic_equation W φ L)
        (AdjoinRoot.root (W.baseChange L).toAffine.polynomial) =
      algebraMap (W.baseChange L).toAffine.CoordinateRing
        (W.baseChange L).toAffine.FunctionField
        (cd.baseChangeAlgHom L (AdjoinRoot.root (W.baseChange L).toAffine.polynomial))
    have hLy : ofEquationCoordRingHom (W.baseChange L) (W.baseChange L)
        (baseChangeXgen W φ L) (baseChangeYgen W φ L)
        (baseChange_generic_equation W φ L)
        (AdjoinRoot.root (W.baseChange L).toAffine.polynomial) =
        baseChangeYgen W φ L :=
      ofEquationCoordAlgHom_y (W.baseChange L) (W.baseChange L) (baseChangeXgen W φ L)
        (baseChangeYgen W φ L) (baseChange_generic_equation W φ L)
    have hRy : cd.baseChangeAlgHom L
        (AdjoinRoot.root (W.baseChange L).toAffine.polynomial) =
        (⟨W.toAffine⟩ : SmoothPlaneCurve K).coordRingMap L
          (cd.toAlgHom (AdjoinRoot.root W.toAffine.polynomial)) :=
      CurveMap.CoordHom.baseChangeAlgHom_root cd L
    rw [hLy, hRy]
    have h3 : algebraMap (W.baseChange L).toAffine.CoordinateRing
        (W.baseChange L).toAffine.FunctionField
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).coordRingMap L
          (cd.toAlgHom (AdjoinRoot.root W.toAffine.polynomial))) =
        (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (cd.toAlgHom (AdjoinRoot.root W.toAffine.polynomial))) :=
      (SmoothPlaneCurve.functionFieldMap_algebraMap
        (⟨W.toAffine⟩ : SmoothPlaneCurve K) L _).symm
    rw [h3]
    have h4 : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (cd.toAlgHom (AdjoinRoot.root W.toAffine.polynomial)) =
        φ.toCurveMap.pullback (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (AdjoinRoot.root W.toAffine.polynomial)) :=
      (cd.compat _).symm
    rw [h4]
    rfl

/-- **The base-changed coordinate-ring witness** (ISO-BC item 2): the
`baseChangeAlgHom` of `cd`, packaged with the `compat` field for the
base-changed isogeny. -/
noncomputable def baseChangeCoordHom [IsAlgClosed L] :
    (baseChangeIsogeny W φ L).toCurveMap.CoordHom where
  toAlgHom := cd.baseChangeAlgHom L
  compat := fun u' => by
    have h1 : (baseChangeIsogeny W φ L).toCurveMap.pullback
        (algebraMap (W.baseChange L).toAffine.CoordinateRing
          (W.baseChange L).toAffine.FunctionField u') =
        ofEquationCoordRingHom (W.baseChange L) (W.baseChange L)
          (baseChangeXgen W φ L) (baseChangeYgen W φ L)
          (baseChange_generic_equation W φ L) u' := by
      show ofEquationPullback (W.baseChange L) (W.baseChange L)
          (baseChangeXgen W φ L) (baseChangeYgen W φ L)
          (baseChange_generic_equation W φ L)
          (baseChangeXgen_transcendental W φ L)
          (algebraMap _ _ u') = _
      unfold ofEquationPullback
      rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
      rfl
    exact h1.trans (RingHom.congr_fun
      (ofEquationCoordRingHom_eq_algebraMap_comp_baseChangeAlgHom W φ L cd) u')

/-! ### The point-map compatibility through base change -/

/-- **The point-map compatibility** (ISO-BC item 4): the coordinatewise
inclusion `Affine.Point.map (algebraMap K L)` intertwines the point map of `φ`
with the point map of the base-changed isogeny.  On affine points this is the
evaluation naturality `evalAt_coordRingMap` applied to the two generator images
of `baseChangeAlgHom`. -/
theorem baseChange_toPointMap_compat [IsAlgClosed L] (P : W.toAffine.Point) :
    HasseWeil.Affine.Point.map (algebraMap K L) (FaithfulSMul.algebraMap_injective K L)
        (φ.toPointMap cd P) =
      (baseChangeIsogeny W φ L).toPointMap (baseChangeCoordHom W φ L cd)
        (HasseWeil.Affine.Point.map (algebraMap K L)
          (FaithfulSMul.algebraMap_injective K L) P) := by
  cases P with
  | zero => rfl
  | some x y h =>
    -- the generator images of the base-changed coordinate hom
    have hgenX : cd.baseChangeAlgHom L
        (algebraMap (Polynomial L) (W.baseChange L).toAffine.CoordinateRing Polynomial.X) =
        (⟨W.toAffine⟩ : SmoothPlaneCurve K).coordRingMap L
          (cd.toAlgHom (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) :=
      CurveMap.CoordHom.baseChangeAlgHom_X cd L
    have hgenY : cd.baseChangeAlgHom L
        (AdjoinRoot.root (W.baseChange L).toAffine.polynomial) =
        (⟨W.toAffine⟩ : SmoothPlaneCurve K).coordRingMap L
          (cd.toAlgHom (AdjoinRoot.root W.toAffine.polynomial)) :=
      CurveMap.CoordHom.baseChangeAlgHom_root cd L
    -- evaluation naturality at the two generators
    have hx : ((⟨W.toAffine⟩ : SmoothPlaneCurve K).baseChange L).evalAt
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).includePoint L ⟨x, y, h⟩)
        (cd.baseChangeAlgHom L
          (algebraMap (Polynomial L) (W.baseChange L).toAffine.CoordinateRing Polynomial.X)) =
        algebraMap K L ((⟨W.toAffine⟩ : SmoothPlaneCurve K).evalAt ⟨x, y, h⟩
          (cd.toAlgHom (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X))) := by
      rw [hgenX]
      exact SmoothPlaneCurve.evalAt_coordRingMap (⟨W.toAffine⟩ : SmoothPlaneCurve K) L
        ⟨x, y, h⟩ (cd.toAlgHom (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X))
    have hy : ((⟨W.toAffine⟩ : SmoothPlaneCurve K).baseChange L).evalAt
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).includePoint L ⟨x, y, h⟩)
        (cd.baseChangeAlgHom L (AdjoinRoot.root (W.baseChange L).toAffine.polynomial)) =
        algebraMap K L ((⟨W.toAffine⟩ : SmoothPlaneCurve K).evalAt ⟨x, y, h⟩
          (cd.toAlgHom (AdjoinRoot.root W.toAffine.polynomial))) := by
      rw [hgenY]
      exact SmoothPlaneCurve.evalAt_coordRingMap (⟨W.toAffine⟩ : SmoothPlaneCurve K) L
        ⟨x, y, h⟩ (cd.toAlgHom (AdjoinRoot.root W.toAffine.polynomial))
    -- assemble the two coordinate identities into the point identity
    have hsome : ∀ (x₁ y₁ x₂ y₂ : L) (h₁ : (W.baseChange L).toAffine.Nonsingular x₁ y₁)
        (h₂ : (W.baseChange L).toAffine.Nonsingular x₂ y₂), x₁ = x₂ → y₁ = y₂ →
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : (W.baseChange L).toAffine.Point) =
          WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ := by
      rintro x₁ y₁ x₂ y₂ h₁ h₂ rfl rfl; rfl
    exact hsome _ _ _ _ _ _ hx.symm hy.symm

end HasseWeil.EC.Isogeny
