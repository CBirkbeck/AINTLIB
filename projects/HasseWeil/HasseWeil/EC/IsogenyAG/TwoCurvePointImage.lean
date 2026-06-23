/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.TwoCurveGenericCovariance
import HasseWeil.EC.IsogenyOrdTransport
import HasseWeil.LocalExpansion

/-!
# The CoordHom-free geometric point map of a separable two-curve isogeny (PE-1, route A)

For a separable two-curve isogeny `φ : Isogeny W₁ W₂` over an algebraically closed base,
this file builds the **CoordHom-free** geometric point map by *place restriction*: a smooth
point `P` of `E₁` has a place `pointValuation P` on `K(E₁)`; pulling it back along
`φ.pullback : K(E₂) → K(E₁)` gives the comap valuation `(pointValuation P).comap φ.pullback`
on `K(E₂)`.  Away from the affine kernel (and the point at infinity), this comap valuation is
again a *point* valuation `pointValuation Q` for a unique smooth point `Q` of `E₂`, and we set
`φ(P) := Q`.  The affine kernel and the point at infinity go into the `bad` set (there the
restricted place is the place at infinity of `E₂`, i.e. `φ(P) = O`).

The mathematical content of the **`PullbackEvaluation_twoCurve` coherence** is then
near-tautological: the value at `P` of the pulled-back generator `φ^*(x_gen₂)` *is*, by the
place-equality, the value of `x_gen₂` at `Q`, which is `Q.x`.  This is
`twoCurve_evaluatesTo_of_comap_eq` below.

## Design (honest reduction)

This file builds the foundation along two complementary, **entirely sorry-free**, axiom-clean
reductions; the only genuine remaining inputs are the **group-homomorphism property** of the
point map (Silverman III.4.8, the CoordHom-free case) and the **stored-point-map agreement**.

**Route I (place-equality interface).**  The genuine algebraic-geometric step — that the comap
valuation of a *finite* place along a separable, affine-kernel pullback is again a *finite*
place (a point of `E₂`) — is the forward place↔point dictionary; the project has it CoordHom-
free only for the *fibre* direction (`Curves/LocalizedDictionary.lean`).  It is isolated as the
record `TwoCurvePlaceData φ bad`, packaging for each good `P` the witnessing point `Q` and the
place-equality `(pointValuation P).comap φ.pullback = pointValuation Q`.  Given the record,
`pullbackEvaluation_twoCurve_of_placeData` assembles `PullbackEvaluation_twoCurve` (Phases 2-3).

**Route II (constructive, place-equality FREE).**  Off the (finite, `twoCurvePoleLocus_finite`)
pole locus, both pulled-back generators are regular, so their **residue values** exist
(`exists_evaluatesTo_of_pointValuation_le_one`, Phase 4c) and **form a point of `E₂`**
(`twoCurve_equation_of_evaluatesTo` + `nonsingular_of_evaluatesTo_generators`, Phase 5).  So
the place-restriction image `φ(P)` is *constructed*, not assumed; the only residual tie to the
stored point map is the residue-value agreement (`pullbackEvaluation_twoCurve_of_residue_agreement`),
which the genuine place-restriction point map satisfies by construction.  This route reduces the
coherence to the **single** geometric input III.4.8 (the point map is a group hom).

`placeRestrictionIsogeny` packages a point map into a `HasseWeil.Isogeny` with III.4.8 supplied
as the named hypothesis `hgrouphom` (Phase 4b).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, II.2.5, III.4.8, III.4.10(b,c).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### Phase 1 — the generic coordinates evaluate to a point's own coordinates -/

variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- The `x`-generator evaluates at a smooth point `Q` to its own `x`-coordinate. -/
theorem evaluatesTo_x_gen_self (Q : (W_smooth W).SmoothPoint) :
    EvaluatesTo W Q (x_gen W) Q.x := by
  -- `x_gen W − Q.x = algebraMap (X − Q.x)`, and `X − Q.x ∈ maximalIdealAt Q`.
  have hx : (W_smooth W).evalAt Q
      (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X) = Q.x := by
    rw [show algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X =
      WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
        (Polynomial.C Polynomial.X) from rfl]
    exact (W_smooth W).evalAt_x Q
  have h0 : (W_smooth W).evalAt Q
      (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X -
        algebraMap F W.toAffine.CoordinateRing Q.x) = 0 :=
    (map_sub ((W_smooth W).evalAt Q) _ _).trans
      (by rw [hx]; exact sub_eq_zero_of_eq ((W_smooth W).evalAt_algebraMap Q Q.x).symm)
  have hmem : (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X -
      algebraMap F W.toAffine.CoordinateRing Q.x) ∈ (W_smooth W).maximalIdealAt Q :=
    (W_smooth W).ker_evalAt Q ▸ RingHom.mem_ker.mpr h0
  -- transport membership to the valuation statement
  have hrw : x_gen W - algebraMap F (W.toAffine.FunctionField) Q.x =
      algebraMap W.toAffine.CoordinateRing (W.toAffine.FunctionField)
        (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X -
          algebraMap F W.toAffine.CoordinateRing Q.x) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply]
    rfl
  unfold EvaluatesTo
  rw [hrw]
  exact (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
    (C := W_smooth W) _ Q).mpr hmem

/-- The `y`-generator evaluates at a smooth point `Q` to its own `y`-coordinate. -/
theorem evaluatesTo_y_gen_self (Q : (W_smooth W).SmoothPoint) :
    EvaluatesTo W Q (y_gen W) Q.y := by
  have hy : (W_smooth W).evalAt Q (AdjoinRoot.root W.toAffine.polynomial) = Q.y := by
    rw [show AdjoinRoot.root W.toAffine.polynomial =
      WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X from rfl]
    exact (W_smooth W).evalAt_y Q
  have h0 : (W_smooth W).evalAt Q
      (AdjoinRoot.root W.toAffine.polynomial -
        algebraMap F W.toAffine.CoordinateRing Q.y) = 0 :=
    (map_sub ((W_smooth W).evalAt Q) _ _).trans
      (by rw [hy]; exact sub_eq_zero_of_eq ((W_smooth W).evalAt_algebraMap Q Q.y).symm)
  have hmem : (AdjoinRoot.root W.toAffine.polynomial -
      algebraMap F W.toAffine.CoordinateRing Q.y) ∈ (W_smooth W).maximalIdealAt Q :=
    (W_smooth W).ker_evalAt Q ▸ RingHom.mem_ker.mpr h0
  have hrw : y_gen W - algebraMap F (W.toAffine.FunctionField) Q.y =
      algebraMap W.toAffine.CoordinateRing (W.toAffine.FunctionField)
        (AdjoinRoot.root W.toAffine.polynomial -
          algebraMap F W.toAffine.CoordinateRing Q.y) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply]
    rfl
  unfold EvaluatesTo
  rw [hrw]
  exact (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
    (C := W_smooth W) _ Q).mpr hmem

/-! ### Phase 2 — the place-restriction coherence

The crux of route A: *given* the place-equality
`(pointValuation P).comap φ.pullback = pointValuation Q`, the value at `P` of any pulled-back
function `φ^* f` equals the value of `f` at `Q`.  This is an exact valuation identity (no
fraction decomposition, unlike the single-curve `PullbackEvaluation.pullback_evaluatesTo`),
since `φ^*` is an `F`-algebra hom and the comap of `pointValuation P` along it *is*
`pointValuation Q`. -/

variable {W₁ W₂ : WeierstrassCurve F} [W₁.toAffine.IsElliptic] [W₂.toAffine.IsElliptic]

/-- **The place-restriction coherence (general function).**  If the comap of `P`'s place
along `φ.pullback` is `Q`'s place, then `φ^* f` takes at `P` the value `f` takes at `Q`. -/
theorem twoCurve_evaluatesTo_of_comap_eq
    (φ : HasseWeil.Isogeny W₁ W₂)
    {P : (W_smooth W₁).SmoothPoint} {Q : (W_smooth W₂).SmoothPoint}
    (hcomap : ((W_smooth W₁).pointValuation P).comap φ.pullback.toRingHom =
      (W_smooth W₂).pointValuation Q)
    {f : W₂.toAffine.FunctionField} {c : F} (hf : EvaluatesTo W₂ Q f c) :
    EvaluatesTo W₁ P (φ.pullback f) c := by
  -- `φ^* f − c = φ^*(f − c)` since `φ^*` fixes the constants.
  have hsub : φ.pullback f - algebraMap F W₁.toAffine.FunctionField c =
      φ.pullback (f - algebraMap F W₂.toAffine.FunctionField c) := by
    rw [map_sub, φ.pullback.commutes c]
  unfold EvaluatesTo
  rw [hsub]
  -- the value of `φ^*(f − c)` at `P` is the comap value, i.e. the value of `f − c` at `Q`.
  have hval : (W_smooth W₁).pointValuation P
      (φ.pullback (f - algebraMap F W₂.toAffine.FunctionField c)) =
      (W_smooth W₂).pointValuation Q (f - algebraMap F W₂.toAffine.FunctionField c) := by
    have hca := Valuation.comap_apply φ.pullback.toRingHom
      ((W_smooth W₁).pointValuation P) (f - algebraMap F W₂.toAffine.FunctionField c)
    rw [hcomap] at hca
    exact hca.symm
  rw [hval]
  exact hf

/-- **The place-restriction coherence for the `x`-generator**: at a good `P` with image `Q`,
`φ^*(x_gen₂)` evaluates at `P` to `Q.x`. -/
theorem twoCurve_evaluatesTo_x_gen_of_comap_eq
    (φ : HasseWeil.Isogeny W₁ W₂)
    {P : (W_smooth W₁).SmoothPoint} {Q : (W_smooth W₂).SmoothPoint}
    (hcomap : ((W_smooth W₁).pointValuation P).comap φ.pullback.toRingHom =
      (W_smooth W₂).pointValuation Q) :
    EvaluatesTo W₁ P (φ.pullback (x_gen W₂)) Q.x :=
  twoCurve_evaluatesTo_of_comap_eq φ hcomap (evaluatesTo_x_gen_self W₂ Q)

/-- **The place-restriction coherence for the `y`-generator**. -/
theorem twoCurve_evaluatesTo_y_gen_of_comap_eq
    (φ : HasseWeil.Isogeny W₁ W₂)
    {P : (W_smooth W₁).SmoothPoint} {Q : (W_smooth W₂).SmoothPoint}
    (hcomap : ((W_smooth W₁).pointValuation P).comap φ.pullback.toRingHom =
      (W_smooth W₂).pointValuation Q) :
    EvaluatesTo W₁ P (φ.pullback (y_gen W₂)) Q.y :=
  twoCurve_evaluatesTo_of_comap_eq φ hcomap (evaluatesTo_y_gen_self W₂ Q)

/-! ### Phase 3 — the place-restriction data and the `PullbackEvaluation_twoCurve` witness

`TwoCurvePlaceData φ bad` is the **honest interface** for route A: for every smooth point `P`
of `E₁` *off* `bad`, it produces the place-restriction image `Q = φ(P)` together with

* the place-equality `(pointValuation P).comap φ.pullback = pointValuation Q` (the heart of the
  forward place↔point dictionary — the genuine algebraic-geometric input, isolated here), and
* the agreement `φ.toAddMonoidHom P.toAffinePoint = Q.toAffinePoint` of the stored point map
  with that image.

`bad` collects the affine kernel (where the restricted place is the place at infinity of `E₂`,
so `φ(P) = O` and there is no affine image) and the point at infinity of `E₁`.  *Given* this
record, `PullbackEvaluation_twoCurve` is sorry-free (Phase 2 + `evaluatesTo_*_gen_self`). -/

/-- **The place-restriction data** of a two-curve isogeny `φ`, with excluded set `bad`.
For each good `P` it records the place-restriction image point and the two witnessing
identities (place-equality + stored-point-map agreement). -/
structure TwoCurvePlaceData (φ : HasseWeil.Isogeny W₁ W₂)
    (bad : Set (W_smooth W₁).SmoothPoint) : Prop where
  /-- For every good `P`, there is an image point `Q` of `E₂` whose place is the restriction
  of `P`'s place along `φ.pullback`, and the stored point map sends `P` to `Q`. -/
  exists_image : ∀ P : (W_smooth W₁).SmoothPoint, P ∉ bad →
    ∃ Q : (W_smooth W₂).SmoothPoint,
      ((W_smooth W₁).pointValuation P).comap φ.pullback.toRingHom =
        (W_smooth W₂).pointValuation Q ∧
      φ.toAddMonoidHom P.toAffinePoint = Q.toAffinePoint

/-- **`PullbackEvaluation_twoCurve` from the place-restriction data** (PE-1a, the
near-tautological coherence).  Given `TwoCurvePlaceData φ bad`, the two-curve cofinite
pullback-evaluation witness holds with the same `bad`: at every good `P`, the stored point map
lands at the affine image `Q = φ(P)`, and the pulled-back generators `φ^* x_gen₂`, `φ^* y_gen₂`
evaluate at `P` to `Q.x`, `Q.y` (Phase 2). -/
theorem pullbackEvaluation_twoCurve_of_placeData
    (φ : HasseWeil.Isogeny W₁ W₂) {bad : Set (W_smooth W₁).SmoothPoint}
    (hdata : TwoCurvePlaceData φ bad) :
    PullbackEvaluation_twoCurve W₁ W₂ φ bad := by
  intro P hP
  obtain ⟨Q, hcomap, hmap⟩ := hdata.exists_image P hP
  refine ⟨Q.x, Q.y, Q.nonsingular, ?_, ?_, ?_⟩
  · -- the stored point map lands at the affine image `Q`
    rw [hmap]
    rfl
  · exact twoCurve_evaluatesTo_x_gen_of_comap_eq φ hcomap
  · exact twoCurve_evaluatesTo_y_gen_of_comap_eq φ hcomap

/-! ### Phase 4a — the canonical finite bad set (pole locus of the pulled-back generators)

The place-restriction map is defined where both pulled-back generators `φ^* x_gen₂`,
`φ^* y_gen₂` are *regular* (no pole), i.e. off the **pole locus**.  Silverman II.1.2
(`finite_setOf_ord_P_nonzero`) makes this locus finite.  This concretizes the `bad` set of
`TwoCurvePlaceData`: the affine kernel (the genuine geometric bad locus, where `φ(P) = O`)
is contained in this finite pole locus, since `φ^*(x_gen₂)` has a pole exactly at the
preimage of `O`. -/

/-- **The pole locus of the pulled-back generators**: the points of `E₁` at which `φ^* x_gen₂`
or `φ^* y_gen₂` is not regular. -/
def twoCurvePoleLocus (φ : HasseWeil.Isogeny W₁ W₂) :
    Set (W_smooth W₁).SmoothPoint :=
  {P | ¬ (W_smooth W₁).pointValuation P (φ.pullback (x_gen W₂)) ≤ 1} ∪
  {P | ¬ (W_smooth W₁).pointValuation P (φ.pullback (y_gen W₂)) ≤ 1}

/-- **The pole locus is finite** (Silverman II.1.2): the pole locus of either pulled-back
generator is contained in its zero/pole set `{P | ord_P ≠ 0}`, which is finite. -/
theorem twoCurvePoleLocus_finite (φ : HasseWeil.Isogeny W₁ W₂) :
    (twoCurvePoleLocus φ).Finite := by
  have hx0 : φ.pullback (x_gen W₂) ≠ 0 := fun h =>
    x_gen_ne_zero W₂ (φ.pullback_injective (h.trans (map_zero _).symm))
  have hy0 : φ.pullback (y_gen W₂) ≠ 0 := fun h =>
    y_gen_ne_zero W₂ (φ.pullback_injective (h.trans (map_zero _).symm))
  -- each component sits inside the (finite) zero/pole set of that generator
  have hsubX : {P : (W_smooth W₁).SmoothPoint |
      ¬ (W_smooth W₁).pointValuation P (φ.pullback (x_gen W₂)) ≤ 1} ⊆
      {P | (W_smooth W₁).ord_P P (φ.pullback (x_gen W₂)) ≠ 0} := by
    intro P hP
    rw [Set.mem_setOf_eq] at hP ⊢
    intro hord
    exact hP (le_of_eq (((W_smooth W₁).ord_P_eq_zero_iff_pointValuation_eq_one hx0).mp hord))
  have hsubY : {P : (W_smooth W₁).SmoothPoint |
      ¬ (W_smooth W₁).pointValuation P (φ.pullback (y_gen W₂)) ≤ 1} ⊆
      {P | (W_smooth W₁).ord_P P (φ.pullback (y_gen W₂)) ≠ 0} := by
    intro P hP
    rw [Set.mem_setOf_eq] at hP ⊢
    intro hord
    exact hP (le_of_eq (((W_smooth W₁).ord_P_eq_zero_iff_pointValuation_eq_one hy0).mp hord))
  exact (((W_smooth W₁).finite_setOf_ord_P_nonzero hx0).subset hsubX).union
    (((W_smooth W₁).finite_setOf_ord_P_nonzero hy0).subset hsubY)

/-! ### Phase 4b — packaging the place-restriction point map into a `HasseWeil.Isogeny`

Given the place-restriction data and a choice of point map, we package a `HasseWeil.Isogeny`
whose `pullback` is `φ.pullback` and whose `toAddMonoidHom` realizes the place-restriction map.
The two-curve `PullbackEvaluation` coherence is inherited from
`pullbackEvaluation_twoCurve_of_placeData`.

The single deferred input is the **group-homomorphism property** of the place-restriction map
(Silverman III.4.8, the CoordHom-free case): that `P ↦ φ(P)` respects addition and the
basepoint.  This is the project's standing geometric-realization wall for a *general*
isogeny — proven elsewhere only for `[n]` (the division-polynomial coordinate formula, where
hom-ness is free from `zsmul`) and for `1 − π` (the addition formula).  It is supplied here as
the named hypothesis `hgrouphom`, NOT discharged. -/

/-- **Packaging the place-restriction realization into a `HasseWeil.Isogeny`**.  Given the
function-field pullback `pb : K(E₂) →ₐ K(E₁)` and a point map `pointMap : E₁ → E₂` that is a
group hom (`hgrouphom`), bundle the `Isogeny`.  This is the data-level packaging; the
geometric coherence (`PullbackEvaluation_twoCurve`) is established separately, from the
place-restriction data, via `pullbackEvaluation_twoCurve_of_placeData`. -/
noncomputable def placeRestrictionIsogeny
    (pb : W₂.toAffine.FunctionField →ₐ[F] W₁.toAffine.FunctionField)
    (pointMap : W₁.toAffine.Point → W₂.toAffine.Point)
    (hgrouphom : ∀ P Q : W₁.toAffine.Point,
      pointMap (P + Q) = pointMap P + pointMap Q)
    (hzero : pointMap 0 = 0) :
    HasseWeil.Isogeny W₁ W₂ where
  pullback := pb
  toAddMonoidHom :=
    { toFun := pointMap
      map_zero' := hzero
      map_add' := hgrouphom }

@[simp] theorem placeRestrictionIsogeny_pullback
    (pb : W₂.toAffine.FunctionField →ₐ[F] W₁.toAffine.FunctionField)
    (pointMap : W₁.toAffine.Point → W₂.toAffine.Point)
    (hgrouphom : ∀ P Q : W₁.toAffine.Point,
      pointMap (P + Q) = pointMap P + pointMap Q)
    (hzero : pointMap 0 = 0) :
    (placeRestrictionIsogeny pb pointMap hgrouphom hzero).pullback = pb := rfl

@[simp] theorem placeRestrictionIsogeny_toAddMonoidHom_apply
    (pb : W₂.toAffine.FunctionField →ₐ[F] W₁.toAffine.FunctionField)
    (pointMap : W₁.toAffine.Point → W₂.toAffine.Point)
    (hgrouphom : ∀ P Q : W₁.toAffine.Point,
      pointMap (P + Q) = pointMap P + pointMap Q)
    (hzero : pointMap 0 = 0) (P : W₁.toAffine.Point) :
    (placeRestrictionIsogeny pb pointMap hgrouphom hzero).toAddMonoidHom P = pointMap P := rfl

/-! ### Phase 4c — residue values exist (toward eliminating the place-equality assumption)

The forward place-restriction `Q = φ(P)` should be *constructed* from `P`, not assumed.  Its
coordinates are the **residue values** at `P` of the (regular) pulled-back generators.  This
section supplies the residue-value existence — a regular function at a smooth point over an
algebraically closed base has a value — which is the gateway to the constructive route (the
remaining step being that those two values form a point on `E₂`, by `EvaluatesTo`-arithmetic
through the Weierstrass equation; see the closing report). -/

/-- **A coordinate-ring element evaluates to its residue value.**  For `r ∈ F[E]` and a smooth
point `P`, the function `algebraMap r ∈ K(E)` takes at `P` the residue value `evalAt P r`. -/
theorem evaluatesTo_algebraMap_coordinateRing
    (r : (W_smooth W).CoordinateRing) (P : (W_smooth W).SmoothPoint) :
    EvaluatesTo W P
      (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField r)
      ((W_smooth W).evalAt P r) := by
  -- `r − evalAt r ∈ ker evalAt = maximalIdealAt P`, so its image vanishes at `P`.
  have h0 : (W_smooth W).evalAt P
      (r - algebraMap F (W_smooth W).CoordinateRing ((W_smooth W).evalAt P r)) = 0 :=
    (map_sub ((W_smooth W).evalAt P) _ _).trans
      (by rw [(W_smooth W).evalAt_algebraMap P ((W_smooth W).evalAt P r), sub_self])
  have hmem : r - algebraMap F (W_smooth W).CoordinateRing ((W_smooth W).evalAt P r) ∈
      (W_smooth W).maximalIdealAt P :=
    (W_smooth W).ker_evalAt P ▸ RingHom.mem_ker.mpr h0
  have hrw : algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField r -
      algebraMap F (W_smooth W).FunctionField ((W_smooth W).evalAt P r) =
      algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField
        (r - algebraMap F (W_smooth W).CoordinateRing ((W_smooth W).evalAt P r)) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply]
  show (W_smooth W).pointValuation P (_ - algebraMap F (W_smooth W).FunctionField _) < 1
  rw [hrw]
  exact (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
    (C := W_smooth W) _ P).mpr hmem

/-- **Good-fraction representation** (Fintype-free, mirroring the private helper of
`CovarianceDischarge`): a function regular at `P` is `algebraMap a / algebraMap s` with the
denominator `s` not vanishing at `P`. -/
theorem exists_mul_algebraMap_eq_of_regular
    {f : (W_smooth W).FunctionField} {P : (W_smooth W).SmoothPoint}
    (hf : (W_smooth W).pointValuation P f ≤ 1) :
    ∃ a s : (W_smooth W).CoordinateRing, s ∉ (W_smooth W).maximalIdealAt P ∧
      f * algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField s =
        algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField a := by
  obtain ⟨xL, hxL⟩ :=
    Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one f hf
  obtain ⟨a, s, hmk⟩ :=
    IsLocalization.exists_mk'_eq ((W_smooth W).maximalIdealAt P).primeCompl xL
  refine ⟨a, (s : (W_smooth W).CoordinateRing), s.prop, ?_⟩
  have h2 : algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField
        (IsLocalization.mk' ((W_smooth W).localRingAt P) a s) *
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField
        (algebraMap (W_smooth W).CoordinateRing ((W_smooth W).localRingAt P)
          (s : (W_smooth W).CoordinateRing)) =
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField
        (algebraMap (W_smooth W).CoordinateRing ((W_smooth W).localRingAt P) a) :=
    (map_mul (algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField) _ _).symm.trans
      (congrArg (algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField)
        (IsLocalization.mk'_spec ((W_smooth W).localRingAt P) a s))
  rw [hmk, hxL,
    ← IsScalarTower.algebraMap_apply (W_smooth W).CoordinateRing ((W_smooth W).localRingAt P)
      (W_smooth W).FunctionField,
    ← IsScalarTower.algebraMap_apply (W_smooth W).CoordinateRing ((W_smooth W).localRingAt P)
      (W_smooth W).FunctionField] at h2
  exact h2

/-- **Residue-value existence** (Silverman II.1, residue field `= F` over `F̄`): every function
`f ∈ K(E)` that is *regular* at a smooth point `P` (`pointValuation P f ≤ 1`) has a value
`c ∈ F` there, `EvaluatesTo W P f c`.

Proof: write `f = algebraMap a / algebraMap s` with `s` not vanishing at `P`
(`exists_mul_algebraMap_eq_of_regular`).  Numerator and denominator evaluate to their residues
(`evaluatesTo_algebraMap_coordinateRing`), with `evalAt P s ≠ 0`, so `EvaluatesTo.div` gives
the value `evalAt P a / evalAt P s`. -/
theorem exists_evaluatesTo_of_pointValuation_le_one
    {f : (W_smooth W).FunctionField} {P : (W_smooth W).SmoothPoint}
    (hf : (W_smooth W).pointValuation P f ≤ 1) :
    ∃ c : F, EvaluatesTo W P f c := by
  obtain ⟨a, s, hsm, hfrac⟩ := exists_mul_algebraMap_eq_of_regular W hf
  have hsval : (W_smooth W).evalAt P s ≠ 0 := fun hc =>
    hsm ((W_smooth W).ker_evalAt P ▸ RingHom.mem_ker.mpr hc)
  have hsne : algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField s ≠ 0 :=
    fun hc => by
      have : s = 0 :=
        IsFractionRing.injective (W_smooth W).CoordinateRing (W_smooth W).FunctionField
          (hc.trans (map_zero _).symm)
      exact hsm (this ▸ Ideal.zero_mem _)
  refine ⟨(W_smooth W).evalAt P a / (W_smooth W).evalAt P s, ?_⟩
  have hfdiv : f = algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField a /
      algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField s :=
    (eq_div_iff hsne).mpr hfrac
  show EvaluatesTo W P f _
  rw [hfdiv]
  exact (evaluatesTo_algebraMap_coordinateRing W a P).div
    (evaluatesTo_algebraMap_coordinateRing W s P) hsval

/-! ### Phase 5 — the residue values lie on `E₂` (the constructive coherence, place-equality-free)

The keystone of the constructive route: if both pulled-back generators `φ^* x_gen₂`,
`φ^* y_gen₂` evaluate at `P` to values `cx`, `cy` (which exist by Phase 4c when `P` is off the
pole locus), then `(cx, cy)` is a point of `E₂` — it satisfies the Weierstrass equation.  The
proof is the two-curve analogue of `CovarianceDischarge.pullback_mk_evaluatesTo`: the pullback
of any coordinate-ring element `mk p` of `E₂` evaluates at `P` to `p(cx, cy)`; specialising to
`p = W₂.polynomial` (which is `0` in `F[E₂]`) gives `W₂.polynomial.evalEval cx cy = 0`. -/

/-- **Two-curve polynomial evaluation transport**: from the two generator evaluations
`φ^* x_gen₂ ↦ cx`, `φ^* y_gen₂ ↦ cy` at `P`, the pullback of every coordinate-ring element
`mk_{E₂} p` evaluates at `P` to `p(cx, cy)`.  Double polynomial induction through `EvaluatesTo`
arithmetic (the two-curve analogue of `CovarianceDischarge.pullback_mk_evaluatesTo`). -/
theorem twoCurve_pullback_mk_evaluatesTo
    (φ : HasseWeil.Isogeny W₁ W₂) {P : (W_smooth W₁).SmoothPoint} {cx cy : F}
    (hx : EvaluatesTo W₁ P (φ.pullback (x_gen W₂)) cx)
    (hy : EvaluatesTo W₁ P (φ.pullback (y_gen W₂)) cy)
    (p : Polynomial (Polynomial F)) :
    EvaluatesTo W₁ P
      (φ.pullback (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField
        (AdjoinRoot.mk W₂.toAffine.polynomial p)))
      (p.evalEval cx cy) := by
  have hxAtom : EvaluatesTo W₁ P (φ.pullback (algebraMap W₂.toAffine.CoordinateRing
      W₂.toAffine.FunctionField
      (AdjoinRoot.mk W₂.toAffine.polynomial (Polynomial.C Polynomial.X)))) cx := hx
  have hyAtom : EvaluatesTo W₁ P (φ.pullback (algebraMap W₂.toAffine.CoordinateRing
      W₂.toAffine.FunctionField
      (AdjoinRoot.mk W₂.toAffine.polynomial Polynomial.X))) cy := hy
  induction p using Polynomial.induction_on with
  | C q =>
    rw [Polynomial.evalEval_C]
    induction q using Polynomial.induction_on with
    | C c =>
      have h1 : algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField
          (AdjoinRoot.mk W₂.toAffine.polynomial (Polynomial.C (Polynomial.C c))) =
          algebraMap F W₂.toAffine.FunctionField c := by
        rw [show AdjoinRoot.mk W₂.toAffine.polynomial (Polynomial.C (Polynomial.C c)) =
          algebraMap F W₂.toAffine.CoordinateRing c from rfl,
          ← IsScalarTower.algebraMap_apply F W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField]
      rw [Polynomial.eval_C, h1, φ.pullback.commutes c]
      exact evaluatesTo_algebraMap P c
    | add q₁ q₂ ih₁ ih₂ =>
      simp only [map_add, Polynomial.eval_add] at ih₁ ih₂ ⊢
      exact ih₁.add ih₂
    | monomial k c ih =>
      rw [show (Polynomial.C c * Polynomial.X ^ (k + 1) : Polynomial F) =
        Polynomial.C c * Polynomial.X ^ k * Polynomial.X by rw [pow_succ, ← mul_assoc]]
      simp only [map_mul, Polynomial.eval_mul, Polynomial.eval_X] at ih ⊢
      exact ih.mul hxAtom
  | add p₁ p₂ ih₁ ih₂ =>
    simp only [map_add, Polynomial.evalEval_add] at ih₁ ih₂ ⊢
    exact ih₁.add ih₂
  | monomial k q ih =>
    rw [show (Polynomial.C q * Polynomial.X ^ (k + 1) : Polynomial (Polynomial F)) =
      Polynomial.C q * Polynomial.X ^ k * Polynomial.X by rw [pow_succ, ← mul_assoc]]
    simp only [map_mul, Polynomial.evalEval_mul, Polynomial.evalEval_X] at ih ⊢
    exact ih.mul hyAtom

/-- **The residue values satisfy the Weierstrass equation of `E₂`** (the constructive
nonsingularity input, *place-equality free*).  If both pulled-back generators evaluate at `P`
to `cx`, `cy`, then `(cx, cy)` lies on `E₂`.  Specialise `twoCurve_pullback_mk_evaluatesTo` to
`p = W₂.polynomial`: the function is `φ^* 0 = 0`, evaluating to both `0` and
`W₂.polynomial.evalEval cx cy`; uniqueness gives the equation. -/
theorem twoCurve_equation_of_evaluatesTo
    (φ : HasseWeil.Isogeny W₁ W₂) {P : (W_smooth W₁).SmoothPoint} {cx cy : F}
    (hx : EvaluatesTo W₁ P (φ.pullback (x_gen W₂)) cx)
    (hy : EvaluatesTo W₁ P (φ.pullback (y_gen W₂)) cy) :
    W₂.toAffine.Equation cx cy := by
  -- the pullback of `mk W₂.polynomial = 0` evaluates at `P` to `W₂.polynomial.evalEval cx cy`
  have h := twoCurve_pullback_mk_evaluatesTo φ hx hy W₂.toAffine.polynomial
  rw [show (AdjoinRoot.mk W₂.toAffine.polynomial W₂.toAffine.polynomial :
      W₂.toAffine.CoordinateRing) = 0 from AdjoinRoot.mk_self,
    map_zero, map_zero] at h
  -- it also evaluates to `0` (the zero function)
  have h0 : EvaluatesTo W₁ P (0 : W₁.toAffine.FunctionField) 0 := by
    have := evaluatesTo_algebraMap (W := W₁) P (0 : F)
    rwa [map_zero] at this
  -- uniqueness of the value forces `W₂.polynomial.evalEval cx cy = 0`, i.e. the equation
  exact (h0.unique h).symm

/-! ### Phase 5 capstone — the place-equality-free coherence

Assembling Phases 4c + 5: at a good `P` (off the pole locus), the residue values `cx`, `cy` of
the pulled-back generators *exist* and *form a point of `E₂`*.  So the only remaining tie to the
stored point map is the (definitional, once the point map is the place-restriction map)
agreement `φ.toAddMonoidHom P.toAffinePoint = some cx cy`.  This is the
`TwoCurvePlaceData`-free interface: it carries no place-equality, only the residue-value
agreement, which the genuine place-restriction point map satisfies by construction. -/

/-- **`PullbackEvaluation_twoCurve` from the residue-value agreement** (place-equality free).
Given `φ`, and a hypothesis `hagree` that off the (finite) pole locus the stored point map
sends `P` to the *finite* point `(cx, cy)` whose coordinates are the residue values of the two
pulled-back generators, the two-curve cofinite pullback-evaluation witness holds with `bad`
the pole locus.  The image point's nonsingularity is automatic (`twoCurve_equation_of_evaluatesTo`
+ `equation_iff_nonsingular`); the generator evaluations are the residue values themselves. -/
theorem pullbackEvaluation_twoCurve_of_residue_agreement
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hagree : ∀ P : (W_smooth W₁).SmoothPoint, P ∉ twoCurvePoleLocus φ →
      ∀ cx cy : F,
        EvaluatesTo W₁ P (φ.pullback (x_gen W₂)) cx →
        EvaluatesTo W₁ P (φ.pullback (y_gen W₂)) cy →
        ∃ h' : W₂.toAffine.Nonsingular cx cy,
          φ.toAddMonoidHom P.toAffinePoint = Affine.Point.some cx cy h') :
    PullbackEvaluation_twoCurve W₁ W₂ φ (twoCurvePoleLocus φ) := by
  intro P hP
  -- off the pole locus, both generators are regular, so their residue values exist
  have hxreg : (W_smooth W₁).pointValuation P (φ.pullback (x_gen W₂)) ≤ 1 := by
    by_contra hc; exact hP (Set.mem_union_left _ hc)
  have hyreg : (W_smooth W₁).pointValuation P (φ.pullback (y_gen W₂)) ≤ 1 := by
    by_contra hc; exact hP (Set.mem_union_right _ hc)
  obtain ⟨cx, hcx⟩ := exists_evaluatesTo_of_pointValuation_le_one W₁ hxreg
  obtain ⟨cy, hcy⟩ := exists_evaluatesTo_of_pointValuation_le_one W₁ hyreg
  -- the residue values form a point of `E₂`, and the stored map agrees
  obtain ⟨h', hmap⟩ := hagree P hP cx cy hcx hcy
  exact ⟨cx, cy, h', hmap, hcx, hcy⟩

/-- **Nonsingularity of the residue-value point** (over `F̄`, elliptic): the residue values of
the pulled-back generators always satisfy the nonsingularity condition of `E₂`, so the only
content of `hagree` above is the *point-map agreement*, never the nonsingularity. -/
theorem nonsingular_of_evaluatesTo_generators [IsAlgClosed F]
    (φ : HasseWeil.Isogeny W₁ W₂) {P : (W_smooth W₁).SmoothPoint} {cx cy : F}
    (hx : EvaluatesTo W₁ P (φ.pullback (x_gen W₂)) cx)
    (hy : EvaluatesTo W₁ P (φ.pullback (y_gen W₂)) cy) :
    W₂.toAffine.Nonsingular cx cy :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (twoCurve_equation_of_evaluatesTo φ hx hy)

/-! ### Phase 6 — the concrete place-restriction point map (TASK A)

We now build the **concrete total point map** `placeRestrictionPointMap φ : E₁ → E₂` and prove,
sorry-free, the `PullbackEvaluation_twoCurve` coherence for it (with `bad = twoCurvePoleLocus φ`).
This makes the realization concrete and reduces PE-1 to *exactly* the group-hom property of
`placeRestrictionPointMap` (TASK B).

The map is:
* `O ↦ O` (the point at infinity);
* an affine smooth `P = (x, y)` whose `SmoothPoint` `⟨x, y, h⟩` lies in the affine kernel
  (`twoCurvePoleLocus φ`, where the pulled-back generators have poles) `↦ O`;
* an affine smooth `P = (x, y)` *off* the pole locus `↦` the **residue-value point**
  `(cx, cy)` of the regular pulled-back generators (`exists_evaluatesTo_of_pointValuation_le_one`),
  which is a point of `E₂` (`twoCurve_equation_of_evaluatesTo` / `nonsingular_of_evaluatesTo_generators`).

The point-map agreement of `PullbackEvaluation_twoCurve` is then **not literally `rfl`** (the
coherence theorem quantifies over *arbitrary* residue values `cx cy`, while the map picks
`Classical.choose`-witnesses), but it is a one-line consequence of the *uniqueness* of the value
at a point (`EvaluatesTo.unique`). -/

section ConcretePointMap

-- Classical decidability of pole-locus membership, used to define the place-restriction point
-- map by `dite` on the (a priori undecidable) condition "`P` is in the affine kernel".
attribute [local instance] Classical.propDecidable

variable [IsAlgClosed F]

/-- **Off the pole locus, the `x`-generator pullback is regular.** -/
private theorem pointValuation_pullback_x_gen_le_one_of_notMem
    (φ : HasseWeil.Isogeny W₁ W₂) {SP : (W_smooth W₁).SmoothPoint}
    (hSP : SP ∉ twoCurvePoleLocus φ) :
    (W_smooth W₁).pointValuation SP (φ.pullback (x_gen W₂)) ≤ 1 := by
  by_contra hc; exact hSP (Set.mem_union_left _ hc)

/-- **Off the pole locus, the `y`-generator pullback is regular.** -/
private theorem pointValuation_pullback_y_gen_le_one_of_notMem
    (φ : HasseWeil.Isogeny W₁ W₂) {SP : (W_smooth W₁).SmoothPoint}
    (hSP : SP ∉ twoCurvePoleLocus φ) :
    (W_smooth W₁).pointValuation SP (φ.pullback (y_gen W₂)) ≤ 1 := by
  by_contra hc; exact hSP (Set.mem_union_right _ hc)

/-- **The residue `x`-value** of `φ` at a good smooth point `SP` (off the pole locus): the value
to which the regular pulled-back generator `φ^*(x_gen₂)` evaluates at `SP`. -/
private noncomputable def placeRestrictionResidueX
    (φ : HasseWeil.Isogeny W₁ W₂) (SP : (W_smooth W₁).SmoothPoint)
    (hSP : SP ∉ twoCurvePoleLocus φ) : F :=
  Classical.choose (exists_evaluatesTo_of_pointValuation_le_one W₁
    (pointValuation_pullback_x_gen_le_one_of_notMem φ hSP))

/-- **The residue `y`-value** of `φ` at a good smooth point `SP`. -/
private noncomputable def placeRestrictionResidueY
    (φ : HasseWeil.Isogeny W₁ W₂) (SP : (W_smooth W₁).SmoothPoint)
    (hSP : SP ∉ twoCurvePoleLocus φ) : F :=
  Classical.choose (exists_evaluatesTo_of_pointValuation_le_one W₁
    (pointValuation_pullback_y_gen_le_one_of_notMem φ hSP))

/-- The residue `x`-value witnesses the evaluation. -/
private theorem evaluatesTo_placeRestrictionResidueX
    (φ : HasseWeil.Isogeny W₁ W₂) (SP : (W_smooth W₁).SmoothPoint)
    (hSP : SP ∉ twoCurvePoleLocus φ) :
    EvaluatesTo W₁ SP (φ.pullback (x_gen W₂)) (placeRestrictionResidueX φ SP hSP) :=
  Classical.choose_spec (exists_evaluatesTo_of_pointValuation_le_one W₁
    (pointValuation_pullback_x_gen_le_one_of_notMem φ hSP))

/-- The residue `y`-value witnesses the evaluation. -/
private theorem evaluatesTo_placeRestrictionResidueY
    (φ : HasseWeil.Isogeny W₁ W₂) (SP : (W_smooth W₁).SmoothPoint)
    (hSP : SP ∉ twoCurvePoleLocus φ) :
    EvaluatesTo W₁ SP (φ.pullback (y_gen W₂)) (placeRestrictionResidueY φ SP hSP) :=
  Classical.choose_spec (exists_evaluatesTo_of_pointValuation_le_one W₁
    (pointValuation_pullback_y_gen_le_one_of_notMem φ hSP))

/-- **The residue-value point** of `φ` at a good smooth point `SP` (off the pole locus): the
*finite* point `(cx, cy) ∈ E₂` whose coordinates are the residue values of the pulled-back
generators.  Its nonsingularity is automatic (`nonsingular_of_evaluatesTo_generators`). -/
private noncomputable def placeRestrictionResiduePoint
    (φ : HasseWeil.Isogeny W₁ W₂) (SP : (W_smooth W₁).SmoothPoint)
    (hSP : SP ∉ twoCurvePoleLocus φ) : W₂.toAffine.Point :=
  Affine.Point.some (placeRestrictionResidueX φ SP hSP) (placeRestrictionResidueY φ SP hSP)
    (nonsingular_of_evaluatesTo_generators φ
      (evaluatesTo_placeRestrictionResidueX φ SP hSP)
      (evaluatesTo_placeRestrictionResidueY φ SP hSP))

/-- **The concrete CoordHom-free geometric point map of `φ` (place-restriction map).**

`O ↦ O`; an affine `P = (x, y)` in the affine kernel (`twoCurvePoleLocus φ`) `↦ O`; an affine
`P` off the pole locus `↦` its residue-value point `(cx, cy) ∈ E₂`.  This is the geometric
realization of `φ.pullback` on points, built *without* a `CoordHom`, purely from the
function-field pullback (Silverman III.4.8, the affine-kernel case).  Its group-hom property is
TASK B. -/
noncomputable def placeRestrictionPointMap
    (φ : HasseWeil.Isogeny W₁ W₂) : W₁.toAffine.Point → W₂.toAffine.Point
  | Affine.Point.zero => Affine.Point.zero
  | Affine.Point.some x y h =>
    if hSP : (⟨x, y, h⟩ : (W_smooth W₁).SmoothPoint) ∈ twoCurvePoleLocus φ then
      Affine.Point.zero
    else
      placeRestrictionResiduePoint φ ⟨x, y, h⟩ hSP

@[simp] theorem placeRestrictionPointMap_zero (φ : HasseWeil.Isogeny W₁ W₂) :
    placeRestrictionPointMap φ Affine.Point.zero = Affine.Point.zero := rfl

theorem placeRestrictionPointMap_some_of_mem (φ : HasseWeil.Isogeny W₁ W₂)
    {x y : F} {h : W₁.toAffine.Nonsingular x y}
    (hSP : (⟨x, y, h⟩ : (W_smooth W₁).SmoothPoint) ∈ twoCurvePoleLocus φ) :
    placeRestrictionPointMap φ (Affine.Point.some x y h) = Affine.Point.zero := by
  show (if _ : (⟨x, y, h⟩ : (W_smooth W₁).SmoothPoint) ∈ twoCurvePoleLocus φ then
    Affine.Point.zero else placeRestrictionResiduePoint φ ⟨x, y, h⟩ _) = Affine.Point.zero
  rw [dif_pos hSP]

theorem placeRestrictionPointMap_some_of_notMem (φ : HasseWeil.Isogeny W₁ W₂)
    {x y : F} {h : W₁.toAffine.Nonsingular x y}
    (hSP : (⟨x, y, h⟩ : (W_smooth W₁).SmoothPoint) ∉ twoCurvePoleLocus φ) :
    placeRestrictionPointMap φ (Affine.Point.some x y h) =
      placeRestrictionResiduePoint φ ⟨x, y, h⟩ hSP := by
  show (if _ : (⟨x, y, h⟩ : (W_smooth W₁).SmoothPoint) ∈ twoCurvePoleLocus φ then
    Affine.Point.zero else placeRestrictionResiduePoint φ ⟨x, y, h⟩ _) =
      placeRestrictionResiduePoint φ ⟨x, y, h⟩ hSP
  rw [dif_neg hSP]

/-- **The residue-value-point agreement for `placeRestrictionPointMap`.**  At a good smooth point
`SP = (x, y)` off the pole locus, with *any* residue values `cx cy` of the two pulled-back
generators, the map sends `(x, y)` to `(cx, cy)`.  This is the residue agreement consumed by
`pullbackEvaluation_twoCurve_of_residue_agreement`; it is a one-line consequence of the
*uniqueness* of the value at a point (`EvaluatesTo.unique`), since the map picks its own
`Classical.choose` residue witnesses. -/
theorem placeRestrictionPointMap_residue_agreement
    (φ : HasseWeil.Isogeny W₁ W₂) (SP : (W_smooth W₁).SmoothPoint)
    (hSP : SP ∉ twoCurvePoleLocus φ) {cx cy : F}
    (hx : EvaluatesTo W₁ SP (φ.pullback (x_gen W₂)) cx)
    (hy : EvaluatesTo W₁ SP (φ.pullback (y_gen W₂)) cy) :
    ∃ h' : W₂.toAffine.Nonsingular cx cy,
      placeRestrictionPointMap φ SP.toAffinePoint = Affine.Point.some cx cy h' := by
  -- the chosen residue values equal `cx`, `cy` by uniqueness of the value at `SP`
  have hxeq : placeRestrictionResidueX φ SP hSP = cx :=
    (evaluatesTo_placeRestrictionResidueX φ SP hSP).unique hx
  have hyeq : placeRestrictionResidueY φ SP hSP = cy :=
    (evaluatesTo_placeRestrictionResidueY φ SP hSP).unique hy
  -- substituting `cx`, `cy` by the chosen residue values turns the goal into a `rfl` on the
  -- residue-value point (the nonsingularity proofs match by proof irrelevance).
  subst hxeq hyeq
  refine ⟨nonsingular_of_evaluatesTo_generators φ hx hy, ?_⟩
  -- the map at the affine point `SP` is exactly the residue-value point.
  have hmap : placeRestrictionPointMap φ SP.toAffinePoint =
      placeRestrictionResiduePoint φ SP hSP := by
    rcases SP with ⟨x, y, h⟩
    exact placeRestrictionPointMap_some_of_notMem φ (h := h) hSP
  rw [hmap, placeRestrictionResiduePoint]

/-- **The concrete place-restriction realization of `φ` as a `HasseWeil.Isogeny`**, given the
group-hom property (TASK B) of `placeRestrictionPointMap φ`.  Its `pullback` is `φ.pullback` and
its `toAddMonoidHom` is the concrete CoordHom-free geometric point map `placeRestrictionPointMap φ`.
This is `placeRestrictionIsogeny` specialised to the concrete map. -/
noncomputable def placeRestrictionRealization
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hgrouphom : ∀ P Q : W₁.toAffine.Point,
      placeRestrictionPointMap φ (P + Q) =
        placeRestrictionPointMap φ P + placeRestrictionPointMap φ Q) :
    HasseWeil.Isogeny W₁ W₂ :=
  placeRestrictionIsogeny φ.pullback (placeRestrictionPointMap φ) hgrouphom
    (placeRestrictionPointMap_zero φ)

@[simp] theorem placeRestrictionRealization_pullback
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hgrouphom : ∀ P Q : W₁.toAffine.Point,
      placeRestrictionPointMap φ (P + Q) =
        placeRestrictionPointMap φ P + placeRestrictionPointMap φ Q) :
    (placeRestrictionRealization φ hgrouphom).pullback = φ.pullback := rfl

@[simp] theorem placeRestrictionRealization_toAddMonoidHom_apply
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hgrouphom : ∀ P Q : W₁.toAffine.Point,
      placeRestrictionPointMap φ (P + Q) =
        placeRestrictionPointMap φ P + placeRestrictionPointMap φ Q)
    (P : W₁.toAffine.Point) :
    (placeRestrictionRealization φ hgrouphom).toAddMonoidHom P = placeRestrictionPointMap φ P :=
  rfl

/-- **TASK A deliverable — the `PullbackEvaluation_twoCurve` coherence of the concrete
place-restriction realization.**  For the realization `placeRestrictionRealization φ hgrouphom`
(stored map `placeRestrictionPointMap φ`, function-field pullback `φ.pullback`), the two-curve
cofinite pullback-evaluation witness holds with `bad = twoCurvePoleLocus φ` (finite), **sorry-free**.

The proof is `pullbackEvaluation_twoCurve_of_residue_agreement` fed with the residue agreement
`placeRestrictionPointMap_residue_agreement`: the residue-value point on the right (whose
coordinates are the values of `φ^*(x_gen₂)`, `φ^*(y_gen₂)` at `P`) *is* the value of the stored
map at `P`, by construction (modulo the uniqueness of the value, `EvaluatesTo.unique`).

This makes the realization concrete and reduces PE-1 to **exactly** the group-hom property
`hgrouphom` of `placeRestrictionPointMap φ` (TASK B): the *only* remaining input is `hgrouphom`. -/
theorem pullbackEvaluation_twoCurve_placeRestrictionRealization
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hgrouphom : ∀ P Q : W₁.toAffine.Point,
      placeRestrictionPointMap φ (P + Q) =
        placeRestrictionPointMap φ P + placeRestrictionPointMap φ Q) :
    PullbackEvaluation_twoCurve W₁ W₂ (placeRestrictionRealization φ hgrouphom)
      (twoCurvePoleLocus φ) := by
  -- the realization shares `φ`'s pullback, so the pole locus and the residue values are the same
  apply pullbackEvaluation_twoCurve_of_residue_agreement (placeRestrictionRealization φ hgrouphom)
  intro P hP cx cy hx hy
  -- the stored map of the realization is `placeRestrictionPointMap φ`; supply the residue agreement
  exact placeRestrictionPointMap_residue_agreement φ P hP hx hy

end ConcretePointMap

end HasseWeil.WeilPairing
