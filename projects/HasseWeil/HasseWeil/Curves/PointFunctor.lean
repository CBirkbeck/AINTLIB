import HasseWeil.Curves.CurveMap
import HasseWeil.Curves.Basic

/-!
# Point functor for `CurveMap`s

For a `CurveMap` `φ : C₁ → C₂` between smooth plane curves over a field `F`,
together with a coordinate-ring witness (`CurveMap.CoordHom`), we construct
the induced map on rational smooth points
`φ.toPointMap : C₁.SmoothPoint → C₂.SmoothPoint`.

The construction is direct. A smooth point `P = (P.x, P.y)` of `C₁` provides an
evaluation ring hom `F[C₁] →+* F` (the residue map at `P`). Composing with the
coordinate-ring pullback `coordHom.toAlgHom : F[C₂] →ₐ[F] F[C₁]` gives an
evaluation `F[C₂] →+* F`. Reading off the images of the coordinate functions
yields the new coordinates `(x', y')` on `C₂`. Under `[IsElliptic C₂.toAffine]`
the point automatically satisfies the nonsingularity condition, by Silverman
III.1.4 (`equation_iff_nonsingular`).

This is the content of Silverman II.2.4(c) at the level of `F`-rational points,
restricted to the smooth-affine setting.

## Main definitions

* `SmoothPlaneCurve.evalAt`: residue map `F[C] →+* F` at a smooth point.
* `CurveMap.toPointMap`: the induced map on smooth points (under
  `[IsElliptic C₂.toAffine]`).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.4(c), III.4
-/

open scoped Polynomial.Bivariate

namespace HasseWeil.Curves

variable {F : Type*} [Field F]

/-! ### Evaluation at a smooth point -/

namespace SmoothPlaneCurve

variable (C : SmoothPlaneCurve F)

/-- Evaluation `F[C] →+* F` of a coordinate-ring element at a smooth point `P`.
This is the residue map at the maximal ideal `maximalIdealAt P`; algebraically,
it factors `Polynomial.evalEval P.x P.y` through the quotient by the
Weierstrass polynomial.
Reference: Silverman II.1 (residue field at a smooth `F`-rational point is `F`). -/
noncomputable def evalAt (P : C.SmoothPoint) : C.CoordinateRing →+* F :=
  AdjoinRoot.evalEval P.nonsingular.1

@[simp] theorem evalAt_mk (P : C.SmoothPoint) (g : Polynomial (Polynomial F)) :
    C.evalAt P (WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine g) =
      g.evalEval P.x P.y :=
  AdjoinRoot.evalEval_mk _ g

/-- Evaluation at `P` sends the `x`-coordinate function to `P.x`. -/
@[simp] theorem evalAt_x (P : C.SmoothPoint) :
    C.evalAt P (WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
      (Polynomial.C Polynomial.X)) = P.x := by
  rw [evalAt_mk]; simp [Polynomial.evalEval_C]

/-- Evaluation at `P` sends the `y`-coordinate function to `P.y`. -/
@[simp] theorem evalAt_y (P : C.SmoothPoint) :
    C.evalAt P (WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine Y) = P.y := by
  rw [evalAt_mk, Polynomial.evalEval_X]

/-- Evaluation at `P` is the identity on the constants of the `F`-algebra
structure. -/
@[simp] theorem evalAt_algebraMap (P : C.SmoothPoint) (c : F) :
    C.evalAt P (algebraMap F C.CoordinateRing c) = c := by
  change C.evalAt P (WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
    (Polynomial.C (Polynomial.C c))) = c
  rw [evalAt_mk]
  simp [Polynomial.evalEval_C]

/-! #### Kernel of `evalAt` is the maximal ideal -/

/-- The kernel of `evalAt P` is the maximal ideal at `P`. This is the
scheme-theoretic identification of "function vanishing at `P`" with "element
of the maximal ideal at `P`". Combined with maximality, the proof reduces to
showing the two generators `XClass` and `YClass` lie in the kernel.
Reference: Silverman II.1 (residue field at a smooth point). -/
theorem ker_evalAt (P : C.SmoothPoint) :
    RingHom.ker (C.evalAt P) = C.maximalIdealAt P := by
  refine ((C.maximalIdealAt_isMaximal P).eq_of_le ?_ ?_).symm
  · rw [Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]
    exact one_ne_zero
  · rw [maximalIdealAt, WeierstrassCurve.Affine.CoordinateRing.XYIdeal,
      Ideal.span_le]
    intro u hu
    rcases hu with rfl | rfl
    · rw [SetLike.mem_coe, RingHom.mem_ker,
        WeierstrassCurve.Affine.CoordinateRing.XClass, evalAt_mk]
      simp [Polynomial.evalEval_C]
    · rw [SetLike.mem_coe, RingHom.mem_ker,
        WeierstrassCurve.Affine.CoordinateRing.YClass, evalAt_mk]
      simp [Polynomial.evalEval_sub, Polynomial.evalEval_X, Polynomial.evalEval_C]

end SmoothPlaneCurve

/-! ### The induced map on smooth points -/

namespace CurveMap

variable {C₁ C₂ : SmoothPlaneCurve F}

/-- Composition `evalAt P ∘ coordHom`: evaluation of pulled-back coordinate-ring
elements at a point of the source curve. The image point of `P` under the curve
map is determined by reading off the coordinates of `C₂` through this map. -/
noncomputable def evalAtPullback {φ : CurveMap C₁ C₂} (coordHom : φ.CoordHom)
    (P : C₁.SmoothPoint) : C₂.CoordinateRing →+* F :=
  (C₁.evalAt P).comp coordHom.toAlgHom.toRingHom

@[simp] theorem evalAtPullback_apply {φ : CurveMap C₁ C₂} (coordHom : φ.CoordHom)
    (P : C₁.SmoothPoint) (u : C₂.CoordinateRing) :
    evalAtPullback coordHom P u = C₁.evalAt P (coordHom.toAlgHom u) := rfl

@[simp] theorem evalAtPullback_algebraMap {φ : CurveMap C₁ C₂}
    (coordHom : φ.CoordHom) (P : C₁.SmoothPoint) (c : F) :
    evalAtPullback coordHom P (algebraMap F C₂.CoordinateRing c) = c := by
  rw [evalAtPullback_apply, AlgHom.commutes, SmoothPlaneCurve.evalAt_algebraMap]

/-- **Universal property at the image point**: for any bivariate polynomial `g`,
the value of `mk g ∈ F[C₂]` under `evalAtPullback` equals `g` evaluated
bivariately at the image coordinates `(x', y')`.

Proof: both sides are ring homs `(F[X])[Y] →+* F`; equality is by
`Polynomial.ringHom_ext` applied at the outer (Y) and inner (X) layers, agreeing
on constants in `F`, on the inner `X`, and on the outer `Y`. -/
theorem evalAtPullback_mk {φ : CurveMap C₁ C₂} (coordHom : φ.CoordHom)
    (P : C₁.SmoothPoint) (g : Polynomial (Polynomial F)) :
    evalAtPullback coordHom P
      (WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine g) =
      g.evalEval
        (evalAtPullback coordHom P
          (WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine
            (Polynomial.C Polynomial.X)))
        (evalAtPullback coordHom P
          (WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine Y)) := by
  set x' : F := evalAtPullback coordHom P
    (WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine
      (Polynomial.C Polynomial.X)) with hx'_def
  set y' : F := evalAtPullback coordHom P
    (WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine Y) with hy'_def
  -- Two ring homs `(F[X])[Y] →+* F`:
  --   `ρ` factors through `F[C₂]`;
  --   `σ` is the bivariate evaluation at `(x', y')`.
  let mk₂ := WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine
  let ρ : Polynomial (Polynomial F) →+* F :=
    (evalAtPullback coordHom P).comp mk₂
  let σ : Polynomial (Polynomial F) →+* F :=
    (Polynomial.evalRingHom x').comp (Polynomial.evalRingHom (Polynomial.C y'))
  change ρ g = σ g
  congr 1
  refine Polynomial.ringHom_ext (fun p => ?_) ?_
  · -- agree on `C p` for `p : F[X]`; reduce to `(ρ ∘ C) = (σ ∘ C)` and apply
    -- `Polynomial.ringHom_ext` again.
    change ρ.comp Polynomial.C p = σ.comp Polynomial.C p
    congr 1
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · change ρ (Polynomial.C (Polynomial.C c)) = σ (Polynomial.C (Polynomial.C c))
      have hρ_c : ρ (Polynomial.C (Polynomial.C c)) = c := by
        change evalAtPullback coordHom P
          (mk₂ (Polynomial.C (Polynomial.C c))) = c
        have h_alg : mk₂ (Polynomial.C (Polynomial.C c)) =
            algebraMap F C₂.CoordinateRing c := rfl
        rw [h_alg, evalAtPullback_algebraMap]
      have hσ_c : σ (Polynomial.C (Polynomial.C c)) = c := by
        change (Polynomial.evalRingHom x') ((Polynomial.evalRingHom
          (Polynomial.C y')) (Polynomial.C (Polynomial.C c))) = c
        simp
      rw [hρ_c, hσ_c]
    · change ρ (Polynomial.C Polynomial.X) = σ (Polynomial.C Polynomial.X)
      have hρ_X : ρ (Polynomial.C Polynomial.X) = x' := rfl
      have hσ_X : σ (Polynomial.C Polynomial.X) = x' := by
        change (Polynomial.evalRingHom x') ((Polynomial.evalRingHom
          (Polynomial.C y')) (Polynomial.C Polynomial.X)) = x'
        simp
      rw [hρ_X, hσ_X]
  · change ρ Polynomial.X = σ Polynomial.X
    have hρ_Y : ρ Polynomial.X = y' := rfl
    have hσ_Y : σ Polynomial.X = y' := by
      change (Polynomial.evalRingHom x') ((Polynomial.evalRingHom
        (Polynomial.C y')) Polynomial.X) = y'
      simp
    rw [hρ_Y, hσ_Y]

/-- The image point `(x', y')` satisfies the Weierstrass equation of `C₂`.
Immediate from `evalAtPullback_mk` applied to `W₂.polynomial`, which vanishes
in `F[C₂]` by `AdjoinRoot.mk_self`. -/
theorem imagePoint_equation {φ : CurveMap C₁ C₂} (coordHom : φ.CoordHom)
    (P : C₁.SmoothPoint) :
    C₂.toAffine.Equation
      (evalAtPullback coordHom P (WeierstrassCurve.Affine.CoordinateRing.mk
        C₂.toAffine (Polynomial.C Polynomial.X)))
      (evalAtPullback coordHom P (WeierstrassCurve.Affine.CoordinateRing.mk
        C₂.toAffine Y)) := by
  have h := evalAtPullback_mk coordHom P C₂.toAffine.polynomial
  rw [show (WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine
    C₂.toAffine.polynomial : C₂.CoordinateRing) = 0 from AdjoinRoot.mk_self,
    map_zero] at h
  exact h.symm

/-- The image of a smooth point `P` of `C₁` under a curve map `φ : C₁ → C₂`,
constructed from the coordinate-ring witness. The coordinates are given by
evaluating the pulled-back coordinate functions at `P`; nonsingularity at the
image point is automatic for elliptic curves via `equation_iff_nonsingular`
(Silverman III.1.4). -/
noncomputable def toPointMap [C₂.toAffine.IsElliptic]
    {φ : CurveMap C₁ C₂} (coordHom : φ.CoordHom) (P : C₁.SmoothPoint) :
    C₂.SmoothPoint where
  x := evalAtPullback coordHom P
    (WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine
      (Polynomial.C Polynomial.X))
  y := evalAtPullback coordHom P
    (WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine Y)
  nonsingular := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (imagePoint_equation coordHom P)

@[simp] theorem toPointMap_x [C₂.toAffine.IsElliptic]
    {φ : CurveMap C₁ C₂} (coordHom : φ.CoordHom) (P : C₁.SmoothPoint) :
    (toPointMap coordHom P).x =
      evalAtPullback coordHom P
        (WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine
          (Polynomial.C Polynomial.X)) := rfl

@[simp] theorem toPointMap_y [C₂.toAffine.IsElliptic]
    {φ : CurveMap C₁ C₂} (coordHom : φ.CoordHom) (P : C₁.SmoothPoint) :
    (toPointMap coordHom P).y =
      evalAtPullback coordHom P
        (WeierstrassCurve.Affine.CoordinateRing.mk C₂.toAffine Y) := rfl

/-! ### Coherence: evaluation at the image equals pullback evaluation -/

variable {C₃ : SmoothPlaneCurve F}

/-- **Coherence**: evaluating any coordinate-ring element of `C₂` at the image
point `toPointMap coordHom P` reproduces the pullback evaluation at `P`. This
is the defining property of the points-functor: the value of `u : F[C₂]` at
`φ(P)` is the value of `φ*(u)` at `P`. -/
@[simp] theorem evalAt_toPointMap [C₂.toAffine.IsElliptic]
    {φ : CurveMap C₁ C₂} (coordHom : φ.CoordHom) (P : C₁.SmoothPoint)
    (u : C₂.CoordinateRing) :
    C₂.evalAt (toPointMap coordHom P) u = evalAtPullback coordHom P u := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective u
  rw [SmoothPlaneCurve.evalAt_mk, evalAtPullback_mk]
  rfl

/-! ### Identity and composition for `CoordHom` -/

namespace CoordHom

/-- The identity coordinate-ring witness for the identity curve map. -/
noncomputable def id (C : SmoothPlaneCurve F) : (CurveMap.id C).CoordHom where
  toAlgHom := AlgHom.id F C.CoordinateRing
  compat _ := rfl

@[simp] theorem id_toAlgHom (C : SmoothPlaneCurve F) :
    (CoordHom.id C).toAlgHom = AlgHom.id F C.CoordinateRing := rfl

/-- Composition of coordinate-ring witnesses, mirroring `CurveMap.comp`:
the pullback of `ψ ∘ φ` is `φ* ∘ ψ*`. -/
noncomputable def comp {φ : CurveMap C₁ C₂} {ψ : CurveMap C₂ C₃}
    (ψ_ch : ψ.CoordHom) (φ_ch : φ.CoordHom) : (ψ.comp φ).CoordHom where
  toAlgHom := φ_ch.toAlgHom.comp ψ_ch.toAlgHom
  compat u := by
    change (φ.pullback.comp ψ.pullback)
        (algebraMap C₃.CoordinateRing C₃.FunctionField u) =
      algebraMap C₁.CoordinateRing C₁.FunctionField
        (φ_ch.toAlgHom (ψ_ch.toAlgHom u))
    rw [AlgHom.comp_apply, ψ_ch.compat, φ_ch.compat]

@[simp] theorem comp_toAlgHom {φ : CurveMap C₁ C₂} {ψ : CurveMap C₂ C₃}
    (ψ_ch : ψ.CoordHom) (φ_ch : φ.CoordHom) :
    (ψ_ch.comp φ_ch).toAlgHom = φ_ch.toAlgHom.comp ψ_ch.toAlgHom := rfl

end CoordHom

/-! ### Functoriality of `toPointMap` -/

/-- The identity curve map induces the identity point map. -/
@[simp] theorem toPointMap_id {C : SmoothPlaneCurve F} [C.toAffine.IsElliptic]
    (P : C.SmoothPoint) : toPointMap (CoordHom.id C) P = P := by
  ext
  · rw [toPointMap_x, evalAtPullback_apply, CoordHom.id_toAlgHom,
      AlgHom.coe_id, _root_.id, SmoothPlaneCurve.evalAt_x]
  · rw [toPointMap_y, evalAtPullback_apply, CoordHom.id_toAlgHom,
      AlgHom.coe_id, _root_.id, SmoothPlaneCurve.evalAt_y]

/-- Composition of curve maps induces composition of point maps. -/
@[simp] theorem toPointMap_comp [C₂.toAffine.IsElliptic] [C₃.toAffine.IsElliptic]
    {φ : CurveMap C₁ C₂} {ψ : CurveMap C₂ C₃}
    (ψ_ch : ψ.CoordHom) (φ_ch : φ.CoordHom) (P : C₁.SmoothPoint) :
    toPointMap (ψ_ch.comp φ_ch) P = toPointMap ψ_ch (toPointMap φ_ch P) := by
  ext <;>
    simp only [toPointMap_x, toPointMap_y, evalAtPullback_apply,
      CoordHom.comp_toAlgHom, AlgHom.comp_apply, evalAt_toPointMap]

/-! ### Maximal-ideal coherence (bridge to `smoothPointEquivMaxIdeal`) -/

/-- The maximal ideal at the image point is the comap of the maximal ideal at
the source. This is the scheme-theoretic shadow of `toPointMap`: at the level
of points, `φ(P)` corresponds to `(coordHom)⁻¹(m_P)` as a maximal ideal.
Reference: Silverman II.2.4(c) (curves-fields equivalence on points). -/
theorem maximalIdealAt_toPointMap [C₂.toAffine.IsElliptic]
    {φ : CurveMap C₁ C₂} (coordHom : φ.CoordHom) (P : C₁.SmoothPoint) :
    C₂.maximalIdealAt (toPointMap coordHom P) =
      Ideal.comap coordHom.toAlgHom.toRingHom (C₁.maximalIdealAt P) := by
  ext u
  rw [← C₂.ker_evalAt (toPointMap coordHom P), ← C₁.ker_evalAt P,
    Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker,
    evalAt_toPointMap, evalAtPullback_apply]
  rfl

end CurveMap

/-! ### Bridge to `WeierstrassCurve.Affine.Point` -/

namespace SmoothPlaneCurve

variable {C : SmoothPlaneCurve F}

/-- A smooth point promotes to a mathlib `WeierstrassCurve.Affine.Point` via the
`some` constructor (using the nonsingularity proof carried by the smooth point).
This is the bridge from our affine `SmoothPoint` representation to the inductive
`Point` type, which also carries the basepoint at infinity (`Point.zero`). -/
def SmoothPoint.toAffinePoint (P : C.SmoothPoint) : C.toAffine.Point :=
  WeierstrassCurve.Affine.Point.some P.x P.y P.nonsingular

@[simp] theorem SmoothPoint.toAffinePoint_def (P : C.SmoothPoint) :
    P.toAffinePoint = WeierstrassCurve.Affine.Point.some P.x P.y P.nonsingular := rfl

end SmoothPlaneCurve

end HasseWeil.Curves
