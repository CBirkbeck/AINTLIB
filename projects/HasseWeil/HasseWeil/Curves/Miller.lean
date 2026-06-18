/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.AFConditional
import HasseWeil.Curves.EffectiveSumReduce
import HasseWeil.Curves.NoFinitePolesBridge
import HasseWeil.Curves.NormValuation
import HasseWeil.IsogenyBaseChange

open scoped Polynomial.Bivariate

/-!
# Miller's relation on an elliptic curve

This file collects the proof of `MillerHypothesis W`:

```
∀ P Q : W.Point,
  ProjIsPrincipal (⟨W⟩) ((P) + (Q) − (P + Q) − (O))
```

This is **Silverman III.3.5**, the chord/tangent divisor identity on an
elliptic curve. The standard proof exhibits a witness function in `F(E)*`
as `ℓ / v`, where `ℓ` is the chord (or tangent) line through `P` and `Q`
and `v` is the vertical line at `x(P + Q)`. The line `ℓ` has divisor
`(P) + (Q) + (-(P+Q)) − 3(O)`, the vertical `v` has divisor
`(P+Q) + (-(P+Q)) − 2(O)`, and the ratio gives exactly the Miller divisor.

This file ships the **degenerate cases** of Miller (one of `P`, `Q`, or
`P + Q` equals the identity) axiom-clean. The non-degenerate chord and
tangent cases reduce to two named geometric inputs:
`verticalLine_projectiveDivisor` and `chordLine_projectiveDivisor`,
which are the substantive divisor computations identifying the divisor
of `X − x(R)` resp. of the line polynomial through two affine points on
`E`. These are tracked as sub-tickets `T-MILLER-VERT` and
`T-MILLER-CHORD` (see `.mathlib-quality/tickets/`).

## Main results (this file)

* `miller_of_zero_left`  — `(0) + (Q) − (Q) − (O)` is principal (trivial).
* `miller_of_zero_right` — `(P) + (0) − (P) − (O)` is principal (trivial).
* `miller_of_neg`        — `(P) + (-P) − (0) − (O)` reduces to the
  vertical-line divisor identity.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.3.5 (chord/tangent).
-/

open WeierstrassCurve

namespace HasseWeil.Curves

variable {F : Type*} [Field F] [DecidableEq F]
  (W : Affine F) [W.IsElliptic]

omit [WeierstrassCurve.IsElliptic W] in
/-- **Miller, left-zero case**: `(0) + (Q) − (0 + Q) − (O)` is the
zero divisor (since `0 + Q = Q` and `0.toProj = ∞`), hence principal. -/
theorem miller_of_zero_left (Q : W.Point) :
    SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
      (Finsupp.single (0 : W.Point).toProjectiveSmoothPoint 1
        + Finsupp.single Q.toProjectiveSmoothPoint 1
        - Finsupp.single ((0 : W.Point) + Q).toProjectiveSmoothPoint 1
        - Finsupp.single (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) 1) := by
  have h_zero :
      Finsupp.single (0 : W.Point).toProjectiveSmoothPoint (1 : ℤ)
          + Finsupp.single Q.toProjectiveSmoothPoint 1
          - Finsupp.single ((0 : W.Point) + Q).toProjectiveSmoothPoint 1
          - Finsupp.single (ProjectiveSmoothPoint.infinity :
              ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) 1 = 0 := by
    rw [zero_add Q,
      show (0 : W.Point).toProjectiveSmoothPoint =
        (ProjectiveSmoothPoint.infinity :
          ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) from rfl]
    abel
  rw [h_zero]
  exact SmoothPlaneCurve.projIsPrincipal_zero (⟨W⟩ : SmoothPlaneCurve F)

omit [WeierstrassCurve.IsElliptic W] in
/-- **Miller, right-zero case**: `(P) + (0) − (P + 0) − (O)` is the
zero divisor (since `P + 0 = P` and `0.toProj = ∞`), hence principal. -/
theorem miller_of_zero_right (P : W.Point) :
    SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
      (Finsupp.single P.toProjectiveSmoothPoint 1
        + Finsupp.single (0 : W.Point).toProjectiveSmoothPoint 1
        - Finsupp.single (P + (0 : W.Point)).toProjectiveSmoothPoint 1
        - Finsupp.single (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) 1) := by
  have h_zero :
      Finsupp.single P.toProjectiveSmoothPoint (1 : ℤ)
          + Finsupp.single (0 : W.Point).toProjectiveSmoothPoint 1
          - Finsupp.single (P + (0 : W.Point)).toProjectiveSmoothPoint 1
          - Finsupp.single (ProjectiveSmoothPoint.infinity :
              ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) 1 = 0 := by
    rw [add_zero P,
      show (0 : W.Point).toProjectiveSmoothPoint =
        (ProjectiveSmoothPoint.infinity :
          ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) from rfl]
    abel
  rw [h_zero]
  exact SmoothPlaneCurve.projIsPrincipal_zero (⟨W⟩ : SmoothPlaneCurve F)

omit [WeierstrassCurve.IsElliptic W] in
/-- Miller's divisor at `(P, -P)` rewrites as the vertical-line divisor
`(P) + (-P) − 2·(O)`. Pure algebraic rearrangement using
`P + (-P) = 0` and `0.toProj = ∞`. -/
theorem miller_divisor_at_neg_eq_vertical (P : W.Point) :
    Finsupp.single P.toProjectiveSmoothPoint (1 : ℤ)
        + Finsupp.single (-P).toProjectiveSmoothPoint 1
        - Finsupp.single (P + (-P)).toProjectiveSmoothPoint 1
        - Finsupp.single (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) 1 =
      Finsupp.single P.toProjectiveSmoothPoint 1
        + Finsupp.single (-P).toProjectiveSmoothPoint 1
        - (2 : ℤ) • Finsupp.single (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) 1 := by
  rw [add_neg_cancel P,
    show (0 : W.Point).toProjectiveSmoothPoint =
      (ProjectiveSmoothPoint.infinity :
        ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) from rfl,
    show ((2 : ℤ) • Finsupp.single (ProjectiveSmoothPoint.infinity :
        ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ)) =
      Finsupp.single (ProjectiveSmoothPoint.infinity :
        ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ) +
      Finsupp.single (ProjectiveSmoothPoint.infinity :
        ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ) by
      rw [show (2 : ℤ) = 1 + 1 from rfl, add_smul, one_smul]]
  abel

omit [WeierstrassCurve.IsElliptic W] in
/-- **Miller, `(P, -P)` case in terms of vertical-line principal**: if
the vertical-line divisor `(P) + (-P) − 2(O)` is principal, then so is
the Miller divisor at `(P, -P)`. Pure algebraic rearrangement. -/
theorem miller_of_neg_of_vertical_principal (P : W.Point)
    (h_vert : SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
      (Finsupp.single P.toProjectiveSmoothPoint 1
        + Finsupp.single (-P).toProjectiveSmoothPoint 1
        - (2 : ℤ) • Finsupp.single (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) 1)) :
    SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
      (Finsupp.single P.toProjectiveSmoothPoint 1
        + Finsupp.single (-P).toProjectiveSmoothPoint 1
        - Finsupp.single (P + (-P)).toProjectiveSmoothPoint 1
        - Finsupp.single (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) 1) := by
  rwa [miller_divisor_at_neg_eq_vertical W P]

end HasseWeil.Curves

namespace HasseWeil.Curves.SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)

/-- The function `coordX − algebraMap F C.FunctionField a` equals
`algebraMap C.CoordinateRing C.FunctionField (XClass C.toAffine a)`. This
identifies the rational function `X − a` on `E` with the class of the
polynomial `X − a` in the coordinate ring, transported to the function
field. -/
theorem coordX_sub_const_eq_algebraMap_XClass (a : F) :
    C.coordX - algebraMap F C.FunctionField a =
      algebraMap C.CoordinateRing C.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine a) := by
  unfold coordX
  rw [show (algebraMap F C.FunctionField a : C.FunctionField) =
        algebraMap C.CoordinateRing C.FunctionField
          (algebraMap F C.CoordinateRing a)
      from IsScalarTower.algebraMap_apply F C.CoordinateRing C.FunctionField a,
    show (algebraMap (Polynomial F) C.FunctionField Polynomial.X :
            C.FunctionField) =
        algebraMap C.CoordinateRing C.FunctionField
          (algebraMap (Polynomial F) C.CoordinateRing Polynomial.X)
      from IsScalarTower.algebraMap_apply (Polynomial F) C.CoordinateRing
        C.FunctionField Polynomial.X,
    ← _root_.map_sub]
  congr 1
  rw [WeierstrassCurve.Affine.CoordinateRing.XClass,
    show (algebraMap (Polynomial F) C.CoordinateRing Polynomial.X :
            C.CoordinateRing) =
        WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
          (Polynomial.C Polynomial.X) by rfl,
    show (algebraMap F C.CoordinateRing a : C.CoordinateRing) =
        WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
          (Polynomial.C (Polynomial.C a)) by rfl,
    ← _root_.map_sub]
  congr 1
  rw [← Polynomial.C_sub]

/-- The function `coordX − algebraMap F C.FunctionField a` is nonzero
(as the image of a nonzero polynomial under an injective algebra map). -/
theorem coordX_sub_const_ne_zero (a : F) :
    C.coordX - algebraMap F C.FunctionField a ≠ 0 := by
  rw [C.coordX_sub_const_eq_algebraMap_XClass a]
  exact fun h ↦ WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero
    (W' := C.toAffine) a
    ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h)

/-- **Order at infinity of `coordX − a`**: equals `-2`. Vertical lines
have a double pole at infinity on a Weierstrass curve. Direct consequence
of `ordAtInfty_algebraMap_polynomial_of_ne_zero` applied to `X − C a` of
`natDegree 1`. -/
theorem ordAtInfty_coordX_sub_const (a : F) :
    C.ordAtInfty (C.coordX - algebraMap F C.FunctionField a) =
      ((-2 : ℤ) : WithTop ℤ) := by
  have hp_ne : (Polynomial.X - Polynomial.C a : Polynomial F) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero a
  have h_eq : C.coordX - algebraMap F C.FunctionField a =
      algebraMap (Polynomial F) C.FunctionField (Polynomial.X - Polynomial.C a) := by
    unfold coordX
    rw [_root_.map_sub,
      show (algebraMap (Polynomial F) C.FunctionField (Polynomial.C a) :
              C.FunctionField) = algebraMap F C.FunctionField a by
        rw [show (Polynomial.C a : Polynomial F) =
              algebraMap F (Polynomial F) a from rfl,
          ← IsScalarTower.algebraMap_apply F (Polynomial F) C.FunctionField a]]
  rw [h_eq, C.ordAtInfty_algebraMap_polynomial_of_ne_zero hp_ne,
    Polynomial.natDegree_X_sub_C]
  norm_num

/-- **Affine divisor of `coordX − a` at smooth point P, in count form**:
under the standard Dedekind hypothesis `[IsIntegrallyClosed C.CoordinateRing]`,
the divisor coefficient at `P` equals the `(maximalIdealAt P)`-adic count of
`Ideal.span {XClass a}`. Direct from
`divisorOf_algebraMap_apply_eq_count` + the algMap-XClass bridge. -/
theorem divisorOf_coordX_sub_const_apply
    [IsIntegrallyClosed C.CoordinateRing]
    (a : F) (P : C.SmoothPoint) :
    C.divisorOf (C.coordX - algebraMap F C.FunctionField a) P =
      ((Associates.mk (C.maximalIdealAt P)).count
        (Associates.mk (Ideal.span
          {WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine a})).factors :
        ℤ) := by
  have hu_ne : WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine a ≠ 0 :=
    WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero (W' := C.toAffine) a
  rw [C.coordX_sub_const_eq_algebraMap_XClass a,
    C.divisorOf_algebraMap_apply_eq_count P hu_ne]

/-- **Vertical-line affine divisor support**: the divisor of
`coordX − a` at a smooth point `Q` vanishes when `Q.x ≠ a`. Direct from
the count formula plus the fact that `XClass a ∉ maximalIdealAt Q` when
`Q.x ≠ a` (the evaluation criterion). -/
theorem divisorOf_coordX_sub_const_apply_eq_zero_of_x_ne
    [IsIntegrallyClosed C.CoordinateRing]
    (a : F) (Q : C.SmoothPoint) (hQa : Q.x ≠ a) :
    C.divisorOf (C.coordX - algebraMap F C.FunctionField a) Q = 0 := by
  rw [C.divisorOf_coordX_sub_const_apply a Q]
  have hXClass_not_mem :
      WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine a ∉
        C.maximalIdealAt Q := by
    have h_basis :
        WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine a =
        (Polynomial.X - Polynomial.C a) • (1 : C.CoordinateRing) +
        (0 : Polynomial F) •
          WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine Y := by
      unfold WeierstrassCurve.Affine.CoordinateRing.XClass
      rw [zero_smul, add_zero, Algebra.smul_def, mul_one]
      rfl
    rw [h_basis, C.mem_maximalIdealAt_iff_eval_zero Q
      (Polynomial.X - Polynomial.C a) 0]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_zero, zero_mul, add_zero]
    exact sub_ne_zero_of_ne hQa
  have hM_ne_bot : C.maximalIdealAt Q ≠ ⊥ := C.maximalIdealAt_ne_bot Q
  have hXClass_ne : WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine a
      ≠ 0 := WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero
      (W' := C.toAffine) a
  have hSpan_ne : Ideal.span ({WeierstrassCurve.Affine.CoordinateRing.XClass
      C.toAffine a} : Set C.CoordinateRing) ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  let vQ : IsDedekindDomain.HeightOneSpectrum C.CoordinateRing :=
    ⟨_, (C.maximalIdealAt_isMaximal Q).isPrime, hM_ne_bot⟩
  by_contra h_count_ne
  apply hXClass_not_mem
  have h_count_ne_nat :
      (Associates.mk vQ.asIdeal).count
        (Associates.mk (Ideal.span
          {WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine a})).factors
        ≠ 0 := by
    intro h
    apply h_count_ne
    exact_mod_cast h
  have h_dvd : vQ.asIdeal ∣ Ideal.span
      ({WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine a} :
        Set C.CoordinateRing) :=
    (Associates.count_ne_zero_iff_dvd hSpan_ne vQ.irreducible).mp h_count_ne_nat
  rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h_dvd

/-- The negation of a smooth point `P : C.SmoothPoint`: same `x`-coordinate,
`y`-coordinate replaced by `W.negY x y`. The result is again a smooth point
(via `Affine.nonsingular_neg`). -/
noncomputable def _root_.HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.neg
    {C : SmoothPlaneCurve F} (P : C.SmoothPoint) : C.SmoothPoint where
  x := P.x
  y := C.toAffine.negY P.x P.y
  nonsingular :=
    (WeierstrassCurve.Affine.nonsingular_neg P.x P.y).mpr P.nonsingular

@[simp] theorem SmoothPoint.neg_x (P : C.SmoothPoint) :
    P.neg.x = P.x := rfl

@[simp] theorem SmoothPoint.neg_y (P : C.SmoothPoint) :
    P.neg.y = C.toAffine.negY P.x P.y := rfl

@[simp] theorem SmoothPoint.neg_neg (P : C.SmoothPoint) :
    P.neg.neg = P := by
  ext
  · rfl
  · exact WeierstrassCurve.Affine.negY_negY (W' := C.toAffine) P.x P.y

/-- The maximal ideal at `P.neg` matches mathlib's `XYIdeal` of the negated
y-coordinate. Definitional unfolding. -/
theorem maximalIdealAt_neg (P : C.SmoothPoint) :
    C.maximalIdealAt P.neg =
      WeierstrassCurve.Affine.CoordinateRing.XYIdeal C.toAffine P.x
        (Polynomial.C (C.toAffine.negY P.x P.y)) := rfl

/-- **Vertical-line ideal factorisation**: the principal ideal `span {XClass P.x}`
factors as the product `maximalIdealAt P.neg · maximalIdealAt P` in
`C.CoordinateRing`. Wrapper around mathlib's `XYIdeal_neg_mul`. -/
theorem span_XClass_eq_maximalIdealAt_neg_mul (P : C.SmoothPoint) :
    Ideal.span ({WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine P.x} :
      Set C.CoordinateRing) =
      C.maximalIdealAt P.neg * C.maximalIdealAt P := by
  rw [C.maximalIdealAt_neg P, maximalIdealAt,
    WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul P.nonsingular]
  rfl

/-- **Self-count**: the count of `maximalIdealAt P` in its own factorisation is 1.
Direct from `Associates.count_self` applied to the `HeightOneSpectrum` element
built from `maximalIdealAt P`. -/
theorem count_maximalIdealAt_self
    [IsIntegrallyClosed C.CoordinateRing] (P : C.SmoothPoint) :
    (Associates.mk (C.maximalIdealAt P)).count
        (Associates.mk (C.maximalIdealAt P)).factors = 1 := by
  let vP : IsDedekindDomain.HeightOneSpectrum C.CoordinateRing :=
    ⟨_, (C.maximalIdealAt_isMaximal P).isPrime, C.maximalIdealAt_ne_bot P⟩
  exact Associates.count_self (vP.associates_irreducible)

/-- **Cross-count is zero for distinct smooth points**: for distinct smooth points
`Q ≠ P`, the count of `maximalIdealAt Q` in the factorisation of
`maximalIdealAt P` is zero. Combines `Associates.count_eq_zero_of_ne` with
`maximalIdealAt_injective`. -/
theorem count_maximalIdealAt_eq_zero_of_ne
    [IsIntegrallyClosed C.CoordinateRing]
    (Q P : C.SmoothPoint) (hQP : Q ≠ P) :
    (Associates.mk (C.maximalIdealAt Q)).count
        (Associates.mk (C.maximalIdealAt P)).factors = 0 := by
  let vQ : IsDedekindDomain.HeightOneSpectrum C.CoordinateRing :=
    ⟨_, (C.maximalIdealAt_isMaximal Q).isPrime, C.maximalIdealAt_ne_bot Q⟩
  let vP : IsDedekindDomain.HeightOneSpectrum C.CoordinateRing :=
    ⟨_, (C.maximalIdealAt_isMaximal P).isPrime, C.maximalIdealAt_ne_bot P⟩
  have hM_ne : (Associates.mk vQ.asIdeal) ≠ (Associates.mk vP.asIdeal) := by
    intro h
    apply hQP
    apply C.maximalIdealAt_injective
    rwa [← associated_iff_eq, ← Associates.mk_eq_mk_iff_associated]
  exact Associates.count_eq_zero_of_ne vQ.associates_irreducible
    vP.associates_irreducible hM_ne

/-- **Fibre dichotomy**: any smooth point `Q` with `Q.x = P.x` is either `P`
itself or its negation `P.neg`. Direct consequence of mathlib's
`Y_eq_of_X_eq`. -/
theorem smoothPoint_x_eq_iff_self_or_neg (P Q : C.SmoothPoint) (hQx : Q.x = P.x) :
    Q = P ∨ Q = P.neg := by
  have hQ_eq : C.toAffine.Equation Q.x Q.y := Q.nonsingular.1
  have hP_eq : C.toAffine.Equation P.x P.y := P.nonsingular.1
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq (W := C.toAffine) hQ_eq hP_eq hQx with
    hy | hy
  · left
    exact SmoothPoint.ext hQx hy
  · right
    refine SmoothPoint.ext hQx ?_
    rw [SmoothPoint.neg_y]
    exact hy

/-- **Vertical-line affine divisor (pointwise Finsupp identity)**: for any
smooth points `P, Q` on the elliptic curve,
`(divisorOf (coordX − P.x)) Q = (single P 1 + single P.neg 1) Q`.

Combines all the building blocks above: count-form divisor, structural
ideal identity, `Associates.count_mul`, the diagonal/off-diagonal entries,
fibre dichotomy, and support-zero result. Handles 2-torsion (`P = P.neg`)
and non-2-torsion (`P ≠ P.neg`) uniformly via Finsupp arithmetic. -/
theorem divisorOf_coordX_sub_const_apply_eq_finsupp
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)] [C.toAffine.IsElliptic]
    [IsIntegrallyClosed C.CoordinateRing]
    (P Q : C.SmoothPoint) :
    C.divisorOf (C.coordX - algebraMap F C.FunctionField P.x) Q =
      ((Finsupp.single P (1 : ℤ) + Finsupp.single P.neg 1 :
        C.SmoothPoint →₀ ℤ) Q) := by
  classical
  have hMneg_assoc_ne : (Associates.mk (C.maximalIdealAt P.neg) :
      Associates (Ideal C.CoordinateRing)) ≠ 0 :=
    Associates.mk_ne_zero.mpr (C.maximalIdealAt_ne_bot P.neg)
  have hMP_assoc_ne : (Associates.mk (C.maximalIdealAt P) :
      Associates (Ideal C.CoordinateRing)) ≠ 0 :=
    Associates.mk_ne_zero.mpr (C.maximalIdealAt_ne_bot P)
  let vQ : IsDedekindDomain.HeightOneSpectrum C.CoordinateRing :=
    ⟨_, (C.maximalIdealAt_isMaximal Q).isPrime, C.maximalIdealAt_ne_bot Q⟩
  have h_count_expand :
      (Associates.mk (C.maximalIdealAt Q)).count
          (Associates.mk (Ideal.span
            {WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine P.x})).factors =
        (Associates.mk (C.maximalIdealAt Q)).count
          (Associates.mk (C.maximalIdealAt P.neg)).factors +
        (Associates.mk (C.maximalIdealAt Q)).count
          (Associates.mk (C.maximalIdealAt P)).factors := by
    rw [C.span_XClass_eq_maximalIdealAt_neg_mul P, ← Associates.mk_mul_mk]
    exact Associates.count_mul hMneg_assoc_ne hMP_assoc_ne
      vQ.associates_irreducible
  rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
    C.divisorOf_coordX_sub_const_apply P.x Q, h_count_expand]
  have h_count_Pneg :
      (Associates.mk (C.maximalIdealAt Q)).count
          (Associates.mk (C.maximalIdealAt P.neg)).factors =
        (if P.neg = Q then 1 else 0) := by
    by_cases h : Q = P.neg
    · rw [if_pos h.symm, h, C.count_maximalIdealAt_self P.neg]
    · rw [if_neg fun he ↦ h he.symm,
        C.count_maximalIdealAt_eq_zero_of_ne Q P.neg h]
  have h_count_P :
      (Associates.mk (C.maximalIdealAt Q)).count
          (Associates.mk (C.maximalIdealAt P)).factors =
        (if P = Q then 1 else 0) := by
    by_cases h : Q = P
    · rw [if_pos h.symm, h, C.count_maximalIdealAt_self P]
    · rw [if_neg fun he ↦ h he.symm,
        C.count_maximalIdealAt_eq_zero_of_ne Q P h]
  rw [h_count_Pneg, h_count_P]
  push_cast
  split_ifs <;> ring

/-- **Vertical-line affine divisor (Finsupp form)**: the affine divisor of
`coordX − P.x` equals `single P 1 + single P.neg 1` as a Finsupp. Direct
Finsupp.ext from the pointwise identity. -/
theorem divisorOf_coordX_sub_const
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)] [C.toAffine.IsElliptic]
    [IsIntegrallyClosed C.CoordinateRing]
    (P : C.SmoothPoint) :
    C.divisorOf (C.coordX - algebraMap F C.FunctionField P.x) =
      Finsupp.single P (1 : ℤ) + Finsupp.single P.neg 1 :=
  Finsupp.ext fun Q ↦ C.divisorOf_coordX_sub_const_apply_eq_finsupp P Q

/-- **Vertical-line projective divisor**: the full projective divisor of
`coordX − P.x` is `(P) + (P.neg) − 2·(∞)` on the projective closure.
Combines the Finsupp affine divisor identity with `ordAtInfty = -2`. -/
theorem projectiveDivisorOf_coordX_sub_const
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)] [C.toAffine.IsElliptic]
    [IsIntegrallyClosed C.CoordinateRing]
    (P : C.SmoothPoint) :
    C.projectiveDivisorOf (C.coordX - algebraMap F C.FunctionField P.x) =
      Finsupp.single (ProjectiveSmoothPoint.affine P) (1 : ℤ)
        + Finsupp.single (ProjectiveSmoothPoint.affine P.neg) 1
        - (2 : ℤ) • Finsupp.single ProjectiveSmoothPoint.infinity 1 := by
  unfold projectiveDivisorOf
  rw [C.divisorOf_coordX_sub_const P, C.ordAtInfty_coordX_sub_const P.x,
    WithTop.untopD_coe, Divisor.toProjective_add]
  have h_single_proj_P :
      Divisor.toProjective (Finsupp.single P (1 : ℤ) : Divisor C) =
        Finsupp.single (ProjectiveSmoothPoint.affine P) 1 := by
    unfold Divisor.toProjective
    exact Finsupp.mapDomain_single
  have h_single_proj_Pneg :
      Divisor.toProjective (Finsupp.single P.neg (1 : ℤ) : Divisor C) =
        Finsupp.single (ProjectiveSmoothPoint.affine P.neg) 1 := by
    unfold Divisor.toProjective
    exact Finsupp.mapDomain_single
  rw [h_single_proj_P, h_single_proj_Pneg]
  have h_two_smul : ((2 : ℤ) • Finsupp.single
      (ProjectiveSmoothPoint.infinity :
        ProjectiveSmoothPoint (⟨C.toAffine⟩ : SmoothPlaneCurve F)) (1 : ℤ) :
        ProjectiveDivisor (⟨C.toAffine⟩ : SmoothPlaneCurve F)) =
      Finsupp.single ProjectiveSmoothPoint.infinity 2 := by
    simp [Finsupp.smul_single]
  have h_neg_single : (Finsupp.single (ProjectiveSmoothPoint.infinity :
          ProjectiveSmoothPoint (⟨C.toAffine⟩ : SmoothPlaneCurve F)) (-2 : ℤ) :
          ProjectiveDivisor (⟨C.toAffine⟩ : SmoothPlaneCurve F)) =
        -Finsupp.single ProjectiveSmoothPoint.infinity 2 :=
    Finsupp.single_neg _ _
  rw [h_two_smul, h_neg_single]
  abel

/-- **Vertical-line is principal** at any affine smooth point: the divisor
`(P) + (P.neg) − 2·(∞)` lies in the principal subgroup of the projective
divisor group, witnessed by the function `coordX − P.x ∈ K(C)*`. -/
theorem vertical_line_principal
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)] [C.toAffine.IsElliptic]
    [IsIntegrallyClosed C.CoordinateRing]
    (P : C.SmoothPoint) :
    SmoothPlaneCurve.ProjIsPrincipal C
      (Finsupp.single (ProjectiveSmoothPoint.affine P) (1 : ℤ)
        + Finsupp.single (ProjectiveSmoothPoint.affine P.neg) 1
        - (2 : ℤ) • Finsupp.single (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint C) 1) :=
  ⟨C.coordX - algebraMap F C.FunctionField P.x,
   C.coordX_sub_const_ne_zero P.x,
   C.projectiveDivisorOf_coordX_sub_const P⟩

end HasseWeil.Curves.SmoothPlaneCurve

namespace HasseWeil.Curves.SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)

/-- The function `coordY − algebraMap F[X] K(C) (linePolynomial x y slope)` equals
`algebraMap C.CoordinateRing K(C) (YClass linePolynomial)`. Identifies the
function-field element corresponding to the chord/tangent line `Y = ℓ(X − x) + y`
with the image of the `Y − ℓ(X − x) − y` class in the coordinate ring. -/
theorem coordY_sub_algMap_linePolynomial_eq_algMap_YClass
    (x y slope : F) :
    C.coordY -
        algebraMap (Polynomial F) C.FunctionField
          (WeierstrassCurve.Affine.linePolynomial x y slope) =
      algebraMap C.CoordinateRing C.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.YClass C.toAffine
          (WeierstrassCurve.Affine.linePolynomial x y slope)) := by
  have h_coordY : C.coordY = algebraMap C.CoordinateRing C.FunctionField
      (WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
        (Polynomial.X : Polynomial (Polynomial F))) := by
    unfold coordY
    rw [WeierstrassCurve.Affine.CoordinateRing.basis_one]
  have h_lp : algebraMap (Polynomial F) C.FunctionField
        (WeierstrassCurve.Affine.linePolynomial x y slope) =
      algebraMap C.CoordinateRing C.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
          (Polynomial.C (WeierstrassCurve.Affine.linePolynomial x y slope))) := by
    rw [IsScalarTower.algebraMap_apply (Polynomial F) C.CoordinateRing
      C.FunctionField _]
    rfl
  rw [h_coordY, h_lp, ← _root_.map_sub]
  unfold WeierstrassCurve.Affine.CoordinateRing.YClass
  rw [show (WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
        ((Polynomial.X : Polynomial (Polynomial F)) -
          Polynomial.C
            (WeierstrassCurve.Affine.linePolynomial x y slope)) :
        C.CoordinateRing) =
      WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
          (Polynomial.X : Polynomial (Polynomial F)) -
        WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
          (Polynomial.C (WeierstrassCurve.Affine.linePolynomial x y slope))
      from (map_sub _ _ _)]

/-- The chord line function `coordY − algMap(linePolynomial x y slope)` is
nonzero in `K(C)` (since `YClass linePoly` is nonzero in the coordinate ring). -/
theorem coordY_sub_algMap_linePolynomial_ne_zero (x y slope : F) :
    C.coordY -
        algebraMap (Polynomial F) C.FunctionField
          (WeierstrassCurve.Affine.linePolynomial x y slope) ≠ 0 := by
  rw [C.coordY_sub_algMap_linePolynomial_eq_algMap_YClass x y slope]
  exact fun h ↦ WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero
    (W' := C.toAffine) _
    ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h)

/-- **Order at infinity of the chord line**: `ord_∞(coordY − ℓ(X − x) − y) = −3`.
The Y-coordinate has triple pole at ∞, and the polynomial term has at most a
double pole, so the difference inherits the triple pole. -/
theorem ordAtInfty_coordY_sub_algMap_linePolynomial (x y slope : F) :
    C.ordAtInfty (C.coordY -
        algebraMap (Polynomial F) C.FunctionField
          (WeierstrassCurve.Affine.linePolynomial x y slope)) =
      ((-3 : ℤ) : WithTop ℤ) := by
  have h_coordY_eq : C.coordY = C.coordYInFunctionField :=
    C.coordY_eq_coordYInFunctionField
  rw [h_coordY_eq]
  have h_form :
      C.coordYInFunctionField -
          algebraMap (Polynomial F) C.FunctionField
            (WeierstrassCurve.Affine.linePolynomial x y slope) =
        algebraMap (Polynomial F) C.FunctionField
          (-(WeierstrassCurve.Affine.linePolynomial x y slope)) +
        algebraMap (Polynomial F) C.FunctionField (1 : Polynomial F) *
          C.coordYInFunctionField := by
    rw [map_one, one_mul, _root_.map_neg]
    ring
  rw [h_form]
  have hp : -(WeierstrassCurve.Affine.linePolynomial x y slope) ≠ 0 ∨
      WeierstrassCurve.Affine.linePolynomial x y slope = 0 := by
    by_cases h : WeierstrassCurve.Affine.linePolynomial x y slope = 0
    · exact Or.inr h
    · exact Or.inl (neg_ne_zero.mpr h)
  rcases hp with hp_ne | hp_zero
  · have h_one_ne : (1 : Polynomial F) ≠ 0 := one_ne_zero
    rw [C.ordAtInfty_basis_polynomial_of_both_ne_zero hp_ne h_one_ne]
    have h_lp_deg : (WeierstrassCurve.Affine.linePolynomial x y slope).natDegree ≤ 1 := by
      unfold WeierstrassCurve.Affine.linePolynomial
      calc (Polynomial.C slope * (Polynomial.X - Polynomial.C x) + Polynomial.C y).natDegree
          ≤ max (Polynomial.C slope * (Polynomial.X - Polynomial.C x)).natDegree
                (Polynomial.C y).natDegree := Polynomial.natDegree_add_le _ _
        _ ≤ max 1 0 := by
            apply max_le_max
            · calc (Polynomial.C slope * (Polynomial.X - Polynomial.C x)).natDegree
                  ≤ (Polynomial.C slope).natDegree + (Polynomial.X - Polynomial.C x).natDegree :=
                    Polynomial.natDegree_mul_le
                _ ≤ 0 + 1 := by
                    apply Nat.add_le_add
                    · exact (Polynomial.natDegree_C _).le
                    · rw [Polynomial.natDegree_X_sub_C]
                _ = 1 := by ring
            · exact (Polynomial.natDegree_C _).le
        _ = 1 := by simp
    have h_neg_deg : (-WeierstrassCurve.Affine.linePolynomial x y slope).natDegree =
        (WeierstrassCurve.Affine.linePolynomial x y slope).natDegree :=
      Polynomial.natDegree_neg _
    rw [h_neg_deg, Polynomial.natDegree_one]
    have h_max : max (2 * (WeierstrassCurve.Affine.linePolynomial x y slope).natDegree)
        (2 * 0 + 3) = 3 := by
      have : 2 * (WeierstrassCurve.Affine.linePolynomial x y slope).natDegree ≤ 2 := by
        omega
      omega
    rw [h_max]
    rfl
  · rw [hp_zero, neg_zero, _root_.map_zero, _root_.map_one,
      one_mul, zero_add]
    exact C.ordAtInfty_coordYInFunctionField

/-- **Chord-line ideal factorisation** (wrapper of mathlib's `XYIdeal_mul_XYIdeal`):
the product `span{XClass(addX)} · maximalIdealAt(P) · maximalIdealAt(Q)`
equals `span{YClass(linePolynomial)} · maximalIdealAt(P+Q)` in
`C.CoordinateRing`. Here `P + Q ≠ 0` (non-degenerate hypothesis on the
addition). -/
theorem span_XClass_mul_maximalIdealAt_mul_eq
    [DecidableEq F]
    (SP SQ : C.SmoothPoint)
    (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y)) :
    Ideal.span ({WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine
        (C.toAffine.addX SP.x SQ.x (C.toAffine.slope SP.x SQ.x SP.y SQ.y))} :
        Set C.CoordinateRing) *
      (C.maximalIdealAt SP * C.maximalIdealAt SQ) =
      Ideal.span ({WeierstrassCurve.Affine.CoordinateRing.YClass C.toAffine
          (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
            (C.toAffine.slope SP.x SQ.x SP.y SQ.y))} :
          Set C.CoordinateRing) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal C.toAffine
          (C.toAffine.addX SP.x SQ.x (C.toAffine.slope SP.x SQ.x SP.y SQ.y))
          (Polynomial.C (C.toAffine.addY SP.x SQ.x SP.y
            (C.toAffine.slope SP.x SQ.x SP.y SQ.y))) := by
  have h_eqP : C.toAffine.Equation SP.x SP.y := SP.nonsingular.1
  have h_eqQ : C.toAffine.Equation SQ.x SQ.y := SQ.nonsingular.1
  rw [show (Ideal.span ({WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine
        (C.toAffine.addX SP.x SQ.x (C.toAffine.slope SP.x SQ.x SP.y SQ.y))} :
        Set C.CoordinateRing) :
        Ideal C.CoordinateRing) =
      WeierstrassCurve.Affine.CoordinateRing.XIdeal C.toAffine
        (C.toAffine.addX SP.x SQ.x (C.toAffine.slope SP.x SQ.x SP.y SQ.y))
      from rfl,
    show (Ideal.span ({WeierstrassCurve.Affine.CoordinateRing.YClass C.toAffine
          (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
            (C.toAffine.slope SP.x SQ.x SP.y SQ.y))} :
          Set C.CoordinateRing) :
          Ideal C.CoordinateRing) =
      WeierstrassCurve.Affine.CoordinateRing.YIdeal C.toAffine
        (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
          (C.toAffine.slope SP.x SQ.x SP.y SQ.y))
      from rfl]
  unfold maximalIdealAt
  exact WeierstrassCurve.Affine.CoordinateRing.XYIdeal_mul_XYIdeal
    h_eqP h_eqQ hxy

/-- **The smooth point `P + Q`** in non-degenerate position: takes two smooth
points `SP, SQ` and the non-degeneracy hypothesis (`¬(SP.x = SQ.x ∧ SP.y =
W.negY SQ.x SQ.y)`, i.e., `SP ≠ -SQ`), constructs the smooth point with
coordinates `(addX, addY)` from the addition formulae. -/
noncomputable def addSmoothPoint
    [DecidableEq F]
    (SP SQ : C.SmoothPoint)
    (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y)) :
    C.SmoothPoint where
  x := C.toAffine.addX SP.x SQ.x (C.toAffine.slope SP.x SQ.x SP.y SQ.y)
  y := C.toAffine.addY SP.x SQ.x SP.y (C.toAffine.slope SP.x SQ.x SP.y SQ.y)
  nonsingular := WeierstrassCurve.Affine.nonsingular_add SP.nonsingular
    SQ.nonsingular hxy

@[simp] theorem addSmoothPoint_x [DecidableEq F]
    (SP SQ : C.SmoothPoint)
    (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y)) :
    (C.addSmoothPoint SP SQ hxy).x =
      C.toAffine.addX SP.x SQ.x (C.toAffine.slope SP.x SQ.x SP.y SQ.y) := rfl

@[simp] theorem addSmoothPoint_y [DecidableEq F]
    (SP SQ : C.SmoothPoint)
    (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y)) :
    (C.addSmoothPoint SP SQ hxy).y =
      C.toAffine.addY SP.x SQ.x SP.y (C.toAffine.slope SP.x SQ.x SP.y SQ.y) := rfl

/-- **Chord-line ideal factorisation in SmoothPoint form**: the principal ideal
`span{XClass(SR.x)} · M_{SP} · M_{SQ}` equals
`span{YClass(linePoly)} · M_{SR}`, where `SR = addSmoothPoint SP SQ hxy`.
Direct SmoothPoint-level form of `span_XClass_mul_maximalIdealAt_mul_eq`. -/
theorem span_XClass_addSmoothPoint_mul_eq
    [DecidableEq F]
    (SP SQ : C.SmoothPoint)
    (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y)) :
    Ideal.span ({WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine
        (C.addSmoothPoint SP SQ hxy).x} :
        Set C.CoordinateRing) *
      (C.maximalIdealAt SP * C.maximalIdealAt SQ) =
      Ideal.span ({WeierstrassCurve.Affine.CoordinateRing.YClass C.toAffine
          (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
            (C.toAffine.slope SP.x SQ.x SP.y SQ.y))} :
          Set C.CoordinateRing) *
        C.maximalIdealAt (C.addSmoothPoint SP SQ hxy) := by
  rw [show C.maximalIdealAt (C.addSmoothPoint SP SQ hxy) =
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal C.toAffine
          (C.toAffine.addX SP.x SQ.x (C.toAffine.slope SP.x SQ.x SP.y SQ.y))
          (Polynomial.C (C.toAffine.addY SP.x SQ.x SP.y
            (C.toAffine.slope SP.x SQ.x SP.y SQ.y)))
      from rfl]
  exact C.span_XClass_mul_maximalIdealAt_mul_eq SP SQ hxy

/-- **Chord-line affine divisor (count-form bridge)**: the divisor coefficient
of `coordY − algMap (linePolynomial SP.x SP.y slope)` at a smooth point Q'
equals the count of `maximalIdealAt Q'` in the factorisation of
`span{YClass(linePolynomial)}`. Direct from
`divisorOf_algebraMap_apply_eq_count` + the YClass bridge. -/
theorem divisorOf_coordY_sub_algMap_linePolynomial_apply
    [IsIntegrallyClosed C.CoordinateRing]
    (x y slope : F) (Q' : C.SmoothPoint) :
    C.divisorOf (C.coordY -
        algebraMap (Polynomial F) C.FunctionField
          (WeierstrassCurve.Affine.linePolynomial x y slope)) Q' =
      ((Associates.mk (C.maximalIdealAt Q')).count
        (Associates.mk (Ideal.span
          {WeierstrassCurve.Affine.CoordinateRing.YClass C.toAffine
            (WeierstrassCurve.Affine.linePolynomial x y slope)})).factors : ℤ) := by
  have hu_ne : WeierstrassCurve.Affine.CoordinateRing.YClass C.toAffine
      (WeierstrassCurve.Affine.linePolynomial x y slope) ≠ 0 :=
    WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero (W' := C.toAffine) _
  rw [C.coordY_sub_algMap_linePolynomial_eq_algMap_YClass x y slope,
    C.divisorOf_algebraMap_apply_eq_count Q' hu_ne]

/-- **Chord-affine divisor (count expansion via structural identity)**: for
non-degenerate `SP, SQ` on E, the count of `M_{Q'}` in `span{YClass linePoly}`
equals `(divisorOf (coordX − SR.x) Q' + δ_{Q' = SP} + δ_{Q' = SQ} − δ_{Q' = SR})`
where `SR = addSmoothPoint SP SQ hxy`. Direct consequence of the structural
identity `span{XClass SR.x} · M_{SP} · M_{SQ} = span{YClass linePoly} · M_{SR}`
combined with `Associates.count_mul`. Stated as a ℤ-equation to handle the
subtraction. -/
theorem count_YClass_linePolynomial_eq
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)] [C.toAffine.IsElliptic]
    [IsIntegrallyClosed C.CoordinateRing] [DecidableEq F]
    (SP SQ : C.SmoothPoint)
    (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y))
    (Q' : C.SmoothPoint) :
    ((Associates.mk (C.maximalIdealAt Q')).count
      (Associates.mk (Ideal.span
        {WeierstrassCurve.Affine.CoordinateRing.YClass C.toAffine
          (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
            (C.toAffine.slope SP.x SQ.x SP.y SQ.y))})).factors : ℤ) +
      ((Associates.mk (C.maximalIdealAt Q')).count
        (Associates.mk (C.maximalIdealAt (C.addSmoothPoint SP SQ hxy))).factors : ℤ) =
      ((Associates.mk (C.maximalIdealAt Q')).count
        (Associates.mk (Ideal.span
          {WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine
            (C.addSmoothPoint SP SQ hxy).x})).factors : ℤ) +
      ((Associates.mk (C.maximalIdealAt Q')).count
        (Associates.mk (C.maximalIdealAt SP)).factors : ℤ) +
      ((Associates.mk (C.maximalIdealAt Q')).count
        (Associates.mk (C.maximalIdealAt SQ)).factors : ℤ) := by
  rw [show ∀ (a b : ℕ), (a : ℤ) + (b : ℤ) = ((a + b : ℕ) : ℤ) from
    fun a b ↦ by push_cast; ring,
    show ∀ (a b c : ℕ), (a : ℤ) + (b : ℤ) + (c : ℤ) = ((a + b + c : ℕ) : ℤ) from
    fun a b c ↦ by push_cast; ring]
  congr 1
  have hMSP_ne : (Associates.mk (C.maximalIdealAt SP) :
      Associates (Ideal C.CoordinateRing)) ≠ 0 :=
    Associates.mk_ne_zero.mpr (C.maximalIdealAt_ne_bot SP)
  have hMSQ_ne : (Associates.mk (C.maximalIdealAt SQ) :
      Associates (Ideal C.CoordinateRing)) ≠ 0 :=
    Associates.mk_ne_zero.mpr (C.maximalIdealAt_ne_bot SQ)
  have hMSR_ne : (Associates.mk (C.maximalIdealAt (C.addSmoothPoint SP SQ hxy)) :
      Associates (Ideal C.CoordinateRing)) ≠ 0 :=
    Associates.mk_ne_zero.mpr (C.maximalIdealAt_ne_bot (C.addSmoothPoint SP SQ hxy))
  have h_XClass_ne : (Associates.mk (Ideal.span
      ({WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine
        (C.addSmoothPoint SP SQ hxy).x} : Set C.CoordinateRing)) :
      Associates (Ideal C.CoordinateRing)) ≠ 0 := by
    rw [Associates.mk_ne_zero, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero
      (W' := C.toAffine) _
  have h_YClass_ne : (Associates.mk (Ideal.span
      ({WeierstrassCurve.Affine.CoordinateRing.YClass C.toAffine
        (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
          (C.toAffine.slope SP.x SQ.x SP.y SQ.y))} : Set C.CoordinateRing)) :
      Associates (Ideal C.CoordinateRing)) ≠ 0 := by
    rw [Associates.mk_ne_zero, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero
      (W' := C.toAffine) _
  let vQ' : IsDedekindDomain.HeightOneSpectrum C.CoordinateRing :=
    ⟨_, (C.maximalIdealAt_isMaximal Q').isPrime, C.maximalIdealAt_ne_bot Q'⟩
  have h_struct := C.span_XClass_addSmoothPoint_mul_eq SP SQ hxy
  have h_count_LHS_split :
      (Associates.mk vQ'.asIdeal).count
        (Associates.mk (Ideal.span
          ({WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine
            (C.addSmoothPoint SP SQ hxy).x} : Set C.CoordinateRing) *
          (C.maximalIdealAt SP * C.maximalIdealAt SQ))).factors =
      (Associates.mk vQ'.asIdeal).count
        (Associates.mk (Ideal.span
          ({WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine
            (C.addSmoothPoint SP SQ hxy).x} : Set C.CoordinateRing))).factors +
      ((Associates.mk vQ'.asIdeal).count
        (Associates.mk (C.maximalIdealAt SP)).factors +
       (Associates.mk vQ'.asIdeal).count
        (Associates.mk (C.maximalIdealAt SQ)).factors) := by
    rw [show (Associates.mk (Ideal.span
          ({WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine
            (C.addSmoothPoint SP SQ hxy).x} : Set C.CoordinateRing) *
          (C.maximalIdealAt SP * C.maximalIdealAt SQ)) :
          Associates (Ideal C.CoordinateRing)) =
        Associates.mk (Ideal.span
          ({WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine
            (C.addSmoothPoint SP SQ hxy).x} : Set C.CoordinateRing)) *
        Associates.mk (C.maximalIdealAt SP * C.maximalIdealAt SQ)
        from Associates.mk_mul_mk]
    rw [show (Associates.mk (C.maximalIdealAt SP * C.maximalIdealAt SQ) :
        Associates (Ideal C.CoordinateRing)) =
      Associates.mk (C.maximalIdealAt SP) *
        Associates.mk (C.maximalIdealAt SQ) from Associates.mk_mul_mk]
    rw [Associates.count_mul h_XClass_ne (mul_ne_zero hMSP_ne hMSQ_ne)
      vQ'.associates_irreducible,
      Associates.count_mul hMSP_ne hMSQ_ne vQ'.associates_irreducible]
  have h_count_RHS_split :
      (Associates.mk vQ'.asIdeal).count
        (Associates.mk (Ideal.span
          ({WeierstrassCurve.Affine.CoordinateRing.YClass C.toAffine
            (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
              (C.toAffine.slope SP.x SQ.x SP.y SQ.y))} : Set C.CoordinateRing) *
          C.maximalIdealAt (C.addSmoothPoint SP SQ hxy))).factors =
      (Associates.mk vQ'.asIdeal).count
        (Associates.mk (Ideal.span
          ({WeierstrassCurve.Affine.CoordinateRing.YClass C.toAffine
            (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
              (C.toAffine.slope SP.x SQ.x SP.y SQ.y))} :
              Set C.CoordinateRing))).factors +
      (Associates.mk vQ'.asIdeal).count
        (Associates.mk (C.maximalIdealAt (C.addSmoothPoint SP SQ hxy))).factors := by
    rw [show (Associates.mk (Ideal.span
          ({WeierstrassCurve.Affine.CoordinateRing.YClass C.toAffine
            (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
              (C.toAffine.slope SP.x SQ.x SP.y SQ.y))} : Set C.CoordinateRing) *
          C.maximalIdealAt (C.addSmoothPoint SP SQ hxy)) :
          Associates (Ideal C.CoordinateRing)) =
        Associates.mk (Ideal.span
          ({WeierstrassCurve.Affine.CoordinateRing.YClass C.toAffine
            (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
              (C.toAffine.slope SP.x SQ.x SP.y SQ.y))} : Set C.CoordinateRing)) *
        Associates.mk (C.maximalIdealAt (C.addSmoothPoint SP SQ hxy))
      from Associates.mk_mul_mk]
    rw [Associates.count_mul h_YClass_ne hMSR_ne vQ'.associates_irreducible]
  have h_struct_count :
      (Associates.mk vQ'.asIdeal).count
        (Associates.mk (Ideal.span
          ({WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine
            (C.addSmoothPoint SP SQ hxy).x} : Set C.CoordinateRing) *
          (C.maximalIdealAt SP * C.maximalIdealAt SQ))).factors =
      (Associates.mk vQ'.asIdeal).count
        (Associates.mk (Ideal.span
          ({WeierstrassCurve.Affine.CoordinateRing.YClass C.toAffine
            (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
              (C.toAffine.slope SP.x SQ.x SP.y SQ.y))} : Set C.CoordinateRing) *
          C.maximalIdealAt (C.addSmoothPoint SP SQ hxy))).factors := by
    rw [h_struct]
  linarith [h_count_LHS_split, h_count_RHS_split, h_struct_count]

/-- **Count of `maximalIdealAt X` at `Q'` in Finsupp form**: the count
(as ℤ) of `maximalIdealAt Q'` in the factorisation of `maximalIdealAt X`
equals `(Finsupp.single X 1) Q'`. Bridges the count-form to Finsupp.single. -/
theorem count_maximalIdealAt_eq_single
    [IsIntegrallyClosed C.CoordinateRing]
    (X Q' : C.SmoothPoint) :
    ((Associates.mk (C.maximalIdealAt Q')).count
      (Associates.mk (C.maximalIdealAt X)).factors : ℤ) =
      (Finsupp.single X (1 : ℤ)) Q' := by
  classical
  rw [Finsupp.single_apply]
  by_cases h : X = Q'
  · rw [h, if_pos rfl, C.count_maximalIdealAt_self Q']
    rfl
  · rw [if_neg h, C.count_maximalIdealAt_eq_zero_of_ne Q' X fun he ↦ h he.symm]
    rfl

/-- **Chord-line affine divisor (pointwise Finsupp identity)**: for
non-degenerate smooth points `SP, SQ` on E with `hxy : ¬(SP = -SQ)`,
`divisorOf (coordY − linePolynomial) Q' = (single SP 1 + single SQ 1 +
single SR.neg 1) Q'` where `SR = addSmoothPoint SP SQ hxy` is the smooth
point of `SP + SQ`. -/
theorem divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)] [C.toAffine.IsElliptic]
    [IsIntegrallyClosed C.CoordinateRing] [DecidableEq F]
    (SP SQ : C.SmoothPoint)
    (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y))
    (Q' : C.SmoothPoint) :
    C.divisorOf (C.coordY -
        algebraMap (Polynomial F) C.FunctionField
          (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
            (C.toAffine.slope SP.x SQ.x SP.y SQ.y))) Q' =
      ((Finsupp.single SP (1 : ℤ) + Finsupp.single SQ 1 +
        Finsupp.single (C.addSmoothPoint SP SQ hxy).neg 1 :
        C.SmoothPoint →₀ ℤ) Q') := by
  rw [C.divisorOf_coordY_sub_algMap_linePolynomial_apply SP.x SP.y _ Q']
  have h_count := C.count_YClass_linePolynomial_eq SP SQ hxy Q'
  have h_XClass_to_vertical :
      ((Associates.mk (C.maximalIdealAt Q')).count
        (Associates.mk (Ideal.span
          {WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine
            (C.addSmoothPoint SP SQ hxy).x})).factors : ℤ) =
      ((Finsupp.single (C.addSmoothPoint SP SQ hxy) (1 : ℤ) +
        Finsupp.single (C.addSmoothPoint SP SQ hxy).neg 1 :
        C.SmoothPoint →₀ ℤ) Q') := by
    rw [← C.divisorOf_coordX_sub_const_apply (C.addSmoothPoint SP SQ hxy).x Q']
    exact C.divisorOf_coordX_sub_const_apply_eq_finsupp
      (C.addSmoothPoint SP SQ hxy) Q'
  rw [h_XClass_to_vertical,
    C.count_maximalIdealAt_eq_single SP Q',
    C.count_maximalIdealAt_eq_single SQ Q',
    C.count_maximalIdealAt_eq_single (C.addSmoothPoint SP SQ hxy) Q'] at h_count
  simp only [Finsupp.add_apply] at h_count ⊢
  linarith [h_count]

/-- **Chord-line affine divisor (Finsupp form)**: the affine divisor of
`coordY − algMap (linePolynomial SP.x SP.y slope)` equals
`single SP 1 + single SQ 1 + single SR.neg 1` as a Finsupp, where
`SR = addSmoothPoint SP SQ hxy`. -/
theorem divisorOf_coordY_sub_algMap_linePolynomial
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)] [C.toAffine.IsElliptic]
    [IsIntegrallyClosed C.CoordinateRing] [DecidableEq F]
    (SP SQ : C.SmoothPoint)
    (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y)) :
    C.divisorOf (C.coordY -
        algebraMap (Polynomial F) C.FunctionField
          (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
            (C.toAffine.slope SP.x SQ.x SP.y SQ.y))) =
      Finsupp.single SP (1 : ℤ) + Finsupp.single SQ 1 +
        Finsupp.single (C.addSmoothPoint SP SQ hxy).neg 1 :=
  Finsupp.ext fun Q' ↦
    C.divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp SP SQ hxy Q'

/-- **Chord-line projective divisor**: the full projective divisor of
`coordY − algMap (linePolynomial)` is `(SP) + (SQ) + (SR.neg) − 3·(∞)`. -/
theorem projectiveDivisorOf_coordY_sub_algMap_linePolynomial
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)] [C.toAffine.IsElliptic]
    [IsIntegrallyClosed C.CoordinateRing] [DecidableEq F]
    (SP SQ : C.SmoothPoint)
    (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y)) :
    C.projectiveDivisorOf (C.coordY -
        algebraMap (Polynomial F) C.FunctionField
          (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
            (C.toAffine.slope SP.x SQ.x SP.y SQ.y))) =
      Finsupp.single (ProjectiveSmoothPoint.affine SP) (1 : ℤ)
        + Finsupp.single (ProjectiveSmoothPoint.affine SQ) 1
        + Finsupp.single (ProjectiveSmoothPoint.affine
            (C.addSmoothPoint SP SQ hxy).neg) 1
        - (3 : ℤ) • Finsupp.single ProjectiveSmoothPoint.infinity 1 := by
  unfold projectiveDivisorOf
  rw [C.divisorOf_coordY_sub_algMap_linePolynomial SP SQ hxy,
    C.ordAtInfty_coordY_sub_algMap_linePolynomial SP.x SP.y _,
    WithTop.untopD_coe]
  rw [Divisor.toProjective_add, Divisor.toProjective_add]
  have h_single_proj_SP :
      Divisor.toProjective (Finsupp.single SP (1 : ℤ) : Divisor C) =
        Finsupp.single (ProjectiveSmoothPoint.affine SP) 1 := by
    unfold Divisor.toProjective
    exact Finsupp.mapDomain_single
  have h_single_proj_SQ :
      Divisor.toProjective (Finsupp.single SQ (1 : ℤ) : Divisor C) =
        Finsupp.single (ProjectiveSmoothPoint.affine SQ) 1 := by
    unfold Divisor.toProjective
    exact Finsupp.mapDomain_single
  have h_single_proj_SRneg :
      Divisor.toProjective
          (Finsupp.single (C.addSmoothPoint SP SQ hxy).neg (1 : ℤ) :
            Divisor C) =
        Finsupp.single (ProjectiveSmoothPoint.affine
          (C.addSmoothPoint SP SQ hxy).neg) 1 := by
    unfold Divisor.toProjective
    exact Finsupp.mapDomain_single
  rw [h_single_proj_SP, h_single_proj_SQ, h_single_proj_SRneg]
  have h_three_smul : ((3 : ℤ) • Finsupp.single
      (ProjectiveSmoothPoint.infinity :
        ProjectiveSmoothPoint (⟨C.toAffine⟩ : SmoothPlaneCurve F)) (1 : ℤ) :
        ProjectiveDivisor (⟨C.toAffine⟩ : SmoothPlaneCurve F)) =
      Finsupp.single ProjectiveSmoothPoint.infinity 3 := by
    simp [Finsupp.smul_single]
  have h_neg_single : (Finsupp.single (ProjectiveSmoothPoint.infinity :
          ProjectiveSmoothPoint (⟨C.toAffine⟩ : SmoothPlaneCurve F)) (-3 : ℤ) :
          ProjectiveDivisor (⟨C.toAffine⟩ : SmoothPlaneCurve F)) =
        -Finsupp.single ProjectiveSmoothPoint.infinity 3 :=
    Finsupp.single_neg _ _
  rw [h_three_smul, h_neg_single]
  abel

/-- **Miller divisor at non-degenerate affine `(SP, SQ)` is principal**: for
smooth points `SP, SQ` with `SP ≠ -SQ`, the divisor `(SP) + (SQ) − (SP+SQ) − (∞)`
on the projective curve is principal, with witness the chord/tangent line
divided by the vertical line at `x(SP+SQ)`. -/
theorem miller_at_addSmoothPoint_principal
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)] [C.toAffine.IsElliptic]
    [IsIntegrallyClosed C.CoordinateRing] [DecidableEq F]
    (SP SQ : C.SmoothPoint)
    (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y)) :
    SmoothPlaneCurve.ProjIsPrincipal C
      (Finsupp.single (ProjectiveSmoothPoint.affine SP) (1 : ℤ)
        + Finsupp.single (ProjectiveSmoothPoint.affine SQ) 1
        - Finsupp.single (ProjectiveSmoothPoint.affine
            (C.addSmoothPoint SP SQ hxy)) 1
        - Finsupp.single (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint C) 1) := by
  set f := C.coordY -
    algebraMap (Polynomial F) C.FunctionField
      (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
        (C.toAffine.slope SP.x SQ.x SP.y SQ.y)) with hf_def
  set g := C.coordX -
    algebraMap F C.FunctionField (C.addSmoothPoint SP SQ hxy).x with hg_def
  have hf_ne : f ≠ 0 := C.coordY_sub_algMap_linePolynomial_ne_zero SP.x SP.y _
  have hg_ne : g ≠ 0 := C.coordX_sub_const_ne_zero (C.addSmoothPoint SP SQ hxy).x
  have hg_inv_ne : g⁻¹ ≠ 0 := inv_ne_zero hg_ne
  refine ⟨f * g⁻¹, mul_ne_zero hf_ne hg_inv_ne, ?_⟩
  rw [C.projectiveDivisorOf_mul hf_ne hg_inv_ne, C.projectiveDivisorOf_inv hg_ne,
    show C.projectiveDivisorOf f =
        Finsupp.single (ProjectiveSmoothPoint.affine SP) (1 : ℤ)
          + Finsupp.single (ProjectiveSmoothPoint.affine SQ) 1
          + Finsupp.single (ProjectiveSmoothPoint.affine
              (C.addSmoothPoint SP SQ hxy).neg) 1
          - (3 : ℤ) • Finsupp.single ProjectiveSmoothPoint.infinity 1 from
      C.projectiveDivisorOf_coordY_sub_algMap_linePolynomial SP SQ hxy,
    show C.projectiveDivisorOf g =
        Finsupp.single (ProjectiveSmoothPoint.affine
            (C.addSmoothPoint SP SQ hxy)) (1 : ℤ)
          + Finsupp.single (ProjectiveSmoothPoint.affine
              (C.addSmoothPoint SP SQ hxy).neg) 1
          - (2 : ℤ) • Finsupp.single ProjectiveSmoothPoint.infinity 1 from
      C.projectiveDivisorOf_coordX_sub_const (C.addSmoothPoint SP SQ hxy)]
  ext Q
  simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.coe_smul,
    Finsupp.coe_neg, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

end HasseWeil.Curves.SmoothPlaneCurve

namespace HasseWeil.Curves

variable {F : Type*} [Field F] [DecidableEq F]
  (W : WeierstrassCurve.Affine F) [W.IsElliptic]

omit [WeierstrassCurve.IsElliptic W] [DecidableEq F] in
/-- For `P = .some x y h`, the projective `(-P).toProj` equals the projective
form of `SmoothPoint.neg ⟨x, y, h⟩`. Direct via case analysis. -/
theorem _root_.WeierstrassCurve.Affine.Point.neg_some_toProjectiveSmoothPoint
    {x y : F} (h : W.Nonsingular x y) :
    (-WeierstrassCurve.Affine.Point.some x y h).toProjectiveSmoothPoint =
      ProjectiveSmoothPoint.affine
        ((⟨x, y, h⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint).neg) := by
  rfl

/-- **Miller at `(P, -P)` for affine `P`**: when `P = .some x y h`, the
Miller divisor `(P) + (-P) − (0) − (∞)` is principal, witnessed via the
vertical-line construction. -/
theorem miller_at_neg_of_some
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    {x y : F} (h_ns : W.Nonsingular x y) :
    SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
      (Finsupp.single (WeierstrassCurve.Affine.Point.some x y h_ns).toProjectiveSmoothPoint 1
        + Finsupp.single (-WeierstrassCurve.Affine.Point.some x y h_ns).toProjectiveSmoothPoint 1
        - Finsupp.single ((WeierstrassCurve.Affine.Point.some x y h_ns) +
            (-WeierstrassCurve.Affine.Point.some x y h_ns)).toProjectiveSmoothPoint 1
        - Finsupp.single (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) 1) := by
  apply miller_of_neg_of_vertical_principal
  let SP : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint := ⟨x, y, h_ns⟩
  have h_P_proj :
      (WeierstrassCurve.Affine.Point.some x y h_ns).toProjectiveSmoothPoint =
        ProjectiveSmoothPoint.affine SP := rfl
  have h_negP_proj :
      (-WeierstrassCurve.Affine.Point.some x y h_ns).toProjectiveSmoothPoint =
        ProjectiveSmoothPoint.affine SP.neg :=
    WeierstrassCurve.Affine.Point.neg_some_toProjectiveSmoothPoint W h_ns
  rw [h_P_proj, h_negP_proj]
  exact (⟨W⟩ : SmoothPlaneCurve F).vertical_line_principal SP

omit [WeierstrassCurve.IsElliptic W] in
/-- **Bridge `some + some` non-degenerate to projective-`affine` of
`addSmoothPoint`**: for `P = .some x₁ y₁ h₁` and `Q = .some x₂ y₂ h₂` with
the non-degeneracy hypothesis `hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)`, we
have `(P + Q).toProjectiveSmoothPoint = .affine (addSmoothPoint SP SQ hxy)`
where `SP = ⟨x₁, y₁, h₁⟩, SQ = ⟨x₂, y₂, h₂⟩`. -/
theorem _root_.WeierstrassCurve.Affine.Point.add_some_some_toProjectiveSmoothPoint
    {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
        (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)).toProjectiveSmoothPoint =
      ProjectiveSmoothPoint.affine
        ((⟨W⟩ : SmoothPlaneCurve F).addSmoothPoint
          ⟨x₁, y₁, h₁⟩ ⟨x₂, y₂, h₂⟩ hxy) := by
  rw [WeierstrassCurve.Affine.Point.add_some hxy]
  rfl

/-- **Miller at non-degenerate `some + some` is principal**: closes the
chord case of Miller for `P, Q : W.Point` both `.some` with `P + Q ≠ 0`.
Combines `miller_at_addSmoothPoint_principal` with the projective-form
bridge. -/
theorem miller_at_some_some_nondegen
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
      (Finsupp.single
            (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁).toProjectiveSmoothPoint 1
        + Finsupp.single
            (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂).toProjectiveSmoothPoint 1
        - Finsupp.single ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
            (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)).toProjectiveSmoothPoint 1
        - Finsupp.single (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) 1) := by
  rw [WeierstrassCurve.Affine.Point.add_some_some_toProjectiveSmoothPoint
      W h₁ h₂ hxy,
    show (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁).toProjectiveSmoothPoint =
        ProjectiveSmoothPoint.affine
          (⟨x₁, y₁, h₁⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) from rfl,
    show (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂).toProjectiveSmoothPoint =
        ProjectiveSmoothPoint.affine
          (⟨x₂, y₂, h₂⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) from rfl]
  exact SmoothPlaneCurve.miller_at_addSmoothPoint_principal
    (⟨W⟩ : SmoothPlaneCurve F) ⟨x₁, y₁, h₁⟩ ⟨x₂, y₂, h₂⟩ hxy

/-- **Miller at `(some x₁ y₁ h₁, some x₂ y₂ h₂)` with `P + Q = 0`**: the
degenerate sum case (`hxy` holds, i.e., `Q = −P`), closed via the
vertical-line principal divisor. -/
theorem miller_at_some_some_degen
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) :
    SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
      (Finsupp.single
            (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁).toProjectiveSmoothPoint 1
        + Finsupp.single
            (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂).toProjectiveSmoothPoint 1
        - Finsupp.single ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
            (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)).toProjectiveSmoothPoint 1
        - Finsupp.single (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) 1) := by
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2,
    show ((0 : W.Point)).toProjectiveSmoothPoint =
        (ProjectiveSmoothPoint.infinity :
          ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) from rfl]
  have h_x : x₂ = x₁ := hxy.1.symm
  have h_y : y₂ = W.negY x₁ y₁ := by
    have : W.negY x₂ y₁ = y₂ := by
      rw [hxy.2]
      exact WeierstrassCurve.Affine.negY_negY x₂ y₂
    rw [← this, ← hxy.1]
  have h_Q_proj :
      (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂).toProjectiveSmoothPoint =
        ProjectiveSmoothPoint.affine
          ((⟨x₁, y₁, h₁⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint).neg) := by
    have h_eq : (⟨x₂, y₂, h₂⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) =
        (⟨x₁, y₁, h₁⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint).neg :=
      HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.ext h_x h_y
    rw [show (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂).toProjectiveSmoothPoint =
        ProjectiveSmoothPoint.affine
          (⟨x₂, y₂, h₂⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) from rfl, h_eq]
  rw [h_Q_proj,
    show (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁).toProjectiveSmoothPoint =
        ProjectiveSmoothPoint.affine
          (⟨x₁, y₁, h₁⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) from rfl]
  have h_vert := (⟨W⟩ : SmoothPlaneCurve F).vertical_line_principal
    (⟨x₁, y₁, h₁⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
  convert h_vert using 1
  rw [show ((2 : ℤ) • Finsupp.single
      (ProjectiveSmoothPoint.infinity :
        ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ) :
        ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) =
      Finsupp.single ProjectiveSmoothPoint.infinity 1 +
        Finsupp.single ProjectiveSmoothPoint.infinity 1 by
    rw [show (2 : ℤ) = 1 + 1 from rfl, add_smul, one_smul]]
  abel

/-- **Miller's relation holds unconditionally** (`MillerHypothesis W` axiom-clean):
for any pair `P, Q : W.Point`, the divisor `(P) + (Q) − (P + Q) − (O)` is principal
on the projective curve. Combines the four cases:
- `P = 0`: `miller_of_zero_left`.
- `Q = 0`: `miller_of_zero_right`.
- `P, Q` both `.some` with `P + Q = 0` (degenerate sum): `miller_at_some_some_degen`.
- `P, Q` both `.some` with `P + Q ≠ 0` (non-degenerate): `miller_at_some_some_nondegen`.

The first three are closed via the vertical-line projective-divisor identity
(Silverman III.3.5's vertical case). The fourth via the chord/tangent line
divided by the vertical at `x(P + Q)` (Silverman III.3.5's chord-tangent case). -/
theorem miller_hypothesis_holds
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] :
    MillerHypothesis W := by
  intro P Q
  cases P with
  | zero =>
    change SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
      (Finsupp.single (0 : W.Point).toProjectiveSmoothPoint 1
        + Finsupp.single Q.toProjectiveSmoothPoint 1
        - Finsupp.single ((0 : W.Point) + Q).toProjectiveSmoothPoint 1
        - Finsupp.single (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) 1)
    exact miller_of_zero_left W Q
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      exact miller_of_zero_right W (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁)
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
      · exact miller_at_some_some_degen W h₁ h₂ hxy
      · exact miller_at_some_some_nondegen W h₁ h₂ hxy

/-- **General κ-reduction (Finsupp induction)**: for any projective divisor
`D`, `D` is linearly equivalent to `kappaDivisor W (σ D) + (deg D) • (∞)`,
where `σ` is the sum-of-points map. By Finsupp induction on `D`: the base
case `D = 0` is trivial; the step uses the unconditional `kappaDivisor` add /
zsmul / single-minus-inf identities. -/
theorem general_kappa_reduce
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) :
    SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F)
      D
      (kappaDivisor W (projectiveDivisorSum W D) +
        (ProjectiveDivisor.degree D) • Finsupp.single
          (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ)) := by
  have h_miller : MillerHypothesis W := miller_hypothesis_holds W
  induction D using Finsupp.induction with
  | zero =>
    rw [projectiveDivisorSum_zero, kappaDivisor_zero, ProjectiveDivisor.degree_zero,
      zero_smul, zero_add]
    exact SmoothPlaneCurve.ProjLinearlyEquiv.refl
      (C := (⟨W⟩ : SmoothPlaneCurve F)) 0
  | single_add P n D' _h_supp _h_n ih =>
    change SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
      ((Finsupp.single P n + D') -
        (kappaDivisor W (projectiveDivisorSum W (Finsupp.single P n + D')) +
          (ProjectiveDivisor.degree (Finsupp.single P n + D')) • Finsupp.single
            (ProjectiveSmoothPoint.infinity :
              ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ)))
    rw [projectiveDivisorSum_add, projectiveDivisorSum_single,
      ProjectiveDivisor.degree_add]
    have h_deg_single : ProjectiveDivisor.degree (Finsupp.single P n :
        ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) = n := by
      unfold ProjectiveDivisor.degree
      exact Finsupp.sum_single_index rfl
    rw [h_deg_single]
    have h_single_n : (Finsupp.single P n : ProjectiveDivisor
        (⟨W⟩ : SmoothPlaneCurve F)) - n • Finsupp.single
        (ProjectiveSmoothPoint.infinity :
          ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ) =
        n • kappaDivisor W P.toAffinePoint := by
      have h_base := single_minus_inf_eq_kappaDivisor W P
      have : n • (Finsupp.single P (1 : ℤ) - Finsupp.single
          (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ)) =
        n • kappaDivisor W P.toAffinePoint := by rw [h_base]
      rw [smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one] at this
      exact this
    have h_part1 : (Finsupp.single P n : ProjectiveDivisor
        (⟨W⟩ : SmoothPlaneCurve F)) - n • Finsupp.single
        (ProjectiveSmoothPoint.infinity :
          ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ) -
        n • kappaDivisor W P.toAffinePoint = 0 := by
      rw [h_single_n, sub_self]
    have h_part2 : SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
        (D' - (kappaDivisor W (projectiveDivisorSum W D') +
          (ProjectiveDivisor.degree D') • Finsupp.single
            (ProjectiveSmoothPoint.infinity :
              ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ))) := ih
    have h_part3_eq :
        SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F)
          (n • kappaDivisor W P.toAffinePoint + kappaDivisor W
            (projectiveDivisorSum W D'))
          (kappaDivisor W (n • P.toAffinePoint + projectiveDivisorSum W D')) := by
      have h_zsmul := (kappaDivisor_zsmul_linEquiv_of_miller W h_miller
        P.toAffinePoint n).symm
      have h_add := (kappaDivisor_add_linEquiv_of_miller W h_miller
        (n • P.toAffinePoint) (projectiveDivisorSum W D')).symm
      have h_step : SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F)
          (n • kappaDivisor W P.toAffinePoint +
            kappaDivisor W (projectiveDivisorSum W D'))
          (kappaDivisor W (n • P.toAffinePoint) +
            kappaDivisor W (projectiveDivisorSum W D')) := by
        change SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F) _
        have h_diff : (n • kappaDivisor W P.toAffinePoint +
              kappaDivisor W (projectiveDivisorSum W D')) -
            (kappaDivisor W (n • P.toAffinePoint) +
              kappaDivisor W (projectiveDivisorSum W D')) =
            n • kappaDivisor W P.toAffinePoint -
              kappaDivisor W (n • P.toAffinePoint) := by abel
        rw [h_diff]
        change SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
          (n • kappaDivisor W P.toAffinePoint - kappaDivisor W (n • P.toAffinePoint))
        have h_neg := (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup.neg_mem
          (h_zsmul.symm : SmoothPlaneCurve.ProjIsPrincipal _ _)
        have h_rw : -(kappaDivisor W (n • P.toAffinePoint) -
              n • kappaDivisor W P.toAffinePoint) =
            n • kappaDivisor W P.toAffinePoint -
              kappaDivisor W (n • P.toAffinePoint) := by abel
        rw [← h_rw]
        exact h_neg
      exact h_step.trans h_add
    have h_diff_eq :
        (Finsupp.single P n + D') -
          (kappaDivisor W (n • P.toAffinePoint + projectiveDivisorSum W D') +
            (n + ProjectiveDivisor.degree D') • Finsupp.single
              (ProjectiveSmoothPoint.infinity :
                ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ)) =
        ((Finsupp.single P n : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) -
            n • Finsupp.single
              (ProjectiveSmoothPoint.infinity :
                ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ) -
            n • kappaDivisor W P.toAffinePoint) +
        (D' - (kappaDivisor W (projectiveDivisorSum W D') +
          (ProjectiveDivisor.degree D') • Finsupp.single
            (ProjectiveSmoothPoint.infinity :
              ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ))) +
        ((n • kappaDivisor W P.toAffinePoint +
            kappaDivisor W (projectiveDivisorSum W D')) -
          kappaDivisor W (n • P.toAffinePoint +
            projectiveDivisorSum W D')) := by
      rw [add_smul]
      abel
    rw [h_diff_eq, h_part1, zero_add]
    have h_part3 : SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
        ((n • kappaDivisor W P.toAffinePoint +
          kappaDivisor W (projectiveDivisorSum W D')) -
        kappaDivisor W (n • P.toAffinePoint + projectiveDivisorSum W D')) :=
      h_part3_eq
    exact (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup.add_mem h_part2 h_part3

/-- **`DivZeroReduce W` is unconditional** (Target 2): for every degree-zero
projective divisor `D`, `D ~ kappaDivisor (σD)` (i.e., `D − ((σD) − (O))` is
principal). Direct corollary of `general_kappa_reduce` restricted to
degree-zero divisors. -/
theorem divZeroReduce_holds
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] :
    DivZeroReduce W := by
  intro D
  have h_deg : ProjectiveDivisor.degree D.val = 0 :=
    ProjectiveDivisor.mem_degZero.mp D.property
  have h_gen := general_kappa_reduce W D.val
  rw [h_deg, zero_smul, add_zero] at h_gen
  exact h_gen

/-- **`AFInputs W` is unconditional**: under the standard hypothesis cone
`[IsAlgClosed F] [NeZero 2] [NeZero 3] [IsElliptic] [IsIntegrallyClosed
C.CoordinateRing]` (acceptable per the §5 alg-closure-internal reframe),
the bundled `AFInputs` record is constructible directly from the shipped
Miller / DivZeroReduce / NoFinitePolesBridge unconditionals. -/
noncomputable def afInputs_unconditional
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] :
    AFInputs W where
  miller := miller_hypothesis_holds W
  divZeroReduce := divZeroReduce_holds W
  noFinitePolesBridge := noFinitePolesBridge_unconditional W

/-- **T-III-3-004 unconditional** (`Pic⁰(E) ≅ E`): the natural map
`picZeroOfPoint : W.Point → PicProj₀ C` is an `AddEquiv` for any elliptic
curve over an algebraically closed field of characteristic ≠ 2, 3.
Discharges `picZeroIsoE_of_AFInputs` against the unconditional `afInputs_unconditional`.

This is the **Pic⁰(E) ≅ E** isomorphism of Silverman III.3.4, ready for
downstream consumers in the §5 cascade (T-III-6-002 → §5.4 keystone → III.6.3
→ qf_nonneg). -/
noncomputable def picZeroIsoE
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] :
    SmoothPlaneCurve.PicProj₀ (⟨W⟩ : SmoothPlaneCurve F) ≃+ W.Point :=
  picZeroIsoE_of_AFInputs (afInputs_unconditional W)

/-- **T-III-3-004 over the algebraic closure (unconditional)**: applies
`picZeroIsoE` at `W.baseChange L` where `L` is algebraically closed. This
is the form the §5 cascade consumes (per the reviewer round-4 reframe:
build §5 over `L = AlgebraicClosure k_q`, descend `qf_nonneg` to `k_q`
at the very end). -/
noncomputable def picZeroIsoE_baseChange
    {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    [IsAlgClosed L] [NeZero (2 : L)] [NeZero (3 : L)]
    [(W.baseChange L).IsElliptic]
    [IsDedekindDomain (⟨W.baseChange L⟩ : SmoothPlaneCurve L).CoordinateRing]
    [IsIntegrallyClosed (⟨W.baseChange L⟩ : SmoothPlaneCurve L).CoordinateRing] :
    SmoothPlaneCurve.PicProj₀ (⟨W.baseChange L⟩ : SmoothPlaneCurve L) ≃+
      WeierstrassCurve.Affine.Point (W.baseChange L) :=
  picZeroIsoE (W.baseChange L)

/-- **`picZeroIsoE` symmetric = `picZeroOfPoint`**: the inverse of the
isomorphism is the natural map `P ↦ [(P) − (O)]`. Useful for downstream
consumers that need to apply the κ map. -/
@[simp] theorem picZeroIsoE_symm_apply
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (P : W.Point) :
    (picZeroIsoE W).symm P = picZeroOfPoint W P := rfl

/-- **`picZeroIsoE` applied to `picZeroOfPoint`**: the forward direction
of the isomorphism inverts `picZeroOfPoint`. -/
@[simp] theorem picZeroIsoE_picZeroOfPoint
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (P : W.Point) :
    picZeroIsoE W (picZeroOfPoint W P) = P := by
  rw [← picZeroIsoE_symm_apply W P, (picZeroIsoE W).apply_symm_apply]

/-- **σ vanishes on principal projective divisors** (T-PIC-A-002 closure):
for any principal projective divisor `D ∈ ProjPrincipalSubgroup`,
`projectiveDivisorSum W D = 0`. Direct corollary of `afInputs_unconditional`
+ Worker C's `principal_mem_degZero`. -/
theorem projectiveDivisorSum_eq_zero_of_principal
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    {D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)}
    (hD : D ∈ (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup) :
    projectiveDivisorSum W D = 0 :=
  (afInputs_unconditional W).h_van
    (fun _ hD' ↦
      SmoothPlaneCurve.principal_mem_degZero (C := (⟨W⟩ : SmoothPlaneCurve F)) hD')
    D hD

/-- **`σ̄ ∘ κ = id` at the Pic⁰ level** (T-PIC-B-003 closure): the sum-of-points
map descended to Pic⁰ (`σ̄`) inverts the κ map (`picZeroOfPoint`). This is
the `right_inv` of `picZeroIsoE`. -/
theorem sigmaBar_picZeroOfPoint
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (P : W.Point) :
    picZeroIsoE W (picZeroOfPoint W P) = P :=
  picZeroIsoE_picZeroOfPoint W P

/-- **`κ ∘ σ̄ = id` at the Pic⁰ level** (T-PIC-F-001c closure): every element
of Pic⁰ is `picZeroOfPoint W P` for some P. This is the `left_inv` of
`picZeroIsoE`. -/
theorem picZeroOfPoint_sigmaBar
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (D : SmoothPlaneCurve.PicProj₀ (⟨W⟩ : SmoothPlaneCurve F)) :
    picZeroOfPoint W (picZeroIsoE W D) = D := by
  rw [← picZeroIsoE_symm_apply W (picZeroIsoE W D), (picZeroIsoE W).symm_apply_apply]

/-- **Existence: every D ∈ Div⁰(E) is linearly equivalent to `(P) - (O)`**
(T-PIC-F-001a closure): for any degree-zero projective divisor `D`, there
exists a point `P : W.Point` such that `D ~ kappaDivisor W P` (i.e.,
`D ~ (P) - (O)`).

Witness: `P = projectiveDivisorSum W D.val` (the σ map). Direct corollary
of `divZeroReduce_holds`. -/
theorem exists_kappa_form
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (D : ProjectiveDivisor.degZero (⟨W⟩ : SmoothPlaneCurve F)) :
    ∃ P : W.Point,
      SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F)
        D.val (kappaDivisor W P) :=
  ⟨projectiveDivisorSum W D.val, divZeroReduce_holds W D⟩

/-- **`picZeroOfPoint` is injective** (Silverman III.3.4 injectivity / κ is
injective): the κ map `P ↦ [(P) - (O)] : W.Point → PicProj₀` is injective.
This is the `Equiv.symm` form of `picZeroIsoE`. -/
theorem picZeroOfPoint_injective
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] :
    Function.Injective (picZeroOfPoint W) := by
  intro P Q hPQ
  have h_iso : (picZeroIsoE W).symm P = (picZeroIsoE W).symm Q := by
    rw [picZeroIsoE_symm_apply, picZeroIsoE_symm_apply]
    exact hPQ
  exact (picZeroIsoE W).symm.injective h_iso

/-- **`picZeroEquiv`** (T-PIC-F-002 closure / Silverman III.3.4): alias for
`picZeroIsoE` matching the picard ticket naming convention. The Pic⁰(E) ≅ E
isomorphism as an `AddEquiv`. -/
noncomputable abbrev picZeroEquiv
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] :
    SmoothPlaneCurve.PicProj₀ (⟨W⟩ : SmoothPlaneCurve F) ≃+ W.Point :=
  picZeroIsoE W

/-- **`AddHomProperty_of_pushforward_principal`**: reduces the universal
Silverman III.4.8 AddHomProperty for an isogeny to the single hypothesis
`h_pres` (pushforward of principal divisors is principal — Worker C's
T-PIC-C-003). With Worker D's Miller + DivZeroReduce shipped unconditional,
the Miller and DivZeroReduce inputs of `AddHomProperty_of_miller_divZeroReduce`
discharge automatically.

This is the entry point for downstream consumers that have an isogeny `φ`
with a `CoordHom` witness and a pushforward-principal witness — applying
this lemma yields the full additive group hom property of `φ.toAddMonoidHom`
without any Miller/DivZeroReduce parameter. -/
theorem AddHomProperty_of_pushforward_principal
    {F : Type*} [Field F] [DecidableEq F]
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    [IsDedekindDomain (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsDedekindDomain (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    (φ : HasseWeil.EC.Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom)
    (h_pres : ∀ D : ProjectiveDivisor (⟨W₁⟩ : SmoothPlaneCurve F),
      D ∈ (⟨W₁⟩ : SmoothPlaneCurve F).projPrincipalSubgroup →
      HasseWeil.EC.Isogeny.pushforwardProjectiveDivisor φ cd D ∈
        (⟨W₂⟩ : SmoothPlaneCurve F).projPrincipalSubgroup) :
    φ.AddHomProperty cd :=
  AddHomProperty_of_miller_divZeroReduce φ cd
    (miller_hypothesis_holds W₁) (miller_hypothesis_holds W₂)
    (divZeroReduce_holds W₁) (divZeroReduce_holds W₂)
    h_pres

/-- **Uniqueness: `kappaDivisor W P ~ kappaDivisor W Q ⟹ P = Q`** (Silverman
III.3.3, T-PIC-F-001b closure): if the divisors `(P) - (O)` and `(Q) - (O)`
are linearly equivalent, then `P = Q` in the group of points. Direct
corollary of `picZeroOfPoint_injective` after lifting the divisor-level
equivalence to Pic⁰. -/
theorem kappaDivisor_inj
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    {P Q : W.Point}
    (h : SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F)
      (kappaDivisor W P) (kappaDivisor W Q)) :
    P = Q := by
  have h_pic : picZeroOfPoint W P = picZeroOfPoint W Q := by
    unfold picZeroOfPoint
    apply Quot.sound
    rw [QuotientAddGroup.leftRel_apply]
    change (-(⟨kappaDivisor W P, _⟩ : ProjectiveDivisor.degZero _) +
            ⟨kappaDivisor W Q, _⟩) ∈
      AddSubgroup.addSubgroupOf
        ((⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup)
        (ProjectiveDivisor.degZero (⟨W⟩ : SmoothPlaneCurve F))
    change (-kappaDivisor W P + kappaDivisor W Q) ∈
      (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup
    rw [show (-kappaDivisor W P + kappaDivisor W Q) =
        -(kappaDivisor W P - kappaDivisor W Q) by abel]
    exact (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup.neg_mem h
  exact picZeroOfPoint_injective W h_pic

end HasseWeil.Curves

namespace HasseWeil.Isogeny

variable {F : Type*} [Field F] [DecidableEq F]
variable {W : WeierstrassCurve.Affine F} [W.IsElliptic]
variable [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]
variable [IsDedekindDomain
  (⟨W⟩ : HasseWeil.Curves.SmoothPlaneCurve F).CoordinateRing]
variable [IsIntegrallyClosed
  (⟨W⟩ : HasseWeil.Curves.SmoothPlaneCurve F).CoordinateRing]

/-- **Pic⁰ pushforward via canonical iso**: instantiates
`HasseWeil.Isogeny.isogPicPushforward` at the canonical `picZeroIsoE`. -/
noncomputable def picZeroPushforward (α : HasseWeil.Isogeny W W) :
    HasseWeil.Curves.SmoothPlaneCurve.PicProj₀
        (⟨W⟩ : HasseWeil.Curves.SmoothPlaneCurve F) →+
      HasseWeil.Curves.SmoothPlaneCurve.PicProj₀
        (⟨W⟩ : HasseWeil.Curves.SmoothPlaneCurve F) :=
  isogPicPushforward (HasseWeil.Curves.picZeroIsoE W) α

/-- **Pic⁰ pullback via canonical iso (witness-parametric on dual)**:
given a dual `α_dual` of `α`, instantiates `isogPicPullback` at
`picZeroIsoE`. -/
noncomputable def picZeroPullback (α_dual : HasseWeil.Isogeny W W) :
    HasseWeil.Curves.SmoothPlaneCurve.PicProj₀
        (⟨W⟩ : HasseWeil.Curves.SmoothPlaneCurve F) →+
      HasseWeil.Curves.SmoothPlaneCurve.PicProj₀
        (⟨W⟩ : HasseWeil.Curves.SmoothPlaneCurve F) :=
  isogPicPullback (HasseWeil.Curves.picZeroIsoE W) α_dual

/-- **Pushforward compat via canonical iso**: the iso-conjugate
pushforward of `picZeroOfPoint W P` is `picZeroOfPoint W (α P)`. Direct
from `isogPicPushforward_compat`. -/
theorem picZeroPushforward_picZeroOfPoint
    (α : HasseWeil.Isogeny W W) (P : W.Point) :
    picZeroPushforward α (HasseWeil.Curves.picZeroOfPoint W P) =
      HasseWeil.Curves.picZeroOfPoint W (α.toAddMonoidHom P) := by
  unfold picZeroPushforward
  have h := isogPicPushforward_compat (HasseWeil.Curves.picZeroIsoE W) α P
  rw [HasseWeil.Curves.picZeroIsoE_symm_apply,
    HasseWeil.Curves.picZeroIsoE_symm_apply] at h
  exact h

/-- **Pullback ∘ pushforward = [deg α] on Pic⁰** via canonical iso:
given the dual identity `α_dual ∘ α = [deg α]` at the point level, the
composition on Pic⁰ equals scalar multiplication by `α.degree`. Direct
from `isogPicPullback_comp_pushforward`. -/
theorem picZeroPullback_comp_pushforward
    (α α_dual : HasseWeil.Isogeny W W)
    (h_dual : ∀ P : W.Point,
      α_dual.toAddMonoidHom (α.toAddMonoidHom P) = α.degree • P) :
    (picZeroPullback α_dual).comp (picZeroPushforward α) =
      (AddMonoidHom.id _).comp
        (α.degree • AddMonoidHom.id _) :=
  isogPicPullback_comp_pushforward (HasseWeil.Curves.picZeroIsoE W) α α_dual h_dual

/-- **Dual isogeny via canonical Pic⁰ iso (witness-parametric on dual)**:
given an endomorphism `α` and a candidate `α_dual` satisfying the dual
identity at the point level, the Silverman III.6.1(b) construction
`α̂ = κ ∘ α_pullback ∘ κ.symm` produces an isogeny with the dual
property. Direct instantiation of `dualOfPicZeroPullback` at the canonical
`picZeroIsoE`. -/
noncomputable def dualViaPicZero
    (α α_dual : HasseWeil.Isogeny W W) :
    HasseWeil.Isogeny W W :=
  dualOfPicZeroPullback _ (HasseWeil.Curves.picZeroIsoE W) α
    (picZeroPushforward α) (picZeroPullback α_dual) α_dual.pullback

/-- **Dual property for `dualViaPicZero`**: given the point-level dual
identity `α_dual ∘ α = [deg α]`, the constructed dual `dualViaPicZero α α_dual`
satisfies the III.6.1 functional equation. Direct application of
`h_dual_comp_from_picZeroPullback_witness` with the canonical iso and
the unconditional compat / pullback-pushforward identities. -/
theorem dualViaPicZero_comp_property
    (α α_dual : HasseWeil.Isogeny W W)
    (h_dual : ∀ P : W.Point,
      α_dual.toAddMonoidHom (α.toAddMonoidHom P) = α.degree • P) (P : W.Point) :
    (dualViaPicZero α α_dual).toAddMonoidHom (α.toAddMonoidHom P) =
      (α.degree : ℤ) • P :=
  h_dual_comp_from_picZeroPullback_witness _ (HasseWeil.Curves.picZeroIsoE W) α
    (picZeroPushforward α) (picZeroPullback α_dual) α_dual.pullback
    (fun P ↦ by
      have h := picZeroPushforward_picZeroOfPoint α P
      rw [HasseWeil.Curves.picZeroIsoE_symm_apply,
        HasseWeil.Curves.picZeroIsoE_symm_apply]
      exact h)
    (picZeroPullback_comp_pushforward α α_dual h_dual) P

/-- **Pic⁰-level Frobenius pushforward** for `E` over `F_p` base-changed
to algebraically-closed `L`. Direct instantiation of `picZeroPushforward`
at `frobeniusIsog_baseChange_charP_prime`. -/
noncomputable def frobeniusPicPushforward_charP_prime
    (p : ℕ) [hp : Fact p.Prime]
    (k : Type*) [Field k] [DecidableEq k]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p)]
    (W₀ : WeierstrassCurve k) [W₀.toAffine.IsElliptic]
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L]
    [IsAlgClosed L] [NeZero (2 : L)] [NeZero (3 : L)] [ExpChar L p]
    [(W₀.baseChange L).toAffine.IsElliptic]
    [IsDedekindDomain (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    [IsIntegrallyClosed (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing] :
    HasseWeil.Curves.SmoothPlaneCurve.PicProj₀
        (⟨(W₀.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L) →+
      HasseWeil.Curves.SmoothPlaneCurve.PicProj₀
        (⟨(W₀.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L) :=
  picZeroPushforward (W := (W₀.baseChange L).toAffine)
    (frobeniusIsog_baseChange_charP_prime p W₀ L)

/-- **Pushforward compat for Frobenius on Pic⁰** (`F_p` case): the
canonical iso transports the pointwise action of
`frobeniusIsog_baseChange_charP_prime` to its Pic⁰ pushforward.
Direct from `picZeroPushforward_picZeroOfPoint`. -/
theorem frobeniusPicPushforward_charP_prime_picZeroOfPoint
    (p : ℕ) [hp : Fact p.Prime]
    (k : Type*) [Field k] [DecidableEq k]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p)]
    (W₀ : WeierstrassCurve k) [W₀.toAffine.IsElliptic]
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L]
    [IsAlgClosed L] [NeZero (2 : L)] [NeZero (3 : L)] [ExpChar L p]
    [(W₀.baseChange L).toAffine.IsElliptic]
    [IsDedekindDomain (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    [IsIntegrallyClosed (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    (P : (W₀.baseChange L).toAffine.Point) :
    frobeniusPicPushforward_charP_prime p k W₀ L
        (HasseWeil.Curves.picZeroOfPoint (W₀.baseChange L).toAffine P) =
      HasseWeil.Curves.picZeroOfPoint (W₀.baseChange L).toAffine
        ((frobeniusIsog_baseChange_charP_prime p W₀ L).toAddMonoidHom P) :=
  picZeroPushforward_picZeroOfPoint
    (W := (W₀.baseChange L).toAffine)
    (frobeniusIsog_baseChange_charP_prime p W₀ L) P

/-- **Pic⁰-level Verschiebung pullback (witness-parametric on
Frobenius dual)** for `E` over `F_p` base-changed to algebraically-closed
`L`. Given a witness `α_dual : Isogeny (W.baseChange L) (W.baseChange L)`
serving as Frobenius's dual at the point level, this instantiates
`picZeroPullback` to yield the Pic⁰-level Verschiebung. -/
noncomputable def verschiebungPicPullback_charP_prime
    (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [DecidableEq k]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p)]
    (W₀ : WeierstrassCurve k) [W₀.toAffine.IsElliptic]
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L]
    [IsAlgClosed L] [NeZero (2 : L)] [NeZero (3 : L)] [ExpChar L p]
    [(W₀.baseChange L).toAffine.IsElliptic]
    [IsDedekindDomain (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    [IsIntegrallyClosed (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    (α_dual : HasseWeil.Isogeny (W₀.baseChange L).toAffine
      (W₀.baseChange L).toAffine) :
    HasseWeil.Curves.SmoothPlaneCurve.PicProj₀
        (⟨(W₀.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L) →+
      HasseWeil.Curves.SmoothPlaneCurve.PicProj₀
        (⟨(W₀.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L) :=
  picZeroPullback (W := (W₀.baseChange L).toAffine) α_dual

/-- **Verschiebung ∘ Frobenius = [p] on Pic⁰** (`F_p` case): given the
point-level identity `α_dual ∘ frobenius = [deg frobenius]` for some
witness dual, the composition of the Pic⁰-level Verschiebung pullback
and Frobenius pushforward equals scalar multiplication by
`frobeniusIsog_baseChange_charP_prime.degree`. Direct from
`picZeroPullback_comp_pushforward`. -/
theorem verschiebungPicPullback_comp_frobeniusPicPushforward
    (p : ℕ) [hp : Fact p.Prime]
    (k : Type*) [Field k] [DecidableEq k]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p)]
    (W₀ : WeierstrassCurve k) [W₀.toAffine.IsElliptic]
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L]
    [IsAlgClosed L] [NeZero (2 : L)] [NeZero (3 : L)] [ExpChar L p]
    [(W₀.baseChange L).toAffine.IsElliptic]
    [IsDedekindDomain (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    [IsIntegrallyClosed (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    (α_dual : HasseWeil.Isogeny (W₀.baseChange L).toAffine
      (W₀.baseChange L).toAffine)
    (h_dual : ∀ P : (W₀.baseChange L).toAffine.Point,
      α_dual.toAddMonoidHom
          ((frobeniusIsog_baseChange_charP_prime p W₀ L).toAddMonoidHom P) =
        (frobeniusIsog_baseChange_charP_prime p W₀ L).degree • P) :
    (verschiebungPicPullback_charP_prime p k W₀ L α_dual).comp
        (frobeniusPicPushforward_charP_prime p k W₀ L) =
      (AddMonoidHom.id _).comp
        ((frobeniusIsog_baseChange_charP_prime p W₀ L).degree •
          AddMonoidHom.id _) :=
  picZeroPullback_comp_pushforward
    (W := (W₀.baseChange L).toAffine)
    (frobeniusIsog_baseChange_charP_prime p W₀ L) α_dual h_dual

/-- **Dual of Frobenius via canonical Pic⁰ iso** (`F_p` case,
witness-parametric on dual): the Silverman III.6.1(b) construction
`α̂ = κ ∘ α_pullback ∘ κ.symm` applied to Frobenius yields an isogeny
with the dual property. Direct from `dualViaPicZero`. -/
noncomputable def frobeniusDualViaPicZero_charP_prime
    (p : ℕ) [hp : Fact p.Prime]
    (k : Type*) [Field k] [DecidableEq k]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p)]
    (W₀ : WeierstrassCurve k) [W₀.toAffine.IsElliptic]
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L]
    [IsAlgClosed L] [NeZero (2 : L)] [NeZero (3 : L)] [ExpChar L p]
    [(W₀.baseChange L).toAffine.IsElliptic]
    [IsDedekindDomain (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    [IsIntegrallyClosed (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    (α_dual : HasseWeil.Isogeny (W₀.baseChange L).toAffine
      (W₀.baseChange L).toAffine) :
    HasseWeil.Isogeny (W₀.baseChange L).toAffine
        (W₀.baseChange L).toAffine :=
  dualViaPicZero (W := (W₀.baseChange L).toAffine)
    (frobeniusIsog_baseChange_charP_prime p W₀ L) α_dual

/-- **Frobenius dual functional equation via Pic⁰** (`F_p` case): given
the point-level dual identity `α_dual ∘ frobenius = [deg frobenius]`,
the dual constructed via `frobeniusDualViaPicZero_charP_prime` satisfies
III.6.1's `α̂ ∘ α = [deg α]`. Direct from `dualViaPicZero_comp_property`. -/
theorem frobeniusDualViaPicZero_charP_prime_comp_property
    (p : ℕ) [hp : Fact p.Prime]
    (k : Type*) [Field k] [DecidableEq k]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p)]
    (W₀ : WeierstrassCurve k) [W₀.toAffine.IsElliptic]
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L]
    [IsAlgClosed L] [NeZero (2 : L)] [NeZero (3 : L)] [ExpChar L p]
    [(W₀.baseChange L).toAffine.IsElliptic]
    [IsDedekindDomain (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    [IsIntegrallyClosed (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    (α_dual : HasseWeil.Isogeny (W₀.baseChange L).toAffine
      (W₀.baseChange L).toAffine)
    (h_dual : ∀ P : (W₀.baseChange L).toAffine.Point,
      α_dual.toAddMonoidHom
          ((frobeniusIsog_baseChange_charP_prime p W₀ L).toAddMonoidHom P) =
        (frobeniusIsog_baseChange_charP_prime p W₀ L).degree • P)
    (P : (W₀.baseChange L).toAffine.Point) :
    (frobeniusDualViaPicZero_charP_prime p k W₀ L α_dual).toAddMonoidHom
        ((frobeniusIsog_baseChange_charP_prime p W₀ L).toAddMonoidHom P) =
      ((frobeniusIsog_baseChange_charP_prime p W₀ L).degree : ℤ) • P :=
  dualViaPicZero_comp_property (W := (W₀.baseChange L).toAffine)
    (frobeniusIsog_baseChange_charP_prime p W₀ L) α_dual h_dual P

/-- **Pic⁰-level Frobenius pushforward** for `E` over `F_{p^r}`
base-changed to algebraically-closed `L`. Direct instantiation of
`picZeroPushforward` at `frobeniusIsog_baseChange_charP_pow`. -/
noncomputable def frobeniusPicPushforward_charP_pow
    (p r : ℕ) [hp : Fact p.Prime]
    (k : Type*) [Field k] [DecidableEq k]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p ^ r)]
    (W₀ : WeierstrassCurve k) [W₀.toAffine.IsElliptic]
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L]
    [IsAlgClosed L] [NeZero (2 : L)] [NeZero (3 : L)] [ExpChar L p]
    [(W₀.baseChange L).toAffine.IsElliptic]
    [IsDedekindDomain (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    [IsIntegrallyClosed (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing] :
    HasseWeil.Curves.SmoothPlaneCurve.PicProj₀
        (⟨(W₀.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L) →+
      HasseWeil.Curves.SmoothPlaneCurve.PicProj₀
        (⟨(W₀.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L) :=
  picZeroPushforward (W := (W₀.baseChange L).toAffine)
    (frobeniusIsog_baseChange_charP_pow p r W₀ L)

/-- **Pushforward compat for Frobenius on Pic⁰** (`F_{p^r}` case): the
canonical iso transports the pointwise action of
`frobeniusIsog_baseChange_charP_pow` to its Pic⁰ pushforward. -/
theorem frobeniusPicPushforward_charP_pow_picZeroOfPoint
    (p r : ℕ) [hp : Fact p.Prime]
    (k : Type*) [Field k] [DecidableEq k]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p ^ r)]
    (W₀ : WeierstrassCurve k) [W₀.toAffine.IsElliptic]
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L]
    [IsAlgClosed L] [NeZero (2 : L)] [NeZero (3 : L)] [ExpChar L p]
    [(W₀.baseChange L).toAffine.IsElliptic]
    [IsDedekindDomain (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    [IsIntegrallyClosed (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    (P : (W₀.baseChange L).toAffine.Point) :
    frobeniusPicPushforward_charP_pow p r k W₀ L
        (HasseWeil.Curves.picZeroOfPoint (W₀.baseChange L).toAffine P) =
      HasseWeil.Curves.picZeroOfPoint (W₀.baseChange L).toAffine
        ((frobeniusIsog_baseChange_charP_pow p r W₀ L).toAddMonoidHom P) :=
  picZeroPushforward_picZeroOfPoint
    (W := (W₀.baseChange L).toAffine)
    (frobeniusIsog_baseChange_charP_pow p r W₀ L) P

/-- **Pic⁰-level Verschiebung pullback (witness-parametric on
Frobenius dual)** for `E` over `F_{p^r}`. -/
noncomputable def verschiebungPicPullback_charP_pow
    (p r : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [DecidableEq k]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p ^ r)]
    (W₀ : WeierstrassCurve k) [W₀.toAffine.IsElliptic]
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L]
    [IsAlgClosed L] [NeZero (2 : L)] [NeZero (3 : L)] [ExpChar L p]
    [(W₀.baseChange L).toAffine.IsElliptic]
    [IsDedekindDomain (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    [IsIntegrallyClosed (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    (α_dual : HasseWeil.Isogeny (W₀.baseChange L).toAffine
      (W₀.baseChange L).toAffine) :
    HasseWeil.Curves.SmoothPlaneCurve.PicProj₀
        (⟨(W₀.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L) →+
      HasseWeil.Curves.SmoothPlaneCurve.PicProj₀
        (⟨(W₀.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L) :=
  picZeroPullback (W := (W₀.baseChange L).toAffine) α_dual

/-- **Verschiebung ∘ Frobenius = [q] on Pic⁰** (`F_{p^r}` case): given
the point-level identity `α_dual ∘ frobenius = [deg frobenius]` for some
witness dual. -/
theorem verschiebungPicPullback_comp_frobeniusPicPushforward_charP_pow
    (p r : ℕ) [hp : Fact p.Prime]
    (k : Type*) [Field k] [DecidableEq k]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p ^ r)]
    (W₀ : WeierstrassCurve k) [W₀.toAffine.IsElliptic]
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L]
    [IsAlgClosed L] [NeZero (2 : L)] [NeZero (3 : L)] [ExpChar L p]
    [(W₀.baseChange L).toAffine.IsElliptic]
    [IsDedekindDomain (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    [IsIntegrallyClosed (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    (α_dual : HasseWeil.Isogeny (W₀.baseChange L).toAffine
      (W₀.baseChange L).toAffine)
    (h_dual : ∀ P : (W₀.baseChange L).toAffine.Point,
      α_dual.toAddMonoidHom
          ((frobeniusIsog_baseChange_charP_pow p r W₀ L).toAddMonoidHom P) =
        (frobeniusIsog_baseChange_charP_pow p r W₀ L).degree • P) :
    (verschiebungPicPullback_charP_pow p r k W₀ L α_dual).comp
        (frobeniusPicPushforward_charP_pow p r k W₀ L) =
      (AddMonoidHom.id _).comp
        ((frobeniusIsog_baseChange_charP_pow p r W₀ L).degree •
          AddMonoidHom.id _) :=
  picZeroPullback_comp_pushforward
    (W := (W₀.baseChange L).toAffine)
    (frobeniusIsog_baseChange_charP_pow p r W₀ L) α_dual h_dual

/-- **Dual of Frobenius via canonical Pic⁰ iso** (`F_{p^r}` case,
witness-parametric on dual). -/
noncomputable def frobeniusDualViaPicZero_charP_pow
    (p r : ℕ) [hp : Fact p.Prime]
    (k : Type*) [Field k] [DecidableEq k]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p ^ r)]
    (W₀ : WeierstrassCurve k) [W₀.toAffine.IsElliptic]
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L]
    [IsAlgClosed L] [NeZero (2 : L)] [NeZero (3 : L)] [ExpChar L p]
    [(W₀.baseChange L).toAffine.IsElliptic]
    [IsDedekindDomain (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    [IsIntegrallyClosed (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    (α_dual : HasseWeil.Isogeny (W₀.baseChange L).toAffine
      (W₀.baseChange L).toAffine) :
    HasseWeil.Isogeny (W₀.baseChange L).toAffine
        (W₀.baseChange L).toAffine :=
  dualViaPicZero (W := (W₀.baseChange L).toAffine)
    (frobeniusIsog_baseChange_charP_pow p r W₀ L) α_dual

/-- **Frobenius dual functional equation via Pic⁰** (`F_{p^r}` case). -/
theorem frobeniusDualViaPicZero_charP_pow_comp_property
    (p r : ℕ) [hp : Fact p.Prime]
    (k : Type*) [Field k] [DecidableEq k]
    [Fintype k] [CharP k p] [Fact (Fintype.card k = p ^ r)]
    (W₀ : WeierstrassCurve k) [W₀.toAffine.IsElliptic]
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L]
    [IsAlgClosed L] [NeZero (2 : L)] [NeZero (3 : L)] [ExpChar L p]
    [(W₀.baseChange L).toAffine.IsElliptic]
    [IsDedekindDomain (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    [IsIntegrallyClosed (⟨(W₀.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing]
    (α_dual : HasseWeil.Isogeny (W₀.baseChange L).toAffine
      (W₀.baseChange L).toAffine)
    (h_dual : ∀ P : (W₀.baseChange L).toAffine.Point,
      α_dual.toAddMonoidHom
          ((frobeniusIsog_baseChange_charP_pow p r W₀ L).toAddMonoidHom P) =
        (frobeniusIsog_baseChange_charP_pow p r W₀ L).degree • P)
    (P : (W₀.baseChange L).toAffine.Point) :
    (frobeniusDualViaPicZero_charP_pow p r k W₀ L α_dual).toAddMonoidHom
        ((frobeniusIsog_baseChange_charP_pow p r W₀ L).toAddMonoidHom P) =
      ((frobeniusIsog_baseChange_charP_pow p r W₀ L).degree : ℤ) • P :=
  dualViaPicZero_comp_property (W := (W₀.baseChange L).toAffine)
    (frobeniusIsog_baseChange_charP_pow p r W₀ L) α_dual h_dual P

end HasseWeil.Isogeny

namespace HasseWeil.Curves.SmoothPlaneCurve

variable {F : Type*} [Field F] [DecidableEq F]
  (C : HasseWeil.Curves.SmoothPlaneCurve F)

/-- **σ vanishes on the chord-line divisor** (T-PIC-A-002a explicit form):
for non-degenerate `SP, SQ`, the σ map applied to the chord-line's
projective divisor equals zero. Direct corollary of
`projectiveDivisorSum_eq_zero_of_principal` plus the chord line being
principal (witnessed by `coordY − algMap linePoly`). -/
theorem projectiveDivisorSum_chord_line
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)] [C.toAffine.IsElliptic]
    [IsDedekindDomain C.CoordinateRing]
    [IsIntegrallyClosed C.CoordinateRing]
    (SP SQ : C.SmoothPoint)
    (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y)) :
    HasseWeil.Curves.projectiveDivisorSum C.toAffine
      (Finsupp.single (HasseWeil.Curves.ProjectiveSmoothPoint.affine SP) (1 : ℤ)
        + Finsupp.single (HasseWeil.Curves.ProjectiveSmoothPoint.affine SQ) 1
        + Finsupp.single (HasseWeil.Curves.ProjectiveSmoothPoint.affine
            (C.addSmoothPoint SP SQ hxy).neg) 1
        - (3 : ℤ) • Finsupp.single HasseWeil.Curves.ProjectiveSmoothPoint.infinity 1) = 0 := by
  rw [← C.projectiveDivisorOf_coordY_sub_algMap_linePolynomial SP SQ hxy]
  exact HasseWeil.Curves.projectiveDivisorSum_eq_zero_of_principal C.toAffine
    ⟨_, C.coordY_sub_algMap_linePolynomial_ne_zero SP.x SP.y _, rfl⟩

/-- **σ vanishes on the vertical-line divisor** (T-PIC-A-002b explicit form):
the σ map applied to the vertical-line's projective divisor `(P) + (P.neg) − 2(∞)`
equals zero. Direct corollary. -/
theorem projectiveDivisorSum_vertical_line_of_principal
    [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)] [C.toAffine.IsElliptic]
    [IsDedekindDomain C.CoordinateRing]
    [IsIntegrallyClosed C.CoordinateRing]
    (P : C.SmoothPoint) :
    HasseWeil.Curves.projectiveDivisorSum C.toAffine
      (Finsupp.single (HasseWeil.Curves.ProjectiveSmoothPoint.affine P) (1 : ℤ)
        + Finsupp.single (HasseWeil.Curves.ProjectiveSmoothPoint.affine P.neg) 1
        - (2 : ℤ) • Finsupp.single HasseWeil.Curves.ProjectiveSmoothPoint.infinity 1) = 0 :=
  HasseWeil.Curves.projectiveDivisorSum_eq_zero_of_principal C.toAffine
    (C.vertical_line_principal P)

end HasseWeil.Curves.SmoothPlaneCurve

namespace HasseWeil.Curves.SmoothPlaneCurve

variable {F : Type*} [Field F] [DecidableEq F] (C : HasseWeil.Curves.SmoothPlaneCurve F)

omit [DecidableEq F] in
/-- **T-PIC-C-003a (explicit form)**: `pointValuation P` of an algebra-map
element from `F[C]` equals `intValuation` of the height-one prime
`smoothPointToHeightOne P`. Direct corollary of
`pointValuation_algebraMap_eq_exp_count` (project) and `intValuation_if_neg`
(mathlib). -/
theorem pointValuation_algebraMap_eq_intValuation
    [IsDedekindDomain C.CoordinateRing] [IsIntegrallyClosed C.CoordinateRing]
    (P : C.SmoothPoint) (u : C.CoordinateRing) :
    C.pointValuation P (algebraMap C.CoordinateRing C.FunctionField u) =
      (HasseWeil.Curves.smoothPointToHeightOne C.toAffine P).intValuation u := by
  by_cases hu : u = 0
  · rw [hu, map_zero, map_zero, Valuation.map_zero]
  · rw [C.pointValuation_algebraMap_eq_exp_count P hu,
      IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg _ hu]
    rfl

end HasseWeil.Curves.SmoothPlaneCurve
