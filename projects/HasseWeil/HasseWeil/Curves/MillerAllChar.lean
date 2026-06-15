/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.Miller

/-!
# Miller's relation — char-uniform version

This file ships `miller_hypothesis_holds_allChar`: the projective Miller divisor
relation `(P) + (Q) − (P+Q) − (O) ∈ Princ` for every pair `P, Q : W.Point`,
without the `[NeZero (2 : F)]` / `[NeZero (3 : F)]` typeclass restrictions
used by `Curves.miller_hypothesis_holds`.

The mathematical content (Silverman III.3.4(e) proof, p. 63) is **uniform in
characteristic**: the chord/tangent line through `P, Q` on the smooth
Weierstrass cubic exists in every characteristic, with the substantive
divisor identities discharged via the mathlib `XYIdeal_mul_XYIdeal`
factorisation — which is itself char-uniform (it does not assume
`[NeZero (2 : F)]` or `[NeZero (3 : F)]`).

The `[NeZero 2/3]` typeclasses in `Curves.Miller` were **inert** on the
chord/tangent divisor chain (they propagated through but were not used in
the proof bodies of the key count-form lemmas). This file re-proves the
chain dropping the inert typeclasses.

## Implementation notes

The `Pic⁰ ≅ E` constructions still carry the `[NeZero 2/3]` typeclasses only
because they discharge the `PrincipalImpliesDegZero` witness through
`principal_mem_degZero` (`NormValuation.lean`), whose chain inherits those
typeclasses inertly via `divisorOf_algMap_degree_eq_natDegree_norm`. Weakening
that chain to char-uniform is the dedicated sub-ticket
`T10-SUB-PRINCIPAL-DEGZERO-ALLCHAR`; `picZeroIsoE_of_AFInputs_witness_pdz_allChar`
factors out the obstruction by taking the degree-zero witness as an explicit
hypothesis, so composing the iso itself needs no characteristic assumption.

## Main results

* `vertical_line_principal_allChar` — `(P) + (P.neg) − 2·(O) ∈ Princ`
  in any characteristic.
* `miller_at_addSmoothPoint_principal_allChar` — non-degenerate Miller
  divisor is principal in any characteristic.
* `miller_hypothesis_holds_allChar` — `MillerHypothesis W` in any
  characteristic.
* `picZeroIsoE_allChar` — `Pic⁰(E) ≅ E` (Abel–Jacobi) in any characteristic.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.3.4(e) (p. 63).
-/

open WeierstrassCurve

namespace HasseWeil.Curves.SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)

/-- **Vertical-line affine divisor (pointwise Finsupp identity, all char)**:
char-uniform version of `divisorOf_coordX_sub_const_apply_eq_finsupp`. -/
theorem divisorOf_coordX_sub_const_apply_eq_finsupp_allChar
    [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] (P Q : C.SmoothPoint) :
    C.divisorOf (C.coordX - algebraMap F C.FunctionField P.x) Q =
      ((Finsupp.single P (1 : ℤ) + Finsupp.single P.neg 1 :
        C.SmoothPoint →₀ ℤ) Q) := by
  classical
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
    exact Associates.count_mul (Associates.mk_ne_zero.mpr (C.maximalIdealAt_ne_bot P.neg))
      (Associates.mk_ne_zero.mpr (C.maximalIdealAt_ne_bot P)) vQ.associates_irreducible
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

/-- **Vertical-line affine divisor (Finsupp form, all char)**. -/
theorem divisorOf_coordX_sub_const_allChar
    [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] (P : C.SmoothPoint) :
    C.divisorOf (C.coordX - algebraMap F C.FunctionField P.x) =
      Finsupp.single P (1 : ℤ) + Finsupp.single P.neg 1 :=
  Finsupp.ext fun Q ↦ C.divisorOf_coordX_sub_const_apply_eq_finsupp_allChar P Q

/-- **Vertical-line projective divisor (all char)**: the full projective
divisor of `coordX − P.x` is `(P) + (P.neg) − 2·(∞)`. -/
theorem projectiveDivisorOf_coordX_sub_const_allChar
    [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] (P : C.SmoothPoint) :
    C.projectiveDivisorOf (C.coordX - algebraMap F C.FunctionField P.x) =
      Finsupp.single (ProjectiveSmoothPoint.affine P) (1 : ℤ)
        + Finsupp.single (ProjectiveSmoothPoint.affine P.neg) 1
        - (2 : ℤ) • Finsupp.single ProjectiveSmoothPoint.infinity 1 := by
  unfold projectiveDivisorOf
  rw [C.divisorOf_coordX_sub_const_allChar P, C.ordAtInfty_coordX_sub_const P.x,
    WithTop.untopD_coe, Divisor.toProjective_add, Divisor.toProjective_single,
    Divisor.toProjective_single, Finsupp.smul_single, smul_eq_mul, mul_one,
    show (-2 : ℤ) = -(2 : ℤ) from rfl, Finsupp.single_neg]
  abel

/-- **Vertical-line is principal at any affine smooth point (all char)**. -/
theorem vertical_line_principal_allChar
    [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] (P : C.SmoothPoint) :
    SmoothPlaneCurve.ProjIsPrincipal C
      (Finsupp.single (ProjectiveSmoothPoint.affine P) (1 : ℤ)
        + Finsupp.single (ProjectiveSmoothPoint.affine P.neg) 1
        - (2 : ℤ) • Finsupp.single (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint C) 1) :=
  ⟨C.coordX - algebraMap F C.FunctionField P.x,
   C.coordX_sub_const_ne_zero P.x,
   C.projectiveDivisorOf_coordX_sub_const_allChar P⟩

/-- **Chord-line count identity (all char)**: char-uniform version of
`count_YClass_linePolynomial_eq` (`Miller.lean:791`). -/
theorem count_YClass_linePolynomial_eq_allChar
    [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] [DecidableEq F]
    (SP SQ : C.SmoothPoint) (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y))
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
        from Associates.mk_mul_mk,
      show (Associates.mk (C.maximalIdealAt SP * C.maximalIdealAt SQ) :
        Associates (Ideal C.CoordinateRing)) =
      Associates.mk (C.maximalIdealAt SP) *
        Associates.mk (C.maximalIdealAt SQ) from Associates.mk_mul_mk,
      Associates.count_mul h_XClass_ne (mul_ne_zero hMSP_ne hMSQ_ne)
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
    rw [C.span_XClass_addSmoothPoint_mul_eq SP SQ hxy]
  linarith [h_count_LHS_split, h_count_RHS_split, h_struct_count]

/-- **Chord-line affine divisor (pointwise Finsupp identity, all char)**. -/
theorem divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp_allChar
    [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] [DecidableEq F]
    (SP SQ : C.SmoothPoint) (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y))
    (Q' : C.SmoothPoint) :
    C.divisorOf (C.coordY -
        algebraMap (Polynomial F) C.FunctionField
          (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
            (C.toAffine.slope SP.x SQ.x SP.y SQ.y))) Q' =
      ((Finsupp.single SP (1 : ℤ) + Finsupp.single SQ 1 +
        Finsupp.single (C.addSmoothPoint SP SQ hxy).neg 1 :
        C.SmoothPoint →₀ ℤ) Q') := by
  rw [C.divisorOf_coordY_sub_algMap_linePolynomial_apply SP.x SP.y _ Q']
  have h_count := C.count_YClass_linePolynomial_eq_allChar SP SQ hxy Q'
  have h_XClass_to_vertical :
      ((Associates.mk (C.maximalIdealAt Q')).count
        (Associates.mk (Ideal.span
          {WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine
            (C.addSmoothPoint SP SQ hxy).x})).factors : ℤ) =
      ((Finsupp.single (C.addSmoothPoint SP SQ hxy) (1 : ℤ) +
        Finsupp.single (C.addSmoothPoint SP SQ hxy).neg 1 :
        C.SmoothPoint →₀ ℤ) Q') := by
    rw [← C.divisorOf_coordX_sub_const_apply (C.addSmoothPoint SP SQ hxy).x Q']
    exact C.divisorOf_coordX_sub_const_apply_eq_finsupp_allChar
      (C.addSmoothPoint SP SQ hxy) Q'
  rw [h_XClass_to_vertical,
    C.count_maximalIdealAt_eq_single SP Q',
    C.count_maximalIdealAt_eq_single SQ Q',
    C.count_maximalIdealAt_eq_single (C.addSmoothPoint SP SQ hxy) Q'] at h_count
  simp only [Finsupp.add_apply] at h_count ⊢
  linarith [h_count]

/-- **Chord-line affine divisor (Finsupp form, all char)**. -/
theorem divisorOf_coordY_sub_algMap_linePolynomial_allChar
    [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] [DecidableEq F]
    (SP SQ : C.SmoothPoint) (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y)) :
    C.divisorOf (C.coordY -
        algebraMap (Polynomial F) C.FunctionField
          (WeierstrassCurve.Affine.linePolynomial SP.x SP.y
            (C.toAffine.slope SP.x SQ.x SP.y SQ.y))) =
      Finsupp.single SP (1 : ℤ) + Finsupp.single SQ 1 +
        Finsupp.single (C.addSmoothPoint SP SQ hxy).neg 1 :=
  Finsupp.ext fun Q' ↦
    C.divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp_allChar
      SP SQ hxy Q'

/-- **Chord-line projective divisor (all char)**: the full projective divisor
of `coordY − algMap (linePolynomial)` is `(SP) + (SQ) + (SR.neg) − 3·(∞)`. -/
theorem projectiveDivisorOf_coordY_sub_algMap_linePolynomial_allChar
    [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] [DecidableEq F]
    (SP SQ : C.SmoothPoint) (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y)) :
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
  rw [C.divisorOf_coordY_sub_algMap_linePolynomial_allChar SP SQ hxy,
    C.ordAtInfty_coordY_sub_algMap_linePolynomial SP.x SP.y _,
    WithTop.untopD_coe, Divisor.toProjective_add, Divisor.toProjective_add,
    Divisor.toProjective_single, Divisor.toProjective_single, Divisor.toProjective_single,
    Finsupp.smul_single, smul_eq_mul, mul_one,
    show (-3 : ℤ) = -(3 : ℤ) from rfl, Finsupp.single_neg]
  abel

/-- **Miller divisor at non-degenerate affine `(SP, SQ)` is principal (all char)**.
Char-uniform `miller_at_addSmoothPoint_principal`. -/
theorem miller_at_addSmoothPoint_principal_allChar
    [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] [DecidableEq F]
    (SP SQ : C.SmoothPoint) (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y)) :
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
        (C.toAffine.slope SP.x SQ.x SP.y SQ.y))
  set g := C.coordX -
    algebraMap F C.FunctionField (C.addSmoothPoint SP SQ hxy).x
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
      C.projectiveDivisorOf_coordY_sub_algMap_linePolynomial_allChar SP SQ hxy,
    show C.projectiveDivisorOf g =
        Finsupp.single (ProjectiveSmoothPoint.affine
            (C.addSmoothPoint SP SQ hxy)) (1 : ℤ)
          + Finsupp.single (ProjectiveSmoothPoint.affine
              (C.addSmoothPoint SP SQ hxy).neg) 1
          - (2 : ℤ) • Finsupp.single ProjectiveSmoothPoint.infinity 1 from
      C.projectiveDivisorOf_coordX_sub_const_allChar (C.addSmoothPoint SP SQ hxy)]
  ext Q
  simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.coe_smul,
    Finsupp.coe_neg, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

end HasseWeil.Curves.SmoothPlaneCurve

namespace HasseWeil.Curves

variable {F : Type*} [Field F] [DecidableEq F]
  (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **Miller at `(P, -P)` for affine `P` (all char)**: when `P = .some x y h`,
the Miller divisor `(P) + (-P) − (0) − (∞)` is principal via the
vertical-line construction, in any characteristic. -/
theorem miller_at_neg_of_some_allChar
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] {x y : F}
    (h_ns : W.Nonsingular x y) :
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
  exact (⟨W⟩ : SmoothPlaneCurve F).vertical_line_principal_allChar SP

/-- **Miller at non-degenerate `some + some` is principal (all char)**. -/
theorem miller_at_some_some_nondegen_allChar
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] {x₁ x₂ y₁ y₂ : F}
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
  exact SmoothPlaneCurve.miller_at_addSmoothPoint_principal_allChar
    (⟨W⟩ : SmoothPlaneCurve F) ⟨x₁, y₁, h₁⟩ ⟨x₂, y₂, h₂⟩ hxy

/-- **Miller at degenerate `some + some` (P + Q = 0) is principal (all char)**. -/
theorem miller_at_some_some_degen_allChar
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] {x₁ x₂ y₁ y₂ : F}
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
  have h_y : y₂ = W.negY x₁ y₁ := by
    have : W.negY x₂ y₁ = y₂ := by
      rw [hxy.2]
      exact WeierstrassCurve.Affine.negY_negY x₂ y₂
    rw [← this, ← hxy.1]
  have h_eq : (⟨x₂, y₂, h₂⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) =
      (⟨x₁, y₁, h₁⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint).neg :=
    HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.ext hxy.1.symm h_y
  have h_Q_proj :
      (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂).toProjectiveSmoothPoint =
        ProjectiveSmoothPoint.affine
          ((⟨x₁, y₁, h₁⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint).neg) := by
    rw [show (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂).toProjectiveSmoothPoint =
        ProjectiveSmoothPoint.affine
          (⟨x₂, y₂, h₂⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) from rfl, h_eq]
  rw [h_Q_proj,
    show (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁).toProjectiveSmoothPoint =
        ProjectiveSmoothPoint.affine
          (⟨x₁, y₁, h₁⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) from rfl]
  convert (⟨W⟩ : SmoothPlaneCurve F).vertical_line_principal_allChar
    (⟨x₁, y₁, h₁⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) using 1
  rw [show ((2 : ℤ) • Finsupp.single
      (ProjectiveSmoothPoint.infinity :
        ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ) :
        ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) =
      Finsupp.single ProjectiveSmoothPoint.infinity 1 +
        Finsupp.single ProjectiveSmoothPoint.infinity 1 from by
    rw [show (2 : ℤ) = 1 + 1 from rfl, add_smul, one_smul]]
  abel

/-- **Miller's relation holds unconditionally** (`MillerHypothesis W` axiom-clean,
all char): for any pair `P, Q : W.Point`, the divisor
`(P) + (Q) − (P + Q) − (O)` is principal on the projective curve, in any
characteristic. -/
theorem miller_hypothesis_holds_allChar
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] : MillerHypothesis W := by
  intro P Q
  cases P with
  | zero => exact miller_of_zero_left W Q
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      exact miller_of_zero_right W (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁)
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
      · exact miller_at_some_some_degen_allChar W h₁ h₂ hxy
      · exact miller_at_some_some_nondegen_allChar W h₁ h₂ hxy

/-- **General κ-reduction (witness-parametric)**: same statement as
`general_kappa_reduce`, but takes `MillerHypothesis W` as a hypothesis
rather than depending on `[NeZero 2/3]`. -/
theorem general_kappa_reduce_of_miller
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (h_miller : MillerHypothesis W) (D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) :
    SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F)
      D
      (kappaDivisor W (projectiveDivisorSum W D) +
        (ProjectiveDivisor.degree D) • Finsupp.single
          (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ)) := by
  induction D using Finsupp.induction with
  | zero =>
    rw [projectiveDivisorSum_zero, kappaDivisor_zero,
      ProjectiveDivisor.degree_zero, zero_smul, zero_add]
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
      have : n • (Finsupp.single P (1 : ℤ) - Finsupp.single
          (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ)) =
        n • kappaDivisor W P.toAffinePoint := by
        rw [single_minus_inf_eq_kappaDivisor W P]
      rw [smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one] at this
      exact this
    have h_part1 : (Finsupp.single P n : ProjectiveDivisor
        (⟨W⟩ : SmoothPlaneCurve F)) - n • Finsupp.single
        (ProjectiveSmoothPoint.infinity :
          ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ) -
        n • kappaDivisor W P.toAffinePoint = 0 := by
      rw [h_single_n, sub_self]
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
    exact (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup.add_mem ih h_part3_eq

/-- **`DivZeroReduce W` axiom-clean (all char)**: char-uniform
`divZeroReduce_holds`. -/
theorem divZeroReduce_holds_allChar
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] : DivZeroReduce W := by
  intro D
  have h_gen := general_kappa_reduce_of_miller W
    (miller_hypothesis_holds_allChar W) D.val
  rw [ProjectiveDivisor.mem_degZero.mp D.property, zero_smul, add_zero] at h_gen
  exact h_gen

/-- **`picZeroIsoE_of_AFInputs` (all char)**: char-uniform version of
`Curves.picZeroIsoE_of_AFInputs`. -/
noncomputable def picZeroIsoE_of_AFInputs_allChar
    [IsAlgClosed F] [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] (a : AFInputs W) :
    SmoothPlaneCurve.PicProj₀ (⟨W⟩ : SmoothPlaneCurve F) ≃+ W.Point :=
  let h_van : ∀ D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F),
      D ∈ (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup →
      Curves.projectiveDivisorSum W D = 0 :=
    a.h_van (fun _ hD ↦ SmoothPlaneCurve.principal_mem_degZero (C := ⟨W⟩) hD)
  let sigmaBar : SmoothPlaneCurve.PicProj₀ (⟨W⟩ : SmoothPlaneCurve F) →+ W.Point :=
    HasseWeil.EC.Isogeny.picZeroSumOfWitness W h_van
  { toFun := sigmaBar
    invFun := picZeroOfPoint W
    left_inv := fun D ↦
      h_inj_of_divZeroReduce W a.divZeroReduce h_van D
    right_inv := fun P ↦
      HasseWeil.EC.Isogeny.picZeroSumOfWitness_picZeroOfPoint W h_van P
    map_add' := sigmaBar.map_add }

/-- **`AFInputs W` (all char)**: bundles `miller_hypothesis_holds_allChar`,
`divZeroReduce_holds_allChar`, and `noFinitePolesBridge_unconditional`. -/
noncomputable def afInputs_allChar
    [IsAlgClosed F] [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] : AFInputs W where
  miller := miller_hypothesis_holds_allChar W
  divZeroReduce := divZeroReduce_holds_allChar W
  noFinitePolesBridge := noFinitePolesBridge_unconditional W

/-- **Pic⁰(E) ≅ E (all char)**: char-uniform `picZeroIsoE`. -/
noncomputable def picZeroIsoE_allChar
    [IsAlgClosed F] [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] :
    SmoothPlaneCurve.PicProj₀ (⟨W⟩ : SmoothPlaneCurve F) ≃+ W.Point :=
  picZeroIsoE_of_AFInputs_allChar W (afInputs_allChar W)

/-- **`picZeroIsoE_of_AFInputs` witness-parametric on `h_pdz` (genuinely
all-char)**: composes the Pic⁰(E) ≅ E iso without `[NeZero 2/3]`. Takes
`PrincipalImpliesDegZero W` as an explicit hypothesis. Discharges to fully
unconditional once `T10-SUB-PRINCIPAL-DEGZERO-ALLCHAR` ships. -/
noncomputable def picZeroIsoE_of_AFInputs_witness_pdz_allChar
    [IsAlgClosed F] [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] (a : AFInputs W)
    (h_pdz : ∀ D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F),
      D ∈ (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup →
      D ∈ ProjectiveDivisor.degZero (⟨W⟩ : SmoothPlaneCurve F)) :
    SmoothPlaneCurve.PicProj₀ (⟨W⟩ : SmoothPlaneCurve F) ≃+ W.Point :=
  let h_van : ∀ D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F),
      D ∈ (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup →
      Curves.projectiveDivisorSum W D = 0 :=
    a.h_van h_pdz
  let sigmaBar : SmoothPlaneCurve.PicProj₀ (⟨W⟩ : SmoothPlaneCurve F) →+ W.Point :=
    HasseWeil.EC.Isogeny.picZeroSumOfWitness W h_van
  { toFun := sigmaBar
    invFun := picZeroOfPoint W
    left_inv := fun D ↦
      h_inj_of_divZeroReduce W a.divZeroReduce h_van D
    right_inv := fun P ↦
      HasseWeil.EC.Isogeny.picZeroSumOfWitness_picZeroOfPoint W h_van P
    map_add' := sigmaBar.map_add }

end HasseWeil.Curves
