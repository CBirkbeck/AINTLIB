/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.PicZero

/-!
# Effective sum reduction via Miller's relation

For an elliptic curve `E`, the **Miller relation**
`(P) + (Q) − (P+Q) − (O) ~ 0` (Silverman III.3.5 corollary, derived from
the chord/tangent group law) lets us reduce any sum of single-point
divisors to a single point plus a multiple of `(O)`. This is the
combinatorial core of `degree_zero_divisor_reduce`.

This file ships the LIST-INDUCTION reduction taking Miller as a
hypothesis. The geometric construction of the witness function for Miller
itself (the chord/tangent line as an element of `K(E)`) is its own ticket
(`T-PIC-AF-UNIFIED.md`, piece (b)).

## Main results

* `MillerHypothesis W` — predicate that Miller's relation holds.
* `effective_sum_reduce` — for any nonempty list of `W.Point`s, the
  effective divisor is linearly equivalent to a single divisor at the
  sum-point plus `(length − 1) · (O)`.

## Implementation notes

The `kappaDivisor_*_of_miller` lemmas are the "homomorphism mod principal"
corollaries of Miller: the map `κ : E → Pic⁰` is a group homomorphism, so at
the divisor level `κ(P+Q)`, `κ(-P)`, `κ(n·P)` differ from
`κ(P)+κ(Q)`, `-κ(P)`, `n·κ(P)` only by a principal divisor.
`single_minus_inf_eq_kappaDivisor` gives the uniform bridge
`single Q 1 − single ∞ 1 = κ(Q.toAffinePoint)` (equality for affine `Q`).

These assemble into the planned generalisation
`general_kappa_reduce_of_miller`, by `Finsupp` induction on the divisor: the
base case `D = 0` is trivial; the step `D = single P n + D'` rewrites
`single P n` via `single_minus_inf_eq_kappaDivisor` + `kappaDivisor_zsmul`,
applies the inductive hypothesis to `D'`, combines via `kappaDivisor_add`,
and collects the `∞`-coefficients (`deg D' + n = deg D`). Restricting to
`D ∈ degZero` then yields `DivZeroReduce W`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.3.5 (corollary).
-/

open WeierstrassCurve

namespace HasseWeil.Curves

variable {F : Type*} [Field F] [DecidableEq F]
  (W : Affine F) [W.IsElliptic]

/-- The Miller hypothesis: for every pair `P, Q : W.Point`, the divisor
`(P) + (Q) − (P+Q) − (O)` is principal. The geometric proof constructs
the chord/tangent line through the relevant points (separate ticket). -/
def MillerHypothesis : Prop :=
  ∀ P Q : W.Point,
    SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
      (Finsupp.single P.toProjectiveSmoothPoint 1
        + Finsupp.single Q.toProjectiveSmoothPoint 1
        - Finsupp.single (P + Q).toProjectiveSmoothPoint 1
        - Finsupp.single (ProjectiveSmoothPoint.infinity :
            ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) 1)

/-- The divisor associated to a list of points. -/
noncomputable def listToDivisor (Ps : List W.Point) :
    ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F) :=
  Ps.foldr (fun P acc => Finsupp.single P.toProjectiveSmoothPoint 1 + acc) 0

omit [DecidableEq F] [W.IsElliptic] in
@[simp] theorem listToDivisor_nil :
    listToDivisor W [] = 0 := rfl

omit [DecidableEq F] [W.IsElliptic] in
@[simp] theorem listToDivisor_cons (P : W.Point) (Ps : List W.Point) :
    listToDivisor W (P :: Ps) =
      Finsupp.single P.toProjectiveSmoothPoint 1 + listToDivisor W Ps := rfl

/-- The sum of points in a list. -/
noncomputable def listSum (Ps : List W.Point) : W.Point :=
  Ps.foldr (· + ·) 0

omit [W.IsElliptic] in
@[simp] theorem listSum_nil : listSum W [] = 0 := rfl

omit [W.IsElliptic] in
@[simp] theorem listSum_cons (P : W.Point) (Ps : List W.Point) :
    listSum W (P :: Ps) = P + listSum W Ps := rfl

/-- σ on the list-divisor equals the list sum. -/
theorem projectiveDivisorSum_listToDivisor (Ps : List W.Point) :
    projectiveDivisorSum W (listToDivisor W Ps) = listSum W Ps := by
  induction Ps with
  | nil => simp
  | cons P Ps ih =>
    rw [listToDivisor_cons, listSum_cons,
      projectiveDivisorSum_add, projectiveDivisorSum_single]
    rw [P.toProjectiveSmoothPoint_toAffinePoint, one_zsmul, ih]

private noncomputable def infDiv : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F) :=
  Finsupp.single (ProjectiveSmoothPoint.infinity :
    ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) 1

omit [DecidableEq F] [W.IsElliptic] in
private theorem ProjLinearlyEquiv.add_left
    {D₁ D₂ E : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)}
    (h : SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F) D₁ D₂) :
    SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F)
      (E + D₁) (E + D₂) := by
  change SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F) _
  rw [show E + D₁ - (E + D₂) = D₁ - D₂ by abel]
  exact h

omit [W.IsElliptic] in
private theorem single_add_infDiv_step_of_miller (h_miller : MillerHypothesis W)
    (P S : W.Point) (m : ℤ) :
    SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F)
      (Finsupp.single P.toProjectiveSmoothPoint 1 +
        (Finsupp.single S.toProjectiveSmoothPoint 1 + m • infDiv W))
      (Finsupp.single (P + S).toProjectiveSmoothPoint 1 + (m + 1) • infDiv W) := by
  change SmoothPlaneCurve.ProjIsPrincipal _ _
  rw [show (Finsupp.single P.toProjectiveSmoothPoint 1 +
        (Finsupp.single S.toProjectiveSmoothPoint 1 + m • infDiv W)) -
      (Finsupp.single (P + S).toProjectiveSmoothPoint 1 + (m + 1) • infDiv W) =
      Finsupp.single P.toProjectiveSmoothPoint 1
        + Finsupp.single S.toProjectiveSmoothPoint 1
        - Finsupp.single (P + S).toProjectiveSmoothPoint 1 - infDiv W by
    rw [add_smul, one_smul]; abel]
  unfold infDiv
  exact h_miller P S

omit [W.IsElliptic] in
/-- **Effective sum reduction**: for a nonempty list of points `[P_1, ..., P_n]`,
the effective divisor `(P_1) + ... + (P_n)` is linearly equivalent to
`(P_1 + ... + P_n) + (n − 1) · (O)`. -/
theorem effective_sum_reduce
    (h_miller : MillerHypothesis W)
    (Ps : List W.Point) (h_ne : Ps ≠ []) :
    SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F)
      (listToDivisor W Ps)
      (Finsupp.single (listSum W Ps).toProjectiveSmoothPoint 1
        + ((Ps.length : ℤ) - 1) • infDiv W) := by
  induction Ps with
  | nil => exact absurd rfl h_ne
  | cons P Ps ih =>
    cases Ps with
    | nil =>
      rw [show (((P :: List.nil).length : ℤ) - 1) = 0 by simp, zero_smul]
      simp only [listToDivisor_cons, listToDivisor_nil, add_zero, listSum_cons, listSum_nil]
      exact SmoothPlaneCurve.ProjLinearlyEquiv.refl (C := (⟨W⟩ : SmoothPlaneCurve F)) _
    | cons P' Ps' =>
      have h_tail := ih (List.cons_ne_nil _ _)
      rw [listToDivisor_cons, listSum_cons,
        show ((P :: P' :: Ps').length : ℤ) - 1 = (((P' :: Ps').length : ℤ) - 1) + 1 by
          push_cast [List.length_cons]; ring]
      exact (ProjLinearlyEquiv.add_left W
        (E := Finsupp.single P.toProjectiveSmoothPoint 1) h_tail).trans
        (single_add_infDiv_step_of_miller W h_miller P (listSum W (P' :: Ps')) _)

omit [DecidableEq F] [W.IsElliptic] in
private theorem zero_toProj :
    (0 : W.Point).toProjectiveSmoothPoint =
      (ProjectiveSmoothPoint.infinity :
        ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) := rfl

omit [W.IsElliptic] in
/-- **Vertical-line principal** (Silverman III.3.5, vertical case): the divisor
`(S) + (-S) - 2·(O)` is principal — the "vertical line at `x = x(S)`" passes
through `S`, `-S`, and infinity (twice). -/
theorem vertical_principal_of_miller
    (h_miller : MillerHypothesis W) (S : W.Point) :
    SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
      (Finsupp.single S.toProjectiveSmoothPoint 1
        + Finsupp.single (-S).toProjectiveSmoothPoint 1
        - (2 : ℤ) • (Finsupp.single
            (ProjectiveSmoothPoint.infinity :
              ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ))) := by
  have h := h_miller S (-S)
  rw [add_neg_cancel S, zero_toProj W] at h
  convert h using 1
  rw [two_smul]
  abel

omit [W.IsElliptic] in
/-- **Sub-form of Miller**: `(R) − (S) ~ (R−S) − (O)` at the divisor level, i.e.
`(R) − (S) − (R−S) + (O)` is principal. -/
theorem sub_principal_of_miller
    (h_miller : MillerHypothesis W) (R S : W.Point) :
    SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
      (Finsupp.single R.toProjectiveSmoothPoint 1
        - Finsupp.single S.toProjectiveSmoothPoint 1
        - Finsupp.single (R - S).toProjectiveSmoothPoint 1
        + Finsupp.single
            (ProjectiveSmoothPoint.infinity :
              ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) 1) := by
  have h_sub := (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup.sub_mem
    (h_miller R (-S)) (vertical_principal_of_miller W h_miller S)
  rw [show R + -S = R - S from sub_eq_add_neg R S |>.symm] at h_sub
  rw [SmoothPlaneCurve.mem_projPrincipalSubgroup] at h_sub
  convert h_sub using 1
  rw [two_smul]
  abel

omit [W.IsElliptic] in
/-- **Single-difference kappa reduction**: `(P) − (Q) ~ (P−Q) − (O)`, i.e.
`sub_principal_of_miller` packaged as a `ProjLinearlyEquiv`. -/
theorem single_diff_kappa_reduce_of_miller
    (h_miller : MillerHypothesis W) (P Q : W.Point) :
    SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F)
      (Finsupp.single P.toProjectiveSmoothPoint 1
        - Finsupp.single Q.toProjectiveSmoothPoint 1)
      (kappaDivisor W (P - Q)) := by
  change SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F) _
  unfold kappaDivisor
  convert sub_principal_of_miller W h_miller P Q using 1
  abel

omit [DecidableEq F] [W.IsElliptic] in
/-- `kappaDivisor` of the basepoint is zero. -/
@[simp] theorem kappaDivisor_zero :
    kappaDivisor W (0 : W.Point) = 0 := by
  rw [kappaDivisor, zero_toProj, sub_self]

omit [W.IsElliptic] in
/-- `kappaDivisor` is additive modulo principal: `κ(P + Q) ~ κ(P) + κ(Q)`. -/
theorem kappaDivisor_add_linEquiv_of_miller
    (h_miller : MillerHypothesis W) (P Q : W.Point) :
    SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F)
      (kappaDivisor W (P + Q))
      (kappaDivisor W P + kappaDivisor W Q) := by
  change SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F) _
  unfold kappaDivisor
  convert SmoothPlaneCurve.mem_projPrincipalSubgroup.mp
    ((⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup.neg_mem (h_miller P Q)) using 1
  abel

omit [W.IsElliptic] in
/-- `kappaDivisor` of a negation: `κ(−P) ~ −κ(P)`. -/
theorem kappaDivisor_neg_linEquiv_of_miller
    (h_miller : MillerHypothesis W) (P : W.Point) :
    SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F)
      (kappaDivisor W (-P))
      (-kappaDivisor W P) := by
  change SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F) _
  unfold kappaDivisor
  convert vertical_principal_of_miller W h_miller P using 1
  rw [two_smul]
  abel

omit [W.IsElliptic] in
/-- `kappaDivisor` is `ℕ`-scalar-multiplicative modulo principal:
`κ(n·P) ~ n · κ(P)`. -/
theorem kappaDivisor_nsmul_linEquiv_of_miller
    (h_miller : MillerHypothesis W) (P : W.Point) (n : ℕ) :
    SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F)
      (kappaDivisor W (n • P))
      (n • kappaDivisor W P) := by
  induction n with
  | zero =>
    rw [show (0 • P : W.Point) = 0 from zero_smul _ _, kappaDivisor_zero,
      zero_smul]
    exact SmoothPlaneCurve.ProjLinearlyEquiv.refl
      (C := (⟨W⟩ : SmoothPlaneCurve F)) _
  | succ k ih =>
    rw [show (k + 1) • P = k • P + P from AddMonoid.nsmul_succ k P,
      show ((k + 1) • kappaDivisor W P :
          ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)) =
        k • kappaDivisor W P + kappaDivisor W P from
      AddMonoid.nsmul_succ k _]
    refine (kappaDivisor_add_linEquiv_of_miller W h_miller (k • P) P).trans ?_
    change SmoothPlaneCurve.ProjIsPrincipal _ _
    rw [show (kappaDivisor W (k • P) + kappaDivisor W P) -
        (k • kappaDivisor W P + kappaDivisor W P) =
        kappaDivisor W (k • P) - k • kappaDivisor W P by abel]
    exact ih

omit [DecidableEq F] [W.IsElliptic] in
/-- For any `Q : ProjectiveSmoothPoint`, the divisor
`single Q 1 − single ∞ 1` is **equal** (not just equivalent) to
`kappaDivisor W Q.toAffinePoint`. -/
theorem single_minus_inf_eq_kappaDivisor (Q : ProjectiveSmoothPoint
    (⟨W⟩ : SmoothPlaneCurve F)) :
    Finsupp.single Q (1 : ℤ) - Finsupp.single
        (ProjectiveSmoothPoint.infinity :
          ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ) =
      kappaDivisor W Q.toAffinePoint := by
  unfold kappaDivisor
  cases Q with
  | infinity =>
    change Finsupp.single (ProjectiveSmoothPoint.infinity :
        ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ) -
      Finsupp.single (ProjectiveSmoothPoint.infinity :
        ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ) =
      Finsupp.single (0 : W.Point).toProjectiveSmoothPoint (1 : ℤ) -
      Finsupp.single (ProjectiveSmoothPoint.infinity :
        ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) (1 : ℤ)
    rfl
  | affine P => rfl

omit [W.IsElliptic] in
/-- ℤ-version of `kappaDivisor_nsmul_linEquiv_of_miller`:
`κ(n·P) ~ n·κ(P)` for `n : ℤ`. -/
theorem kappaDivisor_zsmul_linEquiv_of_miller
    (h_miller : MillerHypothesis W) (P : W.Point) (n : ℤ) :
    SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F)
      (kappaDivisor W (n • P))
      (n • kappaDivisor W P) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [show ((m : ℤ) • P : W.Point) = m • P from natCast_zsmul P m,
        show ((m : ℤ) • kappaDivisor W P : ProjectiveDivisor _) =
          m • kappaDivisor W P from natCast_zsmul _ m]
    exact kappaDivisor_nsmul_linEquiv_of_miller W h_miller P m
  · rw [show ((-↑m : ℤ) • P : W.Point) = -(m • P) by rw [neg_zsmul, natCast_zsmul],
      show ((-↑m : ℤ) • kappaDivisor W P : ProjectiveDivisor _) =
          -(m • kappaDivisor W P) by rw [neg_zsmul, natCast_zsmul]]
    refine (kappaDivisor_neg_linEquiv_of_miller W h_miller (m • P)).trans ?_
    change SmoothPlaneCurve.ProjIsPrincipal _ _
    rw [show -kappaDivisor W (m • P) - (-(m • kappaDivisor W P)) =
        -(kappaDivisor W (m • P) - m • kappaDivisor W P) by abel]
    exact (⟨W⟩ : SmoothPlaneCurve F).projPrincipalSubgroup.neg_mem
      (kappaDivisor_nsmul_linEquiv_of_miller W h_miller P m)

end HasseWeil.Curves
