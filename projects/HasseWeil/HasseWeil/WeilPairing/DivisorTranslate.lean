/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.TranslateOrdInfty
import HasseWeil.EC.TranslateValuation
import HasseWeil.WeilPairing.Constancy
import HasseWeil.WeilPairing.WeilFunction

/-!
# Divisor transport under translation

This file proves the projective divisor transport facts for translation by a
point on a Weierstrass curve, as used in the Weil pairing construction.

## Main definitions

* `placeTranslate W S`: the bijection of projective places induced by `P ↦ P + S`.
* `ordProj W v f`: the order of `f` at the projective place `v`.

## Main results

* `ord_P_translate`: affine order transport under `translateAlgEquivOfPoint`.
* `ordProj_translate`: projective order transport for all places.
* `projectiveDivisorOf_translate`: projective divisor transport under translation.
* `projectiveDivisorOf_translate_weilFunction_div_eq_zero`: the Weil-function quotient has
  trivial divisor under the fibre-divisor invariance hypothesis.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

open HasseWeil.WeilPairing

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-- The bijection of projective places induced by translating the underlying point by `S`. -/
noncomputable def placeTranslate (S : W.toAffine.Point) :
    ProjectiveSmoothPoint (W_smooth W) ≃ ProjectiveSmoothPoint (W_smooth W) :=
  (WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint
      (W := W.toAffine)).symm.trans
    ((Equiv.addRight S).trans
      (WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint (W := W.toAffine)))

theorem placeTranslate_apply (S : W.toAffine.Point)
    (v : ProjectiveSmoothPoint (W_smooth W)) :
    placeTranslate W S v =
      (WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint (W := W.toAffine))
        (v.toAffinePoint + S) := by
  rfl

@[simp] theorem placeTranslate_affine (S : W.toAffine.Point)
    (P : (W_smooth W).SmoothPoint) :
    placeTranslate W S (ProjectiveSmoothPoint.affine P) =
      (@HAdd.hAdd W.toAffine.Point W.toAffine.Point W.toAffine.Point _
        P.toAffinePoint S).toProjectiveSmoothPoint := by
  rw [placeTranslate_apply]
  rfl

@[simp] theorem placeTranslate_infinity (S : W.toAffine.Point) :
    placeTranslate W S ProjectiveSmoothPoint.infinity =
      S.toProjectiveSmoothPoint := by
  rw [placeTranslate_apply]
  change (((0 : W.toAffine.Point) + S)).toProjectiveSmoothPoint = _
  rw [zero_add]

/-- Translation by `O` is the identity place permutation. -/
@[simp] theorem placeTranslate_zero :
    placeTranslate W (0 : W.toAffine.Point) = Equiv.refl _ := by
  refine Equiv.ext fun v ↦ ?_
  rw [placeTranslate_apply, add_zero, Equiv.refl_apply]
  exact WeierstrassCurve.Affine.Point.toAffinePoint_toProjectiveSmoothPoint v

/-- The order of `f` at a projective place. -/
noncomputable def ordProj (v : ProjectiveSmoothPoint (W_smooth W))
    (f : KE) : WithTop ℤ :=
  match v with
  | ProjectiveSmoothPoint.affine P => (W_smooth W).ord_P P f
  | ProjectiveSmoothPoint.infinity => (W_smooth W).ordAtInfty f

@[simp] theorem ordProj_affine (P : (W_smooth W).SmoothPoint) (f : KE) :
    ordProj W (ProjectiveSmoothPoint.affine P) f = (W_smooth W).ord_P P f := rfl

@[simp] theorem ordProj_infinity (f : KE) :
    ordProj W ProjectiveSmoothPoint.infinity f = (W_smooth W).ordAtInfty f := rfl

/-- The coefficient of `projectiveDivisorOf f` at `v` is `(ordProj v f).untopD 0`. -/
theorem projectiveDivisorOf_apply_ordProj (f : KE)
    (v : ProjectiveSmoothPoint (W_smooth W)) :
    (W_smooth W).projectiveDivisorOf f v = (ordProj W v f).untopD 0 := by
  cases v with
  | affine P =>
    rw [(W_smooth W).projectiveDivisorOf_apply_affine, ordProj_affine]
  | infinity =>
    rw [(W_smooth W).projectiveDivisorOf_apply_infinity, ordProj_infinity]

/-- Affine order transport for `translateAlgEquivOfPoint` at finite translated points. -/
theorem ord_P_translate (P : (W_smooth W).SmoothPoint)
    (S : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + S).IsSome) (f : KE) (hf : f ≠ 0) :
    (W_smooth W).ord_P P (translateAlgEquivOfPoint W S f) =
      (W_smooth W).ord_P (P.translate_of_finite S h) f := by
  rcases S with _ | ⟨xk, yk, h_ns⟩
  · change (W_smooth W).ord_P P f = (W_smooth W).ord_P
      (P.translate_of_finite (0 : (W_smooth W).toAffine.Point) h) f
    rw [Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_zero]
  · exact translate_ord_eq_all_nonzero W P xk yk h_ns h f hf

/-- If `P + S` is finite, `placeTranslate W S (affine P)` is the translated affine place. -/
theorem placeTranslate_affine_of_isSome (S : (W_smooth W).toAffine.Point)
    (P : (W_smooth W).SmoothPoint)
    (h : (P.toAffinePoint + S).IsSome) :
    placeTranslate W S (ProjectiveSmoothPoint.affine P) =
      ProjectiveSmoothPoint.affine (P.translate_of_finite S h) := by
  apply (WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint
    (W := W.toAffine)).symm.injective
  rw [placeTranslate_apply, Equiv.symm_apply_apply]
  exact (Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_toAffinePoint
    P S h).symm

/-- When `P + S = O` (the translate hits infinity), the place
`placeTranslate W S (affine P)` is the place at infinity. -/
theorem placeTranslate_affine_eq_infinity (S : (W_smooth W).toAffine.Point)
    (P : (W_smooth W).SmoothPoint)
    (hz : P.toAffinePoint + S = (0 : W.toAffine.Point)) :
    placeTranslate W S (ProjectiveSmoothPoint.affine P) =
      ProjectiveSmoothPoint.infinity := by
  apply (WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint
    (W := W.toAffine)).symm.injective
  rw [placeTranslate_apply, Equiv.symm_apply_apply]
  exact hz

/-- Projective order transport for places involving infinity. -/
theorem ordProj_translate_infinity (S : (W_smooth W).toAffine.Point)
    (f : KE) (_hf : f ≠ 0) (v : ProjectiveSmoothPoint (W_smooth W))
    (hv : v = ProjectiveSmoothPoint.infinity ∨
      placeTranslate W S v = ProjectiveSmoothPoint.infinity) :
    ordProj W v (translateAlgEquivOfPoint W S f) =
      ordProj W (placeTranslate W S v) f := by
  rcases eq_or_ne S (0 : W.toAffine.Point) with hS | hS
  · subst hS
    rw [placeTranslate_zero, Equiv.refl_apply]
    rfl
  · cases v with
    | affine P =>
      have hv_eq : placeTranslate W S (ProjectiveSmoothPoint.affine P) =
          ProjectiveSmoothPoint.infinity := by
        rcases hv with hv | hv
        · cases hv
        · exact hv
      have hz : P.toAffinePoint + S = (0 : W.toAffine.Point) := by
        have h := congrArg (WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint
          (W := W.toAffine)).symm hv_eq
        rwa [placeTranslate_apply, Equiv.symm_apply_apply] at h
      rw [ordProj_affine, hv_eq, ordProj_infinity]
      exact isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint W P S hz f
    | infinity =>
      rw [ordProj_infinity, placeTranslate_infinity]
      obtain ⟨xk, yk, h_ns, hS_some⟩ :
          ∃ xk yk, ∃ h_ns : W.toAffine.Nonsingular xk yk,
            S = Affine.Point.some xk yk h_ns := by
        rcases S with _ | ⟨xk, yk, h_ns⟩
        · exact absurd rfl hS
        · exact ⟨xk, yk, h_ns, rfl⟩
      subst hS_some
      set P_S : (W_smooth W).SmoothPoint := ⟨xk, yk, h_ns⟩
      set a : W.toAffine.Point := P_S.toAffinePoint
      change (W_smooth W).ordAtInfty (translateAlgEquivOfPoint W a f) =
        (W_smooth W).ord_P P_S f
      have hfeq : translateAlgEquivOfPoint W (-a)
          (translateAlgEquivOfPoint W a f) = f := by
        have hsum := translateAlgEquivOfPoint_add_apply W a (-a) f
        rw [add_neg_cancel] at hsum
        exact hsum.symm
      have hcompat := isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint
        W P_S (-a) (add_neg_cancel a)
        (translateAlgEquivOfPoint W a f)
      rw [hfeq] at hcompat
      exact hcompat.symm

/-- Projective order transport for all places under `translateAlgEquivOfPoint`. -/
theorem ordProj_translate (S : (W_smooth W).toAffine.Point)
    (f : KE) (hf : f ≠ 0) (v : ProjectiveSmoothPoint (W_smooth W)) :
    ordProj W v (translateAlgEquivOfPoint W S f) =
      ordProj W (placeTranslate W S v) f := by
  cases v with
  | infinity =>
    exact ordProj_translate_infinity W S f hf ProjectiveSmoothPoint.infinity
      (Or.inl rfl)
  | affine P =>
    by_cases h : (P.toAffinePoint + S).IsSome
    · rw [placeTranslate_affine_of_isSome W S P h, ordProj_affine, ordProj_affine]
      exact ord_P_translate W P S h f hf
    · have hz : P.toAffinePoint + S = (0 : W.toAffine.Point) := by
        unfold WeierstrassCurve.Affine.Point.IsSome at h
        exact not_not.mp h
      exact ordProj_translate_infinity W S f hf (ProjectiveSmoothPoint.affine P)
        (Or.inr (placeTranslate_affine_eq_infinity W S P hz))

/-- Projective divisor transport under translation. -/
theorem projectiveDivisorOf_translate (S : (W_smooth W).toAffine.Point)
    (f : KE) :
    (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S f) =
      Finsupp.equivMapDomain (placeTranslate W S).symm
        ((W_smooth W).projectiveDivisorOf f) := by
  by_cases hf : f = 0
  · subst hf
    have hL : (W_smooth W).projectiveDivisorOf
        (translateAlgEquivOfPoint W S (0 : KE)) = 0 := by
      rw [map_zero]
      exact (W_smooth W).projectiveDivisorOf_zero
    have hR : (W_smooth W).projectiveDivisorOf (0 : KE) = 0 :=
      (W_smooth W).projectiveDivisorOf_zero
    rw [hL, hR, Finsupp.equivMapDomain_zero]
  · refine Finsupp.ext fun w ↦ ?_
    rw [Finsupp.equivMapDomain_apply, projectiveDivisorOf_apply_ordProj,
      projectiveDivisorOf_apply_ordProj, Equiv.symm_symm, ordProj_translate W S f hf w]

/-- Projective divisor transport under translation, in `Finsupp.mapDomain` form. -/
theorem projectiveDivisorOf_translate_mapDomain (S : (W_smooth W).toAffine.Point)
    (f : KE) :
    (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S f) =
      Finsupp.mapDomain (placeTranslate W S).symm
        ((W_smooth W).projectiveDivisorOf f) := by
  rw [projectiveDivisorOf_translate, Finsupp.equivMapDomain_eq_mapDomain]

/-- The affine divisor of a translated function, read through projective place translation. -/
theorem divisorOf_translate_apply (S : (W_smooth W).toAffine.Point)
    (f : KE) (hf : f ≠ 0) (P : (W_smooth W).SmoothPoint) :
    (W_smooth W).divisorOf (translateAlgEquivOfPoint W S f) P =
      (ordProj W (placeTranslate W S (ProjectiveSmoothPoint.affine P)) f).untopD 0 := by
  change (ordProj W (ProjectiveSmoothPoint.affine P)
    (translateAlgEquivOfPoint W S f)).untopD 0 = _
  exact congrArg (WithTop.untopD 0)
    (ordProj_translate W S f hf (ProjectiveSmoothPoint.affine P))

/-- Translation preserves `projectiveDivisorOf g` under place-translation invariance. -/
theorem projectiveDivisorOf_translate_self_of_invariant
    (S : (W_smooth W).toAffine.Point) (g : KE)
    (hinv : Finsupp.equivMapDomain (placeTranslate W S).symm
        ((W_smooth W).projectiveDivisorOf g) =
      (W_smooth W).projectiveDivisorOf g) :
    (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S g) =
      (W_smooth W).projectiveDivisorOf g := by
  rw [projectiveDivisorOf_translate, hinv]

/-- The quotient `translateAlgEquivOfPoint W S g / g` has trivial divisor under invariance. -/
theorem projectiveDivisorOf_translate_div_eq_zero_of_invariant
    (S : (W_smooth W).toAffine.Point) (g : KE) (hg : g ≠ 0)
    (hinv : Finsupp.equivMapDomain (placeTranslate W S).symm
        ((W_smooth W).projectiveDivisorOf g) =
      (W_smooth W).projectiveDivisorOf g) :
    (W_smooth W).projectiveDivisorOf
        (translateAlgEquivOfPoint W S g / g) = 0 := by
  have hτg : translateAlgEquivOfPoint W S g ≠ 0 :=
    (map_ne_zero_iff _ (translateAlgEquivOfPoint W S).injective).mpr hg
  have hself : (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S g) =
      (W_smooth W).projectiveDivisorOf g :=
    projectiveDivisorOf_translate_self_of_invariant W S g hinv
  calc (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S g / g)
      = (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S g) +
          (W_smooth W).projectiveDivisorOf g⁻¹ := by
        rw [div_eq_mul_inv]
        exact (W_smooth W).projectiveDivisorOf_mul hτg (inv_ne_zero hg)
    _ = (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S g) -
          (W_smooth W).projectiveDivisorOf g := by
        rw [(W_smooth W).projectiveDivisorOf_inv hg, sub_eq_add_neg]
    _ = 0 := by rw [hself, sub_self]

/-- The `toAffinePoint` of a translated place is `w.toAffinePoint + S`. -/
theorem placeTranslate_toAffinePoint (S : (W_smooth W).toAffine.Point)
    (w : ProjectiveSmoothPoint (W_smooth W)) :
    (placeTranslate W S w).toAffinePoint =
      @HAdd.hAdd W.toAffine.Point W.toAffine.Point W.toAffine.Point _
        w.toAffinePoint S := by
  rw [placeTranslate_apply]
  exact WeierstrassCurve.Affine.Point.toProjectiveSmoothPoint_toAffinePoint _

/-- The coefficient of `pullbackDiv f hker Q` is `1` on the fibre over `Q` and `0` otherwise. -/
theorem pullbackDiv_apply (f : W.toAffine.Point →+ W.toAffine.Point)
    (hker : Finite f.ker) (Q : W.toAffine.Point)
    (w : ProjectiveSmoothPoint (W_smooth W)) :
    pullbackDiv (W := W.toAffine) f hker Q w =
      if f w.toAffinePoint = Q then (1 : ℤ) else 0 := by
  letI : Fintype {P : W.toAffine.Point // f P = Q} :=
    @Fintype.ofFinite _ (fiber_finite f hker Q)
  rw [pullbackDiv, Finset.sum_apply']
  simp only [Finsupp.single_apply]
  have hkey : ∀ P : W.toAffine.Point,
      (P.toProjectiveSmoothPoint = w) ↔ (P = w.toAffinePoint) := by
    intro P
    constructor
    · intro hPw
      rw [← WeierstrassCurve.Affine.Point.toProjectiveSmoothPoint_toAffinePoint P,
        hPw]
    · intro hPeq
      rw [hPeq,
        WeierstrassCurve.Affine.Point.toAffinePoint_toProjectiveSmoothPoint]
  by_cases hQ : f w.toAffinePoint = Q
  · rw [if_pos hQ, Finset.sum_eq_single (⟨w.toAffinePoint, hQ⟩ :
      {P : W.toAffine.Point // f P = Q})]
    · rw [if_pos ((hkey w.toAffinePoint).mpr rfl)]
    · rintro ⟨P, hP⟩ _ hne
      rw [if_neg]
      intro hPw
      exact hne (Subtype.ext ((hkey P).mp hPw))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hQ]
    apply Finset.sum_eq_zero
    rintro ⟨P, hP⟩ _
    rw [if_neg]
    intro hPw
    exact hQ (by
      rw [← (hkey P).mp hPw]
      exact hP)

/-- If `f S = 0`, `pullbackDiv f hker Q` is pointwise invariant under `placeTranslate W S`. -/
theorem pullbackDiv_placeTranslate_apply (S : (W_smooth W).toAffine.Point)
    (f : W.toAffine.Point →+ W.toAffine.Point) (hker : Finite f.ker)
    (Q : W.toAffine.Point) (hfS : f S = 0)
    (w : ProjectiveSmoothPoint (W_smooth W)) :
    pullbackDiv (W := W.toAffine) f hker Q (placeTranslate W S w) =
      pullbackDiv (W := W.toAffine) f hker Q w := by
  rw [pullbackDiv_apply, pullbackDiv_apply, placeTranslate_toAffinePoint]
  congr 1
  rw [map_add, hfS, add_zero]

/-- Translating a fibre divisor shifts the target point by `-f S` coefficientwise. -/
theorem pullbackDiv_placeTranslate_apply_general (S : (W_smooth W).toAffine.Point)
    (f : W.toAffine.Point →+ W.toAffine.Point) (hker : Finite f.ker)
    (Q : W.toAffine.Point) (w : ProjectiveSmoothPoint (W_smooth W)) :
    pullbackDiv (W := W.toAffine) f hker Q (placeTranslate W S w) =
      pullbackDiv (W := W.toAffine) f hker (Q - f S) w := by
  rw [pullbackDiv_apply, pullbackDiv_apply, placeTranslate_toAffinePoint]
  congr 1
  rw [map_add]
  exact propext eq_sub_iff_add_eq.symm

/-- Translating a fibre divisor shifts the fibre target by `-f S`. -/
theorem equivMapDomain_placeTranslate_pullbackDiv (S : (W_smooth W).toAffine.Point)
    (f : W.toAffine.Point →+ W.toAffine.Point) (hker : Finite f.ker) (Q : W.toAffine.Point) :
    Finsupp.equivMapDomain (placeTranslate W S).symm (pullbackDiv (W := W.toAffine) f hker Q) =
      pullbackDiv (W := W.toAffine) f hker (Q - f S) := by
  refine Finsupp.ext fun w ↦ ?_
  rw [Finsupp.equivMapDomain_symm_apply]
  exact pullbackDiv_placeTranslate_apply_general W S f hker Q w

/-- `equivMapDomain` fixes a divisor invariant under `placeTranslate W S`. -/
theorem equivMapDomain_placeTranslate_symm_eq_self
    (S : (W_smooth W).toAffine.Point)
    (D : ProjectiveDivisor (W_smooth W))
    (hD : ∀ w, D (placeTranslate W S w) = D w) :
    Finsupp.equivMapDomain (placeTranslate W S).symm D = D := by
  refine Finsupp.ext fun w ↦ ?_
  rw [Finsupp.equivMapDomain_symm_apply]
  exact hD w

/-- The Weil-function fibre-difference divisor is invariant under translation by kernel points. -/
theorem equivMapDomain_placeTranslate_pullbackDiv_sub
    (S : (W_smooth W).toAffine.Point)
    (f : W.toAffine.Point →+ W.toAffine.Point) (hker : Finite f.ker)
    (T : W.toAffine.Point) (hfS : f S = 0) :
    Finsupp.equivMapDomain (placeTranslate W S).symm
        (pullbackDiv (W := W.toAffine) f hker T -
          pullbackDiv (W := W.toAffine) f hker 0) =
      pullbackDiv (W := W.toAffine) f hker T -
        pullbackDiv (W := W.toAffine) f hker 0 := by
  refine equivMapDomain_placeTranslate_symm_eq_self W S _ (fun w ↦ ?_)
  change pullbackDiv (W := W.toAffine) f hker T (placeTranslate W S w) -
      pullbackDiv (W := W.toAffine) f hker 0 (placeTranslate W S w) =
    pullbackDiv (W := W.toAffine) f hker T w -
      pullbackDiv (W := W.toAffine) f hker 0 w
  rw [pullbackDiv_placeTranslate_apply W S f hker T hfS,
    pullbackDiv_placeTranslate_apply W S f hker 0 hfS]

/-- The translated Weil-function quotient has trivial divisor for kernel translations. -/
theorem projectiveDivisorOf_translate_weilFunction_div_eq_zero
    (S : (W_smooth W).toAffine.Point)
    (f : W.toAffine.Point →+ W.toAffine.Point) (hker : Finite f.ker)
    (T : W.toAffine.Point) (hfS : f S = 0)
    (g : KE) (hg : g ≠ 0)
    (hg_div : (W_smooth W).projectiveDivisorOf g =
      pullbackDiv (W := W.toAffine) f hker T -
        pullbackDiv (W := W.toAffine) f hker 0) :
    (W_smooth W).projectiveDivisorOf
        (translateAlgEquivOfPoint W S g / g) = 0 := by
  refine projectiveDivisorOf_translate_div_eq_zero_of_invariant W S g hg ?_
  rw [hg_div]
  exact equivMapDomain_placeTranslate_pullbackDiv_sub W S f hker T hfS

end HasseWeil
