/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.GenericCovarianceGeneral
import HasseWeil.EC.IsogenyKernel

/-!
# Two-curve kernel-translation covariance (Silverman III.4.10(b))

This file ports the project's single-curve generic-point covariance engine
(`WeilPairing.GenericCovarianceGeneral`) to a **two-curve** isogeny
`β : Isogeny W₁ W₂`, but only for the **kernel-point** case — which is all the
dual-witness Galois data needs.

The mathematical statement (Silverman, *The Arithmetic of Elliptic Curves*,
III.4.10(b), verbatim):

  "if `T ∈ ker φ` and `f ∈ K̄(E₂)`, then `τ_T*(φ*f) = (φ∘τ_T)*f = φ*f`, since
  `φ∘τ_T = φ`."

For the abstract two-independent-fields `Isogeny` interface (which lacks
divisor functoriality) we prove the `f = x_gen₂` and `f = y_gen₂` cases through
the project's **evaluation + separation** argument, exactly as in the
single-curve engine: at a kernel point `k`, the translate `P ↦ P + k` does not
move the image, `β(P + k) = β P + β k = β P`, so the pulled-back generators
`β* x_gen₂`, `β* y_gen₂ ∈ K(E₁)` take the *same* value at `P` and at `P + k`.
Two functions of `K(E₁)` agreeing at cofinitely many points are equal.

## Main results

* `PullbackEvaluation_twoCurve` — the cofinite pullback-evaluation witness for a
  two-curve `β`: at all but finitely many `P`, the stored point map lands at a
  finite point whose coordinates are the values of `β* x_gen₂`, `β* y_gen₂`.
* `xy_family_of_pullbackEvaluation_twoCurve` — the kernel-translation covariance:
  for `k ∈ ker β`, `τ_k` fixes both `β* x_gen₂` and `β* y_gen₂`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, II.1.2, III.4.10(b).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [DecidableEq F]
variable (W₁ W₂ : Affine F) [W₁.IsElliptic] [W₂.IsElliptic]

/-! ### The two-curve cofinite pullback-evaluation witness -/

/-- **The cofinite pullback-evaluation witness** for a two-curve `Isogeny β`
with excluded set `bad`: at every smooth `P ∉ bad` of `W₁`, the stored point map
sends `P` to a *finite* point `(x', y')` of `W₂`, and the pulled-back generators
`β* x_gen₂`, `β* y_gen₂ ∈ K(E₁)` evaluate at `P` to `x'`, `y'`.

This is the two-curve analogue of `WeilPairing.PullbackEvaluation`: "the stored
`toAddMonoidHom` is the geometric realization of the stored `pullback` away from
`bad`", the coherence between the two independent fields of the abstract
`Isogeny` interface. -/
def PullbackEvaluation_twoCurve (β : HasseWeil.Isogeny W₁ W₂)
    (bad : Set (W_smooth W₁).SmoothPoint) : Prop :=
  ∀ P : (W_smooth W₁).SmoothPoint, P ∉ bad →
    ∃ (x' y' : F) (h' : W₂.toAffine.Nonsingular x' y'),
      β.toAddMonoidHom P.toAffinePoint = Affine.Point.some x' y' h' ∧
      EvaluatesTo W₁ P (β.pullback (x_gen W₂)) x' ∧
      EvaluatesTo W₁ P (β.pullback (y_gen W₂)) y'

variable {W₁ W₂}

/-- `toAffinePoint` is injective on smooth points of `W₁`. -/
private theorem toAffinePoint_injective_W₁ :
    Function.Injective
      (fun P : (W_smooth W₁).SmoothPoint => P.toAffinePoint) := by
  intro P Q h
  simp only [Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint_def] at h
  obtain ⟨hx, hy⟩ := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp h
  cases P; cases Q
  simp_all

/-! ### The kernel-translation covariance -/

variable (W₁ W₂)

/-- **The two-curve kernel-translation covariance** (Silverman III.4.10(b)),
from the cofinite pullback-evaluation witness, over an algebraically closed base.

For `k ∈ ker β`, the translation `τ_k` fixes both pulled-back generators
`β* x_gen₂` and `β* y_gen₂` of `K(E₁)`. Proof: at cofinitely many `P`, the
group-hom property gives `β(P + k) = β P + β k = β P` (kernel), so both
`τ_k (β* x_gen₂)` and `β* x_gen₂` evaluate at `P` to the same value — the
`x`-coordinate of `β P` — and similarly for `y`. Separation
(`eq_of_evaluatesTo_cofinite`) over `F̄` concludes. -/
theorem xy_family_of_pullbackEvaluation_twoCurve [IsAlgClosed F]
    (β : HasseWeil.Isogeny W₁ W₂) {bad : Set (W_smooth W₁).SmoothPoint}
    (hbad : bad.Finite) (hw : PullbackEvaluation_twoCurve W₁ W₂ β bad) (k : β.kernel) :
    (translateAlgEquivOfPoint W₁ k.val (β.pullback (x_gen W₂)) = β.pullback (x_gen W₂)) ∧
    (translateAlgEquivOfPoint W₁ k.val (β.pullback (y_gen W₂)) = β.pullback (y_gen W₂)) := by
  set Bx := β.pullback (x_gen W₂) with hBx
  set By := β.pullback (y_gen W₂) with hBy
  -- `k ∈ ker β`: `β k = 0`.
  have hk0 : β.toAddMonoidHom k.val = 0 := (Isogeny.mem_kernel_iff β k.val).mp k.2
  -- Dispose of `k = 0`: then `τ_0 = refl`.  (`rcases hkeq : k.val` already
  -- substitutes `k.val` in the goal, leaving only `hk0` to update.)
  rcases hkeq : k.val with _ | ⟨xs, ys, hnsS⟩
  · rw [translateAlgEquivOfPoint_zero]
    exact ⟨rfl, rfl⟩
  · -- `k = (xs, ys)` affine.  Rewrite the kernel fact accordingly.
    rw [hkeq] at hk0
    -- `k = (xs, ys)` affine.  Assemble the finite bad set for separation.
    set Sk : (W_smooth W₁).toAffine.Point := Affine.Point.some xs ys hnsS with hSk
    -- the kernel fact, retyped at the wrapper curve via defeq
    have hk0' : β.toAddMonoidHom Sk = 0 := hk0
    -- the two finite exclusion sets tied to the translation
    have hB2fin : {P : (W_smooth W₁).SmoothPoint |
        ¬(P.toAffinePoint + Sk).IsSome}.Finite := by
      refine (Set.Finite.preimage toAffinePoint_injective_W₁.injOn
        (Set.finite_singleton (-Sk))).subset ?_
      intro P hP
      rw [Set.mem_setOf_eq, WeierstrassCurve.Affine.Point.IsSome, not_not] at hP
      have : P.toAffinePoint = -Sk := by
        rw [eq_neg_iff_add_eq_zero, ← WeierstrassCurve.Affine.Point.zero_def] at *
        exact hP
      exact this
    have hB3fin : {P : (W_smooth W₁).SmoothPoint |
        ∃ h' : (P.toAffinePoint + Sk).IsSome,
          P.translate_of_finite Sk h' ∈ bad}.Finite := by
      refine (Set.Finite.preimage toAffinePoint_injective_W₁.injOn
        (((hbad.image (fun P : (W_smooth W₁).SmoothPoint => P.toAffinePoint)).image
          (fun R => R - Sk)))).subset ?_
      rintro P ⟨h', hmem⟩
      refine ⟨(P.translate_of_finite Sk h').toAffinePoint, ⟨_, hmem, rfl⟩, ?_⟩
      change (P.translate_of_finite Sk h').toAffinePoint - Sk = P.toAffinePoint
      rw [Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_toAffinePoint]
      exact add_sub_cancel_right _ _
    have hbadS : (bad ∪ {P : (W_smooth W₁).SmoothPoint | ¬(P.toAffinePoint + Sk).IsSome} ∪
        {P : (W_smooth W₁).SmoothPoint | ∃ h' : (P.toAffinePoint + Sk).IsSome,
          P.translate_of_finite Sk h' ∈ bad}).Finite :=
      (hbad.union hB2fin).union hB3fin
    -- per-good-point evaluation data, for both generators at once
    have hcoords : ∀ P : (W_smooth W₁).SmoothPoint, P ∉ (bad ∪
        {P : (W_smooth W₁).SmoothPoint | ¬(P.toAffinePoint + Sk).IsSome} ∪
        {P : (W_smooth W₁).SmoothPoint | ∃ h' : (P.toAffinePoint + Sk).IsSome,
          P.translate_of_finite Sk h' ∈ bad}) →
        (∃ c, EvaluatesTo W₁ P (translateAlgEquivOfPoint W₁ Sk Bx) c ∧
          EvaluatesTo W₁ P Bx c) ∧
        (∃ c, EvaluatesTo W₁ P (translateAlgEquivOfPoint W₁ Sk By) c ∧
          EvaluatesTo W₁ P By c) := by
      intro P hP
      rw [Set.mem_union, Set.mem_union] at hP
      push_neg at hP
      obtain ⟨⟨hP1, hP2⟩, hP3⟩ := hP
      rw [Set.mem_setOf_eq, not_not] at hP2
      rw [Set.mem_setOf_eq] at hP3
      push_neg at hP3
      -- the witness at the translated point `P + k`
      obtain ⟨xI, yI, hI, heqI, hxI, hyI⟩ := hw (P.translate_of_finite Sk hP2) (hP3 hP2)
      have hι : (P.translate_of_finite Sk hP2).toAffinePoint = P.toAffinePoint + Sk :=
        Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_toAffinePoint P Sk hP2
      -- the witness at `P`
      obtain ⟨xP, yP, hPns, heqP, hxP, hyP⟩ := hw P hP1
      -- identify the image coordinates: `β(P+k) = β P + β k = β P` (term mode to
      -- avoid the `(W_smooth W₁).toAffine.Point` vs `W₁.Point` `rw` mismatch)
      have hβsum : β.toAddMonoidHom P.toAffinePoint =
          (Affine.Point.some xI yI hI : W₂.toAffine.Point) :=
        calc β.toAddMonoidHom P.toAffinePoint
            = β.toAddMonoidHom P.toAffinePoint + β.toAddMonoidHom Sk := by
              rw [hk0', add_zero]
          _ = β.toAddMonoidHom (P.toAffinePoint + Sk) := (map_add _ _ _).symm
          _ = β.toAddMonoidHom (P.translate_of_finite Sk hP2).toAffinePoint :=
              congrArg β.toAddMonoidHom hι.symm
          _ = Affine.Point.some xI yI hI := heqI
      obtain ⟨hxx, hyy⟩ :=
        (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp (heqP.symm.trans hβsum)
      -- the translated generators evaluate at `P` to the witness coordinates
      have hτx : EvaluatesTo W₁ P (translateAlgEquivOfPoint W₁ Sk Bx) xI :=
        evaluatesTo_translate W₁ P xs ys hnsS hP2 hxI
      have hτy : EvaluatesTo W₁ P (translateAlgEquivOfPoint W₁ Sk By) yI :=
        evaluatesTo_translate W₁ P xs ys hnsS hP2 hyI
      exact ⟨⟨xI, hτx, hxx ▸ hxP⟩, ⟨yI, hτy, hyy ▸ hyP⟩⟩
    have hX : (translateAlgEquivOfPoint W₁ Sk).toAlgHom Bx = Bx :=
      eq_of_evaluatesTo_cofinite W₁ hbadS (fun P hP => (hcoords P hP).1)
    have hY : (translateAlgEquivOfPoint W₁ Sk).toAlgHom By = By :=
      eq_of_evaluatesTo_cofinite W₁ hbadS (fun P hP => (hcoords P hP).2)
    exact ⟨hX, hY⟩

end HasseWeil.WeilPairing
