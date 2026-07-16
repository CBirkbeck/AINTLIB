/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LutzNagell.DivisionPolynomial

/-!
# Eval bridge lemmas for Lutz-Nagell

This file bridges the coordinate-ring congruence lemmas (`Affine.CoordinateRing.mk_ψ`,
`mk_φ`, `mk_Ψ_sq`) to concrete equalities after evaluating bivariate polynomials at an
on-curve point `(x, y)`.

## Main results

* `evalEval_eq_of_mk_eq`: if two bivariate polynomials are equal in the coordinate ring
  `R[W]`, they evaluate to the same value at any on-curve point.
* `evalEval_ψ_eq_evalEval_Ψ`: `evalEval x y (ψ n) = evalEval x y (Ψ n)`.
* `evalEval_ψ_odd`: for odd `n`, `evalEval x y (ψ n) = (preΨ n).eval x`.
* `evalEval_φ_eq_eval_Φ`: `evalEval x y (φ n) = (Φ n).eval x`.
* `evalEval_Ψ_sq_eq_eval_ΨSq`: `evalEval x y (Ψ n) ^ 2 = (ΨSq n).eval x`.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F) {x y : F}

/-- Equal bivariate polynomials in the coordinate ring evaluate equally at an on-curve point. -/
theorem evalEval_eq_of_mk_eq (heq : W.toAffine.Equation x y)
    {p q : F[X][Y]}
    (h : Affine.CoordinateRing.mk W.toAffine p = Affine.CoordinateRing.mk W.toAffine q) :
    p.evalEval x y = q.evalEval x y := by
  have hev := AdjoinRoot.evalEval_mk (p := W.toAffine.polynomial) heq
  exact hev p ▸ hev q ▸ congrArg _ h

/-- The division polynomials `ψ n` and `Ψ n` evaluate equally at an on-curve point. -/
theorem evalEval_ψ_eq_evalEval_Ψ (heq : W.toAffine.Equation x y) (n : ℤ) :
    (W.ψ n).evalEval x y = (W.Ψ n).evalEval x y :=
  evalEval_eq_of_mk_eq W heq (Affine.CoordinateRing.mk_ψ W n)

/-- The coordinate-ring square of `Ψ n` evaluates to `(ΨSq n).eval x`. -/
theorem evalEval_Ψ_sq_eq_eval_ΨSq (heq : W.toAffine.Equation x y) (n : ℤ) :
    ((W.Ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x := by
  simpa [evalEval_pow, evalEval_C] using
    evalEval_eq_of_mk_eq W heq (Affine.CoordinateRing.mk_Ψ_sq W n)

/-- The division polynomial `φ n` evaluates to `(Φ n).eval x` at an on-curve point. -/
theorem evalEval_φ_eq_eval_Φ (heq : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  simpa [evalEval_C] using evalEval_eq_of_mk_eq W heq (Affine.CoordinateRing.mk_φ W n)

/-- For odd `n`, `Ψ n` evaluates to `(preΨ n).eval x`. -/
theorem evalEval_Ψ_odd (n : ℤ) (hodd : ¬Even n) :
    (W.Ψ n).evalEval x y = (W.preΨ n).eval x := by
  rw [WeierstrassCurve.Ψ, if_neg hodd, mul_one, evalEval_C]

/-- For odd `n`, `ψ n` evaluates to `(preΨ n).eval x` at an on-curve point. -/
theorem evalEval_ψ_odd (heq : W.toAffine.Equation x y) (n : ℤ) (hodd : ¬Even n) :
    (W.ψ n).evalEval x y = (W.preΨ n).eval x :=
  (evalEval_ψ_eq_evalEval_Ψ W heq n).trans (evalEval_Ψ_odd W n hodd)

end WeierstrassCurve
