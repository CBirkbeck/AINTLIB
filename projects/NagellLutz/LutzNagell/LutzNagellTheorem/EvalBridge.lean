import LutzNagell.DivisionPolynomial
import LutzNagell.LutzNagellTheorem.ShortWeierstrass

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

/-! ### Evaluation at an on-curve point -/

/-- If two bivariate polynomials are equal modulo the Weierstrass polynomial (i.e., equal in
the coordinate ring), they evaluate to the same value at any point satisfying the equation. -/
theorem evalEval_eq_of_mk_eq (heq : W.toAffine.Equation x y)
    {p q : F[X][Y]} (h : Affine.CoordinateRing.mk W.toAffine p = Affine.CoordinateRing.mk W.toAffine q) :
    p.evalEval x y = q.evalEval x y := by
  have hev := AdjoinRoot.evalEval_mk (p := W.toAffine.polynomial) heq
  exact hev p ▸ hev q ▸ congrArg _ h

/-! ### Bridge lemmas from `mk` congruences to `evalEval` equalities -/

/-- The division polynomial `ψ n` and the univariate-dressed `Ψ n` evaluate to the same
value at any on-curve point. -/
theorem evalEval_ψ_eq_evalEval_Ψ (heq : W.toAffine.Equation x y) (n : ℤ) :
    (W.ψ n).evalEval x y = (W.Ψ n).evalEval x y :=
  evalEval_eq_of_mk_eq W heq (Affine.CoordinateRing.mk_ψ W n)

/-- The coordinate-ring square of `Ψ n` evaluates to `(ΨSq n).eval x`. -/
theorem evalEval_Ψ_sq_eq_eval_ΨSq (heq : W.toAffine.Equation x y) (n : ℤ) :
    ((W.Ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x := by
  have h := evalEval_eq_of_mk_eq W heq (Affine.CoordinateRing.mk_Ψ_sq W n)
  rw [evalEval_pow] at h
  rw [h, evalEval_C]

/-- The division polynomial `φ n` evaluates to `(Φ n).eval x` at an on-curve point. -/
theorem evalEval_φ_eq_eval_Φ (heq : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  have h := evalEval_eq_of_mk_eq W heq (Affine.CoordinateRing.mk_φ W n)
  rwa [evalEval_C] at h

/-! ### Odd-n specialization -/

/-- For odd `n`, `Ψ n = C (preΨ n)`, so `evalEval x y (Ψ n) = (preΨ n).eval x`. -/
theorem evalEval_Ψ_odd (n : ℤ) (hodd : ¬Even n) :
    (W.Ψ n).evalEval x y = (W.preΨ n).eval x := by
  simp only [WeierstrassCurve.Ψ, if_neg hodd, mul_one, evalEval_C]

/-- For odd `n`, `evalEval x y (ψ n) = (preΨ n).eval x` at an on-curve point.
This is the key bridge for the prime-order integrality argument. -/
theorem evalEval_ψ_odd (heq : W.toAffine.Equation x y) (n : ℤ) (hodd : ¬Even n) :
    (W.ψ n).evalEval x y = (W.preΨ n).eval x := by
  rw [evalEval_ψ_eq_evalEval_Ψ W heq, evalEval_Ψ_odd W n hodd]

end WeierstrassCurve
