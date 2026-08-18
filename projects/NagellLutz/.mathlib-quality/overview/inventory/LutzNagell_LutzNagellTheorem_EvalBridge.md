# Inventory: LutzNagell/LutzNagellTheorem/EvalBridge.lean

File-level context: bridges coordinate-ring congruence lemmas (`Affine.CoordinateRing.mk_ψ`, `mk_φ`, `mk_Ψ_sq`) to concrete equalities after evaluating bivariate polynomials at an on-curve point `(x, y)`. Namespace `WeierstrassCurve`; section variables `{F : Type*} [Field F] (W : WeierstrassCurve F) {x y : F}`. Imports `LutzNagell.DivisionPolynomial` and `LutzNagell.LutzNagellTheorem.ShortWeierstrass`.

### theorem evalEval_eq_of_mk_eq
- Type: `(heq : W.toAffine.Equation x y) {p q : F[X][Y]} (h : Affine.CoordinateRing.mk W.toAffine p = Affine.CoordinateRing.mk W.toAffine q) : p.evalEval x y = q.evalEval x y`
- What: If two bivariate polynomials over `F` are equal in the affine coordinate ring `F[W]` (i.e. congruent modulo the Weierstrass polynomial), then they evaluate to the same field element at any point `(x,y)` satisfying the curve equation.
- How: Uses mathlib's `AdjoinRoot.evalEval_mk` to convert the coordinate-ring class `mk W.toAffine p` of each polynomial into its evaluation `p.evalEval x y` at the on-curve point; the hypothesis equality of classes is transported by `congrArg` and the two `▸` rewrites.
- Hypotheses: `(x,y)` lies on the affine Weierstrass curve (`W.toAffine.Equation x y`); `p, q` are bivariate polynomials whose coordinate-ring images coincide.
- Uses from project: []
- Used by: evalEval_ψ_eq_evalEval_Ψ; evalEval_Ψ_sq_eq_eval_ΨSq; evalEval_φ_eq_eval_Φ
- Visibility: public
- Lines: 32-36 (proof 2 lines)
- Notes: none

### theorem evalEval_ψ_eq_evalEval_Ψ
- Type: `(heq : W.toAffine.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y = (W.Ψ n).evalEval x y`
- What: The division polynomial `ψ n` and the univariate-dressed division polynomial `Ψ n` evaluate to the same value at any on-curve point.
- How: Direct application of `evalEval_eq_of_mk_eq` to the coordinate-ring congruence `Affine.CoordinateRing.mk_ψ W n` (which states the two have equal images in `F[W]`).
- Hypotheses: `(x,y)` on the curve; `n` an integer.
- Uses from project: evalEval_eq_of_mk_eq
- Used by: evalEval_ψ_odd
- Visibility: public
- Lines: 42-44 (proof 1 line, term-mode)
- Notes: none

### theorem evalEval_Ψ_sq_eq_eval_ΨSq
- Type: `(heq : W.toAffine.Equation x y) (n : ℤ) : ((W.Ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x`
- What: The square of the evaluation of `Ψ n` at an on-curve point equals the univariate polynomial `ΨSq n` evaluated at the x-coordinate.
- How: Applies `evalEval_eq_of_mk_eq` to the congruence `Affine.CoordinateRing.mk_Ψ_sq W n`, then rewrites with mathlib's `evalEval_pow` (to push the square through `evalEval`) and `evalEval_C` (since `ΨSq n` enters as a constant bivariate polynomial `C (ΨSq n)`).
- Hypotheses: `(x,y)` on the curve; `n` an integer.
- Uses from project: evalEval_eq_of_mk_eq
- Used by: unused in file
- Visibility: public
- Lines: 47-51 (proof 3 lines)
- Notes: none

### theorem evalEval_φ_eq_eval_Φ
- Type: `(heq : W.toAffine.Equation x y) (n : ℤ) : (W.φ n).evalEval x y = (W.Φ n).eval x`
- What: The division polynomial `φ n` evaluates at an on-curve point to the univariate polynomial `Φ n` evaluated at the x-coordinate.
- How: Applies `evalEval_eq_of_mk_eq` to the congruence `Affine.CoordinateRing.mk_φ W n`, then finishes with `evalEval_C` (rewriting the constant-embedded `C (Φ n)` evaluation to `(Φ n).eval x`).
- Hypotheses: `(x,y)` on the curve; `n` an integer.
- Uses from project: evalEval_eq_of_mk_eq
- Used by: unused in file
- Visibility: public
- Lines: 54-57 (proof 2 lines)
- Notes: none

### theorem evalEval_Ψ_odd
- Type: `(n : ℤ) (hodd : ¬Even n) : (W.Ψ n).evalEval x y = (W.preΨ n).eval x`
- What: For odd `n`, since `Ψ n = C (preΨ n)`, the bivariate evaluation of `Ψ n` collapses to the univariate evaluation of `preΨ n` at the x-coordinate.
- How: Unfolds the definition `WeierstrassCurve.Ψ` and uses `if_neg hodd` to select the odd branch, then `mul_one` and `evalEval_C` to reduce the constant evaluation; purely by `simp only`. Hinges on the definitional shape of `WeierstrassCurve.Ψ`.
- Hypotheses: `n` is odd (`¬Even n`).
- Uses from project: [] (unfolds `WeierstrassCurve.Ψ` and references `WeierstrassCurve.preΨ` via the def's body, but no NagellLutz lemma is applied)
- Used by: evalEval_ψ_odd
- Visibility: public
- Lines: 62-64 (proof 1 line)
- Notes: none

### theorem evalEval_ψ_odd
- Type: `(heq : W.toAffine.Equation x y) (n : ℤ) (hodd : ¬Even n) : (W.ψ n).evalEval x y = (W.preΨ n).eval x`
- What: For odd `n` at an on-curve point, the division polynomial `ψ n` evaluates to the univariate `preΨ n` evaluated at the x-coordinate; described as the key bridge for the prime-order integrality argument.
- How: Chains `evalEval_ψ_eq_evalEval_Ψ` (replacing `ψ n` by `Ψ n`) with `evalEval_Ψ_odd` (collapsing `Ψ n` to `preΨ n` in the odd case) via two rewrites.
- Hypotheses: `(x,y)` on the curve; `n` odd (`¬Even n`).
- Uses from project: evalEval_ψ_eq_evalEval_Ψ; evalEval_Ψ_odd
- Used by: unused in file
- Visibility: public
- Lines: 68-70 (proof 1 line)
- Notes: none

---

## File Summary

- Total decls: 6 (0 defs / 6 lemmas+theorems / 0 instances). All are public theorems.
- Key API (used by >=3 in-file): `evalEval_eq_of_mk_eq` — the workhorse, used by 3 other theorems (`evalEval_ψ_eq_evalEval_Ψ`, `evalEval_Ψ_sq_eq_eval_ΨSq`, `evalEval_φ_eq_eval_Φ`).
- Unused decls (no in-file consumer; intended as exported API): `evalEval_Ψ_sq_eq_eval_ΨSq`, `evalEval_φ_eq_eval_Φ`, `evalEval_ψ_odd`. (`evalEval_ψ_odd` is flagged in its docstring as the key bridge for the prime-order integrality argument, consumed downstream.)
- Decls with sorry: none.
- Decls with set_option: none.
- Proofs >50 lines (OVER-50): none. Count: 0.
- Proofs 30-50 lines: none. Count: 0.

All proofs are short (1-3 lines). No decomposition pass needed. The file is a thin evaluation-bridge layer: every result reduces a coordinate-ring (`mk`) congruence — supplied by `Affine.CoordinateRing.mk_ψ` / `mk_φ` / `mk_Ψ_sq` from `DivisionPolynomial`/`ShortWeierstrass` — to a concrete `evalEval`/`eval` equality at an on-curve point, leaning on mathlib's `AdjoinRoot.evalEval_mk`, `evalEval_pow`, and `evalEval_C`.
