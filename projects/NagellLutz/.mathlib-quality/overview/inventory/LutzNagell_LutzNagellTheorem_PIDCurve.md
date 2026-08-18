# Inventory: LutzNagell/LutzNagellTheorem/PIDCurve.lean

File path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDCurve.lean`

Namespace: `LutzNagell.PID` (opens `WeierstrassCurve`)

Section variables: `R : Type*` `[CommRing R]`; `K : Type*` `[Field K] [Algebra R K]`; `W : WeierstrassCurve R`.

Purpose: sets up a general Weierstrass curve `W : WeierstrassCurve R` over a PID `R`, its base change to a fraction field `K`, and basic rewriting lemmas. Generalizes `GeneralCurve.lean` from `ℤ/ℚ` to an arbitrary PID `R` with fraction field `K`.

---

### abbrev curveK
- Type: `abbrev curveK : WeierstrassCurve K := W.map (algebraMap R K)`
- What: The base change (push-forward) of the Weierstrass curve `W` over `R` to the field `K`, obtained by applying the structure map `algebraMap R K` to the Weierstrass coefficients.
- How: Direct definition as `W.map (algebraMap R K)`, using mathlib's `WeierstrassCurve.map`.
- Hypotheses: `R` a commutative ring, `K` a field that is an `R`-algebra, `W` a Weierstrass curve over `R`.
- Uses from project: []
- Used by: `curveK_a₁`, `curveK_a₂`, `curveK_a₃`, `curveK_a₄`, `curveK_a₆`, `curveK_equation_iff`
- Visibility: public
- Lines: 26-27 (body 1 line)
- Notes: none

### lemma curveK_a₁
- Type: `(curveK R K W).a₁ = algebraMap R K W.a₁`
- What: The `a₁` coefficient of the base-changed curve `curveK R K W` equals the image of `W.a₁` under `algebraMap R K`.
- How: `by simp [curveK]` — unfolds `curveK` and simplifies via `WeierstrassCurve.map` coefficient simp lemmas.
- Hypotheses: standard section variables (`R`, `K`, `W`).
- Uses from project: [curveK]
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 29 (body 1 line)
- Notes: none

### lemma curveK_a₂
- Type: `(curveK R K W).a₂ = algebraMap R K W.a₂`
- What: The `a₂` coefficient of the base-changed curve equals the image of `W.a₂` under `algebraMap R K`.
- How: `by simp [curveK]` — unfolds `curveK` and simplifies via `WeierstrassCurve.map` coefficient simp lemmas.
- Hypotheses: standard section variables (`R`, `K`, `W`).
- Uses from project: [curveK]
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 30 (body 1 line)
- Notes: none

### lemma curveK_a₃
- Type: `(curveK R K W).a₃ = algebraMap R K W.a₃`
- What: The `a₃` coefficient of the base-changed curve equals the image of `W.a₃` under `algebraMap R K`.
- How: `by simp [curveK]` — unfolds `curveK` and simplifies via `WeierstrassCurve.map` coefficient simp lemmas.
- Hypotheses: standard section variables (`R`, `K`, `W`).
- Uses from project: [curveK]
- Used by: `curveK_equation_iff` (via `simp [curveK]`, indirectly)
- Visibility: public (`@[simp]`)
- Lines: 31 (body 1 line)
- Notes: none

### lemma curveK_a₄
- Type: `(curveK R K W).a₄ = algebraMap R K W.a₄`
- What: The `a₄` coefficient of the base-changed curve equals the image of `W.a₄` under `algebraMap R K`.
- How: `by simp [curveK]` — unfolds `curveK` and simplifies via `WeierstrassCurve.map` coefficient simp lemmas.
- Hypotheses: standard section variables (`R`, `K`, `W`).
- Uses from project: [curveK]
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 32 (body 1 line)
- Notes: none

### lemma curveK_a₆
- Type: `(curveK R K W).a₆ = algebraMap R K W.a₆`
- What: The `a₆` coefficient of the base-changed curve equals the image of `W.a₆` under `algebraMap R K`.
- How: `by simp [curveK]` — unfolds `curveK` and simplifies via `WeierstrassCurve.map` coefficient simp lemmas.
- Hypotheses: standard section variables (`R`, `K`, `W`).
- Uses from project: [curveK]
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 33 (body 1 line)
- Notes: none

### lemma curveK_equation_iff
- Type: `(curveK R K W).toAffine.Equation x y ↔ y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y = x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆` (for `x y : K`)
- What: A point `(x, y) ∈ K²` lies on the affine base-changed curve `curveK R K W` iff it satisfies the explicit (long) Weierstrass equation with coefficients pushed forward by `algebraMap R K`.
- How: Rewrites the affine equation predicate via mathlib's `WeierstrassCurve.Affine.equation_iff`, then closes with `simp [curveK]` to unfold the base-changed coefficients.
- Hypotheses: standard section variables; `x y : K`.
- Uses from project: [curveK] (and the `curveK_a*` simp lemmas fire indirectly via `simp`)
- Used by: unused in file
- Visibility: public
- Lines: 35-41 (body 2 lines)
- Notes: none

---

## File Summary

- Total decls: 8 — 1 def/abbrev (`curveK`) / 7 lemmas+theorems (`curveK_equation_iff` + six `curveK_a*` coefficient lemmas) / 0 instances. (No structures, classes, or inductives.)
- Key API (used by ≥3 in-file): `curveK` — referenced by all 7 other declarations in the file.
- Unused decls (within this file): `curveK_a₁`, `curveK_a₂`, `curveK_a₄`, `curveK_a₆`, `curveK_equation_iff` are not referenced by other decls in this file (they are public API for downstream files). `curveK_a₃` fires indirectly inside `curveK_equation_iff`'s `simp`. `curveK` is heavily used in-file.
- Decls with sorry: none.
- Decls with set_option: none.
- Proofs >50 lines (OVER-50): none.
- Proofs 30-50 lines: none.

All proofs are 1-2 lines; no decomposition or further passes needed. The file is a thin base-change API layer over mathlib's `WeierstrassCurve.map`.
