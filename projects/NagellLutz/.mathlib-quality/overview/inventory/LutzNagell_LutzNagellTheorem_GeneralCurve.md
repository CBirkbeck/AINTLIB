# Inventory: `LutzNagell/LutzNagellTheorem/GeneralCurve.lean`

Path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralCurve.lean`

Namespace: `LutzNagell.LutzNagellTheorem` (with `open WeierstrassCurve`).
File-level `variable (W : WeierstrassCurve ℤ)`.

Purpose (from module docstring): sets up a general Weierstrass curve `W : WeierstrassCurve ℤ` and its base change to `ℚ`, with basic rewriting lemmas (equation, coefficients). Downstream generalized Lutz-Nagell files import this instead of `ShortWeierstrass.lean`.

---

### abbrev curveQ
- Type: `abbrev curveQ (W : WeierstrassCurve ℤ) : WeierstrassCurve ℚ := W.map (algebraMap ℤ ℚ)`
- What: The base change of an integral Weierstrass curve `W` to the rationals, obtained by pushing all coefficients along the canonical ring map `ℤ → ℚ`.
- How: Definitional; applies `WeierstrassCurve.map` to `W` with the structure map `algebraMap ℤ ℚ`. No proof.
- Hypotheses: Takes a Weierstrass curve over `ℤ`; none beyond that.
- Uses from project: []
- Used by: `curveQ_a₁`, `curveQ_a₂`, `curveQ_a₃`, `curveQ_a₄`, `curveQ_a₆`, `curveQ_equation_iff`.
- Visibility: public
- Lines: 23-25 (def, no proof)
- Notes: none

### lemma curveQ_a₁
- Type: `@[simp] lemma curveQ_a₁ : (curveQ W).a₁ = (W.a₁ : ℚ)`
- What: The first Weierstrass coefficient `a₁` of the base-changed curve `curveQ W` equals the image of `W.a₁` under the coercion `ℤ → ℚ`.
- How: `by simp [curveQ]`; unfolds `curveQ` and lets `simp` reduce `(W.map _).a₁` via the `WeierstrassCurve.map` coefficient simp lemmas.
- Hypotheses: none.
- Uses from project: [`curveQ`]
- Used by: unused in file
- Visibility: public
- Lines: 27 (proof 1 line)
- Notes: none

### lemma curveQ_a₂
- Type: `@[simp] lemma curveQ_a₂ : (curveQ W).a₂ = (W.a₂ : ℚ)`
- What: The coefficient `a₂` of `curveQ W` equals the rational coercion of `W.a₂`.
- How: `by simp [curveQ]`; unfolds `curveQ` and discharges via mathlib's `WeierstrassCurve.map` coefficient simp lemmas.
- Hypotheses: none.
- Uses from project: [`curveQ`]
- Used by: unused in file
- Visibility: public
- Lines: 28 (proof 1 line)
- Notes: none

### lemma curveQ_a₃
- Type: `@[simp] lemma curveQ_a₃ : (curveQ W).a₃ = (W.a₃ : ℚ)`
- What: The coefficient `a₃` of `curveQ W` equals the rational coercion of `W.a₃`.
- How: `by simp [curveQ]`; unfolds `curveQ` and reduces via `WeierstrassCurve.map` simp lemmas.
- Hypotheses: none.
- Uses from project: [`curveQ`]
- Used by: unused in file
- Visibility: public
- Lines: 29 (proof 1 line)
- Notes: none

### lemma curveQ_a₄
- Type: `@[simp] lemma curveQ_a₄ : (curveQ W).a₄ = (W.a₄ : ℚ)`
- What: The coefficient `a₄` of `curveQ W` equals the rational coercion of `W.a₄`.
- How: `by simp [curveQ]`; unfolds `curveQ` and reduces via `WeierstrassCurve.map` simp lemmas.
- Hypotheses: none.
- Uses from project: [`curveQ`]
- Used by: unused in file
- Visibility: public
- Lines: 30 (proof 1 line)
- Notes: none

### lemma curveQ_a₆
- Type: `@[simp] lemma curveQ_a₆ : (curveQ W).a₆ = (W.a₆ : ℚ)`
- What: The coefficient `a₆` of `curveQ W` equals the rational coercion of `W.a₆`.
- How: `by simp [curveQ]`; unfolds `curveQ` and reduces via `WeierstrassCurve.map` simp lemmas.
- Hypotheses: none.
- Uses from project: [`curveQ`]
- Used by: unused in file
- Visibility: public
- Lines: 31 (proof 1 line)
- Notes: none

### lemma curveQ_equation_iff
- Type (3 lines):
  ```
  curveQ_equation_iff (x y : ℚ) :
    (curveQ W).toAffine.Equation x y ↔
      y ^ 2 + (W.a₁ : ℚ) * x * y + (W.a₃ : ℚ) * y =
        x ^ 3 + (W.a₂ : ℚ) * x ^ 2 + (W.a₄ : ℚ) * x + (W.a₆ : ℚ)
  ```
- What: A rational point `(x, y)` lies on the affine model of `curveQ W` iff it satisfies the explicit Weierstrass equation `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with the integer coefficients of `W` coerced to `ℚ`.
- How: Rewrites the affine `Equation` predicate via mathlib's `WeierstrassCurve.Affine.equation_iff`, then `simp [curveQ]` unfolds the base change and rewrites the curve's `aᵢ` coefficients into the coercions of `W`'s coefficients.
- Hypotheses: `x y : ℚ`; underlying `W : WeierstrassCurve ℤ` from the file variable.
- Uses from project: [`curveQ`]
- Used by: unused in file
- Visibility: public
- Lines: 33-38 (proof 2 lines: lines 37-38)
- Notes: none

---

## File Summary

- **Total decls: 8** — defs: 1 (`abbrev curveQ`) / lemmas+theorems: 7 (`curveQ_a₁`…`curveQ_a₆`, `curveQ_equation_iff`) / instances: 0.
- **Key API (used by ≥3 in-file):** `curveQ` (used by all 7 lemmas — the single foundational definition of the file).
- **Unused decls (no in-file consumer):** all 7 lemmas — `curveQ_a₁`, `curveQ_a₂`, `curveQ_a₃`, `curveQ_a₄`, `curveQ_a₆`, `curveQ_equation_iff`. These are exported `@[simp]` / rewriting API consumed by downstream generalized Lutz-Nagell files, not internally. (`curveQ` itself is used 7× in-file.)
- **Decls with `sorry`:** none.
- **Decls with `set_option`:** none.
- **Proofs >50 lines:** none (count 0).
- **Proofs 30-50 lines:** none (count 0).

All proofs are 1-2 lines; no decomposition or further `/decompose-proof` pass needed. The file is pure base-change boilerplate over mathlib's `WeierstrassCurve` API (`WeierstrassCurve.map`, `WeierstrassCurve.Affine.equation_iff`).
