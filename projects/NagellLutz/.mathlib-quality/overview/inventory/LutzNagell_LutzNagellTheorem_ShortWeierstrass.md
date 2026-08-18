# Inventory: `LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean`

Namespace: `LutzNagell.LutzNagellTheorem`. Sets up the short Weierstrass curve `y² = x³ + A·x + B` over `ℤ` and its base change to `ℚ`, with basic rewriting lemmas (a-invariants, equation, discriminant).

---

### def shortCurveZ
- Type: `def shortCurveZ (A B : ℤ) : WeierstrassCurve ℤ`
- What: The short Weierstrass curve `y² = x³ + A·x + B` over `ℤ`, given as the `WeierstrassCurve` record with `a₁ = a₂ = a₃ = 0`, `a₄ = A`, `a₆ = B`.
- How: Direct record literal; no proof.
- Hypotheses: Integer coefficients `A B : ℤ`.
- Uses from project: []
- Used by: `shortCurveQ`, `shortCurveZ_a₁`, `shortCurveZ_a₂`, `shortCurveZ_a₃`, `shortCurveZ_a₄`, `shortCurveZ_a₆`, `shortCurveQ_a₁`–`shortCurveQ_a₆`, `shortCurveQ_equation_iff`, `shortCurveZ_delta`
- Visibility: public
- Lines: 25–26 (no proof)
- Notes: none

### def shortCurveQ
- Type: `def shortCurveQ (A B : ℤ) : WeierstrassCurve ℚ`
- What: The short Weierstrass curve over `ℚ`, obtained from `shortCurveZ A B` by base change along `algebraMap ℤ ℚ`.
- How: Applies `WeierstrassCurve.map (algebraMap ℤ ℚ)` to `shortCurveZ A B`; no proof.
- Hypotheses: Integer coefficients `A B : ℤ`.
- Uses from project: [`shortCurveZ`]
- Used by: `shortCurveQ_a₁`, `shortCurveQ_a₂`, `shortCurveQ_a₃`, `shortCurveQ_a₄`, `shortCurveQ_a₆`, `shortCurveQ_equation_iff`
- Visibility: public
- Lines: 29–30 (no proof)
- Notes: none

### lemma shortCurveZ_a₁
- Type: `@[simp] lemma shortCurveZ_a₁ (A B : ℤ) : (shortCurveZ A B).a₁ = 0`
- What: The `a₁`-coefficient of the integral short curve is `0`.
- How: `rfl`.
- Hypotheses: `A B : ℤ`.
- Uses from project: [`shortCurveZ`]
- Used by: unused in file
- Visibility: public
- Lines: 32 (proof: rfl)
- Notes: none

### lemma shortCurveZ_a₂
- Type: `@[simp] lemma shortCurveZ_a₂ (A B : ℤ) : (shortCurveZ A B).a₂ = 0`
- What: The `a₂`-coefficient of the integral short curve is `0`.
- How: `rfl`.
- Hypotheses: `A B : ℤ`.
- Uses from project: [`shortCurveZ`]
- Used by: unused in file
- Visibility: public
- Lines: 33 (proof: rfl)
- Notes: none

### lemma shortCurveZ_a₃
- Type: `@[simp] lemma shortCurveZ_a₃ (A B : ℤ) : (shortCurveZ A B).a₃ = 0`
- What: The `a₃`-coefficient of the integral short curve is `0`.
- How: `rfl`.
- Hypotheses: `A B : ℤ`.
- Uses from project: [`shortCurveZ`]
- Used by: unused in file
- Visibility: public
- Lines: 34 (proof: rfl)
- Notes: none

### lemma shortCurveZ_a₄
- Type: `@[simp] lemma shortCurveZ_a₄ (A B : ℤ) : (shortCurveZ A B).a₄ = A`
- What: The `a₄`-coefficient of the integral short curve equals `A`.
- How: `rfl`.
- Hypotheses: `A B : ℤ`.
- Uses from project: [`shortCurveZ`]
- Used by: unused in file
- Visibility: public
- Lines: 35 (proof: rfl)
- Notes: none

### lemma shortCurveZ_a₆
- Type: `@[simp] lemma shortCurveZ_a₆ (A B : ℤ) : (shortCurveZ A B).a₆ = B`
- What: The `a₆`-coefficient of the integral short curve equals `B`.
- How: `rfl`.
- Hypotheses: `A B : ℤ`.
- Uses from project: [`shortCurveZ`]
- Used by: unused in file
- Visibility: public
- Lines: 36 (proof: rfl)
- Notes: none

### lemma shortCurveQ_a₁
- Type: `@[simp] lemma shortCurveQ_a₁ (A B : ℤ) : (shortCurveQ A B).a₁ = 0`
- What: The `a₁`-coefficient of the rational (base-changed) short curve is `0`.
- How: `simp [shortCurveQ, shortCurveZ]` (unfolds definitions and simplifies the image of `0` under the algebra map).
- Hypotheses: `A B : ℤ`.
- Uses from project: [`shortCurveQ`, `shortCurveZ`]
- Used by: unused in file
- Visibility: public
- Lines: 38–39 (proof: 1 line)
- Notes: none

### lemma shortCurveQ_a₂
- Type: `@[simp] lemma shortCurveQ_a₂ (A B : ℤ) : (shortCurveQ A B).a₂ = 0`
- What: The `a₂`-coefficient of the rational short curve is `0`.
- How: `simp [shortCurveQ, shortCurveZ]`.
- Hypotheses: `A B : ℤ`.
- Uses from project: [`shortCurveQ`, `shortCurveZ`]
- Used by: unused in file
- Visibility: public
- Lines: 41–42 (proof: 1 line)
- Notes: none

### lemma shortCurveQ_a₃
- Type: `@[simp] lemma shortCurveQ_a₃ (A B : ℤ) : (shortCurveQ A B).a₃ = 0`
- What: The `a₃`-coefficient of the rational short curve is `0`.
- How: `simp [shortCurveQ, shortCurveZ]`.
- Hypotheses: `A B : ℤ`.
- Uses from project: [`shortCurveQ`, `shortCurveZ`]
- Used by: unused in file
- Visibility: public
- Lines: 44–45 (proof: 1 line)
- Notes: none

### lemma shortCurveQ_a₄
- Type: `@[simp] lemma shortCurveQ_a₄ (A B : ℤ) : (shortCurveQ A B).a₄ = (A : ℚ)`
- What: The `a₄`-coefficient of the rational short curve equals the image of `A` in `ℚ`.
- How: `simp [shortCurveQ, shortCurveZ]`.
- Hypotheses: `A B : ℤ`.
- Uses from project: [`shortCurveQ`, `shortCurveZ`]
- Used by: unused in file
- Visibility: public
- Lines: 47–48 (proof: 1 line)
- Notes: none

### lemma shortCurveQ_a₆
- Type: `@[simp] lemma shortCurveQ_a₆ (A B : ℤ) : (shortCurveQ A B).a₆ = (B : ℚ)`
- What: The `a₆`-coefficient of the rational short curve equals the image of `B` in `ℚ`.
- How: `simp [shortCurveQ, shortCurveZ]`.
- Hypotheses: `A B : ℤ`.
- Uses from project: [`shortCurveQ`, `shortCurveZ`]
- Used by: unused in file
- Visibility: public
- Lines: 50–51 (proof: 1 line)
- Notes: none

### lemma shortCurveQ_equation_iff
- Type: `lemma shortCurveQ_equation_iff (A B : ℤ) (x y : ℚ) : (shortCurveQ A B).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + (A : ℚ) * x + (B : ℚ)`
- What: The affine Weierstrass equation of the rational short curve at `(x, y)` holds iff `y² = x³ + A·x + B`.
- How: `simpa` with associativity/commutativity rewrites, reducing the general `WeierstrassCurve.Affine.equation_iff` (mathlib) specialised to `shortCurveQ A B` (where `a₁ = a₂ = a₃ = 0`) to the short form.
- Hypotheses: `A B : ℤ`; point coordinates `x y : ℚ`.
- Uses from project: [`shortCurveQ`, `shortCurveZ`]
- Used by: unused in file
- Visibility: public
- Lines: 53–56 (proof: 2 lines)
- Notes: none

### lemma shortCurveZ_delta
- Type: `lemma shortCurveZ_delta (A B : ℤ) : (shortCurveZ A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2)`
- What: The discriminant `Δ` of the integral short curve equals `−16·(4·A³ + 27·B²)`.
- How: `simp` unfolds `Δ` and the `b₂, b₄, b₆, b₈` invariants (mathlib `WeierstrassCurve.Δ`/`b₂`/`b₄`/`b₆`/`b₈`) at `shortCurveZ`, then `ring1` closes the polynomial identity.
- Hypotheses: `A B : ℤ`.
- Uses from project: [`shortCurveZ`]
- Used by: unused in file
- Visibility: public
- Lines: 58–62 (proof: 4 lines)
- Notes: none

---

## File Summary

- **Total decls: 14** — defs: 2 (`shortCurveZ`, `shortCurveQ`); lemmas+theorems: 12; instances: 0.
- **Key API (used by ≥3 in-file):**
  - `shortCurveZ` — used by 13 in-file decls (every other decl).
  - `shortCurveQ` — used by 6 in-file decls (the `shortCurveQ_a*` lemmas + `shortCurveQ_equation_iff`).
- **Unused decls (in this file):** all 12 lemmas are unused within the file — `shortCurveZ_a₁`, `shortCurveZ_a₂`, `shortCurveZ_a₃`, `shortCurveZ_a₄`, `shortCurveZ_a₆`, `shortCurveQ_a₁`, `shortCurveQ_a₂`, `shortCurveQ_a₃`, `shortCurveQ_a₄`, `shortCurveQ_a₆`, `shortCurveQ_equation_iff`, `shortCurveZ_delta`. (This is a foundational API file; lemmas are exported for downstream Lutz-Nagell files, per the file's docstring.)
- **Decls with `sorry`:** none.
- **Decls with `set_option`:** none.
- **Proofs >50 lines:** none (0).
- **Proofs 30–50 lines:** none (0).

All proofs are ≤4 lines (mostly `rfl`/`simp`); no decomposition or further proof-pass needed.
