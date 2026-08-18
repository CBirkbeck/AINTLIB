# Inventory: LutzNagell/LutzNagellTheorem/Main.lean

Path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/LutzNagell/LutzNagellTheorem/Main.lean`

Namespace: `LutzNagell.LutzNagellTheorem` (with `open WeierstrassCurve`)

This file is the top-level façade for the Lutz–Nagell theorem on the short Weierstrass curve `y² = x³ + Ax + B`. It re-packages results proved in the three imported sibling modules (`ShortWeierstrass`, `GeneralMain`, `GeneralDiscriminant`) into the named theorem `lutz_nagell` and its two halves. All heavy mathematical content lives in the imports; this file contains only specialization glue.

---

### theorem lutz_nagell_integrality
- Type: `(A B : ℤ) (hΔ : (shortCurveZ A B).Δ ≠ 0) {x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y) (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) : (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y`
- What: Part 1 of Lutz–Nagell — a nonzero finite-order (torsion) rational point `(x, y)` on the short Weierstrass curve `y² = x³ + Ax + B` over `ℚ` (with nonzero discriminant) has integer coordinates: both `x` and `y` are integers.
- How: Direct re-export; the entire proof is the single term `lutz_nagell_integrality_short A B hpt htor`, deferring all the `p`-adic / reduction-mod-`p` integrality argument to the imported general result. (Note: the `hΔ` hypothesis is accepted for uniform signature but not used in the body — integrality is delegated.)
- Hypotheses: `A, B` integers; the integral curve `shortCurveZ A B` has nonzero discriminant `Δ`; `(x, y)` is a nonsingular (affine) point of the rational curve `shortCurveQ A B`; that point has finite additive order in the group of rational points.
- Uses from project: [lutz_nagell_integrality_short] (imported from `GeneralMain.lean`; `shortCurveZ`, `shortCurveQ` from `ShortWeierstrass.lean` appear in the statement type)
- Used by: lutz_nagell
- Visibility: public
- Lines: 31–39 (proof length: 1 line, term-mode)
- Notes: none

---

### theorem lutz_nagell_discriminant
- Type: `(A B : ℤ) (hΔ : (shortCurveZ A B).Δ ≠ 0) {x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y) (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) {x₀ y₀ : ℤ} (hx : (x₀ : ℚ) = x) (hy : (y₀ : ℚ) = y) : y₀ = 0 ∨ y₀ ^ 2 ∣ (shortCurveZ A B).Δ`
- What: Part 2 of Lutz–Nagell — for a nonzero torsion point with integer coordinates `(x₀, y₀)` on `y² = x³ + Ax + B`, either `y₀ = 0` or `y₀²` divides the discriminant `Δ_{A,B}`.
- How: Specializes the general theorem `lutz_nagell_discriminant_general` (for arbitrary Weierstrass curves, phrased via `κ₀ = 2y₀ + a₁x₀ + a₃` and `κ₀² ∣ 4Δ`) to the short form where `a₁ = a₃ = 0`; rewrites using the simp lemmas `shortCurveZ_a₁`/`shortCurveZ_a₃` to collapse `κ₀` to `2y₀`, then in the divisibility branch rewrites `(2y₀)² = 4y₀²` and cancels the common factor `4` via `mul_dvd_mul_iff_left` (with `(4 : ℤ) ≠ 0`); the `κ₀ = 0` branch yields `y₀ = 0` by `omega`.
- Hypotheses: `A, B` integers; `shortCurveZ A B` has nonzero discriminant; `(x, y)` nonsingular rational point of finite additive order; `x₀, y₀` integers casting to the rational coordinates `x, y`.
- Uses from project: [lutz_nagell_discriminant_general, shortCurveZ_a₁, shortCurveZ_a₃] (`lutz_nagell_discriminant_general` from `GeneralDiscriminant.lean`; `shortCurveZ_a₁`, `shortCurveZ_a₃` simp lemmas from `ShortWeierstrass.lean`; `shortCurveZ`, `shortCurveQ` in the statement type)
- Used by: lutz_nagell
- Visibility: public
- Lines: 41–59 (proof length: 7 lines)
- Notes: none

---

### theorem lutz_nagell
- Type: `(A B : ℤ) (hΔ : (shortCurveZ A B).Δ ≠ 0) {x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y) (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) : ∃ (x₀ y₀ : ℤ), (x₀ : ℚ) = x ∧ (y₀ : ℚ) = y ∧ (y₀ = 0 ∨ y₀ ^ 2 ∣ (shortCurveZ A B).Δ)`
- What: The full Lutz–Nagell theorem (Theorem 1.1 of "Nagell–Lutz, quickly"): a nonidentity rational point of finite order on `E : y² = x³ + Ax + B` (with `Δ_{A,B} = -16(4A³ + 27B²) ≠ 0`) has integer coordinates `x₀, y₀`, and either `y₀ = 0` or `y₀² ∣ Δ_{A,B}`.
- How: Combines the two halves — `obtain` the integer witnesses `x₀, y₀` (with cast equalities `hx, hy`) from `lutz_nagell_integrality`, then packages them with the conclusion of `lutz_nagell_discriminant A B hΔ hpt htor hx hy` into the existential.
- Hypotheses: `A, B` integers; `shortCurveZ A B` has nonzero discriminant; `(x, y)` is a nonsingular rational point; that point has finite additive order.
- Uses from project: [lutz_nagell_integrality, lutz_nagell_discriminant] (both defined above in this file; `shortCurveZ`, `shortCurveQ` in the statement type)
- Used by: unused in file
- Visibility: public
- Lines: 61–72 (proof length: 2 lines)
- Notes: none

---

## File Summary

- Total decls: 3 (defs: 0 / lemmas+theorems: 3 / instances: 0). All three are `theorem`s.
- Key API (used by ≥3 in-file): none. (`lutz_nagell_integrality` and `lutz_nagell_discriminant` are each used once, by `lutz_nagell`.)
- Unused decls (in-file): `lutz_nagell` (the file's exported endpoint; consumed by downstream modules, not within this file).
- Decls with `sorry`: none.
- Decls with `set_option`: none.
- Proofs >50 lines (OVER-50): none (count: 0). Longest proof is `lutz_nagell_discriminant` at 7 lines.
- Proofs 30–50 lines (long): none (count: 0).

Cross-file note: this file is pure façade/glue. All substantive mathematics is imported — `lutz_nagell_integrality_short` (`GeneralMain.lean:153`), `lutz_nagell_discriminant_general` (`GeneralDiscriminant.lean:226`), and the curve definitions/simp lemmas `shortCurveZ`/`shortCurveQ`/`shortCurveZ_a₁`/`shortCurveZ_a₃` (`ShortWeierstrass.lean`). Observation: `hΔ` is unused in `lutz_nagell_integrality`'s body (carried for signature uniformity).
