# Inventory: ./HasseWeil/SingularPoint.lean

**File**: `HasseWeil/SingularPoint.lean`
**Lines**: 226
**Imports**: `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic`, `Mathlib.Algebra.CubicDiscriminant`, `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`

This file develops the theory of singular points on Weierstrass curves (Silverman III.1.4): characterizes singularities via partial derivative vanishing, proves Δ=0 iff a singular point exists (over an algebraically closed field of char ≠ 2), and classifies singularities into nodes (c₄ ≠ 0) and cusps (c₄ = 0).

No other file in the project imports this file.

---

### `def Singular`
- **Type**: `(W : WeierstrassCurve R) (x y : R) : Prop`
- **What**: Defines a point (x, y) to be singular on W if it satisfies the curve equation and both partial derivatives (∂F/∂X and ∂F/∂Y) vanish.
- **How**: Pure propositional conjunction of `W.toAffine.Equation x y`, `polynomialX.evalEval x y = 0`, and `polynomialY.evalEval x y = 0`.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: []
- **Used by**: `Singular.equation`, `Singular.not_nonsingular`, `Δ_eq_zero_of_singular`, `c₄_eq_tangentConeDisc_sq_of_singular`, `exists_singular_of_Δ_eq_zero`, `exists_singular_iff_Δ_eq_zero`, `HasNode`, `HasCusp`
- **Visibility**: public
- **Lines**: 33–36, definition (no proof body)
- **Notes**: Core definition; used by nearly every declaration in the file.

---

### `theorem Singular.equation`
- **Type**: `{x y : R} → W.Singular x y → W.toAffine.Equation x y`
- **What**: Extracts the curve equation from a singularity witness.
- **How**: Direct field projection `h.1`.
- **Hypotheses**: W a Weierstrass curve over a commutative ring R; (x, y) a singular point.
- **Uses from project**: [`Singular`]
- **Used by**: `Δ_eq_zero_of_singular` (indirectly via `not_nonsingular`)
- **Visibility**: public
- **Lines**: 40–41, 1-line proof

---

### `theorem Singular.not_nonsingular`
- **Type**: `{x y : R} → W.Singular x y → ¬W.toAffine.Nonsingular x y`
- **What**: A singular point cannot be nonsingular: the partial-derivative conditions from `Singular` directly contradict `Nonsingular` (which requires at least one partial derivative to be nonzero).
- **How**: Destructs the `Nonsingular` hypothesis to get `hx | hy` (one of the partials nonzero), then applies the corresponding component of `h.2.1`/`h.2.2` to derive `False`.
- **Hypotheses**: (x, y) a singular point on W.
- **Uses from project**: [`Singular`]
- **Used by**: `Δ_eq_zero_of_singular`
- **Visibility**: public
- **Lines**: 43–47, 4-line proof

---

### `theorem Δ_eq_zero_of_singular`
- **Type**: `{W : WeierstrassCurve F} {x y : F} → W.Singular x y → W.Δ = 0`
- **What**: Any singular point on a Weierstrass curve over a field forces the discriminant Δ to be zero.
- **How**: By contradiction: if Δ ≠ 0, then `Affine.equation_iff_nonsingular_of_Δ_ne_zero` (a mathlib lemma) converts the equation at (x, y) into nonsingularity, contradicting `Singular.not_nonsingular`.
- **Hypotheses**: F a field; W a Weierstrass curve over F; (x, y) a singular point.
- **Uses from project**: [`Singular`, `Singular.equation`, `Singular.not_nonsingular`]
- **Used by**: `exists_singular_iff_Δ_eq_zero`, `HasNode.Δ_eq_zero_and_c₄_ne_zero`, `HasCusp.Δ_eq_zero_and_c₄_eq_zero`
- **Visibility**: public
- **Lines**: 54–58, 4-line proof

---

### `def tangentConeDisc`
- **Type**: `(W : WeierstrassCurve R) (x : R) : R`
- **What**: The tangent cone discriminant `a₁² + 12x + 4a₂` at a point with x-coordinate x on W. This is the discriminant of the degree-2 homogeneous part of F (the quadratic form Y² + a₁XY − (3x₀ + a₂)X²) determining whether the singularity is a node or cusp.
- **How**: Direct formula; no proof.
- **Hypotheses**: None beyond CommRing.
- **Uses from project**: []
- **Used by**: `c₄_eq_tangentConeDisc_sq_of_singular`, `HasNode`, `HasCusp`, `HasNode.Δ_eq_zero_and_c₄_ne_zero`, `HasCusp.Δ_eq_zero_and_c₄_eq_zero`, `hasNode_iff`, `hasCusp_iff`
- **Visibility**: public
- **Lines**: 65–66, definition only
- **Notes**: Second most-used definition in the file (called by 6 other declarations).

---

### `theorem c₄_eq_tangentConeDisc_sq_of_singular`
- **Type**: `{W : WeierstrassCurve R} {x y : R} → W.Singular x y → W.c₄ = (W.tangentConeDisc x) ^ 2`
- **What**: At a singular point, the invariant c₄ equals the square of the tangent cone discriminant. This is the key identity connecting the algebraic invariant c₄ to the local geometry of the singularity.
- **How**: Destructs the singularity to get the two partial-derivative equations (using `Affine.evalEval_polynomialX` and `Affine.evalEval_polynomialY`), then uses `simp` to unfold `c₄`, `b₂`, `b₄`, `tangentConeDisc` and concludes by `linear_combination` with coefficients `48 * hpX + (-24 * W.a₁) * hpY`.
- **Hypotheses**: W a Weierstrass curve over a commutative ring R; (x, y) a singular point.
- **Uses from project**: [`Singular`, `tangentConeDisc`]
- **Used by**: `HasNode.Δ_eq_zero_and_c₄_ne_zero`, `HasCusp.Δ_eq_zero_and_c₄_eq_zero`, `hasNode_iff`, `hasCusp_iff`
- **Visibility**: public
- **Lines**: 71–77, 7-line proof

---

### `theorem exists_singular_of_Δ_eq_zero`
- **Type**: `(W : WeierstrassCurve F) [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (hΔ : W.Δ = 0) → ∃ x y, W.Singular x y`
- **What**: Over an algebraically closed field of characteristic ≠ 2, if Δ = 0 then the Weierstrass curve has a singular point. The proof constructs an explicit singular point from a repeated root of the 2-torsion polynomial (= 4x³ + b₂x² + 2b₄x + b₆).
- **How**: The key chain: (1) `twoTorsionPolynomial_discr` gives `discr(twoTorsionPoly) = 16Δ = 0`; (2) `IsAlgClosed.splits` gives three roots x, y, z over F; (3) `Cubic.discr_ne_zero_iff_roots_ne` forces a repeated root (hdup); (4) for the repeated root x₀, set y₀ = −(a₁x₀ + a₃)/2 and verify the three conditions of `Singular` via `linear_combination` after unfolding `twoTorsionPolynomial`, `equation_iff'`, and `evalEval_polynomialX/Y`.
- **Hypotheses**: F algebraically closed, char F ≠ 2; Δ = 0.
- **Uses from project**: [`Singular`, `tangentConeDisc` (implicit via `Singular`)]
- **Used by**: `exists_singular_iff_Δ_eq_zero`, `hasNode_iff`, `hasCusp_iff`
- **Visibility**: public
- **Lines**: 93–166, **74-line proof**
- **Notes**: Longest proof in the file (74 lines), no sorry, no `set_option maxHeartbeats`. Uses three-case split on which pair of the three roots is equal, with structurally identical simp blocks for each case (some repetition). Mathlib lemmas: `Cubic.splits_iff_roots_eq_three`, `Cubic.discr_ne_zero_iff_roots_ne`, `Cubic.eq_prod_three_roots`, `twoTorsionPolynomial_discr`, `Affine.equation_iff'`, `Affine.evalEval_polynomialX`, `Affine.evalEval_polynomialY`.

---

### `theorem exists_singular_iff_Δ_eq_zero`
- **Type**: `[IsAlgClosed F] {W : WeierstrassCurve F} (h2 : (2 : F) ≠ 0) → (∃ x y, W.Singular x y) ↔ W.Δ = 0`
- **What**: Over an algebraically closed field of characteristic ≠ 2, the Weierstrass curve has a singular point if and only if Δ = 0. The iff assembly of the two directions.
- **How**: Forward direction uses `Δ_eq_zero_of_singular`; backward direction uses `exists_singular_of_Δ_eq_zero`.
- **Hypotheses**: F algebraically closed, char F ≠ 2.
- **Uses from project**: [`Singular`, `Δ_eq_zero_of_singular`, `exists_singular_of_Δ_eq_zero`]
- **Used by**: unused in file (leaf theorem; no callers within file)
- **Visibility**: public
- **Lines**: 172–175, 2-line proof

---

### `def HasNode`
- **Type**: `(W : WeierstrassCurve R) : Prop`
- **What**: A Weierstrass curve has a node if it has a singular point (x, y) with nonzero tangent cone discriminant (two distinct tangent directions). Silverman III.1.4(b).
- **How**: Existential definition; no proof.
- **Hypotheses**: None beyond CommRing.
- **Uses from project**: [`Singular`, `tangentConeDisc`]
- **Used by**: `HasNode.Δ_eq_zero_and_c₄_ne_zero`, `hasNode_iff`
- **Visibility**: public
- **Lines**: 182–183, definition only

---

### `def HasCusp`
- **Type**: `(W : WeierstrassCurve R) : Prop`
- **What**: A Weierstrass curve has a cusp if it has a singular point (x, y) with zero tangent cone discriminant (single tangent direction). Silverman III.1.4(c).
- **How**: Existential definition; no proof.
- **Hypotheses**: None beyond CommRing.
- **Uses from project**: [`Singular`, `tangentConeDisc`]
- **Used by**: `HasCusp.Δ_eq_zero_and_c₄_eq_zero`, `hasCusp_iff`
- **Visibility**: public
- **Lines**: 188–189, definition only

---

### `theorem HasNode.Δ_eq_zero_and_c₄_ne_zero`
- **Type**: `{W : WeierstrassCurve F} → W.HasNode → W.Δ = 0 ∧ W.c₄ ≠ 0`
- **What**: If a Weierstrass curve over a field has a node, then Δ = 0 and c₄ ≠ 0.
- **How**: Destructs `HasNode` to get the singular point and non-zero discriminant; applies `Δ_eq_zero_of_singular` for the first conjunct; uses `c₄_eq_tangentConeDisc_sq_of_singular` and `pow_ne_zero` for the second.
- **Hypotheses**: F a field; W has a node.
- **Uses from project**: [`HasNode`, `Singular`, `Δ_eq_zero_of_singular`, `c₄_eq_tangentConeDisc_sq_of_singular`, `tangentConeDisc`]
- **Used by**: `hasNode_iff`
- **Visibility**: public
- **Lines**: 191–195, 5-line proof

---

### `theorem HasCusp.Δ_eq_zero_and_c₄_eq_zero`
- **Type**: `{W : WeierstrassCurve F} → W.HasCusp → W.Δ = 0 ∧ W.c₄ = 0`
- **What**: If a Weierstrass curve over a field has a cusp, then Δ = 0 and c₄ = 0.
- **How**: Destructs `HasCusp`; applies `Δ_eq_zero_of_singular` for Δ = 0; uses `c₄_eq_tangentConeDisc_sq_of_singular`, rewrites with `hdisc = 0`, and `ring` to get 0² = 0.
- **Hypotheses**: F a field; W has a cusp.
- **Uses from project**: [`HasCusp`, `Singular`, `Δ_eq_zero_of_singular`, `c₄_eq_tangentConeDisc_sq_of_singular`, `tangentConeDisc`]
- **Used by**: `hasCusp_iff`
- **Visibility**: public
- **Lines**: 197–201, 5-line proof

---

### `theorem hasNode_iff`
- **Type**: `[IsAlgClosed F] {W : WeierstrassCurve F} (h2 : (2 : F) ≠ 0) → W.HasNode ↔ W.Δ = 0 ∧ W.c₄ ≠ 0`
- **What**: Over an algebraically closed field of characteristic ≠ 2, a Weierstrass curve has a node iff Δ = 0 and c₄ ≠ 0.
- **How**: Forward by `HasNode.Δ_eq_zero_and_c₄_ne_zero`; backward: use `exists_singular_of_Δ_eq_zero` to find a singular point, then show the tangent cone discriminant is nonzero by contradiction using `c₄_eq_tangentConeDisc_sq_of_singular`.
- **Hypotheses**: F algebraically closed, char F ≠ 2.
- **Uses from project**: [`HasNode`, `HasNode.Δ_eq_zero_and_c₄_ne_zero`, `exists_singular_of_Δ_eq_zero`, `c₄_eq_tangentConeDisc_sq_of_singular`, `tangentConeDisc`]
- **Used by**: unused in file (leaf theorem)
- **Visibility**: public
- **Lines**: 205–212, 9-line proof

---

### `theorem hasCusp_iff`
- **Type**: `[IsAlgClosed F] {W : WeierstrassCurve F} (h2 : (2 : F) ≠ 0) → W.HasCusp ↔ W.Δ = 0 ∧ W.c₄ = 0`
- **What**: Over an algebraically closed field of characteristic ≠ 2, a Weierstrass curve has a cusp iff Δ = 0 and c₄ = 0.
- **How**: Forward by `HasCusp.Δ_eq_zero_and_c₄_eq_zero`; backward: use `exists_singular_of_Δ_eq_zero`, then `sq_eq_zero_iff` together with `c₄_eq_tangentConeDisc_sq_of_singular` to extract the zero discriminant from c₄ = 0.
- **Hypotheses**: F algebraically closed, char F ≠ 2.
- **Uses from project**: [`HasCusp`, `HasCusp.Δ_eq_zero_and_c₄_eq_zero`, `exists_singular_of_Δ_eq_zero`, `c₄_eq_tangentConeDisc_sq_of_singular`, `tangentConeDisc`]
- **Used by**: unused in file (leaf theorem)
- **Visibility**: public
- **Lines**: 216–223, 9-line proof

---

## Summary

| Kind | Count |
|------|-------|
| `def` | 3 (`Singular`, `tangentConeDisc`, `HasNode`, `HasCusp`) |
| `theorem` | 10 |
| `instance` | 0 |
| Total | 13 (if counting `HasNode` and `HasCusp` as `def`) |

- **No `sorry`** anywhere in the file.
- **No `set_option maxHeartbeats`** anywhere in the file.
- **Long proof**: `exists_singular_of_Δ_eq_zero` (74 lines, lines 93–166).
- **Unused declarations** (no callers within this file): `exists_singular_iff_Δ_eq_zero`, `hasNode_iff`, `hasCusp_iff`.
  - Additionally, the file itself is not imported by any other project file — all public declarations are effectively dead code with respect to the rest of the project.
- **Key API** (used by 3+ declarations within the file): `Singular` (used by ~10), `tangentConeDisc` (used by 6), `c₄_eq_tangentConeDisc_sq_of_singular` (used by 4), `Δ_eq_zero_of_singular` (used by 4).
- **Notes**: Self-contained file covering Silverman III.1.4 (singular point characterization). Not imported anywhere in the project — this is a standalone contribution (possibly intended for mathlib upstream). The main proof `exists_singular_of_Δ_eq_zero` has three structurally identical branches (for the three possible duplicate-root pairs) that could be refactored.
