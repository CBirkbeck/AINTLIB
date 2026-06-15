# Inventory: ./HasseWeil/EC/DifferentialOrd.lean

**File**: `HasseWeil/EC/DifferentialOrd.lean`  
**Lines**: 1–634  
**Imports**: `HasseWeil.WeilPairing.TorsionGeometric`, `HasseWeil.EC.TranslationOrd`  
**Namespace**: `HasseWeil`  
**Total declarations**: 34 (2 defs, 32 lemmas/theorems, 0 instances)  
**Sorries**: none  
**maxHeartbeats overrides**: none  

---

## Summary

This file develops the **ω-derivative** `Dω : K(E) → K(E)` for the function field of an elliptic
curve over a field `F`, defined as the unique element `c` satisfying `D f = c • ω` (using
`kaehler_rank_one`). It proves: all derivation laws (Leibniz, additivity, F-linearity), that `Dω`
preserves the coordinate ring, that Dω is regular at smooth points, and the key order inequality
`ord_P (Dω f) ≥ ord_P f − 1`. The file then specialises to isogenies (general `e ≤ 1` bound) and
`[ℓ]` (characteristic-free y-coordinate separability input).

---

## Declarations

### `noncomputable def Dω`
- **Type**: `(f : KE) : KE`
- **What**: The ω-derivative of f: the unique c in K(E) with `D f = c • ω`, extracted by choosing from the surjectivity of `(• ω)` on the 1-dimensional Kähler module.
- **How**: Uses `exists_smul_eq_of_finrank_eq_one` applied to `kaehler_rank_one W.toAffine` and `invariantDifferential_ne_zero W.toAffine`, taking `.choose`.
- **Hypotheses**: W is an elliptic curve (IsElliptic).
- **Uses from project**: `kaehler_rank_one`, `invariantDifferential_ne_zero`, `exists_smul_eq_of_finrank_eq_one`, `invariantDifferential`
- **Used by**: All subsequent theorems in the file.
- **Visibility**: public
- **Lines**: 51–54, def body 3 lines
- **Notes**: `noncomputable` (function field is noncomputable).

---

### `theorem Dω_spec`
- **Type**: `(f : KE) : KaehlerDifferential.D F KE f = Dω W f • invariantDifferential W.toAffine`
- **What**: The defining equation `D f = (Dω f) • ω`, i.e., `Dω` is characterised by being the coefficient of ω in the Kähler differential of f.
- **How**: Uses `.choose_spec` on the same `exists_smul_eq_of_finrank_eq_one` choice as `Dω`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `kaehler_rank_one`, `invariantDifferential_ne_zero`, `exists_smul_eq_of_finrank_eq_one`, `invariantDifferential`
- **Used by**: `Dω_add`, `Dω_algebraMap`, `Dω_mul`, `Dω_smul`, `Dω_sub`, `Dω_pow`, `Dω_inv`
- **Visibility**: public
- **Lines**: 56–59, proof 1 line
- **Notes**: Used by all basic Dω law proofs via `← Dω_spec`.

---

### `theorem Dω_eq_of_smul`
- **Type**: `{f c : KE} → (h : c • invariantDifferential W.toAffine = KaehlerDifferential.D F KE f) → c = Dω W f`
- **What**: Uniqueness: if `c • ω = D f` then `c = Dω f`. Reverses the defining equation.
- **How**: Applies `omegaPullbackCoeff_unique` to relate two choices satisfying the same equation.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `omegaPullbackCoeff_unique`, `Dω_spec`
- **Used by**: `Dω_add`, `Dω_algebraMap`, `Dω_mul`, `Dω_smul`, `Dω_sub`, `Dω_pow`, `Dω_inv`, `Dω_x_gen`, `Dω_y_gen`, `Dω_isog_pullback_x_gen`, `Dω_isog_pullback_y_gen`, `Dω_mulByInt_pullback_y_gen`
- **Visibility**: public
- **Lines**: 62–65, proof 2 lines
- **Notes**: The key API lemma — every basic Dω computation reduces to producing the smul equation and applying this.

---

### `theorem Dω_add`
- **Type**: `(f g : KE) : Dω W (f + g) = Dω W f + Dω W g`
- **What**: Dω is additive.
- **How**: Via `Dω_eq_of_smul` applied to `add_smul` + `map_add` on D.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Dω_eq_of_smul`, `Dω_spec`
- **Used by**: `Dω_x_gen_mem_Rimg` (indirectly), `Dω_aeval_x_gen_mem_Rimg`, `Dω_algebraMap_mem_Rimg`
- **Visibility**: public (`@[simp]`)
- **Lines**: 68–70, proof 3 lines

---

### `theorem Dω_algebraMap`
- **Type**: `(a : F) : Dω W (algebraMap F KE a) = 0`
- **What**: Dω kills base-field constants (F-constants have zero Kähler differential over F).
- **How**: Via `Dω_eq_of_smul` applied to `zero_smul` + `map_algebraMap`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Dω_eq_of_smul`
- **Used by**: `Dω_zero`, `Dω_aeval_x_gen_mem_Rimg`, `Dω_algebraMap_mem_Rimg`, `ord_P_isog_pullback_x_sub_const_le_one`, `ord_P_isog_pullback_y_sub_const_le_one`, `ord_P_mulByInt_y_sub_const_le_one`
- **Visibility**: public (`@[simp]`)
- **Lines**: 73–75, proof 3 lines

---

### `theorem Dω_zero`
- **Type**: `Dω W (0 : KE) = 0`
- **What**: Dω of 0 is 0.
- **How**: Specialises `Dω_algebraMap` at `0 : F`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Dω_algebraMap`
- **Used by**: `Dω_neg`
- **Visibility**: public (`@[simp]`)
- **Lines**: 78–79, proof 2 lines

---

### `theorem Dω_mul`
- **Type**: `(f g : KE) : Dω W (f * g) = f * Dω W g + g * Dω W f`
- **What**: Leibniz rule for Dω.
- **How**: Via `Dω_eq_of_smul` + `D.leibniz` (mathlib Kähler differential Leibniz).
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Dω_eq_of_smul`, `Dω_spec`
- **Used by**: `Dω_aeval_x_gen_mem_Rimg`, `Dω_algebraMap_mem_Rimg`, `ord_P_Dω_nonneg`, `one_le_ord_P_Dω_of_two_le`, `two_le_ord_P_of_Dω_vanishes_of_uniformizer`, `ord_P_isog_pullback_x_sub_const_le_one` (via `Dω_sub`)
- **Visibility**: public (`@[simp]`)
- **Lines**: 82–85, proof 4 lines

---

### `theorem Dω_smul`
- **Type**: `(a : F) (f : KE) : Dω W (a • f) = a • Dω W f`
- **What**: Dω is F-linear (homogeneous under scalar multiplication).
- **How**: Via `Dω_eq_of_smul` + `D.map_smul` (Kähler D is F-linear).
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Dω_eq_of_smul`, `Dω_spec`
- **Used by**: unused in file; exported
- **Visibility**: public (`@[simp]`)
- **Lines**: 88–90, proof 3 lines

---

### `theorem Dω_sub`
- **Type**: `(f g : KE) : Dω W (f - g) = Dω W f - Dω W g`
- **What**: Dω is subtractive.
- **How**: Via `Dω_eq_of_smul` + `sub_smul` + `map_sub`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Dω_eq_of_smul`, `Dω_spec`
- **Used by**: `Dω_neg`, `ord_P_isog_pullback_x_sub_const_le_one`, `ord_P_isog_pullback_y_sub_const_le_one`, `ord_P_mulByInt_y_sub_const_le_one`
- **Visibility**: public (`@[simp]`)
- **Lines**: 93–95, proof 3 lines

---

### `theorem Dω_neg`
- **Type**: `(f : KE) : Dω W (-f) = -Dω W f`
- **What**: Dω of negation.
- **How**: Rewrites `-f = 0 - f` and applies `Dω_sub` + `Dω_zero`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Dω_sub`, `Dω_zero`
- **Used by**: unused in file; exported
- **Visibility**: public (`@[simp]`)
- **Lines**: 98–99, proof 2 lines

---

### `theorem Dω_pow`
- **Type**: `(f : KE) (n : ℕ) : Dω W (f ^ n) = (n : KE) * f ^ (n - 1) * Dω W f`
- **What**: Power rule for Dω: Dω(f^n) = n * f^{n-1} * Dω(f).
- **How**: Via `Dω_eq_of_smul` + `D.leibniz_pow` + `smul_smul` + `Nat.cast_smul_eq_nsmul`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Dω_eq_of_smul`, `Dω_spec`
- **Used by**: `Dω_aeval_x_gen_mem_Rimg`, `Dω_algebraMap_mem_Rimg`, `one_le_ord_P_Dω_of_two_le`
- **Visibility**: public
- **Lines**: 102–106, proof 5 lines

---

### `theorem Dω_inv`
- **Type**: `(f : KE) : Dω W f⁻¹ = -f⁻¹ ^ 2 * Dω W f`
- **What**: Dω of inverse: Dω(f⁻¹) = −f⁻² · Dω(f).
- **How**: Via `Dω_eq_of_smul` + `D.leibniz_inv` (mathlib inverse rule for Kähler D).
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Dω_eq_of_smul`, `Dω_spec`
- **Used by**: unused in file; exported
- **Visibility**: public
- **Lines**: 109–111, proof 3 lines

---

### `theorem Dω_x_gen`
- **Type**: `Dω W (x_gen W) = u_gen W`
- **What**: The ω-derivative of x_gen is u_gen = 2y + a₁x + a₃ (the Weierstrass y-partial).
- **How**: Applies `Dω_eq_of_smul` to the project lemma `kaehlerD_x_gen_eq_u_smul_omega`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Dω_eq_of_smul`, `WeilPairing.TorsionGeometric.kaehlerD_x_gen_eq_u_smul_omega`, `x_gen`, `u_gen`
- **Used by**: `Dω_x_gen_mem_Rimg`
- **Visibility**: public
- **Lines**: 116–117, proof 1 line

---

### `theorem Dω_y_gen`
- **Type**: `Dω W (y_gen W) = 3 * x_gen W ^ 2 + 2 * algebraMap F KE W.a₂ * x_gen W + algebraMap F KE W.a₄ - algebraMap F KE W.a₁ * y_gen W`
- **What**: The ω-derivative of y_gen is the x-partial of the Weierstrass equation (3x² + 2a₂x + a₄ − a₁y).
- **How**: Applies `Dω_eq_of_smul` to `kaehlerD_y_gen_eq_num_smul_omega`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Dω_eq_of_smul`, `WeilPairing.TorsionGeometric.kaehlerD_y_gen_eq_num_smul_omega`, `x_gen`, `y_gen`
- **Used by**: `Dω_y_gen_mem_Rimg`
- **Visibility**: public
- **Lines**: 120–124, proof 1 line

---

### `theorem evalEval_xy_gen_eq_algebraMap_mk`
- **Type**: `(p : (Polynomial F)[X]) : (p.map (Polynomial.mapRingHom (algebraMap F KE))).evalEval (x_gen W) (y_gen W) = algebraMap R KE (Affine.CoordinateRing.mk W.toAffine p)`
- **What**: Evaluation of a bivariate polynomial at (x_gen, y_gen) via algebraMap equals the coordinate-ring element it represents — the canonical identification of the bivariate presentation with the coordinate ring.
- **How**: Rewrites algebraMap F KE as `(algebraMap R KE).comp (algebraMap F R)`, uses `Polynomial.map_mapRingHom_evalEval`, then `AdjoinRoot.aeval_eq`.
- **Hypotheses**: IsElliptic (implicit via R, KE).
- **Uses from project**: `x_gen`, `y_gen`
- **Used by**: `Dω_algebraMap_mem_Rimg`
- **Visibility**: public
- **Lines**: 134–153, proof 20 lines

---

### `noncomputable def Rimg`
- **Type**: `Subring KE`
- **What**: The subring of K(E) that is the image of the coordinate ring R under the natural embedding `algebraMap R KE`.
- **How**: Defined as `(algebraMap R KE).range`.
- **Hypotheses**: IsElliptic (implicit).
- **Uses from project**: none (purely structural)
- **Used by**: `algebraMap_F_mem_Rimg`, `x_gen_mem_Rimg`, `y_gen_mem_Rimg`, `Dω_x_gen_mem_Rimg`, `Dω_y_gen_mem_Rimg`, `aeval_x_gen_mem_Rimg`, `Dω_aeval_x_gen_mem_Rimg`, `Dω_algebraMap_mem_Rimg`, `ord_P_nonneg_of_mem_Rimg`, `ord_P_Dω_nonneg`
- **Visibility**: public
- **Lines**: 156, def 1 line

---

### `theorem algebraMap_F_mem_Rimg`
- **Type**: `(c : F) : algebraMap F KE c ∈ Rimg W`
- **What**: Base-field constants lie in the coordinate-ring image.
- **How**: Exhibits the witness `algebraMap F R c` via `IsScalarTower.algebraMap_apply`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Rimg`
- **Used by**: `Dω_x_gen_mem_Rimg`, `Dω_y_gen_mem_Rimg`, `aeval_x_gen_mem_Rimg`, `Dω_aeval_x_gen_mem_Rimg`
- **Visibility**: public
- **Lines**: 159–160, proof 1 line

---

### `theorem x_gen_mem_Rimg`
- **Type**: `x_gen W ∈ Rimg W`
- **What**: The x-generator lies in the coordinate-ring image.
- **How**: Exhibits `algebraMap (Polynomial F) R Polynomial.X` as witness.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Rimg`, `x_gen`
- **Used by**: `Dω_x_gen_mem_Rimg`, `Dω_y_gen_mem_Rimg` (indirectly), `aeval_x_gen_mem_Rimg`, `Dω_aeval_x_gen_mem_Rimg`, `Dω_algebraMap_mem_Rimg`
- **Visibility**: public
- **Lines**: 163–164, proof 1 line

---

### `theorem y_gen_mem_Rimg`
- **Type**: `y_gen W ∈ Rimg W`
- **What**: The y-generator lies in the coordinate-ring image.
- **How**: Exhibits `AdjoinRoot.root W.toAffine.polynomial` as witness.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Rimg`, `y_gen`
- **Used by**: `Dω_x_gen_mem_Rimg`, `Dω_y_gen_mem_Rimg`, `Dω_algebraMap_mem_Rimg`
- **Visibility**: public
- **Lines**: 167–168, proof 1 line

---

### `theorem Dω_x_gen_mem_Rimg`
- **Type**: `Dω W (x_gen W) ∈ Rimg W`
- **What**: Dω(x_gen) = u_gen is in the coordinate-ring image (u_gen is an explicit linear combination of generators).
- **How**: Rewrites via `Dω_x_gen` and `u_gen`, then applies `Subring.add_mem`/`mul_mem` using `y_gen_mem_Rimg`, `x_gen_mem_Rimg`, `algebraMap_F_mem_Rimg`, and `natCast_mem`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Dω_x_gen`, `u_gen`, `y_gen_mem_Rimg`, `x_gen_mem_Rimg`, `algebraMap_F_mem_Rimg`, `natCast_mem`, `Rimg`
- **Used by**: `Dω_aeval_x_gen_mem_Rimg`
- **Visibility**: public
- **Lines**: 171–176, proof 6 lines

---

### `theorem Dω_y_gen_mem_Rimg`
- **Type**: `Dω W (y_gen W) ∈ Rimg W`
- **What**: Dω(y_gen) is in the coordinate-ring image.
- **How**: Rewrites via `Dω_y_gen`, then assembles membership using `Subring.*_mem` primitives together with `x_gen_mem_Rimg`, `y_gen_mem_Rimg`, `algebraMap_F_mem_Rimg`, `natCast_mem`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Dω_y_gen`, `x_gen_mem_Rimg`, `y_gen_mem_Rimg`, `algebraMap_F_mem_Rimg`, `natCast_mem`, `Rimg`
- **Used by**: `Dω_algebraMap_mem_Rimg`
- **Visibility**: public
- **Lines**: 179–185, proof 7 lines

---

### `theorem aeval_x_gen_mem_Rimg`
- **Type**: `(q : Polynomial F) : Polynomial.aeval (x_gen W) q ∈ Rimg W`
- **What**: Any univariate polynomial in x_gen lies in the coordinate-ring image.
- **How**: Induction on q using `Polynomial.induction_on`; base case uses `algebraMap_F_mem_Rimg`, monomial step uses `x_gen_mem_Rimg` and `algebraMap_F_mem_Rimg`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `x_gen_mem_Rimg`, `algebraMap_F_mem_Rimg`, `Rimg`, `x_gen`
- **Used by**: `Dω_algebraMap_mem_Rimg`
- **Visibility**: public
- **Lines**: 188–196, proof 8 lines

---

### `theorem Dω_aeval_x_gen_mem_Rimg`
- **Type**: `(q : Polynomial F) : Dω W (Polynomial.aeval (x_gen W) q) ∈ Rimg W`
- **What**: Dω of any polynomial in x_gen is in the coordinate-ring image.
- **How**: Induction on q; uses `Dω_algebraMap`, `Dω_add`, `Dω_mul`, `Dω_pow` to reduce to `Dω_x_gen_mem_Rimg` and `algebraMap_F_mem_Rimg`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Dω_algebraMap`, `Dω_add`, `Dω_mul`, `Dω_pow`, `Dω_x_gen_mem_Rimg`, `algebraMap_F_mem_Rimg`, `x_gen_mem_Rimg`, `Rimg`, `x_gen`
- **Used by**: `Dω_algebraMap_mem_Rimg`
- **Visibility**: public
- **Lines**: 199–209, proof 11 lines

---

### `theorem Dω_algebraMap_mem_Rimg`
- **Type**: `(r : R) : Dω W (algebraMap R KE r) ∈ Rimg W`
- **What**: Dω maps the coordinate ring into itself (the full regularity result for Dω on R).
- **How**: Represents r as `mk p` (bivariate), rewrites via `evalEval_xy_gen_eq_algebraMap_mk`, then does polynomial induction (C case: `Dω_aeval_x_gen_mem_Rimg`; add: `Dω_add`; monomial `q·Y^(m+1)`: Leibniz `Dω_mul` + `Dω_pow`, using `Dω_y_gen_mem_Rimg`, `aeval_x_gen_mem_Rimg`, `y_gen_mem_Rimg`).
- **Hypotheses**: IsElliptic.
- **Uses from project**: `evalEval_xy_gen_eq_algebraMap_mk`, `Dω_aeval_x_gen_mem_Rimg`, `Dω_add`, `Dω_mul`, `Dω_pow`, `aeval_x_gen_mem_Rimg`, `Dω_y_gen_mem_Rimg`, `y_gen_mem_Rimg`, `Rimg`
- **Used by**: `ord_P_Dω_nonneg`
- **Visibility**: public
- **Lines**: 214–241, proof 28 lines
- **Notes**: Proof is 28 lines (just under 30-line threshold).

---

### `theorem ord_P_nonneg_of_mem_Rimg`
- **Type**: `{f : KE} → (hf : f ∈ Rimg W) → (P : SmoothPoint) → (0 : WithTop ℤ) ≤ ord_P P f`
- **What**: Any element of the coordinate-ring image Rimg has nonnegative order at every smooth point (i.e., coordinate-ring elements are regular).
- **How**: Pulls out the R-preimage, handles f=0 via `ord_P_zero`, and for f≠0 uses `pointValuation_algebraMap_le_one` (valuation ≤ 1 ⟹ order ≥ 0) combined with `WithZero.unzero` + `toAdd` arithmetic.
- **Hypotheses**: IsElliptic, `f ∈ Rimg W`.
- **Uses from project**: `Rimg`, `pointValuation_le_one_of_ord_nonneg` (in ord_P_Dω_nonneg but not here), `SmoothPlaneCurve.pointValuation_algebraMap_le_one`, `SmoothPlaneCurve.ord_P_zero`
- **Used by**: `ord_P_Dω_nonneg`
- **Visibility**: public
- **Lines**: 249–263, proof 15 lines

---

### `theorem ord_P_Dω_nonneg`
- **Type**: `{f : KE} → (P : SmoothPoint) → (0 : WithTop ℤ) ≤ ord_P P f → (0 : WithTop ℤ) ≤ ord_P P (Dω W f)`
- **What**: If f is regular at P (order ≥ 0), then Dω f is also regular at P (Dω preserves the local ring at P).
- **How**: Represents f as a/b (a,b ∈ R, b ∉ m_P) via `mem_localRingAt_image_of_pointValuation_le_one` + `IsLocalization.surj`. Differentiates the relation f·b = a to get Dω f = (Dω a - f·Dω b)·b⁻¹, then uses `ord_P_nonneg_of_mem_Rimg` on Dω a and Dω b (via `Dω_algebraMap_mem_Rimg`), `ord_P_mul`, `ord_P_inv`, and `ord_P_add_le`.
- **Hypotheses**: IsElliptic, ord_P P f ≥ 0.
- **Uses from project**: `Rimg`, `Dω_mul`, `Dω_algebraMap_mem_Rimg`, `ord_P_nonneg_of_mem_Rimg`, `pointValuation_le_one_of_ord_nonneg`, `SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`, `SmoothPlaneCurve.ord_P_mul`, `SmoothPlaneCurve.ord_P_inv`, `SmoothPlaneCurve.ord_P_add_le`, `SmoothPlaneCurve.ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt`, `SmoothPlaneCurve.ord_P_neg`
- **Used by**: `one_le_ord_P_Dω_of_two_le`, `two_le_ord_P_of_Dω_vanishes_of_uniformizer`
- **Visibility**: public
- **Lines**: 269–320, proof 52 lines
- **Notes**: **Proof is 52 lines** — longest in file. Uses local ring structure (IsLocalization) plus Leibniz.

---

### `theorem one_le_ord_P_Dω_of_two_le`
- **Type**: `{f : KE} → (hf_ne : f ≠ 0) → (P : SmoothPoint) → (2 : WithTop ℤ) ≤ ord_P P f → (1 : WithTop ℤ) ≤ ord_P P (Dω W f)`
- **What**: If f vanishes to order ≥ 2 at P, then Dω f vanishes to order ≥ 1 at P (a differential lowers order by at most 1, used form).
- **How**: Factors f = g · s with s a uniformizer (ord_P s = 1) via `exists_uniformizer`. Computes ord_P g = ord_P f − 1 ≥ 1 using `ord_P_mul` and `WithTop.coe_le_coe`/omega. Then writes Dω f = g · Dω s + s · Dω g via `Dω_mul`, and bounds each summand using `ord_P_Dω_nonneg` to get min order ≥ 1; concludes via `ord_P_add_le`.
- **Hypotheses**: IsElliptic, f ≠ 0, ord_P f ≥ 2.
- **Uses from project**: `Dω_mul`, `ord_P_Dω_nonneg`, `SmoothPlaneCurve.exists_uniformizer`, `SmoothPlaneCurve.ord_P_mul`, `SmoothPlaneCurve.ord_P_add_le`
- **Used by**: `two_le_ord_P_of_Dω_vanishes_of_uniformizer`, `ord_P_isog_pullback_x_sub_const_le_one`, `ord_P_isog_pullback_y_sub_const_le_one`, `ord_P_mulByInt_y_sub_const_le_one`
- **Visibility**: public
- **Lines**: 332–377, proof 46 lines
- **Notes**: **Proof is 46 lines**.

---

### `theorem two_le_ord_P_of_Dω_vanishes_of_uniformizer`
- **Type**: `{φ s : KE} → (hφ_ne : φ ≠ 0) → (P : SmoothPoint) → (1 : WithTop ℤ) ≤ ord_P P φ → (1 : WithTop ℤ) ≤ ord_P P (Dω W φ) → ord_P P s = 1 → ord_P P (Dω W s) = 0 → (2 : WithTop ℤ) ≤ ord_P P φ`
- **What**: If φ vanishes at P, Dω φ also vanishes at P, and there exists a uniformizer s with Dω s a unit at P, then φ vanishes to order ≥ 2. (The "doubling / tangent" second-order criterion.)
- **How**: Contradiction: assume ord_P φ = 1 exactly. Set w = φ · s⁻¹ (a unit). Writes Dω φ = w · Dω s + s · Dω w via Dω_mul. The first term has order 0 (both w and Dω s units), the second has order ≥ 1 (s vanishes). Uses `ord_P_add_eq_of_lt` to conclude ord_P(Dω φ) = 0, contradicting hDφ ≥ 1.
- **Hypotheses**: IsElliptic, φ ≠ 0, geometric conditions on orders.
- **Uses from project**: `Dω_mul`, `ord_P_Dω_nonneg`, `SmoothPlaneCurve.ord_P_mul`, `SmoothPlaneCurve.ord_P_inv`, `SmoothPlaneCurve.ord_P_add_eq_of_lt`
- **Used by**: unused in file (called by `OneSubAffineResidues.lean`, `PencilComapWitnesses.lean`)
- **Visibility**: public
- **Lines**: 397–439, proof 43 lines
- **Notes**: **Proof is 43 lines**.

---

### `theorem Dω_isog_pullback_x_gen`
- **Type**: `(α : Isogeny W.toAffine W.toAffine) : Dω W (α.pullback (x_gen W)) = alpha_star_u W α * omegaPullbackCoeff W α`
- **What**: The ω-derivative of the pullback of x_gen by an isogeny α equals the pulled-back differential denominator times the ω-pullback coefficient (chain rule for x_gen).
- **How**: Applies `Dω_eq_of_smul` to `kaehlerD_alpha_pullback_x_eq_smul_omega`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Dω_eq_of_smul`, `WeilPairing.TorsionGeometric.kaehlerD_alpha_pullback_x_eq_smul_omega`, `x_gen`, `alpha_star_u`, `omegaPullbackCoeff`
- **Used by**: `ord_P_isog_pullback_x_sub_const_le_one`
- **Visibility**: public
- **Lines**: 454–457, proof 3 lines

---

### `theorem ord_P_isog_pullback_x_sub_const_le_one`
- **Type**: `(α : Isogeny) → omegaPullbackCoeff W α ∈ range(algebraMap F KE) → omegaPullbackCoeff W α ≠ 0 → (P : SmoothPoint) → (x_Q : F) → α.pullback(x_gen) - algebraMap x_Q ≠ 0 → ord_P P (alpha_star_u W α) = 0 → ord_P P (α.pullback(x_gen) - algebraMap x_Q) ≤ 1`
- **What**: For a separable isogeny α (a_α ≠ 0) with the pulled-back denominator α*u a unit at P (i.e., α(P) is non-2-torsion), the x-coordinate difference α*x_gen − x_Q has order ≤ 1 at P (general characteristic-free e ≤ 1 bound).
- **How**: Computes Dω(α*x − x_Q) = α*u · a_α via `Dω_isog_pullback_x_gen` + `Dω_sub` + `Dω_algebraMap`. Shows this is a unit at P (both factors units — a_α is a nonzero F-constant, α*u unit by hypothesis). Contradiction: if order ≥ 2, then `one_le_ord_P_Dω_of_two_le` gives Dω order ≥ 1, but it's 0.
- **Hypotheses**: IsElliptic, α separable (a_α in range(alg F KE) and ≠ 0), α*u unit at P.
- **Uses from project**: `Dω_isog_pullback_x_gen`, `Dω_sub`, `Dω_algebraMap`, `one_le_ord_P_Dω_of_two_le`, `SmoothPlaneCurve.ord_P_mul`, `SmoothPlaneCurve.ord_P_algebraMap_F_of_ne_zero`, `alpha_star_u`, `omegaPullbackCoeff`
- **Used by**: unused in file (exported to `SamePlace.lean`)
- **Visibility**: public (`set_option linter.unusedDecidableInType false`)
- **Lines**: 468–498, proof 31 lines
- **Notes**: **Proof is 31 lines**. The `set_option linter.unusedDecidableInType false` is present (no justifying comment).

---

### `theorem Dω_isog_pullback_y_gen`
- **Type**: `(α : Isogeny W.toAffine W.toAffine) : Dω W (α.pullback (y_gen W)) = (3 * α.pullback(x_gen)^2 + 2*a₂*α.pullback(x_gen) + a₄ - a₁*α.pullback(y_gen)) * omegaPullbackCoeff W α`
- **What**: The ω-derivative of the pullback of y_gen equals the pulled-back y-numerator (Weierstrass x-partial at α(P)) times the ω-pullback coefficient (chain rule for y_gen).
- **How**: Applies `Dω_eq_of_smul` to `kaehlerD_alpha_pullback_y_eq_smul_omega`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `Dω_eq_of_smul`, `WeilPairing.TorsionGeometric.kaehlerD_alpha_pullback_y_eq_smul_omega`, `x_gen`, `y_gen`, `omegaPullbackCoeff`
- **Used by**: `ord_P_isog_pullback_y_sub_const_le_one`
- **Visibility**: public
- **Lines**: 513–519, proof 3 lines

---

### `theorem ord_P_isog_pullback_y_sub_const_le_one`
- **Type**: `(α : Isogeny) → omegaPullbackCoeff ∈ range → omegaPullbackCoeff ≠ 0 → (P : SmoothPoint) → (y_Q : F) → α.pullback(y_gen) - algebraMap y_Q ≠ 0 → ord_P P (pulled-back y-numerator) = 0 → ord_P P (α.pullback(y_gen) - algebraMap y_Q) ≤ 1`
- **What**: For a separable isogeny α with the pulled-back y-numerator a unit at P (i.e., α(P) is 2-torsion with non-vanishing x-partial), the y-coordinate difference has order ≤ 1 at P (y-coordinate analogue of the x bound, for 2-torsion image case).
- **How**: Same structure as `ord_P_isog_pullback_x_sub_const_le_one`: compute Dω = unit via `Dω_isog_pullback_y_gen`, then contradiction via `one_le_ord_P_Dω_of_two_le`.
- **Hypotheses**: IsElliptic, α separable, pulled-back y-numerator a unit at P.
- **Uses from project**: `Dω_isog_pullback_y_gen`, `Dω_sub`, `Dω_algebraMap`, `one_le_ord_P_Dω_of_two_le`, `SmoothPlaneCurve.ord_P_mul`, `SmoothPlaneCurve.ord_P_algebraMap_F_of_ne_zero`, `omegaPullbackCoeff`
- **Used by**: unused in file (exported to `SamePlace.lean`)
- **Visibility**: public (`set_option linter.unusedDecidableInType false`)
- **Lines**: 529–563, proof 35 lines
- **Notes**: **Proof is 35 lines**. `set_option linter.unusedDecidableInType false` (no justifying comment).

---

### `theorem Dω_mulByInt_pullback_y_gen`
- **Type**: `(ℓ : ℤ) → (hℓ : ℓ ≠ 0) : Dω W ([ℓ].pullback(y_gen)) = (3*(mulByInt_x ℓ)^2 + 2*a₂*(mulByInt_x ℓ) + a₄ - a₁*(mulByInt_y ℓ)) * algebraMap F KE ℓ`
- **What**: Specialises the general y-chain rule to [ℓ]: Dω([ℓ]^*y_gen) = ([ℓ]^*polynomialX) · ℓ, using that the ω-pullback coefficient of [ℓ] is ℓ.
- **How**: Gets the general y-chain rule from `kaehlerD_alpha_pullback_y_eq_smul_omega`, rewrites `omegaPullbackCoeff W [ℓ]` to `algebraMap F KE ℓ` via `omegaCoeff_mulByInt`, then applies `Dω_eq_of_smul`.
- **Hypotheses**: IsElliptic, ℓ ≠ 0.
- **Uses from project**: `Dω_eq_of_smul`, `WeilPairing.TorsionGeometric.kaehlerD_alpha_pullback_y_eq_smul_omega`, `WeilPairing.TorsionGeometric.omegaCoeff_mulByInt`, `mulByInt`
- **Used by**: `ord_P_mulByInt_y_sub_const_le_one`
- **Visibility**: public
- **Lines**: 574–584, proof 5 lines

---

### `theorem ord_P_mulByInt_y_sub_const_le_one`
- **Type**: `(ℓ : ℤ) → (hℓ : ℓ ≠ 0) → (hℓF : (ℓ : F) ≠ 0) → (P : SmoothPoint) → (y_Q : F) → (hf_ne : mulByInt_y ℓ - algebraMap y_Q ≠ 0) → ord_P P ([ℓ]^*polynomialX) = 0 → ord_P P (mulByInt_y ℓ - algebraMap y_Q) ≤ 1`
- **What**: For [ℓ] separable (char does not divide ℓ) with [ℓ]^*polynomialX a unit at P (the 2-torsion image case), the function mulByInt_y ℓ − y_Q has order ≤ 1 at P. The characteristic-free séparabilité input for the y-uniformizer at a 2-torsion image.
- **How**: Computes Dω = unit via `Dω_mulByInt_pullback_y_gen` + `mulByInt_pullback_x/y`; shows unit by `ord_P_mul` + `ord_P_algebraMap_F_of_ne_zero`; concludes by `one_le_ord_P_Dω_of_two_le` contradiction.
- **Hypotheses**: IsElliptic, ℓ ≠ 0, ℓ ≠ 0 in F, pulled-back y-numerator unit at P.
- **Uses from project**: `Dω_sub`, `Dω_algebraMap`, `Dω_mulByInt_pullback_y_gen`, `mulByInt_pullback_x`, `mulByInt_pullback_y`, `one_le_ord_P_Dω_of_two_le`, `SmoothPlaneCurve.ord_P_mul`, `SmoothPlaneCurve.ord_P_algebraMap_F_of_ne_zero`, `mulByInt_x`, `mulByInt_y`
- **Used by**: unused in file (exported to `MulByIntUnramified.lean`)
- **Visibility**: public
- **Lines**: 597–632, proof 36 lines
- **Notes**: **Proof is 36 lines**.

---

## Cross-reference summary

### Key API (used by 3+ declarations in this file)

- **`Dω_eq_of_smul`**: used by `Dω_add`, `Dω_algebraMap`, `Dω_mul`, `Dω_smul`, `Dω_sub`, `Dω_pow`, `Dω_inv`, `Dω_x_gen`, `Dω_y_gen`, `Dω_isog_pullback_x_gen`, `Dω_isog_pullback_y_gen`, `Dω_mulByInt_pullback_y_gen` (12 uses)
- **`Dω_spec`**: used by `Dω_add`, `Dω_algebraMap`, `Dω_mul`, `Dω_smul`, `Dω_sub`, `Dω_pow`, `Dω_inv` (7 uses)
- **`Dω_mul`** (`@[simp]`): used by `Dω_aeval_x_gen_mem_Rimg`, `Dω_algebraMap_mem_Rimg`, `ord_P_Dω_nonneg`, `one_le_ord_P_Dω_of_two_le`, `two_le_ord_P_of_Dω_vanishes_of_uniformizer` (5 uses)
- **`Dω_algebraMap`** (`@[simp]`): used by `Dω_zero`, `Dω_aeval_x_gen_mem_Rimg`, `ord_P_isog_pullback_x_sub_const_le_one`, `ord_P_isog_pullback_y_sub_const_le_one`, `ord_P_mulByInt_y_sub_const_le_one` (5 uses)
- **`one_le_ord_P_Dω_of_two_le`**: used by `two_le_ord_P_of_Dω_vanishes_of_uniformizer` (indirectly via contradiction pattern), `ord_P_isog_pullback_x_sub_const_le_one`, `ord_P_isog_pullback_y_sub_const_le_one`, `ord_P_mulByInt_y_sub_const_le_one` (4 uses)
- **`ord_P_Dω_nonneg`**: used by `one_le_ord_P_Dω_of_two_le`, `two_le_ord_P_of_Dω_vanishes_of_uniformizer` (2 uses — borderline)
- **`algebraMap_F_mem_Rimg`**: used by `Dω_x_gen_mem_Rimg`, `Dω_y_gen_mem_Rimg`, `aeval_x_gen_mem_Rimg`, `Dω_aeval_x_gen_mem_Rimg` (4 uses)
- **`x_gen_mem_Rimg`**: used by `Dω_x_gen_mem_Rimg`, `Dω_y_gen_mem_Rimg`, `aeval_x_gen_mem_Rimg`, `Dω_aeval_x_gen_mem_Rimg`, `Dω_algebraMap_mem_Rimg` (5 uses)
- **`ord_P_nonneg_of_mem_Rimg`**: used by `ord_P_Dω_nonneg` (in two places)
- **`Dω_algebraMap_mem_Rimg`**: used by `ord_P_Dω_nonneg` (in two places — for a and b)

### Unused in file (dead-code candidates — may be used by other files)

- `Dω_smul` — exported; no internal caller
- `Dω_neg` — exported; no internal caller  
- `Dω_inv` — exported; no internal caller  
- `two_le_ord_P_of_Dω_vanishes_of_uniformizer` — used by `OneSubAffineResidues.lean`, `PencilComapWitnesses.lean`
- `ord_P_isog_pullback_x_sub_const_le_one` — used by `SamePlace.lean`
- `ord_P_isog_pullback_y_sub_const_le_one` — used by `SamePlace.lean`
- `ord_P_mulByInt_y_sub_const_le_one` — used by `MulByIntUnramified.lean`

---

## Notes

No `sorry`, no `set_option maxHeartbeats` overrides. Two `set_option linter.unusedDecidableInType false` are present (one before `ord_P_isog_pullback_x_sub_const_le_one`, one before `ord_P_isog_pullback_y_sub_const_le_one`) without justifying comments.
