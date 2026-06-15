# Inventory: ./HasseWeil/Curves/IntegralClosure.lean

**File summary**: Ring-theoretic infrastructure for `IsDedekindDomain C.CoordinateRing` under a smoothness hypothesis. Develops the coordinate ring of a smooth Weierstrass curve as integral over `F[X]`, proves `DimensionLEOne`, separability of `F(C)/F(X)` in char ≠ 2, and — via a squarefree discriminant argument — establishes `IsIntegrallyClosed` (hence `IsDedekindDomain`) under `IsElliptic + char ≠ 2,3`.

---

## Outside `HasseWeil.Curves` namespace (top-level helpers)

---

### `theorem Polynomial.fractionRing_mem_range_of_sq_mul_squarefree`

- **Type**: `{R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K] {q : K} {D r : R} → Squarefree D → q^2 * algebraMap R K D = algebraMap R K r → ∃ q' : R, algebraMap R K q' = q`
- **What**: If `q ∈ FractionRing R` satisfies `q² · D = r` (images in the fraction field) for squarefree `D ∈ R` and `r ∈ R`, then `q` is in the image of `algebraMap R K`.
- **How**: Write `q = s/t` in lowest terms via `IsFractionRing.exists_reduced_fraction`. Then `s² · D = t² · r` in R. Since `D` is squarefree and `t ⊥ s` (`IsRelPrime`), `t²` divides 1, so `t` is a unit and `q = s · t⁻¹ ∈ image`.
- **Hypotheses**: R a UFD and integral domain, K a fraction field of R, D squarefree.
- **Uses from project**: none
- **Used by**: `isIntegrallyClosed_coordinateRing_of_IsElliptic` (line 956)
- **Visibility**: public
- **Lines**: 56–100, proof ~44 lines
- **Notes**: Proof > 30 lines. General UFD lemma, likely has a mathlib analogue; suspected mathlib duplication candidate.

---

### `theorem Polynomial.separable_of_monic_irreducible_natDegree_le_two`

- **Type**: `{K : Type*} [Field K] [NeZero (2 : K)] {p : Polynomial K} → p.Monic → Irreducible p → p.natDegree ≤ 2 → p.Separable`
- **What**: In characteristic ≠ 2, every monic irreducible polynomial of degree ≤ 2 over a field is separable.
- **How**: By `Polynomial.separable_iff_derivative_ne_zero hirr`, it suffices to show `p.derivative ≠ 0`. The leading coefficient of `p.derivative` is `natDegree` (as an element of K); for degree 1 this is 1 ≠ 0, for degree 2 this is 2 ≠ 0 (by `NeZero (2 : K)`). Case split via `interval_cases p.natDegree`.
- **Hypotheses**: Field of char ≠ 2, monic irreducible polynomial of degree ≤ 2.
- **Uses from project**: none
- **Used by**: `algebra_isSeparable_functionField` (line 238)
- **Visibility**: public
- **Lines**: 108–124, proof ~16 lines
- **Notes**: None.

---

## Namespace `HasseWeil.Curves.SmoothPlaneCurve`

---

### `instance dimensionLEOne_coordinateRing`

- **Type**: `Ring.DimensionLEOne C.CoordinateRing`
- **What**: The coordinate ring `F[C]` has Krull dimension ≤ 1: every nonzero prime ideal is maximal.
- **How**: Uses `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap`: the contraction of any nonzero prime `𝔭` of `F[C]` along `F[X] → F[C]` is a nonzero prime of the PID `F[X]` (nonzero by `Ideal.comap_ne_bot_of_integral_mem` + `Algebra.IsIntegral.isIntegral`), hence maximal; maximality lifts to `𝔭`.
- **Hypotheses**: C a smooth plane curve over a field F.
- **Uses from project**: uses `Algebra.IsIntegral.isIntegral` (via FiniteOverKx import)
- **Used by**: `isDedekindRing_coordinateRing` (indirectly via `IsDedekindRing`); unused directly in file
- **Visibility**: public
- **Lines**: 141–156, proof ~15 lines
- **Notes**: None.

---

### `noncomputable def coordYInFunctionField`

- **Type**: `C.FunctionField`
- **What**: The image of the coordinate `Y` (i.e., `AdjoinRoot.root`) in the function field `F(C) = FractionRing(CoordinateRing)`.
- **How**: `algebraMap C.CoordinateRing C.FunctionField (AdjoinRoot.root C.toAffine.polynomial)`.
- **Hypotheses**: None beyond `C : SmoothPlaneCurve F`.
- **Uses from project**: none
- **Used by**: `aeval_coordYInFunctionField_polynomial`, `isIntegral_coordYInFunctionField`, `isIntegral_coordYInFunctionField_fracPoly`, `algebra_isSeparable_functionField`, `functionFieldBasis_one`, `exists_decomp`, `coordYInFunctionField_sq`, `decomp_from_quadratic`, `decomp_zero_iff`, `isIntegrallyClosed_coordinateRing_of_IsElliptic`
- **Visibility**: public
- **Lines**: 168–170, def (1 line body)
- **Notes**: Key api: used by 10+ declarations.

---

### `theorem aeval_coordYInFunctionField_polynomial`

- **Type**: `(Polynomial.aeval (R := Polynomial F) C.coordYInFunctionField) C.toAffine.polynomial = 0`
- **What**: The element `coordYInFunctionField` is a root of the Weierstrass polynomial in `F[X][T]`.
- **How**: Uses `AdjoinRoot.aeval_eq` and `AdjoinRoot.mk_self` in the coordinate ring, then applies `algebraMap` and `map_zero`.
- **Hypotheses**: None.
- **Uses from project**: `coordYInFunctionField`
- **Used by**: `isIntegral_coordYInFunctionField` (line 190)
- **Visibility**: public
- **Lines**: 174–183, proof ~9 lines
- **Notes**: None.

---

### `theorem isIntegral_coordYInFunctionField`

- **Type**: `IsIntegral (Polynomial F) C.coordYInFunctionField`
- **What**: The Y-image in `F(C)` is integral over `F[X]`, witnessed by the monic Weierstrass polynomial.
- **How**: Explicit witness: `⟨C.toAffine.polynomial, WeierstrassCurve.Affine.monic_polynomial, C.aeval_coordYInFunctionField_polynomial⟩`.
- **Hypotheses**: None.
- **Uses from project**: `coordYInFunctionField`, `aeval_coordYInFunctionField_polynomial`
- **Used by**: `isIntegral_coordYInFunctionField_fracPoly` (line 196); transitively used by `algebra_isSeparable_functionField`
- **Visibility**: public
- **Lines**: 187–190, proof 1 line
- **Notes**: None.

---

### `theorem isIntegral_coordYInFunctionField_fracPoly`

- **Type**: `IsIntegral (FractionRing (Polynomial F)) C.coordYInFunctionField`
- **What**: Y is also integral over `F(X)` (the fraction field of `F[X]`).
- **How**: One-liner: `Algebra.IsIntegral.isIntegral _` (from the finite extension).
- **Hypotheses**: None.
- **Uses from project**: `coordYInFunctionField`, `isIntegral_coordYInFunctionField`
- **Used by**: unused in file (may be used by other files)
- **Visibility**: public
- **Lines**: 194–196, proof 1 line
- **Notes**: Unused in this file.

---

### `instance algebra_isSeparable_functionField`

- **Type**: `[NeZero (2 : F)] → Algebra.IsSeparable (FractionRing (Polynomial F)) C.FunctionField`
- **What**: In characteristic ≠ 2, the function field `F(C)` is separable over `F(X)`.
- **How**: For each `α ∈ F(C)`, uses `minpoly.natDegree_le` + `C.finrank_functionField_over_fracPolynomialX` (= 2) to bound the minpoly degree by 2, then applies `Polynomial.separable_of_monic_irreducible_natDegree_le_two`. The `NeZero (2 : FractionRing (Polynomial F))` is derived from `NeZero (2 : F)` via injectivity of `algebraMap`.
- **Hypotheses**: `NeZero (2 : F)` (char ≠ 2).
- **Uses from project**: `finrank_functionField_over_fracPolynomialX` (from FiniteOverKx), `Polynomial.separable_of_monic_irreducible_natDegree_le_two`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 210–239, proof ~29 lines
- **Notes**: None.

---

### `instance isIntegralClosure_coordinateRing_fracPolynomialX`

- **Type**: `[IsIntegrallyClosed C.CoordinateRing] → IsIntegralClosure C.CoordinateRing (Polynomial F) C.FunctionField`
- **What**: Under integral closedness, `F[C]` is the integral closure of `F[X]` in `F(C)`.
- **How**: Directly applies `IsIntegralClosure.of_isIntegrallyClosed`.
- **Hypotheses**: `IsIntegrallyClosed C.CoordinateRing`.
- **Uses from project**: none
- **Used by**: `mem_coordinateRing_of_isIntegral_polynomialX`, `mem_coordinateRing_of_valuation_le_one`, `isDedekindRing_coordinateRing` (all via typeclass inference)
- **Visibility**: public
- **Lines**: 260–263, proof 1 line
- **Notes**: None.

---

### `instance isDedekindRing_coordinateRing`

- **Type**: `[IsIntegrallyClosed C.CoordinateRing] → IsDedekindRing C.CoordinateRing`
- **What**: Under integral closedness, `F[C]` is a Dedekind ring (Noetherian + DimensionLEOne + integrally closed).
- **How**: Rewrites via `isDedekindRing_iff` and supplies `inferInstance` for Noetherian and DimensionLEOne; uses `IsIntegrallyClosed.isIntegral_iff.mp`.
- **Hypotheses**: `IsIntegrallyClosed C.CoordinateRing`.
- **Uses from project**: `dimensionLEOne_coordinateRing` (via `inferInstance`)
- **Used by**: `isDedekindDomain_coordinateRing`
- **Visibility**: public
- **Lines**: 273–278, proof ~5 lines
- **Notes**: None.

---

### `instance isDedekindDomain_coordinateRing`

- **Type**: `[IsIntegrallyClosed C.CoordinateRing] → IsDedekindDomain C.CoordinateRing`
- **What**: Under integral closedness, `F[C]` is a Dedekind domain.
- **How**: Trivially from `IsDedekindRing` + `IsDomain`: `⟨⟩`.
- **Hypotheses**: `IsIntegrallyClosed C.CoordinateRing`.
- **Uses from project**: `isDedekindRing_coordinateRing` (via `IsDedekindRing`)
- **Used by**: `mem_coordinateRing_of_valuation_le_one`, `SmoothPoint.toHeightOneSpectrum`
- **Visibility**: public
- **Lines**: 282–284, proof 1 line
- **Notes**: None.

---

### `theorem mem_coordinateRing_of_isIntegral_polynomialX`

- **Type**: `[IsIntegrallyClosed C.CoordinateRing] → {f : C.FunctionField} → IsIntegral (Polynomial F) f → ∃ u : C.CoordinateRing, algebraMap C.CoordinateRing C.FunctionField u = f`
- **What**: Elements of `F(C)` integral over `F[X]` lie in `F[C]`.
- **How**: Direct application of `IsIntegralClosure.isIntegral_iff.mp`.
- **Hypotheses**: `IsIntegrallyClosed C.CoordinateRing`.
- **Uses from project**: `isIntegralClosure_coordinateRing_fracPolynomialX` (via typeclass)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 291–295, proof 1 line
- **Notes**: Unused in this file.

---

### `theorem mem_coordinateRing_of_valuation_le_one`

- **Type**: `[IsIntegrallyClosed C.CoordinateRing] → (f : C.FunctionField) → (∀ v : IsDedekindDomain.HeightOneSpectrum C.CoordinateRing, v.valuation C.FunctionField f ≤ 1) → ∃ u : C.CoordinateRing, algebraMap C.CoordinateRing C.FunctionField u = f`
- **What**: If `f ∈ F(C)` has no poles at any height-one prime, then `f ∈ F[C]` (Dedekind Liouville step).
- **How**: Direct application of `IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one`.
- **Hypotheses**: `IsIntegrallyClosed C.CoordinateRing`.
- **Uses from project**: `isDedekindDomain_coordinateRing` (via typeclass)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 302–308, proof 1 line
- **Notes**: Unused in this file.

---

### `theorem maximalIdealAt_ne_bot`

- **Type**: `(P : C.SmoothPoint) → C.maximalIdealAt P ≠ ⊥`
- **What**: The maximal ideal at a smooth point P is nonzero (it contains the nonzero element `XClass P.x`).
- **How**: Uses `Ideal.subset_span` to show `XClass P.x ∈ maximalIdealAt P` (via `XYIdeal` definition), then `WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero` for a contradiction.
- **Hypotheses**: P is a smooth point of C.
- **Uses from project**: uses `maximalIdealAt` and `maximalIdealAt_isMaximal` (from elsewhere in project), `XClass_ne_zero` (mathlib/project)
- **Used by**: `SmoothPoint.toHeightOneSpectrum` (line 330)
- **Visibility**: public
- **Lines**: 312–320, proof ~8 lines
- **Notes**: None.

---

### `noncomputable def SmoothPoint.toHeightOneSpectrum`

- **Type**: `[IsIntegrallyClosed C.CoordinateRing] → (P : C.SmoothPoint) → IsDedekindDomain.HeightOneSpectrum C.CoordinateRing`
- **What**: Associates to each smooth point a height-one spectrum element of the Dedekind domain `F[C]`.
- **How**: Packages `maximalIdealAt P` with its primeness (from `maximalIdealAt_isMaximal`) and nonzero-ness (from `maximalIdealAt_ne_bot`).
- **Hypotheses**: `IsIntegrallyClosed C.CoordinateRing`.
- **Uses from project**: `maximalIdealAt_ne_bot`, `maximalIdealAt_isMaximal` (from elsewhere in project)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 325–330, def ~5 lines
- **Notes**: Unused in this file.

---

### `noncomputable def functionFieldBasis`

- **Type**: `Module.Basis (Fin 2) (FractionRing (Polynomial F)) C.FunctionField`
- **What**: An explicit `F(X)`-basis `{1, Y}` of the function field `F(C)`, obtained by localizing the `F[X]`-basis of `F[C]`.
- **How**: Applies `Basis.localizationLocalization` to `WeierstrassCurve.Affine.CoordinateRing.basis`.
- **Hypotheses**: None.
- **Uses from project**: none (uses mathlib's `WeierstrassCurve.Affine.CoordinateRing.basis`)
- **Used by**: `functionFieldBasis_zero`, `functionFieldBasis_one`, `exists_decomp`, `decomp_zero_iff`
- **Visibility**: public
- **Lines**: 336–340, def ~4 lines
- **Notes**: Key API: used by 4+ declarations.

---

### `@[simp] theorem functionFieldBasis_zero`

- **Type**: `C.functionFieldBasis 0 = 1`
- **What**: The zeroth basis element is 1.
- **How**: Unfolds `localizationLocalization_apply` and applies `WeierstrassCurve.Affine.CoordinateRing.basis_zero` + `map_one`.
- **Hypotheses**: None.
- **Uses from project**: `functionFieldBasis`
- **Used by**: `exists_decomp` (line 366), `decomp_zero_iff` (line 735)
- **Visibility**: public
- **Lines**: 342–349, proof ~7 lines
- **Notes**: None.

---

### `@[simp] theorem functionFieldBasis_one`

- **Type**: `C.functionFieldBasis 1 = C.coordYInFunctionField`
- **What**: The first basis element is `coordYInFunctionField`.
- **How**: Unfolds `localizationLocalization_apply` and applies `WeierstrassCurve.Affine.CoordinateRing.basis_one`.
- **Hypotheses**: None.
- **Uses from project**: `functionFieldBasis`, `coordYInFunctionField`
- **Used by**: `exists_decomp` (line 367), `decomp_zero_iff` (line 735)
- **Visibility**: public
- **Lines**: 351–358, proof ~7 lines
- **Notes**: None.

---

### `theorem exists_decomp`

- **Type**: `(x : C.FunctionField) → ∃ p q : FractionRing (Polynomial F), x = p • 1 + q • C.coordYInFunctionField`
- **What**: Every element of `F(C)` decomposes as `p + q · Y` with `p, q ∈ F(X)`.
- **How**: Uses `functionFieldBasis.repr` coefficients and `functionFieldBasis.sum_repr` + `functionFieldBasis_zero/one`.
- **Hypotheses**: None.
- **Uses from project**: `functionFieldBasis`, `functionFieldBasis_zero`, `functionFieldBasis_one`, `coordYInFunctionField`
- **Used by**: `isIntegrallyClosed_coordinateRing_of_IsElliptic` (line 848)
- **Visibility**: public
- **Lines**: 361–368, proof ~7 lines
- **Notes**: None.

---

### `theorem algebra_norm_fracPolyX_algebraMap`

- **Type**: `(u : C.CoordinateRing) → (Algebra.norm (FractionRing (Polynomial F))) (algebraMap C.CoordinateRing C.FunctionField u) = algebraMap (Polynomial F) (FractionRing (Polynomial F)) (Algebra.norm (Polynomial F) u)`
- **What**: The `F(X)`-norm of an element of `F[C]` (viewed in `F(C)`) equals the `F(X)`-image of the `F[X]`-norm.
- **How**: Applies `Algebra.norm_localization` using the free module structure from `WeierstrassCurve.Affine.CoordinateRing.basis`.
- **Hypotheses**: None.
- **Uses from project**: none (uses mathlib's `CoordinateRing.basis`)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 376–384, proof ~8 lines
- **Notes**: Unused in this file; infrastructure for future Task B use.

---

### `noncomputable def polynomialDiscriminant`

- **Type**: `(C : SmoothPlaneCurve F) → Polynomial F`
- **What**: The polynomial `4X³ + b₂X² + 2b₄X + b₆ ∈ F[X]`, the discriminant of the Weierstrass cubic viewed as a quadratic in Y (up to a factor of 16 this equals the Weierstrass discriminant `Δ`).
- **How**: Direct algebraic expression using `b₂, b₄, b₆`.
- **Hypotheses**: None.
- **Uses from project**: uses `WeierstrassCurve.b₂, b₄, b₆` (mathlib)
- **Used by**: `polynomialDiscriminant_natDegree`, `polynomialDiscriminant_ne_zero`, `polynomialDiscriminant_coeff_zero/one/two/three`, `polynomialDiscriminant_degree`, `polynomialDiscriminant_discr`, `polynomialDiscriminant_discr_ne_zero`, `polynomialDiscriminant_derivative_natDegree`, `polynomialDiscriminant_squarefree`, `polynomialDiscriminant_eq_trace_sq_sub_four_norm`, `isIntegrallyClosed_coordinateRing_of_IsElliptic`
- **Visibility**: public
- **Lines**: 399–403, def ~4 lines
- **Notes**: Key API: used by 10+ declarations.

---

### `theorem polynomialDiscriminant_natDegree`

- **Type**: `[NeZero (2 : F)] → C.polynomialDiscriminant.natDegree = 3`
- **What**: In char ≠ 2, the polynomial discriminant has degree 3 (leading coefficient 4 ≠ 0).
- **How**: Bounds degrees of lower-order terms via `Polynomial.natDegree_C_mul_le`, then uses `Polynomial.natDegree_add_eq_left_of_natDegree_lt`.
- **Hypotheses**: `NeZero (2 : F)`.
- **Uses from project**: `polynomialDiscriminant`
- **Used by**: `polynomialDiscriminant_ne_zero`, `polynomialDiscriminant_degree`, `polynomialDiscriminant_discr`, `polynomialDiscriminant_squarefree`, `polynomialDiscriminant_derivative_natDegree`, `isIntegrallyClosed_coordinateRing_of_IsElliptic`
- **Visibility**: public
- **Lines**: 407–448, proof ~41 lines
- **Notes**: Proof > 30 lines. Slightly verbose due to explicit degree-bounding.

---

### `theorem polynomialDiscriminant_ne_zero`

- **Type**: `[NeZero (2 : F)] → C.polynomialDiscriminant ≠ 0`
- **What**: In char ≠ 2, the polynomial discriminant is nonzero.
- **How**: Contradiction: if zero, its natDegree would be 0, contradicting `polynomialDiscriminant_natDegree = 3`.
- **Hypotheses**: `NeZero (2 : F)`.
- **Uses from project**: `polynomialDiscriminant`, `polynomialDiscriminant_natDegree`
- **Used by**: `polynomialDiscriminant_degree`, `polynomialDiscriminant_squarefree`
- **Visibility**: public
- **Lines**: 451–456, proof ~5 lines
- **Notes**: None.

---

### `theorem polynomialDiscriminant_coeff_zero`

- **Type**: `C.polynomialDiscriminant.coeff 0 = C.toAffine.b₆`
- **What**: The constant coefficient of `polynomialDiscriminant` is `b₆`.
- **How**: `simp` after `unfold`.
- **Hypotheses**: None.
- **Uses from project**: `polynomialDiscriminant`
- **Used by**: `polynomialDiscriminant_discr` (line 490)
- **Visibility**: public
- **Lines**: 461–463, proof 1 line
- **Notes**: None.

---

### `theorem polynomialDiscriminant_coeff_one`

- **Type**: `C.polynomialDiscriminant.coeff 1 = 2 * C.toAffine.b₄`
- **What**: The degree-1 coefficient is `2b₄`.
- **How**: `simp` after `unfold`.
- **Hypotheses**: None.
- **Uses from project**: `polynomialDiscriminant`
- **Used by**: `polynomialDiscriminant_discr` (line 490)
- **Visibility**: public
- **Lines**: 465–467, proof 1 line
- **Notes**: None.

---

### `theorem polynomialDiscriminant_coeff_two`

- **Type**: `C.polynomialDiscriminant.coeff 2 = C.toAffine.b₂`
- **What**: The degree-2 coefficient is `b₂`.
- **How**: `simp` after `unfold`.
- **Hypotheses**: None.
- **Uses from project**: `polynomialDiscriminant`
- **Used by**: `polynomialDiscriminant_discr` (line 490)
- **Visibility**: public
- **Lines**: 469–471, proof 1 line
- **Notes**: None.

---

### `theorem polynomialDiscriminant_coeff_three`

- **Type**: `C.polynomialDiscriminant.coeff 3 = 4`
- **What**: The leading coefficient is 4.
- **How**: `simp` after `unfold`.
- **Hypotheses**: None.
- **Uses from project**: `polynomialDiscriminant`
- **Used by**: `polynomialDiscriminant_discr` (line 491), `polynomialDiscriminant_squarefree` (line 554), `polynomialDiscriminant_derivative_natDegree` (line 526)
- **Visibility**: public
- **Lines**: 473–475, proof 1 line
- **Notes**: None.

---

### `theorem polynomialDiscriminant_degree`

- **Type**: `[NeZero (2 : F)] → C.polynomialDiscriminant.degree = 3`
- **What**: The degree (as `WithBot ℕ`) of the polynomial discriminant is 3.
- **How**: From `natDegree = 3` via `Polynomial.degree_eq_natDegree`.
- **Hypotheses**: `NeZero (2 : F)`.
- **Uses from project**: `polynomialDiscriminant`, `polynomialDiscriminant_ne_zero`, `polynomialDiscriminant_natDegree`
- **Used by**: `polynomialDiscriminant_discr`, `polynomialDiscriminant_squarefree`
- **Visibility**: public
- **Lines**: 478–482, proof ~4 lines
- **Notes**: None.

---

### `theorem polynomialDiscriminant_discr`

- **Type**: `[NeZero (2 : F)] → C.polynomialDiscriminant.discr = 16 * C.toAffine.Δ`
- **What**: The standard polynomial discriminant of `polynomialDiscriminant` equals `16 · Δ` (the Weierstrass discriminant).
- **How**: Applies `Polynomial.discr_of_degree_eq_three`, substitutes all coefficients via `polynomialDiscriminant_coeff_*`, and uses `C.toAffine.b_relation` for the `b₈` identity; closes with `linear_combination`.
- **Hypotheses**: `NeZero (2 : F)`.
- **Uses from project**: `polynomialDiscriminant`, `polynomialDiscriminant_degree`, `polynomialDiscriminant_coeff_zero`, `polynomialDiscriminant_coeff_one`, `polynomialDiscriminant_coeff_two`, `polynomialDiscriminant_coeff_three`
- **Used by**: `polynomialDiscriminant_discr_ne_zero`
- **Visibility**: public
- **Lines**: 487–495, proof ~8 lines
- **Notes**: None.

---

### `theorem polynomialDiscriminant_discr_ne_zero`

- **Type**: `[NeZero (2 : F)] → [C.toAffine.IsElliptic] → C.polynomialDiscriminant.discr ≠ 0`
- **What**: Under elliptic hypothesis (Δ ≠ 0) and char ≠ 2, the polynomial discriminant is nonzero.
- **How**: Uses `polynomialDiscriminant_discr` to reduce to `16 · Δ ≠ 0`; then `16 ≠ 0` (since `2 ≠ 0` and `16 = 2^4`) + `Δ ≠ 0` (from `IsElliptic` via `isUnit_Δ`).
- **Hypotheses**: `NeZero (2 : F)`, `C.toAffine.IsElliptic`.
- **Uses from project**: `polynomialDiscriminant`, `polynomialDiscriminant_discr`
- **Used by**: `polynomialDiscriminant_squarefree` (line 567)
- **Visibility**: public
- **Lines**: 498–512, proof ~14 lines
- **Notes**: None.

---

### `theorem polynomialDiscriminant_derivative_natDegree`

- **Type**: `[NeZero (2 : F)] → [NeZero (3 : F)] → C.polynomialDiscriminant.derivative.natDegree = 2`
- **What**: In char ≠ 2,3, the derivative of `polynomialDiscriminant` has degree exactly 2.
- **How**: Leading coefficient of derivative at degree 2 is 12 ≠ 0 (using `NeZero (2 : F)` and `NeZero (3 : F)`, since `12 = 2² · 3`); bounds come from `natDegree_derivative_le` and contradiction if degree < 2.
- **Hypotheses**: `NeZero (2 : F)`, `NeZero (3 : F)`.
- **Uses from project**: `polynomialDiscriminant`, `polynomialDiscriminant_coeff_three`, `polynomialDiscriminant_natDegree`
- **Used by**: `polynomialDiscriminant_squarefree` (line 576)
- **Visibility**: public
- **Lines**: 516–535, proof ~19 lines
- **Notes**: None.

---

### `theorem polynomialDiscriminant_squarefree`

- **Type**: `[NeZero (2 : F)] → [NeZero (3 : F)] → [C.toAffine.IsElliptic] → Squarefree C.polynomialDiscriminant`
- **What**: Under IsElliptic and char ≠ 2, 3, the polynomial discriminant is squarefree.
- **How**: Uses `Polynomial.Separable.squarefree`; to show separability: applies `Polynomial.resultant_deriv` + identifies leading coefficient 4 via `polynomialDiscriminant_coeff_three`, uses `polynomialDiscriminant_discr_ne_zero` to get `resultant D D' ≠ 0`, then applies `Polynomial.resultant_eq_zero_iff` (contrapositive) to derive `IsCoprime D D'` (= separability).
- **Hypotheses**: `NeZero (2 : F)`, `NeZero (3 : F)`, `C.toAffine.IsElliptic`.
- **Uses from project**: `polynomialDiscriminant`, `polynomialDiscriminant_ne_zero`, `polynomialDiscriminant_degree`, `polynomialDiscriminant_natDegree`, `polynomialDiscriminant_coeff_three`, `polynomialDiscriminant_discr_ne_zero`, `polynomialDiscriminant_derivative_natDegree`
- **Used by**: `isIntegrallyClosed_coordinateRing_of_IsElliptic` (line 955)
- **Visibility**: public
- **Lines**: 544–588, proof ~44 lines
- **Notes**: Proof > 30 lines. Key step in the "elliptic ⟹ integrally closed" argument.

---

### `theorem polynomialDiscriminant_eq_trace_sq_sub_four_norm`

- **Type**: Given `p q : FractionRing (Polynomial F)` and `α = 2p - q·b`, `γ = p² - p·q·b - q²·c` (Weierstrass trace/norm), proves `α² - 4γ = q² · algebraMap D` where D = `C.polynomialDiscriminant`.
- **What**: The algebraic identity connecting the trace/norm of the decomposition `p + q·Y` with the polynomial discriminant `D`.
- **How**: Pure algebraic calculation: `rw [hα, hγ]` + `unfold polynomialDiscriminant` + `simp` + `ring`.
- **Hypotheses**: None (abstract `α, γ` with given definitions).
- **Uses from project**: `polynomialDiscriminant`
- **Used by**: `isIntegrallyClosed_coordinateRing_of_IsElliptic` (line 936)
- **Visibility**: public
- **Lines**: 606–630, proof ~24 lines
- **Notes**: None.

---

### `theorem coordY_sq_coord`

- **Type**: `(AdjoinRoot.root C.toAffine.polynomial) ^ 2 + algebraMap (Polynomial F) C.CoordinateRing (C a₁·X + C a₃) * (AdjoinRoot.root ...) - algebraMap (Polynomial F) C.CoordinateRing (X³ + ...) = 0`
- **What**: The Weierstrass Y² relation in the coordinate ring: Y satisfies the Weierstrass equation.
- **How**: Uses `AdjoinRoot.mk_self` to get the polynomial-level identity, distributes `mk` using `map_sub, map_add, map_mul, map_pow`, then closes with `linear_combination`.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: `coordYInFunctionField_sq` (line 675)
- **Visibility**: public
- **Lines**: 636–664, proof ~28 lines
- **Notes**: None.

---

### `theorem coordYInFunctionField_sq`

- **Type**: `C.coordYInFunctionField ^ 2 = -algebraMap ... (a₁X+a₃) * C.coordYInFunctionField + algebraMap ... (X³ + a₂X² + a₄X + a₆)`
- **What**: The Y² relation lifted to the function field `F(C)`.
- **How**: Applies `algebraMap C.CoordinateRing C.FunctionField` to `coordY_sq_coord`, distributes via `map_sub/add/mul/pow`, uses scalar tower compatibility.
- **Hypotheses**: None.
- **Uses from project**: `coordY_sq_coord`, `coordYInFunctionField`
- **Used by**: `decomp_from_quadratic` (lines 754, 785)
- **Visibility**: public
- **Lines**: 667–688, proof ~21 lines
- **Notes**: None.

---

### `noncomputable def bFracPoly`

- **Type**: `FractionRing (Polynomial F)`
- **What**: The Weierstrass linear term `b = a₁X + a₃` viewed as an element of `F(X)`.
- **How**: `algebraMap (Polynomial F) (FractionRing (Polynomial F)) (C a₁ * X + C a₃)`.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: `algebraMap_bFracPoly`, `decomp_from_quadratic`, `isIntegrallyClosed_coordinateRing_of_IsElliptic`
- **Visibility**: public
- **Lines**: 694–696, def 2 lines
- **Notes**: None.

---

### `noncomputable def cFracPoly`

- **Type**: `FractionRing (Polynomial F)`
- **What**: The Weierstrass cubic term `c = X³ + a₂X² + a₄X + a₆` viewed as an element of `F(X)`.
- **How**: `algebraMap (Polynomial F) (FractionRing (Polynomial F)) (X³ + ...)`.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: `algebraMap_cFracPoly`, `decomp_from_quadratic`, `isIntegrallyClosed_coordinateRing_of_IsElliptic`
- **Visibility**: public
- **Lines**: 699–703, def 3 lines
- **Notes**: None.

---

### `theorem algebraMap_bFracPoly`

- **Type**: `algebraMap (FractionRing (Polynomial F)) C.FunctionField C.bFracPoly = algebraMap (Polynomial F) C.FunctionField (C a₁ * X + C a₃)`
- **What**: The image of `bFracPoly` in `F(C)` equals the direct image of the polynomial `a₁X+a₃`.
- **How**: `unfold bFracPoly` + `← IsScalarTower.algebraMap_apply`.
- **Hypotheses**: None.
- **Uses from project**: `bFracPoly`
- **Used by**: `decomp_from_quadratic` (lines 765, 785)
- **Visibility**: public
- **Lines**: 706–711, proof ~5 lines
- **Notes**: None.

---

### `theorem algebraMap_cFracPoly`

- **Type**: `algebraMap (FractionRing (Polynomial F)) C.FunctionField C.cFracPoly = algebraMap (Polynomial F) C.FunctionField (X³ + ...)`
- **What**: Analogous scalar-tower identity for `cFracPoly`.
- **How**: Same as `algebraMap_bFracPoly`.
- **Hypotheses**: None.
- **Uses from project**: `cFracPoly`
- **Used by**: `decomp_from_quadratic` (lines 766, 785)
- **Visibility**: public
- **Lines**: 714–721, proof ~7 lines
- **Notes**: None.

---

### `theorem decomp_zero_iff`

- **Type**: `{p q : FractionRing (Polynomial F)} → p • 1 + q • C.coordYInFunctionField = 0 → p = 0 ∧ q = 0`
- **What**: Linear independence of `{1, coordY}` in `F(C)` over `F(X)`: the only trivial combination is `p = q = 0`.
- **How**: Uses `functionFieldBasis.linearIndependent` via `Fintype.linearIndependent_iff`, assembles the sum and extracts coordinates.
- **Hypotheses**: None.
- **Uses from project**: `functionFieldBasis`, `functionFieldBasis_zero`, `functionFieldBasis_one`, `coordYInFunctionField`
- **Used by**: `decomp_from_quadratic` (line 790)
- **Visibility**: public
- **Lines**: 727–738, proof ~11 lines
- **Notes**: None.

---

### `theorem decomp_from_quadratic`

- **Type**: Given `p, q, α, γ ∈ F(X)` and `x = p•1 + q•Y` satisfying `x² - α·x + γ = 0` in `F(C)`, proves: `p² + q²·c - α·p + γ = 0` and `2·p·q - q²·b - α·q = 0` in `F(X)`.
- **What**: Extracts two scalar equations in `F(X)` from an integral equation for `x` in `F(C)`.
- **How**: Uses `coordYInFunctionField_sq` to substitute Y², rewrites via `algebraMap_bFracPoly/cFracPoly`, assembles as a sum `(coeff_1)•1 + (coeff_Y)•Y = 0`, and applies `decomp_zero_iff`.
- **Hypotheses**: None.
- **Uses from project**: `coordYInFunctionField_sq`, `algebraMap_bFracPoly`, `algebraMap_cFracPoly`, `bFracPoly`, `cFracPoly`, `decomp_zero_iff`, `coordYInFunctionField`
- **Used by**: `isIntegrallyClosed_coordinateRing_of_IsElliptic` (line 903)
- **Visibility**: public
- **Lines**: 746–790, proof ~44 lines
- **Notes**: Proof > 30 lines.

---

### `theorem mem_coordinateRing_of_minpoly_natDegree_one`

- **Type**: `{x : C.FunctionField} → IsIntegral (Polynomial F) x → (minpoly (Polynomial F) x).natDegree = 1 → ∃ y : C.CoordinateRing, algebraMap C.CoordinateRing C.FunctionField y = x`
- **What**: If x is integral over F[X] with minpoly of degree 1, then x is in the image of F[C].
- **How**: Uses `Polynomial.Monic.eq_X_add_C` to write the minpoly as `X + c₀`, so `x = -c₀`; constructs the preimage as `-algebraMap F[X] F[C] c₀`.
- **Hypotheses**: None (other than integrality + degree bound).
- **Uses from project**: none
- **Used by**: `isIntegrallyClosed_coordinateRing_of_IsElliptic` (line 868)
- **Visibility**: public
- **Lines**: 796–809, proof ~13 lines
- **Notes**: None.

---

### `theorem Polynomial.Monic.eq_X_sq_add_C_mul_X_add_C_of_natDegree_two`

- **Type**: `{R : Type*} [Semiring R] [Nontrivial R] {p : Polynomial R} → p.Monic → p.natDegree = 2 → p = X^2 + C(p.coeff 1) * X + C(p.coeff 0)`
- **What**: Any monic polynomial of degree 2 is determined by its coefficients 0 and 1.
- **How**: Coefficient-by-coefficient: uses `interval_cases n` for `n < 3`, and `coeff_eq_zero_of_natDegree_lt` for `n ≥ 3`.
- **Hypotheses**: Nontrivial semiring.
- **Uses from project**: none
- **Used by**: `isIntegrallyClosed_coordinateRing_of_IsElliptic` (line 872)
- **Visibility**: public (but in `Polynomial.Monic` namespace)
- **Lines**: 815–837, proof ~22 lines
- **Notes**: Strong mathlib duplication suspicion (likely `Polynomial.Monic.eq_X_sq_add_C_mul_X_add_C` or similar exists).

---

### `instance isIntegrallyClosed_coordinateRing_of_IsElliptic`

- **Type**: `[NeZero (2 : F)] → [NeZero (3 : F)] → [C.toAffine.IsElliptic] → IsIntegrallyClosed C.CoordinateRing`
- **What**: Under IsElliptic and char ≠ 2,3, the coordinate ring `F[C]` is integrally closed (and hence, by subsequent instances, a Dedekind domain).
- **How**: Rewrites via `isIntegrallyClosed_iff`; for `x ∈ F(C)` integral over `F(X)`, decomposes `x = p + q·Y` via `exists_decomp`, uses `decomp_from_quadratic` to extract two scalar equations, factors via `mul_eq_zero` on `q · (...)`, handles `q = 0` (degree 1 case via `mem_coordinateRing_of_minpoly_natDegree_one`) and `q ≠ 0` (degree 2 case: applies `polynomialDiscriminant_eq_trace_sq_sub_four_norm` + `polynomialDiscriminant_squarefree` + `fractionRing_mem_range_of_sq_mul_squarefree` to extract `q' ∈ F[X]`, then recovers `p' ∈ F[X]`).
- **Hypotheses**: `NeZero (2 : F)`, `NeZero (3 : F)`, `C.toAffine.IsElliptic`.
- **Uses from project**: `exists_decomp`, `decomp_from_quadratic`, `mem_coordinateRing_of_minpoly_natDegree_one`, `Polynomial.Monic.eq_X_sq_add_C_mul_X_add_C_of_natDegree_two`, `polynomialDiscriminant_eq_trace_sq_sub_four_norm`, `polynomialDiscriminant_squarefree`, `Polynomial.fractionRing_mem_range_of_sq_mul_squarefree`, `bFracPoly`, `cFracPoly`, `coordYInFunctionField`, `finrank_functionField_over_fracPolynomialX` (from FiniteOverKx)
- **Used by**: `isDedekindRing_coordinateRing`, `isDedekindDomain_coordinateRing`, `mem_coordinateRing_of_isIntegral_polynomialX`, `mem_coordinateRing_of_valuation_le_one`, `SmoothPoint.toHeightOneSpectrum` (all via typeclass)
- **Visibility**: public
- **Lines**: 842–1049, proof ~207 lines
- **Notes**: `set_option maxHeartbeats 3200000 in` (NO-COMMENT). Proof >> 30 lines — the longest proof in the file by far. Central theorem of the file.
