# Inventory: ./HasseWeil/Curves/FiniteOverKx.lean

**File purpose**: Proves that the coordinate ring `F[C]` of a smooth plane curve is free of rank 2 over `F[X]`, and consequently the function field `F(C)` is a degree-2 extension of the rational function field `F(x) = FractionRing F[X]`. Also defines and studies the coordinate functions `x, y ∈ F(C)`. This is a generalization of `HasseWeil/Basic.lean` which required `[W.toAffine.IsElliptic]` — here no ellipticity is assumed.

**Imports**: `HasseWeil.Auxiliary.Universal`, `HasseWeil.Curves.Basic`, `Mathlib.LinearAlgebra.Dimension.Finrank`, `Mathlib.RingTheory.Localization.Finiteness`

**Namespace**: `HasseWeil.Curves.SmoothPlaneCurve`

**Variable**: `{F : Type*} [Field F] (C : SmoothPlaneCurve F)`

---

## Declarations

### `instance coordinateRing_module_over_polynomialX`
- **Type**: `Module (Polynomial F) C.CoordinateRing`
- **What**: Gives `C.CoordinateRing` the structure of a `Polynomial F`-module via the algebra structure.
- **How**: `Algebra.toModule` — directly converts the algebra structure to a module.
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`.
- **Uses from project**: none (only mathlib `Algebra.toModule`)
- **Used by**: `coordinateRing_finite_over_polynomialX`, `finrank_coordinateRing_over_polynomialX`, `faithfulSMul_polynomialX_coordinateRing`, `isLocalization_coordinateRing_functionField`, `finite_fracPolynomialX_functionField`
- **Visibility**: public
- **Lines**: 36–38, proof length: 1 line (term-mode)
- **Notes**: none

---

### `instance coordinateRing_finite_over_polynomialX`
- **Type**: `Module.Finite (Polynomial F) C.CoordinateRing`
- **What**: The coordinate ring `F[C]` is a finite (module-finite) module over `F[X]`, using the basis `{1, Y}` provided by `Affine.CoordinateRing.basis`.
- **How**: `Module.Finite.of_basis` applied to `Affine.CoordinateRing.basis C.toAffine` — a basis provides fineness directly.
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`.
- **Uses from project**: none directly (uses `Affine.CoordinateRing.basis` from mathlib/project via `HasseWeil.Curves.Basic`)
- **Used by**: `finrank_coordinateRing_over_polynomialX`, `isNoetherianRing_coordinateRing`, `isIntegral_polynomialX_coordinateRing`, `finite_fracPolynomialX_functionField`
- **Visibility**: public
- **Lines**: 43–45, proof length: 1 line (term-mode)
- **Notes**: none

---

### `theorem finrank_coordinateRing_over_polynomialX`
- **Type**: `Module.finrank (Polynomial F) C.CoordinateRing = 2`
- **What**: The finrank of `F[C]` as a `F[X]`-module equals 2; concretely the basis `{1, Y}` has cardinality 2.
- **How**: Chains `Module.finrank_eq_card_basis` (applied to `Affine.CoordinateRing.basis C.toAffine`) with `Fintype.card_fin 2`.
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`.
- **Uses from project**: none (mathlib only)
- **Used by**: `finrank_functionField_over_fracPolynomialX`
- **Visibility**: public
- **Lines**: 50–53, proof length: 2 lines (term-mode)
- **Notes**: Reference cited: Silverman III.3.1.1.

---

### `instance faithfulSMul_polynomialX_functionField`
- **Type**: `FaithfulSMul (Polynomial F) C.FunctionField`
- **What**: The action of `F[X]` on `C.FunctionField` is faithful — distinct polynomials act differently on the function field.
- **How**: Injectivity of the composite `F[X] → F[C] → F(C)` established by composing `IsFractionRing.injective` with `Affine.CoordinateRing.algebraMap_poly_injective`; then the faithful-smul definitional unfolding uses `h 1` and `mul_one`.
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`.
- **Uses from project**: `Affine.CoordinateRing.algebraMap_poly_injective` (from project's `HasseWeil.Curves.Basic` or mathlib)
- **Used by**: `faithfulSMul_polynomialX_coordinateRing` (parallel instance), `isLocalization_coordinateRing_functionField`
- **Visibility**: public (noncomputable)
- **Lines**: 57–68, proof length: 7 lines
- **Notes**: `set_option synthInstance.maxHeartbeats 40000` with justifying comment: "Instance synthesis climbs through the `F[X] → F[C] → F(C)` tower with multiple `Algebra`/`IsScalarTower` steps, requiring extra heartbeats."

---

### `instance algebra_fracRing_polynomialX_functionField`
- **Type**: `Algebra (FractionRing (Polynomial F)) C.FunctionField`
- **What**: Gives `C.FunctionField` the structure of an algebra over `FractionRing (Polynomial F)` via the localization universal property.
- **How**: `FractionRing.liftAlgebra` — the universal property of the fraction ring lifts the `F[X]`-algebra structure on `F(C)`.
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`. Implicitly uses `faithfulSMul_polynomialX_functionField` for injectivity.
- **Uses from project**: `faithfulSMul_polynomialX_functionField`
- **Used by**: `scalarTower_fracRing_polynomialX`, `isBaseChange_coordinateRing_functionField`, `finite_fracPolynomialX_functionField`, `finrank_functionField_over_fracPolynomialX`
- **Visibility**: public (noncomputable)
- **Lines**: 70–72, proof length: 1 line (term-mode)
- **Notes**: none

---

### `instance scalarTower_fracRing_polynomialX`
- **Type**: `IsScalarTower (Polynomial F) (FractionRing (Polynomial F)) C.FunctionField`
- **What**: The scalar tower `F[X] → FractionRing(F[X]) → F(C)` is compatible — the algebra maps compose correctly.
- **How**: `FractionRing.isScalarTower_liftAlgebra` directly provides the tower compatibility.
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`.
- **Uses from project**: `algebra_fracRing_polynomialX_functionField`
- **Used by**: `isLocalizedModule_functionField`, `isBaseChange_coordinateRing_functionField`, `algebraMap_polynomialX_functionField_injective`
- **Visibility**: public (noncomputable)
- **Lines**: 74–76, proof length: 1 line (term-mode)
- **Notes**: none

---

### `instance isIntegral_polynomialX_coordinateRing`
- **Type**: `Algebra.IsIntegral (Polynomial F) C.CoordinateRing`
- **What**: Every element of `F[C]` is integral over `F[X]` — a consequence of the module-finiteness.
- **How**: `Algebra.IsIntegral.of_finite` converts module-finiteness to integrality.
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`. Requires `coordinateRing_finite_over_polynomialX`.
- **Uses from project**: `coordinateRing_finite_over_polynomialX`
- **Used by**: `isLocalization_coordinateRing_functionField`
- **Visibility**: public (noncomputable)
- **Lines**: 78–80, proof length: 1 line (term-mode)
- **Notes**: none

---

### `instance isNoetherianRing_coordinateRing`
- **Type**: `IsNoetherianRing C.CoordinateRing`
- **What**: The coordinate ring `F[C]` is Noetherian — since `F[X]` is Noetherian and `F[C]` is module-finite over `F[X]`.
- **How**: `Algebra.FiniteType.isNoetherianRing` applied at the `(Polynomial F) → C.CoordinateRing` level; `F[X]` is a Noetherian ring (PID) and the algebra is finitely generated as a module.
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`. Requires `coordinateRing_finite_over_polynomialX`.
- **Uses from project**: `coordinateRing_finite_over_polynomialX` (implicit via instance chain)
- **Used by**: unused in file (but available to importing files)
- **Visibility**: public
- **Lines**: 85–87, proof length: 1 line (term-mode)
- **Notes**: Labeled `T-INFRA-IC-001` in the doc-comment.

---

### `instance faithfulSMul_polynomialX_coordinateRing`
- **Type**: `FaithfulSMul (Polynomial F) C.CoordinateRing`
- **What**: The action of `F[X]` on `F[C]` is faithful — distinct polynomials act differently on the coordinate ring.
- **How**: `Affine.CoordinateRing.algebraMap_poly_injective` provides injectivity of `algebraMap`; the faithful-smul unfolding uses `h 1` and `mul_one`.
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`.
- **Uses from project**: `Affine.CoordinateRing.algebraMap_poly_injective`
- **Used by**: `isLocalization_coordinateRing_functionField`
- **Visibility**: public (noncomputable)
- **Lines**: 89–94, proof length: 4 lines
- **Notes**: Parallel structure to `faithfulSMul_polynomialX_functionField`.

---

### `instance isLocalization_coordinateRing_functionField`
- **Type**: `IsLocalization (Algebra.algebraMapSubmonoid C.CoordinateRing (nonZeroDivisors (Polynomial F))) C.FunctionField`
- **What**: The function field `F(C)` is the localization of `F[C]` at the image of `F[X]`'s non-zero-divisors — establishing `F(C)` as a localization in a precise ring-theoretic sense.
- **How**: Uses `IsLocalization.iff_of_le_of_exists_dvd` together with: (1) algebraic integrality (`Algebra.IsAlgebraic.isAlgebraic`), (2) injectivity of `F[X] → F[C]` via `FaithfulSMul.algebraMap_injective` to get `NoZeroDivisors`, (3) `Algebra.IsAlgebraic.isAlgebraic.exists_nonzero_dvd` to produce the required divisibility witnesses, (4) `map_le_nonZeroDivisors_of_injective` for the submonoid inclusion.
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`. Depends on `isIntegral_polynomialX_coordinateRing`, `faithfulSMul_polynomialX_coordinateRing`.
- **Uses from project**: `isIntegral_polynomialX_coordinateRing`, `faithfulSMul_polynomialX_coordinateRing`
- **Used by**: `isLocalizedModule_functionField`
- **Visibility**: public (noncomputable)
- **Lines**: 96–112, proof length: 13 lines
- **Notes**: The proof is technically the most involved in the file, using several mathlib localization lemmas.

---

### `instance isLocalizedModule_functionField`
- **Type**: `IsLocalizedModule (nonZeroDivisors (Polynomial F)) (IsScalarTower.toAlgHom (Polynomial F) C.CoordinateRing C.FunctionField).toLinearMap`
- **What**: The function field `F(C)` is a localized module of `F[C]` at the non-zero-divisors of `F[X]`, via the `IsLocalizedModule` interface.
- **How**: `isLocalizedModule_iff_isLocalization.mpr inferInstance` — converts the localization instance to a localized-module instance.
- **Hypotheses**: Requires `isLocalization_coordinateRing_functionField`.
- **Uses from project**: `isLocalization_coordinateRing_functionField`
- **Used by**: `isBaseChange_coordinateRing_functionField`
- **Visibility**: public (noncomputable)
- **Lines**: 114–117, proof length: 1 line (term-mode)
- **Notes**: none

---

### `theorem isBaseChange_coordinateRing_functionField`
- **Type**: `IsBaseChange (FractionRing (Polynomial F)) (IsScalarTower.toAlgHom (Polynomial F) C.CoordinateRing C.FunctionField).toLinearMap`
- **What**: The function field `F(C)` is the base change of `F[C]` along `F[X] → FractionRing(F[X])` — a ring-theoretic statement saying `F(C) ≅ FractionRing(F[X]) ⊗_{F[X]} F[C]`.
- **How**: `isLocalizedModule_iff_isBaseChange` converts the `IsLocalizedModule` instance to `IsBaseChange`.
- **Hypotheses**: Requires `isLocalizedModule_functionField`.
- **Uses from project**: `isLocalizedModule_functionField`
- **Used by**: `finrank_functionField_over_fracPolynomialX`
- **Visibility**: public
- **Lines**: 119–122, proof length: 1 line (term-mode)
- **Notes**: none

---

### `instance finite_fracPolynomialX_functionField`
- **Type**: `Module.Finite (FractionRing (Polynomial F)) C.FunctionField`
- **What**: The function field `F(C)` is a finite module over `FractionRing(F[X])` — localizing the finite `F[X]`-module `F[C]` preserves finiteness.
- **How**: `Module.Finite.of_isLocalization` at `(Polynomial F)` level, using `coordinateRing_finite_over_polynomialX` as the finiteness input.
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`. Requires `coordinateRing_finite_over_polynomialX`.
- **Uses from project**: `coordinateRing_finite_over_polynomialX`
- **Used by**: `finrank_functionField_over_fracPolynomialX`
- **Visibility**: public (noncomputable)
- **Lines**: 126–131, proof length: 4 lines (with explicit type ascriptions)
- **Notes**: The heavy explicit `@Module.Finite.of_isLocalization` with many underscores suggests instance elaboration requires guidance.

---

### `theorem finrank_functionField_over_fracPolynomialX`
- **Type**: `Module.finrank (FractionRing (Polynomial F)) C.FunctionField = 2`
- **What**: The function field `F(C)` has degree 2 over `FractionRing(F[X]) = F(x)` — the key Silverman III.3.1.1 result without ellipticity assumption.
- **How**: Rewrites via `isBaseChange_coordinateRing_functionField.finrank_eq` (base change preserves finrank) and `finrank_coordinateRing_over_polynomialX` (finrank = 2 at the coordinate ring level).
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`.
- **Uses from project**: `isBaseChange_coordinateRing_functionField`, `finrank_coordinateRing_over_polynomialX`
- **Used by**: unused in file (public API for importing files)
- **Visibility**: public
- **Lines**: 137–140, proof length: 2 lines
- **Notes**: Reference cited: Silverman III.3.1.1.

---

### `noncomputable def coordX`
- **Type**: `C.FunctionField`
- **What**: The coordinate function `x ∈ F(C)` — the image of the formal indeterminate `Polynomial.X : F[X]` under the composite algebra map `F[X] → F[C] → F(C)`.
- **How**: Direct definition: `algebraMap (Polynomial F) C.FunctionField Polynomial.X`.
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`.
- **Uses from project**: none
- **Used by**: `coordX_ne_zero`, `transcendental_coordX`
- **Visibility**: public
- **Lines**: 147–148, proof length: 0 (def)
- **Notes**: none

---

### `theorem algebraMap_polynomialX_functionField_injective`
- **Type**: `Function.Injective (algebraMap (Polynomial F) C.FunctionField)`
- **What**: The composite algebra map `F[X] → F[C] → F(C)` is injective.
- **How**: Uses scalar tower decomposition `IsScalarTower.algebraMap_eq` to factor the map, then composes `IsFractionRing.injective` with `Affine.CoordinateRing.algebraMap_poly_injective`.
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`.
- **Uses from project**: `Affine.CoordinateRing.algebraMap_poly_injective` (referenced from the Affine coordinate ring theory)
- **Used by**: `coordX_ne_zero`, `transcendental_coordX`
- **Visibility**: public
- **Lines**: 151–155, proof length: 3 lines
- **Notes**: none

---

### `theorem coordX_ne_zero`
- **Type**: `C.coordX ≠ 0`
- **What**: The coordinate function `x ∈ F(C)` is nonzero.
- **How**: By contradiction: if `x = 0`, then since `algebraMap (Polynomial F) C.FunctionField` maps `X ↦ x`, and `0` maps to `0`, injectivity (`algebraMap_polynomialX_functionField_injective`) would imply `X = 0`, contradicting `Polynomial.X_ne_zero`.
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`.
- **Uses from project**: `coordX`, `algebraMap_polynomialX_functionField_injective`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 159–163, proof length: 4 lines
- **Notes**: none

---

### `noncomputable def coordY`
- **Type**: `C.FunctionField`
- **What**: The coordinate function `y ∈ F(C)` — the image of the second basis vector `Affine.CoordinateRing.basis C.toAffine 1` under `F[C] → F(C)`.
- **How**: Direct definition: `algebraMap C.CoordinateRing C.FunctionField (Affine.CoordinateRing.basis C.toAffine 1)`.
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`.
- **Uses from project**: none (uses `Affine.CoordinateRing.basis` from mathlib/project)
- **Used by**: `coordY_ne_zero`
- **Visibility**: public
- **Lines**: 170–172, proof length: 0 (def)
- **Notes**: none

---

### `theorem coordY_ne_zero`
- **Type**: `C.coordY ≠ 0`
- **What**: The coordinate function `y ∈ F(C)` is nonzero.
- **How**: By contradiction via injectivity of `IsFractionRing.injective`: if `y = 0` then `algebraMap` maps the basis vector to `0`, but basis vectors are nonzero by `Basis.ne_zero`.
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`.
- **Uses from project**: `coordY`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 175–182, proof length: 7 lines
- **Notes**: none

---

### `theorem transcendental_coordX`
- **Type**: `Transcendental F C.coordX`
- **What**: The coordinate function `x ∈ F(C)` is transcendental over the base field `F`.
- **How**: Rewrites `Transcendental` as injectivity (`transcendental_iff_injective`), then shows polynomial evaluation at `coordX` agrees with `algebraMap (Polynomial F) C.FunctionField` via induction on polynomials (`Polynomial.induction_on'`), using `Polynomial.aeval_monomial`, `map_pow`, `map_mul`, and `Polynomial.algebraMap_eq`; the conclusion follows from injectivity (`algebraMap_polynomialX_functionField_injective`).
- **Hypotheses**: `[Field F]`, `C : SmoothPlaneCurve F`.
- **Uses from project**: `coordX`, `algebraMap_polynomialX_functionField_injective`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 186–200, proof length: 14 lines
- **Notes**: Reference implicit in Silverman II.1.4 discussion.

---

## Summary

| Metric | Count |
|--------|-------|
| Total declarations | 18 |
| `def` / `noncomputable def` | 2 |
| `theorem` | 6 |
| `instance` / `noncomputable instance` | 10 |
| `sorry` | 0 |
| Proofs > 30 lines | 0 |
| `set_option maxHeartbeats` | 1 (`synthInstance.maxHeartbeats 40000` on `faithfulSMul_polynomialX_functionField`) |

**Key API** (used by 3+ other declarations in file): `algebraMap_polynomialX_functionField_injective` (used by `coordX_ne_zero`, `transcendental_coordX`, and `faithfulSMul_polynomialX_functionField`); `coordinateRing_finite_over_polynomialX` (used by `finrank_coordinateRing_over_polynomialX`, `isIntegral_polynomialX_coordinateRing`, `isNoetherianRing_coordinateRing`, `finite_fracPolynomialX_functionField`).

**Unused in file** (dead-code candidates): `isNoetherianRing_coordinateRing`, `finrank_functionField_over_fracPolynomialX`, `coordX_ne_zero`, `coordY_ne_zero`, `transcendental_coordX` — all are public API for importing files.

**Notable**: This file is a clean, self-contained ladder of algebra/localization instances building up from `F[X]`-finiteness to the degree-2 statement. It partially duplicates `HasseWeil/Basic.lean` (which requires `IsElliptic`), dropping that hypothesis. No sorries, no long proofs, one justified `synthInstance.maxHeartbeats` bump.
