# Inventory: ./HasseWeil/Curves/FrobeniusFixedPoint.lean

**Summary**: 345 lines. Builds the geometric Frobenius endomorphism on `L = AlgebraicClosure K` points, the base-change inclusion of `K`-rational points, and proves the point-level fixed-locus theorem (S2): a point over the algebraic closure is Frobenius-fixed iff it is the image of a `K`-rational point. Also packages the `1 − π` AddMonoidHom and its kernel identification. One `sorry`-free file after the main theorem was closed.

**Imports**: `HasseWeil.Curves.FrobeniusFixedLocus`, `HasseWeil.EC.AffinePointMap`, `Mathlib.FieldTheory.Finite.Basic`, `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.

---

## Declarations

### `noncomputable def geomFrobRingHom`

- **Type**: `AlgebraicClosure K →+* AlgebraicClosure K`
- **What**: The geometric Frobenius ring hom `x ↦ x ^ q` on `L = AlgebraicClosure K`, obtained by coercing mathlib's `FiniteField.frobeniusAlgHom K L` to a `RingHom`.
- **How**: Single-line definition: `(FiniteField.frobeniusAlgHom K (AlgebraicClosure K)).toRingHom`.
- **Hypotheses**: `K` is a finite field.
- **Uses from project**: none.
- **Used by**: `geomFrobRingHom_apply`, `map_geomFrob_baseChange_eq_self` (in this file); referenced externally in no other file (not directly imported outside this file).
- **Visibility**: public
- **Lines**: 78–79 (body: 1 line)
- **Notes**: Thin wrapper; essentially identical to `FiniteField.frobeniusAlgHom` coercion.

---

### `@[simp] theorem geomFrobRingHom_apply`

- **Type**: `geomFrobRingHom (K := K) a = a ^ Fintype.card K`
- **What**: The geometric Frobenius ring hom evaluates as the `q`-th power map.
- **How**: `show` unfolds the coercion, then `rw [FiniteField.coe_frobeniusAlgHom]` closes the goal.
- **Hypotheses**: `K` finite field, `a : AlgebraicClosure K`.
- **Uses from project**: `geomFrobRingHom`.
- **Used by**: used externally in `FrobeniusConjugation.lean` and others via `FiniteField.coe_frobeniusAlgHom` directly; within this file not called after definition.
- **Visibility**: public
- **Lines**: 81–85 (proof: 2 lines)
- **Notes**: None.

---

### `@[simp] theorem map_geomFrob_baseChange_eq_self`

- **Type**: `(W.baseChange (AlgebraicClosure K)).map (geomFrobRingHom (K := K)) = W.baseChange (AlgebraicClosure K)`
- **What**: The base-changed curve mapped by the geometric Frobenius ring hom equals itself; the codomain identification making the geometric Frobenius an endomorphism.
- **How**: Rewrites the coercion via `AlgHom.toRingHom_eq_coe`, then applies `W.map_baseChange` (mathlib: a `K`-algebra hom fixes `algebraMap K L` images, so the curve coefficients are unchanged).
- **Hypotheses**: `K` finite field, `W` a Weierstrass curve over `K`.
- **Uses from project**: `geomFrobRingHom`.
- **Used by**: Transitively needed to make `geomFrobeniusPointFun` well-typed; referenced in the docstring of `geomFrobeniusPoint_fixed_iff_mem_range_includePointBC`. Not directly referenced inside this file after declaration (the rewrite in S2 is done differently). Unused directly within this file body.
- **Visibility**: public
- **Lines**: 90–100 (proof: 8 lines)
- **Notes**: The comment in S2 explains that transporting across the propositional equality produced by this `simp` lemma is the key remaining unifier challenge.

---

### `noncomputable def geomFrobeniusPointFun`

- **Type**: `(W.baseChange (AlgebraicClosure K)).toAffine.Point → (W.baseChange (AlgebraicClosure K)).toAffine.Point`
- **What**: The geometric Frobenius on `L`-points as a raw function: applies `Affine.Point.map` of `frobeniusAlgHom K L`.
- **How**: Direct application of `WeierstrassCurve.Affine.Point.map` with the `AlgHom` argument; the codomain identifies by definition with the base-changed curve.
- **Hypotheses**: `K` finite field.
- **Uses from project**: none (uses mathlib's `WeierstrassCurve.Affine.Point.map`).
- **Used by**: `geomFrobeniusPointFun_zero`, `geomFrobeniusPointFun_some`, `geomFrobeniusPoint_fixed_iff_mem_range_includePointBC`, `fixedLocus_geomFrobenius_eq_range_includePointBC`, `ncard_fixedLocus_geomFrobenius_eq_pointCount`, `geomFrobeniusPoint_apply`, `oneSubGeomFrobHom_apply`, `ker_oneSubGeomFrobHom_eq_fixedLocus`, `ncard_ker_oneSubGeomFrobHom_eq_pointCount` (this file); also heavily used in `FrobeniusConjugation.lean`, `L6Witnesses.lean`, `OneSubAffineResidues.lean`, `OneSubWitnesses.lean`.
- **Visibility**: public
- **Lines**: 109–113 (body: 2 lines)
- **Notes**: Key API; mirrors `frobeniusW_KE` in `Hasse/IsogOneSubXyFamily.lean`.

---

### `@[simp] theorem geomFrobeniusPointFun_zero`

- **Type**: `geomFrobeniusPointFun W (0 : (W.baseChange (AlgebraicClosure K)).toAffine.Point) = 0`
- **What**: The geometric Frobenius sends the point at infinity to itself.
- **How**: `rfl` (definitionally true from `Affine.Point.map` on `zero`).
- **Hypotheses**: None beyond the base variables.
- **Uses from project**: `geomFrobeniusPointFun`.
- **Used by**: Used externally in `FrobeniusConjugation.lean`.
- **Visibility**: public
- **Lines**: 115–116 (proof: 1 line / `rfl`)
- **Notes**: None.

---

### `theorem geomFrobeniusPointFun_some`

- **Type**: For a nonsingular point `(x, y)`, `geomFrobeniusPointFun W (.some x y h) = .some (frobeniusAlgHom K L x) (frobeniusAlgHom K L y) _`.
- **What**: The geometric Frobenius applies coordinatewise as the `q`-power to an affine point.
- **How**: Unfolds `geomFrobeniusPointFun` and applies `WeierstrassCurve.Affine.Point.map_some` directly.
- **Hypotheses**: `h : (W.baseChange L).toAffine.Nonsingular x y`.
- **Uses from project**: `geomFrobeniusPointFun`.
- **Used by**: `geomFrobeniusPoint_fixed_iff_mem_range_includePointBC` (this file); `FrobeniusConjugation.lean`, `OneSubAffineResidues.lean` (external).
- **Visibility**: public
- **Lines**: 121–133 (proof: 4 lines)
- **Notes**: Uses `WeierstrassCurve.Affine.baseChange_nonsingular` to produce the nonsingularity hypothesis for the RHS.

---

### `noncomputable def includePointBC`

- **Type**: `W.toAffine.Point → (W.baseChange (AlgebraicClosure K)).toAffine.Point`
- **What**: The base-change inclusion of `K`-rational points into `L`-points, defined as `HasseWeil.Affine.Point.map (algebraMap K L)` with injectivity witness.
- **How**: Applies `HasseWeil.Affine.Point.map` (project declaration from `AffinePointMap.lean`) with `FaithfulSMul.algebraMap_injective` as the injectivity proof.
- **Hypotheses**: `K` finite field.
- **Uses from project**: `HasseWeil.Affine.Point.map` (from `EC/AffinePointMap.lean`).
- **Used by**: `includePointBC_zero`, `includePointBC_some`, `includePointBC_injective`, `geomFrobeniusPoint_fixed_iff_mem_range_includePointBC`, `fixedLocus_geomFrobenius_eq_range_includePointBC`, `ncard_fixedLocus_geomFrobenius_eq_pointCount`, `ncard_ker_oneSubGeomFrobHom_eq_pointCount` (this file); `OneSubWitnesses.lean` (external).
- **Visibility**: public
- **Lines**: 140–143 (body: 2 lines)
- **Notes**: Key API for Route B Step 2.

---

### `@[simp] theorem includePointBC_zero`

- **Type**: `includePointBC W (0 : W.toAffine.Point) = 0`
- **What**: The base-change inclusion sends the zero point to zero.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `includePointBC`.
- **Used by**: `geomFrobeniusPoint_fixed_iff_mem_range_includePointBC`, `includePointBC_injective`.
- **Visibility**: public
- **Lines**: 145–146 (proof: 1 line)
- **Notes**: None.

---

### `@[simp] theorem includePointBC_some`

- **Type**: `includePointBC W (.some x y h) = .some (algebraMap K L x) (algebraMap K L y) _`
- **What**: The base-change inclusion on affine points applies `algebraMap` coordinatewise.
- **How**: `rfl` (definitionally true from `HasseWeil.Affine.Point.map` unfolding).
- **Hypotheses**: `h : W.toAffine.Nonsingular x y`, `x y : K`.
- **Uses from project**: `includePointBC`.
- **Used by**: `includePointBC_injective`, `geomFrobeniusPoint_fixed_iff_mem_range_includePointBC`.
- **Visibility**: public
- **Lines**: 148–152 (proof: 1 line)
- **Notes**: None.

---

### `theorem includePointBC_injective`

- **Type**: `Function.Injective (includePointBC W)`
- **What**: The base-change inclusion of rational points into `L`-points is injective.
- **How**: Case split on both arguments (zero vs some); the `zero = some` cases are discharged by `absurd` with `simp`; the `some = some` case uses `FaithfulSMul.algebraMap_injective` applied coordinatewise to the `injEq` decomposition.
- **Hypotheses**: `K` finite field, injectivity of `algebraMap K L`.
- **Uses from project**: `includePointBC_zero`, `includePointBC_some`.
- **Used by**: `ncard_fixedLocus_geomFrobenius_eq_pointCount`, `ncard_ker_oneSubGeomFrobHom_eq_pointCount`.
- **Visibility**: public
- **Lines**: 156–173 (proof: 17 lines)
- **Notes**: Proof is methodical case analysis; no sorry.

---

### `set_option maxHeartbeats 400000` + `theorem geomFrobeniusPoint_fixed_iff_mem_range_includePointBC`

- **Type**: `geomFrobeniusPointFun W P = P ↔ P ∈ Set.range (includePointBC W)`
- **What**: (S2) The main fixed-locus theorem: a point over `AlgebraicClosure K` is fixed by the geometric Frobenius iff it is in the image of the `K`-rational point inclusion.
- **How**: Case split on `P` (zero vs affine). Zero case: `iff_of_true rfl`. Affine case: `geomFrobeniusPointFun_some` + `Affine.Point.some.injEq` reduces to `x^q = x ∧ y^q = y`; `FiniteField.coe_frobeniusAlgHom` converts to power form; Step 1 (`frobenius_fixed_iff_mem_baseField`) converts each to membership in `range (algebraMap K L)`; the forward direction assembles a `K`-rational point via `WeierstrassCurve.Affine.map_nonsingular`, then `includePointBC_some`; the backward direction extracts coordinates from the `some.injEq`.
- **Hypotheses**: `K` finite field, `P : (W.baseChange L).toAffine.Point`.
- **Uses from project**: `geomFrobeniusPointFun_some`, `includePointBC_zero`, `includePointBC_some`, `frobenius_fixed_iff_mem_baseField` (from `FrobeniusFixedLocus.lean`).
- **Used by**: `fixedLocus_geomFrobenius_eq_range_includePointBC`.
- **Visibility**: public
- **Lines**: 183–249 (proof: 29 lines)
- **Notes**: `set_option maxHeartbeats 400000` — NO justifying comment given; the docstring explains the remaining codomain-transport challenge. Long (29-line) proof.

---

### `theorem fixedLocus_geomFrobenius_eq_range_includePointBC`

- **Type**: `{P : (W.baseChange L).toAffine.Point | geomFrobeniusPointFun W P = P} = Set.range (includePointBC W)`
- **What**: (S3, set form) The fixed locus of the geometric Frobenius equals the image of `K`-rational points as sets.
- **How**: `ext P` then applies `geomFrobeniusPoint_fixed_iff_mem_range_includePointBC`.
- **Hypotheses**: None beyond base variables.
- **Uses from project**: `geomFrobeniusPointFun`, `includePointBC`, `geomFrobeniusPoint_fixed_iff_mem_range_includePointBC`.
- **Used by**: `ncard_fixedLocus_geomFrobenius_eq_pointCount`; `OneSubWitnesses.lean` (external).
- **Visibility**: public
- **Lines**: 261–265 (proof: 2 lines)
- **Notes**: Pure repackaging of S2.

---

### `theorem ncard_fixedLocus_geomFrobenius_eq_pointCount`

- **Type**: `[Fintype W.toAffine.Point] → {P | geomFrobeniusPointFun W P = P}.ncard = Fintype.card W.toAffine.Point`
- **What**: (S4) The cardinality of the geometric-Frobenius fixed locus equals the number of `K`-rational points.
- **How**: Rewrites the fixed locus via `fixedLocus_geomFrobenius_eq_range_includePointBC`, applies `Set.ncard_range_of_injective` (mathlib) with `includePointBC_injective`, and `Nat.card_eq_fintype_card`.
- **Hypotheses**: `Fintype W.toAffine.Point` (the curve has finitely many rational points).
- **Uses from project**: `geomFrobeniusPointFun`, `includePointBC`, `includePointBC_injective`, `fixedLocus_geomFrobenius_eq_range_includePointBC`.
- **Used by**: `ncard_ker_oneSubGeomFrobHom_eq_pointCount`; `L6Witnesses.lean` (external).
- **Visibility**: public
- **Lines**: 284–289 (proof: 4 lines)
- **Notes**: No sorry; the cardinality glue is fully closed.

---

### `noncomputable def geomFrobeniusPoint`

- **Type**: `(W.baseChange L).toAffine.Point →+ (W.baseChange L).toAffine.Point`
- **What**: The geometric Frobenius on `L`-points as an `AddMonoidHom`, defined as `WeierstrassCurve.Affine.Point.map (frobeniusAlgHom K L)`.
- **How**: Direct definition; `.toFun` is definitionally `geomFrobeniusPointFun W`.
- **Hypotheses**: `K` finite field.
- **Uses from project**: none (uses mathlib's `WeierstrassCurve.Affine.Point.map`).
- **Used by**: `geomFrobeniusPoint_apply`, `oneSubGeomFrobHom`; `PointMapSurjective.lean`, `OneSubAffineResidues.lean`, `FrobeniusGenericCovariance.lean`, `FrobeniusGaloisScaling.lean` (external).
- **Visibility**: public
- **Lines**: 303–307 (body: 2 lines)
- **Notes**: The AddMonoidHom version of `geomFrobeniusPointFun`; key API for the broader project.

---

### `@[simp] theorem geomFrobeniusPoint_apply`

- **Type**: `geomFrobeniusPoint W P = geomFrobeniusPointFun W P`
- **What**: The AddMonoidHom `geomFrobeniusPoint` evaluates identically to the raw function `geomFrobeniusPointFun`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `geomFrobeniusPoint`, `geomFrobeniusPointFun`.
- **Used by**: Used externally in `OneSubAffineResidues.lean`, `FrobeniusGaloisScaling.lean`.
- **Visibility**: public
- **Lines**: 309–311 (proof: 1 line)
- **Notes**: None.

---

### `noncomputable def oneSubGeomFrobHom`

- **Type**: `(W.baseChange L).toAffine.Point →+ (W.baseChange L).toAffine.Point`
- **What**: The AddMonoidHom `1 − π` (identity minus geometric Frobenius) on `L`-points.
- **How**: `AddMonoidHom.id _ - geomFrobeniusPoint W`.
- **Hypotheses**: `K` finite field.
- **Uses from project**: `geomFrobeniusPoint`.
- **Used by**: `oneSubGeomFrobHom_apply`, `ker_oneSubGeomFrobHom_eq_fixedLocus`, `ncard_ker_oneSubGeomFrobHom_eq_pointCount`; `OneSubWitnesses.lean`, `L6Witnesses.lean` (external).
- **Visibility**: public
- **Lines**: 316–319 (body: 1 line)
- **Notes**: Key API for the `1 − π` kernel identification.

---

### `@[simp] theorem oneSubGeomFrobHom_apply`

- **Type**: `oneSubGeomFrobHom W P = P - geomFrobeniusPointFun W P`
- **What**: The `1 − π` hom evaluates as subtraction of Frobenius from identity.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `oneSubGeomFrobHom`, `geomFrobeniusPointFun`.
- **Used by**: `ker_oneSubGeomFrobHom_eq_fixedLocus`; externally in `L6Witnesses.lean`.
- **Visibility**: public
- **Lines**: 321–323 (proof: 1 line)
- **Notes**: None.

---

### `theorem ker_oneSubGeomFrobHom_eq_fixedLocus`

- **Type**: `((oneSubGeomFrobHom W).ker : Set _) = {P | geomFrobeniusPointFun W P = P}`
- **What**: The kernel of `1 − π` (as a set) equals the fixed-point locus of the geometric Frobenius.
- **How**: `ext P`, rewrites via `SetLike.mem_coe`, `AddMonoidHom.mem_ker`, `oneSubGeomFrobHom_apply`, then `sub_eq_zero` and `eq_comm`.
- **Hypotheses**: None.
- **Uses from project**: `oneSubGeomFrobHom`, `geomFrobeniusPointFun`, `oneSubGeomFrobHom_apply`.
- **Used by**: `ncard_ker_oneSubGeomFrobHom_eq_pointCount`; `OneSubWitnesses.lean`, `L6Witnesses.lean` (external).
- **Visibility**: public
- **Lines**: 327–332 (proof: 4 lines)
- **Notes**: None.

---

### `theorem ncard_ker_oneSubGeomFrobHom_eq_pointCount`

- **Type**: `[Fintype W.toAffine.Point] → ((oneSubGeomFrobHom W).ker : Set _).ncard = Fintype.card W.toAffine.Point`
- **What**: The cardinality of the kernel of `1 − π` equals the number of `K`-rational points.
- **How**: Rewrites via `ker_oneSubGeomFrobHom_eq_fixedLocus` then `ncard_fixedLocus_geomFrobenius_eq_pointCount`.
- **Hypotheses**: `Fintype W.toAffine.Point`.
- **Uses from project**: `oneSubGeomFrobHom`, `ker_oneSubGeomFrobHom_eq_fixedLocus`, `ncard_fixedLocus_geomFrobenius_eq_pointCount`.
- **Used by**: Unused within this file; `L6Witnesses.lean` uses this externally.
- **Visibility**: public
- **Lines**: 338–343 (proof: 3 lines)
- **Notes**: None.

---

## Local instance

### `noncomputable local instance : DecidableEq (AlgebraicClosure K)`

- **Lines**: 72
- **What**: `Classical.decEq _` — provides decidable equality on the algebraic closure.
- **Hypotheses**: None.
- **Notes**: Local instance, not a named declaration.

---

## Summary statistics

| Metric | Count |
|--------|-------|
| Total declarations (named) | 18 |
| Defs (`def`, `noncomputable def`) | 5 |
| Lemmas/theorems | 13 |
| Instances | 0 (local unnamed instance excluded) |
| Sorries | 0 |
| `set_option maxHeartbeats` occurrences | 1 (line 183, value 400000, no justifying comment) |
| Proofs > 30 lines | 0 (longest is S2 at ~29 lines) |

## Key API (used by 3+ other declarations in this file)

- `geomFrobeniusPointFun` — used by 9 other declarations in this file
- `includePointBC` — used by 7 other declarations in this file
- `geomFrobeniusPoint` — used by 3 other declarations in this file

## Notes

The file is a clean, self-contained Step 2 of the Route B fixed-locus argument, with no sorries. The `set_option maxHeartbeats 400000` on the main theorem `geomFrobeniusPoint_fixed_iff_mem_range_includePointBC` has no accompanying justifying comment, though the docstring discusses the remaining transport challenge. The `geomFrobeniusPointFun` raw function is the main internal hub; the AddMonoidHom wrapper `geomFrobeniusPoint` and the `oneSubGeomFrobHom` family serve external consumers in `L6Witnesses.lean` and `OneSubWitnesses.lean`.
