# Inventory: ./HasseWeil/WeilPairing/FrobeniusDivisorGalois.lean

**File**: `HasseWeil/WeilPairing/FrobeniusDivisorGalois.lean`
**Total lines**: 539
**Imports**: `DivisorGalois`, `FrobeniusFunctionFieldEquiv`, `DivisorTranslate`, `Pairing`, `FrobMatrixData`, `Curves.FrobeniusFixedPoint`, `Curves.NoFinitePolesBridge`

**Purpose**: Applies the abstract divisor-Galois-descent engine to the concrete arithmetic Frobenius σ = `frobeniusFunctionFieldEquiv W`, proving `ord_P(σ g) = ord_{π̄⁻¹P}(g)` (affine order transport) and `ord_∞(σ g) = ord_∞(g)` (infinity transport), then assembling the divisor equality `div(σ g_T) = div(g_{π̄T})` and the σ-naturality `σ(g_T) = c · g_{π̄T}`.

**Sorries**: none (0 sorry in file).

---

## Declarations

### `noncomputable local instance instDecEqACFDG`
- **Type**: `DecidableEq (AlgebraicClosure K)`
- **What**: Provides classical decidable equality on the algebraic closure; needed throughout for smooth-point and coordinate-ring computations.
- **How**: `Classical.decEq _`.
- **Hypotheses**: `[Field K] [Fintype K]`
- **Uses from project**: []
- **Used by**: implicitly throughout the file
- **Visibility**: private (local)
- **Lines**: 36 (1 line)
- **Notes**: none

---

### `theorem map_maximalIdealAt_crFrobEquiv`
- **Type**: For smooth points `P` on `E_{K̄}` and `Q` on `(E_{K̄}).map e` with `Q.x = e P.x`, `Q.y = e P.y`, the pushforward of `maximalIdealAt P` along `crFrobEquiv` equals `maximalIdealAt Q` on the mapped curve.
- **What**: Computes the image of the maximal ideal `m_P` under the coordinate-ring Frobenius `crFrobEquiv = CoordinateRing.map e`, showing it lands at the expected ideal on the mapped curve.
- **How**: Unfolds `crFrobEquiv` to `CoordinateRing.map e`, applies `map_XYIdeal` (the ideal transport lemma for `CoordinateRing.map`), then substitutes `hQx`/`hQy` and `Polynomial.map_C`.
- **Hypotheses**: `E_{K̄}` is elliptic; `Q.x = e P.x` and `Q.y = e P.y`.
- **Uses from project**: `crFrobEquiv`, `map_XYIdeal`
- **Used by**: `pointValuation_frobeniusFunctionFieldEquiv` (via `map_maximalIdealAt_crFrobEquiv`)
- **Visibility**: public
- **Lines**: 48–72, proof ~10 lines
- **Notes**: none

---

### `noncomputable def pointOnMapped`
- **Type**: `(SmoothPoint E_{K̄}) → (SmoothPoint (E_{K̄}).map e)` — takes a smooth point `P` of `E_{K̄}` and produces a smooth point of the mapped curve `(E_{K̄}).map e` with the same coordinates.
- **What**: Packages the nonsingularity re-proof for the same coordinates `(P.x, P.y)` on the mapped curve, using the curve equality `(E_{K̄}).map e = E_{K̄}` (`map_coeffFrobEquiv_eq`).
- **How**: `rw [map_coeffFrobEquiv_eq W]` converts the mapped curve back to the original, then uses `P.nonsingular` directly.
- **Hypotheses**: `(E_{K̄}).map e` is elliptic (provided by `haveI` in callers via `map_coeffFrobEquiv_eq`).
- **Uses from project**: `map_coeffFrobEquiv_eq`
- **Used by**: `pointOnMapped_x`, `pointOnMapped_y`, `pointValuation_frobeniusFunctionFieldEquiv`
- **Visibility**: public
- **Lines**: 81–93, body ~12 lines
- **Notes**: none

---

### `@[simp] theorem pointOnMapped_x`
- **Type**: `(pointOnMapped W P).x = P.x`
- **What**: `pointOnMapped` preserves the x-coordinate (definitionally; `rfl`).
- **How**: `rfl`.
- **Hypotheses**: none beyond `P : SmoothPoint E_{K̄}`
- **Uses from project**: `pointOnMapped`
- **Used by**: `pointValuation_frobeniusFunctionFieldEquiv`
- **Visibility**: public (`@[simp]`)
- **Lines**: 95–96, proof 1 line
- **Notes**: none

---

### `@[simp] theorem pointOnMapped_y`
- **Type**: `(pointOnMapped W P).y = P.y`
- **What**: `pointOnMapped` preserves the y-coordinate (definitionally; `rfl`).
- **How**: `rfl`.
- **Hypotheses**: none beyond `P : SmoothPoint E_{K̄}`
- **Uses from project**: `pointOnMapped`
- **Used by**: `pointValuation_frobeniusFunctionFieldEquiv`
- **Visibility**: public (`@[simp]`)
- **Lines**: 98–99, proof 1 line
- **Notes**: none

---

### `theorem pointValuation_frobeniusFunctionFieldEquiv`
- **Type**: For smooth points `P`, `Q` on `E_{K̄}` with `P.x = e Q.x` and `P.y = e Q.y`, and any `g : K̄(E)`, `ord_P(σ g) = ord_Q g`.
- **What**: The affine order transport for the arithmetic Frobenius: the valuation of `σ g` at `P` equals the valuation of `g` at the "Frobenius-pre-image" point `Q`.
- **How**: Decomposes `frobeniusFunctionFieldEquiv = ffFrobCast ∘ ffFrobEquivRaw`; applies `pointValuation_ringEquivCast` (cast bridge via `map_coeffFrobEquiv_eq`) to transport the cast, then converts both sides to `HeightOneSpectrum.valuation` via `pointValuation_eq_heightOneValuation`, and concludes by `valuation_map_ringEquiv` applied to `crFrobEquiv` with the ideal transport `map_maximalIdealAt_crFrobEquiv`.
- **Hypotheses**: Smooth points satisfy `P.x = e Q.x`, `P.y = e Q.y`; `IsIntegrallyClosed` on the coordinate ring; various `IsDedekindDomain` instances.
- **Uses from project**: `frobeniusFunctionFieldEquiv`, `ffFrobCast`, `pointValuation_ringEquivCast`, `map_coeffFrobEquiv_eq`, `pointOnMapped`, `heq_smoothPoint`, `pointValuation_eq_heightOneValuation`, `ffFrobEquivRaw`, `valuation_map_ringEquiv`, `crFrobEquiv`, `smoothPointToHeightOne`, `smoothPointToHeightOne_asIdeal`, `map_maximalIdealAt_crFrobEquiv`, `pointOnMapped_x`, `pointOnMapped_y`
- **Used by**: `ord_P_frobeniusFunctionFieldEquiv`
- **Visibility**: public
- **Lines**: 112–155, proof ~33 lines
- **Notes**: `set_option maxHeartbeats 1000000` at line 101 (NO accompanying justification comment). Proof >30 lines.

---

### `theorem crFrobEquiv_smul_basis`
- **Type**: For `p q : K̄[X]`, `crFrobEquiv W (p • 1 + q • y) = (p.map e) • 1' + (q.map e) • y'` where the RHS lives in the coordinate ring of the mapped curve.
- **What**: Computes `crFrobEquiv` on the basis decomposition `p • 1 + q • y`, showing it maps the polynomial coefficients through `e` (Frobenius on coefficients) while fixing the basis elements `1` and `y`.
- **How**: `crFrobEquiv_apply` unfolds, `map_add`/`CoordinateRing.map_smul`/`map_one` simplify, then `CoordinateRing.map_mk` and `Polynomial.map_X` handle the `y`-basis.
- **Hypotheses**: none beyond the ambient variables
- **Uses from project**: `crFrobEquiv_apply`, `WeierstrassCurve.Affine.CoordinateRing.map_smul`, `WeierstrassCurve.Affine.CoordinateRing.map_mk`
- **Used by**: `norm_crFrobEquiv`
- **Visibility**: public
- **Lines**: 166–181, proof ~14 lines
- **Notes**: none

---

### `theorem norm_crFrobEquiv`
- **Type**: `Algebra.norm K̄[X] (crFrobEquiv W u) = (Algebra.norm K̄[X] u).map e`
- **What**: The norm of `crFrobEquiv u` (in the coordinate ring of the mapped curve, over `K̄[X]`) equals the Frobenius `e` of the norm of `u`. Both are the `norm_smul_basis` polynomial; the identity follows because the Weierstrass coefficients of the mapped curve are exactly `e(aᵢ)`.
- **How**: Decomposes `u` via `exists_smul_basis_eq`, applies `crFrobEquiv_smul_basis`, then `CoordinateRing.norm_smul_basis` on both sides; the remaining equality is discharged by `simp` with Weierstrass `map_aᵢ` lemmas and `Polynomial.map_*`.
- **Hypotheses**: none beyond ambient
- **Uses from project**: `crFrobEquiv_smul_basis`, `WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis`, `WeierstrassCurve.map_a₁` etc.
- **Used by**: `ordAtInfty_algebraMap_crFrobEquiv`
- **Visibility**: public
- **Lines**: 187–196, proof ~9 lines
- **Notes**: none

---

### `theorem ordAtInfty_algebraMap_crFrobEquiv`
- **Type**: `ord_∞^{mapped}(algebraMap (crFrobEquiv W u)) = ord_∞^{source}(algebraMap u)` for `u : CoordinateRing E_{K̄}`.
- **What**: The order at infinity of the algebraMap of `crFrobEquiv u` (viewed in the function field of the mapped curve) equals the order at infinity of the algebraMap of `u` in the original function field. This is the integral version of the ∞-transport.
- **How**: Case split on `u = 0` (trivial); nonzero case uses `ordAtInfty_algebraMap_coordinateRing` (`ord = -natDegree(N)`) on both sides, then `norm_crFrobEquiv` and `Polynomial.natDegree_map_eq_of_injective` (degree preserved by injective `e`).
- **Hypotheses**: `u : CoordinateRing E_{K̄}`
- **Uses from project**: `crFrobEquiv`, `norm_crFrobEquiv`, `SmoothPlaneCurve.ordAtInfty_algebraMap_coordinateRing`, `SmoothPlaneCurve.ordAtInfty_zero`
- **Used by**: `ordAtInfty_ffFrobEquivRaw`
- **Visibility**: public
- **Lines**: 202–222, proof ~20 lines
- **Notes**: none

---

### `theorem ordAtInfty_ffFrobEquivRaw`
- **Type**: `ord_∞^{mapped}(ffFrobEquivRaw W z) = ord_∞^{source}(z)` for `z : K̄(E)`.
- **What**: The order at infinity of the raw Frobenius image `σ_raw z` (on the mapped curve) equals the order at infinity of `z` — the ∞-transport for `ffFrobEquivRaw`.
- **How**: Case split on `z = 0`; general case: write `z = algebraMap u / algebraMap v` via `IsFractionRing.div_surjective`, use `ordAtInfty_div_eq_mul_inv` and `ordAtInfty_inv` to decompose, unpack `ffFrobEquivRaw = IsFractionRing.ringEquivOfRingEquiv crFrobEquiv` via `IsFractionRing.ringEquivOfRingEquiv_algebraMap`, then apply `ordAtInfty_algebraMap_crFrobEquiv` twice.
- **Hypotheses**: `z : K̄(E)`
- **Uses from project**: `ffFrobEquivRaw`, `crFrobEquiv`, `ordAtInfty_algebraMap_crFrobEquiv`, `SmoothPlaneCurve.ordAtInfty_div_eq_mul_inv`, `SmoothPlaneCurve.ordAtInfty_inv`, `SmoothPlaneCurve.ordAtInfty_zero`
- **Used by**: `ordAtInfty_frobeniusFunctionFieldEquiv`
- **Visibility**: public
- **Lines**: 228–266, proof ~32 lines
- **Notes**: Proof >30 lines. The case analysis and repeated nonzero-ness witnesses make this proof longer than the mathematical content requires.

---

### `theorem ordAtInfty_frobeniusFunctionFieldEquiv`
- **Type**: `ord_∞(frobeniusFunctionFieldEquiv W g) = ord_∞(g)` for `g : K̄(E)`.
- **What**: The arithmetic Frobenius fixes the place at infinity: the order at ∞ is unchanged.
- **How**: Unfolds `frobeniusFunctionFieldEquiv = ffFrobCast ∘ ffFrobEquivRaw`, applies `ordAtInfty_ringEquivCast` (cast bridge) and `ordAtInfty_ffFrobEquivRaw`.
- **Hypotheses**: none beyond ambient
- **Uses from project**: `frobeniusFunctionFieldEquiv`, `ffFrobCast`, `ordAtInfty_ringEquivCast`, `map_coeffFrobEquiv_eq`, `ordAtInfty_ffFrobEquivRaw`
- **Used by**: `projectiveDivisorOf_frobeniusFunctionFieldEquiv_weilFunction`
- **Visibility**: public
- **Lines**: 271–278, proof ~6 lines
- **Notes**: none

---

### `noncomputable def geomFrobSmoothPointInv`
- **Type**: `(SmoothPoint E_{K̄}) → (SmoothPoint E_{K̄})` — the point with coordinates `(e⁻¹ P.x, e⁻¹ P.y)`.
- **What**: Constructs the "inverse Frobenius" of a smooth point: applies `(frobeniusAlgEquivOfAlgebraic).symm` to both coordinates. This is the unique `Q` with `π̄(Q) = P`.
- **How**: Nonsingularity of the new coordinates follows from `WeierstrassCurve.Affine.baseChange_nonsingular` applied to the injective Frobenius inverse.
- **Hypotheses**: `IsElliptic` on `E_{K̄}`
- **Uses from project**: `WeierstrassCurve.Affine.baseChange_nonsingular`
- **Used by**: `coeffFrobEquiv_geomFrobSmoothPointInv_x`, `coeffFrobEquiv_geomFrobSmoothPointInv_y`, `geomFrobeniusPointFun_geomFrobSmoothPointInv`, `ord_P_frobeniusFunctionFieldEquiv`, `pullbackDiv_geomFrobInv_eq`, `projectiveDivisorOf_frobeniusFunctionFieldEquiv_weilFunction` (indirectly)
- **Visibility**: public
- **Lines**: 287–298, body ~11 lines
- **Notes**: none

---

### `@[simp] theorem coeffFrobEquiv_geomFrobSmoothPointInv_x`
- **Type**: `e ((geomFrobSmoothPointInv W P).x) = P.x`
- **What**: The Frobenius `e` of the inverse-Frobenius x-coordinate is `P.x` (apply-symm-apply).
- **How**: `AlgEquiv.apply_symm_apply`.
- **Hypotheses**: none
- **Uses from project**: `geomFrobSmoothPointInv`
- **Used by**: `ord_P_frobeniusFunctionFieldEquiv`
- **Visibility**: public (`@[simp]`)
- **Lines**: 300–306, proof ~5 lines
- **Notes**: none

---

### `@[simp] theorem coeffFrobEquiv_geomFrobSmoothPointInv_y`
- **Type**: `e ((geomFrobSmoothPointInv W P).y) = P.y`
- **What**: The Frobenius `e` of the inverse-Frobenius y-coordinate is `P.y` (apply-symm-apply).
- **How**: `AlgEquiv.apply_symm_apply`.
- **Hypotheses**: none
- **Uses from project**: `geomFrobSmoothPointInv`
- **Used by**: `ord_P_frobeniusFunctionFieldEquiv`
- **Visibility**: public (`@[simp]`)
- **Lines**: 308–314, proof ~5 lines
- **Notes**: none

---

### `theorem geomFrobeniusPointFun_geomFrobSmoothPointInv`
- **Type**: `π̄ ((geomFrobSmoothPointInv W P).toAffinePoint) = P.toAffinePoint`
- **What**: At the affine-point level, applying the geometric Frobenius to the inverse-Frobenius point recovers the original point.
- **How**: `HasseWeil.geomFrobeniusPointFun_some` unrolls the point map; then `Affine.Point.some.injEq` reduces to x/y components, each closed by unfolding `frobeniusAlgHom = frobeniusAlgEquivOfAlgebraic` and `AlgEquiv.apply_symm_apply`.
- **Hypotheses**: none
- **Uses from project**: `geomFrobSmoothPointInv`, `HasseWeil.geomFrobeniusPointFun_some`, `HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint_def`
- **Used by**: `pullbackDiv_geomFrobInv_eq`
- **Visibility**: public
- **Lines**: 318–346, proof ~28 lines
- **Notes**: none

---

### `theorem geomFrobeniusPointFun_injective`
- **Type**: `Function.Injective (HasseWeil.geomFrobeniusPointFun W)`
- **What**: The geometric Frobenius point-map `π̄` is injective (as `Point.map` of the injective field Frobenius).
- **How**: `WeierstrassCurve.Affine.Point.map_injective` applied to `frobeniusAlgHom`.
- **Hypotheses**: none
- **Uses from project**: `WeierstrassCurve.Affine.Point.map_injective`
- **Used by**: `pullbackDiv_geomFrobInv_eq`, `pullbackDiv_geomFrob_infinity`
- **Visibility**: public
- **Lines**: 349–352, proof 2 lines
- **Notes**: none

---

### `theorem pullbackDiv_geomFrobInv_eq`
- **Type**: For affine smooth point `P`, `ℓ : ℤ` nonzero in `K̄`, and torsion point `T`, the fibre-divisor coefficient `pullbackDiv [ℓ] (π̄T) P = pullbackDiv [ℓ] T (geomFrobSmoothPointInv W P)`.
- **What**: The combinatorial heart of σ-naturality (affine case): the count of ℓ-torsion fibres of `π̄T` over `P` equals the count of ℓ-torsion fibres of `T` over `π̄⁻¹P`, because `[ℓ]P = π̄T ↔ [ℓ](π̄⁻¹P) = T` by Frobenius equivariance of `[ℓ]` and injectivity of `π̄`.
- **How**: Unfolds `pullbackDiv_apply`, reduces `[ℓ]_` to `ℓ • _` via `mulByInt_apply`, then proves the `iff` using `geomFrobeniusPointFun_geomFrobSmoothPointInv` and `geomFrobeniusPointFun_injective` in both directions, plus `map_zsmul` to commute ℓ-multiplication with `geomFrobeniusPointFun`.
- **Hypotheses**: `(ℓ : K̄) ≠ 0` (kernel finiteness), `T : E_{K̄}.Point`, `P : SmoothPoint E_{K̄}`
- **Uses from project**: `geomFrobSmoothPointInv`, `geomFrobeniusPointFun_geomFrobSmoothPointInv`, `geomFrobeniusPointFun_injective`, `HasseWeil.geomFrobeniusPoint_apply`, `pullbackDiv_apply`, `mulByInt_apply`, `mulByInt_ker_finite`, `HasseWeil.Curves.ProjectiveSmoothPoint.toAffinePoint_affine`, `geomFrobeniusPoint_apply`
- **Used by**: `projectiveDivisorOf_frobeniusFunctionFieldEquiv_weilFunction`
- **Visibility**: public
- **Lines**: 364–398, proof ~34 lines
- **Notes**: Proof >30 lines.

---

### `theorem pullbackDiv_geomFrob_infinity`
- **Type**: `pullbackDiv [ℓ] (π̄T) ∞ = pullbackDiv [ℓ] T ∞`
- **What**: The fibre-divisor coefficient at infinity is the same for `π̄T` and `T`, because both equal "indicator of `0 = Q`" and `π̄` is injective with `π̄ 0 = 0`.
- **How**: Unfolds `pullbackDiv_apply`, reduces ∞-point to `0` via `rfl`, applies `propext` and `eq_comm` to symmetrize, then uses `geomFrobeniusPointFun_injective` and `map_zero` in both iff directions.
- **Hypotheses**: `(ℓ : K̄) ≠ 0`
- **Uses from project**: `geomFrobeniusPointFun_injective`, `pullbackDiv_apply`, `geomFrobeniusPoint_apply`, `mulByInt_ker_finite`
- **Used by**: `projectiveDivisorOf_frobeniusFunctionFieldEquiv_weilFunction`
- **Visibility**: public
- **Lines**: 402–424, proof ~22 lines
- **Notes**: none

---

### `theorem ord_P_frobeniusFunctionFieldEquiv`
- **Type**: `ord_P P (frobeniusFunctionFieldEquiv W g) = ord_P (geomFrobSmoothPointInv W P) g`
- **What**: Restates the affine order transport with `Q` specialized to `geomFrobSmoothPointInv W P` (so `P.x = e Q.x`), providing a direct "inverse-Frobenius" form ready for the divisor comparison.
- **How**: Unfolds `ord_P` and applies `pointValuation_frobeniusFunctionFieldEquiv` with `hPx = coeffFrobEquiv_geomFrobSmoothPointInv_x.symm` and similarly for `y`.
- **Hypotheses**: `P : SmoothPoint E_{K̄}`, `g : K̄(E)`
- **Uses from project**: `geomFrobSmoothPointInv`, `pointValuation_frobeniusFunctionFieldEquiv`, `coeffFrobEquiv_geomFrobSmoothPointInv_x`, `coeffFrobEquiv_geomFrobSmoothPointInv_y`
- **Used by**: `projectiveDivisorOf_frobeniusFunctionFieldEquiv_weilFunction`
- **Visibility**: public
- **Lines**: 430–441, proof ~10 lines
- **Notes**: none

---

### `theorem projectiveDivisorOf_frobeniusFunctionFieldEquiv_weilFunction`
- **Type**: `div(frobeniusFunctionFieldEquiv W (g_T)) = div(g_{π̄T})` (as projective divisors on `E_{K̄}`).
- **What**: The divisor Galois descent for Weil functions: the divisor of `σ(g_T)` equals the divisor of `g_{π̄T}`. This is the heart of σ-naturality.
- **How**: Expands both divisors using `weilFunction_divisor` (writing them as `pullbackDiv [ℓ] T − pullbackDiv [ℓ] 0`); then compares place-by-place via `Finsupp.ext`: at ∞ uses `ordAtInfty_frobeniusFunctionFieldEquiv`; at each affine `P` uses `ord_P_frobeniusFunctionFieldEquiv` and rewrites fibre-divisor coefficients via `pullbackDiv_geomFrobInv_eq` (and `pullbackDiv_geomFrob_infinity` for the base-point `0` term, using `geomFrobeniusPoint W 0 = 0`).
- **Hypotheses**: `(ℓ : K̄) ≠ 0`, `ℓ • T = 0`, `ℓ • π̄T = 0`
- **Uses from project**: `frobeniusFunctionFieldEquiv`, `weilFunction`, `weilFunction_divisor`, `pullbackDiv`, `mulByInt_ker_finite`, `ordAtInfty_frobeniusFunctionFieldEquiv`, `ord_P_frobeniusFunctionFieldEquiv`, `pullbackDiv_geomFrobInv_eq`, `pullbackDiv_geomFrob_infinity`, `HasseWeil.geomFrobeniusPoint`, `SmoothPlaneCurve.projectiveDivisorOf_apply_infinity`, `SmoothPlaneCurve.projectiveDivisorOf_apply_affine`
- **Used by**: `frobeniusFunctionFieldEquiv_weilFunction_eq_smul`
- **Visibility**: public
- **Lines**: 448–499, proof ~41 lines
- **Notes**: Proof >30 lines (51 total declaration lines).

---

### `theorem frobeniusFunctionFieldEquiv_weilFunction_eq_smul`
- **Type**: There exists `c : K̄` with `c ≠ 0` such that `σ(g_T) = (algebraMap c) * g_{π̄T}`.
- **What**: σ-naturality of the Weil function (Silverman III.8.1, second geometric fact): `σ g_T` and `g_{π̄T}` differ by a nonzero scalar in `K̄`.
- **How**: Both functions are nonzero (via `weilFunction_ne_zero` and injectivity of σ); their ratio `σ(g_T)/g_{π̄T}` has trivial projective divisor (using `projectiveDivisorOf_mul`, `projectiveDivisorOf_inv`, and `projectiveDivisorOf_frobeniusFunctionFieldEquiv_weilFunction`); therefore `const_unit_of_projectiveDivisorOf_eq_zero` yields the scalar `c`.
- **Hypotheses**: `(ℓ : K̄) ≠ 0`, `ℓ • T = 0`, `ℓ • π̄T = 0`
- **Uses from project**: `frobeniusFunctionFieldEquiv`, `weilFunction`, `weilFunction_ne_zero`, `projectiveDivisorOf_frobeniusFunctionFieldEquiv_weilFunction`, `SmoothPlaneCurve.projectiveDivisorOf_mul`, `SmoothPlaneCurve.projectiveDivisorOf_inv`, `const_unit_of_projectiveDivisorOf_eq_zero`
- **Used by**: unused in file (likely called from other files in the Galois descent chain)
- **Visibility**: public
- **Lines**: 505–538, proof ~23 lines
- **Notes**: none

---

## Summary statistics

| Kind | Count |
|------|-------|
| `noncomputable def` | 2 |
| `noncomputable local instance` | 1 |
| `theorem` | 16 |
| `instance` | 0 |
| **Total** | **19** |

**Sorries**: none.

**`set_option maxHeartbeats`**: one occurrence at line 101 (`1000000`, NO-COMMENT — no justifying comment present), covering `pointValuation_frobeniusFunctionFieldEquiv`.

**Long proofs (>30 lines)**:
- `pointValuation_frobeniusFunctionFieldEquiv`: ~33 proof lines
- `ordAtInfty_ffFrobEquivRaw`: ~32 proof lines
- `pullbackDiv_geomFrobInv_eq`: ~34 proof lines
- `projectiveDivisorOf_frobeniusFunctionFieldEquiv_weilFunction`: ~41 proof lines

**Key API** (used by 3+ declarations in this file):
- `crFrobEquiv` — used by `map_maximalIdealAt_crFrobEquiv`, `crFrobEquiv_smul_basis`, `norm_crFrobEquiv`, `ordAtInfty_algebraMap_crFrobEquiv`, `ordAtInfty_ffFrobEquivRaw`, `pointValuation_frobeniusFunctionFieldEquiv`
- `geomFrobSmoothPointInv` — used by simp lemmas, `geomFrobeniusPointFun_geomFrobSmoothPointInv`, `ord_P_frobeniusFunctionFieldEquiv`, `pullbackDiv_geomFrobInv_eq`
- `map_coeffFrobEquiv_eq` — used by `pointOnMapped`, `pointValuation_frobeniusFunctionFieldEquiv`, `ordAtInfty_frobeniusFunctionFieldEquiv`
- `pointValuation_frobeniusFunctionFieldEquiv` — used by `ord_P_frobeniusFunctionFieldEquiv`, `projectiveDivisorOf_frobeniusFunctionFieldEquiv_weilFunction` (indirectly)
- `pointOnMapped` — used by `pointOnMapped_x`, `pointOnMapped_y`, `pointValuation_frobeniusFunctionFieldEquiv`

**Unused in file** (no in-file callers, likely consumed by other files):
- `frobeniusFunctionFieldEquiv_weilFunction_eq_smul` — the top-level σ-naturality result; exported for the Galois geometric facts (`FrobeniusGaloisGeometric`).
- `crFrobEquiv_smul_basis` — helper used only by `norm_crFrobEquiv`; `norm_crFrobEquiv` itself only used by `ordAtInfty_algebraMap_crFrobEquiv`; both are internal steppingstones.
