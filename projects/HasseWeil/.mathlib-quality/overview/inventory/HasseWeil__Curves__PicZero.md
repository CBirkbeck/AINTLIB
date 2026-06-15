# Inventory: ./HasseWeil/Curves/PicZero.lean

**File**: `HasseWeil/Curves/PicZero.lean`
**Total lines**: 364
**Imports**: `HasseWeil.Curves.ProjectiveDivisor`, `HasseWeil.Curves.PointFunctor`
**Total declarations**: 29 (7 defs, 21 theorems/lemmas, 1 instance)
**Sorries**: none
**set_option maxHeartbeats**: none

---

## Namespace `HasseWeil.Curves.ProjectiveSmoothPoint` (lines 37–60)

### `noncomputable def toAffinePoint`
- **Type**: `ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F) → W.Point`
- **What**: Converts a projective smooth point to a mathlib `Affine.Point`: infinity maps to `0`, an affine smooth point maps via `SmoothPlaneCurve.SmoothPoint.toAffinePoint`.
- **How**: Pattern match on `ProjectiveSmoothPoint` constructors; `infinity ↦ 0` by case, `affine Q ↦ Q.toAffinePoint` by case.
- **Hypotheses**: `W : WeierstrassCurve.Affine F`, `[Field F]`
- **Uses from project**: `SmoothPlaneCurve.SmoothPoint.toAffinePoint` (from `PointFunctor`)
- **Used by**: `toAffinePoint_infinity`, `toAffinePoint_affine`, `projectiveDivisorSum`, `projectiveDivisorSum_kappaDivisor`, `projectiveDivisorSum_vertical_line`, `equivProjectiveSmoothPoint`
- **Visibility**: public
- **Lines**: 44–49, proof length 6 lines
- **Notes**: None

### `theorem toAffinePoint_infinity`
- **Type**: `(ProjectiveSmoothPoint.infinity : ProjectiveSmoothPoint ⟨W⟩).toAffinePoint = (0 : W.Point)`
- **What**: The point at infinity converts to the group identity in `W.Point`.
- **How**: `rfl` (definitionally true by the match arm).
- **Hypotheses**: `W : WeierstrassCurve.Affine F`
- **Uses from project**: `toAffinePoint`
- **Used by**: `projectiveDivisorSum_kappaDivisor`, `projectiveDivisorSum_vertical_line`
- **Visibility**: public (`@[simp]`)
- **Lines**: 51–54, proof length 1 line
- **Notes**: None

### `theorem toAffinePoint_affine`
- **Type**: `(ProjectiveSmoothPoint.affine Q).toAffinePoint = Q.toAffinePoint`
- **What**: The affine constructor unfolding: `affine Q` maps to `Q.toAffinePoint`.
- **How**: `rfl`.
- **Hypotheses**: `W : WeierstrassCurve.Affine F`, `Q : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint`
- **Uses from project**: `toAffinePoint`
- **Used by**: unused in file (exported for callers)
- **Visibility**: public (`@[simp]`)
- **Lines**: 56–58, proof length 1 line
- **Notes**: None

---

## Namespace `HasseWeil.Curves` — σ map (lines 64–124)

### `noncomputable def projectiveDivisorSum`
- **Type**: `ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F) → W.Point`
- **What**: The Silverman III.3.4 "sum-of-points" map σ: sends `Σ nᵢ (Pᵢ)` to `Σ nᵢ • Pᵢ` in the elliptic-curve group, with infinity contributing `0`.
- **How**: Defined via `Finsupp.sum`, applying `n • P.toAffinePoint` for each place-multiplicity pair.
- **Hypotheses**: `[DecidableEq F]`, `W : WeierstrassCurve.Affine F`, `[W.IsElliptic]`
- **Uses from project**: `ProjectiveSmoothPoint.toAffinePoint`, `ProjectiveDivisor` (Finsupp)
- **Used by**: `projectiveDivisorSum_zero`, `projectiveDivisorSum_single`, `projectiveDivisorSum_add`, `projectiveDivisorSumHom`, `projectiveDivisorSumHom_apply`, `projectiveDivisorSum_neg`, `projectiveDivisorSum_sub`, `projectiveDivisorSum_zsmul`, `projectiveDivisorSum_kappaDivisor`, `projectiveDivisorSum_projectiveDivisorOf_one`, `projectiveDivisorSum_projectiveDivisorOf_mul`, `projectiveDivisorSum_projectiveDivisorOf_inv`, `projectiveDivisorSum_vertical_line`
- **Visibility**: public
- **Lines**: 72–74, definition body 3 lines
- **Notes**: Key API — used by essentially every downstream declaration in this file and heavily by external files.

### `theorem projectiveDivisorSum_zero`
- **Type**: `projectiveDivisorSum W 0 = 0`
- **What**: σ of the zero divisor is the group identity.
- **How**: `simp [projectiveDivisorSum]` unfolds `Finsupp.sum` on zero.
- **Hypotheses**: as for `projectiveDivisorSum`
- **Uses from project**: `projectiveDivisorSum`
- **Used by**: `projectiveDivisorSumHom` (map_zero' field)
- **Visibility**: public (`@[simp]`)
- **Lines**: 76–79, proof 2 lines

### `theorem projectiveDivisorSum_single`
- **Type**: `projectiveDivisorSum W (Finsupp.single P n) = n • P.toAffinePoint`
- **What**: σ on a single-point divisor `n·(P)` gives `n • P` in the group.
- **How**: Unfolds via `Finsupp.sum_single_index` with the zero-case `zero_zsmul`.
- **Hypotheses**: as for `projectiveDivisorSum`
- **Uses from project**: `projectiveDivisorSum`, `toAffinePoint`
- **Used by**: `projectiveDivisorSum_kappaDivisor`, `projectiveDivisorSum_vertical_line`
- **Visibility**: public (`@[simp]`)
- **Lines**: 80–85, proof 3 lines

### `theorem projectiveDivisorSum_add`
- **Type**: `projectiveDivisorSum W (D₁ + D₂) = projectiveDivisorSum W D₁ + projectiveDivisorSum W D₂`
- **What**: σ is additive: it distributes over divisor addition.
- **How**: `Finsupp.sum_add_index'` with zero and add side conditions `zero_zsmul`/`add_zsmul`.
- **Hypotheses**: as for `projectiveDivisorSum`
- **Uses from project**: `projectiveDivisorSum`, `toAffinePoint`
- **Used by**: `projectiveDivisorSumHom` (map_add' field)
- **Visibility**: public (`@[simp]`)
- **Lines**: 87–94, proof 5 lines

### `noncomputable def projectiveDivisorSumHom`
- **Type**: `ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F) →+ W.Point`
- **What**: Bundles σ as an `AddMonoidHom` to inherit `map_neg`, `map_sub`, `map_zsmul` for free.
- **How**: Structure fields filled by `projectiveDivisorSum_zero` and `projectiveDivisorSum_add`.
- **Hypotheses**: as for `projectiveDivisorSum`
- **Uses from project**: `projectiveDivisorSum`, `projectiveDivisorSum_zero`, `projectiveDivisorSum_add`
- **Used by**: `projectiveDivisorSumHom_apply`, `projectiveDivisorSum_neg`, `projectiveDivisorSum_sub`, `projectiveDivisorSum_zsmul`
- **Visibility**: public
- **Lines**: 99–103, definition body 5 lines

### `theorem projectiveDivisorSumHom_apply`
- **Type**: `projectiveDivisorSumHom W D = projectiveDivisorSum W D`
- **What**: The `@[simp]` unfolding lemma for the bundled hom.
- **How**: `rfl`.
- **Hypotheses**: as for `projectiveDivisorSum`
- **Uses from project**: `projectiveDivisorSumHom`, `projectiveDivisorSum`
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 105–107, proof 1 line

### `theorem projectiveDivisorSum_neg`
- **Type**: `projectiveDivisorSum W (-D) = -(projectiveDivisorSum W D)`
- **What**: σ commutes with negation.
- **How**: Delegates to `projectiveDivisorSumHom W .map_neg`.
- **Uses from project**: `projectiveDivisorSumHom`
- **Used by**: `projectiveDivisorSum_projectiveDivisorOf_inv`
- **Visibility**: public (`@[simp]`)
- **Lines**: 109–112, proof 2 lines

### `theorem projectiveDivisorSum_sub`
- **Type**: `projectiveDivisorSum W (D₁ - D₂) = projectiveDivisorSum W D₁ - projectiveDivisorSum W D₂`
- **What**: σ distributes over divisor subtraction.
- **How**: Delegates to `projectiveDivisorSumHom W .map_sub`.
- **Uses from project**: `projectiveDivisorSumHom`
- **Used by**: `projectiveDivisorSum_kappaDivisor`
- **Visibility**: public (`@[simp]`)
- **Lines**: 114–118, proof 2 lines

### `theorem projectiveDivisorSum_zsmul`
- **Type**: `projectiveDivisorSum W (n • D) = n • projectiveDivisorSum W D`
- **What**: σ is compatible with integer scalar multiplication.
- **How**: Delegates to `projectiveDivisorSumHom W .map_zsmul`.
- **Uses from project**: `projectiveDivisorSumHom`
- **Used by**: `projectiveDivisorSum_vertical_line`
- **Visibility**: public
- **Lines**: 120–123, proof 2 lines

---

## Namespace `WeierstrassCurve.Affine.Point` — κ direction bridge (lines 129–179)

### `noncomputable def toProjectiveSmoothPoint`
- **Type**: `W.Point → HasseWeil.Curves.ProjectiveSmoothPoint (⟨W⟩ : HasseWeil.Curves.SmoothPlaneCurve F)`
- **What**: Sends a mathlib `Affine.Point` to the corresponding `ProjectiveSmoothPoint`: `0 ↦ infinity`, `some x y h ↦ affine ⟨x, y, h⟩`. Inverse to `ProjectiveSmoothPoint.toAffinePoint`.
- **How**: Pattern match on `Point` constructors.
- **Hypotheses**: `{W : WeierstrassCurve.Affine F}`, `[Field F]`
- **Uses from project**: none (uses only mathlib `W.Point` constructors)
- **Used by**: `toProjectiveSmoothPoint_zero`, `toProjectiveSmoothPoint_some`, `toProjectiveSmoothPoint_toAffinePoint`, `toAffinePoint_toProjectiveSmoothPoint`, `equivProjectiveSmoothPoint`, `kappaDivisor`, `projectiveDivisorSum_kappaDivisor`, `projectiveDivisorSum_vertical_line`
- **Visibility**: public
- **Lines**: 136–141, definition body 4 lines

### `theorem toProjectiveSmoothPoint_zero`
- **Type**: `(0 : W.Point).toProjectiveSmoothPoint = HasseWeil.Curves.ProjectiveSmoothPoint.infinity`
- **What**: The group identity maps to the point at infinity.
- **How**: `rfl`.
- **Uses from project**: `toProjectiveSmoothPoint`
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 143–145, proof 1 line

### `theorem toProjectiveSmoothPoint_some`
- **Type**: `(Point.some x y h).toProjectiveSmoothPoint = .affine ⟨x, y, h⟩`
- **What**: An affine point maps to the `affine` constructor.
- **How**: `rfl`.
- **Uses from project**: `toProjectiveSmoothPoint`
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 147–149, proof 1 line

### `theorem toProjectiveSmoothPoint_toAffinePoint`
- **Type**: `P.toProjectiveSmoothPoint.toAffinePoint = P`
- **What**: Round-trip: pushing then pulling back recovers the original `Affine.Point`.
- **How**: Cases on `P` (`zero` and `some`), both by `rfl`.
- **Uses from project**: `toProjectiveSmoothPoint`, `toAffinePoint`
- **Used by**: `equivProjectiveSmoothPoint` (left_inv field)
- **Visibility**: public (`@[simp]`)
- **Lines**: 153–157, proof 4 lines

### `theorem toAffinePoint_toProjectiveSmoothPoint`
- **Type**: `P.toAffinePoint.toProjectiveSmoothPoint = P` (for `P : ProjectiveSmoothPoint`)
- **What**: Round-trip in the other direction: pulling then pushing back recovers the original projective smooth point.
- **How**: Cases on `P` (`infinity` and `affine`), both by `rfl`.
- **Uses from project**: `toAffinePoint`, `toProjectiveSmoothPoint`
- **Used by**: `equivProjectiveSmoothPoint` (right_inv field)
- **Visibility**: public (`@[simp]`)
- **Lines**: 161–167, proof 4 lines

### `noncomputable def equivProjectiveSmoothPoint`
- **Type**: `W.Point ≃ HasseWeil.Curves.ProjectiveSmoothPoint (⟨W⟩ : HasseWeil.Curves.SmoothPlaneCurve F)`
- **What**: The canonical equivalence between mathlib's `Affine.Point` and the project's `ProjectiveSmoothPoint`, with `0 ↔ infinity` and `some x y h ↔ affine ⟨x, y, h⟩`.
- **How**: Packages `toProjectiveSmoothPoint` / `toAffinePoint` as `Equiv`, using the two round-trip lemmas as `left_inv` / `right_inv`.
- **Hypotheses**: `{W : WeierstrassCurve.Affine F}`, `[Field F]`
- **Uses from project**: `toProjectiveSmoothPoint`, `toAffinePoint`, `toProjectiveSmoothPoint_toAffinePoint`, `toAffinePoint_toProjectiveSmoothPoint`
- **Used by**: `fintype`, `card_eq_card_affine_point`
- **Visibility**: public
- **Lines**: 171–178, definition body 8 lines
- **Notes**: Largely superseded by `HasseWeil.Affine.Point.equivProjectiveSmoothPoint` in `FintypeProjectiveSmoothPoint.lean` (which covers the more general `W : WeierstrassCurve F`). Suspected duplication.

---

## Namespace `HasseWeil.Curves.ProjectiveSmoothPoint` — Fintype (lines 190–216)

### `noncomputable instance fintype`
- **Type**: `[Fintype W.Point] → Fintype (ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F))`
- **What**: Derives a `Fintype` instance for `ProjectiveSmoothPoint` from the existing `Fintype W.Point` via the bijection `equivProjectiveSmoothPoint`.
- **How**: `Fintype.ofEquiv W.Point equivProjectiveSmoothPoint`.
- **Hypotheses**: `{W : WeierstrassCurve.Affine F}`, `[Field F]`, `[Fintype W.Point]`
- **Uses from project**: `equivProjectiveSmoothPoint`
- **Used by**: unused in file (externally by `L6Witnesses.lean` and others via `FintypeProjectiveSmoothPoint.lean`)
- **Visibility**: public
- **Lines**: 198–201, definition body 2 lines
- **Notes**: Superseded by `instFintypeProjectiveSmoothPoint` in `FintypeProjectiveSmoothPoint.lean`.

### `theorem card_eq_card_affine_point`
- **Type**: `Fintype.card (ProjectiveSmoothPoint (⟨W⟩ : SmoothPlaneCurve F)) = Fintype.card W.Point`
- **What**: The cardinality of `ProjectiveSmoothPoint` equals that of `W.Point` (no `+1` since the basepoint is included on both sides).
- **How**: `Fintype.card_congr equivProjectiveSmoothPoint.symm`.
- **Hypotheses**: `{W : WeierstrassCurve.Affine F}`, `[Field F]`, `[Fintype W.Point]`
- **Uses from project**: `equivProjectiveSmoothPoint`
- **Used by**: externally by `L6Witnesses.lean`; unused within this file
- **Visibility**: public
- **Lines**: 209–214, proof 2 lines
- **Notes**: Companion to `Fintype.card_projectiveSmoothPoint_eq_pointCount` in `FintypeProjectiveSmoothPoint.lean`.

---

## Namespace `HasseWeil.Curves` — κ map and σ∘κ (lines 219–363)

### `noncomputable def kappaDivisor`
- **Type**: `W.Point → ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)`
- **What**: The divisor `(P) − (O)` as an element of `ProjectiveDivisor`: the Finsupp difference `single(P.toProjectiveSmoothPoint, 1) − single(∞, 1)`.
- **How**: Finsupp subtraction of two single-point divisors.
- **Hypotheses**: `[DecidableEq F]`, `W : WeierstrassCurve.Affine F`, `[W.IsElliptic]`
- **Uses from project**: `toProjectiveSmoothPoint`, `ProjectiveSmoothPoint.infinity`
- **Used by**: `kappaDivisor_degree`, `picZeroOfPoint`, `picZeroOfPoint_zero`, `projectiveDivisorSum_kappaDivisor`
- **Visibility**: public
- **Lines**: 227–230, definition body 4 lines

### `theorem kappaDivisor_degree`
- **Type**: `ProjectiveDivisor.degree (kappaDivisor W P) = 0`
- **What**: The κ-divisor `(P) − (O)` has degree zero.
- **How**: Unfolds `kappaDivisor`, applies `ProjectiveDivisor.degree_sub` and `Finsupp.sum_single_index`, finishes by `ring`.
- **Hypotheses**: as for `kappaDivisor`
- **Uses from project**: `kappaDivisor`, `ProjectiveDivisor.degree`, `ProjectiveDivisor.degree_sub`
- **Used by**: `picZeroOfPoint`
- **Visibility**: public
- **Lines**: 232–244, proof 13 lines

### `noncomputable def picZeroOfPoint`
- **Type**: `W.Point → SmoothPlaneCurve.PicProj₀ (⟨W⟩ : SmoothPlaneCurve F)`
- **What**: The κ map of Silverman III.3.4(d): sends `P` to the class of `(P) − (O)` in `Pic⁰(E)`.
- **How**: `QuotientAddGroup.mk` applied to the subtype element `⟨kappaDivisor W P, _⟩` using `kappaDivisor_degree` for the degree-zero membership proof.
- **Hypotheses**: as for `kappaDivisor`, plus `ProjectiveDivisor.mem_degZero`
- **Uses from project**: `kappaDivisor`, `kappaDivisor_degree`, `ProjectiveDivisor.mem_degZero`
- **Used by**: `picZeroOfPoint_zero`, `projectiveDivisorSum_kappaDivisor` (implicitly via κ definition)
- **Visibility**: public
- **Lines**: 249–252, definition body 4 lines

### `theorem picZeroOfPoint_zero`
- **Type**: `picZeroOfPoint W (0 : W.Point) = 0`
- **What**: κ sends the base point to the zero class: `(O) − (O) = 0` in `Pic⁰(E)`.
- **How**: Shows `kappaDivisor W 0 = 0` (as `∞ − ∞ = 0`), lifts to a subtype equality by `Subtype.ext`, then applies `QuotientAddGroup.mk_zero`.
- **Hypotheses**: as for `picZeroOfPoint`
- **Uses from project**: `picZeroOfPoint`, `kappaDivisor`, `kappaDivisor_degree`, `ProjectiveDivisor.mem_degZero`
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 255–271, proof 17 lines

### `theorem projectiveDivisorSum_kappaDivisor`
- **Type**: `projectiveDivisorSum W (kappaDivisor W P) = P`
- **What**: σ∘κ = id at the divisor level: applying the σ-map to the κ-divisor of P recovers P. This is the easy direction of the Silverman III.3.4 bijection.
- **How**: Unfolds κ, applies `projectiveDivisorSum_sub` and `projectiveDivisorSum_single` twice, uses `toAffinePoint_infinity` to reduce to `P.toProjectiveSmoothPoint.toAffinePoint = P`, settled by cases on `P`.
- **Hypotheses**: as for `projectiveDivisorSum`
- **Uses from project**: `kappaDivisor`, `projectiveDivisorSum`, `projectiveDivisorSum_sub`, `projectiveDivisorSum_single`, `toAffinePoint_infinity`, `toProjectiveSmoothPoint`
- **Used by**: unused in file; externally by `HomProperty.lean`, `RouteCTheoremOfSquareDiv.lean`, `RouteCAddFormula.lean`, `PicDualDivisorClassLemma.lean`, `SeparableScaling.lean`, `PairingNondeg.lean`
- **Visibility**: public (`@[simp]`)
- **Lines**: 279–291, proof 13 lines
- **Notes**: Key exported lemma used across the Weil-pairing pipeline.

### `theorem projectiveDivisorSum_projectiveDivisorOf_one`
- **Type**: `projectiveDivisorSum W ((⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf 1) = 0`
- **What**: σ vanishes on the principal divisor of the constant function 1 (which is the zero divisor).
- **How**: Rewrites via `SmoothPlaneCurve.projectiveDivisorOf_one` then `projectiveDivisorSum_zero`.
- **Uses from project**: `projectiveDivisorSum`, `projectiveDivisorSum_zero`, `SmoothPlaneCurve.projectiveDivisorOf_one`
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 302–306, proof 3 lines

### `theorem projectiveDivisorSum_projectiveDivisorOf_mul`
- **Type**: `projectiveDivisorSum W (projectiveDivisorOf (f * g)) = projectiveDivisorSum W (projectiveDivisorOf f) + projectiveDivisorSum W (projectiveDivisorOf g)` (for `f, g ≠ 0`)
- **What**: σ∘div(−) is multiplicative-to-additive: vanishing on two factors implies vanishing on their product.
- **How**: `SmoothPlaneCurve.projectiveDivisorOf_mul hf hg` + `projectiveDivisorSum_add`.
- **Uses from project**: `projectiveDivisorSum`, `projectiveDivisorSum_add`, `SmoothPlaneCurve.projectiveDivisorOf_mul`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 310–320, proof 3 lines

### `theorem projectiveDivisorSum_projectiveDivisorOf_inv`
- **Type**: `projectiveDivisorSum W (projectiveDivisorOf f⁻¹) = -(projectiveDivisorSum W (projectiveDivisorOf f))` (for `f ≠ 0`)
- **What**: σ∘div(−) commutes with inversion (i.e., vanishing on `f` implies vanishing on `f⁻¹`).
- **How**: `SmoothPlaneCurve.projectiveDivisorOf_inv hf` + `projectiveDivisorSum_neg`.
- **Uses from project**: `projectiveDivisorSum`, `projectiveDivisorSum_neg`, `SmoothPlaneCurve.projectiveDivisorOf_inv`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 324–331, proof 3 lines

### `theorem projectiveDivisorSum_vertical_line`
- **Type**: `projectiveDivisorSum W (single(P.toProjectiveSmoothPoint, 1) + single((-P).toProjectiveSmoothPoint, 1) - 2·single(∞, 1)) = 0`
- **What**: σ vanishes on the divisor `(P) + (−P) − 2·(∞)`, which is the divisor of any "vertical line" `x − x(P)` on the curve. Verified directly from `P + (−P) = 0` in `W.Point`.
- **How**: `simp` with `projectiveDivisorSum_sub`, `_add`, `_single`, `_zsmul`, `toAffinePoint_infinity`, then `add_neg_cancel P`.
- **Hypotheses**: as for `projectiveDivisorSum`
- **Uses from project**: `toProjectiveSmoothPoint`, `projectiveDivisorSum_sub`, `projectiveDivisorSum_add`, `projectiveDivisorSum_single`, `projectiveDivisorSum_zsmul`, `toAffinePoint_infinity`
- **Used by**: unused in file (externally referenced in `Miller.lean` as building block)
- **Visibility**: public
- **Lines**: 351–362, proof 9 lines

---

## Summary Statistics

| Kind | Count |
|------|-------|
| `noncomputable def` | 7 |
| `theorem`/`lemma` | 21 |
| `noncomputable instance` | 1 |
| **Total** | **29** |

**Sorries**: none  
**set_option maxHeartbeats**: none  
**Long proofs (>30 lines)**: none  

**Key API** (used by 3+ other declarations in this file):
- `toAffinePoint` — referenced by 6+ declarations
- `projectiveDivisorSum` — referenced by 13+ declarations  
- `projectiveDivisorSumHom` — referenced by 3 declarations (`_neg`, `_sub`, `_zsmul`)
- `toProjectiveSmoothPoint` — referenced by 7+ declarations
- `kappaDivisor` — referenced by 4 declarations

**Declarations unused within this file** (dead-code candidates, may be used by other files):
- `toAffinePoint_affine`
- `projectiveDivisorSumHom_apply`
- `toProjectiveSmoothPoint_zero`
- `toProjectiveSmoothPoint_some`
- `fintype`
- `card_eq_card_affine_point`
- `picZeroOfPoint_zero`
- `projectiveDivisorSum_projectiveDivisorOf_one`
- `projectiveDivisorSum_projectiveDivisorOf_mul`
- `projectiveDivisorSum_projectiveDivisorOf_inv`
- `projectiveDivisorSum_vertical_line`

**Notable duplication**: `equivProjectiveSmoothPoint`, `fintype`, and `card_eq_card_affine_point` in this file (for `W : WeierstrassCurve.Affine F`) are essentially superseded by the same declarations in `FintypeProjectiveSmoothPoint.lean` (for the more general `W : WeierstrassCurve F`). The latter imports PicZero and builds on top of `toProjectiveSmoothPoint`/`toAffinePoint`, but re-derives the Equiv and Fintype independently.
