# Inventory: ./HasseWeil/EC/TranslateLocalRing.lean

**File purpose**: Worker A's "Step (B'')" lifting bridges — characterising which function-field elements lift to the local ring `(W_smooth W).localRingAt P` by `pointValuation ≤ 1`. Separated from `EC/TranslationOrd.lean` to avoid parallel-edit collisions.

**Import**: `HasseWeil.EC.TranslationOrd` (the sole import).

**Total declarations**: 30 theorems, 0 defs, 0 instances, 0 abbrevs = **30 total**.

---

## Declarations

### `theorem x_gen_sub_const_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) (c : F) → ∃ u : (W_smooth W).localRingAt P, algebraMap ... u = x_gen W - algebraMap F KE c`
- **What**: The difference `x_gen − c` (constant `c : F`) lifts to the local ring at any smooth point `P`.
- **How**: Applies `mem_localRingAt_image_of_pointValuation_le_one`; the valuation bound follows from `Valuation.map_sub` (ultrametric triangle inequality) plus `pointValuation_x_gen_le_one` and `pointValuation_algebraMap_F_le_one`.
- **Hypotheses**: `W` is an elliptic Weierstrass curve over a field `F` with `DecidableEq`.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`, `pointValuation_x_gen_le_one`, `(W_smooth W).pointValuation_algebraMap_F_le_one`
- **Used by**: `xy_gen_sub_const_mem_localRingAt_image` (L70)
- **Visibility**: public
- **Lines**: 38–46, proof 5 lines
- **Notes**: none

---

### `theorem y_gen_sub_const_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) (c : F) → ∃ u : (W_smooth W).localRingAt P, algebraMap ... u = y_gen W - algebraMap F KE c`
- **What**: The difference `y_gen − c` lifts to the local ring at any smooth point `P`.
- **How**: Same structure as `x_gen_sub_const_mem_localRingAt_image`, using `pointValuation_y_gen_le_one` in place of the x bound.
- **Hypotheses**: Same as above.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`, `pointValuation_y_gen_le_one`, `(W_smooth W).pointValuation_algebraMap_F_le_one`
- **Used by**: `xy_gen_sub_const_mem_localRingAt_image` (L71)
- **Visibility**: public
- **Lines**: 50–58, proof 5 lines
- **Notes**: none

---

### `theorem xy_gen_sub_const_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) (c d : F) → (∃ u, algMap u = x_gen − c) ∧ (∃ v, algMap v = y_gen − d)`
- **What**: Both `x_gen − c` and `y_gen − d` lift simultaneously; a conjunction packaging the two previous results.
- **How**: Term-mode conjunction `⟨x_gen_sub_const_mem_localRingAt_image W P c, y_gen_sub_const_mem_localRingAt_image W P d⟩`.
- **Hypotheses**: Same as above.
- **Uses from project**: `x_gen_sub_const_mem_localRingAt_image`, `y_gen_sub_const_mem_localRingAt_image`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 62–71, proof 2 lines (term)
- **Notes**: Convenience bundling; not referenced elsewhere in the file.

---

### `theorem add_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) {f g : KE} → pV P f ≤ 1 → pV P g ≤ 1 → ∃ u, algMap u = f + g`
- **What**: If `f` and `g` individually lift to the local ring, so does their sum.
- **How**: `mem_localRingAt_image_of_pointValuation_le_one` + ultrametric `map_add` bound + `max_le`.
- **Hypotheses**: Both `f`, `g` have pointValuation ≤ 1.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`
- **Used by**: unused in file (used in `SamePlace.lean`, `TranslateValuation.lean` via the imported valuation lemmas, but not directly called in this file)
- **Visibility**: public
- **Lines**: 75–83, proof 3 lines
- **Notes**: none

---

### `theorem sub_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) {f g : KE} → pV P f ≤ 1 → pV P g ≤ 1 → ∃ u, algMap u = f - g`
- **What**: If `f` and `g` lift, so does their difference.
- **How**: Same pattern as `add_mem_localRingAt_image` with `map_sub`.
- **Hypotheses**: Both operands have pointValuation ≤ 1.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 87–95, proof 3 lines
- **Notes**: none

---

### `theorem mul_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) {f g : KE} → pV P f ≤ 1 → pV P g ≤ 1 → ∃ u, algMap u = f * g`
- **What**: If `f` and `g` lift, so does their product.
- **How**: `mem_localRingAt_image_of_pointValuation_le_one` + `Valuation.map_mul` + `mul_le_one'`.
- **Hypotheses**: Both operands have pointValuation ≤ 1.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 99–108, proof 3 lines
- **Notes**: none

---

### `theorem pow_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) {f : KE} → pV P f ≤ 1 → (n : ℕ) → ∃ u, algMap u = f ^ n`
- **What**: If `f` lifts, then `f ^ n` lifts for any natural number `n`.
- **How**: `mem_localRingAt_image_of_pointValuation_le_one` + `Valuation.map_pow` + `pow_le_one'`.
- **Hypotheses**: `f` has pointValuation ≤ 1.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`
- **Used by**: `x_gen_pow_mem_localRingAt_image` (L127), `y_gen_pow_mem_localRingAt_image` (L135)
- **Visibility**: public
- **Lines**: 111–119, proof 4 lines
- **Notes**: none

---

### `theorem x_gen_pow_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) (n : ℕ) → ∃ u, algMap u = x_gen W ^ n`
- **What**: Any power of `x_gen` lifts to the local ring at `P`.
- **How**: Term-mode application of `pow_mem_localRingAt_image` with `pointValuation_x_gen_le_one`.
- **Hypotheses**: none beyond curve hypotheses.
- **Uses from project**: `pow_mem_localRingAt_image`, `pointValuation_x_gen_le_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 122–127, proof 1 line (term)
- **Notes**: none

---

### `theorem y_gen_pow_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) (n : ℕ) → ∃ u, algMap u = y_gen W ^ n`
- **What**: Any power of `y_gen` lifts to the local ring at `P`.
- **How**: Term-mode application of `pow_mem_localRingAt_image` with `pointValuation_y_gen_le_one`.
- **Hypotheses**: none beyond curve hypotheses.
- **Uses from project**: `pow_mem_localRingAt_image`, `pointValuation_y_gen_le_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 130–135, proof 1 line (term)
- **Notes**: none

---

### `theorem x_gen_pow_mul_y_gen_pow_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) (m n : ℕ) → ∃ u, algMap u = x_gen W ^ m * y_gen W ^ n`
- **What**: Any monomial `x_gen^m * y_gen^n` lifts to the local ring at `P`.
- **How**: Applies `mem_localRingAt_image_of_pointValuation_le_one`; bounds via `map_mul` + `mul_le_one'`, with each factor bounded via `map_pow` + `pow_le_one'` from `pointValuation_x/y_gen_le_one`.
- **Hypotheses**: none beyond curve hypotheses.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`, `pointValuation_x_gen_le_one`, `pointValuation_y_gen_le_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 139–150, proof 8 lines
- **Notes**: none

---

### `theorem algebraMap_F_mul_x_gen_pow_mul_y_gen_pow_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) (c : F) (m n : ℕ) → ∃ u, algMap u = algMap F KE c * x_gen W ^ m * y_gen W ^ n`
- **What**: Any monomial with an `F`-constant coefficient lifts to the local ring at `P`.
- **How**: Three-level `map_mul` + `mul_le_one'` decomposition bounding `algMap c`, `x_gen^m`, `y_gen^n` separately via `pointValuation_algebraMap_F_le_one`, `pointValuation_x_gen_le_one`, `pointValuation_y_gen_le_one`.
- **Hypotheses**: none beyond curve hypotheses.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`, `(W_smooth W).pointValuation_algebraMap_F_le_one`, `pointValuation_x_gen_le_one`, `pointValuation_y_gen_le_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 154–168, proof 10 lines
- **Notes**: none

---

### `theorem zero_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) → ∃ u : (W_smooth W).localRingAt P, algMap u = 0`
- **What**: `0` lifts to the local ring; witnessed by `u := 0`.
- **How**: `⟨0, map_zero _⟩` (term).
- **Hypotheses**: none.
- **Uses from project**: none
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 171–174, proof 1 line (term)
- **Notes**: none

---

### `theorem one_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) → ∃ u : (W_smooth W).localRingAt P, algMap u = 1`
- **What**: `1` lifts to the local ring; witnessed by `u := 1`.
- **How**: `⟨1, map_one _⟩` (term).
- **Hypotheses**: none.
- **Uses from project**: none
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 177–180, proof 1 line (term)
- **Notes**: none

---

### `theorem neg_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) {f : KE} → pV P f ≤ 1 → ∃ u, algMap u = -f`
- **What**: If `f` lifts, so does its negation.
- **How**: `mem_localRingAt_image_of_pointValuation_le_one` + `Valuation.map_neg` (valuations are invariant under negation in linear ordered groups).
- **Hypotheses**: `f` has pointValuation ≤ 1.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 183–191, proof 4 lines
- **Notes**: none

---

### `theorem pointValuation_mul_lt_one_of_le_and_lt`
- **Type**: `(P : (W_smooth W).SmoothPoint) {f g : KE} → pV P f ≤ 1 → pV P g < 1 → pV P (f * g) < 1`
- **What**: If `f` has valuation ≤ 1 and `g` has valuation strictly less than 1, then `f * g` has valuation strictly less than 1 (the strict factor dominates).
- **How**: Case-splits on `pV f = 0` (then product is 0, trivially < 1) vs `pV f > 0` (then `pV(f*g) = pV f · pV g ≤ 1 · pV g < 1` via `Valuation.map_mul` + `mul_le_mul_right'`).
- **Hypotheses**: `pV P f ≤ 1`, `pV P g < 1`.
- **Uses from project**: none (pure valuation arithmetic)
- **Used by**: used extensively outside this file (`SamePlace.lean`, `TranslateValuation.lean`), but not within this file
- **Visibility**: public
- **Lines**: 200–213, proof 14 lines
- **Notes**: Proof > 10 lines. This is the key technical lemma — most widely used outside the file.

---

### `theorem mem_localRingAt_image_iff_le_one`
- **Type**: `(P : (W_smooth W).SmoothPoint) (f : KE) → (∃ u, algMap u = f) ↔ pV P f ≤ 1`
- **What**: Biconditional characterisation: an element of `K(E)` lifts to `localRingAt P` if and only if its pointValuation is ≤ 1.
- **How**: Direct delegation to `Curves.SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one`.
- **Hypotheses**: none beyond curve hypotheses.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 221–226, proof 1 line (term)
- **Notes**: Re-exports the biconditional under a shorter local name.

---

### `theorem algebraMap_localRingAt_injective`
- **Type**: `(P : (W_smooth W).SmoothPoint) → Function.Injective (algebraMap ((W_smooth W).localRingAt P) KE)`
- **What**: The map from the local ring to `K(E)` is injective (local ring injects into its fraction field).
- **How**: `IsFractionRing.injective` applied to `(W_smooth W).localRingAt P` and `KE`.
- **Hypotheses**: none beyond curve hypotheses.
- **Uses from project**: none (pure mathlib)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 230–233, proof 1 line (term)
- **Notes**: none

---

### `theorem algebraMap_CoordinateRing_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) (r : (W_smooth W).CoordinateRing) → ∃ u, algMap u = algMap (W_smooth W).CoordinateRing KE r`
- **What**: Every element of the coordinate ring, viewed in `K(E)`, lifts to the local ring at `P`.
- **How**: `mem_localRingAt_image_of_pointValuation_le_one` + `(W_smooth W).pointValuation_algebraMap_le_one` (coordinate ring elements always have valuation ≤ 1).
- **Hypotheses**: none beyond curve hypotheses.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`, `(W_smooth W).pointValuation_algebraMap_le_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 238–244, proof 2 lines
- **Notes**: none

---

### `theorem x_gen_pow_sub_const_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) (n : ℕ) (c : F) → ∃ u, algMap u = x_gen W ^ n - algMap F KE c`
- **What**: Any `x_gen^n − c` (power of `x_gen` minus an F-constant) lifts to the local ring at `P`.
- **How**: `mem_localRingAt_image_of_pointValuation_le_one` + `map_sub` + `max_le` with `map_pow` + `pow_le_one'` for the power factor and `pointValuation_algebraMap_F_le_one` for the constant.
- **Hypotheses**: none beyond curve hypotheses.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`, `pointValuation_x_gen_le_one`, `(W_smooth W).pointValuation_algebraMap_F_le_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 248–258, proof 7 lines
- **Notes**: none

---

### `theorem y_gen_pow_sub_const_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) (n : ℕ) (c : F) → ∃ u, algMap u = y_gen W ^ n - algMap F KE c`
- **What**: Any `y_gen^n − c` lifts to the local ring at `P`.
- **How**: Same as `x_gen_pow_sub_const_mem_localRingAt_image` with `pointValuation_y_gen_le_one`.
- **Hypotheses**: none beyond curve hypotheses.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`, `pointValuation_y_gen_le_one`, `(W_smooth W).pointValuation_algebraMap_F_le_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 261–271, proof 7 lines
- **Notes**: none

---

### `theorem pointValuation_add_le_one`
- **Type**: `(P : (W_smooth W).SmoothPoint) {f g : KE} → pV P f ≤ 1 → pV P g ≤ 1 → pV P (f + g) ≤ 1`
- **What**: The ultrametric/non-Archimedean triangle inequality: sums of ≤ 1 elements are ≤ 1.
- **How**: `le_trans (map_add ...) (max_le hf hg)` — direct from ultrametric property.
- **Hypotheses**: Both operands have pointValuation ≤ 1.
- **Uses from project**: none (pure valuation)
- **Used by**: `pointValuation_linear_combination_le_one` (L325–L333), `neg_x_gen_add_const_mem_localRingAt_image` (L354), used heavily by other files (`SamePlace.lean`, `TranslateValuation.lean`)
- **Visibility**: public
- **Lines**: 276–281, proof 2 lines
- **Notes**: Key API — used by 3+ declarations in this file and many others.

---

### `theorem pointValuation_sub_le_one`
- **Type**: `(P : (W_smooth W).SmoothPoint) {f g : KE} → pV P f ≤ 1 → pV P g ≤ 1 → pV P (f - g) ≤ 1`
- **What**: Differences of ≤ 1 elements are ≤ 1.
- **How**: `le_trans (map_sub ...) (max_le hf hg)`.
- **Hypotheses**: Both operands have pointValuation ≤ 1.
- **Uses from project**: none
- **Used by**: `const_sub_x_gen_mem_localRingAt_image` (L366), `const_sub_y_gen_mem_localRingAt_image` (L377); used heavily in `TranslateValuation.lean`
- **Visibility**: public
- **Lines**: 284–289, proof 2 lines
- **Notes**: none

---

### `theorem pointValuation_mul_le_one`
- **Type**: `(P : (W_smooth W).SmoothPoint) {f g : KE} → pV P f ≤ 1 → pV P g ≤ 1 → pV P (f * g) ≤ 1`
- **What**: Products of ≤ 1 elements are ≤ 1.
- **How**: `Valuation.map_mul` + `mul_le_one'`.
- **Hypotheses**: Both operands have pointValuation ≤ 1.
- **Uses from project**: none
- **Used by**: `pointValuation_linear_combination_le_one` (L327, L330); used in `TranslateValuation.lean`
- **Visibility**: public
- **Lines**: 292–298, proof 3 lines
- **Notes**: none

---

### `theorem pointValuation_pow_le_one`
- **Type**: `(P : (W_smooth W).SmoothPoint) {f : KE} → pV P f ≤ 1 → (n : ℕ) → pV P (f ^ n) ≤ 1`
- **What**: Powers of ≤ 1 elements are ≤ 1.
- **How**: `Valuation.map_pow` + `pow_le_one'`.
- **Hypotheses**: `f` has pointValuation ≤ 1.
- **Uses from project**: none
- **Used by**: used in `TranslateValuation.lean` (e.g., L1365)
- **Visibility**: public
- **Lines**: 301–306, proof 3 lines
- **Notes**: unused directly within this file

---

### `theorem pointValuation_neg_le_one`
- **Type**: `(P : (W_smooth W).SmoothPoint) {f : KE} → pV P f ≤ 1 → pV P (-f) ≤ 1`
- **What**: Negations of ≤ 1 elements are ≤ 1.
- **How**: `Valuation.map_neg` + the hypothesis directly.
- **Hypotheses**: `f` has pointValuation ≤ 1.
- **Uses from project**: none
- **Used by**: `neg_x_gen_add_const_mem_localRingAt_image` (L355)
- **Visibility**: public
- **Lines**: 309–314, proof 3 lines
- **Notes**: none

---

### `theorem pointValuation_linear_combination_le_one`
- **Type**: `(P : (W_smooth W).SmoothPoint) (a b c : F) → pV P (a * x_gen W + b * y_gen W + c) ≤ 1`
- **What**: Any linear combination `a·x_gen + b·y_gen + c` with F-constants has pointValuation ≤ 1.
- **How**: Two applications of `pointValuation_add_le_one` and two of `pointValuation_mul_le_one`, with atomic bounds from `pointValuation_x/y_gen_le_one` and `pointValuation_algebraMap_F_le_one`.
- **Hypotheses**: none beyond curve hypotheses.
- **Uses from project**: `pointValuation_add_le_one`, `pointValuation_mul_le_one`, `(W_smooth W).pointValuation_algebraMap_F_le_one`, `pointValuation_x_gen_le_one`, `pointValuation_y_gen_le_one`
- **Used by**: `linear_combination_mem_localRingAt_image` (L342)
- **Visibility**: public
- **Lines**: 320–333, proof 10 lines
- **Notes**: none

---

### `theorem linear_combination_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) (a b c : F) → ∃ u, algMap u = a * x_gen W + b * y_gen W + c`
- **What**: Any linear combination `a·x_gen + b·y_gen + c` lifts to the local ring at `P`.
- **How**: Delegates to `mem_localRingAt_image_of_pointValuation_le_one` with `pointValuation_linear_combination_le_one`.
- **Hypotheses**: none beyond curve hypotheses.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`, `pointValuation_linear_combination_le_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 336–343, proof 2 lines
- **Notes**: none

---

### `theorem neg_x_gen_add_const_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) (c : F) → ∃ u, algMap u = -(x_gen W) + algMap F KE c`
- **What**: The element `−x_gen + c` lifts to the local ring at `P`.
- **How**: `mem_localRingAt_image_of_pointValuation_le_one` + `pointValuation_add_le_one` with `pointValuation_neg_le_one` for `−x_gen` and `pointValuation_algebraMap_F_le_one` for `c`.
- **Hypotheses**: none beyond curve hypotheses.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`, `pointValuation_add_le_one`, `pointValuation_neg_le_one`, `pointValuation_x_gen_le_one`, `(W_smooth W).pointValuation_algebraMap_F_le_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 348–356, proof 5 lines
- **Notes**: none

---

### `theorem const_sub_x_gen_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) (c : F) → ∃ u, algMap u = algMap F KE c - x_gen W`
- **What**: The element `c − x_gen` lifts to the local ring at `P`.
- **How**: `mem_localRingAt_image_of_pointValuation_le_one` + `pointValuation_sub_le_one` with bounds for `c` and `x_gen`.
- **Hypotheses**: none beyond curve hypotheses.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`, `pointValuation_sub_le_one`, `(W_smooth W).pointValuation_algebraMap_F_le_one`, `pointValuation_x_gen_le_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 360–368, proof 5 lines
- **Notes**: none

---

### `theorem const_sub_y_gen_mem_localRingAt_image`
- **Type**: `(P : (W_smooth W).SmoothPoint) (c : F) → ∃ u, algMap u = algMap F KE c - y_gen W`
- **What**: The element `c − y_gen` lifts to the local ring at `P`.
- **How**: `mem_localRingAt_image_of_pointValuation_le_one` + `pointValuation_sub_le_one` with bounds for `c` and `y_gen`.
- **Hypotheses**: none beyond curve hypotheses.
- **Uses from project**: `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one`, `pointValuation_sub_le_one`, `(W_smooth W).pointValuation_algebraMap_F_le_one`, `pointValuation_y_gen_le_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 371–379, proof 5 lines
- **Notes**: none

---

## Summary

- **Total declarations**: 30 (all theorems)
- **Defs**: 0
- **Instances**: 0
- **Sorries**: none
- **set_option maxHeartbeats**: none
- **Long proofs (>30 lines)**: none
- **Key API** (used by 3+ others in file): `pointValuation_add_le_one` (used in L325, L326, L354), `Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one` (used throughout, from TranslationOrd)
- **Unused in file** (dead code within this file): `xy_gen_sub_const_mem_localRingAt_image`, `add_mem_localRingAt_image`, `sub_mem_localRingAt_image`, `mul_mem_localRingAt_image`, `x_gen_pow_mem_localRingAt_image`, `y_gen_pow_mem_localRingAt_image`, `x_gen_pow_mul_y_gen_pow_mem_localRingAt_image`, `algebraMap_F_mul_x_gen_pow_mul_y_gen_pow_mem_localRingAt_image`, `zero_mem_localRingAt_image`, `one_mem_localRingAt_image`, `neg_mem_localRingAt_image`, `pointValuation_mul_lt_one_of_le_and_lt`, `mem_localRingAt_image_iff_le_one`, `algebraMap_localRingAt_injective`, `algebraMap_CoordinateRing_mem_localRingAt_image`, `x_gen_pow_sub_const_mem_localRingAt_image`, `y_gen_pow_sub_const_mem_localRingAt_image`, `pointValuation_pow_le_one`, `linear_combination_mem_localRingAt_image`, `neg_x_gen_add_const_mem_localRingAt_image`, `const_sub_x_gen_mem_localRingAt_image`, `const_sub_y_gen_mem_localRingAt_image`
- **Notes**: This file is a pure API collection for local-ring lifting. All results are heavily used by downstream files (`TranslateValuation.lean`, `SamePlace.lean`). The most widely-used export is `pointValuation_mul_lt_one_of_le_and_lt` and the valuation bound suite `pointValuation_{add,sub,mul,neg,pow}_le_one`.
