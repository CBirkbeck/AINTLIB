# Inventory: ./HasseWeil/WeilPairing/DivisorTranslate.lean

**File**: `HasseWeil/WeilPairing/DivisorTranslate.lean`
**Lines**: 1–648
**Total declarations**: 27 (2 `noncomputable def`, 25 `theorem`)
**Sorries**: none
**`set_option maxHeartbeats`**: none

---

## Declaration inventory

---

### `noncomputable def placeTranslate`
- **Type**: `(S : W.toAffine.Point) : ProjectiveSmoothPoint (W_smooth W) ≃ ProjectiveSmoothPoint (W_smooth W)`
- **What**: The bijection of projective places induced by adding `S` to the underlying point; it sends `∞ ↦ S` and `(−S) ↦ ∞`, mixing affine and infinity places.
- **How**: Direct composition of `Affine.Point.equivProjectiveSmoothPoint.symm`, `Equiv.addRight S`, and `equivProjectiveSmoothPoint`.
- **Hypotheses**: `W` is an elliptic curve over a field `F`.
- **Uses from project**: `W_smooth`, `WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint`
- **Used by**: `placeTranslate_apply`, `placeTranslate_affine`, `placeTranslate_infinity`, `placeTranslate_zero`, `placeTranslate_affine_of_isSome`, `placeTranslate_affine_eq_infinity`, `ordProj_translate_infinity`, `ordProj_translate`, `projectiveDivisorOf_translate`, `projectiveDivisorOf_translate_mapDomain`, `divisorOf_translate_apply`, `projectiveDivisorOf_translate_self_of_invariant`, `projectiveDivisorOf_translate_div_eq_zero_of_invariant`, `placeTranslate_toAffinePoint`, `pullbackDiv_placeTranslate_apply`, `pullbackDiv_placeTranslate_apply_general`, `equivMapDomain_placeTranslate_pullbackDiv`, `equivMapDomain_placeTranslate_symm_eq_self`, `equivMapDomain_placeTranslate_pullbackDiv_sub`
- **Visibility**: public
- **Lines**: 87–93 (7 lines, definition body 5 lines)
- **Notes**: Key def for the whole file; used by every downstream result.

---

### `theorem placeTranslate_apply`
- **Type**: `(S : W.toAffine.Point) (v : ProjectiveSmoothPoint (W_smooth W)) : placeTranslate W S v = equivProjectiveSmoothPoint (v.toAffinePoint + S)`
- **What**: Unfolds `placeTranslate` to show the image of any place `v` is the projective smooth point of `v.toAffinePoint + S`.
- **How**: `rfl` — definitional equality.
- **Hypotheses**: none beyond the ambient variable declarations.
- **Uses from project**: `placeTranslate`
- **Used by**: `placeTranslate_affine`, `placeTranslate_infinity`, `placeTranslate_zero`, `placeTranslate_affine_of_isSome`, `placeTranslate_affine_eq_infinity`, `ordProj_translate_infinity`, `placeTranslate_toAffinePoint`
- **Visibility**: public
- **Lines**: 94–100 (7 lines, proof ~1 line)
- **Notes**: Unfolding lemma; widely used.

---

### `@[simp] theorem placeTranslate_affine`
- **Type**: `(S : W.toAffine.Point) (P : (W_smooth W).SmoothPoint) : placeTranslate W S (ProjectiveSmoothPoint.affine P) = (P.toAffinePoint + S).toProjectiveSmoothPoint`
- **What**: The `@[simp]` computation rule for `placeTranslate` on an affine place.
- **How**: Unfolds via `placeTranslate_apply` then `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `placeTranslate`, `placeTranslate_apply`
- **Used by**: unused within this file (exported simp lemma)
- **Visibility**: public
- **Lines**: 101–108 (8 lines, proof ~2 lines)
- **Notes**: Dead code within the file; likely consumed by downstream importers.

---

### `@[simp] theorem placeTranslate_infinity`
- **Type**: `(S : W.toAffine.Point) : placeTranslate W S ProjectiveSmoothPoint.infinity = S.toProjectiveSmoothPoint`
- **What**: Translation moves the place at infinity to the place corresponding to `S`.
- **How**: `placeTranslate_apply` then rewrites `0 + S = S` via `zero_add`.
- **Hypotheses**: none.
- **Uses from project**: `placeTranslate`, `placeTranslate_apply`
- **Used by**: `ordProj_translate_infinity`
- **Visibility**: public
- **Lines**: 109–116 (8 lines, proof ~4 lines)
- **Notes**: none.

---

### `@[simp] theorem placeTranslate_zero`
- **Type**: `placeTranslate W (0 : W.toAffine.Point) = Equiv.refl _`
- **What**: Translation by the identity point `O` is the identity bijection of places.
- **How**: `Equiv.ext` + `placeTranslate_apply` + `add_zero` + `toAffinePoint_toProjectiveSmoothPoint`.
- **Hypotheses**: none.
- **Uses from project**: `placeTranslate`, `placeTranslate_apply`, `WeierstrassCurve.Affine.Point.toAffinePoint_toProjectiveSmoothPoint`
- **Used by**: `ordProj_translate_infinity`
- **Visibility**: public
- **Lines**: 117–127 (11 lines, proof ~4 lines)
- **Notes**: none.

---

### `noncomputable def ordProj`
- **Type**: `(v : ProjectiveSmoothPoint (W_smooth W)) (f : KE) : WithTop ℤ`
- **What**: The order of `f` at the projective place `v`: `ord_P` at an affine place, `ordAtInfty` at the place at infinity. Packages the two existing valuations into one function.
- **How**: Pattern match on `v`; the two branches delegate to `(W_smooth W).ord_P` and `(W_smooth W).ordAtInfty`.
- **Hypotheses**: none.
- **Uses from project**: `W_smooth`, `(W_smooth W).ord_P`, `(W_smooth W).ordAtInfty`
- **Used by**: `ordProj_affine`, `ordProj_infinity`, `projectiveDivisorOf_apply_ordProj`, `ordProj_translate_infinity`, `ordProj_translate`, `divisorOf_translate_apply`
- **Visibility**: public
- **Lines**: 128–133 (6 lines, definition body 3 lines)
- **Notes**: Central accessor used by all downstream ordProj results.

---

### `@[simp] theorem ordProj_affine`
- **Type**: `(P : (W_smooth W).SmoothPoint) (f : KE) : ordProj W (ProjectiveSmoothPoint.affine P) f = (W_smooth W).ord_P P f`
- **What**: `ordProj` at an affine place reduces to `ord_P`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `ordProj`
- **Used by**: `projectiveDivisorOf_apply_ordProj`, `ordProj_translate_infinity`, `ordProj_translate`
- **Visibility**: public
- **Lines**: 134–136 (3 lines)
- **Notes**: none.

---

### `@[simp] theorem ordProj_infinity`
- **Type**: `(f : KE) : ordProj W ProjectiveSmoothPoint.infinity f = (W_smooth W).ordAtInfty f`
- **What**: `ordProj` at the infinity place reduces to `ordAtInfty`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `ordProj`
- **Used by**: `projectiveDivisorOf_apply_ordProj`, `ordProj_translate_infinity`
- **Visibility**: public
- **Lines**: 137–142 (6 lines including docstring)
- **Notes**: none.

---

### `theorem projectiveDivisorOf_apply_ordProj`
- **Type**: `(f : KE) (v : ProjectiveSmoothPoint (W_smooth W)) : (W_smooth W).projectiveDivisorOf f v = (ordProj W v f).untopD 0`
- **What**: Reads off the coefficient of the projective divisor at place `v` as `(ordProj W v f).untopD 0`, unifying the two existing apply lemmas `projectiveDivisorOf_apply_affine` and `projectiveDivisorOf_apply_infinity`.
- **How**: Case split on `v`; each branch uses the matching `projectiveDivisorOf_apply_{affine,infinity}` lemma and the corresponding `ordProj_{affine,infinity}` simp.
- **Hypotheses**: none.
- **Uses from project**: `ordProj`, `ordProj_affine`, `ordProj_infinity`, `(W_smooth W).projectiveDivisorOf_apply_affine`, `(W_smooth W).projectiveDivisorOf_apply_infinity`
- **Used by**: `projectiveDivisorOf_translate`
- **Visibility**: public
- **Lines**: 143–166 (24 lines, proof ~22 lines)
- **Notes**: none.

---

### `theorem ord_P_translate`
- **Type**: `(P : (W_smooth W).SmoothPoint) (S : (W_smooth W).toAffine.Point) (h : (P.toAffinePoint + S).IsSome) (f : KE) (hf : f ≠ 0) : (W_smooth W).ord_P P (translateAlgEquivOfPoint W S f) = (W_smooth W).ord_P (P.translate_of_finite S h) f`
- **What**: The affine ord transport (Item 1 of Silverman III.8): the pullback `τ_S` moves the order at `P` to the order at `P + S`, with sign pinned.
- **How**: Case split on `S = 0` (trivial) vs `S = some xk yk h_ns` (calls the shipped `translate_ord_eq_all_nonzero`); zero case uses `translate_of_finite_zero`.
- **Hypotheses**: `f ≠ 0`; `P + S` is finite (`IsSome`).
- **Uses from project**: `translateAlgEquivOfPoint`, `translate_ord_eq_all_nonzero`, `Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_zero`
- **Used by**: `ordProj_translate`
- **Visibility**: public
- **Lines**: 167–182 (16 lines, proof ~10 lines)
- **Notes**: none.

---

### `theorem placeTranslate_affine_of_isSome`
- **Type**: `(S : (W_smooth W).toAffine.Point) (P : (W_smooth W).SmoothPoint) (h : (P.toAffinePoint + S).IsSome) : placeTranslate W S (ProjectiveSmoothPoint.affine P) = ProjectiveSmoothPoint.affine (P.translate_of_finite S h)`
- **What**: When the translate `P + S` stays finite, `placeTranslate W S (affine P)` equals the affine place of the translated smooth point.
- **How**: Injectivity of `equivProjectiveSmoothPoint.symm`, then `placeTranslate_apply` + `translate_of_finite_toAffinePoint`.
- **Hypotheses**: `P + S` finite (`IsSome`).
- **Uses from project**: `placeTranslate`, `placeTranslate_apply`, `WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint`, `Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_toAffinePoint`
- **Used by**: `ordProj_translate`
- **Visibility**: public
- **Lines**: 183–198 (16 lines, proof ~10 lines)
- **Notes**: none.

---

### `theorem placeTranslate_affine_eq_infinity`
- **Type**: `(S : (W_smooth W).toAffine.Point) (P : (W_smooth W).SmoothPoint) (hz : P.toAffinePoint + S = 0) : placeTranslate W S (ProjectiveSmoothPoint.affine P) = ProjectiveSmoothPoint.infinity`
- **What**: When `P + S = O`, translating the affine place of `P` lands on the place at infinity.
- **How**: Injectivity of `equivProjectiveSmoothPoint.symm` + `placeTranslate_apply`; the goal reduces to `hz : P.toAffinePoint + S = 0` matching the `0`-reduction of `equivProjectiveSmoothPoint.symm ∞`.
- **Hypotheses**: `P.toAffinePoint + S = 0`.
- **Uses from project**: `placeTranslate`, `placeTranslate_apply`, `WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint`
- **Used by**: `ordProj_translate`
- **Visibility**: public
- **Lines**: 199–238 (40 lines including docstring; proof ~36 lines)
- **Notes**: Proof is >30 lines. Much of the bulk is the extended proof comment explaining the injectivity argument and the defeq reduction; the actual tactic steps are short.

---

### `theorem ordProj_translate_infinity`
- **Type**: `(S : (W_smooth W).toAffine.Point) (f : KE) (hf : f ≠ 0) (v : ProjectiveSmoothPoint (W_smooth W)) (hv : v = ∞ ∨ placeTranslate W S v = ∞) : ordProj W v (translateAlgEquivOfPoint W S f) = ordProj W (placeTranslate W S v) f`
- **What**: The isolated residual: the projective ord transport at the infinity-touching places (source = ∞, or target = ∞). Relies on `isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint` from `TranslateOrdInfty.lean`, the upstream discharged order-at-infinity compatibility.
- **How**: Case on `S = 0` (trivial); then case on `v = affine P` (target = ∞, forces `P + S = 0`, apply `isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint`) vs `v = ∞` (source = ∞, recover `S = some xk yk h_ns`, apply `isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint` at `(-a)` then use `translateAlgEquivOfPoint_add_apply` and `add_neg_cancel`).
- **Hypotheses**: `f ≠ 0`; `v = ∞` or `placeTranslate W S v = ∞`.
- **Uses from project**: `placeTranslate`, `placeTranslate_apply`, `placeTranslate_zero`, `placeTranslate_infinity`, `ordProj_affine`, `ordProj_infinity`, `isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint`, `translateAlgEquivOfPoint_add_apply`
- **Used by**: `ordProj_translate`
- **Visibility**: public
- **Lines**: 239–320 (82 lines including docstring; proof ~77 lines)
- **Notes**: Longest proof in the file (77 proof lines). The file's module-level comment names this as "the single isolated residual"; upstream `isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint` was itself sorry-free.

---

### `theorem ordProj_translate`
- **Type**: `(S : (W_smooth W).toAffine.Point) (f : KE) (hf : f ≠ 0) (v : ProjectiveSmoothPoint (W_smooth W)) : ordProj W v (translateAlgEquivOfPoint W S f) = ordProj W (placeTranslate W S v) f`
- **What**: The uniform projective ord transport (Item 1 lifted to all places): the pullback `τ_S` transports the order at every place `v` to the order at `v + S`.
- **How**: Case on `v = ∞` (delegates to `ordProj_translate_infinity`); case on `v = affine P` — sub-case on whether `P + S` is finite (`ord_P_translate` + `placeTranslate_affine_of_isSome`) or `P + S = O` (delegates to `ordProj_translate_infinity`).
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `placeTranslate`, `ordProj`, `ordProj_affine`, `ordProj_translate_infinity`, `ord_P_translate`, `placeTranslate_affine_of_isSome`, `placeTranslate_affine_eq_infinity`
- **Used by**: `projectiveDivisorOf_translate`, `divisorOf_translate_apply`
- **Visibility**: public
- **Lines**: 321–367 (47 lines; proof ~44 lines)
- **Notes**: Proof >30 lines. Synthesizes all cases via the two helper residual lemmas.

---

### `theorem projectiveDivisorOf_translate`
- **Type**: `(S : (W_smooth W).toAffine.Point) (f : KE) : (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S f) = Finsupp.equivMapDomain (placeTranslate W S).symm ((W_smooth W).projectiveDivisorOf f)`
- **What**: Item 3 of Silverman III.8: the projective divisor of the translate `τ_S f` equals the push-forward of `projectiveDivisorOf f` along the place translation. Works for `f = 0` separately.
- **How**: Case `f = 0` via `map_zero` + `projectiveDivisorOf_zero` + `equivMapDomain_zero`. Case `f ≠ 0`: `Finsupp.ext`, `equivMapDomain_apply`, `projectiveDivisorOf_apply_ordProj`, `ordProj_translate`.
- **Hypotheses**: none (handles `f = 0` and `f ≠ 0`).
- **Uses from project**: `placeTranslate`, `translateAlgEquivOfPoint`, `projectiveDivisorOf_apply_ordProj`, `ordProj_translate`, `(W_smooth W).projectiveDivisorOf_zero`
- **Used by**: `projectiveDivisorOf_translate_mapDomain`, `projectiveDivisorOf_translate_self_of_invariant`
- **Visibility**: public
- **Lines**: 368–390 (23 lines, proof ~16 lines)
- **Notes**: none.

---

### `theorem projectiveDivisorOf_translate_mapDomain`
- **Type**: `(S : (W_smooth W).toAffine.Point) (f : KE) : (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S f) = Finsupp.mapDomain (placeTranslate W S).symm ((W_smooth W).projectiveDivisorOf f)`
- **What**: Same as `projectiveDivisorOf_translate` but expressed with `Finsupp.mapDomain` instead of `equivMapDomain`.
- **How**: Rewrites `projectiveDivisorOf_translate` then `Finsupp.equivMapDomain_eq_mapDomain`.
- **Hypotheses**: none.
- **Uses from project**: `placeTranslate`, `projectiveDivisorOf_translate`
- **Used by**: unused within this file
- **Visibility**: public
- **Lines**: 391–404 (14 lines, proof ~3 lines)
- **Notes**: Dead code within this file; provided for callers preferring `mapDomain` API.

---

### `theorem divisorOf_translate_apply`
- **Type**: `(S : (W_smooth W).toAffine.Point) (f : KE) (hf : f ≠ 0) (P : (W_smooth W).SmoothPoint) : (W_smooth W).divisorOf (translateAlgEquivOfPoint W S f) P = (ordProj W (placeTranslate W S (ProjectiveSmoothPoint.affine P)) f).untopD 0`
- **What**: Pointwise affine shadow of the projective divisor transport: the affine-divisor coefficient of `τ_S f` at `P` equals the `ordProj` of `f` at the translated place.
- **How**: Converts the goal to `ordProj_translate` (the affine case) and applies `ordProj_translate`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `placeTranslate`, `ordProj`, `ordProj_translate`
- **Used by**: unused within this file
- **Visibility**: public
- **Lines**: 405–429 (25 lines, proof ~22 lines)
- **Notes**: Dead code within this file; useful for consumers who work with the affine divisor.

---

### `theorem projectiveDivisorOf_translate_self_of_invariant`
- **Type**: `(S : (W_smooth W).toAffine.Point) (g : KE) (hinv : Finsupp.equivMapDomain (placeTranslate W S).symm ((W_smooth W).projectiveDivisorOf g) = (W_smooth W).projectiveDivisorOf g) : (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S g) = (W_smooth W).projectiveDivisorOf g`
- **What**: If the projective divisor of `g` is invariant under the place translation, then `τ_S g` has the same divisor as `g`.
- **How**: Directly rewrites with `projectiveDivisorOf_translate` then `hinv`.
- **Hypotheses**: `hinv` — divisor invariance.
- **Uses from project**: `placeTranslate`, `projectiveDivisorOf_translate`
- **Used by**: `projectiveDivisorOf_translate_div_eq_zero_of_invariant`
- **Visibility**: public
- **Lines**: 430–448 (19 lines, proof ~3 lines)
- **Notes**: Thin wrapper; its consumer is the next lemma.

---

### `theorem projectiveDivisorOf_translate_div_eq_zero_of_invariant`
- **Type**: `(S : (W_smooth W).toAffine.Point) (g : KE) (hg : g ≠ 0) (hinv : ...) : (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S g / g) = 0`
- **What**: Item 4 of Silverman III.8 (abstract form): if `div g` is translation-invariant, then `τ_S g / g` has trivial divisor. This is the hypothesis that `pairing_const_of_transport` consumes.
- **How**: Uses `projectiveDivisorOf_translate_self_of_invariant` to match divisors, then a calc chain: `div(τ_S g / g) = div(τ_S g) + div(g⁻¹) = div(τ_S g) − div(g) = 0` via `projectiveDivisorOf_mul`, `projectiveDivisorOf_inv`, and `sub_self`.
- **Hypotheses**: `g ≠ 0`; divisor invariance `hinv`.
- **Uses from project**: `placeTranslate`, `translateAlgEquivOfPoint`, `projectiveDivisorOf_translate_self_of_invariant`, `(W_smooth W).projectiveDivisorOf_mul`, `(W_smooth W).projectiveDivisorOf_inv`
- **Used by**: `projectiveDivisorOf_translate_weilFunction_div_eq_zero`
- **Visibility**: public
- **Lines**: 449–480 (32 lines, proof ~26 lines)
- **Notes**: Proof just over 30 lines by line count including docstring; actual tactic body ~26 lines.

---

### `theorem placeTranslate_toAffinePoint`
- **Type**: `(S : (W_smooth W).toAffine.Point) (w : ProjectiveSmoothPoint (W_smooth W)) : (placeTranslate W S w).toAffinePoint = w.toAffinePoint + S`
- **What**: The `toAffinePoint` of a translated projective smooth point is the translation of the original underlying point.
- **How**: `placeTranslate_apply` + `toProjectiveSmoothPoint_toAffinePoint`.
- **Hypotheses**: none.
- **Uses from project**: `placeTranslate`, `placeTranslate_apply`, `WeierstrassCurve.Affine.Point.toProjectiveSmoothPoint_toAffinePoint`
- **Used by**: `pullbackDiv_placeTranslate_apply`, `pullbackDiv_placeTranslate_apply_general`
- **Visibility**: public
- **Lines**: 481–493 (13 lines, proof ~5 lines)
- **Notes**: none.

---

### `theorem pullbackDiv_apply`
- **Type**: `(f : W.toAffine.Point →+ W.toAffine.Point) (hker : Finite f.ker) (Q : W.toAffine.Point) (w : ProjectiveSmoothPoint (W_smooth W)) : pullbackDiv f hker Q w = if f w.toAffinePoint = Q then 1 else 0`
- **What**: Coefficient formula for the fibre-sum divisor `pullbackDiv f hker Q`: the coefficient at place `w` is `1` if `w.toAffinePoint` lies in the fibre over `Q`, else `0`. Identifies the fibre sum as a simple indicator Finsupp.
- **How**: Instantiates `Fintype` on the fibre via `fiber_finite`, unfolds `pullbackDiv` as a Finset sum, collapses it by uniqueness using `Finset.sum_eq_single` (in the `hQ` case) and `Finset.sum_eq_zero` (in the `¬ hQ` case), with injectivity `hkey : P.toProj = w ↔ P = w.toAffinePoint` as the key bijection lemma.
- **Hypotheses**: `hker : Finite f.ker`.
- **Uses from project**: `pullbackDiv`, `fiber_finite`
- **Used by**: `pullbackDiv_placeTranslate_apply`, `pullbackDiv_placeTranslate_apply_general`
- **Visibility**: public
- **Lines**: 494–538 (45 lines, proof ~41 lines)
- **Notes**: Proof >30 lines. Uses `Finset.sum_eq_single` with injectivity argument as the key step.

---

### `theorem pullbackDiv_placeTranslate_apply`
- **Type**: `(S : (W_smooth W).toAffine.Point) (f : W.toAffine.Point →+ W.toAffine.Point) (hker : Finite f.ker) (Q : W.toAffine.Point) (hfS : f S = 0) (w : ProjectiveSmoothPoint (W_smooth W)) : pullbackDiv f hker Q (placeTranslate W S w) = pullbackDiv f hker Q w`
- **What**: Pointwise invariance of the fibre-sum divisor: when `f S = 0`, the fibre condition at the translated place is unchanged, so each coefficient is preserved.
- **How**: `pullbackDiv_apply` twice + `placeTranslate_toAffinePoint`, then `map_add` and `hfS` to show `f(w + S) = f w`.
- **Hypotheses**: `f S = 0`.
- **Uses from project**: `placeTranslate`, `placeTranslate_toAffinePoint`, `pullbackDiv_apply`
- **Used by**: `equivMapDomain_placeTranslate_pullbackDiv_sub`
- **Visibility**: public
- **Lines**: 539–554 (16 lines, proof ~8 lines)
- **Notes**: none.

---

### `theorem pullbackDiv_placeTranslate_apply_general`
- **Type**: `(S : (W_smooth W).toAffine.Point) (f : W.toAffine.Point →+ W.toAffine.Point) (hker : Finite f.ker) (Q : W.toAffine.Point) (w : ProjectiveSmoothPoint (W_smooth W)) : pullbackDiv f hker Q (placeTranslate W S w) = pullbackDiv f hker (Q - f S) w`
- **What**: General shift law: the fibre-sum divisor coefficient at the translated place equals the coefficient for the shifted base-point `Q − f S`, for any `S` (no kernel condition needed).
- **How**: `pullbackDiv_apply` twice + `placeTranslate_toAffinePoint`, then `map_add` + `propext eq_sub_iff_add_eq.symm`.
- **Hypotheses**: none (general).
- **Uses from project**: `placeTranslate`, `placeTranslate_toAffinePoint`, `pullbackDiv_apply`
- **Used by**: `equivMapDomain_placeTranslate_pullbackDiv`
- **Visibility**: public
- **Lines**: 555–570 (16 lines, proof ~8 lines)
- **Notes**: Generalizes `pullbackDiv_placeTranslate_apply`; used by the push-forward divisor form.

---

### `theorem equivMapDomain_placeTranslate_pullbackDiv`
- **Type**: `(S : (W_smooth W).toAffine.Point) (f : W.toAffine.Point →+ W.toAffine.Point) (hker : Finite f.ker) (Q : W.toAffine.Point) : Finsupp.equivMapDomain (placeTranslate W S).symm (pullbackDiv f hker Q) = pullbackDiv f hker (Q - f S)`
- **What**: The push-forward of the fibre-sum divisor `pullbackDiv f hker Q` along the place translation is `pullbackDiv f hker (Q − f S)`. Divisor-level form of the shift law.
- **How**: `Finsupp.ext` + `Finsupp.equivMapDomain_symm_apply` + `pullbackDiv_placeTranslate_apply_general`.
- **Hypotheses**: none.
- **Uses from project**: `placeTranslate`, `pullbackDiv_placeTranslate_apply_general`
- **Used by**: unused within this file
- **Visibility**: public
- **Lines**: 571–582 (12 lines, proof ~6 lines)
- **Notes**: Dead code within this file; exported for callers using the general shift.

---

### `theorem equivMapDomain_placeTranslate_symm_eq_self`
- **Type**: `(S : (W_smooth W).toAffine.Point) (D : ProjectiveDivisor (W_smooth W)) (hD : ∀ w, D (placeTranslate W S w) = D w) : Finsupp.equivMapDomain (placeTranslate W S).symm D = D`
- **What**: If a divisor `D` is pointwise invariant under `placeTranslate W S`, then `equivMapDomain (placeTranslate W S).symm D = D`. Finsupp-level restatement of translation-invariance.
- **How**: `Finsupp.ext` + `Finsupp.equivMapDomain_symm_apply` + `hD`.
- **Hypotheses**: pointwise invariance `hD`.
- **Uses from project**: `placeTranslate`
- **Used by**: `equivMapDomain_placeTranslate_pullbackDiv_sub`
- **Visibility**: public
- **Lines**: 583–594 (12 lines, proof ~5 lines)
- **Notes**: none.

---

### `theorem equivMapDomain_placeTranslate_pullbackDiv_sub`
- **Type**: `(S : (W_smooth W).toAffine.Point) (f : W.toAffine.Point →+ W.toAffine.Point) (hker : Finite f.ker) (T : W.toAffine.Point) (hfS : f S = 0) : Finsupp.equivMapDomain (placeTranslate W S).symm (pullbackDiv f hker T − pullbackDiv f hker 0) = pullbackDiv f hker T − pullbackDiv f hker 0`
- **What**: The Weil-function divisor (fibre difference `[ℓ]^*(T) − [ℓ]^*(O)`) is invariant under the place translation when `f S = 0` (i.e., `S ∈ E[ℓ]`). Derived from pointwise invariance applied to each summand via `pullbackDiv_placeTranslate_apply`.
- **How**: Applies `equivMapDomain_placeTranslate_symm_eq_self` with `hD w := pullbackDiv_placeTranslate_apply ... T hfS` and `pullbackDiv_placeTranslate_apply ... 0 hfS`.
- **Hypotheses**: `f S = 0`.
- **Uses from project**: `placeTranslate`, `equivMapDomain_placeTranslate_symm_eq_self`, `pullbackDiv_placeTranslate_apply`
- **Used by**: `projectiveDivisorOf_translate_weilFunction_div_eq_zero`
- **Visibility**: public
- **Lines**: 595–632 (38 lines; proof ~30 lines)
- **Notes**: Proof exactly 30 lines (L603–L632), borderline for the >30 threshold.

---

### `theorem projectiveDivisorOf_translate_weilFunction_div_eq_zero`
- **Type**: `(S : (W_smooth W).toAffine.Point) (f : W.toAffine.Point →+ W.toAffine.Point) (hker : Finite f.ker) (T : W.toAffine.Point) (hfS : f S = 0) (g : KE) (hg : g ≠ 0) (hg_div : (W_smooth W).projectiveDivisorOf g = pullbackDiv f hker T − pullbackDiv f hker 0) : (W_smooth W).projectiveDivisorOf (translateAlgEquivOfPoint W S g / g) = 0`
- **What**: Item 4 capstone (Weil-function form): if `g` is a Weil function for `T` (divisor = `[ℓ]^*(T) − [ℓ]^*(O)`) and `S ∈ E[ℓ]` (`f S = 0`), then `τ_S g / g` has trivial projective divisor. This is exactly what `pairing_const_of_transport` in `Constancy.lean` consumes to extract the constant `e_ℓ(S, T)`.
- **How**: Applies `projectiveDivisorOf_translate_div_eq_zero_of_invariant` with invariance provided by `equivMapDomain_placeTranslate_pullbackDiv_sub` after rewriting `hg_div`.
- **Hypotheses**: `g ≠ 0`; `hg_div`; `f S = 0`.
- **Uses from project**: `placeTranslate`, `translateAlgEquivOfPoint`, `projectiveDivisorOf_translate_div_eq_zero_of_invariant`, `equivMapDomain_placeTranslate_pullbackDiv_sub`
- **Used by**: unused within this file (exported capstone)
- **Visibility**: public
- **Lines**: 633–648 (16 lines, proof ~7 lines)
- **Notes**: Dead code within this file; the primary external-facing result of this module.

---

## Summary

| Metric | Value |
|---|---|
| Total declarations | 27 |
| `noncomputable def` | 2 |
| `theorem` | 25 |
| Instances | 0 |
| Sorries | 0 |
| `set_option maxHeartbeats` | 0 |

**Long proofs (>30 lines)**:
- `placeTranslate_affine_eq_infinity`: ~36 proof lines
- `ordProj_translate_infinity`: ~77 proof lines (longest)
- `ordProj_translate`: ~44 proof lines
- `pullbackDiv_apply`: ~41 proof lines

**Unused in file** (dead-code candidates, likely exported):
- `placeTranslate_affine` (simp lemma)
- `projectiveDivisorOf_translate_mapDomain` (alternate form)
- `divisorOf_translate_apply` (pointwise affine shadow)
- `equivMapDomain_placeTranslate_pullbackDiv` (general shift, no kernel condition)
- `projectiveDivisorOf_translate_weilFunction_div_eq_zero` (capstone)

**Key API** (used by 3+ declarations in this file):
- `placeTranslate` (used by 19 others)
- `placeTranslate_apply` (used by 7 others)
- `ordProj` (used by 6 others)
- `ordProj_affine` (used by 3 others)
