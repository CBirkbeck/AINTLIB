# Inventory: ./HasseWeil/EC/IsogenySurjective.lean

**File purpose:** Surjectivity of a nonconstant isogeny on K̄-points, proved via valuation/place theory (Silverman II.2.3, III.4.10c). Works entirely at the valuation level, avoiding `CoordHom`.

**Imports:** `HasseWeil.WeilPairing.DivisorPullback`, `Mathlib.RingTheory.Valuation.LocalSubring`

**Total declarations:** 17 (2 defs, 15 theorems, 0 instances)

---

## Section: The unified projective place valuation

### `noncomputable def projValuation`
- **Type**: `(Q : W.Point) → Valuation KE (WithZero (Multiplicative ℤ))`
- **What**: The discrete valuation of the function field `K(E)` at a projective point `Q`: `ordAtInftyValuation` at `Q = .zero`, and `pointValuation ⟨x,y,h⟩` at `Q = .some x y h`.
- **How**: Pattern match on `W.Point`; each branch is a previously-built valuation from `SmoothPlaneCurve`.
- **Hypotheses**: `W` an elliptic Weierstrass curve over `F` (field), `W.IsElliptic`.
- **Uses from project**: `SmoothPlaneCurve.ordAtInftyValuation`, `SmoothPlaneCurve.pointValuation`
- **Used by**: `projValuation_zero`, `projValuation_some`, `projValuation_surjective`, `projValuation_eq_exp_neg_projOrdAt`, `projValuation_comap_pullback_eq_of_projOrdTransport`, `projValuation_injective`, `pointMap_eq_of_comap_isEquiv`, `PlaceLift`, `surjective_of_PlaceLift_and_hproj`, `surjective_of_finite_comorphism_and_hproj`
- **Visibility**: public
- **Lines**: 70–74, body = 4 lines (match expression)
- **Notes**: Key API entry point; used by essentially every subsequent declaration.

---

### `@[simp] theorem projValuation_zero`
- **Type**: `projValuation (W := W) (0 : W.Point) = (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation`
- **What**: The projective place valuation at the point at infinity equals `ordAtInftyValuation`; a definitional unfolding tagged `@[simp]`.
- **How**: `rfl`.
- **Hypotheses**: None beyond context variables.
- **Uses from project**: `projValuation`
- **Used by**: (internal simp lemma; unused explicitly in this file)
- **Visibility**: public
- **Lines**: 76–78, proof = 1 line
- **Notes**: simp lemma.

---

### `@[simp] theorem projValuation_some`
- **Type**: `projValuation (W := W) (Affine.Point.some x y h) = (⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h⟩`
- **What**: The projective place valuation at an affine point equals `pointValuation`; definitional unfolding tagged `@[simp]`.
- **How**: `rfl`.
- **Hypotheses**: `h : W.Nonsingular x y`.
- **Uses from project**: `projValuation`
- **Used by**: (internal simp lemma; unused explicitly in this file)
- **Visibility**: public
- **Lines**: 80–82, proof = 1 line
- **Notes**: simp lemma.

---

### `theorem projValuation_surjective`
- **Type**: `∀ Q : W.Point, Function.Surjective (projValuation (W := W) Q)`
- **What**: The place valuation `projValuation Q` is surjective onto `WithZero (Multiplicative ℤ)` at every projective point.
- **How**: Cases on `Q`; each case delegates to the appropriate surjectivity lemma (`ordAtInftyValuation_surjective` or `pointValuation_surjective'`) from `SmoothPlaneCurve`.
- **Hypotheses**: None beyond context.
- **Uses from project**: `projValuation`, `SmoothPlaneCurve.ordAtInftyValuation_surjective`, `SmoothPlaneCurve.pointValuation_surjective'`
- **Used by**: `projValuation_injective`
- **Visibility**: public
- **Lines**: 85–89, proof = 5 lines

---

### `theorem projValuation_eq_exp_neg_projOrdAt`
- **Type**: `g ≠ 0 → ∀ Q : W.Point, projValuation (W := W) Q g = WithZero.exp (-(WeilPairing.DivisorPullback.projOrdAt g Q))`
- **What**: For nonzero `g`, the place valuation at `Q` equals `exp(−ordAt(g, Q))`, connecting the multiplicative valuation to the additive order at a projective point.
- **How**: Cases on `Q`; each branch uses `WithTop.ne_top_iff_exists` to unwrap the finite order, then `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq` or `pointValuation_eq_exp_neg_of_ord_P_eq` together with `projOrdAt_zero`/`projOrdAt_some`.
- **Hypotheses**: `g ≠ 0` (so the order is finite).
- **Uses from project**: `projValuation`, `WeilPairing.DivisorPullback.projOrdAt`, `SmoothPlaneCurve.ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`, `pointValuation_eq_exp_neg_of_ord_P_eq`, `DivisorPullback.projOrdAt_zero`, `DivisorPullback.projOrdAt_some`
- **Used by**: `projValuation_comap_pullback_eq_of_projOrdTransport`
- **Visibility**: public
- **Lines**: 93–112, proof = 19 lines

---

## Section: Lemma B — the `hproj` place identification

### `theorem projOrdAt_pullback_eq`
- **Type**: `ProjOrdTransport φ → ∀ g P, projOrdAt (φ.pullback g) P = projOrdAt g (φ.toAddMonoidHom P)`
- **What**: The order transport at a single projective point: the order of `φ*g` at `P` equals the order of `g` at `φ(P)`. This instantiates `ProjOrdTransport` at the smooth-point level.
- **How**: Applies `hproj g P.toProjectiveSmoothPoint` and rewrites via `Affine.Point.toProjectiveSmoothPoint_toAffinePoint`.
- **Hypotheses**: `hproj : ProjOrdTransport φ`.
- **Uses from project**: `WeilPairing.DivisorPullback.ProjOrdTransport`, `WeilPairing.DivisorPullback.projOrdAt`, `Affine.Point.toProjectiveSmoothPoint_toAffinePoint`
- **Used by**: `projValuation_comap_pullback_eq_of_projOrdTransport`
- **Visibility**: public
- **Lines**: 119–126, proof = 7 lines

---

### `theorem projValuation_comap_pullback_eq_of_projOrdTransport`
- **Type**: `ProjOrdTransport φ → ∀ P, (projValuation P).comap φ.pullback.toRingHom = projValuation (φ.toAddMonoidHom P)`
- **What**: Under `hproj`, the comap of the place at `P` along `φ.pullback` equals the place at `φ(P)`, value-precisely (no ramification factor). This is the exact order transport at the valuation level.
- **How**: `Valuation.ext`; zero case by `map_zero`; nonzero case uses `projValuation_eq_exp_neg_projOrdAt` on both sides and `projOrdAt_pullback_eq`. Injectivity of `φ.pullback` via `φ.pullback_injective`.
- **Hypotheses**: `hproj : ProjOrdTransport φ`.
- **Uses from project**: `projValuation`, `projValuation_eq_exp_neg_projOrdAt`, `projOrdAt_pullback_eq`, `HasseWeil.Isogeny.pullback_injective`
- **Used by**: `pointMap_eq_of_comap_isEquiv`
- **Visibility**: public
- **Lines**: 135–146, proof = 11 lines

---

## Section: Point ↔ place injectivity

### `theorem pointValuation_coordX_le_one`
- **Type**: `∀ P : SmoothPoint, pointValuation P coordX ≤ 1`
- **What**: The coordinate function `coordX` (= the image of `X` in the function field) is regular (value ≤ 1) at every affine smooth point.
- **How**: Rewrites `coordX` as `algebraMap (Polynomial F) CR` applied to `Polynomial.X`, composed through the coordinate ring; then applies `pointValuation_algebraMap_le_one`.
- **Hypotheses**: None beyond context.
- **Uses from project**: `SmoothPlaneCurve.coordX`, `SmoothPlaneCurve.pointValuation_algebraMap_le_one`
- **Used by**: `ordAtInftyValuation_ne_pointValuation`
- **Visibility**: public
- **Lines**: 152–161, proof = 9 lines

---

### `theorem ordAtInftyValuation_coordX`
- **Type**: `ordAtInftyValuation coordX = WithZero.exp (2 : ℤ)`
- **What**: `coordX` has a pole of order 2 at infinity, so its valuation at infinity equals `exp 2 > 1`.
- **How**: Uses `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq` with `ordAtInfty_coordX` (which gives order −2), then simplifies the double negation.
- **Hypotheses**: None.
- **Uses from project**: `SmoothPlaneCurve.ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`, `SmoothPlaneCurve.coordX_ne_zero`, `SmoothPlaneCurve.ordAtInfty_coordX`
- **Used by**: `ordAtInftyValuation_ne_pointValuation`
- **Visibility**: public
- **Lines**: 164–169, proof = 5 lines

---

### `theorem ordAtInftyValuation_ne_pointValuation`
- **Type**: `∀ P : SmoothPoint, ordAtInftyValuation ≠ pointValuation P`
- **What**: The infinity place is distinct from every affine place: `coordX` separates them (regular at affine points, pole of order 2 at infinity).
- **How**: Assume equality; evaluate at `coordX`; `ordAtInftyValuation_coordX` gives value `exp 2 > 1`, contradicting `pointValuation_coordX_le_one`.
- **Hypotheses**: None.
- **Uses from project**: `ordAtInftyValuation_coordX`, `pointValuation_coordX_le_one`, `WithZero.exp_zero`, `WithZero.exp_lt_exp`
- **Used by**: `projValuation_injective` (two calls)
- **Visibility**: public
- **Lines**: 173–186, proof = 13 lines

---

### `theorem projValuation_injective`
- **Type**: `(projValuation T₁).IsEquiv (projValuation T₂) → T₁ = T₂`
- **What**: Injectivity of the map `W.Point → place of K(E)` at the valuation level: equivalent place valuations come from the same projective point.
- **How**: Equivalent surjective `ℤᵐ⁰`-valuations are equal (`Valuation.isEquiv_eq_of_surjective_withZeroInt`); then case-split on the pair `(T₁, T₂)`: infinity vs infinity is `rfl`; infinity vs affine (or vice versa) is ruled out by `ordAtInftyValuation_ne_pointValuation`; affine vs affine reduces to equal `maximalIdealAt` via `pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`, then to equal coordinates via `maximalIdealAt_injective`.
- **Hypotheses**: None beyond the equivalence hypothesis.
- **Uses from project**: `projValuation_surjective`, `ordAtInftyValuation_ne_pointValuation`, `SmoothPlaneCurve.maximalIdealAt_injective`, `SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`, `Valuation.isEquiv_eq_of_surjective_withZeroInt`
- **Used by**: `pointMap_eq_of_comap_isEquiv`
- **Visibility**: public
- **Lines**: 192–223, proof = 31 lines
- **Notes**: Proof is 31 lines (just above the 30-line threshold).

---

### `theorem pointMap_eq_of_comap_isEquiv`
- **Type**: `ProjOrdTransport φ → (projValuation P).comap φ.pullback ≅ projValuation Q → φ(P) = Q`
- **What**: Lemma B: if the comap of the place at `P` along `φ.pullback` is equivalent to the place at `Q`, then `φ(P) = Q`.
- **How**: `projValuation_comap_pullback_eq_of_projOrdTransport` gives value-precise equality `(projValuation P).comap φ.pullback = projValuation (φ P)`; then `projValuation_injective` gives `φ P = Q`.
- **Hypotheses**: `hproj : ProjOrdTransport φ`, `hlie : comap isEquiv`.
- **Uses from project**: `projValuation_injective`, `projValuation_comap_pullback_eq_of_projOrdTransport`
- **Used by**: `surjective_of_PlaceLift_and_hproj`
- **Visibility**: public
- **Lines**: 231–238, proof = 7 lines

---

## Section: Lemma A — lying-over for valuation subrings

### `theorem comap_isNontrivial_of_finiteDimensional`
- **Type**: `[FiniteDimensional M L] → (v : Valuation L Γ₀) → [v.IsNontrivial] → (v.comap (algebraMap M L)).IsNontrivial`
- **What**: A nontrivial valuation on a finite extension `L/M` restricts nontrivially to `M`. This is the "place does not collapse" lemma that makes finiteness of the comorphism load-bearing.
- **How**: Pick a uniformizer `y ∈ L` with `v(y) < 1`; it is integral over `M` via `Algebra.IsAlgebraic.isAlgebraic`; its minimal polynomial has nonzero constant term by `minpoly.coeff_zero_ne_zero`. If the restriction were trivial, every nonzero `a : M` has `v(algebraMap a) = 1`; expand `aeval y (minpoly M y) = 0` as a sum; the constant term strictly dominates all higher-degree terms (since `v(y)^i ≤ v(y) < 1` for `i ≥ 1`) via `v.map_sum_eq_of_lt`; contradiction with `v(0) = 0`.
- **Hypotheses**: `M`, `L` fields, `[FiniteDimensional M L]`, `v : Valuation L Γ₀` nontrivial.
- **Uses from project**: none (pure mathlib/general algebra)
- **Used by**: (mentioned in module docstring; unused explicitly in this file — no direct call)
- **Visibility**: public
- **Lines**: 259–302, proof = 43 lines
- **Notes**: Proof is 43 lines (longest in the file). Pure general valuation theory; likely has mathlib overlap (Bourbaki VI §3 argument). No `set_option maxHeartbeats`. Not called within this file — dead-code candidate in-file.

---

### `theorem exists_valuationSubring_comap_le`
- **Type**: `∀ (O : ValuationSubring M), ∃ B : ValuationSubring L, O ≤ B.comap (algebraMap M L)`
- **What**: Lemma A: for any field extension `L/M` and any valuation ring `O` of `M`, there exists a valuation ring `B` of `L` lying above `O`.
- **How**: Uses `LocalSubring.map` to push `O.toLocalSubring` into `L`, then applies `LocalSubring.exists_le_valuationSubring` (Chevalley/Zorn). The domination condition gives the required subring inclusion.
- **Hypotheses**: Fields `M`, `L`, `[Algebra M L]`.
- **Uses from project**: none (uses `LocalSubring.map`, `LocalSubring.exists_le_valuationSubring` from mathlib)
- **Used by**: (mentioned in module docstring; unused explicitly in this file — no direct call)
- **Visibility**: public
- **Lines**: 311–320, proof = 9 lines
- **Notes**: Pure general valuation theory; no direct callers within this file — dead-code candidate in-file.

---

## Section: Lemma C — the surjectivity keystone

### `def PlaceLift`
- **Type**: `(φ : HasseWeil.Isogeny W W) → Prop`
- **What**: The place-lifting predicate: for every target point `Q`, some source point `P` has `(projValuation P).comap φ.pullback ≅ projValuation Q`. This packages the lying-over hypothesis for `φ`.
- **How**: Pure Prop definition by universal/existential quantification.
- **Hypotheses**: None (just a Prop).
- **Uses from project**: `projValuation`, `HasseWeil.Isogeny`
- **Used by**: `surjective_of_PlaceLift_and_hproj`, `surjective_of_finite_comorphism_and_hproj`
- **Visibility**: public
- **Lines**: 342–344, body = 2 lines

---

### `theorem surjective_of_PlaceLift_and_hproj`
- **Type**: `PlaceLift φ → ProjOrdTransport φ → Function.Surjective φ.toAddMonoidHom`
- **What**: Lemma C: if `φ` satisfies place-lifting and the per-place order transport, then `φ.toAddMonoidHom` is surjective.
- **How**: For each target `Q`, `PlaceLift` gives `P` with the comap equivalence; `pointMap_eq_of_comap_isEquiv` turns that into `φ(P) = Q`.
- **Hypotheses**: `hlift : PlaceLift φ`, `hproj : ProjOrdTransport φ`.
- **Uses from project**: `PlaceLift`, `pointMap_eq_of_comap_isEquiv`, `WeilPairing.DivisorPullback.ProjOrdTransport`
- **Used by**: `surjective_of_finite_comorphism_and_hproj`
- **Visibility**: public
- **Lines**: 352–357, proof = 5 lines

---

### `theorem surjective_of_finite_comorphism_and_hproj`
- **Type**: `PlaceLift φ → ProjOrdTransport φ → Function.Surjective φ.toAddMonoidHom`
- **What**: Identical to `surjective_of_PlaceLift_and_hproj`; a public alias under the "requested-name" form mentioned in the module docstring for API discoverability.
- **How**: Directly calls `surjective_of_PlaceLift_and_hproj hlift hproj`.
- **Hypotheses**: Same as `surjective_of_PlaceLift_and_hproj`.
- **Uses from project**: `surjective_of_PlaceLift_and_hproj`, `PlaceLift`, `WeilPairing.DivisorPullback.ProjOrdTransport`
- **Used by**: unused in file (leaf declaration, intended for external use)
- **Visibility**: public
- **Lines**: 375–378, proof = 2 lines
- **Notes**: Duplicate of `surjective_of_PlaceLift_and_hproj`; exists purely as a named API alias.

---

## Summary table

| Declaration | Kind | Lines | Proof lines | Sorry | Notes |
|---|---|---|---|---|---|
| `projValuation` | noncomputable def | 70–74 | 4 | no | Key API |
| `projValuation_zero` | @[simp] theorem | 76–78 | 1 | no | |
| `projValuation_some` | @[simp] theorem | 80–82 | 1 | no | |
| `projValuation_surjective` | theorem | 85–89 | 5 | no | |
| `projValuation_eq_exp_neg_projOrdAt` | theorem | 93–112 | 19 | no | |
| `projOrdAt_pullback_eq` | theorem | 119–126 | 7 | no | |
| `projValuation_comap_pullback_eq_of_projOrdTransport` | theorem | 135–146 | 11 | no | |
| `pointValuation_coordX_le_one` | theorem | 152–161 | 9 | no | |
| `ordAtInftyValuation_coordX` | theorem | 164–169 | 5 | no | |
| `ordAtInftyValuation_ne_pointValuation` | theorem | 173–186 | 13 | no | |
| `projValuation_injective` | theorem | 192–223 | 31 | no | Long proof |
| `pointMap_eq_of_comap_isEquiv` | theorem | 231–238 | 7 | no | |
| `comap_isNontrivial_of_finiteDimensional` | theorem | 259–302 | 43 | no | Long proof, unused in file |
| `exists_valuationSubring_comap_le` | theorem | 311–320 | 9 | no | Unused in file |
| `PlaceLift` | def | 342–344 | 2 | no | |
| `surjective_of_PlaceLift_and_hproj` | theorem | 352–357 | 5 | no | |
| `surjective_of_finite_comorphism_and_hproj` | theorem | 375–378 | 2 | no | Alias/duplicate |
