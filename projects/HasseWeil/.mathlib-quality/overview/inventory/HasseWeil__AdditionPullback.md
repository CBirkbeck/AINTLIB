# Inventory: ./HasseWeil/AdditionPullback.lean

**File**: `HasseWeil/AdditionPullback.lean`
**Total lines**: 1318
**Purpose**: Constructs the function-field pullback of the map `P ↦ α₁(P) + α₂(P)` (addition of two isogenies) on the function field `K(E)`, using Weierstrass addition formulas. Provides both the single-isogeny `id + α` version and the general pair version `α₁ + α₂`. Also develops the transcendence-based injectivity theory needed to extend `CoordinateRing → K(E)` to a field automorphism `K(E) → K(E)`.

**Imports**: `HasseWeil.Basic`, `HasseWeil.MulByIntPullback`, `HasseWeil.OrdAtInftyBridge`, `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula`, `Mathlib.RingTheory.Algebraic.Integral`

---

## Declarations

### `noncomputable instance instDecidableEqFunctionField`
- **Type**: `DecidableEq KE`
- **What**: Provides a `DecidableEq` instance for the function field `KE = W.toAffine.FunctionField`, using classical decidability.
- **How**: `Classical.dec (a = b)`.
- **Hypotheses**: `[Field F] [DecidableEq F] [W.toAffine.IsElliptic]`
- **Uses from project**: none (just `Classical.dec`)
- **Used by**: implicit in all downstream computations needing `DecidableEq KE`
- **Visibility**: public (local instance)
- **Lines**: 39–41, proof length 1 line
- **Notes**: none

---

### `theorem pullback_equation`
- **Type**: `(α : Isogeny W.toAffine W.toAffine) → (W_KE W).toAffine.Equation (α.pullback (x_gen W)) (α.pullback (y_gen W))`
- **What**: The pullback of the generic point `(x_gen, y_gen)` under any isogeny `α` lies on the base-changed Weierstrass curve over `K(E)`, i.e., still satisfies the Weierstrass equation.
- **How**: Applies `Affine.Equation.map` to `generic_equation W` with `α.pullback.toRingHom`, then uses `α.pullback.commutes` to show the base-changed curve equals `W_KE W`.
- **Hypotheses**: `W` an elliptic curve, `α` an isogeny.
- **Uses from project**: `W_KE`, `x_gen`, `y_gen`, `generic_equation`
- **Used by**: `addPullback_equation`, `addPullback_pair_equation`
- **Visibility**: public
- **Lines**: 47–53, proof length 6 lines
- **Notes**: none

---

### `noncomputable def addSlope`
- **Type**: `KE`
- **What**: The slope of the chord connecting the generic point `(x_gen, y_gen)` and its image `(α(x_gen), α(y_gen))` on `W_KE`, computed by the Weierstrass `slope` formula.
- **How**: Direct application of `WeierstrassCurve.Affine.slope`.
- **Hypotheses**: `α : Isogeny W.toAffine W.toAffine`
- **Uses from project**: `W_KE`, `x_gen`, `y_gen`
- **Used by**: `addPullback_x`, `addPullback_y`
- **Visibility**: public
- **Lines**: 60–63, definition only

---

### `noncomputable def addPullback_x`
- **Type**: `KE`
- **What**: The x-coordinate of `P + α(P)` for the generic point `P`, computed via the Weierstrass addition formula `addX`.
- **How**: `(W_KE W).toAffine.addX x_gen (α.pullback x_gen) (addSlope W α)`.
- **Hypotheses**: `α : Isogeny W.toAffine W.toAffine`
- **Uses from project**: `W_KE`, `x_gen`, `addSlope`
- **Used by**: `addBaseHom`, `addPullback_equation`, `addPullback_poly_eval₂_zero`, `addCoordRingHom`, `addCoordAlgHom`, `addPullback_x_ne_const`, `addPullback_x_ne_const_of_pole`, `addPullback_x_quadratic_over_F_case_two`, `addPullback_x_quadratic_over_F`, `minpoly_not_const_degree_two`, `addPullback_x_transcendental`, `addBaseHom_eq_aeval`, `addBaseHom_injective`; and many downstream files
- **Visibility**: public
- **Lines**: 65–67, definition only

---

### `noncomputable def addPullback_y`
- **Type**: `KE`
- **What**: The y-coordinate of `P + α(P)` for the generic point `P`, computed via the Weierstrass addition formula `addY`.
- **How**: `(W_KE W).toAffine.addY x_gen (α.pullback x_gen) y_gen (addSlope W α)`.
- **Hypotheses**: `α : Isogeny W.toAffine W.toAffine`
- **Uses from project**: `W_KE`, `x_gen`, `y_gen`, `addSlope`
- **Used by**: `addPullback_equation`, `addPullback_poly_eval₂_zero`, `addCoordRingHom`, `addCoordAlgHom`, `addCoordAlgHom_injective_of_baseHom_inj`, and downstream files
- **Visibility**: public
- **Lines**: 69–71, definition only

---

### `noncomputable def addBaseHom`
- **Type**: `Polynomial F →+* KE`
- **What**: The base ring hom `F[X] →+* K(E)` that sends the polynomial variable `X` to `addPullback_x W α`.
- **How**: `Polynomial.eval₂RingHom (algebraMap F KE) (addPullback_x W α)`.
- **Hypotheses**: `α : Isogeny W.toAffine W.toAffine`
- **Uses from project**: `addPullback_x`
- **Used by**: `addPullback_poly_eval₂_zero`, `addCoordRingHom`, `addCoordAlgHom`, `addBaseHom_eq_aeval`, `addBaseHom_injective`, `addCoordAlgHom_injective_of_baseHom_inj`
- **Visibility**: public
- **Lines**: 73–75, definition only

---

### `abbrev AddNonInverse`
- **Type**: `Prop` — negation of: `x_gen W = α.pullback (x_gen W) ∧ y_gen W = (W_KE W).toAffine.negY (α.pullback x_gen) (α.pullback y_gen)`
- **What**: Hypothesis that the generic point and its α-image are not additive inverses on `W_KE`; necessary for the Weierstrass addition formula to be valid (the formula breaks at inverse pairs).
- **How**: Definitional abbreviation (a negated conjunction).
- **Hypotheses**: none (abbreviation over section variables)
- **Uses from project**: `x_gen`, `y_gen`, `W_KE`
- **Used by**: `addPullback_equation`, `addPullback_poly_eval₂_zero`, `addCoordRingHom`, `addCoordAlgHom`, `addPullbackAlgHom`, `addPullback_x_ne_const`, `addPullback_x_ne_const_of_pole`, `minpoly_not_const_degree_two`, `addPullback_x_transcendental`, `addBaseHom_injective`, `addCoordAlgHom_injective_of_baseHom_inj`, `addCoordAlgHom_injective`
- **Visibility**: public
- **Lines**: 79–82

---

### `theorem addPullback_equation`
- **Type**: `AddNonInverse W α → (W_KE W).toAffine.Equation (addPullback_x W α) (addPullback_y W α)`
- **What**: The addition formula outputs `(addPullback_x, addPullback_y)` satisfy the Weierstrass equation, given the non-inverse hypothesis.
- **How**: Direct application of `Affine.equation_add` to `generic_equation W` and `pullback_equation W α`.
- **Hypotheses**: `AddNonInverse W α`
- **Uses from project**: `addPullback_x`, `addPullback_y`, `generic_equation`, `pullback_equation`
- **Used by**: `addPullback_poly_eval₂_zero`
- **Visibility**: public
- **Lines**: 87–89, proof length 1 line

---

### `theorem addPullback_poly_eval₂_zero`
- **Type**: `AddNonInverse W α → W.toAffine.polynomial.eval₂ (addBaseHom W α) (addPullback_y W α) = 0`
- **What**: The Weierstrass polynomial vanishes when evaluated at the addition coordinates via `addBaseHom`, bridging `Equation` to the `eval₂` form needed by `AdjoinRoot.lift`.
- **How**: Rewrites via `Polynomial.eval₂_eval₂RingHom_apply` and `Affine.map_polynomial`, then applies `addPullback_equation`.
- **Hypotheses**: `AddNonInverse W α`
- **Uses from project**: `addBaseHom`, `addPullback_y`, `addPullback_equation`
- **Used by**: `addCoordRingHom`
- **Visibility**: public
- **Lines**: 93–97, proof length 4 lines

---

### `noncomputable def addCoordRingHom`
- **Type**: `AddNonInverse W α → R →+* KE`
- **What**: The ring homomorphism `CoordinateRing → K(E)` sending the coordinate generators `X, Y` to the addition formula outputs.
- **How**: `AdjoinRoot.lift (addBaseHom W α) (addPullback_y W α) (addPullback_poly_eval₂_zero hxy)`.
- **Hypotheses**: `AddNonInverse W α`
- **Uses from project**: `addBaseHom`, `addPullback_y`, `addPullback_poly_eval₂_zero`
- **Used by**: `addCoordAlgHom`, `addCoordAlgHom_injective_of_baseHom_inj`
- **Visibility**: public
- **Lines**: 100–101, definition only

---

### `noncomputable def addCoordAlgHom`
- **Type**: `AddNonInverse W α → R →ₐ[F] KE`
- **What**: The coordinate ring ring hom `addCoordRingHom` promoted to an F-algebra hom.
- **How**: Wraps `addCoordRingHom hxy` and proves `commutes` using `AdjoinRoot.lift_mk`, `Polynomial.eval₂_C`, and simp for the scalar tower.
- **Hypotheses**: `AddNonInverse W α`
- **Uses from project**: `addCoordRingHom`, `addBaseHom`
- **Used by**: `addPullbackAlgHom`, `addCoordAlgHom_injective`, `addCoordAlgHom_injective_of_baseHom_inj`; also `addCoordAlgHomPair_id`
- **Visibility**: public
- **Lines**: 104–116, proof length 11 lines

---

### `noncomputable def addPullbackAlgHom`
- **Type**: `(hxy : AddNonInverse W α) → Function.Injective (addCoordAlgHom hxy) → KE →ₐ[F] KE`
- **What**: The function-field algebra automorphism `K(E) →ₐ[F] K(E)` representing the pullback of `P ↦ P + α(P)`, extending the injective coordinate ring hom via `IsFractionRing.liftAlgHom`.
- **How**: `IsFractionRing.liftAlgHom hinj`.
- **Hypotheses**: `AddNonInverse W α`, injectivity of `addCoordAlgHom hxy`
- **Uses from project**: `addCoordAlgHom`
- **Used by**: downstream files (e.g., `Frobenius.lean`, `RouteBInduction.lean`); also `addPullbackAlgHomPair_id`
- **Visibility**: public
- **Lines**: 126–130, definition only

---

### `theorem addBaseHom_eq_aeval`
- **Type**: `(addBaseHom W α : Polynomial F →+* KE) = (Polynomial.aeval (addPullback_x W α) : Polynomial F →ₐ[F] KE).toRingHom`
- **What**: The base ring hom `addBaseHom` equals the aeval map at `addPullback_x`, allowing use of `transcendental_iff_injective`.
- **How**: `ext; simp [addBaseHom, Polynomial.aeval_def]`.
- **Hypotheses**: none
- **Uses from project**: `addBaseHom`, `addPullback_x`
- **Used by**: `addBaseHom_injective`; also used in `AdditionPullback/Frobenius.lean`
- **Visibility**: public (`set_option linter.unusedSectionVars false in`)
- **Lines**: 133–139, proof length 2 lines

---

### `theorem algebraic_in_fracRing_eq_const`
- **Type**: `(z : FractionRing (Polynomial F)) → IsAlgebraic F z → ∃ c : F, z = algebraMap F (FractionRing (Polynomial F)) c`
- **What**: Any element of `FractionRing F[X]` that is algebraic over `F` is actually a constant: the algebraic closure of `F` in its purely transcendental extension `F(X)` is `F` itself.
- **How**: Integral over `F` implies integral over `F[X]` (tower), then `IsIntegrallyClosed.isIntegral_iff` puts it in `F[X]`. Case split on `natDegree`: degree-0 gives a constant; positive degree uses `Polynomial.transcendental` (via `transcendental_algebraMap_iff`) to contradict algebraicity.
- **Hypotheses**: `z : FractionRing (Polynomial F)`, `IsAlgebraic F z`
- **Uses from project**: none (pure mathlib argument)
- **Used by**: `addPullback_x_quadratic_over_F`, `addPullback_x_transcendental`
- **Visibility**: public
- **Lines**: 143–169, proof length 26 lines

---

### `private lemma addPullback_x_ne_const`
- **Type**: `AddNonInverse W α → (c : F) → addPullback_x W α = algebraMap F KE c → False`
- **What**: If `addPullback_x W α` equals a constant from `F`, this is a contradiction. The proof reduces to the pole witness: a constant has `ord_∞ ∈ {0, ⊤}`, never `< 0`.
- **How**: Asserts `sorry` for the pole witness `ord_∞(addPullback_x) < 0`, then case-splits on `c = 0` using `ordAtInfty_zero` and `ordAtInfty_algebraMap_F_nonzero`.
- **Hypotheses**: `AddNonInverse W α`, `hc : addPullback_x W α = algebraMap F KE c`
- **Uses from project**: `addPullback_x`, `W_smooth`, `ordAtInfty_algebraMap_F_nonzero`
- **Used by**: `addPullback_x_transcendental`
- **Visibility**: private
- **Lines**: 194–212, proof length 18 lines
- **Notes**: Contains `sorry` (the pole witness `ord_∞(addPullback_x) < 0`). The sorry is the only gap; the surrounding case analysis is complete.

---

### `theorem addPullback_x_ne_const_of_pole`
- **Type**: `AddNonInverse W α → (c : F) → (W_smooth W).ordAtInfty (addPullback_x W α) < 0 → addPullback_x W α = algebraMap F KE c → False`
- **What**: The witness-parametric form: given the pole hypothesis `ord_∞ < 0` explicitly, `addPullback_x` cannot be a constant. This is the axiom-clean version of `addPullback_x_ne_const`.
- **How**: Case split on `c = 0`: `c = 0` gives `addPullback_x = 0` hence `ord = ⊤`, contradicting `< 0`; `c ≠ 0` gives `ord = 0` via `ordAtInfty_algebraMap_F_nonzero`, also contradicting `< 0`.
- **Hypotheses**: `AddNonInverse W α`, `h_pole : (W_smooth W).ordAtInfty (addPullback_x W α) < 0`, `hc : addPullback_x W α = algebraMap F KE c`
- **Uses from project**: `addPullback_x`, `W_smooth`, `ordAtInfty_algebraMap_F_nonzero`
- **Used by**: unused in this file (external consumers for the axiom-clean variant)
- **Visibility**: public
- **Lines**: 228–242, proof length 14 lines

---

### `private lemma minpoly_F_monic_irreducible_in_F_x_gen`
- **Type**: `{α : KE} → IsAlgebraic F α → Irreducible ((minpoly F α).map (algebraMap F (FractionRing (Polynomial F))))`
- **What**: The F-minpoly of an F-algebraic element of `KE`, when pushed forward to `FractionRing(F[X])` via `algebraMap F`, remains irreducible in `(FractionRing F[X])[T]`.
- **How**: Two-step: (Step 1) Shows `(minpoly F α).map (algebraMap F (Polynomial F))` is irreducible in `F[X][T]` by lifting factorizations back to `F[T]` via evaluation at `X = 0` and using irreducibility of `minpoly F α`; leading-coefficient arguments ensure units propagate. (Step 2) Applies `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` (Gauss lemma, `F[X]` integrally closed as UFD) and `Polynomial.map_map` + `IsScalarTower` to compose.
- **Hypotheses**: `IsAlgebraic F α`
- **Uses from project**: none (pure mathlib)
- **Used by**: `minpoly_F_x_gen_eq_minpoly_F_map`
- **Visibility**: private
- **Lines**: 295–364, proof length 69 lines
- **Notes**: Long proof (69 lines); no sorry. Key mathlib lemma: `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` (Gauss lemma). The evaluation-at-0 trick for step 1 is non-standard.

---

### `private lemma minpoly_F_x_gen_eq_minpoly_F_map`
- **Type**: `{α : KE} → IsAlgebraic F α → minpoly (FractionRing (Polynomial F)) α = (minpoly F α).map (algebraMap F (FractionRing (Polynomial F)))`
- **What**: The `F(x_gen)`-minimal polynomial of an F-algebraic element equals the `algebraMap`-image of the F-minimal polynomial; i.e., the minpoly is stable under scalar extension from `F` to `F(X)`.
- **How**: Uses `minpoly_F_monic_irreducible_in_F_x_gen` for irreducibility, `Polynomial.Monic.map` for monicity, `Polynomial.aeval_map_algebraMap` + `minpoly.aeval F α` for evaluation at zero, then `minpoly.eq_of_irreducible_of_monic` for uniqueness.
- **Hypotheses**: `IsAlgebraic F α`
- **Uses from project**: `minpoly_F_monic_irreducible_in_F_x_gen`
- **Used by**: `addPullback_x_quadratic_over_F_case_two`
- **Visibility**: private
- **Lines**: 377–393, proof length 16 lines

---

### `private lemma minpoly_F_x_gen_natDegree_le_two`
- **Type**: `(α : KE) → IsIntegral (FractionRing (Polynomial F)) α → Module.finrank (FractionRing (Polynomial F)) KE = 2 → (minpoly (FractionRing (Polynomial F)) α).natDegree ≤ 2`
- **What**: The `F(x_gen)`-minpoly of any element of `KE` has degree at most 2, since `[KE : F(x_gen)] = 2`.
- **How**: Derives `FiniteDimensional` from `finrank = 2 > 0` via `Module.finite_of_finrank_pos`, then applies `minpoly.natDegree_le` and the finrank bound.
- **Hypotheses**: `IsIntegral (FractionRing (Polynomial F)) α`, `Module.finrank (FractionRing (Polynomial F)) KE = 2`
- **Uses from project**: none
- **Used by**: `addPullback_x_quadratic_over_F_case_two`
- **Visibility**: private
- **Lines**: 416–424, proof length 8 lines

---

### `private lemma addPullback_x_quadratic_over_F_case_two`
- **Type**: `IsAlgebraic F (addPullback_x W α) → Module.finrank (FractionRing (Polynomial F)) KE = 2 → (¬ ∃ r : FractionRing (Polynomial F), addPullback_x W α = algebraMap ... r) → ∃ c₁ c₀ : F, (addPullback_x W α)² - algebraMap F KE c₁ * addPullback_x W α + algebraMap F KE c₀ = 0`
- **What**: Case 2 of the quadratic-over-F extraction: when `addPullback_x` is not in `F(x_gen)`, uses the three sub-lemmas to extract degree-2 F-polynomial satisfied by `addPullback_x`.
- **How**: Applies `minpoly_F_x_gen_natDegree_le_two` (degree ≤ 2), `minpoly.two_le_natDegree_iff` (degree ≥ 2), deduces degree = 2; then `minpoly_F_x_gen_eq_minpoly_F_map` to descend coefficients to `F`; unpacks via `minpoly.aeval`, `Polynomial.aeval_eq_sum_range`, and `linear_combination`.
- **Hypotheses**: algebraicity, finrank = 2, `px ∉ F(x_gen)`
- **Uses from project**: `addPullback_x`, `minpoly_F_x_gen_eq_minpoly_F_map`, `minpoly_F_x_gen_natDegree_le_two`
- **Used by**: `addPullback_x_quadratic_over_F`
- **Visibility**: private
- **Lines**: 445–494, proof length 49 lines
- **Notes**: Long proof (49 lines); no sorry. Uses `SmoothPlaneCurve.exists_decomp`, `SmoothPlaneCurve.decomp_from_quadratic`, `polynomialDiscriminant_eq_trace_sq_sub_four_norm`, `polynomialDiscriminant_natDegree` — but wait, on inspection this lemma (445–494) does NOT use `SmoothPlaneCurve`; those are in `minpoly_not_const_degree_two` (573–731).

---

### `private lemma addPullback_x_quadratic_over_F`
- **Type**: `IsAlgebraic F (addPullback_x W α) → Module.finrank (FractionRing (Polynomial F)) KE = 2 → ∃ c₁ c₀ : F, (addPullback_x W α)² - algebraMap F KE c₁ * addPullback_x W α + algebraMap F KE c₀ = 0`
- **What**: If `addPullback_x W α` is algebraic over `F`, it satisfies a monic quadratic over `F`.
- **How**: Case split on whether `px ∈ F(x_gen)`: (Case 1) applies `algebraic_in_fracRing_eq_const` to get `px = algebraMap F KE c`, then the quadratic `(T - c)² = T² - 2cT + c²` works; (Case 2) delegates to `addPullback_x_quadratic_over_F_case_two`.
- **Hypotheses**: `IsAlgebraic F (addPullback_x W α)`, `Module.finrank (FractionRing (Polynomial F)) KE = 2`
- **Uses from project**: `addPullback_x`, `algebraic_in_fracRing_eq_const`, `addPullback_x_quadratic_over_F_case_two`
- **Used by**: `addPullback_x_transcendental`
- **Visibility**: private
- **Lines**: 506–539, proof length 33 lines
- **Notes**: Proof > 30 lines. The Case 1 branch is axiom-clean; Case 2 inherits the sub-lemmas.

---

### `private lemma minpoly_not_const_degree_two`
- **Type**: `[NeZero (2 : F)] → AddNonInverse W α → Module.finrank ... KE = 2 → IsAlgebraic F (addPullback_x W α) → (c₁ c₀ : F) → (addPullback_x W α)² - c₁·addPullback_x + c₀ = 0 → (¬ ∃ r ..., addPullback_x = algebraMap ... r) → False`
- **What**: The monic quadratic `T² - c₁T + c₀ ∈ F[T]` cannot be the minpoly of `addPullback_x` over `F(x_gen)` (for non-inverse `α`). Degree-parity argument via the curve discriminant of `W_smooth`.
- **How**: Decomposes `px` in the `F(x_gen)`-basis `{1, y_gen}` of `KE` (via `C.exists_decomp`); uses `C.decomp_from_quadratic` to extract linear algebra constraints; applies `polynomialDiscriminant_eq_trace_sq_sub_four_norm` to get a polynomial identity; clears denominators and derives the degree contradiction `2·deg(v) = 2·deg(u) + 3` (impossible mod 2).
- **Hypotheses**: `[NeZero (2 : F)]`, `AddNonInverse W α`, finrank = 2, algebraicity, concrete coefficients `c₁, c₀ : F` satisfying the quadratic, and `px ∉ F(x_gen)`
- **Uses from project**: `addPullback_x`, `W_smooth`, `Curves.SmoothPlaneCurve.exists_decomp`, `Curves.SmoothPlaneCurve.decomp_from_quadratic`, `Curves.SmoothPlaneCurve.bFracPoly`, `Curves.SmoothPlaneCurve.cFracPoly`, `Curves.SmoothPlaneCurve.coordYInFunctionField`, `polynomialDiscriminant_eq_trace_sq_sub_four_norm`, `polynomialDiscriminant_ne_zero`, `polynomialDiscriminant_natDegree`
- **Used by**: `addPullback_x_transcendental`
- **Visibility**: private
- **Lines**: 573–731, proof length ~158 lines
- **Notes**: Very long proof (158 lines); no sorry. This is the most complex proof in the file. Requires `[NeZero (2 : F)]` for char ≠ 2. Uses heavy `SmoothPlaneCurve` infrastructure from the project.

---

### `private lemma addPullback_x_transcendental`
- **Type**: `[NeZero (2 : F)] → AddNonInverse W α → Transcendental F (addPullback_x W α)`
- **What**: The x-coordinate of `P + α(P)` is transcendental over `F` (for any non-inverse isogeny `α` over a field of characteristic ≠ 2).
- **How**: By contradiction: if algebraic, `addPullback_x_quadratic_over_F` gives coefficients `c₁, c₀`; case splits on `px ∈ F(x_gen)`: in the yes-case, `algebraic_in_fracRing_eq_const` gives `px ∈ F`, contradicting `addPullback_x_ne_const`; in the no-case, `minpoly_not_const_degree_two` gives contradiction.
- **Hypotheses**: `[NeZero (2 : F)]`, `AddNonInverse W α`
- **Uses from project**: `addPullback_x`, `algebraic_in_fracRing_eq_const`, `addPullback_x_quadratic_over_F`, `minpoly_not_const_degree_two`, `addPullback_x_ne_const`, `WeierstrassCurve.degree_functionField_over_kx`
- **Used by**: `addBaseHom_injective`
- **Visibility**: private
- **Lines**: 746–837, proof length 91 lines
- **Notes**: Very long proof (91 lines). No sorry in this lemma itself, but calls `addPullback_x_ne_const` which contains a sorry (the pole witness). So this lemma is transitively sorry-bearing.

---

### `private lemma addBaseHom_injective`
- **Type**: `[NeZero (2 : F)] → AddNonInverse W α → Function.Injective (addBaseHom W α)`
- **What**: The base ring hom `addBaseHom W α : F[X] →+* KE` is injective (since `addPullback_x` is transcendental).
- **How**: Uses `addBaseHom_eq_aeval` to convert to `aeval` form, then `transcendental_iff_injective.mp (addPullback_x_transcendental hxy)`.
- **Hypotheses**: `[NeZero (2 : F)]`, `AddNonInverse W α`
- **Uses from project**: `addBaseHom`, `addBaseHom_eq_aeval`, `addPullback_x_transcendental`
- **Used by**: `addCoordAlgHom_injective`
- **Visibility**: private
- **Lines**: 841–844, proof length 3 lines
- **Notes**: Sorry-bearing (transitively via `addPullback_x_transcendental` → `addPullback_x_ne_const`).

---

### `theorem addCoordAlgHom_injective_of_baseHom_inj`
- **Type**: `AddNonInverse W α → Function.Injective (addBaseHom W α) → Function.Injective (addCoordAlgHom hxy)`
- **What**: Injectivity of `addCoordAlgHom` follows from injectivity of the base ring hom `addBaseHom`. This is the witness-parametric form, allowing axiom-clean callers (e.g., negFrobenius case) to supply their own injectivity proof.
- **How**: Reduces to injectivity of `addCoordRingHom`; uses `Affine.CoordinateRing.exists_smul_basis_eq` to decompose elements in the basis `{1, Y}`; handles `q = 0` case via base-hom injectivity directly; handles `q ≠ 0` case by computing `Algebra.norm` via `Affine.CoordinateRing.coe_norm_smul_basis` and `Affine.CoordinateRing.degree_norm_smul_basis`, deriving a degree contradiction.
- **Hypotheses**: `AddNonInverse W α`, `Function.Injective (addBaseHom W α)`
- **Uses from project**: `addCoordRingHom`, `addBaseHom`, `addPullback_y`; mathlib: `Affine.CoordinateRing.exists_smul_basis_eq`, `Affine.CoordinateRing.coe_norm_smul_basis`, `Affine.CoordinateRing.degree_norm_smul_basis`
- **Used by**: `addCoordAlgHom_injective`; also `AdditionPullback/Frobenius.lean`
- **Visibility**: public
- **Lines**: 857–942, proof length 85 lines
- **Notes**: Very long proof (85 lines). No sorry.

---

### `theorem addCoordAlgHom_injective`
- **Type**: `[NeZero (2 : F)] → AddNonInverse W α → Function.Injective (addCoordAlgHom hxy)`
- **What**: The coordinate ring algebra hom `addCoordAlgHom hxy` is injective (in char ≠ 2).
- **How**: Thin wrapper: calls `addCoordAlgHom_injective_of_baseHom_inj` with `addBaseHom_injective`.
- **Hypotheses**: `[NeZero (2 : F)]`, `AddNonInverse W α`
- **Uses from project**: `addCoordAlgHom`, `addCoordAlgHom_injective_of_baseHom_inj`, `addBaseHom_injective`
- **Used by**: unused in this file (external callers)
- **Visibility**: public
- **Lines**: 952–955, proof length 1 line
- **Notes**: Sorry-bearing (transitively).

---

### `noncomputable def addSlopePair`
- **Type**: `(α₁ α₂ : Isogeny W.toAffine W.toAffine) → KE`
- **What**: The slope of the chord connecting `(α₁(x_gen), α₁(y_gen))` and `(α₂(x_gen), α₂(y_gen))` — the slope for the addition of two arbitrary isogeny images.
- **How**: `(W_KE W).toAffine.slope (α₁.pullback x_gen) (α₂.pullback x_gen) (α₁.pullback y_gen) (α₂.pullback y_gen)`.
- **Hypotheses**: none
- **Uses from project**: `W_KE`, `x_gen`, `y_gen`
- **Used by**: `addPullback_x_pair`, `addPullback_y_pair`, `addSlopePair_id`, `addSlopePair_eq_of_x_ne`, `addSlopePair_sigma_sum_eq_neg_a1`, `addPullback_x_pair_sigma_invariant`
- **Visibility**: public
- **Lines**: 970–972, definition only

---

### `noncomputable def addPullback_x_pair`
- **Type**: `(α₁ α₂ : Isogeny W.toAffine W.toAffine) → KE`
- **What**: The x-coordinate of `α₁(P) + α₂(P)` for the generic point P.
- **How**: `(W_KE W).toAffine.addX (α₁.pullback x_gen) (α₂.pullback x_gen) (addSlopePair α₁ α₂)`.
- **Hypotheses**: none
- **Uses from project**: `W_KE`, `x_gen`, `addSlopePair`
- **Used by**: `addBaseHomPair`, `addPullback_pair_equation`, `addPullback_x_pair_id`, `addBaseHomPair_eq_aeval`, `addCoordAlgHomPair_injective_of_baseHom_inj`, `addPullback_x_pair_sigma_invariant`; many downstream files
- **Visibility**: public
- **Lines**: 975–977, definition only

---

### `noncomputable def addPullback_y_pair`
- **Type**: `(α₁ α₂ : Isogeny W.toAffine W.toAffine) → KE`
- **What**: The y-coordinate of `α₁(P) + α₂(P)` for the generic point P.
- **How**: `(W_KE W).toAffine.addY (α₁.pullback x_gen) (α₂.pullback x_gen) (α₁.pullback y_gen) (addSlopePair α₁ α₂)`.
- **Hypotheses**: none
- **Uses from project**: `W_KE`, `x_gen`, `y_gen`, `addSlopePair`
- **Used by**: `addPullback_pair_equation`, `addCoordRingHomPair`, `addCoordAlgHomPair`, `addPullback_y_pair_id`, `addCoordAlgHomPair_injective_of_baseHom_inj`; downstream files
- **Visibility**: public
- **Lines**: 980–982, definition only

---

### `abbrev AddNonInversePair`
- **Type**: `(α₁ α₂ : Isogeny W.toAffine W.toAffine) → Prop`
- **What**: The hypothesis that `(α₁(x_gen), α₁(y_gen))` and `(α₂(x_gen), α₂(y_gen))` are not additive inverses on `W_KE`. The pair analogue of `AddNonInverse`.
- **How**: Definitional abbreviation.
- **Hypotheses**: none
- **Uses from project**: `x_gen`, `y_gen`, `W_KE`
- **Used by**: `addPullback_pair_equation`, `addPullback_pair_poly_eval₂_zero`, `addCoordRingHomPair`, `addCoordAlgHomPair`, `addPullbackAlgHomPair`, `addIsog`, many `@[simp]` bridge lemmas, `AddNonInversePair_id`, `AddNonInversePair_of_x_ne`, `AddNonInversePair_of_y_ne`, `addCoordAlgHomPair_injective_of_baseHom_inj`, `addSlopePair_sigma_sum_eq_neg_a1`, `addPullback_x_pair_sigma_invariant`; many downstream files
- **Visibility**: public
- **Lines**: 986–989

---

### `theorem addPullback_pair_equation`
- **Type**: `AddNonInversePair α₁ α₂ → (W_KE W).toAffine.Equation (addPullback_x_pair α₁ α₂) (addPullback_y_pair α₁ α₂)`
- **What**: The pair addition outputs satisfy the Weierstrass equation.
- **How**: `Affine.equation_add (pullback_equation W α₁) (pullback_equation W α₂) hxy`.
- **Hypotheses**: `AddNonInversePair α₁ α₂`
- **Uses from project**: `addPullback_x_pair`, `addPullback_y_pair`, `pullback_equation`
- **Used by**: `addPullback_pair_poly_eval₂_zero`
- **Visibility**: public
- **Lines**: 993–997, proof length 1 line

---

### `noncomputable def addBaseHomPair`
- **Type**: `(α₁ α₂ : Isogeny W.toAffine W.toAffine) → Polynomial F →+* KE`
- **What**: The base ring hom sending `X ↦ addPullback_x_pair α₁ α₂`.
- **How**: `Polynomial.eval₂RingHom (algebraMap F KE) (addPullback_x_pair α₁ α₂)`.
- **Hypotheses**: none
- **Uses from project**: `addPullback_x_pair`
- **Used by**: `addPullback_pair_poly_eval₂_zero`, `addCoordRingHomPair`, `addCoordAlgHomPair`, `addBaseHomPair_id`, `addBaseHomPair_eq_aeval`, `addCoordAlgHomPair_injective_of_baseHom_inj`; downstream files
- **Visibility**: public
- **Lines**: 1000–1002, definition only

---

### `theorem addPullback_pair_poly_eval₂_zero`
- **Type**: `AddNonInversePair α₁ α₂ → W.toAffine.polynomial.eval₂ (addBaseHomPair α₁ α₂) (addPullback_y_pair α₁ α₂) = 0`
- **What**: The Weierstrass polynomial vanishes at the pair addition coordinates via `addBaseHomPair`.
- **How**: Same pattern as the single-isogeny case: `Polynomial.eval₂_eval₂RingHom_apply`, `Affine.map_polynomial`, then `addPullback_pair_equation`.
- **Hypotheses**: `AddNonInversePair α₁ α₂`
- **Uses from project**: `addBaseHomPair`, `addPullback_y_pair`, `addPullback_pair_equation`
- **Used by**: `addCoordRingHomPair`
- **Visibility**: public
- **Lines**: 1005–1011, proof length 4 lines

---

### `noncomputable def addCoordRingHomPair`
- **Type**: `AddNonInversePair α₁ α₂ → R →+* KE`
- **What**: The coordinate ring ring hom for the pair addition, built via `AdjoinRoot.lift`.
- **How**: `AdjoinRoot.lift (addBaseHomPair α₁ α₂) (addPullback_y_pair α₁ α₂) (addPullback_pair_poly_eval₂_zero hxy)`.
- **Hypotheses**: `AddNonInversePair α₁ α₂`
- **Uses from project**: `addBaseHomPair`, `addPullback_y_pair`, `addPullback_pair_poly_eval₂_zero`
- **Used by**: `addCoordAlgHomPair`, `addCoordRingHomPair_id`, `addCoordAlgHomPair_injective_of_baseHom_inj`
- **Visibility**: public
- **Lines**: 1014–1017, definition only

---

### `noncomputable def addCoordAlgHomPair`
- **Type**: `AddNonInversePair α₁ α₂ → R →ₐ[F] KE`
- **What**: The pair addition coordinate ring hom promoted to an F-algebra hom.
- **How**: Same pattern as `addCoordAlgHom`: wraps `addCoordRingHomPair` and proves `commutes` via `AdjoinRoot.lift_mk`, `eval₂_C`, and simp.
- **Hypotheses**: `AddNonInversePair α₁ α₂`
- **Uses from project**: `addCoordRingHomPair`, `addBaseHomPair`
- **Used by**: `addPullbackAlgHomPair`, `addIsog`, `addCoordAlgHomPair_id`, `addCoordAlgHomPair_injective_of_baseHom_inj`; downstream files
- **Visibility**: public
- **Lines**: 1020–1031, proof length ~11 lines

---

### `noncomputable def addPullbackAlgHomPair`
- **Type**: `AddNonInversePair α₁ α₂ → Function.Injective (addCoordAlgHomPair hxy) → KE →ₐ[F] KE`
- **What**: The function-field algebra map `K(E) →ₐ[F] K(E)` for the pair addition pullback.
- **How**: `IsFractionRing.liftAlgHom hinj`.
- **Hypotheses**: `AddNonInversePair α₁ α₂`, injectivity of `addCoordAlgHomPair`
- **Uses from project**: `addCoordAlgHomPair`
- **Used by**: `addIsog`, `addIsog_pullback`, `addPullbackAlgHomPair_id`; downstream files
- **Visibility**: public
- **Lines**: 1036–1039, definition only

---

### `noncomputable def addIsog`
- **Type**: `AddNonInversePair α₁ α₂ → Function.Injective (addCoordAlgHomPair hxy) → Isogeny W.toAffine W.toAffine`
- **What**: Packages the pair-addition pullback into an `Isogeny` structure, with `pullback = addPullbackAlgHomPair` and `toAddMonoidHom = α₁.toAddMonoidHom + α₂.toAddMonoidHom`.
- **How**: Record construction.
- **Hypotheses**: `AddNonInversePair α₁ α₂`, injectivity of `addCoordAlgHomPair`
- **Uses from project**: `addPullbackAlgHomPair`
- **Used by**: `addIsog_pullback`, `addIsog_toAddMonoidHom`; heavily used in downstream files (`RouteBInduction.lean`, `DegreeQuadraticForm.lean`, `OpenLemmaPrimitives.lean`, etc.)
- **Visibility**: public
- **Lines**: 1044–1049, definition only

---

### `@[simp] theorem addIsog_pullback`
- **Type**: `(addIsog hxy hinj).pullback = addPullbackAlgHomPair hxy hinj`
- **What**: Simplification: the pullback field of `addIsog` is `addPullbackAlgHomPair`.
- **How**: `rfl`.
- **Hypotheses**: `AddNonInversePair α₁ α₂`, injectivity
- **Uses from project**: `addIsog`, `addPullbackAlgHomPair`
- **Used by**: downstream files
- **Visibility**: public
- **Lines**: 1051–1054, proof length 1 line

---

### `@[simp] theorem addIsog_toAddMonoidHom`
- **Type**: `(addIsog hxy hinj).toAddMonoidHom = α₁.toAddMonoidHom + α₂.toAddMonoidHom`
- **What**: Simplification: the point map of `addIsog` is the sum of the point maps.
- **How**: `rfl`.
- **Hypotheses**: `AddNonInversePair α₁ α₂`, injectivity
- **Uses from project**: `addIsog`
- **Used by**: downstream files
- **Visibility**: public
- **Lines**: 1056–1060, proof length 1 line

---

### `theorem AddNonInversePair_id`
- **Type**: `AddNonInversePair (Isogeny.id W.toAffine) α ↔ AddNonInverse W α`
- **What**: The pair non-inverse condition specialised to `(id, α)` is definitionally the single-isogeny non-inverse condition.
- **How**: `Iff.rfl`.
- **Uses from project**: `AddNonInversePair`, `AddNonInverse`
- **Used by**: unused in file (bridge lemma for downstream)
- **Visibility**: public
- **Lines**: 1070–1072, proof length 1 line

---

### `@[simp] theorem addSlopePair_id`
- **Type**: `addSlopePair (Isogeny.id W.toAffine) α = addSlope W α`
- **What**: The pair slope with `α₁ = id` is definitionally the single-isogeny slope.
- **How**: `rfl`.
- **Uses from project**: `addSlopePair`, `addSlope`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1075–1076, proof length 1 line

---

### `@[simp] theorem addPullback_x_pair_id`
- **Type**: `addPullback_x_pair (Isogeny.id W.toAffine) α = addPullback_x W α`
- **What**: The pair x-coordinate with `α₁ = id` is definitionally the single-isogeny x-coordinate.
- **How**: `rfl`.
- **Uses from project**: `addPullback_x_pair`, `addPullback_x`
- **Used by**: unused in file; used in `RouteBInduction.lean`
- **Visibility**: public
- **Lines**: 1079–1080, proof length 1 line

---

### `@[simp] theorem addPullback_y_pair_id`
- **Type**: `addPullback_y_pair (Isogeny.id W.toAffine) α = addPullback_y W α`
- **What**: The pair y-coordinate with `α₁ = id` is definitionally the single-isogeny y-coordinate.
- **How**: `rfl`.
- **Uses from project**: `addPullback_y_pair`, `addPullback_y`
- **Used by**: unused in file; used in `RouteBInduction.lean`
- **Visibility**: public
- **Lines**: 1083–1084, proof length 1 line

---

### `@[simp] theorem addBaseHomPair_id`
- **Type**: `addBaseHomPair (Isogeny.id W.toAffine) α = addBaseHom W α`
- **What**: The pair base ring hom with `α₁ = id` is definitionally the single-isogeny base hom.
- **How**: `rfl`.
- **Uses from project**: `addBaseHomPair`, `addBaseHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1087–1088, proof length 1 line

---

### `@[simp] theorem addCoordRingHomPair_id`
- **Type**: `addCoordRingHomPair (α₁ := Isogeny.id W.toAffine) hxy = addCoordRingHom hxy`
- **What**: The pair coordinate ring hom with `α₁ = id` is definitionally the single-isogeny coord ring hom.
- **How**: `rfl`.
- **Uses from project**: `addCoordRingHomPair`, `addCoordRingHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1091–1094, proof length 1 line

---

### `@[simp] theorem addCoordAlgHomPair_id`
- **Type**: `addCoordAlgHomPair (α₁ := Isogeny.id W.toAffine) hxy = addCoordAlgHom hxy`
- **What**: The pair F-algebra coord hom with `α₁ = id` is definitionally the single-isogeny coord alg hom.
- **How**: `rfl`.
- **Uses from project**: `addCoordAlgHomPair`, `addCoordAlgHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1097–1100, proof length 1 line

---

### `@[simp] theorem addPullbackAlgHomPair_id`
- **Type**: `addPullbackAlgHomPair (α₁ := Isogeny.id W.toAffine) hxy hinj = addPullbackAlgHom hxy hinj`
- **What**: The pair function-field alg hom with `α₁ = id` is definitionally the single-isogeny version.
- **How**: `rfl`.
- **Uses from project**: `addPullbackAlgHomPair`, `addPullbackAlgHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1105–1109, proof length 1 line

---

### `theorem AddNonInversePair_of_x_ne`
- **Type**: `α₁.pullback (x_gen W) ≠ α₂.pullback (x_gen W) → AddNonInversePair α₁ α₂`
- **What**: Build `AddNonInversePair` from an x-coordinate mismatch alone (the y-conjunct is vacuous).
- **How**: `fun ⟨h, _⟩ => h_x h`.
- **Hypotheses**: x-coordinate mismatch
- **Uses from project**: `x_gen`, `AddNonInversePair`
- **Used by**: unused in file; used in `Frobenius.lean`, `OpenLemmaPrimitives.lean`
- **Visibility**: public
- **Lines**: 1122–1125, proof length 1 line

---

### `theorem AddNonInversePair_of_y_ne`
- **Type**: `α₁.pullback (y_gen W) ≠ (W_KE W).toAffine.negY (α₂.pullback x_gen) (α₂.pullback y_gen) → AddNonInversePair α₁ α₂`
- **What**: Build `AddNonInversePair` from a y-coordinate mismatch (negY form).
- **How**: `fun ⟨_, h⟩ => h_y h`.
- **Hypotheses**: y-coordinate mismatch in negY form
- **Uses from project**: `y_gen`, `x_gen`, `W_KE`, `AddNonInversePair`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1130–1134, proof length 1 line

---

### `theorem addBaseHomPair_eq_aeval`
- **Type**: `(addBaseHomPair α₁ α₂ : Polynomial F →+* KE) = (Polynomial.aeval (addPullback_x_pair α₁ α₂) : Polynomial F →ₐ[F] KE).toRingHom`
- **What**: The pair base ring hom equals aeval at `addPullback_x_pair`. Pair analogue of `addBaseHom_eq_aeval`.
- **How**: `ext; simp [addBaseHomPair, Polynomial.aeval_def]`.
- **Hypotheses**: none
- **Uses from project**: `addBaseHomPair`, `addPullback_x_pair`
- **Used by**: unused in file; used in `Frobenius.lean`, `OpenLemmaPrimitives.lean`
- **Visibility**: public (`set_option linter.unusedSectionVars false in`)
- **Lines**: 1142–1149, proof length 2 lines

---

### `theorem addCoordAlgHomPair_injective_of_baseHom_inj`
- **Type**: `AddNonInversePair α₁ α₂ → Function.Injective (addBaseHomPair α₁ α₂) → Function.Injective (addCoordAlgHomPair hxy)`
- **What**: Witness-parametric pair injectivity: injectivity of `addCoordAlgHomPair` from injectivity of the base hom. Exact pair analogue of `addCoordAlgHom_injective_of_baseHom_inj`.
- **How**: Same norm-argument proof structure: decomposes in the `{1, Y}` basis, uses `Affine.CoordinateRing.coe_norm_smul_basis` and `degree_norm_smul_basis` to derive a degree contradiction in the `q ≠ 0` case.
- **Hypotheses**: `AddNonInversePair α₁ α₂`, `Function.Injective (addBaseHomPair α₁ α₂)`
- **Uses from project**: `addCoordRingHomPair`, `addBaseHomPair`, `addPullback_y_pair`; mathlib: `Affine.CoordinateRing.exists_smul_basis_eq`, `coe_norm_smul_basis`, `degree_norm_smul_basis`
- **Used by**: unused in file; used in `Frobenius.lean`, `OpenLemmaPrimitives.lean`
- **Visibility**: public
- **Lines**: 1156–1231, proof length 75 lines
- **Notes**: Long proof (75 lines). Near-duplicate of `addCoordAlgHom_injective_of_baseHom_inj` (lines 857–942); the only difference is the pair vs. single isogeny naming.

---

### `theorem addSlopePair_eq_of_x_ne`
- **Type**: `α₁.pullback (x_gen W) ≠ α₂.pullback (x_gen W) → addSlopePair α₁ α₂ = (α₁.pullback y_gen - α₂.pullback y_gen) / (α₁.pullback x_gen - α₂.pullback x_gen)`
- **What**: In the non-doubling case (x-coordinates differ), the pair slope equals the chord slope.
- **How**: `unfold addSlopePair; exact Affine.slope_of_X_ne h_x_ne`.
- **Hypotheses**: x-coordinate mismatch
- **Uses from project**: `addSlopePair`, `x_gen`, `y_gen`
- **Used by**: `addSlopePair_sigma_sum_eq_neg_a1`, `addPullback_x_pair_sigma_invariant`; used in `SamePlace.lean`, `SilvermanIV14.lean`, `OpenLemmaPrimitives.lean`
- **Visibility**: public
- **Lines**: 1248–1254, proof length 3 lines

---

### `theorem addSlopePair_sigma_sum_eq_neg_a1`
- **Type**: (conditional on x-ne and σ-action on both pullbacks) `(mulByInt W.toAffine (-1)).pullback (addSlopePair α₁ α₂) + addSlopePair α₁ α₂ = -algebraMap F KE W.toAffine.a₁`
- **What**: When both pullbacks commute with the negation isogeny `[-1]` on x (fixed) and y (negated), the sum `σ(L) + L = -a₁` for the pair slope `L`.
- **How**: Uses `addSlopePair_eq_of_x_ne` to unfold the slope, then `map_div₀`, `map_sub`, the hypotheses on σ-action, `field_simp`, and `ring`.
- **Hypotheses**: x-coordinate mismatch, σ-action on both pullbacks' x and y
- **Uses from project**: `addSlopePair`, `addSlopePair_eq_of_x_ne`, `x_gen`, `y_gen`, `W_KE`
- **Used by**: `addPullback_x_pair_sigma_invariant`
- **Visibility**: public
- **Lines**: 1260–1283, proof length 23 lines

---

### `theorem addPullback_x_pair_sigma_invariant`
- **Type**: (conditional on x-ne and σ-action on both pullbacks) `(mulByInt W.toAffine (-1)).pullback (addPullback_x_pair α₁ α₂) = addPullback_x_pair α₁ α₂`
- **What**: If both pullbacks satisfy the σ-action symmetry on x (fixed) and y (sign-flipped), then σ fixes `addPullback_x_pair α₁ α₂`. This is the key σ-invariance of the x-coordinate of the pair addition.
- **How**: Unfolds `addPullback_x_pair` and `Affine.addX`; uses `AlgHom.commutes` to fix constants; then `linear_combination` with `addSlopePair_sigma_sum_eq_neg_a1` to reduce to the slope identity.
- **Hypotheses**: x-coordinate mismatch, σ-action on both pullbacks' x and y
- **Uses from project**: `addPullback_x_pair`, `addSlopePair`, `addSlopePair_sigma_sum_eq_neg_a1`, `x_gen`, `y_gen`, `W_KE`
- **Used by**: unused in file; used in `Frobenius.lean`, `OpenLemmaPrimitives.lean`, `Verschiebung/Genuine.lean`, `Verschiebung/IsDual.lean`
- **Visibility**: public
- **Lines**: 1289–1317, proof length 28 lines

---

## Key Project Declarations Used

From `HasseWeil.Basic` / project core:
- `W_KE`, `x_gen`, `y_gen`, `generic_equation`, `W_smooth`

From `HasseWeil.OrdAtInftyBridge`:
- `ordAtInfty_algebraMap_F_nonzero`

From `HasseWeil.MulByIntPullback` (transitively):
- `Affine.CoordinateRing.exists_smul_basis_eq`, `Affine.CoordinateRing.coe_norm_smul_basis`, `Affine.CoordinateRing.degree_norm_smul_basis`

From `Curves.SmoothPlaneCurve` (project):
- `exists_decomp`, `decomp_from_quadratic`, `bFracPoly`, `cFracPoly`, `coordYInFunctionField`, `polynomialDiscriminant_eq_trace_sq_sub_four_norm`, `polynomialDiscriminant_ne_zero`, `polynomialDiscriminant_natDegree`

From `WeierstrassCurve.degree_functionField_over_kx`:
- Used in `addPullback_x_transcendental`
