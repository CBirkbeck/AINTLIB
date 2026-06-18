# Inventory: ./HasseWeil/FormalGroup/EvalGroup.lean

**File**: `HasseWeil/FormalGroup/EvalGroup.lean`
**Purpose**: Constructs the abelian group `F(M)` on the maximal ideal `M` of a complete local ring `R` using a formal group law `F` (Silverman IV.3, ticket T-IV-3-001).
**Total lines**: 1173
**Imports**: `HasseWeil.FormalGroup.Definition`, `HasseWeil.FormalGroup.Inverse`, plus several Mathlib topology/power-series modules.

---

## Declarations

### `lemma isTopologicallyNilpotent_of_mem_maximalIdeal`
- **Type**: `(hAdic : IsAdic (IsLocalRing.maximalIdeal R)) {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) : IsTopologicallyNilpotent x`
- **What**: Any element of the maximal ideal is topologically nilpotent in the M-adic topology, i.e., `x^n → 0`.
- **How**: Rewrites via `IsAdic.hasBasis_nhds_zero.tendsto_right_iff`; for `m ≥ n`, uses `Ideal.pow_le_pow_right` and `Ideal.pow_mem_pow` to place `x^m` in `M^n`.
- **Hypotheses**: `R` is a commutative local ring; `IsAdic (maximalIdeal R)` holds; `x ∈ maximalIdeal R`.
- **Uses from project**: None.
- **Used by**: `hasEval_of_mem_maximalIdeal`, `powerSeries_hasEval_of_mem`, `mvPowerSeries_eval_mem_maximalIdeal`, `hasEval_of_mem_maximalIdeal_general`, `eval₂_subst_bridge`
- **Visibility**: public
- **Lines**: 88–98; proof ~8 lines

---

### `lemma hasEval_of_mem_maximalIdeal`
- **Type**: `(hAdic : IsAdic (IsLocalRing.maximalIdeal R)) {a : Fin 2 → R} (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal R) : MvPowerSeries.HasEval a`
- **What**: A `Fin 2`-indexed family of elements of the maximal ideal satisfies the `HasEval` predicate needed for `MvPowerSeries.eval₂` convergence.
- **How**: Provides `hpow` via `isTopologicallyNilpotent_of_mem_maximalIdeal`; provides `tendsto_zero` by observing `Fin 2` is finite so the cofinite filter is `⊥`.
- **Hypotheses**: `IsAdic (maximalIdeal R)`; each `a i ∈ maximalIdeal R`.
- **Uses from project**: `isTopologicallyNilpotent_of_mem_maximalIdeal`
- **Used by**: `evalAdd_mem`, `evalAdd_zero_zero`, `evalAdd_comm`, `evalAdd_zero_right`
- **Visibility**: public
- **Lines**: 102–110; proof ~8 lines

---

### `noncomputable def FormalGroup.evalAdd`
- **Type**: `(F : FormalGroup R) (x y : IsLocalRing.maximalIdeal R) : R`
- **What**: The binary operation `x +_F y := F(x,y)` on the maximal ideal, defined as `MvPowerSeries.eval₂ (RingHom.id R) ![x.1, y.1] F.toSeries`.
- **How**: Direct definition via multivariate power series evaluation.
- **Hypotheses**: `R` is a commutative local ring; the standard topology/uniform-space hypotheses are in the section variable block (but not used in the def itself).
- **Uses from project**: `FormalGroup.toSeries` (field access)
- **Used by**: `evalAdd_mem`, `evalAdd_zero_zero`, `evalAdd_comm`, `coeff_j0_of_ne_one` (comment), `evalAdd_zero_right`, `evalAdd_zero_left`, `evalAdd_evalNeg`, `evalAdd_assoc`, `EvalGroup` instances
- **Visibility**: public
- **Lines**: 117–119; body is 1 line

---

### `lemma maximalIdeal_isClosed`
- **Type**: `(hAdic : IsAdic (IsLocalRing.maximalIdeal R)) : IsClosed (IsLocalRing.maximalIdeal R : Set R)`
- **What**: The maximal ideal is a closed subset of `R` in the M-adic topology.
- **How**: Extracts `IsOpen M` from `isAdic_iff.mp hAdic` at level 1 (`pow_one`), then applies `AddSubgroup.isClosed_of_isOpen`.
- **Hypotheses**: `IsAdic (maximalIdeal R)`.
- **Uses from project**: None (uses Mathlib `isAdic_iff`).
- **Used by**: `evalAdd_mem`, `evalAdd_zero_zero` (indirectly via `hasEval`), `evalNeg_mem`, `powerSeries_eval_mem`, `mvPowerSeries_eval_mem_maximalIdeal`
- **Visibility**: public
- **Lines**: 127–136; proof ~10 lines

---

### `theorem FormalGroup.evalAdd_mem`
- **Type**: `(hAdic : IsAdic ...) (F : FormalGroup R) (x y : IsLocalRing.maximalIdeal R) : F.evalAdd x y ∈ IsLocalRing.maximalIdeal R`
- **What**: The formal group addition `F(x,y)` lands in the maximal ideal.
- **How**: Uses `MvPowerSeries.hasSum_eval₂` to express `eval₂` as a convergent series; invokes `IsClosed.mem_of_tendsto` via `maximalIdeal_isClosed`; for each partial sum term, either `d=0` (coeff is 0 by `HasseWeil.FG.constantCoeff_FG_toSeries`) or `d≠0` so some factor `x` or `y` is in `M`, using `Ideal.pow_mem_of_mem` and `Ideal.prod_mem`.
- **Hypotheses**: `IsAdic`, `F : FormalGroup R`, `x y ∈ M`.
- **Uses from project**: `hasEval_of_mem_maximalIdeal`, `maximalIdeal_isClosed`, `HasseWeil.FG.constantCoeff_FG_toSeries`
- **Used by**: `evalAdd_evalNeg`, `evalAdd_assoc`, `EvalGroup.instAddCommGroup`, `val_add`
- **Visibility**: public
- **Lines**: 141–183; **proof 43 lines** (long)

---

### `theorem FormalGroup.evalAdd_zero_zero`
- **Type**: `(hAdic : IsAdic ...) (F : FormalGroup R) : F.evalAdd ⟨0, _⟩ ⟨0, _⟩ = 0`
- **What**: Evaluating `F` at `(0,0)` gives zero, since the constant coefficient vanishes.
- **How**: Expresses `eval₂` at `(0,0)` as a `HasSum`; shows each term is 0 (d=0 case: `constantCoeff_FG_toSeries`; d≠0 case: some factor `0^n = 0`); concludes via `HasSum.unique` with `hasSum_zero`.
- **Hypotheses**: `IsAdic`, `F : FormalGroup R`.
- **Uses from project**: `hasEval_of_mem_maximalIdeal`, `HasseWeil.FG.constantCoeff_FG_toSeries`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 192–236; **proof 45 lines** (long)
- **Notes**: Dead code within this file (no callers here).

---

### `private noncomputable def finsupp_swap`
- **Type**: `(Fin 2 →₀ ℕ) ≃ (Fin 2 →₀ ℕ)`
- **What**: The coordinate-swap equivalence on `Fin 2 →₀ ℕ`: sends `d ↦ (d 1, d 0)` (swapping components 0 and 1).
- **How**: Both `toFun` and `invFun` are `d ↦ Finsupp.single 0 (d 1) + Finsupp.single 1 (d 0)`; inverse is its own inverse.
- **Hypotheses**: None.
- **Uses from project**: None.
- **Used by**: `finsupp_swap_apply_zero`, `finsupp_swap_apply_one`, `coeff_swap`, `evalAdd_comm`
- **Visibility**: private
- **Lines**: 244–252; body ~9 lines

---

### `private lemma finsupp_swap_apply_zero`
- **Type**: `(d : Fin 2 →₀ ℕ) : (finsupp_swap d) 0 = d 1`
- **What**: The swap equivalence maps index 0 to the value at index 1.
- **How**: `simp [finsupp_swap, Finsupp.single_apply]`.
- **Hypotheses**: None.
- **Uses from project**: `finsupp_swap`
- **Used by**: `coeff_swap`, `evalAdd_comm`
- **Visibility**: private
- **Lines**: 254–256; proof 1 line

---

### `private lemma finsupp_swap_apply_one`
- **Type**: `(d : Fin 2 →₀ ℕ) : (finsupp_swap d) 1 = d 0`
- **What**: The swap equivalence maps index 1 to the value at index 0.
- **How**: `simp [finsupp_swap, Finsupp.single_apply]`.
- **Hypotheses**: None.
- **Uses from project**: `finsupp_swap`
- **Used by**: `coeff_swap`, `evalAdd_comm`
- **Visibility**: private
- **Lines**: 258–260; proof 1 line

---

### `theorem FormalGroup.coeff_swap`
- **Type**: `(F : FormalGroup R) (d : Fin 2 →₀ ℕ) : MvPowerSeries.coeff d F.toSeries = MvPowerSeries.coeff (finsupp_swap d) F.toSeries`
- **What**: The coefficient symmetry of a formal group law: `coeff d F = coeff (d 1, d 0) F`, a consequence of commutativity `F.comm`.
- **How**: Applies `MvPowerSeries.coeff_subst` to `F.comm` (which says `subst ![X 1, X 0] F = F`); uses `finsum_eq_single` to isolate the unique nonzero term at `finsupp_swap d`; verifies the coefficient of the monomial product via `X_pow_eq`, `monomial_mul_monomial`, `coeff_monomial`; uses `finsupp_swap_apply_zero/one`.
- **Hypotheses**: `F : FormalGroup R`.
- **Uses from project**: `finsupp_swap`, `finsupp_swap_apply_zero`, `finsupp_swap_apply_one`; `F.comm` (FormalGroup field from Definition.lean)
- **Used by**: `evalAdd_comm`
- **Visibility**: public
- **Lines**: 265–322; **proof 58 lines** (long)

---

### `theorem FormalGroup.evalAdd_comm`
- **Type**: `(hAdic : IsAdic ...) (F : FormalGroup R) (x y : IsLocalRing.maximalIdeal R) : F.evalAdd x y = F.evalAdd y x`
- **What**: The formal group addition is commutative: `F(x,y) = F(y,x)`.
- **How**: Gets `HasSum` for both `eval₂ F (x,y)` and `eval₂ F (y,x)`; reindexes via `finsupp_swap.hasSum_iff` to get both as sums over the same index set; shows term equality using `FormalGroup.coeff_swap`; concludes by `HasSum.unique`.
- **Hypotheses**: `IsAdic`, `F : FormalGroup R`, `x y ∈ M`.
- **Uses from project**: `hasEval_of_mem_maximalIdeal`, `finsupp_swap`, `finsupp_swap_apply_zero`, `finsupp_swap_apply_one`, `FormalGroup.coeff_swap`
- **Used by**: `evalAdd_zero_left`, `evalAdd_evalNeg` (via `rw`), `instAddCommGroup`
- **Visibility**: public
- **Lines**: 327–377 (with `set_option maxHeartbeats 800000`); **proof 49 lines** (long)
- **Notes**: `set_option maxHeartbeats 800000` at L327, NO-COMMENT on reason.

---

### `theorem FormalGroup.coeff_j0_of_ne_one`
- **Type**: `(F : FormalGroup R) (j : ℕ) (hj : j ≠ 1) : MvPowerSeries.coeff (Finsupp.single 0 j) F.toSeries = 0`
- **What**: For `j ≠ 1`, the coefficient at `(j, 0)` of `F.toSeries` is zero; this expresses the coefficient-level content of `F.lunit : F(X,0) = X`.
- **How**: Applies `coeff_subst` to `F.lunit`; isolates the unique term via `finsum_eq_single`; the RHS coefficient of `X 0` at `single 0 j` is 0 when `j ≠ 1`; non-main terms also vanish by `zero_pow` or `coeff_monomial`.
- **Hypotheses**: `F : FormalGroup R`; `j ≠ 1`.
- **Uses from project**: `F.lunit` (FormalGroup field from Definition.lean)
- **Used by**: `evalAdd_zero_right`
- **Visibility**: public
- **Lines**: 390–451; **proof 62 lines** (long)

---

### `theorem FormalGroup.evalAdd_zero_right`
- **Type**: `(hAdic : IsAdic ...) (F : FormalGroup R) (x : IsLocalRing.maximalIdeal R) : F.evalAdd x ⟨0, _⟩ = x.1`
- **What**: Right unit: `F(x, 0) = x`.
- **How**: Rewrites `eval₂` at `(x, 0)` as a `HasSum`; shows each term equals `x.1` if `d = single 0 1` and `0` otherwise, using `coeff_j0_of_ne_one` (for `d 0 ≠ 1, d 1 = 0`) and `HasseWeil.FG.FormalGroup.coeff_10` (for `d = single 0 1`); uses `hasSum_ite_eq` and `HasSum.unique`.
- **Hypotheses**: `IsAdic`, `F : FormalGroup R`, `x ∈ M`.
- **Uses from project**: `hasEval_of_mem_maximalIdeal`, `FormalGroup.coeff_j0_of_ne_one`, `HasseWeil.FG.FormalGroup.coeff_10`
- **Used by**: `evalAdd_zero_left`
- **Visibility**: public
- **Lines**: 454–517; **proof 64 lines** (long)

---

### `theorem FormalGroup.coeff_0j_of_ne_one`
- **Type**: `(F : FormalGroup R) (j : ℕ) (hj : j ≠ 1) : MvPowerSeries.coeff (Finsupp.single 1 j) F.toSeries = 0`
- **What**: For `j ≠ 1`, the coefficient at `(0, j)` of `F.toSeries` is zero; the coefficient-level form of `F.runit : F(0,X) = X`.
- **How**: Analogous to `coeff_j0_of_ne_one` but applied to `F.runit` and the second variable.
- **Hypotheses**: `F : FormalGroup R`; `j ≠ 1`.
- **Uses from project**: `F.runit` (FormalGroup field from Definition.lean)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 521–573; **proof 53 lines** (long)
- **Notes**: Dead code within this file. Likely intended as a counterpart to `coeff_j0_of_ne_one` for external use.

---

### `theorem FormalGroup.evalAdd_zero_left`
- **Type**: `(hAdic : IsAdic ...) (F : FormalGroup R) (y : IsLocalRing.maximalIdeal R) : F.evalAdd ⟨0, _⟩ y = y.1`
- **What**: Left unit: `F(0, y) = y`.
- **How**: Reduces to `evalAdd_zero_right` via `evalAdd_comm`.
- **Hypotheses**: `IsAdic`, `F : FormalGroup R`, `y ∈ M`.
- **Uses from project**: `FormalGroup.evalAdd_comm`, `FormalGroup.evalAdd_zero_right`
- **Used by**: `instAddCommGroup`
- **Visibility**: public
- **Lines**: 576–581; proof 2 lines

---

### `private lemma powerSeries_hasEval_of_mem`
- **Type**: `(hAdic : IsAdic ...) {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) : PowerSeries.HasEval x`
- **What**: An element of the maximal ideal has `PowerSeries.HasEval`, enabling univariate power series evaluation.
- **How**: Direct application of `isTopologicallyNilpotent_of_mem_maximalIdeal`.
- **Hypotheses**: `IsAdic`, `x ∈ M`.
- **Uses from project**: `isTopologicallyNilpotent_of_mem_maximalIdeal`
- **Used by**: `evalNeg_mem`, `powerSeries_eval_mem`
- **Visibility**: private
- **Lines**: 593–597; proof 1 line

---

### `noncomputable def FormalGroup.evalNeg`
- **Type**: `(F : FormalGroup R) (x : IsLocalRing.maximalIdeal R) : R`
- **What**: The formal negation `-_F x := i(x)`, defined as `PowerSeries.eval₂ (RingHom.id R) x.1 F.inverse`.
- **How**: Direct definition via univariate power series evaluation of `F.inverse`.
- **Hypotheses**: Standard topology/completeness variables in scope.
- **Uses from project**: `FormalGroup.inverse` (field from Inverse.lean)
- **Used by**: `evalNeg_mem`, `evalAdd_evalNeg`, `EvalGroup.instNeg`, `val_neg`
- **Visibility**: public
- **Lines**: 604–606; body is 1 line

---

### `theorem FormalGroup.evalNeg_mem`
- **Type**: `(hAdic : IsAdic ...) (F : FormalGroup R) (x : IsLocalRing.maximalIdeal R) : F.evalNeg x ∈ IsLocalRing.maximalIdeal R`
- **What**: The formal negation lies in the maximal ideal.
- **How**: Uses `PowerSeries.hasSum_eval₂`; applies `IsClosed.mem_of_tendsto` via `maximalIdeal_isClosed`; for n=0 uses `F.inverse_coeff_zero`; for n>0 uses `Ideal.pow_mem_of_mem`.
- **Hypotheses**: `IsAdic`, `F : FormalGroup R`, `x ∈ M`.
- **Uses from project**: `powerSeries_hasEval_of_mem`, `maximalIdeal_isClosed`, `FormalGroup.inverse_coeff_zero` (from Inverse.lean)
- **Used by**: `evalAdd_evalNeg`, `EvalGroup.instNeg`, `val_neg`, `instAddCommGroup`
- **Visibility**: public
- **Lines**: 613–635; proof 23 lines

---

### `private theorem powerSeries_eval_mem`
- **Type**: `(hAdic : IsAdic ...) (x : IsLocalRing.maximalIdeal R) (u : PowerSeries R) (hu : PowerSeries.constantCoeff u = 0) : PowerSeries.eval₂ (RingHom.id R) x.1 u ∈ IsLocalRing.maximalIdeal R`
- **What**: Univariate evaluation of any power series with zero constant coefficient at `x ∈ M` lies in `M`.
- **How**: Same pattern as `evalNeg_mem`: `hasSum_eval₂` + `IsClosed.mem_of_tendsto` + term-by-term M-membership.
- **Hypotheses**: `IsAdic`; `x ∈ M`; `constantCoeff u = 0`.
- **Uses from project**: `powerSeries_hasEval_of_mem`, `maximalIdeal_isClosed`
- **Used by**: unused in file
- **Visibility**: private
- **Lines**: 650–672; proof 23 lines
- **Notes**: Dead code within this file — generalizes `evalNeg_mem`'s pattern but is never called.

---

### `private theorem coeff_prod_pow_support_finite`
- **Type**: `[Finite σ] {a : σ → MvPowerSeries τ R} (ha0 : ∀ s, constantCoeff (a s) = 0) (e : τ →₀ ℕ) : Set.Finite {d : σ →₀ ℕ | coeff e (d.prod fun s e' => (a s)^e') ≠ 0}`
- **What**: For a family `a` of power series with zero constant coefficient, only finitely many multi-indices `d` can contribute a nonzero coefficient at a fixed `e` in a product `∏(a s)^(d s)`.
- **How**: The set is contained in `{d | Finsupp.degree d ≤ Finsupp.degree e}` (finite by `Finsupp.finite_of_degree_le`); for `d` outside this bound, the product's order exceeds `e.degree` by `MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero` and `MvPowerSeries.le_order_prod`, so `coeff_of_lt_order` gives zero.
- **Hypotheses**: `σ` finite; each `constantCoeff (a s) = 0`.
- **Uses from project**: None.
- **Used by**: `continuous_subst_of_constantCoeff_zero`
- **Visibility**: private
- **Lines**: 701–730; proof ~30 lines

---

### `private theorem continuous_subst_of_constantCoeff_zero`
- **Type**: `[Finite σ] {a : σ → MvPowerSeries τ R} (ha0 : ∀ s, constantCoeff (a s) = 0) (ha : MvPowerSeries.HasSubst a) : Continuous (MvPowerSeries.subst a : MvPowerSeries σ R → MvPowerSeries τ R)`
- **What**: Substitution `f ↦ subst a f` is continuous in the Pi topology (on `MvPowerSeries`) when each `a s` has zero constant coefficient.
- **How**: Uses `continuous_pi_iff`; for each output coefficient `e`, uses `coeff_prod_pow_support_finite` to find a finite support `T` for the nonzero contributing `d`'s; rewrites the map as a finite sum of continuous projections via `coeff_subst`; applies `continuous_finset_sum` with `continuous_coeff` from the Pi topology.
- **Hypotheses**: `σ` finite; `∀ s, constantCoeff (a s) = 0`; `HasSubst a`.
- **Uses from project**: `coeff_prod_pow_support_finite`
- **Used by**: `eval₂_subst_bridge`
- **Visibility**: private
- **Lines**: 734–767; **proof 34 lines** (long)

---

### `private theorem mvPowerSeries_eval_mem_maximalIdeal`
- **Type**: `[Finite σ] (hAdic : IsAdic ...) {b : σ → R} (hb_mem : ∀ s, b s ∈ M) (u : MvPowerSeries σ R) (hu : constantCoeff u = 0) : eval₂ id b u ∈ M`
- **What**: Multivariate evaluation of a power series with zero constant coefficient at `b : σ → M` lies in `M`, for any finite index type `σ`.
- **How**: Constructs `MvPowerSeries.HasEval b` using `isTopologicallyNilpotent_of_mem_maximalIdeal` and cofinite-filter argument; applies `hasSum_eval₂` + `IsClosed.mem_of_tendsto`; term-by-term argument using `Ideal.pow_mem_of_mem` and `Ideal.prod_mem`.
- **Hypotheses**: `σ` finite; `IsAdic`; `∀ s, b s ∈ M`; `constantCoeff u = 0`.
- **Uses from project**: `isTopologicallyNilpotent_of_mem_maximalIdeal`, `maximalIdeal_isClosed`
- **Used by**: `eval₂_subst_bridge`
- **Visibility**: private
- **Lines**: 773–807; **proof 35 lines** (long)

---

### `private lemma hasEval_of_mem_maximalIdeal_general`
- **Type**: `[Finite σ] (hAdic : IsAdic ...) {b : σ → R} (hb_mem : ∀ s, b s ∈ M) : MvPowerSeries.HasEval b`
- **What**: General version of `hasEval_of_mem_maximalIdeal` for any finite index type `σ` (not just `Fin 2`).
- **How**: `nonempty_fintype` instance + `isTopologicallyNilpotent_of_mem_maximalIdeal` per component + cofinite filter is `⊥`.
- **Hypotheses**: `σ` finite; `IsAdic`; `∀ s, b s ∈ M`.
- **Uses from project**: `isTopologicallyNilpotent_of_mem_maximalIdeal`
- **Used by**: `eval₂_subst_bridge`
- **Visibility**: private
- **Lines**: 810–818; proof ~9 lines

---

### `theorem eval₂_subst_bridge`
- **Type**: `[Finite σ] [Finite τ] (hAdic : IsAdic ...) {a : σ → MvPowerSeries τ R} (ha0 : ∀ s, constantCoeff (a s) = 0) (ha : HasSubst a) {b : τ → R} (hb_mem : ∀ i, b i ∈ M) (F : MvPowerSeries σ R) : eval₂ id b (subst a F) = eval₂ id (fun s => eval₂ id b (a s)) F`
- **What**: The substitution bridge lemma: evaluating `subst a F` at `b` equals evaluating `F` at the composed point `s ↦ eval₂ id b (a s)`. This is a workaround for `MvPowerSeries.eval₂_subst`, which requires discrete uniformity.
- **How**: Uses `MvPowerSeries.eval₂_unique` (characterization by continuity + polynomial agreement). Continuity of `f ↦ eval₂ id b (subst a f)` is composed from `continuous_subst_of_constantCoeff_zero` and `MvPowerSeries.continuous_eval₂`. Polynomial agreement reduces to `MvPowerSeries.subst_coe`, `MvPolynomial.eval₂_comp_left`, and algebraMap identities.
- **Hypotheses**: `σ`, `τ` finite; `IsAdic`; `constantCoeff (a s) = 0` for all `s`; `HasSubst a`; `b i ∈ M` for all `i`.
- **Uses from project**: `hasEval_of_mem_maximalIdeal_general`, `mvPowerSeries_eval_mem_maximalIdeal`, `isTopologicallyNilpotent_of_mem_maximalIdeal`, `continuous_subst_of_constantCoeff_zero`
- **Used by**: `evalAdd_evalNeg`, `evalAdd_assoc`
- **Visibility**: public
- **Lines**: 826–882; **proof 57 lines** (long)

---

### `private theorem powerSeries_eval₂_eq_mvEval₂`
- **Type**: `(u : PowerSeries R) (x : R) : PowerSeries.eval₂ (RingHom.id R) x u = MvPowerSeries.eval₂ (RingHom.id R) (fun _ : Unit => x) u`
- **What**: Identifies univariate `PowerSeries.eval₂` with the corresponding `MvPowerSeries.eval₂` over `Unit`.
- **How**: `rfl` — definitional equality.
- **Hypotheses**: None.
- **Uses from project**: None.
- **Used by**: unused in file
- **Visibility**: private
- **Lines**: 891–894; proof is `rfl`
- **Notes**: Dead code within this file — never called. Appears to have been written as a bridge but superseded by direct `change` tactics.

---

### `theorem FormalGroup.evalAdd_evalNeg`
- **Type**: `(hAdic : IsAdic ...) (F : FormalGroup R) (x : IsLocalRing.maximalIdeal R) : F.evalAdd x ⟨F.evalNeg x, F.evalNeg_mem hAdic x⟩ = 0`
- **What**: The inverse axiom: `F(x, i(x)) = 0` for all `x ∈ M`.
- **How**: Uses `F.fAdd_X_inverse_eq_zero` (from Inverse.lean: `fAdd F X (F.inverse) = 0` as power series); defines `a := ![PowerSeries.X, F.inverse]`; applies `eval₂_subst_bridge` to transport the power-series equation to the evaluation; verifies `a 0 = X` evaluates to `x` via `PowerSeries.eval₂_X` and `a 1 = F.inverse` evaluates to `F.evalNeg x` by definition; uses `F.inverse_constantCoeff` for `HasSubst`.
- **Hypotheses**: `IsAdic`, `F : FormalGroup R`, `x ∈ M`.
- **Uses from project**: `eval₂_subst_bridge`, `FormalGroup.evalNeg_mem`, `HasseWeil.FG.fAdd`, `F.fAdd_X_inverse_eq_zero` (Inverse.lean), `F.inverse_constantCoeff` (Inverse.lean)
- **Used by**: `instAddCommGroup`
- **Visibility**: public
- **Lines**: 900–967; **proof 68 lines** (long)

---

### `theorem FormalGroup.evalAdd_assoc`
- **Type**: `(hAdic : IsAdic ...) (F : FormalGroup R) (x y z : IsLocalRing.maximalIdeal R) : F.evalAdd ⟨F.evalAdd x y, F.evalAdd_mem hAdic x y⟩ z = F.evalAdd x ⟨F.evalAdd y z, F.evalAdd_mem hAdic y z⟩`
- **What**: Associativity: `F(F(x,y), z) = F(x, F(y,z))`.
- **How**: Uses `F.assoc` (the power-series identity `subst ![F_XY, X 2] F = subst ![X 0, F_YZ] F`); applies `eval₂_subst_bridge` four times (for the two outer and two inner substitutions at `xyz := ![x,y,z]`); reduces to showing the evaluation of `subst` at `xyz` matches `evalAdd` via inner bridge lemmas `hbridge_XY` and `hbridge_YZ`.
- **Hypotheses**: `IsAdic`, `F : FormalGroup R`, `x y z ∈ M`.
- **Uses from project**: `eval₂_subst_bridge`, `FormalGroup.evalAdd_mem`, `HasseWeil.FG.constantCoeff_subst_vanishing`, `HasseWeil.FG.constantCoeff_FG_toSeries`, `F.assoc` (FormalGroup field from Definition.lean)
- **Used by**: `instAddCommGroup`
- **Visibility**: public
- **Lines**: 971–1087 (with `set_option maxHeartbeats 800000`); **proof 114 lines** (long)
- **Notes**: `set_option maxHeartbeats 800000` at L971, NO-COMMENT on reason.

---

### `structure FormalGroup.EvalGroup`
- **Type**: `structure FormalGroup.EvalGroup (_ : FormalGroup R) (_ : IsAdic (IsLocalRing.maximalIdeal R)) where val : IsLocalRing.maximalIdeal R`
- **What**: A wrapper type for the maximal ideal `M` carrying the formal-group `AddCommGroup` structure, avoiding a typeclass diamond with the native `AddCommGroup (maximalIdeal R)` from the submodule structure.
- **How**: One-field structure with `@[ext]` attribute.
- **Hypotheses**: None.
- **Uses from project**: None.
- **Used by**: All `EvalGroup` instances and theorems.
- **Visibility**: public
- **Lines**: 1101–1105

---

### `instance : Zero (F.EvalGroup hAdic)`
- **Type**: `Zero (F.EvalGroup hAdic)`
- **What**: The zero element of the formal group `F(M)`, wrapping `⟨0, M.zero_mem⟩`.
- **How**: Direct constructor.
- **Hypotheses**: None beyond section variables.
- **Uses from project**: `FormalGroup.EvalGroup`
- **Used by**: `val_zero`, `instAddCommGroup`
- **Visibility**: public
- **Lines**: 1112–1113; body 1 line

---

### `noncomputable instance : Add (F.EvalGroup hAdic)`
- **Type**: `Add (F.EvalGroup hAdic)`
- **What**: The formal group addition on `F.EvalGroup hAdic`, wrapping `evalAdd`.
- **How**: Direct constructor using `F.evalAdd` and `F.evalAdd_mem`.
- **Hypotheses**: Full section variables (topology + completeness).
- **Uses from project**: `FormalGroup.evalAdd`, `FormalGroup.evalAdd_mem`
- **Used by**: `val_add`, `instAddCommGroup`
- **Visibility**: public
- **Lines**: 1116–1117; body 1 line

---

### `noncomputable instance : Neg (F.EvalGroup hAdic)`
- **Type**: `Neg (F.EvalGroup hAdic)`
- **What**: The formal group negation on `F.EvalGroup hAdic`, wrapping `evalNeg`.
- **How**: Direct constructor using `F.evalNeg` and `F.evalNeg_mem`.
- **Hypotheses**: Full section variables.
- **Uses from project**: `FormalGroup.evalNeg`, `FormalGroup.evalNeg_mem`
- **Used by**: `val_neg`, `instAddCommGroup`
- **Visibility**: public
- **Lines**: 1120–1121; body 1 line

---

### `theorem val_zero`
- **Type**: `(0 : F.EvalGroup hAdic).val = ⟨0, (IsLocalRing.maximalIdeal R).zero_mem⟩`
- **What**: Simp lemma: the underlying element of the zero is `0`.
- **How**: `rfl`.
- **Hypotheses**: Has `omit` of topology/completeness hypotheses.
- **Uses from project**: `FormalGroup.EvalGroup`
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 1126–1127; proof `rfl`

---

### `theorem val_add`
- **Type**: `(x y : F.EvalGroup hAdic) : (x + y).val = ⟨F.evalAdd x.val y.val, F.evalAdd_mem hAdic x.val y.val⟩`
- **What**: Simp lemma: the underlying element of `x + y` is `evalAdd x.val y.val`.
- **How**: `rfl`.
- **Hypotheses**: Full section variables.
- **Uses from project**: `FormalGroup.evalAdd`, `FormalGroup.evalAdd_mem`
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 1130–1132; proof `rfl`

---

### `theorem val_neg`
- **Type**: `(x : F.EvalGroup hAdic) : (-x).val = ⟨F.evalNeg x.val, F.evalNeg_mem hAdic x.val⟩`
- **What**: Simp lemma: the underlying element of `-x` is `evalNeg x.val`.
- **How**: `rfl`.
- **Hypotheses**: Full section variables.
- **Uses from project**: `FormalGroup.evalNeg`, `FormalGroup.evalNeg_mem`
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 1135–1137; proof `rfl`

---

### `noncomputable instance FormalGroup.EvalGroup.instAddCommGroup`
- **Type**: `AddCommGroup (F.EvalGroup hAdic)`
- **What**: The main result: the formal group law makes the maximal ideal `M` into an abelian group via `+_F`, with carrier `F.EvalGroup hAdic`.
- **How**: Uses `AddGroup.ofLeftAxioms` to build the `AddGroup` from associativity (`evalAdd_assoc`), left unit (`evalAdd_zero_left`), and left inverse (using `evalAdd_comm` + `evalAdd_evalNeg`); then sets `add_comm` via `evalAdd_comm`.
- **Hypotheses**: All section variables (local ring, adic topology, completeness).
- **Uses from project**: `FormalGroup.evalAdd_assoc`, `FormalGroup.evalAdd_zero_left`, `FormalGroup.evalAdd_comm`, `FormalGroup.evalAdd_evalNeg`, `FormalGroup.evalNeg_mem`, `FormalGroup.EvalGroup.ext`
- **Used by**: unused in file (this is the main export)
- **Visibility**: public
- **Lines**: 1149–1169; proof ~21 lines

---

## Summary Statistics

| Kind | Count |
|------|-------|
| `def` (noncomputable) | 2 (`evalAdd`, `evalNeg`) |
| `structure` | 1 (`EvalGroup`) |
| `instance` | 4 (`Zero`, `Add`, `Neg`, `instAddCommGroup`) |
| `theorem`/`lemma` (public) | 19 |
| `theorem`/`lemma`/`def` (private) | 8 (`finsupp_swap`, `finsupp_swap_apply_zero`, `finsupp_swap_apply_one`, `powerSeries_hasEval_of_mem`, `powerSeries_eval_mem`, `coeff_prod_pow_support_finite`, `continuous_subst_of_constantCoeff_zero`, `mvPowerSeries_eval_mem_maximalIdeal`, `hasEval_of_mem_maximalIdeal_general`, `powerSeries_eval₂_eq_mvEval₂`) |
| **Total** | **34** |

## Key API (used by 3+ declarations in file)
- `eval₂_subst_bridge` — used by `evalAdd_evalNeg`, `evalAdd_assoc` (×4 calls)
- `evalAdd_mem` — used by `evalAdd_evalNeg`, `evalAdd_assoc`, `instAdd`, `val_add`, `instAddCommGroup`
- `maximalIdeal_isClosed` — used by `evalAdd_mem`, `evalNeg_mem`, `powerSeries_eval_mem`, `mvPowerSeries_eval_mem_maximalIdeal`
- `isTopologicallyNilpotent_of_mem_maximalIdeal` — used by `hasEval_of_mem_maximalIdeal`, `powerSeries_hasEval_of_mem`, `mvPowerSeries_eval_mem_maximalIdeal`, `hasEval_of_mem_maximalIdeal_general`, `eval₂_subst_bridge`
- `hasEval_of_mem_maximalIdeal` — used by `evalAdd_mem`, `evalAdd_zero_zero`, `evalAdd_comm`, `evalAdd_zero_right`
- `evalAdd_comm` — used by `evalAdd_zero_left`, `evalAdd_evalNeg` (via rw), `instAddCommGroup`
- `finsupp_swap` — used by `finsupp_swap_apply_zero`, `finsupp_swap_apply_one`, `coeff_swap`, `evalAdd_comm`

## Unused within file (dead-code candidates)
- `evalAdd_zero_zero` — no callers in file
- `coeff_0j_of_ne_one` — no callers in file
- `powerSeries_eval_mem` — no callers in file
- `powerSeries_eval₂_eq_mvEval₂` — no callers in file
- `val_zero`, `val_add`, `val_neg` — no callers in file (simp lemmas for external use)
- `FormalGroup.EvalGroup.instAddCommGroup` — no callers in file (main export)

## `set_option maxHeartbeats`
- L327: `800000` on `evalAdd_comm` — NO-COMMENT
- L971: `800000` on `evalAdd_assoc` — NO-COMMENT

## Sorries
None.
