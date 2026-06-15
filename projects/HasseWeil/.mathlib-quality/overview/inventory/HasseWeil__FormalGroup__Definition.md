# Inventory: ./HasseWeil/FormalGroup/Definition.lean

**File**: `HasseWeil/FormalGroup/Definition.lean`
**Lines**: 804
**Namespaces**: `HasseWeil.FormalGroup` (structures and examples), `HasseWeil.FG` (API)
**Imports**: `Mathlib.RingTheory.MvPowerSeries.Substitution`, `Mathlib.RingTheory.PowerSeries.Basic`, `Mathlib.RingTheory.PowerSeries.Substitution`

---

## Structures

### `structure FormalGroup`
- **Type**: `structure FormalGroup where toSeries : MvPowerSeries (Fin 2) R; lunit/runit/assoc/comm : ...`
- **What**: A commutative one-parameter formal group law over a commutative ring `R`, encoded as a bivariate power series `F(X,Y) ∈ R[[X,Y]]` satisfying left/right unit, associativity (in 3 variables), and commutativity axioms via `MvPowerSeries.subst`.
- **How**: Pure data structure; axioms stated as equalities of `MvPowerSeries.subst` expressions.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: none
- **Used by**: `additiveFormalGroup`, `multiplicativeFormalGroup`, and all `HasseWeil.FG` declarations (as their main argument type).
- **Visibility**: public
- **Lines**: 65–106
- **Notes**: `set_option linter.dupNamespace false` applied at line 48 to suppress the `FormalGroup.FormalGroup` namespace warning.

### `structure FormalGroupHom`
- **Type**: `structure FormalGroupHom (F G : FormalGroup R) where toSeries : PowerSeries R; zero_const : constantCoeff toSeries = 0; preserves_add : PowerSeries.subst F.toSeries toSeries = MvPowerSeries.subst ![...] G.toSeries`
- **What**: A homomorphism of formal group laws from `F` to `G`: a univariate power series `f(T) ∈ R[[T]]` with `f(0) = 0` satisfying `f(F(X,Y)) = G(f(X), f(Y))`.
- **How**: Pure data structure.
- **Hypotheses**: `R` a commutative ring; `F G : FormalGroup R`.
- **Uses from project**: `FormalGroup` (as argument)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 121–141
- **Notes**: Defined but not used elsewhere in this file (dead code candidate within file; may be used by other files).

---

## Definitions

### `noncomputable def additiveFormalGroup`
- **Type**: `additiveFormalGroup : FormalGroup R`
- **What**: Constructs the additive formal group law `Ĝ_a` over `R` with `F(X,Y) = X + Y`.
- **How**: Each axiom is verified by `MvPowerSeries.subst_add`, `MvPowerSeries.subst_X`, and `ring`. The `HasSubst` condition for each substitution is checked via `MvPowerSeries.hasSubst_of_constantCoeff_zero`.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: `FormalGroup` (as target type)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 150–235 (proof ~85 lines)
- **Notes**: Long proof (>30 lines). Example/demonstration; not referenced internally.

### `noncomputable def multiplicativeFormalGroup`
- **Type**: `multiplicativeFormalGroup : FormalGroup R`
- **What**: Constructs the multiplicative formal group law `Ĝ_m` over `R` with `F(X,Y) = X + Y + XY`.
- **How**: Same pattern as `additiveFormalGroup`: `subst_add`, `subst_mul`, `subst_X`, and `ring` close each axiom; `HasSubst` checked via `hasSubst_of_constantCoeff_zero`.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: `FormalGroup` (as target type)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 241–347 (proof ~107 lines)
- **Notes**: Long proof (>30 lines). Example/demonstration; not referenced internally.

### `noncomputable def fAdd`
- **Type**: `fAdd (F : FormalGroup.FormalGroup R) (f g : PowerSeries R) : PowerSeries R`
- **What**: Evaluates the formal group law at two univariate power series: computes `F(f, g)` as a univariate series via `MvPowerSeries.subst`.
- **How**: Direct definition: `MvPowerSeries.subst (![f, g]) F.toSeries`.
- **Hypotheses**: `R` a commutative ring; `F` a formal group law.
- **Uses from project**: `FormalGroup` (field `toSeries`)
- **Used by**: `mulByNatSeries`, `formalGroup_preserves_positive_order`, `fAdd_zero_left`, `mulByNatSeries_one`, `coeff_one_fAdd`, `constantCoeff_fAdd`, `constantCoeff_mulByNatSeries`, `coeff_one_mulByNatSeries`, `fAdd_zero_right`, `fAdd_comm`, `fAdd_assoc`, `mulByNatSeries_add`
- **Visibility**: public
- **Lines**: 366–368
- **Notes**: Core operation used by almost every subsequent theorem.

### `noncomputable def mulByNatSeries`
- **Type**: `mulByNatSeries (F : FormalGroup.FormalGroup R) : ℕ → PowerSeries R`
- **What**: The multiplication-by-n series `[n](T)` defined recursively: `[0](T) = 0`, `[n+1](T) = F([n](T), T)`.
- **How**: Recursive definition using `fAdd`.
- **Hypotheses**: `R` a commutative ring; `F` a formal group law.
- **Uses from project**: `fAdd`
- **Used by**: `mulByNatSeries_one`, `constantCoeff_mulByNatSeries`, `coeff_one_mulByNatSeries`, `mulByNatSeries_add`
- **Visibility**: public
- **Lines**: 373–375

---

## Lemmas (Infrastructure)

### `lemma hasSubst_pair`
- **Type**: `hasSubst_pair (f g : PowerSeries R) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) : MvPowerSeries.HasSubst (![f, g] : Fin 2 → MvPowerSeries Unit R)`
- **What**: The substitution data `![f, g]` into `MvPowerSeries Unit R` satisfies the `HasSubst` condition whenever `f` and `g` have zero constant coefficient.
- **How**: Applies `MvPowerSeries.hasSubst_of_constantCoeff_zero` and checks by `fin_cases`.
- **Hypotheses**: `f(0) = g(0) = 0`.
- **Uses from project**: none
- **Used by**: `constantCoeff_fAdd`, `fAdd_zero_left`, `fAdd_zero_right`, `fAdd_comm`, `fAdd_assoc`, `coeff_one_fAdd`
- **Visibility**: public (package-private by convention, no `private` keyword)
- **Lines**: 381–384

### `lemma subst_matrix_X0`
- **Type**: `subst_matrix_X0 {σ} (a : Fin 2 → MvPowerSeries σ R) (ha : HasSubst a) : subst a (X 0 : MvPowerSeries (Fin 2) R) = a 0`
- **What**: Specializes `MvPowerSeries.subst_X` to index 0 for `Fin 2`-indexed substitutions; `subst a (X 0) = a 0`.
- **How**: Direct application of `MvPowerSeries.subst_X`.
- **Hypotheses**: `HasSubst a`.
- **Uses from project**: none
- **Used by**: `fAdd_zero_right`, `fAdd_comm`
- **Visibility**: public
- **Lines**: 386–389

### `lemma subst_matrix_X1`
- **Type**: `subst_matrix_X1 {σ} (a : Fin 2 → MvPowerSeries σ R) (ha : HasSubst a) : subst a (X 1 : MvPowerSeries (Fin 2) R) = a 1`
- **What**: Same as `subst_matrix_X0` but for index 1.
- **How**: Direct application of `MvPowerSeries.subst_X`.
- **Hypotheses**: `HasSubst a`.
- **Uses from project**: none
- **Used by**: `fAdd_zero_left`, `fAdd_comm`
- **Visibility**: public
- **Lines**: 391–394

### `lemma subst_fin3_X`
- **Type**: `subst_fin3_X {σ} (a : Fin 3 → MvPowerSeries σ R) (ha : HasSubst a) (i : Fin 3) : subst a (X i : MvPowerSeries (Fin 3) R) = a i`
- **What**: Specializes `MvPowerSeries.subst_X` for `Fin 3`-indexed substitutions; `subst a (X i) = a i` for all `i : Fin 3`.
- **How**: Direct application of `MvPowerSeries.subst_X`.
- **Hypotheses**: `HasSubst a`.
- **Uses from project**: none
- **Used by**: `fAdd_assoc`
- **Visibility**: public
- **Lines**: 396–399

### `lemma subst_zero_eq`
- **Type**: `subst_zero_eq {σ τ} {a : σ → MvPowerSeries τ R} (ha : HasSubst a) : subst a (0 : MvPowerSeries σ R) = 0`
- **What**: Substitution into the zero series is zero (when all substituted series vanish at 0).
- **How**: Uses the cast of `0 : MvPolynomial σ R` and `MvPowerSeries.subst_coe` followed by simp.
- **Hypotheses**: `HasSubst a`.
- **Uses from project**: none
- **Used by**: `fAdd_zero_left`, `fAdd_zero_right`
- **Visibility**: public
- **Lines**: 401–405

---

## Theorems (Main API)

### `theorem constantCoeff_subst_vanishing`
- **Type**: `constantCoeff_subst_vanishing {σ τ} {a : σ → MvPowerSeries τ R} (ha : HasSubst a) (hcc : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) : constantCoeff (subst a f) = constantCoeff f`
- **What**: When all substituted series vanish at the origin, the constant coefficient is unchanged by substitution: `(subst a f)(0) = f(0)`.
- **How**: Uses `MvPowerSeries.coeff_subst` to expand the sum, then `finsum_eq_single` to isolate the zero multiindex term; all other terms vanish because each `a s` has zero constant coefficient (shown via `Finset.prod_eq_zero` + `map_pow`).
- **Hypotheses**: `HasSubst a`; all `a s` have zero constant coefficient.
- **Uses from project**: none
- **Used by**: `constantCoeff_FG_toSeries`, `fAdd_assoc`
- **Visibility**: public
- **Lines**: 409–425 (proof ~17 lines)

### `theorem constantCoeff_FG_toSeries`
- **Type**: `constantCoeff_FG_toSeries (F : FormalGroup.FormalGroup R) : constantCoeff F.toSeries = 0`
- **What**: The constant coefficient of a formal group law is zero: `F(0,0) = 0`.
- **How**: Applies `constantCoeff_subst_vanishing` to `F.lunit` (substituting `![X 0, 0]`) to extract the constant coefficient of `F.toSeries`.
- **Hypotheses**: none (any formal group law)
- **Uses from project**: `constantCoeff_subst_vanishing`
- **Used by**: `constantCoeff_fAdd`, `fAdd_assoc`, `coeff_one_fAdd`
- **Visibility**: public
- **Lines**: 428–435 (proof ~8 lines)

### `theorem constantCoeff_fAdd`
- **Type**: `constantCoeff_fAdd (F : FormalGroup.FormalGroup R) (f g : PowerSeries R) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) : constantCoeff (fAdd F f g) = 0`
- **What**: The formal group law applied to series vanishing at 0 again vanishes at 0: `F(f,g)(0) = 0`.
- **How**: Uses `constantCoeff_subst_vanishing` for the substitution `![f,g]`, then concludes via `constantCoeff_FG_toSeries`.
- **Hypotheses**: `f(0) = g(0) = 0`.
- **Uses from project**: `fAdd`, `hasSubst_pair`, `constantCoeff_subst_vanishing`, `constantCoeff_FG_toSeries`
- **Used by**: `formalGroup_preserves_positive_order`, `constantCoeff_mulByNatSeries`
- **Visibility**: public
- **Lines**: 438–444 (proof ~7 lines)

### `theorem formalGroup_preserves_positive_order`
- **Type**: `formalGroup_preserves_positive_order (F : FormalGroup.FormalGroup R) (f g : PowerSeries R) (hf : 0 < f.order) (hg : 0 < g.order) : 0 < (fAdd F f g).order`
- **What**: The formal group law maps `𝔪 × 𝔪 → 𝔪`: if `f` and `g` have positive order (vanish at 0), so does `F(f,g)`.
- **How**: Bridges `0 < order` with `constantCoeff = 0` via `PowerSeries.order_ne_zero_iff_constCoeff_eq_zero`, then applies `constantCoeff_fAdd`.
- **Hypotheses**: `f` and `g` have positive power series order.
- **Uses from project**: `fAdd`, `constantCoeff_fAdd`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 451–456 (proof ~5 lines)

### `theorem fAdd_zero_left`
- **Type**: `fAdd_zero_left (F : FormalGroup.FormalGroup R) (g : PowerSeries R) (hg : constantCoeff g = 0) : fAdd F 0 g = g`
- **What**: The left unit law for `fAdd`: `F(0, g) = g`.
- **How**: Applies the outer substitution `![0,g]` to `F.runit`, using `MvPowerSeries.subst_comp_subst_apply` to reduce the composition, then equates the resulting substitution with the identity via `subst_matrix_X1` and `subst_zero_eq`.
- **Hypotheses**: `g(0) = 0`.
- **Uses from project**: `fAdd`, `hasSubst_pair`, `subst_matrix_X1`, `subst_zero_eq`
- **Used by**: `mulByNatSeries_one`
- **Visibility**: public
- **Lines**: 459–478 (proof ~19 lines)

### `theorem mulByNatSeries_one`
- **Type**: `mulByNatSeries_one (F : FormalGroup.FormalGroup R) : mulByNatSeries F 1 = PowerSeries.X`
- **What**: Multiplication by 1 is the identity: `[1](T) = T`.
- **How**: Directly applies `fAdd_zero_left` since `[1](T) = fAdd F 0 T`.
- **Hypotheses**: none
- **Uses from project**: `mulByNatSeries`, `fAdd_zero_left`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 481–483 (proof 1 line)

### `private lemma coeff_one_high_deg`
- **Type**: `coeff_one_high_deg (f g : PowerSeries R) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (a b : ℕ) (hab : 2 ≤ a + b) : PowerSeries.coeff 1 (f^a * g^b) = 0`
- **What**: When `a + b ≥ 2` and `f(0) = g(0) = 0`, the degree-1 coefficient of `f^a * g^b` vanishes.
- **How**: Shows `X^(a+b) | f^a * g^b` using `pow_dvd_pow_of_dvd` and `PowerSeries.X_dvd_iff`, then applies `PowerSeries.X_pow_dvd_iff`.
- **Hypotheses**: `f(0) = g(0) = 0`, `a + b ≥ 2`.
- **Uses from project**: none
- **Used by**: `coeff_one_fAdd`
- **Visibility**: private
- **Lines**: 487–496 (proof ~9 lines)

### `theorem FormalGroup.coeff_10`
- **Type**: `FormalGroup.coeff_10 (F : FormalGroup.FormalGroup R) : coeff (Finsupp.single 0 1) F.toSeries = 1`
- **What**: The coefficient of `X¹Y⁰` in `F(X,Y)` is 1 (derived from `F(X,0) = X`).
- **How**: Extracts the `Finsupp.single 0 1` coefficient from `F.lunit` using `MvPowerSeries.coeff_subst` and `finsum_eq_single`; all other multiindex terms vanish by case analysis (`zero_pow`, `MvPowerSeries.coeff_X_pow`).
- **Hypotheses**: none
- **Uses from project**: `FormalGroup` (field `lunit`)
- **Used by**: `coeff_one_fAdd`
- **Visibility**: public
- **Lines**: 499–525 (proof ~26 lines)

### `theorem FormalGroup.coeff_01`
- **Type**: `FormalGroup.coeff_01 (F : FormalGroup.FormalGroup R) : coeff (Finsupp.single 1 1) F.toSeries = 1`
- **What**: The coefficient of `X⁰Y¹` in `F(X,Y)` is 1 (derived from `F(0,Y) = Y`).
- **How**: Symmetric argument to `coeff_10`, extracting from `F.runit`.
- **Hypotheses**: none
- **Uses from project**: `FormalGroup` (field `runit`)
- **Used by**: `coeff_one_fAdd`
- **Visibility**: public
- **Lines**: 528–555 (proof ~27 lines)

### `theorem coeff_one_fAdd`
- **Type**: `coeff_one_fAdd (F : FormalGroup.FormalGroup R) (f g : PowerSeries R) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) : coeff 1 (fAdd F f g) = coeff 1 f + coeff 1 g`
- **What**: The linear coefficient of `F(f,g)` is the sum of linear coefficients: `[X^1] F(f,g) = [X^1] f + [X^1] g` (abstract analogue of Silverman III.5.6).
- **How**: Expands `coeff_subst`, restricts the finsum to the two multiindices `{e₁₀, e₀₁}` via `finsum_eq_finset_sum_of_support_subset` (using `coeff_one_high_deg` to kill higher-degree terms and the `d=0` case via `constantCoeff_FG_toSeries`), then applies `FormalGroup.coeff_10` and `FormalGroup.coeff_01`.
- **Hypotheses**: `f(0) = g(0) = 0`.
- **Uses from project**: `fAdd`, `hasSubst_pair`, `coeff_one_high_deg`, `constantCoeff_FG_toSeries`, `FormalGroup.coeff_10`, `FormalGroup.coeff_01`
- **Used by**: `coeff_one_mulByNatSeries`
- **Visibility**: public
- **Lines**: 559–609 (proof ~50 lines)
- **Notes**: Long proof (>30 lines).

### `theorem constantCoeff_mulByNatSeries`
- **Type**: `constantCoeff_mulByNatSeries (F : FormalGroup.FormalGroup R) (n : ℕ) : constantCoeff (mulByNatSeries F n) = 0`
- **What**: The constant coefficient of `[n](T)` is zero for all `n : ℕ`.
- **How**: Induction on `n`; base case trivial; inductive step applies `constantCoeff_fAdd`.
- **Hypotheses**: none
- **Uses from project**: `mulByNatSeries`, `constantCoeff_fAdd`
- **Used by**: `coeff_one_mulByNatSeries`, `mulByNatSeries_add`
- **Visibility**: public
- **Lines**: 612–616 (proof ~4 lines)

### `theorem coeff_one_mulByNatSeries`
- **Type**: `coeff_one_mulByNatSeries (F : FormalGroup.FormalGroup R) (n : ℕ) : coeff 1 (mulByNatSeries F n) = (n : R)`
- **What**: Silverman IV.2.3(a): the leading coefficient of `[n](T)` is `n`; i.e., `[n](T) = n·T + O(T²)`.
- **How**: Induction on `n`; inductive step uses `coeff_one_fAdd` then `constantCoeff_mulByNatSeries` to supply the vanishing hypothesis; arithmetic closed by `simp [Nat.cast_succ]`.
- **Hypotheses**: none
- **Uses from project**: `mulByNatSeries`, `coeff_one_fAdd`, `constantCoeff_mulByNatSeries`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 620–627 (proof ~8 lines)

### `theorem fAdd_zero_right`
- **Type**: `fAdd_zero_right (F : FormalGroup.FormalGroup R) (f : PowerSeries R) (hf : constantCoeff f = 0) : fAdd F f 0 = f`
- **What**: The right unit law for `fAdd`: `F(f, 0) = f`.
- **How**: Symmetric to `fAdd_zero_left`: applies outer substitution `![f,0]` to `F.lunit`, uses `subst_comp_subst_apply` and `subst_matrix_X0`, `subst_zero_eq`.
- **Hypotheses**: `f(0) = 0`.
- **Uses from project**: `fAdd`, `hasSubst_pair`, `subst_matrix_X0`, `subst_zero_eq`
- **Used by**: `mulByNatSeries_add`
- **Visibility**: public
- **Lines**: 632–651 (proof ~19 lines)

### `theorem fAdd_comm`
- **Type**: `fAdd_comm (F : FormalGroup.FormalGroup R) (f g : PowerSeries R) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) : fAdd F f g = fAdd F g f`
- **What**: Commutativity of `fAdd`: `F(f, g) = F(g, f)`.
- **How**: Applies outer substitution `![f,g]` to `F.comm`, uses `subst_comp_subst_apply` and then shows the intermediate substitution `![f,g] ∘ ![X 1, X 0]` equals `![g,f]` via `subst_matrix_X0/X1`.
- **Hypotheses**: `f(0) = g(0) = 0`.
- **Uses from project**: `fAdd`, `hasSubst_pair`, `subst_matrix_X0`, `subst_matrix_X1`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 654–674 (proof ~21 lines)

### `theorem fAdd_assoc` *(set_option maxHeartbeats 800000)*
- **Type**: `fAdd_assoc (F : FormalGroup.FormalGroup R) (f g h : PowerSeries R) (hf hg hh : constantCoeff = 0) : fAdd F (fAdd F f g) h = fAdd F f (fAdd F g h)`
- **What**: Associativity of `fAdd`: `F(F(f,g), h) = F(f, F(g,h))`.
- **How**: Applies `![f,g,h]` to `F.assoc` using `MvPowerSeries.subst_comp_subst_apply` twice (for both the LHS composition `F(F(X,Y),Z)` and RHS `F(X,F(Y,Z))`), with `subst_fin3_X` and `hasSubst_pair`; `constantCoeff_subst_vanishing` and `constantCoeff_FG_toSeries` supply the needed `HasSubst` conditions.
- **Hypotheses**: `f(0) = g(0) = h(0) = 0`.
- **Uses from project**: `fAdd`, `hasSubst_pair`, `subst_fin3_X`, `constantCoeff_subst_vanishing`, `constantCoeff_FG_toSeries`
- **Used by**: `mulByNatSeries_add`
- **Visibility**: public
- **Lines**: 678–785 (proof ~107 lines)
- **Notes**: Long proof (>30 lines). `set_option maxHeartbeats 800000` at line 676, NO justifying comment.

### `theorem mulByNatSeries_add` *(set_option maxHeartbeats 1600000)*
- **Type**: `mulByNatSeries_add (F : FormalGroup.FormalGroup R) (m n : ℕ) : mulByNatSeries F (m + n) = fAdd F (mulByNatSeries F m) (mulByNatSeries F n)`
- **What**: The addition formula for multiplication-by-n: `[m+n](T) = F([m](T), [n](T))`.
- **How**: Induction on `n`; base case uses `fAdd_zero_right`; inductive step rewrites using `fAdd_assoc` with `constantCoeff_mulByNatSeries` supplying the vanishing hypotheses.
- **Hypotheses**: none
- **Uses from project**: `mulByNatSeries`, `fAdd`, `fAdd_zero_right`, `fAdd_assoc`, `constantCoeff_mulByNatSeries`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 789–803 (proof ~14 lines)
- **Notes**: `set_option maxHeartbeats 1600000` at line 787, NO justifying comment. The high heartbeat limit is presumably due to the `fAdd_assoc` call which itself needed 800k.

---

## Summary Statistics

| Category | Count |
|---|---|
| Structures | 2 |
| Noncomputable defs | 4 |
| Lemmas (public) | 4 |
| Lemmas (private) | 1 |
| Theorems | 14 |
| **Total declarations** | **25** |

**Sorries**: none

**Long proofs (>30 lines)**:
- `additiveFormalGroup`: ~85 lines
- `multiplicativeFormalGroup`: ~107 lines
- `coeff_one_fAdd`: ~50 lines
- `fAdd_assoc`: ~107 lines

**`set_option maxHeartbeats`**:
- Line 676 (for `fAdd_assoc`): 800000, NO-COMMENT
- Line 787 (for `mulByNatSeries_add`): 1600000, NO-COMMENT

**Key API (used by 3+ declarations in file)**:
- `fAdd`: used by almost all theorems
- `hasSubst_pair`: used by 6 theorems
- `constantCoeff_FG_toSeries`: used by `constantCoeff_fAdd`, `fAdd_assoc`, `coeff_one_fAdd`
- `constantCoeff_subst_vanishing`: used by `constantCoeff_FG_toSeries`, `fAdd_assoc`
- `constantCoeff_mulByNatSeries`: used by `coeff_one_mulByNatSeries`, `mulByNatSeries_add`

**Unused in file** (potential dead code from this file's perspective):
- `FormalGroupHom` (structure defined but never referenced)
- `additiveFormalGroup` (example, not referenced by any theorem in this file)
- `multiplicativeFormalGroup` (example, not referenced by any theorem in this file)
- `mulByNatSeries_one` (not used in this file)
- `formalGroup_preserves_positive_order` (not used in this file)
- `fAdd_comm` (not used in this file)
- `coeff_one_mulByNatSeries` (not used in this file)
- `mulByNatSeries_add` (not used in this file)
