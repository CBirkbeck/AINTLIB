# Inventory: ./HasseWeil/FormalGroup/MulByNat.lean

**File purpose**: Packages `HasseWeil.FG.mulByNatSeries F n` (the [n]-multiplication power series defined by iterated `fAdd`) as a `FormalGroupHom F F` by proving the `preserves_add` axiom `[n](F(X,Y)) = F([n](X),[n](Y))`. This is Silverman IV.2.3. The proof proceeds by induction on n using a bivariate "interchange law" for `fAdd₂`.

**Import**: `HasseWeil.FormalGroup.Definition`

---

## Private infrastructure: bivariate F-addition

### `private noncomputable def fAdd₂`
- **Type**: `(F : FormalGroup.FormalGroup R) → (a b : MvPowerSeries (Fin 2) R) → MvPowerSeries (Fin 2) R`
- **What**: Defines bivariate substitution `F(a, b)` — substitutes the pair `![a, b]` into the two-variable formal group law `F.toSeries`. This is the bivariate analogue of the existing `fAdd` (which maps `PowerSeries → PowerSeries`).
- **How**: Direct `MvPowerSeries.subst (![a, b]) F.toSeries`.
- **Hypotheses**: None (definition-level, no `HasSubst` guard needed at def site).
- **Uses from project**: `FormalGroup.FormalGroup` (Definition.lean)
- **Used by**: `constantCoeff_fAdd₂`, `fAdd₂_assoc`, `fAdd₂_comm`, `fAdd₂_interchange`, `preservesAddCondition_step` (all in this file)
- **Visibility**: private
- **Lines**: 41–43 (body: 1 line)
- **Notes**: None

---

### `private lemma hasSubst_pair₂`
- **Type**: `(a b : MvPowerSeries (Fin 2) R) → constantCoeff a = 0 → constantCoeff b = 0 → MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries (Fin 2) R)`
- **What**: Constructs the `HasSubst` witness for the pair `![a, b]` when both have vanishing constant coefficients.
- **How**: `MvPowerSeries.hasSubst_of_constantCoeff_zero` + `fin_cases`.
- **Hypotheses**: Constant-coefficient vanishing of both series.
- **Uses from project**: None (uses mathlib's `MvPowerSeries.hasSubst_of_constantCoeff_zero`)
- **Used by**: `constantCoeff_fAdd₂`, `fAdd₂_comm` (this file)
- **Visibility**: private
- **Lines**: 45–50 (proof: 5 lines)
- **Notes**: None

---

### `private lemma hasSubst_triple₂`
- **Type**: `(a b c : MvPowerSeries (Fin 2) R) → constantCoeff a = 0 → constantCoeff b = 0 → constantCoeff c = 0 → MvPowerSeries.HasSubst (![a, b, c] : Fin 3 → MvPowerSeries (Fin 2) R)`
- **What**: Constructs the `HasSubst` witness for a triple `![a, b, c]` with vanishing constant coefficients.
- **How**: `MvPowerSeries.hasSubst_of_constantCoeff_zero` + `fin_cases`.
- **Hypotheses**: Constant-coefficient vanishing of all three series.
- **Uses from project**: None
- **Used by**: `fAdd₂_assoc` (this file)
- **Visibility**: private
- **Lines**: 52–59 (proof: 7 lines)
- **Notes**: None

---

### `private lemma constantCoeff_fAdd₂`
- **Type**: `(F : FormalGroup.FormalGroup R) → (a b : MvPowerSeries (Fin 2) R) → constantCoeff a = 0 → constantCoeff b = 0 → constantCoeff (fAdd₂ F a b) = 0`
- **What**: The bivariate substitution `F(a, b)` has vanishing constant coefficient when both `a` and `b` do — i.e., `fAdd₂` maps the maximal ideal product into itself.
- **How**: Unfolds `fAdd₂`, applies `constantCoeff_subst_vanishing` with the `HasSubst` witness from `hasSubst_pair₂`, then uses `constantCoeff_FG_toSeries`.
- **Hypotheses**: Constant-coefficient vanishing of `a` and `b`.
- **Uses from project**: `fAdd₂` (this file), `hasSubst_pair₂` (this file), `constantCoeff_FG_toSeries` (Definition.lean)
- **Used by**: `fAdd₂_interchange` (this file)
- **Visibility**: private
- **Lines**: 61–69 (proof: 8 lines)
- **Notes**: None

---

### `private theorem fAdd₂_assoc`
- **Type**: `(F : FormalGroup.FormalGroup R) → (a b c : MvPowerSeries (Fin 2) R) → constantCoeff a = 0 → constantCoeff b = 0 → constantCoeff c = 0 → fAdd₂ F (fAdd₂ F a b) c = fAdd₂ F a (fAdd₂ F b c)`
- **What**: Associativity of the bivariate F-addition: `F(F(a,b),c) = F(a,F(b,c))` for power series with vanishing constant coefficients.
- **How**: Applies the formal group's associativity axiom `F.assoc` (itself an equality of power series in 3 variables `MvPowerSeries (Fin 3) R`) by substituting `![a,b,c]` into it, then uses `MvPowerSeries.subst_comp_subst_apply` repeatedly to rewrite both sides as `fAdd₂` expressions. Helper lemmas `subst_fin3_X` from Definition.lean are used to simplify the substitution of `X i` variables.
- **Hypotheses**: Constant-coefficient vanishing of `a`, `b`, `c`.
- **Uses from project**: `fAdd₂` (this file), `hasSubst_triple₂` (this file), `constantCoeff_FG_toSeries` (Definition.lean), `subst_fin3_X` (Definition.lean), `FormalGroup.assoc` (Definition.lean)
- **Used by**: `fAdd₂_interchange` (this file)
- **Visibility**: private
- **Lines**: 73–152 (declaration), proof body: lines 83–152 = **70 lines**
- **Notes**: `set_option maxHeartbeats 800000` at line 73, with comment "Deeply nested `MvPowerSeries.subst` expressions; the default limit is exceeded while unifying the `Fin 3 → MvPowerSeries (Fin 2) R` specialization of `F.assoc`." Proof is >30 lines (70 lines).

---

### `private theorem fAdd₂_comm`
- **Type**: `(F : FormalGroup.FormalGroup R) → (a b : MvPowerSeries (Fin 2) R) → constantCoeff a = 0 → constantCoeff b = 0 → fAdd₂ F a b = fAdd₂ F b a`
- **What**: Commutativity of the bivariate F-addition.
- **How**: Applies `F.comm` (the formal group's commutativity axiom, stated for `MvPowerSeries (Fin 2) R`) by substituting `![a,b]` into it, and uses `subst_matrix_X0`/`subst_matrix_X1` from Definition.lean to rewrite the swap of coordinates.
- **Hypotheses**: Constant-coefficient vanishing of `a` and `b`.
- **Uses from project**: `fAdd₂` (this file), `hasSubst_pair₂` (this file), `subst_matrix_X1` (Definition.lean), `subst_matrix_X0` (Definition.lean), `FormalGroup.comm` (Definition.lean)
- **Used by**: `fAdd₂_interchange` (this file)
- **Visibility**: private
- **Lines**: 155–178 (proof: 23 lines)
- **Notes**: None

---

### `private theorem fAdd₂_interchange`
- **Type**: `(F : FormalGroup.FormalGroup R) → (a b c d : MvPowerSeries (Fin 2) R) → constantCoeff a = 0 → constantCoeff b = 0 → constantCoeff c = 0 → constantCoeff d = 0 → fAdd₂ F (fAdd₂ F a b) (fAdd₂ F c d) = fAdd₂ F (fAdd₂ F a c) (fAdd₂ F b d)`
- **What**: The interchange (Eckmann-Hilton) law: `F(F(a,b), F(c,d)) = F(F(a,c), F(b,d))`, derived from associativity and commutativity.
- **How**: A `calc` chain applying `fAdd₂_assoc` four times and `fAdd₂_comm` once (on the `b,c` pair), rearranging brackets.
- **Hypotheses**: Constant-coefficient vanishing of all four series.
- **Uses from project**: `fAdd₂` (this file), `constantCoeff_fAdd₂` (this file), `fAdd₂_assoc` (this file), `fAdd₂_comm` (this file)
- **Used by**: `preservesAddCondition_step` (this file)
- **Visibility**: private
- **Lines**: 182–203 (proof: 21 lines)
- **Notes**: None

---

## Private infrastructure: PreservesAddCondition

### `private def PreservesAddCondition`
- **Type**: `(F : FormalGroup.FormalGroup R) → (f : PowerSeries R) → Prop`
- **What**: The proposition that a univariate power series `f` is a formal group endomorphism: `f(F(X,Y)) = F(f(X), f(Y))` as an equality in `MvPowerSeries (Fin 2) R`.
- **How**: Definition (not a proof).
- **Hypotheses**: None.
- **Uses from project**: None (uses `PowerSeries.subst`, `MvPowerSeries.subst`, `FormalGroup.toSeries`)
- **Used by**: `preservesAddCondition_zero`, `preservesAddCondition_step`, `mulByNatSeries_preserves_add` (all this file)
- **Visibility**: private
- **Lines**: 210–217 (definition: 7 lines)
- **Notes**: None

---

### `private lemma mv_subst_X_of_unit`
- **Type**: `{τ : Type*} → (a : Unit → MvPowerSeries τ R) → MvPowerSeries.HasSubst a → MvPowerSeries.subst a PowerSeries.X = a ()`
- **What**: Evaluates the substitution of `PowerSeries.X` (viewed as `MvPowerSeries Unit R` generator `X ()`) under a `Unit`-indexed substitution: the result is `a ()`.
- **How**: Reduces to `MvPowerSeries.subst_X` after identifying `PowerSeries.X` with `MvPowerSeries.X ()`.
- **Hypotheses**: `HasSubst a`.
- **Uses from project**: None (uses mathlib `MvPowerSeries.subst_X`)
- **Used by**: `subst_F_applied_to_X`, `subst_Xi_applied_to_X`, `preservesAddCondition_step` (all this file)
- **Visibility**: private
- **Lines**: 220–224 (proof: 4 lines)
- **Notes**: None

---

### `private lemma hasSubst_const_F`
- **Type**: `(F : FormalGroup.FormalGroup R) → MvPowerSeries.HasSubst (fun _ : Unit => F.toSeries : Unit → MvPowerSeries (Fin 2) R)`
- **What**: Constructs the `HasSubst` witness for the constant `Unit`-indexed substitution by `F.toSeries`.
- **How**: `MvPowerSeries.hasSubst_of_constantCoeff_zero` + `constantCoeff_FG_toSeries`.
- **Hypotheses**: None (only `F : FormalGroup`).
- **Uses from project**: `constantCoeff_FG_toSeries` (Definition.lean)
- **Used by**: `subst_F_applied_to_X`, `preservesAddCondition_step` (this file)
- **Visibility**: private
- **Lines**: 226–230 (proof: 4 lines)
- **Notes**: None

---

### `private lemma hasSubst_const_Xi`
- **Type**: `(i : Fin 2) → MvPowerSeries.HasSubst (fun _ : Unit => MvPowerSeries.X i : Unit → MvPowerSeries (Fin 2) R)`
- **What**: Constructs the `HasSubst` witness for the constant `Unit`-indexed substitution by `MvPowerSeries.X i`.
- **How**: `MvPowerSeries.hasSubst_of_constantCoeff_zero`; `constantCoeff (X i) = 0` by `simp`.
- **Hypotheses**: None.
- **Uses from project**: None
- **Used by**: `subst_Xi_applied_to_X`, `preservesAddCondition_step` (this file)
- **Visibility**: private
- **Lines**: 232–235 (proof: 3 lines)
- **Notes**: None

---

### `lemma constantCoeff_univariate_subst`
- **Type**: `(g : MvPowerSeries (Fin 2) R) → constantCoeff g = 0 → (f : PowerSeries R) → PowerSeries.constantCoeff f = 0 → MvPowerSeries.constantCoeff (PowerSeries.subst g f) = 0`
- **What**: Substituting a power series with zero constant coefficient into a bivariate series with zero constant coefficient gives a series with zero constant coefficient.
- **How**: Unfolds `PowerSeries.subst_def` to rewrite as `MvPowerSeries.subst`, then applies `MvPowerSeries.constantCoeff_subst_eq_zero`.
- **Hypotheses**: Constant coefficient of `g` is 0; constant coefficient of `f` is 0.
- **Uses from project**: None (uses mathlib)
- **Used by**: `preservesAddCondition_step` (this file); also used externally by `Hom.lean`
- **Visibility**: public
- **Lines**: 237–244 (proof: 7 lines)
- **Notes**: The only non-private lemma in the `HasseWeil.FG` namespace section (besides the main theorem). Used by `Hom.lean`.

---

### `private lemma subst_F_applied_to_X`
- **Type**: `(F : FormalGroup.FormalGroup R) → PowerSeries.subst F.toSeries PowerSeries.X = F.toSeries`
- **What**: Substituting `X` into `F.toSeries` (via the unit-indexed `PowerSeries.subst`) returns `F.toSeries` unchanged.
- **How**: Rewrites via `PowerSeries.subst_def` then applies `mv_subst_X_of_unit`.
- **Hypotheses**: None.
- **Uses from project**: `mv_subst_X_of_unit` (this file), `hasSubst_const_F` (this file)
- **Used by**: unused in file (only defined here; private, so dead code within this file)
- **Visibility**: private
- **Lines**: 246–250 (proof: 4 lines)
- **Notes**: Dead code within this file — never referenced after definition.

---

### `private lemma subst_Xi_applied_to_X`
- **Type**: `(i : Fin 2) → PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) PowerSeries.X = MvPowerSeries.X i`
- **What**: Substituting `X` (univariate) into `MvPowerSeries.X i` (viewed as a univariate series) returns `MvPowerSeries.X i`.
- **How**: Rewrites via `PowerSeries.subst_def` then applies `mv_subst_X_of_unit`.
- **Hypotheses**: None.
- **Uses from project**: `mv_subst_X_of_unit` (this file), `hasSubst_const_Xi` (this file)
- **Used by**: unused in file (only defined here; private, so dead code within this file)
- **Visibility**: private
- **Lines**: 252–256 (proof: 4 lines)
- **Notes**: Dead code within this file — never referenced after definition.

---

### `private lemma subst_univariate_zero`
- **Type**: `(g : MvPowerSeries (Fin 2) R) → constantCoeff g = 0 → PowerSeries.subst g (0 : PowerSeries R) = 0`
- **What**: Substituting the zero power series gives zero.
- **How**: Unfolds `PowerSeries.subst_def`, builds `HasSubst`, applies `subst_zero_eq` from Definition.lean.
- **Hypotheses**: Constant coefficient of `g` is 0.
- **Uses from project**: `subst_zero_eq` (Definition.lean)
- **Used by**: `preservesAddCondition_zero` (this file)
- **Visibility**: private
- **Lines**: 258–264 (proof: 6 lines)
- **Notes**: None

---

### `private lemma subst_pair_zero_fin2`
- **Type**: `(F : FormalGroup.FormalGroup R) → MvPowerSeries.subst (![(0 : MvPowerSeries (Fin 2) R), 0] : Fin 2 → MvPowerSeries (Fin 2) R) F.toSeries = 0`
- **What**: Substituting the zero vector `(0, 0)` into the formal group law gives 0, reflecting that `F(0, 0) = 0`.
- **How**: Rewrites `![0, 0]` as the constant-zero function, unfolds `MvPowerSeries.coeff_subst`, then applies `finsum_eq_zero_of_forall_eq_zero` (from mathlib). Handles the `d = 0` case via `constantCoeff_FG_toSeries` and the `d ≠ 0` case via `Finsupp.prod_eq_zero` using `zero_pow`.
- **Hypotheses**: None.
- **Uses from project**: `constantCoeff_FG_toSeries` (Definition.lean)
- **Used by**: `preservesAddCondition_zero` (this file)
- **Visibility**: private
- **Lines**: 267–292 (proof: 25 lines)
- **Notes**: None

---

### `private lemma preservesAddCondition_zero`
- **Type**: `(F : FormalGroup.FormalGroup R) → PreservesAddCondition F 0`
- **What**: The zero power series satisfies the `PreservesAddCondition`: `0(F(X,Y)) = F(0(X), 0(Y))` (both sides are 0).
- **How**: Rewrites both sides to 0 using `subst_univariate_zero` and then uses `subst_pair_zero_fin2`.
- **Hypotheses**: None.
- **Uses from project**: `PreservesAddCondition` (this file), `subst_univariate_zero` (this file), `subst_pair_zero_fin2` (this file), `constantCoeff_FG_toSeries` (Definition.lean)
- **Used by**: `mulByNatSeries_preserves_add` (this file)
- **Visibility**: private
- **Lines**: 295–301 (proof: 6 lines)
- **Notes**: None

---

### `private lemma preservesAddCondition_step`
- **Type**: `(F : FormalGroup.FormalGroup R) → (f : PowerSeries R) → PowerSeries.constantCoeff f = 0 → PreservesAddCondition F f → PreservesAddCondition F (fAdd F f PowerSeries.X)`
- **What**: The key inductive step: if `f` satisfies `PreservesAddCondition`, then `fAdd F f X = F(f, X)` (the next iterate in the mulByNat recurrence) also satisfies it.
- **How**: Sets `fX = f(X_0)` and `fY = f(X_1)` (the bivariate lifts of `f`). Establishes three `fAdd₂` rewriting lemmas: the LHS `F.toSeries(fAdd F f X)` equals `fAdd₂ F (subst F f) F.toSeries`, and the two RHS substitutions give `fAdd₂ F fX X₀` and `fAdd₂ F fY X₁`. Then uses the induction hypothesis to substitute, rewrites `F.toSeries` itself as `fAdd₂ F X₀ X₁` (via `MvPowerSeries.subst_self`), and applies `fAdd₂_interchange` to conclude. The core mechanism is `MvPowerSeries.subst_comp_subst_apply` and `hasSubst_pair` (from Definition.lean).
- **Hypotheses**: `f` has vanishing constant coefficient; `f` satisfies `PreservesAddCondition`.
- **Uses from project**: `PreservesAddCondition` (this file), `fAdd₂` (this file), `fAdd₂_interchange` (this file), `constantCoeff_univariate_subst` (this file), `mv_subst_X_of_unit` (this file), `hasSubst_const_F` (this file), `hasSubst_const_Xi` (this file), `hasSubst_pair` (Definition.lean), `fAdd` (Definition.lean)
- **Used by**: `mulByNatSeries_preserves_add` (this file)
- **Visibility**: private
- **Lines**: 305–372 (proof body: lines 309–372 = **63 lines**)
- **Notes**: Proof is >30 lines (63 lines). This is the mathematical core of the file.

---

## Main results

### `theorem mulByNatSeries_preserves_add`
- **Type**: `(F : FormalGroup.FormalGroup R) → (n : ℕ) → PowerSeries.subst F.toSeries (mulByNatSeries F n) = MvPowerSeries.subst (![PowerSeries.subst (X 0) (mulByNatSeries F n), PowerSeries.subst (X 1) (mulByNatSeries F n)]) F.toSeries`
- **What**: The main theorem: `[n](F(X, Y)) = F([n](X), [n](Y))` — multiplication-by-n on the formal group is a formal group homomorphism. This is Silverman IV.2.3.
- **How**: Reduces to `PreservesAddCondition F (mulByNatSeries F n)` and proves it by structural induction on `n`, using `preservesAddCondition_zero` for the base case and `preservesAddCondition_step` + `constantCoeff_mulByNatSeries` for the inductive step.
- **Hypotheses**: None (works for all `n : ℕ` and any commutative ring `R`).
- **Uses from project**: `PreservesAddCondition` (this file), `preservesAddCondition_zero` (this file), `preservesAddCondition_step` (this file), `mulByNatSeries` (Definition.lean), `constantCoeff_mulByNatSeries` (Definition.lean), `fAdd` (Definition.lean)
- **Used by**: `FormalGroup.mulByNatHom` (this file, via `preserves_add` field)
- **Visibility**: public
- **Lines**: 381–397 (proof: 16 lines)
- **Notes**: None

---

## FormalGroupHom packaging

### `noncomputable def FormalGroup.mulByNatHom`
- **Type**: `(F : FormalGroup R) → (n : ℕ) → FormalGroupHom F F`
- **What**: Packages `mulByNatSeries F n` as a `FormalGroupHom F F`, assembling the three required fields: `toSeries`, `zero_const`, and `preserves_add`.
- **How**: Direct record construction using `mulByNatSeries`, `constantCoeff_mulByNatSeries`, and `mulByNatSeries_preserves_add`.
- **Hypotheses**: None.
- **Uses from project**: `mulByNatSeries` (Definition.lean), `constantCoeff_mulByNatSeries` (Definition.lean), `mulByNatSeries_preserves_add` (this file)
- **Used by**: `mulByNatHom_toSeries`, `coeff_one_mulByNatHom`, `mulByNatHom_zero_toSeries`, `mulByNatHom_one_toSeries` (all this file); extensively used by `CharP.lean`, `Height.lean`, `Associated.lean`, `Hom.lean`
- **Visibility**: public
- **Lines**: 411–415 (5 lines)
- **Notes**: None

---

### `@[simp] theorem FormalGroup.mulByNatHom_toSeries`
- **Type**: `(F : FormalGroup R) → (n : ℕ) → (F.mulByNatHom n).toSeries = HasseWeil.FG.mulByNatSeries F n`
- **What**: The underlying power series of `mulByNatHom` is exactly `mulByNatSeries`.
- **How**: `rfl`
- **Hypotheses**: None.
- **Uses from project**: `mulByNatSeries` (Definition.lean), `FormalGroup.mulByNatHom` (this file)
- **Used by**: Used externally by `Associated.lean` and `Hom.lean`; unused by other decls within this file.
- **Visibility**: public (`@[simp]`)
- **Lines**: 419–421 (proof: 1 line)
- **Notes**: None

---

### `@[simp] theorem FormalGroup.coeff_one_mulByNatHom`
- **Type**: `(F : FormalGroup R) → (n : ℕ) → PowerSeries.coeff 1 (F.mulByNatHom n).toSeries = (n : R)`
- **What**: The linear coefficient of `[n]` is `n`: the formal group multiplication by `n` has linear term `nT`.
- **How**: Delegates to `HasseWeil.FG.coeff_one_mulByNatSeries` from Definition.lean.
- **Hypotheses**: None.
- **Uses from project**: `coeff_one_mulByNatSeries` (Definition.lean), `FormalGroup.mulByNatHom` (this file)
- **Used by**: Used externally by `CharP.lean` and `Hom.lean`; unused by other decls within this file.
- **Visibility**: public (`@[simp]`)
- **Lines**: 427–429 (proof: 1 line)
- **Notes**: None

---

### `@[simp] theorem FormalGroup.mulByNatHom_zero_toSeries`
- **Type**: `(F : FormalGroup R) → (F.mulByNatHom 0).toSeries = 0`
- **What**: `[0](T) = 0`.
- **How**: `rfl`
- **Hypotheses**: None.
- **Uses from project**: `FormalGroup.mulByNatHom` (this file)
- **Used by**: Used externally by `Associated.lean`; unused by other decls within this file.
- **Visibility**: public (`@[simp]`)
- **Lines**: 433–434 (proof: 1 line)
- **Notes**: None

---

### `@[simp] theorem FormalGroup.mulByNatHom_one_toSeries`
- **Type**: `(F : FormalGroup R) → (F.mulByNatHom 1).toSeries = PowerSeries.X`
- **What**: `[1](T) = T` — the multiplication-by-1 hom is the identity at the power series level.
- **How**: Delegates to `HasseWeil.FG.mulByNatSeries_one` from Definition.lean.
- **Hypotheses**: None.
- **Uses from project**: `mulByNatSeries_one` (Definition.lean), `FormalGroup.mulByNatHom` (this file)
- **Used by**: Used externally by `Hom.lean`; unused by other decls within this file.
- **Visibility**: public (`@[simp]`)
- **Lines**: 438–440 (proof: 2 lines)
- **Notes**: None

---

## Summary statistics

| Kind | Count |
|------|-------|
| `private def` / `private noncomputable def` | 2 |
| `private lemma` / `private theorem` | 11 |
| `lemma` (public) | 1 |
| `theorem` (public) | 5 |
| `noncomputable def` (public) | 1 |
| **Total** | **20** |

- **Sorries**: none
- **`set_option maxHeartbeats`**: 1 occurrence at line 73 (`fAdd₂_assoc`: 800000, reason comment present)
- **Long proofs (>30 lines)**: `fAdd₂_assoc` (70 lines), `preservesAddCondition_step` (63 lines)
- **Unused within file**: `subst_F_applied_to_X`, `subst_Xi_applied_to_X` (both private, dead code)
- **Key API** (used by 3+ other decls in this file): `fAdd₂`, `mv_subst_X_of_unit`, `PreservesAddCondition`, `constantCoeff_fAdd₂`, `fAdd₂_assoc`
