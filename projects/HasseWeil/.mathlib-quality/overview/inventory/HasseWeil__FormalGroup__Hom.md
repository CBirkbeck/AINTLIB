# Inventory: ./HasseWeil/FormalGroup/Hom.lean

**File**: `HasseWeil/FormalGroup/Hom.lean`
**Imports**: `HasseWeil.FormalGroup.MulByNat`, `HasseWeil.FormalGroup.Logarithm`
**Namespace**: `HasseWeil.FormalGroup`
**Total declarations**: 23 (3 defs, 20 theorems/lemmas, 0 instances)
**Sorries**: none
**set_option**: `linter.dupNamespace false` (line 37, not a heartbeat option)

---

## Declarations

---

### `theorem FormalGroupHom.ext`

- **Type**: `{F G : FormalGroup R} {f g : FormalGroupHom F G} → f.toSeries = g.toSeries → f = g`
- **What**: Extensionality for formal group homomorphisms: two homs are equal iff their underlying power series are equal (the other fields are propositions handled by proof irrelevance).
- **How**: `cases f; cases g; congr` — structural deconstruction followed by `congr` using proof irrelevance.
- **Hypotheses**: `R` a commutative ring; `F`, `G` formal groups over `R`.
- **Uses from project**: none (uses only `FormalGroupHom` structure fields)
- **Used by**: `FormalGroupHom.id_comp`, `FormalGroupHom.comp_id`
- **Visibility**: public, tagged `@[ext]`
- **Lines**: 49–52, proof ~2 lines
- **Notes**: Standard ext lemma, no notable issues.

---

### `noncomputable def FormalGroupHom.id`

- **Type**: `(F : FormalGroup R) → FormalGroupHom F F`
- **What**: The identity formal group homomorphism `F → F`, whose underlying power series is `PowerSeries.X` (the variable `T`).
- **How**: The `preserves_add` field requires showing `subst F.toSeries X = F.toSeries` and that the bivariate identity substitution `![X 0, X 1]` fixes `F.toSeries`. The key lemma is `MvPowerSeries.subst_X` (substituting X into a HasSubst system returns X) and `MvPowerSeries.subst_self` (substituting the identity variables fixes any series). Uses `HasseWeil.FG.constantCoeff_FG_toSeries` to obtain `HasSubst` witnesses.
- **Hypotheses**: `R` a commutative ring; `F` a formal group over `R`.
- **Uses from project**: `HasseWeil.FG.constantCoeff_FG_toSeries`
- **Used by**: `FormalGroupHom.id_toSeries`, `FormalGroupHom.coeff_one_id`, `FormalGroupHom.id_eq_mulByNatHom_one`, `FormalGroupHom.id_comp`, `FormalGroupHom.comp_id`, `FormalGroup.mulByNatHom_one_isIso`, `FormalGroup.mulByNatHom_one_exists_inverse`
- **Visibility**: public
- **Lines**: 59–104, proof ~45 lines
- **Notes**: **Proof >30 lines.** The `preserves_add` field is the nontrivial part; requires 3 auxiliary `have` steps to handle the bivariate substitution identity.

---

### `theorem FormalGroupHom.id_toSeries`

- **Type**: `(F : FormalGroup R) → (FormalGroupHom.id F).toSeries = PowerSeries.X`
- **What**: The underlying series of the identity hom is `X`. This is definitionally true.
- **How**: `rfl`.
- **Hypotheses**: none beyond `R` commutative ring.
- **Uses from project**: `FormalGroupHom.id` (definitionally)
- **Used by**: `FormalGroupHom.coeff_one_id`, `FormalGroupHom.id_eq_mulByNatHom_one`, `FormalGroupHom.id_comp`, `FormalGroupHom.comp_id`
- **Visibility**: public, tagged `@[simp]`
- **Lines**: 108–109, proof 0 lines

---

### `theorem FormalGroupHom.coeff_one_id`

- **Type**: `(F : FormalGroup R) → PowerSeries.coeff 1 (FormalGroupHom.id F).toSeries = 1`
- **What**: The linear coefficient (coefficient of `T`) of the identity hom is `1`.
- **How**: `simp` — reduces via `id_toSeries` and `PowerSeries.coeff_one_X`.
- **Hypotheses**: none beyond `R` commutative ring.
- **Uses from project**: `FormalGroupHom.id_toSeries` (via simp)
- **Used by**: unused in file
- **Visibility**: public, tagged `@[simp]`
- **Lines**: 113–115, proof ~1 line
- **Notes**: Dead code within this file; likely intended for downstream consumers.

---

### `theorem FormalGroupHom.id_eq_mulByNatHom_one`

- **Type**: `(F : FormalGroup R) → FormalGroupHom.id F = F.mulByNatHom 1`
- **What**: The identity homomorphism coincides with `mulByNatHom F 1` (multiplication by 1).
- **How**: `ext` followed by `rw [FormalGroupHom.id_toSeries, FormalGroup.mulByNatHom_one_toSeries]`.
- **Hypotheses**: none beyond `R` commutative ring.
- **Uses from project**: `FormalGroupHom.id_toSeries`, `FormalGroup.mulByNatHom_one_toSeries` (from `MulByNat`)
- **Used by**: `FormalGroup.mulByNatHom_one_isIso`, `FormalGroup.mulByNatHom_one_exists_inverse`
- **Visibility**: public
- **Lines**: 118–121, proof ~3 lines

---

### `theorem PowerSeries_subst_MvSubst_eq`

- **Type**: `(A : σ → MvPowerSeries τ R) (hA : MvPowerSeries.HasSubst A) (B : MvPowerSeries σ R) (hB : constantCoeff B = 0) (g : PowerSeries R) → subst (MvPowerSeries.subst A B) g = MvPowerSeries.subst A (subst B g)`
- **What**: Commutativity of univariate substitution into a multivariate series: substituting `MvPowerSeries.subst A B` into a univariate `g` equals first computing `subst B g` (univariate in σ) and then applying `MvPowerSeries.subst A`.
- **How**: Unfolds `PowerSeries.subst_def` twice, converts the inner substitution to a `HasSubst` instance, then applies `MvPowerSeries.subst_comp_subst_apply`.
- **Hypotheses**: `A` must satisfy `MvPowerSeries.HasSubst A`; `B` must have zero constant coefficient.
- **Uses from project**: none (pure mathlib)
- **Used by**: `FormalGroupHom.comp` (3 times: steps 3, s=0 case, s=1 case)
- **Visibility**: public
- **Lines**: 131–140, proof ~9 lines

---

### `private lemma FormalGroupHom.hasSubst_pair_lift`

- **Type**: `(f : PowerSeries R) (hf : constantCoeff f = 0) → MvPowerSeries.HasSubst (![subst (X 0) f, subst (X 1) f] : Fin 2 → MvPowerSeries (Fin 2) R)`
- **What**: The pair `[f(X₀), f(X₁)]` (bivariate lift of `f`) satisfies `HasSubst`, given that `f` has zero constant coefficient.
- **How**: `MvPowerSeries.hasSubst_of_constantCoeff_zero` + `HasseWeil.FG.constantCoeff_univariate_subst` for each component.
- **Hypotheses**: `f` a power series with `constantCoeff f = 0`.
- **Uses from project**: `HasseWeil.FG.constantCoeff_univariate_subst`
- **Used by**: `FormalGroupHom.comp` (twice: for the `f` and `g` lifts)
- **Visibility**: private
- **Lines**: 154–165, proof ~11 lines

---

### `noncomputable def FormalGroupHom.comp`

- **Type**: `(g : FormalGroupHom G H') (f : FormalGroupHom F G) → FormalGroupHom F H'`
- **What**: Composition of formal group homomorphisms: `(g ∘ f)(T) = g(f(T))` as power series, i.e. `subst f.toSeries g.toSeries`.
- **How**: The `preserves_add` field is the substantial content. The proof proceeds in 6 steps: (1) apply `PowerSeries.subst_comp_subst_apply` to factor the LHS; (2) apply `f.preserves_add`; (3) commute univariate/multivariate substitutions via `PowerSeries_subst_MvSubst_eq`; (4) apply `g.preserves_add`; (5) apply `MvPowerSeries.subst_comp_subst_apply` to collapse double substitution; (6) show the resulting substitution functions agree componentwise via `HasseWeil.FG.subst_matrix_X0`/`X1` and `PowerSeries.subst_comp_subst_apply`. Key lemmas: `PowerSeries_subst_MvSubst_eq`, `MvPowerSeries.subst_comp_subst_apply`, `HasseWeil.FG.subst_matrix_X0`, `HasseWeil.FG.subst_matrix_X1`.
- **Hypotheses**: `R` a commutative ring; `f : F → G`, `g : G → H'` formal group homomorphisms.
- **Uses from project**: `PowerSeries_subst_MvSubst_eq`, `FormalGroupHom.hasSubst_pair_lift`, `HasseWeil.FG.constantCoeff_FG_toSeries`, `HasseWeil.FG.subst_matrix_X0`, `HasseWeil.FG.subst_matrix_X1`
- **Used by**: `FormalGroupHom.comp_toSeries`, `FormalGroupHom.id_comp`, `FormalGroupHom.comp_id`, `FormalGroup.mulByNatHom_one_isIso`, `FormalGroup.mulByNatHom_one_exists_inverse`
- **Visibility**: public
- **Lines**: 172–269, proof ~97 lines (the `preserves_add` field body is ~91 lines)
- **Notes**: **Proof >30 lines.** Largest proof in the file. The 6-step strategy is clearly documented in inline comments.

---

### `theorem FormalGroupHom.comp_toSeries`

- **Type**: `(g : FormalGroupHom G H') (f : FormalGroupHom F G) → (g.comp f).toSeries = PowerSeries.subst f.toSeries g.toSeries`
- **What**: The underlying series of the composite is the series composition.
- **How**: `rfl`.
- **Hypotheses**: none beyond the homomorphisms.
- **Uses from project**: `FormalGroupHom.comp` (definitionally)
- **Used by**: `FormalGroupHom.id_comp`, `FormalGroupHom.comp_id`
- **Visibility**: public, tagged `@[simp]`
- **Lines**: 273–275, proof 0 lines

---

### `theorem FormalGroupHom.id_comp`

- **Type**: `(f : FormalGroupHom F G) → (FormalGroupHom.id G).comp f = f`
- **What**: Left identity law for composition: `id ∘ f = f`.
- **How**: `FormalGroupHom.ext`, then rewrite via `comp_toSeries`, `id_toSeries`, and finally `MvPowerSeries.subst_X` (substituting `X` into a HasSubst system).
- **Hypotheses**: `f : F → G` a formal group homomorphism.
- **Uses from project**: `FormalGroupHom.ext`, `FormalGroupHom.comp_toSeries`, `FormalGroupHom.id_toSeries`
- **Used by**: `FormalGroup.mulByNatHom_one_isIso`, `FormalGroup.mulByNatHom_one_exists_inverse`
- **Visibility**: public, tagged `@[simp]`
- **Lines**: 279–290, proof ~11 lines

---

### `theorem FormalGroupHom.comp_id`

- **Type**: `(f : FormalGroupHom F G) → f.comp (FormalGroupHom.id F) = f`
- **What**: Right identity law for composition: `f ∘ id = f`.
- **How**: `FormalGroupHom.ext`, then `comp_toSeries`, `id_toSeries`, then uses `PowerSeries.subst_def` and `MvPowerSeries.subst_self` (substituting the identity variables is the identity on series).
- **Hypotheses**: `f : F → G` a formal group homomorphism.
- **Uses from project**: `FormalGroupHom.ext`, `FormalGroupHom.comp_toSeries`, `FormalGroupHom.id_toSeries`
- **Used by**: `FormalGroup.mulByNatHom_one_isIso`, `FormalGroup.mulByNatHom_one_exists_inverse`
- **Visibility**: public, tagged `@[simp]`
- **Lines**: 294–305, proof ~11 lines

---

### `theorem FormalGroup.mulByNatHom_one_isIso`

- **Type**: `(F : FormalGroup R) → (F.mulByNatHom 1).comp (FormalGroupHom.id F) = FormalGroupHom.id F ∧ (FormalGroupHom.id F).comp (F.mulByNatHom 1) = FormalGroupHom.id F`
- **What**: `mulByNatHom F 1` is an isomorphism of formal groups, with identity as both left and right inverse (Silverman IV.2.3(b), trivial case `n = 1`).
- **How**: Rewrites `mulByNatHom F 1 = id F` via `id_eq_mulByNatHom_one`, then applies `comp_id` and `id_comp`.
- **Hypotheses**: none beyond `R` commutative ring.
- **Uses from project**: `FormalGroupHom.id_eq_mulByNatHom_one`, `FormalGroupHom.comp_id`, `FormalGroupHom.id_comp`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 338–348, proof ~10 lines
- **Notes**: Dead code within this file; external consumers for the `n=1` isomorphism case.

---

### `theorem FormalGroup.mulByNatHom_one_exists_inverse`

- **Type**: `(F : FormalGroup R) → ∃ g : FormalGroupHom F F, g.comp (F.mulByNatHom 1) = FormalGroupHom.id F ∧ (F.mulByNatHom 1).comp g = FormalGroupHom.id F`
- **What**: Existence of a two-sided inverse to `mulByNatHom F 1` as a `FormalGroupHom` (the existence form of `mulByNatHom_one_isIso`, matching ticket T-IV-2-008 criteria for `n = 1`).
- **How**: Witnesses `g = FormalGroupHom.id F`, then uses `id_eq_mulByNatHom_one` + `id_comp`/`comp_id`.
- **Hypotheses**: none beyond `R` commutative ring.
- **Uses from project**: `FormalGroupHom.id`, `FormalGroupHom.id_eq_mulByNatHom_one`, `FormalGroupHom.id_comp`, `FormalGroupHom.comp_id`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 353–363, proof ~10 lines
- **Notes**: Dead code within this file.

---

### `theorem FormalGroup.mulByNatHom_hasInverse`

- **Type**: `(F : FormalGroup R) (n : ℕ) (hn : IsUnit ((n : ℕ) : R)) → ∃ g : PowerSeries R, subst g (F.mulByNatHom n).toSeries = X ∧ constantCoeff g = 0`
- **What**: For `n : ℕ` with `(n : R)` a unit, there exists a right compositional inverse (as a power series) for `mulByNatHom F n` at the series level; i.e., `[n] ∘ g = id`. This is the primary acceptance theorem for T-IV-2-008 (general unit case).
- **How**: Witnesses `compInverseOfUnit (F.mulByNatHom n).toSeries (n : R) hn`, applies `subst_compInverseOfUnit_eq_X` using `(F.mulByNatHom n).zero_const` and `FormalGroup.coeff_one_mulByNatHom`, and `compInverseOfUnit_constantCoeff`.
- **Hypotheses**: `(n : R)` is a unit in `R`.
- **Uses from project**: `FormalGroup.coeff_one_mulByNatHom` (from `MulByNat`); `compInverseOfUnit`, `subst_compInverseOfUnit_eq_X`, `compInverseOfUnit_constantCoeff` (from `Logarithm`)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 397–409, proof ~12 lines
- **Notes**: Dead code within this file. The module doc notes that packaging the inverse as a `FormalGroupHom` (needing `preserves_add`) is deferred.

---

### `theorem FormalGroup.mulByNatHom_hasInverse'`

- **Type**: `(F : FormalGroup R) (n : ℕ) (hn : IsUnit ((n : ℕ) : R)) → ∃ g : PowerSeries R, subst g (F.mulByNatHom n).toSeries = X ∧ constantCoeff g = 0 ∧ PowerSeries.HasSubst g`
- **What**: Enriched version of `mulByNatHom_hasInverse` that additionally asserts `HasSubst g`, making the inverse immediately substitutable.
- **How**: Same witness as `mulByNatHom_hasInverse`, adds `compInverseOfUnit_hasSubst` for the third conjunct.
- **Hypotheses**: `(n : R)` is a unit.
- **Uses from project**: `FormalGroup.coeff_one_mulByNatHom`; `compInverseOfUnit`, `subst_compInverseOfUnit_eq_X`, `compInverseOfUnit_constantCoeff`, `compInverseOfUnit_hasSubst` (from `Logarithm`)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 414–426, proof ~12 lines
- **Notes**: Dead code within this file; slight strengthening of `mulByNatHom_hasInverse`.

---

### `noncomputable def FormalGroup.mulByNatInvSeries`

- **Type**: `(F : FormalGroup R) (n : ℕ) (hn : IsUnit ((n : ℕ) : R)) → PowerSeries R`
- **What**: Named definition of the right compositional inverse of `mulByNatHom F n` as a bare power series; defined as `compInverseOfUnit (F.mulByNatHom n).toSeries (n : R) hn`.
- **How**: Direct definition (no proof).
- **Hypotheses**: `(n : R)` is a unit.
- **Uses from project**: `FormalGroup.mulByNatHom` (from `MulByNat`); `compInverseOfUnit` (from `Logarithm`)
- **Used by**: `FormalGroup.constantCoeff_mulByNatInvSeries`, `FormalGroup.mulByNatInvSeries_hasSubst`, `FormalGroup.subst_mulByNatInvSeries_mulByNatHom`, `FormalGroup.subst_mulByNatHom_mulByNatInvSeries`, `FormalGroup.subst_mulByNatHom_subst_mulByNatInvSeries`, `FormalGroup.mulByNatHom_subst_injective_of_unit`
- **Visibility**: public
- **Lines**: 438–440

---

### `theorem FormalGroup.constantCoeff_mulByNatInvSeries`

- **Type**: `(F : FormalGroup R) (n : ℕ) (hn : IsUnit ((n : ℕ) : R)) → constantCoeff (F.mulByNatInvSeries n hn) = 0`
- **What**: The constant coefficient of `mulByNatInvSeries` is zero (the inverse fixes 0).
- **How**: Unfolds definition and applies `compInverseOfUnit_constantCoeff`.
- **Hypotheses**: `(n : R)` is a unit.
- **Uses from project**: `FormalGroup.mulByNatInvSeries`; `compInverseOfUnit_constantCoeff` (from `Logarithm`)
- **Used by**: `FormalGroup.subst_mulByNatHom_mulByNatInvSeries`, `FormalGroup.mulByNatHom_subst_injective_of_unit`
- **Visibility**: public, tagged `@[simp]`
- **Lines**: 444–447, proof 0 lines (direct term)

---

### `theorem FormalGroup.mulByNatInvSeries_hasSubst`

- **Type**: `(F : FormalGroup R) (n : ℕ) (hn : IsUnit ((n : ℕ) : R)) → PowerSeries.HasSubst (F.mulByNatInvSeries n hn)`
- **What**: `mulByNatInvSeries` can be substituted into power series (its constant coefficient is 0, witnessed by `HasSubst`).
- **How**: Unfolds and applies `compInverseOfUnit_hasSubst`.
- **Hypotheses**: `(n : R)` is a unit.
- **Uses from project**: `FormalGroup.mulByNatInvSeries`; `compInverseOfUnit_hasSubst` (from `Logarithm`)
- **Used by**: `FormalGroup.subst_mulByNatHom_mulByNatInvSeries`
- **Visibility**: public
- **Lines**: 450–453, proof 0 lines (direct term)

---

### `theorem FormalGroup.subst_mulByNatInvSeries_mulByNatHom`

- **Type**: `(F : FormalGroup R) (n : ℕ) (hn : IsUnit ((n : ℕ) : R)) → subst (F.mulByNatInvSeries n hn) (F.mulByNatHom n).toSeries = X`
- **What**: Right inverse identity: `[n] ∘ g = id` at the series level (composing `mulByNatHom n` after the inverse gives `X`).
- **How**: Unfolds `mulByNatInvSeries` and applies `subst_compInverseOfUnit_eq_X` with `(F.mulByNatHom n).zero_const` and `FormalGroup.coeff_one_mulByNatHom`.
- **Hypotheses**: `(n : R)` is a unit.
- **Uses from project**: `FormalGroup.mulByNatInvSeries`; `subst_compInverseOfUnit_eq_X`, `FormalGroup.coeff_one_mulByNatHom`
- **Used by**: `FormalGroup.subst_mulByNatHom_mulByNatInvSeries`
- **Visibility**: public
- **Lines**: 458–465, proof ~7 lines

---

### `private theorem subst_X_eq_self`

- **Type**: `(f : PowerSeries R) → subst X f = f`
- **What**: Substituting `X` (the identity series) for the variable of `f` returns `f` unchanged.
- **How**: `PowerSeries.subst_def` reduces to `MvPowerSeries.subst`, then `MvPowerSeries.subst_self`.
- **Hypotheses**: none.
- **Uses from project**: none (pure mathlib)
- **Used by**: `FormalGroup.subst_mulByNatHom_mulByNatInvSeries` (L538)
- **Visibility**: private
- **Lines**: 470–477, proof ~7 lines
- **Notes**: This is essentially `PowerSeries.subst_X_eq_self` — may have a mathlib analogue; used as a bootstrap helper.

---

### `theorem FormalGroup.subst_mulByNatHom_mulByNatInvSeries`

- **Type**: `(F : FormalGroup R) {n : ℕ} (hn : IsUnit ((n : ℕ) : R)) → subst (F.mulByNatHom n).toSeries (F.mulByNatInvSeries n hn) = X`
- **What**: Left inverse identity: `g ∘ [n] = id` at the series level (composing the inverse after `mulByNatHom n` gives `X`). Together with the right inverse, this shows `mulByNatHom F n` and `mulByNatInvSeries F n hn` are mutual compositional inverses.
- **How**: Bootstrap argument: set `f = [n].toSeries`, `g = mulByNatInvSeries`, compute `coeff 1 g = n⁻¹` (via `compInverseOfUnit_coeff_one`), construct `h = compInverseOfUnit g n⁻¹` (right inverse of `g`), apply `PowerSeries.subst_comp_subst_apply` associativity to get `h = f` from the equations `subst g f = X` and `subst h g = X`, then conclude `subst f g = subst h g = X`.
- **Hypotheses**: `(n : R)` is a unit.
- **Uses from project**: `FormalGroup.mulByNatInvSeries`, `FormalGroup.constantCoeff_mulByNatInvSeries`, `FormalGroup.mulByNatInvSeries_hasSubst`, `FormalGroup.subst_mulByNatInvSeries_mulByNatHom`; `compInverseOfUnit_coeff_one`, `compInverseOfUnit_hasSubst`, `subst_compInverseOfUnit_eq_X` (from `Logarithm`); `subst_X_eq_self` (private)
- **Used by**: `FormalGroup.subst_mulByNatHom_subst_mulByNatInvSeries`
- **Visibility**: public
- **Lines**: 497–542, proof ~45 lines
- **Notes**: **Proof >30 lines.** The bootstrap approach (constructing a second inverse to prove left-inverse from right-inverse) is mathematically interesting: it exploits the fact that `compInverseOfUnit` can be applied to any unit-leading-coefficient series.

---

### `theorem FormalGroup.subst_mulByNatHom_subst_mulByNatInvSeries`

- **Type**: `(F : FormalGroup R) {n : ℕ} (hn : IsUnit ((n : ℕ) : R)) (x : PowerSeries R) (hx : PowerSeries.HasSubst x) → subst (subst x (F.mulByNatHom n).toSeries) (F.mulByNatInvSeries n hn) = x`
- **What**: Recovery formula: applying `[n]` and then the inverse recovers any substitutable series `x`. Equivalently, `g ∘ [n] = id` applied to an arbitrary element.
- **How**: Uses associativity `subst_comp_subst_apply` and the left-inverse identity `subst_mulByNatHom_mulByNatInvSeries` and `PowerSeries.subst_X`.
- **Hypotheses**: `(n : R)` a unit; `x` a power series with `HasSubst x`.
- **Uses from project**: `FormalGroup.mulByNatInvSeries`, `FormalGroup.subst_mulByNatHom_mulByNatInvSeries`
- **Used by**: `FormalGroup.mulByNatHom_subst_injective_of_unit`
- **Visibility**: public
- **Lines**: 550–567, proof ~17 lines

---

### `theorem FormalGroup.mulByNatHom_subst_injective_of_unit`

- **Type**: `(F : FormalGroup R) {n : ℕ} (hn : IsUnit ((n : ℕ) : R)) {x : PowerSeries R} (hx : PowerSeries.HasSubst x) → subst x (F.mulByNatHom n).toSeries = 0 → x = 0`
- **What**: Series-level injectivity of `[n]` when `(n : R)` is a unit: if `x` composed with `[n]` is the zero series, then `x` is zero. This is the series form of the statement "`[n]` is injective on `F(M)`" (required by T-IV-3-007).
- **How**: Applies `subst_mulByNatHom_subst_mulByNatInvSeries` to get `subst 0 inv = x`, then computes `subst 0 g = 0` term-by-term using `PowerSeries.coeff_subst'` and `finsum_eq_zero_of_forall_eq_zero`: each term is zero because either `d = 0` (zero constant coefficient of `mulByNatInvSeries`) or `d ≠ 0` (zero series has zero powers).
- **Hypotheses**: `(n : R)` a unit; `x` substitutable power series; `subst x [n].toSeries = 0`.
- **Uses from project**: `FormalGroup.mulByNatInvSeries`, `FormalGroup.constantCoeff_mulByNatInvSeries`, `FormalGroup.subst_mulByNatHom_subst_mulByNatInvSeries`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 577–608, proof ~31 lines
- **Notes**: **Proof >30 lines.** Terminal result (dead code within this file); the downstream consumer is T-IV-3-007.

---

## Cross-reference summary

| Declaration | Used by (in file) |
|---|---|
| `FormalGroupHom.ext` | `id_comp`, `comp_id` |
| `FormalGroupHom.id` | `id_toSeries`, `coeff_one_id`, `id_eq_mulByNatHom_one`, `id_comp`, `comp_id`, `mulByNatHom_one_isIso`, `mulByNatHom_one_exists_inverse` |
| `FormalGroupHom.id_toSeries` | `coeff_one_id`, `id_eq_mulByNatHom_one`, `id_comp`, `comp_id` |
| `FormalGroupHom.id_eq_mulByNatHom_one` | `mulByNatHom_one_isIso`, `mulByNatHom_one_exists_inverse` |
| `PowerSeries_subst_MvSubst_eq` | `FormalGroupHom.comp` (3×) |
| `FormalGroupHom.hasSubst_pair_lift` (private) | `FormalGroupHom.comp` (2×) |
| `FormalGroupHom.comp` | `comp_toSeries`, `id_comp`, `comp_id`, `mulByNatHom_one_isIso`, `mulByNatHom_one_exists_inverse` |
| `FormalGroupHom.comp_toSeries` | `id_comp`, `comp_id` |
| `FormalGroupHom.id_comp` | `mulByNatHom_one_isIso`, `mulByNatHom_one_exists_inverse` |
| `FormalGroupHom.comp_id` | `mulByNatHom_one_isIso`, `mulByNatHom_one_exists_inverse` |
| `FormalGroup.mulByNatInvSeries` | `constantCoeff_mulByNatInvSeries`, `mulByNatInvSeries_hasSubst`, `subst_mulByNatInvSeries_mulByNatHom`, `subst_mulByNatHom_mulByNatInvSeries`, `subst_mulByNatHom_subst_mulByNatInvSeries`, `mulByNatHom_subst_injective_of_unit` |
| `constantCoeff_mulByNatInvSeries` | `subst_mulByNatHom_mulByNatInvSeries`, `mulByNatHom_subst_injective_of_unit` |
| `mulByNatInvSeries_hasSubst` | `subst_mulByNatHom_mulByNatInvSeries` |
| `subst_mulByNatInvSeries_mulByNatHom` | `subst_mulByNatHom_mulByNatInvSeries` |
| `subst_X_eq_self` (private) | `subst_mulByNatHom_mulByNatInvSeries` |
| `subst_mulByNatHom_mulByNatInvSeries` | `subst_mulByNatHom_subst_mulByNatInvSeries` |
| `subst_mulByNatHom_subst_mulByNatInvSeries` | `mulByNatHom_subst_injective_of_unit` |

## Unused within this file (dead-code candidates)

- `FormalGroupHom.coeff_one_id`
- `FormalGroup.mulByNatHom_one_isIso`
- `FormalGroup.mulByNatHom_one_exists_inverse`
- `FormalGroup.mulByNatHom_hasInverse`
- `FormalGroup.mulByNatHom_hasInverse'`
- `FormalGroup.mulByNatHom_subst_injective_of_unit`

(These are all clearly designed as API for external consumers, not internal helpers.)
