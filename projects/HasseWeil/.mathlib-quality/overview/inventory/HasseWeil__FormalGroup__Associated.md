# Inventory: ./HasseWeil/FormalGroup/Associated.lean

**File summary**: 922 lines. Formalises Silverman IV.3.1 (`Ĝ_a`, `Ĝ_m`) and IV.3.2(a)/(b): operation identities for the additive/multiplicative formal groups, the decreasing filtration `F(Mⁿ)`, the graded-isomorphism congruence `F(x,y) ≡ x+y (mod Mⁿ⁺¹)`, the graded map `F(Mⁿ) →+ R/Mⁿ⁺¹`, the `nsmul`/formal-`[n]` bridge, injectivity of `[n]` when `n` is a unit, torsion p-power theorem (IV.3.2(b)/IV.6.1), and the `Ĝ_m(M) ≃* (1+M)ˣ` multiplicative equivalence.

---

## Declarations

### `theorem evalAdd_additiveFormalGroup`
- **Type**: `(x y : maximalIdeal R) → (additiveFormalGroup R).evalAdd x y = x.1 + y.1`
- **What**: The formal-group operation on `Ĝ_a` is ordinary ring addition.
- **How**: Reduces `evalAdd` (which is `MvPowerSeries.eval₂`) to an `MvPolynomial` evaluation via `MvPowerSeries.eval₂_coe`, then uses `MvPolynomial.eval₂_add`/`eval₂_X`.
- **Hypotheses**: `R` a commutative local ring with uniform space structure; `x, y ∈ maximalIdeal R`.
- **Uses from project**: `additiveFormalGroup`
- **Used by**: `evalNeg_additiveFormalGroup`, `evalAdd_sub_add_mem_pow_succ` (via `HasseWeil.FG.FormalGroup.coeff_10`/`coeff_01` path)
- **Visibility**: public
- **Lines**: 58–70; proof ~12 lines
- **Notes**: No `sorry`, no `set_option maxHeartbeats`.

---

### `theorem evalAdd_multiplicativeFormalGroup`
- **Type**: `(x y : maximalIdeal R) → (multiplicativeFormalGroup R).evalAdd x y = x.1 + y.1 + x.1 * y.1`
- **What**: The formal-group operation on `Ĝ_m` evaluates to `x + y + xy`.
- **How**: Same `eval₂_coe`/`MvPolynomial.eval₂_add`/`eval₂_mul`/`eval₂_X` pattern; uses the definition of `multiplicativeFormalGroup` as `F(X,Y) = X + Y + XY`.
- **Hypotheses**: `R` a commutative local ring with uniform space.
- **Uses from project**: `multiplicativeFormalGroup`
- **Used by**: `evalAdd_multiplicativeFormalGroup_one_add`, `multiplicativeFormalGroup_EvalGroup_mulEquiv`
- **Visibility**: public
- **Lines**: 77–91; proof ~14 lines
- **Notes**: No `sorry`.

---

### `theorem evalAdd_multiplicativeFormalGroup_one_add`
- **Type**: `(x y : maximalIdeal R) → 1 + (multiplicativeFormalGroup R).evalAdd x y = (1 + x.1) * (1 + y.1)`
- **What**: The bijection `x ↦ 1+x` intertwines the `Ĝ_m` operation with ring multiplication.
- **How**: Rewrites via `evalAdd_multiplicativeFormalGroup`, then `ring`.
- **Hypotheses**: `R` local ring with uniform space.
- **Uses from project**: `evalAdd_multiplicativeFormalGroup`
- **Used by**: `multiplicativeFormalGroup_EvalGroup_mulEquiv`
- **Visibility**: public
- **Lines**: 98–102; proof ~4 lines
- **Notes**: No `sorry`.

---

### `theorem evalNeg_additiveFormalGroup`
- **Type**: `(hAdic : IsAdic (maximalIdeal R)) → (x : maximalIdeal R) → (additiveFormalGroup R).evalNeg x = -x.1`
- **What**: The formal-group negation on `Ĝ_a` is ordinary ring negation.
- **How**: Applies `FormalGroup.evalAdd_evalNeg` (the inverse axiom), rewrites with `evalAdd_additiveFormalGroup`, and concludes by `eq_neg_of_add_eq_zero_right`.
- **Hypotheses**: Complete local ring with adic topology; `x ∈ maximalIdeal R`.
- **Uses from project**: `additiveFormalGroup`, `evalAdd_additiveFormalGroup`, `FormalGroup.evalNeg_mem`, `FormalGroup.evalAdd_evalNeg`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 119–127; proof ~8 lines
- **Notes**: No `sorry`. The declaration is not referenced within this file; it is public API for downstream callers.

---

### `lemma maximalIdeal_pow_isClosed`
- **Type**: `(hAdic : IsAdic (maximalIdeal R)) → (n : ℕ) → IsClosed (((maximalIdeal R)^n : Ideal R) : Set R)`
- **What**: Each power of the maximal ideal is a closed subset under the adic topology (it is a basic open neighbourhood of 0, hence also closed in a T1 space).
- **How**: Uses `isAdic_iff.mp` to extract the open-neighbourhood property, then `AddSubgroup.isClosed_of_isOpen`.
- **Hypotheses**: `R` a uniform topological ring with adic topology; `n : ℕ`.
- **Uses from project**: (none — uses only mathlib)
- **Used by**: `FormalGroup.evalAdd_pow_mem`, `FormalGroup.evalNeg_pow_mem`, `FormalGroup.evalAdd_sub_add_mem_pow_succ` (via `mem_of_tendsto`)
- **Visibility**: public (but `omit [...]` omits some typeclasses)
- **Lines**: 144–152; proof ~8 lines
- **Notes**: No `sorry`. Decorated with `omit` to drop unneeded topology instances.

---

### `theorem FormalGroup.evalAdd_pow_mem`
- **Type**: `(hAdic : IsAdic (maximalIdeal R)) → (F : FormalGroup R) → (n : ℕ) → {x y : maximalIdeal R} → x.1 ∈ (maximalIdeal R)^n → y.1 ∈ (maximalIdeal R)^n → F.evalAdd x y ∈ (maximalIdeal R)^n`
- **What**: `F(Mⁿ)` is closed under the formal-group addition: if `x, y ∈ Mⁿ` then `F(x,y) ∈ Mⁿ`.
- **How**: Unfolds `evalAdd` as a `hasSum` via `MvPowerSeries.hasSum_eval₂`. For each monomial index `d`, the `d=0` term is zero by `HasseWeil.FG.constantCoeff_FG_toSeries`; the `d≠0` term has a factor in `Mⁿ` from `x` or `y`, so the product is in `Mⁿ` by `Ideal.pow_mem_of_mem`. Membership of the limit uses `maximalIdeal_pow_isClosed` + `IsClosed.mem_of_tendsto`.
- **Hypotheses**: Complete local ring with adic topology; `x.1, y.1 ∈ Mⁿ`.
- **Uses from project**: `hasEval_of_mem_maximalIdeal`, `maximalIdeal_pow_isClosed`, `HasseWeil.FG.constantCoeff_FG_toSeries`
- **Used by**: `FormalGroup.evalGroup_powerIdeal`
- **Visibility**: public
- **Lines**: 162–198; proof ~36 lines
- **Notes**: Proof >30 lines. No `sorry`.

---

### `theorem FormalGroup.evalNeg_pow_mem`
- **Type**: `(hAdic : IsAdic (maximalIdeal R)) → (F : FormalGroup R) → (n : ℕ) → {x : maximalIdeal R} → x.1 ∈ (maximalIdeal R)^n → F.evalNeg x ∈ (maximalIdeal R)^n`
- **What**: `F(Mⁿ)` is closed under formal-group negation.
- **How**: Same `hasSum_eval₂` / `IsClosed.mem_of_tendsto` strategy for `PowerSeries.eval₂`; `k=0` term is zero by `FormalGroup.inverse_coeff_zero`; `k≥1` term has `x.1^k ∈ Mⁿ` by `Ideal.pow_mem_of_mem`. Uses `isTopologicallyNilpotent_of_mem_maximalIdeal` for `HasEval`.
- **Hypotheses**: Complete local ring with adic topology; `x.1 ∈ Mⁿ`.
- **Uses from project**: `isTopologicallyNilpotent_of_mem_maximalIdeal`, `maximalIdeal_pow_isClosed`, `FormalGroup.inverse_coeff_zero`
- **Used by**: `FormalGroup.evalGroup_powerIdeal`, `FormalGroup.evalNeg_add_mem_pow_succ`
- **Visibility**: public
- **Lines**: 206–227; proof ~21 lines
- **Notes**: No `sorry`.

---

### `noncomputable def FormalGroup.evalGroup_powerIdeal`
- **Type**: `(F : FormalGroup R) → (hAdic : IsAdic (maximalIdeal R)) → (n : ℕ) → AddSubgroup (F.EvalGroup hAdic)`
- **What**: The subgroup `F(Mⁿ)` of `F(M)`, yielding the decreasing filtration `F(M) ⊇ F(M²) ⊇ …`.
- **How**: Constructs the `AddSubgroup` record with `zero_mem` (trivial), `add_mem` via `evalAdd_pow_mem`, and `neg_mem` via `evalNeg_pow_mem`.
- **Hypotheses**: Complete local ring with adic topology; `n : ℕ`.
- **Uses from project**: `FormalGroup.evalAdd_pow_mem`, `FormalGroup.evalNeg_pow_mem`
- **Used by**: `FormalGroup.evalGroup_powerIdeal_mono`, `FormalGroup.evalGroup_powerIdeal_toQuot`, `FormalGroup.evalGroup_powerIdeal_toQuot_ker`, `FormalGroup.evalGroup_powerIdeal_toQuot_range`, `FormalGroup.evalGroup_powerIdeal_quotKerEquivRange`
- **Visibility**: public
- **Lines**: 234–242; body ~8 lines
- **Notes**: No `sorry`. Key filtration definition; heavily referenced within file.

---

### `theorem FormalGroup.evalGroup_powerIdeal_mono`
- **Type**: `(F : FormalGroup R) → (hAdic : IsAdic (maximalIdeal R)) → {m n : ℕ} → m ≤ n → F.evalGroup_powerIdeal hAdic n ≤ F.evalGroup_powerIdeal hAdic m`
- **What**: The filtration is monotone: `Mⁿ ⊆ Mᵐ` for `m ≤ n` pulls back to `F(Mⁿ) ≤ F(Mᵐ)`.
- **How**: Direct from `Ideal.pow_le_pow_right`.
- **Hypotheses**: Complete local ring; `m ≤ n`.
- **Uses from project**: `FormalGroup.evalGroup_powerIdeal`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 245–249; proof ~4 lines
- **Notes**: No `sorry`. Unused within this file; public API.

---

### `theorem FormalGroup.EvalGroup.nsmul_val`
- **Type**: `(F : FormalGroup R) → (hAdic : IsAdic (maximalIdeal R)) → (n : ℕ) → (x : F.EvalGroup hAdic) → (n • x).val.1 = PowerSeries.eval₂ (RingHom.id R) x.val.1 (F.mulByNatHom n).toSeries`
- **What**: The `AddGroup` scalar action `n • x` at the underlying ring element equals evaluation of the formal multiplication-by-`n` series `[n](T)` at `x.val.1`.
- **How**: Induction on `n`. Base: uses `FormalGroup.mulByNatHom_zero_toSeries` and `PowerSeries.eval₂_coe`. Step: uses `FormalGroup.EvalGroup.val_add`, `FormalGroup.mulByNatHom_toSeries`, and the substitution bridge `eval₂_subst_bridge` with `HasseWeil.FG.mulByNatSeries`/`fAdd`; relies on `HasseWeil.FG.constantCoeff_mulByNatSeries`.
- **Hypotheses**: Complete local ring with adic topology.
- **Uses from project**: `FormalGroup.mulByNatHom_zero_toSeries`, `FormalGroup.EvalGroup.val_add`, `FormalGroup.mulByNatHom_toSeries`, `eval₂_subst_bridge`, `HasseWeil.FG.mulByNatSeries`, `HasseWeil.FG.fAdd`, `HasseWeil.FG.constantCoeff_mulByNatSeries`
- **Used by**: `FormalGroup.EvalGroup.nsmul_injective_of_unit`
- **Visibility**: public
- **Lines**: 261–341; proof ~80 lines
- **Notes**: Proof >30 lines. No `sorry`. Most complex proof in the file; uses the MvPowerSeries substitution bridge.

---

### `private noncomputable def lowDegFinset`
- **Type**: `Finset (Fin 2 →₀ ℕ)`
- **What**: The three "low-degree" monomial indices `{0, single 0 1, single 1 1}` used to separate the linear part of `F(x,y)` from higher-order terms.
- **How**: Literal definition.
- **Hypotheses**: None.
- **Uses from project**: (none)
- **Used by**: `lowDegFinset_mem_iff`, `two_le_sum_of_not_mem_lowDeg`, `FormalGroup.evalAdd_sub_add_mem_pow_succ`
- **Visibility**: private
- **Lines**: 357–358; body 1 line
- **Notes**: No `sorry`. Auxiliary for the graded-congruence proof.

---

### `private lemma lowDegFinset_mem_iff`
- **Type**: `(d : Fin 2 →₀ ℕ) → d ∈ lowDegFinset ↔ d = 0 ∨ d = Finsupp.single 0 1 ∨ d = Finsupp.single 1 1`
- **What**: Membership characterisation of `lowDegFinset`.
- **How**: `unfold`, `simp`.
- **Hypotheses**: None.
- **Uses from project**: `lowDegFinset`
- **Used by**: `two_le_sum_of_not_mem_lowDeg`
- **Visibility**: private
- **Lines**: 361–365; proof ~4 lines
- **Notes**: No `sorry`.

---

### `private lemma single_zero_one_ne_zero`
- **Type**: `(Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ 0`
- **What**: Distinctness of `single 0 1` from the zero finsupp.
- **How**: `DFunLike.congr_fun` at index 0, `simp`.
- **Hypotheses**: None.
- **Uses from project**: (none)
- **Used by**: `FormalGroup.evalAdd_sub_add_mem_pow_succ`
- **Visibility**: private
- **Lines**: 367–371; proof ~4 lines
- **Notes**: No `sorry`. Small distinctness helper.

---

### `private lemma single_one_one_ne_zero`
- **Type**: `(Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ 0`
- **What**: Distinctness of `single 1 1` from the zero finsupp.
- **How**: `DFunLike.congr_fun` at index 1, `simp`.
- **Hypotheses**: None.
- **Uses from project**: (none)
- **Used by**: `FormalGroup.evalAdd_sub_add_mem_pow_succ` (implicitly via `lowDegFinset`)
- **Visibility**: private
- **Lines**: 373–377; proof ~4 lines
- **Notes**: No `sorry`.

---

### `private lemma single_zero_ne_single_one`
- **Type**: `(Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1`
- **What**: Distinctness of `single 0 1` and `single 1 1`.
- **How**: `DFunLike.congr_fun` at index 0, `simp`.
- **Hypotheses**: None.
- **Uses from project**: (none)
- **Used by**: `FormalGroup.evalAdd_sub_add_mem_pow_succ`
- **Visibility**: private
- **Lines**: 379–383; proof ~4 lines
- **Notes**: No `sorry`.

---

### `private lemma two_le_sum_of_not_mem_lowDeg`
- **Type**: `{d : Fin 2 →₀ ℕ} → d ∉ lowDegFinset → 2 ≤ d 0 + d 1`
- **What**: If a monomial index is not in `lowDegFinset`, its total degree is at least 2.
- **How**: Contradiction — if `d 0 + d 1 < 2` then `d ∈ lowDegFinset`, established by case analysis using `lowDegFinset_mem_iff`.
- **Hypotheses**: None.
- **Uses from project**: `lowDegFinset`, `lowDegFinset_mem_iff`
- **Used by**: `FormalGroup.evalAdd_sub_add_mem_pow_succ`
- **Visibility**: private
- **Lines**: 386–405; proof ~19 lines
- **Notes**: No `sorry`.

---

### `theorem FormalGroup.evalAdd_sub_add_mem_pow_succ`
- **Type**: `(hAdic : IsAdic (maximalIdeal R)) → (F : FormalGroup R) → {n : ℕ} → 1 ≤ n → {x y : maximalIdeal R} → x.1 ∈ (maximalIdeal R)^n → y.1 ∈ (maximalIdeal R)^n → F.evalAdd x y - (x.1 + y.1) ∈ (maximalIdeal R)^(n+1)`
- **What**: The key congruence underlying the graded isomorphism (Silverman IV.3.2(a)): `F(x,y) ≡ x+y (mod Mⁿ⁺¹)` for `x, y ∈ Mⁿ`.
- **How**: Expands `evalAdd` as a `hasSum` (via `MvPowerSeries.hasSum_eval₂`), separates the sum over `lowDegFinset` (which equals `x+y` using `HasseWeil.FG.constantCoeff_FG_toSeries`, `HasseWeil.FG.FormalGroup.coeff_10`, `HasseWeil.FG.FormalGroup.coeff_01`), and shows the tail lies in `Mⁿ⁺¹` by `two_le_sum_of_not_mem_lowDeg` combined with `Ideal.pow_mem_pow` and `Ideal.pow_le_pow_right`. The limit argument uses `maximalIdeal_pow_isClosed` + `IsClosed.mem_of_tendsto`.
- **Hypotheses**: Complete local ring with adic topology; `n ≥ 1`; `x.1, y.1 ∈ Mⁿ`.
- **Uses from project**: `hasEval_of_mem_maximalIdeal`, `maximalIdeal_pow_isClosed`, `HasseWeil.FG.constantCoeff_FG_toSeries`, `HasseWeil.FG.FormalGroup.coeff_10`, `HasseWeil.FG.FormalGroup.coeff_01`, `lowDegFinset`, `single_zero_one_ne_zero`, `single_zero_ne_single_one`, `two_le_sum_of_not_mem_lowDeg`
- **Used by**: `FormalGroup.evalNeg_add_mem_pow_succ`, `FormalGroup.evalGroup_powerIdeal_toQuot`
- **Visibility**: public
- **Lines**: 422–507; proof ~85 lines
- **Notes**: Proof >30 lines. No `sorry`. The main analytical result of the file.

---

### `theorem FormalGroup.evalNeg_add_mem_pow_succ`
- **Type**: `(hAdic : IsAdic (maximalIdeal R)) → (F : FormalGroup R) → {n : ℕ} → 1 ≤ n → {x : maximalIdeal R} → x.1 ∈ (maximalIdeal R)^n → F.evalNeg x + x.1 ∈ (maximalIdeal R)^(n+1)`
- **What**: The negation analogue of the graded congruence: `−_F x ≡ −x (mod Mⁿ⁺¹)`, i.e., `F.evalNeg x + x ∈ Mⁿ⁺¹`.
- **How**: Applies `evalAdd_sub_add_mem_pow_succ` with `u = x`, `v = F.evalNeg x` (which is in `Mⁿ` by `FormalGroup.evalNeg_pow_mem`), using the inverse axiom `F.evalAdd_evalNeg`.
- **Hypotheses**: Complete local ring with adic topology; `n ≥ 1`; `x.1 ∈ Mⁿ`.
- **Uses from project**: `FormalGroup.evalNeg_pow_mem`, `FormalGroup.evalAdd_sub_add_mem_pow_succ`, `FormalGroup.evalAdd_evalNeg`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 519–537; proof ~18 lines
- **Notes**: No `sorry`. Public API; unused within this file.

---

### `noncomputable def FormalGroup.evalGroup_powerIdeal_toQuot`
- **Type**: `(F : FormalGroup R) → (hAdic : IsAdic (maximalIdeal R)) → {n : ℕ} → 1 ≤ n → F.evalGroup_powerIdeal hAdic n →+ R ⧸ ((maximalIdeal R)^(n+1))`
- **What**: The forward map of the graded isomorphism (IV.3.2(a)): sends `⟨x, hx⟩ ↦ [x.1]` in `R/Mⁿ⁺¹`, a group homomorphism by the congruence `F(x,y) ≡ x+y (mod Mⁿ⁺¹)`.
- **How**: Constructs the `AddMonoidHom` record; `map_add'` uses `evalAdd_sub_add_mem_pow_succ` via `Ideal.Quotient.eq.mpr`.
- **Hypotheses**: Complete local ring with adic topology; `n ≥ 1`.
- **Uses from project**: `FormalGroup.evalGroup_powerIdeal`, `FormalGroup.evalAdd_sub_add_mem_pow_succ`
- **Used by**: `FormalGroup.evalGroup_powerIdeal_toQuot_ker`, `FormalGroup.evalGroup_powerIdeal_toQuot_range`, `FormalGroup.evalGroup_powerIdeal_quotKerEquivRange`
- **Visibility**: public
- **Lines**: 549–561; body ~12 lines
- **Notes**: No `sorry`.

---

### `theorem FormalGroup.evalGroup_powerIdeal_toQuot_ker`
- **Type**: `(F : FormalGroup R) → (hAdic : IsAdic (maximalIdeal R)) → {n : ℕ} → 1 ≤ n → (F.evalGroup_powerIdeal_toQuot hAdic hn).ker = (F.evalGroup_powerIdeal hAdic (n+1)).addSubgroupOf (F.evalGroup_powerIdeal hAdic n)`
- **What**: The kernel of the graded map is `F(Mⁿ⁺¹)` embedded in `F(Mⁿ)`.
- **How**: `iff` by `Ideal.Quotient.eq_zero_iff_mem` in both directions.
- **Hypotheses**: Complete local ring; `n ≥ 1`.
- **Uses from project**: `FormalGroup.evalGroup_powerIdeal_toQuot`, `FormalGroup.evalGroup_powerIdeal`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 565–579; proof ~14 lines
- **Notes**: No `sorry`. Public API; unused within this file.

---

### `theorem FormalGroup.evalGroup_powerIdeal_toQuot_range`
- **Type**: `(F : FormalGroup R) → (hAdic : IsAdic (maximalIdeal R)) → {n : ℕ} → 1 ≤ n → (F.evalGroup_powerIdeal_toQuot hAdic hn).range = (Ideal.map (Ideal.Quotient.mk ((maximalIdeal R)^(n+1))) ((maximalIdeal R)^n)).toAddSubgroup`
- **What**: The image of the graded map is `Mⁿ/Mⁿ⁺¹` realised inside `R/Mⁿ⁺¹`.
- **How**: Forward via `Ideal.mem_map_of_mem`; backward via `Ideal.mem_map_iff_of_surjective` + `Ideal.Quotient.mk_surjective`.
- **Hypotheses**: Complete local ring; `n ≥ 1`.
- **Uses from project**: `FormalGroup.evalGroup_powerIdeal_toQuot`, `FormalGroup.evalGroup_powerIdeal`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 583–596; proof ~13 lines
- **Notes**: No `sorry`. Public API; unused within this file.

---

### `noncomputable def FormalGroup.evalGroup_powerIdeal_quotKerEquivRange`
- **Type**: `(F : FormalGroup R) → (hAdic : IsAdic (maximalIdeal R)) → {n : ℕ} → 1 ≤ n → (F.evalGroup_powerIdeal hAdic n ⧸ (F.evalGroup_powerIdeal_toQuot hAdic hn).ker) ≃+ (F.evalGroup_powerIdeal_toQuot hAdic hn).range`
- **What**: The first isomorphism theorem applied to `evalGroup_powerIdeal_toQuot`, giving `F(Mⁿ)/ker ≃+ range`.
- **How**: One-liner: `QuotientAddGroup.quotientKerEquivRange`.
- **Hypotheses**: Complete local ring; `n ≥ 1`.
- **Uses from project**: `FormalGroup.evalGroup_powerIdeal`, `FormalGroup.evalGroup_powerIdeal_toQuot`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 605–609; body ~4 lines
- **Notes**: No `sorry`. Public API; unused within this file.

---

### `private theorem FormalGroup.eval₂_zero_of_constantCoeff_zero`
- **Type**: `(hAdic : IsAdic (maximalIdeal R)) → {f : PowerSeries R} → PowerSeries.constantCoeff R f = 0 → PowerSeries.eval₂ (RingHom.id R) (0 : R) f = 0`
- **What**: Evaluation of a power series with zero constant term at `0 ∈ R` gives `0`.
- **How**: Obtains `HasEval 0` from `isTopologicallyNilpotent_of_mem_maximalIdeal`, then shows every term `coeff_d * 0^d` is zero (by `hf` for `d=0`, by `zero_pow` for `d≥1`); uses `HasSum.unique`.
- **Hypotheses**: Complete local ring with adic topology; `f` has zero constant term.
- **Uses from project**: `isTopologicallyNilpotent_of_mem_maximalIdeal`
- **Used by**: `FormalGroup.eval_mulByNatHom_injective_of_unit`
- **Visibility**: private
- **Lines**: 633–656; proof ~23 lines
- **Notes**: No `sorry`. Helper for the injectivity argument.

---

### `theorem FormalGroup.eval_mulByNatHom_injective_of_unit`
- **Type**: `(F : FormalGroup R) → (hAdic : IsAdic (maximalIdeal R)) → {n : ℕ} → IsUnit ((n : ℕ) : R) → {a : maximalIdeal R} → PowerSeries.eval₂ (RingHom.id R) a.1 (F.mulByNatHom n).toSeries = 0 → a.1 = 0`
- **What**: If `(n : R)` is a unit, then evaluation of `[n](T)` at `a ∈ M` being zero forces `a = 0` (injectivity of the multiplication-by-`n` series at the evaluation level).
- **How**: Uses the series-level left-inverse identity `subst [n].toSeries invSeries = X` (from `FormalGroup.subst_mulByNatHom_mulByNatInvSeries`), applies `eval₂_subst_bridge` to transport the evaluation, collapses the inner function using the hypothesis `ha`, and concludes by `eval₂_zero_of_constantCoeff_zero` using `FormalGroup.constantCoeff_mulByNatInvSeries`.
- **Hypotheses**: Complete local ring; `(n : R)` a unit; `a ∈ maximalIdeal R`.
- **Uses from project**: `FormalGroup.subst_mulByNatHom_mulByNatInvSeries`, `FormalGroup.mulByNatHom`, `FormalGroup.mulByNatInvSeries`, `eval₂_subst_bridge`, `FormalGroup.eval₂_zero_of_constantCoeff_zero`, `FormalGroup.constantCoeff_mulByNatInvSeries`
- **Used by**: `FormalGroup.EvalGroup.nsmul_injective_of_unit`
- **Visibility**: public
- **Lines**: 665–705; proof ~40 lines
- **Notes**: Proof >30 lines. No `sorry`.

---

### `theorem FormalGroup.EvalGroup.nsmul_injective_of_unit`
- **Type**: `(F : FormalGroup R) → (hAdic : IsAdic (maximalIdeal R)) → {n : ℕ} → IsUnit ((n : ℕ) : R) → {x : F.EvalGroup hAdic} → n • x = 0 → x = 0`
- **What**: When `(n : R)` is a unit, the `AddGroup` scalar action `n • (−)` on `F.EvalGroup hAdic` is injective.
- **How**: Extracts `(n • x).val.1 = 0`, uses `nsmul_val` to rewrite as `eval₂ ... [n].toSeries = 0`, applies `eval_mulByNatHom_injective_of_unit` to get `x.val.1 = 0`, then extensionality via `FormalGroup.EvalGroup.ext`.
- **Hypotheses**: Complete local ring; `(n : R)` a unit.
- **Uses from project**: `FormalGroup.EvalGroup.nsmul_val`, `FormalGroup.eval_mulByNatHom_injective_of_unit`, `FormalGroup.EvalGroup.ext`
- **Used by**: `FormalGroup.EvalGroup.addOrderOf_isPowOf`
- **Visibility**: public
- **Lines**: 710–726; proof ~16 lines
- **Notes**: No `sorry`.

---

### `theorem FormalGroup.EvalGroup.addOrderOf_isPowOf`
- **Type**: `(F : FormalGroup R) → (hAdic : IsAdic (maximalIdeal R)) → (p : ℕ) → p.Prime → (∀ m : ℕ, ¬ p ∣ m → IsUnit ((m : ℕ) : R)) → (x : F.EvalGroup hAdic) → IsOfFinAddOrder x → ∃ k : ℕ, addOrderOf x = p^k`
- **What**: Silverman IV.3.2(b): every torsion element of `F(M)` has order a power of `p`, when any `m` not divisible by `p` is a unit in `R`.
- **How**: Decomposes `addOrderOf x = p^k * m` with `gcd(m,p) = 1` via `Nat.ordProj_mul_ordCompl_eq_self`/`Nat.not_dvd_ordCompl`; the hypothesis gives `(m : R)` a unit; sets `y = (p^k) • x`, shows `m • y = 0` by `addOrderOf_nsmul_eq_zero`, concludes `y = 0` by `nsmul_injective_of_unit`, then `p^k | addOrderOf x` and vice versa.
- **Hypotheses**: Complete local ring; `p` prime; all non-`p`-multiples are units in `R`.
- **Uses from project**: `FormalGroup.EvalGroup.nsmul_injective_of_unit`
- **Used by**: `FormalGroup.EvalGroup.addOrderOf_isPowOf_residueChar`
- **Visibility**: public
- **Lines**: 733–765; proof ~32 lines
- **Notes**: Proof >30 lines. No `sorry`. Main torsion theorem.

---

### `def oneUnitsSubgroup`
- **Type**: `(R : Type*) → [CommRing R] → [IsLocalRing R] → Subgroup Rˣ`
- **What**: The subgroup of `Rˣ` consisting of "1-units": units `u` with `(u : R) - 1 ∈ maximalIdeal R`.
- **How**: Constructs the `Subgroup` record: `one_mem'` by `simp`; `mul_mem'` by the identity `uv - 1 = (u-1)(v-1) + (u-1) + (v-1)` and ideal membership; `inv_mem'` by `u⁻¹ - 1 = -(u-1)·u⁻¹`.
- **Hypotheses**: `R` a commutative local ring.
- **Uses from project**: (none — uses only mathlib)
- **Used by**: `oneAddUnit_mem`, `multiplicativeFormalGroup_EvalGroup_mulEquiv`
- **Visibility**: public
- **Lines**: 784–808; body ~24 lines
- **Notes**: No `sorry`. Standalone group definition; does not require the topology hypotheses.

---

### `private theorem oneAdd_isUnit`
- **Type**: `(x : maximalIdeal R) → IsUnit (1 + x.1)`
- **What**: In a local ring, `1 + x` is a unit for any `x ∈ maximalIdeal R`.
- **How**: `IsLocalRing.notMem_maximalIdeal.mp`: if `1 + x ∈ M` then `1 = (1+x) - x ∈ M`, contradicting `1 ∉ M` (the ideal is proper).
- **Hypotheses**: `R` a local ring; `x ∈ maximalIdeal R`.
- **Uses from project**: (none)
- **Used by**: `oneAddUnit`
- **Visibility**: private
- **Lines**: 813–820; proof ~7 lines
- **Notes**: No `sorry`. Decorated with `omit` to drop topology instances.

---

### `private noncomputable def oneAddUnit`
- **Type**: `(x : maximalIdeal R) → Rˣ`
- **What**: The unit `1 + x` packaged as an element of `Rˣ`.
- **How**: `(oneAdd_isUnit x).unit`.
- **Hypotheses**: `R` local ring; `x ∈ maximalIdeal R`.
- **Uses from project**: `oneAdd_isUnit`
- **Used by**: `oneAddUnit_val`, `oneAddUnit_mem`, `multiplicativeFormalGroup_EvalGroup_mulEquiv`
- **Visibility**: private
- **Lines**: 826–827; body 1 line
- **Notes**: No `sorry`.

---

### `private theorem oneAddUnit_val`
- **Type**: `(x : maximalIdeal R) → ((oneAddUnit x : Rˣ) : R) = 1 + x.1`
- **What**: The coercion of `oneAddUnit x` back to `R` equals `1 + x.1`.
- **How**: `IsUnit.unit_spec`.
- **Hypotheses**: `R` local ring; `x ∈ maximalIdeal R`.
- **Uses from project**: `oneAddUnit`
- **Used by**: `oneAddUnit_mem`, `multiplicativeFormalGroup_EvalGroup_mulEquiv`
- **Visibility**: private
- **Lines**: 832–834; proof ~2 lines
- **Notes**: No `sorry`. Decorated with `omit` to drop topology instances.

---

### `private theorem oneAddUnit_mem`
- **Type**: `(x : maximalIdeal R) → oneAddUnit x ∈ oneUnitsSubgroup R`
- **What**: The unit `1 + x` belongs to the 1-units subgroup.
- **How**: Unfolds the membership condition, rewrites using `oneAddUnit_val`, and observes `(1 + x.1) - 1 = x.1 ∈ maximalIdeal R`.
- **Hypotheses**: `R` local ring; `x ∈ maximalIdeal R`.
- **Uses from project**: `oneAddUnit`, `oneAddUnit_val`, `oneUnitsSubgroup`
- **Used by**: `multiplicativeFormalGroup_EvalGroup_mulEquiv`
- **Visibility**: private
- **Lines**: 839–843; proof ~4 lines
- **Notes**: No `sorry`.

---

### `noncomputable def multiplicativeFormalGroup_EvalGroup_mulEquiv`
- **Type**: `(hAdic : IsAdic (maximalIdeal R)) → Multiplicative ((multiplicativeFormalGroup R).EvalGroup hAdic) ≃* oneUnitsSubgroup R`
- **What**: Silverman IV.3.1.2 packaged: `Ĝ_m(M) ≃* (1+M, ·)` as multiplicative groups, where the target is the 1-units subgroup of `Rˣ`.
- **How**: Explicit `MulEquiv` record: `toFun x = oneAddUnit x.toAdd.val`, `invFun u = u - 1`. `left_inv`/`right_inv` by `oneAddUnit_val` + `ring`/`Units.ext`. `map_mul'` uses `evalAdd_multiplicativeFormalGroup_one_add`.
- **Hypotheses**: Complete local ring with adic topology.
- **Uses from project**: `multiplicativeFormalGroup`, `oneAddUnit`, `oneAddUnit_val`, `oneAddUnit_mem`, `oneUnitsSubgroup`, `evalAdd_multiplicativeFormalGroup_one_add`, `FormalGroup.EvalGroup.ext`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 852–886; body ~34 lines
- **Notes**: Proof/body >30 lines. No `sorry`. Public API; unused within this file.

---

### `theorem isUnit_natCast_of_not_dvd_residueChar`
- **Type**: `(p : ℕ) → [CharP (IsLocalRing.ResidueField R) p] → {m : ℕ} → ¬ p ∣ m → IsUnit ((m : ℕ) : R)`
- **What**: In a local ring with residue field of characteristic `p`, any integer `m` not divisible by `p` is a unit when cast to `R`.
- **How**: By contrapositive via `IsLocalRing.notMem_maximalIdeal`: if `m ∈ M` then its image in the residue field is zero, so `p | m` by `CharP.cast_eq_zero_iff`.
- **Hypotheses**: `R` local ring; residue field has characteristic `p`; `¬ p ∣ m`.
- **Uses from project**: (none — uses only mathlib)
- **Used by**: `FormalGroup.EvalGroup.addOrderOf_isPowOf_residueChar`
- **Visibility**: public
- **Lines**: 899–908; proof ~9 lines
- **Notes**: No `sorry`. Decorated with `omit` to drop topology instances.

---

### `theorem FormalGroup.EvalGroup.addOrderOf_isPowOf_residueChar`
- **Type**: `(F : FormalGroup R) → (hAdic : IsAdic (maximalIdeal R)) → (p : ℕ) → p.Prime → [CharP (IsLocalRing.ResidueField R) p] → (x : F.EvalGroup hAdic) → IsOfFinAddOrder x → ∃ k : ℕ, addOrderOf x = p^k`
- **What**: Silverman IV.6.1: for a formal group over a complete local ring with residue field of characteristic `p`, every torsion element has `p`-power order.
- **How**: Direct instantiation of `addOrderOf_isPowOf` with the `hR` hypothesis supplied by `isUnit_natCast_of_not_dvd_residueChar`.
- **Hypotheses**: Complete local ring; residue field has characteristic `p`; `p` prime.
- **Uses from project**: `FormalGroup.EvalGroup.addOrderOf_isPowOf`, `isUnit_natCast_of_not_dvd_residueChar`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 914–920; proof ~6 lines
- **Notes**: No `sorry`. Public API; unused within this file.

---

## Summary

| Kind | Count |
|------|-------|
| Declarations (total) | 35 |
| `def`/`noncomputable def` | 7 |
| `theorem`/`lemma` | 26 |
| `instance` | 0 |
| Private declarations | 9 |
| `sorry` | 0 |

**Long proofs (>30 lines)**:
- `FormalGroup.EvalGroup.nsmul_val` (~80 lines)
- `FormalGroup.evalAdd_sub_add_mem_pow_succ` (~85 lines)
- `FormalGroup.eval_mulByNatHom_injective_of_unit` (~40 lines)
- `FormalGroup.EvalGroup.addOrderOf_isPowOf` (~32 lines)
- `multiplicativeFormalGroup_EvalGroup_mulEquiv` (~34 lines body)

**Key API** (referenced by 3+ declarations in file):
- `maximalIdeal_pow_isClosed`: used by `evalAdd_pow_mem`, `evalNeg_pow_mem`, `evalAdd_sub_add_mem_pow_succ`
- `FormalGroup.evalGroup_powerIdeal`: used by `evalGroup_powerIdeal_mono`, `evalGroup_powerIdeal_toQuot`, `evalGroup_powerIdeal_toQuot_ker`, `evalGroup_powerIdeal_toQuot_range`, `evalGroup_powerIdeal_quotKerEquivRange`
- `FormalGroup.evalGroup_powerIdeal_toQuot`: used by `_ker`, `_range`, `_quotKerEquivRange`
- `lowDegFinset`: used by `lowDegFinset_mem_iff`, `two_le_sum_of_not_mem_lowDeg`, `evalAdd_sub_add_mem_pow_succ`
- `oneAddUnit`: used by `oneAddUnit_val`, `oneAddUnit_mem`, `multiplicativeFormalGroup_EvalGroup_mulEquiv`
