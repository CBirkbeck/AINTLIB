# Inventory: ./HasseWeil/FormalGroup/PDeriv.lean

**File purpose**: Defines `MvPowerSeries.pderiv s`, the formal partial derivative of a multivariate formal power series with respect to variable `s : σ`. Mathlib has `PowerSeries.derivative` (univariate) and `MvPolynomial.pderiv` (polynomial), but no multivariate power-series analogue. This file fills that gap and proves: basic additive/multiplicative API, the Leibniz rule, agreement with the polynomial `pderiv` under coercion, continuity in the product topology, and a substitution chain rule. Downstream use: Silverman IV.4.2 (translation invariance of the invariant differential on a formal group).

**Total declarations**: 22 (1 def, 17 theorems/lemmas public + 4 private)

---

### `def pderiv`
- **Type**: `(s : σ) → MvPowerSeries σ R → MvPowerSeries σ R` (requires `CommSemiring R`)
- **What**: Defines the formal partial derivative of a multivariate power series. The coefficient of `X^d` in `pderiv s f` is `(d s + 1) • coeff_{d + e_s} f` where `e_s = Finsupp.single s 1`.
- **How**: Direct definitional assignment (not a tactic proof); the formula is the standard shift-and-scale definition of formal differentiation.
- **Hypotheses**: `CommSemiring R`
- **Uses from project**: none
- **Used by**: essentially every other declaration in this file (via `coeff_pderiv`)
- **Visibility**: public
- **Lines**: 62–63, definition (1 line body)
- **Notes**: None

---

### `theorem coeff_pderiv`
- **Type**: `coeff R d (pderiv s f) = (d s + 1 : ℕ) • coeff R (d + Finsupp.single s 1) f`
- **What**: Computes the `d`-th coefficient of `pderiv s f`; this is the definitional unfolding packaged as a simp lemma.
- **How**: `rfl` — the definition is definitionally equal.
- **Hypotheses**: `CommSemiring R`
- **Uses from project**: `pderiv`
- **Used by**: `pderiv_zero`, `pderiv_add`, `pderiv_smul`, `pderiv_one`, `pderiv_C`, `pderiv_X_self`, `pderiv_X_of_ne`, `coeff_pderiv_mul_left`, `coeff_pderiv_mul_right`, `pderiv_mul`, `pderiv_monomial`, `pderiv_neg`, `pderiv_sub`, `continuous_pderiv`
- **Visibility**: public (`@[simp]`)
- **Lines**: 65–69, proof length 1 line
- **Notes**: `@[simp]` tagged; used by 14+ other declarations — the primary key API lemma

---

### `theorem pderiv_zero`
- **Type**: `pderiv s (0 : MvPowerSeries σ R) = 0`
- **What**: The derivative of zero is zero.
- **How**: `ext d; simp [coeff_pderiv]`
- **Hypotheses**: `CommSemiring R`
- **Uses from project**: `coeff_pderiv`, `pderiv`
- **Used by**: `pderiv_subst_polynomial` (implicitly via `hsubst0` + `pderiv_C`)
- **Visibility**: public (`@[simp]`)
- **Lines**: 73–76, proof 2 lines
- **Notes**: None

---

### `theorem pderiv_add`
- **Type**: `pderiv s (f + g) = pderiv s f + pderiv s g`
- **What**: The partial derivative is additive.
- **How**: `ext d; simp [coeff_pderiv, map_add, smul_add]`
- **Hypotheses**: `CommSemiring R`
- **Uses from project**: `coeff_pderiv`, `pderiv`
- **Used by**: `pderiv_coe`, `pderiv_subst_polynomial`
- **Visibility**: public
- **Lines**: 78–81, proof 2 lines
- **Notes**: None

---

### `theorem pderiv_smul`
- **Type**: `pderiv s (r • f) = r • pderiv s f`
- **What**: The partial derivative commutes with scalar multiplication.
- **How**: `ext d; simp only [coeff_pderiv, coeff_smul]; ring`
- **Hypotheses**: `CommSemiring R`
- **Uses from project**: `coeff_pderiv`, `pderiv`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 83–87, proof 3 lines
- **Notes**: Not referenced by any other declaration in this file (potential dead code within file, but part of the standard API expected by downstream)

---

### `private lemma single_self_apply`
- **Type**: `(Finsupp.single s (1 : ℕ)) s = 1`
- **What**: Evaluating `Finsupp.single s 1` at `s` gives 1; a small helper to avoid repeated classical decidability bookkeeping.
- **How**: `classical; simp`
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: `pderiv_X_of_ne`, `smul_eq_zero_of_not_le`, `coeff_pderiv_mul_left`, `coeff_pderiv_mul_right`, `pderiv_mul`, `pderiv_monomial`
- **Visibility**: private
- **Lines**: 89–92, proof 2 lines
- **Notes**: Used by 6 declarations — a key micro-lemma

---

### `private lemma add_single_ne_zero`
- **Type**: `d + Finsupp.single s 1 ≠ 0`
- **What**: The Finsupp `d + e_s` is never zero (since the `s`-component is at least 1).
- **How**: Contradiction: if it were zero, the `s`-component would be 0, but `Finsupp.add_apply` + `single_self_apply` gives it as `d s + 1 ≥ 1`.
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: `pderiv_one`, `pderiv_C`
- **Visibility**: private
- **Lines**: 94–98, proof 4 lines
- **Notes**: None

---

### `theorem pderiv_one`
- **Type**: `pderiv s (1 : MvPowerSeries σ R) = 0`
- **What**: The derivative of the constant 1 is zero.
- **How**: `ext d; rw [coeff_pderiv, coeff_one, if_neg (add_single_ne_zero d s), smul_zero, coeff_zero]` — uses that `d + e_s ≠ 0` (via `add_single_ne_zero`) to eliminate the `coeff_one` indicator.
- **Hypotheses**: `CommSemiring R`
- **Uses from project**: `coeff_pderiv`, `add_single_ne_zero`, `pderiv`
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 100–104, proof 3 lines
- **Notes**: None

---

### `theorem pderiv_C`
- **Type**: `pderiv s (C (σ := σ) r) = 0`
- **What**: The derivative of a constant power series is zero.
- **How**: Same structure as `pderiv_one`: `coeff_C` indicator is zero since `d + e_s ≠ 0`.
- **Hypotheses**: `CommSemiring R`
- **Uses from project**: `coeff_pderiv`, `add_single_ne_zero`, `pderiv`
- **Used by**: `pderiv_subst_polynomial`
- **Visibility**: public (`@[simp]`)
- **Lines**: 106–110, proof 3 lines
- **Notes**: None

---

### `theorem pderiv_X_self`
- **Type**: `pderiv s (X s : MvPowerSeries σ R) = 1`
- **What**: The partial derivative of the variable `X s` with respect to `s` is 1.
- **How**: Case split on `d = 0`: at `d = 0`, shows `d + e_s = e_s = Finsupp.single s 1`, matching `coeff_X`; at `d ≠ 0`, shows `d + e_s ≠ e_s` by `add_right_cancel`, so both coefficients are 0.
- **Hypotheses**: `CommSemiring R`
- **Uses from project**: `coeff_pderiv`, `pderiv`
- **Used by**: `pderiv_subst_polynomial`
- **Visibility**: public (`@[simp]`)
- **Lines**: 112–127, proof 14 lines
- **Notes**: None

---

### `theorem pderiv_X_of_ne`
- **Type**: `pderiv s (X t : MvPowerSeries σ R) = 0` (for `s ≠ t`)
- **What**: The partial derivative of `X t` with respect to a different variable `s` is zero.
- **How**: Shows `d + e_s ≠ Finsupp.single t 1` by comparing the `s`-component: the LHS has `s`-value ≥ 1 while the RHS has `s`-value 0 (since `s ≠ t`). Uses `single_self_apply` and `Finsupp.single_apply`.
- **Hypotheses**: `CommSemiring R`, `s ≠ t`
- **Uses from project**: `coeff_pderiv`, `single_self_apply`, `pderiv`
- **Used by**: `pderiv_subst_polynomial`
- **Visibility**: public (`@[simp]`)
- **Lines**: 129–142, proof 12 lines
- **Notes**: None

---

### `private lemma smul_eq_zero_of_not_le`
- **Type**: `¬ (Finsupp.single s 1 ≤ a) → (a s : ℕ) • x = 0`
- **What**: If `e_s ⊄ a` (i.e., `a s = 0`), then `(a s) • x = 0`. Helper used to discard off-support terms in the Leibniz rule proof.
- **How**: Shows `a s = 0` by contradiction (if `a s ≥ 1` then `e_s ≤ a` pointwise); uses `single_self_apply` for the diagonal case.
- **Hypotheses**: none
- **Uses from project**: `single_self_apply`
- **Used by**: `coeff_pderiv_mul_left`, `coeff_pderiv_mul_right`
- **Visibility**: private
- **Lines**: 147–162, proof 14 lines
- **Notes**: None

---

### `private theorem coeff_pderiv_mul_left`
- **Type**: `coeff R d (pderiv s f * g) = ∑ p ∈ antidiagonal (d + e_s), (p.1 s : ℕ) • (coeff p.1 f * coeff p.2 g)`
- **What**: The "left-derivative" half of the Leibniz rule: computes the coefficient of `pderiv s f * g` as a sum over the antidiagonal of `d + e_s`.
- **How**: Expands via `coeff_pderiv` + `coeff_mul`, then reindexes the antidiagonal sum from `antidiag d` to a filtered subset of `antidiag (d + e_s)` using `Finset.sum_nbij'` with the bijection `p ↦ (p.1 + e, p.2)`. Terms outside the filter vanish by `smul_eq_zero_of_not_le` and `Finset.sum_filter_of_ne`.
- **Hypotheses**: `CommSemiring R`, `DecidableEq σ`
- **Uses from project**: `coeff_pderiv`, `single_self_apply`, `smul_eq_zero_of_not_le`
- **Used by**: `pderiv_mul`
- **Visibility**: private
- **Lines**: 166–226, proof ~57 lines
- **Notes**: Proof longer than 30 lines; the reindexing via `Finset.sum_nbij'` is the non-trivial combinatorial step

---

### `private theorem coeff_pderiv_mul_right`
- **Type**: `coeff R d (f * pderiv s g) = ∑ p ∈ antidiagonal (d + e_s), (p.2 s : ℕ) • (coeff p.1 f * coeff p.2 g)`
- **What**: The "right-derivative" half of the Leibniz rule: analogous to `coeff_pderiv_mul_left` but for the right factor.
- **How**: Same strategy as `coeff_pderiv_mul_left` but reindexes via `p ↦ (p.1, p.2 + e)`.
- **Hypotheses**: `CommSemiring R`, `DecidableEq σ`
- **Uses from project**: `coeff_pderiv`, `single_self_apply`, `smul_eq_zero_of_not_le`
- **Used by**: `pderiv_mul`
- **Visibility**: private
- **Lines**: 229–276, proof ~45 lines
- **Notes**: Proof longer than 30 lines; parallel structure to `coeff_pderiv_mul_left`

---

### `theorem pderiv_mul`
- **Type**: `pderiv s (f * g) = pderiv s f * g + f * pderiv s g`
- **What**: The Leibniz product rule for the formal partial derivative on multivariate power series.
- **How**: Reduces to showing coefficient equality. Computes LHS coefficient via `coeff_pderiv` + `coeff_mul` as a single antidiagonal sum with scalar `(p.1 s + p.2 s)`, then splits via `coeff_pderiv_mul_left` + `coeff_pderiv_mul_right`. Uses `single_self_apply` to relate `p.1 s + p.2 s = d s + 1` on the antidiagonal, then `add_smul` to combine.
- **Hypotheses**: `CommSemiring R`
- **Uses from project**: `single_self_apply`, `coeff_pderiv`, `coeff_pderiv_mul_left`, `coeff_pderiv_mul_right`, `pderiv`
- **Used by**: `pderiv_subst_polynomial`
- **Visibility**: public
- **Lines**: 280–300, proof ~20 lines
- **Notes**: None

---

### `theorem pderiv_monomial`
- **Type**: `pderiv s (monomial n a) = monomial (n - Finsupp.single s 1) (a * n s)`
- **What**: Computes the derivative of a monomial `a · X^n`: gives `(n s) · a · X^(n - e_s)`, matching the polynomial formula.
- **How**: Coefficient comparison; case splits on `e_s ≤ n` and `d + e_s = n`. Uses `single_self_apply` to get `d s + 1 = n s`, `nsmul_eq_mul` and `mul_comm` to match the output form. When `e_s ⊄ n`, shows `n s = 0` so the result is zero.
- **Hypotheses**: `CommSemiring R`
- **Uses from project**: `coeff_pderiv`, `single_self_apply`, `pderiv`
- **Used by**: `pderiv_coe`
- **Visibility**: public
- **Lines**: 304–349, proof ~43 lines
- **Notes**: Proof longer than 30 lines

---

### `theorem pderiv_neg`
- **Type**: `pderiv s (-f) = -pderiv s f`
- **What**: The partial derivative commutes with negation.
- **How**: `ext d; simp [coeff_pderiv]`
- **Hypotheses**: `CommRing R`
- **Uses from project**: `coeff_pderiv`, `pderiv`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 359–361, proof 2 lines
- **Notes**: None

---

### `theorem pderiv_sub`
- **Type**: `pderiv s (f - g) = pderiv s f - pderiv s g`
- **What**: The partial derivative distributes over subtraction.
- **How**: `ext d; simp [coeff_pderiv, map_sub, smul_sub]`
- **Hypotheses**: `CommRing R`
- **Uses from project**: `coeff_pderiv`, `pderiv`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 363–366, proof 2 lines
- **Notes**: None

---

### `theorem pderiv_coe`
- **Type**: `MvPowerSeries.pderiv s (↑p) = ↑(MvPolynomial.pderiv s p)` (for `p : MvPolynomial σ R`)
- **What**: The power-series `pderiv s` agrees with the polynomial `MvPolynomial.pderiv s` under the coercion `MvPolynomial → MvPowerSeries`.
- **How**: Polynomial induction via `MvPolynomial.induction_on'`. For monomials: uses `pderiv_monomial` + `MvPolynomial.pderiv_monomial`. For sums: uses `pderiv_add` and `MvPolynomial.coe_add`.
- **Hypotheses**: `CommSemiring R`
- **Uses from project**: `pderiv_monomial`, `pderiv_add`, `pderiv`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 376–386, proof ~9 lines
- **Notes**: None

---

### `theorem continuous_pderiv`
- **Type**: `Continuous (MvPowerSeries.pderiv (R := R) (σ := σ) s)` (in the product/Pi topology on `MvPowerSeries σ R`)
- **What**: The formal partial derivative is a continuous map in the product topology on `MvPowerSeries σ R`.
- **How**: By `continuous_pi_iff`, it suffices to show continuity of each coefficient map `f ↦ coeff d (pderiv s f)`. By `coeff_pderiv`, this equals `(d s + 1) • coeff (d + e_s) f`, which is a constant smul of the continuous projection `WithPiTopology.continuous_coeff`.
- **Hypotheses**: `CommSemiring R`, `TopologicalSpace R`, `ContinuousConstSMul ℕ R`
- **Uses from project**: `coeff_pderiv`, `pderiv`
- **Used by**: `pderiv_subst`
- **Visibility**: public
- **Lines**: 399–413, proof ~13 lines
- **Notes**: None

---

### `private theorem pderiv_subst_polynomial`
- **Type**: For `p : MvPolynomial σ R`, `Fintype σ`, and `HasSubst a`: `pderiv t (subst a ↑p) = ∑ s : σ, pderiv t (a s) * subst a (pderiv s ↑p)`
- **What**: The substitution chain rule for `MvPowerSeries.pderiv`, restricted to polynomial inputs — the dense auxiliary case used to extend to all power series by continuity.
- **How**: Polynomial induction via `MvPolynomial.induction_on`. For `C r`: both sides are zero (via `pderiv_C` and `AlgHom.commutes`). For sums: additive decomposition using `pderiv_add` + `subst_add`. For `mul_X`: Leibniz + chain rule step; uses `pderiv_mul`, `subst_mul`, `subst_X`, `pderiv_X_self`, `pderiv_X_of_ne`, and a summand rewrite with `Finset.sum_eq_single` to pick out the `s = i` term.
- **Hypotheses**: `CommRing R`, `Fintype σ`, `MvPowerSeries.HasSubst a`
- **Uses from project**: `pderiv_C`, `pderiv_add`, `pderiv_mul`, `pderiv_X_self`, `pderiv_X_of_ne`, `pderiv`
- **Used by**: `pderiv_subst`
- **Visibility**: private
- **Lines**: 430–520, proof ~88 lines
- **Notes**: Proof longer than 30 lines (the longest single proof in the file); the `mul_X` induction step is the mathematical core — the computation reduces to extracting the `s = i` term from `Finset.sum_eq_single`

---

### `theorem pderiv_subst`
- **Type**: For `Fintype σ` and `HasSubst a`: `pderiv t (subst a f) = ∑ s : σ, pderiv t (a s) * subst a (pderiv s f)` (for `f : MvPowerSeries σ R`)
- **What**: The substitution chain rule for `MvPowerSeries.pderiv` over finite index types — the full power-series version of the multivariate chain rule.
- **How**: Both sides are continuous functions of `f` (LHS via `continuous_pderiv.comp continuous_subst`; RHS via `continuous_finset_sum`). They agree on polynomials by `pderiv_subst_polynomial`. Polynomials are dense by `WithPiTopology.denseRange_toMvPowerSeries`. Extends by `Continuous.ext_on`.
- **Hypotheses**: `CommRing R`, `Fintype σ`, `MvPowerSeries.HasSubst a`
- **Uses from project**: `pderiv_subst_polynomial`, `continuous_pderiv`, `pderiv`
- **Used by**: `pderiv_subst_fin2`
- **Visibility**: public
- **Lines**: 527–563, proof ~35 lines
- **Notes**: Proof longer than 30 lines; the density + continuity extension argument is the key mathematical strategy

---

### `theorem pderiv_subst_fin2`
- **Type**: For `σ = Fin 2` and `HasSubst a`: `pderiv t (subst a f) = pderiv t (a 0) * subst a (pderiv 0 f) + pderiv t (a 1) * subst a (pderiv 1 f)`
- **What**: Specialization of the substitution chain rule to `σ = Fin 2`, the form used in Silverman IV.4.2 for the formal group invariant differential.
- **How**: `rw [pderiv_subst t ha f, Fin.sum_univ_two]` — the finite sum over `Fin 2` unfolds to two terms.
- **Hypotheses**: `CommRing R`, `MvPowerSeries.HasSubst a`
- **Uses from project**: `pderiv_subst`, `pderiv`
- **Used by**: unused in file (leaf; called externally by `Differential.lean`)
- **Visibility**: public
- **Lines**: 574–580, proof 1 line
- **Notes**: The stated downstream use is Silverman IV.4.2

---

## Summary Statistics

| Category | Count |
|---|---|
| Total declarations | 22 |
| Definitions (`def`) | 1 (`pderiv`) |
| Public theorems/lemmas | 17 |
| Private lemmas/theorems | 4 (`single_self_apply`, `add_single_ne_zero`, `smul_eq_zero_of_not_le`, `coeff_pderiv_mul_left`, `coeff_pderiv_mul_right`, `pderiv_subst_polynomial`) |
| Instances | 0 |
| Sorry | 0 |
| set_option maxHeartbeats | 0 |

**Key API**: `coeff_pderiv` (used by 14+ others), `single_self_apply` (used by 6 others), `continuous_pderiv` (used by `pderiv_subst`).

**Long proofs (>30 lines)**: `coeff_pderiv_mul_left` (~57 lines), `coeff_pderiv_mul_right` (~45 lines), `pderiv_monomial` (~43 lines), `pderiv_subst_polynomial` (~88 lines), `pderiv_subst` (~35 lines).

**Unused in file** (not referenced by any other declaration in this file): `pderiv_smul`, `pderiv_one`, `pderiv_neg`, `pderiv_sub`, `pderiv_coe`, `pderiv_subst_fin2`.

**Notes**: This is a self-contained infrastructure file extending Mathlib's power series API; there is strong potential for this to be contributed to Mathlib as it fills a genuine gap (`MvPowerSeries.pderiv`). The density-plus-continuity argument in `pderiv_subst` is notably elegant.
