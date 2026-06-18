# Inventory: ./HasseWeil/FormalGroup/Inverse.lean

**File**: `HasseWeil/FormalGroup/Inverse.lean`  
**Total lines**: 671  
**Namespace**: `HasseWeil.FormalGroup`  
**Imports**: `HasseWeil.FormalGroup.Definition`, `HasseWeil.FormalGroup.Logarithm`  
**Topic**: Formal inverse power series `i(T)` for a formal group law `F(X, Y)` (Silverman IV.2).

---

## Declarations

### `noncomputable def FormalGroup.inverseTrunc`
- **Type**: `(F : FormalGroup R) : ℕ → PowerSeries R`
- **What**: Iterative truncation of the formal inverse: `inverseTrunc F 0 = 0`; at step `n+1`, add the monomial `C(-coeff(n+1)(fAdd F X prev)) * X^(n+1)` to `prev`.
- **How**: Structural recursion (pattern matching). The correction coefficient is chosen to zero out the `(n+1)`-th coefficient of `fAdd F X prev`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `HasseWeil.FG.fAdd`
- **Used by**: `FormalGroup.inverseCoeff`, `FormalGroup.inverseTrunc_zero`, `FormalGroup.coeff_inverseTrunc_succ_of_le`, `FormalGroup.coeff_inverseTrunc_of_le`, `FormalGroup.inverseTrunc_constantCoeff`, `FormalGroup.inverseTrunc_hasSubst`, `FormalGroup.inverse_coeff_one`, `FormalGroup.inverseTrunc_fAdd_coeff_eq_zero`, `FormalGroup.fAdd_X_inverse_eq_zero`
- **Visibility**: public
- **Lines**: 64–72 (body: 8 lines)
- **Notes**: Mirrors `compInvTrunc` in `Logarithm.lean` for the two-variable fixed-point equation.

---

### `noncomputable def FormalGroup.inverseCoeff`
- **Type**: `(F : FormalGroup R) (n : ℕ) : R`
- **What**: The `n`-th coefficient of the formal inverse, defined as `coeff n (inverseTrunc F n)` — stable value extracted from the truncation at step `n`.
- **How**: Direct definition.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `FormalGroup.inverseTrunc`
- **Used by**: `FormalGroup.inverse`, `FormalGroup.inverseCoeff_zero`, `FormalGroup.coeff_inverseTrunc_of_le`
- **Visibility**: public
- **Lines**: 74–75 (body: 1 line)
- **Notes**: None.

---

### `noncomputable def FormalGroup.inverse`
- **Type**: `(F : FormalGroup R) : PowerSeries R`
- **What**: The formal inverse power series `i(T) = Σ (inverseCoeff F n) * T^n`, constructed via `PowerSeries.mk`.
- **How**: `PowerSeries.mk F.inverseCoeff` — assembles the coefficient sequence.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `FormalGroup.inverseCoeff`
- **Used by**: `FormalGroup.inverse_coeff_zero`, `FormalGroup.inverse_constantCoeff`, `FormalGroup.inverse_hasSubst`, `FormalGroup.inverse_coeff_one`, `FormalGroup.fAdd_X_inverse_eq_zero`; also referenced from `EvalGroup.lean` and `Associated.lean`.
- **Visibility**: public
- **Lines**: 84–85 (body: 1 line)
- **Notes**: Key public API.

---

### `theorem FormalGroup.inverseTrunc_zero`
- **Type**: `(F : FormalGroup R) : F.inverseTrunc 0 = 0`
- **What**: Base case of the iterative construction: `inverseTrunc F 0 = 0`.
- **How**: `rfl`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `FormalGroup.inverseTrunc`
- **Used by**: `FormalGroup.inverse_coeff_one`, `FormalGroup.inverseTrunc_fAdd_coeff_eq_zero`
- **Visibility**: public (`@[simp]`)
- **Lines**: 90–93 (proof: 1 line)
- **Notes**: None.

---

### `theorem FormalGroup.inverseCoeff_zero`
- **Type**: `(F : FormalGroup R) : F.inverseCoeff 0 = 0`
- **What**: The zeroth stable coefficient is zero (constant term of formal inverse vanishes).
- **How**: `simp [FormalGroup.inverseCoeff]` reduces to `coeff 0 0 = 0`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `FormalGroup.inverseCoeff`, `FormalGroup.inverseTrunc_zero`
- **Used by**: `FormalGroup.inverseTrunc_constantCoeff`
- **Visibility**: public (`@[simp]`)
- **Lines**: 95–97 (proof: 2 lines)
- **Notes**: None.

---

### `theorem FormalGroup.inverse_coeff_zero`
- **Type**: `(F : FormalGroup R) : PowerSeries.coeff 0 F.inverse = 0`
- **What**: The 0th coefficient of `inverse F` is zero.
- **How**: `simp [FormalGroup.inverse]` unfolds `PowerSeries.mk` and uses `coeff_mk`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `FormalGroup.inverse`
- **Used by**: `FormalGroup.inverse_constantCoeff`; also used in `EvalGroup.lean`.
- **Visibility**: public (`@[simp]`)
- **Lines**: 101–103 (proof: 2 lines)
- **Notes**: None.

---

### `theorem FormalGroup.inverse_constantCoeff`
- **Type**: `(F : FormalGroup R) : @PowerSeries.constantCoeff R _ F.inverse = 0`
- **What**: The constant coefficient of the formal inverse is zero (necessary for substitution).
- **How**: Rewrites via `PowerSeries.coeff_zero_eq_constantCoeff_apply` to reduce to `inverse_coeff_zero`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `FormalGroup.inverse_coeff_zero`
- **Used by**: `FormalGroup.inverse_hasSubst`, `FormalGroup.inverseTrunc_fAdd_coeff_eq_zero` (indirectly), `FormalGroup.fAdd_X_inverse_eq_zero`; also used in `EvalGroup.lean`.
- **Visibility**: public (`@[simp]`)
- **Lines**: 107–110 (proof: 3 lines)
- **Notes**: None.

---

### `theorem FormalGroup.coeff_inverseTrunc_succ_of_le`
- **Type**: `(F : FormalGroup R) (n k : ℕ) (hk : k ≤ n) : PowerSeries.coeff k (F.inverseTrunc (n+1)) = PowerSeries.coeff k (F.inverseTrunc n)`
- **What**: Adding the degree-`(n+1)` correction to pass from `inverseTrunc F n` to `inverseTrunc F (n+1)` does not change coefficients at degree `≤ n`.
- **How**: Unfolds the recursive definition, applies `PowerSeries.coeff_C_mul_X_pow`, and uses `if_neg` with `omega` since `k ≤ n < n+1`.
- **Hypotheses**: `CommRing R`, `k ≤ n`
- **Uses from project**: `FormalGroup.inverseTrunc`
- **Used by**: `FormalGroup.coeff_inverseTrunc_of_le`, `FormalGroup.inverseTrunc_fAdd_coeff_eq_zero`
- **Visibility**: public
- **Lines**: 120–131 (proof: 11 lines)
- **Notes**: None.

---

### `theorem FormalGroup.coeff_inverseTrunc_of_le`
- **Type**: `(F : FormalGroup R) (n k : ℕ) (hk : k ≤ n) : PowerSeries.coeff k (F.inverseTrunc n) = F.inverseCoeff k`
- **What**: For `k ≤ n`, the `k`-th coefficient of `inverseTrunc F n` stabilizes to `inverseCoeff F k`.
- **How**: Induction on `n`; base uses `inverseCoeff_zero`; inductive step uses `coeff_inverseTrunc_succ_of_le` for `k < n+1` and definitional equality for `k = n+1`.
- **Hypotheses**: `CommRing R`, `k ≤ n`
- **Uses from project**: `FormalGroup.coeff_inverseTrunc_succ_of_le`, `FormalGroup.inverseCoeff_zero`
- **Used by**: `FormalGroup.inverseTrunc_constantCoeff`, `FormalGroup.fAdd_X_inverse_eq_zero`
- **Visibility**: public
- **Lines**: 134–150 (proof: 16 lines)
- **Notes**: None.

---

### `theorem FormalGroup.inverseTrunc_constantCoeff`
- **Type**: `(F : FormalGroup R) (n : ℕ) : @PowerSeries.constantCoeff R _ (F.inverseTrunc n) = 0`
- **What**: Every truncation `inverseTrunc F n` has zero constant coefficient.
- **How**: Rewrites via `coeff_zero_eq_constantCoeff_apply`, then uses `coeff_inverseTrunc_of_le` at `k = 0` and `inverseCoeff_zero`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `FormalGroup.coeff_inverseTrunc_of_le`, `FormalGroup.inverseCoeff_zero`
- **Used by**: `FormalGroup.inverseTrunc_hasSubst`, `FormalGroup.inverseTrunc_fAdd_coeff_eq_zero`, `FormalGroup.fAdd_X_inverse_eq_zero`
- **Visibility**: public
- **Lines**: 153–157 (proof: 4 lines)
- **Notes**: None.

---

### `theorem FormalGroup.inverseTrunc_hasSubst`
- **Type**: `(F : FormalGroup R) (n : ℕ) : PowerSeries.HasSubst (F.inverseTrunc n)`
- **What**: Each truncation `inverseTrunc F n` satisfies the `HasSubst` property (needed for power series substitution).
- **How**: Applies `PowerSeries.HasSubst.of_constantCoeff_zero'` to `inverseTrunc_constantCoeff`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `FormalGroup.inverseTrunc_constantCoeff`
- **Used by**: unused in this file (utility lemma for external use)
- **Visibility**: public
- **Lines**: 160–162 (proof: 2 lines)
- **Notes**: Unused within this file; likely API for downstream callers.

---

### `theorem FormalGroup.inverse_hasSubst`
- **Type**: `(F : FormalGroup R) : PowerSeries.HasSubst F.inverse`
- **What**: The formal inverse power series satisfies `HasSubst` (zero constant coefficient).
- **How**: Applies `PowerSeries.HasSubst.of_constantCoeff_zero'` to `inverse_constantCoeff`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `FormalGroup.inverse_constantCoeff`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 165–167 (proof: 2 lines)
- **Notes**: Unused within this file; utility for external use.

---

### `theorem FormalGroup.inverse_coeff_one`
- **Type**: `(F : FormalGroup R) : PowerSeries.coeff 1 F.inverse = -1`
- **What**: The linear coefficient of the formal inverse is `-1` (the isomorphism `T ↦ i(T)` has derivative `-1` at the origin, consistent with `i(T) = -T + O(T²)`).
- **How**: Unfolds via `PowerSeries.coeff_mk`, reduces to `coeff 1 (inverseTrunc F 1)`, expands the recursive definition using `inverseTrunc_zero`, applies `coeff_C_mul_X_pow` with `if_pos`, then uses `HasseWeil.FG.coeff_one_fAdd` (the second unit axiom: coefficient of `Y` in `F(X,Y)` is 1) to conclude `coeff 1 (fAdd F X 0) = 1`.
- **Hypotheses**: `CommRing R`
- **Uses from project**: `FormalGroup.inverseTrunc_zero`, `HasseWeil.FG.coeff_one_fAdd`
- **Used by**: unused in this file
- **Visibility**: public (`@[simp]`)
- **Lines**: 176–198 (proof: 22 lines)
- **Notes**: The key lemma invoked is `HasseWeil.FG.coeff_one_fAdd` from `Definition.lean`.

---

### `private theorem coeff_X_pow_mul_pow_eq_of_coeff_eq`
- **Type**: `(g₁ g₂ : PowerSeries R) (h1 : constantCoeff g₁ = 0) (h2 : constantCoeff g₂ = 0) (n : ℕ) (hg : ∀ j ≤ n, coeff j g₁ = coeff j g₂) (a b k : ℕ) (hk : k ≤ n) : coeff k (X^a * g₁^b) = coeff k (X^a * g₂^b)`
- **What**: Coefficient stabilization for monomials in a power series: if `g₁` and `g₂` agree up to degree `n`, then `X^a * g₁^b` and `X^a * g₂^b` also agree at each degree `k ≤ n`.
- **How**: Expands via `coeff_mul` and `Finset.sum_congr`; uses `coeff_pow_eq_of_coeff_eq` (from `Logarithm.lean`) for the `g`-factors when `j ≤ n`, and `coeff_pow_eq_zero_of_gt` (also from `Logarithm.lean`) when `j < b`.
- **Hypotheses**: `CommRing R`; `g₁`, `g₂` have zero constant coefficient; `g₁` and `g₂` agree on coefficients 0 through `n`; `k ≤ n`.
- **Uses from project**: `coeff_pow_eq_of_coeff_eq` (Logarithm.lean), `coeff_pow_eq_zero_of_gt` (Logarithm.lean)
- **Used by**: `FormalGroup.coeff_fAdd_X_eq_of_coeff_eq`
- **Visibility**: private
- **Lines**: 220–249 (proof: ~29 lines)
- **Notes**: Proof is ~29 lines (just under threshold but close).

---

### `theorem FormalGroup.coeff_fAdd_X_eq_of_coeff_eq`
- **Type**: `(F : FormalGroup R) (g₁ g₂ : PowerSeries R) (h1 h2 : constantCoeff · = 0) (n : ℕ) (hg : ∀ j ≤ n, coeff j g₁ = coeff j g₂) (k : ℕ) (hk : k ≤ n) : coeff k (fAdd F X g₁) = coeff k (fAdd F X g₂)`
- **What**: MvPowerSeries stabilization for `fAdd F X g`: if `g₁` and `g₂` have zero constant coefficient and agree up to degree `n`, then `fAdd F X g₁` and `fAdd F X g₂` agree at each degree `k ≤ n`.
- **How**: Both sides are expanded using `MvPowerSeries.coeff_subst` (via `HasseWeil.FG.hasSubst_pair`), Finsupp product unfolded to `Fin.prod_univ_two`, then `finsum_congr` reduces to `coeff_X_pow_mul_pow_eq_of_coeff_eq` per term.
- **Hypotheses**: `CommRing R`, `g₁`, `g₂` zero constant coefficient, agreement up to degree `n`, `k ≤ n`.
- **Uses from project**: `HasseWeil.FG.hasSubst_pair` (Definition.lean), `coeff_X_pow_mul_pow_eq_of_coeff_eq`
- **Used by**: `FormalGroup.inverseTrunc_fAdd_coeff_eq_zero`, `FormalGroup.fAdd_X_inverse_eq_zero`
- **Visibility**: public
- **Lines**: 254–286 (proof: ~32 lines)
- **Notes**: Proof is 32 lines (exceeds 30-line threshold). Key external dependency: `MvPowerSeries.coeff_subst`.

---

### `private theorem coeff_add_monomial_pow_stable`
- **Type**: `(g : PowerSeries R) (_hg : constantCoeff g = 0) (n : ℕ) (c : R) (d : ℕ) (k : ℕ) (hk : k < n+1) : coeff k ((g + C c * X^(n+1))^d) = coeff k (g^d)`
- **What**: Adding a high-order monomial `C c * X^(n+1)` to `g` does not affect the coefficient of `(·)^d` at degrees `k < n+1`.
- **How**: Uses the binomial theorem via `add_pow`; the `m = 0` term gives `g^d`; for `m ≥ 1`, uses `monomial_pow_eq` (from `Logarithm.lean`) to show `(C c * X^(n+1))^m = C(c^m) * X^(m*(n+1))`, then `coeff_mul` + `coeff_X_pow` shows these terms vanish because `k < m*(n+1)`.
- **Hypotheses**: `CommRing R`, `k < n+1`.
- **Uses from project**: `monomial_pow_eq` (Logarithm.lean)
- **Used by**: `coeff_X_pow_mul_add_monomial_pow`
- **Visibility**: private
- **Lines**: 299–377 (proof: ~78 lines)
- **Notes**: Longest proof in the file at ~78 lines. Notable effort converting `Nat.cast` to `C` applied for `choose` coefficients (manual induction).

---

### `private theorem coeff_X_pow_mul_add_monomial_pow`
- **Type**: `(g : PowerSeries R) (hg : constantCoeff g = 0) (n : ℕ) (c : R) (a j : ℕ) : coeff (n+1) (X^a * (g + C c * X^(n+1))^j) = coeff (n+1) (X^a * g^j) + if a = 0 ∧ j = 1 then c else 0`
- **What**: The `(n+1)`-th coefficient of `X^a * (g + C c * X^(n+1))^j` picks up an extra `c` precisely when `(a, j) = (0, 1)` (i.e., the `Y`-linear term in `F`).
- **How**: Split on `a = 0` vs `a ≥ 1`. For `a = 0`: use `coeff_add_monomial_pow_eq` (Logarithm.lean). For `a ≥ 1`: use `coeff_mul` + `coeff_X_pow` to show `p = a` forces `q = n+1-a < n+1`, then `coeff_add_monomial_pow_stable`.
- **Hypotheses**: `CommRing R`, `constantCoeff g = 0`.
- **Uses from project**: `coeff_add_monomial_pow_stable`, `coeff_add_monomial_pow_eq` (Logarithm.lean)
- **Used by**: `FormalGroup.coeff_fAdd_X_add_monomial`
- **Visibility**: private
- **Lines**: 381–429 (proof: ~48 lines)
- **Notes**: Proof is ~48 lines (exceeds 30-line threshold).

---

### `theorem FormalGroup.coeff_fAdd_X_add_monomial`
- **Type**: `(F : FormalGroup R) (g : PowerSeries R) (n : ℕ) (c : R) (hg : constantCoeff g = 0) : coeff (n+1) (fAdd F X (g + C c * X^(n+1))) = coeff (n+1) (fAdd F X g) + c`
- **What**: The two-variable monomial-addition step: adding `C c * X^(n+1)` to `g` increments the `(n+1)`-th coefficient of `fAdd F X g` by exactly `c`. This is the critical step for the inductive construction, reflecting that the coefficient of `Y` in `F(X, Y)` is `1`.
- **How**: Expands both sides via `MvPowerSeries.coeff_subst` and `hasSubst_pair`; applies `coeff_X_pow_mul_add_monomial_pow` per monomial term; then uses `finsum_add_distrib` and `finsum_eq_single` to isolate the `d = Finsupp.single 1 1` term, whose coefficient in `F.toSeries` is `1` by `HasseWeil.FG.FormalGroup.coeff_01` (the right-unit axiom of the formal group law).
- **Hypotheses**: `CommRing R`, `g` has zero constant coefficient.
- **Uses from project**: `HasseWeil.FG.hasSubst_pair` (Definition.lean), `HasseWeil.FG.FormalGroup.coeff_01` (Definition.lean), `coeff_X_pow_mul_add_monomial_pow`, `monomial_constantCoeff_zero` (Logarithm.lean)
- **Used by**: `FormalGroup.inverseTrunc_fAdd_coeff_eq_zero`
- **Visibility**: public
- **Lines**: 438–578 (proof: ~140 lines)
- **Notes**: By far the longest proof in the file (~140 lines), exceeding the 30-line threshold significantly. Most of the length is the finiteness argument (`hfin1`, `hfin2`) for `finsum_add_distrib`, and the `Nat.cast → C` conversion boilerplate inside `coeff_add_monomial_pow_stable`. The culminating use of `coeff_01` is the mathematical core.

---

### `theorem FormalGroup.inverseTrunc_fAdd_coeff_eq_zero`
- **Type**: `(F : FormalGroup R) (n k : ℕ) (hk : k ≤ n) : coeff k (fAdd F X (inverseTrunc F n)) = 0`
- **What**: Core invariant of the iterative construction: for each `k ≤ n`, the `k`-th coefficient of `fAdd F X (inverseTrunc F n)` is zero. This shows the truncation correctly approximates the formal inverse up to degree `n`.
- **How**: Induction on `n`. Base case: `inverseTrunc F 0 = 0` and `fAdd F X 0 = X` (by `fAdd_zero_right`), so `coeff 0 X = 0`. Inductive step splits into `k ≤ n` (stabilization via `coeff_fAdd_X_eq_of_coeff_eq` + IH) and `k = n+1` (monomial-addition via `coeff_fAdd_X_add_monomial` + cancellation `c + (-c) = 0`).
- **Hypotheses**: `CommRing R`, `k ≤ n`.
- **Uses from project**: `FormalGroup.inverseTrunc_zero`, `FormalGroup.coeff_inverseTrunc_succ_of_le`, `FormalGroup.inverseTrunc_constantCoeff`, `FormalGroup.coeff_fAdd_X_eq_of_coeff_eq`, `FormalGroup.coeff_fAdd_X_add_monomial`, `HasseWeil.FG.fAdd_zero_right` (Definition.lean)
- **Used by**: `FormalGroup.fAdd_X_inverse_eq_zero`
- **Visibility**: public
- **Lines**: 592–638 (proof: ~46 lines)
- **Notes**: Proof is ~46 lines (exceeds 30-line threshold). Central lemma connecting the recursive construction to its invariant.

---

### `theorem FormalGroup.fAdd_X_inverse_eq_zero`
- **Type**: `(F : FormalGroup R) : HasseWeil.FG.fAdd F PowerSeries.X F.inverse = 0`
- **What**: Functional equation of the formal inverse: `F(T, i(T)) = 0` (Silverman IV.2). This is the defining property of the formal inverse as a power series.
- **How**: Extensionality on coefficients. At each degree `k`, `inverse F` agrees with `inverseTrunc F k` up to degree `k` (via `coeff_inverseTrunc_of_le` + `coeff_mk`); then `coeff_fAdd_X_eq_of_coeff_eq` transfers the computation to `inverseTrunc F k`; finally `inverseTrunc_fAdd_coeff_eq_zero` gives the result.
- **Hypotheses**: `CommRing R`.
- **Uses from project**: `FormalGroup.inverse_constantCoeff`, `FormalGroup.inverseTrunc_constantCoeff`, `FormalGroup.coeff_inverseTrunc_of_le`, `FormalGroup.coeff_fAdd_X_eq_of_coeff_eq`, `FormalGroup.inverseTrunc_fAdd_coeff_eq_zero`
- **Used by**: unused in this file; referenced in `EvalGroup.lean` as the key identity for the formal inverse action.
- **Visibility**: public
- **Lines**: 647–668 (proof: ~21 lines)
- **Notes**: The capstone theorem of the file. Referenced from `EvalGroup.lean` (lines 43, 589, 911).

---

## Cross-reference summary

**Used by 3+ declarations within this file** (key internal API):
- `FormalGroup.inverseTrunc_constantCoeff` — used by `inverseTrunc_hasSubst`, `inverseTrunc_fAdd_coeff_eq_zero`, `fAdd_X_inverse_eq_zero`
- `FormalGroup.coeff_fAdd_X_eq_of_coeff_eq` — used by `inverseTrunc_fAdd_coeff_eq_zero`, `fAdd_X_inverse_eq_zero` (also used in setup inside those proofs with multiple calls)
- `FormalGroup.coeff_inverseTrunc_succ_of_le` — used by `coeff_inverseTrunc_of_le`, `inverseTrunc_fAdd_coeff_eq_zero`

**Declarations unused within this file** (API for other files or dead code):
- `FormalGroup.inverseTrunc_hasSubst`
- `FormalGroup.inverse_hasSubst`
- `FormalGroup.inverse_coeff_one`

**No `sorry`** anywhere in the file.

**No `set_option maxHeartbeats`** (only `set_option linter.dupNamespace false` at line 44).
