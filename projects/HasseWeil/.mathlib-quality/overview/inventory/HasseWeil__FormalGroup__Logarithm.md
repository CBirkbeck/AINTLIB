# Inventory: ./HasseWeil/FormalGroup/Logarithm.lean

**File**: `HasseWeil/FormalGroup/Logarithm.lean`
**Lines**: 1629
**Imports**: `HasseWeil.FormalGroup.InvariantDiff`, `Mathlib.Algebra.Module.Rat`
**Namespace**: `HasseWeil.FormalGroup`
**Global options**: `set_option linter.dupNamespace false` (line 32)
**Sorries**: none

---

## Section 1: Formal Logarithm definition and basic coefficients (lines 48–93)

### `noncomputable def FormalGroup.log`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : PowerSeries R`
- **What**: The formal logarithm of a formal group F, defined as the antiderivative of the normalized invariant differential: `log_F(T) = ∑_{n≥1} (1/n) • (coeff_{n-1} ω_F) • T^n`.
- **How**: Direct coefficient-by-coefficient definition via `PowerSeries.mk`; the n=0 coefficient is forced to 0, and coefficient at n+1 is `(n+1 : ℚ)⁻¹ • coeff n F.normalizedDifferential.toSeries`.
- **Hypotheses**: `R` a commutative ring with `Module ℚ R` (so rational scalars exist).
- **Uses from project**: `FormalGroup` structure, `FormalGroup.normalizedDifferential`, `InvariantDifferential.toSeries`.
- **Used by**: `log_coeff_succ`, `log_coeff_zero`, `log_constantCoeff`, `log_coeff_one`, `FormalGroup.exp`, many downstream.
- **Visibility**: public
- **Lines**: 48–54 (body: 7 lines)

---

### `theorem FormalGroup.log_coeff_succ`
- **Type**: `(F : FormalGroup R) [Module ℚ R] (n : ℕ) : PowerSeries.coeff (n + 1) F.log = ((n + 1 : ℚ)⁻¹) • PowerSeries.coeff n F.normalizedDifferential.toSeries`
- **What**: Explicit formula for the (n+1)-th coefficient of log_F: it equals (1/(n+1)) times the n-th coefficient of the invariant differential.
- **How**: Direct `simp [FormalGroup.log, PowerSeries.coeff_mk]`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.log`.
- **Used by**: `log_coeff_one`, `log_coeff_succ_nsmul`, `pderiv_log`, `log_additiveFormalGroup`.
- **Visibility**: public
- **Lines**: 57–61 (proof: 1 line)

---

### `theorem FormalGroup.log_coeff_zero`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : PowerSeries.coeff 0 F.log = 0`
- **What**: The constant coefficient of the formal logarithm is zero.
- **How**: `simp [FormalGroup.log, PowerSeries.coeff_mk]`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.log`.
- **Used by**: `log_constantCoeff`, `log_coeff_one` (indirectly), `exp_coeff_zero`, various.
- **Visibility**: public (`@[simp]`)
- **Lines**: 65–67 (proof: 1 line)

---

### `theorem FormalGroup.log_constantCoeff`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : PowerSeries.constantCoeff R F.log = 0`
- **What**: The constant term `constantCoeff (log F) = 0`; reformulation of `log_coeff_zero` using the constantCoeff spelling.
- **How**: Rewrite `← PowerSeries.coeff_zero_eq_constantCoeff_apply` then exact `log_coeff_zero`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.log_coeff_zero`.
- **Used by**: `compInverseOfUnit_constantCoeff`, `constantCoeff_log_subst`, `logHomOfLogPreservesAdd`, many others.
- **Visibility**: public (`@[simp]`)
- **Lines**: 71–74 (proof: 2 lines)

---

### `theorem FormalGroup.log_coeff_one`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : PowerSeries.coeff 1 F.log = 1`
- **What**: The linear coefficient of log_F is 1, i.e. `log_F(T) = T + O(T²)`.
- **How**: Uses `log_coeff_succ` at n=0 to get `(1⁻¹ : ℚ) • coeff 0 ω_F`; then `inv_one`, `one_smul`; then `normalizedDifferential_isNormalized` to conclude `coeff 0 ω_F = 1`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.log_coeff_succ`, `FormalGroup.normalizedDifferential_isNormalized`.
- **Used by**: Indirectly via `subst_compInverse_eq_X` (need `coeff 1 F.log = 1`).
- **Visibility**: public (`@[simp]`)
- **Lines**: 79–88 (proof: 9 lines)

---

## Section 2: Compositional inverse construction (lines 111–205)

### `noncomputable def compInvTrunc`
- **Type**: `(f : PowerSeries R) : ℕ → PowerSeries R`
- **What**: Iterative truncation of the compositional inverse: `compInvTrunc f 0 = 0`, and `compInvTrunc f (n+1) = compInvTrunc f n + C c * X^(n+1)` where c is chosen to force the (n+1)-th coefficient of `f ∘ compInvTrunc f (n+1)` to equal the Kronecker delta `[n+1 = 1]`.
- **How**: Recursive definition by `ℕ`-recursion; the correction `c` equals `1 - coeff 1 (subst prev f)` if n+1=1, else `-coeff (n+1) (subst prev f)`.
- **Hypotheses**: None beyond `CommRing R`.
- **Uses from project**: None (pure `PowerSeries` API).
- **Used by**: `compInvCoeff`, `compInvTrunc_zero`, `coeff_compInvTrunc_succ_of_le`, `coeff_compInvTrunc_of_le`, `compInvTrunc_constantCoeff`, `compInvTrunc_hasSubst`, `compInvTrunc_subst_coeff_eq`.
- **Visibility**: public
- **Lines**: 111–119 (body: 9 lines)

---

### `noncomputable def compInvCoeff`
- **Type**: `(f : PowerSeries R) (n : ℕ) : R`
- **What**: The n-th stable coefficient of the compositional inverse: `coeff n (compInvTrunc f n)`.
- **How**: One-liner: `PowerSeries.coeff n (compInvTrunc f n)`.
- **Hypotheses**: None.
- **Uses from project**: `compInvTrunc`.
- **Used by**: `compInverse` (via `PowerSeries.mk`), `compInvCoeff_zero`, `coeff_compInvTrunc_of_le`.
- **Visibility**: public
- **Lines**: 122–123 (body: 1 line)

---

### `noncomputable def compInverse`
- **Type**: `(f : PowerSeries R) : PowerSeries R`
- **What**: The formal compositional inverse of f, assembled coefficient-by-coefficient: `(compInverse f).coeff n = compInvCoeff f n`.
- **How**: `PowerSeries.mk (compInvCoeff f)`.
- **Hypotheses**: None.
- **Uses from project**: `compInvCoeff`.
- **Used by**: `compInverse_coeff_zero`, `compInverse_constantCoeff`, `compInverse_coeff_one`, `compInverse_hasSubst`, `subst_compInverse_eq_X`, `FormalGroup.exp`, `compInverseOfUnit`.
- **Visibility**: public
- **Lines**: 137–138 (body: 1 line)

---

### `theorem compInvTrunc_zero`
- **Type**: `(f : PowerSeries R) : compInvTrunc f 0 = 0`
- **What**: The base case: the 0-th truncation is the zero series.
- **How**: `rfl` (by definition).
- **Hypotheses**: None.
- **Uses from project**: `compInvTrunc`.
- **Used by**: `compInvCoeff_zero`, `compInverse_coeff_zero` (transitively), `compInverse_coeff_one`.
- **Visibility**: public (`@[simp]`)
- **Lines**: 142–143 (proof: 1 line)

---

### `theorem compInvCoeff_zero`
- **Type**: `(f : PowerSeries R) : compInvCoeff f 0 = 0`
- **What**: The 0-th stable coefficient is zero.
- **How**: `simp [compInvCoeff]`.
- **Hypotheses**: None.
- **Uses from project**: `compInvCoeff`.
- **Used by**: `compInverse_coeff_zero`.
- **Visibility**: public (`@[simp]`)
- **Lines**: 147–148 (proof: 1 line)

---

### `theorem compInverse_coeff_zero`
- **Type**: `(f : PowerSeries R) : PowerSeries.coeff 0 (compInverse f) = 0`
- **What**: The constant coefficient of the compositional inverse is 0.
- **How**: `simp [compInverse]`.
- **Hypotheses**: None.
- **Uses from project**: `compInverse`.
- **Used by**: `compInverse_constantCoeff`.
- **Visibility**: public (`@[simp]`)
- **Lines**: 152–154 (proof: 2 lines)

---

### `theorem compInverse_constantCoeff`
- **Type**: `(f : PowerSeries R) : PowerSeries.constantCoeff R (compInverse f) = 0`
- **What**: `constantCoeff (compInverse f) = 0`.
- **How**: Rewrites via `PowerSeries.coeff_zero_eq_constantCoeff_apply` then `compInverse_coeff_zero`.
- **Hypotheses**: None.
- **Uses from project**: `compInverse_coeff_zero`.
- **Used by**: `compInverse_hasSubst`, `subst_compInverse_eq_X`, `compInverseOfUnit` (via scaling).
- **Visibility**: public (`@[simp]`)
- **Lines**: 158–161 (proof: 2 lines)

---

### `private theorem coeff_one_subst_zero`
- **Type**: `(f : PowerSeries R) : PowerSeries.coeff 1 (PowerSeries.subst (0 : PowerSeries R) f) = 0`
- **What**: The linear coefficient of `f` substituted at 0 is zero; auxiliary for `compInverse_coeff_one`.
- **How**: Uses `PowerSeries.coeff_subst'` with `HasSubst.zero'`, then `finsum_eq_zero_of_forall_eq_zero`; for d=0 shows `coeff 1 (0^0) = coeff 1 1 = 0`, for d≠0 uses `zero_pow`.
- **Hypotheses**: None.
- **Uses from project**: None (pure mathlib).
- **Used by**: `compInverse_coeff_one`.
- **Visibility**: private
- **Lines**: 165–181 (proof: 17 lines)

---

### `theorem compInverse_coeff_one`
- **Type**: `(f : PowerSeries R) : PowerSeries.coeff 1 (compInverse f) = 1`
- **What**: The linear coefficient of `compInverse f` is always 1, regardless of f; because the iterative construction forces `c = 1 - 0 = 1` at step 1.
- **How**: Unfolds to `compInvCoeff f 1 = coeff 1 (compInvTrunc f 1)`, then expands the recursive definition, uses `compInvTrunc_zero` and `coeff_one_subst_zero` to reduce to `coeff 1 (C 1 * X^1) = 1` (by simp).
- **Hypotheses**: None.
- **Uses from project**: `compInvTrunc`, `compInvTrunc_zero`, `coeff_one_subst_zero`.
- **Used by**: `subst_compInverse_eq_X` (needs linear coeff = 1), `compInverseOfUnit_coeff_one`.
- **Visibility**: public (`@[simp]`)
- **Lines**: 188–206 (proof: 19 lines)

---

## Section 3: Stabilisation lemmas for CompInverseProof (lines 231–535)

### `theorem coeff_compInvTrunc_succ_of_le`
- **Type**: `(f : PowerSeries R) (n k : ℕ) (hk : k ≤ n) : PowerSeries.coeff k (compInvTrunc f (n + 1)) = PowerSeries.coeff k (compInvTrunc f n)`
- **What**: Lower coefficients are unchanged when adding the (n+1)-th correction monomial: `compInvTrunc f (n+1)` and `compInvTrunc f n` agree in degrees ≤ n.
- **How**: Unfolds the recursive step; uses `PowerSeries.coeff_C_mul_X_pow` + `if_neg (k ≠ n+1)` to drop the correction.
- **Hypotheses**: `k ≤ n`.
- **Uses from project**: `compInvTrunc`.
- **Used by**: `coeff_compInvTrunc_of_le`, `compInvTrunc_subst_coeff_eq`.
- **Visibility**: public
- **Lines**: 238–248 (proof: 11 lines)

---

### `theorem coeff_compInvTrunc_of_le`
- **Type**: `(f : PowerSeries R) (n k : ℕ) (hk : k ≤ n) : PowerSeries.coeff k (compInvTrunc f n) = compInvCoeff f k`
- **What**: For k ≤ n, the k-th coefficient of `compInvTrunc f n` has already stabilised to the limit `compInvCoeff f k`.
- **How**: Induction on n; base case is `compInvCoeff` definition; inductive step splits on k ≤ n-1 (use `coeff_compInvTrunc_succ_of_le`) vs k = n+1 (rfl).
- **Hypotheses**: `k ≤ n`.
- **Uses from project**: `compInvTrunc`, `compInvCoeff`, `coeff_compInvTrunc_succ_of_le`.
- **Used by**: `compInvTrunc_constantCoeff`, `subst_compInverse_eq_X`.
- **Visibility**: public
- **Lines**: 252–267 (proof: 16 lines)

---

### `theorem compInvTrunc_constantCoeff`
- **Type**: `(f : PowerSeries R) (n : ℕ) : PowerSeries.constantCoeff R (compInvTrunc f n) = 0`
- **What**: Every truncation `compInvTrunc f n` has zero constant coefficient.
- **How**: Via `coeff_compInvTrunc_of_le` at k=0, then `compInvCoeff_zero`.
- **Hypotheses**: None.
- **Uses from project**: `compInvTrunc`, `coeff_compInvTrunc_of_le`.
- **Used by**: `compInvTrunc_hasSubst`, `coeff_subst_eq_of_coeff_eq` (via hasSubst), `compInvTrunc_subst_coeff_eq`.
- **Visibility**: public
- **Lines**: 271–275 (proof: 4 lines)

---

### `theorem compInvTrunc_hasSubst`
- **Type**: `(f : PowerSeries R) (n : ℕ) : PowerSeries.HasSubst (compInvTrunc f n)`
- **What**: Each truncation admits substitution (zero constant coefficient hypothesis is satisfied).
- **How**: `PowerSeries.HasSubst.of_constantCoeff_zero'` applied to `compInvTrunc_constantCoeff`.
- **Hypotheses**: None.
- **Uses from project**: `compInvTrunc_constantCoeff`.
- **Used by**: `compInvTrunc_subst_coeff_eq` (indirectly via coeff_subst_eq_of_coeff_eq).
- **Visibility**: public
- **Lines**: 279–281 (proof: 1 line)

---

### `theorem compInverse_hasSubst`
- **Type**: `(f : PowerSeries R) : PowerSeries.HasSubst (compInverse f)`
- **What**: `compInverse f` admits substitution.
- **How**: `PowerSeries.HasSubst.of_constantCoeff_zero'` applied to `compInverse_constantCoeff`.
- **Hypotheses**: None.
- **Uses from project**: `compInverse_constantCoeff`.
- **Used by**: `subst_compInverseOfUnit_eq_X`.
- **Visibility**: public
- **Lines**: 285–287 (proof: 1 line)

---

### `theorem coeff_pow_eq_of_coeff_eq`
- **Type**: `(g₁ g₂ : PowerSeries R) (n : ℕ) (hg : ∀ j ≤ n, coeff j g₁ = coeff j g₂) (d : ℕ) : ∀ k ≤ n, coeff k (g₁ ^ d) = coeff k (g₂ ^ d)`
- **What**: If two power series agree up to degree n, then so do their d-th powers (at all degrees ≤ n).
- **How**: Induction on d; the inductive step uses `coeff_mul` to expand and `Finset.sum_congr` with the IH on each (i,j) with i+j = k ≤ n.
- **Hypotheses**: `∀ j ≤ n, coeff j g₁ = coeff j g₂`.
- **Uses from project**: None.
- **Used by**: `coeff_subst_eq_of_coeff_eq`.
- **Visibility**: public
- **Lines**: 292–312 (proof: 21 lines)

---

### `theorem coeff_subst_eq_of_coeff_eq`
- **Type**: `(f g₁ g₂ : PowerSeries R) (h1 : constantCoeff g₁ = 0) (h2 : constantCoeff g₂ = 0) (n : ℕ) (hg : ∀ j ≤ n, coeff j g₁ = coeff j g₂) (k : ℕ) (hk : k ≤ n) : coeff k (subst g₁ f) = coeff k (subst g₂ f)`
- **What**: Substitution stabilisation: if two series with zero constant coefficient agree up to degree n, substituting them into f gives the same coefficients up to degree n.
- **How**: Expands both sides via `coeff_subst'`, applies `finsum_congr`; uses `coeff_pow_eq_of_coeff_eq` when d ≤ k, and `PowerSeries.le_order_pow_of_constantCoeff_eq_zero` + `coeff_of_lt_order` when d > k.
- **Hypotheses**: Both g₁, g₂ have zero constant coefficient; they agree to degree n; k ≤ n.
- **Uses from project**: `coeff_pow_eq_of_coeff_eq`.
- **Visibility**: public
- **Lines**: 318–344 (proof: 27 lines)
- **Notes**: Proof >30 lines boundary (27 lines, just under).

---

### `theorem coeff_pow_eq_zero_of_gt`
- **Type**: `(g : PowerSeries R) (hg : constantCoeff g = 0) (k d : ℕ) (hdk : k < d) : coeff k (g ^ d) = 0`
- **What**: If g has zero constant term, then coeff k (g^d) = 0 for k < d (the order of g^d is ≥ d).
- **How**: Uses `PowerSeries.le_order_pow_of_constantCoeff_eq_zero` and `coeff_of_lt_order`.
- **Hypotheses**: `constantCoeff g = 0`, `k < d`.
- **Uses from project**: None.
- **Used by**: `coeff_subst_eq_of_coeff_eq` (inline, not by name).
- **Visibility**: public
- **Lines**: 355–361 (proof: 7 lines)
- **Notes**: Slightly redundant with the inline proof inside `coeff_subst_eq_of_coeff_eq`.

---

### `theorem monomial_constantCoeff_zero`
- **Type**: `(n : ℕ) (c : R) : constantCoeff (PowerSeries.C c * PowerSeries.X ^ (n + 1)) = 0`
- **What**: The monomial `C c * X^(n+1)` has zero constant coefficient.
- **How**: `PowerSeries.coeff_C_mul_X_pow` + simp.
- **Hypotheses**: None.
- **Uses from project**: None.
- **Used by**: `coeff_subst_add_monomial`.
- **Visibility**: public
- **Lines**: 367–370 (proof: 3 lines)

---

### `theorem monomial_pow_eq`
- **Type**: `(n : ℕ) (c : R) (j : ℕ) : (PowerSeries.C c * PowerSeries.X ^ (n + 1)) ^ j = PowerSeries.C (c ^ j) * PowerSeries.X ^ (j * (n + 1))`
- **What**: The j-th power of the monomial `C c * X^(n+1)` equals `C (c^j) * X^(j*(n+1))`.
- **How**: Uses `mul_pow`, `← map_pow` (for C), `← pow_mul`, `mul_comm`.
- **Hypotheses**: None.
- **Uses from project**: None.
- **Used by**: `coeff_monomial_pow_high`, `coeff_add_monomial_pow_eq` (in the high-m term vanishing).
- **Visibility**: public
- **Lines**: 374–383 (proof: 10 lines)

---

### `theorem coeff_monomial_pow_high`
- **Type**: `(n : ℕ) (c : R) (i : ℕ) (hi : 2 ≤ i) : coeff (n + 1) ((C c * X ^ (n + 1)) ^ i) = 0`
- **What**: For i ≥ 2, the monomial `C c * X^(n+1)` raised to i-th power has zero coefficient at degree n+1 (since its order is ≥ 2(n+1) > n+1).
- **How**: Applies `monomial_pow_eq`, then `coeff_C_mul_X_pow`; the equality n+1 = i*(n+1) with i≥2 is contradicted by `nlinarith`.
- **Hypotheses**: `2 ≤ i`.
- **Uses from project**: `monomial_pow_eq`.
- **Used by**: `coeff_add_monomial_pow_eq` (the high-m sum).
- **Visibility**: public
- **Lines**: 388–395 (proof: 8 lines)

---

### `theorem coeff_add_monomial_pow_eq`
- **Type**: `(g : PowerSeries R) (hg : constantCoeff g = 0) (n : ℕ) (c : R) (d : ℕ) : coeff (n+1) ((g + C c * X^(n+1))^d) = coeff (n+1) (g^d) + (if d = 1 then c else 0)`
- **What**: The key monomial-correction formula: adding `C c * X^(n+1)` to g shifts the (n+1)-th coefficient by c exactly when d=1, and leaves higher powers unchanged.
- **How**: Expands via `add_pow h g d` (binomial theorem); extracts terms m=0 and m=1 by `Finset.sum_range_succ`; shows the sum over m≥2 vanishes using `monomial_pow_eq` + `coeff_C_mul_X_pow` + `nlinarith`; verified by cases d=0, d=1, d≥2. This is the most computationally involved lemma in the file.
- **Hypotheses**: `constantCoeff g = 0`.
- **Uses from project**: `monomial_pow_eq`, `coeff_monomial_pow_high`.
- **Used by**: `coeff_subst_add_monomial`.
- **Visibility**: public
- **Lines**: 400–536 (proof: **137 lines**)
- **Notes**: Longest proof in the file at 137 lines; three-way case split (d=0, d=1, d≥2) with the d≥2 case requiring manual finset splitting.

---

### `theorem coeff_subst_add_monomial`
- **Type**: `(f g : PowerSeries R) (n : ℕ) (c : R) (hg : constantCoeff g = 0) : coeff (n+1) (subst (g + C c * X^(n+1)) f) = coeff (n+1) (subst g f) + c * coeff 1 f`
- **What**: When a monomial correction `C c * X^(n+1)` is added to g, the (n+1)-th coefficient of `subst _ f` increases by exactly `c * coeff 1 f`.
- **How**: Expands both sides via `coeff_subst'`; applies `coeff_add_monomial_pow_eq` for each d; uses `finsum_add_distrib` and `finsum_eq_single` to isolate the d=1 term.
- **Hypotheses**: `constantCoeff g = 0`.
- **Uses from project**: `monomial_constantCoeff_zero`, `coeff_add_monomial_pow_eq`.
- **Used by**: `compInvTrunc_subst_coeff_eq`.
- **Visibility**: public
- **Lines**: 542–582 (proof: **41 lines**)

---

### `theorem compInvTrunc_subst_coeff_eq`
- **Type**: `(f : PowerSeries R) (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1) (n k : ℕ) (hk : k ≤ n) : coeff k (subst (compInvTrunc f n) f) = (if k = 1 then 1 else 0)`
- **What**: The core invariant: for k ≤ n, the k-th coefficient of `f(compInvTrunc f n)` equals the Kronecker delta `[k = 1]` — the iterative construction maintains the right compositional-inverse property up to each truncation.
- **How**: Induction on n. Base (k=0): uses `PowerSeries.constantCoeff_subst_eq_zero`. Inductive step (k ≤ n): uses `coeff_subst_eq_of_coeff_eq` + `coeff_compInvTrunc_succ_of_le` to reduce to IH. At k = n+1: unfolds the recursive step, applies `coeff_subst_add_monomial`, `h1`, then `split_ifs` + `ring`.
- **Hypotheses**: `constantCoeff f = 0`, `coeff 1 f = 1`, `k ≤ n`.
- **Uses from project**: `compInvTrunc`, `coeff_compInvTrunc_succ_of_le`, `compInvTrunc_constantCoeff`, `coeff_subst_eq_of_coeff_eq`, `coeff_subst_add_monomial`.
- **Used by**: `subst_compInverse_eq_X`.
- **Visibility**: public
- **Lines**: 595–657 (proof: **63 lines**)

---

### `theorem subst_compInverse_eq_X`
- **Type**: `(f : PowerSeries R) (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1) : subst (compInverse f) f = X`
- **What**: The compositional inverse identity: `compInverse f` is a true right inverse of f.
- **How**: `ext k`; case k=0 by `constantCoeff_subst_eq_zero`; case k≥1 by stabilisation (`coeff_compInvTrunc_of_le` shows `compInverse f` and `compInvTrunc f k` agree up to k), then `coeff_subst_eq_of_coeff_eq` reduces to `compInvTrunc_subst_coeff_eq`, and `coeff_X` finishes.
- **Hypotheses**: `constantCoeff f = 0`, `coeff 1 f = 1`.
- **Uses from project**: `compInverse`, `compInverse_constantCoeff`, `compInvTrunc_constantCoeff`, `coeff_compInvTrunc_of_le`, `coeff_subst_eq_of_coeff_eq`, `compInvTrunc_subst_coeff_eq`.
- **Used by**: `subst_compInverseOfUnit_eq_X`.
- **Visibility**: public
- **Lines**: 663–693 (proof: **31 lines**)

---

## Section 4: Unit-coefficient compositional inverse (lines 714–867)

### `private theorem scaled_constantCoeff_zero`
- **Type**: `(f : PowerSeries R) (v : R) (h0 : constantCoeff f = 0) : constantCoeff (v • f) = 0`
- **What**: Scaling a series with zero constant term preserves that property.
- **How**: `smul_zero`.
- **Hypotheses**: `constantCoeff f = 0`.
- **Uses from project**: None.
- **Used by**: `subst_compInverseOfUnit_eq_X`.
- **Visibility**: private
- **Lines**: 714–719 (proof: 5 lines)

---

### `private theorem scaled_coeff_one`
- **Type**: `(f : PowerSeries R) (v : R) : coeff 1 (v • f) = v * coeff 1 f`
- **What**: The linear coefficient of a scalar multiple `v • f` is `v * coeff 1 f`.
- **How**: `smul_eq_mul`.
- **Hypotheses**: None.
- **Uses from project**: None.
- **Used by**: `subst_compInverseOfUnit_eq_X`.
- **Visibility**: private
- **Lines**: 723–726 (proof: 3 lines)

---

### `private theorem smul_X_constantCoeff_zero`
- **Type**: `(v : R) : constantCoeff (v • PowerSeries.X : PowerSeries R) = 0`
- **What**: `v • X` has zero constant coefficient, so it admits substitution.
- **How**: `coeff_zero_X`, `smul_zero`.
- **Hypotheses**: None.
- **Uses from project**: None.
- **Used by**: `compInverseOfUnit_constantCoeff`, `subst_compInverseOfUnit_eq_X`.
- **Visibility**: private
- **Lines**: 730–734 (proof: 4 lines)

---

### `noncomputable def compInverseOfUnit`
- **Type**: `(f : PowerSeries R) (u : R) (hu : IsUnit u) : PowerSeries R`
- **What**: The compositional inverse of f when `coeff 1 f = u` is a unit, constructed by scaling: let `v = u⁻¹`, then `compInverseOfUnit f u hu = subst (v • X) (compInverse (v • f))`.
- **How**: Direct term `PowerSeries.subst (v • X) (compInverse (v • f))` where `v = (hu.unit⁻¹ : Rˣ)`.
- **Hypotheses**: `IsUnit u`.
- **Uses from project**: `compInverse`.
- **Used by**: `compInverseOfUnit_constantCoeff`, `compInverseOfUnit_hasSubst`, `subst_compInverseOfUnit_eq_X`, `compInverseOfUnit_coeff_one`.
- **Visibility**: public
- **Lines**: 754–757 (body: 3 lines)

---

### `theorem compInverseOfUnit_constantCoeff`
- **Type**: `(f : PowerSeries R) (u : R) (hu : IsUnit u) : constantCoeff (compInverseOfUnit f u hu) = 0`
- **What**: The compInverseOfUnit has zero constant coefficient.
- **How**: Applies `PowerSeries.constantCoeff_subst_eq_zero` with `smul_X_constantCoeff_zero` and `compInverse_constantCoeff`.
- **Hypotheses**: `IsUnit u`.
- **Uses from project**: `compInverseOfUnit`, `smul_X_constantCoeff_zero`, `compInverse_constantCoeff`.
- **Used by**: `compInverseOfUnit_hasSubst`.
- **Visibility**: public (`@[simp]`)
- **Lines**: 762–769 (proof: 7 lines)

---

### `theorem compInverseOfUnit_hasSubst`
- **Type**: `(f : PowerSeries R) (u : R) (hu : IsUnit u) : PowerSeries.HasSubst (compInverseOfUnit f u hu)`
- **What**: `compInverseOfUnit f u hu` admits substitution.
- **How**: `PowerSeries.HasSubst.of_constantCoeff_zero'` applied to `compInverseOfUnit_constantCoeff`.
- **Hypotheses**: `IsUnit u`.
- **Uses from project**: `compInverseOfUnit_constantCoeff`.
- **Used by**: (not used elsewhere in this file — external API).
- **Visibility**: public
- **Lines**: 773–775 (proof: 1 line)
- **Notes**: Declared for external use; not called within this file.

---

### `theorem subst_compInverseOfUnit_eq_X`
- **Type**: `(f : PowerSeries R) (u : R) (hu : IsUnit u) (h0 : constantCoeff f = 0) (h1 : coeff 1 f = u) : subst (compInverseOfUnit f u hu) f = X`
- **What**: The unit-case compositional inverse identity: `subst (compInverseOfUnit f u hu) f = X`.
- **How**: Scales f by `v = u⁻¹`; applies the monic case `subst_compInverse_eq_X` to `v • f`; uses `PowerSeries.subst_smul` to get `subst g̃ f = u • X`; then reparametrises via `subst_comp_subst_apply`, `subst_smul`, `subst_X`, and `mul_smul`/`huv` to conclude `u • (v • X) = X`.
- **Hypotheses**: `IsUnit u`, `constantCoeff f = 0`, `coeff 1 f = u`.
- **Uses from project**: `compInverseOfUnit`, `compInverse_hasSubst`, `scaled_constantCoeff_zero`, `scaled_coeff_one`, `subst_compInverse_eq_X`, `smul_X_constantCoeff_zero`.
- **Used by**: (external API — not used in this file).
- **Visibility**: public
- **Lines**: 784–847 (proof: **64 lines**)

---

### `theorem compInverseOfUnit_coeff_one`
- **Type**: `(f : PowerSeries R) (u : R) (hu : IsUnit u) : coeff 1 (compInverseOfUnit f u hu) = ((hu.unit⁻¹ : Rˣ) : R)`
- **What**: The linear coefficient of `compInverseOfUnit f u hu` is the inverse of u.
- **How**: Uses `PowerSeries.rescale_eq_subst` and `coeff_rescale` (substituting `v • X` is rescaling by v); then `compInverse_coeff_one` gives coeff 1 of the inner series = 1.
- **Hypotheses**: `IsUnit u`.
- **Uses from project**: `compInverseOfUnit`, `compInverse_coeff_one`.
- **Used by**: (external API — not used in this file).
- **Visibility**: public (`@[simp]`)
- **Lines**: 858–867 (proof: 9 lines)

---

## Section 5: Formal exponential (lines 878–893)

### `noncomputable def FormalGroup.exp`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : PowerSeries R`
- **What**: The formal exponential of a formal group F, defined as the compositional inverse of `log_F`.
- **How**: `compInverse F.log`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `compInverse`, `FormalGroup.log`.
- **Used by**: `exp_coeff_zero`, `exp_constantCoeff`.
- **Visibility**: public
- **Lines**: 878–880 (body: 1 line)

---

### `theorem FormalGroup.exp_coeff_zero`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : coeff 0 F.exp = 0`
- **What**: The constant coefficient of exp_F is zero.
- **How**: `simp [FormalGroup.exp]`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.exp`.
- **Used by**: `exp_constantCoeff`.
- **Visibility**: public (`@[simp]`)
- **Lines**: 884–886 (proof: 1 line)

---

### `theorem FormalGroup.exp_constantCoeff`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : constantCoeff R F.exp = 0`
- **What**: `constantCoeff (exp F) = 0`.
- **How**: Rewrites via `coeff_zero_eq_constantCoeff_apply` then `exp_coeff_zero`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.exp_coeff_zero`.
- **Used by**: (not used in this file — external API).
- **Visibility**: public (`@[simp]`)
- **Lines**: 890–893 (proof: 3 lines)

---

## Section 6: Silverman IV.5 corollaries (lines 908–939)

### `theorem FormalGroup.commutative`
- **Type**: `(F : FormalGroup R) : MvPowerSeries.subst (![X 1, X 0]) F.toSeries = F.toSeries`
- **What**: Every formal group (as defined in this project) is commutative: `F(X, Y) = F(Y, X)`.
- **How**: `F.comm` (commutativity is axiomatic in the `FormalGroup` structure).
- **Hypotheses**: None.
- **Uses from project**: `FormalGroup.comm`.
- **Used by**: `commutative_of_torsion_free`.
- **Visibility**: public
- **Lines**: 908–912 (proof: 1 line)
- **Notes**: Wrapper exposing the `FormalGroup.comm` field directly; the classical non-trivial statement (that torsion-free ℤ-algebras force commutativity) is bypassed since commutativity is axiomatic here.

---

### `theorem FormalGroup.commutative_of_torsion_free`
- **Type**: `(F : FormalGroup R) [NoZeroSMulDivisors ℤ R] : MvPowerSeries.subst (![X 1, X 0]) F.toSeries = F.toSeries`
- **What**: Same commutativity statement but with a torsion-free hypothesis (which is not actually needed since commutativity is axiomatic).
- **How**: `F.commutative`.
- **Hypotheses**: `NoZeroSMulDivisors ℤ R` (not used).
- **Uses from project**: `FormalGroup.commutative`.
- **Used by**: (not used in this file).
- **Visibility**: public
- **Lines**: 917–922 (proof: 1 line)
- **Notes**: The `NoZeroSMulDivisors ℤ R` hypothesis is UNUSED — this is a vestigial hypothesis from the classical version.

---

### `theorem FormalGroup.log_coeff_succ_nsmul`
- **Type**: `(F : FormalGroup R) [Module ℚ R] (n : ℕ) : (n + 1) • coeff (n+1) F.log = coeff n F.normalizedDifferential.toSeries`
- **What**: The integral identity: `(n+1) · log_F.coeff(n+1) = ω_F.coeff n` (Silverman IV.5.4 coefficient bound).
- **How**: Rewrites via `log_coeff_succ`; uses `← Nat.cast_smul_eq_nsmul ℚ` and `smul_smul` to get `(n+1 : ℚ) * (n+1 : ℚ)⁻¹ = 1` via `field_simp`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.log_coeff_succ`.
- **Used by**: (not used in this file — external API).
- **Visibility**: public
- **Lines**: 932–939 (proof: 7 lines)

---

## Section 7: LogPreservesAdd (lines 989–1552)

### `def FormalGroup.LogPreservesAdd`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : Prop`
- **What**: The proposition that log_F is a formal group homomorphism to the additive formal group: `log_F(F(X, Y)) = log_F(X) + log_F(Y)`.
- **How**: Direct propositional definition.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.log`, `FormalGroup.toSeries`.
- **Used by**: `logPreservesAdd_constantCoeff`, `logPreservesAdd`, `logHomOfLogPreservesAdd`, `additiveFormalGroup_logPreservesAdd`, `logHom`.
- **Visibility**: public
- **Lines**: 989–992 (body: 3 lines)

---

### `theorem FormalGroup.constantCoeff_log_subst`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : MvPowerSeries.constantCoeff (subst F.toSeries F.log : MvPowerSeries (Fin 2) R) = 0`
- **What**: The bivariate series `log_F(F(X,Y))` has zero constant coefficient.
- **How**: `PowerSeries.constantCoeff_subst_eq_zero` using `HasseWeil.FG.constantCoeff_FG_toSeries F` and `F.log_constantCoeff`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.log_constantCoeff`, `HasseWeil.FG.constantCoeff_FG_toSeries`.
- **Used by**: `logPreservesAdd_constantCoeff`.
- **Visibility**: public
- **Lines**: 1000–1004 (proof: 4 lines)

---

### `theorem FormalGroup.constantCoeff_log_subst_X_add`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : constantCoeff (subst (X 0) F.log + subst (X 1) F.log : MvPowerSeries (Fin 2) R) = 0`
- **What**: The bivariate RHS `log_F(X) + log_F(Y)` has zero constant coefficient.
- **How**: `map_add` then twice `PowerSeries.constantCoeff_subst_eq_zero` with `log_constantCoeff`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.log_constantCoeff`.
- **Used by**: `logPreservesAdd_constantCoeff`.
- **Visibility**: public
- **Lines**: 1010–1017 (proof: 7 lines)

---

### `theorem FormalGroup.logPreservesAdd_constantCoeff`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : constantCoeff (subst F.toSeries F.log : ...) = constantCoeff (subst (X 0) F.log + subst (X 1) F.log : ...)`
- **What**: The constant-coefficient case of `LogPreservesAdd` (both sides agree at (0,0)).
- **How**: Rewrites both sides to 0 using `constantCoeff_log_subst` and `constantCoeff_log_subst_X_add`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.constantCoeff_log_subst`, `FormalGroup.constantCoeff_log_subst_X_add`.
- **Used by**: (not used further in this file).
- **Visibility**: public
- **Lines**: 1023–1029 (proof: 3 lines)

---

### `theorem FormalGroup.log_additiveFormalGroup`
- **Type**: `[Module ℚ R] : (additiveFormalGroup R).log = PowerSeries.X`
- **What**: For the additive formal group Ĝ_a, the formal logarithm is the identity series T.
- **How**: `ext n` with case split on n=0,1,n+2; for n=0 and n=1 uses `log_coeff_zero`/`log_coeff_one`; for n+2 uses `log_coeff_succ`, then explicitly computes `dX_at_zero = 1` and `invariantDiff = 1` for Ĝ_a (using `dX_at_zero_mul_invariantDiff`) to show `coeff (n+1) ω = 0`, giving `smul_zero`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.log_coeff_zero`, `FormalGroup.log_coeff_one`, `FormalGroup.log_coeff_succ`, `FormalGroup.dX_at_zero`, `FormalGroup.dX_at_zero_mul_invariantDiff`, `FormalGroup.invariantDiff`.
- **Used by**: `additiveFormalGroup_logPreservesAdd`, `additiveFormalGroup_logHom`.
- **Visibility**: public
- **Lines**: 1039–1105 (proof: **67 lines**)
- **Notes**: The computation of `dX_at_zero` for Ĝ_a requires a detailed coefficient analysis of the Mv-power-series addition map, making this longer than expected.

---

### `theorem FormalGroup.additiveFormalGroup_logPreservesAdd`
- **Type**: `[Module ℚ R] : (additiveFormalGroup R).LogPreservesAdd`
- **What**: Ĝ_a satisfies `LogPreservesAdd`; since `log_{Ĝ_a} = X`, this is immediate from `subst F X = F`.
- **How**: Unfolds `LogPreservesAdd`, rewrites via `log_additiveFormalGroup`, then uses `PowerSeries.subst_X` three times and the definition of `additiveFormalGroup.toSeries`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.LogPreservesAdd`, `FormalGroup.log_additiveFormalGroup`, `HasseWeil.FG.constantCoeff_FG_toSeries`.
- **Used by**: `additiveFormalGroup_logHom`.
- **Visibility**: public
- **Lines**: 1109–1127 (proof: 19 lines)

---

### `theorem FormalGroup.pderiv_log`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : MvPowerSeries.pderiv () F.log = F.invariantDiff`
- **What**: The formal derivative of `log_F` is the normalized invariant differential: `d/dT log_F(T) = ω_F(T)`.
- **How**: `ext n`; uses `MvPowerSeries.coeff_pderiv` to get `(n+1) • coeff(n+1)(log_F)`; then `log_coeff_succ` and `Nat.cast_smul_eq_nsmul ℚ` with `smul_smul` and `field_simp` to cancel `(n+1)*(n+1)⁻¹ = 1`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.log_coeff_succ`.
- **Used by**: `pderiv_LogPreservesAdd_LHS`, `pderiv_LogPreservesAdd_RHS`.
- **Visibility**: public
- **Lines**: 1145–1167 (proof: 23 lines)

---

### `private theorem pderiv_PowerSeries_subst`
- **Type**: `{τ : Type*} (t : τ) {a : MvPowerSeries τ R} (ha : PowerSeries.HasSubst a) (f : PowerSeries R) : pderiv t (subst a f) = pderiv t a * subst a (pderiv () f)`
- **What**: Chain rule for `PowerSeries.subst`: the partial derivative of `f(a)` with respect to variable t is `(∂a/∂t) * f'(a)`.
- **How**: Unfolds `PowerSeries.subst_def`, applies `MvPowerSeries.pderiv_subst` (multivariate chain rule), and simplifies the univ-sum over Unit.
- **Hypotheses**: `PowerSeries.HasSubst a`.
- **Uses from project**: None (pure mathlib).
- **Used by**: `pderiv_LogPreservesAdd_LHS`, `pderiv_LogPreservesAdd_RHS`.
- **Visibility**: private
- **Lines**: 1180–1188 (proof: 9 lines)

---

### `private theorem coeff_zero_of_pderiv_zero_fin2`
- **Type**: `[Module ℚ R] (h : MvPowerSeries (Fin 2) R) (hd : pderiv 0 h = 0) (e : Fin 2 →₀ ℕ) (he : e 0 ≠ 0) : coeff e h = 0`
- **What**: If a bivariate series has zero partial derivative in variable 0, then all coefficients at monomials with positive 0-degree vanish (using torsion-freeness from `Module ℚ R`).
- **How**: Extracts `d = e - single 0 1`; reads off `(d 0 + 1) • coeff e h = 0` from `coeff_pderiv`; cancels via `nsmul_right_injective` using `IsAddTorsionFree.of_module_rat`.
- **Hypotheses**: `Module ℚ R`, `pderiv 0 h = 0`, `e 0 ≠ 0`.
- **Uses from project**: None (purely mathlib; `IsAddTorsionFree.of_module_rat` is a mathlib lemma).
- **Used by**: `eq_zero_of_pderiv_zero_and_const_zero`.
- **Visibility**: private
- **Lines**: 1196–1230 (proof: **35 lines**)

---

### `private theorem eq_zero_of_pderiv_zero_and_const_zero`
- **Type**: `[Module ℚ R] (h : MvPowerSeries (Fin 2) R) (hd : pderiv 0 h = 0) (hc : ∀ b : ℕ, coeff (single 1 b) h = 0) : h = 0`
- **What**: A bivariate series is zero if its partial derivative in variable 0 vanishes and all coefficients at Y-monomials are zero. This is the uniqueness lemma driving the main proof.
- **How**: `ext e`; if e 0 = 0 then e = single 1 (e 1), and `hc` gives the coefficient is zero; if e 0 ≠ 0 use `coeff_zero_of_pderiv_zero_fin2`.
- **Hypotheses**: `Module ℚ R`, `pderiv 0 h = 0`, coefficients at `single 1 b` all zero.
- **Uses from project**: `coeff_zero_of_pderiv_zero_fin2`.
- **Used by**: `logPreservesAdd`.
- **Visibility**: private
- **Lines**: 1234–1252 (proof: 19 lines)

---

### `private theorem pderiv_LogPreservesAdd_LHS`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : pderiv 0 (subst F.toSeries F.log : MvPowerSeries (Fin 2) R) = subst (X 0) F.invariantDiff`
- **What**: The X-derivative of `log_F(F(X,Y))` equals `ω_F(X)` (chain rule + translation invariance IV.4.2).
- **How**: Applies `pderiv_PowerSeries_subst` (chain rule) and `F.pderiv_log`; then `mul_comm` and `F.invariantDiff_translation`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.pderiv_log`, `pderiv_PowerSeries_subst`, `HasseWeil.FG.constantCoeff_FG_toSeries`, `FormalGroup.invariantDiff_translation`.
- **Used by**: `logPreservesAdd`.
- **Visibility**: private
- **Lines**: 1268–1280 (proof: 13 lines)

---

### `private theorem pderiv_LogPreservesAdd_RHS`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : pderiv 0 (subst (X 0) F.log + subst (X 1) F.log : MvPowerSeries (Fin 2) R) = subst (X 0) F.invariantDiff`
- **What**: The X-derivative of `log_F(X) + log_F(Y)` also equals `ω_F(X)`.
- **How**: `pderiv_add`, `pderiv_PowerSeries_subst` twice, `F.pderiv_log`; then `pderiv_X_self 0 = 1` and `pderiv_X_of_ne 0 1 = 0`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.pderiv_log`, `pderiv_PowerSeries_subst`.
- **Used by**: `logPreservesAdd`.
- **Visibility**: private
- **Lines**: 1284–1300 (proof: 17 lines)

---

### `private theorem subst_zero_LogPreservesAdd_LHS`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : subst (![0, X 1]) (subst F.toSeries F.log : MvPowerSeries (Fin 2) R) = subst (X 1) F.log`
- **What**: Setting X=0 in `log_F(F(X,Y))` gives `log_F(Y)`, using the right unit law `F(0, Y) = Y`.
- **How**: `PowerSeries.subst_def`, `MvPowerSeries.subst_comp_subst_apply`, then `F.runit` to reduce `subst ![0, X 1] F.toSeries = X 1`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `HasseWeil.FG.constantCoeff_FG_toSeries`, `FormalGroup.runit`.
- **Used by**: `logPreservesAdd`.
- **Visibility**: private
- **Lines**: 1304–1327 (proof: 24 lines)

---

### `private theorem PowerSeries_subst_zero_of_constantCoeff_zero`
- **Type**: `{τ : Type*} (f : PowerSeries R) (hf : constantCoeff f = 0) : subst (0 : MvPowerSeries τ R) f = 0`
- **What**: Substituting 0 into a series with zero constant coefficient gives the zero series.
- **How**: `coeff_subst`, `finsum_eq_single _ 0`, then `coeff 0 f = 0` from `hf`.
- **Hypotheses**: `constantCoeff f = 0`.
- **Uses from project**: None.
- **Used by**: `subst_zero_LogPreservesAdd_RHS`.
- **Visibility**: private
- **Lines**: 1331–1348 (proof: 18 lines)

---

### `private theorem subst_zero_LogPreservesAdd_RHS`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : subst (![0, X 1]) (subst (X 0) F.log + subst (X 1) F.log : MvPowerSeries (Fin 2) R) = subst (X 1) F.log`
- **What**: Setting X=0 in `log_F(X) + log_F(Y)` gives `log_F(Y)`, since `log_F(0) = 0`.
- **How**: `subst_add`, then the X 0 term goes to zero via `PowerSeries_subst_zero_of_constantCoeff_zero` + `subst_X`; the X 1 term uses `subst_comp_subst_apply` + `subst_X`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.log_constantCoeff`, `PowerSeries_subst_zero_of_constantCoeff_zero`.
- **Used by**: `logPreservesAdd`.
- **Visibility**: private
- **Lines**: 1352–1398 (proof: **47 lines**)

---

### `private theorem coeff_subst_zero_X1_at_single_1`
- **Type**: `(h : MvPowerSeries (Fin 2) R) (b : ℕ) : coeff (single 1 b) (subst (![0, X 1]) h) = coeff (single 1 b) h`
- **What**: Substituting X 0 ↦ 0, X 1 ↦ X 1 into h preserves the coefficients at Y-only monomials.
- **How**: `coeff_subst h0X1 h (single 1 b)` + `finsum_eq_single _ (single 1 b)`; shows d = single 1 b contributes coefficient 1 via `MvPowerSeries.X_pow_eq` + `coeff_monomial_same`; for d ≠ single 1 b the contribution is zero (case split on d 0 = 0 with d 1 ≠ b, or d 0 ≠ 0).
- **Hypotheses**: None.
- **Uses from project**: None.
- **Used by**: `logPreservesAdd`.
- **Visibility**: private
- **Lines**: 1407–1507 (proof: **101 lines**)
- **Notes**: Second longest proof at 101 lines; detailed finsupp product computation.

---

### `theorem FormalGroup.logPreservesAdd`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : F.LogPreservesAdd`
- **What**: **Silverman IV.5.2**: the formal logarithm is a homomorphism `F → Ĝ_a`, i.e. `log_F(F(X,Y)) = log_F(X) + log_F(Y)`.
- **How**: Forms the difference h = LHS − RHS; shows `pderiv 0 h = 0` from `pderiv_LogPreservesAdd_LHS/RHS`; shows `subst ![0, X 1] h = 0` from `subst_zero_LogPreservesAdd_LHS/RHS`; extracts `coeff (single 1 b) h = 0` via `coeff_subst_zero_X1_at_single_1`; concludes `h = 0` via `eq_zero_of_pderiv_zero_and_const_zero`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.LogPreservesAdd`, `pderiv_LogPreservesAdd_LHS`, `pderiv_LogPreservesAdd_RHS`, `subst_zero_LogPreservesAdd_LHS`, `subst_zero_LogPreservesAdd_RHS`, `coeff_subst_zero_X1_at_single_1`, `eq_zero_of_pderiv_zero_and_const_zero`.
- **Used by**: `logHom`.
- **Visibility**: public
- **Lines**: 1510–1552 (proof: **43 lines**)

---

## Section 8: Formal group homomorphism packaging (lines 1568–1629)

### `noncomputable def FormalGroup.logHomOfLogPreservesAdd`
- **Type**: `(F : FormalGroup R) [Module ℚ R] (hlog : F.LogPreservesAdd) : FormalGroupHom F (additiveFormalGroup R)`
- **What**: Packages `log_F` as a `FormalGroupHom F Ĝ_a` given the hypothesis `LogPreservesAdd F`.
- **How**: Provides `toSeries := F.log`, `zero_const := log_constantCoeff`, `preserves_add` from `hlog` by unfolding the additive formal group definition and using `MvPowerSeries.subst_add`, `subst_X`.
- **Hypotheses**: `Module ℚ R`, `F.LogPreservesAdd`.
- **Uses from project**: `FormalGroup.log`, `FormalGroup.log_constantCoeff`, `FormalGroup.LogPreservesAdd`.
- **Used by**: `logHomOfLogPreservesAdd_toSeries`, `additiveFormalGroup_logHom`, `logHom`.
- **Visibility**: public
- **Lines**: 1568–1601 (proof: **34 lines**, def with `where` proof)

---

### `theorem FormalGroup.logHomOfLogPreservesAdd_toSeries`
- **Type**: `(F : FormalGroup R) [Module ℚ R] (hlog : F.LogPreservesAdd) : (F.logHomOfLogPreservesAdd hlog).toSeries = F.log`
- **What**: The underlying series of the packaged homomorphism is `F.log`.
- **How**: `rfl`.
- **Hypotheses**: `Module ℚ R`, `F.LogPreservesAdd`.
- **Uses from project**: `FormalGroup.logHomOfLogPreservesAdd`, `FormalGroup.log`.
- **Used by**: (not used in this file).
- **Visibility**: public (`@[simp]`)
- **Lines**: 1604–1606 (proof: 1 line)

---

### `noncomputable def FormalGroup.additiveFormalGroup_logHom`
- **Type**: `[Module ℚ R] : FormalGroupHom (additiveFormalGroup R) (additiveFormalGroup R)`
- **What**: The identity-as-log formal group homomorphism `Ĝ_a → Ĝ_a` (log of Ĝ_a is the identity).
- **How**: `logHomOfLogPreservesAdd` applied to `additiveFormalGroup_logPreservesAdd`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.logHomOfLogPreservesAdd`, `FormalGroup.additiveFormalGroup_logPreservesAdd`.
- **Used by**: (not used in this file).
- **Visibility**: public
- **Lines**: 1611–1614 (body: 2 lines)

---

### `noncomputable def FormalGroup.logHom`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : FormalGroupHom F (additiveFormalGroup R)`
- **What**: The formal logarithm `log_F : F → Ĝ_a` as a formal group homomorphism (Silverman IV.5.2 packaged).
- **How**: `F.logHomOfLogPreservesAdd F.logPreservesAdd`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.logHomOfLogPreservesAdd`, `FormalGroup.logPreservesAdd`.
- **Used by**: `logHom_toSeries`.
- **Visibility**: public
- **Lines**: 1621–1623 (body: 1 line)

---

### `theorem FormalGroup.logHom_toSeries`
- **Type**: `(F : FormalGroup R) [Module ℚ R] : F.logHom.toSeries = F.log`
- **What**: The underlying series of `logHom` is `F.log`.
- **How**: `rfl`.
- **Hypotheses**: `Module ℚ R`.
- **Uses from project**: `FormalGroup.logHom`, `FormalGroup.log`.
- **Used by**: (not used in this file).
- **Visibility**: public (`@[simp]`)
- **Lines**: 1626–1627 (proof: 1 line)

---

## Summary

| Category | Count |
|---|---|
| Total declarations | 65 |
| `noncomputable def` / `def` | 10 |
| `theorem` (public) | 45 |
| `private theorem` | 10 |
| Instances | 0 |
| Sorries | 0 |
| `set_option maxHeartbeats` | 0 |

**Key API declarations** (used by 3+ others in this file):
- `FormalGroup.log` (many callers)
- `FormalGroup.log_coeff_succ` (≥4 callers)
- `FormalGroup.log_constantCoeff` (≥6 callers)
- `FormalGroup.LogPreservesAdd` (many: definition + all prove/consume it)
- `compInvTrunc` (core of compositional inverse)
- `compInvTrunc_constantCoeff` (≥4 callers)
- `coeff_subst_eq_of_coeff_eq` (core stabilisation engine)
- `monomial_pow_eq` (used in high-order vanishing arguments)
- `subst_compInverse_eq_X` (key theorem, used externally)
- `FormalGroup.logPreservesAdd` (consumed by `logHom`)

**Declarations unused within this file** (external API candidates):
- `compInverseOfUnit_hasSubst`
- `subst_compInverseOfUnit_eq_X`
- `compInverseOfUnit_coeff_one`
- `FormalGroup.exp_constantCoeff`
- `FormalGroup.commutative_of_torsion_free` (also has unused hypothesis)
- `FormalGroup.log_coeff_succ_nsmul`
- `FormalGroup.logPreservesAdd_constantCoeff`
- `FormalGroup.logHomOfLogPreservesAdd_toSeries`
- `FormalGroup.additiveFormalGroup_logHom`
- `FormalGroup.logHom_toSeries`
