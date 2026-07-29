# GaussNorm.lean — inventory (part 1: lines 1-460)

File: `projects/AdicSpaces/Adic spaces/FarguesFontaine/GaussNorm.lean` (923 lines total).
Namespace `FarguesFontaine`, `noncomputable section`, `universe u`.
Shared variables: `(p : ℕ) [Fact p.Prime]`, `(F : Type u)` a perfectoid field of
characteristic `p` (`[Field F] [TopologicalSpace F] [IsTopologicalRing F] [UniformSpace F]
[NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]`). `OF F` is the ring of integers
(`PerfectoidFieldCharP.lean`), `Ainf p F = WittVector p (OF F)` (`AinfHuber.lean`).

---

### `def perfectoidValuation`
- **Type**: `(p : ℕ) [Fact p.Prime] (F : Type u) [...] : Valuation F NNReal`
- **What**: The fixed rank-1 valuation of the perfectoid field `F`, extracted by choice from the existence statement packaged in the `IsPerfectoidField` class (Wedhorn Prop 6.1).
- **How**: `Classical.choose` applied to `IsPerfectoidField.exists_valuation`.
- **Hypotheses**: `F` a perfectoid field over `p`; no characteristic assumption is used for the definition itself.
- **Uses from project**: `IsPerfectoidField.exists_valuation`
- **Used by**: `gaussTerm`, `perfectoidValuation_integers`, `perfectoidValuation_le_one`, and essentially every later result in the file.
- **Visibility**: public
- **Lines**: 56-59 (definition, 2 lines)
- **Notes**: choice-based definition; the *only* handle on it is the `choose_spec` lemma below.

### `theorem perfectoidValuation_integers`
- **Type**: `(perfectoidValuation p F).Integers ↥(powerBoundedSubring.toSubring F)`
- **What**: The chosen valuation has the power-bounded subring `F°` as its ring of integers, i.e. `v x ≤ 1 ↔ x ∈ F°`.
- **How**: Literally the `choose_spec` of `IsPerfectoidField.exists_valuation`, the defining property of `perfectoidValuation`.
- **Hypotheses**: `IsPerfectoidField p F`; `CharP F p` is explicitly omitted.
- **Uses from project**: `perfectoidValuation`, `IsPerfectoidField.exists_valuation`, `powerBoundedSubring`
- **Used by**: `perfectoidValuation_le_one`
- **Visibility**: public
- **Lines**: 61-64 (term proof, 1 line)
- **Notes**: `omit [CharP F p]`.

### `theorem perfectoidValuation_le_one`
- **Type**: `(a : OF F) → perfectoidValuation p F (a : F) ≤ 1`
- **What**: The valuation is bounded by `1` on the integer ring `O_F`.
- **How**: `Valuation.Integers.map_le_one` applied to `perfectoidValuation_integers`.
- **Hypotheses**: `a` an element of `OF F` (the power-bounded subring).
- **Uses from project**: `perfectoidValuation_integers`, `perfectoidValuation`, `OF`
- **Used by**: `gaussTerm_le`
- **Visibility**: public
- **Lines**: 66-70 (term proof, 1 line)
- **Notes**: `omit [CharP F p]`.

### `def teichCoeff`
- **Type**: `(x : Ainf p F) (n : ℕ) : OF F`
- **What**: The `n`-th Teichmüller coordinate `a_n = θ^{-n}(x_n)` of a Witt vector `x ∈ A_inf`, so that `x = Σ_n p^n [a_n]` `p`-adically.
- **How**: Applies the `n`-th power of the inverse Frobenius automorphism `frobeniusEquiv (OF F) p |>.symm` (available because `O_F` is perfect) to the `n`-th Witt coefficient `x.coeff n`.
- **Hypotheses**: `O_F` perfect of characteristic `p`, so `frobeniusEquiv` is a `RingAut`.
- **Uses from project**: `Ainf`, `OF`
- **Used by**: `gaussTerm`, `teichCoeff_zero_vector`, `teichCoeff_eq_zero_iff`, and every expansion lemma downstream.
- **Visibility**: public
- **Lines**: 72-75 (definition, 1 line)
- **Notes**: none.

### `@[simp] theorem teichCoeff_zero_vector`
- **Type**: `(n : ℕ) → teichCoeff p F (0 : Ainf p F) n = 0`
- **What**: All Teichmüller coordinates of the zero Witt vector are zero.
- **How**: Unfold `teichCoeff`, use `WittVector.zero_coeff` then `map_zero` for the ring automorphism.
- **Hypotheses**: none beyond the ambient setup.
- **Uses from project**: `teichCoeff`
- **Used by**: unused in file (simp lemma)
- **Visibility**: public
- **Lines**: 77-79 (proof, 1 line)
- **Notes**: `@[simp]`.

### `theorem teichCoeff_eq_zero_iff`
- **Type**: `teichCoeff p F x n = 0 ↔ x.coeff n = 0`
- **What**: A Teichmüller coordinate vanishes exactly when the corresponding Witt coefficient does.
- **How**: The inverse Frobenius is a ring *equiv*, hence injective, so `map_eq_zero_iff` transfers vanishing.
- **Hypotheses**: implicit `x : Ainf p F`, `n : ℕ`.
- **Uses from project**: `teichCoeff`
- **Used by**: `exists_gaussValue_eq_gaussTerm`
- **Visibility**: public
- **Lines**: 81-83 (proof, 1 line)
- **Notes**: none.

### `def gaussTerm`
- **Type**: `(ρ : NNReal) (x : Ainf p F) (n : ℕ) : NNReal`
- **What**: The `n`-th term `ρ^n · v(a_n)` of the weighted Gauss value, where `a_n` is the `n`-th Teichmüller coordinate.
- **How**: Product of `ρ ^ n` with `perfectoidValuation p F` applied to the coercion of `teichCoeff p F x n` into `F`.
- **Hypotheses**: `ρ : NNReal` arbitrary at the definition site.
- **Uses from project**: `perfectoidValuation`, `teichCoeff`, `Ainf`
- **Used by**: `gaussValue` and every Gauss-value lemma in the file.
- **Visibility**: public
- **Lines**: 85-87 (definition, 1 line)
- **Notes**: none.

### `def gaussValue`
- **Type**: `(ρ : NNReal) (x : Ainf p F) : NNReal`
- **What**: The weighted Gauss value `w_ρ(x) = ⨆_n ρ^n · v(a_n)` — Kedlaya's `λ_t` in the untwisted normalization `w_ρ = λ_t^{1/t}`, `ρ = p^{-1/t}`.
- **How**: `⨆ n, gaussTerm p F ρ x n`, an indexed supremum in the conditionally complete lattice `NNReal`.
- **Hypotheses**: none at the definition; boundedness (needed for the sup to be meaningful) is supplied separately by `bddAbove_range_gaussTerm` under `ρ ≤ 1`.
- **Uses from project**: `gaussTerm`, `Ainf`
- **Used by**: all `gaussValue_*` lemmas and the whole second half of the file.
- **Visibility**: public
- **Lines**: 89-92 (definition, 1 line)
- **Notes**: main definition of the file.

### `theorem gaussTerm_le`
- **Type**: `(ρ : NNReal) (x : Ainf p F) (n : ℕ) → gaussTerm p F ρ x n ≤ ρ ^ n`
- **What**: Each Gauss term is at most `ρ^n`, since the valuation of an integral element is `≤ 1`.
- **How**: `mul_le_of_le_one_right` with the bound `perfectoidValuation_le_one`.
- **Hypotheses**: none on `ρ`.
- **Uses from project**: `gaussTerm`, `perfectoidValuation_le_one`
- **Used by**: `gaussTerm_le_one`, `exists_gaussValue_eq_gaussTerm`
- **Visibility**: public
- **Lines**: 94-96 (term proof, 1 line)
- **Notes**: none.

### `theorem gaussTerm_le_one`
- **Type**: `(hρ1 : ρ ≤ 1) (x : Ainf p F) (n : ℕ) → gaussTerm p F ρ x n ≤ 1`
- **What**: For weight `ρ ≤ 1` every Gauss term is at most `1`.
- **How**: Chain `gaussTerm_le` with `pow_le_one₀` applied to `hρ1`.
- **Hypotheses**: `ρ ≤ 1`.
- **Uses from project**: `gaussTerm_le`, `gaussTerm`
- **Used by**: `gaussValue_le_one`, `bddAbove_range_gaussTerm`, `gaussValue_p_mul`
- **Visibility**: public
- **Lines**: 98-100 (term proof, 1 line)
- **Notes**: none.

### `theorem gaussValue_le_one`
- **Type**: `(hρ1 : ρ ≤ 1) (x : Ainf p F) → gaussValue p F ρ x ≤ 1`
- **What**: The Gauss value of any element of `A_inf` is at most `1` when `ρ ≤ 1` (so `w_ρ` takes values in the unit interval).
- **How**: `ciSup_le` reduces to the termwise bound `gaussTerm_le_one`.
- **Hypotheses**: `ρ ≤ 1`.
- **Uses from project**: `gaussValue`, `gaussTerm_le_one`
- **Used by**: (headline result; consumed downstream / second half)
- **Visibility**: public
- **Lines**: 102-104 (term proof, 1 line)
- **Notes**: listed as a main result in the module docstring.

### `theorem bddAbove_range_gaussTerm`
- **Type**: `(hρ1 : ρ ≤ 1) (x : Ainf p F) → BddAbove (Set.range (gaussTerm p F ρ x))`
- **What**: For `ρ ≤ 1` the family of Gauss terms is bounded above (by `1`), which is what makes the `⨆` in `gaussValue` well-behaved.
- **How**: Exhibit `1` as an explicit upper bound via `gaussTerm_le_one`.
- **Hypotheses**: `ρ ≤ 1`.
- **Uses from project**: `gaussTerm`, `gaussTerm_le_one`
- **Used by**: `gaussValue_one`, `gaussValue_teichmuller`, `gaussValue_p_mul`, `exists_gaussValue_eq_gaussTerm`
- **Visibility**: public
- **Lines**: 106-108 (proof, 1 line)
- **Notes**: the workhorse side condition for every `le_ciSup` application in the file.

### `@[simp] theorem gaussValue_zero`
- **Type**: `(ρ : NNReal) → gaussValue p F ρ (0 : Ainf p F) = 0`
- **What**: `w_ρ(0) = 0`.
- **How**: `le_antisymm` with `ciSup_le`, each term being `0` because all Teichmüller coordinates of `0` vanish (`teichCoeff_zero_vector` via `simp [gaussTerm]`).
- **Hypotheses**: none on `ρ`.
- **Uses from project**: `gaussValue`, `gaussTerm`
- **Used by**: (main result; consumed downstream)
- **Visibility**: public
- **Lines**: 110-114 (proof, 3 lines)
- **Notes**: `@[simp]`.

### `@[simp] theorem gaussValue_one`
- **Type**: `(hρ1 : ρ ≤ 1) → gaussValue p F ρ (1 : Ainf p F) = 1`
- **What**: `w_ρ(1) = 1`, i.e. the Gauss value is normalized.
- **How**: Two-sided: `ciSup_le` with a case split on `n = 0` vs `n > 0`, where `WittVector.one_coeff_eq_of_pos` kills all higher coefficients and `WittVector.one_coeff_zero` gives `v(1) = 1` at `n = 0`; the reverse bound is `le_ciSup` at index `0` with `bddAbove_range_gaussTerm`.
- **Hypotheses**: `ρ ≤ 1`.
- **Uses from project**: `gaussValue`, `gaussTerm`, `teichCoeff`, `bddAbove_range_gaussTerm`
- **Used by**: (main result; consumed downstream)
- **Visibility**: public
- **Lines**: 116-127 (proof, 9 lines)
- **Notes**: `@[simp]`.

### `theorem gaussValue_teichmuller`
- **Type**: `(hρ1 : ρ ≤ 1) (a : OF F) → gaussValue p F ρ (teichmuller p a) = perfectoidValuation p F (a : F)`
- **What**: On a Teichmüller lift `[a]`, the Gauss value is just the valuation of `a`.
- **How**: `WittVector.teichmuller_coeff_pos` makes every term with `n > 0` vanish and `WittVector.teichmuller_coeff_zero` identifies the `n = 0` term with `v(a)`; then `le_antisymm` of `ciSup_le` against `le_ciSup … 0` using `bddAbove_range_gaussTerm`.
- **Hypotheses**: `ρ ≤ 1`; `a ∈ O_F`.
- **Uses from project**: `gaussValue`, `gaussTerm`, `teichCoeff`, `bddAbove_range_gaussTerm`, `perfectoidValuation`, `OF`
- **Used by**: (main result; consumed downstream)
- **Visibility**: public
- **Lines**: 129-138 (proof, 7 lines)
- **Notes**: none.

### `theorem gaussValue_p_mul`
- **Type**: `(hρ1 : ρ ≤ 1) (x : Ainf p F) → gaussValue p F ρ ((p : Ainf p F) * x) = ρ * gaussValue p F ρ x`
- **What**: The `p`-shift rule `w_ρ(p·x) = ρ·w_ρ(x)`: multiplying by `p` shifts the Teichmüller expansion up one index, scaling the value by `ρ`.
- **How**: Three `have`s — a coordinate shift `teichCoeff (p·x) (n+1) = teichCoeff x n` proved from `WittVector.mul_charP_coeff_succ` (coefficients of `x·p` are `0, x_0^p, x_1^p, …` in characteristic `p`) combined with `RingEquiv.symm_apply_apply` cancelling one inverse Frobenius; vanishing of the `0`-th term via `WittVector.mul_charP_coeff_zero`; hence `gaussTerm (p·x) (n+1) = ρ · gaussTerm x n`. Then `NNReal.mul_iSup` turns the goal into a two-sided `ciSup_le`/`le_ciSup` comparison of the two shifted families.
- **Hypotheses**: `ρ ≤ 1` (only to get boundedness of the term families); `CharP F p` is essential for the Witt-coefficient shift.
- **Uses from project**: `teichCoeff`, `gaussTerm`, `gaussValue`, `gaussTerm_le_one`, `bddAbove_range_gaussTerm`
- **Used by**: (main result; consumed downstream)
- **Visibility**: public
- **Lines**: 140-175 (proof, 32 lines)
- **Notes**: >30 lines; supplies an ad-hoc inline `BddAbove` witness for the scaled family rather than a named lemma.

### `theorem exists_gaussValue_eq_gaussTerm`
- **Type**: `(hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hx : x ≠ 0) → ∃ n, gaussValue p F ρ x = gaussTerm p F ρ x n`
- **What**: For a strictly contracting weight `0 < ρ < 1` and `x ≠ 0`, the supremum defining `w_ρ(x)` is attained — "the supremum becomes a maximum as soon as `ρ < 1`" (Kedlaya AWS, Rem. 2.6.3).
- **How**: Pick `m` with `x.coeff m ≠ 0` (from `WittVector.ext` and `teichCoeff_eq_zero_iff`), so `t := gaussTerm x m > 0` using `Valuation.zero_iff`. Since `ρ < 1`, `exists_pow_lt_of_lt_one` plus `pow_le_pow_of_le_one` gives `N` with `ρ^n < t` for all `n ≥ N`, and `gaussTerm_le` shows every term beyond `N` is `< t`. The maximum over the finite set `Finset.range (N+1)` (`Finset.exists_max_image`) is therefore a global maximum, and `le_antisymm` of `ciSup_le` against `le_ciSup` with `bddAbove_range_gaussTerm` finishes.
- **Hypotheses**: `0 < ρ`, `ρ < 1`, `x ≠ 0`.
- **Uses from project**: `gaussTerm`, `gaussValue`, `teichCoeff`, `teichCoeff_eq_zero_iff`, `perfectoidValuation`, `gaussTerm_le`, `bddAbove_range_gaussTerm`
- **Used by**: (main result; consumed downstream)
- **Visibility**: public
- **Lines**: 177-212 (proof, 32 lines)
- **Notes**: >30 lines; the "`m` is in `range (N+1)`" argument is duplicated verbatim twice (lines 200-203 and 209-212) — a golf/dedup target.

---
## Expansion-uniqueness layer (from line 214)

Toolkit for the ultrametric inequality, after [Kedlaya, *New methods for (φ,Γ)-modules*, arXiv:1004.0466] §3-4: elements of `A_inf` have unique `p`-adic Teichmüller expansions, read off by `teichCoeff`.

### `theorem coe_p_ne_zero`
- **Type**: `(p : Ainf p F) ≠ 0`
- **What**: The image of the prime `p` in `A_inf = W(O_F)` is nonzero.
- **How**: `WittVector.teichmuller_mul_pow_coeff` at index `1` shows the first Witt coefficient of `(p : Ainf p F)` is `1`, which contradicts `WittVector.zero_coeff` if `p = 0`.
- **Hypotheses**: only `Fact p.Prime` and `CharP F p`; the topological/perfectoid instances are explicitly omitted.
- **Uses from project**: `Ainf`, `OF`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 220-227 (proof, 5 lines)
- **Notes**: `omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F]` — deliberately stated at minimal hypotheses.

### `theorem frobeniusEquiv_symm_pow_pow_cancel`
- **Type**: `(b : OF F) (j : ℕ) → ((frobeniusEquiv (OF F) p).symm ^ j) (b ^ p ^ j) = b`
- **What**: Applying the inverse Frobenius `j` times to `b^{p^j}` returns `b` — the perfectness identity that makes Teichmüller coordinates well defined.
- **How**: Induction on `j`; the step rewrites `p^{k+1} = p^k · p`, uses `pow_mul` to see `(b^{p^k})^p`, cancels one Frobenius via `frobeniusEquiv_apply`/`frobenius_def` and `RingEquiv.symm_apply_apply`, then applies the induction hypothesis.
- **Hypotheses**: `O_F` perfect of characteristic `p`.
- **Uses from project**: `OF`
- **Used by**: `teichCoeff_sum_range_add`
- **Visibility**: public
- **Lines**: 229-239 (proof, 9 lines)
- **Notes**: none.

### `theorem exists_eq_sum_teichCoeff_add`
- **Type**: `(x : Ainf p F) (N : ℕ) → ∃ z, x = (∑ i ∈ range N, teichmuller p (teichCoeff p F x i) * p ^ i) + p ^ N * z`
- **What**: Every `x ∈ A_inf` equals its length-`N` Teichmüller prefix `Σ_{i<N} [a_i] p^i` plus a remainder divisible by `p^N`.
- **How**: Case `N = 0` is trivial (`z := x`); for `N = n+1` it is exactly mathlib's `WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff`, after rewriting `Finset.Iic n = Finset.range (n+1)` and matching the summands with `teichCoeff` unfolded, then `sub_eq_iff_eq_add'`.
- **Hypotheses**: `O_F` perfect, characteristic `p` (for the Witt/Teichmüller series statement).
- **Uses from project**: `teichCoeff`, `Ainf`, `OF`
- **Used by**: `exists_head_split`, `teichCoeff_teichmuller_mul`, and the second half (lines 613-647)
- **Visibility**: public
- **Lines**: 241-259 (proof, 13 lines)
- **Notes**: the foundational "expansion exists" half of the uniqueness layer.

### `theorem teichCoeff_sum_range_add`
- **Type**: `(b : ℕ → OF F) (z : Ainf p F) (hj : j < N) → teichCoeff p F ((∑ i ∈ range N, teichmuller p (b i) * p ^ i) + p ^ N * z) j = b j`
- **What**: Uniqueness of Teichmüller expansions: reading `teichCoeff` off the explicit expansion `Σ_{i<N}[b_i]p^i + p^N z` recovers exactly the digits `b_0,…,b_{N-1}`.
- **How**: First, the `p^N z` tail does not affect coefficients below `N` (`WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero` together with `WittVector.mul_pow_charP_coeff_zero`). Second, the `j`-th Witt coefficient of the prefix is `(b j)^{p^j}`: interchange sum and coefficient by `WittVector.sum_coeff_eq_coeff_sum` (whose pairwise-disjointness side goal is discharged from `WittVector.teichmuller_mul_pow_coeff_of_ne`), then `Finset.sum_eq_single j` with `WittVector.teichmuller_mul_pow_coeff`. Finally `frobeniusEquiv_symm_pow_pow_cancel` strips the `j`-fold Frobenius.
- **Hypotheses**: `j < N`; `CharP` for the Witt-coefficient vanishing.
- **Uses from project**: `teichCoeff`, `frobeniusEquiv_symm_pow_pow_cancel`, `Ainf`, `OF`
- **Used by**: `exists_head_split`, `teichCoeff_teichmuller_mul`, and the second half (lines 561, 645)
- **Visibility**: public
- **Lines**: 261-289 (proof, 24 lines)
- **Notes**: the key uniqueness theorem; every later "read off the coordinates" argument goes through it.

### `theorem exists_head_split`
- **Type**: `(x : Ainf p F) → ∃ x', x = teichmuller p (teichCoeff p F x 0) + p * x' ∧ ∀ k, teichCoeff p F x' k = teichCoeff p F x (k+1)`
- **What**: Head split: peel the leading Teichmüller digit off `x`, leaving a tail `x'` whose Teichmüller coordinates are those of `x` shifted down by one.
- **How**: Take `z` from `exists_eq_sum_teichCoeff_add` at `N = 1` for the split itself. For the coordinate claim, expand `z` to depth `k+1`, multiply by `p` (re-indexing the sum by `Finset.sum_range_succ'`) to write `x` as an explicit depth-`(k+2)` expansion whose digits are `x`'s head followed by `z`'s digits, then apply `teichCoeff_sum_range_add` at index `k+1` to read `teichCoeff z k`.
- **Hypotheses**: none beyond the ambient perfectoid/char-`p` setup.
- **Uses from project**: `exists_eq_sum_teichCoeff_add`, `teichCoeff_sum_range_add`, `teichCoeff`
- **Used by**: `exists_list_head_split`, `exists_fold_teichmuller_heads`
- **Visibility**: public
- **Lines**: 291-328 (proof, 32 lines)
- **Notes**: >30 lines; uses `Nat.casesOn` to describe the concatenated digit sequence, which makes the rewriting heavy.

### `theorem teichCoeff_teichmuller_mul`
- **Type**: `(w : OF F) (s : Ainf p F) (j : ℕ) → teichCoeff p F (teichmuller p w * s) j = w * teichCoeff p F s j`
- **What**: Scaling by a Teichmüller lift multiplies every Teichmüller coordinate by the same scalar.
- **How**: Expand `s` to depth `j+1` via `exists_eq_sum_teichCoeff_add`, distribute `[w]` across the expansion using multiplicativity of `teichmuller` (`map_mul`), obtaining an explicit depth-`(j+1)` expansion with digits `w * teichCoeff s i`; then `teichCoeff_sum_range_add` reads off the `j`-th digit.
- **Hypotheses**: `w ∈ O_F`.
- **Uses from project**: `exists_eq_sum_teichCoeff_add`, `teichCoeff_sum_range_add`, `teichCoeff`
- **Used by**: `valuation_teichCoeff_teichmuller_add_le_left`
- **Visibility**: public
- **Lines**: 330-342 (proof, 10 lines)
- **Notes**: none.

### `private theorem valuation_teichCoeff_teichmuller_add_le_left`
- **Type**: `(h : v b ≤ v a) (j : ℕ) → v (teichCoeff p F (teichmuller p a + teichmuller p b) j) ≤ v a`
- **What**: The ordered half of the pair bound: when `v b ≤ v a`, every Teichmüller coordinate of `[a] + [b]` has valuation at most `v a`.
- **How**: The `u = b/a` scaling trick, no Witt-polynomial homogeneity. If `a = 0` then `b = 0` by `Valuation.zero_iff` and everything is `0`. Otherwise `v(b/a) ≤ 1`, so `perfectoidValuation_integers.exists_of_le_one` produces `u ∈ O_F` with `a·u = b`; hence `[a] + [b] = [a] · (1 + [u])`, and `teichCoeff_teichmuller_mul` turns each coordinate into `a ·` (something integral), whose valuation is `≤ v a` by `Valuation.map_mul` and `perfectoidValuation_le_one`.
- **Hypotheses**: `v b ≤ v a`.
- **Uses from project**: `perfectoidValuation`, `perfectoidValuation_integers`, `perfectoidValuation_le_one`, `teichCoeff`, `teichCoeff_teichmuller_mul`, `OF`
- **Used by**: `valuation_teichCoeff_teichmuller_add_le`
- **Visibility**: private
- **Lines**: 344-381 (proof, 33 lines)
- **Notes**: >30 lines; the mathematical heart of the ultrametric estimate for two Teichmüller lifts.

### `theorem valuation_teichCoeff_teichmuller_add_le`
- **Type**: `(a b : OF F) (j : ℕ) → v (teichCoeff p F (teichmuller p a + teichmuller p b) j) ≤ max (v a) (v b)`
- **What**: Pair bound: every Teichmüller coordinate of `[a] + [b]` has valuation at most `max (v a) (v b)`.
- **How**: `le_total` on the two valuations, then `valuation_teichCoeff_teichmuller_add_le_left` in each case (the second after `add_comm`).
- **Hypotheses**: none.
- **Uses from project**: `valuation_teichCoeff_teichmuller_add_le_left`, `perfectoidValuation`, `teichCoeff`
- **Used by**: `gaussValue_teichmuller_add_le`, `exists_fold_teichmuller_heads`
- **Visibility**: public
- **Lines**: 383-392 (proof, 4 lines)
- **Notes**: none.

### `theorem gaussTerm_le_gaussValue`
- **Type**: `(hρ1 : ρ ≤ 1) (x : Ainf p F) (n : ℕ) → gaussTerm p F ρ x n ≤ gaussValue p F ρ x`
- **What**: Each individual Gauss term is bounded by the Gauss value (the sup).
- **How**: `le_ciSup` with the boundedness witness `bddAbove_range_gaussTerm`.
- **Hypotheses**: `ρ ≤ 1`.
- **Uses from project**: `gaussTerm`, `gaussValue`, `bddAbove_range_gaussTerm`
- **Used by**: `mul_gaussValue_le_of_tail`, `exists_list_head_split`, and heavily in the second half (lines 715, 717, 795, 812, 831, 834, 871)
- **Visibility**: public
- **Lines**: 394-396 (term proof, 1 line)
- **Notes**: the most-used utility lemma in the file.

### `theorem mul_gaussValue_le_of_tail`
- **Type**: `(hρ1 : ρ ≤ 1) (hcoords : ∀ k, teichCoeff p F x' k = teichCoeff p F x (k+1)) → ρ * gaussValue p F ρ x' ≤ gaussValue p F ρ x`
- **What**: Tail bound: if `x'` carries the once-shifted Teichmüller coordinates of `x` (as produced by `exists_head_split`), then `ρ·w(x') ≤ w(x)`.
- **How**: `NNReal.mul_iSup` pushes `ρ` inside the sup, then `ciSup_le`; termwise `ρ · gaussTerm x' k = gaussTerm x (k+1)` by `pow_succ` and the coordinate hypothesis, and that is `≤ gaussValue x` by `gaussTerm_le_gaussValue`.
- **Hypotheses**: `ρ ≤ 1`; the coordinate-shift relation between `x'` and `x`.
- **Uses from project**: `gaussValue`, `gaussTerm`, `teichCoeff`, `gaussTerm_le_gaussValue`
- **Used by**: `exists_list_head_split`, `exists_fold_teichmuller_heads`
- **Visibility**: public
- **Lines**: 398-409 (proof, 7 lines)
- **Notes**: none.

### `theorem nnreal_mul_max`
- **Type**: `(s a b : NNReal) → s * max a b = max (s * a) (s * b)`
- **What**: Multiplication by a nonnegative real distributes over `max` in `NNReal`.
- **How**: `le_total a b` plus `max_eq_left`/`max_eq_right` and monotonicity of multiplication (`mul_le_mul_of_nonneg_left`).
- **Hypotheses**: none (nonnegativity is automatic in `NNReal`).
- **Uses from project**: []
- **Used by**: `exists_fold_teichmuller_heads`
- **Visibility**: public
- **Lines**: 411-414 (proof, 3 lines)
- **Notes**: general-purpose `NNReal` fact with no Fargues-Fontaine content — a mathlib-upstreaming / dedup candidate (mathlib has `mul_max_of_nonneg`).

### `theorem gaussValue_teichmuller_add_le`
- **Type**: `(hρ1 : ρ ≤ 1) (a b : OF F) → gaussValue p F ρ (teichmuller p a + teichmuller p b) ≤ max (v a) (v b)`
- **What**: The Gauss value of a sum of two Teichmüller lifts is at most the max of the two valuations — the ultrametric inequality in the two-digit case.
- **How**: `ciSup_le` reduces to the terms; each term is `ρ^j ·` (a coordinate valuation), so drop `ρ^j ≤ 1` by `mul_le_of_le_one_left`/`pow_le_one₀` and apply the pair bound `valuation_teichCoeff_teichmuller_add_le`.
- **Hypotheses**: `ρ ≤ 1`.
- **Uses from project**: `gaussValue`, `gaussTerm`, `valuation_teichCoeff_teichmuller_add_le`, `perfectoidValuation`, `OF`
- **Used by**: `exists_fold_teichmuller_heads`
- **Visibility**: public
- **Lines**: 416-425 (proof, 5 lines)
- **Notes**: none.

### `private theorem exists_list_head_split`
- **Type**: `(hρ1 : ρ ≤ 1) (s B : NNReal) (L : List (Ainf p F)) (hL : ∀ w ∈ L, s * gaussValue p F ρ w ≤ B) → ∃ hl tl, L.sum = (hl.map (teichmuller p ·)).sum + p * tl.sum ∧ (∀ h ∈ hl, s * v h ≤ B) ∧ ∀ t ∈ tl, s * (ρ * gaussValue p F ρ t) ≤ B`
- **What**: Simultaneous head split of a whole list: given a list of elements each satisfying a uniform bound `s·w(·) ≤ B`, split every member as head Teichmüller digit plus `p`-times-tail, keeping the same bound on the heads' valuations and on the (`ρ`-scaled) tails. This is operation 1 in Kedlaya's proof of Lemma 4.1.
- **How**: Induction on the list. For `cons w rest`, apply `exists_head_split` to `w`; the head bound comes from `gaussTerm_le_gaussValue` at `n = 0` (where `gaussTerm x 0 = v (teichCoeff x 0)` since `ρ^0 = 1`), and the tail bound from `mul_gaussValue_le_of_tail`, both composed with `hL w` by monotonicity of multiplication.
- **Hypotheses**: `ρ ≤ 1`; every list member satisfies `s * gaussValue ρ w ≤ B`.
- **Uses from project**: `gaussValue`, `gaussTerm`, `teichCoeff`, `exists_head_split`, `gaussTerm_le_gaussValue`, `mul_gaussValue_le_of_tail`, `perfectoidValuation`, `Ainf`, `OF`
- **Used by**: `exists_level_rep` (line 522, second half)
- **Visibility**: private
- **Lines**: 427-457 (proof, 22 lines)
- **Notes**: the bookkeeping half of the ultrametric induction; bounds are carried as an explicit `s`/`B` pair rather than instantiated at `ρ^n`/`max (w x) (w y)`.

### `private theorem exists_fold_teichmuller_heads` (boundary decl — docstring starts at 459, `private theorem` at 461)
- **Type**: `(hρ1 : ρ ≤ 1) (s B : NNReal) (l : List (OF F)) (hl : ∀ h ∈ l, s * v h ≤ B) → ∃ c P, (l.map (teichmuller p ·)).sum = teichmuller p c + p * P.sum ∧ s * v c ≤ B ∧ ∀ w ∈ P, s * (ρ * gaussValue p F ρ w) ≤ B`
- **What**: Fold a whole list of Teichmüller lifts into a *single* Teichmüller head `[c]` plus `p` times a controlled remainder list, preserving the uniform bound. This is Kedlaya's operation 2, iterated.
- **How**: Induction on `l`; at each step combine the new head `[h]` with the accumulated head `[c]` and head-split the pair via `exists_head_split`. The bound on the new head is `valuation_teichCoeff_teichmuller_add_le` (pair bound) fed into `nnreal_mul_max` + `max_le`; the bound on the new remainder is `mul_gaussValue_le_of_tail` composed with `gaussValue_teichmuller_add_le`.
- **Hypotheses**: `ρ ≤ 1`; uniform bound `s * v h ≤ B` on each list entry.
- **Uses from project**: `exists_head_split`, `nnreal_mul_max`, `gaussValue_teichmuller_add_le`, `valuation_teichCoeff_teichmuller_add_le`, `mul_gaussValue_le_of_tail`, `gaussValue`, `teichCoeff`, `perfectoidValuation`, `Ainf`, `OF`
- **Used by**: `exists_level_rep` (line 524, second half)
- **Visibility**: private
- **Lines**: 459-497 (proof, 30 lines)
- **Notes**: straddles the part-1/part-2 boundary; included here in full. Together with `exists_list_head_split` it feeds `exists_level_rep` (line 502, part 2), which is where the full ultrametric inequality is assembled.

---
*Part 1 ends here (line 497). Part 2 begins with `exists_level_rep` at line 499.*

## Part 2 — lines 499–923

### `private theorem exists_level_rep`
- **Type**: `(hρ1 : ρ ≤ 1) (x y : Ainf p F) (n : ℕ) → ∃ b : ℕ → OF F, ∃ L : List (Ainf p F), x + y = (∑ i ∈ Finset.range n, teichmuller p (b i) * p ^ i) + p ^ n * L.sum ∧ (∀ i < n, ρ ^ i * v (b i) ≤ max (w x) (w y)) ∧ ∀ z ∈ L, ρ ^ n * w z ≤ max (w x) (w y)`
- **What**: For every truncation level `n`, the sum `x + y` can be written as a length-`n` Teichmüller expansion whose digits `b i` already obey the target bound `ρ^i · v(b i) ≤ max (w x) (w y)`, plus `p^n` times a list of remainders each still obeying the (`ρ^n`-scaled) bound. This is Kedlaya's inductive normal form (4.1.1)/(4.1.2).
- **How**: Induction on `n`. Base case takes the two-element list `[x, y]` and the zero digit function. The successor step is exactly Kedlaya's two operations run in sequence: `exists_list_head_split` peels one Teichmüller head off every list member, `exists_fold_teichmuller_heads` collapses all those heads into a single digit `c`, and the digit function is extended by `Function.update b n c` (the prefix sum is re-associated by `Finset.sum_range_succ` plus `Function.update_of_ne`/`Function.update_self`).
- **Hypotheses**: `ρ ≤ 1`.
- **Uses from project**: `exists_list_head_split`, `exists_fold_teichmuller_heads`, `gaussValue`, `perfectoidValuation`, `Ainf`, `OF`
- **Used by**: `gaussValue_add_le`
- **Visibility**: private
- **Lines**: 499-550 (proof, 39 lines)
- **Notes**: >30-line proof; the technical heart of the whole ultrametric argument, and the only consumer of the two private list lemmas from part 1.

### `theorem gaussValue_add_le`
- **Type**: `(hρ1 : ρ ≤ 1) (x y : Ainf p F) → gaussValue p F ρ (x + y) ≤ max (gaussValue p F ρ x) (gaussValue p F ρ y)`
- **What**: **The ultrametric inequality** `w(x + y) ≤ max (w x) (w y)` for the weighted Gauss value (Kedlaya, Lemma 4.1 / Lemma 2.3(a)).
- **How**: `ciSup_le` reduces to bounding each term `ρ^j · v (teichCoeff (x+y) j)`. Instantiate `exists_level_rep` at level `j + 1`; then `teichCoeff_sum_range_add` identifies the `j`-th Teichmüller coordinate of `x + y` with the digit `b j` of that representation, whose bound is part of the conclusion of `exists_level_rep`.
- **Hypotheses**: `ρ ≤ 1`.
- **Uses from project**: `gaussValue`, `gaussTerm`, `teichCoeff`, `exists_level_rep`, `teichCoeff_sum_range_add`, `Ainf`
- **Used by**: `gaussValue_list_sum_le`, `gaussValue_finset_sum_le`, `gaussValue_mul_le` (×3), `gaussValue_sub_le`, `gaussValue_add_eq_of_lt`, `gaussValue_mul`
- **Visibility**: public
- **Lines**: 552-563 (proof, 6 lines)
- **Notes**: headline result of the file's first half; 5 further uses elsewhere in the project.

### `theorem teichCoeff_p_pow_mul`
- **Type**: `(x : Ainf p F) (n k : ℕ) → teichCoeff p F (p ^ n * x) (n + k) = teichCoeff p F x k`
- **What**: Multiplying by `p^n` shifts the Teichmüller coordinates by `n`: the `(n+k)`-th coordinate of `p^n · x` is the `k`-th coordinate of `x`.
- **How**: Induction on `n`, reduced to the one-step claim `teichCoeff (p·y) (j+1) = teichCoeff y j`. That step uses `WittVector.mul_charP_coeff_succ` (in characteristic `p`, `(y·p).coeff (j+1) = (y.coeff j)^p`) and then cancels the extra Frobenius power against the inverse-Frobenius twist in `teichCoeff` via `RingEquiv.symm_apply_apply`.
- **Hypotheses**: none beyond the ambient `CharP F p` / perfectoid setting.
- **Uses from project**: `teichCoeff`, `Ainf`, `OF`
- **Used by**: `gaussValue_mul` (line 852)
- **Visibility**: public
- **Lines**: 565-583 (proof, 18 lines)
- **Notes**: none.

### `theorem gaussValue_p_pow_mul`
- **Type**: `(hρ1 : ρ ≤ 1) (n : ℕ) (x : Ainf p F) → gaussValue p F ρ (p ^ n * x) = ρ ^ n * gaussValue p F ρ x`
- **What**: The Gauss value scales by exactly `ρ^n` under multiplication by `p^n` — the iterated form of `w(p·x) = ρ·w(x)`.
- **How**: Induction on `n`, splitting `p^(m+1)·x = p·(p^m·x)` by `ring` and applying the one-step lemma `gaussValue_p_mul` followed by the induction hypothesis.
- **Hypotheses**: `ρ ≤ 1`.
- **Uses from project**: `gaussValue`, `gaussValue_p_mul`, `Ainf`
- **Used by**: `gaussValue_teichmuller_mul_p_pow`, `gaussValue_mul_le` (×2), `gaussValue_shift_tail_le`
- **Visibility**: public
- **Lines**: 585-593 (proof, 8 lines)
- **Notes**: 2 further uses elsewhere in the project.

### `theorem gaussValue_list_sum_le`
- **Type**: `(hρ1 : ρ ≤ 1) (B : NNReal) (L : List (Ainf p F)) (hL : ∀ z ∈ L, gaussValue p F ρ z ≤ B) → gaussValue p F ρ L.sum ≤ B`
- **What**: Ultrametric bound for list sums: if every member of a list has Gauss value at most `B`, so does the sum.
- **How**: Induction on the list, using `gaussValue_add_le` on `w :: rest` and `max_le` to combine the head bound with the induction hypothesis.
- **Hypotheses**: `ρ ≤ 1`; uniform bound `B` on every member.
- **Uses from project**: `gaussValue`, `gaussValue_add_le`, `Ainf`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 595-604 (proof, 8 lines)
- **Notes**: not an instance and not `@[simp]` — genuinely unused, both in this file and elsewhere in the project; the `Finset` twin `gaussValue_finset_sum_le` is the one actually consumed.

### `theorem exists_iter_split`
- **Type**: `(x : Ainf p F) (n : ℕ) → ∃ X : Ainf p F, x = (∑ i ∈ Finset.range n, teichmuller p (teichCoeff p F x i) * p ^ i) + p ^ n * X ∧ ∀ k, teichCoeff p F X k = teichCoeff p F x (n + k)`
- **What**: Iterated head split of a single element: `x` equals its own length-`n` Teichmüller prefix plus `p^n` times a tail `X`, and the tail's Teichmüller coordinates are exactly the `n`-shifted coordinates of `x`.
- **How**: The decomposition itself is `exists_eq_sum_teichCoeff_add`; the coordinate identification is the new content. Splitting `x` again at level `k+1` inside `X` and re-assembling by `Finset.sum_range_add` gives a *single* length-`n+k+1` expansion of `x` whose digits are the glued family, and `teichCoeff_sum_range_add` then reads off the `(n+k)`-th coordinate of `x` as `teichCoeff X k`.
- **Hypotheses**: none.
- **Uses from project**: `teichCoeff`, `exists_eq_sum_teichCoeff_add`, `teichCoeff_sum_range_add`, `Ainf`
- **Used by**: `gaussValue_mul_le` (×2), `gaussValue_mul` (×2)
- **Visibility**: public
- **Lines**: 606-655 (proof, 48 lines)
- **Notes**: >30-line proof; the glued digit family is a `dite` on `i < n`, so much of the length is `dif_pos`/`dif_neg`/`omega` index bookkeeping.

### `theorem gaussValue_finset_sum_le`
- **Type**: `{ι : Type*} (hρ1 : ρ ≤ 1) (B : NNReal) (s : Finset ι) (f : ι → Ainf p F) (hf : ∀ i ∈ s, gaussValue p F ρ (f i) ≤ B) → gaussValue p F ρ (∑ i ∈ s, f i) ≤ B`
- **What**: Ultrametric bound for finite sums indexed by a `Finset`: a uniform bound on the summands bounds the sum.
- **How**: `Finset.induction_on`, with the insert step handled by `gaussValue_add_le` on `f a + ∑ rest` and `max_le`.
- **Hypotheses**: `ρ ≤ 1`; uniform bound `B` on the summands over `s`.
- **Uses from project**: `gaussValue`, `gaussValue_add_le`, `Ainf`
- **Used by**: `gaussValue_mul_le` (×2, nested for a double sum), `gaussValue_mul`
- **Visibility**: public
- **Lines**: 657-667 (proof, 9 lines)
- **Notes**: needs `classical` for the `Finset.induction_on` decidability.

### `theorem gaussValue_teichmuller_mul_p_pow`
- **Type**: `(hρ1 : ρ ≤ 1) (a : OF F) (i : ℕ) → gaussValue p F ρ (teichmuller p a * p ^ i) = ρ ^ i * perfectoidValuation p F (a : F)`
- **What**: The Gauss value of a single term `[a]·p^i` of a Teichmüller expansion is exactly `ρ^i · v(a)`.
- **How**: Commute the product and chain the two computed values: `gaussValue_p_pow_mul` for the `p^i` factor and `gaussValue_teichmuller` for the Teichmüller factor.
- **Hypotheses**: `ρ ≤ 1`.
- **Uses from project**: `gaussValue`, `gaussValue_p_pow_mul`, `gaussValue_teichmuller`, `perfectoidValuation`, `Ainf`, `OF`
- **Used by**: `gaussValue_mul` (line 898)
- **Visibility**: public
- **Lines**: 669-673 (proof, 1 line)
- **Notes**: none.

### `theorem gaussValue_mul_le`
- **Type**: `(hρ1 : ρ < 1) (x y : Ainf p F) → gaussValue p F ρ (x * y) ≤ gaussValue p F ρ x * gaussValue p F ρ y`
- **What**: **Submultiplicativity** `w(x·y) ≤ w(x)·w(y)` for `0 ≤ ρ < 1` (Kedlaya, Lemma 4.1).
- **How**: Prove the family of approximate bounds `w(x·y) ≤ max (w x · w y) (ρ^(n+1))` for every `n`: split `x` and `y` at level `n+1` by `exists_iter_split`, expand `x·y` into the prefix-prefix product plus three `p^(n+1)`-divisible terms, bound the prefix product by a double `gaussValue_finset_sum_le` over `Finset.sum_mul_sum` (each term evaluated by `gaussValue_p_pow_mul` + `gaussValue_teichmuller` and bounded by two copies of `gaussTerm_le_gaussValue`), and bound each tail by `ρ^(n+1)` via `gaussValue_le_one`. Then let `n → ∞`: `exists_pow_lt_of_lt_one` makes `ρ^(N+1)` smaller than any hypothetical excess, contradiction.
- **Hypotheses**: `ρ < 1` (strict — needed for `ρ^n → 0`).
- **Uses from project**: `gaussValue`, `teichCoeff`, `exists_iter_split`, `gaussValue_finset_sum_le`, `gaussValue_p_pow_mul`, `gaussValue_teichmuller`, `gaussTerm_le_gaussValue`, `gaussValue_add_le`, `gaussValue_le_one`, `perfectoidValuation`, `Ainf`, `OF`
- **Used by**: `gaussValue_neg`, `gaussValue_mul` (×3)
- **Visibility**: public
- **Lines**: 675-744 (proof, 68 lines)
- **Notes**: >30-line proof (the longest in part 2 after `gaussValue_mul`); 3 further uses elsewhere in the project.

### `theorem gaussValue_neg`
- **Type**: `(hρ1 : ρ < 1) (x : Ainf p F) → gaussValue p F ρ (-x) = gaussValue p F ρ x`
- **What**: The Gauss value is invariant under negation.
- **How**: `-z = (-1)·z`, so `gaussValue_mul_le` plus `gaussValue_le_one` applied to `-1` gives `w(-z) ≤ w(z)` for all `z`; antisymmetry follows by applying that inequality to `-x` and rewriting `neg_neg`.
- **Hypotheses**: `ρ < 1` (inherited from `gaussValue_mul_le`).
- **Uses from project**: `gaussValue`, `gaussValue_mul_le`, `gaussValue_le_one`, `Ainf`
- **Used by**: `gaussValue_sub_le`
- **Visibility**: public
- **Lines**: 746-757 (proof, 10 lines)
- **Notes**: none.

### `theorem gaussValue_sub_le`
- **Type**: `(hρ1 : ρ < 1) (x y : Ainf p F) → gaussValue p F ρ (x - y) ≤ max (gaussValue p F ρ x) (gaussValue p F ρ y)`
- **What**: The ultrametric inequality in subtractive form, `w(x - y) ≤ max (w x) (w y)`.
- **How**: `sub_eq_add_neg` then `gaussValue_add_le` on `x + (-y)`, and `gaussValue_neg` rewrites `w(-y)` to `w(y)`.
- **Hypotheses**: `ρ < 1` (needed only because `gaussValue_neg` needs it).
- **Uses from project**: `gaussValue`, `gaussValue_add_le`, `gaussValue_neg`, `Ainf`
- **Used by**: `gaussValue_add_eq_of_lt`
- **Visibility**: public
- **Lines**: 759-764 (proof, 3 lines)
- **Notes**: 1 further use elsewhere in the project.

### `theorem gaussValue_add_eq_of_lt`
- **Type**: `(hρ1 : ρ < 1) {A B : Ainf p F} (hAB : gaussValue p F ρ B < gaussValue p F ρ A) → gaussValue p F ρ (A + B) = gaussValue p F ρ A`
- **What**: The isosceles / "all triangles are isosceles" principle: perturbing by a strictly smaller element leaves the Gauss value unchanged.
- **How**: `≤` is `gaussValue_add_le` with `max_le`. For `≥`, write `A = (A + B) - B` and apply `gaussValue_sub_le`; a `max_cases` split rules out the branch where the max is `w B`, since that would give `w A ≤ w B < w A`.
- **Hypotheses**: `ρ < 1`; strict domination `w B < w A`.
- **Uses from project**: `gaussValue`, `gaussValue_add_le`, `gaussValue_sub_le`, `Ainf`
- **Used by**: `gaussValue_mul`
- **Visibility**: public
- **Lines**: 766-779 (proof, 12 lines)
- **Notes**: none.

### `theorem gaussValue_pos_of_ne_zero`
- **Type**: `(hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {x : Ainf p F} (hx : x ≠ 0) → 0 < gaussValue p F ρ x`
- **What**: Positivity / nondegeneracy: a nonzero Witt vector has strictly positive Gauss value when `0 < ρ ≤ 1`.
- **How**: `WittVector.ext` yields some coordinate `x.coeff m ≠ 0`; then `teichCoeff_eq_zero_iff` and `Valuation.zero_iff` show `v (teichCoeff x m) ≠ 0`, so the single term `gaussTerm ρ x m = ρ^m · v(...)` is positive, and `gaussTerm_le_gaussValue` transfers positivity to the supremum.
- **Hypotheses**: `0 < ρ` (else all terms could vanish), `ρ ≤ 1` (for the sup bound), `x ≠ 0`.
- **Uses from project**: `gaussValue`, `gaussTerm`, `teichCoeff`, `teichCoeff_eq_zero_iff`, `gaussTerm_le_gaussValue`, `perfectoidValuation`, `Ainf`
- **Used by**: `gaussValue_mul` (×2)
- **Visibility**: public
- **Lines**: 781-795 (proof, 13 lines)
- **Notes**: 2 further uses elsewhere in the project.

### `theorem teichCoeff_zero_eq`
- **Type**: `(W : Ainf p F) → teichCoeff p F W 0 = W.coeff 0`
- **What**: The `0`-th Teichmüller coordinate is just the `0`-th Witt coordinate (no Frobenius twist at level `0`).
- **How**: Unfold `teichCoeff`; the inverse-Frobenius power is `θ^{-0} = id`, closed by `simp`.
- **Hypotheses**: none.
- **Uses from project**: `teichCoeff`, `Ainf`
- **Used by**: `gaussValue_mul` (×3, in `hmul0`)
- **Visibility**: public
- **Lines**: 797-799 (proof, 2 lines)
- **Notes**: the only declaration in part 2 with no docstring; 2 further uses elsewhere in the project.

### `private theorem gaussValue_shift_tail_le`
- **Type**: `(hρ1 : ρ ≤ 1) {x X : Ainf p F} {n : ℕ} (hcoords : ∀ k, teichCoeff p F X k = teichCoeff p F x (n + k)) → gaussValue p F ρ (p ^ n * X) ≤ gaussValue p F ρ x`
- **What**: If `X` carries the `n`-shifted Teichmüller coordinates of `x`, then the tail `p^n · X` has Gauss value at most that of `x` — the sup over a shifted subfamily is dominated by the full sup.
- **How**: `gaussValue_p_pow_mul` turns the left side into `ρ^n · w X`; `NNReal.mul_iSup` pushes the scalar inside, and `ciSup_le` reduces to the term identity `ρ^n · gaussTerm X i = gaussTerm x (n + i)` (from `hcoords` and `pow_add`), which is bounded by `gaussTerm_le_gaussValue`.
- **Hypotheses**: `ρ ≤ 1`; the coordinate-shift hypothesis `hcoords` (supplied by `exists_iter_split`).
- **Uses from project**: `gaussValue`, `gaussTerm`, `teichCoeff`, `gaussValue_p_pow_mul`, `gaussTerm_le_gaussValue`, `Ainf`
- **Used by**: `gaussValue_mul` (×2)
- **Visibility**: private
- **Lines**: 801-812 (proof, 10 lines)
- **Notes**: none.

### `theorem gaussValue_mul`
- **Type**: `(hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x y : Ainf p F) → gaussValue p F ρ (x * y) = gaussValue p F ρ x * gaussValue p F ρ y`
- **What**: **Multiplicativity** `w(x·y) = w(x)·w(y)` for `0 < ρ < 1` (Kedlaya, Lemma 4.1 / Lemma 2.3(b)) — the Gauss value is a multiplicative seminorm, which is what makes it a point of `𝒴`.
- **How**: The classical "leading-term" argument. Discard the zero cases; `exists_gaussValue_eq_gaussTerm` gives *first* indices `j`, `k` attaining the suprema (`Nat.find`, with `Nat.find_min` giving strict inequality below them). Split off the prefixes with `exists_iter_split` and set `x' = p^j X`, `y' = p^k Y`; the `(j+k)`-th term of `x'·y'` is computed exactly by `teichCoeff_p_pow_mul`, `teichCoeff_zero_eq`, `WittVector.mul_coeff_zero` and `Valuation.map_mul` to be `w(x)·w(y)`, and the reverse bound is `gaussValue_mul_le` + `gaussValue_shift_tail_le`, so `w(x'y') = w(x)·w(y)` exactly. A helper `hprefix` shows each prefix `x - x'` has strictly smaller value (`gaussValue_finset_sum_le` against `Finset.sup_lt_iff` over the strictly-smaller earlier terms), hence the perturbation `x(y - y') + (x - x')y'` is strictly below `w(x)·w(y)`, and `gaussValue_add_eq_of_lt` finishes.
- **Hypotheses**: `0 < ρ` (positivity, so the sup is attained and nonzero) and `ρ < 1` (needed for attainment and for `gaussValue_mul_le`).
- **Uses from project**: `gaussValue`, `gaussTerm`, `teichCoeff`, `gaussValue_pos_of_ne_zero`, `exists_gaussValue_eq_gaussTerm`, `gaussTerm_le_gaussValue`, `exists_iter_split`, `gaussValue_shift_tail_le`, `teichCoeff_p_pow_mul`, `teichCoeff_zero_eq`, `gaussValue_mul_le`, `gaussValue_finset_sum_le`, `gaussValue_teichmuller_mul_p_pow`, `gaussValue_add_le`, `gaussValue_add_eq_of_lt`, `perfectoidValuation`, `Ainf`, `OF`
- **Used by**: unused in file (terminal result)
- **Visibility**: public
- **Lines**: 814-919 (proof, 104 lines)
- **Notes**: >30-line proof and by far the longest in the file; it is the file's capstone theorem and has 3 consumers elsewhere in the project. Contains an inlined general helper `hprefix` (a `have` of full lemma shape, applied twice) that is a natural `/decompose-proof` extraction candidate.

---

### File Summary (whole file, lines 1–923)

**Totals.** 47 declarations: **4 `def`s** (`perfectoidValuation`, `teichCoeff`, `gaussTerm`,
`gaussValue`), **43 theorems**, **0 instances**, 0 structures/classes. **5 are `private`**
(`valuation_teichCoeff_teichmuller_add_le_left`, `exists_list_head_split`,
`exists_fold_teichmuller_heads`, `exists_level_rep`, `gaussValue_shift_tail_le`); the other 42 are
public. **3 carry `@[simp]`** (`teichCoeff_zero_vector`, `gaussValue_zero`, `gaussValue_one`).
Structurally the file is three layers: definitions + basic bounds (56–212), the
Teichmüller-expansion/uniqueness toolkit (220–497), and the seminorm axioms
(499–919: ultrametric, submultiplicativity, multiplicativity).

**Key API used by 3+ in-file consumers.**
- `gaussValue`, `gaussTerm`, `teichCoeff`, `perfectoidValuation` — the four defs, used pervasively.
- `gaussValue_add_le` (7 in-file consumers, plus 5 elsewhere in the project) — the ultrametric
  inequality; the single most-used lemma of the second half.
- `gaussTerm_le_gaussValue` (6 in-file consumers: `mul_gaussValue_le_of_tail`,
  `exists_list_head_split`, `gaussValue_pos_of_ne_zero`, `gaussValue_mul_le`,
  `gaussValue_shift_tail_le`, `gaussValue_mul`) — the "one term bounds the sup" workhorse.
- `teichCoeff_sum_range_add` (4: `exists_head_split`, `teichCoeff_teichmuller_mul`,
  `gaussValue_add_le`, `exists_iter_split`) — coordinate uniqueness for truncated expansions.
- `bddAbove_range_gaussTerm` (4: `gaussValue_one`, `gaussValue_teichmuller`, `gaussValue_p_mul`,
  `exists_gaussValue_eq_gaussTerm`) — the boundedness side condition every `ciSup` argument needs.
- `gaussValue_p_pow_mul` (3: `gaussValue_teichmuller_mul_p_pow`, `gaussValue_mul_le`,
  `gaussValue_shift_tail_le`).
- `exists_eq_sum_teichCoeff_add` (3: `exists_head_split`, `teichCoeff_teichmuller_mul`,
  `exists_iter_split`) and `gaussTerm_le_one` (3: `gaussValue_le_one`,
  `bddAbove_range_gaussTerm`, `gaussValue_p_mul`).

**Unused declarations (no in-file consumer).**
- `@[simp] theorem teichCoeff_zero_vector`, `@[simp] theorem gaussValue_zero`,
  `@[simp] theorem gaussValue_one` — **`@[simp]`, therefore NOT dead**: they are consumed by the
  simp set rather than by name (`gaussValue_zero`/`gaussValue_one` additionally have named uses
  elsewhere in the project).
- `theorem gaussValue_mul` — terminal capstone, not an instance/simp lemma, but consumed **outside**
  the file (`GaussPoint.lean` uses it as `map_mul'` of the Gauss point; `UniformizerEquivariance.lean`
  uses it too). Not dead.
- `theorem coe_p_ne_zero` — plain theorem, no `@[simp]`, no instance, **0 uses in the file and 0
  elsewhere in the project**: genuinely dead.
- `theorem gaussValue_list_sum_le` — plain theorem, **0 uses in the file and 0 elsewhere**: genuinely
  dead; its `Finset` twin `gaussValue_finset_sum_le` is the one actually consumed (3 in-file uses).

**Declarations with `sorry`.** None — the file is sorry-free end to end.

**Declarations with `set_option`.** None — no `maxHeartbeats`/`maxRecDepth` bumps anywhere in the
file.

**Proofs longer than 30 lines (9 total, 4 in part 1 / 4 in part 2, plus one at exactly 30).**
| declaration | proof lines |
|---|---|
| `gaussValue_mul` | 104 |
| `gaussValue_mul_le` | 68 |
| `exists_iter_split` | 48 |
| `exists_level_rep` | 39 |
| `valuation_teichCoeff_teichmuller_add_le_left` | 33 |
| `gaussValue_p_mul` | 32 |
| `exists_gaussValue_eq_gaussTerm` | 32 |
| `exists_head_split` | 32 |
| `exists_fold_teichmuller_heads` | 30 (exactly at the threshold) |

The four longest are all in the second half and all belong to the multiplicativity chain.
`gaussValue_mul` in particular contains an inlined general helper `hprefix` (stated as a full
∀-quantified `have` and applied twice) that is a natural `/decompose-proof` extraction candidate.

**Repeated proof preamble (3+ proofs).** The opener
```
  rw [gaussValue]
  refine … (ciSup_le fun n => ?_) …
```
is repeated verbatim (up to the bound variable name and the surrounding `le_antisymm`) in **5**
proofs: `gaussValue_zero` (112–113), `gaussValue_one` (119–120), `gaussValue_teichmuller`
(132–133), `gaussValue_teichmuller_add_le` (421–422), `gaussValue_add_le` (557–558). A
`gaussValue_le_iff` / `gaussValue_le_of_forall_gaussTerm_le` helper (`w x ≤ B ↔ ∀ n, gaussTerm ρ x n ≤ B`)
would absorb all five and is the clearest dedup opportunity in the file. A second, smaller
repetition — `induction n with | zero => simp | succ m ih =>` followed verbatim by
`have hsplit : (p : Ainf p F) ^ (m + 1) * x = (p : Ainf p F) * ((p : Ainf p F) ^ m * x) := by ring`
— occurs in **2** proofs (`teichCoeff_p_pow_mul` 580, `gaussValue_p_pow_mul` 590), below the
3-proof threshold but worth noting.

**Cross-file note.** `nnreal_mul_max` (part 1, line 411) is a general `NNReal` fact with no
Fargues–Fontaine content and is used from four other files in the project (`WittF.lean` ×4,
`Groebner.lean`, `Euclidean.lean`) — a mathlib-upstreaming / relocation candidate rather than
GaussNorm API.
