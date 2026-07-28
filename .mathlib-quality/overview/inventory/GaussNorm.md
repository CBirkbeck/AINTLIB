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
