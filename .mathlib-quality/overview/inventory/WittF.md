# Inventory — `projects/AdicSpaces/Adic spaces/FarguesFontaine/WittF.lean`

2058 lines, 75 declarations, namespace `FarguesFontaine`, `noncomputable section`.
Imports `«Adic spaces».FarguesFontaine.RobbaLoc` (transitively `GaussNorm`, `GaussPoint`,
`PerfectoidFieldCharP`, `AinfHuber`, `Bounded`, `PseudoUniformizer`).

**Ambient variables** (assumed by every declaration below unless noted):
`(p : ℕ) [Fact (Nat.Prime p)]`, `(F : Type u) [Field F] [TopologicalSpace F]
[IsTopologicalRing F] [UniformSpace F] [NonarchimedeanRing F] [hPF : IsPerfectoidField p F]
[CharP F p]`. Only `exists_mul_pow_isPowerBounded` carries an explicit `include hPF in`.

**Global**: no `sorry`, no `set_option`, no `TODO`/`FIXME` anywhere in the file.

---

## Part 1 — Hölder continuity of the Teichmüller section over `O_F` (T902(b))

### `theorem exists_teichmuller_sub_coeff_eq`
- **Type**: `(x y : OF F) (k : ℕ) : ∃ r : OF F, (WittVector.teichmuller p x - WittVector.teichmuller p y).coeff k = (x - y) * r`
- **What**: Diagonal divisibility — every Witt coefficient of the difference of two Teichmüller lifts `[x] − [y]` is divisible by `x − y` in `O_F`.
- **How**: Naturality of Witt vectors along polynomial evaluation, with no Witt-polynomial computation. Sets `E := ([C x] − [X]).coeff k ∈ Polynomial (O_F)`; `WittVector.map_coeff` + `WittVector.map_teichmuller` along `Polynomial.evalRingHom x` show `E.eval x = ([x] − [x]).coeff k = 0`, so `Polynomial.dvd_iff_isRoot` factors `E = (X − C x) * q`; evaluating at `y` gives the witness `r = −(q.eval y)`.
- **Hypotheses**: `x y : OF F`, `k : ℕ` arbitrary (the `k = 0` case is the trivial `x − y = (x−y)·1`).
- **Uses from project**: `OF`, `teichCoeff` (statement context only — the body is pure mathlib `WittVector`/`Polynomial` API).
- **Used by**: `valuation_teichCoeff_teichmuller_sub_pow_le`
- **Visibility**: public
- **Lines**: 51–81 (proof ≈ 25 lines)
- **Notes**: none.

### `theorem valuation_teichCoeff_teichmuller_sub_pow_le`
- **Type**: `(x y : OF F) (k : ℕ) : (perfectoidValuation p F ((teichCoeff p F ([x] − [y]) k : OF F) : F)) ^ (p ^ k) ≤ perfectoidValuation p F ((x − y : OF F) : F)`
- **What**: The twist bound. The `k`-th Teichmüller coordinate of `[x] − [y]` obeys a `p^k`-th power estimate against `|x − y|` — the Hölder exponent `p^{-k}` in `pow` form.
- **How**: `teichCoeff` is defined via `k` inverse Frobenii, so `frobeniusEquiv_symm_pow_pow_cancel` turns `(teichCoeff … k)^(p^k)` back into the raw Witt coefficient; `exists_teichmuller_sub_coeff_eq` writes that coefficient as `(x−y)·r`; then `Valuation.map_mul` plus `perfectoidValuation_le_one p F r` (the `r` lives in `O_F`) drops the extra factor via `mul_le_of_le_one_right`.
- **Hypotheses**: `x y : OF F`; `perfectoidValuation` is a valuation on `F` with `O_F` in its ring of integers.
- **Uses from project**: `exists_teichmuller_sub_coeff_eq`, `teichCoeff`, `frobeniusEquiv_symm_pow_pow_cancel`, `perfectoidValuation`, `perfectoidValuation_le_one`, `OF`
- **Used by**: `gaussValue_teichmuller_sub_le_of_le`
- **Visibility**: public
- **Lines**: 82–113 (proof ≈ 24 lines, a 5-step `calc`)
- **Notes**: none.

### `theorem gaussValue_teichmuller_sub_le_of_le`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ε : NNReal} (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ∃ δ : NNReal, 0 < δ ∧ ∀ a b : OF F, perfectoidValuation p F ((a − b : OF F) : F) ≤ δ → gaussValue p F ρ ([a] − [b]) ≤ ε`
- **What**: ε–δ (uniform, non-Lipschitz) continuity of the Teichmüller section `a ↦ [a]` for the Gauss value on `A_inf`.
- **How**: Split the sup over coordinates at a threshold `K` chosen by `exists_pow_lt_of_lt_one` so `ρ^K < ε`; take `δ := ε^{p^K}`. For `k ≤ K` the twist bound `valuation_teichCoeff_teichmuller_sub_pow_le` plus `pow_le_pow_iff_left₀` extracts the `p^k`-th root, giving digit bound `ε^{p^{K−k}} ≤ ε`; for `k > K` the crude `gaussTerm_le` bound `ρ^k < ρ^K < ε` already wins.
- **Hypotheses**: `0 < ρ < 1` (so `ρ^k` decays and `ρ^k ≤ 1`), `0 < ε ≤ 1`.
- **Uses from project**: `valuation_teichCoeff_teichmuller_sub_pow_le`, `gaussValue`, `gaussTerm`, `gaussTerm_le`, `teichCoeff`, `perfectoidValuation`, `OF`
- **Used by**: `exists_delta_teichCoeff_sub`, `gaussValueF_teichmuller_sub_le_of_le_scaled`
- **Visibility**: public
- **Lines**: 114–158 (proof ≈ 39 lines)
- **Notes**: proof > 30 lines.

### `theorem exists_delta_teichCoeff_sub`
- **Type**: `(n : ℕ) {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ε : NNReal} (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ∃ δ : NNReal, 0 < δ ∧ ∀ a b : Ainf p F, gaussValue p F ρ (a − b) ≤ δ → perfectoidValuation p F ((teichCoeff p F a n − teichCoeff p F b n : OF F) : F) ≤ ε`
- **What**: Per-coordinate uniform continuity of the level-`n` Teichmüller coordinate on `A_inf = W(O_F)` for the Gauss value.
- **How**: Induction on `n` generalising `ε`. Level 0 is exact because `teichCoeff … 0 = constantCoeff` is additive (`teichCoeff_zero_eq` + `RingHom.map_sub`) so the digit difference *is* `gaussTerm … 0`, dominated by `gaussTerm_le_gaussValue`. For `n+1` take head splits `exists_head_split` of `a` and `b`, rewrite `p·(x'−y') = (a−b) − ([a₀]−[b₀])`, bound the head difference by `gaussValue_teichmuller_sub_le_of_le`, then use `gaussValue_p_mul` and the ultrametric `gaussValue_sub_le` to get `ρ·w(x'−y') ≤ ρ·δn`, cancel `ρ` and apply the induction hypothesis to the tails.
- **Hypotheses**: `0 < ρ < 1`, `0 < ε ≤ 1`; the head-split representation of `A_inf` elements.
- **Uses from project**: `gaussValue_teichmuller_sub_le_of_le`, `exists_head_split`, `teichCoeff_zero_eq`, `teichCoeff`, `gaussTerm`, `gaussTerm_le_gaussValue`, `gaussValue`, `gaussValue_p_mul`, `gaussValue_sub_le`, `perfectoidValuation`, `OF`, `Ainf`
- **Used by**: unused in file (the `W(F)` analogue `exists_delta_teichCoeffF_sub` supersedes it downstream)
- **Visibility**: public
- **Lines**: 159–218 (proof ≈ 55 lines)
- **Notes**: proof > 30 lines. Not referenced anywhere else in the project.

---

## Part 2 — `F` is perfect (Tate absorption)

### `theorem exists_mul_pow_isPowerBounded`
- **Type**: `(ϖ : PseudoUniformizer F) (x : F) : ∃ k : ℕ, IsPowerBounded (x * ((ϖ.val : Fˣ) : F) ^ k)`
- **What**: Tate absorption — any element of `F` becomes power-bounded (lands in `O_F`) after multiplying by a sufficiently large power of a pseudo-uniformizer.
- **How**: `ϖ.isTopologicallyNilpotent` gives `ϖ^k → 0`; multiplying by the constant `x` (`Filter.Tendsto.const_mul`, then `mul_zero`) keeps the limit `0`. A pair of definition (`IsHuberRing.exists_pairOfDefinition`) makes `powerBoundedSubring F` open, hence a neighbourhood of `0` via `isOpen_powerBoundedSubring.mem_nhds isPowerBounded_zero`, and `Tendsto.eventually_mem … .exists` produces the index `k`.
- **Hypotheses**: `F` is a Huber/Tate ring with a pseudo-uniformizer; `hPF` explicitly included.
- **Uses from project**: `PseudoUniformizer`, `PseudoUniformizer.isTopologicallyNilpotent`, `IsPowerBounded`, `isPowerBounded_zero`, `powerBoundedSubring`, `isOpen_powerBoundedSubring`, `IsHuberRing.exists_pairOfDefinition`
- **Used by**: `instPerfectRingF`
- **Visibility**: public
- **Lines**: 219–233 (proof ≈ 11 lines)
- **Notes**: preceded by `include hPF in` (line 217).

### `instance instPerfectRingF`
- **Type**: `PerfectRing F p`
- **What**: The perfectoid field `F` of characteristic `p` is a perfect ring — Frobenius is bijective on `F`, not merely on `O_F`. This is what makes `frobeniusEquiv F p` (and hence `teichCoeffF`) exist.
- **How**: `PerfectRing.ofSurjective`: given `x : F`, absorb it into `O_F` with `exists_mul_pow_isPowerBounded` at the canonical `IsTateRing.pseudoUniformizer`, then bump the exponent to `p·k` (rewriting `x·ϖ^{pk} = (x·ϖ^k)·ϖ^{(p−1)k}` and closing with `isPowerBounded_mul`), take a `p`-th root `b ∈ O_F` via `frobenius_surjective_OF`, and divide by `ϖ^k`: `(b·ϖ^{-k})^p = x·ϖ^{pk}·ϖ^{-pk} = x` by `mul_inv_cancel₀` on `(ϖ : Fˣ).ne_zero`.
- **Hypotheses**: `IsPerfectoidField p F`, `CharP F p`, `F` Tate (for the pseudo-uniformizer).
- **Uses from project**: `exists_mul_pow_isPowerBounded`, `IsTateRing.pseudoUniformizer`, `PseudoUniformizer`, `PseudoUniformizer.isTopologicallyNilpotent`, `frobenius_surjective_OF`, `IsPowerBounded`, `isPowerBounded_mul`, `isPowerBounded_one`, `OF`
- **Used by**: unused in file *by name*, but used pervasively as an **instance** — every occurrence of `frobeniusEquiv F p` (i.e. all of `teichCoeffF`) depends on it.
- **Visibility**: public (instance)
- **Lines**: 234–266 (proof ≈ 32 lines)
- **Notes**: proof > 30 lines. Load-bearing instance despite "no named user".

---

## Part 3 — Teichmüller coordinates over `W(F)`

### `def teichCoeffF`
- **Type**: `(x : WittVector p F) (n : ℕ) : F := (((_root_.frobeniusEquiv F p).symm ^ n : RingAut F)) (x.coeff n)`
- **What**: The `n`-th Teichmüller coordinate (digit) of a Witt vector over the *field* `F`: the `n`-th Witt coefficient pulled back through `n` inverse Frobenii.
- **How**: Direct definition; well-defined because `instPerfectRingF` supplies the Frobenius automorphism `frobeniusEquiv F p` on `F`. This is the `W(F)`-analogue of `teichCoeff` on `A_inf = W(O_F)`.
- **Hypotheses**: `F` perfect of characteristic `p` (supplied by `instPerfectRingF`).
- **Uses from project**: `[]` (only the `instPerfectRingF` instance, implicitly)
- **Used by**: 35 declarations — `bddAbove_gaussTermF_add`, `bddAbove_gaussTermF_of_coords_shift`, `bddAbove_gaussTermF_of_tail`, `bddAbove_gaussTermF_teichmuller`, `degF_spec`, `exists_delta_teichCoeffF_sub`, `exists_eq_sum_teichCoeffF_add`, `exists_fold_teichmuller_headsF`, `exists_gaussValueF_eq_gaussTermF`, `exists_head_splitF`, `exists_iter_splitF`, `exists_list_head_splitF`, `gaussTermF`, `gaussTermF_mul_le`, `gaussValueF_add_le`, `gaussValueF_finset_sum_le`, `gaussValueF_sub_prefix`, `gaussValueF_teichmuller`, `headBoundF`, `mul_gaussValueF_le_of_tail`, `tailValueF_add_le`, `tailValueF_add_le_gaussValueF`, `tailValueF_eq_of_coords`, `teichCoeffF_eq_of_sub_eq_pow_mul`, `teichCoeffF_map`, `teichCoeffF_p_mul`, `teichCoeffF_p_mul_zero`, `teichCoeffF_sum_range_add`, `teichCoeffF_teichmuller_mul`, `tendsto_gaussTermF_add_of_tendsto`, `tendsto_headBoundF_of_tendsto`, `twoBddSubring`, `valuation_teichCoeffF_prefix_add_le`, `valuation_teichCoeffF_teichmuller_add_le`, `valuation_teichCoeffF_teichmuller_add_le_left`
- **Visibility**: public
- **Lines**: 267–269 (definition, 2 lines)
- **Notes**: the central definition of the file.

### `theorem frobeniusEquivF_symm_pow_pow_cancel`
- **Type**: `(b : F) (j : ℕ) : ((_root_.frobeniusEquiv F p).symm ^ j : RingAut F) (b ^ p ^ j) = b`
- **What**: The `j`-fold inverse Frobenius undoes raising to the `p^j`-th power on `F`.
- **How**: Induction on `j`. The step rewrites `b^{p^{k+1}} = (b^{p^k})^p`, recognises `(b^{p^k})^p = frobeniusEquiv F p (b^{p^k})` (via `frobeniusEquiv_apply` + `frobenius_def`) so `RingEquiv.symm_apply_apply` peels one layer, then applies the induction hypothesis through `RingAut.mul_apply`.
- **Hypotheses**: `F` perfect char `p`.
- **Uses from project**: `[]`
- **Used by**: `teichCoeffF_sum_range_add`
- **Visibility**: public
- **Lines**: 270–283 (proof ≈ 12 lines)
- **Notes**: `F`-side twin of `frobeniusEquiv_symm_pow_pow_cancel` in `GaussNorm.lean`.

### `theorem exists_eq_sum_teichCoeffF_add`
- **Type**: `(x : WittVector p F) (N : ℕ) : ∃ z, x = (∑ i ∈ Finset.range N, [teichCoeffF p F x i] * (p : WittVector p F) ^ i) + (p : WittVector p F) ^ N * z`
- **What**: "CORE-2 over `F`" — every Witt vector over `F` is its length-`N` Teichmüller prefix plus a `p^N`-multiple tail.
- **How**: `N = 0` is trivial (`z = x`). For `N = n+1`, mathlib's `WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff` gives `x − ∑_{i ≤ n} [σ^{-i}(x_i)]·p^i = p^{n+1}·w`; the sum over `Finset.Iic n` is converted to `Finset.range (n+1)` (`Nat.lt_succ_iff`) and the summands rewritten by unfolding `teichCoeffF`, then `sub_eq_iff_eq_add'`.
- **Hypotheses**: none beyond the ambient perfect char-`p` field.
- **Uses from project**: `teichCoeffF`
- **Used by**: `exists_head_splitF`, `exists_iter_splitF`, `teichCoeffF_teichmuller_mul`
- **Visibility**: public
- **Lines**: 284–303 (proof ≈ 15 lines)
- **Notes**: none.

### `theorem teichCoeffF_sum_range_add`
- **Type**: `{N : ℕ} (b : ℕ → F) (z : WittVector p F) {j : ℕ} (hj : j < N) : teichCoeffF p F ((∑ i ∈ Finset.range N, [b i] * p ^ i) + p ^ N * z) j = b j`
- **What**: "CORE-1 over `F`" — uniqueness of Teichmüller expansions: the digits read off a prefix-plus-`p^N`-tail expression are exactly the prescribed `b j`.
- **How**: Two steps. (i) `WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero` + `WittVector.mul_pow_charP_coeff_zero` kill the `p^N·z` term in coefficients below `N`. (ii) The prefix's `j`-th coefficient collapses to a single summand: `WittVector.sum_coeff_eq_coeff_sum` (with a pairwise-disjointness side goal discharged from `WittVector.teichmuller_mul_pow_coeff_of_ne`) plus `Finset.sum_eq_single j` and `WittVector.teichmuller_mul_pow_coeff` give `(b j)^{p^j}`. Finally `frobeniusEquivF_symm_pow_pow_cancel` extracts `b j`.
- **Hypotheses**: `j < N` — the digit must lie inside the prefix.
- **Uses from project**: `teichCoeffF`, `frobeniusEquivF_symm_pow_pow_cancel`
- **Used by**: `bddAbove_gaussTermF_add`, `exists_head_splitF`, `exists_iter_splitF`, `gaussValueF_add_le`, `teichCoeffF_teichmuller_mul`
- **Visibility**: public
- **Lines**: 304–336 (proof ≈ 25 lines)
- **Notes**: the workhorse "read off a digit" lemma of the file.

### `theorem frobeniusEquivF_symm_subtype`
- **Type**: `(z : OF F) : (_root_.frobeniusEquiv F p).symm ((z : OF F) : F) = (((_root_.frobeniusEquiv (OF F) p).symm z : OF F) : F)`
- **What**: The inverse Frobenius commutes with the inclusion `O_F ↪ F` (one step).
- **How**: Apply `RingEquiv.symm_apply_eq` to reduce to `frobeniusEquiv F p` of the right-hand side; both sides then become the `p`-th power of the `O_F`-root, and `RingEquiv.apply_symm_apply` on `frobeniusEquiv (OF F) p` (with `frobenius_def`) shows that power is `z`. The coercion `((w^p : OF F) : F) = ((w : F))^p` is `rfl`.
- **Hypotheses**: both `F` and `O_F` are perfect (the `O_F` side from `IsPerfectoidField`, the `F` side from `instPerfectRingF`).
- **Uses from project**: `OF`
- **Used by**: `frobeniusEquivF_symm_pow_subtype`
- **Visibility**: public
- **Lines**: 337–350 (proof ≈ 11 lines)
- **Notes**: none.

### `theorem frobeniusEquivF_symm_pow_subtype`
- **Type**: `(z : OF F) (k : ℕ) : ((_root_.frobeniusEquiv F p).symm ^ k : RingAut F) ((z : OF F) : F) = ((((_root_.frobeniusEquiv (OF F) p).symm ^ k : RingAut (OF F)) z : OF F) : F)`
- **What**: Iterated version of the previous lemma: `k` inverse Frobenii commute with `O_F ↪ F`.
- **How**: Induction on `k` generalising `z`; the step splits both `pow_succ`s through `RingAut.mul_apply` and applies `frobeniusEquivF_symm_subtype` once followed by the induction hypothesis.
- **Hypotheses**: as above.
- **Uses from project**: `frobeniusEquivF_symm_subtype`, `OF`
- **Used by**: `teichCoeffF_map`
- **Visibility**: public
- **Lines**: 351–361 (proof ≈ 7 lines)
- **Notes**: none.

### `theorem teichCoeffF_map`
- **Type**: `(a : Ainf p F) (n : ℕ) : teichCoeffF p F (WittVector.map ((powerBoundedSubring.toSubring F).subtype) a) n = ((teichCoeff p F a n : OF F) : F)`
- **What**: Coordinate transport along `W(O_F) → W(F)`: the `F`-digits of the image of an `A_inf`-element are the coercions of its `O_F`-digits.
- **How**: Unfold both `teichCoeffF` and `teichCoeff`, push the coefficient through `WittVector.map_coeff`, and close with `frobeniusEquivF_symm_pow_subtype` applied to `a.coeff n`.
- **Hypotheses**: `a : Ainf p F = W(O_F)`.
- **Uses from project**: `teichCoeffF`, `frobeniusEquivF_symm_pow_subtype`, `teichCoeff`, `powerBoundedSubring.toSubring`, `OF`, `Ainf`
- **Used by**: `gaussTermF_map`, `valuation_teichCoeffF_prefix_add_le`, `valuation_teichCoeffF_teichmuller_add_le_left`
- **Visibility**: public
- **Lines**: 362–375 (proof ≈ 3 lines)
- **Notes**: the bridge that lets every `W(O_F)` fact be reused over `W(F)`.

---

## Part 4 — The Gauss value over `W(F)` (boundedness-threaded)

### `def gaussTermF`
- **Type**: `(ρ : NNReal) (x : WittVector p F) (n : ℕ) : NNReal := ρ ^ n * perfectoidValuation p F (teichCoeffF p F x n)`
- **What**: The `n`-th Gauss term of a Witt vector over `F` at radius `ρ`.
- **How**: Direct definition, mirroring `gaussTerm` on `A_inf` but with no `≤ 1` bound available (coordinates in `F` are unbounded).
- **Hypotheses**: `ρ : NNReal`.
- **Uses from project**: `teichCoeffF`, `perfectoidValuation`
- **Used by**: 46 declarations (essentially the whole rest of the file — see the `BddAbove (Set.range (gaussTermF …))` hypothesis threaded through every later statement).
- **Visibility**: public
- **Lines**: 376–380 (definition, 2 lines)
- **Notes**: none.

### `def gaussValueF`
- **Type**: `(ρ : NNReal) (x : WittVector p F) : NNReal := ⨆ n, gaussTermF p F ρ x n`
- **What**: The Gauss value `w_ρ(x)` of `x : W(F)` — the sup of its Gauss terms; junk value `0` when the terms are unbounded.
- **How**: `iSup` in `NNReal`. Because `NNReal`'s `iSup` returns junk on unbounded families, every consuming lemma carries an explicit `BddAbove (Set.range (gaussTermF p F ρ x))` hypothesis rather than the global `≤ 1` bound available on `A_inf`.
- **Hypotheses**: `ρ : NNReal`.
- **Uses from project**: `gaussTermF`
- **Used by**: 27 declarations, including `gaussValueF_add_le`, `gaussValueF_mul_le`, `gaussValueF_p_mul`, `degF`, `tailValueF_eq_of_coords`.
- **Visibility**: public
- **Lines**: 381–383 (definition, 2 lines)
- **Notes**: none.

### `theorem gaussTermF_le_gaussValueF`
- **Type**: `{ρ : NNReal} {x : WittVector p F} (hB : BddAbove (Set.range (gaussTermF p F ρ x))) (n : ℕ) : gaussTermF p F ρ x n ≤ gaussValueF p F ρ x`
- **What**: Each Gauss term is dominated by the Gauss value, provided the terms are bounded.
- **How**: `le_ciSup hB n` — a one-liner, but it is the point where boundedness is consumed.
- **Hypotheses**: `BddAbove (Set.range (gaussTermF p F ρ x))` — essential, since without it `⨆` is junk.
- **Uses from project**: `gaussTermF`, `gaussValueF`
- **Used by**: `exists_delta_teichCoeffF_sub`, `exists_list_head_splitF`, `gaussTermF_mul_le`, `gaussValueF_p_mul`, `mul_gaussValueF_le_of_tail`
- **Visibility**: public
- **Lines**: 384–389 (term-mode, 1 line)
- **Notes**: none.

### `theorem teichCoeffF_teichmuller_mul`
- **Type**: `(w : F) (s : WittVector p F) (j : ℕ) : teichCoeffF p F ([w] * s) j = w * teichCoeffF p F s j`
- **What**: Scaling by a Teichmüller lift scales every digit by `w`.
- **How**: Expand `s` via `exists_eq_sum_teichCoeffF_add` at level `j+1`, multiply through by `[w]` (`map_mul` turns `[w]·[s_i]` into `[w·s_i]`), so `[w]·s` is again in prefix-plus-`p^{j+1}`-tail normal form with digits `w · teichCoeffF s i`; `teichCoeffF_sum_range_add` reads off digit `j`.
- **Hypotheses**: none beyond the ambient setting.
- **Uses from project**: `exists_eq_sum_teichCoeffF_add`, `teichCoeffF_sum_range_add`, `teichCoeffF`
- **Used by**: `gaussTermF_teichmuller_mul`, `valuation_teichCoeffF_prefix_add_le`, `valuation_teichCoeffF_teichmuller_add_le_left`
- **Visibility**: public
- **Lines**: 390–403 (proof ≈ 10 lines)
- **Notes**: none.

### `theorem exists_head_splitF`
- **Type**: `(x : WittVector p F) : ∃ x', x = [teichCoeffF p F x 0] + (p : WittVector p F) * x' ∧ ∀ k, teichCoeffF p F x' k = teichCoeffF p F x (k + 1)`
- **What**: Head split over `F`: peel off the `0`-th Teichmüller digit; the tail witness carries the shifted digits.
- **How**: `exists_eq_sum_teichCoeffF_add` at `N = 1` gives `x = [x₀] + p·z`. To identify `z`'s digits, expand `z` at level `k+1`, multiply by `p` (shifting exponents), and reassemble `x` as a length-`(k+2)` prefix whose digit function is `Nat.casesOn i x₀ (fun i' => z_{i'})` via `Finset.sum_range_succ'`; `teichCoeffF_sum_range_add` at `j = k+1` then equates `z`'s `k`-th digit with `x`'s `(k+1)`-st.
- **Hypotheses**: none beyond the ambient setting.
- **Uses from project**: `exists_eq_sum_teichCoeffF_add`, `teichCoeffF_sum_range_add`, `teichCoeffF`
- **Used by**: `exists_delta_teichCoeffF_sub`, `exists_fold_teichmuller_headsF`, `exists_list_head_splitF`
- **Visibility**: public
- **Lines**: 404–443 (proof ≈ 34 lines)
- **Notes**: proof > 30 lines.

### `private theorem valuation_teichCoeffF_teichmuller_add_le_left`
- **Type**: `{a b : F} (h : perfectoidValuation p F b ≤ perfectoidValuation p F a) (j : ℕ) : perfectoidValuation p F (teichCoeffF p F ([a] + [b]) j) ≤ perfectoidValuation p F a`
- **What**: One-sided pair bound: if `|b| ≤ |a|` then every digit of `[a] + [b]` has valuation at most `|a|`.
- **How**: The `u = b/a` trick. If `a = 0` then `b = 0` by `Valuation.zero_iff` and everything is `0`. Otherwise `|b/a| ≤ 1`, so `perfectoidValuation_integers.exists_of_le_one` lifts `b/a` to `u : O_F`, giving `[a] + [b] = [a]·(1 + [u])`. Then `teichCoeffF_teichmuller_mul` + `Valuation.map_mul` reduce to showing every digit of `1 + [u]` is `≤ 1`, which follows because `1 + [u]` is the image of an `A_inf`-element under `WittVector.map`, so `teichCoeffF_map` + `perfectoidValuation_le_one` apply.
- **Hypotheses**: `|b| ≤ |a|` (the "left-dominant" case).
- **Uses from project**: `teichCoeffF`, `teichCoeffF_map`, `teichCoeffF_teichmuller_mul`, `perfectoidValuation`, `perfectoidValuation_integers`, `perfectoidValuation_le_one`, `powerBoundedSubring.toSubring`, `OF`
- **Used by**: `valuation_teichCoeffF_teichmuller_add_le`
- **Visibility**: **private**
- **Lines**: 444–485 (proof ≈ 36 lines)
- **Notes**: proof > 30 lines.

### `theorem valuation_teichCoeffF_teichmuller_add_le`
- **Type**: `(a b : F) (j : ℕ) : perfectoidValuation p F (teichCoeffF p F ([a] + [b]) j) ≤ max (perfectoidValuation p F a) (perfectoidValuation p F b)`
- **What**: Symmetric pair bound: every digit of a two-Teichmüller sum is bounded by `max |a| |b|`.
- **How**: `le_total` on the two valuations; each branch is the private one-sided lemma `valuation_teichCoeffF_teichmuller_add_le_left`, with `add_comm` in the second branch.
- **Hypotheses**: none.
- **Uses from project**: `valuation_teichCoeffF_teichmuller_add_le_left`, `teichCoeffF`, `perfectoidValuation`
- **Used by**: `bddAbove_gaussTermF_teichmuller_add`, `exists_fold_teichmuller_headsF`, `gaussValueF_teichmuller_add_le`
- **Visibility**: public
- **Lines**: 486–495 (proof ≈ 5 lines)
- **Notes**: none.

### `theorem bddAbove_gaussTermF_of_tail`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) {x x' : WittVector p F} (hcoords : ∀ k, teichCoeffF p F x' k = teichCoeffF p F x (k + 1)) (hB : BddAbove (Set.range (gaussTermF p F ρ x))) : BddAbove (Set.range (gaussTermF p F ρ x'))`
- **What**: Term-boundedness propagates from a Witt vector to its head-split tail.
- **How**: If `M` bounds `x`'s terms, `M/ρ` bounds `x'`'s: the identity `ρ · gaussTermF ρ x' k = gaussTermF ρ x (k+1)` (unfold both, use `hcoords k` and `pow_succ`) plus `le_div_iff₀ hρ0`.
- **Hypotheses**: `0 < ρ` (needed to divide), and the coordinate-shift relation.
- **Uses from project**: `gaussTermF`, `teichCoeffF`
- **Used by**: `exists_delta_teichCoeffF_sub`, `exists_fold_teichmuller_headsF`, `exists_list_head_splitF`
- **Visibility**: public
- **Lines**: 496–510 (proof ≈ 9 lines)
- **Notes**: none.

### `theorem mul_gaussValueF_le_of_tail`
- **Type**: `{ρ : NNReal} {x x' : WittVector p F} (hB : BddAbove (Set.range (gaussTermF p F ρ x))) (hcoords : ∀ k, teichCoeffF p F x' k = teichCoeffF p F x (k + 1)) : ρ * gaussValueF p F ρ x' ≤ gaussValueF p F ρ x`
- **What**: The tail estimate `ρ·w_ρ(x') ≤ w_ρ(x)` for a head-split tail.
- **How**: `NNReal.mul_iSup` pushes `ρ` inside the sup, then `ciSup_le`; each term becomes `gaussTermF ρ x (k+1)` by the shift identity and is bounded by `gaussTermF_le_gaussValueF p F hB (k+1)`.
- **Hypotheses**: term-boundedness of `x` and the coordinate shift.
- **Uses from project**: `gaussTermF`, `gaussTermF_le_gaussValueF`, `gaussValueF`, `teichCoeffF`
- **Used by**: `exists_delta_teichCoeffF_sub`, `exists_fold_teichmuller_headsF`, `exists_list_head_splitF`
- **Visibility**: public
- **Lines**: 511–523 (proof ≈ 8 lines)
- **Notes**: none.

### `theorem gaussValueF_teichmuller_add_le`
- **Type**: `{ρ : NNReal} (hρ1 : ρ < 1) (a b : F) : gaussValueF p F ρ ([a] + [b]) ≤ max (perfectoidValuation p F a) (perfectoidValuation p F b)`
- **What**: The Gauss value of a two-Teichmüller sum is at most the max of the two valuations.
- **How**: `ciSup_le` over terms; each term `ρ^j · |digit_j|` loses the `ρ^j ≤ 1` factor (`pow_le_one₀`, `mul_le_of_le_one_left`) and then `valuation_teichCoeffF_teichmuller_add_le` bounds the digit.
- **Hypotheses**: `ρ < 1`.
- **Uses from project**: `gaussTermF`, `gaussValueF`, `valuation_teichCoeffF_teichmuller_add_le`, `perfectoidValuation`
- **Used by**: `exists_fold_teichmuller_headsF`
- **Visibility**: public
- **Lines**: 524–533 (proof ≈ 5 lines)
- **Notes**: none.

### `theorem bddAbove_gaussTermF_teichmuller_add`
- **Type**: `{ρ : NNReal} (hρ1 : ρ < 1) (a b : F) : BddAbove (Set.range (gaussTermF p F ρ ([a] + [b])))`
- **What**: The Gauss terms of a two-Teichmüller sum are bounded (by `max |a| |b|`).
- **How**: Exhibit the bound `max |a| |b|` explicitly and repeat the estimate of the previous lemma pointwise: `pow_le_one₀` on `ρ^j` then `valuation_teichCoeffF_teichmuller_add_le`.
- **Hypotheses**: `ρ < 1`.
- **Uses from project**: `gaussTermF`, `valuation_teichCoeffF_teichmuller_add_le`, `perfectoidValuation`
- **Used by**: `exists_fold_teichmuller_headsF`
- **Visibility**: public
- **Lines**: 534–543 (proof ≈ 5 lines)
- **Notes**: none.

### `private theorem exists_list_head_splitF`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (s B : NNReal) (L : List (WittVector p F)) (hL : ∀ w ∈ L, BddAbove (Set.range (gaussTermF p F ρ w)) ∧ s * gaussValueF p F ρ w ≤ B) : ∃ hl tl, L.sum = (hl.map ([·])).sum + p * tl.sum ∧ (∀ h ∈ hl, s * |h| ≤ B) ∧ ∀ t ∈ tl, BddAbove (…) ∧ s * (ρ * gaussValueF p F ρ t) ≤ B`
- **What**: Head-split a whole list of Witt vectors at once, separating a list of Teichmüller heads from a `p`-multiplied list of tails, with the value bounds carried along.
- **How**: Induction on `L`. Each `cons` applies `exists_head_splitF` to the head vector; the head's valuation is bounded because `gaussTermF_le_gaussValueF … 0` says `|w₀| ≤ w_ρ(w)`; the tail's boundedness and value bound come from `bddAbove_gaussTermF_of_tail` and `mul_gaussValueF_le_of_tail`, both scaled by `s` with `mul_le_mul_of_nonneg_left`.
- **Hypotheses**: `0 < ρ`; every list member is boundedly termed with `s·w_ρ ≤ B`.
- **Uses from project**: `exists_head_splitF`, `bddAbove_gaussTermF_of_tail`, `mul_gaussValueF_le_of_tail`, `gaussTermF`, `gaussTermF_le_gaussValueF`, `gaussValueF`, `teichCoeffF`, `perfectoidValuation`
- **Used by**: `exists_level_repF`
- **Visibility**: **private**
- **Lines**: 544–579 (proof ≈ 24 lines)
- **Notes**: none.

### `private theorem exists_fold_teichmuller_headsF`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (s B : NNReal) (l : List F) (hl : ∀ h ∈ l, s * |h| ≤ B) : ∃ c P, (l.map ([·])).sum = [c] + p * P.sum ∧ s * |c| ≤ B ∧ ∀ w ∈ P, BddAbove (…) ∧ s * (ρ * gaussValueF p F ρ w) ≤ B`
- **What**: Fold a list of Teichmüller lifts into a *single* Teichmüller lift plus a `p`-multiple pool, keeping the bound `s·|c| ≤ B`.
- **How**: Induction on the list. Each step adds `[h]` to the already-folded `[c]` and head-splits the two-Teichmüller sum `[h] + [c]` via `exists_head_splitF`; the new head is bounded by `valuation_teichCoeffF_teichmuller_add_le … 0`, and the new pool member's value by `mul_gaussValueF_le_of_tail` composed with `gaussValueF_teichmuller_add_le`, using `bddAbove_gaussTermF_teichmuller_add` for boundedness and `nnreal_mul_max` to distribute `s` over the max.
- **Hypotheses**: `0 < ρ < 1`; every list entry satisfies `s·|h| ≤ B`.
- **Uses from project**: `exists_head_splitF`, `bddAbove_gaussTermF_of_tail`, `bddAbove_gaussTermF_teichmuller_add`, `gaussValueF_teichmuller_add_le`, `mul_gaussValueF_le_of_tail`, `valuation_teichCoeffF_teichmuller_add_le`, `gaussTermF`, `gaussValueF`, `teichCoeffF`, `perfectoidValuation`, `nnreal_mul_max`
- **Used by**: `exists_level_repF`
- **Visibility**: **private**
- **Lines**: 580–619 (proof ≈ 30 lines)
- **Notes**: proof ≈ 30 lines.

### `private theorem exists_level_repF`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x y : WittVector p F} (hBx hBy : BddAbove …) (n : ℕ) : ∃ b L, x + y = (∑ i ∈ Finset.range n, [b i] * p ^ i) + p ^ n * L.sum ∧ (∀ i < n, ρ^i * |b i| ≤ max (w_ρ x) (w_ρ y)) ∧ ∀ w ∈ L, BddAbove (…) ∧ ρ^n * w_ρ w ≤ max (w_ρ x) (w_ρ y)`
- **What**: The level representation of a sum: `x + y` written as a length-`n` Teichmüller expansion with digits obeying the ultrametric bound, plus a `p^n`-multiplied residual pool.
- **How**: Induction on `n`. Base case: pool `[x, y]`, empty digit constraint. Step: head-split the pool with `exists_list_head_splitF` (scale `s = ρ^n`), fold the resulting heads into one digit `c` with `exists_fold_teichmuller_headsF`, set the new digit function to `Function.update b n c` (using `Function.update_of_ne`/`Function.update_self` to prove the prefix identity via `Finset.sum_range_succ`), and concatenate the new pools; the exponent bookkeeping `ρ^{n+1} = ρ^n·ρ` is `pow_succ` + `mul_assoc`.
- **Hypotheses**: `0 < ρ < 1`; both `x` and `y` boundedly termed.
- **Uses from project**: `exists_list_head_splitF`, `exists_fold_teichmuller_headsF`, `gaussTermF`, `gaussValueF`, `perfectoidValuation`
- **Used by**: `bddAbove_gaussTermF_add`, `gaussValueF_add_le`
- **Visibility**: **private**
- **Lines**: 620–676 (proof ≈ 43 lines)
- **Notes**: proof > 30 lines. This is the combinatorial heart of the ultrametric inequality over `W(F)`.

### `theorem gaussValueF_add_le`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x y : WittVector p F} (hBx hBy : BddAbove …) : gaussValueF p F ρ (x + y) ≤ max (gaussValueF p F ρ x) (gaussValueF p F ρ y)`
- **What**: The ultrametric (strong triangle) inequality for the Gauss value over `W(F)`.
- **How**: `ciSup_le` over `j`; for each `j` invoke `exists_level_repF` at level `j+1`, read off `teichCoeffF (x+y) j = b j` with `teichCoeffF_sum_range_add`, and quote the digit bound from the representation.
- **Hypotheses**: `0 < ρ < 1`; both arguments boundedly termed.
- **Uses from project**: `exists_level_repF`, `teichCoeffF_sum_range_add`, `gaussTermF`, `gaussValueF`, `teichCoeffF`
- **Used by**: `exists_delta_teichCoeffF_sub`, `gaussValueF_finset_sum_le`, `tailValueF_add_le`
- **Visibility**: public
- **Lines**: 677–691 (proof ≈ 9 lines)
- **Notes**: headline result of Part 4.

### `theorem gaussTermF_map`
- **Type**: `{ρ : NNReal} (z : Ainf p F) (n : ℕ) : gaussTermF p F ρ (WittVector.map ((powerBoundedSubring.toSubring F).subtype) z) n = gaussTerm p F ρ z n`
- **What**: The `W(F)` Gauss term of the image of an `A_inf`-element equals its `A_inf` Gauss term.
- **How**: Unfold both definitions and apply `teichCoeffF_map`.
- **Hypotheses**: `z : Ainf p F`.
- **Uses from project**: `gaussTermF`, `teichCoeffF_map`, `gaussTerm`, `powerBoundedSubring.toSubring`, `Ainf`
- **Used by**: `bddAbove_gaussTermF_neg_one`, `bddAbove_gaussTermF_teichmuller_sub`, `gaussValueF_map`, `twoBddSubring`
- **Visibility**: public
- **Lines**: 692–696 (proof: 1 line)
- **Notes**: none.

### `theorem gaussValueF_map`
- **Type**: `{ρ : NNReal} (z : Ainf p F) : gaussValueF p F ρ (WittVector.map ((powerBoundedSubring.toSubring F).subtype) z) = gaussValue p F ρ z`
- **What**: The Gauss *value* is likewise preserved by `W(O_F) → W(F)`.
- **How**: Unfold both sups and apply `iSup_congr` with the termwise `gaussTermF_map`.
- **Hypotheses**: `z : Ainf p F`.
- **Uses from project**: `gaussTermF_map`, `gaussValueF`, `gaussValue`, `powerBoundedSubring.toSubring`, `Ainf`
- **Used by**: `gaussValueF_teichmuller_sub_le_of_le_scaled`
- **Visibility**: public
- **Lines**: 697–703 (proof: 2 lines)
- **Notes**: none.

### `theorem gaussTermF_teichmuller_mul`
- **Type**: `{ρ : NNReal} (w : F) (s : WittVector p F) (n : ℕ) : gaussTermF p F ρ ([w] * s) n = perfectoidValuation p F w * gaussTermF p F ρ s n`
- **What**: Gauss terms are exactly multiplicative under scaling by a Teichmüller lift.
- **How**: Unfold `gaussTermF`, apply `teichCoeffF_teichmuller_mul` and `Valuation.map_mul`, then `ring`.
- **Hypotheses**: none.
- **Uses from project**: `gaussTermF`, `teichCoeffF_teichmuller_mul`, `perfectoidValuation`
- **Used by**: `bddAbove_gaussTermF_teichmuller_sub`, `gaussValueF_teichmuller_mul`
- **Visibility**: public
- **Lines**: 704–709 (proof: 2 lines)
- **Notes**: none.

### `theorem gaussValueF_teichmuller_mul`
- **Type**: `{ρ : NNReal} (w : F) (s : WittVector p F) : gaussValueF p F ρ ([w] * s) = perfectoidValuation p F w * gaussValueF p F ρ s`
- **What**: The Gauss value is exactly multiplicative under Teichmüller scaling (an equality, not just `≤`).
- **How**: `NNReal.mul_iSup` moves the scalar inside, then `iSup_congr` with `gaussTermF_teichmuller_mul`.
- **Hypotheses**: none — no boundedness needed, because `NNReal.mul_iSup` holds unconditionally.
- **Uses from project**: `gaussTermF_teichmuller_mul`, `gaussValueF`, `perfectoidValuation`
- **Used by**: `gaussValueF_teichmuller_sub_le_of_le_scaled`
- **Visibility**: public
- **Lines**: 710–717 (proof: 2 lines)
- **Notes**: none.

### `theorem gaussValueF_teichmuller_sub_le_of_le_scaled`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ϖ : PseudoUniformizer F) (m : ℕ) {ε : NNReal} (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ∃ δ > 0, ∀ a b : F, |a| ≤ (|ϖ|⁻¹)^m → |b| ≤ (|ϖ|⁻¹)^m → |a − b| ≤ δ → gaussValueF p F ρ ([a] − [b]) ≤ ε`
- **What**: Scaled Teichmüller-difference continuity over `F`: on the ball of radius `(vϖ)^{-m}` the map `a ↦ [a]` is uniformly continuous for `w_ρ`.
- **How**: Multiply into `O_F` and pull back. Setting `c := |ϖ|`, the hypothesis `|a| ≤ (c⁻¹)^m` gives `|a·ϖ^m| ≤ 1`, so `perfectoidValuation_integers.exists_of_le_one` produces lifts `â, b̂ : O_F`; `|â − b̂| ≤ δT` where `δT` comes from the `O_F`-continuity `gaussValue_teichmuller_sub_le_of_le` applied with target `ε·c^m`. Transport back through the exact identity `[a] − [b] = [(ϖ^m)⁻¹] · map(([â] − [b̂]))`, then `gaussValueF_teichmuller_mul` and `gaussValueF_map` turn the value into `(c⁻¹)^m · gaussValue(…) ≤ (c⁻¹)^m·(ε·c^m) = ε` via `inv_mul_cancel₀`.
- **Hypotheses**: `0 < ρ < 1`, `0 < ε ≤ 1`, a pseudo-uniformizer `ϖ`, and both arguments in the `(vϖ)^{-m}` ball.
- **Uses from project**: `gaussValue_teichmuller_sub_le_of_le`, `gaussValueF_map`, `gaussValueF_teichmuller_mul`, `gaussValueF`, `gaussValue`, `perfectoidValuation`, `perfectoidValuation_integers`, `perfectoidValuation_le_one`, `PseudoUniformizer`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `powerBoundedSubring.toSubring`, `OF`
- **Used by**: `exists_delta_teichCoeffF_sub`
- **Visibility**: public
- **Lines**: 718–787 (proof ≈ 60 lines)
- **Notes**: proof > 30 lines.

---

## Part 5 — The `p`-shift and boundedness calculus

### `theorem teichCoeffF_p_mul`
- **Type**: `(x : WittVector p F) (n : ℕ) : teichCoeffF p F ((p : WittVector p F) * x) (n + 1) = teichCoeffF p F x n`
- **What**: Multiplication by `p` shifts Teichmüller digits up by one.
- **How**: `WittVector.mul_charP_coeff_succ` says `(x·p).coeff (n+1) = (x.coeff n)^p` in characteristic `p`; that extra `p`-th power is exactly cancelled by one of the `n+1` inverse Frobenii (`pow_succ` on the automorphism, `RingAut.mul_apply`, then `RingEquiv.symm_apply_apply` on `frobeniusEquiv F p`).
- **Hypotheses**: `CharP F p`.
- **Uses from project**: `teichCoeffF`
- **Used by**: `exists_delta_teichCoeffF_sub`, `gaussTermF_p_mul`
- **Visibility**: public
- **Lines**: 788–797 (proof ≈ 8 lines)
- **Notes**: none.

### `theorem teichCoeffF_p_mul_zero`
- **Type**: `(x : WittVector p F) : teichCoeffF p F ((p : WittVector p F) * x) 0 = 0`
- **What**: The `0`-th digit of `p·x` vanishes.
- **How**: `WittVector.mul_charP_coeff_zero` gives `(x·p).coeff 0 = 0`; the (identity) automorphism then sends `0` to `0`.
- **Hypotheses**: `CharP F p`.
- **Uses from project**: `teichCoeffF`
- **Used by**: `gaussTermF_p_mul_zero`
- **Visibility**: public
- **Lines**: 798–806 (proof ≈ 6 lines)
- **Notes**: none.

### `theorem gaussTermF_p_mul`
- **Type**: `{ρ : NNReal} (x : WittVector p F) (n : ℕ) : gaussTermF p F ρ ((p : WittVector p F) * x) (n + 1) = ρ * gaussTermF p F ρ x n`
- **What**: Term identity for the `p`-shift at positive index.
- **How**: Unfold, apply `teichCoeffF_p_mul` and `pow_succ`, then `ring`.
- **Hypotheses**: none.
- **Uses from project**: `gaussTermF`, `teichCoeffF_p_mul`
- **Used by**: `bddAbove_gaussTermF_p_mul`, `gaussValueF_p_mul`
- **Visibility**: public
- **Lines**: 807–811 (proof: 2 lines)
- **Notes**: none.

### `theorem gaussTermF_p_mul_zero`
- **Type**: `{ρ : NNReal} (x : WittVector p F) : gaussTermF p F ρ ((p : WittVector p F) * x) 0 = 0`
- **What**: The `0`-th Gauss term of `p·x` is `0`.
- **How**: Unfold and apply `teichCoeffF_p_mul_zero`, then `simp` (`Valuation.map_zero`).
- **Hypotheses**: none.
- **Uses from project**: `gaussTermF`, `teichCoeffF_p_mul_zero`
- **Used by**: `bddAbove_gaussTermF_p_mul`, `gaussValueF_p_mul`
- **Visibility**: public
- **Lines**: 812–816 (proof: 2 lines)
- **Notes**: none.

### `theorem bddAbove_gaussTermF_p_mul`
- **Type**: `{ρ : NNReal} {x : WittVector p F} (hB : BddAbove (Set.range (gaussTermF p F ρ x))) : BddAbove (Set.range (gaussTermF p F ρ ((p : WittVector p F) * x)))`
- **What**: Boundedness is inherited by `p·x`.
- **How**: If `M` bounds `x`'s terms then `ρ·M` bounds `p·x`'s: case-split on the index, using `gaussTermF_p_mul_zero` at `0` and `gaussTermF_p_mul` + `mul_le_mul_of_nonneg_left` at `n+1`.
- **Hypotheses**: boundedness of `x`.
- **Uses from project**: `gaussTermF`, `gaussTermF_p_mul`, `gaussTermF_p_mul_zero`
- **Used by**: `bddAbove_gaussTermF_p_pow_mul`, `gaussValueF_p_mul`
- **Visibility**: public
- **Lines**: 817–829 (proof ≈ 8 lines)
- **Notes**: none.

### `theorem gaussValueF_p_mul`
- **Type**: `{ρ : NNReal} {x : WittVector p F} (hB : BddAbove …) : gaussValueF p F ρ ((p : WittVector p F) * x) = ρ * gaussValueF p F ρ x`
- **What**: Exact `p`-shift for the Gauss value: `w_ρ(p·x) = ρ·w_ρ(x)`.
- **How**: `NNReal.mul_iSup` then `le_antisymm` of two `ciSup_le`s. `≤`: index `0` contributes `0`, index `n+1` reduces by `gaussTermF_p_mul` to `ρ·gaussTermF ρ x n` and is bounded by `le_ciSup` with the explicit bound `ρ·w_ρ(x)` (from `gaussTermF_le_gaussValueF`). `≥`: rewrite backwards through `gaussTermF_p_mul` and use `le_ciSup (bddAbove_gaussTermF_p_mul …) (n+1)`.
- **Hypotheses**: boundedness of `x` (needed on both directions to make the sups meaningful).
- **Uses from project**: `bddAbove_gaussTermF_p_mul`, `gaussTermF`, `gaussTermF_le_gaussValueF`, `gaussTermF_p_mul`, `gaussTermF_p_mul_zero`, `gaussValueF`
- **Used by**: `exists_delta_teichCoeffF_sub`, `gaussValueF_p_pow_mul`
- **Visibility**: public
- **Lines**: 830–847 (proof ≈ 14 lines)
- **Notes**: none.

### `theorem bddAbove_gaussTermF_add`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x y : WittVector p F} (hBx hBy : BddAbove …) : BddAbove (Set.range (gaussTermF p F ρ (x + y)))`
- **What**: The sum of two boundedly-termed Witt vectors is boundedly termed, with explicit bound `max (w_ρ x) (w_ρ y)`.
- **How**: Same mechanism as `gaussValueF_add_le`: for each index `j`, run `exists_level_repF` at level `j+1`, extract `teichCoeffF (x+y) j = b j` via `teichCoeffF_sum_range_add`, and use the representation's digit bound.
- **Hypotheses**: `0 < ρ < 1`; both summands boundedly termed.
- **Uses from project**: `exists_level_repF`, `teichCoeffF_sum_range_add`, `gaussTermF`, `gaussValueF`, `teichCoeffF`
- **Used by**: `exists_delta_teichCoeffF_sub`, `gaussValueF_finset_sum_le`, `tailValueF_add_le`, `tendsto_gaussTermF_add_of_tendsto`, `tendsto_gaussTermF_of_w_approx`, `twoBddSubring`
- **Visibility**: public
- **Lines**: 848–861 (proof ≈ 9 lines)
- **Notes**: none.

### `theorem bddAbove_gaussTermF_teichmuller_sub`
- **Type**: `{ρ : NNReal} (hρ1 : ρ < 1) (ϖ : PseudoUniformizer F) (a b : F) : BddAbove (Set.range (gaussTermF p F ρ ([a] − [b])))`
- **What**: The Gauss terms of *any* Teichmüller difference over `F` are bounded (no size hypothesis on `a`, `b`).
- **How**: Choose `m` with `max |a| |b| ≤ (c⁻¹)^m` where `c = |ϖ| < 1` (`perfectoidValuation_toOF_lt_one` plus `exists_pow_lt_of_lt_one` and `NNReal.lt_inv_iff_mul_lt`). Scale into `O_F` by `ϖ^m` (`perfectoidValuation_integers.exists_of_le_one`), write `[a] − [b] = [(ϖ^m)⁻¹]·map([â] − [b̂])`, and conclude with `gaussTermF_teichmuller_mul`, `gaussTermF_map` and the global `A_inf` bound `gaussTerm_le_one`.
- **Hypotheses**: `ρ < 1`, existence of a pseudo-uniformizer.
- **Uses from project**: `gaussTermF`, `gaussTermF_map`, `gaussTermF_teichmuller_mul`, `perfectoidValuation`, `perfectoidValuation_integers`, `perfectoidValuation_toOF_lt_one`, `gaussTerm_le_one`, `PseudoUniformizer`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `powerBoundedSubring.toSubring`, `OF`
- **Used by**: `exists_delta_teichCoeffF_sub`
- **Visibility**: public
- **Lines**: 862–922 (proof ≈ 56 lines)
- **Notes**: proof > 30 lines; shares the scaling boilerplate with `gaussValueF_teichmuller_sub_le_of_le_scaled` (duplication candidate).

### `theorem exists_delta_teichCoeffF_sub`
- **Type**: `(ϖ : PseudoUniformizer F) (n : ℕ) {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (m : ℕ) {ε : NNReal} (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ∃ δ > 0, ∀ x y : WittVector p F, BddAbove … x → BddAbove … y → BddAbove … (x−y) → w_ρ x ≤ (|ϖ|⁻¹)^m → w_ρ y ≤ (|ϖ|⁻¹)^m → w_ρ (x−y) ≤ δ → |teichCoeffF p F x n − teichCoeffF p F y n| ≤ ε`
- **What**: Per-coordinate uniform continuity over `W(F)` on value-bounded sets — the engine behind coordinates on the completion `A^r` (T903 step 4).
- **How**: Induction on `n`, generalising *both* `m` and `ε` (the scale must grow along the recursion). Level `0` is exact via additivity of `constantCoeff`. For `n+1`: head-split `x` and `y` (`exists_head_splitF`), form `p·(x'−y') = (x−y) + ([y₀]−[x₀])`; the head difference is small (it *is* `gaussTermF (x−y) 0`) so `gaussValueF_teichmuller_sub_le_of_le_scaled` bounds `w_ρ([y₀]−[x₀]) ≤ min (ρδn) 1`; `bddAbove_gaussTermF_teichmuller_sub` + `bddAbove_gaussTermF_add` supply the boundedness for `gaussValueF_add_le`, and `gaussValueF_p_mul` cancels the `p`. The scale hypothesis for the tails is re-derived by a local `hscaleup` claim: `mul_gaussValueF_le_of_tail` plus `ρ^K < c` (chosen by `exists_pow_lt_of_lt_one`) upgrades `(c⁻¹)^m` to `(c⁻¹)^{m+K}`.
- **Hypotheses**: `0 < ρ < 1`, `0 < ε ≤ 1`, a pseudo-uniformizer, boundedness of `x`, `y` and `x − y`, and value bounds `≤ (vϖ)^{-m}`.
- **Uses from project**: `exists_head_splitF`, `bddAbove_gaussTermF_add`, `bddAbove_gaussTermF_of_tail`, `bddAbove_gaussTermF_teichmuller_sub`, `gaussTermF`, `gaussTermF_le_gaussValueF`, `gaussValueF`, `gaussValueF_add_le`, `gaussValueF_p_mul`, `gaussValueF_teichmuller_sub_le_of_le_scaled`, `mul_gaussValueF_le_of_tail`, `teichCoeffF`, `teichCoeffF_p_mul`, `perfectoidValuation`, `perfectoidValuation_toOF_lt_one`, `PseudoUniformizer`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `OF`
- **Used by**: unused in file; **used downstream** in `FarguesFontaine/ArCompletion.lean`.
- **Visibility**: public
- **Lines**: 923–1052 (proof ≈ 118 lines)
- **Notes**: **longest proof in the file after `valuation_teichCoeffF_prefix_add_le`**; proof > 30 lines. Prime `/decompose-proof` candidate.

### `theorem bddAbove_gaussTermF_p_pow_mul`
- **Type**: `{ρ : NNReal} {x : WittVector p F} (hB : BddAbove …) (n : ℕ) : BddAbove (Set.range (gaussTermF p F ρ ((p : WittVector p F) ^ n * x)))`
- **What**: Boundedness for iterated `p`-power multiples.
- **How**: Induction on `n`, peeling `p^{m+1}·x = p·(p^m·x)` and applying `bddAbove_gaussTermF_p_mul`.
- **Hypotheses**: boundedness of `x`.
- **Uses from project**: `bddAbove_gaussTermF_p_mul`, `gaussTermF`
- **Used by**: `gaussTermF_mul_le`, `gaussValueF_p_pow_mul`
- **Visibility**: public
- **Lines**: 1053–1064 (proof ≈ 8 lines)
- **Notes**: none.

### `theorem gaussValueF_p_pow_mul`
- **Type**: `{ρ : NNReal} {x : WittVector p F} (hB : BddAbove …) (n : ℕ) : gaussValueF p F ρ ((p : WittVector p F) ^ n * x) = ρ ^ n * gaussValueF p F ρ x`
- **What**: Exact iterated `p`-shift: `w_ρ(p^n·x) = ρ^n·w_ρ(x)`.
- **How**: Induction on `n`, peeling one `p` and applying `gaussValueF_p_mul` with the boundedness supplied by `bddAbove_gaussTermF_p_pow_mul`, then `pow_succ` and `ring`.
- **Hypotheses**: boundedness of `x`.
- **Uses from project**: `bddAbove_gaussTermF_p_pow_mul`, `gaussValueF_p_mul`, `gaussTermF`, `gaussValueF`
- **Used by**: `gaussTermF_mul_le`, `gaussValueF_sub_prefix`
- **Visibility**: public
- **Lines**: 1065–1078 (proof ≈ 9 lines)
- **Notes**: none.

### `theorem bddAbove_gaussTermF_teichmuller`
- **Type**: `{ρ : NNReal} (c : F) : BddAbove (Set.range (gaussTermF p F ρ ([c] : WittVector p F)))`
- **What**: The Gauss terms of a single Teichmüller lift are bounded (by `|c|`; all terms above index `0` vanish).
- **How**: Exhibit `|c|`; index `0` gives exactly `|c|` (`WittVector.teichmuller_coeff_zero`) and every positive index gives `0` (`WittVector.teichmuller_coeff_pos`).
- **Hypotheses**: none.
- **Uses from project**: `gaussTermF`, `teichCoeffF`, `perfectoidValuation`
- **Used by**: `gaussTermF_mul_le`
- **Visibility**: public
- **Lines**: 1079–1089 (proof ≈ 7 lines)
- **Notes**: none.

### `theorem gaussValueF_finset_sum_le`
- **Type**: `{ι : Type*} {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (B : NNReal) (s : Finset ι) (f : ι → WittVector p F) (hf : ∀ i ∈ s, BddAbove … ∧ gaussValueF p F ρ (f i) ≤ B) : BddAbove (Set.range (gaussTermF p F ρ (∑ i ∈ s, f i))) ∧ gaussValueF p F ρ (∑ i ∈ s, f i) ≤ B`
- **What**: Ultrametric bound for finite sums over `W(F)`, bundled with boundedness of the sum.
- **How**: `Finset.induction_on`. Empty sum: all digits of `0` vanish. Insert step: `Finset.sum_insert` then `bddAbove_gaussTermF_add` for the boundedness half and `gaussValueF_add_le` + `max_le` for the value half.
- **Hypotheses**: `0 < ρ < 1`; every summand boundedly termed with value `≤ B`.
- **Uses from project**: `bddAbove_gaussTermF_add`, `gaussValueF_add_le`, `gaussTermF`, `gaussValueF`, `teichCoeffF`
- **Used by**: `gaussTermF_mul_le`
- **Visibility**: public
- **Lines**: 1090–1116 (proof ≈ 21 lines)
- **Notes**: `classical` used for the `Finset` induction.

### `theorem exists_iter_splitF`
- **Type**: `(x : WittVector p F) (n : ℕ) : ∃ X, x = (∑ i ∈ Finset.range n, [teichCoeffF p F x i] * p ^ i) + p ^ n * X ∧ ∀ k, teichCoeffF p F X k = teichCoeffF p F x (n + k)`
- **What**: Iterated head split: the level-`n` Teichmüller prefix of `x` plus a `p^n`-multiple witness `X` whose digits are `x`'s digits shifted by `n`.
- **How**: `exists_eq_sum_teichCoeffF_add` supplies `X`; identifying `X`'s digits needs a second expansion of `X` at level `k+1` and reassembly of `x` as one long prefix of length `n + (k+1)` with digit function `if i < n then x_i else X_{i−n}` (`Finset.sum_range_add`, `pow_add`, `dif_pos`/`dif_neg`), after which `teichCoeffF_sum_range_add` at `j = n + k` reads off the digit and `dif_neg` reduces it to `teichCoeffF X k`.
- **Hypotheses**: none.
- **Uses from project**: `exists_eq_sum_teichCoeffF_add`, `teichCoeffF_sum_range_add`, `teichCoeffF`
- **Used by**: `gaussTermF_mul_le`, `gaussValueF_sub_prefix`, `tailValueF_add_le`
- **Visibility**: public
- **Lines**: 1117–1166 (proof ≈ 44 lines)
- **Notes**: proof > 30 lines; uses `Exists.choose`/`choose_spec` on `exists_eq_sum_teichCoeffF_add` inside a `have`.

### `theorem gaussValueF_teichmuller`
- **Type**: `(ρ : NNReal) (c : F) : gaussValueF p F ρ ([c] : WittVector p F) = perfectoidValuation p F c`
- **What**: The Gauss value of a single Teichmüller lift is exactly `|c|`, for every radius.
- **How**: `le_antisymm`. `≤` by `ciSup_le` with the same digit case-split as `bddAbove_gaussTermF_teichmuller` (`WittVector.teichmuller_coeff_zero` / `teichmuller_coeff_pos`); `≥` by `le_ciSup` at index `0` with the explicit `BddAbove` witness `|c|` re-proved inline.
- **Hypotheses**: none.
- **Uses from project**: `gaussTermF`, `gaussValueF`, `teichCoeffF`, `perfectoidValuation`
- **Used by**: `gaussTermF_mul_le`
- **Visibility**: public
- **Lines**: 1167–1187 (proof ≈ 18 lines)
- **Notes**: the boundedness witness duplicates `bddAbove_gaussTermF_teichmuller` (dedup candidate).

### `theorem teichCoeffF_eq_of_sub_eq_pow_mul`
- **Type**: `{a b : WittVector p F} {N j : ℕ} (hj : j < N) {K : WittVector p F} (h : a − b = (p : WittVector p F) ^ N * K) : teichCoeffF p F a j = teichCoeffF p F b j`
- **What**: Congruence mod `p^N` forces agreement of all Teichmüller digits below `N`.
- **How**: Reduce to Witt coefficients (`congr 1` after unfolding `teichCoeffF`), then `WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero` plus `WittVector.mul_pow_charP_coeff_zero` show `(a−b).coeff i = 0` for `i < N`.
- **Hypotheses**: `j < N`, congruence `a − b = p^N·K`.
- **Uses from project**: `teichCoeffF`
- **Used by**: `gaussTermF_mul_le`, `tailValueF_add_le`
- **Visibility**: public
- **Lines**: 1188–1203 (proof ≈ 11 lines)
- **Notes**: none.

### `theorem gaussTermF_mul_le`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x y : WittVector p F} (hBx hBy : BddAbove …) (n : ℕ) : gaussTermF p F ρ (x * y) n ≤ gaussValueF p F ρ x * gaussValueF p F ρ y`
- **What**: Term-by-term submultiplicativity over `W(F)`: `ρ^n·|(xy)_n| ≤ w_ρ(x)·w_ρ(y)`.
- **How**: Truncation. `exists_iter_splitF` at level `n+1` writes `x = Px + p^{n+1}X`, `y = Py + p^{n+1}Y`; expanding `x·y − Px·Py` shows it is `p^{n+1}` times an explicit element, so `teichCoeffF_eq_of_sub_eq_pow_mul` gives `(xy)_n = (Px·Py)_n`. The prefix product is expanded as a `Finset.range(n+1) ×ˢ range(n+1)` sum (`Finset.sum_mul_sum`, `Finset.sum_product'`) of pieces `[x_i·y_j]·p^{i+j}`, each of whose value is *exactly* `ρ^{i+j}|x_i||y_j|` (`gaussValueF_p_pow_mul` ∘ `gaussValueF_teichmuller`), which factors as `(ρ^i|x_i|)(ρ^j|y_j|) ≤ w_ρ(x)·w_ρ(y)`. `gaussValueF_finset_sum_le` assembles the pieces.
- **Hypotheses**: `0 < ρ < 1`; both factors boundedly termed.
- **Uses from project**: `exists_iter_splitF`, `teichCoeffF_eq_of_sub_eq_pow_mul`, `gaussValueF_finset_sum_le`, `bddAbove_gaussTermF_p_pow_mul`, `bddAbove_gaussTermF_teichmuller`, `gaussValueF_p_pow_mul`, `gaussValueF_teichmuller`, `gaussTermF_le_gaussValueF`, `gaussTermF`, `gaussValueF`, `teichCoeffF`, `perfectoidValuation`
- **Used by**: `gaussValueF_mul_le`
- **Visibility**: public
- **Lines**: 1204–1276 (proof ≈ 68 lines)
- **Notes**: proof > 30 lines. Decomposition candidate.

### `theorem gaussValueF_mul_le`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x y : WittVector p F} (hBx hBy : BddAbove …) : BddAbove (Set.range (gaussTermF p F ρ (x * y))) ∧ gaussValueF p F ρ (x * y) ≤ gaussValueF p F ρ x * gaussValueF p F ρ y`
- **What**: Submultiplicativity over `W(F)`, bundled with boundedness of the product's terms.
- **How**: Both halves are immediate from `gaussTermF_mul_le`: the bound `w_ρ(x)·w_ρ(y)` is a uniform term bound, and `ciSup_le` turns the termwise estimate into the value estimate.
- **Hypotheses**: `0 < ρ < 1`; both factors boundedly termed.
- **Uses from project**: `gaussTermF_mul_le`, `gaussTermF`, `gaussValueF`
- **Used by**: `bddAbove_gaussTermF_neg`, `twoBddSubring`
- **Visibility**: public
- **Lines**: 1277–1289 (proof ≈ 6 lines)
- **Notes**: none.

### `theorem bddAbove_gaussTermF_neg_one`
- **Type**: `{ρ : NNReal} (hρ1 : ρ < 1) : BddAbove (Set.range (gaussTermF p F ρ (−1 : WittVector p F)))`
- **What**: `−1` has bounded Gauss terms (bound `1`).
- **How**: `−1 : W(F)` is the image of `−1 : A_inf` under `WittVector.map` (`map_neg`, `map_one`), so `gaussTermF_map` transports the global `A_inf` bound `gaussTerm_le_one`.
- **Hypotheses**: `ρ < 1` (for `gaussTerm_le_one`).
- **Uses from project**: `gaussTermF_map`, `gaussTermF`, `gaussTerm_le_one`, `powerBoundedSubring.toSubring`, `Ainf`
- **Used by**: `bddAbove_gaussTermF_neg`
- **Visibility**: public
- **Lines**: 1290–1300 (proof ≈ 6 lines)
- **Notes**: none.

### `theorem bddAbove_gaussTermF_neg`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x : WittVector p F} (hB : BddAbove …) : BddAbove (Set.range (gaussTermF p F ρ (−x)))`
- **What**: Negation preserves term-boundedness.
- **How**: Write `−x = (−1)·x` and apply the boundedness half of `gaussValueF_mul_le` with `bddAbove_gaussTermF_neg_one`.
- **Hypotheses**: `0 < ρ < 1`; boundedness of `x`.
- **Uses from project**: `bddAbove_gaussTermF_neg_one`, `gaussValueF_mul_le`, `gaussTermF`
- **Used by**: `tendsto_gaussTermF_of_w_approx`, `twoBddSubring`
- **Visibility**: public
- **Lines**: 1301–1311 (proof ≈ 3 lines)
- **Notes**: none.

### `def twoBddSubring`
- **Type**: `{ρ ρ₂ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) : Subring (WittVector p F)`
- **What**: The two-radius bounded carrier — the integral model of the interval ring `B^I` (Kedlaya Def 4.2): Witt vectors over `F` whose Gauss terms are bounded at *both* radii `ρ` and `ρ₂`.
- **How**: Assembles a `Subring` structure whose carrier is the conjunction of two `BddAbove` conditions. `zero_mem'` because all digits of `0` vanish; `one_mem'` because `1` comes from `A_inf` (`gaussTermF_map` + `gaussTerm_le_one`); `add_mem'` from `bddAbove_gaussTermF_add`; `mul_mem'` from `(gaussValueF_mul_le …).1`; `neg_mem'` from `bddAbove_gaussTermF_neg` — each applied at both radii.
- **Hypotheses**: `0 < ρ, ρ₂ < 1`.
- **Uses from project**: `bddAbove_gaussTermF_add`, `bddAbove_gaussTermF_neg`, `gaussValueF_mul_le`, `gaussTermF_map`, `gaussTermF`, `teichCoeffF`, `gaussTerm_le_one`, `powerBoundedSubring.toSubring`, `Ainf`
- **Used by**: unused in file (and not referenced elsewhere in the project yet)
- **Visibility**: public
- **Lines**: 1312–1345 (structure definition, 34 lines)
- **Notes**: > 30 lines; the intended API entry point for the Euclidean/Gröbner development.

---

## Part 6 — Decay, degree, and the moving-prefix tail estimate

### `theorem tendsto_gaussTermF_of_bddAbove_gt`
- **Type**: `{ρ σ : NNReal} (hσ0 : 0 < σ) (hσρ : σ < ρ) {x : WittVector p F} (hB : BddAbove (Set.range (gaussTermF p F ρ x))) : Filter.Tendsto (gaussTermF p F σ x) Filter.atTop (nhds 0)`
- **What**: The ρ′-principle — boundedness at a larger radius forces the terms to decay at any strictly smaller radius.
- **How**: Geometric domination. `gaussTermF σ x n = (σ/ρ)^n · gaussTermF ρ x n ≤ (σ/ρ)^n · M`, and `tendsto_pow_atTop_nhds_zero_of_lt_one` (with `div_lt_one`) makes the majorant tend to `0`; conclude by squeeze (`tendsto_of_tendsto_of_tendsto_of_le_of_le`).
- **Hypotheses**: `0 < σ < ρ`, boundedness at radius `ρ`.
- **Uses from project**: `gaussTermF`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1346–1368 (proof ≈ 20 lines)
- **Notes**: none.

### `theorem exists_gaussValueF_eq_gaussTermF`
- **Type**: `{σ : NNReal} (hσ0 : 0 < σ) {x : WittVector p F} (hdecay : Filter.Tendsto (gaussTermF p F σ x) Filter.atTop (nhds 0)) (hx : x ≠ 0) : ∃ n, gaussValueF p F σ x = gaussTermF p F σ x n ∧ ∀ m, gaussTermF p F σ x m ≤ gaussTermF p F σ x n`
- **What**: Max attainment: for a decaying nonzero element the sup defining `w_σ` is attained at some index.
- **How**: Nonzero gives some `x.coeff m₀ ≠ 0` (`WittVector.ext`), hence `gaussTermF σ x m₀ > 0` (the inverse Frobenius is injective, so its image is nonzero — `map_eq_zero_iff` + `RingEquiv.injective`). Decay makes terms eventually `< gaussTermF σ x m₀`, so only the finite window `Finset.range (N+1)` matters; `Finset.exists_max_image` picks the maximiser `n₀`, and `le_antisymm (ciSup_le hmax) (le_ciSup …)` identifies the sup.
- **Hypotheses**: `0 < σ`, decay of the terms, `x ≠ 0`.
- **Uses from project**: `gaussTermF`, `gaussValueF`, `teichCoeffF`
- **Used by**: `degF_spec`
- **Visibility**: public
- **Lines**: 1369–1410 (proof ≈ 36 lines)
- **Notes**: proof > 30 lines.

### `def degF`
- **Type**: `(σ : NNReal) (x : WittVector p F) : ℕ := sSup {n | gaussTermF p F σ x n = gaussValueF p F σ x}`
- **What**: The degree of a Witt vector at radius `σ`: the largest index realising the Gauss value (Kedlaya Def 2.5). Junk value `0` off the decaying-nonzero locus.
- **How**: `sSup` on `ℕ` of the attaining set; `Nat.sSup_mem` gives membership once nonemptiness and bounded-aboveness are known (supplied in `degF_spec`).
- **Hypotheses**: none in the definition (junk-valued in general).
- **Uses from project**: `gaussTermF`, `gaussValueF`
- **Used by**: `degF_spec`
- **Visibility**: public
- **Lines**: 1411–1415 (definition, `noncomputable def`)
- **Notes**: decision AD-6 — no Newton polygons.

### `theorem degF_spec`
- **Type**: `{σ : NNReal} (hσ0 : 0 < σ) {x : WittVector p F} (hdecay : …) (hx : x ≠ 0) : gaussTermF p F σ x (degF p F σ x) = gaussValueF p F σ x ∧ ∀ m, degF p F σ x < m → gaussTermF p F σ x m < gaussValueF p F σ x`
- **What**: The defining property of the degree on the decaying-nonzero locus: the value is attained at `degF` and strictly dropped beyond it.
- **How**: `exists_gaussValueF_eq_gaussTermF` gives an attaining index, so the attaining set `A` is nonempty and (by positivity of `w_σ(x)` and decay) bounded above; `Nat.sSup_mem` puts `degF` in `A`. For `m > degF`, `hmax m` gives `≤`, and equality would put `m ∈ A`, contradicting `le_csSup`.
- **Hypotheses**: `0 < σ`, decay, `x ≠ 0`.
- **Uses from project**: `degF`, `exists_gaussValueF_eq_gaussTermF`, `gaussTermF`, `gaussValueF`, `teichCoeffF`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1416–1457 (proof ≈ 37 lines)
- **Notes**: proof > 30 lines; the positivity sub-argument duplicates part of `exists_gaussValueF_eq_gaussTermF` (dedup candidate).

### `def tailValueF`
- **Type**: `(σ : NNReal) (x : WittVector p F) (N : ℕ) : NNReal := ⨆ k, gaussTermF p F σ x (N + k)`
- **What**: The tail value `T_N(x) = sup_{n ≥ N} σ^n|x_n|`.
- **How**: Direct `iSup` over shifted indices.
- **Hypotheses**: none (junk when unbounded).
- **Uses from project**: `gaussTermF`
- **Used by**: `gaussTermF_le_tailValueF`, `gaussValueF_sub_prefix`, `tailValueF_add_le`, `tailValueF_add_le_gaussValueF`, `tailValueF_eq_of_coords`, `tailValueF_le_gaussValueF`, `tendsto_gaussTermF_add_of_tendsto`, `tendsto_gaussTermF_of_w_approx`, `tendsto_tailValueF_of_tendsto`
- **Visibility**: public
- **Lines**: 1458–1461 (definition)
- **Notes**: introduced by the 2026-07-26 decay-closure consult.

### `def headBoundF`
- **Type**: `(σ : NNReal) (x : WittVector p F) (N : ℕ) : NNReal := σ ^ N * (Finset.range N).sup (fun i => perfectoidValuation p F (teichCoeffF p F x i))`
- **What**: The head bound `H_N(x) = σ^N · max_{i<N} |x_i|` — the price of moving the prefix boundary.
- **How**: Direct definition using `Finset.sup` over the first `N` digit valuations.
- **Hypotheses**: none.
- **Uses from project**: `teichCoeffF`, `perfectoidValuation`
- **Used by**: `tailValueF_add_le_gaussValueF`, `tendsto_gaussTermF_add_of_tendsto`, `tendsto_gaussTermF_of_w_approx`, `tendsto_headBoundF_of_tendsto`
- **Visibility**: public
- **Lines**: 1462–1467 (definition)
- **Notes**: none.

### `theorem valuation_teichCoeffF_prefix_add_le`
- **Type**: `(x y : WittVector p F) (N : ℕ) (j : ℕ) : |teichCoeffF p F (Px + Py) j| ≤ (Finset.range N).sup (fun i => max |x_i| |y_i|)` where `Px`, `Py` are the length-`N` Teichmüller prefixes of `x` and `y`
- **What**: The prefix-pair digit bound: *all* digits (not just the first `N`) of a sum of two length-`N` prefixes are bounded by the largest input coordinate.
- **How**: Factor out a max-attaining coefficient. Degenerate case `M = 0`: all input digits vanish (`Valuation.zero_iff`), both prefixes are `0`, done. Otherwise `Finset.exists_mem_eq_sup` picks `i₀` attaining `M` and `c` is whichever of `x_{i₀}`, `y_{i₀}` realises it; every `x_i/c` and `y_i/c` then has valuation `≤ 1`, so `perfectoidValuation_integers.exists_of_le_one` + `choose` lifts them all to `O_F`, and the sum factors as `[c] · map(S)` with `S : A_inf`. Then `teichCoeffF_teichmuller_mul`, `Valuation.map_mul`, `teichCoeffF_map` and `perfectoidValuation_le_one` give `|digit| ≤ |c| = M`.
- **Hypotheses**: none beyond the ambient setting — this is the key *unconditional* estimate.
- **Uses from project**: `teichCoeffF`, `teichCoeffF_map`, `teichCoeffF_teichmuller_mul`, `perfectoidValuation`, `perfectoidValuation_integers`, `perfectoidValuation_le_one`, `powerBoundedSubring.toSubring`, `OF`, `Ainf`
- **Used by**: `tailValueF_add_le`
- **Visibility**: public
- **Lines**: 1468–1603 (proof ≈ 126 lines)
- **Notes**: **longest proof in the file**; proof > 30 lines. The `hchx`/`hchy` blocks are verbatim duplicates modulo `x`/`y` (dedup / decompose candidate).

### `theorem coe_p_ne_zero_wittF`
- **Type**: `(p : WittVector p F) ≠ 0`
- **What**: The image of `p` in `W(F)` is nonzero (so `p^N` is a non-zero-divisor for the cancellation used in `tailValueF_add_le`).
- **How**: `WittVector.teichmuller_mul_pow_coeff (p := p) (R := F) 1 1` computes `((p : W F)).coeff 1 = 1`; if `p = 0` that coefficient would be `0`, contradiction.
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: `tailValueF_add_le`
- **Visibility**: public
- **Lines**: 1605–1613 (proof ≈ 6 lines)
- **Notes**: none.

### `theorem tailValueF_eq_of_coords`
- **Type**: `{σ : NNReal} {x X : WittVector p F} {N : ℕ} (hc : ∀ k, teichCoeffF p F X k = teichCoeffF p F x (N + k)) : tailValueF p F σ x N = σ ^ N * gaussValueF p F σ X`
- **What**: Bridge identity: the tail value of `x` at level `N` is the `σ^N`-scaled Gauss value of the iter-split witness `X`.
- **How**: `NNReal.mul_iSup` moves `σ^N` inside; `iSup_congr` then matches terms via `hc k` and `pow_add`.
- **Hypotheses**: the coordinate-shift relation between `X` and `x`.
- **Uses from project**: `tailValueF`, `gaussValueF`, `gaussTermF`, `teichCoeffF`
- **Used by**: `gaussValueF_sub_prefix`, `tailValueF_add_le`
- **Visibility**: public
- **Lines**: 1614–1623 (proof ≈ 4 lines)
- **Notes**: none.

### `theorem tailValueF_add_le`
- **Type**: `{σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ < 1) {x y : WittVector p F} (hBx hBy : BddAbove …) (N : ℕ) : tailValueF p F σ (x + y) N ≤ max (max (tailValueF p F σ x N) (tailValueF p F σ y N)) (σ^N * (Finset.range N).sup (fun i => max |x_i| |y_i|))`
- **What**: The moving-prefix tail estimate: the tail of a sum is controlled by the two tails plus the scaled head bound.
- **How**: Iter-split `x`, `y`, `A := Px + Py`, and `x+y` at level `N` (four uses of `exists_iter_splitF`), giving witnesses `X, Y, C, Z`. `valuation_teichCoeffF_prefix_add_le` bounds every digit of `A` — hence of `C` — by `M`, so `w_σ(C) ≤ M` and `C`'s terms are bounded. `teichCoeffF_eq_of_sub_eq_pow_mul` shows `x+y` and `A` share digits below `N`, so their prefixes agree; cancelling `p^N` (`mul_left_cancel₀` with `coe_p_ne_zero_wittF`) yields the exact identity `Z = C + X + Y`. Two applications of `gaussValueF_add_le` then bound `w_σ(Z)` by `max(w_σ C, max(w_σ X, w_σ Y))`, and `tailValueF_eq_of_coords` + `nnreal_mul_max` translate everything back into tail values.
- **Hypotheses**: `0 < σ < 1`; both summands boundedly termed.
- **Uses from project**: `exists_iter_splitF`, `valuation_teichCoeffF_prefix_add_le`, `teichCoeffF_eq_of_sub_eq_pow_mul`, `coe_p_ne_zero_wittF`, `tailValueF_eq_of_coords`, `gaussValueF_add_le`, `bddAbove_gaussTermF_add`, `tailValueF`, `gaussTermF`, `gaussValueF`, `teichCoeffF`, `perfectoidValuation`, `nnreal_mul_max`
- **Used by**: `tailValueF_add_le_gaussValueF`, `tendsto_gaussTermF_add_of_tendsto`
- **Visibility**: public
- **Lines**: 1624–1752 (proof ≈ 120 lines)
- **Notes**: proof > 30 lines; the `hBX`/`hBY` blocks are duplicates of each other and of `bddAbove_gaussTermF_of_coords_shift` (dedup candidate). Second-longest proof in the file.

### `theorem tendsto_tailValueF_of_tendsto`
- **Type**: `{σ : NNReal} {x : WittVector p F} (hdecay : Filter.Tendsto (gaussTermF p F σ x) Filter.atTop (nhds 0)) : Filter.Tendsto (fun N => tailValueF p F σ x N) Filter.atTop (nhds 0)`
- **What**: Decay of the terms is equivalent to (here: implies) decay of the tail sups.
- **How**: `tendsto_order`; the lower half is vacuous in `NNReal`. For the upper half pick `b` between `0` and the target `a` (`exists_between`), take `K` with `gaussTermF σ x n < b` for `n ≥ K` (`Filter.eventually_atTop` on `hdecay.eventually_lt_const`), then `ciSup_le` bounds `tailValueF … N ≤ b < a` for all `N ≥ K`.
- **Hypotheses**: decay of the terms.
- **Uses from project**: `gaussTermF`, `tailValueF`
- **Used by**: `tendsto_gaussTermF_add_of_tendsto`, `tendsto_gaussTermF_of_w_approx`
- **Visibility**: public
- **Lines**: 1753–1768 (proof ≈ 12 lines)
- **Notes**: none.

### `theorem bddAbove_of_tendsto_gaussTermF`
- **Type**: `{σ : NNReal} {x : WittVector p F} (hdecay : …) : BddAbove (Set.range (gaussTermF p F σ x))`
- **What**: Decaying elements are automatically boundedly termed.
- **How**: Terms are eventually `< 1` (`hdecay.eventually_lt_const one_pos`); split at the threshold `K` and bound by `max 1 ((Finset.range (K+1)).sup (gaussTermF …))` using `Finset.le_sup` below and the eventual bound above.
- **Hypotheses**: decay.
- **Uses from project**: `gaussTermF`
- **Used by**: `tendsto_gaussTermF_add_of_tendsto`, `tendsto_gaussTermF_of_w_approx`
- **Visibility**: public
- **Lines**: 1769–1782 (proof ≈ 10 lines)
- **Notes**: structurally identical to the `hBf` block inside `exists_iSup_eq_of_tendsto_zero` (dedup candidate).

### `theorem tendsto_headBoundF_of_tendsto`
- **Type**: `{σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ < 1) {x : WittVector p F} (hdecay : …) : Filter.Tendsto (fun N => headBoundF p F σ x N) Filter.atTop (nhds 0)`
- **What**: Head-bound decay: for decaying `x`, `H_N(x) = σ^N·max_{i<N}|x_i| → 0`.
- **How**: The split-max argument. Fix `b` below the target. Choose `K` past which terms are `< b`. The "old" head `σ^N·max_{i<K}|x_i|` tends to `0` geometrically (`tendsto_pow_atTop_nhds_zero_of_lt_one … .mul_const`), giving a threshold `N₂`. For `N ≥ N₂`, `Finset.exists_mem_eq_sup` picks the maximising index `i₀ < N`; if `i₀ < K` the geometric estimate applies, otherwise `σ^N·|x_{i₀}| ≤ σ^{i₀}·|x_{i₀}| = gaussTermF σ x i₀ < b` (using `pow_le_pow_of_le_one` since `i₀ ≤ N` and `σ ≤ 1`).
- **Hypotheses**: `0 < σ < 1`, decay.
- **Uses from project**: `headBoundF`, `gaussTermF`, `teichCoeffF`, `perfectoidValuation`
- **Used by**: `tendsto_gaussTermF_add_of_tendsto`, `tendsto_gaussTermF_of_w_approx`
- **Visibility**: public
- **Lines**: 1783–1828 (proof ≈ 42 lines)
- **Notes**: proof > 30 lines.

### `theorem tendsto_gaussTermF_add_of_tendsto`
- **Type**: `{σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ < 1) {x y : WittVector p F} (hdx hdy : Filter.Tendsto (gaussTermF p F σ ·) Filter.atTop (nhds 0)) : Filter.Tendsto (gaussTermF p F σ (x + y)) Filter.atTop (nhds 0)`
- **What**: Decay is closed under addition — the crux of the decay-closure consult.
- **How**: Assemble the crux inequality `gaussTermF σ (x+y) n ≤ max (max T_n(x) T_n(y)) (max H_n(x) H_n(y))`: the left side is `≤ tailValueF σ (x+y) n` (index `0` of the shifted sup, boundedness from `bddAbove_gaussTermF_add`), then `tailValueF_add_le` bounds that, and a `Finset.sup`-of-max splitting lemma (`Finset.sup_le`/`Finset.sup_mono_fun` + `nnreal_mul_max`) turns the mixed head term into `max (headBoundF x n) (headBoundF y n)`. Both `tendsto_tailValueF_of_tendsto` and `tendsto_headBoundF_of_tendsto` send the majorant to `0` (`Tendsto.max`), and squeezing finishes.
- **Hypotheses**: `0 < σ < 1`; both summands decaying (boundedness derived via `bddAbove_of_tendsto_gaussTermF`).
- **Uses from project**: `tailValueF_add_le`, `tendsto_tailValueF_of_tendsto`, `tendsto_headBoundF_of_tendsto`, `bddAbove_of_tendsto_gaussTermF`, `bddAbove_gaussTermF_add`, `tailValueF`, `headBoundF`, `gaussTermF`, `teichCoeffF`, `perfectoidValuation`, `nnreal_mul_max`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1829–1885 (proof ≈ 52 lines)
- **Notes**: proof > 30 lines. Headline result of the decay section.

### `theorem gaussTermF_le_tailValueF`
- **Type**: `{σ : NNReal} {x : WittVector p F} (hB : BddAbove …) (n : ℕ) : gaussTermF p F σ x n ≤ tailValueF p F σ x n`
- **What**: A term is at most the tail value at its own index.
- **How**: The `k = 0` element of the shifted family: rewrite `n` as `n + 0` and apply `le_ciSup` to the restricted family, whose boundedness is inherited from `hB`.
- **Hypotheses**: term-boundedness of `x`.
- **Uses from project**: `gaussTermF`, `tailValueF`
- **Used by**: `tendsto_gaussTermF_of_w_approx`
- **Visibility**: public
- **Lines**: 1886–1897 (proof ≈ 7 lines)
- **Notes**: none.

### `theorem tailValueF_le_gaussValueF`
- **Type**: `{σ : NNReal} {x : WittVector p F} (hB : BddAbove …) (N : ℕ) : tailValueF p F σ x N ≤ gaussValueF p F σ x`
- **What**: The tail value never exceeds the full Gauss value.
- **How**: `ciSup_le fun k => le_ciSup hB (N + k)` — the shifted family is a subfamily.
- **Hypotheses**: term-boundedness.
- **Uses from project**: `tailValueF`, `gaussValueF`, `gaussTermF`
- **Used by**: `tailValueF_add_le_gaussValueF`
- **Visibility**: public
- **Lines**: 1898–1904 (term-mode, 1 line)
- **Notes**: none.

### `theorem tailValueF_add_le_gaussValueF`
- **Type**: `{σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ < 1) {u e : WittVector p F} (hBu hBe : BddAbove …) (N : ℕ) : tailValueF p F σ (u + e) N ≤ max (max (tailValueF p F σ u N) (headBoundF p F σ u N)) (gaussValueF p F σ e)`
- **What**: The perturbation estimate: the tail of `u + e` is controlled by the tail and head of `u` together with the *full* Gauss value of the perturbation `e`.
- **How**: Start from `tailValueF_add_le`, then absorb the two `e`-contributions: `tailValueF_le_gaussValueF` handles `T_N(e)`, and for the mixed head term `Finset.exists_mem_eq_sup` picks the maximiser `i₀ < N` and `nnreal_mul_max` splits it — the `u`-side goes into `headBoundF u N` (`Finset.le_sup`) and the `e`-side into `gaussValueF σ e` via `σ^N|e_{i₀}| ≤ σ^{i₀}|e_{i₀}| = gaussTermF σ e i₀ ≤ le_ciSup hBe i₀` (`pow_le_pow_of_le_one`).
- **Hypotheses**: `0 < σ < 1`; both `u` and `e` boundedly termed.
- **Uses from project**: `tailValueF_add_le`, `tailValueF_le_gaussValueF`, `headBoundF`, `tailValueF`, `gaussTermF`, `gaussValueF`, `teichCoeffF`, `perfectoidValuation`, `nnreal_mul_max`
- **Used by**: `tendsto_gaussTermF_of_w_approx`
- **Visibility**: public
- **Lines**: 1905–1947 (proof ≈ 35 lines)
- **Notes**: proof > 30 lines.

### `theorem tendsto_gaussTermF_of_w_approx`
- **Type**: `{σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ < 1) {u : WittVector p F} {S : ℕ → WittVector p F} (hBu : BddAbove …) (hdec : ∀ j, Tendsto (gaussTermF p F σ (S j)) atTop (nhds 0)) (happrox : Tendsto (fun j => gaussValueF p F σ (u − S j)) atTop (nhds 0)) : Tendsto (gaussTermF p F σ u) atTop (nhds 0)`
- **What**: `w`-closedness of decay: a `w_σ`-limit of decaying elements is decaying. This is what makes the decaying locus a *closed* subring, i.e. complete.
- **How**: `tendsto_order`; fix `b` below the target `a` and pick one approximant index `j₀` with `w_σ(u − S_{j₀}) < b`. Write `u = S_{j₀} + (u − S_{j₀})` and apply `tailValueF_add_le_gaussValueF` — the three resulting quantities are `T_n(S_{j₀})`, `H_n(S_{j₀})` and `w_σ(u − S_{j₀})`, all eventually `< b` by `tendsto_tailValueF_of_tendsto`, `tendsto_headBoundF_of_tendsto` and the choice of `j₀`. `gaussTermF_le_tailValueF` connects the term to the tail; boundedness of the difference comes from `bddAbove_gaussTermF_add` + `bddAbove_gaussTermF_neg`.
- **Hypotheses**: `0 < σ < 1`; `u` boundedly termed; every approximant decaying; `w_σ`-convergence `S_j → u`.
- **Uses from project**: `tailValueF_add_le_gaussValueF`, `gaussTermF_le_tailValueF`, `tendsto_tailValueF_of_tendsto`, `tendsto_headBoundF_of_tendsto`, `bddAbove_of_tendsto_gaussTermF`, `bddAbove_gaussTermF_add`, `bddAbove_gaussTermF_neg`, `tailValueF`, `headBoundF`, `gaussTermF`, `gaussValueF`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1948–1990 (proof ≈ 37 lines)
- **Notes**: proof > 30 lines. The completion-closure statement the whole Part 6 was built for.

### `theorem bddAbove_gaussTermF_of_coords_shift`
- **Type**: `{σ : NNReal} (hσ0 : 0 < σ) {x X : WittVector p F} {N : ℕ} (hc : ∀ k, teichCoeffF p F X k = teichCoeffF p F x (N + k)) (hB : BddAbove …) : BddAbove (Set.range (gaussTermF p F σ X))`
- **What**: An `N`-fold coordinate shift preserves term-boundedness (bound `(σ^N)⁻¹·M`).
- **How**: The shift identity `σ^N · gaussTermF σ X k = gaussTermF σ x (N+k)` (unfold, `hc k`, `pow_add`) plus `inv_mul_cancel₀ (pow_pos hσ0 N).ne'` to divide out.
- **Hypotheses**: `0 < σ`; the coordinate-shift relation; boundedness of `x`.
- **Uses from project**: `gaussTermF`, `teichCoeffF`
- **Used by**: `gaussValueF_sub_prefix`
- **Visibility**: public
- **Lines**: 1991–2008 (proof ≈ 13 lines)
- **Notes**: an `N`-step generalisation of `bddAbove_gaussTermF_of_tail`, and duplicates the `hBX`/`hBY` blocks inside `tailValueF_add_le` (dedup candidate).

### `theorem gaussValueF_sub_prefix`
- **Type**: `{σ : NNReal} (hσ0 : 0 < σ) {x : WittVector p F} (hB : BddAbove …) (N : ℕ) : gaussValueF p F σ (x − ∑ i ∈ Finset.range N, [teichCoeffF p F x i] * p ^ i) = tailValueF p F σ x N`
- **What**: The tail-of-prefix identity: the Gauss value of `x` minus its `N`-th Teichmüller prefix is *exactly* the tail value `T_N(x)`.
- **How**: `exists_iter_splitF` writes the difference as `p^N·X` (`sub_eq_iff_eq_add'`), `gaussValueF_p_pow_mul` (with boundedness from `bddAbove_gaussTermF_of_coords_shift`) turns its value into `σ^N·w_σ(X)`, and `tailValueF_eq_of_coords` identifies that with `T_N(x)`.
- **Hypotheses**: `0 < σ`; boundedness of `x`.
- **Uses from project**: `exists_iter_splitF`, `gaussValueF_p_pow_mul`, `bddAbove_gaussTermF_of_coords_shift`, `tailValueF_eq_of_coords`, `tailValueF`, `gaussTermF`, `gaussValueF`, `teichCoeffF`
- **Used by**: unused in file; **used downstream** in `FarguesFontaine/ArCompletion.lean`.
- **Visibility**: public
- **Lines**: 2009–2022 (proof ≈ 6 lines)
- **Notes**: none.

### `theorem exists_iSup_eq_of_tendsto_zero`
- **Type**: `{f : ℕ → NNReal} (hf : Filter.Tendsto f Filter.atTop (nhds 0)) (hne : (⨆ n, f n) ≠ 0) : ∃ n₀, (⨆ n, f n) = f n₀ ∧ ∀ m, f m ≤ f n₀`
- **What**: A general `NNReal` fact (no Witt vectors): a sequence tending to `0` with nonzero sup attains that sup.
- **How**: First `f` is bounded (eventually `< 1`, plus a finite `Finset.sup` below the threshold). Pick `b` strictly between `0` and the sup (`exists_between`) and `K` past which `f < b`; then all values are `≤ max ((Finset.range (K+1)).sup f) b`, and `max_cases` rules out the `b` branch (it would contradict `b < ⨆ f`), so the sup is `≤` the finite sup, which `Finset.exists_mem_eq_sup` realises at some `n₀`. `le_antisymm` with `le_ciSup` closes it.
- **Hypotheses**: `f → 0`, `⨆ f ≠ 0`.
- **Uses from project**: `[]` (pure mathlib)
- **Used by**: unused in file; **used downstream** in `FarguesFontaine/ArCompletion.lean`.
- **Visibility**: public
- **Lines**: 2023–2058 (proof ≈ 33 lines)
- **Notes**: proof > 30 lines. Fully general — a **mathlib-able** candidate (`NNReal`/`ciSup` lemma with no project content); its `hBf` block duplicates `bddAbove_of_tendsto_gaussTermF`.

---

### File Summary

- **Total declarations: 75** (7 defs — `teichCoeffF`, `gaussTermF`, `gaussValueF`, `twoBddSubring`, `degF`, `tailValueF`, `headBoundF`; 67 lemmas/theorems; 1 instance — `instPerfectRingF`)
- **Key API (used by 3+ others)**:
  - `teichCoeffF` (35 users), `gaussTermF` (46), `gaussValueF` (27) — the three core definitions
  - `tailValueF` (9), `headBoundF` (4)
  - `teichCoeffF_sum_range_add` (5), `gaussTermF_le_gaussValueF` (5), `exists_eq_sum_teichCoeffF_add` (3)
  - `bddAbove_gaussTermF_add` (6), `gaussValueF_add_le` (3), `exists_head_splitF` (3), `bddAbove_gaussTermF_of_tail` (3), `mul_gaussValueF_le_of_tail` (3)
  - `teichCoeffF_map` (3), `teichCoeffF_teichmuller_mul` (3), `gaussTermF_map` (4), `exists_iter_splitF` (3), `valuation_teichCoeffF_teichmuller_add_le` (3)
- **Unused declarations** (no in-file consumer):
  - Used downstream in `FarguesFontaine/ArCompletion.lean`: `exists_delta_teichCoeffF_sub`, `gaussValueF_sub_prefix`, `exists_iSup_eq_of_tendsto_zero`
  - Not referenced anywhere in the project: `exists_delta_teichCoeff_sub`, `twoBddSubring`, `tendsto_gaussTermF_of_bddAbove_gt`, `degF_spec` (and its `degF` is only used by it), `tendsto_gaussTermF_add_of_tendsto`, `tendsto_gaussTermF_of_w_approx`
  - `instPerfectRingF` has no *named* user but is consumed as a typeclass instance by every `frobeniusEquiv F p` in the file
- **Downstream consumers in the project** (37 of the 75 declarations are used outside this file):
  `FarguesFontaine/ArCompletion.lean` (the heaviest consumer — 30 declarations, including the whole
  tail/head-bound decay API), `FarguesFontaine/Euclidean.lean` (16), `FarguesFontaine/IntervalCoordinates.lean`
  (`teichCoeffF`, `teichCoeffF_map`, `teichCoeffF_teichmuller_mul`, `teichCoeffF_p_mul`,
  `teichCoeffF_p_mul_zero`), `FarguesFontaine/Presentation.lean` (`gaussTermF`, `gaussValueF`).
- **Declarations with `sorry`**: none
- **Declarations with `set_option`**: none (no `maxHeartbeats`/`maxRecDepth` bumps anywhere)
- **Proofs > 30 lines** (proof body, excluding statement):
  - `valuation_teichCoeffF_prefix_add_le` — ~126 (L1468–1603)
  - `tailValueF_add_le` — ~120 (L1624–1752)
  - `exists_delta_teichCoeffF_sub` — ~118 (L923–1052)
  - `gaussTermF_mul_le` — ~68 (L1204–1276)
  - `gaussValueF_teichmuller_sub_le_of_le_scaled` — ~60 (L718–787)
  - `bddAbove_gaussTermF_teichmuller_sub` — ~56 (L862–922)
  - `exists_delta_teichCoeff_sub` — ~55 (L159–218)
  - `tendsto_gaussTermF_add_of_tendsto` — ~52 (L1829–1885)
  - `exists_iter_splitF` — ~44 (L1117–1166)
  - `exists_level_repF` — ~43 (L620–676)
  - `tendsto_headBoundF_of_tendsto` — ~42 (L1783–1828)
  - `gaussValue_teichmuller_sub_le_of_le` — ~39 (L114–158)
  - `degF_spec` — ~37 (L1416–1457)
  - `tendsto_gaussTermF_of_w_approx` — ~37 (L1948–1990)
  - `valuation_teichCoeffF_teichmuller_add_le_left` — ~36 (L444–485)
  - `exists_gaussValueF_eq_gaussTermF` — ~36 (L1369–1410)
  - `tailValueF_add_le_gaussValueF` — ~35 (L1905–1947)
  - `exists_head_splitF` — ~34 (L404–443)
  - `exists_iSup_eq_of_tendsto_zero` — ~33 (L2023–2058)
  - `instPerfectRingF` — ~32 (L234–266)
  - `twoBddSubring` — 34-line structure definition (L1312–1345)
  - (borderline, ~30) `exists_fold_teichmuller_headsF` (L580–619)
- **Cross-cutting cleanup observations**:
  - The `ϖ^m`-scaling boilerplate (`hscale` / `exists_of_le_one` lifts / `hsplit` transport) appears verbatim in `gaussValueF_teichmuller_sub_le_of_le_scaled` and `bddAbove_gaussTermF_teichmuller_sub`.
  - The `BddAbove`-from-coordinate-shift argument appears three times: `bddAbove_gaussTermF_of_coords_shift`, and inline as `hBX`/`hBY` inside `tailValueF_add_le`.
  - The "eventually `< 1` ⇒ `BddAbove`" argument appears in `bddAbove_of_tendsto_gaussTermF` and inline in `exists_iSup_eq_of_tendsto_zero`.
  - The `hchx`/`hchy` lift blocks in `valuation_teichCoeffF_prefix_add_le` differ only by `x`↔`y`.
  - The digit-`0`-is-additive computation (`teichCoeffF … 0` of a difference) is re-derived inline four times in `exists_delta_teichCoeff_sub` and `exists_delta_teichCoeffF_sub`; it deserves a named lemma.
