# Inventory — `projects/AdicSpaces/Adic spaces/FarguesFontaine/Euclidean.lean`

File: `/Users/mcu22seu/Documents/GitHub/aintlib-adic-spaces/projects/AdicSpaces/Adic spaces/FarguesFontaine/Euclidean.lean`
2224 lines. Single import: `«Adic spaces».FarguesFontaine.ArCompletion`.
Namespace `FarguesFontaine`, inside `noncomputable section`, `open TopologicalRing ValuationSpectrum WittVector`.

Ambient section variables (all declarations are parameterised by these):
```
variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)          -- introduced at line 331
```
Every declaration from line 336 on additionally takes `ϖ`.

Naming shorthand used below: `Ar := ArSub p F ϖ hρ0 hρ1`, `λ_ρ := Valued.v` on `hatK p F hρ0 hρ1`,
`|·| := perfectoidValuation p F`, `xₙ := teichCoeffAr p F ϖ hρ0 hρ1 x n`.

---

### `theorem gaussValueF_map_le_of_coeff_zero`
- **Type**: `{ρ : NNReal} (hρ1 : ρ ≤ 1) {E : Ainf p F} (h0 : E.coeff 0 = 0) : gaussValueF p F ρ (WittVector.map ((powerBoundedSubring.toSubring F).subtype) E) ≤ ρ`
- **What**: The normalized master bound of Kedlaya's homogeneity estimate (2.8.1): an *integral* Witt vector (entries in `O_F`) whose zeroth Witt coordinate vanishes has Gauss value at most `ρ`.
- **How**: `exists_eq_sum_teichCoeff_add p F E 1` gives the 1-term Teichmüller expansion `E = [teichCoeff 0] + p·X`; `h0` kills the `0`-th Teichmüller coefficient (`teichCoeff` unfolds to a `p`-th power root of `E.coeff 0`), so `E = p·X` with `X` integral, and then `gaussValueF_p_mul` + `gaussValueF_map` reduce the bound to `ρ · gaussValue p F ρ X ≤ ρ · 1` via `gaussValue_le_one`.
- **Hypotheses**: `ρ ≤ 1` (so integral vectors have Gauss value ≤ 1); `E` integral (lives in `Ainf p F = WittVector p (O_F)`); vanishing zeroth coordinate.
- **Uses from project**: `Ainf`, `gaussValueF`, `gaussValue`, `gaussTermF`, `powerBoundedSubring`, `exists_eq_sum_teichCoeff_add`, `teichCoeff`, `gaussTermF_map`, `gaussTerm_le_one`, `gaussValueF_p_mul`, `gaussValueF_map`, `gaussValue_le_one`
- **Used by**: `gaussValueF_teichmuller_add_sub_le`, `gaussValueF_teichmuller_sub_sub_le`
- **Visibility**: public
- **Lines**: 52–72 (proof 55–72, 18 lines)
- **Notes**: headline result advertised in the module docstring. No `sorry`, no `set_option`.

### `theorem gaussValueF_zero`
- **Type**: `{ρ : NNReal} : gaussValueF p F ρ (0 : WittVector p F) = 0`
- **What**: The Gauss value of the zero Witt vector is `0`.
- **How**: Each `gaussTermF p F ρ 0 n` unfolds through `teichCoeffF` and `WittVector.zero_coeff` to `ρ^n * |0| = 0` (`Valuation.map_zero`), so the defining supremum is a supremum of zeros; `simp` closes `⨆ n, 0 = 0`.
- **Hypotheses**: none beyond the ambient perfectoid setup.
- **Uses from project**: `gaussValueF`, `gaussTermF`, `teichCoeffF`
- **Used by**: `gaussValueF_teichmuller_add_sub_le`, `gaussValueF_teichmuller_sub_sub_le`, `gaussValueF_teichmuller_sum_sub_le`
- **Visibility**: public
- **Lines**: 74–82 (proof 76–82, 7 lines)
- **Notes**: none

### `theorem exists_attaining_coeff`
- **Type**: `{a b : F} (hmax : max (perfectoidValuation p F a) (perfectoidValuation p F b) ≠ 0) : ∃ c : F, c ≠ 0 ∧ |c| = max |a| |b| ∧ |a| ≤ |c| ∧ |b| ≤ |c|`
- **What**: If the larger of `|a|`, `|b|` is nonzero, one of `a`, `b` is a nonzero element realizing that maximum — the scaling pivot of the homogeneity argument.
- **How**: `max_cases` on `|a|`, `|b|`; in each branch return the max-attaining element and derive `c ≠ 0` by contraposition — `c = 0` would force `max |a| |b| = |0| = 0` via `Valuation.map_zero`, contradicting `hmax`.
- **Hypotheses**: the max of the two valuations is nonzero (equivalently, not both `a` and `b` are `0`).
- **Uses from project**: `perfectoidValuation`
- **Used by**: `gaussValueF_teichmuller_add_sub_le`, `gaussValueF_teichmuller_sub_sub_le`
- **Visibility**: public
- **Lines**: 84–98 (proof 92–98, 6 lines)
- **Notes**: none

### `theorem gaussValueF_teichmuller_add_sub_le`
- **Type**: `{ρ : NNReal} (hρ1 : ρ ≤ 1) (a b : F) : gaussValueF p F ρ ([a] + [b] - [a+b]) ≤ ρ * max |a| |b|` (where `[·] = WittVector.teichmuller p`)
- **What**: Witt homogeneity (2.8.1), binary sum form: the failure of the Teichmüller lift to be additive is `ρ`-small relative to the entries.
- **How**: Scaling argument. Degenerate case `max = 0` forces `a = b = 0` (`Valuation.zero_iff`) and the expression is `0` (`gaussValueF_zero`). Otherwise pick the max-attaining `c` (`exists_attaining_coeff`), note `|a c⁻¹|, |b c⁻¹| ≤ 1` so they lift to `aInt, bInt : O_F` (`perfectoidValuation_integers.exists_of_le_one`); the integral discrepancy `E = [aInt] + [bInt] - [aInt+bInt]` has `constantCoeff E = 0` because `WittVector.teichmuller_coeff_zero` makes `constantCoeff` a ring hom on Teichmüller lifts, so `gaussValueF_map_le_of_coeff_zero` gives `gaussValueF (map E) ≤ ρ`; finally `[c] · map E` equals the original expression (`WittVector.map_teichmuller`, `field_simp` for `c·(a c⁻¹) = a`) and `gaussValueF_teichmuller_mul` converts multiplication by `[c]` into multiplication by `|c| = max |a| |b|`.
- **Hypotheses**: `ρ ≤ 1`; `F` perfectoid of characteristic `p` (needed for the `O_F`-integrality lift and the multiplicativity of `gaussValueF` against Teichmüller lifts).
- **Uses from project**: `gaussValueF`, `perfectoidValuation`, `perfectoidValuation_integers`, `Ainf`, `OF`, `powerBoundedSubring`, `gaussValueF_zero`, `exists_attaining_coeff`, `gaussValueF_map_le_of_coeff_zero`, `gaussValueF_teichmuller_mul`
- **Used by**: `gaussValueF_teichmuller_sum_sub_le`
- **Visibility**: public
- **Lines**: 100–182 (proof 106–182, 77 lines)
- **Notes**: proof >30 lines; near-duplicate of `gaussValueF_teichmuller_sub_sub_le` (only `+`/`-` differ) — a dedup candidate.

### `theorem gaussValueF_teichmuller_sub_sub_le`
- **Type**: `{ρ : NNReal} (hρ1 : ρ ≤ 1) (a b : F) : gaussValueF p F ρ ([a] - [b] - [a-b]) ≤ ρ * max |a| |b|`
- **What**: Witt homogeneity (2.8.1), binary *difference* form — the same estimate with subtraction.
- **How**: Verbatim the same scaling argument as the sum form: max-attaining `c` from `exists_attaining_coeff`, integral lifts via `perfectoidValuation_integers.exists_of_le_one`, `WittVector.teichmuller_coeff_zero` shows `constantCoeff ([aInt] - [bInt] - [aInt-bInt]) = 0` (the zeroth coordinate is a ring hom, so the signs cancel), then `gaussValueF_map_le_of_coeff_zero` and `gaussValueF_teichmuller_mul` rescale by `|c|`.
- **Hypotheses**: `ρ ≤ 1`; ambient perfectoid `F` of char `p`.
- **Uses from project**: `gaussValueF`, `perfectoidValuation`, `perfectoidValuation_integers`, `Ainf`, `OF`, `powerBoundedSubring`, `gaussValueF_zero`, `exists_attaining_coeff`, `gaussValueF_map_le_of_coeff_zero`, `gaussValueF_teichmuller_mul`
- **Used by**: `digit_sub_le`, `valued_sub_sub_PhiHatK_le`
- **Visibility**: public
- **Lines**: 184–265 (proof 189–265, 76 lines)
- **Notes**: proof >30 lines; structurally identical to the `add` form.

### `theorem gaussValueF_teichmuller_sum_sub_le`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ι : Type*} (s : Finset ι) (f : ι → F) {B : NNReal} (hf : ∀ i ∈ s, |f i| ≤ B) : gaussValueF p F ρ ((∑ i ∈ s, [f i]) - [∑ i ∈ s, f i]) ≤ ρ * B`
- **What**: The `n`-ary form of (2.8.1): the discrepancy between a finite sum of Teichmüller lifts and the lift of the sum is `ρ·B`-small, `B` a common bound on the entries.
- **How**: `Finset.induction_on`. Insert step splits the discrepancy algebraically (`ring`) into the binary error `[f a] + [Σ_t f] - [f a + Σ_t f]` plus the inductive discrepancy over `t`; `gaussValueF_add_le` bounds the total by the max of the two, the binary term by `gaussValueF_teichmuller_add_sub_le` (with `max |f a| |Σ_t f| ≤ B` from `Valuation.map_sum_le`), and the tail by the induction hypothesis. Boundedness side conditions are assembled from `bddAbove_gaussTermF_add` / `bddAbove_gaussTermF_neg` / `bddAbove_gaussTermF_teichmuller` and `gaussValueF_finset_sum_le`.
- **Hypotheses**: `0 < ρ < 1` (needed for `gaussValueF_add_le` and the boundedness lemmas); uniform entry bound `B` over `s`.
- **Uses from project**: `gaussValueF`, `gaussTermF`, `perfectoidValuation`, `gaussValueF_zero`, `gaussValueF_teichmuller_add_sub_le`, `gaussValueF_finset_sum_le`, `gaussValueF_add_le`, `gaussValueF_teichmuller`, `bddAbove_gaussTermF_teichmuller`, `bddAbove_gaussTermF_add`, `bddAbove_gaussTermF_neg`
- **Used by**: `gaussValueF_convPartial_sub_prefix_le`
- **Visibility**: public
- **Lines**: 267–329 (proof 275–329, 53 lines)
- **Notes**: proof >30 lines; `classical` opener.

### `def degAr`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x : hatK p F hρ0 hρ1) : ℕ`
- **What**: Kedlaya Definition 2.4, the **degree**: the largest coordinate index `n` at which `λ_ρ(x) = ρⁿ·|xₙ|` is attained. Junk value `0` for `x = 0` (Kedlaya's `deg 0 = -∞`) and for points outside `A^r`.
- **How**: `sSup` of the attainment set `{n | Valued.v x = ρ ^ n * |teichCoeffAr … x n|}` in `ℕ` (which is `0` when the set is empty or unbounded).
- **Hypotheses**: `0 < ρ < 1` (only to make `hatK`/`teichCoeffAr` typecheck); nothing forces `x ∈ Ar` — the definition is total.
- **Uses from project**: `hatK`, `teichCoeffAr`, `perfectoidValuation`
- **Used by**: `degAr_spec`, `gaussTerm_lt_of_degAr_lt`, `exists_eps_terms_le`, `degAr_eq_of_valued_sub_lt`, `valued_degAr_PhiHatK_convF`, `degAr_mul`, `divStep`, `valued_divStep_le`, `gaussTerm_sub_convF_divStep_le`, `descent_step`, `division_descent`, `approx_division`, `exact_division`, `isPrincipalIdealRing_ArSub` (also consumed downstream in `Groebner.lean`)
- **Visibility**: public
- **Lines**: 334–338 (definition body 336–338)
- **Notes**: the file's central definition; junk-value convention documented in the docstring.

### `theorem bddAbove_attainment`
- **Type**: `{ρ : NNReal} {hρ0 hρ1} {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) : BddAbove {n | Valued.v x = ρ ^ n * |teichCoeffAr … x n|}`
- **What**: For nonzero `x ∈ A^r`, only finitely many coordinate indices realize the value; the attainment set is bounded above.
- **How**: Since `x ≠ 0`, `Valued.v x > 0` (`Valuation.ne_zero_iff`); the coordinate terms tend to `0` (`tendsto_gaussTerm_teichCoeffAr`), so `eventually_lt_const` gives `K` past which every term is `< Valued.v x` and hence no index `> K` can be an equality point — a `by_contra` on membership.
- **Hypotheses**: `x ∈ A^r` (to have decaying coordinates) and `x ≠ 0` (to have a positive value to beat).
- **Uses from project**: `hatK`, `ArSub`, `teichCoeffAr`, `perfectoidValuation`, `tendsto_gaussTerm_teichCoeffAr`
- **Used by**: `degAr_spec`
- **Visibility**: public
- **Lines**: 340–355 (proof 344–355, 11 lines)
- **Notes**: `push Not` used (mathlib's generalized `push_neg`).

### `theorem degAr_spec`
- **Type**: `… (hx : x ∈ Ar) (hx0 : x ≠ 0) : Valued.v x = ρ ^ (degAr … x) * |x_(degAr … x)| ∧ ∀ m, Valued.v x = ρ ^ m * |x_m| → m ≤ degAr … x`
- **What**: The defining specification of `degAr` for nonzero elements of `A^r`: the value *is* attained at the degree index, and that index dominates every attaining index.
- **How**: The attainment set is nonempty by `exists_valued_eq_teichCoeffAr` and bounded above by `bddAbove_attainment`, so `Nat.sSup_mem` gives membership of the `sSup` and `le_csSup` gives the upper-bound half.
- **Hypotheses**: `x ∈ A^r`, `x ≠ 0`.
- **Uses from project**: `degAr`, `hatK`, `ArSub`, `teichCoeffAr`, `perfectoidValuation`, `exists_valued_eq_teichCoeffAr`, `bddAbove_attainment`
- **Used by**: `gaussTerm_lt_of_degAr_lt`, `valued_degAr_PhiHatK_convF`, `valued_divStep_le`, `gaussTerm_sub_convF_divStep_le`
- **Visibility**: public
- **Lines**: 357–373 (proof 364–373, 9 lines)
- **Notes**: none

### `theorem gaussTerm_lt_of_degAr_lt`
- **Type**: `… (hx : x ∈ Ar) (hx0 : x ≠ 0) {n : ℕ} (hn : degAr … x < n) : ρ ^ n * |x_n| < Valued.v x`
- **What**: Strictly above the degree, every coordinate term is strictly below the value.
- **How**: First `≤`: rewrite `Valued.v x` as the supremum of the terms (`valued_eq_iSup_teichCoeffAr`) and apply `le_ciSup`, boundedness of the range coming from the maximizing index in `exists_valued_eq_teichCoeffAr`. Then `lt_or_eq_of_le`: equality would put `n` in the attainment set, and `degAr_spec.2` would force `n ≤ degAr x`, contradicting `hn`.
- **Hypotheses**: `x ∈ A^r`, `x ≠ 0`, index strictly past the degree.
- **Uses from project**: `degAr`, `hatK`, `ArSub`, `teichCoeffAr`, `perfectoidValuation`, `valued_eq_iSup_teichCoeffAr`, `exists_valued_eq_teichCoeffAr`, `degAr_spec`
- **Used by**: `exists_eps_terms_le`, `valued_degAr_PhiHatK_convF`
- **Visibility**: public
- **Lines**: 375–393 (proof 380–393, 13 lines)
- **Notes**: proof >10 lines.

### `theorem exists_eps_terms_le`
- **Type**: `… (hx : x ∈ Ar) (hx0 : x ≠ 0) : ∃ ε : NNReal, ρ ≤ ε ∧ ε < 1 ∧ ∀ n, degAr … x < n → ρ ^ n * |x_n| ≤ ε * Valued.v x`
- **What**: The `ε` of Kedlaya Lemma 2.8: a *uniform* damping constant in `[ρ, 1)` bounding all post-degree coordinate terms relative to the value.
- **How**: The coordinate terms tend to `0` (`tendsto_gaussTerm_teichCoeffAr`), so past some `K` they are `< ρ·v(x)`. Only the finitely many indices in `Ioc (deg x) K` remain; take `ε := max ρ R` where `R` is the `Finset.sup` of the normalized terms `ρⁿ|xₙ|/v(x)` over that window. `ε < 1` follows from `Finset.sup_lt_iff` together with `gaussTerm_lt_of_degAr_lt` (each windowed term is `< v(x)`, so its normalization is `< 1`); the bound for `n ≤ K` is `Finset.le_sup` un-normalized, and for `n > K` it is the tail estimate.
- **Hypotheses**: `x ∈ A^r`, `x ≠ 0`, `0 < ρ < 1`.
- **Uses from project**: `degAr`, `hatK`, `ArSub`, `teichCoeffAr`, `perfectoidValuation`, `tendsto_gaussTerm_teichCoeffAr`, `gaussTerm_lt_of_degAr_lt`
- **Used by**: `approx_division`
- **Visibility**: public
- **Lines**: 395–440 (proof 402–440, 38 lines)
- **Notes**: proof >30 lines.

### `theorem tendsto_antidiagonal_sup_zero`
- **Type**: `{fa fb : ℕ → NNReal} (ha : Tendsto fa atTop (nhds 0)) (hb : Tendsto fb atTop (nhds 0)) : Tendsto (fun n => (Finset.range (n+1)).sup (fun i => fa i * fb (n - i))) atTop (nhds 0)`
- **What**: A purely real-analytic lemma: the antidiagonal sup of products of two null `NNReal` sequences is null.
- **How**: Both sequences are bounded (an internal `hbdd` helper: `eventually_lt_const 1` past `K₀`, then `max 1 (Finset.sup over range (K₀+1))`). Given `s > 0`, pick `b' ∈ (0, s)` (`exists_between`) and thresholds `Ka, Kb` where `fa < b'/Mb`, `fb < b'/Ma`; for `n ≥ Ka + Kb` and any `i ≤ n`, `omega` forces `Ka ≤ i` or `Kb ≤ n - i`, and in either case `fa i * fb (n-i) < b' < s` by `mul_lt_mul_of_pos_*`. `tendsto_order` + `Finset.sup_lt_iff` package it.
- **Hypotheses**: both input sequences tend to `0`; values in `NNReal` (order-topology argument via `tendsto_order`).
- **Uses from project**: []
- **Used by**: `tendsto_convF`
- **Visibility**: public
- **Lines**: 442–492 (proof 447–492, 45 lines)
- **Notes**: proof >30 lines; project-independent (a mathlib-able candidate); `push Not` used.

### `def convF`
- **Type**: `(a b : ℕ → F) (n : ℕ) : F := ∑ i ∈ Finset.range (n + 1), a i * b (n - i)`
- **What**: The Cauchy convolution of two coordinate sequences — the coefficient sequence of a product of two `Φ`-series.
- **How**: The usual finite antidiagonal sum `∑_{i+j=n} aᵢ bⱼ`, written with `n - i`.
- **Hypotheses**: none (any two sequences in `F`).
- **Uses from project**: []
- **Used by**: `tendsto_convF`, `gaussValueF_convPartial_sub_prefix_le`, `valued_mul_sub_PhiHatK_convF_le`, `gaussTerm_convF_le`, `valued_degAr_PhiHatK_convF`, `degAr_mul`, `gaussTerm_sub_convF_divStep_le`, `descent_step`
- **Visibility**: public
- **Lines**: 494–497
- **Notes**: none

### `theorem tendsto_convF`
- **Type**: `{ρ : NNReal} {a b : ℕ → F} (ha : Tendsto (fun n => ρ^n * |a n|) atTop (nhds 0)) (hb : … b …) : Tendsto (fun n => ρ^n * |convF F a b n|) atTop (nhds 0)`
- **What**: Decay of scaled coordinate sequences is preserved by convolution — the Cauchy product of two admissible series is admissible.
- **How**: Squeeze (`tendsto_of_tendsto_of_tendsto_of_le_of_le`) against `tendsto_antidiagonal_sup_zero` applied to the two scaled sequences. The pointwise bound uses the ultrametric inequality `Valuation.map_sum_le` to replace `|convF a b n|` by the `Finset.sup` of `|aₖ b_{n-k}|`, picks the maximizing index with `Finset.exists_mem_eq_sup`, and splits `ρⁿ = ρ^{k₀}·ρ^{n-k₀}` (`Nat.add_sub_cancel'`) to factor the term as a product of one `a`-term and one `b`-term, which is `≤` the antidiagonal sup by `Finset.le_sup`.
- **Hypotheses**: both input scaled sequences null; `F` nonarchimedean (for `Valuation.map_sum_le`).
- **Uses from project**: `convF`, `perfectoidValuation`, `tendsto_antidiagonal_sup_zero`
- **Used by**: `valued_mul_sub_PhiHatK_convF_le`, `valued_degAr_PhiHatK_convF`, `degAr_mul`, `descent_step`
- **Visibility**: public
- **Lines**: 499–538 (proof 506–538, 32 lines)
- **Notes**: proof >30 lines.

### `theorem bddAbove_range_of_tendsto_zero`
- **Type**: `{f : ℕ → NNReal} (hf : Tendsto f atTop (nhds 0)) : BddAbove (Set.range f)`
- **What**: A null `NNReal` sequence has bounded range.
- **How**: `eventually_lt_const one_pos` gives `K₀` past which `f < 1`; the explicit bound `max 1 ((Finset.range (K₀+1)).sup f)` covers the finite head via `Finset.le_sup` and the tail via `1`.
- **Hypotheses**: `f` tends to `0` in `NNReal`.
- **Uses from project**: []
- **Used by**: `digit_sub_le`, `valued_degAr_PhiHatK_convF`
- **Visibility**: public
- **Lines**: 540–549 (proof 543–549, 6 lines)
- **Notes**: project-independent; duplicates the internal `hbdd` of `tendsto_antidiagonal_sup_zero` (dedup candidate).

### `theorem gaussTerm_teichCoeffAr_le'`
- **Type**: `… (hx : x ∈ Ar) (n : ℕ) : ρ ^ n * |teichCoeffAr … x n| ≤ Valued.v x`
- **What**: Total ("primed") form of the `A^r` coordinate-term bound — the `x ≠ 0` hypothesis of `gaussTerm_teichCoeffAr_le` removed.
- **How**: Case on `Valued.v x = 0`: then `x = 0` by `Valuation.zero_iff` and all coordinates vanish (`teichCoeffAr_zero`), so both sides are `0`; otherwise delegate to the ArCompletion lemma `gaussTerm_teichCoeffAr_le`.
- **Hypotheses**: `x ∈ A^r` only.
- **Uses from project**: `hatK`, `ArSub`, `teichCoeffAr`, `perfectoidValuation`, `teichCoeffAr_zero`, `gaussTerm_teichCoeffAr_le`
- **Used by**: `digit_sub_le`, `degAr_eq_of_valued_sub_lt`, `valued_mul_sub_PhiHatK_convF_le`, `valued_degAr_PhiHatK_convF`, `valued_divStep_le`, `valued_sub_sub_PhiHatK_le`, `gaussTerm_sub_convF_divStep_le`, `descent_step`
- **Visibility**: public
- **Lines**: 551–561 (proof 555–561, 6 lines)
- **Notes**: one of the two most-reused lemmas of the file.

### `theorem digit_sub_le`
- **Type**: `… (hx : x ∈ Ar) (hy : y ∈ Ar) (n : ℕ) : ρ ^ n * |x_n - y_n| ≤ max (Valued.v (x - y)) (ρ * max (Valued.v x) (Valued.v y))`
- **What**: "Digit comparison (DC⁺)", the engine of Kedlaya Remark 2.7 at one radius: coordinatewise differences of two elements of `A^r` are controlled by the value of the difference plus one `ρ`-damped term.
- **How**: Let `e k := xₖ - yₖ`; `e` decays (squeeze against `max` of the two decaying term sequences using `Valuation.map_sub` and `nnreal_mul_max`), so `Φ(e) := PhiHatK … e` exists and `valued_PhiHatK` identifies `v(Φ e)` with `⨆ ρᵏ|eₖ|`. The core estimate `hPNval` bounds, uniformly in `N`, the value of the `Aloc` prefix combination `prefix a N - prefix b N - prefix e N`: after `valued_AlocToHatK` + `gaussValueF_alocToWittF` + `alocToWittF_prefixAloc` the difference regroups (`Finset.sum_sub_distrib`, `ring`) into `∑ₖ pᵏ·([aₖ] - [bₖ] - [aₖ-bₖ])`, and each summand is bounded by `ρ·max(ρᵏ|aₖ|, ρᵏ|bₖ|) ≤ ρ·M` via `gaussValueF_teichmuller_sub_sub_le`, `gaussValueF_p_pow_mul` and `gaussTerm_teichCoeffAr_le'`. Passing to the limit (`tendsto_PhiHatK`, `eventually_valued_sub_le_of_tendsto`) gives `v((x-y) - Φ e) ≤ ρ·M`, hence `v(Φ e) ≤ max (v(x-y)) (ρ M)` by the ultrametric triangle inequality, and finally `ρⁿ|eₙ| ≤ ⨆ ρᵏ|eₖ| = v(Φ e)` (`le_ciSup` with `bddAbove_range_of_tendsto_zero`).
- **Hypotheses**: `x, y ∈ A^r`; `0 < ρ < 1`; completeness of `hatK` (implicit in `PhiHatK`).
- **Uses from project**: `hatK`, `ArSub`, `teichCoeffAr`, `perfectoidValuation`, `PhiHatK`, `AlocToHatK`, `prefixAloc`, `alocToWittF`, `gaussTermF`, `gaussValueF`, `nnreal_mul_max`, `tendsto_gaussTerm_teichCoeffAr`, `valued_PhiHatK`, `PhiHatK_teichCoeffAr`, `tendsto_PhiHatK`, `valued_AlocToHatK`, `gaussValueF_alocToWittF`, `alocToWittF_prefixAloc`, `gaussValueF_finset_sum_le`, `bddAbove_gaussTermF_add`, `bddAbove_gaussTermF_neg`, `bddAbove_gaussTermF_teichmuller`, `bddAbove_gaussTermF_p_pow_mul`, `gaussValueF_p_pow_mul`, `gaussValueF_teichmuller_sub_sub_le`, `gaussTerm_teichCoeffAr_le'`, `eventually_valued_sub_le_of_tendsto`, `bddAbove_range_of_tendsto_zero`
- **Used by**: `degAr_eq_of_valued_sub_lt`, `descent_step`
- **Visibility**: public
- **Lines**: 563–715 (proof 571–715, 144 lines)
- **Notes**: proof >30 lines — the longest "engine" proof; substantially overlaps `valued_sub_sub_PhiHatK_le` (lines 1451–1588), which re-proves `hPNval` verbatim. Decomposition/dedup candidate.

### `theorem valued_eq_of_valued_sub_lt`
- **Type**: `… {x y : hatK p F hρ0 hρ1} (hxy : Valued.v (x - y) < Valued.v x) : Valued.v y = Valued.v x`
- **What**: Ultrametric "isosceles" stability: a perturbation of strictly smaller value does not change the value.
- **How**: Write `y = x + (-(x-y))` and apply `Valuation.map_add_eq_of_lt_left` (using `Valuation.map_neg` to transport `hxy`).
- **Hypotheses**: the difference has strictly smaller value than `x`; `Valued.v` is a (nonarchimedean) valuation.
- **Uses from project**: `hatK`
- **Used by**: `degAr_eq_of_valued_sub_lt`
- **Visibility**: public
- **Lines**: 717–725 (proof 720–725, 5 lines)
- **Notes**: none

### `theorem degAr_eq_of_valued_sub_lt`
- **Type**: `… (hx : x ∈ Ar) (hy : y ∈ Ar) (hxy : Valued.v (x - y) < Valued.v x) : degAr … x = degAr … y`
- **What**: Kedlaya Remark 2.7, leading-support stability: a perturbation strictly below the value changes neither the value nor the set of attaining indices, hence not the degree.
- **How**: `valued_eq_of_valued_sub_lt` gives `v y = v x`; then `digit_sub_le` (with `max_self`) bounds every coordinate difference by `B := max (v(x-y)) (ρ·v x)`, which is `< v x` since `ρ < 1` (`mul_lt_of_lt_one_left`). The attainment sets are then shown *equal* as sets: if `n` attains for `x`, the ultrametric split `xₙ = yₙ + (xₙ - yₙ)` plus `nnreal_mul_max` forces the max to be realized by the `y`-term (the difference term is `≤ B < v x`), giving attainment for `y` by `le_antisymm` against `gaussTerm_teichCoeffAr_le'`; symmetrically in the other direction. Finally `rw [degAr, degAr, hsets]`.
- **Hypotheses**: `x, y ∈ A^r`; `v(x - y) < v x`; `ρ < 1`.
- **Uses from project**: `degAr`, `hatK`, `ArSub`, `teichCoeffAr`, `perfectoidValuation`, `nnreal_mul_max`, `valued_eq_of_valued_sub_lt`, `digit_sub_le`, `gaussTerm_teichCoeffAr_le'`
- **Used by**: `degAr_mul` (and, outside the file, `Groebner.valued_degAr_eq_of_sub_lt`)
- **Visibility**: public
- **Lines**: 727–809 (proof 732–809, 77 lines)
- **Notes**: proof >30 lines; the two set-inclusion branches are near-mirror images (decomposition candidate).

### `def convPartialAloc`
- **Type**: `(a b : ℕ → F) (N : ℕ) : Aloc p F ϖ := ∑ n ∈ Finset.range N, (p : Aloc p F ϖ)^n * ∑ k ∈ Finset.range (n+1), alocTeich p F ϖ (a k * b (n - k))`
- **What**: Kedlaya's `T_N`: the `Aloc`-level partial sum of the double series `Σₙ pⁿ Σ_{i+j=n} [aᵢbⱼ]` — the antidiagonal regrouping of a prefix product.
- **How**: A literal finite double sum over `range N` and each antidiagonal `range (n+1)`, using `alocTeich` for the Teichmüller lift into the localization `Aloc`.
- **Hypotheses**: none beyond ambient (`ϖ` a pseudo-uniformizer, to define `Aloc`).
- **Uses from project**: `Aloc`, `alocTeich`
- **Used by**: `alocToWittF_convPartialAloc`, `gaussValueF_convPartial_sub_prefix_le`, `gaussValueF_prefix_mul_sub_convPartial_le`, `valued_mul_sub_PhiHatK_convF_le`
- **Visibility**: public
- **Lines**: 811–815
- **Notes**: none

### `theorem alocToWittF_convPartialAloc`
- **Type**: `(a b : ℕ → F) (N : ℕ) : alocToWittF p F ϖ (convPartialAloc p F ϖ a b N) = ∑ n ∈ range N, (p : WittVector p F)^n * ∑ k ∈ range (n+1), [a k * b (n-k)]`
- **What**: The ring map `alocToWittF` transports the `Aloc` convolution partial to the corresponding Witt-vector double sum.
- **How**: Push `alocToWittF` through the sums and products (`map_sum`, `map_mul`, `map_pow`, `map_natCast`) and use `alocToWittF_alocTeich` on each Teichmüller generator.
- **Hypotheses**: none beyond ambient.
- **Uses from project**: `convPartialAloc`, `alocToWittF`, `alocToWittF_alocTeich`
- **Used by**: `gaussValueF_convPartial_sub_prefix_le`, `gaussValueF_prefix_mul_sub_convPartial_le`
- **Visibility**: public
- **Lines**: 817–827 (proof 822–827, 5 lines)
- **Notes**: none

### `theorem gaussValueF_convPartial_sub_prefix_le`
- **Type**: `(hρ0 : 0 < ρ) (hρ1 : ρ < 1) (a b : ℕ → F) {A B : NNReal} (hA : ∀ n, ρⁿ|a n| ≤ A) (hB : ∀ n, ρⁿ|b n| ≤ B) (N : ℕ) : gaussValueF p F ρ (alocToWittF (convPartialAloc a b N) - alocToWittF (prefixAloc (convF F a b) N)) ≤ ρ * (A * B)`
- **What**: The **Witt-addition error** of the convolution partials: replacing each antidiagonal sum of Teichmüller lifts by the Teichmüller lift of the antidiagonal sum costs at most `ρ·A·B`, uniformly in `N`.
- **How**: After `alocToWittF_convPartialAloc` and `alocToWittF_prefixAloc` the difference regroups (`Finset.sum_sub_distrib`, `ring`) as `∑ₙ pⁿ·((∑ₖ [aₖ b_{n-k}]) - [convF a b n])`; `gaussValueF_finset_sum_le` reduces to a per-`n` bound, `gaussValueF_p_pow_mul` peels the `pⁿ`, and the `n`-ary homogeneity `gaussValueF_teichmuller_sum_sub_le` bounds the inner discrepancy by `ρ·Bₙ` where `Bₙ` is the `Finset.sup` of `|aₖ b_{n-k}|`. Finally `ρⁿ·Bₙ ≤ A·B` by picking the max-attaining index (`Finset.exists_mem_eq_sup`) and splitting `ρⁿ = ρ^{k₀}ρ^{n-k₀}`.
- **Hypotheses**: `0 < ρ < 1`; uniform scaled bounds `A` on `a` and `B` on `b`.
- **Uses from project**: `convF`, `convPartialAloc`, `alocToWittF`, `prefixAloc`, `gaussValueF`, `gaussTermF`, `perfectoidValuation`, `alocToWittF_convPartialAloc`, `alocToWittF_prefixAloc`, `gaussValueF_finset_sum_le`, `gaussValueF_teichmuller_sum_sub_le`, `bddAbove_gaussTermF_teichmuller`, `bddAbove_gaussTermF_neg`, `bddAbove_gaussTermF_add`, `bddAbove_gaussTermF_p_pow_mul`, `gaussValueF_p_pow_mul`, `gaussValueF_teichmuller`
- **Used by**: `valued_mul_sub_PhiHatK_convF_le`
- **Visibility**: public
- **Lines**: 829–904 (proof 838–904, 66 lines)
- **Notes**: proof >30 lines; contains an inline comment explaining the `ρⁿ·(ρ·Bₙ) ≤ ρ·(A·B)` reduction.

### `theorem gaussValueF_prefix_mul_sub_convPartial_le`
- **Type**: `(hρ0 : 0 < ρ) (hρ1 : ρ < 1) (a b : ℕ → F) {T : NNReal} (N : ℕ) (hT : ∀ i j, N ≤ i + j → (ρⁱ|aᵢ|)(ρʲ|bⱼ|) ≤ T) : gaussValueF p F ρ (alocToWittF (prefixAloc a N) * alocToWittF (prefixAloc b N) - alocToWittF (convPartialAloc a b N)) ≤ T`
- **What**: The **prefix-product tail** (Kedlaya's identity (10)): a prefix product and the convolution partial differ only in the antidiagonal terms of total index `≥ N`, so any uniform tail bound `T` controls the difference.
- **How**: Combinatorial box-minus-triangle computation. `Finset.sum_product'` + `Finset.sum_mul_sum` writes the prefix product as a sum over `box = range N ×ˢ range N` of `p^{i+j}·[aᵢbⱼ]`; `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk` + `Finset.sum_biUnion` (with pairwise-disjointness of the antidiagonals) writes the convolution partial as the sum over the triangle `TRI = ⋃_{n<N} antidiagonal n`; `Finset.sum_sdiff` for `TRI ⊆ box` makes the difference a sum over `box \ TRI`, every member of which satisfies `N ≤ q.1 + q.2`. Then `gaussValueF_finset_sum_le` + `gaussValueF_p_pow_mul` + `gaussValueF_teichmuller` reduce each term to `ρ^{i+j}|aᵢbⱼ| = (ρⁱ|aᵢ|)(ρʲ|bⱼ|) ≤ T`.
- **Hypotheses**: `0 < ρ < 1`; the tail hypothesis `hT` for all `i + j ≥ N`.
- **Uses from project**: `convPartialAloc`, `alocToWittF`, `prefixAloc`, `gaussValueF`, `gaussTermF`, `perfectoidValuation`, `alocToWittF_prefixAloc`, `alocToWittF_convPartialAloc`, `gaussValueF_finset_sum_le`, `bddAbove_gaussTermF_p_pow_mul`, `bddAbove_gaussTermF_teichmuller`, `gaussValueF_p_pow_mul`, `gaussValueF_teichmuller`
- **Used by**: `valued_mul_sub_PhiHatK_convF_le`
- **Visibility**: public
- **Lines**: 906–998 (proof 917–998, 80 lines)
- **Notes**: proof >30 lines; `classical` opener; `push Not` used.

### `theorem valued_mul_sub_PhiHatK_convF_le`
- **Type**: `… (hx : x ∈ Ar) (hy : y ∈ Ar) : Valued.v (x * y - PhiHatK … (convF F (teichCoeffAr … x) (teichCoeffAr … y))) ≤ ρ * (Valued.v x * Valued.v y)`
- **What**: The **product decomposition** (Kedlaya's leading-term control, sol (13)): the product of two elements of `A^r` agrees with the `Φ`-series of the convolution of their coordinates up to a `ρ`-damped error.
- **How**: Four-term telescoping chain `x·y → (prefix a N)(prefix b N) → convPartialAloc → prefix (convF a b) N → Φ(convF a b)` (assembled by `ring` and split with `Valuation.map_add`/`max_le`). Leg 1 and leg 4 are limit errors, handled by `eventually_valued_sub_le_of_tendsto` applied to `hSx.mul hSy` and `tendsto_PhiHatK`; leg 2 is `gaussValueF_prefix_mul_sub_convPartial_le` with the tail constant `ρ·v(x)v(y)` (justified by choosing `N ≥ Ka + Kb` past the decay thresholds of both coordinate sequences, then an `omega` case split `Ka ≤ i ∨ Kb ≤ j`); leg 3 is `gaussValueF_convPartial_sub_prefix_le` with `A := v x`, `B := v y` from `gaussTerm_teichCoeffAr_le'`. A separate degenerate branch handles `v x · v y = 0`, where every convolution term vanishes.
- **Hypotheses**: `x, y ∈ A^r`; `0 < ρ < 1`.
- **Uses from project**: `hatK`, `ArSub`, `teichCoeffAr`, `perfectoidValuation`, `convF`, `convPartialAloc`, `PhiHatK`, `AlocToHatK`, `prefixAloc`, `tendsto_gaussTerm_teichCoeffAr`, `tendsto_convF`, `gaussTerm_teichCoeffAr_le'`, `valued_PhiHatK`, `PhiHatK_teichCoeffAr`, `tendsto_PhiHatK`, `eventually_valued_sub_le_of_tendsto`, `valued_AlocToHatK`, `gaussValueF_alocToWittF`, `gaussValueF_prefix_mul_sub_convPartial_le`, `gaussValueF_convPartial_sub_prefix_le`
- **Used by**: `degAr_mul`, `descent_step`
- **Visibility**: public
- **Lines**: 1000–1142 (proof 1008–1142, 134 lines)
- **Notes**: proof >30 lines; annotated with inline section comments (`-- the three convergences`, `-- the four-term chain`). Decomposition candidate.

### `theorem gaussTerm_convF_le`
- **Type**: `{ρ : NNReal} (a b : ℕ → F) {A B : NNReal} (hA : ∀ n, ρⁿ|a n| ≤ A) (hB : ∀ n, ρⁿ|b n| ≤ B) (n : ℕ) : ρ ^ n * |convF F a b n| ≤ A * B`
- **What**: Scaled convolution terms are bounded by the product of the input bounds (submultiplicativity of the Gauss norm at the coefficient level).
- **How**: `Valuation.map_sum_le` replaces `|convF a b n|` by the `Finset.sup` of `|aₖ b_{n-k}|`; the max-attaining index from `Finset.exists_mem_eq_sup` plus the splitting `ρⁿ = ρ^{k₀}·ρ^{n-k₀}` (`Nat.add_sub_cancel'`) factors the term into an `a`-term times a `b`-term, each bounded by `hA`/`hB`.
- **Hypotheses**: uniform scaled bounds `A`, `B`; `F` nonarchimedean.
- **Uses from project**: `convF`, `perfectoidValuation`
- **Used by**: `valued_degAr_PhiHatK_convF`, `descent_step`
- **Visibility**: public
- **Lines**: 1144–1169 (proof 1148–1169, 21 lines)
- **Notes**: proof >10 lines; its core computation is repeated verbatim inside `tendsto_convF`, `gaussValueF_convPartial_sub_prefix_le` and `valued_degAr_PhiHatK_convF` (dedup candidate).

### `theorem valued_degAr_PhiHatK_convF`
- **Type**: `… (hx : x ∈ Ar) (hy : y ∈ Ar) (hx0 : x ≠ 0) (hy0 : y ≠ 0) : Valued.v (PhiHatK … (convF F x_• y_•)) = Valued.v x * Valued.v y ∧ degAr … (PhiHatK … (convF F x_• y_•)) = degAr … x + degAr … y`
- **What**: **Degree of the convolution series**: the `Φ`-series of the convolution attains exactly `v(x)·v(y)`, and does so at index `deg x + deg y`, dropping strictly above it.
- **How**: The key strict bound `hstrict` says that any antidiagonal factorization `(k, n-k)` with `k > deg x` or `n-k > deg y` is *strictly* below `v(x)v(y)`, by `gaussTerm_lt_of_degAr_lt` on the offending factor and `gaussTerm_teichCoeffAr_le'` on the other. At `n = m + l` the convolution splits (`Finset.add_sum_erase`) into the leading term `a_m b_l` — whose scaled value is `v(x)v(y)` by the two `degAr_spec` attainments — plus an erased remainder that is strictly smaller (`hrest`, via `Valuation.map_sum_le` + `hstrict`); `Valuation.map_add_eq_of_lt_left` then gives exact attainment. `hdrop` shows every `n > m + l` is strictly below. `valued_PhiHatK` turns the value into `⨆ₙ ρⁿ|convF a b n|`, bounded above by `gaussTerm_convF_le` and below by the attained index (`le_ciSup` with `bddAbove_range_of_tendsto_zero`). For the degree, `teichCoeffAr_PhiHatK` identifies the coordinates of `Φ(conv)` with `convF a b`, so the attainment set is `{n | v(x)v(y) = ρⁿ|convF a b n|}`, which contains `m+l` and is bounded by it — `csSup_le`/`le_csSup` give `sSup = m + l`.
- **Hypotheses**: `x, y ∈ A^r` both nonzero; `0 < ρ < 1`.
- **Uses from project**: `degAr`, `hatK`, `ArSub`, `teichCoeffAr`, `perfectoidValuation`, `convF`, `PhiHatK`, `tendsto_gaussTerm_teichCoeffAr`, `tendsto_convF`, `gaussTerm_teichCoeffAr_le'`, `degAr_spec`, `gaussTerm_lt_of_degAr_lt`, `valued_PhiHatK`, `gaussTerm_convF_le`, `bddAbove_range_of_tendsto_zero`, `teichCoeffAr_PhiHatK`
- **Used by**: `degAr_mul`
- **Visibility**: public
- **Lines**: 1171–1336 (proof 1181–1336, 155 lines)
- **Notes**: proof >30 lines — the longest in the file; heavily commented with step markers. Decomposition candidate (`hstrict` / `hattain` / `hdrop` are natural helper lemmas).

### `theorem degAr_mul`
- **Type**: `… (hx : x ∈ Ar) (hy : y ∈ Ar) (hx0 : x ≠ 0) (hy0 : y ≠ 0) : degAr … (x * y) = degAr … x + degAr … y`
- **What**: **Kedlaya Lemma 2.6** (single-radius specialization): the degree is additive on nonzero elements of `A^r`.
- **How**: `valued_degAr_PhiHatK_convF` computes the value and degree of `Φ(conv)`; `valued_mul_sub_PhiHatK_convF_le` shows `v(x·y - Φ(conv)) ≤ ρ·v(x)v(y) < v(x·y)` (using `mul_lt_of_lt_one_left` with `ρ < 1` and `Valuation.map_mul`), so `degAr_eq_of_valued_sub_lt` (applied to `x·y ∈ A^r` by `mul_mem` and `Φ(conv) ∈ A^r` by `PhiHatK_mem_ArSub`) transfers the degree.
- **Hypotheses**: `x, y ∈ A^r`, both nonzero; `ρ < 1` (strict, to make the error term subdominant).
- **Uses from project**: `degAr`, `hatK`, `ArSub`, `teichCoeffAr`, `PhiHatK`, `convF`, `valued_degAr_PhiHatK_convF`, `tendsto_gaussTerm_teichCoeffAr`, `tendsto_convF`, `valued_mul_sub_PhiHatK_convF_le`, `degAr_eq_of_valued_sub_lt`, `PhiHatK_mem_ArSub`
- **Used by**: unused in file (and unused elsewhere in the project — a stated-but-unconsumed headline result)
- **Visibility**: public
- **Lines**: 1338–1363 (proof 1344–1363, 19 lines)
- **Notes**: proof >10 lines. Currently dead code within the repo.

### `theorem tendsto_div_shift`
- **Type**: `… (hy : y ∈ Ar) (m : ℕ) (c : F) : Tendsto (fun n => ρ ^ n * |teichCoeffAr … y (n + m) / c|) atTop (nhds 0)`
- **What**: The division-step coordinate sequence — the coordinates of `y` shifted by `m` and divided by a fixed `c` — decays, so it defines an element of `A^r`.
- **How**: Compose the decay `tendsto_gaussTerm_teichCoeffAr` with `Filter.tendsto_add_atTop_nat m` to shift, then multiply by the constant `(ρ^m)⁻¹ (|c|)⁻¹` (`Tendsto.mul_const`, `zero_mul`); a `congr` computation using `map_div₀` and `ρ^{n+m}(ρ^m)⁻¹ = ρⁿ` (`mul_inv_cancel₀`, `pow_pos hρ0 m`) matches the two expressions.
- **Hypotheses**: `y ∈ A^r`; `0 < ρ` (to invert `ρ^m`). Note `c = 0` is allowed — the identity still holds in `NNReal` since `|0|⁻¹ = 0`.
- **Uses from project**: `hatK`, `ArSub`, `teichCoeffAr`, `perfectoidValuation`, `tendsto_gaussTerm_teichCoeffAr`
- **Used by**: `divStep_mem`, `valued_divStep_le`, `descent_step`
- **Visibility**: public
- **Lines**: 1365–1388 (proof 1370–1388, 18 lines)
- **Notes**: proof >10 lines.

### `def divStep`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x y : hatK p F hρ0 hρ1) : hatK p F hρ0 hρ1`
- **What**: **The division quotient** (Kedlaya's `z_l`): the `Φ`-series of the coordinates of `y`, shifted by `deg x` and divided by the leading coefficient `x_{deg x}` — one Euclidean division step.
- **How**: `PhiHatK … (fun n => teichCoeffAr … y (n + degAr … x) / teichCoeffAr … x (degAr … x))`, i.e. the "long division" guess that cancels the top coefficient of `y` against the leading coefficient of `x`.
- **Hypotheses**: none stated (total on `hatK × hatK`); meaningful only when `x, y ∈ A^r` and `x ≠ 0`.
- **Uses from project**: `hatK`, `PhiHatK`, `teichCoeffAr`, `degAr`
- **Used by**: `divStep_mem`, `valued_divStep_le`, `valued_sub_divStep_mul_le`, `descent_step`, `division_descent`
- **Visibility**: public
- **Lines**: 1390–1396
- **Notes**: none

### `theorem divStep_mem`
- **Type**: `… (hx : x ∈ Ar) (hy : y ∈ Ar) : divStep p F ϖ hρ0 hρ1 x y ∈ ArSub p F ϖ hρ0 hρ1`
- **What**: The division quotient stays in `A^r`.
- **How**: Term-mode: `PhiHatK_mem_ArSub` applied to the decay supplied by `tendsto_div_shift`.
- **Hypotheses**: `y ∈ A^r` (used); `hx` is present but unused by the term.
- **Uses from project**: `divStep`, `ArSub`, `hatK`, `PhiHatK_mem_ArSub`, `tendsto_div_shift`
- **Used by**: `descent_step`, `division_descent`
- **Visibility**: public
- **Lines**: 1398–1402 (term proof, 1 line)
- **Notes**: `hx` appears unused in the proof term (generalisation/cleanup candidate); no docstring.

### `theorem valued_divStep_le`
- **Type**: `… (hx : x ∈ Ar) (hy : y ∈ Ar) (hx0 : x ≠ 0) : Valued.v (divStep … x y) * Valued.v x ≤ Valued.v y`
- **What**: **Quotient value bound**: `v(z)·v(x) ≤ v(y)` for the division quotient `z` (the inequality suffices; equality is not needed downstream).
- **How**: `valued_PhiHatK` (with the decay from `tendsto_div_shift`) turns `v z` into `⨆ₙ ρⁿ|y_{n+m}/x_m|`; `NNReal.mul_iSup` moves `v x` inside and `ciSup_le` reduces to a per-`n` bound. There the leading attainment `degAr_spec` (`v x = ρ^m |x_m|`) cancels against `|x_m|⁻¹` (`mul_inv_cancel₀`, with `|x_m| ≠ 0` derived from `v x ≠ 0`), leaving exactly `ρ^{n+m}|y_{n+m}| ≤ v y` — which is `gaussTerm_teichCoeffAr_le'`.
- **Hypotheses**: `x, y ∈ A^r`; `x ≠ 0` (so the leading coefficient is invertible).
- **Uses from project**: `divStep`, `degAr`, `hatK`, `ArSub`, `teichCoeffAr`, `perfectoidValuation`, `degAr_spec`, `valued_PhiHatK`, `tendsto_div_shift`, `gaussTerm_teichCoeffAr_le'`
- **Used by**: `valued_sub_divStep_mul_le`, `descent_step`
- **Visibility**: public
- **Lines**: 1404–1437 (proof 1408–1437, 29 lines)
- **Notes**: proof >10 lines.

### `theorem valued_sub_divStep_mul_le`
- **Type**: `… (hx : x ∈ Ar) (hy : y ∈ Ar) (hx0 : x ≠ 0) : Valued.v (y - divStep … x y * x) ≤ Valued.v y`
- **What**: One division step never increases the value of the remainder.
- **How**: Ultrametric `Valuation.map_sub` + `max_le`: the `y` leg is `le_rfl`, and the `z·x` leg is `Valuation.map_mul` followed by `valued_divStep_le`.
- **Hypotheses**: `x, y ∈ A^r`; `x ≠ 0`.
- **Uses from project**: `divStep`, `hatK`, `ArSub`, `valued_divStep_le`
- **Used by**: `descent_step`, `division_descent`
- **Visibility**: public
- **Lines**: 1439–1446 (proof 1443–1446, 3 lines)
- **Notes**: none

### `theorem valued_sub_sub_PhiHatK_le`
- **Type**: `… (hx : x ∈ Ar) (hy : y ∈ Ar) : Valued.v ((x - y) - PhiHatK … (fun k => x_k - y_k)) ≤ ρ * max (Valued.v x) (Valued.v y)`
- **What**: The **`Φ`-subtraction comparison** — the `H∞` bound of (DC⁺) as a standalone statement: the actual difference `x - y` deviates from the `Φ`-series of the pointwise coordinate difference by at most `ρ·max(v x, v y)`.
- **How**: The same `hPNval` computation as `digit_sub_le`: after `valued_AlocToHatK` + `gaussValueF_alocToWittF` + `alocToWittF_prefixAloc`, the prefix combination regroups into `∑ₖ pᵏ([aₖ]-[bₖ]-[aₖ-bₖ])` and each summand is bounded by `gaussValueF_teichmuller_sub_sub_le` composed with `gaussValueF_p_pow_mul`, `nnreal_mul_max` and `gaussTerm_teichCoeffAr_le'`. Passing to the limit with `eventually_valued_sub_le_of_tendsto` on `(hSx.sub hSy).sub hSe` and splitting with `Valuation.map_add`/`Valuation.map_sub_swap` yields the claim; a degenerate `M = 0` branch handles `x = y = 0`.
- **Hypotheses**: `x, y ∈ A^r`; `0 < ρ < 1`.
- **Uses from project**: `hatK`, `ArSub`, `teichCoeffAr`, `perfectoidValuation`, `PhiHatK`, `AlocToHatK`, `prefixAloc`, `alocToWittF`, `gaussTermF`, `nnreal_mul_max`, `tendsto_gaussTerm_teichCoeffAr`, `PhiHatK_teichCoeffAr`, `tendsto_PhiHatK`, `valued_AlocToHatK`, `gaussValueF_alocToWittF`, `alocToWittF_prefixAloc`, `gaussValueF_finset_sum_le`, `bddAbove_gaussTermF_add`, `bddAbove_gaussTermF_neg`, `bddAbove_gaussTermF_teichmuller`, `bddAbove_gaussTermF_p_pow_mul`, `gaussValueF_p_pow_mul`, `gaussValueF_teichmuller_sub_sub_le`, `gaussTerm_teichCoeffAr_le'`, `valued_PhiHatK`, `eventually_valued_sub_le_of_tendsto`
- **Used by**: `descent_step`
- **Visibility**: public
- **Lines**: 1448–1588 (proof 1456–1588, 132 lines)
- **Notes**: proof >30 lines; lines 1495–1548 duplicate `digit_sub_le`'s `hPNval` almost verbatim — the single clearest dedup opportunity in the file.

### `theorem gaussTerm_sub_convF_divStep_le`
- **Type**: `… (hx : x ∈ Ar) (hy : y ∈ Ar) (hx0 : x ≠ 0) {ε c : NNReal} {N : ℕ} (hεx : ∀ j > degAr … x, ρʲ|x_j| ≤ ε * Valued.v x) (hw1 : ε * Valued.v y ≤ c) (hmN : degAr … x ≤ N) (hw2 : ∀ n > N, ρⁿ|y_n| ≤ c) : ∀ n ≥ N, ρⁿ * |y_n - convF F (fun k => y_{k+m}/x_m) x_• n| ≤ c`
- **What**: **The (2.8.2) coefficient analysis**: past the working index `N`, the coordinates of `y` and of the quotient-times-divisor convolution agree to within `c`.
- **How**: The `k = n - m` term of the convolution is exactly `(y_n / x_m)·x_m = y_n` (`div_mul_cancel₀` after `omega`-index arithmetic), so `Finset.add_sum_erase` isolates it and the difference is `-(erased sum)`. Bounding the erased sum termwise via `Valuation.map_sum_le` + `Finset.exists_mem_eq_sup`, the maximizing index `k₀ ≠ n - m` falls into two cases decided by `lt_or_gt_of_ne` + `omega`: if `k₀ < n - m` then `n - k₀ > m`, so the `x`-factor is `ε`-damped by `hεx` and the `y`-factor is `≤ v y`, giving `≤ (ε·v y)·v x ≤ c·v x` by `hw1`; if `k₀ > n - m` then `k₀ + m > N`, so the `y`-factor is `c`-damped by `hw2` and the `x`-factor is `≤ v x` (`gaussTerm_teichCoeffAr_le'`). An explicit `hstep` calc multiplies through by `v x = ρ^m|x_m|` (from `degAr_spec`) to clear the denominator, and `le_of_mul_le_mul_right` with `v x > 0` finishes.
- **Hypotheses**: `x, y ∈ A^r`; `x ≠ 0`; the `ε`-property of `x` past its degree; the working-window hypotheses `hw1`, `hmN`, `hw2`.
- **Uses from project**: `degAr`, `hatK`, `ArSub`, `teichCoeffAr`, `perfectoidValuation`, `convF`, `degAr_spec`, `gaussTerm_teichCoeffAr_le'`
- **Used by**: `descent_step`
- **Visibility**: public
- **Lines**: 1590–1745 (proof 1609–1745, 135 lines)
- **Notes**: proof >30 lines; heavily commented with the three-case narrative from Kedlaya (2.8.2). Decomposition candidate.

### `theorem descent_step`
- **Type**: `… (hx : x ∈ Ar) (hy : y ∈ Ar) (hx0 : x ≠ 0) {ε c : NNReal} {N : ℕ} (hρε : ρ ≤ ε) (hεx : …) (hw1 : ε * Valued.v y ≤ c) (hmN : degAr … x ≤ N) (hw2 : ∀ n > N, ρⁿ|y_n| ≤ c) : ∀ n ≥ N, ρⁿ * |teichCoeffAr … (y - divStep … x y * x) n| ≤ c`
- **What**: **The descent step of Kedlaya Lemma 2.8**: after one division step, *every* coordinate term from index `N` on — including index `N` itself — is below the threshold `c`. That inclusion of `N` is what drives the strict descent of the top `ε`-index.
- **How**: Let `z = divStep x y` with coordinate sequence `zc` (identified by `teichCoeffAr_PhiHatK`). Three errors are chained. (i) `valued_mul_sub_PhiHatK_convF_le` bounds `v(z·x - Φ(convF zc x_•))` by `ρ·v(z)v(x) ≤ ρ·v y ≤ ε·v y ≤ c` (using `valued_divStep_le` and `hρε`, `hw1`). (ii) `valued_sub_sub_PhiHatK_le` applied to `y` and `Φ(convF …)` bounds `v((y - Φ conv) - Φ w) ≤ ρ·max(v y, v(Φ conv)) ≤ c`, where `w k := y_k - convF zc x_• k` and `v(Φ conv) ≤ v y` via `gaussTerm_convF_le` + `valued_PhiHatK`. Combining gives `v((y - z·x) - Φ w) ≤ c`. (iii) `digit_sub_le` transfers this to the *coordinates*: `ρⁿ|(y-zx)_n - (Φ w)_n| ≤ max(c, ρ·max(v(y-zx), v(Φ w))) ≤ c` using `valued_sub_divStep_mul_le`. Finally `gaussTerm_sub_convF_divStep_le` bounds `ρⁿ|w n| ≤ c` directly, and the ultrametric split `(y-zx)_n = ((y-zx)_n - (Φ w)_n) + w n` with `nnreal_mul_max` closes it.
- **Hypotheses**: `x, y ∈ A^r`; `x ≠ 0`; `ρ ≤ ε`; the `ε`-property of `x`; `ε·v y ≤ c`; `deg x ≤ N`; `y`'s coordinate terms below `c` past `N`.
- **Uses from project**: `degAr`, `divStep`, `hatK`, `ArSub`, `teichCoeffAr`, `perfectoidValuation`, `convF`, `PhiHatK`, `nnreal_mul_max`, `tendsto_div_shift`, `divStep_mem`, `teichCoeffAr_PhiHatK`, `tendsto_gaussTerm_teichCoeffAr`, `tendsto_convF`, `PhiHatK_mem_ArSub`, `valued_divStep_le`, `valued_mul_sub_PhiHatK_convF_le`, `gaussTerm_teichCoeffAr_le'`, `valued_PhiHatK`, `gaussTerm_convF_le`, `valued_sub_sub_PhiHatK_le`, `digit_sub_le`, `valued_sub_divStep_mul_le`, `gaussTerm_sub_convF_divStep_le`
- **Used by**: `division_descent`
- **Visibility**: public
- **Lines**: 1747–1894 (proof 1762–1894, 131 lines)
- **Notes**: proof >30 lines; the file's main assembly lemma — consumes almost every earlier estimate. Decomposition candidate.

### `theorem division_descent`
- **Type**: `… (hx : x ∈ Ar) (hx0 : x ≠ 0) {ε V : NNReal} (hρε : ρ ≤ ε) (hε1 : ε < 1) (hεx : …) : ∀ K : ℕ, ∀ y ∈ Ar, Valued.v y ≤ V → (∀ n > K, ρⁿ|y_n| ≤ ε * V) → ∃ z ∈ Ar, Valued.v (y - z*x) ≤ V ∧ (ε*V < Valued.v (y - z*x) → degAr … (y - z*x) < degAr … x)`
- **What**: **The division iteration** of Kedlaya Lemma 2.8: strong induction on the window size `K`, producing a quotient whose remainder has value `≤ V` and, unless already `ε·V`-small, degree strictly below `deg x`.
- **How**: `Nat.strong_induction_on` on `K`. Base `K < deg x`: take `z = 0`; the attainment set of `y` is bounded by `K` (any attaining index `> K` would contradict the window hypothesis), so `csSup_le` with `exists_valued_eq_teichCoeffAr` gives `deg y ≤ K < deg x`. Step: if `v y ≤ ε·V` take `z = 0` again. Otherwise apply `descent_step` with `c := ε·V`, `N := K` to get that all coordinates of `y' = y - divStep x y · x` from `K` on are `≤ ε·V`. If `K = 0` this makes *every* coordinate small, so `valued_eq_iSup_teichCoeffAr` + `ciSup_le` gives `v y' ≤ ε·V` and the degree obligation is vacuous. If `K > 0`, the window has shrunk to `K - 1`, so the IH applies to `y'` (`sub_mem`/`mul_mem`/`divStep_mem` for membership, `valued_sub_divStep_mul_le` for the value), and the quotients add: `y - (divStep x y + z')·x = y' - z'·x` by `ring`.
- **Hypotheses**: `x ∈ A^r`, `x ≠ 0`; `ρ ≤ ε < 1`; the `ε`-property of `x` past `deg x`; per-call: `y ∈ A^r`, `v y ≤ V`, and the coordinate window hypothesis past `K`.
- **Uses from project**: `degAr`, `divStep`, `hatK`, `ArSub`, `teichCoeffAr`, `perfectoidValuation`, `exists_valued_eq_teichCoeffAr`, `descent_step`, `divStep_mem`, `valued_sub_divStep_mul_le`, `valued_eq_iSup_teichCoeffAr`
- **Used by**: `approx_division`
- **Visibility**: public
- **Lines**: 1896–1984 (proof 1914–1984, 69 lines)
- **Notes**: proof >30 lines; three inline case comments.

### `theorem approx_division`
- **Type**: `… (hx : x ∈ Ar) (hx0 : x ≠ 0) : ∃ ε, ρ ≤ ε ∧ ε < 1 ∧ ∀ y ∈ Ar, ∃ z ∈ Ar, Valued.v (y - z*x) ≤ Valued.v y ∧ (ε * Valued.v y < Valued.v (y - z*x) → degAr … (y - z*x) < degAr … x)`
- **What**: **Kedlaya Lemma 2.8 (approximate division)**: a single `ε ∈ [ρ,1)` works for *all* dividends `y` — the remainder never gains value and drops in degree unless it is already `ε·v(y)`-small.
- **How**: Take the `ε` produced by `exists_eps_terms_le` for `x`. For a given `y`: if `v y = 0` take `z = 0` (the degree obligation is vacuous since `ε·0 = 0`). Otherwise `tendsto_gaussTerm_teichCoeffAr` + `eventually_lt_const` gives a window `K` past which `ρⁿ|yₙ| < ε·v y`, so `division_descent` applies with `V := v y`.
- **Hypotheses**: `x ∈ A^r`, `x ≠ 0`; `0 < ρ < 1`.
- **Uses from project**: `degAr`, `hatK`, `ArSub`, `teichCoeffAr`, `perfectoidValuation`, `exists_eps_terms_le`, `tendsto_gaussTerm_teichCoeffAr`, `division_descent`
- **Used by**: `exact_division`
- **Visibility**: public
- **Lines**: 1986–2012 (proof 1997–2012, 14 lines)
- **Notes**: proof >10 lines.

### `theorem tendsto_of_valued_sub_le`
- **Type**: `… {g : ℕ → hatK p F hρ0 hρ1} {y : hatK …} {f : ℕ → NNReal} (hle : ∀ i, Valued.v (g i - y) ≤ f i) (hf : Tendsto f atTop (nhds 0)) : Tendsto g atTop (nhds y)`
- **What**: A convergence criterion: if the deviations of `g` from `y` are dominated by a null sequence, then `g → y`.
- **How**: `g` is Cauchy by `cauchySeq_of_valued_le` (the ultrametric `Valuation.map_sub` bounds `v(g m - g n)` by `max (f m) (f n)`, both eventually `< ε`), so it converges to some `L` by `cauchySeq_tendsto_of_complete`. Then `L = y`: otherwise `v(L - y) > 0` and, choosing `i` with both `v(L - g i) < v(L-y)/2` (`eventually_valued_sub_le_of_tendsto`) and `f i < v(L-y)/2`, the split `L - y = (L - g i) + (g i - y)` gives `v(L-y) ≤ v(L-y)/2`, contradicting `NNReal.half_lt_self`.
- **Hypotheses**: pointwise domination by a null sequence; completeness of `hatK` (used via `cauchySeq_tendsto_of_complete`).
- **Uses from project**: `hatK`, `cauchySeq_of_valued_le`, `eventually_valued_sub_le_of_tendsto`
- **Used by**: `exact_division`
- **Visibility**: public
- **Lines**: 2014–2049 (proof 2019–2049, 30 lines)
- **Notes**: proof ~30 lines.

### `theorem exact_division`
- **Type**: `… (hx : x ∈ Ar) (hx0 : x ≠ 0) {y : hatK …} (hy : y ∈ Ar) : ∃ z ∈ Ar, Valued.v (y - z*x) ≤ Valued.v y ∧ (y - z*x = 0 ∨ degAr … (y - z*x) < degAr … x)`
- **What**: **Kedlaya Proposition 2.9 (exact division)**: division in `A^r` by a nonzero element leaves a remainder that is either exactly `0` or of degree strictly below the divisor.
- **How**: Iterate the `approx_division` quotient: `step` is a self-map of the subtype `{u // u ∈ A^r}` that stops once the degree has dropped and otherwise subtracts `(choose)·x`; `seq l := step^[l] y`. Two invariants are proved by induction: `v(seq l) ≤ v y`, and `(y - seq l)/x ∈ A^r`. *Dichotomy*: if some iterate's degree drops (`hdrop`), the accumulated quotient `(y - seq l)/x` works directly (`div_mul_cancel₀`). Otherwise no iterate ever drops, so the approximate-division dichotomy forces geometric shrinking `v(seq l) ≤ εˡ·v y` (by contradiction on the degree branch); then `Z l := (y - seq l)/x` satisfies `v(Z l · x - y) ≤ εˡ v y → 0`, so `tendsto_of_valued_sub_le` gives `Z l · x → y`, hence `Z l → y/x` (multiply by `x⁻¹`, `tendsto_pow_atTop_nhds_zero_of_lt_one` for `εˡ → 0`). Since `A^r` is by definition the *closure* of the image of `AlocToHatK` it is closed (`isClosed_closure`), so `IsClosed.mem_of_tendsto` puts `y/x ∈ A^r` and the remainder is exactly `0`.
- **Hypotheses**: `x, y ∈ A^r`, `x ≠ 0`; `0 < ρ < 1`; completeness of `hatK` and closedness of `A^r`.
- **Uses from project**: `degAr`, `hatK`, `ArSub`, `AlocToHatK`, `approx_division`, `tendsto_of_valued_sub_le`
- **Used by**: `isPrincipalIdealRing_ArSub` (and, outside the file, `Groebner.lean`)
- **Visibility**: public
- **Lines**: 2051–2175 (proof 2061–2175, 114 lines)
- **Notes**: proof >30 lines; uses `Exists.choose`/`choose_spec` on the `approx_division` witness and `Function.iterate_succ_apply'`. Decomposition candidate.

### `theorem isPrincipalIdealRing_ArSub`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : IsPrincipalIdealRing ↥(ArSub p F ϖ hρ0 hρ1)`
- **What**: **Kedlaya Corollary 2.10**: `A^r` is a principal ideal ring (the ring-theoretic payoff of the Euclidean algorithm).
- **How**: Given a nonzero ideal `I`, `Submodule.exists_mem_ne_zero_of_ne_bot` provides a nonzero element, so the degree set `S = {deg b | b ∈ I, b ≠ 0}` is nonempty and `Nat.sInf_mem` yields a minimal-degree generator `x₀`. For `y ∈ I`, `exact_division` gives `z` with remainder `w = y - z·x₀ ∈ I`; if `w = 0` then `y ∈ span {x₀}` (`Ideal.mem_span_singleton`), otherwise `deg w < deg x₀ = sInf S` contradicts `Nat.sInf_le`. The reverse inclusion `span {x₀} ≤ I` is `Ideal.span_le` + membership.
- **Hypotheses**: `0 < ρ < 1`; implicitly `x₀ ≠ 0` as an element of `hatK` (deduced from `x₀ ≠ 0` in the subring via `Subtype.ext`).
- **Uses from project**: `degAr`, `hatK`, `ArSub`, `exact_division`
- **Used by**: unused in file (and unused elsewhere in the project — the terminal result of the file)
- **Visibility**: public
- **Lines**: 2177–2220 (proof 2181–2220, 39 lines)
- **Notes**: proof >30 lines. States `IsPrincipalIdealRing` rather than `EuclideanDomain`/PID; the module docstring advertises "Euclidean domain, hence a PID", so the `EuclideanDomain` instance is not (yet) formalised.

---

### File Summary
- **Total declarations**: 40 (4 defs, 36 lemmas/theorems, 0 instances, 0 structures/classes/abbrevs)
  - defs: `degAr`, `convF`, `convPartialAloc`, `divStep`
- **Key API (used by 3+ others in this file)**:
  - `degAr` (14 in-file consumers + `Groebner.lean`)
  - `convF` (8)
  - `gaussTerm_teichCoeffAr_le'` (8)
  - `divStep` (5)
  - `degAr_spec` (4)
  - `tendsto_convF` (4)
  - `divStep_mem` (3, via `descent_step`/`division_descent`)
  - `tendsto_div_shift` (3)
  - `gaussValueF_zero` (3)
  - `gaussTerm_lt_of_degAr_lt`, `gaussTerm_convF_le`, `gaussValueF_teichmuller_sub_sub_le`, `bddAbove_range_of_tendsto_zero`, `gaussValueF_map_le_of_coeff_zero`, `exists_attaining_coeff`, `alocToWittF_convPartialAloc`, `valued_mul_sub_PhiHatK_convF_le`, `valued_divStep_le`, `valued_sub_divStep_mul_le`, `digit_sub_le` (2 each)
- **Unused declarations**: `degAr_mul` (Kedlaya Lemma 2.6 — stated, proved, never consumed here or anywhere in the project), `isPrincipalIdealRing_ArSub` (terminal result, no consumer yet). Every other declaration has at least one in-file consumer; `degAr`, `exact_division` and `degAr_eq_of_valued_sub_lt` additionally feed `FarguesFontaine/Groebner.lean`.
- **Declarations with sorry**: none — the file is completely sorry-free.
- **Declarations with set_option**: none — no heartbeat or recursion-depth bumps anywhere in the file.
- **Proofs >30 lines**:
  - `valued_degAr_PhiHatK_convF` — 155
  - `digit_sub_le` — 144
  - `gaussTerm_sub_convF_divStep_le` — 135
  - `valued_mul_sub_PhiHatK_convF_le` — 134
  - `valued_sub_sub_PhiHatK_le` — 132
  - `descent_step` — 131
  - `exact_division` — 114
  - `gaussValueF_prefix_mul_sub_convPartial_le` — 80
  - `gaussValueF_teichmuller_add_sub_le` — 77
  - `degAr_eq_of_valued_sub_lt` — 77
  - `gaussValueF_teichmuller_sub_sub_le` — 76
  - `division_descent` — 69
  - `gaussValueF_convPartial_sub_prefix_le` — 66
  - `gaussValueF_teichmuller_sum_sub_le` — 53
  - `tendsto_antidiagonal_sup_zero` — 45
  - `isPrincipalIdealRing_ArSub` — 39
  - `exists_eps_terms_le` — 38
  - `tendsto_convF` — 32
  - `tendsto_of_valued_sub_le` — 30
- **Duplication hot spots** (cleanup candidates, no action taken):
  - `gaussValueF_teichmuller_add_sub_le` vs `gaussValueF_teichmuller_sub_sub_le` — same 76-line scaling proof with `+`/`-` swapped.
  - `digit_sub_le` (lines 612–665) vs `valued_sub_sub_PhiHatK_le` (lines 1495–1548) — the `hPNval` prefix-error computation appears twice verbatim.
  - The "`ρⁿ = ρ^{k₀}ρ^{n-k₀}` at the max-attaining antidiagonal index" calc block appears five times (`tendsto_convF`, `gaussValueF_convPartial_sub_prefix_le`, `gaussTerm_convF_le`, `valued_mul_sub_PhiHatK_convF_le`, `valued_degAr_PhiHatK_convF` ×3).
  - `bddAbove_range_of_tendsto_zero` duplicates the internal `hbdd` helper of `tendsto_antidiagonal_sup_zero`.
  - `tendsto_antidiagonal_sup_zero` and `bddAbove_range_of_tendsto_zero` are project-independent `NNReal`/filter facts (mathlib-able candidates).
