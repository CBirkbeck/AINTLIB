# Inventory: `NumberFieldEulerProduct.lean`

Path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/Chebotarev/CebotarevDensity/NumberFieldEulerProduct.lean`

Namespace `Chebotarev`, section `NumberFieldEulerProduct`. Variable `(L : Type*) [Field L] [NumberField L]` throughout. The file builds generic analytic number-field Euler-product infrastructure for the Dedekind zeta function `ζ_K(s) = Σ_𝔞 N𝔞^{-s} = ∏_𝔭 (1 - N𝔭^{-s})^{-1}`. Module is `@[expose] public`. Originally from `flt-regular-bernoulli`; depends only on mathlib.

---

### `instance instFintypeSym`
- **Type**: `(α : Type*) [Finite α] (n : ℕ) : Fintype (Sym α n)`
- **What**: Provides a `Fintype` instance for the `n`-th symmetric power `Sym α n` whenever `α` is finite.
- **How**: `Fintype.ofFinite (Sym α n)` — converts the existing `Finite` instance to `Fintype`.
- **Hypotheses**: `α` finite.
- **Uses from project**: []
- **Used by**: unused in file (instance, resolved by typeclass search; supports `summable_tsum_symGeometric`)
- **Visibility**: public (noncomputable instance, declared before `namespace Chebotarev`)
- **Lines**: 35–37 (proof 1 line)
- **Notes**: none

### `abbrev NonzeroIdeal`
- **Type**: `NonzeroIdeal : Type _ := {I : Ideal (𝓞 L) // I ≠ ⊥}`
- **What**: The type of nonzero integral ideals of the ring of integers `𝓞 L`.
- **How**: Subtype definition.
- **Hypotheses**: none beyond the section variables.
- **Uses from project**: []
- **Used by**: `idealNormMultiplicity`, `dedekindZeta_eq_tsum_idealNormMultiplicity`, `sum_idealNormMultiplicity_isBigO`, `instFiniteAbsNormFiber`, `tsum_absNormFiber`, `hasSum_nonzeroIdeal_absNorm_cpow`, `primeFactorsOf`, `mem_primeFactorsOf`, `prod_primePow_count_eq`, `weight_prod_primePow` (and weighted-Euler lemmas), `weighted_prod_eulerFactor_eq_tsum`, `weighted_eulerProduct_eq_tsum`
- **Visibility**: public
- **Lines**: 45 (single line)
- **Notes**: none

### `def idealNormMultiplicity`
- **Type**: `(n : ℕ) : ℕ := Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 = n}`
- **What**: Counts the number of nonzero ideals of `𝓞 L` whose absolute norm equals `n`.
- **How**: `Nat.card` of the subtype of nonzero ideals with `absNorm = n`.
- **Hypotheses**: none.
- **Uses from project**: [`NonzeroIdeal`]
- **Used by**: `idealNormMultiplicity_zero`, `idealNormMultiplicity_one`, `idealNormMultiplicity_mul`, `dedekindZeta_eq_tsum_idealNormMultiplicity`, `sum_idealNormMultiplicity_isBigO`, `summable_idealNormMultiplicity_mul_cpow_neg`, `dedekindZeta_eq_tprod_primePowerSeries`, `tsum_absNormFiber`, `hasSum_nonzeroIdeal_absNorm_cpow`, `dedekindZeta_re_pos_of_one_lt`
- **Visibility**: public (noncomputable)
- **Lines**: 47–48 (single line)
- **Notes**: none

### `lemma idealNormMultiplicity_zero`
- **Type**: `idealNormMultiplicity L 0 = 0`
- **What**: No nonzero ideal has norm `0`, so the multiplicity at `0` is `0`.
- **How**: `Nat.card_eq_zero`; the counted subtype is empty since `Ideal.absNorm_eq_zero_iff` forces `I = ⊥`, contradicting `I ≠ ⊥`.
- **Hypotheses**: none.
- **Uses from project**: [`idealNormMultiplicity`]
- **Used by**: `idealNormMultiplicity_mul`
- **Visibility**: public
- **Lines**: 50–53 (proof 3 lines)
- **Notes**: none

### `lemma idealNormMultiplicity_one`
- **Type**: `idealNormMultiplicity L 1 = 1`
- **What**: Exactly one nonzero ideal (the unit ideal `⊤`) has norm `1`.
- **How**: Builds a `Unique` instance on the fiber (default `⊤` via `Ideal.absNorm_top`, uniqueness via `Ideal.absNorm_eq_one_iff`), then `Nat.card_unique`.
- **Hypotheses**: none.
- **Uses from project**: [`idealNormMultiplicity`]
- **Used by**: `idealNormMultiplicity_mul`, `dedekindZeta_eq_tprod_primePowerSeries`, `dedekindZeta_re_pos_of_one_lt`
- **Visibility**: public
- **Lines**: 55–61 (proof 6 lines)
- **Notes**: none

### `lemma span_natCast_sup_span_natCast`
- **Type**: `{m n : ℕ} (hcop : Nat.Coprime m n) : Ideal.span {(m : 𝓞 L)} ⊔ Ideal.span {(n : 𝓞 L)} = ⊤`
- **What**: For coprime naturals `m, n`, the ideals they generate in `𝓞 L` are comaximal (their sup is everything).
- **How**: `Ideal.isCoprime_iff_sup_eq` + `Ideal.isCoprime_span_singleton_iff`, transporting coprimality of `m, n` along `algebraMap ℤ (𝓞 L)` via `Nat.Coprime.isCoprime`.
- **Hypotheses**: `m, n` coprime; `NumberField L` omitted (`omit`).
- **Uses from project**: []
- **Used by**: `sup_span_mul_sup_span`, `mul_sup_span_natCast_left`
- **Visibility**: private
- **Lines**: 63–67 (proof 2 lines)
- **Notes**: none

### `lemma sup_span_mul_sup_span`
- **Type**: `{m n : ℕ} (hcop : Nat.Coprime m n) (I : Ideal (𝓞 L)) : (I ⊔ span{m}) * (I ⊔ span{n}) = I ⊔ span{m*n}`
- **What**: For coprime `m, n`, the product of `I ⊔ ⟨m⟩` and `I ⊔ ⟨n⟩` equals `I ⊔ ⟨mn⟩` (a CRT-style ideal factorization identity).
- **How**: Distributes `Ideal.sup_mul`/`Ideal.mul_sup`, uses `Ideal.span_singleton_mul_span_singleton`, rearranges via `ac_rfl`, and collapses the cross term using `span_natCast_sup_span_natCast`.
- **Hypotheses**: `m, n` coprime; `NumberField L` omitted.
- **Uses from project**: [`span_natCast_sup_span_natCast`]
- **Used by**: `absNorm_sup_span_natCast`, `idealNormMultiplicity_mul`
- **Visibility**: private
- **Lines**: 69–84 (proof ~12 lines)
- **Notes**: long-ish; hinges on `span_natCast_sup_span_natCast` and `Ideal.span_singleton_mul_span_singleton`. none

### `lemma span_natCast_le_of_absNorm_eq`
- **Type**: `{I : Ideal (𝓞 L)} {k : ℕ} (hI : Ideal.absNorm I = k) : Ideal.span {(k : 𝓞 L)} ≤ I`
- **What**: If `I` has norm `k`, then the principal ideal generated by `k` is contained in `I` (since `k = N(I) ∈ I`).
- **How**: `Ideal.span_le` reduces to membership; `Ideal.absNorm_mem` gives `N(I) ∈ I`, cast through `hI`.
- **Hypotheses**: `absNorm I = k`.
- **Uses from project**: []
- **Used by**: `mul_sup_span_natCast_left`
- **Visibility**: private
- **Lines**: 86–89 (proof 2 lines)
- **Notes**: none

### `lemma absNorm_sup_span_natCast`
- **Type**: `{m n : ℕ} (hcop) (hm : 0 < m) (hn : 0 < n) (I) (hI : absNorm I = m*n) : absNorm (I ⊔ ⟨m⟩) = m ∧ absNorm (I ⊔ ⟨n⟩) = n`
- **What**: For coprime positive `m, n` and `I` of norm `mn`, the two ideals `I ⊔ ⟨m⟩` and `I ⊔ ⟨n⟩` have norms exactly `m` and `n`.
- **How**: Their product is `I` (via `sup_span_mul_sup_span` + `absNorm_mem`), so `a·b = mn`; divisibility (`a ∣ m`, `b ∣ n`) follows from `Ideal.absNorm_dvd_absNorm_of_le` and coprimality `Nat.Coprime.pow_left ... .coprime_dvd_left`; `nlinarith` closes the equalities.
- **Hypotheses**: `m, n` coprime and positive; `absNorm I = m*n`.
- **Uses from project**: [`sup_span_mul_sup_span`]
- **Used by**: `idealNormMultiplicity_mul`
- **Visibility**: private
- **Lines**: 91–114 (proof ~22 lines)
- **Notes**: `long (30–50)`? No — proof is ~22 lines, under 30. Hinges on `Ideal.absNorm_dvd_absNorm_of_le`, `Ideal.absNorm_span_natCast`, `Nat.Coprime.coprime_dvd_left`. none

### `lemma mul_sup_span_natCast_left`
- **Type**: `{m n : ℕ} (hcop) (J L' : Ideal (𝓞 L)) (hJ : absNorm J = m) (hL : absNorm L' = n) : J * L' ⊔ ⟨m⟩ = J`
- **What**: For coprime `m, n` with `N J = m`, `N L' = n`, recovers `J` from the product `J·L'` by joining with `⟨m⟩` (CRT recovery of one factor).
- **How**: Shows `⟨m⟩ ⊔ L' = ⊤` (using `span_natCast_sup_span_natCast` and `span_natCast_le_of_absNorm_eq L hL`), then a `calc` chain: `J = J·⊤ = J·(⟨m⟩ ⊔ L') = ...` bounded above by `J·L' ⊔ ⟨m⟩` and below via `Ideal.mul_le_left/right`.
- **Hypotheses**: `m, n` coprime; `N J = m`, `N L' = n`.
- **Uses from project**: [`span_natCast_sup_span_natCast`, `span_natCast_le_of_absNorm_eq`]
- **Used by**: `idealNormMultiplicity_mul`
- **Visibility**: private
- **Lines**: 116–130 (proof ~13 lines)
- **Notes**: hinges on `span_natCast_sup_span_natCast`, `span_natCast_le_of_absNorm_eq`. none

### `lemma idealNormMultiplicity_mul`
- **Type**: `{m n : ℕ} (hcop : Nat.Coprime m n) : idealNormMultiplicity L (m*n) = idealNormMultiplicity L m * idealNormMultiplicity L n`
- **What**: The ideal-norm multiplicity is multiplicative on coprime arguments (CRT for ideals).
- **What math**: Number of norm-`mn` ideals = (number of norm-`m`) × (number of norm-`n`).
- **How**: Handles zero/one edge cases via `idealNormMultiplicity_zero/one`. Main case builds an explicit `Equiv` `{N = mn} ≃ {N = m} × {N = n}` with `fwd : I ↦ (I⊔⟨m⟩, I⊔⟨n⟩)` and `bwd : (J,L') ↦ J·L'`, whose inverse laws are `sup_span_mul_sup_span`, `mul_sup_span_natCast_left`, and `absNorm_sup_span_natCast`; then `Nat.card_congr` + `Nat.card_prod`.
- **Hypotheses**: `m, n` coprime.
- **Uses from project**: [`idealNormMultiplicity`, `idealNormMultiplicity_zero`, `idealNormMultiplicity_one`, `sup_span_mul_sup_span`, `mul_sup_span_natCast_left`, `absNorm_sup_span_natCast`]
- **Used by**: `dedekindZeta_eq_tprod_primePowerSeries`
- **Visibility**: public
- **Lines**: 132–191 (proof ~58 lines)
- **Notes**: `OVER-50 — needs further /decompose-proof pass` (proof ~58 lines; the `fwd`/`bwd`/`h_equiv` block is the bulk and could be extracted). `classical` used.

### `lemma dedekindZeta_eq_tsum_idealNormMultiplicity`
- **Type**: `{s : ℂ} (hs : 1 < s.re) : NumberField.dedekindZeta L s = ∑' n : ℕ, (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)`
- **What**: Rewrites the Dedekind zeta function as a Dirichlet series `Σ_n (a_n) n^{-s}` with `a_n =` ideal-norm multiplicity.
- **How**: Unfolds `dedekindZeta`/`LSeries`/`LSeries.term`; for `n = 0` uses `Complex.zero_cpow`; for `n > 0` rewrites `cpow_neg` and identifies the coefficient via a `Nat.card_congr` between `{Ideal // absNorm = n}` and the nonzero-ideal fiber.
- **Hypotheses**: `1 < Re s`.
- **Uses from project**: [`idealNormMultiplicity`, `idealNormMultiplicity_zero`, `NonzeroIdeal`]
- **Used by**: `dedekindZeta_eq_tprod_primePowerSeries`, `hasSum_nonzeroIdeal_absNorm_cpow`, `dedekindZeta_re_pos_of_one_lt`
- **Visibility**: public
- **Lines**: 193–216 (proof ~22 lines)
- **Notes**: hinges on `Nat.card_congr` and `LSeries.term` unfolding. none

### `lemma summable_tsum_symGeometric`
- **Type**: `(α : Type*) [Fintype α] {z : ℂ} (hz : ‖z‖ < 1) : Summable (fun n ↦ card(Sym α n) * z^n) ∧ ∑' n, card(Sym α n) * z^n = ((1-z)⁻¹)^card α`
- **What**: The symmetric-power generating function `Σ_n |Sym α n| z^n` is summable and sums to `(1-z)^{-|α|}` for `‖z‖ < 1`.
- **How**: Splits on `card α = 0` (support is `{0}`, via `Sym.card_sym_eq_multichoose` + `Nat.multichoose_zero_succ`) vs `card α = k+1` (rewrites `Sym.card_sym_eq_choose` to `(n+k).choose k`, applies `summable_choose_mul_geometric_of_norm_lt_one` and `tsum_choose_mul_geometric_of_norm_lt_one`).
- **Hypotheses**: `α` finite (`Fintype`); `‖z‖ < 1`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 218–240 (proof ~22 lines)
- **Notes**: hinges on mathlib `tsum_choose_mul_geometric_of_norm_lt_one`, `Sym.card_sym_eq_choose`. Unused in file (likely consumed by sibling files / prime-power factor analysis). none

### `lemma sum_idealNormMultiplicity_isBigO`
- **Type**: `(fun n ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity L k : ℝ)) =O[atTop] (fun n ↦ (n : ℝ) ^ (1 : ℝ))`
- **What**: The count of nonzero ideals with norm `≤ n` grows like `O(n)`.
- **How**: Identifies the partial sum with `Nat.card {I // absNorm I ≤ n}` via `Finset.card_preimage_eq_sum_card_image_eq` (fibers finite by `Ideal.finite_setOf_absNorm_eq`), bridges to ideals in `(Ideal (𝓞 L))⁰`, then applies `Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow` with `NumberField.Ideal.tendsto_norm_le_div_atTop₀` (the ideal-counting asymptotic).
- **Hypotheses**: none beyond section variables.
- **Uses from project**: [`idealNormMultiplicity`, `NonzeroIdeal`]
- **Used by**: `summable_idealNormMultiplicity_mul_cpow_neg`
- **Visibility**: public
- **Lines**: 245–280 (proof ~34 lines)
- **Notes**: `long (30–50)` (~34 lines). Hinges on `NumberField.Ideal.tendsto_norm_le_div_atTop₀`, `Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow`, `Finset.card_preimage_eq_sum_card_image_eq`. `classical` used.

### `lemma summable_idealNormMultiplicity_mul_cpow_neg`
- **Type**: `{s : ℂ} (hs : 1 < s.re) : Summable (fun n ↦ ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)‖)`
- **What**: The Dirichlet series coefficients of `ζ_K` are absolutely summable for `Re s > 1`.
- **How**: Gets `LSeriesSummable` from the `O(n)` partial-sum bound via `LSeriesSummable_of_sum_norm_bigO_and_nonneg` (using `sum_idealNormMultiplicity_isBigO`), rewrites `LSeries.term` to the explicit product, and takes `.norm`.
- **Hypotheses**: `1 < Re s`.
- **Uses from project**: [`idealNormMultiplicity`, `idealNormMultiplicity_zero`, `sum_idealNormMultiplicity_isBigO`]
- **Used by**: `dedekindZeta_eq_tprod_primePowerSeries`, `hasSum_nonzeroIdeal_absNorm_cpow`, `dedekindZeta_re_pos_of_one_lt`
- **Visibility**: public
- **Lines**: 282–299 (proof ~16 lines)
- **Notes**: hinges on mathlib `LSeriesSummable_of_sum_norm_bigO_and_nonneg`. `classical` used. none

### `lemma dedekindZeta_eq_tprod_primePowerSeries`
- **Type**: `{s : ℂ} (hs : 1 < s.re) : dedekindZeta L s = ∏' q : Nat.Primes, ∑' k : ℕ, (idealNormMultiplicity L (q^k) : ℂ) * ((q^k : ℕ) : ℂ) ^ (-s)`
- **What**: The Euler product of `ζ_K` over rational primes `q`, each factor being the local series in prime powers `q^k`.
- **How**: Defines `f n = a_n n^{-s}`, verifies `f 1 = 1` (`idealNormMultiplicity_one`), `f` is multiplicative on coprimes (`idealNormMultiplicity_mul`), `f 0 = 0`, norm-summable (`summable_idealNormMultiplicity_mul_cpow_neg`), then applies `EulerProduct.eulerProduct_tprod`.
- **Hypotheses**: `1 < Re s`.
- **Uses from project**: [`idealNormMultiplicity`, `idealNormMultiplicity_zero`, `idealNormMultiplicity_one`, `idealNormMultiplicity_mul`, `summable_idealNormMultiplicity_mul_cpow_neg`, `dedekindZeta_eq_tsum_idealNormMultiplicity`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 301–315 (proof ~14 lines)
- **Notes**: hinges on mathlib `EulerProduct.eulerProduct_tprod`. Unused in file (an exported endpoint). none

### `def insertPiEquiv`
- **Type**: `{ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι) (ha : a ∉ s) : ({i // i ∈ insert a s} → ℕ) ≃ ℕ × ({i // i ∈ s} → ℕ)`
- **What**: Re-indexes exponent vectors over `insert a s` as a pair `(value at a, restriction to s)`.
- **How**: Composes `Finset.subtypeInsertEquivOption` (`arrowCongr` refl) with `Equiv.piOptionEquivProd`.
- **Hypotheses**: `DecidableEq ι`, `a ∉ s`.
- **Uses from project**: []
- **Used by**: `insertPiEquiv_fst`, `insertPiEquiv_snd`, `prodInsertAttach`, `finsetGeometricProd_summable_and_hasSum`
- **Visibility**: private (noncomputable)
- **Lines**: 325–327 (proof 1 line)
- **Notes**: none

### `lemma insertPiEquiv_fst`
- **Type**: `(... e) : (insertPiEquiv a s ha e).1 = e ⟨a, Finset.mem_insert_self a s⟩`
- **What**: The first component of `insertPiEquiv e` is the exponent value at `a`.
- **How**: `rfl`.
- **Hypotheses**: as for `insertPiEquiv`.
- **Uses from project**: [`insertPiEquiv`]
- **Used by**: `prodInsertAttach`
- **Visibility**: private, `@[simp]`
- **Lines**: 329–331 (proof: rfl)
- **Notes**: none

### `lemma insertPiEquiv_snd`
- **Type**: `(... e) (i : {i // i ∈ s}) : (insertPiEquiv a s ha e).2 i = e ⟨i.1, Finset.mem_insert_of_mem i.2⟩`
- **What**: The second component of `insertPiEquiv e` is the restriction of `e` to `s`.
- **How**: `rfl`.
- **Hypotheses**: as for `insertPiEquiv`.
- **Uses from project**: [`insertPiEquiv`]
- **Used by**: `prodInsertAttach`
- **Visibility**: private, `@[simp]`
- **Lines**: 333–335 (proof: rfl)
- **Notes**: none

### `lemma prodInsertAttach`
- **Type**: `{ι} [DecidableEq ι] (g : ι → ℂ) (a : ι) (s : Finset ι) (ha : a ∉ s) (e) : ∏ i ∈ (insert a s).attach, g i.1 ^ e i = g a ^ (insertPiEquiv ...).1 * ∏ i ∈ s.attach, g i.1 ^ (insertPiEquiv ...).2 i`
- **What**: Splits a product over `insert a s` (indexed by exponents) into the factor at `a` times the product over `s`, re-indexed via `insertPiEquiv`.
- **How**: Uses `insertPiEquiv_fst/snd` to rewrite components, then `Finset.attach_insert`, `Finset.prod_insert`, `Finset.prod_image` (with injectivity of the attach embedding).
- **Hypotheses**: `DecidableEq ι`, `a ∉ s`.
- **Uses from project**: [`insertPiEquiv`, `insertPiEquiv_fst`, `insertPiEquiv_snd`]
- **Used by**: `finsetGeometricProd_summable_and_hasSum`
- **Visibility**: private
- **Lines**: 339–351 (proof ~10 lines)
- **Notes**: none

### `lemma finsetGeometricProd_summable_and_hasSum`
- **Type**: `{ι} (g : ι → ℂ) (hg : ∀ i, ‖g i‖ < 1) (s : Finset ι) : Summable (fun e : {i // i ∈ s} → ℕ ↦ ‖∏ i ∈ s.attach, g i.1 ^ e i‖) ∧ HasSum (fun e ↦ ∏ i ∈ s.attach, g i.1 ^ e i) (∏ i ∈ s, (1 - g i)⁻¹)`
- **What**: Combinatorial heart of the finite Euler-factor identity: for ratios with `‖g i‖ < 1`, the finite product of geometric series `∏(1-g i)⁻¹` equals the (norm-summable) `tsum` over exponent vectors of `∏ g i ^ e i`.
- **How**: `Finset.induction` on `s`. Empty case: product is `1`, support trivial. Insert case: combines the single geometric series (`hasSum_geometric_of_norm_lt_one`, `summable_geometric_of_lt_one`) with the IH via `HasSum.mul` / `Summable.mul_norm` / `summable_mul_of_summable_norm`, then transports along `insertPiEquiv` using `prodInsertAttach` and `Equiv.summable_iff`/`hasSum_iff`.
- **Hypotheses**: `‖g i‖ < 1` for all `i`.
- **Uses from project**: [`insertPiEquiv`, `prodInsertAttach`]
- **Used by**: `prod_eulerFactor_eq_tsum_exponentVector`, `weighted_prod_eulerFactor_eq_tsum`
- **Visibility**: private
- **Lines**: 366–422 (proof ~55 lines)
- **Notes**: `OVER-50 — needs further /decompose-proof pass` (proof ~55 lines; empty/insert branches each substantial). `classical` used. Hinges on `prodInsertAttach`, `HasSum.mul`, `summable_mul_of_summable_norm`.

### `lemma prod_natCast_cpow`
- **Type**: `{ι} (S : Finset ι) (m : ι → ℕ) (z : ℂ) : (∏ i ∈ S, (m i : ℂ) ^ z) = ((∏ i ∈ S, m i : ℕ) : ℂ) ^ z`
- **What**: A finite product of `cpow`s of natural casts equals the `cpow` of the product cast.
- **How**: `Finset.induction`; insert step uses `Complex.natCast_mul_natCast_cpow`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `prod_absNorm_cpow_eq_absNorm_prod_pow_cpow`
- **Visibility**: private
- **Lines**: 425–432 (proof ~5 lines)
- **Notes**: `classical` used. none

### `lemma norm_absNorm_cpow_neg_lt_one`
- **Type**: `{s : ℂ} (hs : 1 < s.re) (𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) : ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ < 1`
- **What**: For `Re s > 1`, a nonzero prime ideal's Euler ratio `N𝔭^{-s}` has norm `< 1` (since `N𝔭 ≥ 2`).
- **How**: `absNorm 𝔭 ≠ 0, ≠ 1` (so `≥ 2`) from `absNorm_eq_zero_iff` / `absNorm_eq_one_iff` + primality, then `Complex.norm_natCast_cpow_of_pos` and `Real.rpow_lt_one_of_one_lt_of_neg`.
- **Hypotheses**: `1 < Re s`; `𝔭` a nonzero prime ideal.
- **Uses from project**: []
- **Used by**: `prod_eulerFactor_eq_tsum_exponentVector`, `weighted_prod_eulerFactor_eq_tsum`
- **Visibility**: public
- **Lines**: 435–442 (proof ~6 lines)
- **Notes**: none

### `theorem prod_eulerFactor_eq_tsum_exponentVector`
- **Type**: `{s : ℂ} (hs : 1 < s.re) (S : Finset {𝔭 // IsPrime ∧ ≠⊥}) : (∏ 𝔭 ∈ S, (1 - (N𝔭)^{-s})⁻¹) = ∑' e : S →₀ ℕ, ∏ 𝔭 ∈ S.attach, (N𝔭)^{-(e 𝔭) * s}`
- **What**: Finite Euler-factor identity (Sharifi Prop. 7.1.9): the finite product of geometric Euler factors over primes in `S` equals the sum over exponent vectors of `∏ N𝔭^{-(e𝔭)s}`.
- **How**: Applies `finsetGeometricProd_summable_and_hasSum` to `g 𝔭 = N𝔭^{-s}` (norm `< 1` by `norm_absNorm_cpow_neg_lt_one`), re-indexes exponent functions to `Finsupp` via `Finsupp.equivFunOnFinite`, and rewrites `((N𝔭^{-s})^{e𝔭})` to `N𝔭^{-(e𝔭)s}` using `Complex.cpow_nat_mul`.
- **Hypotheses**: `1 < Re s`.
- **Uses from project**: [`finsetGeometricProd_summable_and_hasSum`, `norm_absNorm_cpow_neg_lt_one`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 448–467 (proof ~18 lines)
- **Notes**: `classical` used. Unused in file (exported endpoint; the weighted path supersedes it for `dedekindZeta_eq_tprod_primeIdeal`). none

### `theorem absNorm_prod_pow_of_primeIdeal`
- **Type**: `(S : Finset {𝔭 // IsPrime ∧ ≠⊥}) (e : S → ℕ) : Ideal.absNorm (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) = ∏ 𝔭 ∈ S.attach, Ideal.absNorm 𝔭.1.1 ^ e 𝔭`
- **What**: The norm of `∏_𝔭 𝔭^{e𝔭}` factors as `∏_𝔭 (N𝔭)^{e𝔭}` (multiplicativity of `absNorm` over the finite product).
- **How**: `map_prod` then `map_pow` of `Ideal.absNorm` factorwise.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `prod_absNorm_cpow_eq_absNorm_prod_pow_cpow`
- **Visibility**: public
- **Lines**: 470–475 (proof 2 lines)
- **Notes**: none

### `theorem prod_absNorm_cpow_eq_absNorm_prod_pow_cpow`
- **Type**: `{s : ℂ} (S : Finset {𝔭 // IsPrime ∧ ≠⊥}) (e : S → ℕ) : (∏ 𝔭 ∈ S.attach, (N𝔭)^{-(e𝔭)*s}) = (N(∏ 𝔭 ∈ S.attach, 𝔭^{e𝔭}))^{-s}`
- **What**: Identifies the product of Euler-summand factors `∏ N𝔭^{-(e𝔭)s}` with `(N(∏ 𝔭^{e𝔭}))^{-s}`.
- **How**: Rewrites each factor `N𝔭^{-(e𝔭)s} = (N𝔭^{e𝔭})^{-s}` via `Complex.natCast_cpow_natCast_mul`, applies `prod_natCast_cpow` and `absNorm_prod_pow_of_primeIdeal`.
- **Hypotheses**: none.
- **Uses from project**: [`prod_natCast_cpow`, `absNorm_prod_pow_of_primeIdeal`]
- **Used by**: `weighted_prod_eulerFactor_eq_tsum`
- **Visibility**: public
- **Lines**: 478–487 (proof ~7 lines)
- **Notes**: none

### `instance instFiniteAbsNormFiber`
- **Type**: `(n : ℕ) : Finite {I : NonzeroIdeal L // Ideal.absNorm I.1 = n}`
- **What**: The fiber of nonzero ideals of fixed norm `n` is finite.
- **How**: `Ideal.finite_setOf_absNorm_eq` gives finiteness for all ideals; restricts/injects to the nonzero subtype via `Set.Finite.of_finite_image` (injectivity of `I ↦ I.1`).
- **Hypotheses**: none.
- **Uses from project**: [`NonzeroIdeal`]
- **Used by**: unused in file (instance; supports `tsum_absNormFiber`, `hasSum_nonzeroIdeal_absNorm_cpow` via typeclass)
- **Visibility**: private (noncomputable instance)
- **Lines**: 500–504 (proof ~3 lines)
- **Notes**: none

### `lemma tsum_absNormFiber`
- **Type**: `{M} [AddCommGroup M] [TopologicalSpace M] [T2Space M] [IsTopologicalAddGroup M] (n : ℕ) (g : ℕ → M) : (∑' y : {I : NonzeroIdeal L // absNorm I.1 = n}, g (absNorm y.1.1)) = idealNormMultiplicity L n • g n`
- **What**: A `tsum` of a constant `g(absNorm) = g(n)` over the norm-`n` fiber equals `(multiplicity) • g n`.
- **How**: `tsum_congr` collapses `g(absNorm y) = g n` using `y.2`, then `tsum_const` over the finite fiber gives the `Nat.card`-scaled value (= `idealNormMultiplicity`).
- **Hypotheses**: `M` a Hausdorff topological abelian group.
- **Uses from project**: [`idealNormMultiplicity`, `NonzeroIdeal`]
- **Used by**: `hasSum_nonzeroIdeal_absNorm_cpow`
- **Visibility**: private
- **Lines**: 506–511 (proof ~3 lines)
- **Notes**: none

### `theorem hasSum_nonzeroIdeal_absNorm_cpow`
- **Type**: `{s : ℂ} (hs : 1 < s.re) : HasSum (fun I : NonzeroIdeal L ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s)) (NumberField.dedekindZeta L s)`
- **What**: For `Re s > 1`, the unconditional sum over nonzero ideals `Σ_𝔞 N𝔞^{-s}` converges to `ζ_K(s)`.
- **How**: Uses `Equiv.sigmaFiberEquiv` (sigma over norm fibers); `tsum_absNormFiber` gives per-fiber values/norms (= `a_n n^{-s}`); summability via `summable_sigma_of_nonneg` + `summable_idealNormMultiplicity_mul_cpow_neg`; then `tsum_sigma` and `dedekindZeta_eq_tsum_idealNormMultiplicity` to identify the sum with `ζ_K`.
- **Hypotheses**: `1 < Re s`.
- **Uses from project**: [`NonzeroIdeal`, `idealNormMultiplicity`, `tsum_absNormFiber`, `summable_idealNormMultiplicity_mul_cpow_neg`, `dedekindZeta_eq_tsum_idealNormMultiplicity`]
- **Used by**: `weighted_eulerProduct_eq_tsum`, `dedekindZeta_eq_tprod_primeIdeal`
- **Visibility**: public
- **Lines**: 514–540 (proof ~24 lines)
- **Notes**: hinges on `Equiv.sigmaFiberEquiv`, `Summable.tsum_sigma`, `tsum_absNormFiber`. `classical` used. none

### `theorem factorization_primePow_apply`
- **Type**: `(𝔭 𝔮 : {𝔭 // IsPrime ∧ ≠⊥}) (n : ℕ) : factorization (𝔭.1 ^ n) 𝔮.1 = if 𝔮 = 𝔭 then n else 0`
- **What**: The exponent of `𝔮` in the UFM factorization of `𝔭^n` is `n` if `𝔮 = 𝔭`, else `0`.
- **How**: `factorization_pow`, `factorization_eq_count`, `normalizedFactors_irreducible` (via `Ideal.prime_of_isPrime`), `Multiset.count_singleton`; case split.
- **Hypotheses**: `𝔭, 𝔮` nonzero primes.
- **Uses from project**: []
- **Used by**: `factorization_prod_primePow_eq`
- **Visibility**: private (`open UniqueFactorizationMonoid in`)
- **Lines**: 544–550 (proof ~4 lines)
- **Notes**: none

### `theorem factorization_prod_primePow_apply`
- **Type**: `(S : Finset {𝔭 // IsPrime ∧ ≠⊥}) (e : {𝔭 // ...} → ℕ) (𝔮) : factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭.1) 𝔮.1 = ∑ 𝔭 ∈ S.attach, factorization (𝔭.1.1 ^ e 𝔭.1) 𝔮.1`
- **What**: The exponent of `𝔮` in `∏_{𝔭∈S} 𝔭^{e𝔭}` is the sum of the exponents of `𝔮` in each factor.
- **How**: `Finset.induction`; insert step uses `factorization_mul` (factors nonzero via `pow_ne_zero`, `Finset.prod_ne_zero_iff`), `Finsupp.add_apply`, `Finset.prod_image`/`sum_image` with the attach-injectivity side goals.
- **Hypotheses**: none beyond the ambient nonzero-prime structure.
- **Uses from project**: []
- **Used by**: `factorization_prod_primePow_eq`
- **Visibility**: private (`open UniqueFactorizationMonoid in`)
- **Lines**: 554–572 (proof ~12 lines)
- **Notes**: `classical` used. none

### `theorem factorization_prod_primePow_eq`
- **Type**: `(S) (e) (𝔮) : factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭.1) 𝔮.1 = if 𝔮 ∈ S then e 𝔮 else 0`
- **What**: The exponent of `𝔮` in `∏_{𝔭∈S} 𝔭^{e𝔭}` is `e 𝔮` if `𝔮 ∈ S`, else `0`.
- **How**: Combines `factorization_prod_primePow_apply` + `factorization_primePow_apply`; case `𝔮 ∈ S` uses `Finset.sum_eq_single ⟨𝔮, h⟩`, case `𝔮 ∉ S` uses `Finset.sum_eq_zero`.
- **Hypotheses**: none.
- **Uses from project**: [`factorization_prod_primePow_apply`, `factorization_primePow_apply`]
- **Used by**: `factorization_idealOfExp_eq`
- **Visibility**: private (`open UniqueFactorizationMonoid in`)
- **Lines**: 576–592 (proof ~12 lines)
- **Notes**: `classical` used. none

### `def primeFactorsOf`
- **Type**: `(𝔞 : NonzeroIdeal L) : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}`
- **What**: The normalized prime factors of `𝔞`, as a `Finset` of nonzero prime ideals.
- **How**: `(normalizedFactors 𝔞.1).toFinset.attach.map` along an embedding promoting each normalized factor `p` to the subtype, using `Ideal.isPrime_of_prime` / `prime_of_normalized_factor` for the prime/nonzero proofs.
- **Hypotheses**: none.
- **Uses from project**: [`NonzeroIdeal`]
- **Used by**: `mem_primeFactorsOf`, `weighted_eulerProduct_eq_tsum`
- **Visibility**: private (noncomputable, `open UniqueFactorizationMonoid in`)
- **Lines**: 596–607 (definition ~11 lines, no proof body)
- **Notes**: none

### `theorem mem_primeFactorsOf`
- **Type**: `(𝔞 : NonzeroIdeal L) (p : Ideal (𝓞 L)) (hp : p ∈ normalizedFactors 𝔞.1) : ∃ 𝔭 ∈ primeFactorsOf L 𝔞, 𝔭.1 = p`
- **What**: Every normalized prime factor `p` of `𝔞` is realized by an element of `primeFactorsOf 𝔞`.
- **How**: Provides the witness `⟨p, ...⟩`; membership follows from `primeFactorsOf` / `Finset.mem_map` and `Multiset.mem_toFinset`.
- **Hypotheses**: `p ∈ normalizedFactors 𝔞.1`.
- **Uses from project**: [`primeFactorsOf`, `NonzeroIdeal`]
- **Used by**: `weighted_eulerProduct_eq_tsum`
- **Visibility**: private (`open UniqueFactorizationMonoid in`)
- **Lines**: 611–617 (proof ~5 lines)
- **Notes**: none

### `theorem factorization_idealOfExp_eq`
- **Type**: `(S : Finset {𝔭 // ...}) (f : S →₀ ℕ) (𝔮 : S) : factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ f 𝔭) 𝔮.1.1 = f 𝔮`
- **What**: For an exponent `Finsupp` `f` over `S`, the factorization exponent of `𝔮 ∈ S` in `∏ 𝔭^{f𝔭}` is exactly `f 𝔮`.
- **How**: Rewrites `f 𝔭` to the dite-extended exponent, applies `factorization_prod_primePow_eq`, then `if_pos`/`dif_pos` at `𝔮 ∈ S`.
- **Hypotheses**: `𝔮 ∈ S`.
- **Uses from project**: [`factorization_prod_primePow_eq`]
- **Used by**: `weighted_eulerProduct_eq_tsum` (proves `hinj`)
- **Visibility**: private (`open UniqueFactorizationMonoid in`)
- **Lines**: 620–628 (proof ~6 lines)
- **Notes**: `classical` used. none

### `theorem prod_primePow_count_eq`
- **Type**: `(S) (𝔞 : NonzeroIdeal L) (hsupp : ∀ p ∈ normalizedFactors 𝔞.1, ∃ 𝔭 ∈ S, 𝔭.1 = p) : (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ (normalizedFactors 𝔞.1).count 𝔭.1.1) = 𝔞.1`
- **What**: If every normalized factor of `𝔞` lies in `S`, then reconstructing the product `∏_{𝔭∈S} 𝔭^{count}` recovers `𝔞` exactly.
- **How**: Rewrites the attach-product to a product over `S.image (·.1)`, restricts to `normalizedFactors.toFinset` via `Finset.prod_subset` (factors outside have count `0`), then `finprod_pow_count_eq_of_subsingleton_units` / `finprod_eq_finsetProd_of_mulSupport_subset`.
- **Hypotheses**: all normalized factors of `𝔞` are in `S`.
- **Uses from project**: [`NonzeroIdeal`]
- **Used by**: `weighted_eulerProduct_eq_tsum` (proves `hmem`)
- **Visibility**: private (`open UniqueFactorizationMonoid in`)
- **Lines**: 631–655 (proof ~24 lines)
- **Notes**: hinges on `finprod_pow_count_eq_of_subsingleton_units`, `finprod_eq_finsetProd_of_mulSupport_subset`. `classical` used. none

### `theorem weight_prod_primePow`
- **Type**: `(w : Ideal (𝓞 L) → ℂ) (hw_one : w ⊤ = 1) (hw_mul : ∀ {𝔞 𝔟}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → w (𝔞*𝔟) = w 𝔞 * w 𝔟) (S) (e : S → ℕ) : w (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) = ∏ 𝔭 ∈ S.attach, (w 𝔭.1.1) ^ e 𝔭`
- **What**: A completely-multiplicative weight `w` is multiplicative over prime-power products: `w(∏𝔭^{e𝔭}) = ∏ w(𝔭)^{e𝔭}`.
- **How**: First `w(𝔭^k) = (w𝔭)^k` by induction on `k` (using `hw_mul`, `pow_ne_zero`); then induction over a generic `Finset T : Finset S` (`Finset.induction`) carrying `hw_mul` through `Finset.prod_insert`; instantiate at `S.attach`.
- **Hypotheses**: `w ⊤ = 1`; `w` multiplicative on nonzero ideals; `NumberField L` omitted.
- **Uses from project**: []
- **Used by**: `weighted_prod_eulerFactor_eq_tsum`
- **Visibility**: private (`omit [NumberField L]`)
- **Lines**: 670–689 (proof ~18 lines)
- **Notes**: `classical` used. none

### `theorem weighted_prod_eulerFactor_eq_tsum`
- **Type**: `{s} (hs : 1 < s.re) (w) (hw_one) (hw_mul) (hw_norm : ∀ 𝔞, ‖w 𝔞‖ ≤ 1) (S) (idealOfExp : (S →₀ ℕ) → NonzeroIdeal L) (hidealOfExp : ∀ e, (idealOfExp e).1 = ∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) (hinj) : (∏ 𝔭 ∈ S, (1 - w 𝔭.1 * (N𝔭)^{-s})⁻¹) = ∑' 𝔞 : Set.range idealOfExp, w 𝔞.1.1 * (N𝔞)^{-s}`
- **What**: Weighted finite Euler-factor identity: the finite product `∏_{𝔭∈S}(1 - w(𝔭)N𝔭^{-s})⁻¹` equals the weighted Dirichlet partial sum `Σ_𝔞 w(𝔞)N𝔞^{-s}` over `S`-factored ideals.
- **How**: Applies `finsetGeometricProd_summable_and_hasSum` to `g𝔭 = w(𝔭)N𝔭^{-s}` (norm `< 1` via `norm_absNorm_cpow_neg_lt_one` + `hw_norm`); identifies each summand with `w(idealOfExp e)·N(...)^{-s}` using `prod_absNorm_cpow_eq_absNorm_prod_pow_cpow` and `weight_prod_primePow`; transports via `Finsupp.equivFunOnFinite` and `tsum_range` (using injectivity `hinj`).
- **Hypotheses**: `1 < Re s`; `w` completely multiplicative with `‖w‖ ≤ 1`; `idealOfExp` an injective realization of exponent vectors as ideals.
- **Uses from project**: [`finsetGeometricProd_summable_and_hasSum`, `norm_absNorm_cpow_neg_lt_one`, `prod_absNorm_cpow_eq_absNorm_prod_pow_cpow`, `weight_prod_primePow`, `NonzeroIdeal`]
- **Used by**: `weighted_eulerProduct_eq_tsum`
- **Visibility**: private
- **Lines**: 694–735 (proof ~40 lines)
- **Notes**: `long (30–50)` (~40 lines). `classical` used. Hinges on `finsetGeometricProd_summable_and_hasSum`, `tsum_range`.

### `theorem weighted_eulerProduct_eq_tsum`
- **Type**: `{s} (hs : 1 < s.re) (w) (hw_one) (hw_mul) (hw_norm) : (∏' 𝔭 : {𝔭 // IsPrime ∧ ≠⊥}, (1 - w 𝔭.1 * (N𝔭)^{-s})⁻¹) = ∑' 𝔞 : NonzeroIdeal L, w 𝔞.1 * (N𝔞)^{-s}`
- **What**: Weighted prime-ideal Euler product (Sharifi 7.1.18): `∏_𝔭 (1 - w(𝔭)N𝔭^{-s})⁻¹ = Σ_𝔞 w(𝔞)N𝔞^{-s}` for a completely-multiplicative weight with `‖w‖ ≤ 1`.
- **How**: Sets up `idealOfExp S` and proves: summability `hnormD` (dominated by `hasSum_nonzeroIdeal_absNorm_cpow`); injectivity `hinj` (via `factorization_idealOfExp_eq`); surjectivity-onto-`S`-factored `hmem` (via `prod_primePow_count_eq`); the finite-`S` partial identity `hpartial` (via `weighted_prod_eulerFactor_eq_tsum`). The `S ↑ ⊤` limit (`HasProd` via `Metric.tendsto_atTop`) chooses `F` with small tail (`tendsto_tsum_compl_atTop_zero`) and `S ⊇ F.biUnion (primeFactorsOf)` capturing all of `F` (via `mem_primeFactorsOf`), bounding the residual by the tail using `tsum_subtype_add_tsum_subtype_compl` and `tsum_le_tsum_of_inj`.
- **Hypotheses**: `1 < Re s`; `w` completely multiplicative with `‖w‖ ≤ 1`.
- **Uses from project**: [`NonzeroIdeal`, `hasSum_nonzeroIdeal_absNorm_cpow`, `factorization_idealOfExp_eq`, `prod_primePow_count_eq`, `weighted_prod_eulerFactor_eq_tsum`, `primeFactorsOf`, `mem_primeFactorsOf`]
- **Used by**: `dedekindZeta_eq_tprod_primeIdeal`
- **Visibility**: public (`open UniqueFactorizationMonoid in`)
- **Lines**: 742–802 (proof ~60 lines)
- **Notes**: `OVER-50 — needs further /decompose-proof pass` (proof ~60 lines; the `hnormD`/`hinj`/`hmem`/`hpartial` setup and the `S↑⊤` limit are separable). `classical` used. Hinges on `tendsto_tsum_compl_atTop_zero`, `Summable.tsum_subtype_add_tsum_subtype_compl`, `prod_primePow_count_eq`.

### `theorem dedekindZeta_eq_tprod_primeIdeal`
- **Type**: `{s : ℂ} (hs : 1 < s.re) : NumberField.dedekindZeta L s = ∏' 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹`
- **What**: Prime-ideal Euler product (Sharifi Thm 7.1.12): `ζ_K(s) = ∏_𝔭 (1 - N𝔭^{-s})⁻¹` for `Re s > 1`.
- **How**: Specializes `weighted_eulerProduct_eq_tsum` to the trivial weight `w ≡ 1` (hypotheses by `simp`), simplifies `one_mul`, and identifies the RHS `tsum` with `ζ_K` via `hasSum_nonzeroIdeal_absNorm_cpow`.
- **Hypotheses**: `1 < Re s`.
- **Uses from project**: [`weighted_eulerProduct_eq_tsum`, `hasSum_nonzeroIdeal_absNorm_cpow`]
- **Used by**: unused in file
- **Visibility**: public (`open UniqueFactorizationMonoid in`)
- **Lines**: 807–813 (proof ~3 lines)
- **Notes**: top-level exported endpoint. none

### `theorem dedekindZeta_re_pos_of_one_lt`
- **Type**: `(s : ℝ) (hs : 1 < s) : 0 < (NumberField.dedekindZeta L (s : ℂ)).re`
- **What**: For real `s > 1`, `ζ_K(s)` is a positive real (Sharifi Def 7.1.11).
- **How**: Writes the coefficients as real `g n = a_n n^{-s}`, shows the complex term casts to `g n`; gets real summability from complex (`summable_idealNormMultiplicity_mul_cpow_neg` + `Complex.summable_ofReal`); rewrites `Re ζ_K = Σ g n` via `Complex.re_tsum` and `dedekindZeta_eq_tsum_idealNormMultiplicity`; then `Summable.tsum_pos` with the `n = 1` term positive (`idealNormMultiplicity_one`).
- **Hypotheses**: real `s > 1`.
- **Uses from project**: [`idealNormMultiplicity`, `summable_idealNormMultiplicity_mul_cpow_neg`, `dedekindZeta_eq_tsum_idealNormMultiplicity`, `idealNormMultiplicity_one`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 816–842 (proof ~26 lines)
- **Notes**: hinges on `Summable.tsum_pos`, `Complex.re_tsum`. none

---

## File Summary

**Total declarations: 36**
- **Defs / abbrevs: 4** — `NonzeroIdeal` (abbrev), `idealNormMultiplicity`, `insertPiEquiv`, `primeFactorsOf`
- **Lemmas + theorems: 30**
- **Instances: 2** — `instFintypeSym`, `instFiniteAbsNormFiber` (plus `instFintypeSym` is the only one outside the namespace)

**Key API (used by ≥ 3 in-file declarations):**
- `NonzeroIdeal` — used by ≥ 12 declarations (pervasive)
- `idealNormMultiplicity` — used by ≥ 10
- `idealNormMultiplicity_one` — used by 3 (`idealNormMultiplicity_mul`, `dedekindZeta_eq_tprod_primePowerSeries`, `dedekindZeta_re_pos_of_one_lt`)
- `dedekindZeta_eq_tsum_idealNormMultiplicity` — used by 3 (`dedekindZeta_eq_tprod_primePowerSeries`, `hasSum_nonzeroIdeal_absNorm_cpow`, `dedekindZeta_re_pos_of_one_lt`)
- `summable_idealNormMultiplicity_mul_cpow_neg` — used by 3 (`dedekindZeta_eq_tprod_primePowerSeries`, `hasSum_nonzeroIdeal_absNorm_cpow`, `dedekindZeta_re_pos_of_one_lt`)

**Unused-in-file declarations (exported endpoints or typeclass-resolved):** `instFintypeSym`, `summable_tsum_symGeometric`, `dedekindZeta_eq_tprod_primePowerSeries`, `prod_eulerFactor_eq_tsum_exponentVector`, `instFiniteAbsNormFiber`, `dedekindZeta_eq_tprod_primeIdeal`, `dedekindZeta_re_pos_of_one_lt`. (The latter four are the file's headline public results, consumed by sibling Chebotarev files.)

**Declarations with `sorry`:** none.

**Declarations with `set_option`:** none. (Module-level `@[expose] public section`, `noncomputable section`; `classical` is used locally in many proofs but no `set_option`.)

**Proofs > 50 lines (decompose-needed):**
- `idealNormMultiplicity_mul` — lines 132–191, proof ~58 lines
- `finsetGeometricProd_summable_and_hasSum` — lines 366–422, proof ~55 lines
- `weighted_eulerProduct_eq_tsum` — lines 742–802, proof ~60 lines

**Proofs 30–50 lines:**
- `sum_idealNormMultiplicity_isBigO` — lines 245–280, proof ~34 lines
- `weighted_prod_eulerFactor_eq_tsum` — lines 694–735, proof ~40 lines

(Borderline ~24-line proofs, under 30, not flagged: `dedekindZeta_eq_tsum_idealNormMultiplicity`, `hasSum_nonzeroIdeal_absNorm_cpow`, `prod_primePow_count_eq`, `dedekindZeta_re_pos_of_one_lt`, `absNorm_sup_span_natCast` ~22.)
