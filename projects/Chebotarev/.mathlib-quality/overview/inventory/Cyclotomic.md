# Inventory: `Cyclotomic.lean`

Path: `projects/Chebotarev/CebotarevDensity/Cyclotomic.lean` (1004 lines).
Namespace `Chebotarev`. Proves the **cyclotomic case of Chebotarev density** (`chebotarev_cyclotomic`): for `L = K(μ_m)`, the Dirichlet density of primes of `K` unramified in `L` with Frobenius `σ` is `1/|Gal(L/K)|`. File-wide `@[expose] public section`, `noncomputable section`. Shared `variable (K L) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]` (most decls re-bind these explicitly).

---

### `private theorem unramifiedPrime_toPrimeNeBot_injective`
- **Type**: `Function.Injective (fun 𝔭 : {𝔭 // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦ ⟨𝔭.1, …⟩ : {𝔭 // 𝔭 ∈ {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})`
- **What**: The reindexing map from the unramified-prime subtype into the `primeIdealZetaSum` index subtype is injective.
- **How**: `Subtype.ext` after `Subtype.mk_eq_mk.mp` on the hypothesis; the anonymous-constructor (non-`Equiv`) form keeps projections `rfl`.
- **Hypotheses**: none beyond `Field K`, `Field L`, `Algebra K L`, `IsGalois K L` (`NumberField` instances omitted).
- **Uses from project**: `UnramifiedIn`, `UnramifiedIn.ne_bot`.
- **Used by**: `log_artinLSeries_asymp_character_sum`, `summable_twistedPrimeSum`, `artinLSeries_prime_sum_bounded_of_analytic_extension` (via `hsummr`).
- **Visibility**: private
- **Lines**: 57–62 (proof 1 line)
- **Notes**: none

### `private theorem unramifiedPrime_toPrimeNeBot_surjective`
- **Type**: `Function.Surjective` of the same reindexing map as above.
- **What**: That reindexing map is surjective onto the `primeIdealZetaSum` index subtype.
- **How**: Construct the preimage `⟨𝔮.1, 𝔮.2.1.1, 𝔮.2.1.2⟩` and close with `Subtype.ext rfl`.
- **Hypotheses**: none beyond field/algebra/Galois (NumberField omitted).
- **Uses from project**: `UnramifiedIn` (in the type).
- **Used by**: `log_artinLSeries_asymp_character_sum` (via `range_eq`).
- **Visibility**: private
- **Lines**: 64–69 (proof 1 line)
- **Notes**: none

### `theorem log_artinLSeries_asymp_character_sum`
- **Type**: `[IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L) : ∃ C, ∀ᶠ s in 𝓝[>] 1, ‖∑' 𝔭, χ(Frob 𝔭) · N𝔭^(-s)‖ ≤ C · log(1/(s-1)) + C`
- **What**: Sharifi 7.2.1 step (ii): the twisted character prime sum over unramified primes is bounded above by `C·log(1/(s-1)) + C` near `s = 1`.
- **How**: `‖χ(c.out)‖ = 1` (root-of-unity, `Complex.norm_eq_one_of_pow_eq_one`), so each summand norm is `N𝔭^(-s)`; dominate by `primeIdealZetaSum` over univ via `primeIdealZetaSum_le_log_plus_bounded`, using `norm_tsum_le_tsum_norm` and `primeIdealZetaSum_le_of_subset`.
- **Hypotheses**: `K, L` number fields, `K`-Galois `L`, `Gal(L/K)` commutative; `χ` a Galois character.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `UnramifiedIn.ne_bot`, `primeIdealZetaSum_le_log_plus_bounded`, `summable_prime_absNorm_rpow`, `unramifiedPrime_toPrimeNeBot_injective`, `unramifiedPrime_toPrimeNeBot_surjective`, `primeIdealZetaSum_def`, `primeIdealZetaSum`, `primeIdealZetaSum_le_of_subset`.
- **Used by**: unused in file (no in-file caller).
- **Visibility**: public
- **Lines**: 96–159 (proof ~61 lines)
- **Notes**: OVER-50 — needs further /decompose-proof pass

### `private theorem sum_galoisCharacter_eq_card_or_zero`
- **Type**: `(G) [Group G] [IsMulCommutative G] [Finite G] [Fintype (G →* ℂˣ)] (g : G) : (∑ χ : G →* ℂˣ, χ g) = if g = 1 then Nat.card G else 0`
- **What**: Column orthogonality of the ℂˣ-valued characters of a finite commutative group: the sum of all characters at `g` is `|G|` if `g = 1`, else `0`.
- **How**: `split_ifs`; matching case uses `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity` (ℂ algebraically closed ⇒ `HasEnoughRootsOfUnity`); other case is `sum_char_apply_eq_zero_of_ne_one`.
- **Hypotheses**: `G` finite commutative group with a `Fintype` of ℂˣ-characters; `g ∈ G`.
- **Uses from project**: `sum_char_apply_eq_zero_of_ne_one` (from `ForMathlib.CharacterOrthogonality`).
- **Used by**: `sum_galoisCharacter_mul_inv_eq`.
- **Visibility**: private (`open scoped Classical in`)
- **Lines**: 166–177 (proof ~10 lines)
- **Notes**: none

### `private theorem sum_galoisCharacter_mul_inv_eq`
- **Type**: `[IsMulCommutative Gal(L/K)] [Fintype (galoisCharacter K L)] (σ τ) : (∑ χ, χ σ · (χ τ)⁻¹) = if σ·τ⁻¹ = 1 then Nat.card Gal(L/K) else 0`
- **What**: Two-argument character orthogonality: `∑_χ χ(σ)·χ(τ)⁻¹` is `|G|` if `σ = τ`, else `0`.
- **How**: Rewrite `χ(σ)·χ(τ)⁻¹ = χ(σ·τ⁻¹)` via `map_mul`/`map_inv`/`Units.val_inv_eq_inv_val`, then apply `sum_galoisCharacter_eq_card_or_zero`.
- **Hypotheses**: `Gal(L/K)` commutative with a `Fintype` of Galois characters; `σ, τ ∈ Gal(L/K)`.
- **Uses from project**: `galoisCharacter`, `sum_galoisCharacter_eq_card_or_zero`.
- **Used by**: `character_orthogonality_cyclotomic_eq`, `character_orthogonality_cyclotomic_ne`.
- **Visibility**: private (`open scoped Classical in`)
- **Lines**: 180–187 (proof ~3 lines)
- **Notes**: none

### `theorem character_orthogonality_cyclotomic_eq`
- **Type**: `(m) [NeZero m] [IsCyclotomicExtension {m} K L] [Fintype (galoisCharacter K L)] (σ) (𝔭) [𝔭.IsPrime] (hunr) (h : frobeniusClass K L 𝔭 = ConjClasses.mk σ) : (∑ χ, χ σ · (χ (Frob 𝔭).out)⁻¹) = Nat.card Gal(L/K)`
- **What**: Sharifi 7.2.1 step (iii), matching case: when `Frob 𝔭 = [σ]`, the orthogonality character sum equals `|G|`.
- **How**: Cyclotomic ⇒ `IsMulCommutative` (`IsCyclotomicExtension.isMulCommutative`); from `IsConj τ σ` and commutativity derive `σ·τ⁻¹ = 1`, then `sum_galoisCharacter_mul_inv_eq` with `if_pos`.
- **Hypotheses**: `L = K(μ_m)`; finitely many characters; `𝔭` prime unramified; Frobenius of `𝔭` equals the class of `σ`.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `sum_galoisCharacter_mul_inv_eq`.
- **Used by**: `sum_charTwist_eq`.
- **Visibility**: public
- **Lines**: 192–208 (proof ~9 lines)
- **Notes**: none

### `theorem character_orthogonality_cyclotomic_ne`
- **Type**: same shape as above but with `h : frobeniusClass K L 𝔭 ≠ ConjClasses.mk σ`, concluding the sum `= 0`.
- **What**: Sharifi 7.2.1 step (iii), non-matching case: when `Frob 𝔭 ≠ [σ]`, the orthogonality character sum vanishes.
- **How**: Derive `σ·τ⁻¹ ≠ 1` from `h` (`mul_inv_eq_one`), then `sum_galoisCharacter_mul_inv_eq` with `if_neg`.
- **Hypotheses**: as above but Frobenius of `𝔭` not equal to the class of `σ`.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `sum_galoisCharacter_mul_inv_eq`.
- **Used by**: `sum_charTwist_ne`.
- **Visibility**: public
- **Lines**: 213–225 (proof ~6 lines)
- **Notes**: none

### `private theorem differentiableAt_logSum_of_two_le`
- **Type**: `{ι} (N : ι → ℕ) (c : ι → ℂ) (s₀) (hs₀ : 1 < s₀) (hN : ∀ i, 2 ≤ N i) (hc : ∀ i, ‖c i‖ = 1) (hsummr) : DifferentiableAt ℝ (fun s ↦ ∑' i, -Complex.log (1 - c i · N i^(-s))) s₀`
- **What**: The abstract log sum `g(s) = Σ_i -Log(1 - c_i N_i^{-s})` is real-differentiable at any `s₀ > 1`.
- **How**: Apply `hasDerivAt_tsum_of_isPreconnected` on `t = Ioi (1 + ε)`; per-term derivative via `Complex.hasStrictDerivAt_const_cpow` + `HasDerivAt.clog` (1 - w in `slitPlane` since `‖w‖ ≤ 1/2`); uniform bound `u i = 2 log(N i)·N i^{-(1+ε)}` summable via `Real.log_le_rpow_div`.
- **Hypotheses**: norm-base `N i ≥ 2`, unit coefficients `‖c i‖ = 1`, summability of `i ↦ N i^{-r}` for all `r > 1`; `s₀ > 1`.
- **Uses from project**: `[]`
- **Used by**: `norm_logSum_bounded_nhdsGT_aux`.
- **Visibility**: private
- **Lines**: 236–340 (proof ~103 lines)
- **Notes**: OVER-50 — needs further /decompose-proof pass

### `private theorem cexp_logSum_eq_tprod`
- **Type**: `{ι} (w : ι → ℂ) (hsumw : Summable w) (hslit : ∀ i, (1 - w i) ∈ slitPlane) : Complex.exp (∑' i, -Complex.log (1 - w i)) = ∏' i, (1 - w i)⁻¹`
- **What**: `exp(g(s)) = ∏_i (1 - w_i)⁻¹` for the log sum, the Euler-product identity in exponential form.
- **How**: `Complex.cexp_tsum_eq_tprod` after rewriting `log(f i) = -log(1 - w i)` (`Complex.log_inv`, `slitPlane_arg_ne_pi`) and establishing summability of the logs (`Summable.clog_one_sub`).
- **Hypotheses**: weights `w` summable; each `1 - w i` in the slit plane.
- **Uses from project**: `[]`
- **Used by**: `artinLSeries_prime_sum_bounded_of_analytic_extension` (via `hexpeq`).
- **Visibility**: private
- **Lines**: 344–354 (proof ~9 lines)
- **Notes**: none

### `private theorem hasDerivAt_logSum_eq_logDeriv`
- **Type**: `(G : ℝ → ℂ) (G') (s₀) (hs₀ : 1 < s₀) (Lf : ℂ → ℂ) (hG : HasDerivAt G G' s₀) (hLfdiff) (heq : ∀ s > 1, exp (G s) = Lf s) (hLf0 : Lf s₀ ≠ 0) : G' = deriv Lf s₀ / Lf s₀`
- **What**: The derivative of the log sum at `s₀` equals the logarithmic derivative `Lf'/Lf` of any `Lf` with `exp∘G = Lf` near `s₀`.
- **How**: Differentiate both sides of `exp(G s) = Lf s` (`HasDerivAt.cexp`, `comp_ofReal`); `HasDerivAt.unique` + `congr_of_eventuallyEq` gives `G'·exp(G s₀) = Lf'(s₀)`; `field_simp`/`linear_combination`.
- **Hypotheses**: `s₀ > 1`; `G` differentiable at `s₀`; `Lf` ℂ-differentiable at `s₀`; `exp(G s) = Lf s` for `s > 1`; `Lf s₀ ≠ 0`.
- **Uses from project**: `[]`
- **Used by**: `norm_logSum_bounded_nhdsGT_aux`.
- **Visibility**: private
- **Lines**: 358–373 (proof ~12 lines)
- **Notes**: none

### `private theorem norm_bounded_nhdsGT_of_deriv_continuousOn`
- **Type**: `(G F : ℝ → ℂ) (hGderiv : ∀ s > 1, HasDerivAt G (F s) s) (hFcont : ContinuousOn F (Icc 1 2)) : ∃ C, ∀ᶠ s in 𝓝[>] 1, ‖G s‖ ≤ C`
- **What**: Mean-value packaging: if `G' = F` on `(1,∞)` and `F` is continuous on `[1,2]`, then `‖G‖` is bounded as `s ↓ 1`.
- **How**: Bound `‖F‖ ≤ M` on compact `[1,2]` (`isCompact_Icc.exists_bound_of_continuousOn`); MVT inequality `Convex.norm_image_sub_le_of_norm_deriv_le` gives `‖G s - G 2‖ ≤ M·‖s-2‖`; triangle inequality with `C = ‖G 2‖ + M`.
- **Hypotheses**: `G` has derivative `F` on `(1,∞)`; `F` continuous on `[1,2]`.
- **Uses from project**: `[]`
- **Used by**: `norm_logSum_bounded_nhdsGT_aux`.
- **Visibility**: private
- **Lines**: 377–398 (proof ~20 lines)
- **Notes**: long (30–50)? No — 20 lines, none

### `private noncomputable def twistedPrimeSum`
- **Type**: `(χ : galoisCharacter K L) (s : ℝ) : ℂ := ∑' 𝔭 : {𝔭 // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭}, χ(Frob 𝔭) · N𝔭^(-s)`
- **What**: The twisted prime sum `Σ_𝔭 χ(Frob 𝔭) N𝔭^{-s}` over unramified primes, as a complex function of `s`.
- **How**: Direct definition (a `tsum`).
- **Hypotheses**: `K,L` number fields, `K`-Galois `L`; `χ` a Galois character; `s` real.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`.
- **Used by**: `summable_twistedPrimeSum`, `twistedPrimeSum_one_eq`, `sum_charTwist_mul_twistedPrimeSum_eq`, `card_mul_frobeniusFibre_eq`, `exists_sum_charTwist_erase_norm_bounded`, `primeIdealZetaSum_frobeniusFibre_asymp`.
- **Visibility**: private
- **Lines**: 403–407 (def, no proof)
- **Notes**: none

### `private theorem summable_twistedPrimeSum`
- **Type**: `(χ : galoisCharacter K L) {s} (hs : 1 < s) : Summable (fun 𝔭 ↦ χ(Frob 𝔭) · N𝔭^(-s))`
- **What**: The twisted-prime-sum family is summable for `s > 1`.
- **How**: Each summand has norm `N𝔭^(-s)` (`‖χ(Frob)‖ = 1` via `isOfFinOrder.norm_eq_one`), dominated by `summable_prime_absNorm_rpow`; `Summable.of_norm`.
- **Hypotheses**: `χ` a Galois character; `s > 1`.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `UnramifiedIn.ne_bot`, `summable_prime_absNorm_rpow`, `unramifiedPrime_toPrimeNeBot_injective`.
- **Used by**: `artinLSeries_prime_sum_bounded_of_analytic_extension` (via `hexpeq`), `sum_charTwist_mul_twistedPrimeSum_eq`.
- **Visibility**: private
- **Lines**: 411–431 (proof ~19 lines)
- **Notes**: none

### `private theorem two_le_absNorm_prime`
- **Type**: `(𝔭 : Ideal (𝓞 K)) (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) : 2 ≤ Ideal.absNorm 𝔭`
- **What**: A nonzero prime ideal has absolute norm `≥ 2`.
- **How**: `absNorm ≠ 0` (`absNorm_eq_zero_iff`) and `≠ 1` (`absNorm_eq_one_iff` + `IsPrime.ne_top`), then `lia`.
- **Hypotheses**: `𝔭` a nonzero prime ideal of `𝓞 K`.
- **Uses from project**: `[]`
- **Used by**: `artinLSeries_prime_sum_bounded_of_analytic_extension` (via `hN2`).
- **Visibility**: private
- **Lines**: 434–439 (proof ~3 lines)
- **Notes**: none

### `private theorem norm_logSumTerm_sub_self_le_aux`
- **Type**: `{ι} (N) (c) (s) (hs : 1 < s) (hN : ∀ i, 2 ≤ N i) (hc : ∀ i, ‖c i‖ = 1) (i) : ‖-Complex.log (1 - c i·N i^(-s)) - c i·N i^(-s)‖ ≤ N i^(-2)`
- **What**: Per-term quadratic remainder bound: the difference between `-Log(1 - w)` and `w` is `≤ N_i^{-2}` (`w = c_i N_i^{-s}`).
- **How**: `‖w‖ ≤ 1/2 < 1`, then `Complex.norm_log_one_sub_inv_sub_self_le` (rewriting `log_inv`), giving `‖-Log(1-w) - w‖ ≤ ‖w‖² = N i^{-2s} ≤ N i^{-2}` (`Real.rpow_le_rpow_of_exponent_le`).
- **Hypotheses**: `N i ≥ 2`, `‖c i‖ = 1`, `s > 1`.
- **Uses from project**: `[]`
- **Used by**: `norm_tsumLinear_bounded_of_logSum_bounded_aux`.
- **Visibility**: private
- **Lines**: 443–477 (proof ~34 lines)
- **Notes**: long (30–50)

### `private theorem norm_logSum_bounded_nhdsGT_aux`
- **Type**: `{ι} (N) (c) (hN) (hc) (hsummr) (Lf : ℂ → ℂ) (D) (hDopen) (hmemD) (hLf_an : AnalyticOn ℂ Lf D) (hLf0 : Lf 1 ≠ 0) (hexpeq) : ∃ C, ∀ᶠ s in 𝓝[>] 1, ‖∑' i, -Complex.log (1 - c i·N i^(-s))‖ ≤ C`
- **What**: The log sum `G(s)` is bounded as `s ↓ 1`, given an analytic extension `Lf` of `exp∘G` (on open `D ⊇ [1,∞)`, `Lf 1 ≠ 0`).
- **How**: `Lf ≠ 0` on `[1,∞)` (`exp_ne_zero`); `F = Lf'/Lf` continuous on `[1,2]` (`AnalyticOnNhd.deriv`/`.continuousAt`); `G' = F` via `hasDerivAt_logSum_eq_logDeriv` (uses `differentiableAt_logSum_of_two_le`); conclude with `norm_bounded_nhdsGT_of_deriv_continuousOn`.
- **Hypotheses**: norm-base `≥ 2`, unit coefficients, summability of `N i^{-r}` (`r>1`); `Lf` analytic on open `D ⊇ ℝ_{≥1}`, `Lf 1 ≠ 0`, `exp(G s) = Lf s` for `s > 1`.
- **Uses from project**: `differentiableAt_logSum_of_two_le`, `hasDerivAt_logSum_eq_logDeriv`, `norm_bounded_nhdsGT_of_deriv_continuousOn`.
- **Used by**: `artinLSeries_prime_sum_bounded_of_analytic_extension`.
- **Visibility**: private
- **Lines**: 483–521 (proof ~39 lines)
- **Notes**: long (30–50)

### `private theorem norm_tsumLinear_bounded_of_logSum_bounded_aux`
- **Type**: `{ι} (N) (c) (hN) (hc) (hsummr) (hGbdd : ∃ C, ∀ᶠ s, ‖∑' i, -Complex.log(1 - c i·N i^(-s))‖ ≤ C) : ∃ C, ∀ᶠ s in 𝓝[>] 1, ‖∑' i, c i·N i^(-s)‖ ≤ C`
- **What**: The linear sum `Σ_i c_i N_i^{-s}` is bounded as `s ↓ 1` once the log sum `G` is, since they differ by a quadratically-convergent tail bounded by `Σ_i N_i^{-2}`.
- **How**: Write linear sum = `G - Σ_i (logterm - linterm)`; tail summable & bounded by `Σ N i^{-2}` via `norm_logSumTerm_sub_self_le_aux`; `norm_sub_le` + `gcongr` + `tsum_le_tsum`.
- **Hypotheses**: norm-base `≥ 2`, unit coefficients, summability of `N i^{-r}`; the log sum bounded near `s=1`.
- **Uses from project**: `norm_logSumTerm_sub_self_le_aux`.
- **Used by**: `artinLSeries_prime_sum_bounded_of_analytic_extension`.
- **Visibility**: private
- **Lines**: 526–560 (proof ~34 lines)
- **Notes**: long (30–50)

### `private theorem artinLSeries_prime_sum_bounded_of_analytic_extension`
- **Type**: `[IsMulCommutative Gal(L/K)] (χ) (hχ : χ ≠ 1) (Lf) (hLf_an : AnalyticOn ℂ Lf {s | 1 - (finrank ℚ K)⁻¹ < s.re}) (hLf_eq) (hLf0 : Lf 1 ≠ 0) : ∃ C, ∀ᶠ s in 𝓝[>] 1, ‖∑' 𝔭, χ(Frob 𝔭) · N𝔭^(-s)‖ ≤ C`
- **What**: The complex-analytic bridge of Dirichlet's argument: given an analytic extension `Lf` of `L(χ,·)`, nonzero at 1, the twisted prime sum stays bounded as `s ↓ 1`.
- **How**: Instantiate the abstract `ι = {unramified primes}`, `N = absNorm`, `c = χ(Frob)`; verify `‖c‖ = 1`, `N ≥ 2` (`two_le_absNorm_prime`), summability (`summable_prime_absNorm_rpow`), Euler-product identity `exp(G s) = Lf s` (`cexp_logSum_eq_tprod` + `exists_artinLSeries_eulerProduct_abelian` + `hLf_eq`), then chain `norm_logSum_bounded_nhdsGT_aux` ⟶ `norm_tsumLinear_bounded_of_logSum_bounded_aux`.
- **Hypotheses**: `Gal(L/K)` commutative; `χ ≠ 1`; `Lf` analytic on the half-plane `Re s > 1 - 1/[K:ℚ]`, equal to the ideal Dirichlet series for `Re s > 1`, `Lf 1 ≠ 0`.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `UnramifiedIn.ne_bot`, `galoisCharacterOnIdeal`, `two_le_absNorm_prime`, `summable_prime_absNorm_rpow`, `unramifiedPrime_toPrimeNeBot_injective`, `summable_twistedPrimeSum`, `cexp_logSum_eq_tprod`, `exists_artinLSeries_eulerProduct_abelian`, `norm_logSum_bounded_nhdsGT_aux`, `norm_tsumLinear_bounded_of_logSum_bounded_aux`.
- **Used by**: `artinLSeries_prime_sum_bounded_of_ne_one`.
- **Visibility**: private
- **Lines**: 567–623 (proof ~44 lines)
- **Notes**: long (30–50)

### `private theorem artinLSeries_prime_sum_bounded_of_ne_one`
- **Type**: `(m) [NeZero m] [IsCyclotomicExtension {m} K L] [IsMulCommutative Gal(L/K)] (hm : m % 4 ≠ 2) (χ) (hχ : χ ≠ 1) : ∃ C, ∀ᶠ s in 𝓝[>] 1, ‖∑' 𝔭, χ(Frob 𝔭) · N𝔭^(-s)‖ ≤ C`
- **What**: The analytic input of the cyclotomic case: for a nontrivial abelian `χ`, the twisted prime sum is bounded as `s ↓ 1`.
- **How**: Obtain the analytic extension from `artinLSeries_analytic_extension` (LF4) and nonvanishing from `artinLSeries_one_ne_zero` (LF5), then apply `artinLSeries_prime_sum_bounded_of_analytic_extension`.
- **Hypotheses**: `L = K(μ_m)`, `m % 4 ≠ 2`, `Gal(L/K)` commutative; `χ ≠ 1`.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `artinLSeries_analytic_extension`, `artinLSeries_one_ne_zero`, `artinLSeries_prime_sum_bounded_of_analytic_extension`.
- **Used by**: `exists_sum_charTwist_erase_norm_bounded`.
- **Visibility**: private
- **Lines**: 632–641 (proof ~3 lines)
- **Notes**: none

### `private theorem sum_charTwist_eq`
- **Type**: `(m) [NeZero m] [IsCyclotomicExtension {m} K L] [Fintype (galoisCharacter K L)] (σ) (𝔭) [𝔭.IsPrime] (hunr) (h : frobeniusClass K L 𝔭 = ConjClasses.mk σ) : (∑ χ, (χ σ)⁻¹ · χ(Frob 𝔭)) = Nat.card Gal(L/K)`
- **What**: Character-twist orthogonality collapse, matching case: `∑_χ (χσ)⁻¹·χ(Frob 𝔭) = |G|` when `Frob 𝔭 = [σ]`.
- **How**: Reindex by `Equiv.inv` to convert to `character_orthogonality_cyclotomic_eq`'s shape; per-term `Units.val_inv_eq_inv_val`, `inv_inv`, `mul_comm`.
- **Hypotheses**: `L = K(μ_m)`; finitely many characters; `𝔭` prime unramified; `Frob 𝔭 = [σ]`.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `character_orthogonality_cyclotomic_eq`.
- **Used by**: `sum_charTwist_mul_twistedPrimeSum_eq`.
- **Visibility**: private
- **Lines**: 657–669 (proof ~6 lines)
- **Notes**: none

### `private theorem sum_charTwist_ne`
- **Type**: same shape as `sum_charTwist_eq` but with `h : frobeniusClass K L 𝔭 ≠ ConjClasses.mk σ`, concluding `= 0`.
- **What**: Character-twist orthogonality collapse, non-matching case: the inner twist sum vanishes when `Frob 𝔭 ≠ [σ]`.
- **How**: Same `Equiv.inv` reindexing reducing to `character_orthogonality_cyclotomic_ne`.
- **Hypotheses**: as `sum_charTwist_eq` but `Frob 𝔭 ≠ [σ]`.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `character_orthogonality_cyclotomic_ne`.
- **Used by**: `sum_charTwist_mul_twistedPrimeSum_eq`.
- **Visibility**: private
- **Lines**: 673–685 (proof ~6 lines)
- **Notes**: none

### `private theorem primeIdealZetaSum_unramified_div_log_tendsto_one`
- **Type**: `: Tendsto (fun s ↦ primeIdealZetaSum {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s / log(1/(s-1))) (𝓝[>] 1) (𝓝 1)`
- **What**: The bare prime sum over unramified primes is asymptotic to `log(1/(s-1))` (differs from the universal sum only by finitely many ramified primes).
- **How**: Split univ = unramified `U` ∪ ramified `R` (disjoint); `R` finite (`finite_ramifiedIn`) so its zeta sum is bounded (`primeIdealZetaSum_le_card_of_finite`) ⇒ `R`-ratio → 0 (`squeeze_zero_norm'` with `tendsto_log_one_div_sub_one_atTop`); subtract from `primeIdealZetaSum_univ_tendsto_log`; reassemble via `primeIdealZetaSum_union_of_disjoint` + `primeIdealZetaSum_eq_univ_of_forall_prime_mem`.
- **Hypotheses**: `K,L` number fields, `K`-Galois `L`.
- **Uses from project**: `UnramifiedIn`, `finite_ramifiedIn`, `primeIdealZetaSum`, `primeIdealZetaSum_def`, `primeIdealZetaSum_le_card_of_finite`, `tendsto_log_one_div_sub_one_atTop`, `primeIdealZetaSum_univ_tendsto_log`, `primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_eq_univ_of_forall_prime_mem`.
- **Used by**: `primeIdealZetaSum_frobeniusFibre_asymp`.
- **Visibility**: private
- **Lines**: 690–732 (proof ~42 lines)
- **Notes**: long (30–50)

### `private theorem twistedPrimeSum_one_eq`
- **Type**: `(s) : twistedPrimeSum K L 1 s = (primeIdealZetaSum {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s : ℂ)`
- **What**: The trivial-character twisted prime sum equals the (cast of the) bare unramified prime zeta sum, since `1(Frob 𝔭) = 1`.
- **How**: Reindex (`hinj`/`hsurj` on the prime subtype) to identify the two index sets; per-summand `1(Frob).out = 1`, then `Complex.ofReal_cpow`/`ofReal_natCast` to match `N𝔭^{-s}`.
- **Hypotheses**: `K,L` number fields, `K`-Galois `L`; `s` real.
- **Uses from project**: `twistedPrimeSum`, `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `UnramifiedIn.ne_bot`, `primeIdealZetaSum`, `primeIdealZetaSum_def`.
- **Used by**: `card_mul_frobeniusFibre_eq`.
- **Visibility**: private
- **Lines**: 736–759 (proof ~22 lines)
- **Notes**: none

### `private theorem sum_charTwist_mul_twistedPrimeSum_eq`
- **Type**: `(m) [NeZero m] [IsCyclotomicExtension {m} K L] [Fintype (galoisCharacter K L)] (σ) {s} (hs : 1 < s) : (∑ χ, (χ σ)⁻¹ · twistedPrimeSum K L χ s) = Nat.card Gal(L/K) · primeIdealZetaSum {fibre σ} s`
- **What**: Orthogonality collapse (complex form): the character-twisted sum collapses to `|G| · P_σ(s)`, the prime sum over the Frobenius fibre `{σ_𝔭 = σ}`.
- **How**: Interchange finite `∑_χ` with prime `∑'_𝔭` (`Summable.tsum_finsetSum`); per prime, `sum_charTwist_eq`/`sum_charTwist_ne` collapse inner sum to `|G|·[Frob = [σ]]`; reindex fibre subtype (`hfinj`) and identify with `primeIdealZetaSum` of the fibre set; `Complex.ofReal_tsum`/`tsum_mul_left`.
- **Hypotheses**: `L = K(μ_m)`; finitely many characters; `σ ∈ Gal`; `s > 1`.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `UnramifiedIn.ne_bot`, `twistedPrimeSum`, `summable_twistedPrimeSum`, `sum_charTwist_eq`, `sum_charTwist_ne`, `primeIdealZetaSum`, `primeIdealZetaSum_def`.
- **Used by**: `card_mul_frobeniusFibre_eq`.
- **Visibility**: private
- **Lines**: 765–823 (proof ~50 lines)
- **Notes**: long (30–50) — at the 50-line boundary; borderline /decompose candidate

### `private theorem card_mul_frobeniusFibre_eq`
- **Type**: `(m) [NeZero m] [IsCyclotomicExtension {m} K L] [Fintype (galoisCharacter K L)] [DecidableEq (galoisCharacter K L)] (σ) {s} (hs : 1 < s) : (Nat.card Gal(L/K) : ℝ) · primeIdealZetaSum {fibre σ} s = primeIdealZetaSum {unramified} s + (∑ χ ∈ erase 1, (χ σ)⁻¹ · twistedPrimeSum K L χ s).re`
- **What**: Orthogonality-collapsed master identity (real form): `|G|·P_σ(s)` equals the bare unramified sum plus the real part of the `χ≠1` remainder.
- **How**: Peel the `χ=1` term off the full character sum (`Finset.add_sum_erase`, `twistedPrimeSum_one_eq`), equate with `sum_charTwist_mul_twistedPrimeSum_eq`, take real parts (`Complex.mul_re`/`natCast_re`/`natCast_im`).
- **Hypotheses**: `L = K(μ_m)`; finitely many characters with decidable equality; `σ`; `s > 1`.
- **Uses from project**: `galoisCharacter`, `twistedPrimeSum`, `twistedPrimeSum_one_eq`, `sum_charTwist_mul_twistedPrimeSum_eq`, `frobeniusClass`, `UnramifiedIn`, `primeIdealZetaSum`.
- **Used by**: `primeIdealZetaSum_frobeniusFibre_asymp`.
- **Visibility**: private
- **Lines**: 828–850 (proof ~12 lines)
- **Notes**: none

### `private theorem exists_sum_charTwist_erase_norm_bounded`
- **Type**: `(m) [NeZero m] [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) [Fintype (galoisCharacter K L)] [DecidableEq (galoisCharacter K L)] (σ) : ∃ CB, ∀ᶠ s in 𝓝[>] 1, ‖∑ χ ∈ erase 1, (χ σ)⁻¹ · twistedPrimeSum K L χ s‖ ≤ CB`
- **What**: The nontrivial-character remainder `∑_{χ≠1} (χσ)⁻¹·twistedPrimeSum χ s` stays bounded as `s ↓ 1`.
- **How**: Each `χ≠1` term bounded by `artinLSeries_prime_sum_bounded_of_ne_one` (`‖(χσ)⁻¹‖ = 1` harmless); `choose` per-character constants, `eventually_all_finset`, then `norm_sum_le` + `Finset.sum_le_sum`.
- **Hypotheses**: `L = K(μ_m)`, `m % 4 ≠ 2`; finitely many characters with decidable equality; `σ`.
- **Uses from project**: `galoisCharacter`, `twistedPrimeSum`, `artinLSeries_prime_sum_bounded_of_ne_one`.
- **Used by**: `primeIdealZetaSum_frobeniusFibre_asymp`.
- **Visibility**: private
- **Lines**: 855–894 (proof ~40 lines)
- **Notes**: long (30–50)

### `theorem primeIdealZetaSum_frobeniusFibre_asymp`
- **Type**: `(m) [NeZero m] [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (σ) : Tendsto (fun s ↦ primeIdealZetaSum {fibre σ} s / log(1/(s-1))) (𝓝[>] 1) (𝓝 (Nat.card Gal(L/K))⁻¹)`
- **What**: Sharifi 7.2.1 step (iv-a), numerator asymptotic: the fibre prime sum `P_σ(s)` is asymptotic to `(1/|G|)·log(1/(s-1))`.
- **How**: Remainder `B(s)` bounded (`exists_sum_charTwist_erase_norm_bounded`) ⇒ `B.re/log → 0` (`squeeze_zero_norm'`); the master identity `card_mul_frobeniusFibre_eq` rewrites `|G|·P_σ = U-sum + B.re`; combine with `primeIdealZetaSum_unramified_div_log_tendsto_one` and divide by `|G|`.
- **Hypotheses**: `L = K(μ_m)`, `m % 4 ≠ 2`; `σ ∈ Gal`.
- **Uses from project**: `galoisCharacter`, `twistedPrimeSum`, `frobeniusClass`, `UnramifiedIn`, `primeIdealZetaSum`, `exists_sum_charTwist_erase_norm_bounded`, `tendsto_log_one_div_sub_one_atTop`, `primeIdealZetaSum_unramified_div_log_tendsto_one`, `card_mul_frobeniusFibre_eq`.
- **Used by**: `cyclotomic_density_from_two_sided_asymp`.
- **Visibility**: public
- **Lines**: 898–940 (proof ~42 lines)
- **Notes**: long (30–50)

### `theorem tendsto_ratio_of_log_asymp_numerator`
- **Type**: `(num den : ℝ → ℝ) (c) (hnum : Tendsto (num/log) (𝓝[>] 1) (𝓝 c)) (hden : Tendsto (den/log) (𝓝[>] 1) (𝓝 1)) : Tendsto (fun s ↦ num s / den s) (𝓝[>] 1) (𝓝 c)`
- **What**: Pure real-analysis glue: if `num/log → c` and `den/log → 1`, then `num/den → c`.
- **How**: `log(1/(s-1)) ≠ 0` eventually (`Real.log_pos`); divide the two ratios (`hnum.div hden`) and cancel the common `log` factor (`div_div_div_cancel_right₀`).
- **Hypotheses**: the two log-normalised limits.
- **Uses from project**: `[]`
- **Used by**: `cyclotomic_density_from_two_sided_asymp`.
- **Visibility**: public
- **Lines**: 944–956 (proof ~12 lines)
- **Notes**: none

### `theorem cyclotomic_density_from_two_sided_asymp`
- **Type**: `(m) [NeZero m] [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (σ) : Tendsto (fun s ↦ primeIdealZetaSum {fibre σ} s / primeIdealZetaSum univ s) (𝓝[>] 1) (𝓝 (Nat.card Gal(L/K))⁻¹)`
- **What**: Sharifi 7.2.1 step (iv): two-sided log-asymptotic comparison giving the fibre/universal prime-sum ratio limit `1/|G|` — the Dirichlet-density limit.
- **How**: Apply `tendsto_ratio_of_log_asymp_numerator` to the numerator asymptotic (`primeIdealZetaSum_frobeniusFibre_asymp`) and denominator asymptotic (`primeIdealZetaSum_univ_tendsto_log`).
- **Hypotheses**: `L = K(μ_m)`, `m % 4 ≠ 2`; `σ`.
- **Uses from project**: `primeIdealZetaSum`, `frobeniusClass`, `UnramifiedIn`, `tendsto_ratio_of_log_asymp_numerator`, `primeIdealZetaSum_frobeniusFibre_asymp`, `primeIdealZetaSum_univ_tendsto_log`.
- **Used by**: `chebotarev_cyclotomic`.
- **Visibility**: public
- **Lines**: 962–975 (proof ~3 lines, term-mode)
- **Notes**: none

### `theorem chebotarev_cyclotomic`
- **Type**: `(m) [NeZero m] [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (σ) : HasDirichletDensity {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = ConjClasses.mk σ} (Nat.card Gal(L/K))⁻¹`
- **What**: Chebotarev's theorem, cyclotomic case: the primes of `K` unramified in `L = K(μ_m)` with Frobenius `[σ]` have Dirichlet density `1/|Gal(L/K)|`. (Main result.)
- **How**: `HasDirichletDensity` unfolds to the ratio limit, supplied directly by `cyclotomic_density_from_two_sided_asymp`.
- **Hypotheses**: `K,L` number fields, `K`-Galois `L = K(μ_m)`, `m % 4 ≠ 2`; `σ ∈ Gal(L/K)`.
- **Uses from project**: `UnramifiedIn`, `frobeniusClass`, `HasDirichletDensity`, `cyclotomic_density_from_two_sided_asymp`.
- **Used by**: `chebotarev_cyclotomic_lowerDensity_ge`.
- **Visibility**: public
- **Lines**: 982–989 (proof ~1 line, term-mode)
- **Notes**: none

### `theorem chebotarev_cyclotomic_lowerDensity_ge`
- **Type**: `(m) [NeZero m] [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (σ) : HasLowerDirichletDensity {fibre σ} (Nat.card Gal(L/K))⁻¹`
- **What**: Lower-density-inequality variant of the cyclotomic case, used downstream in the abelian case via `HasLowerDirichletDensity.mono`.
- **How**: `(chebotarev_cyclotomic …).hasLower` — a density gives a lower density.
- **Hypotheses**: as `chebotarev_cyclotomic`.
- **Uses from project**: `UnramifiedIn`, `frobeniusClass`, `HasLowerDirichletDensity`, `chebotarev_cyclotomic`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 994–1001 (proof ~1 line, term-mode)
- **Notes**: none

---

## File Summary

**Total declarations: 27** — defs: 1 (`twistedPrimeSum`); lemmas/theorems: 26; instances: 0; structures/classes/abbrevs/inductives: 0.

**Key API (used by ≥3 in-file):**
- `twistedPrimeSum` (def) — used by 6 decls.
- `unramifiedPrime_toPrimeNeBot_injective` — used by 3 decls.

(Mathlib-style API consumers: the public step lemmas are used 1× each; the project's *external* API `frobeniusClass`/`UnramifiedIn`/`primeIdealZetaSum`/`galoisCharacter` are pervasive but defined in other files.)

**Unused decls (no in-file caller):** `log_artinLSeries_asymp_character_sum` (public step (ii), not wired into the main chain — its content is re-derived inside the complex-analytic bridge); `chebotarev_cyclotomic_lowerDensity_ge` (public, consumed by the abelian-case file). The other "unused" leaves of the dep tree are the two public terminal theorems by design.

**Decls with `sorry`:** none.

**Decls with `set_option`:** none. (Two `open scoped Classical in` on `sum_galoisCharacter_eq_card_or_zero` and `sum_galoisCharacter_mul_inv_eq`; several in-proof `classical`.)

**Proofs >50 lines (decompose-needed):**
- `differentiableAt_logSum_of_two_le` — **~103 lines** (236–340).
- `log_artinLSeries_asymp_character_sum` — **~61 lines** (96–159).

**Proofs 30–50 lines:**
- `sum_charTwist_mul_twistedPrimeSum_eq` — ~50 (765–823) [boundary; borderline decompose candidate].
- `artinLSeries_prime_sum_bounded_of_analytic_extension` — ~44 (567–623).
- `primeIdealZetaSum_frobeniusFibre_asymp` — ~42 (898–940).
- `primeIdealZetaSum_unramified_div_log_tendsto_one` — ~42 (690–732).
- `exists_sum_charTwist_erase_norm_bounded` — ~40 (855–894).
- `norm_logSum_bounded_nhdsGT_aux` — ~39 (483–521).
- `norm_logSumTerm_sub_self_le_aux` — ~34 (443–477).
- `norm_tsumLinear_bounded_of_logSum_bounded_aux` — ~34 (526–560).

**Note:** The whole file is `sorry`-free at the Lean level; the "leaf" gaps (LF4 `artinLSeries_analytic_extension`, LF5 `artinLSeries_one_ne_zero`, geometry-of-numbers bound) are imported hypotheses/results from sibling files (`ZetaProduct`, `CyclotomicNormResidue`), not local sorries.
