# Inventory: PadicLFunctions/Interpolation/Sawtooth.lean

Namespace `PadicLFunctions`. `noncomputable section`. Opens `Filter`, scoped `Topology`.
File goal: the conditionally-convergent sawtooth evaluation `∑_{n≥1} sin(2πnx)/n = π(1/2−x)` on `(0,1)` (Abel limit + Dirichlet's test), packaged as `sinZeta_one_eq_boundary`, and its functional-equation consequence `hurwitzZeta x 0 = −B₁(x)` (extending mathlib's `hurwitzZeta_neg_nat` to `k=0` on the open interval).

---

### lemma norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded
- Type: `{E} [NormedAddCommGroup E] [NormedSpace ℝ E] {a : ℕ → ℝ} {z : ℕ → E} {B : ℝ} (ha : Antitone a) (ha_nonneg : ∀ n, 0 ≤ a n) (hbound : ∀ n, ‖∑ i ∈ range n, z i‖ ≤ B) (n : ℕ) : ‖∑ i ∈ range n, a i • z i‖ ≤ B * a 0`
- What: Abel/summation-by-parts bound: a weighted partial sum of `z` with antitone nonneg weights `a` and uniformly `B`-bounded partial sums of `z` is bounded by `B * a 0`.
- How: Discharges `n = 0` trivially; otherwise rewrites via `Finset.sum_range_by_parts`, bounds the boundary term by `B * a(n-1)` and the telescoping sum `Σ (a i − a(i+1))` (via `Finset.sum_range_sub`, `Finset.sum_neg_distrib`) by `B * (a 0 − a(n-1))`, then `norm_sub_le` + `add_le_add` give `B * a 0`. Hinges on `Finset.sum_range_by_parts` and `Finset.sum_range_sub`.
- Hypotheses: `a` antitone and nonnegative; partial sums of `z` over every initial range bounded in norm by `B`.
- Uses from project: []
- Used by: `norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded`
- Visibility: public
- Lines: 35–108 (proof ~68 lines)
- Notes: OVER-50 (needs /decompose-proof). No sorry/set_option/TODO.

### lemma norm_sum_range_shift_le_of_bounded
- Type: `{E} [NormedAddCommGroup E] {z : ℕ → E} {B : ℝ} (hbound : ∀ n, ‖∑ i ∈ range n, z i‖ ≤ B) (m n : ℕ) : ‖∑ i ∈ range n, z (m + i)‖ ≤ 2 * B`
- What: Partial sums of the `m`-shifted sequence are bounded by `2B` (block difference of two `B`-bounded prefixes).
- How: Rewrites the shifted sum as `(prefix m+n) − (prefix m)` via `Finset.sum_range_add`, then `norm_sub_le` and `add_le_add (hbound _) (hbound _)` give `B + B = 2B`.
- Hypotheses: prefix sums of `z` uniformly bounded by `B`.
- Uses from project: []
- Used by: `norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded`
- Visibility: public
- Lines: 111–128 (proof ~18 lines)
- Notes: none.

### lemma norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded
- Type: `{E} [NormedAddCommGroup E] [NormedSpace ℝ E] {a : ℕ → ℝ} {z : ℕ → E} {B : ℝ} (ha : Antitone a) (ha_nonneg : ∀ n, 0 ≤ a n) (hbound : ∀ n, ‖∑ i ∈ range n, z i‖ ≤ B) (m n : ℕ) : ‖∑ i ∈ range n, a (m + i) • z (m + i)‖ ≤ (2 * B) * a m`
- What: Tail (shifted) weighted sums inherit the summation-by-parts bound with constant `2B` and leading weight `a m`.
- How: Applies the base `norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded` to the shifted sequences `k ↦ a(m+k)`, `k ↦ z(m+k)` with bound `2B` supplied by `norm_sum_range_shift_le_of_bounded`; antitonicity/nonnegativity transported by `Nat.add_le_add_left`; `simpa` normalises arithmetic.
- Hypotheses: `a` antitone and nonnegative; prefix sums of `z` bounded by `B`.
- Uses from project: `norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded`, `norm_sum_range_shift_le_of_bounded`
- Used by: `norm_sum_range_shifted_sin_term_le`
- Visibility: public
- Lines: 131–143 (proof ~7 lines)
- Notes: none.

### lemma one_sub_exp_ofReal_mul_I
- Type: `(t : ℝ) : (1 : ℂ) − Complex.exp (t * I) = (2 * sin(t/2) : ℝ) * (cos(t/2 − π/2) + sin(t/2 − π/2) * I)`
- What: Polar form of `1 − e^{it}` on the upper unit semicircle as a real factor `2 sin(t/2)` times a unit phasor.
- How: Three-step `calc`: expand `exp_ofReal_mul_I`, apply double-angle identities `Real.cos_two_mul`/`Real.sin_two_mul` with `Real.sin_sq_add_cos_sq`, then rewrite phase via `Real.cos_sub_pi_div_two`/`Real.sin_sub_pi_div_two`; closed by `ring`/`ring_nf`.
- Hypotheses: none (all real `t`).
- Uses from project: []
- Used by: `arg_one_sub_exp_ofReal_mul_I`, `uniformCauchySeqOn_shiftedSinPartialSums`
- Visibility: public
- Lines: 146–164 (proof ~15 lines)
- Notes: none.

### lemma arg_one_sub_exp_ofReal_mul_I
- Type: `{t : ℝ} (ht₀ : 0 < t) (ht₂π : t < 2 * π) : Complex.arg ((1 : ℂ) − Complex.exp (t * I)) = t/2 − π/2`
- What: Principal argument of `1 − e^{it}` equals `t/2 − π/2` for `t ∈ (0, 2π)`.
- How: Shows `2 sin(t/2) > 0` (`Real.sin_pos_of_mem_Ioo`) and `t/2 − π/2 ∈ Ioc (−π) π`, rewrites via `one_sub_exp_ofReal_mul_I`, then applies `Complex.arg_mul_cos_add_sin_mul_I`.
- Hypotheses: `0 < t < 2π`.
- Uses from project: `one_sub_exp_ofReal_mul_I`
- Used by: `neg_log_one_sub_exp_ofReal_mul_I_im`
- Visibility: public
- Lines: 167–178 (proof ~12 lines)
- Notes: none.

### lemma neg_log_one_sub_exp_ofReal_mul_I_im
- Type: `{t : ℝ} (ht₀ : 0 < t) (ht₂π : t < 2 * π) : (−Complex.log ((1 : ℂ) − Complex.exp (t * I))).im = π/2 − t/2`
- What: The imaginary part of `−log(1 − e^{it})` (the Abel-sum logarithm) is `π/2 − t/2`.
- How: `Complex.neg_im` + `Complex.log_im` reduce to the argument, which is `arg_one_sub_exp_ofReal_mul_I`; `ring` finishes.
- Hypotheses: `0 < t < 2π`.
- Uses from project: `arg_one_sub_exp_ofReal_mul_I`
- Used by: `tendsto_sum_range_sin_div_nat`
- Visibility: public
- Lines: 181–184 (proof ~3 lines)
- Notes: none.

### lemma hasSum_mul_rpow_sin
- Type: `(x r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r < 1) : HasSum (fun n : ℕ => (r^n / n) * sin(2πxn)) (−Complex.log ((1 : ℂ) − (r : ℂ) * Complex.exp ((2πx) * I))).im`
- What: Abel-damped sine series `Σ (rⁿ/n) sin(2πxn)` sums to the imaginary part of `−log(1 − r·e^{2πix})`.
- How: Sets `z = r·e^{2πix}`, proves `‖z‖ = r < 1` via `Complex.norm_exp_ofReal_mul_I`, then takes imaginary part of mathlib's `Complex.hasSum_taylorSeries_neg_log`; congr term-by-term using `Complex.div_natCast_im`, `Complex.exp_nat_mul`, `Complex.exp_ofReal_mul_I_im`.
- Hypotheses: `0 ≤ r < 1`.
- Uses from project: []
- Used by: `tendsto_sum_range_sin_div_nat`
- Visibility: public
- Lines: 187–213 (proof ~26 lines)
- Notes: none.

### lemma norm_sum_range_sin_le
- Type: `{x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) (n : ℕ) : ‖∑ i ∈ range n, sin(2πxi)‖ ≤ 2 / ‖(1 : ℂ) − Complex.exp ((2πx) * I)‖`
- What: Partial sums of the sine kernel are uniformly bounded by `2/‖1 − e^{2πix}‖` for interior `x`.
- How: Sets `z = e^{2πix}`, shows `z ≠ 1` (`Complex.exp_eq_one_iff` + `omega` on the integer multiplier), identifies the sum with `Im(Σ zⁱ)` (`Complex.exp_ofReal_mul_I_im`), bounds the geometric sum `(zⁿ−1)/(z−1)` using `geom_sum_eq`, `‖z‖=1`, and `RCLike.norm_im_le_norm`.
- Hypotheses: `0 < x < 1`.
- Uses from project: []
- Used by: `norm_sum_range_shifted_sin_term_le`, `exists_tendsto_sum_range_sin_div_nat`
- Visibility: public
- Lines: 216–265 (proof ~49 lines)
- Notes: long(30-50). No sorry/set_option/TODO.

### lemma continuous_shiftedSinTerm
- Type: `(x : ℝ) (i : ℕ) : Continuous fun s : ℝ => sin(2πx(i+1)) / ((i+1 : ℂ) ^ (s : ℂ))`
- What: Each shifted sine Dirichlet term is continuous in the exponent `s`.
- How: `Continuous.div` of constant numerator over `Continuous.const_cpow`, with nonvanishing denominator from `Nat.cast_add_one_ne_zero` and `Complex.cpow_eq_zero_iff`.
- Hypotheses: none.
- Uses from project: []
- Used by: `sinZeta_one_eq_boundary`
- Visibility: public
- Lines: 268–273 (proof ~3 lines)
- Notes: none.

### lemma hasSum_shifted_sinZeta
- Type: `(x s : ℝ) (hs : 1 < s) : HasSum (fun n : ℕ => sin(2πx(n+1)) / ((n+1 : ℂ) ^ (s : ℂ))) (HurwitzZeta.sinZeta x s)`
- What: Repackages mathlib's `hasSum_nat_sinZeta` over the `n+1`-indexed terms (the `n=0` term vanishes), summing to `sinZeta x s`.
- How: Takes mathlib `HurwitzZeta.hasSum_nat_sinZeta`, shifts the index via `summable_nat_add_iff`, recovers the value with `hShift.zero_add` and `tendsto_nhds_unique` on partial sums, then `congr_fun`.
- Hypotheses: `1 < s`.
- Uses from project: []
- Used by: `sinZeta_one_eq_boundary`
- Visibility: public
- Lines: 276–287 (proof ~11 lines)
- Notes: none.

### lemma norm_sum_range_shifted_sin_term_le
- Type: `{x s : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) (hs : 1 ≤ s) (m n : ℕ) : ‖∑ i ∈ range n, sin(2πx(m+i+1)) / ((m+i+1 : ℕ : ℂ) ^ (s : ℂ))‖ ≤ (4 / ‖(1 : ℂ) − Complex.exp ((2πx) * I)‖) * (1 / (m+1 : ℝ)^s)`
- What: Uniform tail bound for the shifted sine Dirichlet series on `s ≥ 1`: tail starting at `m` is `O((m+1)^{−s})`.
- How: Sets weights `a k = 1/(k+1)^s` (antitone via `Real.rpow_le_rpow`, nonneg), kernel `z k = sin(2πx(k+1))` (prefix-bounded by `norm_sum_range_sin_le` after reindexing with `Finset.sum_range_add`), recasts the term as `a • z` via `Complex.ofReal_cpow`, then invokes `norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded`; `ring` consolidates `2·(2/·) = 4/·`.
- Hypotheses: `0 < x < 1`, `1 ≤ s`.
- Uses from project: `norm_sum_range_sin_le`, `norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded`
- Used by: `uniformCauchySeqOn_shiftedSinPartialSums`
- Visibility: public
- Lines: 290–338 (proof ~49 lines)
- Notes: long(30-50). No sorry/set_option/TODO.

### lemma exists_tendsto_sum_range_sin_div_nat
- Type: `{x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) : ∃ l : ℝ, Tendsto (fun n ↦ ∑ i ∈ range n, if i = 0 then 0 else sin(2πxi)/i) atTop (𝓝 l)`
- What: The endpoint sine series `Σ sin(2πxi)/i` converges (some limit `l`) on `(0,1)` by Dirichlet's test.
- How: Weights `f n = 1/n` (antitone, `→ 0` via `tendsto_one_div_add_atTop_nhds_zero_nat`), kernel `z` with prefix sums bounded by `norm_sum_range_sin_le`; applies `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded` (Dirichlet's test) and `cauchySeq_tendsto_of_complete`, then matches the `f • z` series with the `if`-guarded series.
- Hypotheses: `0 < x < 1`.
- Uses from project: `norm_sum_range_sin_le`
- Used by: `tendsto_sum_range_sin_div_nat`
- Visibility: public
- Lines: 341–393 (proof ~52 lines)
- Notes: OVER-50 (needs /decompose-proof). No sorry/set_option/TODO.

### lemma tendsto_sum_range_sin_div_nat
- Type: `{x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) : Tendsto (fun n ↦ ∑ i ∈ range n, if i = 0 then 0 else sin(2πxi)/i) atTop (𝓝 (π * (1/2 − x)))`
- What: The endpoint sine series converges to the classical sawtooth boundary value `π(1/2 − x)` on `(0,1)`.
- How: Identifies the limit `l` (from `exists_tendsto_sum_range_sin_div_nat`) via Abel's theorem `Real.tendsto_tsum_powerSeries_nhdsWithin_lt`; on `Ioo 0 1` rewrites the power series tsum as `Im(−log(1 − r e^{2πix}))` using `hasSum_mul_rpow_sin`; takes the radial limit `r → 1⁻` via `Tendsto.clog` (slit-plane membership shown through `2 sin(πx)² > 0`) and evaluates with `neg_log_one_sub_exp_ofReal_mul_I_im`; `tendsto_nhds_unique` pins `l = π(1/2 − x)`.
- Hypotheses: `0 < x < 1`.
- Uses from project: `exists_tendsto_sum_range_sin_div_nat`, `hasSum_mul_rpow_sin`, `neg_log_one_sub_exp_ofReal_mul_I_im`
- Used by: `tendsto_sum_range_shifted_sin_one`
- Visibility: public
- Lines: 397–498 (proof ~101 lines)
- Notes: OVER-50 (needs /decompose-proof). No sorry/set_option/TODO.

### lemma tendsto_sum_range_shifted_sin_one
- Type: `{x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) : Tendsto (fun n : ℕ => ∑ i ∈ range n, sin(2πx(i+1)) / ((i+1 : ℂ) ^ (1 : ℂ))) atTop (nhds (π * (1/2 − x) : ℂ))`
- What: The shifted (1-indexed) endpoint sine series converges to the same boundary value `π(1/2 − x)`, now in `ℂ` at `s = 1`.
- How: Casts `tendsto_sum_range_sin_div_nat` to `ℂ` (`.ofReal`), shifts the index by 1 (`tendsto_add_atTop_iff_nat`), and matches partial sums via `Finset.sum_range_add` and `congr'`/`Eventually.of_forall`.
- Hypotheses: `0 < x < 1`.
- Uses from project: `tendsto_sum_range_sin_div_nat`
- Used by: `sinZeta_one_eq_boundary`
- Visibility: public
- Lines: 501–516 (proof ~12 lines)
- Notes: none.

### lemma uniformCauchySeqOn_shiftedSinPartialSums
- Type: `{x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) : UniformCauchySeqOn (fun n (s : ℝ) => ∑ i ∈ range n, sin(2πx(i+1)) / ((i+1 : ℂ) ^ (s : ℂ))) atTop (Set.Ici 1)`
- What: The shifted sine Dirichlet partial sums are uniformly Cauchy in `n` on the half-line `s ≥ 1`.
- How: Via `Metric.uniformCauchySeqOn_iff`; sets `B = 4/‖1 − e^{2πix}‖`, proving the denominator positive through `one_sub_exp_ofReal_mul_I` factored as `(2 sin(πx))·(unit phasor)` (both nonzero, `Complex.norm_cos_add_sin_mul_I`). Given `ε`, picks `N` with `1/(N+1) < ε/B` (`exists_nat_one_div_lt`); the tail distance is bounded by `norm_sum_range_shifted_sin_term_le` then monotonically by `B·1/(N+1) < ε` using `Real.rpow_le_rpow_of_exponent_le` and `one_div_le_one_div_of_le`; symmetrised over `m,n` by `le_total`.
- Hypotheses: `0 < x < 1`.
- Uses from project: `one_sub_exp_ofReal_mul_I`, `norm_sum_range_shifted_sin_term_le`
- Used by: `sinZeta_one_eq_boundary`
- Visibility: public
- Lines: 519–603 (proof ~84 lines)
- Notes: OVER-50 (needs /decompose-proof). No sorry/set_option/TODO.

### theorem sinZeta_one_eq_boundary
- Type: `{x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) : HurwitzZeta.sinZeta x 1 = (π * (1/2 − x) : ℂ)`
- What: The sine zeta function at `s = 1` equals the sawtooth boundary value `π(1/2 − x)` for `x ∈ (0,1)`.
- How: Defines `G s = if s = 1 then boundary else sinZeta x s`; uniform Cauchyness (`uniformCauchySeqOn_shiftedSinPartialSums`) + pointwise limits (`tendsto_sum_range_shifted_sin_one` at `s=1`, `hasSum_shifted_sinZeta` elsewhere) give `ContinuousOn G` on `Ici 1` (`tendstoUniformlyOn_of_tendsto`, terms continuous by `continuous_shiftedSinTerm`); the right limit of `G` at `1` is `boundary`, while `sinZeta` itself is continuous there (`HurwitzZeta.differentiableAt_sinZeta`), so `tendsto_nhds_unique` forces equality.
- Hypotheses: `0 < x < 1`.
- Uses from project: `uniformCauchySeqOn_shiftedSinPartialSums`, `tendsto_sum_range_shifted_sin_one`, `hasSum_shifted_sinZeta`, `continuous_shiftedSinTerm`
- Used by: `hurwitzZetaOdd_apply_zero_of_mem_Ioo`
- Visibility: public
- Lines: 607–642 (proof ~35 lines)
- Notes: long(30-50). No sorry/set_option/TODO.

### lemma unitAddCircle_coe_ne_zero
- Type: `{x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) : (↑x : UnitAddCircle) ≠ 0`
- What: A real number in `(0,1)` maps to a nonzero element of `ℝ/ℤ`.
- How: From `AddCircle.coe_eq_zero_iff`, `x` would equal an integer `n`; `0 < n < 1` is impossible by `omega` after casting.
- Hypotheses: `0 < x < 1`.
- Uses from project: []
- Used by: `hurwitzZeta_neg_nat_of_mem_Ioo`
- Visibility: public
- Lines: 645–652 (proof ~7 lines)
- Notes: none.

### theorem hurwitzZetaOdd_apply_zero_of_mem_Ioo
- Type: `{x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) : HurwitzZeta.hurwitzZetaOdd x 0 = ((1/2 − x : ℝ) : ℂ)`
- What: The odd Hurwitz zeta at `s = 0` equals `1/2 − x` for `x ∈ (0,1)`.
- How: Applies the functional equation `HurwitzZeta.hurwitzZetaOdd_one_sub` at `s = 1` (needs `1 ≠ −n`), substitutes the sawtooth value via `sinZeta_one_eq_boundary`, evaluates `sin(π/2)=1`, `Complex.Gamma_one`, `cpow_neg_one`, and clears `π` with `field_simp`/`ring`.
- Hypotheses: `0 < x < 1`.
- Uses from project: `sinZeta_one_eq_boundary`
- Used by: `hurwitzZeta_neg_nat_of_mem_Ioo`
- Visibility: public
- Lines: 657–674 (proof ~17 lines)
- Notes: none.

### theorem hurwitzZeta_neg_nat_of_mem_Ioo
- Type: `(k : ℕ) {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) : HurwitzZeta.hurwitzZeta x (−(k : ℂ)) = −1/(k+1) * ((Polynomial.bernoulli (k+1)).map (algebraMap ℚ ℂ)).eval (x : ℂ)`
- What: Extends mathlib's `hurwitzZeta_neg_nat` to include `k = 0` for interior `x`: `hurwitzZeta x (−k) = −B_{k+1}(x)/(k+1)`.
- How: For `k > 0` defers to mathlib `HurwitzZeta.hurwitzZeta_neg_nat`. For `k = 0` splits `hurwitzZeta` into even+odd (`hurwitzZetaEven_apply_zero` vanishes since `x ≢ 0` by `unitAddCircle_coe_ne_zero`; odd part from `hurwitzZetaOdd_apply_zero_of_mem_Ioo`), then identifies `B₁(x) = x − 1/2` via `Polynomial.bernoulli_one` and `ring`.
- Hypotheses: `0 < x < 1`; `k : ℕ` arbitrary.
- Uses from project: `unitAddCircle_coe_ne_zero`, `hurwitzZetaOdd_apply_zero_of_mem_Ioo`
- Used by: unused in file
- Visibility: public
- Lines: 679–694 (proof ~15 lines)
- Notes: none.

---

## File Summary

- Total decls: 18 (defs: 0 / lemmas+theorems: 18 / instances: 0). No structures/classes/abbrevs/inductives. All public.
- Key API (used by ≥3 decls in file): `norm_sum_range_sin_le` (used by 2 in-file, but central — see below). Strictly ≥3 in-file consumers: none; the most reused are `norm_sum_range_sin_le` (2), `one_sub_exp_ofReal_mul_I` (2), `sinZeta_one_eq_boundary` is the file's external API hub. Note: no single decl has ≥3 in-file consumers; the dependency chain is mostly linear toward `sinZeta_one_eq_boundary` → `hurwitzZeta_neg_nat_of_mem_Ioo`.
- Unused in file (terminal/exported results): `hurwitzZeta_neg_nat_of_mem_Ioo` (top-level export; the file's deliverable).
- Decls with sorry: none.
- set_option: none.
- Proofs >50 lines (OVER-50) — 4: `norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded` (~68), `exists_tendsto_sum_range_sin_div_nat` (~52), `tendsto_sum_range_sin_div_nat` (~101), `uniformCauchySeqOn_shiftedSinPartialSums` (~84).
- Proofs 30–50 lines (long) — 3: `norm_sum_range_sin_le` (~49), `norm_sum_range_shifted_sin_term_le` (~49), `sinZeta_one_eq_boundary` (~35).
