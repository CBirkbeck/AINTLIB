# Inventory: PadicLFunctions/ValuesAtOneComplex.lean

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/ValuesAtOneComplex.lean`

Scope: The classical complex value `L(θ,1)` (RJW §6.1, Thm 6.1(i), cluster C6), following Washington Thm 4.9. Complex-analysis "quarantine" file stated against mathlib's `DirichletCharacter.LFunction`. Namespace `PadicLFunctions.ValuesAtOneComplex`; section variable `{N : ℕ} [NeZero N]`. Opens `Complex DirichletCharacter`.

---

### theorem gaussSum_mul_coprime
- Type: `{R : Type*} [CommRing R] {D M : ℕ} [NeZero D] [NeZero M] (hco : Nat.Coprime D M) (η : DirichletCharacter R D) (χ : DirichletCharacter R M) {θ : DirichletCharacter R (D*M)} (hθ : θ = changeLevel _ η * changeLevel _ χ) {εD εM : R} (hεD : εD^D = 1) (hεM : εM^M = 1) : gaussSum θ (zmodChar (D*M) …) = gaussSum η (zmodChar D hεD) * gaussSum χ (zmodChar M hεM)` (abbreviated, >3 lines)
- What: Gauss sums are multiplicative over coprime levels: for `θ` the product of `η` (level `D`) and `χ` (level `M`) at level `DM`, with the split additive character `ε = εD·εM`, one has `G(θ) = G(η)·G(χ)`.
- How: Chinese Remainder Theorem. Uses the ring iso `ZMod.chineseRemainder hco` to factor both the multiplicative character (`hθfac`, splitting `θ a` into `η·χ` on the CRT components, handling non-units via `MulChar.map_nonunit` and `Prod.isUnit_iff`) and the additive character (`hψfac` via `AddChar.zmodChar_apply'`), then transports the Gauss-sum over the equiv with `Equiv.sum_comp` and `Finset.sum_product`/`Finset.sum_mul_sum`, finishing with `ring`.
- Hypotheses: `R` a commutative ring; `D, M` nonzero and coprime; `θ` factors as the level-changed product of `η` and `χ`; `εD, εM` roots of unity of orders dividing `D`, `M` respectively.
- Uses from project: []
- Used by: unused in file
- Visibility: public
- Lines: 30–90 (proof ~44 lines)
- Notes: long(30-50); no sorry/set_option.

### theorem tendsto_sum_pow_div_eq_neg_log
- Type: `{z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, z^(n+1)/(n+1)) atTop (nhds (-Complex.log (1 - z)))`
- What: Abel-type boundary convergence: for `z` on the unit circle with `z ≠ 1`, the truncated logarithm series `Σ_{n<N} zⁿ⁺¹/(n+1)` converges to `−log(1−z)`.
- How: First shows `z.re < 1` (from `‖z‖=1`, `z≠1` via `normSq`). Establishes a uniform bound `‖Σ zⁱ⁺¹‖ ≤ 2/‖1−z‖` using `geom_sum_eq`. Dirichlet/Abel test: `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded` with weights `1/(n+1)→0` gives a Cauchy (hence convergent) limit `l`. Identifies `l = −log(1−z)` by Abel's theorem `Complex.tendsto_tsum_powerSeries_nhdsWithin_lt` together with continuity of `clog` (`Tendsto.clog`, `mem_slitPlane`) and `Complex.hasSum_taylorSeries_neg_log`, concluding by `tendsto_nhds_unique`.
- Hypotheses: `z` complex with norm 1 and `z ≠ 1`.
- Uses from project: []
- Used by: `tendsto_LSeries_pow_boundary`
- Visibility: public
- Lines: 92–177 (proof ~84 lines)
- Notes: OVER-50 (needs /decompose-proof); no sorry/set_option.

### lemma isPrimitive_inv
- Type: `{θ : DirichletCharacter ℂ N} (hθ : θ.IsPrimitive) : θ⁻¹.IsPrimitive` (with `omit [NeZero N]`)
- What: The inverse of a primitive Dirichlet character is primitive.
- How: Unfolds `IsPrimitive` (conductor = level) and rewrites by `DirichletCharacter.conductor_inv` (conductor is invariant under inversion).
- Hypotheses: `θ` a primitive ℂ-valued Dirichlet character mod `N`.
- Uses from project: []
- Used by: `gaussSum_inv_ne_zero`, `LSeries_eq_gaussSum_inv_mul_sum`
- Visibility: private
- Lines: 179–183 (proof 2 lines)
- Notes: `omit [NeZero N]`; no sorry/set_option.

### lemma gaussSum_inv_ne_zero
- Type: `{θ : DirichletCharacter ℂ N} (hθ : θ.IsPrimitive) {ε : ℂ} (hε : IsPrimitiveRoot ε N) : gaussSum θ⁻¹ (AddChar.zmodChar N hε.pow_eq_one) ≠ 0`
- What: For a primitive character `θ` and a primitive `N`-th root of unity `ε`, the Gauss sum of `θ⁻¹` against the standard additive character is nonzero.
- How: By contradiction. Uses `gaussSum_mul_gaussSum_inv` (the product `G(χ)·G(χ̄) = N` for primitive `χ` and a primitive additive character, here via `isPrimitive_inv` and `AddChar.zmodChar_primitive_of_primitive_root`); if the Gauss sum were zero the product would be `0 = N`, contradicting `NeZero (N : ℂ)`.
- Hypotheses: `θ` primitive; `ε` a primitive `N`-th root of unity.
- Uses from project: `isPrimitive_inv`
- Used by: `LSeries_eq_gaussSum_inv_mul_sum`
- Visibility: private
- Lines: 185–193 (proof 7 lines)
- Notes: none.

### theorem LSeries_eq_gaussSum_inv_mul_sum
- Type: `{θ : DirichletCharacter ℂ N} (hθ : θ.IsPrimitive) {ε : ℂ} (hε : IsPrimitiveRoot ε N) {s : ℂ} (hs : 1 < s.re) : LSeries (fun n => θ n) s = (gaussSum θ⁻¹ (AddChar.zmodChar N hε.pow_eq_one))⁻¹ * ∑ c : (ZMod N)ˣ, θ⁻¹ c * LSeries (fun n => ε^(n*c.val)) s`
- What: Gauss-sum / finite-Fourier rearrangement of the Dirichlet L-series of a primitive `θ` for `Re s > 1`: `L(θ,s) = G(θ⁻¹)⁻¹ · Σ_c θ⁻¹(c)·L(n ↦ εⁿᶜ, s)`.
- How: Sets `G = gaussSum θ⁻¹ ψ`, nonzero by `gaussSum_inv_ne_zero`. Proves the pointwise Fourier identity `θ(m)·G = Σ_c θ⁻¹(c)·ε^((m·c).val)` via `gaussSum_mulShift_of_isPrimitive` and restricting the sum to units (`Finset.sum_subset`, `MulChar.map_nonunit`). Shows each exponential series is `LSeriesSummable` (`LSeriesSummable_of_bounded_of_one_lt_re`, norm 1 via `IsPrimitiveRoot.norm'_eq_one`), reduces the exponent mod `N` (`pow_eq_pow_mod`, `ZMod.val_mul`), writes the coefficient as a scaled finite sum, then distributes with `LSeries_smul` and `LSeries_sum`.
- Hypotheses: `θ` primitive; `ε` a primitive `N`-th root of unity; `Re s > 1`.
- Uses from project: `isPrimitive_inv`, `gaussSum_inv_ne_zero`
- Used by: `LFunction_one_eq`
- Visibility: public
- Lines: 195–248 (proof ~44 lines)
- Notes: long(30-50); no sorry/set_option.

### lemma rpow_neg_sub_le
- Type: `{a s : ℝ} (ha : 0 < a) (hs : 1 ≤ s) : a^(-s) - (a+1)^(-s) ≤ s * a^(-s-1)`
- What: A mean-value bound for the decay of `x ↦ x^(-s)`: the forward difference over a unit step is bounded by `s·a^(-s-1)`.
- How: Mean Value Theorem via `exists_hasDerivAt_eq_slope` on `x^(-s)` with derivative `-s·x^(-s-1)` (`Real.hasDerivAt_rpow_const`), giving a midpoint `ξ ∈ (a, a+1)`; then `ξ^(-s-1) ≤ a^(-s-1)` since the exponent is negative (`Real.rpow_le_rpow_of_nonpos`), and `nlinarith`/`mul_le_mul_of_nonneg_left` finishes.
- Hypotheses: `a > 0`, `s ≥ 1` (real).
- Uses from project: []
- Used by: `tendsto_LSeries_pow_boundary`
- Visibility: private
- Lines: 250–269 (proof ~19 lines)
- Notes: none.

### lemma tendsto_LSeries_pow_boundary
- Type: `{w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) : Filter.Tendsto (fun s : ℝ => LSeries (fun n => w^n) (s:ℂ)) (nhdsWithin 1 (Set.Ioi 1)) (nhds (-Complex.log (1 - w)))`
- What: Boundary limit of the geometric L-series: for `w` on the unit circle, `w ≠ 1`, the L-series `Σ wⁿ n^{-s}` tends to `−log(1−w)` as `s → 1⁺` along reals.
- How: Summation-by-parts (`Finset.sum_range_by_parts`, identity `hSBP`) rewrites partial sums in terms of the differences `d s n = (n+1)^{-s} − (n+2)^{-s}` and the bounded partial sums `B n` of `wⁿ⁺¹` (`‖B n‖ ≤ 2/‖1−w‖` via `geom_sum_eq`). A uniform summable dominating bound `u n` (from `rpow_neg_sub_le` and `Real.summable_nat_rpow_inv`) gives a function `g s = Σ d_s(n)·B(n+1)`; `hpartial` shows partial L-sums tend to `g s` (boundary term → 0 by `squeeze_zero_norm` + `tendsto_rpow_neg_atTop`). For `s>1`, `g s = L(wⁿ, s)` (`hg_eq`); at `s=1`, `g 1 = −log(1−w)` (`hg_one`, via `tendsto_sum_pow_div_eq_neg_log`); `g` is continuous on `[1,2]` (`continuousOn_tsum`), so `Tendsto.congr'` transfers the limit to `s → 1⁺`.
- Hypotheses: `w` complex with norm 1 and `w ≠ 1`.
- Uses from project: `rpow_neg_sub_le`, `tendsto_sum_pow_div_eq_neg_log`
- Used by: `LFunction_one_eq`
- Visibility: private
- Lines: 271–415 (proof ~144 lines)
- Notes: OVER-50 (needs /decompose-proof); no sorry/set_option.

### theorem LFunction_one_eq
- Type: `{θ : DirichletCharacter ℂ N} (hθ : θ.IsPrimitive) (hθ1 : θ ≠ 1) {ε : ℂ} (hε : IsPrimitiveRoot ε N) : LFunction θ 1 = -(gaussSum θ⁻¹ (AddChar.zmodChar N hε.pow_eq_one))⁻¹ * ∑ c : (ZMod N)ˣ, θ⁻¹ c * Complex.log (1 - ε^c.val)`
- What: **RJW Theorem 6.1(i)** / Washington Thm 4.9 — the closed form `L(θ,1) = −G(θ⁻¹)⁻¹ Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·log(1−ε_N^c)` for a nontrivial primitive character `θ` and a primitive `N`-th root of unity `ε`.
- How: Establishes `1 < N` (else `θ = 1` by `DirichletCharacter.level_one'`). Takes the limit `s → 1⁺` of two equal functions of `s`: the L-function `LFunction θ s` (continuous at 1 since `θ ≠ 1`, via `differentiable_LFunction`) and the Gauss-sum/Fourier expression. For each unit `c`, `tendsto_LSeries_pow_boundary` (applied to `w = ε^c.val`, which has norm 1 by `IsPrimitiveRoot.norm'_eq_one` and `≠ 1` by `hε.pow_eq_one_iff_dvd`) gives the boundary value `−log(1−ε^c)`; the two functions agree for `Re s > 1` by `LFunction_eq_LSeries` and `LSeries_eq_gaussSum_inv_mul_sum`. Concludes with `tendsto_nhds_unique` and `ring`.
- Hypotheses: `θ` primitive and nontrivial (`θ ≠ 1`); `ε` a primitive `N`-th root of unity.
- Uses from project: `LSeries_eq_gaussSum_inv_mul_sum`, `tendsto_LSeries_pow_boundary`
- Used by: unused in file (top-level result)
- Visibility: public
- Lines: 417–466 (proof ~48 lines)
- Notes: long(30-50); no sorry/set_option.

---

## File Summary

- **Total declarations: 7** — defs 0 / lemmas+theorems 7 (4 `theorem` + 3 `lemma`) / instances 0. (No structures/classes/abbrevs/inductives; one local `haveI : Fact (1 < N)` inside a proof, not a top-level decl.)
- **Key API (used by ≥3 in-file): none.** Most-used internal lemma is `isPrimitive_inv` (used by 2). The file is a short dependency chain culminating in `LFunction_one_eq`.
- **Unused in file (no in-file consumer):** `gaussSum_mul_coprime` (public, no project caller here), `LFunction_one_eq` (top-level result).
- **Decls with `sorry`: none.**
- **`set_option`: none.** One `omit [NeZero N]` (on `isPrimitive_inv`); no `sorry`/`TODO`/`admit`.
- **Proofs > 50 lines (2):** `tendsto_sum_pow_div_eq_neg_log` (~84), `tendsto_LSeries_pow_boundary` (~144). Both flagged OVER-50 → candidates for `/decompose-proof`.
- **Proofs 30–50 lines (3):** `gaussSum_mul_coprime` (~44), `LSeries_eq_gaussSum_inv_mul_sum` (~44), `LFunction_one_eq` (~48).
