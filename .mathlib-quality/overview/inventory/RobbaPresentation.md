# RobbaPresentation.lean — inventory (part 1: lines 1-1700)

Source: `projects/AdicSpaces/Adic spaces/FarguesFontaine/RobbaPresentation.lean`
(6578 lines total; this part covers declarations whose definition starts in lines 1–1700).

Ambient context for the whole file: `namespace FarguesFontaine`, `noncomputable section`,
`set_option linter.overlappingInstances false` (file-level, L26).
Section variables: `p` prime, `F` a perfectoid field of char `p`, `ϖ` a pseudo-uniformizer,
and radii `ρ₁ ρ₂ : NNReal` with `0 < ρᵢ < 1` (all implicit).

---

### `theorem wI_resIHom_le`
- **Type**: `{θ η : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hσ₁0 hσ₁1 hσ₂0 hσ₂1 : …) (z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1 (resIHom … z) ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 z`
- **What**: The interval-restriction ring map `resIHom` from the annulus ring `B^I` to a sub-annulus `B^{I'}` does not increase the interval Gauss norm `wI`.
- **How**: `wI` is a max of the two endpoint valuations, so `max_le` reduces to one bound per coordinate; each is exactly `valued_resI_le_wI` applied at the interpolation parameter `θ` (resp. `η`).
- **Hypotheses**: `θ, η ∈ [0,1]` (the sub-interval endpoints are log-interpolants `ρ₁^θ ρ₂^{1-θ}` of the ambient ones), and those interpolants lie in `(0,1)`.
- **Uses from project**: `valued_resI_le_wI`
- **Used by**: L5733 (part 4)
- **Visibility**: public
- **Lines**: 39–55 (proof 3 lines)
- **Notes**: []

### `theorem BISub_coe_add`
- **Type**: `{σ₁ σ₂ : NNReal} {h1 h2 h3 h4} (x y : ↥(BISub p F ϖ h1 h2 h3 h4)) : ((x + y : ↥(BISub …)) : hatK × hatK) = (x : _) + (y : _)`
- **What**: The subring coercion `B^I ↪ hatK(σ₁) × hatK(σ₂)` is additive, stated as a bare equation.
- **How**: `rfl` — the subtype addition is definitionally the ambient addition.
- **Hypotheses**: `0 < σ₁ < 1`, `0 < σ₂ < 1`.
- **Uses from project**: `BISub`, `hatK`
- **Used by**: L323 (`evalBITerm_add`), L1627 (`wIRPS_add_le`), L5555 (part 4)
- **Visibility**: public
- **Lines**: 57–67 (proof: `rfl`)
- **Notes**: Docstring explicitly says it is kept standalone so heavy contexts rewrite rather than pay the defeq check.

### `theorem isRestricted_iff_wI`
- **Type**: `{k : ℕ} (f : MvPowerSeries (Fin k) ↥(BISub p F ϖ …)) : MvPowerSeries.IsRestricted f ↔ ∀ ε : NNReal, 0 < ε → {s | ε < wI … (coeff s f)}.Finite`
- **What**: A multivariate power series over the annulus ring `B^I` is restricted (coefficients tend to `0` along the cofinite filter) exactly when, for every positive `ε`, only finitely many coefficients have interval Gauss norm above `ε`.
- **How**: Forward: the `wI`-ball of radius `ε` is a neighbourhood of `0` (`wI_ball_mem_nhds_BISub`), so restrictedness makes its preimage cofinite; unfold `Filter.mem_cofinite` and take the complement. Backward: every neighbourhood of `0` in the subtype contains a `wI`-ball by `exists_wI_ball_subset` (via `nhds_subtype_eq_comap` and `Filter.mem_comap`), and the hypothesis makes the exceptional set finite.
- **Hypotheses**: none beyond the ambient radii being in `(0,1)`.
- **Uses from project**: `wI`, `BISub`, `hatK`, `wI_ball_mem_nhds_BISub`, `exists_wI_ball_subset`
- **Used by**: L118 (`tendsto_wI_coeffSeq`), L488 (`bddAbove_wIRPS`), L704 (`isRestricted_column_limits`), L779, L3025 (part 2)
- **Visibility**: public
- **Lines**: 69–106 (proof 29 lines)
- **Notes**: >30-line declaration; the `wI`-ball ↔ neighbourhood-basis translation is the whole content.

### `theorem tendsto_wI_coeffSeq`
- **Type**: `{f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ …)} (hf : MvPowerSeries.IsRestricted f) : Filter.Tendsto (fun n => wI … (coeffSeq f n)) atTop (nhds 0)`
- **What**: For a restricted one-variable series over `B^I`, the sequence of coefficient interval norms tends to `0`.
- **How**: By `tendsto_order`, only the upper half matters; for `δ > 0` apply `isRestricted_iff_wI` at `δ/2`, pull the finite exceptional set back along the injection `n ↦ Finsupp.single 0 n`, take an upper bound `N` of that finite set, and conclude every `n > N` has norm `≤ δ/2 < δ` (`NNReal.half_lt_self`).
- **Hypotheses**: `f` restricted; one variable (`Fin 1`).
- **Uses from project**: `isRestricted_iff_wI`, `coeffSeq`, `wI`, `BISub`, `hatK`
- **Used by**: L221 (`tendsto_wI_evalBITerm`), L236, L247, L261, L2697, L2735 (part 2), L3343, L3356 (part 2)
- **Visibility**: public
- **Lines**: 108–134 (proof 19 lines)
- **Notes**: >10-line proof; `Finsupp.single_injective` supplies the injectivity for `Set.Finite.preimage`.

### `theorem exists_evalBI_series`
- **Type**: `{σ₁ σ₂ …} (φ : ↥(BISub p F ϖ hρ…) →+* ↥(BISub p F ϖ hσ…)) (hφ : ∀ z, wI (φ z) ≤ wI z) (a : ℕ → ↥(BISub p F ϖ hρ…)) (ha : Tendsto (wI ∘ a) atTop (nhds 0)) {b} (hbmem : b ∈ BISub …) (hb : wI b ≤ 1) : ∃ S ∈ BISub …, Tendsto (fun n => ∑ l ∈ range n, φ (a l) * b ^ l) atTop (nhds S)`
- **What**: The abstract convergence engine: if the coefficients `a l` have norms tending to `0` and `φ` is norm-contracting into the target annulus ring, then `∑ φ(a l) · b^l` converges in `B^{I'}` at any power-bounded `b`.
- **How**: Feed `exists_BI_series_limit` with the term sequence and the majorant `C l := wI (a l)`; the termwise bound is `wI_mul_le` followed by `wI_pow` plus `pow_le_one₀ hb` (so `wI (b^l) ≤ 1`) and then the contraction hypothesis `hφ`.
- **Hypotheses**: `φ` a ring hom contracting `wI`; `a` norm-null; `b` in the annulus subring with `wI b ≤ 1` (power-bounded).
- **Uses from project**: `exists_BI_series_limit`, `wI_mul_le`, `wI_pow`, `wI`, `BISub`, `hatK`
- **Used by**: L233 (`evalBI`), L244 (`evalBI_mem`), L258 (`tendsto_evalBI`)
- **Visibility**: public
- **Lines**: 136–188 (proof 25 lines)
- **Notes**: >30-line declaration; the statement's `∃ S` is the choice source for `evalBI`.

### `def evalBITerm`
- **Type**: `(b : hatK × hatK) (f : MvPowerSeries (Fin 1) ↥(BISub p F ϖ hρ…)) (l : ℕ) : hatK × hatK`
- **What**: The `l`-th term `φ(coeffSeq f l) · b^l` of the evaluation series of `f` at `b`.
- **How**: Direct definition — coerce `φ` applied to the `l`-th coefficient into the product of completions and multiply by `b^l`.
- **Hypotheses**: ambient `φ`; no contraction needed for the definition itself.
- **Uses from project**: `coeffSeq`, `BISub`, `hatK`
- **Used by**: L255 (`tendsto_evalBI`), L280+ (`evalBITerm_add`), L348 (`evalBITerm_mul_sum`), L413/L427/L441 (`evalBI_one`, `evalBI_zero`), L1563/L1570 (`evalBI_monomial`), L3303+ (part 2), L4268+ (part 3)
- **Visibility**: public
- **Lines**: 197–202 (definition 2 lines)
- **Notes**: Opens `section EvalBI` (L190) with `variable`s `σ₁ σ₂`, `φ`, and later the contraction hypothesis `hφ` (L204).

### `theorem tendsto_wI_evalBITerm`
- **Type**: `{f : MvPowerSeries (Fin 1) ↥(BISub …)} (hf : IsRestricted f) : Tendsto (fun l => wI (φ (coeffSeq f l))) atTop (nhds 0)`
- **What**: For a restricted series, the norms of the transported coefficients `φ(coeffSeq f l)` tend to `0`.
- **How**: Squeeze between the constant `0` and `tendsto_wI_coeffSeq`, using the contraction hypothesis `hφ` termwise.
- **Hypotheses**: `hφ` (included), `f` restricted.
- **Uses from project**: `tendsto_wI_coeffSeq`, `coeffSeq`, `wI`, `BISub`, `hatK`
- **Used by**: L395–396 (`evalBI_mul`)
- **Visibility**: public
- **Lines**: 211–222 (proof 3 lines, term mode)
- **Notes**: `include hφ in`.

### `def evalBI`
- **Type**: `{b} (hbmem : b ∈ BISub …) (hb : wI b ≤ 1) (f : ↥(restrictedMvPowerSeriesSubring 1 ↥(BISub p F ϖ hρ…))) : hatK × hatK`
- **What**: The value at `b` of a restricted one-variable series over `B^I`, transported through the contracting hom `φ` — i.e. the sum of the evaluation series.
- **How**: `Exists.choose` of `exists_evalBI_series`, applied to `coeffSeq f` with the null-norm hypothesis supplied by `tendsto_wI_coeffSeq` from `f.2`.
- **Hypotheses**: `hφ` (included); `b` power-bounded in the target annulus ring.
- **Uses from project**: `exists_evalBI_series`, `tendsto_wI_coeffSeq`, `coeffSeq`, `restrictedMvPowerSeriesSubring`, `BISub`, `hatK`, `wI`
- **Used by**: pervasively — L238+, L249+, L331+, L378+, L404+, L434+, L453 (`evalBIHom`), and throughout parts 2–4
- **Visibility**: public
- **Lines**: 224–236 (definition 4 lines)
- **Notes**: Noncomputable (choice); its three specification lemmas follow immediately.

### `theorem evalBI_mem`
- **Type**: `… : evalBI p F ϖ φ hφ hbmem hb f ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1`
- **What**: The evaluation lands in the target annulus subring `B^{I'}`.
- **How**: First component of the `choose_spec` of `exists_evalBI_series`.
- **Hypotheses**: same as `evalBI`.
- **Uses from project**: `exists_evalBI_series`, `tendsto_wI_coeffSeq`, `evalBI`, `BISub`
- **Used by**: L459 (`evalBIHom`), L1984 (part 2), L5021 (part 4)
- **Visibility**: public
- **Lines**: 238–247 (proof: term-mode projection)
- **Notes**: []

### `theorem tendsto_evalBI`
- **Type**: `… : Tendsto (fun n => ∑ l ∈ Finset.range n, evalBITerm p F ϖ φ b f l) atTop (nhds (evalBI p F ϖ φ hφ hbmem hb f))`
- **What**: The partial sums of the evaluation series converge to `evalBI f` — the defining characterisation.
- **How**: Second component of the `choose_spec` of `exists_evalBI_series`.
- **Hypotheses**: same as `evalBI`.
- **Uses from project**: `exists_evalBI_series`, `tendsto_wI_coeffSeq`, `evalBITerm`, `evalBI`
- **Used by**: L338–340 (`evalBI_add`), L385/L397–398 (`evalBI_mul`), L408 (`evalBI_one`), L438 (`evalBI_zero`), L885 (`wI_evalBI_le`), L1558 (`evalBI_monomial`), L3300 (part 2), L4265 (part 3)
- **Visibility**: public
- **Lines**: 249–261 (proof: term-mode projection)
- **Notes**: This is the workhorse: every algebraic property of `evalBI` is proved by `tendsto_nhds_unique` against this.

### `theorem evalBI_carrier_sum`
- **Type**: `{ι : Type*} (s : Finset ι) (a : ι → ↥(BISub p F ϖ hρ…)) : φ (∑ i ∈ s, a i) = ∑ i ∈ s, φ (a i)`
- **What**: A ring hom between annulus subrings commutes with finite sums.
- **How**: `Finset.induction` using `φ.map_zero` and `φ.map_add`; stated separately (per the docstring) to avoid typeclass search on the nested subring types that `map_sum` would trigger.
- **Hypotheses**: none beyond `φ` being a ring hom.
- **Uses from project**: `BISub`
- **Used by**: L371 (`evalBITerm_mul_sum`)
- **Visibility**: public
- **Lines**: 263–274 (proof 7 lines)
- **Notes**: Re-proves `map_sum` for performance reasons.

### `theorem evalBITerm_add`
- **Type**: `(b) (f g : ↥(restrictedMvPowerSeriesSubring 1 ↥(BISub …))) (l : ℕ) : evalBITerm φ b (f + g) l = evalBITerm φ b f l + evalBITerm φ b g l`
- **What**: The `l`-th evaluation term is additive in the series.
- **How**: `coeffSeq_add` gives additivity of coefficient extraction, `φ.map_add` transports it, `BISub_coe_add` pushes the sum through the subring coercion, and `add_mul` distributes over `b^l`.
- **Hypotheses**: none beyond ambient `φ`.
- **Uses from project**: `coeffSeq_add`, `BISub_coe_add`, `evalBITerm`, `coeffSeq`, `BISub`, `hatK`, `restrictedMvPowerSeriesSubring`
- **Used by**: L342 (`evalBI_add`)
- **Visibility**: public
- **Lines**: 276–328 (proof 42 lines)
- **Notes**: >30 lines; length is entirely coercion bookkeeping in an explicit `calc` with `congrArg` steps (elaboration-cost avoidance, not mathematics).

### `theorem evalBI_add`
- **Type**: `{b} (hbmem) (hb) (f g : ↥(restrictedMvPowerSeriesSubring 1 ↥(BISub …))) : evalBI (f + g) = evalBI f + evalBI g`
- **What**: Evaluation of restricted series is additive.
- **How**: `tendsto_nhds_unique` against `tendsto_evalBI` at `f + g`, comparing with the sum of the two partial-sum limits; termwise equality is `evalBITerm_add` under `Finset.sum_add_distrib`.
- **Hypotheses**: `hφ`; `b` power-bounded in `B^{I'}`.
- **Uses from project**: `tendsto_evalBI`, `evalBITerm_add`, `evalBI`
- **Used by**: L463 (`evalBIHom`), L930 (`wI_z_sub_evalBI_add_le`), L1705 (`evalBI_finset_sum`), L2019 (part 2), L3510 (part 2), L4381 (part 3), L5056 (part 4)
- **Visibility**: public
- **Lines**: 330–342 (proof 5 lines)
- **Notes**: []

### `theorem evalBITerm_mul_sum`
- **Type**: `(b) (f g) (l : ℕ) : evalBITerm φ b (f * g) l = (∑ q ∈ Finset.antidiagonal l, φ (coeffSeq f q.1) * φ (coeffSeq g q.2)) * b ^ l`
- **What**: The `l`-th evaluation term of a product is the antidiagonal (Cauchy) convolution of the transported coefficients, times `b^l`.
- **How**: `coeffSeq_mul` gives the convolution formula for the coefficient, `evalBI_carrier_sum` pushes `φ` through the finite sum, `AddSubmonoidClass.coe_finsetSum` through the coercion, and `φ.map_mul` splits each product.
- **Hypotheses**: none beyond ambient `φ`.
- **Uses from project**: `coeffSeq_mul`, `evalBI_carrier_sum`, `evalBITerm`, `coeffSeq`, `BISub`, `hatK`
- **Used by**: L401 (`evalBI_mul`)
- **Visibility**: public
- **Lines**: 344–374 (proof 15 lines)
- **Notes**: >10-line proof; declaration spans >30 lines mostly from explicit coercions.

### `theorem evalBI_mul`
- **Type**: `{b} (hbmem) (hb) (f g) : evalBI (f * g) = evalBI f * evalBI g`
- **What**: Evaluation is multiplicative — the Cauchy product converges to the product of the limits at the target radii.
- **How**: `tendsto_nhds_unique` against `tendsto_evalBI` at `f * g`, matched with `tendsto_cauchy_product` fed the two transported coefficient sequences (null-norm by `tendsto_wI_evalBITerm`) and their partial-sum limits (`tendsto_evalBI`); termwise reconciliation is `evalBITerm_mul_sum`.
- **Hypotheses**: `hφ`; `wI b ≤ 1` (needed by `tendsto_cauchy_product` for the geometric control).
- **Uses from project**: `tendsto_evalBI`, `tendsto_cauchy_product`, `tendsto_wI_evalBITerm`, `evalBITerm_mul_sum`, `coeffSeq`, `evalBI`
- **Used by**: L461 (`evalBIHom`), L3727 (part 2), L5422 (part 4)
- **Visibility**: public
- **Lines**: 376–401 (proof 17 lines)
- **Notes**: >10-line proof; the mathematical content is delegated to `tendsto_cauchy_product`.

### `theorem evalBI_one`
- **Type**: `{b} (hbmem) (hb) : evalBI p F ϖ φ hφ hbmem hb 1 = 1`
- **What**: Evaluation sends the constant series `1` to `1`.
- **How**: `tendsto_nhds_unique` against `tendsto_evalBI` and the constant sequence: `coeffSeq_one` makes every term `if l = 0 then 1 else 0`, and `Finset.sum_ite_eq'` collapses the partial sum to `1` for `n ≥ 1`.
- **Hypotheses**: `hφ`; `b` power-bounded.
- **Uses from project**: `tendsto_evalBI`, `evalBITerm`, `coeffSeq_one`, `evalBI`
- **Used by**: L460 (`evalBIHom`)
- **Visibility**: public
- **Lines**: 403–431 (proof 24 lines)
- **Notes**: >10-line proof; eventual-equality (`Filter.eventually_atTop` from `n = 1`) rather than pointwise.

### `theorem evalBI_zero`
- **Type**: `{b} (hbmem) (hb) : evalBI p F ϖ φ hφ hbmem hb 0 = 0`
- **What**: Evaluation sends `0` to `0`.
- **How**: `tendsto_nhds_unique` against `tendsto_evalBI` and `tendsto_const_nhds`; every term vanishes since `coeffSeq_zero` and `φ.map_zero` give a zero factor.
- **Hypotheses**: `hφ`; `b` power-bounded.
- **Uses from project**: `tendsto_evalBI`, `evalBITerm`, `coeffSeq_zero`, `evalBI`
- **Used by**: L462 (`evalBIHom`), L1702 (`evalBI_finset_sum`), L2004 (part 2), L5041 (part 4)
- **Visibility**: public
- **Lines**: 433–447 (proof 10 lines)
- **Notes**: []

### `def evalBIHom`
- **Type**: `{b} (hbmem : b ∈ BISub …) (hb : wI b ≤ 1) : ↥(restrictedMvPowerSeriesSubring 1 ↥(BISub p F ϖ hρ…)) →+* ↥(BISub p F ϖ hσ…)`
- **What**: **The Robba-localization presentation map** `B^I⟨T⟩ →+* B^{I'}`, `T ↦ b` — Kedlaya Lemma 4.9 case 1/2, generic in the contracting coefficient carrier `φ`.
- **How**: Bundle `evalBI` (landing in the subring by `evalBI_mem`) with the four ring-hom axioms supplied by `evalBI_one`, `evalBI_mul`, `evalBI_zero`, `evalBI_add`, each wrapped in `Subtype.ext`.
- **Hypotheses**: `hφ` (`φ` contracts `wI`); `b` in the target annulus ring and power-bounded.
- **Uses from project**: `evalBI`, `evalBI_mem`, `evalBI_one`, `evalBI_mul`, `evalBI_zero`, `evalBI_add`, `restrictedMvPowerSeriesSubring`, `BISub`
- **Used by**: L3431+, L3505+, L3553, L3575, L3603, L3682 (part 2), L4304+, L4376+, L4398, L4420, L4447 (part 3), L5377, L6446 (part 4)
- **Visibility**: public
- **Lines**: 449–463 (definition 6 lines)
- **Notes**: `include hφ in`; closes `section EvalBI` at L465. This is the headline export named in the module docstring.

---

## Section: The interval Gauss norm on restricted series (T910 P3 substrate) — L468

Section variable added here: `{k : ℕ}` (number of variables).

### `def wIRPS`
- **Type**: `(hρ₁0 hρ₁1 hρ₂0 hρ₂1) (f : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ…)) : NNReal`
- **What**: The interval Gauss norm of a power series over `B^I` with radius-1 variables: `⨆ s, wI (coeff s f)`.
- **How**: Direct definition as an indexed supremum over multi-indices of the coefficient interval norms.
- **Hypotheses**: radii in `(0,1)`; no restrictedness (the `⨆` is junk-valued when unbounded, whence `bddAbove_wIRPS`).
- **Uses from project**: `wI`, `BISub`, `hatK`
- **Used by**: pervasive — L512, L517, L680, L786+, L918, L1599, L1623–1625, L1638+, and throughout parts 2–4
- **Visibility**: public
- **Lines**: 472–478 (definition 3 lines)
- **Notes**: The central norm of the second half of the file.

### `theorem bddAbove_wIRPS`
- **Type**: `{f} (hf : MvPowerSeries.IsRestricted f) : BddAbove (Set.range (fun s => wI (coeff s f)))`
- **What**: The coefficient norms of a restricted series are bounded above, so the supremum defining `wIRPS` is genuine.
- **How**: Apply `isRestricted_iff_wI` at `ε = 1`: only finitely many coefficients exceed `1`, so `max 1 (Finset.sup …)` over that finite exceptional set is an upper bound; split on `wI (coeff s f) ≤ 1` or not and use `Finset.le_sup`.
- **Hypotheses**: `f` restricted.
- **Uses from project**: `isRestricted_iff_wI`, `wI`, `BISub`, `hatK`
- **Used by**: L513 (`wI_coeff_le_wIRPS`), L1614, L2303/L2313 (part 2), L2685/L2723 (part 2)
- **Visibility**: public
- **Lines**: 480–503 (proof 16 lines)
- **Notes**: >10-line proof; `Set.Finite.toFinset` converts the exceptional set to a `Finset` for `sup`.

### `theorem wI_coeff_le_wIRPS`
- **Type**: `{f} (hf : IsRestricted f) (s : Fin k →₀ ℕ) : wI (coeff s f) ≤ wIRPS p F ϖ … f`
- **What**: Every coefficient norm is bounded by the interval Gauss norm.
- **How**: `le_ciSup` with boundedness from `bddAbove_wIRPS`.
- **Hypotheses**: `f` restricted.
- **Uses from project**: `bddAbove_wIRPS`, `wIRPS`, `wI`
- **Used by**: L561, L827, L926, L1629–1630, L2319/L2321 (part 2), L6234–6235, L6350 (part 4)
- **Visibility**: public
- **Lines**: 505–513 (proof 1 line)
- **Notes**: []

### `theorem wIRPS_zero`
- **Type**: `wIRPS p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (0 : MvPowerSeries (Fin k) ↥(BISub …)) = 0`
- **What**: The interval Gauss norm of the zero series is `0`.
- **How**: `ciSup_le` reduces to each coefficient, which is `0` by `map_zero`, and `wI_zero` gives norm `0`.
- **Hypotheses**: none.
- **Uses from project**: `wIRPS`, `wI_zero`, `BISub`, `hatK`
- **Used by**: L1655 (`wIRPS_finset_sum_le`), L6372 (part 4)
- **Visibility**: public
- **Lines**: 515–524 (proof 6 lines)
- **Notes**: []

### `theorem exists_BI_coeff_column_limit`
- **Type**: `{u : ℕ → ↥(restrictedMvPowerSeriesSubring k ↥(BISub …))} {C : ℕ → NNReal} (hC : ∀ l, wIRPS (u l) ≤ C l) (hC0 : Tendsto C atTop (nhds 0)) (K : Fin k →₀ ℕ) : ∃ S ∈ BISub …, Tendsto (fun n => ∑ l ∈ range n, coeff K (u l)) atTop (nhds S)`
- **What**: For a series of restricted series whose Gauss norms are dominated by a null sequence `C`, each fixed coefficient column `K` sums to an element of `B^I`.
- **How**: Apply the interval-ring completeness engine `exists_BI_series_limit` to the column sequence, with majorant `C`; the termwise bound is `wI_coeff_le_wIRPS` on `u l` composed with `hC l`.
- **Hypotheses**: uniform Gauss-norm domination by a null `C`; each `u l` restricted (carried in the subring type).
- **Uses from project**: `exists_BI_series_limit`, `wI_coeff_le_wIRPS`, `wIRPS`, `restrictedMvPowerSeriesSubring`, `BISub`, `hatK`
- **Used by**: unused in file (exported building block; see `exists_rps_series_limit_BI` which re-derives via `exists_wI_series_limit`)
- **Visibility**: public
- **Lines**: 526–561 (proof 14 lines)
- **Notes**: >30-line declaration; >10-line proof.

### `theorem exists_wI_series_limit`
- **Type**: `{u : ℕ → ↥(BISub …)} {C : ℕ → NNReal} (hC : ∀ l, wI (u l) ≤ C l) (hC0 : Tendsto C atTop (nhds 0)) : ∃ S : ↥(BISub …), ∀ n b, 0 < b → (∀ l ≥ n, C l ≤ b) → wI (S - ∑ l ∈ range n, u l) ≤ b`
- **What**: The residual (tail-estimate) form of series convergence in `B^I`: a `wI`-dominated series has a sum whose distance to every partial sum obeys the corresponding eventual bound on `C`.
- **How**: Get the limit `Sp` from `exists_BI_series_limit`; the tails `∑_{range m} - ∑_{range n}` equal `∑_{Ico n m}` (`Finset.sum_Ico_eq_sub`), each of which lies in the closed `wI`-ball of radius `b` by the ultrametric `wI_sum_le`; conclude by `isClosed_wI_ball.mem_of_tendsto` applied to `htend.sub_const`.
- **Hypotheses**: termwise domination `wI (u l) ≤ C l` with `C → 0`.
- **Uses from project**: `exists_BI_series_limit`, `isClosed_wI_ball`, `wI_sum_le`, `wI`, `BISub`, `hatK`
- **Used by**: L821 (`exists_rps_series_limit_BI`)
- **Visibility**: public
- **Lines**: 563–609 (proof 31 lines)
- **Notes**: >30 lines; the "residual form" is what makes columnwise restrictedness (`isRestricted_column_limits`) provable.

### `theorem RPS_BI_coe_sub`
- **Type**: `(a b : ↥(restrictedMvPowerSeriesSubring k ↥(BISub …))) : ((a - b : _) : MvPowerSeries …) = (a : _) - (b : _)`
- **What**: The coercion from the restricted-series subring to all power series commutes with subtraction.
- **How**: `rfl` (subring subtraction is the ambient one).
- **Hypotheses**: none.
- **Uses from project**: `restrictedMvPowerSeriesSubring`, `BISub`
- **Used by**: L851 (`exists_rps_series_limit_BI`)
- **Visibility**: public
- **Lines**: 611–620 (proof: `rfl`)
- **Notes**: Micro-lemma for rewriting in heavy contexts (same rationale as `BISub_coe_add`).

### `theorem coeff_sub_eq_BI`
- **Type**: `(y w : MvPowerSeries (Fin k) ↥(BISub …)) (K) : (coeff K (y - w) : hatK × hatK) = (coeff K y : _) - (coeff K w : _)`
- **What**: Taking the `K`-th coefficient of a difference and coercing to the product of completions is the difference of the coerced coefficients.
- **How**: `congrArg` of the subring coercion applied to `map_sub (MvPowerSeries.coeff K)`.
- **Hypotheses**: none.
- **Uses from project**: `BISub`, `hatK`
- **Used by**: L851 (`exists_rps_series_limit_BI`)
- **Visibility**: public
- **Lines**: 622–635 (proof: term mode, 3 lines)
- **Notes**: []

### `theorem coeff_partial_sum_BI`
- **Type**: `(u : ℕ → ↥(restrictedMvPowerSeriesSubring k ↥(BISub …))) (n) (K) : (coeff K (∑ l ∈ range n, u l) : hatK × hatK) = ∑ l ∈ range n, (coeff K (u l) : hatK × hatK)`
- **What**: Coefficient extraction of a finite partial sum of restricted series commutes with the sum, at the level of the product of completions.
- **How**: Two applications of `AddSubmonoidClass.coe_finsetSum` (once for the RPS subring coercion, once for the `B^I` coercion) with `map_sum` for `MvPowerSeries.coeff` in between.
- **Hypotheses**: none.
- **Uses from project**: `restrictedMvPowerSeriesSubring`, `BISub`, `hatK`
- **Used by**: L852 (`exists_rps_series_limit_BI`)
- **Visibility**: public
- **Lines**: 637–677 (proof 23 lines, all `rw [show … from …]`)
- **Notes**: >30-line declaration; length is coercion plumbing only.

### `theorem isRestricted_column_limits`
- **Type**: `{u : ℕ → ↥(restrictedMvPowerSeriesSubring k ↥(BISub …))} {C : ℕ → NNReal} (hC0 : Tendsto C atTop (nhds 0)) (S : (Fin k →₀ ℕ) → ↥(BISub …)) (hS : ∀ K n b, 0 < b → (∀ l ≥ n, C l ≤ b) → wI (S K - ∑ l ∈ range n, coeff K (u l)) ≤ b) : MvPowerSeries.IsRestricted (fun K => S K)`
- **What**: If each coefficient column of a `wIRPS`-vanishing series of restricted series converges with uniform tail estimates, the columnwise limit is again a restricted series.
- **How**: Via `isRestricted_iff_wI`: for `t > 0` pick `N` with `C l < t` for `l ≥ N`; the ultrametric inequality `wI_add_le` splits `S K` into (tail ≤ t) + (partial sum), so any `K` with `wI (S K) > t` forces `wI (∑_{range N} coeff K (u l)) > t`, and `wI_sum_le` then forces some single `l < N` to exceed `t`. The exceptional set is thus contained in a finite union of the (finite, by `isRestricted_iff_wI` on each `u l`) exceptional sets.
- **Hypotheses**: `C → 0`; the residual/tail estimate `hS` for every column.
- **Uses from project**: `isRestricted_iff_wI`, `wI_add_le`, `wI_sum_le`, `wI`, `BISub`, `hatK`, `restrictedMvPowerSeriesSubring`
- **Used by**: L829 (`exists_rps_series_limit_BI`)
- **Visibility**: public
- **Lines**: 679–783 (proof 82 lines)
- **Notes**: >30 lines — the longest proof so far in the file; two nested `by_contra … push Not` arguments.

### `theorem exists_rps_series_limit_BI`
- **Type**: `{u : ℕ → ↥(restrictedMvPowerSeriesSubring k ↥(BISub …))} {C : ℕ → NNReal} (hC : ∀ l, wIRPS (u l) ≤ C l) (hC0 : Tendsto C atTop (nhds 0)) : ∃ U, ∀ n b, 0 < b → (∀ l ≥ n, C l ≤ b) → wIRPS (U - ∑ l ∈ range n, u l) ≤ b`
- **What**: **Completeness of the `B^I`-Tate algebra for the Gauss norm**: a series of restricted series with Gauss norms dominated by a null sequence converges to a restricted series, with the corresponding tail estimates. This is the analytic engine behind the case-1/2 Robba-localization surjectivity.
- **How**: Column-by-column, `exists_wI_series_limit` (fed `wI_coeff_le_wIRPS` ∘ `hC`) produces limits `S K` with residual bounds; `choose` them, apply `isRestricted_column_limits` to see the assembled `fun K => S K` is restricted, then bound `wIRPS` of the residual by `ciSup_le` over columns, rewriting the coefficient of the difference via `RPS_BI_coe_sub`, `coeff_sub_eq_BI`, `coeff_partial_sum_BI`.
- **Hypotheses**: uniform Gauss-norm domination by a null `C`.
- **Uses from project**: `exists_wI_series_limit`, `wI_coeff_le_wIRPS`, `isRestricted_column_limits`, `RPS_BI_coe_sub`, `coeff_sub_eq_BI`, `coeff_partial_sum_BI`, `wIRPS`, `wI`, `BISub`, `hatK`, `restrictedMvPowerSeriesSubring`
- **Used by**: L2195 (part 2), L5232 (part 4)
- **Visibility**: public
- **Lines**: 785–855 (proof 50 lines)
- **Notes**: >30 lines; headline completeness statement of the P3 substrate.

### `theorem wI_evalBI_le`
- **Type**: `{b} (hbmem) (hb) (f) {ε : NNReal} (hε : 0 < ε) (hf : ∀ l, wI (coeffSeq f l) ≤ ε) : wI (evalBI p F ϖ φ hφ hbmem hb f) ≤ ε`
- **What**: The evaluation-value bound: if every coefficient of `f` has interval norm at most `ε`, so does the value `evalBI f`.
- **How**: The `wI`-ball of radius `ε` is closed (`isClosed_wI_ball`), so it suffices that every partial sum lies in it; by the ultrametric `wI_sum_le` this reduces to a single term, bounded via `wI_mul_le`, `hφ`, `hf l`, and `wI_pow`/`pow_le_one₀ hb` for the `b^l` factor.
- **Hypotheses**: `hφ` (contraction), `b` power-bounded, `0 < ε` (needed for the ball to be closed as stated).
- **Uses from project**: `isClosed_wI_ball`, `tendsto_evalBI`, `wI_sum_le`, `wI_mul_le`, `wI_pow`, `evalBI`, `coeffSeq`
- **Used by**: L925 (`wI_z_sub_evalBI_add_le`)
- **Visibility**: public
- **Lines**: 870–904 (proof 21 lines)
- **Notes**: >30-line declaration; opens `section EvalBIBounds` (L857) which re-declares `σ₁ σ₂`, `φ`, `hφ` as `variable`s.

### `theorem wI_z_sub_evalBI_add_le`
- **Type**: `{b} (hbmem) (hb) (z) (SS V : ↥(restrictedMvPowerSeriesSubring 1 ↥(BISub …))) {ε} (hε : 0 < ε) (h1 : wI (z - evalBI SS) ≤ ε) (h2 : wIRPS V ≤ ε) : wI (z - evalBI (SS + V)) ≤ ε`
- **What**: The residual estimate for a corrected approximation: adding a correction series `V` of small Gauss norm does not worsen an already-small residual `z - evalBI SS`.
- **How**: `wI_evalBI_le` (via `wI_coeff_le_wIRPS` on `V`) bounds `wI (evalBI V) ≤ ε`; `evalBI_add` splits `evalBI (SS + V)`, and the ultrametric `wI_add_le` with `wI_neg` finishes by `max_le`.
- **Hypotheses**: `hφ`; `b` power-bounded; `0 < ε`; both residual and correction bounded by `ε`.
- **Uses from project**: `wI_evalBI_le`, `wI_coeff_le_wIRPS`, `evalBI_add`, `wI_add_le`, `wI_neg`, `evalBI`, `wIRPS`
- **Used by**: L2221 (part 2), L5258 (part 4)
- **Visibility**: public
- **Lines**: 906–935 (proof 14 lines)
- **Notes**: >10-line proof; this is the induction step of the successive-approximation (Newton/telescoping) surjectivity argument. Closes `section EvalBIBounds` at L937.

---

## Section: The case-1/2 generator and the per-monomial twist (T910 P3d) — L940

### `def teichPowGen`
- **Type**: `(zb : OF F) (m : ℕ) : Bloc p F ϖ`
- **What**: **The case-1/2 Robba generator** `[z̄]/p^m ∈ B_loc` — the Teichmüller lift of `zb` divided by `p^m`; substituting `T ↦` this element cuts the annulus at radius `|z̄|^{1/m}`.
- **How**: `algebraMap (Ainf) (Bloc)` of `WittVector.teichmuller p zb`, multiplied by the `m`-th power of the inverse of the unit `p` in `B_loc` (`isUnit_p_image`).
- **Hypotheses**: none in the definition (the valuation conditions on `zb` appear in the lemmas).
- **Uses from project**: `Bloc`, `Ainf`, `isUnit_p_image`
- **Used by**: L963/L969 (`teichPowGen_pow_mul_twist`), and downstream in parts 2–4
- **Visibility**: public
- **Lines**: 942–946 (definition 3 lines)
- **Notes**: `p` is invertible in `B_loc`, which is what makes the negative power legal.

### `theorem algebraMap_p_pow_mul_vp_pow`
- **Type**: `(m : ℕ) : algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) ^ m) * (↑(isUnit_p_image p F ϖ).unit⁻¹) ^ m = 1`
- **What**: `p^m` and the `m`-th power of the inverse of `p` cancel in `B_loc`.
- **How**: From `IsUnit.unit.mul_inv` and `unit_spec` at exponent 1, then `map_pow`/`← mul_pow` to raise to the `m`-th power.
- **Hypotheses**: `p` invertible in `B_loc` (`isUnit_p_image`).
- **Uses from project**: `Ainf`, `Bloc`, `isUnit_p_image`
- **Used by**: L968 (`teichPowGen_pow_mul_twist`)
- **Visibility**: public
- **Lines**: 948–956 (proof 5 lines)
- **Notes**: []

### `theorem teichPowGen_pow_mul_twist`
- **Type**: `(zb : OF F) (m i j : ℕ) (c c' : OF F) (hc : c = zb ^ j * c') : teichPowGen p F ϖ zb m ^ j * algebraMap _ _ (p ^ (i + m*j) * teichmuller p c') = algebraMap _ _ (p ^ i * teichmuller p c)`
- **What**: **The exact per-monomial lift identity** (Kedlaya lines 546–551, substitution side): if the coordinate `c` is divisible by `zb^j`, then the Teichmüller monomial `p^i [c]` equals the `j`-th power of the generator times the "twisted" monomial `p^{i+mj} [c']`.
- **How**: Expand `teichPowGen` and use multiplicativity of `WittVector.teichmuller` on `c = zb^j c'`; the `p^{mj}` produced by `pow_add` cancels the `m j` inverse-`p` factors by `algebraMap_p_pow_mul_vp_pow`. The final rearrangement is a `generalize`d `ring`/`mul_one` calc (generalising to opaque names to keep the `ring` cheap).
- **Hypotheses**: `c = zb ^ j * c'` in `OF F`.
- **Uses from project**: `teichPowGen`, `algebraMap_p_pow_mul_vp_pow`, `Ainf`, `Bloc`, `isUnit_p_image`
- **Used by**: L1147+ (`mk'_monomial_twist_factor`) — via the monomial-twist chain
- **Visibility**: public
- **Lines**: 958–997 (proof 30 lines)
- **Notes**: >10-line proof; the five `generalize` steps are a deliberate elaboration-cost device before the closing `ring`.

### `theorem exists_twist`
- **Type**: `(zb c : OF F) (hzb0 : perfectoidValuation p F zb ≠ 0) (hzb1 : perfectoidValuation p F zb < 1) (hc0 : perfectoidValuation p F c ≠ 0) : ∃ (j : ℕ) (c' : OF F), c = zb ^ j * c' ∧ perfectoidValuation p F zb < perfectoidValuation p F c'`
- **What**: **The maximal-twist normalization** (Kedlaya's choice of `j`): a nonzero integral coordinate `c` factors as `zb^j · c'` with the cofactor's valuation strictly above `|zb|` — i.e. `j` is the exact `zb`-adic order.
- **How**: Since `|zb| < 1`, some power drops below `|c|` (`NNReal.exists_pow_lt_of_lt_one`), so `j := Nat.findGreatest (fun j => |c| ≤ |zb|^j) j₀` is well defined; `Nat.findGreatest_spec` gives `|c| ≤ |zb|^j`, whence divisibility by the valuation-ring criterion `(perfectoidValuation_integers p F).dvd_of_le`, and `Nat.findGreatest_is_greatest` gives `|zb|^{j+1} < |c| = |zb|^j |c'|`, so `|zb| < |c'|` by `lt_of_mul_lt_mul_left`.
- **Hypotheses**: `zb` nonzero with `|zb| < 1`; `c` nonzero.
- **Uses from project**: `perfectoidValuation`, `perfectoidValuation_le_one`, `perfectoidValuation_integers`, `OF`
- **Used by**: L1082 (`exists_twist_deep`)
- **Visibility**: public
- **Lines**: 999–1065 (proof 57 lines)
- **Notes**: >30 lines; contains both of the file's repeated boilerplate blocks (the `hval` multiplicativity block and the `algebraMap ↥(powerBoundedSubring.toSubring F) F` coercion block).

### `theorem exists_twist_deep`
- **Type**: `(zb c : OF F) (m : ℕ) (hm : 0 < m) (hzb0) (hzb1) (hc0) (i k : ℕ) (hcm : |c|^m ≤ |zb|^(k-i)) : ∃ (j : ℕ) (c' : OF F), c = zb ^ j * c' ∧ k < i + m*j + m ∧ |zb| < |c'|`
- **What**: **The twist reaches within one generator-step of the denominator**: under the `σ₁`-Gauss bound in `m`-th-power form, the maximal twist depth `j` from `exists_twist` additionally satisfies `i + m·j + m > k`, so the residual denominator dominance is strictly less than one generator step.
- **How**: Take `j` from `exists_twist`; maximality gives `|zb|^{j+1} < |c|`, so `|zb|^{m(j+1)} = (|zb|^{j+1})^m < |c|^m ≤ |zb|^{k-i}` by `pow_lt_pow_left₀`; since the base is `< 1`, `pow_le_pow_of_le_one` reverses the exponent comparison to `k - i < m(j+1)`, and `omega` converts to `k < i + m j + m`.
- **Hypotheses**: `0 < m`; `zb` nonzero with `|zb| < 1`; `c` nonzero; the multiplicative Gauss bound `hcm`.
- **Uses from project**: `exists_twist`, `perfectoidValuation`, `OF`
- **Used by**: L1198 (`exists_monomial_twist_data`)
- **Visibility**: public
- **Lines**: 1067–1115 (proof 34 lines)
- **Notes**: >30 lines; the "exponent reversal for a base < 1" step is the crux.

### `theorem gaussValue_p_pow_mul_teichmuller`
- **Type**: `{ρ : NNReal} (hρ1 : ρ ≤ 1) (i : ℕ) (c : OF F) : gaussValue p F ρ ((p : Ainf p F) ^ i * WittVector.teichmuller p c) = ρ ^ i * perfectoidValuation p F c`
- **What**: The `ρ`-Gauss value of the Teichmüller monomial `p^i·[c]` is `ρ^i · |c|`.
- **How**: Induction on `i`, using `gaussValue_teichmuller` at the base and `gaussValue_p_mul` (multiplicativity in the `p` factor) at the step.
- **Hypotheses**: `ρ ≤ 1`.
- **Uses from project**: `gaussValue`, `gaussValue_teichmuller`, `gaussValue_p_mul`, `perfectoidValuation`, `Ainf`, `OF`
- **Used by**: L1142 (`wLoc_mk'_monomial`)
- **Visibility**: public
- **Lines**: 1117–1131 (proof 10 lines)
- **Notes**: []

### `theorem wLoc_mk'_monomial`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (i k : ℕ) (c : OF F) : wLoc p F ϖ hρ0 hρ1 (IsLocalization.mk' (Bloc …) (p^i * teichmuller p c) (sPow p F ϖ k)) = ρ^i * |c| * ((ρ * |ϖ|)^k)⁻¹`
- **What**: The localized `ρ`-norm of the monomial fraction `p^i[c]/(p[ϖ])^k`, in closed form.
- **How**: `wLoc_mk'` reduces to a quotient of Gauss values; `gaussValue_sPow` computes the denominator `(ρ|ϖ|)^k`, `gaussValue_p_pow_mul_teichmuller` the numerator.
- **Hypotheses**: `0 < ρ < 1`.
- **Uses from project**: `wLoc`, `wLoc_mk'`, `gaussValue_sPow`, `gaussValue_p_pow_mul_teichmuller`, `sPow`, `Bloc`, `Ainf`, `perfectoidValuation`, `PseudoUniformizer.toOF`
- **Used by**: L1504+ (`wLoc_mk'_monomial_le`) and downstream twist estimates
- **Visibility**: public
- **Lines**: 1133–1142 (proof 2 lines)
- **Notes**: []

### `theorem mk'_monomial_twist_factor`
- **Type**: `(zb : OF F) (m i j k : ℕ) (c c' : OF F) (hc : c = zb ^ j * c') : mk' (Bloc …) (p^i * [c]) (sPow p F ϖ k) = teichPowGen p F ϖ zb m ^ j * mk' (Bloc …) (p^(i + m*j) * [c']) (sPow p F ϖ k)`
- **What**: **The twisted factorization of a monomial fraction**: extracting `zb^j` from the Teichmüller coordinate amounts to multiplying by the `j`-th power of the generator.
- **How**: Split each `mk'` as `algebraMap numerator * mk' 1 denominator` (`IsLocalization.mk'_eq_mul_mk'_one`), then apply the numerator identity `teichPowGen_pow_mul_twist` and reassociate by `ring`.
- **Hypotheses**: `c = zb ^ j * c'`.
- **Uses from project**: `teichPowGen`, `teichPowGen_pow_mul_twist`, `sPow`, `Bloc`, `Ainf`
- **Used by**: L1350+ (`exists_monomial_lift_package`) — via the lift chain
- **Visibility**: public
- **Lines**: 1144–1180 (proof 26 lines)
- **Notes**: >30-line declaration; pure localization bookkeeping over the numerator identity.

### `theorem exists_monomial_twist_data`
- **Type**: `(zb : OF F) (m) (hm : 0 < m) (hzb0) (hzb1) (i k : ℕ) (c : OF F) (hc0) (hcm : i < k → |c|^m ≤ |zb|^(k-i)) : ∃ (j) (c'), c = zb^j * c' ∧ |c'| ≠ 0 ∧ (i < k → (k < i + m*j + m ∧ |zb| < |c'|)) ∧ (k ≤ i → j = 0)`
- **What**: **The zone-dispatched twist data of a monomial coordinate**: in the numerator zone (`k ≤ i`) no twist is applied (`j = 0`); in the denominator zone (`i < k`) one takes the deficit-bounded maximal twist supplied by the `σ₁`-Gauss bound.
- **How**: Case split on `i < k`. In the denominator zone use `exists_twist_deep` and derive `|c'| ≠ 0` from multiplicativity of `perfectoidValuation` on `c = zb^j c'`; in the numerator zone take `j = 0`, `c' = c`.
- **Hypotheses**: `0 < m`; `zb` nonzero with `|zb| < 1`; `c` nonzero; the Gauss bound only in the denominator zone.
- **Uses from project**: `exists_twist_deep`, `perfectoidValuation`, `OF`
- **Used by**: L1350+ (`exists_monomial_lift_package`)
- **Visibility**: public
- **Lines**: 1182–1213 (proof 17 lines)
- **Notes**: >10-line proof; repeats the `hval` multiplicativity block verbatim.

### `theorem exists_monomial_twist_div`
- **Type**: `(zb : OF F) (m) (hm : 0 < m) (i k : ℕ) (c : OF F) (hdvd : |c| ≤ |zb|^((k-i)/m)) : ∃ c' : OF F, c = zb ^ ((k-i)/m) * c' ∧ k < i + m*((k-i)/m) + m`
- **What**: **The floor-division twist**: under a direct divisibility bound the coordinate factors through `zb^{⌊(k−i)/m⌋}`, and the twisted exponent lands in the window `(k − m, k]` — no overshoot.
- **How**: `(perfectoidValuation_integers p F).dvd_of_le` turns the valuation bound into a divisibility; the exponent window is `Nat.div_add_mod` together with `Nat.mod_lt` closed by `omega`.
- **Hypotheses**: `0 < m`; the divisibility-strength valuation bound.
- **Uses from project**: `perfectoidValuation`, `perfectoidValuation_integers`, `OF`
- **Used by**: unused in file (companion to `exists_monomial_twist_data`, exported)
- **Visibility**: public
- **Lines**: 1215–1242 (proof 19 lines)
- **Notes**: >10-line proof; repeats the `algebraMap ↥(powerBoundedSubring.toSubring F) F` coercion block verbatim.

### `theorem pow_mul_pow_le_of_le`
- **Type**: `{a b : NNReal} (hab : a ≤ b) {k n : ℕ} (hkn : k ≤ n) : a ^ n * b ^ k ≤ b ^ n * a ^ k`
- **What**: Cross-multiplied radial monotonicity: for `a ≤ b` and `k ≤ n`, `a^n b^k ≤ b^n a^k`. This is the engine of every zone norm-comparison in the section.
- **How**: Split `a^n = a^k a^{n-k}` and `b^n = b^k b^{n-k}` (`pow_add` + `omega` on exponents), then the single inequality `a^{n-k} ≤ b^{n-k}` via `pow_le_pow_left'`.
- **Hypotheses**: `a ≤ b` in `NNReal`; `k ≤ n`.
- **Uses from project**: `[]`
- **Used by**: L1304, L1322 (`twisted_formula_le`), L1344 (`numerator_formula_le`)
- **Visibility**: public
- **Lines**: 1244–1259 (proof 12 lines)
- **Notes**: >10-line proof; purely `NNReal` arithmetic — a mathlib-able micro-lemma.

### `theorem perfectoidValuation_twist_factor`
- **Type**: `(zb c c' : OF F) (j : ℕ) (hfact : c = zb ^ j * c') : perfectoidValuation p F c = perfectoidValuation p F zb ^ j * perfectoidValuation p F c'`
- **What**: The valuation of a `zb^j`-factored coordinate is `|zb|^j · |c'|`.
- **How**: Rewrite with the factorization, push the `OF F → F` coercion through the product/power (`push_cast`), then `Valuation.map_mul` and `map_pow`.
- **Hypotheses**: `c = zb ^ j * c'`.
- **Uses from project**: `perfectoidValuation`, `OF`
- **Used by**: L1396 (`exists_monomial_lift_package`)
- **Visibility**: public
- **Lines**: 1261–1271 (proof 3 lines)
- **Notes**: `omit [CharP F p] in`. This is the extraction of the block copy-pasted verbatim in `exists_twist`, `exists_twist_deep`, `exists_monomial_twist_data` — those three predate it and were not retrofitted.

### `theorem twisted_formula_le`
- **Type**: `{ρ₁ σ₁ ρ₂ V vc vc' : NNReal} (hρ₁0 hσ₁0 hρ₂0 hV0 : 0 < _) (hρσ : ρ₁ ≤ σ₁) (hσρ : σ₁ ≤ ρ₂) {m i k j : ℕ} (hval : vc = σ₁^(m*j) * vc') (he : i + m*j ≤ k) (hwin : k < i + m*j + m) : ρ₂^(i+m*j) * vc' * ((ρ₂*V)^k)⁻¹ ≤ σ₁^i * vc * ((σ₁*V)^k)⁻¹ ∧ ρ₁^(i+m*j) * vc' * ((ρ₁*V)^k)⁻¹ ≤ σ₁^m * (ρ₁^m)⁻¹ * (σ₁^i * vc * ((σ₁*V)^k)⁻¹)`
- **What**: **The zone norm-comparison at formula level** (denominator zone): the twisted monomial's values at the two outer radii `ρ₁ ≤ σ₁ ≤ ρ₂` are controlled by the original's value at the cut radius `σ₁` — exactly (constant `1`) at the top radius, and up to the `m`-step constant `σ₁^m/ρ₁^m` at the bottom radius.
- **How**: The "fold" identity `σ₁^i · vc = σ₁^{i+mj} · vc'` from `hval`; then each half is a `div_le_div_iff₀` cross-multiplication whose core inequality is `pow_mul_pow_le_of_le` — applied with `(hσρ, he)` for the `ρ₂` half and with `(hρσ, hwin.le)` for the `ρ₁` half (this is where the window `k < i+mj+m` is spent).
- **Hypotheses**: all radii and `V` positive; `ρ₁ ≤ σ₁ ≤ ρ₂`; the twist value relation `hval`; the two-sided exponent window `i+mj ≤ k < i+mj+m`.
- **Uses from project**: `pow_mul_pow_le_of_le`
- **Used by**: L1398 (`exists_monomial_lift_package`)
- **Visibility**: public
- **Lines**: 1273–1325 (proof 39 lines)
- **Notes**: >30 lines; pure `NNReal` inequality bookkeeping, radii abstracted away from the ring.

### `theorem numerator_formula_le`
- **Type**: `{ρ₁ σ₁ V vc : NNReal} (hρ₁0 hσ₁0 hV0) (hρσ : ρ₁ ≤ σ₁) {i k : ℕ} (hki : k ≤ i) : ρ₁^i * vc * ((ρ₁*V)^k)⁻¹ ≤ σ₁^i * vc * ((σ₁*V)^k)⁻¹`
- **What**: **The numerator-zone comparison**: when `k ≤ i` the monomial's value at the inner radius `ρ₁` is dominated by its value at the cut radius `σ₁`, with no constant.
- **How**: Same cross-multiplication as `twisted_formula_le` (`div_le_div_iff₀`) with the core inequality `pow_mul_pow_le_of_le hρσ hki`.
- **Hypotheses**: `0 < ρ₁, σ₁, V`; `ρ₁ ≤ σ₁`; `k ≤ i` (numerator zone).
- **Uses from project**: `pow_mul_pow_le_of_le`
- **Used by**: L1416 (`exists_monomial_lift_package`)
- **Visibility**: public
- **Lines**: 1327–1345 (proof 12 lines)
- **Notes**: >10-line proof; the no-twist companion of `twisted_formula_le`.

### `theorem exists_monomial_lift_package`
- **Type**: `{ρ₁ σ₁ ρ₂} (positivity/upper-bound hyps) (hρσ : ρ₁ ≤ σ₁) (hσρ : σ₁ ≤ ρ₂) (zb : OF F) (m) (hm : 0 < m) (hgen : |zb| = σ₁^m) (i k : ℕ) (c : OF F) (hdvd : i < k → |c| ≤ |zb|^((k-i)/m)) : ∃ (j e : ℕ) (c' : OF F), mk' (p^i[c]) (sPow k) = teichPowGen zb m ^ j * mk' (p^e[c']) (sPow k) ∧ wLoc_{ρ₁} (…) ≤ σ₁^m (ρ₁^m)⁻¹ · wLoc_{σ₁} (…) ∧ wLoc_{ρ₂} (…) ≤ max (wLoc_{σ₁} …) (wLoc_{ρ₂} …)`
- **What**: **The per-monomial lift package**: every monomial fraction satisfying the cut-radius divisibility factors as (generator power) × (cofactor monomial), where the cofactor is controlled at both outer radii by the original's `σ`-radius norm — the bottom radius costing at most the fixed constant `σ₁^m/ρ₁^m`.
- **How**: Case split on the zone. Denominator zone: `exists_monomial_twist_div` gives the factorization at depth `j = (k-i)/m` with the window `hwin`; `perfectoidValuation_twist_factor` plus `hgen` turns it into `hval`; `twisted_formula_le` supplies both estimates once `wLoc_mk'_monomial` converts the norms to closed formulas, and `mk'_monomial_twist_factor` supplies the algebraic identity. Numerator zone: take `j = 0`, use `numerator_formula_le` and absorb the constant via `1 ≤ σ₁^m (ρ₁^m)⁻¹`.
- **Hypotheses**: `0 < ρ₁, σ₁, ρ₂ < 1` with `ρ₁ ≤ σ₁ ≤ ρ₂`; `0 < m`; the generator's valuation is exactly `σ₁^m` (the cut condition); floor-division divisibility in the denominator zone.
- **Uses from project**: `exists_monomial_twist_div`, `perfectoidValuation_twist_factor`, `twisted_formula_le`, `numerator_formula_le`, `mk'_monomial_twist_factor`, `wLoc_mk'_monomial`, `teichPowGen`, `vpi_pos`, `wLoc`, `sPow`, `Bloc`, `Ainf`, `PseudoUniformizer.toOF`
- **Used by**: consumed downstream (parts 2–4) — unused earlier in file
- **Visibility**: public
- **Lines**: 1347–1419 (proof 39 lines)
- **Notes**: >30 lines; this is the mathematical heart of the P3d twist section (Kedlaya's per-monomial lift).

### `theorem monomial_dvd_of_wLoc_le_one`
- **Type**: `{σ₁} (hσ₁0 : 0 < σ₁) (hσ₁1 : σ₁ < 1) (zb : OF F) (m) (hgen : |zb| = σ₁^m) (w : Ainf p F) (k : ℕ) (hw : wLoc_{σ₁} (mk' w (sPow k)) ≤ 1) (i : ℕ) (hik : i < k) : |teichCoeff p F w i| ≤ |zb| ^ ((k - i) / m)`
- **What**: **The cut-radius Gauss bound supplies the twist divisibility**: for a fraction of `σ₁`-norm ≤ 1, every denominator-zone Teichmüller coordinate is divisible to the floor-division depth `(k−i)/m` — exactly the hypothesis `exists_monomial_lift_package` needs.
- **How**: `gaussTerm_le_of_wLoc_mk'_le_one` gives `σ₁^i |c| ≤ (σ₁ |ϖ|)^k`; splitting `σ₁^k = σ₁^i σ₁^{k-i}` and cancelling by `le_of_mul_le_mul_left` yields `|c| ≤ σ₁^{k-i} |ϖ|^k`; since `|ϖ| < 1` (`perfectoidValuation_toOF_lt_one`) and `σ₁ < 1`, `pow_le_pow_of_le_one` weakens `σ₁^{k-i}` to `σ₁^{m·⌊(k-i)/m⌋} = |zb|^{⌊(k-i)/m⌋}` via `hgen`.
- **Hypotheses**: `0 < σ₁ < 1`; the generator valuation `|zb| = σ₁^m`; `σ₁`-norm of the fraction at most `1`; denominator zone `i < k`.
- **Uses from project**: `gaussTerm_le_of_wLoc_mk'_le_one`, `perfectoidValuation_toOF_lt_one`, `teichCoeff`, `perfectoidValuation`, `wLoc`, `sPow`, `Bloc`, `Ainf`, `PseudoUniformizer.toOF`
- **Used by**: consumed downstream (parts 2–4)
- **Visibility**: public
- **Lines**: 1421–1466 (proof 33 lines)
- **Notes**: >30 lines; `Nat.div_mul_le_self` supplies the floor inequality.

### `theorem resIHom_blocToBI`
- **Type**: `{θ η : ℝ} (hθ0 hθ1 hη0 hη1) (hσ₁0 hσ₁1 hσ₂0 hσ₂1) (x : Bloc p F ϖ) : (resIHom … (blocToBI … x) : hatK × hatK) = BIProd p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 x`
- **What**: The interval restriction carries `B_loc`-images to `B_loc`-images: restricting `blocToBI x` to the sub-interval gives the sub-interval image `BIProd x` of the same `x`.
- **How**: `Prod.ext` into the two coordinates; each is `resI_BIProd` (compatibility of `resI` with `BIProd` at interpolation parameter `θ`, resp. `η`) followed by `BIProd_fst` / `BIProd_snd`.
- **Hypotheses**: `θ, η ∈ [0,1]`; the interpolated radii in `(0,1)`.
- **Uses from project**: `resIHom`, `blocToBI`, `BIProd`, `resI`, `resI_BIProd`, `BIProd_fst`, `BIProd_snd`, `BISub`, `hatK`, `Bloc`
- **Used by**: consumed downstream (parts 2–4)
- **Visibility**: public
- **Lines**: 1468–1501 (proof 23 lines)
- **Notes**: >30-line declaration; the two `show` blocks are needed because the coercion is only definitionally `BIProd`.

### `theorem wLoc_mk'_monomial_le`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (w : Ainf p F) (k i : ℕ) : wLoc_{ρ} (mk' (p^i * [teichCoeff p F w i]) (sPow k)) ≤ wLoc_{ρ} (mk' w (sPow k))`
- **What**: Each Teichmüller monomial of `w` has localized norm at most that of the whole fraction.
- **How**: Rewrite both sides with `wLoc_mk'_monomial`, `wLoc_mk'` and `gaussValue_sPow`, then the numerator comparison is `le_ciSup` over the Gauss terms with boundedness from `bddAbove_range_gaussTerm`.
- **Hypotheses**: `0 < ρ < 1`.
- **Uses from project**: `wLoc_mk'_monomial`, `wLoc_mk'`, `gaussValue_sPow`, `bddAbove_range_gaussTerm`, `teichCoeff`, `wLoc`, `sPow`, `Bloc`, `Ainf`
- **Used by**: consumed downstream (parts 2–4)
- **Visibility**: public
- **Lines**: 1503–1514 (proof 4 lines)
- **Notes**: []

### `theorem isRestricted_monomial_BI`
- **Type**: `{J : Fin k →₀ ℕ} (a : ↥(BISub p F ϖ hρ…)) : MvPowerSeries.IsRestricted (MvPowerSeries.monomial J a)`
- **What**: A single monomial over `B^I` is a restricted series.
- **How**: All coefficients but the `J`-th vanish (`MvPowerSeries.coeff_monomial`), so the exceptional set is contained in `{J}` (`Set.finite_singleton`) and the cofinite-tendsto condition holds.
- **Hypotheses**: none.
- **Uses from project**: `BISub`
- **Used by**: consumed downstream (parts 2–4); supplies the `hres` argument shape of `evalBI_monomial`
- **Visibility**: public
- **Lines**: 1516–1532 (proof 11 lines)
- **Notes**: >10-line proof; uses `mem_of_mem_nhds` for the zero coefficient.

### `theorem evalBI_monomial`
- **Type**: `{b} (hbmem) (hb) (l : ℕ) (y : ↥(BISub p F ϖ hρ…)) (hres : IsRestricted (monomial (Finsupp.single 0 l) y)) : evalBI p F ϖ φ hφ hbmem hb ⟨_, hres⟩ = (φ y : hatK × hatK) * b ^ l`
- **What**: **The evaluation of a monomial**: `y·T^l ↦ φ(y)·b^l`.
- **How**: `tendsto_nhds_unique` against `tendsto_evalBI` and a constant sequence: `MvPowerSeries.coeff_monomial` plus injectivity of `Finsupp.single` makes `coeffSeq` the indicator `if m = l then y else 0`, so every partial sum with `n > l` collapses by `Finset.sum_ite_eq'` to `φ(y) b^l`.
- **Hypotheses**: `hφ`; `b` power-bounded; `hres` (restrictedness of the monomial, supplied by `isRestricted_monomial_BI`).
- **Uses from project**: `tendsto_evalBI`, `evalBITerm`, `evalBI`, `coeffSeq`, `BISub`, `hatK`
- **Used by**: consumed downstream (parts 2–4)
- **Visibility**: public
- **Lines**: 1547–1592 (proof 36 lines)
- **Notes**: >30 lines; inside `section EvalBIMonomial` (L1534–1594), which re-declares `σ₁ σ₂`, `φ`, `hφ` as `variable`s for the third time in the file.

### `theorem wIRPS_monomial`
- **Type**: `(J : Fin k →₀ ℕ) (y : ↥(BISub p F ϖ hρ…)) : wIRPS p F ϖ … (MvPowerSeries.monomial J y) = wI p F … (y : hatK × hatK)`
- **What**: The interval Gauss norm of a monomial equals the interval norm of its coefficient.
- **How**: `≤` by `ciSup_le`: every coefficient is `y` (at `s = J`) or `0` (`wI_zero`). `≥` by `le_ciSup` at `s = J`, with boundedness from `bddAbove_wIRPS` applied to `isRestricted_monomial_BI`.
- **Hypotheses**: none.
- **Uses from project**: `wIRPS`, `wI`, `wI_zero`, `bddAbove_wIRPS`, `isRestricted_monomial_BI`, `BISub`, `hatK`
- **Used by**: consumed downstream (parts 2–4)
- **Visibility**: public
- **Lines**: 1596–1617 (proof 13 lines)
- **Notes**: >10-line proof.

### `theorem wIRPS_add_le`
- **Type**: `{f g : MvPowerSeries (Fin k) ↥(BISub …)} (hf : IsRestricted f) (hg : IsRestricted g) : wIRPS (f + g) ≤ max (wIRPS f) (wIRPS g)`
- **What**: The ultrametric (strong triangle) inequality for the interval Gauss norm on restricted series.
- **How**: `ciSup_le` over multi-indices; coefficientwise `map_add` + `BISub_coe_add` and the ultrametric `wI_add_le`, then `max_le_max` with `wI_coeff_le_wIRPS` on each summand (restrictedness is what makes those `⨆` bounds legal).
- **Hypotheses**: both `f` and `g` restricted.
- **Uses from project**: `wIRPS`, `BISub_coe_add`, `wI_add_le`, `wI_coeff_le_wIRPS`, `BISub`
- **Used by**: L1671 (`wIRPS_finset_sum_le`)
- **Visibility**: public
- **Lines**: 1619–1630 (proof 5 lines)
- **Notes**: []

### `theorem wIRPS_finset_sum_le`
- **Type**: `{ι : Type*} (s : Finset ι) (f : ι → ↥(restrictedMvPowerSeriesSubring k ↥(BISub …))) (B : NNReal) (hf : ∀ i ∈ s, wIRPS (f i) ≤ B) : wIRPS (∑ i ∈ s, f i) ≤ B`
- **What**: A finite sum of restricted series has Gauss norm bounded by any common bound on the summands (the ultrametric sum bound).
- **How**: `Finset.induction_on`: the empty case is `wIRPS_zero`, the insert case is `wIRPS_add_le` followed by `max_le` of the head bound and the induction hypothesis.
- **Hypotheses**: a uniform bound `B` on the members of `s`.
- **Uses from project**: `wIRPS`, `wIRPS_zero`, `wIRPS_add_le`, `restrictedMvPowerSeriesSubring`, `BISub`
- **Used by**: consumed downstream (parts 2–4)
- **Visibility**: public
- **Lines**: 1632–1673 (proof 26 lines)
- **Notes**: >30-line declaration; the two `rfl`-typed `have`s are coercion-transport steps for the subring sum.

### `theorem evalBI_finset_sum`
- **Type**: `{ι : Type*} (s : Finset ι) {b} (hbmem) (hb) (g : ι → ↥(restrictedMvPowerSeriesSubring 1 ↥(BISub …))) : evalBI p F ϖ φ hφ hbmem hb (∑ i ∈ s, g i) = ∑ i ∈ s, evalBI p F ϖ φ hφ hbmem hb (g i)`
- **What**: Evaluation commutes with finite sums of restricted series.
- **How**: `Finset.induction_on` with `evalBI_zero` at the base and `evalBI_add` at the step.
- **Hypotheses**: `hφ` (included); `b` power-bounded.
- **Uses from project**: `evalBI`, `evalBI_zero`, `evalBI_add`, `restrictedMvPowerSeriesSubring`, `BISub`
- **Used by**: consumed downstream (parts 2–4)
- **Visibility**: public
- **Lines**: 1688–1705 (proof 7 lines)
- **Notes**: `include hφ in`; inside `section EvalBISum` (L1675–1707), the fourth re-declaration of the `σ₁ σ₂`/`φ`/`hφ` variable block.

---

**End of part 1.** The next declaration, `exists_evalBI_approx_bloc`, begins at L1733 inside
`section Assembly` (opened L1712, "The first approximation (T910 case 1, the Kedlaya lift)"
at L1710) and belongs to part 2.
