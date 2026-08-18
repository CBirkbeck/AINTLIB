# Step 4 — Mathlib API Audit: PadicLFunctions

Scope: the project's ~225 definitions and core concepts (p-adic measures/distributions on ℤ_p and ℤ_p^×, the Iwasawa algebra Λ, the Mahler/Amice transform, generalised Bernoulli numbers, rational/complex ζ-values, the Kubota–Leopoldt p-adic L-function and pseudo-measures, the p-adic exp/log, the Coleman map/norm operator, cyclotomic units). Audited against current mathlib (`Mathlib.NumberTheory.Bernoulli`, `Mathlib.NumberTheory.Padics.*`, `Mathlib.NumberTheory.Padics.MahlerBasis`, `Mathlib.NumberTheory.LSeries.*`, `Mathlib.NumberTheory.DirichletCharacter.*`, `Mathlib.Analysis.Normed.*`, `Mathlib.RingTheory.PowerSeries.*`, `Mathlib.Topology.Algebra.Nonarchimedean.*`).

Method: read 17 inventory files in full + targeted `WebSearch "mathlib4 …"` for each high-value concept. No live `lean_loogle`/`lean_local_search` (local build stale); web + mathlib-docs cross-checks used instead. **Confidence is LOWER than a live-search audit** — every "no equivalent" below should be re-verified with `exact?`/`loogle`/`#find` once the build is green, and every "mathlib has it" name should be confirmed to still exist (names drift with the daily bump).

Headline orientation. This project deliberately **does not use mathlib's measure-theoretic `MeasureTheory.Measure`**, and that is correct: a "p-adic measure" here is a *bounded ℤ_p-linear functional on `C(X, ℤ_p)`* (the continuous dual / Amice picture), which is a different object from a σ-additive `MeasureTheory.Measure`. So the big structural pieces (`PadicMeasure`, `MeasureR`, the Iwasawa algebra, the Mahler transform iso, pseudo-measures, the Coleman map) have **no mathlib equivalent** and should NOT be redirected to `MeasureTheory`. The real wins are smaller: (1) genuine duplications of mathlib infrastructure (`integerRing` vs the unit-ball subring; `ModEqPow`; bespoke summability/Abel-summation lemmas), (2) `MATHLIB-PR`-flagged general lemmas the authors already know are upstreamable, and (3) the p-adic exp/log file, which reproduces a substantial analytic API that is partly in mathlib and largely PR-able.

---

## Definitions to Replace

These are project definitions with a plausible existing mathlib counterpart. **None is a slam-dunk "delete and import"** — each needs a live `exact?`/`loogle` confirmation — but each is a concrete redirect to try.

### 1. `integerRing` (Coefficients.lean) — the norm-unit-ball subring `{x : L // ‖x‖ ≤ 1}`
- **Finding:** mathlib has the closed-unit-ball-as-subring for normed (division) rings. `WebSearch` confirms `Mathlib.Analysis.Normed.Field.UnitBall` and the seminorm/ball API; for a `NormedField` the unit ball `{x | ‖x‖ ≤ 1}` is a standard subring there. The project re-derives all four subring axioms by hand from the ultrametric inequality.
- **Action:** Try to define `integerRing L` as (or prove `≃+*` to) the existing mathlib unit-ball subring. Confirm the exact decl with `exact? `/`#find Subring … "‖·‖ ≤ 1"`; candidates to check: the `unitBall`/`closedBall` subring in `Mathlib.Analysis.Normed.Field.UnitBall`, or `Valuation.integer`/`Valuation.valuationSubring` if the norm is wired to a `Valuation`. Even if the carrier is kept, the *instances* `integerRing.instIsUltrametricDist`, `instCompleteSpace` (closed subset of complete), and `instIsBoundedSMul` are very likely already-derivable subtype instances rather than needing the hand proofs here.
- **Caveat:** the project needs `Algebra ℤ_[p] (integerRing L)` + isometry of `algebraMap ℤ_[p] → integerRing L`; check whether mathlib's unit-ball subring already carries (or easily yields) that. If the unit-ball subring exists but lacks these, keep `integerRing` as a thin wrapper and only delete the duplicated subring-axiom/instance proofs.

### 2. `padicIntEquivIntegerRing` (Coleman/NormOperator.lean) — `ℤ_[p] ≃+* integerRing ℚ_[p]`
- **Finding:** this is exactly "ℤ_p is the unit ball of ℚ_p", which mathlib knows in some form (`PadicInt` *is* `{x : ℚ_[p] // ‖x‖ ≤ 1}` up to the subring packaging). Directly downstream of #1.
- **Action:** Once #1 redirects `integerRing ℚ_[p]` to the mathlib unit-ball subring, search for an existing `ℤ_[p] ≃+* (unit ball of ℚ_[p])` (`PadicInt.…`). If absent, this is a 1-line `RingEquiv.ofBijective` that is a fine `MATHLIB-PR` candidate but small; low priority.

### 3. `mahlerCoeff` (Measure/MahlerTransform.lean) `:= μ (mahler n)`
- **Finding:** `mahler n : C(ℤ_[p], ℤ_[p])` is mathlib's Mahler basis (`Mathlib.NumberTheory.Padics.MahlerBasis`) — the project correctly reuses it. `mahlerCoeff` is just `μ` applied to it; it is a trivial wrapper, not a duplication.
- **Action:** **No replacement.** Keep. (Listed only to record that the *underlying* `mahler` basis is mathlib's, not hand-rolled — good.) Consider inlining `mahlerCoeff` if it earns its keep elsewhere, but that's a cleanup nicety, not an API choice.

### 4. `del` / `delQ` (Measure/Toolbox.lean, KubotaLeopoldt/MuA.lean) — the operator `∂ = (1+T)·d/dT` on power series
- **Finding:** built from `PowerSeries.derivativeFun` (mathlib). The operator `(1+X) * F.derivativeFun` itself is not a named mathlib def, but the *two copies* (`del` over ℤ_p, `delQ` over ℚ_p) duplicate each other; `MuA.lean`'s docstring already flags "merge with `PadicMeasure.del`".
- **Action:** **Not a mathlib replacement** — it's an internal dedup. Unify `del`/`delQ` into one definition over a general `[CommRing A] [Algebra ℚ A]` (or relate them by `map_del`, which already exists). Leave the `∂` concept as project API (mathlib has no `(1+T)d/dT` operator).

### 5. `zetaNeg` (KubotaLeopoldt/ZetaValues.lean) `:= (-1)^k * bernoulli (k+1)/(k+1)` and `LvalNeg`
- **Finding:** `bernoulli` is mathlib's. `riemannZeta (-k) = (-1)^k * bernoulli (k+1)/(k+1)` is **in mathlib** as `riemannZeta_neg_nat_eq_bernoulli'` (the project's `ZetaValuesComplex` already bridges to it). `zetaNeg` is a deliberate *rational-valued* stand-in kept to avoid importing complex analysis into the main p-adic chain.
- **Action:** **Keep `zetaNeg` as a rational def** (the no-complex-import rationale is sound), but it is NOT new mathematics — it is `riemannZeta`'s negative-integer value transported to ℚ. Ensure the bridge lemma to `riemannZeta_neg_nat_eq_bernoulli'` is the single point of contact (it already is, via `ZetaValuesComplex`). No code to delete.

---

## API Choice Improvements

Cases where the project uses a hand-rolled construction/predicate where a richer mathlib API exists or where a general mathlib lemma should be used.

### A. `ModEqPow` (Coleman/NormOperator.lean) — bespoke "≡ mod p^k" on `PowerSeries ℤ_[p]`
- **Finding:** `ModEqPow p k f g := ∀ m, (p:ℤ_[p])^k ∣ coeff m (f - g)`. The whole `ModEqPow.{refl,symm,trans,mul,mul_right,pow,of_le}` algebra re-implements congruence-modulo-an-ideal. Mathlib has `Int.ModEq`-style and, more relevantly, **`SmodEq` / `Ideal.Quotient` + `Submodule.Quotient`** machinery, and `a ≡ b [SMOD I]` (`SModEq`) for modules, which gives refl/symm/trans/add/mul for free. The natural mathlib phrasing is "`f - g` lies in the ideal `(Ideal.span {(p)^k}).map C` / the coefficientwise condition", or `PowerSeries.map (Ideal.Quotient.mk …)`-equality (the project's own `modEqPow_one_iff_map_toZMod` already shows the `k=1` case is `map toZMod f = map toZMod g`).
- **Action:** Try recasting `ModEqPow p k f g` as `f ≡ g [SMOD (Ideal.span {(p:ℤ_[p])^k}).map (PowerSeries.C _)]` (or as equality after `PowerSeries.map (Ideal.Quotient.mk …)`), and derive `refl/symm/trans/mul/pow` from mathlib's `SModEq`/quotient-hom lemmas instead of the ~8 hand proofs. Search: `SModEq`, `Ideal.Quotient.mk`, `Submodule.Quotient.mk_eq_mk`. If a clean coercion exists this removes a dozen boilerplate lemmas; if not, keep `ModEqPow` but tag the algebra lemmas as the dedup target. (Generalisation, not deletion — gate behind a check that the substitution/`normOp_modEq_*` proofs still go through.)

### B. Hand-rolled `Filter.Tendsto`/limit usage is already idiomatic — no custom limits
- **Finding:** I specifically checked for "custom limits vs `Filter.Tendsto`" and "custom convergence predicates". The project consistently uses mathlib's `Filter.Tendsto`, `HasSum`, `Summable`, `Tendsto … atTop (𝓝 …)`, `Metric.tendsto_atTop`, `UniformCauchySeqOn`, `tendsto_nhds_unique`. There is **no hand-rolled limit/convergence notion** to replace. The Mahler transform's inverse uses `tsum`; the exp/log use `tsum`/`HasSum`. Good.
- **Action:** **No change.** (Recorded as a positive: the convergence layer is on mathlib API.)

### C. `summable_iff_tendsto_cofinite_zero` / `summable_*_terms` (PadicExp.lean) — re-export + repeated pattern
- **Finding:** `summable_iff_tendsto_cofinite_zero` is a 1-line delegation to `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` (mathlib). The instance `NonarchimedeanRing L` (from ultrametric normed field) is **flagged `MATHLIB-PR` in the file's own docstring**. The several `summable_padicExp_terms` / `summable_padicLog_terms` / `summable_prod_family` lemmas all follow the identical "cofinite-zero + geometric bound + `tendsto_pow_atTop_nhds_zero_of_lt_one`" recipe.
- **Action:** (1) Drop the local `summable_iff_tendsto_cofinite_zero` re-export and call `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` directly (confirm name). (2) PR the `NonarchimedeanRing` instance for ultrametric normed fields (authors agree). (3) The repeated geometric-decay summability is a candidate for one shared helper lemma "`Summable f` if `‖f n‖^(p-1) ≤ C·rⁿ` with `r<1`", which would also be PR-able. These are API/generalisation cleanups, not new math.

### D. `charFnCM` / `levelChar` indicators — already on `LocallyConstant.charFn`
- **Finding:** both `MeasureR.charFnCM` and `PadicMeasure.levelChar` are built from mathlib's `LocallyConstant.charFn` coerced to `ContinuousMap`. Correct reuse.
- **Action:** **No change.** (Recorded as good reuse; the only nicety is that `PadicMeasure.levelChar` could be expressed via `charFnCM` over `ℤ_p` coefficients to share the simp lemmas, a minor dedup.)

### E. Gauss sums — `gaussSum`/`AddChar.zmodChar` are mathlib; `gaussSum_mul_gaussSum_inv` is the general-level upgrade
- **Finding:** the project uses mathlib `gaussSum`, `AddChar.zmodChar`, `gaussSum_mulShift_of_isPrimitive`, `AddChar.sum_mulShift`. Its `gaussSum_mul_gaussSum_inv` (G(χ,e)·G(χ⁻¹,e⁻¹) = N) is explicitly noted as the **general-N version that mathlib has only for the prime/field case**.
- **Action:** **Keep, and flag `gaussSum_mul_gaussSum_inv` + `norm_eq_one_of_pow_eq_one` as MATHLIB-PR candidates** (the latter is the verbatim analogue of `Complex.norm_eq_one_of_pow_eq_one` for a general normed field). No redirect; these *extend* mathlib.

### F. L-value at negative integers — `LFunction_neg_nat` overlaps mathlib's Dirichlet-continuation API
- **Finding:** `WebSearch` confirms `Mathlib.NumberTheory.LSeries.DirichletContinuation` gives `LFunction χ` as a combination of Hurwitz zetas, and `Mathlib.NumberTheory.LSeries.HurwitzZetaValues` gives `hurwitzZeta_neg_nat` (`ζ_α(-k) = -B_{k+1}(α)/(k+1)` for k ≥ 1). The project's `GenBernoulliComplex.LFunction_neg_nat` proves `LFunction χ (-k) = -B_{k+1,χ}/(k+1)` by **assembling those mathlib pieces** — it is the *generalised-Bernoulli packaging* of values mathlib already has per-Hurwitz-term. The k=0 gap (mathlib's `hurwitzZeta_neg_nat` excludes k=0) is exactly why the project built the whole `Sawtooth.lean` file.
- **Action:** **Keep** `LFunction_neg_nat` (it is the genuinely-new "sum over residues = generalised Bernoulli" statement). But verify it is built on `hurwitzZeta_neg_nat` / `riemannZeta_neg_nat_eq_bernoulli'` and `LFunction_modOne_eq` rather than re-deriving any per-term value — the inventory shows it does. No code to remove; this is the right division of labour.

---

## Hand-Rolled Patterns

Larger bodies of analysis/algebra the project develops itself. The recurring question is "is this in mathlib, or PR-able?" — answered per item.

### I. p-adic exp / log on a general complete ultrametric ℚ_p-algebra (PadicExp.lean, ~668 lines)
- **Finding:** This is the single biggest hand-rolled analytic block: `padicExp`, `padicLog`, convergence on the ball `‖x‖^(p-1) < p⁻¹` (`InExpBall`), isometry, `padicExp_add`, `padicLog_mul`, mutual inversion (`padicExp_padicLog`/`padicLog_padicExp` via formal `exp_subst_log`/`log_subst_exp_sub_one` + a `master_bridge` evaluation theorem), Legendre/valuation bounds, and the integral versions on `pℤ_p` / `1+pℤ_p`. **`WebSearch` confirms mathlib does NOT have a p-adic exp/log on `PadicInt` or on general normed ℚ_p-algebras** (only `Padic`/`PadicInt` arithmetic + `MahlerBasis`; the formal `PowerSeries.exp`/`PowerSeries.log` exist and the project *does* reuse them). So the analytic theory genuinely is not upstream.
- **Action:** **Keep** — no mathlib equivalent for the analytic `exp`/`log` on these fields. BUT this file is the richest source of **MATHLIB-PR candidates**: the formal-power-series identities `exp_subst_log`/`log_subst_exp_sub_one`/`oneAddX_mul_derivative_log` (stated over any `[CommRing A] [Algebra ℚ A]`), the nonarchimedean Cauchy-product theorems (`hasSum_pow_fin`, `tsum_eval_pow`, `master_bridge`, `summable_eval_pow`), and the Legendre bound `sub_one_mul_padicValNat_succ_le` (no primality needed). Several already carry `omit` of all the analytic instances, signalling they want to live at a more general home. Recommend: (a) split the formal-PS + nonarchimedean-Cauchy-product lemmas out as a PR-able layer, (b) the genuine `padicExp`/`padicLog` API stays in-project (or becomes a larger mathlib contribution later). No redirect to existing mathlib.

### II. The measure/Iwasawa-algebra core (Measure/*, MeasureR/*) — bounded functionals, NOT `MeasureTheory`
- **Finding:** `PadicMeasure X := C(X,ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` and `MeasureR K X := C(X,𝒪_K) →ₗ[𝒪_K] 𝒪_K`, with automatic boundedness/continuity (`norm_apply_le`, `continuous`), density of locally-constant functions, `dirac`, `pushforward`, `compRight`, convolution `conv`, the Iwasawa-algebra `CommRing`, Fubini (`integral_swap`), pseudo-measures, `QuotientField`. This is the **continuous-dual / Amice description of measures**, which is a *different object* from mathlib's σ-additive `MeasureTheory.Measure`. `WebSearch` confirms the Amice transform "measures ≅ power series" is **not in mathlib** (mathlib has only the `mahler` basis).
- **Action:** **Do NOT redirect to `MeasureTheory`.** This is the correct, intended formalisation and has no mathlib equivalent. Two sub-notes: (a) `exists_locallyConstant_norm_sub_le'` (Fubini.lean) is **flagged a MATHLIB-PR candidate** (generalises mathlib's ℤ_p-valued `LocallyConstant` density to any ultrametric target) — pursue. (b) The `Measure/*` (ℤ_p coefficients) and `MeasureR/*` (𝒪_K coefficients) layers are near-verbatim duplicates of each other; the *intended* generality is "measures over any complete ultrametric coefficient ring", so the dedup target is to unify them (a big generalisation, already partially anticipated by the `§11 R11.5` general-`G` convolution pass) — not a mathlib import.

### III. Abel summation / Dirichlet's test / sawtooth analysis (Sawtooth.lean, ~18 lemmas, 5 over 50 lines)
- **Finding:** to get `hurwitzZeta x 0 = -B₁(x)` on (0,1) (the k=0 case mathlib's `hurwitzZeta_neg_nat` omits), the file develops summation-by-parts bounds (`norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded`, `norm_sum_range_shift_*`), the conditional convergence of `Σ sin(2πnx)/n` via Dirichlet's test, Abel's theorem, and uniform-Cauchy machinery. The **summation-by-parts / Dirichlet-test pieces are generic real analysis**; mathlib has `Finset.sum_range_by_parts`, `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded` (Dirichlet's test — the file *already uses* it), and Abel's theorem `Real.tendsto_tsum_powerSeries_nhdsWithin_lt` (also used).
- **Action:** Audit whether `norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded` and the shift-bound lemmas duplicate existing mathlib summation-by-parts corollaries — they are stated for a general `NormedSpace ℝ E` and look PR-able / possibly already-present. Search: `Finset.abel`, `sum_range_by_parts`, `Dirichlet test`, `norm_sum_le … antitone`. The sawtooth value itself (`sinZeta_one_eq_boundary`, `hurwitzZetaOdd_apply_zero_of_mem_Ioo`, `hurwitzZeta_neg_nat_of_mem_Ioo`) is a genuine extension of mathlib's Hurwitz-value API to the boundary case and should be **kept + flagged MATHLIB-PR** (it closes the k=0 gap in `HurwitzZetaValues`). Net: keep the sawtooth results, dedup/PR the generic summation-by-parts helpers.

### IV. Generalised Bernoulli numbers `DirichletCharacter.genBernoulli` (Interpolation/GenBernoulli.lean)
- **Finding:** `B_{k,χ} = N^{k-1} Σ χ(a) B_k(a/N)` (Bernoulli-polynomial form), plus parity-vanishing and the generating-function identity `genBernoulliPowerSeries_mul`. `WebSearch` confirms generalised Bernoulli numbers were formalised in **Lean 3** (Narayanan, p-adic L-functions) but are **NOT in mathlib4** — mathlib4 has only `bernoulli`/`Polynomial.bernoulli` and `bernoulliPowerSeries_mul_exp_sub_one`. So `genBernoulli` is genuinely new to mathlib4.
- **Action:** **Keep** — no mathlib4 equivalent. Strong **MATHLIB-PR candidate** (the Lean-3 version's existence shows the community wants it; `genBernoulliPowerSeries_mul` is the §5 analogue of mathlib's `bernoulliPowerSeries_mul_exp_sub_one`). Ensure it is built on `Polynomial.bernoulli`/`bernoulli'` (mathlib) — inventory confirms it is (`Polynomial.bernoulli_eval_one`, `bernoulli_eval_one_sub`). No redirect.

### V. The Coleman norm operator `normOp` and digit basis (Coleman/NormOperator.lean)
- **Finding:** `normOp f := Algebra.norm (PowerSeries ℤ_[p]) ((toPS).symm f)`, with the free rank-p digit basis `digitBasis` over the Frobenius subalgebra `PhiAlg`, `digitMatrix`, `trace_digitMatrix = p·ψ`, and the mod-p^k congruence theory. This is built **on top of mathlib's `Algebra.norm`/`Algebra.trace`/`Module.Basis`/`leftMulMatrix`/`Algebra.norm_eq_matrix_det`** — exemplary reuse. The Frobenius identity over 𝔽_p⟦T⟧ uses mathlib's `add_pow_char`/`frobenius`/`expand`.
- **Action:** **Keep** — no mathlib equivalent for the Coleman norm operator; the underlying linear-algebra is already mathlib's. The only API-choice item here is `ModEqPow` (item A above). The compactness/seq-compactness instances (`instCompactSpace`, `instSeqCompactSpace`, `exists_subseq_tendsto`, `isClosed_isUnit`) for `PowerSeries ℤ_[p]` with the Pi topology are thin wrappers over mathlib Tychonoff/`SeqCompactSpace`/`WithPiTopology` — correct, and `isClosed_isUnit`/`instSeqCompactSpace` may be PR-able as general `PowerSeries`-over-compact-ring facts.

### VI. `CompactSpace ℤ_[p]ˣ` and units topology (Measure/UnitsZp.lean)
- **Finding:** `instance CompactSpace ℤ_[p]ˣ` is **explicitly noted "not in mathlib (verified absent)"**, derived via the closed embedding `Units.embedProduct`. Likewise `TotallyDisconnectedSpace ℤ_[p]ᵐᵒᵖ`/`ℤ_[p]ˣ`, `unitsHomeo`.
- **Action:** **Keep + MATHLIB-PR candidate** (`CompactSpace Rˣ` for a compact T2 topological ring is a general fact — units of a compact ring with continuous inverse / closed unit group). Worth a general PR; no existing mathlib decl to import. Confirm absence with `#find CompactSpace _ˣ` once building.

### VII. Misc small hand-rolled lemmas that are really mathlib-shaped
- `norm_eq_one_of_pow_eq_one` (Characters.lean) — verbatim general-field analogue of `Complex.norm_eq_one_of_pow_eq_one`. **PR candidate.**
- `IsPrimitiveRoot.norm_sub_one_lt` / `tendsto_pow_sub_one` / `norm_pow_sub_one_eq_one` (Coefficients.lean) — "‖ζ−1‖<1 for a p^n-th root, =1 for a tame root" — clean `IsPrimitiveRoot`-namespace facts over an ultrametric ℚ_p-algebra. **PR candidates** (extend `IsPrimitiveRoot` API).
- `charZero_of_qpAlgebra` (Coefficients.lean) — "any normed ℚ_p-algebra field is `CharZero`" — likely already derivable from `charZero_of_injective_algebraMap` + an existing instance; **check for an existing instance** before keeping.
- `del`/`delQ` merge (item 4) and `Measure`↔`MeasureR` unification (item II) are the two biggest *internal* dedups.

---

## Summary of recommended actions (priority order)

1. **Redirect `integerRing` to mathlib's unit-ball subring** (`Mathlib.Analysis.Normed.Field.UnitBall`), deleting the hand-proved subring axioms + subtype instances where mathlib already supplies them (Defn-to-Replace #1; cascades to `padicIntEquivIntegerRing` #2). *Verify with `exact?` first — highest payoff if it lands.*
2. **Recast `ModEqPow` on top of mathlib `SModEq`/`Ideal.Quotient`** to delete ~8 boilerplate congruence lemmas (API Choice A).
3. **Unify the `Measure/*` ↔ `MeasureR/*` duplication** and the `del`/`delQ` pair into single coefficient-general definitions (Hand-Rolled II, Defn #4) — big internal dedup, no mathlib import.
4. **PR the flagged general lemmas:** `NonarchimedeanRing` instance, `exists_locallyConstant_norm_sub_le'`, `CompactSpace ℤ_[p]ˣ`, `norm_eq_one_of_pow_eq_one`, the `IsPrimitiveRoot.norm_*` facts, generalised Bernoulli, the boundary Hurwitz values, the formal exp/log + nonarchimedean-Cauchy-product lemmas (PadicExp), `gaussSum_mul_gaussSum_inv`.
5. **Audit the Sawtooth summation-by-parts helpers** for duplication with mathlib's `sum_range_by_parts`/Dirichlet-test corollaries (Hand-Rolled III).
6. **Keep as genuinely-new-to-mathlib (no redirect):** `PadicMeasure`/`MeasureR` and the whole Iwasawa-algebra/pseudo-measure/Mahler-transform-iso layer, the Kubota–Leopoldt `padicZeta`/`kubotaLeopoldt`, `LpFunction`/`Lp_interpolation`, the Coleman map `Col`/`normOp`, `padicExp`/`padicLog`/`extLog`, `genBernoulli`, `zetaNeg`.

**Verification caveat (repeat):** produced without live symbol search. Before acting on any "replace"/"PR-candidate" line, run `exact?`/`apply?`/`loogle`/`#find` against the current pin to (a) confirm the mathlib decl exists and is named as guessed, and (b) confirm the project decl is not already importing it. Treat every name above as a search seed, not a settled fact.
