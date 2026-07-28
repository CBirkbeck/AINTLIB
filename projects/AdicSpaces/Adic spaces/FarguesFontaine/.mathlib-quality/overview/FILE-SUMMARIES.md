
## ★★★ THE HIGHEST-LEVERAGE FINDING IN THE FOLDER — the radii boilerplate ★★★

`ChartComparison.lean` declares the annulus radii and their constraints as implicit variables:

    variable {rho1 rho2 : NNReal} {h10 : 0 < rho1} {h11 : rho1 < 1}
             {h20 : 0 < rho2} {h21 : rho2 < 1}

Because they are IMPLICIT, essentially every call site must respell them by name.  The
resulting `(h10 := h10) (h11 := h11) (h20 := h20) (h21 := h21)` boilerplate occurs

    465 TIMES ACROSS 14 FILES

| File | occurrences |
|---|---|
| ChartComparison | 142 |
| ChartVObj | 107 |
| FrobeniusGauss | 70 |
| Presentation | 50 |
| ChartData | 27 |
| UniformizerEquivariance | 25 |
| IntervalRing | 18 |
| ChartSpa 6, RestrictionInjective 5, YStalks 4, CurveAdicPresentation 4,
  RobbaPresentation 3, SheafyBI 2, ChartBIQ 2 | |

Bundling `(rho1, rho2)` + the four constraints into a single structure (or making them
instance-implicit) removes ~465 lines of pure noise with ZERO mathematical change.  The
ChartComparison worker estimates this alone cuts ~1/3 of that file.

This is a Step-7 API-design change, cross-cutting 14 files — it must be decided and executed
BEFORE the per-file /cleanup sweep, or every one of those files gets cleaned twice.

## ChartComparison.lean — 29 decls (6 defs, 23 theorems), 632 lines
Finite-level chart comparison: the rational-localization chart maps into `B^I` at the exact
chart interval with dense range, and is uniformly inducing (two-sided neighbourhood-basis
comparison, upgraded topological->uniform via the additive group structure).  So `B^I` IS an
abstract completion of the chart localization; uniqueness of completions gives
`O_Y(U) = B^I` (ID2d), and transporting sheafiness across it gives ID2e.
- Key API: `chartToBI` (7), `presheafChartRingEquivBISub` (3 + 4 downstream files)
- **DEAD (0 consumers anywhere)**: `two_le_p_add_one` (L626, `2 <= p+1` by omega) —
  also topically unrelated to the file
- 10 in-file-only scaffolding decls are candidates for `private`
- Extractable ~90-110 lines: the four-instance `letI` bundle appears 3x (would collapse the
  92-line `isSheafy_presheafChart` to ~15); `chartUniformity` letI 3x; plus blocks that were
  extracted as lemmas but left inlined at their original sites
- Proofs >30: 3.  Largest `isSheafy_presheafChart` (~50 on a 42-line statement)

## GaussNorm.lean — 47 decls (4 defs, 43 theorems; 5 private, 3 @[simp]), 923 lines
Weighted Gauss value `w_rho(x) = sup_n rho^n v(a_n)` on A_inf, proved a MULTIPLICATIVE
non-archimedean seminorm (Kedlaya Lem 4.1 / 2.3ab).  Part 1: definitions, basic bounds,
Teichmuller expansion + uniqueness toolkit, the two-digit ultrametric estimate via the `u=b/a`
scaling trick (avoiding Witt-polynomial homogeneity).  Part 2: level-`n` normal form ->
`gaussValue_add_le` in six lines, p-power scaling, then submultiplicativity and exact
multiplicativity (leading-term computation + isosceles principle).
- Key API: the four defs pervasively; `gaussValue_add_le` (7 in-file + 5 elsewhere);
  `gaussTerm_le_gaussValue` (6)
- **GENUINELY DEAD (0 uses anywhere, not instance/simp)**: `coe_p_ne_zero`,
  `gaussValue_list_sum_le` (the Finset twin `gaussValue_finset_sum_le` is what is used)
- NOT dead despite no in-file use: `teichCoeff_zero_vector`, `gaussValue_zero`,
  `gaussValue_one` — all `@[simp]`
- Repeated preamble x5: `rw [gaussValue]` + `ciSup_le` reduction — a
  `gaussValue_le_of_forall_gaussTerm_le` helper absorbs all five
- **UPSTREAMING CANDIDATE**: `nnreal_mul_max` (L411) is a general NNReal fact with NO
  Fargues-Fontaine content, used from 4 other files -> relocate (or mathlib)
- sorry: none.  set_option: none.
- Proofs >30: 8.  Largest `gaussValue_mul` (104), `gaussValue_mul_le` (68)

## Curve.lean — 29 decls (2 defs, 21 theorems, 6 instances), 580 lines
DEFINES the curve: `Curve = Y/phi^Z` as a topological quotient.  Proves the Frobenius action
free and WANDERING (the properly-discontinuous hypothesis the sources invoke), the quotient
map open, injective on each window, `im(U_0) u im(V_0)` covering, and — by exhibiting U_0,V_0
as rational subsets — that the curve is T0 and quasicompact.
- Unused but NOT dead: `smul_ne_of_ne_zero`, `exists_nhd_smul_disjoint` (headline
  freeness/wandering statements, public API); `instT0SpaceCurve`, `instCompactSpaceCurve`
  (INSTANCES); `Y_nonempty` (one-line re-export)
- **REFACTOR**: `injOn_toCurve_windowU`/`V` RE-DERIVE the freeness argument inline instead of
  calling `smul_ne_of_ne_zero`
- **THIS FILE IS DEFEQ PLUMBING, not duplication** — `instCompactSpaceCurve` (39 lines) is
  four `have` blocks moving one compact set between three subtype spellings; `ainf_pair_spec`
  is ~100% plumbing.  Fix = a Set-level `Subtype.image_preimage` helper + a window-family-
  generic helper (roughly halves the file).
- EXCEPTION: `mem_rationalOpen_pair_iff` (34 lines) is long for GENUINE mathematical reasons
  (valuation-axiom work, no `show`-respelling) and mentions Ainf only incidentally —
  a plausible promotion candidate to the general Spa API.  Leave it alone in cleanup.
- U/V TWIN PAIRS are line-for-line duplicates throughout: `injOn_toCurve_windowU`/`V`,
  `isOpen_windowU_Y`/`V`, `windowU_zero_trace_eq`/`V`, `isCompact_windowU_zero`/`V`

## RobbaPresentation.lean part 1 (lines 1-1700) — 55 of 192 decls
Evaluation machinery for restricted power series over an annulus ring, culminating in
`evalBIHom : B^I<T> -> B^{I'}` (Kedlaya case-1/2 Robba presentation), stated generically in a
norm-contracting coefficient hom.  Then the interval Gauss norm `wIRPS` and the main analytic
result `exists_rps_series_limit_BI` (completeness with tail estimates, via columnwise limits).
Last third: the case-1/2 generator `teichPowGen` and per-monomial twist theory.
- **DEDUP**: the `hval` multiplicativity block appears verbatim in `exists_twist`,
  `exists_twist_deep`, `exists_monomial_twist_data` — and is EXACTLY the body of
  `perfectoidValuation_twist_factor` (L1261), which was extracted later but the three earlier
  callers were never retrofitted
- The `variable {sigma1 sigma2} (phi) (hphi)` block is re-declared verbatim 4x, once per
  section, with a 5th variant
