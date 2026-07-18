# HANDOVER — DedekindResidue (Belabas–Friedman residue formalisation)

## 2026-07-03 leg 9: ★★★ PROJECT TARGET PROVEN — `belabas_friedman_thm1` ★★★

**The project's single intentional sorry is discharged** (commit d5ea59a3, pushed).
`belabas_friedman_thm1` (MainTheorem.lean) is proven for every number field `K` with
`n > 1`, under `GeneralizedRiemannHypothesis K` + mathlib's `RiemannHypothesis`, for
`X ≥ 69` — the paper's Theorem 1 verbatim, constants 2.324 / 3.88 / 4.26. Axioms:
`{propext, Classical.choice, Quot.sound}`. **Whole library builds green, zero
warnings, zero sorries.**

This leg (T012-b N3–N6, all in `Theorem1.lean` + `MainTheorem.lean`):
- **N3** `nrRealPlaces_rat`/`nrComplexPlaces_rat`, `sinh_int_two` (= 1+2log2),
  `vonMangoldtSum_nonneg`, **`dSigma_rat_two_eq`** (d_{ℚ,2} = 2W+γ+logπ−1),
  **`dSigma_ge`** (2γ+2log2π−3 =: dLow ≤ d_{K,σ}, 1 < σ ≤ 2, n ≥ 2; brackets
  nonneg via I_s(σ)+1/σ = I_s(σ+1) ≤ I_s(3) = 3/2+2log2; generalize-to-atoms +
  a `2/σ = 2·(1/σ)` bridge unstuck nlinarith — linarith does NOT connect `c/x`
  with `1/x` atoms on its own).
- **N4** `ratPrimeIdeal p` (span of `(p : 𝓞 ℚ)`; primality transported along
  `Rat.ringOfIntegersEquiv` via `MulEquiv.prime_iff`; `absNorm = p` via
  `Ideal.absNorm_span_singleton` + `Algebra.norm_algebraMap` + rank-1),
  `vmIndex : Fin 9 → …` (`![...]`-matrix; injectivity by the `(absNorm, m)`
  invariant table + `decide`), **`vonMangoldtSum_rat_two_ge`** (9-term W ≥
  (21/64)log2 + (10/81)log3 + log5/25 + log7/49 + log11/121 + log13/169 ≈ 0.5012),
  **`zeroSumSigma_rat_le`** (Σℚ ≤ dLow): reduces to 12 ≤ 6W+5γ+5logπ+2log2
  (margin 0.39) with mathlib's `log_two/three/five_gt_d9`, power certificates
  `2^14 ≤ 7^5`, `2^10 ≤ 11^3`, `2^11 ≤ 13^3`, `one_half_lt_eulerMascheroniConstant`,
  `pi_gt_three`.
- **N5** `log_one_add_le_quintic` (Mercator ≤ degree-5; deficit deriv u⁵/(1+u)),
  `archKernelL_eq_log_one_add` (L(t) = log(1+u), u = 2/(eᵗ−1)),
  `exp_le_one_div_one_sub`, `log_twentyThree_thirds_ge` (log(23/3) ≥ 2.0246 via
  e² ≤ 2.7182818286²), **`beta_bound_core`** ((1/2+1/t)·eᵗ·L(t) ≤ 2 for
  t ≥ log(23/3): eᵗ·quintic(u) = 2+u²(1−u)/6+(3/20)u⁴+u⁵/5 ≤ 2.012201 at
  u ≤ 3/10, then (1/2+1/2.0246)·2.012201 ≤ 2), **`beta_bound_half`** (the
  e^{t/2}-form ≤ 2e^{−t/2} used by step1).
- **N6** the assembly (MainTheorem.lean): step1 + arch-term ≤ 6log9/√X
  (β-bound at T′ = log(X/9), e^{−T′/2} = 3/√X) + COEFF ≤ 2+log3+12/T′ ≤
  (4/3)·2.324·(1+3.88/T′) (**`log_three_lt_d9` closes the paper-tight
  (3/2)(1+log9/4) < 2.324, margin 5.4e-5**) + zero sums ≤ (√logΔ+2)² via
  `landau_stark_estimate` at σ = 1+1/√logΔ (σ ≤ 2 ⟸ logΔ ≥ 1 ⟸ |Δ| ≥ 3 =
  `abs_discr_gt_two`; `dSigma_ge` + `zeroSumSigma_rat_le`;
  (2σ−1)(logΔ+2/(σ−1)) = (√logΔ+2)² by `← hs2`-substitution + field_simp) +
  6log9 ≤ (4/3)·2.324·4.26; cancel (4/3)√X·log3X by `le_of_mul_le_mul_left`.
  Lean gotchas: identifiers may not contain `Σ`; `set L := Real.log (|discr K| : ℝ)`
  must match the goal's elaborated coercion form (ℝ-abs of cast, NOT cast-of-ℤ-abs).

**Board state**: T001–T003, T-ADM, T-BV, SP1, SP2, SP3, T010, T011, **T012** all
done. CLEANUP-1 superseded (fleet cleans on `main` post-merge). Remaining stubs
(need `/develop` before they are workable): **T013** (paper Thm 7 / Cor 8
refinements), **T014** (bridge `log κ_K` to `log(h_K R_K)` via mathlib's
`dedekindZeta_residue` class-number formula). Natural next steps beyond those:
PR `dev/dedekind-residue` → `main` (hands the sorry-free library to the cleanup
fleet), and the parked verso-blueprint render (Linux-only, `_blueprint/`).

## 2026-07-03 leg 7: SP3 HYPOTHESIS DISCHARGE COMPLETE — weil_explicit_formula_auxF landed

All pushed, axiom-clean, zero warnings. **Every hypothesis of `weil_explicit_formula`
is now discharged at `F = F_{s,X}`** (`1 < X`, `0 < a ≤ 1/4`, `a < Re s − 1`), and the
instantiated milestone **`weil_explicit_formula_auxF`** (WeilAssembly.lean, end) gives
the zero-capture limit = Poitou's (6) RHS at the auxiliary function with
`Hp = Hm = H(0)`.

The bricks of this leg (all in `WeilAssembly.lean` / `AuxAdmissible.lean`):
- **SP3-c1** `memLp_two_auxF_diffQuot` (hFdiv2).
- **SP3-c2** (AuxAdmissible) parametrised weight `auxF_mul_exp_bv_Ici` (any real
  `c < Re s − 1/2`), `boundedVariationOn_auxF_mul_exp` on `univ` (`|c| < Re s − 1/2`,
  evenness reflection flips the weight sign), `lipschitzWith_complex_re/im`,
  `locallyBoundedVariationOn_auxF_re/im` (hre/him, `c = 0`),
  `locallyBoundedVariationOn_auxF_mul_exp_re/im` (hGre/hGim, `c = 1/2+a`),
  `integrable_auxF_mul_exp` (hFa, full line).
- **SP3-c3** hΦd was over-strong (global `Differentiable ℂ (paperPhi F)` is FALSE at
  auxF — Φ-integral only converges on `1−Re s < Re < Re s`): **weakened to band-local**
  `∀ ζ, −a ≤ Re ζ ≤ 1+a → DifferentiableAt` through `tendsto_shift_vertical_sub`
  (GammaSide), `tendsto_edge_integral`, `weil_explicit_formula`; discharged by
  `differentiableAt_paperPhi_auxF` (witness ε = (a + (Re s −1))/2).
- **SP3-c4a** the IBP identity `mul_paperPhi_auxF_eq`:
  `w·Φ(z) = −∫_{log X}^∞ F'(x)(e^{wx} − e^{−wx}) dx` (`w = z−1/2`, `|Re w| < Re s−1/2`)
  via even fold `paperPhi_eq_half_line_fold`, plateau FTC (antisymmetric kernel
  vanishes at 0), tail improper-FTC at the kink; + `integrable_auxF_mul_cexp`,
  `auxF_tail_form`, `norm_auxF_tail_deriv_mul_le`.
- **SP3-c4b THE MAIN PIECE** `exists_band_bound_paperPhi_auxF`:
  `‖Φ(σ+it)‖ ≤ M/max(|t|,1)` uniformly on `σ ∈ [−a,1+a]` (small `|t|`: L¹ majorant;
  large: IBP + `‖w‖ ≥ |t|`); `tendsto_div_max_mul_log_sq` gives `B·log² → 0`.
  So hB/hBlog2 hold with `B T = M/max(T,1)`.
- **SP3-c5** `hasDerivAt_poleWindow` (`E_c' = c·E_c − 2G`) →
  `locallyBoundedVariationOn_poleWindow_add` → `..._poleWindow_auxF_re/im` (hEre/hEim).
- **SP3-c6** `eVariationOn_tsum_le` (countable subadditivity of variation —
  mathlib-worthy) + `eVariationOn_smul_translate_le`; primeSideH = weighted sum of
  translates of `G = auxF·e^{(1/2+a)x}` ⟹ `boundedVariationOn_primeSideH_auxF`
  (hHre/hHim) and `continuous_primeSideH_auxF` (M-test) ⟹ hHp/hHm at `H(0)`.

**NEXT (B–F Theorem 1 chain; consult refs REGULARLY — Poitou PDF local,
B–F 1305.0035 via alphaXiv):**
1. `primeSideH_auxF_zero_eq`: `H(0) = ∑_{𝔭,m} log N·N^{−m/2}·F_{s,X}(m log N)` — the
   weights collapse: `N^{−m(1+a)}·e^{(1/2+a)m log N} = N^{−m/2}`.
2. B–F Lemma 3 (apply the formula at `F_{s,X}`, Re s > 1 first), eq (19), Lemma 5,
   Lemma 4, `belabas_friedman_thm1` + mathlib `dedekindZeta_residue`
   (MainTheorem.lean's single intentional sorry).

---

## 2026-07-02 leg 5: SP2-RECT COMPLETE — full contour mechanics for the explicit formula

All pushed, axiom-clean, zero warnings. See decomposition-sp2.md §"SP2-RECT STATUS" for
the lemma inventory (zero capture, two-sided good heights, contour heights with the
log² Landau bound, FE folding, and Poitou's Prop 1 in quantitative form
`zero_capture_edge_form`). Bridge lemmas divisor↔zero + the global
order-ne-top (identity theorem) now make zero-set reasoning cheap.

**NEXT (per decomposition-sp2.md): SP2-vM** — `neg_logDeriv_dedekindZeta_eq_tsum`:
`−ζ_K'/ζ_K(s) = ∑_𝔭 ∑_m log(N𝔭)·N𝔭^{−ms}` on `Re s > 1` by differentiating
Chebotarev's Euler product through `TendstoLocallyUniformlyOn.deriv` (pattern:
mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`, Cotangent.lean sine-product
logDeriv). Then SP2-FJ (Fourier–Jordan; Dirichlet integral to build), SP2-Γψ (Gauss
digamma formula to build), SP2-MAIN.


## 2026-07-02 session (Fable, leg 4, third update): SP2-RECT nearly done — R-a/R-b/R-c/R-d + nonvanishing landed

**All pushed, axiom-clean. Files: `ExplicitFormula/{PhiTransform, RectangleContour, ZeroCapture}.lean`.**

- **SP2-Φ COMPLETE** (PhiTransform.lean): `paperPhi`, `integrable_paperPhi_kernel`
  (band `-ε ≤ Re s ≤ 1+ε`), `paperPhi_half_add_mul_I` (= F̂), `paperPhi_one_sub`
  (Φ(1−s) = Φ(s), even F), `hasDerivAt_paperPhi` (holomorphy),
  `integrable_admissible_majorant`, reflection helpers.
- **SP2-RECT R-b/R-c COMPLETE** (RectangleContour.lean): `rectangleIntegral` (=
  mathlib's Goursat combination), `rectangleIntegral_eq_zero`, `log_neg_of_im_pos/neg`,
  segment FTCs, **`rectangleIntegral_inv_sub`** (∮ dζ/(ζ−ρ) = 2πi),
  **`rectangleIntegral_cauchy`** (∮ Φ(ζ)(ζ−ρ)⁻¹ = 2πiΦ(ρ), dslope peel), plus
  boundary plumbing: `rectangleBoundary`, 4 segment-membership lemmas,
  `rectangleIntegral_congr/const_mul/add/finset_sum`,
  `logDeriv_eq_sum_add_of_factorization` (generic peeled-logDeriv pointwise).
- **SP2-RECT R-a COMPLETE** (ZeroCapture.lean): `completedDedekindZetaEntire_ne_zero_of_one_lt`
  (real ray, Chebotarev Euler-product positivity — FIRST cross-project import:
  `import CebotarevDensity.NumberFieldEulerProduct`, namespace `Chebotarev`),
  `convex_reProdIm`, `isBounded_Ioo_reProdIm`, `exists_H_rectangle_factorization`.
- **SP2-RECT R-d COMPLETE** (ZeroCapture.lean): **`rectangleIntegral_mul_logDeriv_H`**
  — for H boundary-zero-free + Φ holomorphic on the closed rectangle:
  `∮ Φ·H'/H = 2πi·∑ᶠ ρ, m_ρ·Φ(ρ)` over the divisor of H on the OPEN rectangle.
  (Peel on enlarged rectangle, Goursat on cofactor, per-zero Cauchy/Goursat dichotomy
  via `hsplit_closed` (closed ∖ open = boundary).)
- **Nonvanishing + strip confinement COMPLETE** (ZeroCapture.lean):
  `dedekindZeta_ne_zero_of_one_lt_re` (ζ_K(s) ≠ 0, Re > 1 — via mathlib's
  `tprod_one_add_ne_zero_of_summable` on Chebotarev's Euler product;
  `Chebotarev.norm_absNorm_cpow_neg_lt_one`, `hasSum_nonzeroIdeal_absNorm_cpow`),
  `completedDedekindZetaEntire_ne_zero_of_one_lt_re` / `_of_re_lt_zero` (FE),
  **`re_mem_of_completedDedekindZetaEntire_eq_zero`** (zeros have 0 ≤ Re ≤ 1).

**USER DIRECTIVE (2026-07-02, leg 4)**: check AINTLIB siblings for reusable machinery.
Audit done → recorded in decomposition-sp2.md §"AINTLIB reuse audit": LeanModularForms/
ForMathlib/GeneralizedResidueTheory has `generalizedResidueTheorem'` (CPV, simple poles
on-curve, winding numbers) = FALLBACK if good-heights gets painful; nothing else reusable
for vM/FJ/Γψ. Keep checking siblings before building new machinery.

**NEXT SP2 leaves (order)**:
1. **R-e good heights**: finite-set pigeonhole `∃ t ∈ [a,a+1], ∀ s ∈ S, 1/(2(N+1)) ≤ |t−s|`
   for `S.card ≤ N` (midpoints of N+1 subintervals + injective-map contradiction via
   `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`), then apply with S := im-parts of
   the divisor support of H on `ball(A+iT₀+…)`-window (STRIP CONFINEMENT makes the
   near-T zeros live in `closedBall(A+iT₀, A+2)` — counted by A4
   `exists_ball_zero_count_big`), N := C·log(2+T₀).
2. **R-f horizontal edges**: on `Im = T` (good height), `Re ∈ [-1/4, 5/4]`:
   `‖logDeriv H‖ ≤ C log²(2+T)` via A5 `exists_logDeriv_partial_fractions` + separation
   (near zeros: |s−ρ| ≥ |T−ρ.im| ≥ c/log; far zeros (|im−T| ≥ 1): |s−ρ| ≥ 1, ∑ ≤ count).
   Edge integral ≤ (3/2)·CΦ/T·C log² → 0 with the **Φ-decay hypothesis threaded**
   (hΦdecay : ‖Φ(σ+it)‖ ≤ CΦ/|t| — discharge in SP3 for concrete F, per doc Φ-d).
3. **R-g Poitou Prop 1**: apply R-d on rectangles [−a, 1+a]×[−T,T] (boundary
   nonvanishing: vertical edges by the new Re>1 / Re<0 lemmas + FE; horizontal by good
   heights), split H'/H = 1/s + 1/(s−1) + G'/G + ζ'/ζ on Re = 1+a, fold left edge by
   `paperPhi_one_sub` + `completedDedekindZetaEntire_one_sub`.
4. SP2-vM (ζ_K log-deriv series; differentiate Chebotarev's Euler product via
   `TendstoLocallyUniformlyOn.deriv`, mirror `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`).
5. SP2-FJ (Fourier–Jordan for BV: Dirichlet integral ∫sinc = π/2 NOT in mathlib —
   build via Frullani/Fubini; RL lemma ✓ `Real.tendsto_integral_exp_smul_cocompact`;
   BV monotone-split ✓ `exists_monotoneOn_sub_monotoneOn`; Stieltjes-Fubini for the
   variation part).
6. SP2-Γψ (Gauss digamma integral — NOT in mathlib, mathlib HAS digamma_one = −γ,
   digamma_one_half; series rep must be built from Gamma_seq or recurrence+asymptotic).
7. SP2-MAIN assembly (Poitou (6) chain of three displays).

**Technique notes (new this leg)**: `Subtype.mk_eq_mk.mp` beats congrArg for nested
subtype injectivity; linarith can inexplicably fail on 3-step rpow chains — use calc;
field_simp needs INSTANTIATED ne-hypotheses in context (`have he := hfac_ne 𝔭`);
`Complex.summable_ofReal`, `Summable.comp_injective`, `Complex.norm_natCast_cpow_of_pos`,
`inv_le_inv₀` (iff form); rectangle membership plumbing via `Complex.mem_reProdIm` +
`Set.uIcc_of_le`; mathlib deprecations bite: `integral_finset_sum → integral_finsetSum`,
`push_neg → push Not`, `continuousOn_finset_sum → continuousOn_finsetSum`.


## 2026-07-02 session (Fable, leg 4 continued): SP2 UNDERWAY — Φ-transform + rectangle Cauchy landed

**SP2 route doc: `.mathlib-quality/decomposition-sp2.md`** (READ FIRST for SP2 work) —
full Poitou-faithful leaf tree with verified mathlib anchors. **Poitou's paper is now
LOCAL: `refs/DedekindResidue/poitou-petits-discriminants.pdf`** (pp. 6-01–6-08 read;
his Théorème (A. Weil) p. 6-06/07 = B–F eq (1) verbatim; Props 1–3 + Lemmes 1–2 are
the proof to transcribe).

**Landed this leg (all axiom-clean, pushed):**
- `ExplicitFormula/PhiTransform.lean` (SP2-Φ COMPLETE): `paperPhi F s = ∫ F(x)e^{(s−1/2)x}dx`;
  `integrableOn_Ici_mul_cexp` (half-line domination workhorse); `integrable_paperPhi_kernel`
  (band `-ε ≤ Re s ≤ 1+ε`); `paperPhi_half_add_mul_I` (= F̂(γ), B–F (2));
  `paperPhi_one_sub` (Φ(1−s) = Φ(s) for even F — folds Poitou's left edge; his
  {Φ(s)+Φ(1−s)} = 2Φ(s)); `integral_comp_neg_real`, `integrableOn_Iio_comp_neg_iff`;
  `integrable_admissible_majorant`; `hasDerivAt_paperPhi` (holomorphy in the open band,
  dominated-deriv with |x|-absorption via the gap/2 margin).
- `ExplicitFormula/RectangleContour.lean` (SP2-RECT R-b/R-c COMPLETE — the main NEW
  mechanism): `rectangleIntegral` (bottom − top + I•right − I•left, matches mathlib's
  Goursat combination), `rectangleIntegral_eq_zero` (off-countable Goursat wrapper),
  `log_neg_of_im_pos/neg` (log(−u) = log u ∓ πi), `integral_horizontal_inv_sub` +
  `smul_integral_vertical_inv_sub` (segment FTC via `HasDerivAt.clog_real`; LEFT side
  through the reflected branch log(−(ζ−ρ))), **`rectangleIntegral_inv_sub`**
  (∮ dζ/(ζ−ρ) = 2πi, telescoping + jump identities), `integral_horizontal_split`/
  `integral_vertical_split` (dslope + Φρ·inv decomposition per segment),
  **`rectangleIntegral_cauchy`** (∮ Φ(ζ)(ζ−ρ)⁻¹dζ = 2πi·Φ(ρ); dslope peel:
  `continuousOn_dslope` needs the CONJUNCTION ⟨ContinuousOn, DifferentiableAt at ρ⟩).
- NOTE: project files use the MODULE SYSTEM — new files need `module`, `public import`,
  and `@[expose] public section` (forgot the section once: build green but declarations
  invisible to importers).

**SP1-AC is COMPLETE** (earlier this leg): A5 `exists_logDeriv_partial_fractions` +
A6 `exists_norm_digamma_le` + the generic Landau lemma `norm_logDeriv_le_of_norm_le`
(reusable!), two-radius peel `exists_H_two_radius_factorization`, window Γ-bounds.
All in `CompletedZeta/AnalyticControl.lean` (~3500 lines now).

**NEXT SP2 leaves (in order, per decomposition-sp2.md):**
1. **R-a** rectangle zero-peel: `exists_H_ball_factorization`-mirror with `U := open
   rectangle` (convex ✓ same extract_zeros_poles chain); nonvanishing witness leaf
   `H_ne_zero_of_one_lt_real` (H(x) ≠ 0 for real x > 1: Euler product positivity via
   `Chebotarev.dedekindZeta_re_pos_of_one_lt` (:817) + prefactor/Γ nonvanishing).
2. **R-e** good heights from A4 counting (pigeonhole in [T,T+1]: ∃T' with
   dist(T', ordinates) ≥ c/log T).
3. **R-f** horizontal-edge bound (A5 + good heights + Φ = O(1/T) — Φ-decay still a
   HYPOTHESIS to thread; discharge for concrete F in SP3 per the doc's Φ-d decision).
4. **R-d/R-g** argument-principle assembly + FE folding + G/ζ split (Poitou Prop 1).
5. Then SP2-vM (ζ_K log-deriv series), SP2-FJ (Fourier–Jordan, incl. Dirichlet
   integral ∫sinc = π/2 — NOT in mathlib), SP2-Γψ (Gauss digamma formula — NOT in
   mathlib; digamma_one/digamma_one_half ARE), SP2-MAIN.


## 2026-07-02 session (Fable, leg 4): SP1-AC COMPLETE — A0 through A6 all landed

**The entire analytic-control epic is done, axiom-clean, pushed (through the digamma
commit).** `AnalyticControl.lean` now ends with the two SP2 workhorses:

- **AC-A5 ✅ `exists_logDeriv_partial_fractions`**: for `|T| ≥ A+5`, `s` in the slab ball
  `closedBall (A+iT) (A+5/4)` (contains `-1 ≤ Re ≤ 2`, `|Im−T| ≤ 1`), `H s ≠ 0`:
  `‖H'/H(s) − ∑ᶠ_ρ m_ρ/(s−ρ)‖ ≤ C·log(2+|T|)` — zeros = divisor of `H` on
  `ball (A+iT) (A+2)`. Proof chain (all in AnalyticControl.lean, in order):
  `exists_H_ball_factorization` (single-ball peel, extract_zeros_poles + codiscrete→EqOn
  upgrade `eqOn_of_eventuallyEq_codiscreteWithin`), `exists_H_two_radius_factorization`
  (divisor split `D₂ = D₁ + dA`, `zpow_add'` per-factor, cofactor analytic on the BIG
  ball), `exists_H_ball_sup_big` (sup at radius A+3; third regime Re < −1 via FE
  reflection), `exists_ball_zero_count_big` (Jensen at (A+2, A+3), parametric in A),
  `norm_logDeriv_le_of_norm_le` (GENERIC Landau lemma: holomorphic log on convex ball +
  recentered borelCaratheodory_zero + Schwarz norm_deriv_le_div_of_mapsTo_ball;
  `‖h'/h‖ ≤ 32r(log(mS/mL)+1)` on `closedBall c (r−3/4)`), `exists_H_landau_cofactor`
  (assembly: max principle on the A+5/2 sphere, peel ≥ (1/2)^D, center (A+2)^D,
  envelope `e^{−n_Kπ|T|/4}` cancels in the ratio), and the logDeriv unwind
  (`logDeriv_mul`/`logDeriv_prod`/`logDeriv_fun_zpow`; peel product ↦ exactly the
  partial-fraction finsum).
- **AC-A6 ✅ `exists_norm_digamma_le`**: `‖digamma(σ+it)‖ ≤ C log(2+|t|)` on
  `-1 ≤ σ ≤ 2`, `|t| ≥ 2`. Via `digamma = logDeriv Gamma` (rfl) + the SAME generic
  Landau lemma on unit balls, fed by `exists_norm_Gamma_le_window` (σ ∈ [−2,3] upper;
  downward recurrence `norm_Gamma_eq_norm_Gamma_add_one_div`) and
  `exists_le_norm_Gamma_window` (σ ∈ [−1,2] lower, `c·e^{−π|t|/2}/(1+|t|)³`).
- Also landed en route: `re_le_of_forall_mem_frontier_re_le` (Re max principle).

**Lean-technique notes for this leg**: `MeromorphicOn.AnalyticOnNhd.divisor_nonneg`
(nested namespace!); `Pi.smul_apply'` for `(f • g) z` with function-valued `f`;
`hfin.mem_toFinset` beats `rw [Set.Finite.mem_toFinset]` after `set F := hfin.toFinset`;
`ring` CANNOT prove `a/(1+x)^3 = ((a/(1+x))/(1+x))/(1+x)` (inverse-of-sum) — use
`rw [show (1+x)^3 = (1+x)*(1+x)*(1+x) by ring, ← div_div, ← div_div]`;
`Int.toNat_natCast` after rewriting `D u = ((D u).toNat : ℤ)`; positivity can't see
`0 < ‖w‖` (provide `norm_pos_iff.mpr` + `mul_pos`); `finsum_eq_sum_of_support_subset`
for statement-level finsums; `Filter.EventuallyEq.eq_of_nhds` + `.deriv_eq` for logDeriv
congruence; `div_le_div_of_nonneg_left (ha) (hb : 0 < b) (h : b ≤ c) : a/c ≤ a/b`.

**NEXT: SP2 — the explicit formula** (task #17). Plan first (`decomposition-sp2.md`):
reread paper pp. 3–4 (eq (1)–(3) + hypotheses = `IsAdmissibleTestFn` verbatim) and the
Poitou scheme; contour of `−Λ'/Λ·F̂`-pairing over expanding rectangles with heights from
A4 counting, horizontal segments by A5, Γ-side by A6, prime side by
`Chebotarev.dedekindZeta_eq_tprod_primeIdeal` (projects/Chebotarev/CebotarevDensity/
NumberFieldEulerProduct.lean:808), F-side by `fourier_auxF` (Lemma 2, landed).
Zero-sum = `lim_{R→∞} ∑_{|Im ρ|<R}` per paper p.3.


## 2026-07-02 session (Fable): T003 + T-BV + T-ADM COMPLETE — Lemma 2 fully proven

- **Lemma 2 done** (`Lemma2.lean`, sorry-free, axiom-clean): `fourier_auxF` (eq (8) verbatim
  vs p.6 display, γ ≠ 0) + `fourier_auxF_zero` (γ = 0 companion via one FTC application —
  the integrand `(h²+(2ht+2)/t²)g` has antiderivative `-(h+1/t)g`). Chain: evenness
  reduction → plateau `sin(Tγ)/γ` → eq (7) derivatives (`hasDerivAt_gAux_core/deriv`) →
  two improper IBPs (`integral_Ioi_gAux_ibp₁/₂` via `integral_Ioi_deriv_mul_eq_sub`) →
  `tail_integral_identity` → assembly (endgame trick: field_simp then linear_combination
  against explicit `E·E⁻¹=1` (`exp_add`) and `w·w⁻¹=1` companion equations whose atom
  shapes match the field_simp normal form).
- **T-BV done** (`ExplicitFormula/TestFunction.lean`): `eVariationOn_le_integral_norm_deriv`
  (≤ ∫‖f′‖; partition increments via FTC-right + adjacent-interval chaining — NOT in
  mathlib, mathlibable), `boundedVariationOn_Ici_of_piecewise_deriv` (kink glue).
- **T-ADM done**: `IsAdmissibleTestFn` = the paper's p.3 explicit-formula hypotheses
  verbatim (even / ∃ε>0 BV+integrable weighted / diff-quotient BV / jump-average), and
  `isAdmissibleTestFn_auxF` (`ExplicitFormula/AuxAdmissible.lean`) for **Re s > 1**
  (paper-faithful regime — Lemma 3 continues analytically afterwards), ε = (Re s−1)/2.
- Paper PDF fetched fresh (arXiv 1305.0035) — pp. 3–7 re-read: explicit formula (1) and
  its test-function hypotheses verbatim, Lemma 3 = eq (13), Lemma 2 display confirmed.
- **Next: SP1-AC** (blocks SP2+SP3): mathlib has NO Hadamard factorization / finite-order
  theory (checked: only three-lines + `ZetaZeros.lean` discreteness). Chain to decompose
  (per plan, from sources): finite order of Λ_K → Jensen → zero counting → Hadamard
  order ≤ 1 → Λ′/Λ partial fractions → contour bounds. Sources to fetch into
  `refs/DedekindResidue/`: Poitou (Numdam, free) for SP2; public Hadamard notes
  (Tao 246A supplement) for the factorization chain.
- Commits this session: bfeb0694 → a7eb90bc (all pushed).

### Later same session: SP1-AC underway (Hadamard-free route) — through 40a69cd1
- **Route documents**: `.mathlib-quality/decomposition-sp1ac.md` (READ FIRST — the full leaf
  plan A0–A6 with mathlib anchors + the refined A1 PL-comparator plan).
- **AC-A0 DONE** (`Existence.lean`): `heckeFEPair_symm` (self-dual pair),
  `completedDedekindZeta_one_sub` — the clean FE `Λ_K(1-s) = Λ_K(s)`.
- **AC-A1 DONE** (`CompletedZeta/GammaStrip.lean`, all axiom-clean, Stirling-free):
  exact `norm_Gamma_half_add_mul_I_sq` (= π/cosh(πt)), `norm_Gamma_one_add_mul_I_sq`
  (= πt/sinh(πt)); `norm_Gamma_le_Gamma_re` (integral triangle);
  `norm_sin_add_mul_I_sq` (= sin²x+sinh²y); `Gamma_le_max_of_mem_Icc` (convexity);
  `norm_Gamma_sq_mul_sin_div_le` — the **Phragmén–Lindelöf comparator**
  `‖Γ(z)²sin(πz)/z²‖ ≤ 4π` on `1/2 ≤ Re ≤ 3/2` (PhragmenLindelof.vertical_strip,
  boundary values exact); payoffs `norm_Gamma_le_mul_exp` (decaying upper
  `≤ √(12π)‖z‖e^{-π|t|/2}`, base strip, |t| ≥ 1), `norm_Gamma_le_mul_exp_left`
  (left strip via recurrence), `norm_sin_pi_mul_le`, and the **matching lower**
  `le_norm_Gamma_base` (`≥ π e^{-π|t|/2}/(√(12π)‖(2-σ)-it‖)`) via reflection.
- **AC-A2 DONE** (`CompletedZeta/AnalyticControl.lean`): `norm_heckeΛ₀_le`,
  `integrable_heckeΛ₀_norm`, `exists_heckeΛ₀_strip_bound` (uniform-in-t strip bound via
  the endpoint-exponent trick), `exists_completedDedekindZetaEntire_strip_bound`
  (`‖H(s)‖ ≤ B(1+‖s‖)²` on strips).
- **NEXT: AC-A3** — ζ_K polynomial bounds on `-1 ≤ σ ≤ 2`: express
  `dedekindZeta = completedDedekindZetaEntire/(s(s-1)·prefactor·Γ-product)` and divide the
  H-strip bound by `le_norm_Gamma_base`-type lower bounds (mind: prefactor
  `|Δ|^{s/2}γ(s)` where `gammaFactor K s = Γℝ(s)^{r₁}Γℂ(s)^{r₂}`; Γℝ(s) = π^{-s/2}Γ(s/2),
  arguments s/2 ∈ [-1/2,1] need base+left strip lowers — may need a right-extension of
  `le_norm_Gamma_base` to σ ∈ [-1/2, 1/2] via reflection+recurrence, or restrict the
  convexity strip to what Jensen at center 2+iT with radius 5/2 needs: σ ∈ [-1/2, 9/2]).
  Then **AC-A4** Jensen counting via `AnalyticOnNhd.sum_divisor_le` (needs ζ_K entire
  ON THE BALL — ζ_K has a pole at s=1! For the ball centered 2+iT with |T| ≥ 3 the pole
  is outside ✓; small-T balls handled separately or count zeros of H instead — DECIDE
  when implementing; counting zeros of H = s(s-1)Λ avoids the pole and Γ has no zeros so
  strip-zeros(H) = strip-zeros(ζ_K) ∪ {0,1}-adjust — HdivisorBound may be cleaner:
  H entire ✓ sum_divisor_le applies directly with the A2-ii bound + lower |H(2+iT)| via
  Euler product + Γ-lower + prefactor: all in hand).
- Everything through 40a69cd1 pushed; zero sorries outside MainTheorem.lean's
  belabas_friedman_thm1; #print axioms clean on all new decls.

### Second /beastmode leg (same day): A3 COMPLETE + A4 center pieces — through 252361b6
- **A4-i** `exists_re_norm_dedekindZeta_ge_half` (∃ A ≥ 2 with ‖ζ_K‖ ≥ 1/2 right of A;
  Dirichlet-tail route, `card_absNorm_eq_one`), **A4-ii** `le_norm_Gamma_base_add_nat`
  (rightward Γ-lower propagation). tprod-free: the Chebotarev Euler product
  (`Chebotarev.dedekindZeta_eq_tprod_primeIdeal` in
  `projects/Chebotarev/CebotarevDensity/NumberFieldEulerProduct.lean`, verified) is
  reserved for SP2's prime side.
- **A3 COMPLETE** (route: decomposition doc §A3 REVISED — H-language, envelope-matched):
  `norm_Gammaℝ_le`, `norm_Gammaℂ_le`, `norm_gammaFactor_le` (decaying γ-uppers, rate
  n_Kπ/4); `norm_dedekindZeta_le_of_two_le_re`; `exists_H_two_line_bound` (Re = 2);
  `completedDedekindZetaEntire_one_sub` (H(1-s) = H(s)); `gammaExponent` (opaque def —
  abbrev caused whnf blowups); `one_add_abs_im_le_two_norm_sub_four`;
  `comparator_bound_right/left` (left rides on right via FE; both lines have
  |sin(π·)| = |sinh(πt)|); `comparator_bound_strip` (PL, width-3 strip admits e^{|t|});
  **`exists_H_strip_decay`**: ‖H(z)‖ ≤ C(1+|Im|)^{n_K+2}e^{-n_Kπ|Im|/4} on
  [-1,2] × {|Im| ≥ 1} — THE A3 deliverable. All in `CompletedZeta/AnalyticControl.lean`,
  axiom-clean.
- **A4 ✅ COMPLETE (f563ce33)**: `exists_ball_zero_count` — per-height zero count of H
  in slab-covering balls at A+iT is ≤ C_K·log(2+|T|), via sum_divisor_le on the
  normalized g = H/H(c) (envelope-matched ratio → polynomial), divisor transfer via
  divisor_fun_mul/divisor_const, order-finiteness by preconnectedness. Full supporting
  stack in AnalyticControl.lean: exists_H_ball_sup, exists_H_upper_right,
  exists_norm_gammaFactor_le_range, exists_norm_Gamma_le_range, exists_H_center_lower,
  exists_gammaFactor_lower, exists_le_norm_Gammaℝ/ℂ, exists_norm_Gamma_le,
  exists_le_norm_Gamma, exists_base_add_nat, norm_Gamma_le_mul_exp_add_nat.
- **NEXT: A5 Landau local partial fractions** (Complex.borelCaratheodory + A4's counting
  → truncated Λ′/Λ = Σ_{nearby ρ} 1/(s-ρ) + O(log)), then A6 digamma bounds, then SP2
  (the explicit-formula contour; Poitou/IK 5.12 scheme; Chebotarev Euler product for the
  prime side). (superseded plan below:) A4 Jensen assembly: center c = A+iT (A from A4-i; |T| ≥ 2 covers all slabs
  via T' = ±max(2,|T|)): lower ‖H(c)‖ ≥ |c||c-1|·Δ^{A/2}·γ-lower(A1-propagated,
  matching rate)·(1/2); upper on ball ⊆ strip... CAREFUL: the ball around A+iT sticks
  RIGHT of Re = 2 where exists_H_strip_decay doesn't apply — extend the decaying upper
  to [-1, A+R] (right of 2: H = s(s-1)prefactor·γ·ζ directly, γ-upper by rightward
  recurrence-propagation of norm_Gamma_le_mul_exp (UPPER analogue of
  le_norm_Gamma_base_add_nat — factors ‖z+k‖ ≤ (‖z‖+k), poly-loss), ζ ≤ T₂-const,
  |Δ^{s/2}| ≤ Δ^{(A+R)/2}) — then AnalyticOnNhd.sum_divisor_le + slab-in-ball geometry
  gives m_K(T) = O_K(log(2+|T|)). Then A5 (Landau local fractions via
  Complex.borelCaratheodory), A6 (digamma bounds), then SP2.


*Written 2026-07-01 so that any Claude account (or human) can take over mid-stream. Read this
first, then `plan.md` → `tickets.md` → `substrate-api.md` in this directory. Keep this file
updated at every commit checkpoint.*

## 0. TL;DR for a fresh session

```
cd /Users/mcu22seu/Documents/GitHub/aintlib-dedekind    # worktree, branch dev/dedekind-residue
lake exe cache get                                       # only if mathlib oleans missing
lake build DedekindResidue.CompletedZeta.PoissonSummation
```

**UPDATE 2026-07-02 (later — AGE nearly assembled).** AGE-0 ✓, AGE-1 ✓, **AGE-2 ✓**
(`dualZLattice_idealZLattice`: the dual of an ideal lattice is the `diagScale dualityWeights`
(conj∘double) twist of the trace-dual ideal lattice; pairing dictionary
`inner_diagScale_embeddingCoords` = `Tr_{K/ℚ}(ba)`; rigidity `eq_of_le_of_covolume_eq` +
`covolume_zlattice_comap` in DualLattice.lean). **AGE-3 nearly done** (`HeckeTheta.lean`):
`heckeTheta I c` (multivariable, per-place weights), `heckeTheta_unit_mul` (unit symmetry),
**`heckeTheta_inversion`** (`Θ_I(c) = covol⁻¹(∏c)^{-1/2}Θ_{I^∨}(c^∨)`, `c^∨ = (c⁻¹; 4c⁻¹)`),
`heckeWeights t u = t^{1/n}exp(2·fullLog(u)/mult)` (equivariance + periodicity + norm-ray
`∏c_w^{mult}=t`), and **`heckeG I t`** (unit-box-averaged theta). REMAINING: g-inversion
(pointwise `heckeTheta_inversion` under the box integral + `u ↦ -u` change of variables;
watch the `4^{r₂}` place-type factor: `dualPlaceWeights (heckeWeights t u) =
(1 real; 4 complex)·heckeWeights t⁻¹ (-u)` pointwise — verify and absorb into constants),
integrability estimates for `heckeG`, then **AGE-4**: `Λ := completedZetaPrefactor-normalised
∑_{classes} N(J)^s-weighted mellin(heckeG_J − const)` split at 1, agreement on `Re s > 1` via
`FundamentalCone.idealSetEquivNorm` counting + `prod_heckeWeights_pow_mult` (the per-point
Mellin gives `N(𝔞)^{-s}·Γ-factors`), `s(s-1)Λ` entire ⇒ `∃ Λ, IsCompletedDedekindZeta K Λ`
(GRH non-vacuity) + FE from the g-inversion.

**UPDATE 2026-07-02 (earlier — AGE-4 chain progressing).** AGE-0 ✓ (multivariable theta), AGE-1 ✓
(`IdealLattice.lean`: `euclideanIdealLattice`, `idealZLattice`, `covolume_idealZLattice`,
`idealTheta` + `idealTheta_transform`). Remaining chain to GRH non-vacuity is in the SP1-AGE
ticket (AGE-2/3/4). **AGE-2 WARNING (archimedean-constant trap, review Q5)**: with our PLAIN
L² metric on `euclidean.mixedSpace`, `⟪σx, σy⟫ = ∑_real x_v y_v + ∑_complex Re(x_w·conj(y_w))`
which is NOT the trace form `Tr_{K/ℚ}(xy)` at complex places (factor 2 + conjugation) — so
`dualZLattice (idealZLattice K I)` is a *scaled/conjugated* codifferent lattice, not verbatim
`(I·𝔡)⁻¹`. Derive the exact dictionary from the pairing computation BEFORE stating AGE-2;
cross-check against `Different.lean`'s `FractionalIdeal.dual` (trace-form convention) and
record the conversion in `Normalisation.lean`.

**UPDATE 2026-07-01 (GRH properly stated — user directive executed).** The project now has
**exactly one `sorry`: `belabas_friedman_thm1` itself** (the target theorem). The sorried
`completedDedekindZeta` definition is GONE, replaced by the characterisation architecture in
`FunctionalEquation.lean`: `completedZetaPrefactor` (genuine), `IsCompletedDedekindZeta K Λ`
(agrees with `prefactor·ζ_K` on `Re s > 1` where the L-series is honest, and `s(s-1)Λ`
entire) with the PROVEN uniqueness `IsCompletedDedekindZeta.eqOn` (identity theorem; values
at the poles `0,1` are junk by nature and excluded). `GRH.lean` now states
`GeneralizedRiemannHypothesis K` in the paper's verbatim form: every such `Λ` is nonvanishing
on `Re s > 1/2` off the pole `s = 1`. Genuine, junk-free, no placeholders. **Non-vacuity**
(∃ Λ, IsCompletedDedekindZeta K Λ) is Hecke's theorem = the AGE-4 target: the constructed
theta-Mellin `Λ` will inhabit the predicate and the FE `Λ(1-s)=Λ(s)` is proven of it.
Rule going forward (user): NO sorried definitions, no `True`-placeholders, ever.

**UPDATE 2026-07-01 (earlier): SP1-N DONE + AGE STARTED, AGE-0 DONE.** `Normalisation.lean`
(gammaFactor, paper-Fourier bridge `paperFourierIntegral_eq_fourierIntegral`) and the
**multivariable theta transformation `weightedThetaLattice_transform`** (AGE-0, the engine for
nontrivial unit rank) are proven, axiom-clean, pushed. The AGE decomposition (AGE-0..4, with
mathlib windfalls `FundamentalCone.idealSet`/`idealSetEquivNorm`, `euclidean.mixedSpace`,
`covolume_idealLattice`, `mellin`) is in the SP1-AGE ticket. Frontier: **AGE-1** — euclidean
ideal lattices (`ZLattice.comap` of `mixedEmbedding.idealLattice` along `toMixed`, then
transport along `(euclidean.stdOrthonormalBasis K).repr` to `EuclideanSpace ℝ (index K)`).
Goal: genuine `completedDedekindZeta` (AGE-4) so GRH is fully stated — the user's priority.

**UPDATE 2026-07-01 (earlier): SP1-AGΘ DONE.** `ThetaLattice.lean`
(sorry-free, axiom-clean) proves **`thetaLattice_transform`:
`Θ_L(t) = covol(L)⁻¹·t^{-n/2}·Θ_{L♯}(1/t)`** — the full lattice/Poisson/theta layer
(reviewer milestone (a)) is complete. Frontier: **SP1-AGE** — Hecke partial theta over ideal
classes (ideal lattices via `mixedEmbedding.idealLattice`/`latticeBasis`, codifferent =
`dualSubmodule` of the trace form for the dual side, unit fundamental domain sealed behind a
small API per review Q2). Also do **SP1-N** (normalisation file) early — the paper's Fourier
convention (`e^{+itγ}`, no 2π) vs mathlib's `𝓕` is recorded in the T003 ticket.

**UPDATE 2026-07-01 (earlier): P.3 DONE — SP1-AGP COMPLETE.** `PoissonLattice.lean`
(sorry-free, axiom-clean) has `tsum_eq_tsum_fourier_zlattice` (Poisson over an arbitrary
ℤ-lattice, covolume factor + dual lattice) and `fourier_comp_linearEquiv` (GL change of
variables for 𝓕). Frontier: **SP1-AGΘ** — Gaussian theta + transformation law; leaf plan in
the SP1-AGP ticket ("Next epic: SP1-AGΘ"). Everything below about P.2 is history.

**UPDATE 2026-07-01 (earlier): P.2 IS DONE.** `tsum_eq_tsum_fourier_zpoint` (n-dim Poisson over
`ℤ^ι`) is fully proven, sorry-free, axiom-clean — `PoissonSummation.lean` builds with zero
warnings. The §4 leaf plan below was executed exactly as written (all of e1–e6 + f landed).
The live frontier is now **P.3 (transport to a general lattice)** then **AGΘ (Gaussian theta +
transformation law)** — see the SP1-AGP ticket in `tickets.md` for the P.3 sketch: pull the
`ℤ^ι` formula back along the lattice-basis linear equiv (`Module.Basis.ofZLatticeBasis` +
`LinearEquiv` change of variables in `𝓕`, covolume factor via
`ZLattice.covolume_eq_det_mul_measureReal`), dual side via `dualZLattice` +
`covolume_dualZLattice_mul` (P.1, done); then instantiate at the Gaussian
(`fourier_gaussian_innerProductSpace` is already in mathlib;
`summable_gaussian_zlattice` discharges the convergence hypotheses).
Work in `/beastmode` style; plan any new gaps in `/develop` style (ticket per leaf, verbatim
source justification, verified mathlib lemma names).

## 1. What the project is

Formalise **Belabas–Friedman, "Computing the residue of the Dedekind zeta function"
(arXiv:1305.0035), Theorem 1** in Lean 4 / mathlib, inside the AINTLIB monorepo:

> Under GRH, `|log κ_K − f_K(X)| ≤ B(X, d_K, disc K)` (explicit bound), where
> `κ_K = Res_{s=1} ζ_K` (mathlib: `NumberField.dedekindZeta_residue K`) and `f_K(X)` is the
> prime-power sum built from the test function `F_{s,X}` (our `auxF` / `bSum` / `fK`).

**Binding constraints (user-set, non-negotiable):**
- **GRH is the SOLE hypothesis** — a `Prop` argument threaded through statements, **never an
  `axiom`**. Everything else genuinely proven.
- **General number fields** (not abelian-only).
- **Axiom bar**: every public declaration must have `#print axioms` ⊆
  `{propext, Classical.choice, Quot.sound}`.
- **No empty structures / junk witnesses / vacuous instances** — no placeholder constructions
  that make statements trivially true. Definitions must be the genuine mathematical objects.
  (mathlib-standard junk values inside total functions, e.g. `tsum = 0` when not summable, are
  fine — theorems must carry the real summability/integrability hypotheses.)
- **Faithful to the literature**: proofs mirror the paper / standard references; don't invent
  decompositions (quote-or-delete discipline from `/develop`). **Standing instruction
  (user, 2026-07-01): consult the references REGULARLY** — re-read the source before/after
  every statement-level definition; audit for drift, wrong statements, junk hypotheses.
  The paper is NOT on disk (`refs/DedekindResidue/` doesn't exist) — fetch arXiv:1305.0035
  via the alphaXiv MCP (`answer_pdf_queries` on `https://arxiv.org/pdf/1305.0035`).

**Literature audit 2026-07-01 (full paper text fetched and cross-checked):**
- `gAux` ✓ = eq. (6); `auxF` ✓ = eqs. (11)–(12); Theorem-1 statement ✓ verbatim constants
  (2.324, 3.88, 4.26, `(1+2/√log Δ)²`, `X ≥ 69`, `n > 1`, GRH(ζ_K) ∧ RH(ζ_ℚ)).
- **DRIFT CAUGHT AND FIXED**: the paper's `B_K(X)` is the *relative* sum `∑^{K−ℚ}` ("the sum
  for k is subtracted from the corresponding sum for K", p. 2) — our `bSum` was the K-sum
  only. Fixed by adding `bSumRel K X := bSum K X - bSum ℚ X` and redefining `fK` over it.
- **CONVENTION TRAP RECORDED** (T003 ticket): paper's Fourier transform (eq. 2) is
  `∫ F(t)e^{+itγ}dt` — no `2π`, opposite sign vs mathlib's `𝓕`. Lemma 2 must be stated in
  the paper's convention (plain integral), with any 𝓕-bridge filed under SP1-N.
- AGΘ target cross-checked: `Θ_L(t) = covol(L)⁻¹ t^{−n/2} Θ_{L♯}(1/t)` (standard lattice
  theta inversion, Neukirch ANT VII §3 shape) is forced by our proven Poisson +
  mathlib's `fourier_gaussian_innerProductSpace` at `b = πt`; self-consistency: applying it
  twice returns `Θ_L` via `covolume_dualZLattice_mul` (P.1).

**Confirmed route for the ζ_K functional equation** (expert review, 2026-07-01, reply in
`expert-review/2026-07-01/`): the classical **Hecke theta stack** —
(P) n-dim Poisson (Gaussian class first) → (Θ) lattice Gaussian theta + transformation law →
(H) Hecke partial theta over ideal classes, unit domain sealed behind a small API →
(FE) completed `Λ_K` + functional equation, Tate-normalisation discipline for constants.
**NOT** Tate adelic. Abelian case only as a validation harness, never as substrate.
mathlib has **no** completed Dedekind zeta / FE (checked 2026-07-01: `NumberTheory/NumberField/
DedekindZeta.lean` is L-series + residue only) — SP1 is genuinely new.

## 2. Where everything lives

- **Worktree**: `/Users/mcu22seu/Documents/GitHub/aintlib-dedekind`, branch
  **`dev/dedekind-residue`**, sharing `.git` with the main checkout
  `/Users/mcu22seu/Documents/GitHub/AINTLIB` (which stays on `main`). Remote:
  `https://github.com/CBirkbeck/AINTLIB.git`. From another machine: clone + checkout the branch.
- **Project**: `projects/DedekindResidue/` — library `DedekindResidue`, Lean **module system**
  (`module` header, `public import`, `@[expose] public section`), no copyright headers by
  AINTLIB convention.
- **Pin**: mathlib rev `11b908e5cdd9`, toolchain `v4.32.0-rc1` (moves with the central daily
  bump on `main`; rebase only at stable points, never mid-proof).
- **Process artifacts** (this directory, dev-branch only, never merged to `main`):
  `plan.md` (strategy + sub-epics), `tickets.md` (**the live board** — statuses are kept
  current), `substrate-api.md` (verified mathlib foothold map, sections A–F),
  `decomposition.md` (decompose pass), `expert-review/2026-07-01/{brief,reply,state}.md`,
  `beastmode_active` (session sentinel — **do not commit**).
- **Paper**: `refs/DedekindResidue/` via the gitignored `refs` symlink (local-only, never
  committed). `REVIEW_BRIEF.md` in the project root is the self-contained math briefing.
- **Verify recipe** (no lean MCP on this setup): build the fully-qualified module
  (`lake build DedekindResidue.CompletedZeta.<Mod>`), then axiom-check via a scratch file:
  `import DedekindResidue...; #print axioms <FQN>` run with `lake env lean <file>`.
  Never put `2>/dev/null` next to `lake`/`lean` (repo guardrail blocks it; use `2>&1`).

## 3. State of the code (2026-07-01, all committed on `dev/dedekind-residue`)

| File | Status |
|---|---|
| `Basic.lean` | residue/`dedekindZeta` re-exports + conventions. Sorry-free. |
| `AuxiliaryFunction.lean` | `gAux`, `auxF` + evenness/plateau/measurability API (**T002 done**, axiom-clean). |
| `MainTheorem.lean` | `bSum` (**T001 done**), `fK` sorry-free; `belabas_friedman_thm1` = the single target `sorry`. |
| `CompletedZeta/DualLattice.lean` | **P.1 COMPLETE, axiom-clean**: `dualZLattice`, `mem_dualZLattice`, `innerₗ_nondegenerate`, `dualZLattice_eq_span`, `DiscreteTopology`/`IsZLattice` instances, `volumeReal_fundamentalDomain_orthonormal`, **`covolume_dualZLattice_mul`** (`covol L♯ · covol L = 1`). |
| `CompletedZeta/PoissonSummation.lean` | **P.2 IN PROGRESS**. Done + axiom-clean: `zpoint`, `zpoint_add`, `summable_gaussian_zlattice`, `mFourier_neg_coe`, `periodization` + `periodization_add_zpoint`, `fourierIntegral_zpoint_eq` (the `𝓕` bridge). Remaining: **`tsum_eq_tsum_fourier_zpoint` (`sorry` ~line 155)** — plan in §4. |
| `CompletedZeta/FunctionalEquation.lean` | `completedDedekindZeta` + FE statements, both `sorry` (SP1-FE — blocked on AGP/AGΘ/AGE). |
| `CompletedZeta/GRH.lean` | GRH predicates (dual form `GRH_Λ` / `GRH_{>1/2}` per review Q4). Definitions only. |

Ticket board: SP1 sub-epics `N / AGP / AGΘ / AGE / FE / AC / Γ / GRH` (+`T-ADM`, `T-BV`);
current epic **SP1-AGP** (P.1 ✓, P.2 live, P.3 transport pending). Then AGΘ (theta = P.2/P.3 ⊕
`fourier_gaussian_innerProductSpace`, which mathlib already has), then AGE (Hecke; reuse the
codifferent-as-`dualSubmodule` from `RingTheory/DedekindDomain/Different.lean` — see
`substrate-api.md` §B), then FE/AC/GRH, then SP2 (zeros/Hadamard), SP3 (explicit formula ⇒ Thm 1).

## 4. Live frontier: `tsum_eq_tsum_fourier_zpoint` — verified leaf plan

Goal (statement already in the file, mirrors mathlib's 1-D `Real.tsum_eq_tsum_fourier`):
for continuous `g : C(EuclideanSpace ℝ ι, ℂ)` with `h_norm` (per-compact summability of
translate norms) and `h_sum` (summability of `𝓕g` at lattice points),
`∑'_{n:ι→ℤ} g (zpoint n) = ∑'_m 𝓕 g (zpoint m)`.

Engine: torus Fourier series (`UnitAddTorus`, mathlib `Analysis/Fourier/AddCircleMulti.lean`).
All footholds below **verified against the pin on 2026-07-01** (exact signatures checked):

- **(c) Periodization as a `C(·,·)`-tsum.** `P := ∑' n : ι → ℤ, g.comp (ContinuousMap.addRight
  (zpoint n))` in `C(EuclideanSpace ℝ ι, ℂ)`. Summable from `h_norm` via
  `ContinuousMap.summable_of_locally_summable_norm` (needs `LocallyCompactSpace` domain — OK,
  finite-dim). Pointwise `P x = periodization g x` via `ContinuousMap.tsum_apply`.
- **(d) Torus lift.** `π : (ι → ℝ) → UnitAddTorus ι := fun x i => ↑(x i)` is an open quotient
  map: `IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)`. Define
  `G : C(UnitAddTorus ι, ℂ)` on points by `q ↦ P (toLp (fun i => (AddCircle.equivIoc 1 0 (q i)
  : ℝ)))` (genuine Ioc-representatives — NOT a junk section). Descent identity `G (π x) = P
  (toLp x)` from the **proven** kernel/well-definedness argument (scratch compiled clean
  2026-07-01, paste-ready):

  ```lean
  -- q x = q y ⟹ x − y ∈ ℤ^ι, hence periodization agrees (uses periodization_add_zpoint)
  have hi : ∀ i, ∃ n : ℤ, x i - y i = n := fun i => by
    have h2 := congrFun h i
    rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff] at h2
    obtain ⟨n, hn⟩ := h2
    exact ⟨-n, by simp only [zsmul_eq_mul, mul_one] at hn; push_cast; linarith⟩
  choose k hk using hi
  have hxy : x = y + (fun i => (k i : ℝ)) := funext fun i => by
    have := hk i; simp only [Pi.add_apply]; linarith
  have hadd : (WithLp.equiv 2 (ι→ℝ)).symm (y + fun i => (k i:ℝ))
      = (WithLp.equiv 2 (ι→ℝ)).symm y + zpoint k := by
    ext i
    simp only [zpoint, PiLp.add_apply, Pi.add_apply, WithLp.equiv_symm_apply, WithLp.ofLp_toLp]
  rw [hxy, hadd, periodization_add_zpoint]
  ```

  Continuity of `G`: `G ∘ π = P ∘ toLp` is continuous; conclude via
  `(IsOpenQuotientMap...).isQuotientMap.continuous_iff`.
- **(e) THE key lemma — `mFourierCoeff_periodization`**: `mFourierCoeff ⇑G m = 𝓕 ⇑g (zpoint m)`
  (n-dim analogue of mathlib's `Real.fourierCoeff_tsum_comp_add`; mirror that proof's calc
  chain — read it at `Mathlib/Analysis/Fourier/PoissonSummation.lean:51`). Steps:
  1. `UnitAddTorus.mFourierCoeff_eq_integral` (with `a := fun _ => 0`) → integral over the
     Ioc-box `{x | ∀ i, x i ∈ Ioc 0 1}`.
  2. Insert descent identity; swap `∑'`/`∫` on the box (`h_norm` at the compact closed box;
     1-D used `intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm` — n-dim: dominated
     convergence / `integral_tsum` with the norm bound).
  3. Character shift-invariance: `mFourier (-m) (π (x + zpoint n)) = mFourier (-m) (π x)`
     (each coordinate shifts by an integer; via `mFourier_neg_coe` or `AddCircle.coe_add_int`).
  4. Reassemble `∑'_n ∫_box (translate n) = ∫_{ι→ℝ}` via
     `ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) volume` +
     `IsAddFundamentalDomain.integral_eq_tsum'` (verified sig: needs `Integrable f`; yields
     `∫ f = ∑' g, ∫_s f (-g +ᵥ x)`). **Watch**: ZSpan fundamental domain is the **Ico**-box,
     torus side is the **Ioc**-box — reconcile a.e. (coordinate hyperplanes are null;
     `Measure.pi`-null boundary). Integrability of the full integrand from `h_norm` summed
     (as in 1-D `integrable_of_summable_norm_Icc` — may need an n-dim analogue lemma).
  5. Finish with `fourierIntegral_zpoint_eq` (already proven in-file).
- **(f) Assembly.** `UnitAddTorus.hasSum_mFourier_series_apply_of_summable` (needs
  `Summable (mFourierCoeff ⇑G)` ⟸ (e) + `h_sum`) evaluated at `x = 0`; `mFourier m 0 = 1`
  (`fourier_eval_zero` productised); LHS `G 0 = P 0 = periodization g 0 = ∑' n, g (zpoint n)`
  (needs `zpoint`-of-`0` + `zero_add`). Conclude `tsum_eq` from `HasSum`.

After (f): **P.3** (transport `ℤ^ι → general L` by the lattice-basis linear equiv, covolume
factor via `ZLattice.covolume`; see ticket) — then **AGΘ** (theta transformation:
`fourier_gaussian_innerProductSpace` is already in mathlib, so Θ = Poisson + that lemma +
`covolume_dualZLattice_mul`).

## 5. Session-earned gotchas (will bite again)

- **Module system**: bare `Basis` unknown → `Module.Basis` (same for `Module.Basis.addHaar_self`,
  `.toMatrix_apply`, `.det_apply`).
- **Inner-product notation**: `open scoped RealInnerProductSpace` exports `⟪x, y⟫` (NO `_ℝ`
  suffix — `⟪·,·⟫_ℝ` is a mathlib-file-local notation, not importable).
- **`omit [inst] in` goes BEFORE the docstring**, else "unexpected token 'omit'".
- `ZLattice.covolume_eq_det_mul_measureReal (L) (μ := autoParam) (b) (b₀)`: `L` explicit, `μ`
  autoParam. In `rw`, pass named `(μ := volume) (b := …) (b₀ := …)`; after rewriting a carrier
  equality (e.g. `dualZLattice_eq_span`), re-fold `set`-variables with `rw [← hc, ← hcstar]`
  before the covolume rewrite pattern can match.
- **EuclideanSpace coordinates**: `ext i; simp only [zpoint, PiLp.add_apply, Pi.add_apply,
  WithLp.equiv_symm_apply, WithLp.ofLp_toLp]` is the working idiom.
- **Torus kernel**: `QuotientAddGroup.eq` + `AddSubgroup.mem_zmultiples_iff` (NOT
  `AddCircle.coe_eq_coe_iff_of_mem_Ioc`, which demands Ioc membership).
- `fourier_eq'` is namespaced: **`Real.fourier_eq'`**.
- After `integral_congr_ae` the integrand is a beta-redex — `dsimp only` before `rw` can match.
- `ring` cannot rewrite inside `cexp` — `congr 1` down to the exponent first. Sum-order
  mismatches (`∑ xᵢmᵢ` vs `∑ mᵢxᵢ`): `Finset.sum_congr rfl (fun i _ => mul_comm _ _)`.
- `Metric.finite_isBounded_inter_isClosed (discrete) (bounded) (closed) : (K ∩ s).Finite` —
  bounded set FIRST in the intersection.
- 1-D Poisson template lives at `Mathlib/Analysis/Fourier/PoissonSummation.lean:51` — mirror it.

## 6. Working conventions

- `/develop` to plan (every new leaf gets: statement, sketch, verified mathlib lemma names,
  source citation), `/beastmode` to execute (sentinel `beastmode_active`; spawn sub-tickets for
  gaps; never stop on "hard").
- Commit per green increment on `dev/dedekind-residue`; commit message style is in `git log`.
  Trailer: `Co-Authored-By: Claude <model> <noreply@anthropic.com>`.
- Producers don't clean/golf/restyle (fleet does that on `main` post-merge). Leave the
  ticket-board statuses current — the next session resumes from `tickets.md` + this file.

## 2026-07-02 — AGE-3 COMPLETE (`heckeG_inversion` proven); AGE-4 route derived, constants verified

**State**: whole project builds green; single `sorry` = `belabas_friedman_thm1`; all else
axiom-clean. Branch pushed through the `heckeG_inversion` + ticket commits.

**Landed today** (all in `CompletedZeta/HeckeTheta.lean`):
- `prod_placeWeights` / `prod_placeWeights_heckeWeights` (coordinate product = t).
- `fullLog_restrict` (fullLog onto the trace-zero hyperplane), `dualShift`,
  `fullLog_dualShift`, `heckeWeights_mul_left`/`_add_right`, `ite_mul_heckeWeights`,
  `dualPlaceWeights_heckeWeights_eq` — `c(t,u)^∨ = c(4^{2r₂}t⁻¹, -u+dualShift)`.
- `setIntegral_fundamentalDomain_comp_neg_add` — ∫ over a ZSpan box of a lattice-periodic
  f is invariant under `u ↦ -u+s` (preimage FD via `IsAddFundamentalDomain.preimage_of_equiv`,
  then `setIntegral_eq`; needed `VAddInvariantMeasure` transported from `.toAddSubgroup`
  via `inferInstanceAs`, and `Submodule.vadd_def`).
- **`heckeG_inversion : g_I(t) = covol(L_I)⁻¹·(√t)⁻¹·g_{I^∨}(4^{2r₂}·t⁻¹)`** — the
  Mellin-ready inversion.

**AGE-4 route (fully derived, see SP1-AGE ticket for detail)**: normalise
`Ĝ_C(x) := heckeG I (N(I)⁻²·β·x)`, `β := 4^{r₂}/|Δ|` — class-invariant via the new target
`heckeG_smul : heckeG (x•I) t = heckeG I (|Nx|²t)`; then `Ĝ_C(1/x) = √x·Ĝ_{C^∨}(x)` with
coefficient EXACTLY 1 (verified: covol_I⁻¹·N(I)·β^{-1/2} = 1). Sum over the class group ⇒
`f(1/x) = √x f(x)` ⇒ mathlib `WeakFEPair f f (1/2) 1` (AbstractFuncEq, the
completedRiemannZeta machinery) gives Λ₀ entire + poles ⇒ `s(s−1)Λ` entire. Agreement on
Re>1 via `P.hasMellin` + box-unfolding + per-place Gamma integrals + `idealSetEquivNorm`
counting; s-dependent constants absorbed by a `C₁·C₂^s` adjust (harmless for both
`IsCompletedDedekindZeta` conditions). **Next bricks in order**: (1a) translation-only FD
invariance (apply the neg lemma twice); (1b) `xShift`+`fullLog_xShift` (mirror dualShift,
zero-sum via `InfinitePlace.prod_eq_abs_norm`); (1c) `sq_mul_heckeWeights` (mirror
`ite_mul_heckeWeights`); (1d) `heckeTheta_smul` (generalise `unitMulLatticeEquiv` to
`mulCoords x`, `x ≠ 0`); then `heckeG_smul`, `Ĝ`, the FE-pair, integrability, decay,
Mellin agreement.

## 2026-07-03 — heckeFEPair ASSEMBLED (WeakFEPair complete); Mellin agreement is the last gap

**State**: green, single sorry = `belabas_friedman_thm1`, all axiom-clean, pushed through
`a50e5f6d`. New files: `CompletedZeta/ClassTheta.lean` (normalised class theta Ĝ_C, the
coefficient-1 symmetry `heckeGClass_inversion`, total theta `heckeF` + `heckeF_inversion`),
`CompletedZeta/ThetaEstimates.lean` (shortest vector, Gaussian tails, 0-split, weight lower
bounds, joint continuity, `continuousOn_heckeG`, `unitBoxVol`, `exists_heckeG_dev_bound`),
`CompletedZeta/FEPair.lean` (**`heckeFEPair : WeakFEPair ℂ`** — f = g = heckeF, k = 1/2,
ε = 1, f₀ = g₀ = `heckeFConst` = h·w⁻¹·vol; `isBigO_exp_neg_rpow` + transfers).

**What mathlib now gives for free** (`Mathlib.NumberTheory.LSeries.AbstractFuncEq`):
`(heckeFEPair K).Λ₀` entire, `.Λ` with poles exactly at σ ∈ {0, 1/2} + residues,
`.hasMellin` on Re σ > 1/2, `.functional_equation : Λ(1/2−σ) = Λ(σ)`.

**Verified constant derivation** (in SP1-AGE ticket, step-by-step): the final agreement is
`mellin (heckeF − heckeFConst) (s/2) = κ·2^{-r₂}·completedZetaPrefactor K s·ζ_K(s)` with κ
the (t,u)→y Jacobian constant — **s-independent** (β = 4^{r₂}/|Δ| kills every s-dependent
mismatch: `s_C^{-s/2} = N(I)^s·2^{-r₂s}|Δ|^{s/2}`, the `N(I)^s` cancels the counting side,
`2^{-r₂s}` turns `π^{-s}Γ(s)` into `Γℂ(s)/2`, `|Δ|^{s/2}` is the prefactor's power). So
`completedDedekindZeta := (κ·2^{-r₂})⁻¹·(heckeFEPair K).Λ (s/2)`, and `s(s−1)Λ_K` entire
falls out of `Λ = Λ₀ − f₀/σ − ε g₀/(k−σ)` (pole terms → entire `−2(s−1)f₀`, `+2s g₀`).

**Remaining Lean bricks to `∃ Λ, IsCompletedDedekindZeta K Λ`** (order): (α) Mellin scaling
`mellin (g∘(c·)) σ = c^{-σ}·mellin g σ` (mathlib `mellin_comp_mul_left`? verify);
(β) box-unfolding `w⁻¹∫_box ∑_{L_I∖0} = ∑_{(I∖0)/units}∫_{logSpace}` (torsion-w cancellation;
`IsAddFundamentalDomain` unfolding + `heckeTheta_unit_mul` orbit structure);
(γ) per-orbit `(t,u) → y` change of variables ⇒ `κ·Γ(σ)^{r₁}π^{-r₁σ}Γ(2σ)^{r₂}π^{-2r₂σ}·|Na|^{-2σ}`
(pins κ; the Jacobian is the regulator-style determinant of
`(τ,u) ↦ τ/n + 2·fullLog(u)_w/mult_w`); (δ) `∑_{(I∖0)/units}|Na|^{-s} = N(I)^{-s}·∑_{𝔞∈[I⁻¹]}N𝔞^{-s}`
(mathlib `FundamentalCone.idealSetEquivNorm`); (ε) sum over classes, define
`completedDedekindZeta`, prove both `IsCompletedDedekindZeta` conditions, conclude existence.
(β)+(γ) are the two big ones — both fully specified above.

**Interface alignment for (β)/(δ) (2026-07-03)**: `classRep K C = FractionalIdeal.mk0 K J_C`
with `J_C := (ClassGroup.mk0_surjective C).choose : (Ideal (𝓞 K))⁰` — INTEGRAL ideal reps,
exactly matching mathlib's cone machinery: use `fundamentalCone.idealSet K J_C` (cone ∩ the
same `idealLattice`) as the orbit-rep set. Unfolding: `L_{J_C}∖0 ≃ idealSet × (free units)`
(cone is fundamental mod torsion: `exists_unit_smul_mem` + `torsion_unit_smul_mem_of_mem`;
idealSet carries each free orbit torsionOrder-times, so `∑_{v∈L∖0} h = ∑_{a∈idealSet}∑_{l∈unitLattice} h(ε_l·a)`
with NO stray factor, and heckeG's `w⁻¹` cancels against `idealSetEquivNorm`'s `× torsion`
in (δ): `card_isPrincipal_norm_eq_mul_torsion`). For (δ) use `idealSetEquivNorm K J n`:
cone-points of norm n ≃ {principal ideals ∣-divisible by J, norm n} × torsion; then
`𝔞 = (a) ⊆ J ↦ 𝔟 := 𝔞·J⁻¹ ∈ [J]⁻¹` gives the partial zeta. Agreement needs only REAL s > 1
(both sides analytic on Re>1, identity theorem — mirror `IsCompletedDedekindZeta.eqOn`),
so all swaps are Tonelli-on-nonneg. Mellin scaling = mathlib `mellin_comp_mul_left` ✓.

**β1+β3 LANDED (2026-07-03, `MellinAgreement.lean`, commits 44099204/a3ba23f3)**:
`heckeG_sub_const_eq` (the all-t>0 deviation identity) and **`coneUnfoldEquiv`**
(`idealSet K J × (Fin (rank K) → ℤ) ≃ {x ∈ idealLattice (mk0 K J) | x ≠ 0}`, via
`exist_unique_eq_mul_prod` + `unit_smul_mem_iff_mem_torsion` + `exists_unit_smul_mem`).
**Next (β4)**: transport `coneUnfoldEquiv` through `embeddingCoords`/the euclidean comaps to
reindex `∑'_{v ∈ idealZLattice (classRep C), v≠0}` (note `classRep K C = FractionalIdeal.mk0
K J_C`, `J_C := (ClassGroup.mk0_surjective C).choose`, so the mixedSpace lattice matches);
per-point unit shift = `heckeWeights_add_logEmbedding` + `logEmbedding_fundSystem`
(`logEmb(∏fs^n) = ∑ nᵢ·basisUnitLattice i`, ℤ-combination of the box basis — mind
`basisUnitLattice` vs `(chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ`: check whether they
agree or need a base-change det-1 argument!); then tsum-reindex + `∑_n ∫_box (·+n·basis) =
∫_{logSpace}` (IsAddFundamentalDomain.integral_eq_tsum'-reverse, P.2-era machinery). Then γ
(per-orbit (t,u)→y Jacobian ⇒ Γℝ/Γ-integrals × |Na|^{-2σ}, pins κ), δ
(`idealSetEquivNorm`/`card_isPrincipal_norm_eq_mul_torsion` counting — the ×torsion cancels
heckeG's w⁻¹), ε (assemble: real s>1 agreement → identity theorem → `completedDedekindZeta`
def → `IsCompletedDedekindZeta` → existence = GRH non-vacuity).

**β COMPLETE THROUGH THE GEOMETRIC HALF (2026-07-03, commits through 37af7f48)**: in
`MellinAgreement.lean` now: `heckeG_sub_const_eq`, `coneUnfoldEquiv`, `setIntegral_box_swap`
+ `heckeG_eq_basisUnitLattice`, `euclidMixedEquiv` + `mem_idealZLattice_iff_euclidMixed` +
`euclidConeEquiv`, `logEmbedding_prod_fundSystem`, `sum_placeWeights_unit_smul`,
`tsum_ite_eq_tsum_coneUnfold`, **`heckeTheta_tail_cone`** (the tail as
`∑'_{(a,n)} exp(-π ∑ pW(c(t, u + logEmb(∏fs^n)))·ζ(y_a)²)`, `y_a` the canonical
`preimageOfMemIntegerSet` preimage), and **`integral_eq_tsum_box_shift`**
(`∫_{logSpace} f = ∑'_n ∫_box f(· + logEmb(∏fs^n))`, Integrable f). **Remaining β-glue**:
the Tonelli swap `∫_box ∑'_p (...) = ∑'_p ∫_box (...)` (use `MeasureTheory.integral_tsum`
with the summability of ∫‖·‖ — all terms nonneg, or lintegral route), then per cone point
`a` chain: `∑'_n ∫_box gauss(c(t, u+shift_n), ζ(y_a)) = ∫_{logSpace} gauss(c(t,u), ζ(y_a))`
(box-shift backwards; Integrable per-a to be produced by γ's computation or a dominated
bound). **Then γ**: for fixed a, compute `∫_0^∞ t^{σ-1} ∫_{logSpace} exp(-π ∑_w
c_w(t,u)(w y_a)²) du dt = κ·Γ(σ)^{r₁}π^{-r₁σ}·Γ(2σ)^{r₂}π^{-2r₂σ}·|N y_a|^{-2σ}` via the
per-place substitution `y_w = c_w(t,u)·(w y_a)²` — the Jacobian κ is the determinant of
`(τ, u) ↦ τ/n + 2·fullLog(u)_w/mult_w` in log-coordinates (regulator-flavoured constant,
computed once; row-reduce by adding `(mult_w/2)`-weighted rows: ∑ gives `τ/2`).
**Then δ**: `∑_{a ∈ idealSet, norm = m} 1 = torsionOrder·#{principal ideals ⊆ J of norm m}`
(`card_isPrincipal_norm_eq_mul_torsion`-style via `idealSetEquivNorm`), so
`∑'_a |N y_a|^{-2σ} = w·N(J)^{-2σ}·∑_{𝔟 ∈ [J]⁻¹-ish} N𝔟^{-2σ}` — w cancels heckeG's w⁻¹.
**Then ε**: sum classes → `ζ_K(2σ)`; at `σ = s/2` with the `s_C`-scaling
(`mellin_comp_mul_left`) → the s-independent-constant agreement; identity theorem to
Re s > 1; define `completedDedekindZeta := (κ·2^{-r₂})⁻¹·P.Λ(s/2)`; prove
`IsCompletedDedekindZeta`; conclude `∃ Λ` = GRH non-vacuity.

**γ-REDUCTION LANDED (2026-07-03, commits b2968dfd/ada27c38)**: `heckeLogEquiv` (the
(τ,u)↦λ linear equivalence, bijective via the weighted-row-sum kernel trick),
`lintegral_gaussTerm_eq_norm_scaled` (per-point y-dependence = |N(y)|²-scaling of the ray
parameter, via the PROVEN sq_mul_heckeWeights — NO Jacobian for y!), and
`lintegral_Ioi_mellin_scale` (1-D ENNReal Mellin scaling). **Consequence — the universal
constant**: define `M₀(σ) := ∫⁻_{t∈Ioi 0} ofReal(t^{σ-1})·∫⁻_u ofReal(gaussTerm t u ζ(1))`;
then per cone point `∫⁻ₜ t^{σ-1}·∫⁻_u gauss(ζ(y_a)) = ofReal(|N y_a|^{-2σ})·M₀(σ)`. The
whole agreement is now: Mellin-lintegral of (heckeF − h·w⁻¹·vol) at σ =
β^{-σ}·M₀(σ)·∑_{all integral 𝔟≠0} N𝔟^{-2σ}, with w and N(J_C) cancelling (torsion via
idealSetEquivNorm, N(J_C)^{2σ} from the s_C-scaling against the counting). Remaining:
(δ) the counting: ∑'_{a : idealSet K J} ofReal(|N y_a|)^{-2σ} = w·N(J)^{-2σ}·∑_{𝔟∈[J]⁻¹}
N𝔟^{-2σ} in ENNReal (fiber the tsum over the norm; `idealSetEquivNorm` per fiber;
{principal ⊆ J} ↔ {𝔟 ∈ [J]⁻¹} via 𝔟 = 𝔞J⁻¹); summed over classRep's: ζ_K(2σ).
(γ-main) M₀(σ) explicit: t = e^τ then `heckeLogEquiv` change of variables
(`Measure.map_linearMap_addHaar_eq_smul_addHaar`), τ = ∑_w mult_w·λ_w on the image,
product-split the Pi-lintegral, per-place ∫⁻_ℝ ofReal(e^{mσλ − πe^λ})dλ = ofReal(π^{-mσ}Γ(mσ)).
(ε) toReal + mellin-identification + identity theorem + definitions.

## 2026-07-03 (late) — ε-assembly: e-i through e-iv DONE; e-v (LSeries bridge) in progress

**Landed** (`MellinAgreement.lean`, pushed through ab0feab0): `ofReal_heckeG_sub_const` (e-i),
`setLIntegral_box_swap` + `conePreimage_ne_zero` + **`lintegral_mellin_heckeG_dev`** (e-ii — the
per-class chain, antitone-measurability route via `aemeasurable_restrict_of_antitoneOn`),
**`lintegral_mellin_heckeGClass_dev`** (e-iii — ALL cancellations w/N(J)/s_C machine-verified),
`heckeG_dev_nonneg`/`heckeGClass_dev_nonneg` + **`lintegral_mellin_heckeF_dev`** (e-iv):

  ∫⁻ Mellin of (heckeF − heckeFConst) at σ = β^{-σ}·(heckeJacobian·Γ-prod)·∑'_{𝔟:(Ideal 𝓞K)⁰}(N𝔟²)^{-σ}

Also earlier today: γ complete (`lintegral_M0_eq`, `lintegral_exp_heckeLog`, `heckeJacobian`
via Haar-uniqueness — no determinant needed), γ-N1/N2 reductions, g5 Gamma integrals.
**USER CONFIRMED the named target: `exists_isCompletedDedekindZeta`.** Remaining: e-v →
e-viii exactly as in the beastmode sentinel (full breakdown there): the LSeries/dedekindZeta
bridge at real s > 1, the toReal/hasMellin identification, the identity theorem, the
definition and the existence theorem.

## 2026-07-03 — ★★★ SP1-AGE COMPLETE: `exists_isCompletedDedekindZeta` PROVEN ★★★

**Hecke's theorem is formalized** (commit 35352d14, all pushed): for every number field K,

    theorem exists_isCompletedDedekindZeta : ∃ Λ : ℂ → ℂ, IsCompletedDedekindZeta K Λ

axiom-clean ({propext, Classical.choice, Quot.sound}), sorry-free, general K. The GRH
predicate now quantifies over a genuinely inhabited characterisation. The witness is
`completedDedekindZeta := heckeAdjust⁻¹ · (heckeFEPair K).Λ (s/2)` with the entire
extension `completedDedekindZetaEntire` built from `Λ₀` + explicit pole terms.

**CRITICAL predicate fix en route** (commit c7a3cd76): the old entirety condition
`Differentiable ℂ (fun s => s(s-1)Λ s)` was UNSATISFIABLE for total functions with
genuine poles (the product literally vanishes at 0,1 while the continuation carries the
residues). Faithful form now: `∃ H entire, ∀ s ≠ 0, s ≠ 1, H s = s(s-1)Λ s`. Uniqueness
(.eqOn) adapted; GRH statement unchanged.

**The ε-chain that closed it** (all in `MellinAgreement.lean` + `Existence.lean`):
e-i ENNReal deviation, e-ii per-class Mellin chain (antitone-measurability trick),
e-iii ALL constant cancellations machine-verified (w, N(J), s_C), e-iv the total Mellin
identity, e-v ζ-convergence from ideal-count asymptotics (`count_LSeriesSummable` extracted)
+ `dedekindZeta_real_eq`, e-vi `heckeFEPair_Λ_real` (the Λ-value = Γ–ζ closed form),
e-vii `prod_place_gamma` + `Gammaℝ/Gammaℂ_ofReal` + `heckeAdjust := heckeJacobian·2^{-r₂}` +
`Λ_half_eq_prefactor_mul_zeta`, e-viii the identity theorem (frequently-agreement along
2 + 1/(n+1); analyticity of both sides) + the definitions + the existence theorem.

**The user's directive "get the GRH done properly before we do belabas" is DISCHARGED.**
Next per ticket board: the Belabas-paper spine — T003 (Lemma 2: paperFourierIntegral of
auxF), T-ADM, T-BV, then the explicit formula and Theorem 1 (`belabas_friedman_thm1`,
still the project's single sorry).

---

## Leg 5 continued (2026-07-02): SP2-vM, SP2-FJ COMPLETE; SP2-Γψ Gauss layer landed

**SP2-vM COMPLETE** (`ExplicitFormula/PrimeSide.lean`): `neg_logDeriv_dedekindZeta_eq_tsum`
(−ζ_K'/ζ_K(s) = ∑_𝔭 log N𝔭·N𝔭^{−s}/(1−N𝔭^{−s}) for Re s > 1) via mathlib's
`logDeriv_tprod_eq_tsum` + the Euler product imported from the Chebotarev project.

**SP2-FJ COMPLETE** (`ExplicitFormula/FourierJordan.lean`, ~900 lines, all axiom-clean):
- FJ-c: the Dirichlet integral. `tendsto_integral_sinc_atTop` (∫₀^b sinc → π/2, Frullani/
  Fubini + dominated convergence), `exists_bound_primitive_sinc`/`exists_bound_integral_sinc`
  (the C_sinc uniform window constant).
- Scaling layer: `integral_sin_mul_div_eq`, `exists_bound_integral_sin_mul_div`,
  `tendsto_integral_sin_mul_div_atTop` (plateau → π/2).
- FJ-b: `integral_cexp_window` (∫_{−T}^T e^{itu}dt = 2sin(Tu)/u),
  `integral_fourier_window_collapse` (Fubini, symmetric window ↦ Dirichlet kernel).
- FJ-d: `tendsto_integral_mul_cexp_neg/pos_atTop`, `tendsto_integral_mul_sin_atTop`
  (Riemann–Lebesgue, reparametrised from mathlib's cocompact form).
- FJ-f: `abs_integral_stieltjes_kernel_le` (THE Stieltjes–Fubini engine: monotone g,
  C-bounded windows ⟹ |∫₀^δ(ḡ−ḡ(0+))K| ≤ C(ḡ(δ)−ḡ(0+)), Fubini on the triangle against
  the Lebesgue–Stieltjes measure), `abs_integral_monotone_kernel_le` (transfer to g),
  `abs_integral_monotone_sub_kernel_le` (difference-of-monotone).
- FJ-g: `tendsto_rightLim_sub_rightLim`, dirichlet-kernel facts,
  `norm_integral_sub_rightLim_kernel_le` (re/im split remainder bound),
  `integral_dirichlet_split` (far + right + reflected-left decomposition),
  `tendsto_integral_dirichlet_far` (RL), `tendsto_integral_dirichlet_plateau` (→ π),
  **`tendsto_integral_dirichlet_jordan`** (∫H·2sin(Tu)/u → π(Hp+Hm) for integrable BV H
  with one-sided limits: ε/4-assembly) and **`tendsto_fourier_window_jordan`**
  (the symmetric-window Jordan inversion — Poitou p. 6-03's "réciprocité de Fourier
  sous la forme de Jordan").

**SP2-Γψ underway** (`ExplicitFormula/GammaSide.lean`, all axiom-clean): mathlib has NO
digamma integral representation (explicit TODO in Gamma/Digamma.lean) — built from scratch:
`integral_frullani_log` (∫(e^{−x}−e^{−tx})/x = log t), `integrableOn_rpow_mul_exp_neg_mul_abs_log`,
`abs_frullani_kernel_le`, `integral_gauss_inner`, **`digamma_eq_integral_gauss_one`**
(Gauss's first form ψ(z) = ∫₀^∞(e^{−x}−(1+x)^{−z})/x dx via Γ'-integral + Frullani + Fubini),
`integrableOn_gauss_one_integrand`, **`digamma_sub_digamma_eq_integral`**
(ψ(w)−ψ(σ) = ∫₀^∞(e^{−σu}−e^{−wu})/(1−e^{−u})du — Poitou's (5) in the only form used;
KEY simplification: the counterterms cancel in differences, so Gauss's second form and the
Euler-γ integral are never needed; ψ(1/2)-values come from mathlib's digamma_one_half).

**Next (Γψ continuation)**: p. 6-04 Re-kernel identities (Re ψ(σ+it)−ψ(σ) with cos-kernels;
σ=1/2 sh-kernel; the (1/4, t/2)−(1/2, t) ch-combination; ∫dx/(2ch(x/2)) = π/2 elementary),
then Prop 3 via Lemme 1 (5-way split — REUSES the sinc-tail constants) + Lemme 2 (Plancherel).
Then Γψ-b (d log G expansion via Normalisation.lean) + Γψ-a (contour shift to Re = 1/2).
Then SP2-MAIN assembly.

---

## Leg 5 continued (2026-07-03): Prop 3's Lemme 1 + Lemme 2 + Plancherel infrastructure

All in `ExplicitFormula/GammaSide.lean`, all axiom-clean, pushed:

**Lemme 1** (γ' = −iφ): `sincTail` (+ window/deriv/decay lemmas,
`tendsto_integral_cexp_sub_div_window`), `hasDerivAt_integral_mul_cexp` (dominated
differentiation engine), `gammaFT` (Poitou's γ with improper sinc-tails),
`hasDerivAt_gammaFT`.

**Lemme 2 (IBP half)**: `rhoFT` (+ `rhoFT_zero`, `integrable_rhoFT_integrand`,
`hasDerivAt_rhoFT` — ρ' = −iμ), `norm_cexp_mul_I_sub_one_le` (chord bound), continuity
layer (`norm_muFT_le`, `continuous_muFT`, `continuous_rhoFT`, `exists_bound_sincTail`,
`continuous_integral_mul_cexp`, `continuousAt_gammaFT`, `exists_bound_gammaFT`),
`integral_rhoFT_mul_phi_eq` (IBP off zero), `integral_rhoFT_mul_phi_symm` (fixed-T
identity via ε → 0), **`tendsto_integral_rhoFT_mul_phi`** (∫_{−T}^T ρφ → −∫_ℝ μγ
given boundary decay ργ → 0 and μγ ∈ L¹). NOTE the MINUS sign — machine-checked;
Poitou's displayed "+" absorbs the odd-k reflection that appears in the Plancherel
step (k(−x) = −k(x) for Prop 3's kernel); final signs to be cross-checked against the
independently-proven `re_digamma_sub_eq_integral`.

**Plancherel infrastructure**: `muFT_eq_fourierIntegral` (μ(t) = 𝓕k(−t/2π)),
`integral_fourier_schwartz_smul` (multiplication formula vs Schwartz),
**`coeFn_fourier_toLp_two`** (L¹∩L²: the L²-𝓕 agrees a.e. with the pointwise 𝓕 —
via tempered distributions + ae_eq_zero_of_integral_contDiff_smul_eq_zero; mathlib
has this nowhere), `fourier_conj_neg`, **`integral_fourier_mul_fourier`**
(∫𝓕k·𝓕h = ∫k(−x)h(x) — the Plancherel pairing).

**REMAINING for Prop 3**: (P-c) `gammaFT F =ᵐ (fun t => 𝓕h(−t/2π))` for
h := (F0−F)/x ∈ L¹loc-near-0 ∩ L² — truncation h·1_{[−n,n]}, L²-isometry limit,
pointwise pieces-convergence, ae-subsequence. (P-d) substitution t = −2πs in ∫μγ
(factor 2π). Then hμγ-discharge (L²×L² Cauchy–Schwarz), the boundary-decay
hypotheses for the concrete odd kernel k_σ(x) = x e^{−σx}/(1−e^{−x}) (|ρ| = O(log t)
from the kernel integral; γ-decay o(1/log) is Prop 3's hypothesis on F), and the
Prop-3 statement assembly. Then Γψ-b (d log G expansion via Normalisation.lean),
Γψ-a (contour shift to Re = 1/2 using A6 + Φ-decay), I_G assembly
(digamma_one_half + integral_inv_two_cosh_half + re_digamma_quarter_sub_half),
Prop 2 (prime side via Jordan + vM series), and the Weil formula (6).

---

## Leg 5 continued (2026-07-03): Prop 3 abstract form COMPLETE

The full Plancherel chain is landed in `ExplicitFormula/GammaSide.lean` (all axiom-clean):
`tendsto_integral_cexp_sub_div_window'`, `tendsto_truncated_fourier_gammaFT` (P-c step 1),
`tendsto_eLpNorm_indicator_truncation` (P-c step 2), **`gammaFT_ae_eq_fourierL2`** (P-c:
γ = the L² Fourier transform a.e., by truncation + isometry + a.e.-subsequence + QMP
pullback), `integrable_muFT_mul_gammaFT`, **`integral_muFT_mul_gammaFT`** (P-d:
∫μγ = 2π∫k(−x)(F0−F)/x), **`tendsto_integral_rhoFT_mul_phi_eq_plancherel`**
(**Prop 3 abstract**: lim ∫_{−T}^T ρφ = −2π∫k(−x)(F0−F)/x under boundary decay ργ → 0).

**NEXT — the concrete kernel** k_σ := odd extension of x e^{−σx}/(1−e^{−x}) (x > 0):
(1) k_σ ∈ L¹∩L² (→ 1 at 0+, exp decay); (2) for odd k the ρ-fold:
ρ(t) = 2∫₀^∞ e^{−σx}(1−cos tx)/(1−e^{−x})dx = 2(Re ψ(σ+it) − ψ(σ)) — via
`re_digamma_sub_eq_integral` (ground truth, already landed); so ρ is REAL and the
−2π∫k(−x)… = +2π∫₀^∞ 2·e^{−σx}·(F0−F-even-fold)…-signs settle here; (3) boundary decay:
|ρ| = O(log|t|) elementary kernel estimate + γ = o(1/log) as Prop-3's hypothesis on F
(Poitou p. 6-06); (4) the final Prop 3 for ζ: (1/2π)-normalised pairing with
φ real-even for real-even F. Then Γψ-b (d log G via Normalisation.lean), Γψ-a
(contour shift Re 1+a → 1/2 via A6 + Φ-decay), I_G assembly (digamma_one_half,
integral_inv_two_cosh_half, re_digamma_quarter_sub_half_eq_integral), Prop 2
(prime side: Jordan + neg_logDeriv_dedekindZeta_eq_tsum), Weil (6), then SP3.

---

## Leg 5 continued (2026-07-03): PROPOSITION 3 COMPLETE

`ExplicitFormula/GammaSide.lean` now contains the full Prop-3 chain, ending in
**`prop3_poitou`**: for σ > 0 and even admissible F (integrable; (F0−F)/x locally
integrable at 0 and in L²) with boundary decay ργ → 0 at ±∞,
`lim ∫_{−T}^T 2(Reψ(σ+it) − ψ(σ))·φ(t)dt = 4π∫₀^∞ e^{−σy}(F0−F)/(1−e^{−y})dy` —
Poitou's display with all signs machine-verified. Supporting concrete-kernel layer:
`poitouKernel` (+ neg/of_pos/eq/abs-bound/measurable/L¹/L² = `integrable_poitouKernel`,
`memLp_two_poitouKernel`), `integrable_exp_neg_mul_abs`, `one_add_abs_mul_exp_le`,
`integrable_one_add_abs_mul_exp`, **`rhoFT_poitouKernel`** (ρ = 2(Reψ-diff): the
digamma bridge), `integral_poitouKernel_neg_mul` (even-F fold).

**REMAINING for the Γ-side**: discharge the boundary-decay hypotheses for SP3's F
(needs |ρ| = O(log|t|) elementary estimate + γ = o(1/log) for the concrete F — Poitou's
Remarque: BV of (F0−F)/x suffices); Γψ-b (d log G expansion: G'/G = ½log|d| +
r₁(−½logπ + ½ψ(s/2)) + r₂(−log2π + ψ(s)) from Normalisation.lean's gammaFactor);
Γψ-a (contour shift Re = 1+a → 1/2 via A6 exists_norm_digamma_le + Φ-decay);
I_G assembly (uses digamma_one_half for ψ(½) = −γ−2log2, integral_inv_two_cosh_half,
re_digamma_quarter_sub_half_eq_integral + prop3_poitou at σ = 1/2 and the
(1/4, t/2)-variant). Then Prop 2 (prime side: tendsto_fourier_window_jordan +
neg_logDeriv_dedekindZeta_eq_tsum + Prop 1's zero_capture_edge_form), and the
Weil formula (6) assembly. Then SP3 (Theorem 1).

## 2026-07-03 — Γψ COMPLETE: I_G (Poitou's Γ-side) fully landed

The entire ψ/Γ-side of Poitou's explicit formula is now machine-verified in
`ExplicitFormula/GammaSide.lean` (all axiom-clean, zero warnings):

- **Γψ-a strip bound** `exists_norm_logDeriv_gammaFactor_le`: ‖logDeriv γ_K(σ+it)‖ ≤
  C·log(2+|t|) on 1/4 ≤ σ ≤ 5/4, |t| ≥ 4 (from the d log γ_K expansion + A6 at s, s/2).
- **Γψ-d ψ-constants**: `digamma_three_quarter_sub_quarter` (ψ(3/4)−ψ(1/4) = π, via
  K4 + Gauss-difference + u=2x — NO reflection formula), `digamma_quarter_add_three_quarter`
  (logDeriv of Legendre duplication at 1/4), `digamma_half_sub_quarter`
  (ψ(1/2)−ψ(1/4) = π/2 + log 2 — the source of Poitou's r₁π/2).
- **Γψ-e rescaled Prop 3** `prop3_poitou_quarter`: lim ∫2(Reψ(1/4+it/2)−ψ(1/4))φ =
  8π∫e^{−x/2}(F0−F)/(1−e^{−2x}), via prop3_poitou at the half-scaled test function
  F(x/2)/2 (transfers: `integrable_halfScale`, `integrableOn_halfScale_div`,
  `memLp_two_halfScale_div`, `map_volume_half_mul`).
- **Γψ-f kernels**: `integrableOn_sinh_kernel_mul` (L²×L² Poitou pairing),
  `integrableOn_cosh_kernel_mul` (domination), `integral_gauss_half_eq_sinh`,
  `integral_gauss_quarter_eq_sinh_add_cosh` (quarter kernel = avg of sinh+cosh kernels).
- **Γψ-g I_G** `tendsto_IG_gammaFactor`:
  lim_{T→∞} ∫_{−T}^T 2Re(γ_K'/γ_K)(1/2+it)·φ(t) dt
    = 2π{ −(n(γ_E+log 8π) + r₁π/2)·F(0) + n∫₀^∞(F0−F)/(2sinh(x/2)) + r₁∫₀^∞(F0−F)/(2cosh(x/2)) }
  — Poitou p. 6-04's display exactly (n = r₁+2r₂ stated as such; convert via
  `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank` when assembling Weil).
  Hypotheses: F integrable, BV (re/im), right-continuous at 0, even, (F0−F)/x ∈ L¹(Ioc(−1,1)) ∩ L²(ℝ),
  plus 4 boundary-decay hypotheses ργ→0 (at σ=1/2 with F; at σ=1/4 with F(x/2)/2) —
  discharged later at SP3's concrete F. `two_re_logDeriv_gammaFactor_half` is the
  pointwise integrand split (re-extraction pattern: normalise casts to ofReal, then
  simp [add_re, re_ofReal_mul, ofReal_re, neg_re, sub_re], then linear_combination
  with log_mul/log_pow facts).

REMAINING Γ-side: Γψ-c contour shift (Re=1+a→1/2, rectangle Cauchy + strip bound ×
Φ-decay). Then Prop 2 (prime side), Weil (6) assembly, SP3.

Gotcha of the day: `∫ y in s, A + c * ∫ y in s, B` — the first ∫ swallows everything
after the comma (nested-∫ in the ring-atom diff was the tell). Parenthesise every
integral that is followed by `+`.

## 2026-07-03 (later) — Prop 2 (prime side) COMPLETE + contour shift + fold

- **Γψ-c complete**: `digamma_conj` + `logDeriv_gammaFactor_conj` (Schwarz reflection,
  via the Gauss integral — digamma_conj is mathlib-worthy), `differentiableAt_logDeriv_gammaFactor`,
  `tendsto_shift_vertical_sub` (generic Re=1+a→1/2 rectangle shift with B·C→0 decay),
  `continuous_logDeriv_gammaFactor_half`, `integral_half_line_fold` (critical-line fold
  into the 2Re-form; evenness suffices, no reality assumption).
- **Prop 2 (prime side) complete** in PrimeSide.lean + FourierJordan.lean:
  `summable_primeIdeal_pow_log_rpow`, `neg_logDeriv_dedekindZeta_eq_tsum_prod`
  (geometric m-expansion), `countable_ideal_ringOfIntegers` (instance),
  `integrable_tsum_of_summable_integral_norm` (mathlib-worthy companion),
  `integral_translate_cexp`, `primeSideH` (Poitou's H) + term-integrability +
  L¹-norm summability + `integrable_primeSideH`, `paperPhi_mul_neg_logDeriv_eq`
  (fixed-t identity: Φ·(−ζ'/ζ) = ∫He^{itu}), `tendsto_prime_side`
  (lim ∫{Φ(s)+Φ(1−s)}(−ζ'/ζ) = 2π(H(0+)+H(0−))).
- H's Jordan hypotheses (BV re/im + one-sided limits at 0) are taken as hypotheses,
  as is the ργ boundary decay on the Γ-side — all discharged at SP3's concrete F
  (compact support ⟹ locally finite sums).
- Process guardrail learned: never `lake build | tail -1 && git commit…` — the pipe
  masks build failure (tail exits 0). Build bare with exit check FIRST, then commit.

NEXT: Weil (6) assembly (edge split + Prop 1 + Prop 2 + shift + fold + I_G, T→∞
via exists_contour_height), then boundary-decay discharges, then SP3.

## 2026-07-03 (later still) — Weil assembly: W-a/W-b/W-c1 landed

WeilAssembly.lean now contains (all axiom-clean):
- **W-a** `logDeriv_completedDedekindZetaEntire_split`: on Re>1,
  Λ_ent'/Λ_ent = 1/s + 1/(s−1) + ½log|d| + γ_K'/γ_K + ζ_K'/ζ_K (ζ-differentiability
  via the entire completion, no LSeries plumbing).
- **W-b** the pole piece: `integral_cexp_neg_mul_Ioi`, `integral_cexp_mul_Iio`,
  `restrict_Iio_eq_map_sub`, `integrableOn_exp_mul_Iio`, `integral_exp_mul_Iio`,
  `poleWindow` (tail form 2e^{cu}∫_u^∞Ge^{−cw}), kernel-L¹, `tail_integral_eq`,
  `continuous_poleWindow`, `poleWindow_zero`, `integrable_poleWindow_pair`
  (half-plane-indicator Fubini), `integral_poleWindow_cexp`
  (∫E_c e^{itu} = 2(∫Ge^{itx})/(c+it)), `integrable_poleWindow`, `paperPhi_edge`,
  `integrable_F_mul_exp_half`, `poleWindow_zero_add_eq` (E_a(0)+E_{1+a}(0) = Φ(0)+Φ(1)),
  `tendsto_pole_piece` (→ 2π(Φ(0)+Φ(1))).
- **W-c1** `tendsto_const_piece`: ∫(Φ+Φ(1−·))·κ → 2πκ(F(0+)+F(0−)) — the ½log|d| piece.

REMAINING for Weil (6): W-c2 `tendsto_edge_integral` (pointwise edge-split + 4-way
interval split (all pieces continuous in t; ζ-piece = full − others) + limits:
pole (tendsto_pole_piece), disc (tendsto_const_piece at κ=½log|d|), Γ (shift-instance
of tendsto_shift_vertical_sub at g=logDeriv γ_K with C=C₀log(2+·) from
exists_norm_logDeriv_gammaFactor_le, + integral_half_line_fold via
paperPhi_half_add_mul_I, + tendsto_IG_gammaFactor), ζ (tendsto_prime_side, sign −).
Then W-c3 `weil_explicit_formula`: zero_capture_edge_form at exists_contour_height
heights, horizontal error CΦ·C(logT₀)² → 0 given Φ = o(1/log²) band decay ⟹
divisor sums → (1/2π)·[edge limit]. Then boundary/BV discharges at SP3's concrete F.

Process rule (twice burned): NEVER pipe `lake build` or sequence `; git push` —
build bare, check exit, THEN commit/push in a separate command.

## 2026-07-03 — **WEIL'S EXPLICIT FORMULA LANDED** (weil_explicit_formula, axiom-clean)

SP2's capstone is machine-verified: `weil_explicit_formula` in WeilAssembly.lean —
there is a sequence of good contour heights T n → ∞ along which
  Σᶠ ρ, divisor(Λ_ent, (−a,1+a)×(−Tn,Tn))(ρ)·Φ(ρ)
converges to
  Φ(0) + Φ(1) + log|d|·F(0) − (n(γ_E+log 8π) + r₁π/2)·F(0)
    + n∫₀^∞(F0−F)/(2sh(x/2)) + r₁∫₀^∞(F0−F)/(2ch(x/2)) − (H(0+)+H(0−)),
Poitou's (6) with the prime side folded into H(0±) (its unfolding to
−2Σ log N𝔭/N𝔭^{m/2} F(m log N𝔭) is the H-value computation at SP3's concrete F).
Route: tendsto_edge_integral (all four edge pieces jointly) + exists_contour_height
(choice sequence T n ∈ [A+5+n, A+6+n], Λ≠0 + logDeriv ≤ C log² on horizontals) +
zero_capture_edge_form (per-height bound 2(1+2a)·B(Tn)·C·log²(2+T₀n) → 0 given
B = o(1/log²)) + division by 2πi.

Hypotheses still to discharge at SP3 (concrete B–F test function; all standard):
- BV re/im of: F, F_a, poleWindow-sum E, primeSideH H (locally finite sums for
  compact support), one-sided limits Hp/Hm (continuity), htop/hbot ργ-decay at
  σ = 1/2, 1/4 (|ρ| = O(log) from A6 + rhoFT_poitouKernel; γ = o(1/log) from BV
  of (F0−F)/x per Poitou's Remarque), Φ entire (hasDerivAt_paperPhi), band bound
  B with B·log² → 0 (compact support ⟹ Φ decays like 1/t²-ish via IBP).
Then: H(0)-value = Σ log N𝔭 N𝔭^{−m/2}F(m log N𝔭) (locally finite evaluation),
Lemma 3 / (19) / Lemma 5 / Lemma 4 / belabas_friedman_thm1.

## 2026-07-03 (SP3 leg) — γ-decay chain COMPLETE; 4 Weil boundary hypotheses discharged

- `abs_sincTail_le` (|sincTail t| ≤ 2/t, IBP), `exists_norm_fourier_auxF_le`
  (φ_auxF = O(1/γ²) read off the fourier_auxF closed form — NO BV-Stieltjes needed),
  `tendsto_gammaFT_atTop/atBot` (unconditional: set-restricted RL wrappers +
  sincTail → 0), `norm_gammaFT_le_of_fourier_decay` (γ = O(1/t) via Lemme 1 +
  improper FTC; negative ray by reflection), `integrable_auxF`,
  `integrableOn_auxF_diffQuot_window` (plateau-vanishing + bounded remainder),
  `paperFourierIntegral_eq_muFT`, `tendsto_log_two_add_abs_div_abs`,
  `tendsto_rhoFT_mul_gammaFT_of_decay` (O(log)·O(1/t) squeeze),
  **`tendsto_boundary_auxF` + `tendsto_boundary_auxF_half`** — instantiating at
  σ = 1/2, 1/4 and l = atTop/atBot (with habs = tendsto_abs_atTop_atTop resp. the
  neg-composition) discharges htop2/hbot2/htop4/hbot4 of weil_explicit_formula
  at F = auxF s X. All axiom-clean.

REMAINING SP3 hypotheses of weil_explicit_formula at auxF:
(1) BV re/im of F (from isAdmissibleTestFn_auxF's pieces? its bv is on Ici 0 with
    the e^{(1/2+ε)x}-weight — need plain LocallyBoundedVariationOn on univ: auxF is
    C⁰ + piecewise-C¹ ⟹ eVariationOn_le_integral_norm_deriv per piece + evenness
    reflection), hF0 (continuity ✓ continuous_auxF), evenness ✓ (auxF_even exists?),
    hFdiv ✓ landed, hFdiv2 (MemLp 2 of the diffQuot: same plateau+bounded argument
    with the L²-window + exponential tail — mirror integrableOn_auxF_diffQuot_window
    globally: (1−F)/x bounded on |x| ≤ max(1,δ), ≤ (1+e^{hT}e^{−h|x|})/|x| beyond —
    L² ✓).
(2) hΦd : Differentiable ℂ (paperPhi (auxF s X)) — from hasDerivAt_paperPhi +
    admissibility (check its hypotheses).
(3) The band bound B with B·log² → 0: ‖paperPhi F(σ+it)‖ ≤ B|t| on σ ∈ [−a,1+a] —
    needs a σ-uniform version of the closed-form decay (fourier_auxF is at σ = 1/2
    only!). Options: generalize Lemma-2's IBP to the shifted weight (paperPhi F(σ+it)
    = paperFourierIntegral of F·e^{(σ−1/2)x} at t), or a direct two-fold IBP bound.
    THIS IS THE MAIN REMAINING ANALYTIC PIECE.
(4) BV re/im + limits of poleWindow-sum E, primeSideH H at auxF (locally-finite/
    C¹-piece arguments), Hp/Hm values.
(5) H(0)-value = Σ log N𝔭·N𝔭^{−m/2}·auxF(m log N𝔭), then Lemma 3, (19), Lemma 5,
    Lemma 4, belabas_friedman_thm1.

## 2026-07-03 leg 8: T010 COMPLETE (Lemma 3 landed) + T011 underway + blueprint bootstrapped

All pushed, axiom-clean, zero warnings. **Belabas–Friedman Lemma 3 is fully
machine-verified** and the Lemma-4 estimate suite is 3/4 done.

- **T010-b5** (GRHZeros.lean): `finite_zetaZeros_mem_of_isBounded`,
  `finsum_divisor_mul_eq_sum_zetaZeros` (window bridge, Finset.map embedding),
  `tendsto_finsum_window_zetaZeros` (window sums → tsum under GRH; Finset-exhaustion
  against HasSum, GRH pins Re = 1/2 in the band).
- **T010-b6** (NEW Lemma3.lean): `summable_zetaZeros_paperPhi_auxF` (quadratic Fourier
  decay glued to the band bound vs Landau), `tsum_zetaZeros_paperPhi_auxF_eq` (the
  explicit formula as an honest Σ' — tendsto_nhds_unique vs weil_explicit_formula_auxF);
  the three-piece split `zeroSin/Cos/IntTerm` + `paperFourierIntegral_auxF_split` +
  bounds + `tsum_zetaZeros_paperPhi_auxF_split` (the three B–F (13) zero-series).
- **T010-b7**: `auxF_ofReal`, `tsum_kernel_eq_log_zeta` (kernel prime sum =
  T·e^{hT}·log ζ_K(σ) via `real_log_dedekindZeta`), `finite_plateau_support`,
  `summable_kernel`, `primeSideH_auxF_zero_split` (H(0) = plateau defect + T e^{hT} log ζ).
- **T010 capstone**: **`lemma3_display`** — the canonical rearrangement of B–F (13)
  at real σ > 1 under GRH (2Te^{hT}·log ζ_K(σ) = Φ(0)+Φ(1)+logΔ+c_Γ+arch-integrals
  −2·plateau −S_sin −S_cos +S_int), by linear_combination of the three splits.
- **PAPER SOURCE NOW LOCAL**: `refs/DedekindResidue/bf-src/paper.tex` (arXiv e-print,
  986 lines). §3 read verbatim; T011/T012 route in
  `.mathlib-quality/decomposition-t011.md` (Lemma 4 = `Mostways` lines 409–519, applied
  at s=1; WE avoid analytic continuation by σ-tracking + σ→1⁺ limits; Lemma 5 =
  `Estimate` lines 523–562 via **eq:Stark, provable with the explicit formula at
  F(x)=e^{−(σ−1/2)|x|}** per the paper's own footnote — reuses our weil machinery +
  digamma bridges; Theorem-1 endgame lines 564–631 with the exact constant extraction).
- **T011 (Lemma4.lean, NEW)**: c1 `norm_tsum_zeroSinTerm_sub_le` (MVT via
  LipschitzWith 1 sin, no log X loss); c2 `norm_tsum_zetaZeros_mul_le` (generic) +
  `norm_tsum_zeroCosTerm_sub_le`; c3 `integrableOn_kernel` + `integral_Ioi_kernel_eval`
  (∫_T^∞(h+1/t)e^{−ht}/t = e^{−hT}/T, FTC on −e^{−ht}/t) +
  `norm_zeroIntTerm_le_refined` (‖zeroIntTerm‖ ≤ 4/(T(h²+γ²))) +
  `norm_tsum_zeroIntTerm_sub_le`.
- **Blueprint bootstrapped** (user-requested; then parked "later" — Lean priority):
  `DedekindResidueBlueprint/Blueprint.lean` (52 chunks, 63 (lean := …) refs
  machine-verified), side package `_blueprint/` (verso v4.32.0). **RENDER IS
  LINUX-ONLY**: Lean clamps RLIMIT_NOFILE to OPEN_MAX (10240) on macOS; classic-mode
  Verso importing module-system mathlib needs ~15k fds. `_blueprint/scripts/ci-pages.sh`.

**NEXT (per decomposition-t011.md + sentinel):**
1. **c4** arch integrals: σ-tracked q/q̃ difference bound (paper eq:deriv lines
   476–518) → the β(T−a) term. The display's integrals are ∫_{Ioi 0}(1−F_{σ,X})/2sinh(y/2)
   (integrand vanishes on the plateau y ≤ T).
2. **L4-b/d**: difference of `lemma3_display` at X, X/9-style cutoffs (log Δ + c_Γ +
   Φ(0)+Φ(1) cancel), relative K−ℚ (Δ_ℚ=1 via `Rat.numberField_discr`, n_ℚ=r_ℚ=1),
   then σ→1⁺: LHS via `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` (+ κ_ℚ=1),
   zero-sums by dominated convergence (majorant (9/4)m/(¼+γ²)) → **Explicit2 at k=ℚ**.
3. **L5**: weil at F_h(x)=e^{−h|x|} (new, EASIER discharge suite) → eq:Stark(σ) →
   `Estimate`.
4. **T012**: eq:Diff ((1/g(T)−1/g(T−a)) = (2/3)√X log 3X), A↔bSum bridge, numerics
   (β(log(X/9))<1 for X≥69; d_{K,σ}>1.163 via Ψ(4)=11/6−γ_E; ζℚ-sum ≤ 1.163 via
   L5-at-ℚ σ=2 certified numerics), constants 2.324/3.88/4.26.

### Leg 8 continued: T011 estimate suite — 3.9 of 4 done (through de61a4d0)

Lemma4.lean now carries, all axiom-clean/zero-warnings/pushed:
- c1 `norm_zeroSinTerm_sub_le` + `norm_tsum_zeroSinTerm_sub_le` (MVT sine difference).
- c2 `norm_tsum_zetaZeros_mul_le` (generic) + `norm_tsum_zeroCosTerm_sub_le`.
- c3 `integrableOn_kernel` + `integral_Ioi_kernel_eval` (∫_T^∞(h+1/t)e^{−ht}/t = e^{−hT}/T)
  + `norm_zeroIntTerm_le_refined` (≤ 4/(T(h²+γ²))) + `norm_tsum_zeroIntTerm_sub_le`.
- c4(A) `archKernelL` + `archKernelL_le_two_inv_sinh`; (B) `hasDerivAt_exp_half_mul_archKernelL`
  + `antitoneOn_exp_half_mul_archKernelL` (e^{U/2}L(U) decreasing — the β-monotonicity,
  NO e^{a/2} loss); (C1) `auxFCut` + bridge + `cutKernel` API + `auxFCut_sub_eq_integral`
  (FTC in the log-cutoff, kink split); (C2a) `integral_Ioi_inv_exp_sub_one/_add_one`
  closed forms; (C2b) `inner_arch_bound`
  (∫_{y>U}(w₁+w₂)cutKernel ≤ (h+1/U)e^{U/2}L(U), h-exponentials collapse exactly).

**REMAINING for c4**: (C2c) the Tonelli swap Δ(q+q̃) = ∫_{Ioc T' T}(inner) (lintegral
route; joint measurability of uncurried (U,y) ↦ w(y)·cutKernel σ y U via Measurable.ite
(measurableSet_lt measurable_fst measurable_snd); ofReal / lintegral_lintegral_swap /
toReal transfer with finiteness from C2b+C3); (C3) outer bound ≤
(T−T')(h+1/T')e^{T'/2}L(T') via the antitone kernel + monotone (h+1/U); c4-final
assembly with |r_K−1| ≤ n_K−1 (paper 497–501 at k=ℚ). Then L4-b/d, L5, T012 — the full
map with paper line refs is in the beastmode sentinel and decomposition-t011.md.

### Leg 8 final: T011 ESTIMATE SUITE COMPLETE (through 73ac378d)

c4 landed in full: `weight_mul_cutKernel_le`, `archWeight` API,
`integrableOn_archWeight_mul_cutKernel`, `integral_archWeight_mul_cutKernel_Ioi_zero`,
`inner_arch_bound'`, and **`arch_sum_diff_le`** (Δ(q+q̃) ≤ (T−T')(h+1/T')e^{T'/2}L(T'),
the paper's β-bound, via C1 cutoff-FTC + ofReal/lintegral Tonelli + antitone kernel).
All four Lemma-4 estimates are now machine-verified at real σ, axiom-clean.
NEXT: L4-a relative display (K−ℚ; Φ-terms cancel), L4-b T-difference, L4-c
realification + bounds assembly, L4-d σ→1⁺ → Explicit2 at k=ℚ. Full continuation
map in the beastmode sentinel.

### Leg 8 (cont.): L4 assembly underway (through L4-c-i)

- **L4-Q COMPLETE** (QSide.lean): `card_int/rat_ideal_absNorm_eq`,
  `dedekindZeta_rat_eq_riemannZeta` (Re>1), `completedZetaPrefactor_rat` (= Γℝ),
  `isCompletedDedekindZeta_rat` (completedRiemannZeta is Λ_ℚ; entire ext
  H = s(s−1)Λ₀+1), **`generalizedRiemannHypothesis_rat`** (mathlib RH ⟹ our GRH(ℚ)).
  Q4 (κ_ℚ = 1) deferred to T012.
- **L4-a** `lemma4_relative_display` (K−ℚ display; Φ-terms cancel, logΔ_ℚ = 0,
  arch coefficients shift by 1).
- **L4-b** `plateauSum` + `lemma4_diff_display` (two-cutoff difference; logΔ_K and
  the Γ-constant cancel).
- **L4-c(i)** `arch_display_integral_eq` (realification via integral_complex_ofReal),
  `one_sub_auxFCut_mem`, `integrableOn_{sinh,cosh}_weight_one_sub`.

**NEXT: L4-c(ii/iii)** — the Explicit2-σ estimate: (ii) arch-difference bound:
realify both display arch-diffs, ∫w(1−F_T)−∫w(1−F_T') = −∫w(F_T−F_T') (integral_sub),
Dsinh, Dcosh ≥ 0 (setIntegral_nonneg via auxFCut_sub_eq_integral-nonneg),
Dsinh+Dcosh = ∫archWeight(F_T−F_T') (integral_add) ≤ `arch_sum_diff_le`;
|(n−1)Dsinh+(r₁−1)Dcosh| ≤ (n−1)(Dsinh+Dcosh) needs hn : 1 < finrank and r₁ ≤ n.
(iii) zero-sum diffs via norm_tsum_zero{Sin,Cos,Int}Term_sub_le at K and ℚ
(triangle over the K/ℚ split). Assemble |LHS − plateau-moved| ≤
(n−1)·arch-bound + C(σ,T,T')·(Σ_K + Σ_ℚ). **THEN L4-d** σ→1⁺ (map in sentinel).
**THEN L5** (weil at e^{−h|x|} → eq:Stark → Estimate), **THEN T012**.

### Leg 8 (cont.): T011 COMPLETE, L5 COMPLETE

- **T011 (B–F Lemma 4) COMPLETE** in Lemma4.lean: `lemma4_sigma_estimate`
  (σ-tracked Explicit2, phantom-`a` instantiable) and **`lemma4_explicit2`**
  (σ→1⁺ limit): |2(T√X−T'√X')·log(κ_K/κ_ℚ) + 2ΔP_K − 2ΔP_ℚ| ≤
  (n−1)(T−T')(1/2+1/T')e^{T'/2}L(T') + [(T−T')/2 + 2(1/2+1/T) + 2(1/2+1/T')
  + 4/T+4/T']·(zeroSumSigma K 1 + zeroSumSigma ℚ 1). Limit machinery:
  tendsto_sub_one_mul_dedekindZeta_re, tendsto_log_dedekindZeta_ratio,
  tendsto_plateauSum (finite support), zeroSumSigma_anti.
- **L5 (Landau–Stark) COMPLETE** in Lemma5.lean: `expTest h = e^{−h|x|}`, full
  weil-hypothesis discharge suite (closed-form transform
  `paperPhi_expTest : Φ = 1/(h−w)+1/(h+w)` on |Re w| < h; Fourier decay 2h/γ²;
  band bound from the rational; BV via deriv-integrable + reflection;
  primeSideH M-test), packaged `weil_explicit_formula_expTest`, and:
  - **`stark_identity`** (eq:Stark ×2): 2(σ−1/2)·zeroSumSigma K σ = 2/σ +
    2/(σ−1) + logΔ − Γconst + n·I_sinh(σ) + r₁·I_cosh(σ) − 2·vonMangoldtSum K σ.
  - **`dSigma`** (B–F d_{K,σ}, arch side in integral form) and
    **`landau_stark_estimate`**: zeroSumSigma K 1 ≤ (2σ−1)(logΔ + 2/(σ−1) − dSigma).

**NEXT: T012** (endgame; paper lines 564–631):
- **T12-a**: (i) plateauSum↔bSum bridge: `bSum K X = −plateauSum K 1 X`
  (at σ=1 the plateau term is exactly minus the bSum term; boundary N^m = X
  both vanish; finsum-pair vs tsum-product bookkeeping). (ii) eq:Diff:
  √X·logX − √(X/9)·log(X/9) = ... note OUR lemma4_explicit2 LHS factor is
  2(logX·√X − logX'·√X'), X' := X/9: = (2/3)√X·(3logX − logX + log9)·... =
  (2/3)√X·log(9X²)/... CHECK against paper (2/3)√X log 3X ✓ (√(X/9) = √X/3,
  log(X/9) = logX − log9: logX√X − (√X/3)(logX−log9) = (√X/3)(2logX+log9) =
  (2√X/3)·log(3X) ✓ since 2logX+log9 = 2log3X). (iii) Step1: combine with
  landau_stark_estimate at K and ℚ (logΔ_ℚ = 0), coeff ≥ 0.
- **T12-b numerics**: dSigma's integrals → digamma via GammaSide's proven
  `digamma_sub_digamma_eq_integral` (check exact form); d_{K,σ} > 2log2π − 2Ψ(4)
  = 1.163 (n ≥ 2, vonMangoldt ≥ 0, Ψ mono); ζℚ-sum ≤ 1.163 via
  landau_stark_estimate at ℚ, σ = 2 + certified numerics (vonMangoldtSum ℚ 2 =
  Σ log p·p^{−2m} bounds, γ_E, Ψ(4) = 11/6 − γ_E); β-monotonicity + β(log(X/9))<1
  for X ≥ 69; σ := 1+1/√logΔ with |Δ| ≥ 3 (n ≥ 2 Minkowski).
- **T12-c**: Q4 κ_ℚ = 1 (dedekindZeta_residue ℚ = regulator ℚ · h/w-form:
  2^1·reg·1/(2·1) = reg; regulator ℚ = 1 rank-0) → log κ_ℚ = 0; assemble
  `belabas_friedman_thm1` (hn : 1 < finrank, X ≥ 69, constants 2.324/3.88/4.26).

### Leg 8 final state (this session): T011 + L5 + T012-a + T012-b(N1,N2) COMPLETE

Proven this session (all green, pushed, no new sorries; the single intentional
sorry remains `belabas_friedman_thm1`):
- **Lemma4.lean**: full B–F Lemma 4 — `lemma4_sigma_estimate`, `lemma4_explicit2`.
- **QSide.lean**: `generalizedRiemannHypothesis_rat`, **`dedekindZeta_residue_rat_eq_one`**
  (κ_ℚ = 1: regulator ℚ = 1, torsion 2, class number 1).
- **Lemma5.lean**: full B–F Lemma 5 — expTest discharge suite,
  `weil_explicit_formula_expTest`, **`stark_identity`** (eq:Stark),
  `dSigma`, **`landau_stark_estimate`**.
- **Theorem1.lean**: `bSum` (redesigned index, its design ticket), bridges
  **`bSum_eq_neg_plateauSum`**, `cutoff_weight_diff` (eq:Diff), **`step1`**;
  numerics N1 (`sinh_int_rec` I(σ+1)=I(σ)+1/σ, `sinh_int_mono`,
  `sinh_int_one` I(1)=2log2, `cosh_int_nonneg/le`) and N2 (`cosh_int_two`
  I_cosh(2) = π/2−(1−log2)). **No digamma anywhere.**

**REMAINING (map + margins in `.mathlib-quality/decomposition-t012b.md`, sentinel
has the live focus):**
- **N3**: `dSigma_rat_two_eq : dSigma ℚ 2 = 2·vonMangoldtSum ℚ 2 + γ_E + log π − 1`
  (unfold dSigma at ℚ, n=r₁=1, I_s(2) = 1+2log2 by rec+base, I_c(2) by N2,
  log8π = 3log2+logπ) and `dSigma_ge : 1 < σ ≤ 2 → 2γ+2log2π−3 ≤ dSigma K σ`
  (vonMangoldt ≥ 0; n ≥ 2 with bracket ≥ 0; cosh bracket ≥ 0 via cosh_int_le;
  I_s(σ)+1/σ = I_s(σ+1) ≤ I_s(3) = 3/2+2log2 via rec+mono).
- **N4**: `vonMangoldtSum ℚ 2 ≥ log2/4 + log3/9 + log5/25 + log7/49 + log2/16`
  (≥ 0.4778): five explicit indices (span p ideals of 𝓞 ℚ via
  Rat.ringOfIntegersEquiv transport, absNorm p; p=2 twice: m=1,2);
  Summable.sum_le_tsum. Then the master numeric:
  `zeroSumSigma ℚ 1 ≤ 2γ + 2log2π − 3` via landau_stark_estimate ℚ σ=2 +
  N3 + certificates (γ > 1/2: one_half_lt_eulerMascheroniSeq_six +
  eulerMascheroniSeq_lt_eulerMascheroniConstant; log2 > 0.6931:
  Real.log_two_gt_d9; logπ ≥ log3 = log2 + log(3/2), log(3/2) > 0.405;
  margin analysis says 15 ≤ 6W+5γ+5logπ+5log2 needs the N2 refinement — 
  RE-CHECK the final inequality shape in decomposition-t012b.md before coding).
- **N5**: β-bound (1/2+1/t)e^t·L(t) ≤ 2 for t ≥ log(23/3): quintic
  log(1+u) ≤ u−u²/2+u³/3−u⁴/4+u⁵/5 (derivative 0 ≤ u⁵, integrate via
  monotoneOn_of_hasDerivWithinAt_nonneg), u := 2/(e^t−1), monotone reduction,
  exp certificates (e² < 7.39, e^{0.03} < 1.031). archKernelL(T') = L form.
- **N6**: assemble `belabas_friedman_thm1` in MainTheorem.lean (replace the
  sorry; imports already flow): step1 + landau_stark_estimate at K
  (σ := 1+1/√logΔ, needs |Δ_K| ≥ 3 for n ≥ 2 — find mathlib's
  abs_discr bound name), (2σ−1)(logΔ+2/(σ−1)) = (√logΔ+2)², the ℚ-sum
  absorption (N4 master), β-absorption (N5), constants
  (3/2)(1+log9/4) < 2.324 etc. via log3 certificates. `#print axioms` check.
