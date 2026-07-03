# SP2 — the Weil–Poitou explicit formula: methodical decomposition

**Goal**: B–F eq (1) (= Poitou's Théorème (A. Weil), formule (6)) for every
`IsAdmissibleTestFn F`:

```
∑_ρ F̂(γ_ρ) = −2∑_{𝔭,m} (log N𝔭/N𝔭^{m/2}) F(m log N𝔭) + 4∫₀^∞ F(x)cosh(x/2)dx
  + F(0)(log Δ_K − n_K·γ_E − n_K log(8π) − r_K·π/2)
  + n_K ∫₀^∞ (F(0)−F(x))/(2 sinh(x/2)) dx + r_K ∫₀^∞ (F(0)−F(x))/(2 cosh(x/2)) dx
```

zero sum understood as `lim_{R→∞} ∑_{|Im ρ|<R} F̂(γ_ρ)`, `ρ = 1/2 + iγ_ρ` the
nontrivial zeros of `ζ_K` with multiplicity (= zeros of `H := completedDedekindZetaEntire`
minus none: `H(0), H(1) ≠ 0` since the simple poles of `Λ` cancel `s(s−1)`).

**Source** (LOCAL, fetched 2026-07-02): `refs/DedekindResidue/poitou-petits-discriminants.pdf`
(G. Poitou, *Sur les petits discriminants*, Sém. DPP 1976/77 exp. 6, pp. 6-01–6-08).
The whole of §1 was read and is transcribed leaf-by-leaf below. B–F p.3 defers to
exactly this ("Weil's explicit formula [12], as simplified by Poitou [9]").
Secondary: B–F pp. 3–4 (statement + hypotheses = `IsAdmissibleTestFn` verbatim).

**Standing conventions**: work with `H = completedDedekindZetaEntire K` (entire;
`H = s(s−1)·Λ` up to the fixed nonzero constant; `H(1−s) = H(s)` =
`completedDedekindZetaEntire_one_sub`). `Φ(s) := ∫_ℝ F(x)e^{(s−1/2)x}dx`;
`F̂(γ) = Φ(1/2+iγ)`.

---

## Leaf tree

### SP2-Φ — the two-sided transform (file `ExplicitFormula/PhiTransform.lean`)
Source: Poitou 6-01 "(2) Φ(s) = ∫ F(x) exp((s−1/2)x)dx … F(x)exp((1/2+a′)|x|) sommable".
- **Φ-a** `paperPhi` def + integrability: for admissible `F` (ε from the structure) and
  `|Re s − 1/2| ≤ 1/2 + a`, `a < ε`: integrand L¹. From the structure's field
  (`F·e^{(1/2+ε)x}` integrable on `[0,∞)` + evenness). Anchor: the same manipulations
  as `AuxAdmissible.lean` (integrable_auxF_kernel pattern).
- **Φ-b** `paperPhi_half_add_I_mul γ = paperFourierIntegral F γ` (ties to `fourier_auxF`'s
  LHS notion; B–F (2)).
- **Φ-c** holomorphy of Φ on the open band `−a < Re s − 1/2 − 1/2 < a`-form:
  `hasDerivAt_integral_of_dominated_loc_of_lip` (mathlib ✓, used in Lemma2 already).
- **Φ-d** **vertical decay O(1/|t|)**: `‖Φ(σ+it)‖ ≤ (V_a + sup‖·‖)/|t|`-shape, uniform
  on the band, from the BV field. Source: Poitou 6-02 "la fonction Φ(s) est o(1/|t|)
  uniformément dans la bande" — for Prop 1 only `‖Φ‖_{a,T} = o(1/log T)` is needed
  (his exact condition), and O(1/|t|) suffices. Mechanism: one Stieltjes/BV integration
  by parts. Lean route: reuse `eVariationOn` machinery (T-BV) + the piecewise-C¹
  structure of our concrete F's is NOT assumed — do the abstract version via
  `exists_monotoneOn_sub_monotoneOn` (mathlib ✓ BoundedVariation.lean:48) +
  `StieltjesFunction` measures + `MeasureTheory.integral_mul_deriv_eq...`? —
  ALTERNATIVE (cheaper, sufficient): prove O(1/|t|) only for
  even-with-BV-density F via IBP `integral_Ioi_deriv_mul_eq_sub` when F is locally
  absolutely continuous, and separately the general-BV version if SP3 needs a
  non-AC test function. Our SP3 functions (auxF-family, e^{−h|x|}) are piecewise-C¹
  with one kink+jump — the piecewise IBP version is enough. DECISION: state Φ-d for
  `IsAdmissibleTestFn` via the BV-Stieltjes route ONLY IF the piecewise route proves
  insufficient; start with a hypothesis-packaged version
  (`hΦdecay : ∀ …, ‖Φ‖ ≤ CΦ/|t|`) threaded through SP2-CONTOUR, discharged for the
  concrete F's in SP3. (Keeps SP2 unblocked; the abstract discharge is leaf Φ-d′.)

### SP2-RECT — rectangle contour mechanics (file `ExplicitFormula/RectangleContour.lean`)
Source: Poitou 6-01 "(1) ∑_{|γ|<T} Φ(ρ) − Φ(0) − Φ(1) = (1/2πi)∫ Φ(s) d log Λ(s) …
bord du rectangle [−a, 1+a]×[−T,T]".
- **R-a** rectangle zero-peel: `H = P·g` on an open neighbourhood of the closed
  rectangle, `P = ∏(z−ρ)^{m_ρ}` over the divisor, `g` analytic zero-free — VERBATIM
  the `exists_H_ball_factorization` proof with `U := Ioo-rectangle` (convexity ✓,
  `divisor_support_finite_of_subset` with the compact closed rectangle ✓,
  `MeromorphicOn.extract_zeros_poles` ✓, codiscrete upgrade ✓). Nonvanishing witness:
  `H(1+a′+i0)`? — need a point in the rectangle with `H ≠ 0`: take `2+iT₀`-type via
  `exists_re_norm_dedekindZeta_ge_half`-adjacent or simply `H` at the center-lower
  abscissa… cleanest: `H(A+iT')` for suitable `T'` inside; or use
  `dedekindZeta_re_pos_of_one_lt` (Chebotarev, line 817!) + `completedDedekindZeta`
  nonvanishing on `(1,∞)` — `H(x) ≠ 0` for real `x > 1` (all factors nonzero). Leaf:
  `H_ne_zero_of_one_lt_real`.
- **R-b** rectangle Cauchy–Goursat: `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`
  (mathlib ✓ CauchyIntegral.lean:266-ish) applied to `Φ·g'/g` — kills the zero-free part.
- **R-c** rectangle Cauchy FORMULA for the peeled factors:
  `(1/2πi)∮_{∂R} Φ(z)/(z−ρ) dz = Φ(ρ)` for `ρ` in the open rectangle. Mathlib has NO
  rectangle winding/Cauchy formula (only circles + Goursat-zero on rects). Route:
  `Φ(z)/(z−ρ) = (Φ(z)−Φ(ρ))/(z−ρ) + Φ(ρ)/(z−ρ)`; first term extends
  differentiably-off-countable (`dslope`! `differentiable_dslope`-adjacent:
  `(Φ(z)−Φ(ρ))/(z−ρ) = dslope Φ ρ z`, differentiable where Φ is — mathlib
  `DifferentiableOn.dslope`?? check; else off-countable version of Goursat with the
  one-point set) ⟹ its boundary integral is 0 by
  `integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` (mathlib ✓ :266);
  second term: `∮_{∂R} dz/(z−ρ) = 2πi` — compute the four segments explicitly:
  each side integral of `1/(z−ρ)` = log-difference along a segment not through ρ;
  sum = 2πi. Lean: parametrize, `intervalIntegral.integral_one_div`-type +
  `Complex.log` branch care — OR imaginary-part/arctan route:
  `∮ 1/(z−ρ)` over the rectangle = 2πi·(indicator of interior) is the classical
  computation with `arctan` sums; ~60–100 lines of calculus. (This is the one
  genuinely new complex-analysis mechanism SP2 needs.)
- **R-d** the assembled rectangle argument principle for H:
  `(1/2πi)∮_{∂R_T} Φ·H'/H = ∑_{ρ ∈ R_T} m_ρ·Φ(ρ)` (finite sum over the divisor),
  from R-a + R-b + R-c (logDeriv of the finite peel product = ∑ m_ρ/(z−ρ), as in
  `exists_logDeriv_partial_fractions`'s unwind).
- **R-e** good heights: from `exists_ball_zero_count` (A4): for every large T₀ there
  is `T ∈ [T₀, T₀+1]` with `dist(T, {γ}) ≥ c/log T` (pigeonhole over ≤ C·log T
  ordinates in the window; Poitou 6-01: "T … distant de tous les γ d'au moins
  α/Log T"). Leaf `exists_good_height`.
- **R-f** horizontal-edge vanishing at good heights: on the segment
  `[−a+iT, 1+a+iT]`: `H'/H = ∑_{ball} m_ρ/(s−ρ) + O(log T)` (A5 =
  `exists_logDeriv_partial_fractions`, slab ball radius A+5/4 ⊇ the segment for
  `a ≤ 1/4`), each `|s−ρ| ≥ c/log T` (good height), count ≤ C log T (A4) ⟹
  `‖H'/H‖ ≤ C log²T` on the edge ⟹ edge integral ≤ `(1+2a)·CΦ/T·C log²T → 0`.
  Source: Poitou 6-02 Prop 1 + "Comme dans E. LANDAU, Algebraische Zahlen, page 122".
- **R-g** FE-folding + splitting `H'/H = 1/s + 1/(s−1) + G'/G + ζ_K'/ζ_K` on
  `Re = 1+a` (needs `Λ = G·ζ_K` there = `completedDedekindZeta_eq_of_one_lt_re` ✓
  landed, `G := completedZetaPrefactor·gammaFactor`), left edge ↦ right edge via
  `s ↦ 1−s` (`H(1−s) = H(s)` ✓): conclusion = Poitou Prop 1:
  `∑_{|γ|<T} Φ(ρ) − Φ(0) − Φ(1) = I_ζ(T) + I_G(T) + o(1)` with both `I`'s on the
  single vertical segment `Re = 1+a`, integrand `{Φ(s)+Φ(1−s)}·(−logDeriv …)`.

### SP2-RECT STATUS (2026-07-02, leg 5): ✅ COMPLETE (all in ExplicitFormula/ZeroCapture.lean
unless noted; RectangleContour.lean holds the generic mechanics)
- R-a ✅ `exists_H_rectangle_factorization` + witness `completedDedekindZetaEntire_ne_zero_of_one_lt`
- R-b/R-c ✅ `rectangleIntegral_eq_zero`, `rectangleIntegral_inv_sub`, `rectangleIntegral_cauchy`
- R-d ✅ `rectangleIntegral_mul_logDeriv_H` (+ boundary plumbing, `logDeriv_eq_sum_add_of_factorization`)
- R-e ✅ `exists_dist_ge_of_card_le` + **two-sided** `exists_good_height` (both `|T∓Im ρ|`)
  + bridges `meromorphicOrderAt_…_ne_top` (identity theorem), `…_eq_zero_of_divisor_ne_zero`,
  `divisor_ne_zero_of_…_eq_zero`
- R-f ✅ `exists_contour_height` (both edges zero-free + `‖H'/H‖ ≤ C log²(2+T₀)` on
  `-1/4 ≤ Re ≤ 5/4`; A5's count-conjunct was exported for this)
- R-g ✅ `rectangle_zero_capture` (∮ΦH'/H = 2πi∑m_ρΦ(ρ) on `[-a,1+a]×[-T,T]`),
  `logDeriv_completedDedekindZetaEntire_one_sub` (H'/H(1−s) = −H'/H(s)),
  `rectangleIntegral_fold_vertical` (left edge folds onto right: `(Φ+Φ(1−·))·H'/H`),
  `zero_capture_edge_form` (**Poitou Prop 1, quantitative**: zero sum − folded edge
  integral bounded by `2(1+2a)·CΦ·Cl`)
- REMAINING for the full Prop 1 limit (deferred to SP2-MAIN): instantiate Φ := paperPhi F,
  CΦ := O(1/T) (Φ-d decay, still hypothesis-packaged), Cl from `exists_contour_height`,
  T → ∞ through contour heights; then split the right-edge integral H'/H = 1/s + 1/(s−1)
  + G'/G + ζ'/ζ (subtract `rectangleIntegral_cauchy` at ρ = 0, 1 for the −Φ(0) −Φ(1)
  terms; the H-divisor itself carries no mass at 0,1).

### SP2-vM — the prime side series (file `ExplicitFormula/PrimeSide.lean`)
Source: Poitou 6-02 "− d log ζ_K(s)/ds = ∑_{𝔭,m} (log N𝔭)/(N𝔭)^{ms}".
- **vM-a** `neg_logDeriv_dedekindZeta_eq_tsum`: for `Re s > 1`:
  `−ζ_K'/ζ_K(s) = ∑_{𝔭} ∑_{m≥1} log(N𝔭)·N𝔭^{−ms}` with normal convergence on
  `Re ≥ 1+a`. Route: differentiate Chebotarev's Euler product
  (`Chebotarev.dedekindZeta_eq_tprod_primeIdeal`, NumberFieldEulerProduct.lean:808)
  through `TendstoLocallyUniformlyOn.deriv` (mathlib ✓ LocallyUniformLimit.lean) on
  partial products, or logDeriv of finite products + limits (pattern:
  mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` for ℚ, Dirichlet.lean:434,
  and the Cotangent.lean sine-product logDeriv). Per-factor:
  `logDeriv (1−N𝔭^{−s})⁻¹ = −log N𝔭·N𝔭^{−s}/(1−N𝔭^{−s}) = −∑_m log N𝔭·N𝔭^{−ms}`.
- **vM-b** Fubini/normal-convergence package: the double family
  `(𝔭,m) ↦ log N𝔭·N𝔭^{−m(1+a)}` is summable (compare `∑_𝔭 log N𝔭·N𝔭^{−(1+a)}·(1−N𝔭^{−(1+a)})⁻¹`
  ≤ ζ_K-type comparison; anchors: `hasSum_nonzeroIdeal_absNorm_cpow` (Chebotarev:515),
  `Nat.card`-norm summability from AGE work).

### SP2-FJ — Fourier–Jordan inversion for BV (file `ExplicitFormula/FourierJordan.lean`)
Source: Poitou 6-03 "Il résulte alors de la réciprocité de Fourier (sous la forme de
Jordan) que l'intégrale I_ζ(T) a pour limite … −2H(0)" + Prop 2.
THE stand-alone real-analysis brick (mathlib has inversion only for `f, f̂ ∈ L¹` at
continuity points — not Jordan's form).
- **FJ-a** statement: `H : ℝ → ℂ` integrable, BV on ℝ (`eVariationOn ≠ ⊤`), jump-mean
  at 0 (`H 0 = (lim_{0+} H + lim_{0−} H)/2`): then
  `(1/2π)∫_{−T}^{T} (∫ H(u)·e^{itu} du) dt → H 0` as `T → ∞`.
- **FJ-b** kernel collapse (Fubini): inner-outer swap ⟹ `(1/π)∫ H(u)·sin(Tu)/u du`
  (mathlib `MeasureTheory.integral_integral_swap`; integrand jointly L¹ on
  `[−T,T]×ℝ`).
- **FJ-c** Dirichlet integral `∫₀^∞ sin x/x dx = π/2` (as
  `Tendsto (∫₀^b sinc) atTop (π/2)`): NOT in mathlib (checked Sinc.lean — only
  algebraic lemmas). Build: Frullani/Fubini route
  `∫₀^b sin x/x = ∫₀^b sin x ∫₀^∞ e^{−xy} dy dx` swap + `∫₀^∞ e^{−xy} sin x dx = 1/(1+y²)`
  (mathlib `integral_exp_mul_sin`?? check `Integrals.lean`; else 10-line IBP pair) +
  dominated convergence ⟹ `arctan` limit. Plus the uniform tail bound
  `C_sinc := sup_{0≤A≤B} |∫_A^B sin x/x|  < ∞` (corollary of convergence + continuity).
- **FJ-d** Riemann–Lebesgue away from 0: `u ↦ H(u)/u·1_{|u|≥δ}` ∈ L¹ ⟹
  `∫ … sin(Tu) → 0` (`Real.tendsto_integral_exp_smul_cocompact`, mathlib ✓
  RiemannLebesgueLemma.lean:208; sin = combination of exps).
- **FJ-e** near-zero, plateau part: `∫_{0}^{δ} H(0+)·sin(Tu)/u du → (π/2)H(0+)`
  (FJ-c after `u ↦ Tu`).
- **FJ-f** near-zero, variation part: `|∫₀^δ (H(u)−H(0+))·sin(Tu)/u du| ≤ C_sinc·V(H;(0,δ])`
  — Stieltjes–Fubini against the monotone decomposition
  (`exists_monotoneOn_sub_monotoneOn` mathlib ✓ + `StieltjesFunction.measure` ✓;
  right-continuous modification changes neither side): for monotone g with g(0+)=0:
  `∫₀^δ g(u)K_T(u)du = ∫_{(0,δ]} (∫_v^δ K_T) dμ_g` (Fubini for the product measure,
  `g(u) = μ_g((0,u])`), and `|∫_v^δ sin(Tu)/u du| ≤ 2C_sinc`. Then `V(H;(0,δ]) → 0`
  as `δ → 0` (variation continuity from above at a point where H is right-regular —
  BV ⟹ one-sided limits exist; `eVariationOn`-monotonicity + `iSup` argument).
  Mirror for `(−δ, 0)`. This is the technical heart; ~2–4 bricks.
- **FJ-g** assembly: FJ-b…f ⟹ FJ-a. Then the **shifted/cos variants** used twice:
  `(1/2π)∫_{−T}^T φ(t)cos(xt)dt → (F(x)+F(−x))/2 = F(x)` for the Γ-side (φ = F̂),
  and Prop 2's prime-side application with
  `H(u) := ∑_{𝔭,m} (log N𝔭/N𝔭^{m/2}) F_a-translates` (BV: Poitou 6-03's V-inequality,
  jump-mean inherited — his "Enfin, la condition de moyenne 2H(x) = H(x+0)+H(x−0) est
  vérifiée pour H dès qu'elle l'est pour F").

### SP2-Γψ — the archimedean side (file `ExplicitFormula/GammaSide.lean`)
Source: Poitou 6-03/6-04 (Calcul de la partie archimédienne) + 6-04/6-05/6-06
(Prop 3, Lemmes 1–2).
- **Γψ-a** move `I_G` from `Re = 1+a` to `Re = 1/2` + conjugate-fold: allowed since
  `‖G'/G‖ = O(log|t|)` in the band (A6 `exists_norm_digamma_le` + prefactor linear
  term + `digamma(s/2)` at `Re s/2 ∈ [1/4, (1+a)/2]` ⊆ window ✓) and Φ = O(1/|t|):
  the connecting horizontals vanish; Cauchy–Goursat on the strip rectangle
  (G'/G analytic there — Γ has no zeros/poles in `0 < Re`; `digamma` analyticity:
  `Complex.differentiableAt_Gamma` quotient or `meromorphic_digamma` off poles).
- **Γψ-b** `d log G` expansion (Poitou 6-03 display): `G'/G(s) = (1/2)log|d| +
  r₁(−(1/2)log π + (1/2)ψ(s/2)) + r₂(−log 2π + ψ(s))` — from
  `gammaFactor`/`completedZetaPrefactor` definitional work (Normalisation.lean ✓ has
  the conventions; `Complex.deriv_cpow`-type for `|d|^{s/2}`, `Γℝ'/Γℝ`, `Γℂ'/Γℂ`).
- **Γψ-c** **Gauss's formula** (Poitou (5)): `ψ(z) = −∫₀^∞ (e^{−xz}/(1−e^{−x}) − e^{−x}/x) dx`
  for `Re z > 0`. NOT in mathlib (Digamma.lean is 64 lines; checked). Route:
  (i) `ψ(z) − ψ(1) = ∫₀^∞ (e^{−x} − e^{−zx})/(1−e^{−x}) dx` from the recurrence/series:
  telescoping `ψ(z+n)` via `digamma_apply_add_one` + the asymptotics, or directly the
  standard series `ψ(z) = −γ + ∑_{n≥0} (1/(n+1) − 1/(n+z))` — mathlib has NO series
  rep either ⟹ derive it: `logDeriv` of the Weierstrass/Euler product of Γ — mathlib
  has `Complex.Gamma_seq_tendsto_Gamma` (Euler's limit formula) — logDeriv through the
  limit via `TendstoLocallyUniformlyOn.deriv`… OR from
  `digamma_apply_add_one` (ψ(s+1) = ψ(s) + 1/s) iterated + `ψ(n+1) = H_n − γ`
  (`digamma_one` + induction) + the limit `ψ(z+N) − log N → 0` (from Stirling?
  mathlib `Complex.Stirling`?? — check `Real.log_Gamma`… risky). SAFEST series route:
  geometric expansion under the integral: for `Re z > 0`:
  `∫₀^∞ (e^{−x} − e^{−zx})/(1−e^{−x}) dx = ∑_{n≥0} ∫₀^∞ (e^{−(n+1)x} − e^{−(n+z)x}) dx
  = ∑_{n≥0} (1/(n+1) − 1/(n+z))` (Tonelli ✓ elementary), so (i) reduces to the SERIES
  rep of ψ — which itself reduces by telescoping+limit to
  `ψ(z+N) − ψ(1+N) → 0` — hmm; DECIDE at implementation: the cleanest mathlib-native
  path may be `deriv`-of-`LogGamma` series if `Complex.logGamma_eq_tsum`?? (check
  `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean` + `GammaCompletion`…).
  Fallback (fully self-contained): prove the SERIES rep from
  `Gamma_seq_tendsto_Gamma` + logDeriv interchange (locally uniform on compacts of
  `ℂ ∖ −ℕ` — the same machinery as vM-a). Then (ii) `γ = ∫₀^∞ (1/(1−e^{−x}) − 1/x)e^{−x} dx`
  (= `−ψ(1)` in Gauss form): from (i) at… (i)+(ii) ⟹ (5). For (ii): mathlib
  `Real.eulerMascheroniConstant` defs + `digamma_one = −γ` given ✓ — so (ii) IS
  `Gauss at z=1`: `∫₀^∞(e^{−x}/(1−e^{−x}) − e^{−x}/x)dx = −ψ(1) = γ` — prove THIS
  integral identity directly: `e^{−x}/(1−e^{−x}) − e^{−x}/x = ∑_{n≥1}e^{−nx} − e^{−x}/x`;
  `∫₀^b`-truncated + `∑_{n≤N}` Frullani-style: `∫(e^{−x}−e^{−Nx})/x dx → log N`
  (mathlib: `integral_exp_neg_mul_sub…`? Frullani exists? check
  `Mathlib/Analysis/SpecialFunctions/Log/...` — if absent it's a 30-line dominated-
  convergence argument) and `∑_{n≤N}1/n − log N → γ` (mathlib:
  `Real.tendsto_sum_range_one_div_nat_succ_sub_log`?? the harmonic-γ limit EXISTS as
  the definition/characterization of `eulerMascheroniConstant` — check exact name).
- **Γψ-d** the three cos-kernel identities (Poitou 6-04):
  `Re ψ(1/2+it) = −∫₀^∞ (cos xt/(2 sinh(x/2)) − e^{−x}/x) dx`,
  `Re ψ(1/4+it/2)` variant, and the difference-with-log2 identity
  `Re ψ(1/4+it/2) − Re ψ(1/2+it) + log 2 = −∫₀^∞ cos(xt)/(2cosh(x/2)) dx`.
  All from Γψ-c by `Re`-parts (`e^{−x(1/2+it)}` → `e^{−x/2}cos xt`) + algebra
  (`e^{−x/2}/(1−e^{−x}) = 1/(2sinh(x/2))`; the 1/4-variant needs `x ↦ 2x` rescale and
  `e^{x/2}/(sinh x)` bookkeeping — Poitou's displays, transcribe exactly).
- **Γψ-e** the two constants: `∫₀^∞ (1/(2sinh(x/2)) − e^{−x}/x) dx = γ + 2log2 = −ψ(1/2)`
  (Gauss at 1/2 + `digamma_one_half` ✓ mathlib) and `∫₀^∞ dx/(2cosh(x/2)) = π/2`
  (elementary: `= [2 arctan(sinh(x/2))]`-type primitive? actually
  `∫ dx/(2cosh(x/2)) = 2arctan(tanh(x/4))`… simplest: substitute `u = e^{−x/2}`:
  `∫₀^1 du/(… )`… gives `2∫₀^1 du/(1+u²) = 2·(π/4) = π/2` ✓ 15 lines).
- **Γψ-f** **Prop 3** (Poitou 6-04→6-06): for σ > 0, F integrable with
  `(F(0)−F(x))/x` BV (his Remarque: BV ⟹ the L² + o(1/log) hypotheses):
  `(1/2π)∫_ℝ {Re ψ(σ+it) − ψ(σ)} φ(t) dt = ∫₀^∞ e^{−σx}(F(0)−F(x))/(1−e^{−x}) dx`.
  Via Lemme 1 (`γ(t) :=` FT of `(F(0)−F(x))/x` is differentiable off 0 with
  `γ' = −iφ` — dominated convergence, his 6-05 five-piece split) and Lemme 2
  (Plancherel pairing `∫ k·(F(0)−F(x))/x = (1/2π)∫ μ·γ` + IBP in `t` — mathlib
  Plancherel: `MeasureTheory.LpSpace`-Fourier? CHECK `Mathlib/Analysis/Fourier/LpSpace`
  + `Plancherel` name at implementation; if the measure-theoretic Plancherel is
  awkward, note k, F are concrete-enough that the pairing can be done by direct
  Fubini for L¹∩L² pairs — `∫ k·ǧ = ∫ k̂·g`-multiplication formula EXISTS:
  `MeasureTheory.integral_fourierIntegral_smul_eq…`/`Real.fourierIntegral`
  multiplication formula `∫ f·ĝ = ∫ f̂·g` for L¹ pairs — mathlib ✓
  `VectorFourier.integral_fourierIntegral_smul_eq_flip`!). With
  `k(x) := (x/(1−e^{−x}))e^{−σx}` (odd extension), `ρ(t) = 2(Re ψ(σ+it) − ψ(σ))`
  by Γψ-c ✓, `ρ·γ → 0` from A6 (`ρ = O(log t)`) + `γ(t) = o(1/log t)` — his LAST
  hypothesis; for BV `(F(0)−F(x))/x` one gets γ = O(1/t) by the Φ-d mechanism ✓
  (stronger than needed).
- **Γψ-g** assembly of the archimedean side (Poitou 6-04 bottom + 6-07 (6) chain):
  `I_G(T) → F(0)[log|d| − n(γ_E + log 8π) − r₁π/2] + n∫₀^∞(F(0)−F(x))/(2sinh(x/2)) +
  r₁∫₀^∞(F(0)−F(x))/(2cosh(x/2))` — combining Γψ-b,d,e,f + FJ-g's cos-variant +
  the sinh-halving `1/(2sinh(x/2))` vs `1/(1−e^{−x})`-rescale bookkeeping
  (Poitou's `Re ψ(1/2+it)` uses σ = 1/2 in Prop 3 after `x`-rescale: transcribe the
  6-07 chain of three displayed rearrangements exactly).

### SP2-MAIN — the theorem (file `ExplicitFormula/ExplicitFormula.lean`)
- **M-a** `explicit_formula` (Poitou (6), first display) for `IsAdmissibleTestFn F`:
  `Tendsto (fun T => ∑_{|γ|<T} m_ρ·Φ(ρ)) atTop (𝓝 (Φ(0) + Φ(1) − 2∑_{𝔭,m}… + F(0)[…]
  + n∫… + r₁∫…))` — sum over the divisor of H per height window (formulate the
  truncated sum via `MeromorphicOn.divisor H (strip-rectangle T)` finsums — the A4/A5
  divisor language ✓; B–F's `∑_ρ F̂(γ_ρ)` translation layer to `GRH.lean`'s zero
  predicate for SP3).
- **M-b** `Φ(0) + Φ(1) = 4∫₀^∞ F(x)cosh(x/2)dx` (Poitou 6-07 Remarque; evenness).
- **M-c** B–F eq (1) restatement + eq (3) K−k subtraction form (`L_{K/k}` const).

---

## Order of work (dependencies)
1. SP2-Φ (a,b,c + packaged d) — unblocks everything. ~1 session.
2. SP2-RECT R-c (the 1/(z−ρ) rectangle integral — the new mechanism; do EARLY as
   it's the main risk) then R-a,b,d,e,f,g. ~2 sessions.
3. SP2-vM. ~1 session.
4. SP2-FJ (c first — Dirichlet integral; then b,d,e,f,g). ~2 sessions.
5. SP2-Γψ (c Gauss — second main risk, do early after FJ-c; then b,d,e; f; a,g). ~3 sessions.
6. SP2-MAIN. ~1 session.

## Verified mathlib anchors (2026-07-02 pin)
- `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` ✓ (:266)
- `Real.tendsto_integral_exp_smul_cocompact` ✓ (RiemannLebesgueLemma.lean:208)
- `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn` ✓ (BoundedVariation.lean:48)
- `StieltjesFunction.measure` ✓; `TendstoLocallyUniformlyOn.deriv` ✓ (LocallyUniformLimit)
- `Complex.digamma` API: `digamma_def` (= logDeriv Γ, rfl), `digamma_one = −γ`,
  `digamma_one_half = −2log2 − γ`, `digamma_apply_add_one`, `meromorphic_digamma` — ✓
  but NO series rep, NO Gauss integral (build = Γψ-c).
- `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` ✓ (ℚ-pattern, Dirichlet.lean:434);
  `Chebotarev.dedekindZeta_eq_tprod_primeIdeal` ✓ (:808) +
  `hasSum_nonzeroIdeal_absNorm_cpow` (:515), `dedekindZeta_re_pos_of_one_lt` (:817).
- `VectorFourier.integral_fourierIntegral_smul_eq_flip` (multiplication formula) —
  NAME TO RE-VERIFY at Γψ-f time.
- NOT in mathlib (to build): Dirichlet integral `∫₀^∞ sinc = π/2` (FJ-c); Jordan
  inversion (FJ); rectangle Cauchy formula (R-c); Gauss digamma integral (Γψ-c);
  ζ_K log-derivative series (vM-a); Φ vertical decay for BV (Φ-d′).

## AINTLIB reuse audit (2026-07-02, user-prompted)

Swept all sibling projects for contour/residue machinery:
- **`LeanModularForms/ForMathlib/GeneralizedResidueTheory/`** has a full CPV residue
  library: `generalizedResidueTheorem'` (Residue/GeneralizedTheoremBase.lean:280) —
  CPV = `2πi·∑ winding·residue` for piecewise-C¹ closed immersions on convex opens,
  SIMPLE poles allowed even ON the curve; plus `GeneralizedWindingNumber`,
  `SimplePoleIntegral.integral_inv_sub_eq_winding`, `NullHomologous`,
  `ContourIntegral/SegmentFTC`, `HungerbuhlerWasem` crossing theorems.
  **Decision**: R-d was completed directly (rectangle Goursat + own rectangle Cauchy
  formula) — it handles arbitrary-multiplicity divisor zeros, whereas the GRT is
  simple-poles-of-`f` (usable for `Φ·H'/H` only after HasSimplePoleAt bridging +
  immersion-rectangle + winding computation = more glue than the direct proof).
  **Fallback recorded**: Poitou's "T through an ordinate with principal value and
  half-weight" variant is EXACTLY this CPV machinery — if the good-heights route
  (R-e) ever becomes painful downstream, switch to `generalizedResidueTheorem'`.
- `FltRegularBernoulli/ZetaFactorisation/Residue.lean`: s = 1 residue consequences of
  Euler products for CYCLOTOMIC L-products — possible SP3-era cross-check for the
  class-number-formula side; not needed for SP2.
- No von Mangoldt/ζ-log-derivative series, no Dirichlet integral/sinc, no
  Fourier–Jordan/BV inversion anywhere else in AINTLIB — SP2-vM, SP2-FJ, SP2-Γψ must
  be built as planned.
- mathlib has `NumberField.dedekindZeta_residue` + `tendsto_sub_one_mul_dedekindZeta_nhdsGT`
  (NumberTheory/NumberField/DedekindZeta.lean) — the κ_K object Theorem 1 approximates;
  SP3's statement should be phrased against it.

## Faithfulness notes
- Poitou's Prop 1 condition is `‖Φ‖_{a,T} = o(1/log T)`; we use the stronger O(1/T)
  from BV — same conclusion, one fewer epsilon.
- Poitou allows `T` through zero ordinates with principal values; we ALWAYS pick good
  heights (R-e) — the limit statement is unaffected (monotone exhaustion between good
  heights: the partial sums differ by the zeros in `[T, T']` with
  `∑|Φ(ρ)| ≤ count·sup‖Φ‖ → 0` by A4 + Φ-d — fold into M-a).
- His G'/G shift-to-critical-line (Γψ-a) is stated "on peut remplacer"; we transcribe
  with the explicit Goursat rectangle between the two vertical lines.
