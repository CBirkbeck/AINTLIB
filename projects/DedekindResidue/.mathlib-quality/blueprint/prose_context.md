# Prose Context for Blueprint Authoring — DedekindResidue

## Project narrative

Formalise Belabas–Friedman (arXiv:1305.0035) **Theorem 1**: under GRH, the residue
κ_K = Res_{s=1} ζ_K of the Dedekind zeta function of a number field K of degree n > 1
satisfies the explicit bound |log κ_K − f_K(X)| ≤ B(X, n, Δ_K) for X ≥ 69, where
f_K(X) is a computable truncated prime-power sum. GRH is a Prop hypothesis (never an
axiom); everything else is genuinely proven; axiom bar {propext, Classical.choice,
Quot.sound}. The development: SP1 builds the completed zeta Λ_K via the Hecke
theta-Mellin route (Poisson summation → lattice theta inversion → Hecke theta over
ideal classes → WeakFEPair → Mellin agreement), stating GRH via the characterisation
predicate `IsCompletedDedekindZeta` with proven non-vacuity; SP1-AC supplies
Hadamard-free analytic control (Γ-strip bounds, H-strip decay, Jensen zero-counting,
Landau partial fractions, digamma bounds); SP2 proves the Weil–Poitou explicit
formula by rectangle contours (Φ-transform, zero capture, prime side via the
Chebotarev Euler product, Fourier–Jordan inversion, the Gauss-digamma Γ-side, Poitou
Props 1–3); SP3 discharges every hypothesis at the concrete test function F_{s,X};
Tier 3 (T010–T014) walks Lemma 3 → Lemma 4 → Theorem 1.

## Notational conventions

- $K$ a number field, $n = r_1 + 2r_2$, $Δ_K = |\mathrm{disc}(K)|$, $\mathfrak{p}$
  nonzero prime ideals of $\mathcal{O}_K$, $N\mathfrak{p} = $ absolute norm.
- $h := s − 1/2$, $T := \log X$ throughout Lemma 2/3 (matches the paper).
- The paper's Fourier transform (eq. (2)) is $\hat F(γ) = \int F(t)e^{itγ}\,dt$ — no
  $2π$, plus sign: `paperFourierIntegral`.
- $Φ_F(z) = \int F(x)e^{(z−1/2)x}\,dx$ (`paperPhi`); on the critical line
  $Φ_F(1/2+iγ) = \hat F(γ)$.
- $g_s(t) = e^{−h|t|}/|t|$; $f_{s,X}(t) = g_s(t)/g_s(T)$; $F_{s,X}$ = 1 on
  $|t| ≤ T$, $f_{s,X}$ outside (`auxF`, from `gAux` = eq. (6)).
- The completed zeta: $Λ_K(s) = |Δ_K|^{s/2} γ_K(s) ζ_K(s)$-normalised via the
  theta-Mellin construction; `completedDedekindZetaEntire` = the entire function
  agreeing with $s(s−1)Λ_K(s)$ off $\{0,1\}$.
- Zero index: `ZetaZeros K` = subtype of ℂ where the global divisor
  `zetaZeroDivisor` of the entire completion is nonzero; multiplicity $m_ρ$ =
  divisor value; under GRH $ρ = 1/2 + iγ_ρ$.
- Prime side: $H(u) = H_{K,a,F}(u) = \sum_{\mathfrak p, m} \log N\mathfrak p \cdot
  N\mathfrak p^{−m(1+a)} F(u + m\log N\mathfrak p) e^{(1/2+a)(u+m\log N\mathfrak p)}$
  (`primeSideH`); at the auxiliary function the $a$-dependence collapses at $u = 0$.

## Source mappings (per module group)

### CompletedZeta/* (SP1)
- Poisson: `tsum_eq_tsum_fourier_zpoint` (n-dim over ℤ^ι, torus Fourier route);
  transport to lattices; dual lattice covolume `covolume_dualZLattice_mul`.
- Theta: `thetaLattice_transform` = Θ_L(t) = covol(L)⁻¹ t^{−n/2} Θ_{L♯}(1/t);
  `heckeTheta_inversion` / `heckeG_inversion` (per-ideal-class, unit-box-averaged);
  `heckeF` (class-summed normalised theta), `heckeGClass_inversion` (coefficient 1).
- FE: `heckeFEPair : WeakFEPair ℂ` (k = 1/2, ε = 1); mathlib's AbstractFuncEq gives
  Λ₀ entire + functional equation; Mellin agreement (MellinAgreement.lean, ε-chain)
  identifies `(heckeFEPair K).Λ (s/2)` with `heckeAdjust · prefactor · ζ_K(s)`.
- `IsCompletedDedekindZeta K Λ`: agrees with prefactor·ζ_K on Re s > 1 AND
  ∃ entire H with H = s(s−1)Λ off {0,1}; uniqueness `IsCompletedDedekindZeta.eqOn`;
  existence `exists_isCompletedDedekindZeta` (Hecke's theorem, axiom-clean);
  `GeneralizedRiemannHypothesis K`: every such Λ is nonvanishing on Re > 1/2, s ≠ 1.
- References: Neukirch ANT VII §3 shape for theta; Tate-normalisation notes in
  Normalisation.lean; expert review 2026-07-01 fixed the route (classical Hecke, not
  adelic).

### CompletedZeta/AnalyticControl.lean + GammaStrip.lean (SP1-AC)
- A1 Γ-strip: exact |Γ(1/2+it)|² = π/cosh(πt); Phragmén–Lindelöf comparator
  Γ(z)²sin(πz)/z²; uppers `norm_Gamma_le_mul_exp` (≤ √(12π)‖z‖e^{−π|t|/2}) and
  matching lowers `le_norm_Gamma_base` — all Stirling-free.
- A3 `exists_H_strip_decay`: ‖H(z)‖ ≤ C(1+|Im|)^{n_K+2} e^{−n_Kπ|Im|/4} on the strip.
- A4 `exists_ball_zero_count`: Jensen counting, zeros of H per unit height ≲ log(2+|T|).
- A5 `exists_logDeriv_partial_fractions`: H'/H = Σ_{nearby ρ} m_ρ/(s−ρ) + O(log|T|)
  via the generic Landau lemma `norm_logDeriv_le_of_norm_le` (Borel–Carathéodory +
  Schwarz).
- A6 `exists_norm_digamma_le`: ‖ψ(σ+it)‖ ≲ log(2+|t|) on −1 ≤ σ ≤ 2.
- Source: Tao 246A-flavoured Hadamard-free chain; Poitou's scheme needs only these.

### ExplicitFormula/* (SP2)
- `paperPhi` + band integrability + `paperPhi_half_add_mul_I` (= F̂) +
  `paperPhi_one_sub` (Φ(1−s) = Φ(s), even F) + `hasDerivAt_paperPhi`.
- Rectangle contour: `rectangleIntegral_cauchy` (∮Φ(ζ)/(ζ−ρ) = 2πiΦ(ρ)),
  `rectangleIntegral_mul_logDeriv_H` (argument principle for boundary-zero-free H:
  ∮Φ·H'/H = 2πi Σ m_ρ Φ(ρ) over the open window).
- Zero capture: `dedekindZeta_ne_zero_of_one_lt_re` (Euler product),
  `re_mem_of_completedDedekindZetaEntire_eq_zero` (0 ≤ Re ρ ≤ 1),
  `exists_contour_height` (good heights T_n with log²-bounds via A5 + pigeonhole),
  `zero_capture_edge_form` (Poitou Prop 1, quantitative).
- Prime side: `neg_logDeriv_dedekindZeta_eq_tsum` (−ζ'_K/ζ_K = Σ log N·N^{−ms},
  differentiating the Chebotarev Euler product), `primeSideH`,
  `tendsto_prime_side` (Prop 2: lim ∫{Φ(s)+Φ(1−s)}(−ζ'/ζ) = 2π(H(0+)+H(0−))
  via Fourier–Jordan).
- Fourier–Jordan: Dirichlet integral ∫ sinc = π/2 built from scratch (Frullani +
  Fubini); `tendsto_fourier_window_jordan` (symmetric-window Jordan inversion for
  BV functions); Stieltjes–Fubini remainder bounds.
- Γ-side: `digamma_eq_integral_gauss_one` (Gauss's integral, NOT in mathlib),
  `digamma_sub_digamma_eq_integral` (Poitou's (5)), Plancherel chain →
  `prop3_poitou` (Prop 3: lim ∫ 2(Reψ(σ+it)−ψ(σ))φ(t) dt = 4π∫₀^∞ e^{−σy}(F(0)−F(y))/(1−e^{−y})),
  `tendsto_IG_gammaFactor` (the full I_G display: −(n(γ_E+log 8π)+r₁π/2)F(0) +
  n∫(F0−F)/2sinh + r₁∫(F0−F)/2cosh).
- **`weil_explicit_formula`** (Poitou (6)): along good heights, Σ m_ρ Φ(ρ) over the
  band-window → Φ(0)+Φ(1)+log Δ·F(0) + I_G-terms − (H(0+)+H(0−)). ~20 hypotheses
  (BV/decay/band-bound), all discharged at F_{s,X} in SP3.
- Source: Poitou, "Sur les petits discriminants" (Sém. DPP 1976/77, exposé 6) —
  local PDF; B–F §2.

### AuxiliaryFunction.lean, Lemma2.lean, AuxAdmissible.lean, WeilAssembly.lean (SP3)
- `gAux` (eq. (6)), `auxF` = F_{s,X} (eqs. (11)–(12)).
- Lemma 2: `fourier_auxF` (eq. (8) closed form: sin + cos − tail-integral pieces),
  `fourier_auxF_zero` (γ = 0 companion).
- `IsAdmissibleTestFn` = the paper's p.3 hypotheses verbatim; `isAdmissibleTestFn_auxF`.
- Hypothesis discharges: `exists_band_bound_paperPhi_auxF` (‖Φ(σ+it)‖ ≤ M/max(|t|,1)
  on the band, the main analytic piece), `exists_norm_fourier_auxF_le` (F̂ = O(1/γ²)),
  BV suites, boundary ργ-decay at σ = 1/2, 1/4.
- **`weil_explicit_formula_auxF`**: every hypothesis holds at F = F_{s,X}
  (1 < X, 0 < a ≤ 1/4, a < Re s − 1); `primeSideH_auxF_zero_eq`
  (H(0) = Σ log N·N^{−m/2} F(m log N)).

### GRHZeros.lean + Lemma3.lean + PrimeSide real-ray (T010, Lemma 3)
- `zetaZeroDivisor` (global divisor), `ZetaZeros` (countable zero index),
  `ZetaZeros_re_eq_half` (GRH pins Re = 1/2),
  `exists_slab_zetaZeroDivisor_sum_le` (unit-slab count ≲ log(3+n)),
  `summable_zetaZeros_inv_sq` (Landau Σ m_ρ/(h²+γ²) < ∞),
  `finsum_divisor_mul_eq_sum_zetaZeros` (window bridge),
  `tendsto_finsum_window_zetaZeros` (window sums → tsum under GRH).
- `real_log_dedekindZeta` (log ζ_K(σ) = Σ N^{−mσ}/m, σ > 1, from
  `dedekindZeta_eq_exp_tsum_prod`).
- Lemma3.lean: `summable_zetaZeros_paperPhi_auxF`, `tsum_zetaZeros_paperPhi_auxF_eq`
  (the explicit formula as an honest Σ' over zeros), zeroSin/Cos/IntTerm +
  `paperFourierIntegral_auxF_split` + `tsum_zetaZeros_paperPhi_auxF_split` (the three
  B–F (13) zero-series), `tsum_kernel_eq_log_zeta` + `primeSideH_auxF_zero_split`
  (H(0) = plateau defect + T e^{hT} log ζ_K(σ)).

### MainTheorem.lean (target)
- `bSum` (B_K(X), p. 2 verbatim), `bSumRel` (the K−ℚ relative sum), `fK`,
  `belabas_friedman_thm1` (the single remaining sorry).

## High-priority unformalisation sources
1. Module docstrings (each file has a thorough `/-! ... -/` header).
2. `.mathlib-quality/HANDOVER.md` — the full development narrative.
3. `.mathlib-quality/decomposition-sp1ac.md`, `decomposition-sp2.md` — leaf plans.
4. Poitou PDF (`refs/DedekindResidue/poitou-petits-discriminants.pdf`), B–F 1305.0035.
