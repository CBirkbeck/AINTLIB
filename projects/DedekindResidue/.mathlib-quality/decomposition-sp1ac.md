# SP1-AC decomposition — analytic control WITHOUT global Hadamard (2026-07-02)

## Route decision (source-verified, replaces the board's "Hadamard product" plan)

**Discovery 1 (paper, p. 10, footnote 4, verbatim):** "One can prove (19) with the explicit
formula, using F(x) := exp(−(σ−½)|x|). However, the classical proof [11] with the
Weierstraß product and functional equation is faster."
⇒ Stark's identity (19) — the only global-zero-sum SP3 needs — is a *consequence of SP2*
applied to the elementary test function `F(x) = e^{-(σ-1/2)|x|}` (F̂(γ) = 2h/(h²+γ²)),
plus digamma evaluations of the archimedean integrals. **The global Hadamard/Weierstrass
product is NOT needed anywhere in the Theorem-1 pipeline.** ("Faster" is a statement about
human effort with classical tools in hand; for us SP2 is mandatory anyway.)

**Discovery 2 (mathlib audit, 2026-07-02):** the hard classical inputs are already in
mathlib (all names verified against the pinned mathlib):
- **Jensen's formula**: `MeromorphicOn.circleAverage_log_norm`,
  `AnalyticOnNhd.circleAverage_log_norm` (`Mathlib/Analysis/Complex/JensenFormula.lean`);
  and the ready-made zero-counting corollary **`AnalyticOnNhd.sum_divisor_le`**:
  `∑ᶠ u, divisor f (closedBall c |r|) u ≤ log (M / ‖f c‖) / log (R / r)`.
- **Borel–Carathéodory**: `Complex.borelCaratheodory`
  (`Mathlib/Analysis/Complex/BorelCaratheodory.lean`).
- **Hadamard three-lines**: `Mathlib/Analysis/Complex/Hadamard.lean`
  (`norm_le_interp_of_mem_verticalClosedStrip`).
- **Γ reflection**: `Complex.Gamma_mul_Gamma_one_sub : Γ z · Γ(1−z) = π / sin (π z)`;
  **Γ recurrence**: `Complex.Gamma_add_one`.
- **digamma**: `Complex.digamma := logDeriv Gamma`, `digamma_one` (= −γ),
  `digamma_one_half`, `digamma_apply_add_one`, `meromorphic_digamma`
  (`Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean`).
- Divisor-with-multiplicity language: `MeromorphicOn.divisor` + `ValueDistribution/`.
- What mathlib does NOT have (checked): complex Stirling on vertical strips, Hadamard
  factorization, finite-order theory, N(T) zero counting. Of these, only **two-sided
  vertical Γ-bounds** are needed, and they are derivable WITHOUT Euler–Maclaurin (leaf A1).

**Why no Stirling mountain:** the only places vertical Γ-asymptotics enter are (i) the
upper/lower Γ-bounds in the convexity bound for ζ_K and (ii) Γ-log-derivative bounds.
Both follow from *exact* reflection values on two lines + recurrence + three-lines
interpolation:
- `|Γ(1/2+it)|² = π/cosh(πt)` (reflection at `z = 1/2+it`: `sin(π(1/2+it)) = cos(πit) =
  cosh(πt)`), `|Γ(1+it)|² = πt/sinh(πt)` (reflection + `Γ(1+w) = wΓ(w)`), both **exact**;
- upper bounds on the strip `1/2 ≤ σ ≤ 1` by three-lines; extend to any compact σ-range by
  recurrence; lower bounds via `1/Γ(z) = Γ(1−z)·sin(πz)/π` + the upper bounds.

## The leaves (bottom-up; each with source + mathlib anchors)

- **[AC-A1] Γ-strip two-sided bounds** (`CompletedZeta/GammaStrip.lean`):
  **REFINED PLAN (2026-07-02 adversarial audit)**: constant-boundary three-lines is NOT
  enough (gives bounded, non-decaying upper; quotients then blow up exponentially — the
  ζ_K convexity bound genuinely needs the `e^{-π|t|/2}`-decaying upper). Route that works,
  all inputs verified in mathlib:
  (A1-i) DONE (7001571f): exact `‖Γ(1/2+it)‖² = π/cosh(πt)`, `‖Γ(1+it)‖² = πt/sinh(πt)`;
    also derive `‖Γ(3/2+it)‖² = ‖1/2+it‖²·π/cosh(πt)` by recurrence when needed.
  (A1-ii) `‖Γ(z)‖ ≤ Real.Gamma (Re z)` for `0 < Re z` (triangle ineq in
    `Complex.Gamma_eq_integral`; check for existing mathlib name first).
  (A1-iii) **PL comparator**: `G(z) := Γ(z)²·sin(πz)/z²` on the strip `Re ∈ [1/2, 3/2]`:
    `|G| = π/|z|² ≤ 4π` on `Re = 1/2` (exact values + `|sin(π(1/2+it))| = cosh(πt)`),
    `|G| = π·|1/2+it|²/|3/2+it|² ≤ π` on `Re = 3/2`; interior growth
    `|G| ≤ Γ(σ)²·e^{π|t|}` is sub-double-exponential, so
    `PhragmenLindelof.vertical_strip` (mathlib, verified) applies ⇒ `|G| ≤ C₀` on the
    strip ⇒ `‖Γ(σ+it)‖ ≤ C·(1+|t|)·e^{-π|t|/2}` for `|t| ≥ 1`, `σ ∈ [1/2, 3/2]`
    (using `|sin(x+iy)|² = sin²x + sinh²y ≥ sinh²y`).
  (A1-iv) extend the decaying upper to any compact σ-strip by finite recurrence
    (`Γ(z) = Γ(z+1)/z` leftward, `Γ(z+1) = zΓ(z)` rightward), poly-slack absorbing the
    `z`-factors; state for `|t| ≥ 1`.
  (A1-v) matching lower `‖Γ(σ+it)‖ ≥ c·e^{-π|t|/2}·(1+|t|)^{-A}` via
    `1/Γ(z) = Γ(1-z)·sin(πz)/π` + (A1-iv) + `|sin(π(σ+it))| ≤ cosh(πt) ≤ e^{π|t|}`.
  Deliverables: `exists_Gamma_strip_upper/lower` (∃ C A, two-sided with matching
  exponential); then the Γℝ/Γℂ-product versions for `gammaFactor K`.
  ORIGINAL SKETCH (superseded):
  `Gamma_half_line_norm_sq : ‖Γ(1/2+it)‖^2 = π/cosh(πt)`,
  `Gamma_one_line_norm_sq : ‖Γ(1+it)‖^2 = πt/sinh(πt)` (t ≠ 0),
  `norm_Gamma_le / le_norm_Gamma` on `σ ∈ [σ₀, σ₁]`, shape
  `c₁·e^{-π|t|/2}·(1+|t|)^{σ-1/2} ≤ ‖Γ(σ+it)‖ ≤ c₂·e^{-π|t|/2}·(1+|t|)^{σ-1/2}`
  (or any two-sided form strong enough for A3/A5; constants may depend on the strip).
  Source: classical (e.g. Tao 246B Notes 1 context; refs/DedekindResidue/tao-246b-notes1.html);
  proofs from the three mathlib ingredients above. **No sorries about asymptotic series.**
- **[AC-A2] Λ strip bounds from the theta side** (`CompletedZeta/AnalyticControl.lean`):
  uniform-in-t bound `‖(heckeFEPair K).Λ₀ s‖ ≤ B(Re s)` on every vertical strip, from the
  symmetric Mellin representation over `x ∈ [1,∞)` (mathlib `WeakFEPair` API + our
  `exists_heckeF_dev_bound`); consequence: `H(s) := s(s-1)·completedDedekindZeta K s`
  entire (have: `completedDedekindZetaEntire`) with
  `‖H(s)‖ ≤ exp(C·|s|·log(2+|s|))`-type global bound via FE-reflection (Re s ≥ 1/2 by the
  integral bound, Re s < 1/2 by `Λ(s) = Λ(1-s)`). Order-(≤1+ε) statement, constants may
  depend on K.
- **[AC-A3] REVISED (2026-07-02, envelope-matched Jensen scheme) — ✅ COMPLETE (252361b6, `exists_H_strip_decay`)** — the deliverable is a
  **decaying upper for `H = completedDedekindZetaEntire` on the strip `-1 ≤ Re ≤ 2`**:
  `‖H(σ+it)‖ ≤ C_K·(1+|t|)^P·e^{-(n_K π/4)|t|}` — matching the center-lower's envelope
  exactly (Γℝ-factor decays at rate π|t|/4, Γℂ at π|t|/2; total `(r₁+2r₂)π/4 = n_K π/4`),
  so the Jensen ratio at center `A+iT` is polynomial and per-height counting is
  `O(log Δ_K + log(2+|T|))` as classically required (paper p. 8 "all sums in (13) are
  absolutely convergent" needs per-height O(log), NOT O(T)). Sub-leaves:
  (a) rightward UPPER propagation `‖Γ(z+n)‖ ≤ poly·upper` (mirror of the landed
      `le_norm_Gamma_base_add_nat`); decaying upper for `gammaFactor K (σ+it)`, σ ∈ [1,2];
  (b) `‖ζ_K(σ+it)‖ ≤ T₂` for σ ≥ 2 (norm-sum at 2 — same machinery as A4-i);
  (c) decaying upper for H on the line Re = 2 (combine via
      completedDedekindZetaEntire_eq + completedDedekindZeta_eq_of_one_lt_re);
  (d) `completedDedekindZetaEntire_one_sub : H(1-s) = H(s)` (s(s-1) is 1-s-symmetric;
      off {0,1} from A0's FE, everywhere by continuity + density);
  (e) PL comparator `G := H⁴·sin(πz)^{n_K}` (exponent-matched: 4·(n_Kπ/4) = n_K·π) on
      [-1, 2] with the A1-iii scheme → decaying upper inside the strip.
  Then **A4** = `AnalyticOnNhd.sum_divisor_le` at center `A+iT` (A from
  `exists_re_norm_dedekindZeta_ge_half`, LANDED) with (e)'s sup-bound and the
  center-lower from `le_norm_Gamma_base_add_nat` (LANDED) + ζ ≥ 1/2 + prefactor const.
  ORIGINAL SKETCH (superseded — dedekindZeta is LSeries-junk off Re > 1, so ζ_K-strip
  bounds are the wrong object; H-language throughout): `‖dedekindZeta K (σ+it)‖ ≤ C_K·(2+|t|)^{c}`
  for `-1 ≤ σ ≤ 2` — from A2 (Λ-bound) divided by the Γ-lower bound of A1 (+ prefactor).
  Also the Euler-product lower bound `‖ζ_K(2+it)‖ ≥ ζ_K(4)/ζ_K(2)`-type (mathlib Euler
  product for `dedekindZeta`; exact constant shape free).
- **[AC-A4] per-height zero counting — ✅ COMPLETE (f563ce33, `exists_ball_zero_count`)**:
  `m_K(T) := ∑ᶠ (divisor of ζ_K on closedBall (2+iT) 3/2? — radius covering the critical
  strip slab |γ−T| ≤ 1) ≤ C·(log Δ_K + log(2+|T|))` — direct application of
  `AnalyticOnNhd.sum_divisor_le` with A3's upper bound and the `2+iT`-center lower bound
  (Γ-free since we count zeros of ζ_K, not Λ). Also: zeros of Λ in the strip = zeros of
  ζ_K (Γ has no zeros; prefactor nonvanishing) — bridge lemma to `GRH.lean`'s predicate.
- **[AC-A5] Landau local partial fractions — ✅ COMPLETE (`exists_logDeriv_partial_fractions`)**:
  for `|T| ≥ A+5` and `s ∈ closedBall (A+iT) (A+5/4)` (⊇ strip `-1 ≤ Re ≤ 2`, `|Im-T| ≤ 1`)
  with `H s ≠ 0`: `‖H'/H(s) − ∑ᶠ_ρ m_ρ/(s−ρ)‖ ≤ C·log(2+|T|)`, sum over the divisor of
  `H` on `ball (A+iT) (A+2)`. Chain: `exists_H_two_radius_factorization` (peel inner zeros,
  cofactor analytic on the bigger ball via divisor split + `zpow_add'`), maximum principle
  on the `A+5/2` sphere (peel product ≥ `(1/2)^D`), envelope-matched center lower
  (`(A+2)^D`), `exists_ball_zero_count_big` (Jensen at radii `(A+2, A+3)`, FE-reflected
  ball-sup `exists_H_ball_sup_big`), the generic `norm_logDeriv_le_of_norm_le`
  (holomorphic log + recentered `Complex.borelCaratheodory_zero` + Schwarz
  `norm_deriv_le_div_of_mapsTo_ball` on quarter-balls), and the `logDeriv_prod`/
  `logDeriv_fun_zpow` unwind. Envelopes `e^{-n_Kπ|T|/4}` cancel in the log-ratio.
- **[AC-A6] digamma vertical bound — ✅ COMPLETE (`exists_norm_digamma_le`)**:
  `‖digamma(σ+it)‖ ≤ C·log(2+|t|)` for `-1 ≤ σ ≤ 2`, `|t| ≥ 2` — the generic Landau
  lemma applied to `Γ` itself on unit balls (`digamma = logDeriv Gamma` by definition),
  with σ-uniform window bounds `exists_norm_Gamma_le_window` (`-2 ≤ σ ≤ 3`, downward
  recurrence `Γ(z)=Γ(z+1)/z` past the left strip) and `exists_le_norm_Gamma_window`
  (`-1 ≤ σ ≤ 2`, lower `c·e^{-π|t|/2}/(1+|t|)³`). SP1-AC IS NOW FULLY COMPLETE.

Then (separate epics, consuming SP1-AC):
- **[SP2] explicit formula** (eq (1), K-form; the K−k form (3) by subtraction): contour
  integral of `−Λ'/Λ` against the Mellin/Fourier side of an `IsAdmissibleTestFn` F over
  expanding rectangles chosen by A4, horizontal control by A5, vertical shifts by A2/A3;
  prime side via the Euler product (mathlib `dedekindZeta` Euler factors; reuse
  Chebotarev project's Euler-product API if it fits). Source: Poitou (Numdam — TO FETCH),
  Iwaniec–Kowalski Thm 5.12 scheme. Zero-sum stated as `lim_{R→∞} ∑_{|Im ρ|<R}`
  (paper p. 3 convention, verbatim: "the sum over ρ converges when understood as
  lim_{R→+∞} Σ_{|Im(ρ)|<R} F̂(γ_ρ)").
- **[SP3→eq(19)]** = SP2 @ `F(x) = e^{-(σ-1/2)|x|}` (footnote 4) + digamma integral
  evaluations (`∫_0^∞ e^{-hx}cosh(x/2)dx = h/(h²-1/4)`-type elementary +
  `∫_0^∞ (e^{-x/2}... )/(2sinh(x/2))`-Gauss-digamma identities — decompose when reached).
  Then **Lemma 5** verbatim (paper p. 9–10): `∑_ρ 1/(¼+γ_ρ²) ≤ (2σ-1)(log Δ_K +
  2/(σ-1) - d_{K,σ})` by `1/(¼+γ²) < 4h²/(h²+(2hγ)²)... < 4h²/(h²+γ²)` + conjugate
  pairing (GRH ⇒ γ_ρ ∈ ℝ).
- **[T005/Lemma 4]** (paper pp. 8–9): elementary once Lemma 3 exists (MVT on sin, the
  q/q̃ integral estimates (17), `|r_K - r_k| ≤ n_K - n_k`).
- **[T012/Theorem 1]** (paper pp. 10–12): `k = ℚ`, `a = log 9`, `T = log X`,
  `σ = 1 + (log Δ_K)^{-1/2}`, plus the classical ζ_ℚ zero-sum constant
  `∑_{ζ_ℚ} 1/(¼+γ²) = C/2 + 1 - log(4π)/2` (derive from eq (19) at K = ℚ).

## Adversarial notes (decompose-mode discipline)

- **A4 radius audit**: the slab `|γ-T| ≤ 1` must sit inside `closedBall (2+iT) r` with
  `r < R` and the ball inside the zero-free-boundary region where A3's bound holds:
  zeros have `0 ≤ Re ρ ≤ 1` (mathlib: `dedekindZeta` nonvanishing on `Re > 1` +
  functional-equation reflection — VERIFY the `Re > 1` nonvanishing exists for
  `dedekindZeta` in mathlib (`riemannZeta_ne_zero_of_one_lt_re` analogue; if K-version
  missing, it's a leaf via the Euler product)). Center distance to slab-corner:
  `|2+iT - (0 + i(T±1))| = √5 < 5/2`; take `r = 5/2, R = 3`? Then ball reaches Re = -1 ✓
  inside A3's range ✓ and `log(R/r) = log(6/5)` constant ✓.
- **A2 FE-reflection audit**: `Λ(s) = Λ(1-s)` — our concrete FE is
  `(heckeFEPair K).functional_equation` at `s/2`-normalisation with ε = 1, k = 1/2 —
  RE-DERIVE the exact `completedDedekindZeta K s = completedDedekindZeta K (1-s)`
  statement (NOT yet landed as such! `Existence.lean` has the pieces; the clean FE lemma
  is a small missing leaf — add as **[AC-A0]**).
- **Convergence conventions**: zero-sums are conditional (`lim_R`); NEVER state as `tsum`
  over an infinite index without the R-limit wrapper (board warning, review Q5).
- **`Complex.digamma` vs paper's `Ψ(σ) = Γ'(σ)/Γ(σ)` on ℝ**: bridge lemma needed
  (`Complex.digamma_ofReal`-type; check mathlib for `Real.digamma`).

## Verbatim source anchors

- Paper p. 3 (explicit formula (1) + hypotheses): fetched 2026-07-02, pp. 3–7 and 8–11
  read in-session; quotes recorded in HANDOVER + tickets.
- Paper p. 10: eq (18) `d_{K,σ}`, eq (19) + footnote 4 (quoted above).
- Tao, 246B Notes 1 ("Zeroes, poles, and factorisation of meromorphic functions"),
  saved: `refs/DedekindResidue/tao-246b-notes1.html` — Jensen (Thm 2), order/counting
  (Prop 8), truncated log-derivative (Thm 9), Hadamard (Thm 22, NOT on our path).
- Poitou, "Sur les petits discriminants" (Numdam) — TO FETCH for SP2's contour details.
