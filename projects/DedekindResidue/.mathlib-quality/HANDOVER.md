# HANDOVER — DedekindResidue (Belabas–Friedman residue formalisation)

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
- **NEXT: A4 Jensen assembly**: center c = A+iT (A from A4-i; |T| ≥ 2 covers all slabs
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
