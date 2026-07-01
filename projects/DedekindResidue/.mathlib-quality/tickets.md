# Ticket Board — DedekindResidue

## Summary
- Bottom-up (SP1 → SP2/SP3 → Tier 3). The three deep sub-projects are **epics**: each
  expands into leaf tickets via its own `/develop --decompose` pass (needs its reference).
- Concrete near-term (SP-independent, actionable now): T001, T002, T003, T-ADM, T-BV.
- Tier-3 spine (T010–T014): blocked on the epics.
- Done ✓: T001 (bSum), T002 (auxF API + measurability) — build green, axiom-clean.
- Open near-term: 3 (T003 Lemma 2, T-ADM, T-BV) · Epics needing decomposition: 3 (SP1 w/ 8 sub-epics, SP2, SP3) · Blocked (tier-3 spine): 5
- Expert-review adjustments folded in (2026-07-01): +SP1-AC, +SP1-N, +T-ADM, +T-BV; AGP
  Gaussian-first; AGE sealed unit-domain API; GRH dual-form. See `expert-review/2026-07-01/`.

---

## Epics (need their own `/develop --decompose` pass before leaf tickets exist)

### [SP1] Completed ζ_K + FE + Hadamard + analytic control — the general theta stack
- **Status**: needs-decomposition · **Files**: `CompletedZeta/{DualLattice,ThetaLattice,Normalisation,GammaFactor,FunctionalEquation,HadamardProduct,AnalyticControl,GRH}.lean`
- **Type**: epic (foundation) · **Depends on**: N → AG-P → AG-Θ → AG-E → FE → AC · **Blocks**: SP2, SP3, T010+
- **Route confirmed (expert review 2026-07-01)**: general-K **Hecke theta route**, NOT Tate
  (adelic substrate too large) and NOT abelian (validation-only). Implement as a
  **Hecke-classical proof with Tate-style normalisation discipline**. Narrowed next milestone
  (review): (a) reusable lattice/Poisson/theta layer → (b) a *sealed* Hecke partial-zeta
  theorem → (c) `Λ_K` with **all constants fixed**. See `decomposition.md`. Sub-epics, bottom-up:

  - **[SP1-N] normalisation** (`Normalisation.lean`) — **DO EARLY** (review Q5, archimedean
    constants). Pin the `Γℝ/Γℂ` convention (`Γℂ(s)=2(2π)^{-s}Γ(s)`), state the residue constant
    of `Λ_K` with the **`2^{r₂}` factor explicit**, and write conversion lemmas *now* so no
    downstream constant chase silently drifts by a hidden `2^{r₂}`/`π^{r₂}`/`√Δ_K`.
  - **[SP1-AGP] n-dim Poisson summation** over a `ZLattice` — **START HERE** (self-contained;
    no external reference). **Gaussian-class first, full-Schwartz deferred (review Q2).** Leaves
    in order: (P.1) **dual lattice** of a `ZLattice` + covolume identities [gap — none in
    mathlib]; (P.2) Poisson on `ℤⁿ` *for the Gaussian class* [from 1-D `Real.tsum_eq_tsum_fourier`
    / torus Fourier]; (P.3) transport to a general full lattice + covolume factor
    [`ZLattice.covolume`, `VectorFourier.fourierIntegral`]. (P.opt) general Schwartz-class
    Poisson — **optional, off the critical path**, only if cheaply reusable. **Next action**:
    `/develop --decompose` scoped to SP1-AGP.
    - **P.1 DONE ✓✓ (2026-07-01, `CompletedZeta/DualLattice.lean`, build green + axiom-clean
      `{propext, Classical.choice, Quot.sound}`)**: `dualZLattice` (via `innerₗ` +
      `LinearMap.BilinForm.dualSubmodule`), `mem_dualZLattice`, `innerₗ_nondegenerate`, the
      structural lever `dualZLattice_eq_span` (`L♯ = span ℤ (dual basis)`), the
      `instDiscreteTopologyDualZLattice` + `instIsZLatticeDualZLattice` instances (free from
      `dualZLattice_eq_span` + `ZSpan.span_top`), the measure fact
      `volumeReal_fundamentalDomain_orthonormal` (`vol.real(FD b₀)=1`), AND the covolume
      reciprocal `covolume_dualZLattice_mul` (`covolume L♯ · covolume L = 1`). NB `Basis` is now
      `Module.Basis`; `⟪x,y⟫` (no `_ℝ` subscript) via `open scoped RealInnerProductSpace`.
    - **[SP1-AGP-COVOL] covolume reciprocal — DONE ✓✓** (2026-07-01): `covolume_dualZLattice_mul`.
      Proof exactly as sketched: (1) `ZLattice.covolume_eq_det_mul_measureReal (μ := volume)` with
      `b₀ := (EuclideanSpace.basisFun ι ℝ).toBasis` (reindex `chooseBasis` to `ι` via
      `Fintype.equivOfCardEq` + `finrank_euclideanSpace`); (2) `volumeReal_fundamentalDomain_orthonormal`;
      (3) `Module.Basis.span hlinind` as the dual ℤ-basis (fold post-`dualZLattice_eq_span` goal with
      `← hc, ← hcstar`); (4) `MᵀM* = 1` from `apply_dualBasis_left` (δ_ij) + `OrthonormalBasis.sum_inner_mul_inner`
      Parseval + `real_inner_comm`, then `Module.Basis.det_apply` + `Matrix.det_transpose` + `Matrix.det_mul`.
  - **[SP1-AGΘ] lattice Gaussian theta** `Θ_L(t)=∑_{x∈L}e^{-πt‖x‖²}` + transformation law —
    depends on SP1-AGP (Gaussian class) + n-dim Gaussian self-duality (assemble from 1-D
    `Gaussian/FourierTransform`).
  - **[SP1-AGE] Hecke construction** — ideal-lattice theta over `FundamentalCone` (unit action) +
    `ClassGroup 𝓞_K`, Mellin → gamma factors + `completedDedekindZeta` + FE. Deepest; needs a
    reference PDF into `refs/` (Tate's thesis / Lang *ANT* XIII–XIV / Neukirch VII §5).
    **Seal the unit fundamental domain behind a small API (review Q2)**: one theorem
    "sum over nonzero elements of an ideal mod units = partial-zeta / Mellin expression";
    everything downstream sees only that theorem, not the domain geometry.
  - **[SP1-FE] assembly** (`FunctionalEquation.lean`): `completedDedekindZeta_one_sub` (clean FE),
    continuation + poles tied to `dedekindZeta_residue` — replaces the current stubs.
  - **[SP1-AC] analytic control** (`AnalyticControl.lean` + `HadamardProduct.lean`) — **promoted
    to an explicit deliverable (review Q1/Q4); blocks SP2 + SP3.** Leaves: finite order of `Λ_K`;
    vertical-strip growth bounds (for contour shifts); **zeros as a locally-finite multiset /
    indexed type with multiplicity** + lemmas to compare/bound/subtract zero-sums; canonical/
    Hadamard product **and its logarithmic derivative** (usable statement); contour-shift decay
    estimates; the **real-branch-of-log** convention for `log(ζ_K/ζ_k)`, `s>1`. ⚠ zero-sums carry
    a **convergence convention** — do NOT model them as absolutely summable unless proven (review Q5).
  - **[SP1-Γ] `GammaFactor.lean`**: `Γℝ^{r₁}Γℂ^{r₂}` bookkeeping → mathlib Deligne (leaf).
  - **[SP1-GRH] `GRH.lean`** — provide **both** `GRH_Λ K` (zeros of `Λ_K` on the line) and
    `GRH_{>½} K` (zero-free `Re s > ½`), plus the **equivalence lemma** (FE + Euler-product
    nonvanishing on `Re>1` + Γ-factors have no zeros). Use `GRH_{>½}` for Lemma 3, `GRH_Λ` for the
    explicit-formula zero-sum. Replaces the current single-form stub (review Q4).

### [SP2] Weil–Poitou explicit formula
- **Status**: needs-decomposition · **File**: `ExplicitFormula/WeilPoitou.lean`
- **Type**: epic · **Depends on**: SP1 · **Blocks**: T004 (Lemma 3)
- **Goal**: the explicit formula (eqs 1, 3): `Σ_ρ F̂(γ_ρ) = −2 Σ_{𝔭,m} (log N𝔭/N𝔭^{m/2})
  F(m log N𝔭) + 4∫F(x)cosh(x/2)dx + F(0)(log Δ_K − n_K C − n_K log 8π − r_K π/2) +
  n_K∫(F(0)−F)/(2 sinh) + r_K∫(F(0)−F)/(2 cosh)`. **Route**: Poitou (Numdam) / Lang *ANT*
  XVII / Iwaniec–Kowalski §5 — contour integral of `−Λ'_K/Λ_K`. Reuse Chebotarev Euler
  product for the prime side. **Next action**: acquire reference, then `/develop --decompose`.
- **Depends on (promoted, review Q1/Q4/Q5)**: SP1-AC (finite order, zero multiset with
  multiplicity, log-derivative, contour-shift estimates) + `[T-ADM]`. ⚠ the zero-sum
  `Σ_ρ F̂(γ_ρ)` carries a **convergence convention** (conditional, not absolute until the
  post-Lemma-3 estimates) — keep that visible in the Lean statement.

### [SP3] Stark's formula + Landau–Stark bound
- **Status**: needs-decomposition · **File**: `Stark.lean`
- **Type**: epic · **Depends on**: SP1 · **Blocks**: T005 (Lemma 4), T012 (Thm 1)
- **Goal**: eq (19) `Σ_ρ 1/(σ−ρ) = ½log Δ_K + 1/(σ−1) + 1/σ − ½ d_{K,σ}` and Lemma 5
  `Σ_ρ (¼+γ_ρ²)^{−1} = O(log Δ_K)`. **Route**: Stark 1974 eq (9); Landau §180; mathlib
  `digamma`. **Next action**: acquire reference, then `/develop --decompose`.
- **Depends on (promoted, review Q4)**: SP1-AC — Stark's identity is the **log-derivative of
  the canonical/Hadamard product** of `Λ_K`, so it needs finite order + the product + its
  log-derivative, not just meromorphic continuation + FE.

---

## Concrete near-term tickets (actionable now — SP-independent)

### [T001] Define `bSum` (`B_K(X)`) — replace the stub
- **Status**: DONE ✓ (2026-07-01) · **File**: `MainTheorem.lean` · **Depends on**: none · **Parallel**: yes · **Type**: def
- **Outcome**: `bSum` defined via nested `∑ᶠ` over `{p : Ideal (𝓞 K) // p.IsPrime ∧ p ≠ ⊥}`
  and `m : ℕ`, guarded by `0 < m ∧ N𝔭^m < X`; finsum totality ⇒ no finiteness proof needed to
  define. Build green, axiom-clean `{propext, Classical.choice, Quot.sound}`. (`fK` now
  sorry-free too.) Finite-support / `Finset` reformulation deferred to when a proof needs it.
#### Statement
Replace `noncomputable def bSum (K) (X : ℝ) : ℝ := sorry` with Belabas–Friedman's `B_K(X)`
(p. 2): the sum over prime ideals `𝔭 ⊆ 𝓞_K` and integers `m ≥ 1` with `N𝔭^m < X` of
`(log N𝔭 / N𝔭^{m/2}) · (√X·log X / (N𝔭^{m/2}·log N𝔭^m) − 1)`, where `N𝔭 = Ideal.absNorm 𝔭`.
#### Proof sketch (design)
1. Index over `p : {p : Ideal (𝓞 K) // p.IsPrime ∧ p ≠ ⊥}` and `m : ℕ`; summand `0`
   unless `0 < m` and `(absNorm p.1 : ℝ)^m < X`. Set `q := (Ideal.absNorm p.1 : ℝ)`.
2. Summand: `(Real.log q / q ^ ((m:ℝ)/2)) * (Real.sqrt X * Real.log X / (q ^ ((m:ℝ)/2) *
   Real.log (q ^ m)) - 1)` (use `Real.rpow` for `q^{m/2}`; `log N𝔭^m = Real.log (q^m)`).
3. Finiteness: `{𝔭 : absNorm 𝔭 < X}` is finite (`Ideal.finite_setOf_absNorm_le` / the
   Chebotarev prime-ideal finiteness API); express as a `Finset.sum` or a `tsum` with
   finite support so it is well-defined and later manipulable.
#### Mathlib / project lemmas
- `Ideal.absNorm`, `Ideal.finite_setOf_absNorm_le`, `Real.rpow`, prime-ideal API; cross-check
  Chebotarev `NumberFieldEulerProduct` (`idealNormMultiplicity`, prime-power indexing) for
  a reusable index type.
#### Sources
- Belabas–Friedman, arXiv:1305.0035, p. 2 (definition of `B_K`).
#### Generality
- General number field `K`; `X : ℝ`. Real-valued.

### [T002] Basic API for `gAux` / `auxF`
- **Status**: DONE ✓ (2026-07-01) · **File**: `AuxiliaryFunction.lean` · **Depends on**: none · **Parallel**: yes · **Type**: lemma
- **Outcome**: `gAux_neg`, `auxF_neg` (evenness, `@[simp]`), `auxF_of_le` (plateau = 1),
  `auxF_zero` (`X ≥ 1 → F(0)=1`), and `measurable_auxF` (`Measurable.ite` + `fun_prop`; the
  break locus `|t|=log X` is `measurableSet_le`) — the measurability prerequisite T003 needs.
  All build green + axiom-clean `{propext, Classical.choice, Quot.sound}`.
#### Statement
`auxF_of_le` (`|t| ≤ log X → auxF s X t = 1`), `auxF_even` (`auxF s X (-t) = auxF s X t`),
`gAux_even`, `auxF_apply_zero` (`auxF s X 0 = 1` for `X ≥ 1`), and measurability/continuity
of `auxF s X` off `|t| = log X` (needed for the Fourier integral in T003).
#### Proof sketch
Unfold the `if`; `abs_neg`; standard continuity of `Complex.exp`, `Real.log`, division.
#### Mathlib lemmas
- `abs_neg`, `Complex.continuous_exp`, `Continuous.div`, `Real.continuous_log` (off 0).
#### Sources
- Belabas–Friedman eqs (6), (11)–(12).
#### Generality
- `s : ℂ`, `X t : ℝ`.

### [T003] Lemma 2 — Fourier transform of `auxF` (eq 8)
- **Status**: open · **File**: `AuxiliaryFunction.lean` · **Depends on**: T002 · **Parallel**: no · **Type**: lemma
#### Statement
`fourier_auxF`: for `Re s > ½`, `X > 1`, `γ ∈ ℝ`, the Fourier transform `F̂_{s,X}(γ)`
equals the closed form of Lemma 2 (eq 8 / the `\widehat{F_{s,X}}` display, p. 6):
`2h² sin(γT)/((h²+γ²)γ) + 2(h+1/T)cos(γT)/(h²+γ²) − (4/(h²+γ²))∫_T^∞ cos(γt) f_{s,X}(t)(ht+1)/t² dt`,
`h = s − ½`, `T = log X`.
#### Proof sketch
Split `F̂ = ∫_{|t|≤T} e^{iγt}dt + ∫_{|t|>T} f_{s,X}(t)e^{iγt}dt`; the first is `2 sin(γT)/γ`;
for the second use `g'_s`, `g''_s` (eq 7) and two integrations by parts (paper eq 8). This
is the one spine leaf provable now (mathlib Fourier + `auxF`), independent of SP1/2/3.
**Review note (Q5)**: not trivial in Lean — mind the even extension, the improper `∫_T^∞`,
the complex parameter `h = s − ½`, and the denominator `h²+γ²` (typing/branch care). Best early
target above the definitions nonetheless.
#### Mathlib lemmas
- `Real.fourierIntegral`, `intervalIntegral.integral_comp`, `integral_cos`, integration-by-parts
  lemmas; `Complex.exp` derivatives.
#### Sources
- Belabas–Friedman, Lemma 2, eqs (7)–(8), pp. 5–6.
#### Generality
- `s : ℂ` with `½ < Re s`; `X : ℝ`, `1 < X`.

### [T-ADM] Admissibility structure for explicit-formula test functions
- **Status**: open · **File**: `ExplicitFormula/TestFunction.lean` · **Depends on**: T-BV · **Parallel**: yes · **Type**: def/structure
#### Statement
A named `structure` (not loose hypotheses) capturing Weil–Poitou admissibility (review Q4):
evenness; bounded variation + integrability of `x ↦ F(x)·e^{(1/2+ε)x}`; bounded variation of
`x ↦ (F(0)−F(x))/x`; the average-of-jump convention at discontinuities. Bundles the side
conditions the explicit formula (SP2) and its application (Lemma 3) quote.
#### Proof sketch (design)
Define once as `structure IsAdmissibleTestFn (F : ℝ → ℂ) : Prop` (or bundled with data);
downstream theorems take `(hF : IsAdmissibleTestFn F)` instead of copying the four conditions.
Provide a constructor from `[T-BV]` (piecewise-C¹) so `F_{s,X}` discharges it cheaply.
#### Sources
- Belabas–Friedman §5 (explicit-formula hypotheses); Poitou 1977. Expert review Q4.
#### Generality
- `F : ℝ → ℂ`; `ε > 0`. Reused verbatim across SP2 + Tier-3.

### [T-BV] Piecewise-C¹-with-integrable-derivative ⇒ bounded variation
- **Status**: open · **File**: `ExplicitFormula/TestFunction.lean` (or `Common/`) · **Depends on**: none · **Parallel**: yes · **Type**: lemma
#### Statement
A reusable lemma: a continuous function that is piecewise `C¹` with integrable derivative on
`ℝ` (finitely many break-points) is of bounded variation on every interval, with the expected
`∫|F'|` bound. Instantiated for `F_{s,X}` (break at `|t|=T`) so its admissibility (`[T-ADM]`) is
not re-proved from scratch (review Q5).
#### Proof sketch (design)
Split at the break-points; on each `C¹` piece bound the variation by `∫|F'|` (FTC-2 +
`intervalIntegral`); glue with additivity of `eVariationOn`/`BoundedVariationOn`.
#### Mathlib lemmas
- `BoundedVariationOn`, `eVariationOn`, FTC-2 (`intervalIntegral.integral_deriv_eq_sub`).
#### Sources
- Standard real analysis; motivated by Belabas–Friedman `F_{s,X}` (eqs 11–12). Review Q5.
#### Generality
- `F : ℝ → ℂ` (or `ℝ → ℝ`) piecewise `C¹`. General.

### [CLEANUP-1] `/cleanup` on `AuxiliaryFunction.lean`
- **Status**: open · **Depends on**: T003 · **Type**: cleanup (after 3 tickets touch the file: T002, T003 + the def).

---

## Tier-3 spine (blocked on the epics)

- **[T010]** `lemma3` (eq 13) — `File`: `Lemma3.lean` — **Depends on**: SP1, SP2, T003 — statement + proof.
- **[T011]** `lemma4` (eq 14) — `File`: `Lemma4.lean` — **Depends on**: T010, SP3. ⚠ **Review Q5
  hotspot**: the `T`-vs-`T−a` trick (MVT + monotonicity to avoid a lost `log X`) — the hard part
  is proving the named real functions monotone on the *exact* numerical domains (`X ≥ 69`,
  `a = log 9`, `T = log X`); the constants `2.324/3.88/4.26` live here.
- **[T012] (milestone)** `belabas_friedman_thm1` — `File`: `MainTheorem.lean` — **Depends on**: T011, SP3, T001.
- **[T013]** `Refinements` (Thm 7, Cor 8) — **Depends on**: T012. *(Later /develop pass.)*
- **[T014]** `Residue` — bridge `|log κ_K − f_K(X)| ≤ …` to `log(h_K R_K)` via
  `dedekindZeta_residue` — **Depends on**: T012.

## Cleanup cadence (to expand as leaf tickets land)
- `[CLEANUP-1]` after T003 (AuxiliaryFunction). Per-file + pre-milestone `[CLEANUP-ALL]`
  before T012 and a final `[CLEANUP-FINAL] /cleanup-all` get inserted as each epic's leaf
  tickets are created.

## Next actions
1. `/beastmode` on **T001** (define `bSum`) and **T002/T003** (auxF API + Lemma 2) — the
   sorry-free, SP-independent near-term work.
2. `/develop --decompose` scoped to **SP1** (the foundation) — mirror mathlib/FltRegularBernoulli.
3. Acquire SP2/SP3 references (Poitou via Numdam; Stark), then their decompose passes.
4. `/blueprint` once SP1 leaf declarations exist (more decls to unformalise).
