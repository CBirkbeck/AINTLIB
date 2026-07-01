# Ticket Board — DedekindResidue

## Summary
- Bottom-up (SP1 → SP2/SP3 → Tier 3). The three deep sub-projects are **epics**: each
  expands into leaf tickets via its own `/develop --decompose` pass (needs its reference).
- Concrete near-term (SP-independent, actionable now): T001, T002, T003.
- Tier-3 spine (T010–T014): blocked on the epics.
- Open: 12 · Epics needing decomposition: 3 · Blocked: 5

---

## Epics (need their own `/develop --decompose` pass before leaf tickets exist)

### [SP1] Completed ζ_K + functional equation + Hadamard product — the general theta stack
- **Status**: needs-decomposition · **Files**: `CompletedZeta/{ThetaLattice,GammaFactor,FunctionalEquation,HadamardProduct}.lean`
- **Type**: epic (foundation) · **Depends on**: AG-P → AG-Θ → AG-E · **Blocks**: SP2, SP3, T010+
- **Decision (2026-07-01)**: build the general-K Hecke theta route (not abelian-first). See
  `decomposition.md` § "Decision: build the general theta stack". Sub-epics, bottom-up:

  - **[SP1-AGP] n-dimensional Poisson summation** over a `ZLattice` — **START HERE** (self-contained
    real analysis; no external reference). Leaves: (P.1) dual lattice of a `ZLattice`
    [gap — none in mathlib]; (P.2) Poisson on `ℤⁿ` [from 1-D `Real.tsum_eq_tsum_fourier` by
    iteration / torus Fourier]; (P.3) transport to a general lattice + covolume factor
    [`ZLattice.covolume`, `VectorFourier.fourierIntegral`]. **Next action**: `/develop --decompose`
    scoped to SP1-AGP.
  - **[SP1-AGΘ] lattice Gaussian theta** `Θ_L(t)=∑_{x∈L}e^{-πt‖x‖²}` + transformation law —
    depends on SP1-AGP + n-dim Gaussian self-duality (assemble from 1-D
    `Gaussian/FourierTransform`).
  - **[SP1-AGE] Hecke construction** — ideal-lattice theta over `FundamentalCone` (unit action) +
    `ClassGroup 𝓞_K`, Mellin → gamma factors + `completedDedekindZeta` + FE. **Deepest; needs a
    reference PDF into `refs/` (Tate's thesis / Lang *ANT* XIII–XIV / Neukirch VII §5).**
  - **[SP1-FE] assembly**: `completedDedekindZeta_one_sub` (clean FE), continuation + poles tied
    to `dedekindZeta_residue`, Hadamard product / zero set / `γ_ρ ∈ ℝ` — replaces the current stubs.
  - **[SP1-Γ] `GammaFactor.lean`**: `Γℝ^{r₁}Γℂ^{r₂}` bookkeeping → mathlib Deligne (leaf).

### [SP2] Weil–Poitou explicit formula
- **Status**: needs-decomposition · **File**: `ExplicitFormula/WeilPoitou.lean`
- **Type**: epic · **Depends on**: SP1 · **Blocks**: T004 (Lemma 3)
- **Goal**: the explicit formula (eqs 1, 3): `Σ_ρ F̂(γ_ρ) = −2 Σ_{𝔭,m} (log N𝔭/N𝔭^{m/2})
  F(m log N𝔭) + 4∫F(x)cosh(x/2)dx + F(0)(log Δ_K − n_K C − n_K log 8π − r_K π/2) +
  n_K∫(F(0)−F)/(2 sinh) + r_K∫(F(0)−F)/(2 cosh)`. **Route**: Poitou (Numdam) / Lang *ANT*
  XVII / Iwaniec–Kowalski §5 — contour integral of `−Λ'_K/Λ_K`. Reuse Chebotarev Euler
  product for the prime side. **Next action**: acquire reference, then `/develop --decompose`.

### [SP3] Stark's formula + Landau–Stark bound
- **Status**: needs-decomposition · **File**: `Stark.lean`
- **Type**: epic · **Depends on**: SP1 · **Blocks**: T005 (Lemma 4), T012 (Thm 1)
- **Goal**: eq (19) `Σ_ρ 1/(σ−ρ) = ½log Δ_K + 1/(σ−1) + 1/σ − ½ d_{K,σ}` and Lemma 5
  `Σ_ρ (¼+γ_ρ²)^{−1} = O(log Δ_K)`. **Route**: Stark 1974 eq (9); Landau §180; mathlib
  `digamma`. **Next action**: acquire reference, then `/develop --decompose`.

---

## Concrete near-term tickets (actionable now — SP-independent)

### [T001] Define `bSum` (`B_K(X)`) — replace the stub
- **Status**: open · **File**: `MainTheorem.lean` · **Depends on**: none · **Parallel**: yes · **Type**: def
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
- **Status**: open · **File**: `AuxiliaryFunction.lean` · **Depends on**: none · **Parallel**: yes · **Type**: lemma
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
#### Mathlib lemmas
- `Real.fourierIntegral`, `intervalIntegral.integral_comp`, `integral_cos`, integration-by-parts
  lemmas; `Complex.exp` derivatives.
#### Sources
- Belabas–Friedman, Lemma 2, eqs (7)–(8), pp. 5–6.
#### Generality
- `s : ℂ` with `½ < Re s`; `X : ℝ`, `1 < X`.

### [CLEANUP-1] `/cleanup` on `AuxiliaryFunction.lean`
- **Status**: open · **Depends on**: T003 · **Type**: cleanup (after 3 tickets touch the file: T002, T003 + the def).

---

## Tier-3 spine (blocked on the epics)

- **[T010]** `lemma3` (eq 13) — `File`: `Lemma3.lean` — **Depends on**: SP1, SP2, T003 — statement + proof.
- **[T011]** `lemma4` (eq 14) — `File`: `Lemma4.lean` — **Depends on**: T010, SP3.
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
