# Development Plan: DedekindResidue

Effective, GRH-conditional bound on the residue of the Dedekind zeta function,
after **Belabas–Friedman**, *Computing the residue of the Dedekind zeta function*
(arXiv:1305.0035). Feeds the analytic class number formula for certified class-number
/ regulator computation. See `docs/2026-07-01-design.md` for the design rationale.

## Goal

Theorem 1 (target Lean statement; some objects — `f_K`, `Δ`, `n` — are project defs
introduced below, so the exact form settles once those land):

```lean
theorem belabas_friedman_thm1 {K : Type*} [Field K] [NumberField K]
    (hn : 1 < Module.finrank ℚ K)
    (hGRH : GeneralizedRiemannHypothesis K) (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 69 ≤ X) :
    |Real.log (NumberField.dedekindZeta_residue K) - f_K K X|
      ≤ 2.324 * Real.log Δ / (Real.sqrt X * Real.log (3 * X)) *
          ((1 + 3.88 / Real.log (X / 9)) * (1 + 2 / Real.sqrt (Real.log Δ)) ^ 2
            + 4.26 * (n - 1) / (Real.sqrt X * Real.log Δ)) := by sorry
```

with `Δ = |NumberField.discr K|`, `n = Module.finrank ℚ K`. The residue `κ_K` is
mathlib's `NumberField.dedekindZeta_residue K` (already proved equal to
`2^{r₁}(2π)^{r₂} R h / (w √|d_K|)`), so this bound is *directly* a certified handle on
`log(h_K R_K)`. Secondary targets: Theorem 7, Corollary 8 (refinements; later pass).

Note both `hGRH` (for `ζ_K`) and `hRH` (mathlib's `RiemannHypothesis` for the `k = ℚ`
comparison field) are **hypotheses, never axioms** — the sole assumptions; every other
result is unconditional and sorry-free.

## References

**Primary (the estimates — Tier 3):** Belabas–Friedman, arXiv:1305.0035
(`refs/ANCF/1305.0035.pdf`). Provides Theorems 1/7, Corollary 8, Lemmas 2–5 with full
proofs — but *cites without proof* three deep inputs (see "Deep sub-projects").

**Deep sub-project references (NOT Belabas–Friedman — must be sourced separately; not
yet in `refs/`):**
- **Weil–Poitou explicit formula** — Poitou, *Sur les petits discriminants* (1977);
  Weil (1952); Lang, *Algebraic Number Theory* Ch. XVII; Iwaniec–Kowalski §5.
- **Functional equation + completed `ζ_K` (general `K`)** — Hecke; Tate's thesis; Lang
  *ANT* Ch. XIII–XIV; Neukirch VII §5. (mathlib has ℚ + Dirichlet-L; AINTLIB
  FltRegularBernoulli has cyclotomic only.)
- **Stark's formula (19) / Landau–Stark bound** — Stark, *Some effective cases of the
  Brauer–Siegel theorem* (1974), eq. (9); Landau §180.

## Mathlib + AINTLIB inventory (verified 2026-07-01)

| Concept | Status | Action |
|---|---|---|
| `ζ_K`, `dedekindZeta_residue` (=ANCF value), `tendsto_sub_one_mul_dedekindZeta_nhdsGT` | mathlib `NumberField/DedekindZeta.lean` ✓ | USE |
| `classNumber`, `Units.regulator`, `discr`, `torsionOrder`, `nrRealPlaces`/`nrComplexPlaces`, `Ideal.absNorm` | mathlib ✓ | USE |
| `ζ_K = ∏_𝔭 (1−N𝔭^{−s})^{−1}`, prime-power sums, `primeIdealZetaSum`, ζ_K pole (log form) | Chebotarev `NumberFieldEulerProduct.lean`, `Density.lean` ✓ | IMPORT |
| `completedRiemannZeta`, `completedRiemannZeta_one_sub` (FE), `RiemannHypothesis` | mathlib `RiemannZeta.lean` ✓ | USE (`k=ℚ` side) |
| `WeakFEPair`/`StrongFEPair` (Mellin FE engine) | mathlib `AbstractFuncEq.lean` ✓ | BUILD ON (SP1) |
| `Gammaℝ`, `Gammaℂ` (Deligne), `Complex.digamma`, `eulerMascheroniConstant` (+bounds) | mathlib ✓ | USE |
| `mixedEmbedding` (Minkowski), `ZLattice.covolume`, Poisson summation, `Real.fourierIntegral`, `mellin`, `BoundedVariationOn` | mathlib ✓ | BUILD ON |
| cyclotomic completed `ζ_K` + FE (precedent to mirror) | FltRegularBernoulli `CompletedDedekindZeta.lean` | MIRROR (SP1) |
| Mellin→completed→FE→continuation template | LeanModularForms `LFunctionFEq.lean` | MIRROR (SP1) |

**Rule honoured:** never define what mathlib has. `κ_K`, all invariants, the FE engine,
gamma factors, and the ζ_K Euler product are consumed, not reproved.

## Deep sub-projects (API gaps — Belabas–Friedman cites these; we must build them)

The paper's own proof bottoms out at three results it treats as known. Under
"sorry-free, GRH-only" each becomes a sub-project with its own reference-driven
decomposition (a focused `/develop --decompose` per sub-project, once its reference is
in `refs/`):

- **SP1 — general `ζ_K` completed zeta + FE + Hadamard product + analytic control** (Tier
  1, `CompletedZeta/`). The foundation; the largest. **Route confirmed (expert review
  2026-07-01): the general-K Hecke theta stack** — n-dim Poisson (AG-P, Gaussian-class
  first) → lattice Gaussian theta (AG-Θ) → Hecke construction over the class group (AG-E,
  needs a Tate/Lang/Neukirch reference) → FE assembly. NOT Tate (adelic substrate too
  large), NOT abelian (validation-only). Implement it as a **Hecke-classical proof with
  Tate-style normalisation discipline** — every covolume, Fourier transform, discriminant
  factor and Γ-factor written for comparison against Tate, guarding against a hidden
  `2^{r₂}`/`π^{r₂}`/`√Δ_K`. **Tier 1 is larger than "FE + Hadamard": the review promotes
  an explicit analytic-control layer** — finite order of `Λ_K`, vertical-strip growth
  bounds, zeros as a locally-finite multiset with multiplicity + zero-sum manipulation, the
  canonical/Hadamard product *and its logarithmic derivative*, contour-shift estimates, the
  real-branch-of-log convention, and a pinned Γ-factor normalisation (residue constant with
  the `2^{r₂}` factor) fixed early. See `decomposition.md` and the restructured `[SP1]` epic
  (sub-epics AG-P/AG-Θ/AG-E/FE + **AC (analytic control)** + **N (normalisation)** + GRH) in
  `tickets.md`.
- **SP2 — Weil–Poitou explicit formula** (Tier 2, `ExplicitFormula/`). Source:
  Poitou/Lang/Iwaniec–Kowalski. Depends on SP1.
- **SP3 — Stark's formula (19) + Landau–Stark bound** (Tier 3, `Stark.lean`). Source:
  Stark/Landau. Depends on SP1 (Hadamard product + log-derivative of the FE).

Everything else — Lemmas 2–4, Theorems 1/7, Corollary 8, the auxiliary function `F_{s,X}`
and `f_K`/`B_K`, the residue bridge — is Belabas–Friedman's own content (Tier 3) and is
decomposed directly from `refs/ANCF/1305.0035.pdf`.

## File structure (proving order = module order; see design doc §5)

```
DedekindResidue/
  Basic.lean                       -- notation, imports (scaffold ✓)
  CompletedZeta/  (SP1)  DualLattice, ThetaLattice, Normalisation, GammaFactor,
                         FunctionalEquation, HadamardProduct, AnalyticControl, GRH
  ExplicitFormula/(SP2)  TestFunction, WeilPoitou
  Stark.lean       (SP3)
  AuxiliaryFunction.lean           -- F_{s,X} (11/12) + Fourier transform (Lemma 2)
  Lemma3.lean  Lemma4.lean  MainTheorem.lean  Refinements.lean  Residue.lean
```

## Dependency graph

```
              mathlib θ/Mellin/Poisson/WeakFEPair, mixedEmbedding
                                  │
                        SP1  CompletedZeta/  (Λ_K, FE, Hadamard, zeros, analytic control, normalisation)
                        │                     │
              ┌─────────┘                     └───────────┐
        SP2 WeilPoitou (explicit formula)            SP3 Stark (eq 19, Landau–Stark)
              │        + Chebotarev Euler product         │
              └───────────────┐        ┌──────────────────┘
    AuxiliaryFunction (F_{s,X}, Lemma 2)│
              │                         │
           Lemma3 (eq 13, uses GRH) ────┤
              │                         │
           Lemma4 (eq 14) ─────────────┤
              │                         │
           MainTheorem (Thm 1) ◄────────┘   ← + mathlib RiemannHypothesis (k=ℚ), ζ_ℚ zero-sum
              │
           Refinements (Thm 7, Cor 8),  Residue (bridge to log h_K R_K via dedekindZeta_residue)
```

GRH is used only from `Lemma3` upward (the `γ² + h² ≠ 0` continuation step) and in
`MainTheorem`.

## Generality decisions

- **General number field `K`, `1 < [K:ℚ]`** — the paper's setting; all final statements are
  general, never abelian-restricted. **Abelian / `K=ℚ` are used only as a *validation
  harness*** for the upper tiers (explicit-formula API, `F_{s,X}`, Lemma 2, the `T`-vs-`T−a`
  trick, constant chasing) — **not** as a substrate strategy: the abelian FE closes the wrong
  gaps (conductor–discriminant, ∏ root numbers, both separate projects). Expert review
  2026-07-01, Q3.
- **GRH (and `k=ℚ` RH) as hypotheses, never axioms.** `#print axioms` must stay
  `{propext, Classical.choice, Quot.sound}`.
- **Residues as `Tendsto (fun s ↦ (s−1) • f s) (𝓝[>] 1) (𝓝 c)`** — mathlib's convention
  (no residue primitive); matches `dedekindZeta_residue`.
- **Reuse over redefinition** — `κ_K`, invariants, gamma factors, the FE engine, the ζ_K
  Euler product are all consumed from mathlib/Chebotarev.
- **GRH provided in two equivalent forms** (expert review, Q4), both `Prop`, both hypotheses:
  `GRH_Λ K := ∀ s, completedDedekindZeta K s = 0 → s.re = 1/2` (zeros of `Λ_K` on the line —
  natural for the explicit-formula zero-sum over `ρ = ½+iγ`) and `GRH_{>½} K := ∀ s, ½ < s.re →
  dedekindZeta K s ≠ 0` (zero-free half-plane — natural for Lemma 3's analyticity of
  `log(ζ_K/ζ_k)`), plus an **equivalence lemma** (FE + Euler-product nonvanishing on `Re>1` +
  Γ-factors have no zeros). Mirrors mathlib's `RiemannHypothesis`; pinned once
  `completedDedekindZeta` (SP1) exists.

## Sequencing recommendation

Strict bottom-up ⇒ SP1 → SP2/SP3 → Tier 3. Do the detailed per-leaf decomposition one
sub-project at a time (a focused `/develop --decompose` each), **bottom-first (SP1)**, as
each is a mathlib-PR-scale effort with its own reference. This session establishes this
plan + the Theorem 1 spine decomposition + the sorried top-level skeleton; the deep
sub-project trees are authored next, once their references are in `refs/`.
