# `/mathlibable` report — `PadicLFunctions.MeasureR.sum_seriesEval_Ftilde`

**Final verdict: `BORDERLINE-needs-human`.**

Mode A, full 10-phase workflow with the exhaustive 9-channel literature search.
The literature search positively identified the source and the exact step
(RJW §6.2, the unnumbered φ∘ψ-trace inside the proof of Theorem 6.1(ii) /
Leopoldt's formula); the ChatGPT MCP channel is unavailable in this environment
and was substituted with extra WebSearch + a verbatim primary-source extraction
(`pdftotext` of the arXiv PDF, §6.2). `lake build` was **not** re-run (stale/slow
per the task note); reasoned from source per the Phase-0 fallback.

This is the **Dirichlet-character-twisted (Leopoldt, `L_p(θ,1)`) sibling** of the
already-assessed `PadicLFunctions.sum_seriesEval_FtildeA` (the ζ_p-residue version
of the identical μ_p-trace step), which was also `BORDERLINE-needs-human`. The
structural situation is the same; the verdict matches.

---

### Baseline (Phase 0)

- lake build:               **not re-run** (stale/slow per task note); reasoned from source (Phase-0 fallback). The file elaborates as part of `main`; all dependencies read directly.
- decl `PadicLFunctions.MeasureR.sum_seriesEval_Ftilde`: resolved at
  `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:1353`
- kind:                      theorem
- has sorry:                 **no** (proof complete, lines 1353–1443; verified `grep` — no `sorry`/`admit`)
- namespace:                 `PadicLFunctions` → `MeasureR` (opened at lines 35, 37; closed 1802, 1804) → qualified name `PadicLFunctions.MeasureR.sum_seriesEval_Ftilde`
- module docstring summary:  "The p-adic value `L_p(θ,1)` (RJW §6.2, Thm 6.1(ii), decomposition P6)" — the file formalises **Leopoldt's formula** for the value at `s=1` of the p-adic L-function of a non-trivial Dirichlet character `θ = χη`, following Rodrigues Jacinto–Williams, working over a complete ultrametric normed `ℚ_p`-algebra `K` carrying `μ_N`.

---

### Statement (Phase 1)

`PadicLFunctions.MeasureR.sum_seriesEval_Ftilde` is a **theorem** stating the following.

Let `p` be a prime, `K` a complete ultrametric normed `ℚ_p`-algebra of
characteristic 0, `N > 1`, `θ` a **primitive** Dirichlet character mod `N` over
`K` with `θ ≠ 1`, `ε ∈ K` a primitive `N`-th root of unity, and `ξ ∈ K` a primitive
`p`-th root of unity. Assume the **norm-one hypothesis** `hnorm`: for every
`c ∈ {0,…,N-1}` coprime to `N` (i.e. `(c : ZMod N)` a unit), `‖ε^c − 1‖ = 1`. Then
the sum over the `p`-th roots of unity of the **series evaluation** of RJW's explicit
antiderivative power series `F̃_θ` collapses to `θ(p)` times its constant coefficient:

$$\sum_{i=0}^{p-1} \widetilde{F}_\theta(\xi^{\,i} - 1)\;=\;\theta(p)\cdot \widetilde{F}_\theta(0).$$

Here `F̃_θ` (project def `Ftilde`) is RJW's G-cleared antiderivative
`F̃_θ(T) = −G(θ⁻¹)⁻¹ · Σ_{c<N} θ⁻¹(c)·log((1+T)ε^c − 1)`, realised in Lean as
`−Σ_{c<N} C(θ⁻¹(c)) · logSeriesAt p K (ε^c)` where `logSeriesAt u` is the per-root
log power series with constant term `extLog(u−1)`; `seriesEval F z = Σ_n (coeff_n F)·zⁿ`
is junk-total power-series evaluation (a `tsum`); `extLog` is the project's
Iwasawa-branch (`log_p p = 0`) extended logarithm (`ExtLog.lean`); and
`constantCoeff (Ftilde …)` is `F̃_θ(0)`.

Variables / typeclasses (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime.
- `K : Type*`, `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]` — the ambient p-adic field; `μ_N, μ_p ⊆ K` supplied by the `ε`, `ξ` hypotheses.
- `{N : ℕ}`, `[NeZero N]` — the conductor.
- `{θ : DirichletCharacter K N}` — the Dirichlet character (the `θ⁻¹` is the inverse character).

Hypotheses (Lean side):
- `hN : 1 < N` — non-degenerate conductor.
- `hprim : θ.IsPrimitive` — `θ` primitive (drives the `sum_theta_inv_mul_extLog_pc` `c↦pc` bookkeeping, both the automorphism `¬p∣N` and the primitive-character fiber-sum `p∣N` cases).
- `_hθ1 : θ ≠ 1` — non-triviality (Leopoldt's hypothesis; carried but only used implicitly).
- `hε : IsPrimitiveRoot ε N` — `ε` generates `μ_N`.
- `hξ : IsPrimitiveRoot ξ p` — `ξ` generates `μ_p` (the trace is *over* `μ_p`).
- `hnorm : ∀ c ∈ Finset.range N, IsUnit (c : ZMod N) → ‖ε^c − 1‖ = 1` — the coprime-guarded norm-one fact (replan R6.6; the non-unit terms vanish via `θ⁻¹(c)=0`).

Conclusion (math): the `μ_p`-trace of `F̃_θ` equals `θ(p)·F̃_θ(0)`.
Conclusion (Lean): `∑ i : Fin p, seriesEval (Ftilde p K θ hε) (ξ ^ (i:ℕ) − 1) = θ ((p : ZMod N)) * PowerSeries.constantCoeff (Ftilde p K θ hε)`.

**Source identification (load-bearing).** This is the **unnumbered φ∘ψ-trace step
inside the proof of RJW Theorem 6.1(ii)** (Rodrigues Jacinto–Williams, *An
Introduction to p-adic L-functions*, §6.2). RJW Theorem 6.1(ii) is **Leopoldt's
formula**:
`L_p(θ,1) = −(1 − θ(p)p⁻¹)·G(θ⁻¹)⁻¹·Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·log_p(1 − ε_N^c)`.
The target here is the step in its proof (verbatim, §6.2, case n=0):
`ϕ∘ψ(F̃_θ) = (1/p)·Σ_{ξ∈μ_p} F̃_θ((1+T)ξ−1)`, which evaluated at `T=0` via the
μ_p-collapse `Σ_{ξ∈μ_p} log_p(ξε_N^c−1) = log_p(ε_N^{pc}−1)` and the `c↦pc` reindex
gives `ϕ∘ψ(F̃_θ)(0) = (θ(p)/p)·F̃_θ(0)`; multiplying by `p` is exactly this theorem's
`Σ_{i<p} F̃_θ(ξⁱ−1) = θ(p)·F̃_θ(0)`. The source dispatches it inline in a displayed
multi-line computation — it is **below the granularity RJW number** (it is not a
lemma; it is two displayed lines in the proof of Theorem 6.1(ii)).

---

### Size classification (Phase 2a)

Verdict: **SMALL** (but a substantial ~90-line glue step).
Reason: it is a proof step inside the assembly of one theorem (Leopoldt's formula,
`LpFunction_one`) — not a new structure, not named after a person/place, not a
`## Main results` headline. The headline result of the file is Theorem 6.1(ii)
itself (the value `L_p(θ,1)`); this is STEP 2 / T616 feeding into it.

(Literature width was EXHAUSTIVE regardless. The SMALL tag only frames the report:
this is internal bookkeeping toward a named theorem, which biases away from a
standalone mathlib lemma.)

### One-line check (Phase 2b)

Body line count: ~90 substantive lines. One-liner verdict: **n/a — kind is `theorem`.**

---

### PHASE 3 — Literature search (EXHAUSTIVE 9-channel protocol)

#### Literature search table

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Rodrigues Jacinto Williams introduction to p-adic L-functions Theorem 6.1 Leopoldt formula `L_p(θ,1)` Gauss sum p-adic logarithm" | **yes** | identifies the paper (MSP/Essential Number Theory 4 (2025) no.1; arXiv 2309.15692); §6.2 = "the p-adic value at s=1", Thm 6.1(ii) due to Leopoldt | exact source for the project file |
| 2 | WebSearch (general / named form) | "Leopoldt formula p-adic L-function value at 1 `L_p(χ,1)` Gauss sum p-adic log sum over roots of unity Dirichlet character" | **yes** | returned Leopoldt's formula verbatim: `L_p(1,χ) = −(1−χ(p)/p)·(τ(χ)/f)·Σ_a χ̄(a)·log_p(1−ζ^a)` (Springer/Washington Ch.4) | the *ambient* named theorem; confirms the `θ(p)` factor = the `χ(p)/p` Euler factor |
| 3 | WebSearch (machinery / aliases) | "p-adic L-function antiderivative power series trace over p-th roots of unity θ(p) constant coefficient distribution Mahler transform" | partial | Mahler transform of measures on `ℤ_p`; Iwasawa power series; ϕ/ψ-operator machinery is standard | the *machinery* (ϕ∘ψ, Mahler transform) is standard; the trace-collapse step is not independently named |
| 4 | WebSearch (μ_p-collapse) | "μ_p collapse identity sum over p-th roots of unity log(ξw−1)=log(w^p−1) p-adic Iwasawa norm cyclotomic" | partial | `Π_{ξ∈μ_p}(Xξ−1)=Xᵖ−1` is the standard cyclotomic identity; `log_p` additive on principal units | both ingredients standard; their combination here is the proof step, not a named lemma |
| 5 | **Primary source, verbatim** (`pdftotext` of arXiv 2309.15692, §6.2) | Theorem 6.1 + the proof of Thm 6.1(ii), lines 3390–3960 | **yes (decisive)** | Thm 6.1(ii) verbatim (Leopoldt). Proof, case n=0: `ϕ∘ψ(F̃_θ) = (1/p)Σ_{ξ∈μ_p}F̃_θ((1+T)ξ−1)`; at `T=0`, μ_p-collapse + `c↦pc` ⟹ `ϕ∘ψ(F̃_θ)(0)=(θ(p)/p)F̃_θ(0)`. Case n≥1: `χ\|_{pℤ_p}=0` ⟹ `ϕ∘ψ(F̃_θ)=0` and `θ(p)=0`, both sides vanish. | **the target = `p·ϕ∘ψ(F̃_θ)(0) = Σ_{i<p}F̃_θ(ξⁱ−1) = θ(p)F̃_θ(0)`, an unnumbered displayed step in the proof of Thm 6.1(ii); the two-case split p\|N / ¬p\|N is RJW's, faithfully mirrored** |
| 6 | nLab | "Iwasawa theory" (Kubota–Leopoldt ζ_p, main conjecture, `g_i(v^s−1)=L_p(ω^{1−i},s)`) | partial (ambient only) | survey of Iwasawa theory + main conjecture; carries `L_p` notation but no per-step lemma | not a categorical concept; nLab has **no** φ∘ψ-trace, **no** Leopoldt-formula proof, **no** antiderivative-sum identity (fetched & confirmed survey-altitude only) |
| 7 | nCatLab (categorical?) | (categorical reformulation of the trace step?) | n/a | — | not a categorical concept — an explicit p-adic analytic computation over a normed field |
| 8 | Stacks Project (alg-geom?) | (algebraic-geometry concept?) | n/a | — | not an algebraic-geometry concept — p-adic functional analysis / Iwasawa theory |
| 9 | MathOverflow / Math.SE | "sum over μ_p of p-adic log = log; Leopoldt `L_p(θ,1)`; φ∘ψ trace" | n/a (not surfaced) | — | not reachable as an independent fetch channel here; the decisive standard-form question is answered directly by channels 2 + 5 (named theorem + verbatim proof), so this n/a does not weaken the protocol |
| 10 | recent arXiv (≤5 yr) + formalization | "formalization Lean mathlib p-adic L-function Kubota–Leopoldt value at one Leopoldt formula extended logarithm" | yes (context) | **arXiv 2302.14491** (Narayanan, *Formalization of p-adic L-functions in Lean 3* — Kubota–Leopoldt via generalized Bernoulli numbers); **arXiv 2201.08870** (sum expressions for K–L p-adic L-functions) | establishes the state of the art: the only Lean p-adic L-function work is **Lean 3, never ported to mathlib4**, and approaches via Bernoulli numbers — **not** the `extLog` / Mahler-transform / value-at-1 route this project takes. Leopoldt's formula via this route is formalised **nowhere public**. |

**Protocol compliance.** WebSearch ran 4 distinct queries at different generality
levels (#1 specific source, #2 the most-general named form = Leopoldt's formula,
#3 the machinery/aliases, #4 the μ_p-collapse ingredient). The ChatGPT MCP channel
is unavailable in this environment (only unrelated OAuth stubs surfaced in the
deferred-tool list); it is substituted by extra WebSearch (#3, #4) **and** a
verbatim primary-source extraction (#5 — `pdftotext` of the arXiv PDF §6.2), which
answers the standard-form / generality / case-split questions directly and
authoritatively from RJW. Local references checked: **n/a** (no
`.mathlib-quality/references/` directory and no `refs/` PDFs present — recorded
n/a). nLab checked (#6). nCatLab / Stacks / MathOverflow / arXiv each addressed
(#7–#10).

#### Literature summary (Phase 3)

Concept identified as: **the φ∘ψ-trace step inside the proof of RJW Theorem 6.1(ii)
(Leopoldt's formula for `L_p(θ,1)`)** — Rodrigues Jacinto–Williams, *An Introduction
to p-adic L-functions*, §6.2 "The p-adic value at s = 1". Mathematically: the
`μ_p`-trace of the antiderivative power series `F̃_θ` evaluates to `θ(p)·F̃_θ(0)`,
via the μ_p-collapse `Σ_{ξ∈μ_p} log_p(ξε^c−1) = log_p(ε^{pc}−1)` and the `c↦pc`
reindex (for `n=0`; for `n≥1` both sides vanish because `θ(p)=0`).

Sources agree on the standard form: **n/a — there is no standard *standalone* form.**
The literature names the *ambient* result (Theorem 6.1(ii) = Leopoldt's formula,
with the well-known closed form `L_p(θ,1) = −(1−θ(p)p⁻¹)G(θ⁻¹)⁻¹Σθ⁻¹(c)log_p(1−ε^c)`),
but the target is the **unnumbered intermediate computation** RJW dispatch in a
displayed two-line step inside that proof. No external work treats it as a citeable
object.

Most general standard form: not applicable — the statement is fused to the project's
own objects (`Ftilde`, `seriesEval`, `extLog`, `logSeriesAt`), each a project-specific
realisation of an RJW construction. The named anchor (Leopoldt's formula) is the
*downstream wrapper* `LpFunction_one`, not this step.

Generality dimensions where the literature varies: none meaningful. `N`, `θ`
primitive, `θ ≠ 1`, the `μ_N`/`μ_p`-carrying field, and the coprime-guarded norm-one
hypothesis are all intrinsic to RJW's setting (`θ = χη`, `η` tame conductor `D > 1`
prime to `p`, `χ` of conductor `pⁿ`), not incidental restrictions one would weaken.

Disagreement with the literature: **none.** The Lean statement faithfully transcribes
RJW's φ∘ψ step (with the project's bookkeeping that `p·ϕ∘ψ(F̃_θ)(0) = Σ_i seriesEval(F̃_θ)(ξⁱ−1)`),
and the two-case proof (`p∣N` vanishing / `¬p∣N` collapse) is exactly RJW's case split.

**Signal.** The exhaustive sweep returned the *named ambient theorem* (Leopoldt's
formula) and its *verbatim proof*, but **no independent name or standalone standard
form for the target step**. Per the verdict reference, literature naming the
surroundings but not the step is a strong signal that the decl is
internal-construction bookkeeping — biasing Phase 7 toward BORDERLINE / NO, never
toward a standalone YES.

---

### PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): there is **no standalone standard form**;
the target is an internal step in the proof of Theorem 6.1(ii). The closest *named*
anchor is Leopoldt's formula itself — a downstream wrapper, mirrored by the project's
own `LpFunction_one` assembly (lines ~1700+), not by this step.

#### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `K` complete ultrametric normed `ℚ_p`-algebra, CharZero, with `μ_N` | a field `K ⊇ ℚ_p(μ_N)` (e.g. ℂ_p) | RJW work over `ℂ_p` / a field containing `μ_N` | NO | `seriesEval` needs summability (ultrametric + complete); `μ_N, μ_p ⊆ K` essential to even *state* the sum; `extLog` defined here. This *is* RJW's setting. |
| 2 | `hN : 1 < N` | conductor > 1 | RJW: `θ` non-trivial ⟹ `N > 1` | NO | a conductor-1 character is trivial; excluded by `θ ≠ 1`. Intrinsic. |
| 3 | `hprim : θ.IsPrimitive` | θ primitive | RJW: `θ = χη` written at its conductor | NO | the `c↦pc` bookkeeping (`sum_theta_inv_mul_extLog_pc`) uses primitivity (fiber sums in the `p∣N` case). Intrinsic. |
| 4 | `_hθ1 : θ ≠ 1` | θ ≠ 1 | RJW: θ non-trivial (Leopoldt's hypothesis) | NO | Leopoldt's formula is *about* non-trivial θ; the trivial character is ζ_p (a different object, the `sum_seriesEval_FtildeA` sibling). Intrinsic. |
| 5 | `hε : IsPrimitiveRoot ε N` | ε generates μ_N | RJW: ε_N a primitive N-th root | NO | the formula is stated at the primitive root; `Ftilde` is parametrised by it. Intrinsic. |
| 6 | `hξ : IsPrimitiveRoot ξ p` | ξ generates μ_p | RJW: ξ ∈ μ_p (the trace is over μ_p) | NO | the sum is *over* μ_p; primitivity pins the indexing `i ↦ ξⁱ`. Intrinsic. |
| 7 | `hnorm` (coprime-guarded `‖ε^c−1‖=1`) | norm-one on coprime c | RJW: implicit (`ε_N^c` a unit for `(N,p)=1`; mixed case via the tame part) | NO | needed so every shifted argument `ξⁱε^c−1` lies in the extended-log domain (replan R6.6); the non-unit terms vanish (`θ⁻¹(c)=0`). Intrinsic; the project discharges it via `norm_pow_sub_one_eq_one_of_unit`. |

#### 4b. Generality verdict

The current form is: **MAXIMALLY GENERAL** *for what it is* — but "maximally general"
is the wrong frame here. Every hypothesis is intrinsic to RJW's construction; there is
no weakening to propose, and no broader literature form to aim at. The decl is not a
narrowed specialisation of anything; it is a fixed internal step in the proof of a
named theorem.

Number of weakening opportunities found: **0**.
Proposed restatement: none.
Cost of restatement: n/a.

#### 4c. Modern mathlib-idiom check (Bourbaki 2.0)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | already fully typeclass-driven (`NormedAlgebra ℚ_[p] K`, `IsUltrametricDist`, `DirichletCharacter`) | — |
| 2 | sequences/metric → filters/topological? | no | the trace is a finite `Finset.sum` over `Fin p`; `seriesEval` already uses `tsum` (a filter-limit). No sequence to filter-ise. | — |
| 3 | construct an object → universal-property class? | no | this is a *value identity*, not a construction. | — |
| 4 | set+closure-predicate → bundled substructure? | no | no substructure here. | — |
| 5 | vector-space/metric/field-specific → weaken typeclasses? | no | already at the natural `NormedField`/`NormedAlgebra ℚ_p` level dictated by `extLog`/`seriesEval`/`logSeriesAt`. | — |
| 6 | 1-categorical → higher-categorical? | no | purely an analytic/algebraic computation. | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | the index `Fin p` *is* `μ_p`; `N`, `c` are genuine natural-number conductors/residues. Not generalisable. | — |

Modern idiom available: **no.** One-line reason: the statement is an explicit finite
p-adic identity over the exact typeclass setting its constituent objects (`Ftilde`,
`seriesEval`, `extLog`, `logSeriesAt`) demand — there is no contemporary-idiom
reorganisation that composes with more of mathlib, because mathlib has **none** of
these objects to compose with (confirmed in Phase 5).

---

### PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`** (introduces no definitional equalities or
typeclass-search paths).

---

### PHASE 5 — Mathlib search (five-method)

#### Mathlib search-status: `PadicLFunctions.MeasureR.sum_seriesEval_Ftilde`

```
[A] Lean-Finder   n/a — MCP not available in this environment (substituted by D + web NL queries).
[B] Loogle        n/a — MCP not surfaced; substituted by structural grep over the
                  local mathlib checkout (./.lake/packages/mathlib/Mathlib) for the
                  building blocks and for the constituent objects.
[C] LeanSearch    n/a — MCP not surfaced; substituted by WebSearch NL queries
                  (Phase 3 #2, #3, #4) and grep.
[D] Grep mathlib  searched: `def extLog`, `ExtLogDomain`, `def seriesEval`,
    src           `def Ftilde`, `def padicLog`, `InExpBall`, `Leopoldt`, `Kubota`,
                  `pAdicLFunction`/`padicLFunction`/`PadicLFunction`,
                  `DirichletCharacter.*padic`, `padic.*log`, cyclotomic product
                  identities, `IsPrimitiveRoot` API, `MahlerBasis`.
[E] Name pattern  searched repo-wide for `sum_seriesEval_Ftilde`, `seriesEval`,
                  `Ftilde`, `extLog`, `logSeriesAt`, `padicLog`, `InExpBall`.
```

Searched for **both** the user's current form **and** the (non-existent) literature-
standard standalone form, and for the named ambient theorem (Leopoldt's formula).

Findings:
- **None of the constituent objects exist in mathlib** (grep returned **0 files**
  each): `extLog`, `ExtLogDomain`, `seriesEval`, `Ftilde`, `padicLog`, `InExpBall`.
  All are project-local (`ExtLog.lean:286`/`278`, `MeasureR/FormalPsi.lean:577`,
  `ValuesAtOne.lean:53`/`46`, `PadicExp.lean`).
- **Mathlib has NO p-adic L-function / Kubota–Leopoldt machinery** at all. Grep over
  `Mathlib/NumberTheory/` for `Kubota`, `pAdicLFunction`, `Leopoldt`,
  `DirichletCharacter.*padic` returned **nothing**. The Lean-3 formalisation
  (arXiv 2302.14491) was never ported to mathlib4, and it uses Bernoulli numbers,
  not this `extLog`/Mahler-transform/value-at-1 route.
- The `padic.*log` hits (3 files) are about `Padic`/`padicValNat` valuation-log
  bounds, **not** a p-adic logarithm *function* — unrelated.
- Mathlib **does** have the *individual* building blocks: the cyclotomic product /
  primitive-root API (`RingTheory/RootsOfUnity/Lemmas.lean`
  `prod_pow_sub_one_eq_order`, `RingTheory/RootsOfUnity/CyclotomicUnits.lean`
  `associated_pow_sub_one_pow_of_coprime`, `Polynomial.X_pow_sub_one_eq_prod`), and
  `NumberTheory/Padics/MahlerBasis.lean` (the Mahler basis of `C(ℤ_p, field)` — a
  building block, not the L-function transform). `DirichletCharacter` / `LSeries`
  exist but for **complex** L-functions, not p-adic.

Concluded: **not in mathlib** (all methods exhausted — including the constituent
objects, the named ambient theorem, and the literature framing). **Mathlib cannot
even state this theorem**: the objects `extLog`, `seriesEval`, `Ftilde`,
`logSeriesAt`, `padicLog` do not exist there, and there is no p-adic L-function
development to host it. Of the genuinely-mathlib ingredients, only the cyclotomic
product identity and the `IsPrimitiveRoot` API are reused; everything p-adic-analytic
is project-local. Both NO buckets are therefore excluded.

---

### PHASE 6 — Composition check (+ call-sites)

#### 6.0 Call sites — `PadicLFunctions.MeasureR.sum_seriesEval_Ftilde`

Internal use count: **K = 1** (within the project, excluding the declaring line).
External-to-file callers: 0 distinct files. Cross-project callers: 0 (grep over
`projects/` for `sum_seriesEval_Ftilde` outside the declaring file returns only the
sibling `sum_seriesEval_FtildeA`, a *different* name, in `ResidueZeta.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `ValuesAtOne.lean:1741` | `have hT616 := sum_seriesEval_Ftilde hN hprim hθ1 hε hξ hnorm` — STEP 2 / T616 inside the assembly of Leopoldt's formula `L_p(θ,1)` (the `LpFunction_one` development) |

Inline-derivation grep (was the equivalent re-derived elsewhere without this lemma?):
**(none)** — the `μ_p`-trace for the twisted `F̃_θ` is computed *only* here. (The
ζ_p-residue analogue is computed once, separately, in `sum_seriesEval_FtildeA`.)

Call-sites reading: **K = 1 internal use, no inline re-derivation** → "possibly the
wrong abstraction / could be inlined" per the signal table — but here it is a
deliberate proof decomposition (a ~90-line step factored out of the Leopoldt-formula
assembly, T616 in the project's ledger), not an accidental wrapper. The single
consumer is the value-at-1 assembly that this step feeds.

#### 6a. Composition attempt

Can `sum_seriesEval_Ftilde` be derived from mathlib in ≤3 chained calls? **No.**

Attempt 1 (sketch): the proof is ~90 lines (`ValuesAtOne.lean:1359–1443`) and chains
**five-plus project-local lemmas** plus genuine reasoning:
- `seriesEval_logSeriesAt_eq_extLog` (the per-term identity `seriesEval(logSeriesAt(ε^c))(ξⁱ−1) = extLog(ξⁱε^c−1)`),
- `summable_seriesEval_logSeriesAt` (summability, to commute `tsum` with the finite `Σ_c`),
- `sum_extLog_pow_mul_collapse` (the `μ_p`-collapse `Σ_{i<p} extLog(ξⁱε^c−1) = extLog(ε^{pc}−1)`),
- `sum_theta_inv_mul_extLog_pc` (the `c↦pc` bookkeeping — automorphism for `¬p∣N`, primitive-character fiber sums for `p∣N`),
- the constant-coefficient computation of `Ftilde` (coeff-0 of `logSeriesAt = extLog(ε^c−1)`),
plus `MulChar.map_nonunit` to kill non-unit `c`, a two-case `by_cases IsUnit (c:ZMod N)`
split, `Finset.sum_comm`, `Summable.tsum_finsetSum`, `tsum_congr`, and a final `ring`.
  - Mathlib decls used: only peripheral (`PowerSeries.coeff_*`, `Finset.*`,
    `MulChar.map_nonunit`, `tsum`/`Summable` API, `ring`).
  - Result: **fails** as a composition — the substance is project-specific.

Conclusion: **NOT-COMPOSABLE.** This is a real, substantial proof, not a 1–3-call
mathlib glue. (And the building blocks it composes are themselves project-local, so
even "inline at the call site" is impossible without first upstreaming `extLog`,
`seriesEval`, `Ftilde`, `logSeriesAt`, and the four named helper lemmas.)

---

## Verdict: `PadicLFunctions.MeasureR.sum_seriesEval_Ftilde`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): identified as the **unnumbered φ∘ψ-trace step inside
  the proof of RJW Theorem 6.1(ii) — Leopoldt's formula for `L_p(θ,1)`** (Rodrigues
  Jacinto–Williams, §6.2). Verbatim primary-source extraction confirmed the exact
  step (`p·ϕ∘ψ(F̃_θ)(0) = Σ_{i<p}F̃_θ(ξⁱ−1) = θ(p)F̃_θ(0)`) and the two-case split
  `p∣N`/`¬p∣N`. The literature names the surrounding theorem (Leopoldt's formula) and
  proves it, but gives **the target step itself no standalone name or standard form**.
- Generality analysis (Phase 4): MAXIMALLY GENERAL *for what it is* — 0 weakenings;
  every hypothesis intrinsic to RJW's `θ = χη` setting. Phase 4c: no modern-idiom
  reformulation (nothing in mathlib to compose with).
- Mathlib search (Phase 5): **not in mathlib**, and *cannot be* — `extLog`,
  `seriesEval`, `Ftilde`, `logSeriesAt`, `padicLog`, and **all** p-adic L-function /
  Kubota–Leopoldt machinery are absent from mathlib (0 files); only the cyclotomic
  product identity + `IsPrimitiveRoot` API are genuinely reused.
- Composition check (Phase 6): **NOT-COMPOSABLE** (~90-line proof over 5+ project
  lemmas + a two-case split); call sites **K = 1**, no inline re-derivation, name
  unique to the file.

**Rationale.**
The decision genuinely turns on a judgment the skill cannot make from the evidence
alone, which is the definition of BORDERLINE. The clean buckets are all excluded: it
is **not `NO-mathlib-has-it`** (mathlib has nothing to redirect to — it cannot even
state the theorem); it is **not `NO-composable-from-mathlib`** (the proof is large and
its building blocks are themselves non-mathlib); and it is **not a clean YES**, because
(a) the target is not a standalone, literature-recognised statement — it is the
unnumbered φ∘ψ-trace that RJW dispatch inline in a displayed computation, and (b) it is
welded to four project-specific objects (`Ftilde`, `seriesEval`, `extLog`,
`logSeriesAt`) and four project-specific helper lemmas, none of which exist in mathlib.
A `YES-add-as-is` verdict would also fail the Phase-7 gate's "name the concrete mathlib
gap" requirement: the only honest gap is "mathlib has no p-adic L-functions at all,"
which is a *programme*, not a single-lemma contribution.

The real question is therefore upstream of this lemma: **should the whole p-adic
L-function / Leopoldt-formula development (the `padicLog` + `extLog` + `logSeriesAt` +
Mahler-transform machinery this project builds, RJW Part I §3–§6) be contributed to
mathlib?** If yes, this lemma rides along as one private step of the Leopoldt-formula
(`LpFunction_one` / Theorem 6.1(ii)) proof — almost certainly inlined or kept
`private`, *not* shipped as a standalone public API lemma (K = 1, no external consumer,
no independent name). If the development stays project-local (the current AINTLIB
posture — `ValuesAtOne` is research-frontier work), this decl is correctly
project-internal as-is. That is a project-policy + mathlib-roadmap call, not a
mathematical one — hence BORDERLINE. This matches Case 5 in the verdict reference (a
project-specific analytic-number-theory bookkeeping result built on non-mathlib
objects, single internal use), and it matches the verdict already reached for the
direct ζ_p-residue sibling `sum_seriesEval_FtildeA` (`BORDERLINE-needs-human`) and the
parent def `Ftilde` (`NO-composable-from-mathlib`).

**Numbered questions (≤5):**

1. **Is the entire p-adic L-function development in `PadicLFunctions/` intended for
   eventual mathlib upstreaming**, or is it permanently project-local research-frontier
   work? (This is the gating question — every sub-verdict below depends on it.)
2. If upstreaming is intended: the foundational objects this lemma rests on —
   **`padicLog`, `extLog`, `seriesEval`, `logSeriesAt`, and the Mahler-transform
   machinery** — are the true contributions and must go first. Should those be
   assessed/PR'd as a *batch* (e.g. `/mathlibable` Mode B over `PadicExp.lean`,
   `ExtLog.lean`, `MeasureR/FormalPsi.lean`), with this trace step deferred until they
   land?
3. Even under upstreaming, this φ∘ψ-trace step has **K = 1 internal use, no external
   consumer, and no name in the literature** (RJW do not number it). Do you agree it
   should be **inlined into (or kept `private` to) the proof of the Leopoldt-formula
   assembly (`LpFunction_one` / RJW Theorem 6.1(ii))** rather than shipped as a
   standalone public mathlib lemma?
4. If a packaged public result *is* wanted, the **citeable** RJW object is **Theorem
   6.1(ii)** itself — **Leopoldt's formula** `L_p(θ,1) = −(1−θ(p)p⁻¹)G(θ⁻¹)⁻¹Σθ⁻¹(c)log_p(1−ε^c)`
   — the project's downstream value-at-1 result. Should the mathlibable effort target
   *that* named theorem, treating `sum_seriesEval_Ftilde` purely as supporting
   machinery?
5. The ζ_p-residue sibling `sum_seriesEval_FtildeA` (the same μ_p-trace step for the
   trivial character / residue) was already assessed `BORDERLINE-needs-human` with the
   same reasoning. Do you want the two siblings — and the four-name `extLog`/`seriesEval`/
   `Ftilde`/`logSeriesAt` foundation they share — handled together as one upstreaming
   decision, rather than per-lemma?

**Next action:** user answers the questions (Q1 is gating: is the `PadicLFunctions`
development headed for mathlib at all?). Re-run `/mathlibable PadicLFunctions.MeasureR.sum_seriesEval_Ftilde`
if the upstreaming decision flips the framing. Likely outcomes:
- *Permanently project-local* → drop from mathlib consideration; the decl is fine
  as-is (a deliberate, sorry-free proof decomposition, T616).
- *Upstream the development* → this lemma becomes `private`/inlined supporting
  machinery; the real mathlibable work is the foundational
  `padicLog`/`extLog`/`seriesEval`/`logSeriesAt` layer (batch-assess those first,
  shared with the ζ_p siblings) and the named RJW Theorem 6.1(ii) (Leopoldt's formula).

---

## Next step

User answers the five numbered questions (Q1 is gating: is the `PadicLFunctions`
development headed for mathlib at all?). If the answer reframes the verdict, re-run
`/mathlibable PadicLFunctions.MeasureR.sum_seriesEval_Ftilde`. Absent upstreaming,
this decl is correctly project-internal as-is; under upstreaming, assess the
foundational `padicLog`/`extLog`/`seriesEval`/`logSeriesAt` layer first (shared with
the ζ_p-residue siblings) and keep this φ∘ψ-trace step private to the
Leopoldt-formula (RJW Theorem 6.1(ii)) proof.
