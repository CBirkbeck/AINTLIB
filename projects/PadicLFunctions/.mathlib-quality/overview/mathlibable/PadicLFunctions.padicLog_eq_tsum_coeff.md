# `/mathlibable` report — `PadicLFunctions.padicLog_eq_tsum_coeff`

Mode A, full 10-phase workflow, exhaustive 9-channel literature search.

**Final verdict: `BORDERLINE-needs-human`**

The decisive finding: this is a **bridge lemma** — `padicLog` is *defined* in the project as one
`tsum` (with `(n+1)⁻¹` denominators, re-indexed `k = n+1`), and this theorem re-expresses that same
analytic value as the `tsum` of mathlib's *formal* `PowerSeries.log` coefficients evaluated at
`x − 1`. Its entire purpose is to glue the project's bespoke `padicLog` def to mathlib's
`PowerSeries.log`, so the inversion proofs (`padicExp_padicLog`, `padicLog_padicExp`) can run formal
power-series composition. Mathlib has **no** p-adic / nonarchimedean logarithm at all, and **no**
generic "convergent evaluation of `PowerSeries.log` = its `tsum`-of-coefficients" bridge; the only
log series in mathlib is the *complex* `Complex.logTaylor`. So Phase 5 is a clean miss, and Phase 6
is NOT-COMPOSABLE. The literature confirms the *content* is utterly standard (the p-adic log is
universally *defined* as this evaluation) — but standard as a **definition**, not as a theorem
bridging two formulations. That, plus the shared `InExpBall` hypothesis, lands this on exactly the
**same two interacting human judgment calls** that made the sibling `summable_padicLog_terms`
BORDERLINE: (1) whether the mathlib-worthy statement should weaken `InExpBall p (x − 1)` to the
literature-standard `‖x − 1‖ < 1`, and (2) whether the whole `padicLog` development is being
upstreamed as a unit (this bridge lemma is internal scaffolding of that development, not a
standalone contribution). Two genuinely-fitting buckets (`NO-composable-from-mathlib` once the
`padicLog`/`PowerSeries.log` def-layer exists upstream, vs `YES-but-generalise-first`/`YES-add-as-is`
as part of the upstreamed development) cannot be silently picked between — so per the skill's "never
silently pick" rule the honest verdict is `BORDERLINE-needs-human`, with the questions spelled out.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per the task BUILD NOTE — `lake build` is stale/slow here; the declaration and its full dependency chain — `padicLog`, `InExpBall`, `summable_padicLog_terms`, `padicLog_term_eq`, and mathlib's `PowerSeries.log`/`coeff_log` — were read directly from source, exactly as the skill's Phase-0 fallback allows).
- decl `PadicLFunctions.padicLog_eq_tsum_coeff`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:884`
- kind:                      theorem
- has sorry:                 no (complete `by`-proof; depends only on already-proven project lemmas — `summable_padicLog_terms`, `padicLog_term_eq` — plus mathlib's `PowerSeries.coeff_log`, `summable_nat_add_iff`, `Summable.tsum_eq_zero_add`, `tsum_congr`)
- module docstring summary:  *The p-adic exponential and logarithm (RJW Lem 5.14)* — `exp(x)=∑xⁿ/n!` converges and is an isometry on the open ball `‖x‖ < p^{−1/(p−1)}`; `log(1+y)=∑(−1)^{n+1}yⁿ/n` converges for `‖y‖<1` and inverts `exp` on the matched balls (Cassels §12 / Washington §5.1). This theorem (decomposition cluster R5.E, node E4) is the **representation bridge**: it identifies the analytic `padicLog` with the evaluation of the *formal* `PowerSeries.log`.

---

### Statement (Phase 1)

`padicLog_eq_tsum_coeff` is a **theorem** stating the following:

> Let `L` be a complete nonarchimedean (ultrametric) normed field that is a normed `ℚ_p`-algebra.
> For `x` with `x − 1` in the exponential convergence ball (`‖x − 1‖^{p−1} < p⁻¹`), the `p`-adic
> logarithm `log x` equals the evaluation, at the point `x − 1`, of the *formal* power series
> `PowerSeries.log` over `ℚ_p`:  `log x = ∑_{n≥0} [Xⁿ](log) · (x − 1)ⁿ`, where `[Xⁿ](log)` is the
> `n`-th coefficient of `PowerSeries.log ℚ_[p]` (which is `0` at `n = 0` and `(−1)^{n+1}/n` for `n ≥ 1`).

In one sentence: the analytic `p`-adic logarithm **is** the value of the formal logarithmic power
series evaluated at `x − 1` — termwise, the "abstract Bourbaki principle" that *the same identities
hold for the formal series, hence for the function it defines* (the exact phrasing surfaced by the
literature search).

This is a **bridge / representation** statement, not a convergence or arithmetic statement. The
left side `padicLog p x` is *itself defined* as a `tsum` (`PadicExp.lean:384`,
`∑' n, (−1)ⁿ · (n+1)⁻¹ • (x−1)^{n+1}`, the re-indexed `k = n+1` form with explicit `(n+1)⁻¹`
scalars). The right side is the `tsum` of `(coeff n (PowerSeries.log ℚ_[p]) : ℚ_[p]) • (x−1)ⁿ`. The
theorem says these two `tsum`s agree.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime.
- `L : Type*`, `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — a
  complete ultrametric normed `ℚ_p`-algebra field (the general nonarchimedean setting: subsumes `ℚ_[p]`,
  `ℂ_p`, finite/algebraic extensions of `ℚ_[p]`).

Hypotheses (Lean side):
- `hx : InExpBall p (x − 1)` — i.e. `‖x − 1‖^{p−1} < p⁻¹`, the rpow-free spelling of
  `‖x − 1‖ < p^{−1/(p−1)}`, the **exponential** ball. **Strictly smaller** than the logarithm's
  natural convergence domain `‖x − 1‖ < 1`. It is needed here only to invoke
  `summable_padicLog_terms` (which is itself stated on the exp ball — see the sibling report).

Conclusion (math): `log x = ∑_{n≥0} [Xⁿ](formal log) · (x − 1)ⁿ`.

Conclusion (Lean): `padicLog p x = ∑' n : ℕ, (coeff n (PowerSeries.log ℚ_[p]) : ℚ_[p]) • (x - 1) ^ n`.

**Proof shape (read from source, lines 884–893).** (i) `hsum0`: the family
`n ↦ [X^{n+1}](log)·(x−1)^{n+1}` is summable, obtained from `summable_padicLog_terms p hx` via
`.congr` along the per-term identity `padicLog_term_eq` (`PadicExp.lean:869`, which matches
`(−1)ⁿ(n+1)⁻¹•(x−1)^{n+1}` to `[X^{n+1}](log)•(x−1)^{n+1}` using mathlib's `coeff_log`). (ii) `hsum`:
re-index back to start at `0` via `(summable_nat_add_iff 1).mp` (the `n = 0` term vanishes since
`[X⁰](log) = 0`). (iii) Unfold `padicLog`, peel the zeroth term with `hsum.tsum_eq_zero_add`,
`coeff_log`, `if_pos rfl`, `zero_smul`, `zero_add`, and finish with `tsum_congr` + `padicLog_term_eq`.
So the proof is a `tsum` re-indexing + termwise rewrite — pure bridge bookkeeping on top of the
already-proven `summable_padicLog_terms` and the mathlib coefficient formula `coeff_log`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (with a BIG caveat)
Reason: as a *declaration* it is a representation/bridge lemma (decomposition node E4), not a
`def`/structure and not a named theorem. **However**, the object it is *about* is BIG: the project's
`p`-adic logarithm `padicLog` (`PadicExp.lean:384`), a named mathematical object **absent from
mathlib**, and mathlib's formal `PowerSeries.log`. The lemma's mathlib fate is therefore governed by
the BIG `padicLog` upstreaming decision — exactly as for the sibling `summable_padicLog_terms`.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only and does
not gate which channels Phase 3 ran.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-liner check **n/a** (one-line note). The
body is a multi-step `by`-proof (a `tsum` re-index + termwise congruence), not a one-line `:= rfl`.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | p-adic logarithm equals sum of formal power-series log coefficients, `log(1+x)=∑(−1)^{n+1}xⁿ/n` evaluation | yes  | `log(1+X)=∑((−1)^{j+1}/j)Xʲ`; evaluate the formal series wherever it converges; `\|xⁿ/n\|_p ≤ λⁿ p^{v_p(n)}→0` | MIT 18.785 PS10; K. Conrad "Infinite series in p-adic fields"; Wikipedia "p-adic exponential function". The p-adic log **is defined as** this evaluation. |
|  2 | WebSearch (general / formal-vs-analytic) | p-adic log as evaluation of formal power series; identity power series log substituted `x−1`, nonarchimedean | yes  | "the same identities hold for the **formal power series**, hence for the **p-adic functions they define**" — the value = sum of formal coeffs × powers, valid where it converges | arXiv 1502.04607 ("Some aspects of analysis related to p-adic numbers"); Koblitz; Cambridge `jat58/all.pdf`. This is **verbatim the content of the target**, stated as the standard definitional principle. |
|  3 | WebSearch (named-after / Koblitz–Washington) | p-adic log/exp formal power series coefficients termwise; Koblitz, Washington *Intro to Cyclotomic Fields* | yes  | identical formal-series definition; Koblitz §IV and Washington §5.1 are the canonical references (the module cites Washington §5.1 + Cassels §12 + RJW Lem 5.14) | Koblitz ENS notes; Washington *Introduction to Cyclotomic Fields*; confirms the project's own cited sources. The identity is a textbook fact, never stated as a *named* lemma. |
|  4 | ChatGPT MCP                      | (intended: "Is the p-adic log standardly stated as the *evaluation of the formal log power series*, and is the 'function = tsum of formal coefficients' identity a definition or a theorem? Any historical evolution?") | n/a  | —                                | A `chatgpt-math` MCP server is *listed* in `~/.claude.json` but is **not exposed as a callable tool** in this worker environment (no `mcp__chatgpt*` tool resolves via ToolSearch; `/setup-chatgpt` server not live here). Recorded n/a — WebSearch (3 queries at three generality levels) + nLab + the module's own citations (RJW, Cassels §12, Washington §5.1, Koblitz) fully cover the standard-form question; sources are unanimous. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                | n/a  | (no references dir; no `refs/` symlink) | both directories **absent** on this machine (`.mathlib-quality/references/` does not exist; `refs/PadicLFunctions/` not symlinked). Recorded n/a. The module docstring's inline citations serve as the literature anchor. |
|  6 | nLab                             | power series: convergent sum = formal coefficients; analytic function determined by its formal series   | yes  | nLab "power series": a power series is `∑ aₙXⁿ`; **"if a function can be expressed by a convergent power series, the coefficients are determined by the function"**; where `∑aᵢzⁱ` converges absolutely it "defines a function on this set" | `ncatlab.org/nlab/show/power+series`. Confirms (generically, over any complete valued field) the value↔formal-coefficient correspondence that the target instantiates for the p-adic log. Not stated as a *named* bridge theorem — it is the definitional setup. |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                | not a categorical concept (a concrete `tsum`-equals-formal-series identity for the p-adic log over a normed field). The relevant nLab content is the "power series" page already covered in #6. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                | not an algebraic-geometry concept (analytic evaluation of a series, not scheme/sheaf theory). |
|  9 | MathOverflow / Math.StackExchange| convergent power-series evaluation = sum of formal coefficients; nonarchimedean; `tsum` well-defined    | partial | community treatments match #1–#3: over a nonarchimedean field a series converges iff terms→0, and one *evaluates* the formal log series where it converges; the value-equals-formal-coefficient-sum is taken as the definition | recurring Q&A on p-adic log; the formal-vs-analytic identity is textbook and never disputed (no single canonical MO thread; consistent across many). |
| 10 | recent arXiv (last 5 years)      | p-adic logarithm power-series evaluation, formal series coefficients, termwise convergence (2021–2025)   | partial | arXiv 2106.09315 ("Fast evaluation of p-adic transcendental functions"), 1907.06437 (2-adic log on principal units), 2207.03979 (analytic Nullstellensätze for formal *and convergent* p-adic power series) all **reuse** the classical "log = evaluation of the formal log series on `‖x−1‖<1`"; none reformulates it | confirms no modern reformulation supersedes the classical formal-series definition of the p-adic log. |

The protocol passed: WebSearch ran **3** distinct queries at three generality levels (the specific
log-coefficient-evaluation form / the general formal-vs-analytic "same identities hold for the formal
series" principle / the named Koblitz–Washington textbook references); ChatGPT MCP recorded n/a with
reason (server listed but not a live callable tool here); local references recorded n/a with reason
(no dir); nLab checked (the "power series" page, which gives the generic value↔formal-coefficient
correspondence); nCatLab / Stacks recorded n/a with reason; MathOverflow and recent arXiv each checked.

### Literature summary (Phase 3)

Concept identified as: **the representation of the `p`-adic logarithm as the evaluation of the formal
logarithmic power series** `log(1+X) = ∑_{k≥1} (−1)^{k+1} Xᵏ/k` at the point `x − 1` — i.e. the
formal-series ⇒ analytic-function correspondence specialised to `log_p`.

Sources agree on the standard form: **yes, unanimously — but as a *definition*, not a theorem.** Every
source (K. Conrad, Koblitz, Washington §5.1, MIT 18.785, nLab) *defines* the p-adic logarithm as the
evaluation of the formal log series wherever it converges; the identity "`log x = ∑ [Xⁿ](log)·(x−1)ⁿ`"
is the **defining equation**, taken for granted, not isolated as a named lemma. arXiv 1502.04607
states the underlying principle verbatim: "the same identities hold for the formal power series, hence
for the p-adic functions they define."

Most general standard form: over **any complete nonarchimedean field extending `ℚ_p`**, for
`‖x − 1‖ < 1` (the **full open unit ball**), `log x = ∑_{n} [Xⁿ](log)·(x−1)ⁿ`. The project's `L` is
exactly this maximal *field* setting — but the project's **hypothesis** is `InExpBall p (x − 1)`
(`‖x−1‖^{p−1} < p⁻¹`, the **exponential** ball), which is **strictly smaller** than the literature's
`‖x − 1‖ < 1`.

Generality dimensions where the literature varies:
- **Underlying field**: `ℚ_p` → `ℂ_p` / arbitrary complete nonarchimedean extension. Most general =
  "any complete ultrametric normed `ℚ_p`-algebra field" — which the target already uses. ✓ maximal.
- **Convergence domain (the binding axis)**: literature radius is **`1`** (`‖x−1‖<1`); the target's
  hypothesis radius is **`p^{−1/(p−1)} < 1`** (the exp ball). → the target is **strictly narrower** here.
  (Same axis as the sibling `summable_padicLog_terms`.)
- **Status (definition vs theorem)**: in the literature this is the *definition* of `log_p`. In the
  project, `padicLog` is given a *different* (re-indexed, `(n+1)⁻¹`-explicit) `tsum` definition, and
  this theorem is the **bridge** proving the project def equals the formal-`PowerSeries.log` evaluation.
  The bridge only has content because the two `tsum` spellings differ syntactically.

Disagreement with the literature: none on the *content* (the identity is exactly the textbook
defining equation). Two structural mismatches: (a) the hypothesis is **strictly stronger** than the
literature standard (exp ball vs unit ball — the generalisation lever, Phase 4); (b) the literature
treats this as a *definition* whereas the project needs it as a *bridge theorem* between its own def
and mathlib's `PowerSeries.log` (the upstreaming/packaging lever, Phase 7).

---

### Generality analysis — `padicLog_eq_tsum_coeff`

Literature-standard form (from Phase 3): over any complete nonarchimedean field ⊇ `ℚ_p`,
`log x = ∑_{n} [Xⁿ](log)·(x−1)ⁿ` for **`‖x − 1‖ < 1`** (the full open unit ball).

| # | Parameter / hypothesis                | Current Lean form          | Literature-standard form     | Weaker form exists? | Reason it can/can't be weakened |
|---|---------------------------------------|----------------------------|------------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L]`                     | normed field               | complete nonarch field ⊇ ℚ_p | NO                  | the `(n+1)⁻¹`/coefficient scalars and the norm need a field; matches the standard setting |
| 2 | `[NormedAlgebra ℚ_[p] L]`             | normed ℚ_p-algebra          | extension of ℚ_p             | NO (essentially)    | `coeff n (PowerSeries.log ℚ_[p])` lives in `ℚ_p` and is pushed into `L` via the algebra map; the algebra structure is what makes the bridge typecheck |
| 3 | `[IsUltrametricDist L]`               | ultrametric norm            | nonarchimedean field         | NO                  | inherited via `summable_padicLog_terms`, whose nonarchimedean Σ⇔→0 proof needs the ultrametric inequality |
| 4 | `[CompleteSpace L]`                   | complete                   | complete                     | NO                  | both `tsum`s are meaningful only with completeness; inherited from the summability dependency |
| 5 | **`hx : InExpBall p (x − 1)` (`‖x−1‖^{p−1} < p⁻¹`, radius `p^{−1/(p−1)}`)** | **exponential** ball | **`‖x − 1‖ < 1`** (unit ball, radius 1) | **YES** | **The binding weakening — but it is *inherited*, not intrinsic.** The bridge itself is a pure `tsum` re-index + termwise rewrite (`padicLog_term_eq`, valid for *every* `n` with no ball constraint); the *only* place `hx` enters is to invoke `summable_padicLog_terms p hx`. So this lemma is narrow *exactly because* `summable_padicLog_terms` is narrow. Once summability is available on the full `‖x−1‖<1` ball (the sibling's Phase-4b generalisation, ingredients already in mathlib — `padicValNat_le_nat_log` etc.), this bridge generalises to `‖x−1‖<1` for **free** (CHEAP — `hx` just routes to the more-general summability lemma). |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD.**
Number of weakening opportunities found: **1** (the convergence-domain hypothesis, row 5) — and it is
an **inherited** narrowing, not intrinsic to the bridge.

Proposed restatement (weaken `InExpBall p (x − 1)` → `‖x − 1‖ < 1`):

```lean
theorem padicLog_eq_tsum_coeff' {x : L} (hx : ‖x - 1‖ < 1) :
    padicLog p x = ∑' n : ℕ, (coeff n (PowerSeries.log ℚ_[p]) : ℚ_[p]) • (x - 1) ^ n := by
  sorry -- identical proof, BUT the `summable_padicLog_terms p hx` call must be replaced by the
        -- full-unit-ball summability lemma (the sibling's Phase-4b `summable_logSeries_terms`,
        -- re-proved with the polynomial×geometric majorant via `padicValNat_le_nat_log`).
        -- The re-index + `padicLog_term_eq` termwise rewrite are unchanged.
```

Cost of restatement: **CHEAP for this bridge in isolation** — the bridge's own proof is unchanged; it
only swaps which summability lemma it calls. **But the prerequisite is the sibling's MODERATE
re-proof** of summability on `‖x−1‖<1`. So the *effective* cost is gated on generalising
`summable_padicLog_terms` first — i.e. this lemma's generalisation is downstream of (and contingent
on) the sibling's. This is precisely why the two share one mathlib fate.

→ Phase 7 considers `YES-but-generalise-first` (STRICTLY NARROWER, inherited from the summability
sibling), tensioned against the `BORDERLINE` scope/packaging question (the upstream-the-whole-
`padicLog`-development decision) and the bridge's NOT-COMPOSABLE-yet-internal-scaffolding nature.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                        | no       | — | hypotheses are already typeclasses; nothing to bundle |
|  2 | sequences/metric → filters/nets/topological?                                                              | no       | — | `tsum`/`Summable` is already the filter-free idiomatic packaging; no sequence to filter-ise |
|  3 | construct an object → universal-property class?                                                           | no       | — | this is an identity between two `tsum`s, not a construction |
|  4 | set-with-closure-predicate → bundled substructure?                                                        | no       | — | n/a |
|  5 | field-specific → weaken typeclass hierarchy / **use a `FormalMultilinearSeries.radius`/analytic-eval idiom (cf. mathlib's `NormedSpace.exp_eq_tsum`)?** | **partial** | the cleanest mathlib idiom would be a **generic "analytic evaluation of `PowerSeries.log` on its nonarchimedean radius-of-convergence ball = `∑ coeff·xⁿ`" lemma**, mirroring the *archimedean* `NormedSpace.exp_eq_tsum` (`Analysis/Normed/Algebra/Exponential.lean:163`). **Blocked today**: mathlib has no nonarchimedean `PowerSeries`-evaluation / log-radius machinery (its analytic-eval API — `HasFPowerSeriesOnBall`, `FormalMultilinearSeries.coeff_ofScalars`, `Complex.logTaylor` — is archimedean; `PowerSeries.log` is purely formal with no convergence). | once a nonarchimedean `PowerSeries`→analytic-eval bridge exists upstream, this lemma would become a one-line specialisation; same def-layer modernisation lever flagged for the sibling |
|  6 | 1-categorical → higher-categorical?                                                                       | no       | — | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive structure?                                                     | no       | — | the index `n : ℕ` is intrinsic to the power-series exponent |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for the signature as a standalone statement; the genuine
generalisation lever is the **domain weakening** of Phase 4b, not a categorical recast).

The mathlib-idiomatic ideal — a generic *nonarchimedean analytic-evaluation* lemma
`PowerSeries.log`-value `= ∑ coeff·xⁿ` on the convergence ball, mirroring the archimedean
`NormedSpace.exp_eq_tsum` — is a **real** organisational improvement (it would subsume both this log
bridge and the sibling `padicExp_eq_tsum_coeff` under one nonarchimedean evaluation API), but it
lives **one layer down** and is **infeasible today**: mathlib has no nonarchimedean power-series
convergence/evaluation theory. `NormedSpace.exp_eq_tsum` exists only for the archimedean
`NormedSpace.exp`, and there is no `log` analogue at all. One-line reason this lemma is not itself a
modernisation move: it is a concrete bridge between two already-idiomatic `tsum`s; the modernisation
target is the missing **def-layer** (a nonarchimedean `PowerSeries`-evaluation framework), which is a
separate, large, currently-nonexistent mathlib development.

---

### Diamond / defeq risk — `padicLog_eq_tsum_coeff`

**n/a — declaration kind is `theorem`.** (Phase 4.5 runs only for `def`/`class`/`instance`. This
theorem introduces no definitional equalities or typeclass-search paths.)

---

### Mathlib search-status: `padicLog_eq_tsum_coeff`

[A] Lean-Finder       "p-adic logarithm equals tsum of formal log coefficients", "padicLog = sum coeff PowerSeries.log"   n/a: Lean-Finder web UI not callable in this worker environment — substituted with exhaustive grep over the mathlib tree (method D) for every candidate name/shape, plus reading the candidate decls' actual statements.
[B] Loogle            `padicLog _ _ = tsum _`, `_ = ∑' n, (PowerSeries.coeff n (PowerSeries.log _)) • _ ^ n`, `_ → _ = ∑' n, _ • _ ^ n` (log-coeff shape)   **no p-adic hit** — grep for `padicLog p x =` and `coeff … log … smul … tsum` over `.lake/packages/mathlib/Mathlib/` returns empty. Mathlib has **no** p-adic logarithm and no `tsum`-of-`PowerSeries.log`-coefficients identity in any namespace.
[C] LeanSearch        "p-adic logarithm equals evaluation of formal log power series", "convergent power series equals sum of formal coefficients nonarchimedean"   no direct hit: surfaces the **complex** `Complex.logTaylor` / `hasSum_taylorSeries_log` family and the **archimedean** `NormedSpace.exp_eq_tsum`; nothing nonarchimedean / p-adic, and no `PowerSeries.log`-evaluation bridge.
[D] Grep mathlib src  `grep -rniE "padicLog|tsum.*coeff|coeff.*tsum|PowerSeries.*HasSum|subst.*tsum"` over `.lake/packages/mathlib/Mathlib/`   **NO** p-adic logarithm anywhere; **no** generic "`PowerSeries` value = `tsum` of its coefficients" bridge. Found instead the **building blocks**: mathlib's *formal* `PowerSeries.log` + `PowerSeries.coeff_log` (`RingTheory/PowerSeries/Log.lean:42,48`); the *archimedean analogue* `NormedSpace.exp_eq_tsum` (`Analysis/Normed/Algebra/Exponential.lean:163`); `Summable.tsum_eq_zero_add`, `summable_nat_add_iff`, `tsum_congr` (the `tsum`-manipulation API the proof uses). Also `Mathlib.RingTheory.PowerSeries.Substitution` (formal substitution — purely algebraic, no convergence/evaluation). |
[E] Name pattern      `padicLog`, `log_eq_tsum`, `eval_log`, `PowerSeries.log_eval`, `tsum_coeff_log`, `InExpBall`   `padicLog`/`InExpBall` do not exist in mathlib. The only `*_eq_tsum` evaluation lemma of this shape is `NormedSpace.exp_eq_tsum` (archimedean exp). `Complex.logTaylor` (`Analysis/SpecialFunctions/Complex/LogBounds.lean`) is the complex Taylor polynomial of `log(1+z)` — archimedean, finite-truncation, **not** a nonarchimedean `tsum` identity.

Searched for both:
- the user's current form (`padicLog p x = ∑' n, (coeff n (PowerSeries.log ℚ_[p])) • (x−1)ⁿ` on the
  exp ball) — **not** in mathlib.
- the **literature-standard / more-general** form (the same identity on the **full unit ball**
  `‖x−1‖<1`, and the generic "convergent `PowerSeries` evaluation = `tsum` of its coefficients"
  bridge) — also **not** in mathlib. The general-form search is important precisely because mathlib
  often has the general form; here it has **neither** form for the logarithm — the only analytic
  `*_eq_tsum` bridge is the *archimedean* `NormedSpace.exp_eq_tsum`, and the only log series is the
  *complex* `Complex.logTaylor`.

Concluded: **not in mathlib (all 5 methods exhausted, plus the literature-standard `‖x−1‖<1` form and
the generic-evaluation form).** Mathlib has the *ingredients* (the formal `PowerSeries.log` +
`coeff_log`; the archimedean evaluation precedent `NormedSpace.exp_eq_tsum`; the `tsum`-manipulation
API), but **no** p-adic logarithm and **no** `PowerSeries.log`-evaluation/`tsum`-bridge in any form.

---

### Call sites — `padicLog_eq_tsum_coeff`

Internal use count: **2** (both within the declaring file `PadicExp.lean`, in theorems *other than*
the declaring one — the skill's grep convention counts uses outside the declaring theorem)
External-to-file callers: **0 distinct files**

| Caller file:line               | Usage pattern (one-line excerpt)                                              |
|--------------------------------|-------------------------------------------------------------------------------|
| PadicExp.lean:941              | `rw [padicExp_eq_tsum_coeff, padicLog_eq_tsum_coeff p hx, …]` — inside **`padicExp_padicLog`** (the inversion `exp(log x) = x` on the matched balls, E4); rewrites both sides to formal-coefficient `tsum`s so ultrametric-Fubini series composition (`tsum_coeff_pow_eq_coeff_subst`) applies |
| PadicExp.lean:965              | `rw [padicLog_eq_tsum_coeff p hb, ← tsum_coeff_exp_sub_one p x hx, …]` — inside **`padicLog_padicExp`** (the inversion `log(exp x) = x`, E4); same role — moves `padicLog` into formal-`PowerSeries.log` form for the composition argument |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `padicLog_eq_tsum_coeff`?):
  - (none) — the only two places the `padicLog`-as-formal-`PowerSeries.log`-evaluation form is needed
    are the two inversion proofs above, and both route through this lemma. No competing inline
    `tsum`-bridge derivation exists. The downstream full-unit-ball log identities
    (`ValuesAtOne.lean`: `padicLog_mul_of_norm_lt_one`, `padicLog_pow_*`) work from the *isometry* and
    multiplicativity, not from re-expanding the formal-coefficient `tsum`, so they do not bypass this.

What the call-sites pattern tells you: **K = 2 internal uses, no external file, no inline
re-derivation.** Per the Phase-6 signal table this sits between "K = 1 (possibly wrong abstraction)"
and "K ≥ 3 (real API)": it is **genuinely used** (not dead code, never bypassed), but its reuse is
**narrow and single-purpose** — it exists specifically to feed the two inversion proofs by converting
`padicLog` into the formal-`PowerSeries.log` representation that the series-composition machinery
(`tsum_coeff_pow_eq_coeff_subst`) consumes. It is **internal scaffolding of the inversion argument**,
not a broadly-reused public fact. This is a weaker reuse signal than the sibling's K=3, and it
reinforces that the lemma's value is *as part of the `padicLog` development*, not standalone.

---

### Composition check (Phase 6)

Can `padicLog_eq_tsum_coeff` be derived from mathlib in ≤3 chained calls?

Attempt 1: a mathlib "p-adic log = `tsum` of formal log coefficients" lemma applied directly.
  - Mathlib decls used: (none exist).
  - Result: **fails** — Phase 5 found mathlib has **no** p-adic logarithm and **no**
    `PowerSeries.log`-evaluation/`tsum`-bridge in any form. The only `*_eq_tsum` analytic bridge,
    `NormedSpace.exp_eq_tsum`, is archimedean-exp-specific and inapplicable.

Attempt 2: re-index a known summable family + termwise coefficient rewrite via `coeff_log`.
  - Mathlib decls used: `summable_nat_add_iff` + `Summable.tsum_eq_zero_add` + `tsum_congr` +
    `PowerSeries.coeff_log` — **on top of the project-local `summable_padicLog_terms` and
    `padicLog_term_eq`**.
  - Result: **this is essentially the project's actual proof**, and it is **not** a ≤3-call
    composition. It requires (i) building `hsum0` by `.congr`-ing `summable_padicLog_terms` along
    `padicLog_term_eq`, (ii) re-indexing via `(summable_nat_add_iff 1).mp`, (iii) unfolding
    `padicLog` and peeling the zeroth term with `tsum_eq_zero_add` + `coeff_log` + `if_pos` +
    `zero_smul`, (iv) a final `tsum_congr` with `padicLog_term_eq`. That is a genuine multi-step
    `tsum`-manipulation proof, and crucially it **depends on two project-local lemmas** that are
    themselves not in mathlib (`summable_padicLog_terms` is itself BORDERLINE; `padicLog_term_eq` is
    the per-term coefficient match). It is not a composition of *mathlib* primitives.

Conclusion: **NOT-COMPOSABLE** *from mathlib as it stands today*. Mathlib has the `tsum`-manipulation
API and the formal `coeff_log`, but the proof is a real multi-step argument that **routes through
project-local, not-in-mathlib lemmas** (`summable_padicLog_terms`, `padicLog_term_eq`) and through
the project-local **def** `padicLog`. **Caveat that drives the verdict:** *if* the `padicLog` /
`PowerSeries.log`-evaluation def-layer were upstreamed (so `padicLog` and a nonarchimedean evaluation
API exist in mathlib), this bridge would likely *become* a short composition — i.e. its
NOT-COMPOSABLE status is **contingent on the missing def-layer**, exactly the BORDERLINE pivot.

---

## Verdict: `padicLog_eq_tsum_coeff`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the target is the **standard formal-series representation of the
  p-adic logarithm** (`log x = ∑ [Xⁿ](log)·(x−1)ⁿ`) — but in the literature this is the *defining
  equation* of `log_p` (Koblitz, Washington §5.1, K. Conrad, nLab: "the same identities hold for the
  formal power series, hence for the functions they define"), not a named bridge theorem. The
  literature-standard convergence domain is the **full open unit ball `‖x−1‖<1`** (radius 1), strictly
  larger than the **exp ball** this lemma uses (inherited from `summable_padicLog_terms`).
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — exactly one weakening (row 5),
  `InExpBall p (x−1)` → `‖x−1‖ < 1`, and it is **inherited** (the bridge's own proof is ball-free; `hx`
  only routes to `summable_padicLog_terms`). Cost CHEAP for the bridge itself, **but contingent** on
  the sibling summability lemma's MODERATE generalisation. Modern-idiom (4c): the genuine improvement
  (a nonarchimedean analogue of `NormedSpace.exp_eq_tsum`) is a missing **def-layer** development, not
  a recast of this lemma.
- Mathlib search (Phase 5): **not in mathlib** in any form — no p-adic logarithm; no
  `PowerSeries.log`-evaluation/`tsum`-bridge; the only analytic `*_eq_tsum` is the archimedean
  `NormedSpace.exp_eq_tsum`, and the only log series is the complex `Complex.logTaylor`. Building
  blocks (`PowerSeries.coeff_log`, `summable_nat_add_iff`, `Summable.tsum_eq_zero_add`, `tsum_congr`,
  and the archimedean precedent) **are** mathlib.
- Composition check (Phase 6): **NOT-COMPOSABLE** *from mathlib today* — a genuine multi-step
  `tsum`-manipulation that routes through the project-local, not-in-mathlib `summable_padicLog_terms`,
  `padicLog_term_eq`, and the def `padicLog`. Status is **contingent on the missing def-layer**. Call
  sites: **K=2 internal, no external, no inline re-derivation** — genuine but narrow single-purpose
  scaffolding for the two inversion proofs.

**Rationale (why BORDERLINE — and not a clean YES-but-generalise-first, nor a NO):**

This is a *true, genuinely-missing-from-mathlib* representation lemma for the p-adic logarithm, proved
sorry-free, with real (K=2) but narrow reuse. Phases 5 and 6 push *away* from the NO buckets **as
mathlib stands today**: it is **not** NO-mathlib-has-it (mathlib has no p-adic log and no
`PowerSeries.log`-evaluation bridge in either ball form — Phase 5; the only `*_eq_tsum` is archimedean
exp), and it is **not** cleanly NO-composable *right now* (the proof is a real multi-step argument that
depends on project-local lemmas and the project-local `padicLog` def — Phase 6). So the live choice is
between a YES bucket (as part of an upstreamed `padicLog` development) and BORDERLINE, and per the
skill's "never silently pick between fitting buckets" rule the decision turns on the **same two
interacting human judgment calls that governed the sibling `summable_padicLog_terms`** — which this
lemma inherits almost verbatim, plus one bridge-specific subtlety:

1. **The generalisation (`InExpBall → ‖x−1‖<1`) is inherited, not intrinsic, and is downstream of the
   summability sibling.** Phase 4b is unambiguous that the literature statement is the full-unit-ball
   one (radius 1). But this bridge is narrow *only because* it calls `summable_padicLog_terms` (which is
   itself narrow); the re-index + `padicLog_term_eq` rewrite hold on the whole ball with no change.
   So "generalise this bridge to `‖x−1‖<1`" is **free once the summability lemma is generalised first**
   — it cannot be decided independently of the sibling. Whether to take the unit-ball form here is the
   *same* packaging decision as for `summable_padicLog_terms`, not a separate one.

2. **It cannot be PR'd standalone — it is a bridge between a `padicLog` def mathlib does not have and a
   formal `PowerSeries.log`, used only inside the inversion proofs.** Its two consumers are
   `padicExp_padicLog` and `padicLog_padicExp` (the E4 inversions). Mathlib has **no** p-adic /
   nonarchimedean logarithm. So upstreaming this lemma sensibly means upstreaming the **BIG, multi-decl
   nonarchimedean exp/log development** (`padicExp`, `padicLog`, their summability, the isometry,
   multiplicativity, and the inversions) — and this bridge is internal scaffolding of the inversion
   argument within that development, not a standalone contribution. This is the **same governing
   decision** flagged for `summable_padicLog_terms`, `summable_padicExp_terms`, and the
   `norm_padicExp_*` family; they share one mathlib fate.

3. **Bridge-specific pivot (the contingency):** Phase 6's NOT-COMPOSABLE status is itself *contingent
   on the missing def-layer*. If the `padicLog`/`PowerSeries.log`-nonarchimedean-evaluation layer were
   upstreamed (especially as the Phase-4c modern idiom — a nonarchimedean analogue of
   `NormedSpace.exp_eq_tsum`), this lemma would plausibly **collapse to a short composition or a
   one-line specialisation** of that generic evaluation API — i.e. flip toward
   `NO-composable-from-mathlib`. Whether mathlib should have the generic evaluation lemma (under which
   this becomes a corollary) or this specific log bridge (as a named development lemma) is a
   design/taste call the search cannot make.

The CHEAP/MODERATE generalisation cost is **not** invoked as the reason for BORDERLINE (the skill
forbids cost-as-verdict-driver outside BORDERLINE, and an inherited re-proof would still be worth
doing — mathlib's value is the right form). The genuine blocker is the cluster of *interacting
scope/packaging/def-layer judgments* in (1)+(2)+(3), which the skill must defer. The K=2 narrow-but-
genuine reuse confirms the lemma is load-bearing scaffolding within the project's inversion argument
but does not settle its mathlib form or its standalone upstreamability.

**Numbered questions (≤5):**

1. **Scope (governs everything):** do you intend to upstream the project's `p`-adic / nonarchimedean
   **exp/log development** to mathlib as a unit — `padicExp`, `padicLog`, their summability, the
   isometry, multiplicativity, and the inversions `padicExp_padicLog`/`padicLog_padicExp`? This bridge
   lemma is internal scaffolding of the inversion argument and should travel *with* that development,
   not alone. (No → go to Q5.)
2. **Def-layer / modern idiom:** would you prefer mathlib to gain a **generic nonarchimedean
   power-series-evaluation lemma** — `PowerSeries`-value `= ∑ coeff·xⁿ` on the convergence ball,
   mirroring the *archimedean* `NormedSpace.exp_eq_tsum` — under which both this log bridge **and** the
   sibling `padicExp_eq_tsum_coeff` become one-line corollaries? (Yes → this lemma is likely
   `NO-composable-from-mathlib`/a corollary once that layer exists; No, ship the bespoke log bridge as
   a named development lemma → go to Q3.)
3. **Generality (inherited):** the literature-standard domain is the **full open unit ball
   `‖x−1‖<1`** (radius 1), strictly larger than the exp ball this lemma uses — but this lemma is narrow
   *only because* `summable_padicLog_terms` is. Do you want the mathlib statement on `‖x−1‖<1` (which
   requires generalising the summability sibling **first**, then this bridge follows for free)? If yes,
   this and the summability sibling should be generalised together as one packaging decision.
4. **Sibling coupling:** confirm you want this lemma's verdict resolved **jointly** with
   `summable_padicLog_terms` (also BORDERLINE) and the exp siblings — they share the convergence-domain
   axis and the upstreaming decision, so resolving them independently risks inconsistent ball/packaging
   choices. (Yes → resolve as a batch.)
5. **Drop-from-consideration:** if you do **not** plan to upstream the p-adic exp/log machinery, then
   this lemma stays a (real, K=2) project-local bridge — correct as-is on the exp ball, scaffolding for
   the inversions — and should be dropped from mathlib consideration. Is that the case?

**Next action:** user answers the questions; re-run `/mathlibable padicLog_eq_tsum_coeff` — preferably
**together with** `/mathlibable PadicLFunctions.padicLog`, `/mathlibable
PadicLFunctions.summable_padicLog_terms`, `/mathlibable PadicLFunctions.padicExp_eq_tsum_coeff`, and
`/mathlibable PadicLFunctions.padicExp` — since this bridge's verdict is governed by (a) the BIG,
multi-decl upstreaming decision on the p-adic exp/log definitions it scaffolds, (b) the inherited
generality choice `InExpBall → ‖x−1‖<1` (downstream of the summability sibling), and (c) whether
mathlib gains the generic nonarchimedean evaluation idiom under which this becomes a corollary. Likely
resolutions:
  - "Upstream the development + add the generic nonarchimedean `PowerSeries`-evaluation lemma" → this
    bridge flips to **NO-composable-from-mathlib** (a one-line specialisation of the generic evaluation
    API, shipped as part of the development).
  - "Upstream the development, keep bespoke log bridges (no generic evaluation layer), stated at
    literature generality" → **YES-but-generalise-first** on `‖x−1‖<1` (generalise the summability
    sibling first; this bridge then follows for free), shipped within the multi-decl nonarchimedean
    exp/log PR series.
  - "Upstream verbatim, keep the project structure" → **YES-add-as-is** on the exp-ball form as a
    representation lemma of the development.
  - "Keep project-local" → drop from mathlib consideration; it stays the (correct, K=2) bridge
    scaffolding the project's inversion proofs.

---

## Next step

User answers the five numbered questions above; re-run `/mathlibable padicLog_eq_tsum_coeff` —
preferably alongside `/mathlibable PadicLFunctions.padicLog`, `/mathlibable
PadicLFunctions.summable_padicLog_terms`, `/mathlibable PadicLFunctions.padicExp_eq_tsum_coeff`, and
`/mathlibable PadicLFunctions.padicExp`, since this bridge lemma's verdict is governed by the BIG,
multi-decl upstreaming decision on the p-adic exp/log definitions it scaffolds, the inherited
convergence-domain generalisation (`InExpBall → ‖x−1‖<1`, downstream of the summability sibling), and
whether mathlib gains a generic nonarchimedean power-series-evaluation idiom (mirroring
`NormedSpace.exp_eq_tsum`) under which this lemma becomes a corollary — to resolve to
`NO-composable-from-mathlib` (corollary of a generic evaluation lemma), `YES-but-generalise-first`
(unit-ball form, with the summability sibling generalised first), `YES-add-as-is` (upstream the
project structure verbatim), or drop-from-consideration (keep project-local).
