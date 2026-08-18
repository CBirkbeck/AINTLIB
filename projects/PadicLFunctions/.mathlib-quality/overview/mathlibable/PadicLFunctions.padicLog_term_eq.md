# `/mathlibable` report — `PadicLFunctions.padicLog_term_eq`

**Final verdict: `NO-composable-from-mathlib`.** This is a project-internal
reindexing/glue lemma that bridges the hand-rolled `padicLog` `tsum` to the
`PowerSeries.log`-coefficient form. Its genuine content is a single-coefficient
arithmetic identity that mathlib's `coeff_log` discharges, wrapped in `smul`
bookkeeping; the surrounding `tsum` reindexing it feeds is exactly what
mathlib's `PowerSeries.aeval` / `aeval_eq_sum` already package. It is not a
standalone mathlib result. See the verdict section for the alternative reading
(BORDERLINE) and the explicit question this hinges on.

---

### Baseline (Phase 0)

- lake build:               build not re-run (stale/slow per task note); **reasoned from source** — Phase-0 fallback
- decl `PadicLFunctions.padicLog_term_eq`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:869`
- kind:                      theorem
- has sorry:                 no (proof at lines 872–880 is complete: `rw … congr 2 … ring`)
- module docstring summary:  the p-adic exponential and logarithm (RJW Lem 5.14); `exp`/`log` as evaluations of the formal `PowerSeries.exp`/`PowerSeries.log`, convergence and mutual inversion on the matched ball.

Section context (lines 31–33, 461–466): `variable (p : ℕ) [hp : Fact p.Prime]`,
`{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`;
the decl carries `omit [IsUltrametricDist L] [CompleteSpace L]` (line 867), so it
is a purely algebraic identity needing only `NormedAlgebra ℚ_[p] L` (in fact only
an `ℚ_[p]`-algebra structure on `L`).

---

### Statement (Phase 1)

`PadicLFunctions.padicLog_term_eq` is a **theorem** stating the following:

For an element `x` of a normed `ℚ_[p]`-algebra `L` and `n : ℕ`, the `n`-th term
of the hand-rolled `padicLog` series equals the `(n+1)`-th coefficient term of
mathlib's formal logarithm power series evaluated at `x − 1`:

$$(-1)^n \cdot \big((n+1)^{-1} \cdot (x-1)^{n+1}\big)
   \;=\; \big(\text{coeff}_{n+1}\,(\log \mathbb{Q}_p)\big)\cdot (x-1)^{n+1},$$

where `coeff (n+1) (PowerSeries.log ℚ_[p]) ∈ ℚ_[p]` acts on `(x−1)^{n+1} ∈ L`
by the scalar (`•`) action. In words: the project defines `padicLog x` as the
sum `∑ₙ (-1)^n · ((n+1)⁻¹ • (x−1)^{n+1})` (index from `0`, with the `(n+1)`
shift and the `(-1)^n` sign pulled out front), whereas the canonical
"evaluate `PowerSeries.log` at `x−1`" form is `∑ₙ coeff n (log) • (x−1)^n`.
This lemma is the **termwise dictionary** between the two encodings at the
shifted index.

Variables / typeclasses (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime; only used so `ℚ_[p]` exists.
- `{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]` — the ambient field; the
  norm/ultrametric/complete instances are `omit`-ted, so only the `ℚ_[p]`-algebra
  structure is used.
- `(x : L)` — the point; the series is in `(x − 1)`.
- `(n : ℕ)` — the term index (from `0`).

Hypotheses (Lean side): none beyond the typeclass parameters.

Conclusion (math): the `n`-th summand of the project's `padicLog` series equals
`coeff_{n+1}(log) • (x−1)^{n+1}`.

Conclusion (Lean):
`(-1 : L) ^ n * (((n : ℚ_[p]) + 1)⁻¹ • (x - 1) ^ (n + 1)) = (coeff (n + 1) (PowerSeries.log ℚ_[p]) : ℚ_[p]) • (x - 1) ^ (n + 1)`.

**Reduced mathematical content.** Cancelling the common `(x−1)^{n+1}` factor (and
moving the `(-1)^n` through `Algebra.smul_def`), the lemma is the scalar identity
in `ℚ_[p]`:
$$(-1)^n \cdot (n+1)^{-1} \;=\; \text{algebraMap}_{\mathbb{Q}\to\mathbb{Q}_p}\big((-1)^{(n+1)+1}/(n+1)\big),$$
i.e. `coeff_log` at `n+1` (which is `algebraMap ((-1)^{n+2}/(n+1))`) with
`(-1)^{n+2} = (-1)^n`. That is the entire substance; everything else is `smul`/
`algebraMap`/`map_*` plumbing closed by `ring`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper/glue lemma — a termwise reindexing identity feeding the
`tsum`-reindex in `padicLog_eq_tsum_coeff`; not a named theorem, not a new
structure, not listed as a `## Main results` headline (the headline results in
this file are `padicExp_padicLog`, `padicLog_padicExp`, the isometry, and the
`x^s` construction — this lemma is plumbing under them).

(Literature width is EXHAUSTIVE regardless. Recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~8 substantive proof lines (`rw`, `congr 2`, `push_cast`,
`ring`). Kind is **theorem**, not `def`/`abbrev`/`structure`.
One-liner verdict: **n/a (kind is theorem)** — the one-line check applies to
definitions. Skipped.

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | `log(1+x) = sum (-1)^(n+1) x^n / n coefficient formula`                                                 | yes  | `log(1+x)=∑_{n≥1}(-1)^{n-1}x^n/n`; coeff at `n` is `(-1)^{n-1}/n` | ProofWiki, Study.com, Physics Forums — unanimous standard series; **no reindexing-bridge concept** |
|  2 | WebSearch (most-general form)    | `formal power series logarithm log(1+X)=∑(-1)^(n-1)/n X^n over ℚ-algebras`                              | yes  | same series as a formal power series over a ℚ-algebra | nLab "power series", IMPAN notes, arXiv "Invitation to formal power series" — confirms the formal-series form mathlib uses |
|  3 | WebSearch (named-after / domain) | `p-adic logarithm power series ∑(-1)^(n-1)(x-1)^n/n Washington cyclotomic fields`                       | yes  | `log_p(1+y)=∑(-1)^{n-1}y^n/n`, conv. `|y|_p<1`, isometry on the ball | Wikipedia "p-adic exponential function", arXiv 1904.09850, MIT exp.pdf — the analytic object the project is building; standard, but no termwise-reindex lemma named |
|  4 | ChatGPT MCP                      | (would ask: "standard form of the log power series, its generality, and is the termwise index-shift to coefficient form a named identity?") | n/a  | —                                | **MCP tool unavailable in this environment** (no `chatgpt`/`openai` MCP tool surfaced). Compensated with extra WebSearch + WebFetch channels (#9, #10 below). Recorded n/a-tool-unavailable, not skipped. |
|  5 | Local references                 | `grep .mathlib-quality/references/` and project `refs/`                                                 | n/a  | (no references dir)              | `projects/PadicLFunctions/.mathlib-quality/references/` absent; `refs/` symlink absent. Recorded n/a. |
|  6 | nLab                             | WebFetch `ncatlab.org/nlab/show/power+series`                                                           | yes (partial) | general formal-series algebra; no log series stated, **no index-shift bridge lemma** | nLab covers substitution/inversion abstractly; explicitly **no named termwise-reindexing identity** |
|  7 | nCatLab (categorical)            | — categorical angle of "log power series coefficient reindex"                                          | n/a  | —                                | Not a categorical concept; it is an elementary coefficient identity. n/a with reason. |
|  8 | Stacks Project (alg geom)        | — "logarithm power series coefficient"                                                                  | n/a  | —                                | Not an algebraic-geometry concept (no schemes/sheaves/sites). n/a with reason. |
|  9 | MathOverflow / Math.StackExchange| `formal power series logarithm coefficient (-1)^{n+1}/n index shift identity`                           | yes (partial) | confirms coeff `(-1)^{n-1}/n`; `(-1)^{n-1}≡(-1)^{n+1}` indexing remark | No MO/MSE post treats a 0-indexed→(n+1)-coefficient bridge as a result; it's recognised only as an indexing convention |
| 10 | recent arXiv (last 5 years)      | `p-adic logarithm as evaluation of formal power series log coefficients termwise`                       | yes (adjacent) | p-adic log series + convergence (arXiv 2304.02789, 0705.4047, 1502.04607) | Many recent p-adic-log papers; none isolates a termwise reindexing lemma — it is implicit bookkeeping |

Protocol completeness:
- WebSearch ran **5 distinct queries** at three generality levels (specific log
  series, formal-series-over-ℚ-algebra, p-adic/named-domain) — passes the ≥3 bar.
- ChatGPT MCP: **tool genuinely unavailable** in this environment; recorded
  n/a-tool-unavailable and compensated by adding the MathOverflow (#9) and
  recent-arXiv (#10) channels and a direct nLab WebFetch (#6).
- Local references: checked, **absent**, recorded n/a.
- nLab: checked via WebFetch — confirms no named bridge lemma.
- Stacks / nCatLab / MathOverflow / arXiv: each checked, each with a one-line
  reason (n/a for Stacks/nCatLab; partial/adjacent hits for MO and arXiv).

### Literature summary (Phase 3)

Concept identified as: the **logarithmic (formal) power series**
`log(1+X) = ∑_{n≥1} (-1)^{n-1} X^n / n` and its **p-adic evaluation**
`log_p(x) = ∑_{n≥1} (-1)^{n-1}(x−1)^n/n`. The *target theorem itself* is **not** a
named literature object — it is a **termwise reindexing identity** between two
encodings of the same series (a hand-rolled `∑_{n≥0}` with the `(n+1)` shift and
`(-1)^n` pulled out, vs. the coefficient form `∑_{n} coeff_n(log)·(x−1)^n`).

Sources agree on the standard form: **yes** — `(-1)^{n-1}/n` at index `n`,
identically to mathlib's `coeff_log` (`(-1)^{n+1}/n`, same value).

Most general standard form: the **formal** logarithm power series over any
`ℚ`-algebra (mathlib's `PowerSeries.log A`), evaluated by the canonical
"power series at a topologically-nilpotent point = `∑ coeff_d • a^d`" rule.

Generality dimensions where the literature varies:
  - **base/scalars**: from `ℝ`/`ℂ` (analytic), to `ℚ_[p]`/`ℂ_p` (p-adic), to any
    `ℚ`-algebra (formal). The most general is the formal `ℚ`-algebra form, which
    mathlib already has as `PowerSeries.log`.
  - **what "evaluation" means**: substitution of one power series into another
    (formal) vs. summation of a convergent `tsum` at a point (analytic). The
    project uses the analytic `tsum` form; mathlib has both, including
    `PowerSeries.aeval` for the `tsum` form.

Disagreement with the literature: **none on the mathematics**. The literature's
log series is exactly the one being summed. The literature simply **has no name
for, and assigns no theorem-status to, the 0-indexed→(n+1)-coefficient
reindexing** — it treats `(-1)^{n-1}` vs `(-1)^{n+1}` and "start at `n=1` vs
peel the `n=0` term" as indexing conventions, not results. This is a strong
signal that the target is a Lean-encoding artifact, not a mathematical theorem.

---

## PHASE 4 — Generality analysis

### Generality analysis — `PadicLFunctions.padicLog_term_eq`

Literature-standard form (from Phase 3): the formal/analytic log series
`∑ coeff_n(log)·(x−1)^n` over a `ℚ`-algebra, whose evaluation-as-`tsum` is the
mathlib-idiomatic content this lemma hand-rolls around.

| # | Parameter / hypothesis            | Current Lean form                | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|----------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `[NormedField L]`, `[NormedAlgebra ℚ_[p] L]` (norm instances `omit`-ted) | normed `ℚ_[p]`-algebra; only the algebra structure used | any `ℚ`-algebra `A` (the `coeff_log` codomain) | yes | The identity is purely algebraic; `coeff_log` lives over any `[CommRing A] [Algebra ℚ A]`. The `ℚ_[p]`-specialisation is incidental to the project. |
| 2 | base ring `ℚ_[p]` (in `coeff (n+1) (log ℚ_[p])`) | the p-adic field | any ℚ-algebra | yes | mathlib's `log` is over a generic ℚ-algebra; pinning `ℚ_[p]` is project-specific. |
| 3 | `(x : L)`, the `(x − 1)` argument | element of `L`, series in `(x−1)` | element of the algebra; series in the substitution point | yes | nothing uses `x−1` specifically except as the smul argument; trivially general. |
| 4 | index `n : ℕ` with the `(n+1)` shift | 0-indexed term with a manual `+1` shift | the coefficient form is naturally `n`-indexed; the shift is the *whole point* of the lemma | NO | The `(n+1)` shift is not a hypothesis to weaken — it **is** the encoding mismatch this lemma exists to absorb. Removing it dissolves the lemma. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (rows 1–3: pinned to
`ℚ_[p]`/normed where a generic `ℚ`-algebra suffices) — **but this does not lead
to a YES-but-generalise-first verdict**, because the lemma is not a mathematical
result whose generalised form mathlib would want; generalising it just produces a
more-general *encoding-bridge*, which mathlib has no use for (it does not encode
`log` this way — see Phase 4c and Phase 5).

Number of weakening opportunities found: 3 (all incidental specialisations).
Proposed restatement: not pursued — see rationale. The "generalised" form would
be `(-1)^n · ((n+1)⁻¹ • (x-1)^{n+1}) = coeff (n+1) (log A) • (x-1)^{n+1}` over
any `[CommRing A] [Algebra ℚ A]` and `A`-algebra `L`, but it remains a
0-indexed↔coefficient bridge with no consumer outside this encoding.
Cost of restatement: CHEAP (mechanical) — but moot.

### Modern-idiom check (Phase 4c) — the Bourbaki 2.0 check

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "Let X be a foo" preambles → typeclasses/instances? | no | — | Already typeclass-based (`[Algebra ℚ_[p] L]`). |
| 2 | sequences/metric → filters/topological? | no | — | The statement is a single algebraic equation in `n`; no convergence here (summability is in the *sibling* lemmas). |
| 3 | **construct an object where a universal-property / canonical evaluation class would characterise it?** | **YES** | Don't hand-roll the `padicLog` `tsum` term-by-term against `coeff`; obtain `padicLog x = PowerSeries.aeval h (PowerSeries.log ℚ_[p])` and use `PowerSeries.aeval_eq_sum` (`aeval ha f = ∑' d, coeff d f • a^d`, `Evaluation.lean:237`) to get the coefficient form **for free**, with no per-term reindexing lemma. | **`PowerSeries.aeval`, `aeval_eq_sum`, `hasSum_aeval` (Evaluation.lean:211/237/232)** — the entire "power series evaluated at a point = `∑ coeff_d • a^d`" API, which subsumes this lemma and `padicExp_eq_tsum_coeff` and the index-0 peeling at line 892. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | No substructure involved. |
| 5 | vector-space/field-specific → modules/(semi)ring? | partial | the algebraic identity holds over any `ℚ`-algebra (Phase 4a row 1) | full ℚ-algebra `coeff_log` API — but again only relevant if the lemma were kept. |
| 6 | 1-categorical → higher-categorical? | no | — | Elementary identity. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | — | The index `n : ℕ` is intrinsic to power-series coefficients. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — and it is the decisive observation.
  - Proposed mathlib-idiomatic restatement: there should be **no** `padicLog_term_eq`
    at all. The mathlib-idiomatic move is to express `padicLog` (or its
    coefficient form) via `PowerSeries.aeval` and invoke `aeval_eq_sum`
    (`Evaluation.lean:237`) for the `∑' d, coeff d f • a^d` shape. The 0-index
    peeling (project line 892) is then `tsum`-shift bookkeeping over the
    *already-coefficient-indexed* series, not a per-term sign/shift identity.
  - Cost: MODERATE (would touch the `padicLog` definition / its `_eq_tsum_coeff`
    lemma to route through `aeval`; the downstream inversion proofs are unaffected
    in statement).
  - Mathlib downstream this enables: nothing *new in mathlib* — rather, it shows
    the lemma's content is **already in mathlib** as `aeval_eq_sum`. This is an
    argument **against** adding `padicLog_term_eq`, not for a generalised version.
  - Real mathematical improvement: the reindexing identity is an artifact of
    hand-rolling the series; mathlib's `aeval` API removes the need for it.

(Phase 4c does NOT flip this to YES-but-generalise-first: the modern idiom shows
the lemma is redundant with mathlib's evaluation API, not that mathlib wants a
modernised version of *this* bridge.)

---

## PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is **theorem** (introduces no definitional equality or
typeclass-search path). Skipped per skill scope.

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `PadicLFunctions.padicLog_term_eq`

[A] Lean-Finder       (queries we would run: "n-th term of log series equals coeff(n+1) smul")   n/a — Lean-Finder MCP not available in this environment; coverage via [D]/[E] over mathlib source + the Evaluation/Log API read directly
[B] Loogle            type pattern `?a ^ ?n * (?c⁻¹ • ?x ^ (?n+1)) = coeff (?n+1) (log _) • ?x ^ (?n+1)` and `coeff _ (PowerSeries.log _) = _`   n/a — Loogle MCP not available; substituted by reading `Mathlib/RingTheory/PowerSeries/Log.lean` + `Evaluation.lean` in full (the relevant files) and grepping
[C] LeanSearch        "termwise equality of logarithm power series with its coefficients", "evaluate power series as sum of coefficient times power"   n/a — LeanSearch MCP not available; the natural-language target ("power series = sum of coeff·a^d") resolves to `aeval_eq_sum` found via WebSearch #(mathlib eval) and source grep
[D] Grep mathlib src  `term_eq`, `termwise`, `coeff.*log.*•`, `coeff_log`, `aeval.*tsum`, `tsum.*coeff` under `Mathlib/RingTheory/PowerSeries/`   hits — `PowerSeries.coeff_log` (Log.lean:48), `PowerSeries.aeval_eq_sum`/`hasSum_aeval` (Evaluation.lean:237/232), `PiTopology.lean:336` (`f = tsum monomial`); **no termwise log-coeff bridge lemma exists in mathlib**
[E] Name pattern      all `*log*` decls in `Mathlib/RingTheory/PowerSeries/Log.lean`   hits — `log`, `coeff_log`, `constantCoeff_log`, `map_log`, `coeff_one_log`, `order_log`, `deriv_log`, `HasSubst.log`, `logOf*`; the Log API stops at `coeff_log` and substitution — **no `_term_eq`-style reindexing lemma**

Searched for both:
  - the user's current form (0-indexed term = `coeff (n+1) • …`) — **not in mathlib**;
  - the literature-standard / mathlib-idiomatic form (`aeval f = ∑' d, coeff d f • a^d`) — **IS in mathlib**, as `PowerSeries.aeval_eq_sum` (`Mathlib/RingTheory/PowerSeries/Evaluation.lean:237`), together with `hasSum_aeval` (:232) and `coeff_log` (`Log.lean:48`).

Concluded: **found the building blocks** — `PowerSeries.coeff_log`
(`Mathlib/RingTheory/PowerSeries/Log.lean:48`), `PowerSeries.aeval_eq_sum`
(`Mathlib/RingTheory/PowerSeries/Evaluation.lean:237`), and the elementary
arithmetic of `algebraMap`/`smul`/`(-1)^{n+2}=(-1)^n`. The exact *target form*
(a per-term 0-indexed↔(n+1)-coefficient identity) is **not in mathlib**, and
should not be: it is an artifact of the project's hand-rolled `padicLog`
encoding, and mathlib's `aeval_eq_sum` is the canonical replacement for the
whole reindexing manoeuvre.

---

## PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `PadicLFunctions.padicLog_term_eq`

Internal use count: **3** (all within the declaring file `PadicExp.lean`;
**0** outside the declaring file; **0** in any other project; **0** downstream/external)
External-to-file callers: **0 distinct files**

| Caller file:line                | Usage pattern (one-line excerpt) |
|---------------------------------|-----------------------------------|
| PadicExp.lean:888               | `(summable_padicLog_terms p hx).congr fun n => padicLog_term_eq p x n` (re-express the summable hand-rolled terms as coeff-terms) |
| PadicExp.lean:893               | `exact tsum_congr fun n => padicLog_term_eq p x n` (rewrite the `tsum` body to coeff-form inside `padicLog_eq_tsum_coeff`) |
| PadicExp.lean:940               | `((summable_padicLog_terms p hx).congr fun n => padicLog_term_eq p x n)` (same `.congr` in `padicExp_padicLog`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using
`padicLog_term_eq`?): **(none)** — the only place this term↔coeff dictionary is
needed is the three sites above; all three go through this lemma.

**What the pattern tells you.** All 3 uses are *inside the declaring file*, and
all 3 are the same idiom: feed `summable_padicLog_terms` / the `padicLog` `tsum`
into a `.congr` / `tsum_congr` to switch from the hand-rolled term shape to the
`coeff (n+1) (log) • …` shape, so that `summable_nat_add_iff` / `tsum_eq_zero_add`
can peel the `n = 0` term. There are **0 consumers outside the file** and **0
downstream**. Per the call-sites table in the verdicts reference, "K internal
uses but they are all the same intra-file bridge into a reindex, with no external
consumer" is a NO-leaning composability signal: it is glue between *this
project's* `padicLog` definition and mathlib's `coeff_log`, not a reusable API.

### Composition check (Phase 6)

Can `padicLog_term_eq` be derived from mathlib in ≤3 chained calls?

Attempt 1: `by rw [Algebra.smul_def, Algebra.smul_def, …, coeff_log, if_neg …]; congr 2; …; ring` (the actual proof)
  - Mathlib decls used: `Algebra.smul_def`, `PowerSeries.coeff_log`, `map_pow`,
    `map_neg`, `map_one`, `map_natCast`, `map_div₀`, `pow_succ`, `mul_comm`, `ring`.
  - Result: **succeeds** as a proof, but it is **NOT a ≤3-call composition** — it
    is a genuine multi-step rewrite of a coefficient identity (a "proof in
    disguise" per the Phase-6 heuristics table: `rw […]; ring` chains are not
    compositions).

Attempt 2 (the right framing): don't prove this lemma at all — route `padicLog`'s
coefficient form through `PowerSeries.aeval` + `aeval_eq_sum`.
  - Mathlib decls used: `PowerSeries.aeval`, `PowerSeries.aeval_eq_sum`
    (`Evaluation.lean:237`), `PowerSeries.coeff_log` (`Log.lean:48`).
  - Result: this **eliminates the lemma** rather than composing it. The
    coefficient-indexed series comes directly from `aeval_eq_sum`; the
    `n=0`-peeling is `tsum`-shift bookkeeping over an already-`coeff`-indexed
    series (`Summable.tsum_eq_zero_add` + `coeff_log … if_pos`), with **no
    per-term sign/shift identity needed**.

Conclusion: **COMPOSABLE** — in the precise sense the verdict requires: mathlib
has the building blocks (`coeff_log`, `aeval_eq_sum`) and the canonical
evaluation API that makes the hand-rolled per-term bridge unnecessary. The
lemma's own proof is a real rewrite, but its *role* (term↔coeff dictionary +
index-0 peeling) is exactly what `aeval_eq_sum` + standard `tsum`-shift lemmas
deliver, so no new lemma is justified once `padicLog` is expressed via `aeval`.

---

## Verdict: `PadicLFunctions.padicLog_term_eq`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the log power series `∑(-1)^{n-1}x^n/n` is
  unanimous and standard, but **no source names or theorem-ifies the
  0-indexed↔(n+1)-coefficient reindexing** — it is an indexing convention, not a
  result (nLab WebFetch: no bridge lemma; MO/arXiv: only the series itself).
- Generality analysis (Phase 4): STRICTLY NARROWER (pinned to `ℚ_[p]`/normed,
  generic-ℚ-algebra would do), but Phase 4c shows the lemma is **redundant with
  mathlib's evaluation API**, not a candidate for a generalised mathlib form.
- Mathlib search (Phase 5): exact form not in mathlib; **building blocks present**
  — `PowerSeries.coeff_log` (`Log.lean:48`) and `PowerSeries.aeval_eq_sum`
  (`Evaluation.lean:237`).
- Composition check (Phase 6): COMPOSABLE in the verdict's sense — the term↔coeff
  dictionary plus index-0 peeling is exactly what `aeval_eq_sum` + standard
  `tsum`-shift lemmas provide; 0 external/downstream consumers.

**Rationale (1–2 paragraphs):**

`padicLog_term_eq` is **infrastructure glue internal to this project's `padicLog`
encoding**, not a mathlib-shaped result. The project *defines* `padicLog x` as the
hand-rolled sum `∑ₙ (-1)^n · ((n+1)⁻¹ • (x−1)^{n+1})` (0-indexed, with the `(n+1)`
shift and the `(-1)^n` sign manually pulled out), and this lemma is the dictionary
that re-expresses each such term as `coeff (n+1) (PowerSeries.log ℚ_[p]) • (x−1)^{n+1}`
so the series can be re-summed against mathlib's `coeff_log` and have its `n=0` term
peeled (`summable_nat_add_iff` / `tsum_eq_zero_add` at lines 888–893). Stripping the
common `(x−1)^{n+1}`, its entire mathematical content is the one-coefficient
arithmetic identity `(-1)^n·(n+1)⁻¹ = algebraMap((-1)^{n+2}/(n+1))` — i.e. exactly
`coeff_log` at index `n+1` together with `(-1)^{n+2}=(-1)^n`. The literature search
confirms this is not a named theorem anywhere; the `(-1)^{n-1}` vs `(-1)^{n+1}` and
"start at `n=1` vs peel `n=0`" choices are indexing conventions, which is precisely
why no source elevates them to a lemma.

Mathlib already owns the genuinely reusable content twice over: `PowerSeries.coeff_log`
(`Mathlib/RingTheory/PowerSeries/Log.lean:48`) gives the coefficient, and
`PowerSeries.aeval_eq_sum` (`Mathlib/RingTheory/PowerSeries/Evaluation.lean:237`)
gives the canonical "power series evaluated at a point equals `∑' d, coeff d f • a^d`"
identity — which is the exact coefficient-indexed shape this lemma is hand-building
toward. Were `padicLog` expressed via `PowerSeries.aeval`, this per-term reindexing
lemma would not exist: the coefficient form would come directly from `aeval_eq_sum`
and the `n=0` peeling would be ordinary `tsum`-shift bookkeeping over an
already-`coeff`-indexed series. With **zero consumers outside the declaring file**
and **zero downstream**, and its role fully covered by mathlib's evaluation API plus
`coeff_log`, no new mathlib lemma is justified. (Note: the lemma is perfectly fine to
*keep in the project* as local scaffolding under the `padicExp`/`padicLog` inversion
proofs — the verdict is only that mathlib should not carry it.)

**WHY not (refactor-actionable detail):**
Mathlib has the building blocks; the user's form is the per-term bridge between
the project's hand-rolled `padicLog` series and the `coeff`-indexed series, which
mathlib's evaluation API supplies directly.
  - Mathlib building blocks:
    - `PowerSeries.coeff_log` — `Mathlib/RingTheory/PowerSeries/Log.lean:48`
      (`coeff n (log A) = if n = 0 then 0 else algebraMap ℚ A ((-1)^(n+1)/n)`).
    - `PowerSeries.aeval_eq_sum` — `Mathlib/RingTheory/PowerSeries/Evaluation.lean:237`
      (`aeval ha f = tsum fun d ↦ coeff d f • a ^ d`); companion `hasSum_aeval` (:232).
  - Composition sketch (the per-term identity, ≤3 lines, as a standalone goal it
    is a `coeff_log` + arithmetic rewrite — i.e. a proof, hence "compose by
    eliminating, not by adding"):
    ```lean
    -- the single-coefficient content, the only non-bookkeeping step:
    example (n : ℕ) :
        ((-1 : ℚ_[p]) ^ n * ((n : ℚ_[p]) + 1)⁻¹)
          = (coeff (n + 1) (PowerSeries.log ℚ_[p]) : ℚ_[p]) := by
      rw [coeff_log, if_neg (Nat.succ_ne_zero n), map_div₀, map_pow, map_neg,
        map_one, map_natCast]; push_cast; rw [pow_succ, pow_succ]; ring
    -- and the whole reindexing it feeds is `PowerSeries.aeval_eq_sum` once
    -- `padicLog` is phrased via `PowerSeries.aeval`.
    ```
  - Call sites in our project (from Phase 6.0): **K = 3**, all in
    `PadicExp.lean` (lines 888, 893, 940), all the `.congr`/`tsum_congr` bridge
    into the coefficient form; **0 external**, **0 downstream**.
  - Refactor plan (for a *mathlib-upstreaming* decision only — keeping it
    project-local needs no change): do **not** upstream `padicLog_term_eq`. If/when
    the project wants to shed the hand-rolled reindexing, re-express `padicLog`'s
    coefficient form through `PowerSeries.aeval` + `aeval_eq_sum` (`Evaluation.lean:237`)
    and obtain the `∑' n, coeff n (log) • (x−1)^n` form for free; the three call
    sites then use the `aeval` route + `coeff_log`/`tsum_eq_zero_add` directly
    instead of `padicLog_term_eq`. No mathlib lemma is added.
  - Next action: leave `padicLog_term_eq` as project-local scaffolding; **do not
    open a mathlib PR for it**. (Optional project cleanup, on the `dev/padic`
    branch, not on `main`: route `padicLog`/`padicLog_eq_tsum_coeff` through
    `PowerSeries.aeval`/`aeval_eq_sum` to remove the manual term↔coeff bridge.)

---

### Alternative reading (recorded for the human)

A reasonable reviewer could instead file this as **`BORDERLINE-needs-human`**,
because the verdict turns on a project-design judgment the skill cannot make
unilaterally: *is the project committed to the hand-rolled `padicLog` `tsum`
encoding, or open to routing through `PowerSeries.aeval`?* If committed to the
hand-rolled encoding, `padicLog_term_eq` is irreducible local glue that is simply
never a mathlib decl (still `NO`, but for a "project-glue, out of scope" reason
rather than "composable"). If open to `aeval`, the lemma disappears entirely
(clearly `NO-composable-from-mathlib`, as ruled above). Either way the verdict is
**NO for mathlib**; the only open question is the project's encoding choice, which
does not affect the mathlib-inclusion answer. The single question, if the human
wants to resolve the framing:

1. Should the project's `padicLog` (and `padicLog_eq_tsum_coeff`) be re-expressed
   via mathlib's `PowerSeries.aeval` / `aeval_eq_sum`, which would delete the need
   for `padicLog_term_eq` altogether? (yes → do the project-local refactor on
   `dev/padic`; no → keep `padicLog_term_eq` as local scaffolding.) Either answer
   leaves the mathlib verdict at NO.

---

## Next step

Leave `padicLog_term_eq` as project-local scaffolding under the
`padicExp`/`padicLog` inversion proofs; **do not open a mathlib PR for it** — its
reusable content is already in mathlib as `PowerSeries.coeff_log`
(`Mathlib/RingTheory/PowerSeries/Log.lean:48`) and `PowerSeries.aeval_eq_sum`
(`Mathlib/RingTheory/PowerSeries/Evaluation.lean:237`). Optional follow-up on the
`dev/padic` branch (not `main`, not a mathlib PR): route `padicLog` through
`PowerSeries.aeval` to remove the manual term↔coefficient reindexing and inline
the three call sites against `aeval_eq_sum` + `coeff_log`.
