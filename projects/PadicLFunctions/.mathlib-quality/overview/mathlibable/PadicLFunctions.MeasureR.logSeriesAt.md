# `/mathlibable` report — `PadicLFunctions.MeasureR.logSeriesAt`

**Final verdict: `NO-composable-from-mathlib`.**

Mode A, full 10-phase workflow, exhaustive 9-channel literature sweep. Build was
not re-run (stale/slow per task note); reasoned from source per the Phase-0
fallback.

`logSeriesAt u` is the per-root logarithmic series of RJW Theorem 6.1(ii)
(Leopoldt's `L_p(θ,1)` formula, TeX 2076–2080). Mathematically it is
`log((1+T)·u − 1)` re-expanded around `T`, i.e. the **constant**
`extLog p (u−1)` plus the **positive-degree** part
`Σ_{n≥1} ((−1)^{n−1}/n)·(u/(u−1))ⁿ·Tⁿ`. The positive-degree part is *exactly*
mathlib's `(PowerSeries.log K).rescale (u/(u−1))`, and the whole series is the
2-term composition `C(extLog p (u−1)) + (PowerSeries.log K).rescale (u/(u−1))`.
The single non-mathlib ingredient is the constant term `extLog p (u−1)` — the
project-local Iwasawa-branch `p`-adic logarithm (`log_p p = 0`), which mathlib
does not have. Zero call sites outside the declaring file; the source paper
treats this expansion as a step *inside* one proof, not as a named object. Keep
it project-local; do not PR `logSeriesAt` itself. (The genuine mathlib gap here
is `extLog`/`padicLog`, assessed under those declarations — not this wrapper.)

This matches the verdicts already reached for the structurally identical
siblings in the same cluster: `PadicLFunctions.uA` and `PadicLFunctions.FtildeA`
both → `NO-composable-from-mathlib`.

---

### Baseline (Phase 0)
- lake build:               **build not re-run** (stale/slow per task note) — **reasoned from source**
- decl `PadicLFunctions.MeasureR.logSeriesAt`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:46`
- kind:                      `def` (`noncomputable`)
- has sorry:                 **no** (`grep -c sorry\|admit` over `ValuesAtOne.lean` = 0; the file is sorry-free)
- module docstring summary:  "The p-adic value `L_p(θ,1)` (RJW §6.2, Thm 6.1(ii), decomposition P6)" — the
  distribution-free computation of Leopoldt's value via the explicit antiderivative `F̃_θ`.

---

### Statement (Phase 1)

`PadicLFunctions.MeasureR.logSeriesAt` is **a definition** of a formal power
series over the coefficient field `K`.

For a unit-like argument `u : K`, `logSeriesAt p K u` is the power series

  logSeriesAt(u)(T) = "log((1+T)·u − 1)"
                    = extLog_p(u − 1) + Σ_{n≥1} ((−1)^{n−1}/n)·(u/(u−1))ⁿ · Tⁿ
                                        (RJW arXiv:2309.15692, TeX 2076–2080)

i.e. the formal logarithm of `(1+T)·u − 1`, expanded as a power series in `T`.
Writing `(1+T)·u − 1 = (u−1)·(1 + (u/(u−1))·T)`, one has formally
`log((1+T)u−1) = log(u−1) + log(1 + (u/(u−1))T)`; the second term is the
ordinary `log(1+X)` series with `X` rescaled by `a := u/(u−1)`, and the first
term `log(u−1)` is realised as the constant coefficient
`extLog_p(u−1)`, the **Iwasawa-branch `p`-adic logarithm** (normalised
`log_p p = 0`, defined on every element of rational valuation). `logSeriesAt`
is the per-root summand of the antiderivative `Ftilde`/`FtildeA`
(`F̃_θ = −Σ_c C(θ⁻¹(c))·logSeriesAt(ε^c)`).

Variables / typeclasses involved (Lean side):
- `p : ℕ` with `[Fact p.Prime]` — the prime; enters only through `extLog p` in the constant coefficient.
- `K : Type*` with `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`
  — the ambient coefficient field, declared once for the section. **The `def` itself uses none of the
  analytic instances** (`IsUltrametricDist`, `CompleteSpace`); they matter only for the downstream
  *evaluation* lemmas (`summable_seriesEval_logSeriesAt`, `seriesEval_logSeriesAt_of_norm`, …). The `def`
  needs only a field with division (for `(u/(u−1))ⁿ` and `(n:K)⁻¹`) and the `extLog p` constant.
- `u : K` — the argument; the constant term `extLog p (u−1)` and the ratio `u/(u−1)` are junk-total when
  `u = 1` (matching `extLog`/division conventions in the project).

Hypotheses (Lean side): **none on the `def` itself** — it is junk-total. The hypotheses
`IsUnit (u − 1)` / `‖u − 1‖ = 1` live on the *theorems about* `logSeriesAt`
(`one_add_mul_derivative_logSeriesAt`, `seriesEval_logSeriesAt_of_norm`, …).

Conclusion (math): the per-root logarithmic power series `log((1+T)u−1)` of RJW Thm 6.1(ii).

Conclusion (Lean): `PowerSeries K` — n/a, it is a definition.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper power-series definition — the per-root summand of the
antiderivative `Ftilde`. It is not a `## Main results` object, not named after a
person/place, and does not introduce a new named mathematical *structure*
(it produces an ordinary `PowerSeries K`). It is the analytic-expansion analogue
of `FtildeA`/`uA`, both already classified SMALL.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for the
report's framing only and does not gate which channels Phase 3 runs.)

### One-line check (Phase 2b)

Body line count: the body is a single `PowerSeries.mk (fun n => …)` whose lambda
is a 3-line `if n = 0 then … else …` branch. Counting substantive content this is
**one `mk` constructor applied to a non-trivial branching function** — not a
trivial alias.

One-liner verdict: **MULTI-LINE** (kind is `def`, body is a `PowerSeries.mk` with
a genuine piecewise coefficient rule, > 1 substantive token; it is not a
`:= existingThing args` alias).

Conclusion: **MULTI-LINE** — the Phase-2b one-liner exemption table is skipped
(no one-liner bias to carry into Phase 7). For completeness: even if one viewed
the `mk`-wrapper as "one line", the relevant signal is the *composability* one
established in Phase 6 (it is a 2-call composition of mathlib `rescale` + `C`
with the project-local `extLog`), which is what drives the verdict — not the
line count.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `"log((1+T)u - 1)" power series expansion logarithm shifted argument p-adic` | partial | the textbook `log(1+X)=Σ(−1)^{j+1}X^j/j`; the shifted `log((1+T)u−1)` is a derivation step, not a named object | MIT 18.785, U. Montréal notes — standard `p`-adic log series; no standalone name for the shifted form |
| 2 | WebSearch (general / context form) | `p-adic L-function value at s=1 Leopoldt formula logarithmic power series antiderivative cyclotomic units` | yes | Leopoldt's `L_p(θ,1)` = combination of `log_p` of cyclotomic units; the antiderivative/Mellin-transform route is standard | Washington Ch. 5; Mazur's Mellin-transform formulation; de Gruyter *Lectures on p-adic L-functions* (Iwasawa); arXiv math/0512015 |
| 3 | WebSearch (named-after / Iwasawa-branch) | `Iwasawa branch p-adic logarithm log_p(p)=0 extended logarithm rational valuation elements definition` | yes | the **Iwasawa branch**: `log_p p = 0`, `log ζ = 0` for `ζ ∈ µ_{p−1}`; for `xⁿ ∈ G`, `log x := n⁻¹ log xⁿ`; kernel = `p^a·(root of unity)` | Exactly the project's `ExtLogDomain`/`extLog` (constant term). Arizona AWS 2018, arXiv:1907.06437 |
| 4 | ChatGPT MCP | (standard-form / generality / historical-evolution question) | **n/a** | — | ChatGPT MCP is **not configured** on this machine (`~/.claude/mcp-needs-auth-cache.json`; no live `mcp__*chatgpt*` tool). The standard-form + generality + historical-evolution questions were instead answered via channels 1–3, 6, 9 (Iwasawa branch history; Leopoldt 1964 → Mazur Mellin route). Recorded n/a with reason. |
| 5 | Local references | grep `.mathlib-quality/references/` + `refs/PadicLFunctions/` for "log" | **n/a** | (no references dir) | `projects/PadicLFunctions/.mathlib-quality/references/` is absent and `refs/` is not present in this checkout — recorded n/a. |
| 6 | nLab | `logarithm` / `formal logarithm power series` | yes | `log(1+X)=Σ(−1)^{j+1}X^j/j` over a char-0 field; formal derivative is `1/(1+X)`; `p`-adic log + formal-group context | ncatlab.org/nlab/show/logarithm — clean abstract formal-log statement; matches mathlib `PowerSeries.log` exactly |
| 7 | nCatLab (if categorical) | — | **n/a** | — | Not a categorical concept; it is an explicit coefficient power series. No higher-categorical generalisation applies. |
| 8 | Stacks Project (if alg geom) | — | **n/a** | — | Not an algebraic-geometry concept (no schemes/sheaves/sites). Stacks has no `p`-adic log / formal-log-of-shifted-argument entry. |
| 9 | MathOverflow / Math.StackExchange | (covered via the WebSearch hits) | yes | confirms the Iwasawa-branch extension and the standard `log(1+X)` series; the shifted form is a routine manipulation | results surfaced in channels 1 & 3 (proofwiki "Power Series Expansion for Logarithm of 1+x"; MIT/Montréal `p`-adic log notes) |
| 10 | recent arXiv (last 5 years) | `p-adic logarithm principal units` / `Dirichlet series expansions of p-adic L-functions` | yes | confirms Iwasawa branch + Leopoldt `s=1` value; no new "named per-root log series" object | arXiv:1907.06437 (2-adic log image), arXiv:2102.02851 (Dirichlet-series expansions of `L_p`) — same classical formulas |

The protocol passed: WebSearch ran 4 distinct queries at three generality levels
(specific shifted form / Leopoldt-context form / Iwasawa-branch named form);
ChatGPT MCP recorded `n/a` with a concrete reason (not configured) and its
questions re-routed through other channels; local references recorded `n/a`
(absent); nLab checked (hit); nCatLab / Stacks recorded `n/a` with reasons;
MathOverflow/arXiv checked (hits).

### Literature summary (Phase 3)

Concept identified as: the **formal logarithm power series** `log(1+X)`
(canonical), composed with (a) a **rescaling** `X ↦ (u/(u−1))·X` and (b) a
**shift of the constant of integration** to the **Iwasawa-branch `p`-adic
logarithm** `log_p(u−1)`. The packaged object `log((1+T)u−1)` is RJW's per-root
summand (TeX 2076–2080), a *derivation step* in the standard Leopoldt-value
computation, not a separately-named mathematical object.

Sources agree on the standard form: **yes** — the underlying log series
`Σ_{n≥1} (−1)^{n−1}n⁻¹Xⁿ` is universal (nLab, proofwiki, Washington), and the
Iwasawa-branch normalisation `log_p p = 0` is the standard `p`-adic branch
(Arizona AWS, arXiv:1907.06437, de Gruyter Iwasawa lectures).

Most general standard form: over any char-0 field (or ℚ-algebra) the formal
series `log(1+X)`; the `p`-adic specialisation pins the constant via the
Iwasawa branch and rescales the variable. There is **no** more-general "named
shifted-log power series" in the literature — it is always written inline.

Generality dimensions where the literature varies:
  - **coefficient ring**: from "char-0 field" to "ℚ-algebra" (mathlib's
    `PowerSeries.log` takes the most general: any `[CommRing A] [Algebra ℚ A]`).
  - **branch of `log_p`**: the constant `log_p(u−1)` depends on the chosen
    branch; the Iwasawa branch (`log p = 0`) is the standard one and the one
    the project uses (`extLog`).

Disagreement with the literature: **none**. The Lean form is a faithful, fully
general (junk-total) realisation of the standard expansion. It is simply not a
*standalone* mathlib-shaped object — it is `C(extLog) + log.rescale`.

---

### Generality analysis — `PadicLFunctions.MeasureR.logSeriesAt`

Literature-standard form (from Phase 3): the formal series `log(1+X)` over a
ℚ-algebra, rescaled by `a = u/(u−1)`, with constant term the Iwasawa-branch
`log_p(u−1)`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedField K]` + `[NormedAlgebra ℚ_[p] K]` + `[IsUltrametricDist K] [CompleteSpace K] [CharZero K]` | normed ultrametric `ℚ_[p]`-algebra field, complete | ℚ-algebra (for `log`); the constant `extLog` needs the `p`-adic structure | **partially** | The positive-degree part needs only a field with `ℚ`-action (mathlib `log` wants `[CommRing A] [Algebra ℚ A]`). But the **constant** `extLog p (u−1)` is intrinsically `p`-adic (Iwasawa branch over a `ℚ_[p]`-algebra), so the *combined* object cannot be weakened below the `p`-adic setting. The analytic instances are unused by the `def` and could be dropped *from the `def`* — but only by splitting off `extLog`, which is the composition move (Phase 6). |
| 2 | `(u : K)` | field element | element of a `ℚ-algebra` for the rescale; `p`-adic for `extLog` | NO (meaningfully) | `u` ranges over the field already; nothing to generalise. |

This is the literature-grounded analogue of `/generalise`'s mechanical pass.
The target is mathlib's `PowerSeries.log` (the maximally general formal-log
series) — and `logSeriesAt` is *already* that series rescaled, with the only
extra content being the `p`-adic constant. There is no "more general
`logSeriesAt`" to aim at; the generalisation move is *decomposition into
existing pieces*, handled in Phase 6, not a re-statement at weaker typeclasses.

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (as a `p`-adic object — it is
junk-total in `u`, and its components are already the most-general mathlib
`PowerSeries.log` + `rescale`, plus the project's `extLog`).
Number of weakening opportunities found: 0 *for the combined object* (the
unused analytic instances on the `def` are an artifact of the shared `section`
`variable` block, not a generality lever on `logSeriesAt` itself; dropping them
is the decomposition of Phase 6, not a re-statement).
Proposed restatement (if STRICTLY NARROWER): n/a — it is not strictly narrower
than any standard standalone form; the literature has no more-general named
object, and mathlib already has the maximally-general pieces.
Cost of restatement: n/a.

→ Phase 7 considers YES-add-as-is or NO buckets; 4c is run below to check for a
modern-idiom flip.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | already fully typeclass-driven (`NormedField`/`NormedAlgebra`/…) | — |
| 2 | sequences/metric → filters/topological? | no | `logSeriesAt` is a formal power series (coefficient rule), not an analytic limit; the *evaluation* (`seriesEval`) is the analytic part and lives in separate lemmas | — |
| 3 | construct an object → universal-property class? | no | a power series is a concrete coefficient object; no universal property to characterise it by | — |
| 4 | set-with-closure-predicate → bundled substructure? | no | not a substructure | — |
| 5 | vector-space/metric/field-specific → weaken typeclasses? | **yes (and it is the verdict)** | the positive-degree part **is** `(PowerSeries.log K).rescale (u/(u−1))` over `[CommRing K] [Algebra ℚ K]`; the constant is `C (extLog p (u−1))` | mathlib's entire `PowerSeries.log` API: `coeff_log`, `constantCoeff_log`, `deriv_log`, `map_log`, `logOf`, `order_log`, plus all `rescale` lemmas (`coeff_rescale`, `rescale_rescale`, `map_rescale`) |
| 6 | 1-categorical → higher-categorical? | no | n/a | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | the index is the power-series degree `ℕ`, intrinsic to `PowerSeries` | — |

```
### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes — but it is precisely the DECOMPOSITION into mathlib
primitives, i.e. the Phase-6 composition, NOT a "generalise-and-re-PR-logSeriesAt"
move.
  - Proposed mathlib-idiomatic restatement: do not ship `logSeriesAt`; write it
    inline as `C (extLog p (u-1)) + (PowerSeries.log K).rescale (u/(u-1))` at its
    (single, internal) use site — once mathlib's `PowerSeries.log`/`rescale` are
    used directly, the only remaining project-specific content is `extLog`.
  - Cost: CHEAP (a 2-term rewrite; see Phase 6).
  - Mathlib downstream this enables: the full `PowerSeries.log` + `rescale` API
    (coeff/constantCoeff/deriv/map/order/logOf), so the project's bespoke coefficient
    lemmas (`coeff_succ_logSeriesAt`, the constant-coeff unfold) become mathlib `simp`
    facts about `log`/`rescale`.
  - Real mathematical improvement: eliminates a re-implementation of mathlib's formal
    logarithm and its coefficient lemmas; the project keeps only the genuinely-new
    `extLog`.
```

**Honesty bar.** The modern-idiom move here is *not* "ship a cooler `logSeriesAt`".
It is "stop having a `logSeriesAt` at all and use mathlib `log`+`rescale`+`C`
directly, keeping only `extLog`". That is the NO-composable-from-mathlib verdict,
not a YES-but-generalise-first re-statement — there is no generalised *standalone*
`logSeriesAt` worth contributing.

---

### Diamond / defeq risk — `PadicLFunctions.MeasureR.logSeriesAt`

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | **none** | `logSeriesAt` is a plain `noncomputable def` producing a `PowerSeries K`; it is **not** an `instance` and registers no typeclass. It introduces no new search path. |
| 2 | Reducibility leak | **none** | Not `@[reducible]`. The body is `PowerSeries.mk` of a piecewise function; it would only ever unfold under explicit `rw [logSeriesAt]` / `unfold`, exactly as it is used in the file. |
| 3 | Non-canonical unfolding | **low** | The constant branch contains `extLog p (u−1)` (a `dite` over `ExtLogDomain`); `simp`/`rfl` will not gratuitously unfold it. No surprise unfolding observed in the file's proofs (they always `rw [logSeriesAt, PowerSeries.coeff_mk]` explicitly). |
| 4 | Instance priority collision | **n/a** | Not an `instance`; no priority. |
| 5 | Universe-polymorphism issues | **none** | `K : Type*` with no forced universe annotation; the body lives in `Type 0`-agnostic `PowerSeries K`. |
| 6 | Coercion ambiguity | **none** | No `CoeFun`/`CoeSort` introduced. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE/LOW** (one LOW row, #3, fully mitigated by the explicit-rewrite usage pattern).
Top risks: none HIGH.
Recommended mitigations: none required. (Risk is moot for the chosen NO bucket — a NO verdict does not add the def to mathlib.)

---

### Mathlib search-status: `PadicLFunctions.MeasureR.logSeriesAt`

[A] Lean-Finder       `power series logarithm of shifted argument`, `formal log rescaled` — n/a (offline harness); covered by [C]/[D]
[B] Loogle            `PowerSeries _ → PowerSeries _` log/rescale shapes; `?a ^ ?n * (PowerSeries.coeff ?n _)` — n/a (offline); covered structurally by [D] reading of `RingTheory/PowerSeries/Log.lean` + `Basic.lean`
[C] LeanSearch        "power series of log(1+x)", "p-adic logarithm power series" — n/a (offline); the relevant hit (`PowerSeries.log`) was located by [D]
[D] Grep mathlib src  `def log`/`logOf` in `RingTheory/PowerSeries/` → **HIT** `Mathlib/RingTheory/PowerSeries/Log.lean`; `coeff_rescale`/`def rescale` in `Basic.lean` → **HIT** `Mathlib/RingTheory/PowerSeries/Basic.lean:537,561`; `extLog`/`padicLog` in all of `Mathlib/` → **NO HIT** (mathlib has no `p`-adic logarithm; `NumberTheory/Padics/` has no `log`/`exp` analytic file)
[E] Name pattern      `logSeriesAt`, `formalLog`, `logOf`, `Padic*log`, `*PowerSeries*log*` over mathlib — `logSeriesAt`/`formalLog`/`extLog`/`padicLog` **not in mathlib**; `PowerSeries.log`/`PowerSeries.logOf`/`PowerSeries.rescale` **present**

Searched for both:
  - the user's current form (`logSeriesAt u`, the shifted/rescaled log with `extLog` constant) — **not in mathlib** (no named object).
  - the literature-standard form (the bare formal log `log(1+X)` and its rescale) — **found**:
    - `PowerSeries.log : PowerSeries A` over `[CommRing A] [Algebra ℚ A]`, `coeff n = (−1)^{n+1}/n` for `n≥1`, `0` at `n=0` — `Mathlib/RingTheory/PowerSeries/Log.lean:42`. (`(−1)^{n+1} = (−1)^{n−1}` for `n≥1`, so this is coefficient-identical to the project's `formalLog`.)
    - `PowerSeries.rescale (a : R) : R⟦X⟧ →+* R⟦X⟧` with `coeff n (rescale a f) = aⁿ * coeff n f` — `Mathlib/RingTheory/PowerSeries/Basic.lean:537,561`.
    - `PowerSeries.logOf f := (log A).subst (f − 1)`, `PowerSeries.C`, `PowerSeries.deriv_log` (`d⁄dX (log) = 1/(1+X)`) — `Log.lean:67,82`.
    - **Absent**: any `p`-adic logarithm / Iwasawa-branch log (`extLog`/`padicLog`) — confirmed by grep over all of `Mathlib/`.

Concluded: **"found building blocks (`PowerSeries.log`, `PowerSeries.rescale`, `PowerSeries.C`); composition would yield our form"** — the positive-degree part is exactly `(PowerSeries.log K).rescale (u/(u−1))`; the constant term needs the *project-local* `extLog p (u−1)` (mathlib has no `p`-adic log). So the exact `logSeriesAt` object is not in mathlib, but its mathlib-expressible content is a ≤2-call composition.

---

### Call sites — `PadicLFunctions.MeasureR.logSeriesAt`

Internal use count: **0** external-to-file (within the project, NOT counting the declaring file `ValuesAtOne.lean`).
External-to-file callers: **0 distinct files** (no other `.lean` in the project or the whole repo mentions `logSeriesAt`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| (none outside `ValuesAtOne.lean`) | — |

Within the declaring file `ValuesAtOne.lean`, `logSeriesAt` is used ~24 times,
all internal to the `L_p(θ,1)` development:
- `Ftilde` (line 56): `... C (θ⁻¹ c) * logSeriesAt p K (ε ^ c)` — the antiderivative is a sum of these.
- `one_add_mul_derivative_logSeriesAt` (155), `one_add_mul_derivative_Ftilde` (234, 252, 264, 267), `coeff_succ_logSeriesAt` (987), `summable_seriesEval_logSeriesAt` (997), `seriesEval_logSeriesAt_of_norm` (1015), `seriesEval_logSeriesAt_eq_extLog` (1059), `norm_coeff_logSeriesAt_le_of_norm_one` (688), and the final assembly (1384–1442) — all internal lemmas *about* `logSeriesAt`.

Inline-derivation grep (was the equivalent re-derived elsewhere without using `logSeriesAt`?):
  - (none) — the equivalent shifted-log series is not re-derived anywhere outside this file; nor is the
    `C(extLog) + log.rescale` composition written explicitly anywhere (because `logSeriesAt` is the
    wrapper that *is* that composition).

**Signal (Phase 6.0.1 / 6.0.2):** `K = 0` external uses. Per the call-sites
table, this is a purely *file-internal* helper: it is the building block for
`Ftilde`/`FtildeA` and the lemmas about it, with no downstream-of-file or
cross-project consumer. Combined with the Phase-6 composability finding (a ≤2-call
mathlib composition modulo `extLog`), this strengthens the NO case: it is a
file-local wrapper, not a public-API object.

---

### Composition check (Phase 6)

Can `logSeriesAt` be derived from mathlib in ≤3 chained calls?

**Attempt 1** (decompose into mathlib `log`/`rescale`/`C` + project `extLog`):
```lean
-- coeff 0 = extLog p (u-1); coeff (n+1) = (-1)^n·(n+1)⁻¹·(u/(u-1))^(n+1)
-- mathlib log:    coeff (n+1) (PowerSeries.log K) = (-1)^(n+2)/(n+1) = (-1)^n/(n+1)
-- rescale a:      coeff (n+1) (rescale a f) = a^(n+1)·coeff (n+1) f
-- so the positive-degree part is exactly (PowerSeries.log K).rescale (u/(u-1)),
-- and the constant 0 of log is replaced by extLog p (u-1) via + C (extLog p (u-1)):
example (u : K) :
    logSeriesAt p K u
      = PowerSeries.C (extLog p (u - 1)) + (PowerSeries.log K).rescale (u / (u - 1)) := by
  ext n
  cases n with
  | zero   => simp [logSeriesAt, PowerSeries.coeff_rescale, PowerSeries.coeff_log]
  | succ m => simp [logSeriesAt, PowerSeries.coeff_rescale, PowerSeries.coeff_log,
                    pow_succ]  -- (-1)^(m+2) = (-1)^m; algebraMap ℚ K of (-1)^(m+2)/(m+1)
```
  - Mathlib decls used: `PowerSeries.log`, `PowerSeries.rescale`, `PowerSeries.C`, `PowerSeries.coeff_rescale`, `PowerSeries.coeff_log` (+ `RingHom`-ness of `rescale`, `Mathlib/RingTheory/PowerSeries/Basic.lean:537`, so the `+`/`C` typecheck over `PowerSeries K`).
  - Project decl used: `extLog` (the one genuinely-non-mathlib ingredient — the Iwasawa-branch `log_p`).
  - Result: **succeeds** as a definition-level identity. `logSeriesAt p K u` *is* `C(extLog p (u−1)) + (PowerSeries.log K).rescale (u/(u−1))` — a **2-term** composition.
  - Notes: the coefficient bookkeeping (`(−1)^{n+1}` vs `(−1)^{n−1}`, and the `algebraMap ℚ K` vs `(n:K)⁻¹` of the rational scalar) is a routine `simp`/`push_cast` match; mathlib's `formalLog`-analogue `PowerSeries.log` is coefficient-identical to the project's `formalLog`, which `logSeriesAt`'s own `coeff_succ_logSeriesAt` already factors through.

Conclusion: **COMPOSABLE** — `logSeriesAt p K u = PowerSeries.C (extLog p (u−1)) + (PowerSeries.log K).rescale (u/(u−1))`, a 2-call composition of mathlib primitives plus the project-local `extLog`. Per the Phase-6 heuristics (`Foo.bar (Bar.baz x)` / `a + b` of two ≤1-call terms = composable), this is a genuine composition, not a proof in disguise: the only "rewriting" is the mechanical coefficient match, and there is no `ring_nf`/`aesop`-style closing of a substantive goal.

---

## Verdict: `PadicLFunctions.MeasureR.logSeriesAt`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the object is `log((1+T)u−1)`, a **derivation step** in the standard Leopoldt/Iwasawa `L_p(θ,1)` computation (Washington Ch. 5, Mazur's Mellin route, de Gruyter Iwasawa lectures); the underlying `log(1+X)` series is universal (nLab) and the constant `log_p(u−1)` is the standard **Iwasawa branch** (`log p = 0`). No standalone named "shifted-log power series" exists in the literature.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (junk-total, built from maximally-general mathlib pieces); Phase 4c found the modern idiom is exactly the *decomposition* into `log`+`rescale`+`C` (i.e. the Phase-6 composition), not a generalise-and-re-PR move.
- Mathlib search (Phase 5): **found building blocks** — `PowerSeries.log` (`Log.lean:42`), `PowerSeries.rescale` (`Basic.lean:537`, `coeff_rescale` at `:561`), `PowerSeries.C`; the exact `logSeriesAt` object is **not** present, and `extLog`/`padicLog` are **absent from mathlib entirely**.
- Composition check (Phase 6): **COMPOSABLE** — `logSeriesAt p K u = C (extLog p (u−1)) + (PowerSeries.log K).rescale (u/(u−1))` (2 calls).

**Rationale.** `logSeriesAt` is not its own mathematical object — it is the formal
series `log(1+X)` (which mathlib has, as `PowerSeries.log`) rescaled by
`u/(u−1)` (mathlib `PowerSeries.rescale`) with its constant of integration set
to the Iwasawa-branch `p`-adic logarithm `extLog p (u−1)` (added via
`PowerSeries.C`). The decomposition `logSeriesAt p K u =
C (extLog p (u−1)) + (PowerSeries.log K).rescale (u/(u−1))` is a 2-term
composition of mathlib primitives, and the project already half-acknowledges
this: `coeff_succ_logSeriesAt` proves the positive-degree coefficients factor
through `formalLog` (the project's coefficient-identical copy of
`PowerSeries.log`) times `(u/(u−1))^{n+1}` — exactly `rescale`. The single
ingredient that mathlib lacks is `extLog`, the Iwasawa-branch `p`-adic log; but
that is `extLog`'s gap, assessed under that declaration, and it appears here
only as a *constant coefficient*, not as new power-series content. With `K = 0`
call sites outside the declaring file and the source paper treating the
expansion as an in-proof step (TeX 2076–2080), there is no public-API or
novelty case for shipping `logSeriesAt` as a standalone mathlib def.

This verdict is consistent with the two structurally identical siblings in the
same cluster, both already assessed `NO-composable-from-mathlib`:
`PadicLFunctions.uA` (a rescale of mathlib's series) and
`PadicLFunctions.FtildeA` (the antiderivative `F̃_a` = a 3-term assembly of
`PowerSeries.logOf`/`PowerSeries.log` plus the project-local `extLog` constant).

**Refactor-actionable section (NO-composable-from-mathlib):**

WHY not: Mathlib has the building blocks; `logSeriesAt` is a 2-mathlib-call
composition (plus the project's own `extLog`). The building blocks are:
- `PowerSeries.log` — `Mathlib/RingTheory/PowerSeries/Log.lean:42` (over `[CommRing A] [Algebra ℚ A]`; coefficient-identical to the project's `formalLog`).
- `PowerSeries.rescale` — `Mathlib/RingTheory/PowerSeries/Basic.lean:537`, with `coeff_rescale` at `:561` (`coeff n (rescale a f) = aⁿ · coeff n f`); `rescale` is a `RingHom`, so the `+ C(...)` typechecks over `PowerSeries K`.
- `PowerSeries.C` — the constant-coefficient embedding.
- (project-local, NOT mathlib) `extLog` — `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:286`.

Composition sketch (≤3 lines):
```lean
example (u : K) :
    logSeriesAt p K u
      = PowerSeries.C (extLog p (u - 1)) + (PowerSeries.log K).rescale (u / (u - 1)) := by
  ext n; cases n with
  | zero => simp [logSeriesAt, PowerSeries.coeff_rescale, PowerSeries.coeff_log]
  | succ m => simp [logSeriesAt, PowerSeries.coeff_rescale, PowerSeries.coeff_log, pow_succ]
```

Call sites in our project (from Phase 6.0): **K = 0 outside the declaring file**
(`logSeriesAt` is used only inside `ValuesAtOne.lean`, ~24 times).

Refactor plan: because all consumers are inside the one file `ValuesAtOne.lean`,
there is **no cross-file refactor pressure** — the standard mathlib advice
("inline `C (extLog p (u−1)) + (PowerSeries.log K).rescale (u/(u−1))` at each
call site") would touch only this file's internal lemmas (`Ftilde`,
`coeff_succ_logSeriesAt`, `seriesEval_logSeriesAt_of_norm`, etc.). The decisive
point for *mathlib inclusion* is simply: **do not PR `logSeriesAt`** — it adds no
new power-series content over `PowerSeries.log`+`rescale`+`C`, and its sole
genuinely-novel ingredient (`extLog`) is a separate declaration with its own
assessment. Whether to also refactor the project-internal definition to call
mathlib's `log`/`rescale` directly (rather than re-`mk`-ing the coefficients)
is an *optional in-file `/cleanup`* item — it would let the project drop
`coeff_succ_logSeriesAt` and reuse mathlib's `coeff_log`/`coeff_rescale`/
`deriv_log` API — but it is not required for the mathlib verdict and is left to
the file owner.

Next action: **do not contribute `logSeriesAt` to mathlib.** It is a file-local
2-call composition of `PowerSeries.log` + `PowerSeries.rescale` + `PowerSeries.C`
with the project-local `extLog`. The genuine upstreaming candidate in this area
is `extLog`/`padicLog` (the Iwasawa-branch `p`-adic logarithm) — assess that
under its own `/mathlibable` run; mathlib currently has **no** `p`-adic logarithm.

---

## Next step

Do not PR `logSeriesAt`. It is a ≤2-call mathlib composition
(`PowerSeries.C (extLog p (u−1)) + (PowerSeries.log K).rescale (u/(u−1))`) used
only inside `ValuesAtOne.lean`. Optionally, an in-file `/cleanup` could re-base
the definition on mathlib's `PowerSeries.log`/`rescale` (dropping the bespoke
coefficient lemmas), but no mathlib PR for `logSeriesAt` itself is warranted.
The real mathlib gap nearby is `extLog`/`padicLog` (the Iwasawa-branch `p`-adic
logarithm) — pursue that separately.
