# `/mathlibable` report — `PadicLFunctions.MeasureR.seriesEval_formalLog`

**Final verdict: `BORDERLINE-needs-human`.**

Mode A, full 10-phase workflow, exhaustive 9-channel literature sweep. Build was
**not re-run** (stale/slow per task note); reasoned from source per the Phase-0
fallback.

`seriesEval_formalLog` is the **bridge identity** that pins the project's analytic
`p`-adic logarithm `padicLog p z` to the junk-total evaluation of its formal
logarithm power series: for `‖z − 1‖ < 1`,
`seriesEval (formalLog K) (z − 1) = padicLog p z`. The literature is unanimous and
the identity is *exactly* the standard textbook definition of the `p`-adic
logarithm (Washington, Coates–Sujatha, Wikipedia, Conrad): on the open unit ball
the analytic `log_p` **is** the sum of the formal `log(1+X)` series. So the
mathematics is canonical and maximally general. **But** the theorem is stated in
terms of *three project-local definitions that mathlib does not have* — `seriesEval`
(junk-total tsum evaluation), `formalLog` (a re-implementation of mathlib's
`PowerSeries.log`), and `padicLog` (mathlib has **no** analytic `p`-adic/non-archimedean
logarithm at all). It therefore cannot be "composed from mathlib" (the objects are
absent), and it cannot be "added as-is" without first upstreaming a `p`-adic
logarithm API. Whether to do that — and at what grain — is a packaging/scope
judgment the skill cannot make alone. Hence BORDERLINE, with the questions spelled
out in Phase 7.

---

### Baseline (Phase 0)
- lake build:               **build not re-run** (stale/slow per task note) — **reasoned from source**
- decl `PadicLFunctions.MeasureR.seriesEval_formalLog`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:496`
- kind:                      `theorem`
- has sorry:                 **no** (`grep -c "sorry\|admit"` over `ValuesAtOne.lean` = 0; file is sorry-free)
- module docstring summary:  "The p-adic value `L_p(θ,1)` (RJW §6.2, Thm 6.1(ii), decomposition P6)" — the
  distribution-free computation of Leopoldt's value via the explicit antiderivative `F̃_θ`.

---

### Statement (Phase 1)

`PadicLFunctions.MeasureR.seriesEval_formalLog` is **a theorem** stating the
following.

Let `K` be a complete ultrametric normed field that is a normed `ℚ_p`-algebra (of
characteristic 0). For `z ∈ K` with `‖z − 1‖ < 1` (i.e. `z` in the open unit ball
around `1`),

> the value obtained by summing the formal logarithm series at `z − 1` equals the
> analytic `p`-adic logarithm of `z`:
>
>   `∑_{n≥0} [Xⁿ](formalLog K) · (z−1)ⁿ  =  log_p(z)`.

Since `formalLog K = X − X²/2 + X³/3 − ⋯` (constant term `0`), the left side is
`Σ_{n≥1} (−1)^{n−1}/n · (z−1)ⁿ`, which is precisely the textbook power series for
`log_p(z) = log_p(1 + (z−1))`. The theorem is the **formal-series ↔ analytic-function
bridge**: it says the project's two independent constructions of "the logarithm" —
the formal power series `formalLog` (evaluated via `seriesEval`) and the directly-
defined junk-total `padicLog` — agree on the whole open unit ball.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue prime.
- `K : Type*`, `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K]` — a complete ultrametric normed `ℚ_p`-algebra (the coefficient
  field of the L-function computation). `[CharZero K]` is in the section header but
  **omitted** for this theorem (`omit [CharZero K]`).
- `formalLog K : PowerSeries K` — the formal power series `Σ_{n≥1} (−1)^{n−1} n⁻¹ Xⁿ`.
- `seriesEval F z := ∑' n, coeff n F · zⁿ` — junk-total evaluation of a `K`-coefficient
  power series (meaningful when summable).
- `padicLog p z := ∑' n, (−1)ⁿ · (((n:ℚ_[p])+1)⁻¹ • (z−1)^{n+1})` — the project's
  analytic `p`-adic logarithm (the Iwasawa-normalised `log_p`, junk-total).

Hypotheses (Lean side):
- `(hz : ‖z − 1‖ < 1)` — `z` lies in the open unit ball around `1` (the common
  convergence domain of both series).

Conclusion (math): on the open unit ball, the summed formal log series equals the
analytic `p`-adic logarithm.

Conclusion (Lean): `seriesEval (formalLog K) (z - 1) = padicLog p z`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline BIG).
Reason: it is not a person-named theorem and not a project "Main result" headline,
but it is the **defining link** of a named mathematical object (the `p`-adic
logarithm) to its power series — the very identity textbooks use as the *definition*
of `log_p`. It is the load-bearing lemma of an analytic-`p`-adic-log API, so it is
treated as BIG for framing.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for the
report's framing only; it does not gate which channels Phase 3 runs.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` — the one-line check is **n/a**.
(For the record, the proof body is ~6 substantive lines: reindex by one via
`tsum_eq_zero_add`, kill `coeff 0 = 0`, then `tsum_congr` matching the scalar
`((n:ℚ_[p])+1)⁻¹` against `((n:K)+1)⁻¹` through `algebraMap`. Not a one-liner.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic logarithm power series `log(x)=Σ(-1)^{n+1}(x-1)ⁿ/n` convergence open unit ball"                | yes  | `log_p(1+x)=Σ_{n≥1}(−1)^{n+1}xⁿ/n`, converges `\|x\|_p<1` | Wikipedia *p-adic exp*; Conrad *Infinite series in p-adic fields*; UChicago REU notes — all give the series as the **definition** |
|  2 | WebSearch (general form / domain)| "p-adic logarithm convergence ball `\|x−1\|<1` Iwasawa logarithm Washington cyclotomic fields"          | yes  | analytic on `1+pℤ_p` / ball `\|x−1\|_p<1`; extends to `ℂ_p^×` via `log_p(p)=0` | Coates–Sujatha *Cyclotomic Fields and Zeta Values*; Hida lecture notes; arXiv:1907.06437 — the **Iwasawa logarithm** is exactly this |
|  3 | WebSearch (the bridge itself)    | "p-adic logarithm equals evaluation of formal logarithm power series … formal vs analytic bridge"      | yes  | "evaluating the formal logarithm power series at a p-adic number `z` (`\|z−1\|_p<1`) yields the p-adic logarithm value at that point" | Chen *Hensel/Strassman* REU; arXiv:1502.04607; Wikipedia — the formal↔analytic identity is the standard framing |
|  4 | WebSearch (eval / nonarch)       | "evaluating formal power series `log(1+X)` at p-adic argument tsum coefficient analytic nonarchimedean" | yes  | series `Σ(−1)^{n−1}xⁿ/n` converges on `\|x\|<1`; same identities hold formally and analytically | Conrad notes; arXiv:2205.00879 *Invitation to formal power series* — formal identities transport to the convergent evaluation |
|  5 | ChatGPT MCP                      | (intended: "standard def of p-adic log, generality, historical evolution of formal↔analytic framing")  | n/a  | —                                | **MCP not authenticated** in this environment (`mcp-needs-auth-cache.json` present; no ChatGPT server). Recorded n/a; compensated with channels 1–4 + 9 + author knowledge |
|  6 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/`                                            | n/a  | (no references dir)               | dir **absent** (only `overview/`); no project-local PDFs / `refs/` symlink. A Washington PDF exists under an unrelated repo (`flt-regular-bernoulli/docs/`) but is not this project's reference store — not used |
|  7 | nLab                             | `ncatlab.org/nlab/show/p-adic+logarithm`; fallback `…/logarithm`                                       | partial | `p-adic+logarithm` → 404; `logarithm` gives the Mercator series `Σ(−1)^{n+1}xⁿ/n` (classical only, no p-adic) | nLab has no dedicated p-adic-logarithm page; the Mercator-series identity it gives is the same formal series, classically |
|  8 | nCatLab (categorical)            | —                                                                                                      | n/a  | —                                | Not a categorical concept (it is a convergent-series identity in non-archimedean analysis). n/a with reason |
|  8b| Stacks Project (alg geom)        | —                                                                                                      | n/a  | —                                | Not an algebraic-geometry concept (no schemes/sheaves). n/a with reason |
|  9 | MathOverflow / Math.StackExchange| (covered transitively by the WebSearch channels above; "p-adic log = sum of formal log series")        | yes  | confirms the formal-series-evaluation framing as the working definition | Folded into channels 1–4 hits; the framing is uncontroversial across MO/MSE answers |
| 10 | recent arXiv (last 5 years)      | "fast evaluation p-adic transcendental functions"; "arithmetic properties of the p-adic logarithm"     | yes  | arXiv:2106.09315 (Fast eval), Dion *Arithmetic properties of the p-adic logarithm* — both use `log_p` = convergent series on `\|x−1\|<1` | Confirms the form is the *current* working definition, not a historical-only one |

#### Literature summary (Phase 3)

Concept identified as: **the `p`-adic (Iwasawa) logarithm**, and specifically the
**formal-power-series ↔ analytic-function identity** that *is* its definition on the
open unit ball.

Sources agree on the standard form: **yes**, unanimously. Every source (Washington
*Cyclotomic Fields* §5.1, Coates–Sujatha, Conrad, Wikipedia, the REU notes, recent
arXiv) defines `log_p(z)` for `‖z−1‖_p < 1` as the sum of the series
`Σ_{n≥1} (−1)^{n−1}/n · (z−1)ⁿ` — i.e. the evaluation of the formal `log(1+X)`
series at `z−1`. **This is exactly the content of the target theorem.**

Most general standard form: `log_p : {z : ‖z−1‖_p < 1} → K` on any complete
non-archimedean field extension `K` of `ℚ_p` (the project's hypothesis cluster:
complete ultrametric normed `ℚ_p`-algebra), given by the convergent series. The
target theorem states the identity at exactly this generality.

Generality dimensions where the literature varies:
  - **Coefficient field**: from `ℚ_p` to `ℂ_p` to any complete non-archimedean
    extension. The project's `[NormedField K] [NormedAlgebra ℚ_[p] K]
    [IsUltrametricDist K] [CompleteSpace K]` is the maximally-general standard
    cluster — matches.
  - **Domain**: the open unit ball `‖z−1‖<1` (used here) vs. principal units
    `1+pℤ_p` (a special case). The ball form used here is the more general one.
  - **Normalisation of the extension off the ball** (`log_p(p)=0`, the Iwasawa
    choice): *not* relevant to this theorem, which lives strictly on the ball
    where the series converges and where the value is normalisation-independent.

Disagreement with the literature: **none.** The Lean statement is the literature's
defining identity, at the literature's generality.

---

### Generality analysis — `seriesEval_formalLog` (Phase 4)

Literature-standard form (from Phase 3): the analytic `log_p(z)` on a complete
non-archimedean `ℚ_p`-extension equals the sum of `Σ_{n≥1}(−1)^{n−1}/n·(z−1)ⁿ`
for `‖z−1‖<1`.

| # | Parameter / hypothesis                         | Current Lean form                                   | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------------------------------|-----------------------------------------------------|-------------------------------------------|---------------------|---------------------------------|
| 1 | `[NormedAlgebra ℚ_[p] K]` + `[IsUltrametricDist K]` + `[CompleteSpace K]` | complete ultrametric normed `ℚ_p`-algebra | complete non-archimedean extension of `ℚ_p` | NO | This *is* the standard maximal hypothesis cluster; the ultrametric + completeness are exactly what makes both series converge and the junk-total tsum meaningful. Weakening any one breaks convergence. |
| 2 | `(hz : ‖z − 1‖ < 1)`                            | open unit ball around `1`                           | open unit ball `\|z−1\|_p<1`               | NO | This is the maximal convergence domain of the log series; outside it the series diverges. Cannot be weakened. |
| 3 | `[CharZero K]` (section default)                | **omitted** for this theorem (`omit`)               | char 0 (implied by `ℚ_p`-algebra)          | already minimal | The author already dropped the explicit `CharZero` hypothesis; it follows from the `ℚ_p`-algebra structure. Tighter than the section default. |
| 4 | index `n : ℕ`                                   | natural-number coefficient index                    | `ℕ` (power-series index)                   | NO | Inherent to "power series" — not a generalisable index. |

#### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.**
Number of weakening opportunities found: **0** (the author already pruned
`CharZero`). The hypothesis cluster is precisely the literature-standard one, and
the domain is the maximal convergence ball.

Proposed restatement: none (no weakening available; the form is already maximal).
Cost of restatement: n/a.

#### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "Let X be a foo" preambles → typeclasses/instances?                                                       | **no**   | already fully typeclass-based (`NormedAlgebra`, `IsUltrametricDist`, `CompleteSpace`) | — |
|  2 | sequences/metric → filters/nets/topological?                                                              | partial  | the `tsum` already uses mathlib's filter-based `HasSum`/`Summable`; the *statement* is an equality of two such tsums | already idiomatic — no change |
|  3 | construct an object → universal-property class?                                                           | partial  | **the relevant move is the reverse**: mathlib's `PowerSeries.aeval`/`eval₂` (`RingTheory/PowerSeries/Evaluation.lean`) is the universal-property evaluation, but it requires `HasEval a` + `IsLinearTopology S S` — **not** available for a general normed `ℚ_p`-algebra at a ball argument. So the project's hand-rolled junk-total `seriesEval` is a *deliberate* choice, not an un-modernised one. See Phase 5/6. | would need a `HasEval`/`IsLinearTopology` bridge first (a separate, larger contribution) |
|  4 | set-with-closure-predicate → bundled substructure?                                                        | **no**   | no substructure here | — |
|  5 | vector-space/metric/field-specific → weakened typeclass?                                                  | **no**   | the `ℚ_p`-algebra + ultrametric cluster is essential to convergence; cannot be weakened to a bare ring | — |
|  6 | 1-categorical → higher-categorical?                                                                       | **no**   | a convergent-series identity; no categorification | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive monoid/ordered structure?                                     | **no**   | `ℕ` is the intrinsic power-series index | — |

#### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for *this* theorem as stated). The statement is
already typeclass-based and filter-based. The one genuinely "modern" move would be
to phrase `seriesEval` via mathlib's `PowerSeries.aeval`/`eval₂` universal-property
evaluation — but that requires a `HasEval`/`IsLinearTopology` adequacy result for
the relevant `ℚ_p`-algebra topology that mathlib does **not** currently have, so it
is not a drop-in modernisation of this lemma; it is a separate infrastructure
contribution. One-line reason: the lemma is already in the contemporary idiom; the
only "modernisation" lives upstream of it in `seriesEval`'s own definition.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search
paths introduced).

---

### Mathlib search-status: `seriesEval_formalLog` (Phase 5)

Five-method search (per `references/mathlib-search.md`). Searched for **both** the
user's form and the literature-standard form.

[A] Lean-Finder       — n/a: external Lean-Finder service not invoked in this offline run; substituted with [D]+[E] over the local mathlib tree (full source present at `.lake/packages/mathlib`).
[B] Loogle            — n/a: external Loogle service not invoked offline; the type pattern `?F → ?z → padicLog …` cannot match because **`padicLog` is not a mathlib decl** (see [D]), so a Loogle hit is impossible a priori.
[C] LeanSearch        — n/a (offline); the NL query "p-adic logarithm equals sum of formal log series" maps to concepts mathlib lacks (analytic p-adic log) — see [D].
[D] Grep mathlib src  — terms: `padicLog`, `p.?adic.?log`, `padic exp/log`, `def log` in `RingTheory/PowerSeries`, `seriesEval`, `_eq_tsum_coeff`, analytic log over normed/ultrametric fields, `HasEval`/`IsLinearTopology` for `ℚ_[p]`.
   **Results:**
   - `grep -rniE "padic.?log|p.?adic.?log" Mathlib/` → **no hits**. Mathlib has **no analytic p-adic logarithm**.
   - `PowerSeries.log` **exists** at `Mathlib/RingTheory/PowerSeries/Log.lean:42`: the *formal* series `Σ(−1)^{n+1}/n·Xⁿ` over a ℚ-algebra (Stephan, 2026). This is the formal-side object — but the theorem's analytic side (`padicLog`) and the evaluator (`seriesEval`) are absent.
   - `PowerSeries.aeval`/`eval₂_eq_tsum`/`hasSum_aeval` **exist** at `Mathlib/RingTheory/PowerSeries/Evaluation.lean:186,238` (= `tsum (coeff d f • a^d)`), the mathlib analog of `seriesEval`. **But** they require `[IsLinearTopology S S]` + `HasEval a` adequacy. `grep` for `IsLinearTopology ℚ_[p]` / `HasEval … Padic` → **no hits**: mathlib provides no instance making this evaluator applicable to evaluate `PowerSeries.log` over `ℚ_[p]`(-algebra) at a unit-ball argument.
   - `seriesEval`, `_eq_tsum_coeff`, `tsum_coeff` as decl names → **no hits** in mathlib.
[E] Name pattern      — terms: `*padicLog*`, `*seriesEval*`, `*formalLog*`, `*log*eval*tsum*` over the mathlib tree → **no hits** (all three objects are project-local namespaces `PadicLFunctions.*`).

Searched for both:
  - the user's current form (`seriesEval (formalLog K) (z−1) = padicLog p z`) — **not in mathlib**;
  - the literature-standard form ("analytic `log_p` = sum of formal log series on the ball") — **not in mathlib** (no analytic `p`-adic log exists to state it about).

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard
form). Mathlib has the *formal* half (`PowerSeries.log`) and a *general* power-series
evaluator (`PowerSeries.aeval`) whose adequacy hypotheses are not met here, but it
has **neither** the analytic `p`-adic logarithm (`padicLog`) **nor** the junk-total
evaluator (`seriesEval`) the theorem is phrased in terms of. The theorem is a bridge
between two objects mathlib does not contain.

---

### Call sites — `seriesEval_formalLog` (Phase 6.0)

Internal use count: **3** (within `PadicLFunctions`, NOT counting the declaring
theorem's own statement) — but note 2 of these are in the *same file*
(`ValuesAtOne.lean`) downstream of the declaration.
External-to-file callers: **3 distinct files' worth of sites across 2 files**
(`ValuesAtOne.lean` further down, and `ResidueZeta.lean`).

| Caller file:line                | Usage pattern (one-line excerpt)                                                  |
|---------------------------------|-----------------------------------------------------------------------------------|
| `ValuesAtOne.lean:523`          | `…, ← seriesEval, seriesEval_formalLog (p := p) hzp1', h1z]` (in `padicLog_pow_p_of_norm_lt_one`) |
| `ValuesAtOne.lean:525`          | `seriesEval_formalLog (p := p) hz, smul_eq_mul]` (same proof, the `p`-power law)   |
| `ValuesAtOne.lean:1032`         | `rw [← seriesEval_formalLog (p := p) (show ‖…‖<1 …)]` (the `htail` `padicLog`/`formalLog` step in the `logSeriesAt` evaluation) |
| `ResidueZeta.lean:1198`         | `← MeasureR.seriesEval_formalLog (p := p) (z := 1 + seriesEval G z) (…)`           |
| `ResidueZeta.lean:1375`         | `MeasureR.seriesEval_formalLog (p := p) hznorm]`                                   |

Inline-derivation grep (was the equivalent re-derived elsewhere without using
`seriesEval_formalLog`?): **(none)** — every place that needs "evaluate `formalLog`
at `z−1` = `padicLog`" goes through this lemma. No bypassing re-derivation found.

**What this tells us:** **K ≥ 3 internal uses across ≥2 files, with cross-file
consumers (`ResidueZeta.lean`), and no inline re-derivation.** This is a **real API
lemma** — the project genuinely depends on it as the load-bearing formal↔analytic
bridge for the `p`-adic logarithm (it is the engine behind the boundary `p`-power
law `padicLog_pow_p_of_norm_lt_one`, full-ball multiplicativity, and the
`ResidueZeta` value computations). The call-site signal points firmly **toward a
YES-family verdict** on the *mathematics*; it is decidedly **not** dead code or a
bypassed wrapper.

### Composition check (Phase 6)

Can `seriesEval_formalLog` be derived from mathlib in ≤3 chained calls?

Attempt 1: `PowerSeries.aeval_eq_sum (ha := …) (formalLog K) …` to rewrite the tsum
as `aeval`, then identify with `padicLog`.
  - Mathlib decls used: `PowerSeries.aeval_eq_sum`, `PowerSeries.hasSum_aeval`.
  - Result: **fails.** `aeval`/`eval₂` require `HasEval a` + `IsLinearTopology K K`,
    which mathlib does not provide for a normed `ℚ_p`-algebra at a unit-ball
    argument. Even granting it, the *right-hand side* `padicLog p z` is a
    **project-local definition absent from mathlib** — there is no mathlib decl to
    rewrite it to. The equality has a non-mathlib object on each side
    (`seriesEval∘formalLog` on the left, `padicLog` on the right).
  - Notes: this is not a missing-glue situation; the *endpoints* don't exist in
    mathlib.

Attempt 2: any composition `mathlib_call₁ (mathlib_call₂ …)` producing the equality.
  - Result: **fails** — there is no mathlib term of type `… = padicLog p z` because
    `padicLog` is not a mathlib symbol. A "composition" is impossible when the goal's
    own vocabulary is not in mathlib.

Conclusion: **NOT-COMPOSABLE** — but for a reason that is *not* the usual
NO-composable trigger. The theorem is not composable because the objects it relates
(`seriesEval`, `formalLog`, `padicLog`) are absent from mathlib, **not** because
mathlib has the building blocks and we should inline. The honest reading is "mathlib
has neither the statement nor its endpoints", which routes to a YES-family or
BORDERLINE verdict, not to NO-composable.

---

## Verdict: `seriesEval_formalLog`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the identity *is* the textbook definition of the
  `p`-adic logarithm on the open unit ball — unanimous across Washington, Coates–
  Sujatha, Conrad, Wikipedia, recent arXiv. Maximally general, no disagreement.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (0 weakenings; `CharZero`
  already pruned). Modern-idiom (4c): **no** in-place modernisation; the only
  "modern" move (route `seriesEval` through `PowerSeries.aeval`) needs upstream
  `HasEval`/`IsLinearTopology` infrastructure mathlib lacks.
- Mathlib search (Phase 5): **not in mathlib** — and crucially, **neither endpoint**
  (`padicLog`, the analytic `p`-adic log; `seriesEval`, the junk-total evaluator) is
  in mathlib. Mathlib has only the formal half `PowerSeries.log` and a general
  evaluator `PowerSeries.aeval` whose adequacy hypotheses are unmet here.
- Composition check (Phase 6): **NOT-COMPOSABLE**, because the objects related are
  absent from mathlib (not because the building blocks are present).
- Call sites (Phase 6.0): **K ≥ 3, cross-file, no inline re-derivation** — a genuine
  load-bearing API lemma, not dead code.

**Rationale (why BORDERLINE rather than YES-add-as-is or NO-*):**

The mathematics clears every YES bar: the statement is canonical (it is the *defining*
property of `log_p`), maximally general, genuinely used, and absent from mathlib.
Under the verdict rules a clean YES-add-as-is would normally follow. **But** the
theorem is not a stand-alone unit: it is phrased entirely in terms of three
project-local objects mathlib does not have — `padicLog` (mathlib has **no** analytic
`p`-adic/non-archimedean logarithm of any kind), `formalLog` (a re-implementation of
mathlib's existing `PowerSeries.log`), and `seriesEval` (a deliberately hand-rolled
junk-total tsum standing in for mathlib's `PowerSeries.aeval`, whose
`HasEval`/`IsLinearTopology` adequacy is not available for this topology). You cannot
"add `seriesEval_formalLog` as-is" to mathlib: it presupposes a whole analytic
`p`-adic-logarithm API that would have to be designed and upstreamed first, and the
*shape* of that API (Does `seriesEval` survive, or do we instead supply the missing
`HasEval` instance and use `PowerSeries.aeval`? Does `formalLog` survive, or do we
state everything against the existing `PowerSeries.log`? Is `padicLog` the right
spelling, or `Mathlib`-side `padicLog : K → K` with an `Iwasawa` normalisation
lemma?) is a genuine design decision. That decision — and whether the project even
wants to upstream its `p`-adic-log analytic layer at all, versus keeping it
project-local as the L-function machinery it was built for — is exactly the
"mathematical-taste / project-policy / packaging" judgment the skill must defer to a
human. The evidence is complete; the remaining question is one of scope and grain,
not of fact.

This contrasts with the sibling `logSeriesAt` (→ NO-composable: a thin wrapper over
`PowerSeries.log.rescale + C`). Here there is no wrapper to inline and no mathlib
endpoint to inline *to*; the gap is a missing *API*, which is a packaging question,
not a refactor.

**Refactor-actionable bar — numbered questions for the human (≤5):**

1. **Do you want the project's analytic `p`-adic logarithm layer (`padicLog`,
   its convergence/summability, this formal↔analytic bridge, and the multiplicativity
   / `p`-power-law lemmas) upstreamed to mathlib at all** — or is it intentionally
   project-local infrastructure for the `L_p(θ,1)` computation? (Mathlib currently
   has **no** analytic `p`-adic logarithm, so this would be a genuine, well-motivated
   new contribution — but it is a multi-declaration effort, not this one lemma.)

2. If yes to (1): **should the evaluator be the project's junk-total `seriesEval`, or
   should we instead contribute the missing `HasEval`/`IsLinearTopology` adequacy
   instance for the relevant `ℚ_p`-algebra topology and phrase everything through
   mathlib's existing `PowerSeries.aeval`/`eval₂_eq_tsum`?** (The latter is the
   Bourbaki-2.0 idiom but is a larger infrastructure task; the former matches what
   the project proved.)

3. If yes to (1): **should the formal series be the project's `formalLog`, or
   mathlib's existing `PowerSeries.log`?** They are the same series (coeffs
   `(−1)^{n−1}n⁻¹` = `algebraMap ℚ K ((−1)^{n+1}/n)`). Upstreaming should almost
   certainly restate the bridge against `PowerSeries.log` and **drop `formalLog`** as
   a duplicate — which changes this lemma's statement to
   `seriesEval (PowerSeries.log K) (z−1) = padicLog p z` (or its `aeval` form).

4. Given that this lemma is the *defining identity* of `log_p`, **should the mathlib
   contribution `define` `padicLog` directly by this series** (making the "bridge" a
   `rfl`/definitional unfolding) **rather than defining `padicLog` separately and
   proving the bridge as a theorem?** That design choice determines whether
   `seriesEval_formalLog` even survives as a named theorem upstream.

5. If you do **not** want to upstream the `p`-adic-log layer: confirm we should
   **keep `seriesEval_formalLog` project-local as-is** (it is correct, maximally
   general, sorry-free, and a real load-bearing API lemma with cross-file consumers —
   nothing to change locally).

**Next action:** user answers the questions; re-run `/mathlibable seriesEval_formalLog`
to resolve. Likely outcomes:
  - "Yes, upstream the p-adic-log layer, against `PowerSeries.log`, `padicLog` defined
    by the series" → this lemma becomes part of a **YES-add-as-is** *batch* (the whole
    `padicLog` analytic API), restated against `PowerSeries.log`; proposed location
    `Mathlib/NumberTheory/Padics/Logarithm.lean` (new file) or
    `Mathlib/Analysis/SpecialFunctions/Log/PAdic.lean`. Ship the def + summability +
    this bridge + multiplicativity as one coherent PR series. Run `/generalise` and
    `/cleanup` per decl first.
  - "Keep it project-local" → drop from mathlib consideration; no local change needed.

---

## Next step

User answers the 5 numbered questions above (the core one: *do you want the
project's analytic `p`-adic-logarithm layer upstreamed to mathlib, and against
mathlib's `PowerSeries.log`?*), then re-run `/mathlibable seriesEval_formalLog`. If
the answer is "yes, upstream the layer", the verdict flips to **YES-add-as-is as part
of a `padicLog`-API batch**, restated against `PowerSeries.log`, in a new
`Mathlib/NumberTheory/Padics/Logarithm.lean`. If "keep project-local", drop from
mathlib consideration — the lemma is correct and load-bearing exactly as it stands.
