# `/mathlibable` report — `PadicLFunctions.MeasureR.one_add_mul_derivative_logSeriesAt`

**Final verdict: `BORDERLINE-needs-human`.**

Mode A, full 10-phase workflow, exhaustive 9-channel literature sweep. Build was
**not re-run** (stale/slow per the task note); reasoned from source per the
Phase-0 fallback.

This is the **per-root formal logarithmic-derivative identity** of RJW Theorem
6.1(ii) (TeX 2102–2105):
`∂(logSeriesAt u) = 1 + ((1+T)·u − 1)⁻¹` for `u − 1` a unit, written in the
unfolded form `(1+T)·d/dT(logSeriesAt u) = 1 + Ring.inverse((1+T)·C u − 1)`. It
is the §6.2 building block — used at `ValuesAtOne.lean:268` to assemble
`one_add_mul_derivative_Ftilde` (the §6.2 analog of RJW Lemma 7.3, exactly as
`FtildeA`'s version assembles in the pure-`p`-power §7 file). The identity is
true, non-trivial (≈60-line proof leaning on two project-private helpers), and
absent from mathlib: mathlib has `PowerSeries.deriv_log` (`d/dX log(1+X) =
1/(1+X)`) but **no** `(1+T)d/dT` logarithmic-derivative operator and **no**
log-derivative-of-affine-argument lemma. But it is **constitutively about** the
project-local definition `logSeriesAt`, which a prior `/mathlibable` run placed
at `NO-composable-from-mathlib` (it is `C(extLog) + (PowerSeries.log K).rescale`),
and a theorem can only be upstreamed once the def it mentions has a mathlib home
and name. So — exactly like its directly-analogous sibling
`PadicLFunctions.one_add_mul_derivative_FtildeA` (also `BORDERLINE-needs-human`)
— the mathlib-worthiness is a packaging/timing judgment downstream of whether the
whole §6.2 Leopoldt-value tower is upstreamed at all. That call belongs to the
maintainer, not the search. Numbered questions in Phase 7.

---

### Baseline (Phase 0)
- lake build:               **build not re-run** (stale/slow per task note) — **reasoned from source**
- decl `PadicLFunctions.MeasureR.one_add_mul_derivative_logSeriesAt`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:155`
- kind:                      `theorem`
- has sorry:                 **no** (`grep -cE '\bsorry\b|\badmit\b'` over `ValuesAtOne.lean` = 0; the file is sorry-free)
- module docstring summary:  "The p-adic value `L_p(θ,1)` (RJW §6.2, Thm 6.1(ii), decomposition P6)" — the
  distribution-free computation of Leopoldt's value `L_p(θ,1)` via the explicit antiderivative `F̃_θ`.

---

### Statement (Phase 1)

`PadicLFunctions.MeasureR.one_add_mul_derivative_logSeriesAt` is **a theorem**
stating the following.

Let `p` be prime and `K` a normed `ℚ_p`-algebra field of characteristic 0 (the
working field of §5–6). For `u : K` with `u − 1` a unit, the formal power series
`logSeriesAt u ∈ K⟦T⟧` — i.e. `"log((1+T)·u − 1)"`, the per-root logarithmic
series of TeX 2076–2080 — satisfies the **logarithmic-derivative identity**

  (1 + T) · (d/dT) (logSeriesAt u)  =  1 + 1/((1+T)·u − 1),

equivalently `∂(logSeriesAt u) = 1 + ((1+T)u − 1)⁻¹` for the derivation
`∂ := (1+T) d/dT`.

Mathematical sanity check: for `f := (1+T)·u − 1`, the logarithmic derivative of
`log f` under `∂` is `∂(log f) = (1+T)·f′/f = (1+T)·u/((1+T)u − 1)`. Since
`(1+T)·u = ((1+T)u − 1) + 1`, this equals `1 + 1/((1+T)u − 1)` — exactly the
stated RHS. The identity is correct.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime. It enters `logSeriesAt`'s *constant term*
  (`extLog p (u−1)`) only; **it does not appear in this theorem's statement or
  proof** (the constant is annihilated by `derivativeFun`, `derivativeFun_C = 0`).
- `K : Type*`, `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K] [CharZero K]` — declared once for the section. The theorem
  **`omit`s `[IsUltrametricDist K] [CompleteSpace K]`** (see line 148); it uses
  only that `K` is a field with division (for `u/(u−1)`, `(n:K)⁻¹`, `mul_inv_cancel₀`)
  and the `PowerSeries`/`Ring.inverse` API. No `p`-adic / analytic structure is used.
- `u : K` — the per-root argument; in the application `u = ε^c` for a root of unity `ε`.

Hypotheses (Lean side):
- `hu : IsUnit (u − 1)` — needed so the affine factor `C(u−1)` is a unit (the
  geometric factorisation and the `Ring.inverse` identification both require it),
  and so `a := u/(u−1)` is well-defined. Genuine, not over-constraint.

Conclusion (math): the per-root logarithmic-derivative identity
`∂(log((1+T)u−1)) = 1 + 1/((1+T)u−1)` (RJW TeX 2102–2105).

Conclusion (Lean): an equality of `PowerSeries K`:
`(1 + PowerSeries.X) * PowerSeries.derivativeFun (logSeriesAt p K u)
  = 1 + Ring.inverse ((1 + PowerSeries.X) * PowerSeries.C u - 1)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (with a BIG-adjacent flag — same as the sibling).
Reason: it is a *named in-paper* step of RJW Thm 6.1(ii) (the §6.2 per-root
analog of Lemma 7.3), which leans BIG (a result tied to a source). But it is not
named after a person/place, it is not a `## Main results` headline (the headline
is the value `L_p(θ,1)` itself), and it is stated entirely in terms of the
project-internal series `logSeriesAt`. On balance a **specialised helper lemma**,
the building block of `one_add_mul_derivative_Ftilde`.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for the
report's framing only and does not gate which channels Phase 3 runs.)

### One-line check (Phase 2b)

Body line count: ≈60 substantive lines (a multi-step formal-calculus argument:
affine factorisation → geometric inversion → `Ring.inverse` identification →
coefficient match by cases with `linear_combination`).
One-liner verdict: **n/a** — kind is `theorem`, not `def`. (Skipped.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | `"logarithmic derivative of log(1+X)" formal power series (1+T) d/dT identity 1/(1+X) geometric series` | yes  | `d/dX log(1+X) = Σ(−1)ⁿXⁿ = 1/(1+X)`; the formal log-derivative is *the* geometric series | proofwiki "Power Series Expansion for Logarithm of 1+x"; scitechnol "Formal Power Series of Logarithms"; the bare `d/dX log` identity is universal. The `(1+T)d/dT` *operator* version is not separately named. |
|  2 | WebSearch (general / context form)| `Iwasawa power series measure derivation "(1+T) d/dT" logarithmic derivative formal power series antiderivative p-adic L-function` | yes  | the derivation `∂ = (1+T)d/dT` and the iso `μ ↦ Φ_μ` to `W[[T]]` with `∫ xᵐ dμ = (t d/dt)ᵐ Φ_μ|_{t=1}` are standard Iwasawa theory | Warwick lecture notes (Williams); Sciencedirect "Derivative of power series attached to Γ-transform of p-adic measures"; arXiv math/0512015; arXiv 0709.2838 (Leopoldt transform of a power series). The *specific* per-root `∂log((1+T)u−1)` is an in-proof step, not a packaged theorem. |
|  3 | WebSearch (named-source / aliases)| `Rodrigues Jacinto Williams "introduction to p-adic L-functions" arXiv 2309.15692 Leopoldt L_p(theta,1) cyclotomic units logarithm` | yes  | confirms RJW = Rodrigues Jacinto & Williams, arXiv:2309.15692; Kubota–Leopoldt `L_p`, measure-theoretic + Coleman (cyclotomic-unit) + Iwasawa constructions | the file `ValuesAtOne.lean` formalises Thm 6.1(ii) of this paper; `Essential Number Theory` v4(1) published version, MSP |
|  4 | ChatGPT MCP                      | (intended: "standard form / generality / historical evolution of the formal `∂log((1+T)u−1)` identity") | **n/a** | — | The `chatgpt-math` MCP server is **configured but unauthenticated** on this machine (`~/.claude/mcp-needs-auth-cache.json` lists `plugin:mathlib-quality:chatgpt-math`; no live `mcp__*chatgpt*` tool is exposed this session). Recorded `n/a` with reason, consistent with the sibling reports. Its role — pinning the standard form, generality, and history — was re-routed through channels 1–3, 6, 9 (universal `log` series; standard Iwasawa `∂`; Leopoldt 1964 → RJW exposition). |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` for "log"/"derivative" | **n/a** | (no references dir; no `refs/` store) | `.mathlib-quality/references/` is **absent** and the `refs/` symlink is **not present** in this checkout — recorded `n/a` per Phase-0 fallback. |
|  6 | nLab                             | `logarithmic derivative formal power series f'/f; logarithm in nLab; derivative in nLab` | yes  | nLab "logarithm" + "derivative": the formal-derivative product rule `(FG)′ = F′G + FG′`; the *logarithmic derivative* `f′/f` notion (cotangent = log-deriv of sine; β-function = log-deriv of coupling) | ncatlab.org/nlab/show/logarithm, /derivative, /Taylor+series. nLab has the *generic* log-derivative concept, **no** named "log-derivative of a shifted-unit power series" object. |
|  7 | nCatLab (if categorical)         | —                                                                                                      | **n/a** | — | Not a categorical concept — it is a concrete formal-power-series calculus identity. No higher-categorical generalisation applies. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | **n/a** | — | Not an algebraic-geometry concept (analytic NT / Iwasawa theory; no schemes/sheaves/sites). |
|  9 | MathOverflow / Math.StackExchange| (covered via the WebSearch hits) — `"log((1+T)u" formal logarithm shifted unit p-adic L-function value s=1 Dirichlet derivative` | partial | confirms shifted-unit log appears in `L_p` functional equations (Pollack half-logs, `log_p^+(T)`); the precise `∂log((1+T)u−1)` is routine manipulation | results surfaced via channel-9 web query (arXiv 1907.06437 p-adic-log image; MIT exp/log-in-p-adic-fields notes; arXiv math/0512015). No standalone named lemma. |
| 10 | recent arXiv (last 5 years)      | `Derivative of power series attached to Γ-transform of p-adic measures`; `Dirichlet-series expansions of p-adic L-functions` | yes  | confirms the `(t d/dt)`-style derivation of measure power series is applied ad hoc per paper; no reusable "per-root log-derivative" theorem | Sciencedirect Γ-transform-derivative paper; arXiv 2401.06100 (special values + λ-invariants). Same classical machinery. |

The protocol passed: WebSearch ran 4 distinct queries at three generality levels
(specific `d/dX log(1+X)` form / the most-general `(1+T)d/dT` Iwasawa-derivation
form / the named-source RJW form), plus a channel-9 query; ChatGPT MCP recorded
`n/a` with a concrete reason (configured-but-unauthenticated) and its questions
re-routed; local references recorded `n/a` (absent); nLab checked (hit on the
generic log-derivative notion); nCatLab / Stacks recorded `n/a` with reasons;
MathOverflow/arXiv checked (hits). Attempt to read the RJW PDF §6.2 verbatim
(`WebFetch https://arxiv.org/pdf/2309.15692`) **failed** — the arXiv PDF is
flate-compressed and not machine-readable through WebFetch; the source grounding
instead rests on (a) the file's verbatim TeX line reference (2102–2105) in the
theorem docstring, and (b) the sibling `one_add_mul_derivative_FtildeA` report,
which read the same paper and pinned the analogous `∂F̃_a = F_a` (Lemma 7.3).

### Literature summary (Phase 3)

Concept identified as: the **formal logarithmic derivative** of `log((1+T)u−1)`
under the standard Iwasawa derivation `∂ = (1+T) d/dT`. The underlying ingredients
are all classical and universal — `d/dX log(1+X) = 1/(1+X)` (nLab, proofwiki) and
the `(1+T)d/dT` measure derivation (Iwasawa, Amice; Warwick/Williams notes;
math/0512015) — but the *packaged per-root identity* `∂log((1+T)u−1) =
1 + 1/((1+T)u−1)` is a **derivation step inside one computation** (RJW Thm
6.1(ii), §6.2, TeX 2102–2105), not a separately-named mathematical object.

Sources agree on the standard form: **yes** — the formal `log` series and its
derivative are universal; the `(1+T)d/dT` derivation is the standard Iwasawa
operator. The specific per-root identity has exactly one source (the paper being
formalised), and the Lean form matches it (the unfolded `(1+T)·derivativeFun`
spelling of `∂`).

Most general standard form: the identity is **not** a general theorem — it is the
log-derivative of one specific shifted-unit series `log((1+T)u−1)`. The generality
lives in the *coefficient ring* (any char-0 field; the project already drops the
analytic instances via `omit`) and in the *derivation API*, not in the statement.

Generality dimensions where the literature varies:
  - **Coefficient field**: from "char-0 field" to "ℚ-algebra". The proof uses only
    division in `K` (`u/(u−1)`, `(n:K)⁻¹`); RJW works over `ℂ_p`, the project over
    abstract `K`. Already maximally general for what it states.
  - **The derivation `∂ = (1+T)d/dT`**: a fixed, standard operator — no variation.

Disagreement with the literature: **none**. The Lean statement is the standard
formal log-derivative identity, faithfully realised; it is simply not a
*standalone* mathlib-shaped object — it is a property *of* the project-local
`logSeriesAt`.

If the literature search had returned nothing this would itself be a NO/BORDERLINE
signal; it did not — the surrounding mathematics is entirely standard, which is
precisely why the question is "right unit + right time", not "is it real".

---

### Generality analysis — `PadicLFunctions.MeasureR.one_add_mul_derivative_logSeriesAt`

Literature-standard form (from Phase 3): `∂log((1+T)u−1) = 1 + 1/((1+T)u−1)` for
`u−1` a unit, over a char-0 field; `∂ = (1+T)d/dT`.

| # | Parameter / hypothesis            | Current Lean form                          | Literature-standard form       | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|--------------------------------------------|--------------------------------|---------------------|----------------------------------|
| 1 | `K` (coefficient field)           | normed `ℚ_p`-algebra field, `CharZero` (analytic instances **already `omit`ted**) | char-0 field / ℚ-algebra      | already near-maximal | The theorem already `omit`s `[IsUltrametricDist K] [CompleteSpace K]`; the proof uses only field division + `PowerSeries`/`Ring.inverse` API. In principle the *statement* could live over any char-0 field, but it is stated about `logSeriesAt p K u`, which is intrinsically `ℚ_p`-tied via its `extLog` constant — so the object cannot be detached from the `p`-adic setting without first restating it about a mathlib log-derivative-of-affine series. That restatement is the Phase-6 composition question, not a typeclass weakening. |
| 2 | `hu : IsUnit (u − 1)`             | `u − 1` a unit                             | `u − 1 ≠ 0` (in a field, same) | NO (meaningfully)   | Essential: without it `C(u−1)` is not a unit, the geometric factorisation `(1+T)u−1 = C(u−1)(1+C a·X)` and the `Ring.inverse` identification both fail, and the RHS `Ring.inverse((1+T)u−1)` is junk (`Ring.inverse` of a non-unit constant-coefficient series). Genuine mathematical hypothesis. |
| 3 | the derivation `(1+T)·derivativeFun` | `(1+X)*PowerSeries.derivativeFun`        | `∂ = (1+T)d/dT`                | NO                  | Fixed standard operator; nothing to weaken. |

This is the rare case where the project's form is already maximally general for
the identity (analytic instances dropped, abstract `K`), and the one hypothesis
is mathematically necessary. There is no "more general `one_add_mul_derivative_
logSeriesAt`" to aim at; any generalisation move is *restating the object* via
mathlib's log/rescale (Phase 6), not a re-statement at weaker typeclasses.

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for this specific identity — analytic
instances already `omit`ted, abstract `K`, the single hypothesis essential).
Number of weakening opportunities found: **0**.
Proposed restatement (if STRICTLY NARROWER): n/a.
Cost of restatement: n/a.

→ Phase 7 considers YES-add-as-is, the NO buckets, or BORDERLINE; 4c is run below
to check for a modern-idiom flip.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                           | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                 | no       | — | already fully typeclass-driven (`NormedField`, `NormedAlgebra`, `CharZero`); the analytic instances are already `omit`ted |
|  2 | sequences/metric → filters/topological?                                                            | no       | — | a **formal** (algebraic) power-series identity; no convergence/topology in the statement |
|  3 | construct an object → universal-property class?                                                    | no       | — | a stated equation between two given series, not a construction |
|  4 | set-with-closure-predicate → bundled substructure?                                                 | no       | — | no substructure |
|  5 | vector-space/metric/field-specific → weaken typeclass (module/(semi)ring)?                          | **partial** | the generic shape `∂(logOf f) = (1+T)·f′·(f⁻¹)` could live over a `CommRing`/`ℚ`-algebra via mathlib's `PowerSeries.logOf` + `deriv_log` + `derivative_subst` | this is a **real** mathlib-idiom observation — see note below — but it is a *restatement about a mathlib object*, i.e. the Phase-6 composition, not a "ship a generalised `one_add_mul_derivative_logSeriesAt`" |
|  6 | 1-categorical → higher/∞-categorical?                                                               | no       | — | not categorical |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid?                                                    | no       | — | the index is the power-series degree `ℕ`, intrinsic to `PowerSeries` |

```
### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes (row 5) — but it is a RESTATEMENT-ABOUT-A-MATHLIB-OBJECT,
not a generalise-and-re-PR of this theorem.
  - Proposed mathlib-idiomatic restatement: rather than proving an identity about
    the project's `logSeriesAt`, mathlib's contemporary idiom would be a *general*
    lemma about `PowerSeries.logOf` / `PowerSeries.log.rescale`, e.g.
      `(1 + X) * derivativeFun ((log K).rescale a) = (1+X)·a·(1 + C a·X)⁻¹`
    (the rescaled-log derivative), or, more useful, a generic
      `deriv_logOf : d⁄dX A (logOf f) = (d⁄dX A f) * (Ring.inverse f)`  (logarithmic
    derivative of `logOf`), from which the project's identity is a substitution.
  - Cost: MODERATE (a genuinely new general mathlib lemma about `logOf`/`rescale`,
    not a one-liner — see honesty bar).
  - Mathlib downstream this enables: a `deriv_logOf` log-derivative lemma would
    compose with the whole `PowerSeries.log`/`logOf`/`rescale`/`derivative` API
    (`coeff_log`, `deriv_log`, `derivative_subst`, `derivative_pow`,
    `invUnitsSub_mul_sub`) and would be the natural companion to the existing
    `PowerSeries.deriv_log`. Mathlib currently has `deriv_log` (for `log(1+X)`)
    but **no** `logOf`-derivative / log-derivative-of-affine lemma — a real gap.
  - Real mathematical improvement: yes — the contribution-worthy object is the
    *generic* `deriv_logOf`, not this `p`-adic-flavoured per-root specialisation.
```

**Honesty bar.** The modern-idiom move here is *not* "ship a cooler
`one_add_mul_derivative_logSeriesAt`". The genuinely mathlib-worthy artifact this
phase surfaces is a **new general lemma** — the logarithmic derivative of
`PowerSeries.logOf` (`d⁄dX (logOf f) = (d⁄dX f) · f⁻¹`), or the `(1+T)d/dT`
version — which is *not* in mathlib (only `deriv_log` for the bare `log(1+X)` is).
That observation is what feeds the Phase-7 BORDERLINE question (q4): the right
mathlib contribution is the generic `logOf`-derivative lemma, and *this* theorem
becomes its `subst`-specialisation. But proposing that is a real design call
(name, generality, `∂`-operator vs plain `d/dX`), not something the search can
unilaterally pick — hence BORDERLINE, not a self-resolving `YES-but-generalise`.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional
equalities or typeclass-search paths; skipped per the skill's scope rule.

---

### Mathlib search-status: `PadicLFunctions.MeasureR.one_add_mul_derivative_logSeriesAt`

[A] Lean-Finder       `logarithmic derivative power series`, `(1+X) derivative log affine` — **n/a (tool not available this session)**; the relevant facts located by [D]
[B] Loogle            type-pattern `(1 + PowerSeries.X) * PowerSeries.derivativeFun _ = 1 + Ring.inverse _`; `d⁄dX _ (logOf _) = _` — **n/a (no `lean_loogle` tool this session)**; reasoned structurally from [D] reading of `RingTheory/PowerSeries/Log.lean` + `Derivative.lean` + `WellKnown.lean`
[C] LeanSearch        "(1+T) times derivative of log of affine power series equals one plus inverse"; "logarithmic derivative of logOf power series" — **n/a (no `lean_leansearch` tool this session)**; covered by [D]
[D] Grep mathlib src  `deriv_log`/`logOf`/`derivative.*log`/`logarithmic`/`one_add.*derivative`/`invUnitsSub` over `.lake/packages/mathlib/Mathlib/` → **HITs**: `PowerSeries.deriv_log` (`Log.lean:67`, `d⁄dX (log A) = mk (n ↦ (−1)ⁿ)`), `PowerSeries.logOf`/`logOf_eq`/`constantCoeff_logOf` (`Log.lean:82–96`), `PowerSeries.derivativeFun`/`derivative_subst`/`derivative_pow`/Leibniz (`Derivative.lean`), `PowerSeries.invUnitsSub` with `invUnitsSub_mul_sub : invUnitsSub u * (C u − X) = 1` (`WellKnown.lean:38–62`). **NO HIT** for any `(1+T)d/dT` log-derivation operator, any `deriv_logOf`, or any log-derivative-of-affine lemma.
[E] Name pattern      `one_add_mul_derivative`, `logSeriesAt`, `deriv_logOf`, `extLog`/`padicLog`, `*log*deriv*` over mathlib → `one_add_mul_derivative_logSeriesAt`/`logSeriesAt`/`extLog`/`padicLog`/`Ftilde` **all absent**; only the generic `PowerSeries.deriv_log` and the analytic `LogDeriv` (functions, not power series) exist

Searched for both:
  - the user's current form (`(1+X)·∂(logSeriesAt u) = 1 + Ring.inverse((1+X)·C u − 1)`) — **absent**.
  - the literature-standard form (the formal log-derivative `∂log((1+T)u−1)`, and
    the generic `logOf`-derivative) — **absent**: mathlib has `deriv_log` (the
    *bare* `log(1+X)` derivative) but **no** `logOf`/affine version and **no**
    `(1+T)d/dT` operator. The closest building blocks are `deriv_log`,
    `derivative_subst` (chain rule), and `invUnitsSub_mul_sub` (geometric inverse).

What mathlib *does* have (the generic building blocks the proof's spirit uses):
  - `PowerSeries.deriv_log`, `PowerSeries.coeff_log`, `PowerSeries.constantCoeff_log` (`Log.lean`).
  - `PowerSeries.logOf`, `logOf_eq`, `constantCoeff_logOf` (`Log.lean:82–96`) — the affine-substituted log, but **no derivative lemma about it**.
  - `PowerSeries.derivativeFun`, `derivative_subst`, `derivative_pow`, the Leibniz rule, `derivativeFun_C = 0` (`Derivative.lean`).
  - `PowerSeries.invUnitsSub` + `invUnitsSub_mul_sub : invUnitsSub u * (C u − X) = 1` and `invUnitsSub_mul_X` (`WellKnown.lean`) — the geometric inverse of an affine series, but in the `(u − X)` form, not the project's `((1+X)u − 1)` form.
  - **Absent**: any `p`-adic log (`extLog`/`padicLog`), any `logSeriesAt`/`Ftilde`, any `(1+T)d/dT` derivation, any `deriv_logOf`.

Concluded: **"not in mathlib"** — neither the user's form nor the
literature-standard formal-log-derivative-of-affine form is present; the exact
identity and the object `logSeriesAt` it is about are both absent. Only the
generic `PowerSeries.log`/`logOf`/`derivative`/`invUnitsSub` API exists (and the
*generic* `deriv_logOf` companion lemma is itself a gap — see Phase 4c).

---

### Call sites — `PadicLFunctions.MeasureR.one_add_mul_derivative_logSeriesAt`

Internal use count: **1** (within the project, not counting the declaring statement).
External-to-file callers: **0 distinct files** (the one use is in the same file `ValuesAtOne.lean`).

| Caller file:line               | Usage pattern (one-line excerpt)                                          |
|--------------------------------|---------------------------------------------------------------------------|
| ValuesAtOne.lean:268           | `one_add_mul_derivative_logSeriesAt hu, mul_add, mul_one]]`                |

That single site is inside `one_add_mul_derivative_Ftilde` (`ValuesAtOne.lean:223`),
where it discharges the per-root term `(1+X)·(C(θ⁻¹ c)·∂(logSeriesAt(ε^c)))` in the
sum that proves `∂F̃_θ = F_θ` (the §6.2 analog of RJW Lemma 7.3, TeX 2100–2110).
I.e. it is the per-root building block; `one_add_mul_derivative_Ftilde` is the
assembled antiderivative identity, exactly mirroring how
`one_add_mul_derivative_FtildeA` (§7) assembles its per-root steps.

Inline-derivation grep (was the equivalent re-derived elsewhere without using it?):
  - **(none)** — no other proof re-derives `(1+X)·∂(logSeriesAt u) = …` inline; the
    `A`-cluster file uses a structurally analogous device through `FtildeA`/`uA`.

**Composability signal (Phase 6.0.1 / 6.0.2):** **K = 1 internal use only, 0
external, no inline re-derivation.** This is the "possibly the wrong abstraction /
could be inlined" pattern — *except* that the proof body is ≈60 lines, so inlining
is not viable (see Phase 6). The signal therefore reads as: a genuine, non-trivial
helper lemma with exactly one consumer because it is the unique per-root step in
one computation. It is real (not dead code, not a bypassed wrapper), but its
audience is a single proof in a single paper-formalisation — the same profile as
the sibling `one_add_mul_derivative_FtildeA` (which was `BORDERLINE`).

---

### Composition check (Phase 6)

Can `one_add_mul_derivative_logSeriesAt` be derived from mathlib in ≤3 chained calls?

**Attempt 1** — chain the generic derivative lemmas directly. Using the
established decomposition `logSeriesAt p K u = C(extLog p (u−1)) + (log K).rescale a`
(`a = u/(u−1)`, from the `logSeriesAt` report) and `derivativeFun_C = 0`:
```lean
-- ∂(logSeriesAt u) = ∂((log K).rescale a)                        -- derivativeFun_C kills the constant
--                  = (1+X)·a·(deriv of (log K) at rescaled pt)   -- chain rule (rescale = subst (a·X))
--                  = ... = 1 + Ring.inverse((1+X)·C u − 1)        -- after affine factorisation + geom inverse
```
  - Mathlib decls available: `derivativeFun_C`, `derivative_subst`/`derivative_pow`,
    `deriv_log`, `invUnitsSub_mul_sub`, `Ring.inverse_mul_cancel`.
  - Result: **fails as a ≤3-call composition.** Assembling the identity needs, in
    order: (i) commute `derivativeFun` past `rescale`/`C`; (ii) apply `deriv_log`
    composed with the rescale (chain rule); (iii) the **affine factorisation**
    `(1+X)·C u − 1 = C(u−1)·(1 + C a·X)` (a non-trivial algebraic rearrangement,
    needing `hu` and `a = u/(u−1)`); (iv) **invert the geometric factor**
    `(1 + C a·X)·(Σ(−a)ⁿ) = 1`; (v) **identify** `Ring.inverse` via uniqueness of
    the inverse; (vi) a **coefficient match by cases** (`n = 0` vs `n+1`) closed
    with `linear_combination`. This is genuine multi-step formal calculus.
  - Notes: the actual proof body is ≈60 lines and uses **two project-private
    helper lemmas** — `ring_inverse_eq_of_mul_eq_one` (uniqueness of `Ring.inverse`)
    and `one_add_C_mul_X_mul_geom` (the geometric inverse `(1+C b·X)·Σ(−b)ⁿ = 1`),
    *neither* of which is a single mathlib call (mathlib's `invUnitsSub_mul_sub` is
    in the `(u − X)` shape, not `(1 + C b·X)`, so it does not drop in directly).

**Attempt 2** — derive from a more general mathlib log-derivative theorem.
  - Result: **fails** — Phase 5 confirms mathlib has **no** `deriv_logOf` / affine
    log-derivative / `(1+T)d/dT` operator. There is nothing to specialise from.

Conclusion: **NOT-COMPOSABLE** (far more than 3 mathlib calls; a real ≈60-line
proof resting on two project-private lemmas and a `Ring.inverse`-uniqueness
coefficient argument). Per the Phase-6 heuristics, multiple `have`s with
non-trivial reasoning between them + a `linear_combination`-closed coefficient
match is *a proof*, not a composition.

---

## Verdict: `PadicLFunctions.MeasureR.one_add_mul_derivative_logSeriesAt`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the **per-root formal logarithmic-derivative
  identity** of RJW Thm 6.1(ii) §6.2 (TeX 2102–2105). The ingredients are all
  classical/universal (`d/dX log(1+X) = 1/(1+X)`, nLab/proofwiki; the `(1+T)d/dT`
  derivation, Iwasawa/Williams notes), but the packaged per-root identity is an
  **in-proof step**, not a separately-named object.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** for this identity (analytic
  instances already `omit`ted, abstract `K`, the one hypothesis essential). Phase
  4c surfaced a *real* mathlib gap — a generic `deriv_logOf` log-derivative lemma —
  but that is a new general contribution, not a generalisation of *this* theorem.
- Mathlib search (Phase 5): **not in mathlib** — neither the identity, nor the
  object `logSeriesAt`, nor any `(1+T)d/dT` / `deriv_logOf` lemma is present; only
  the generic `deriv_log`/`logOf`/`derivative`/`invUnitsSub` API the proof's spirit
  uses (and even the generic `deriv_logOf` companion is a gap).
- Composition check (Phase 6): **NOT-COMPOSABLE** (≈60-line proof on two
  project-private helpers + a `Ring.inverse`-uniqueness coefficient match; K = 1
  internal use, 0 external).

**Rationale (1–2 paragraphs).**

This is not a "is it true and useful" question — it plainly is both — but a "is
this the right *unit* for mathlib, and is now the right time" question, which turns
on facts the search cannot settle. The result is genuinely novel for mathlib and
non-trivial, so it is neither `NO-mathlib-has-it` nor `NO-composable-from-mathlib`;
and it is maximally general for what it states, so the generality gate does not
force a clean `YES-but-generalise-first`. The reason it is **not** a clean
`YES-add-as-is` is that the theorem is *constitutively about* `logSeriesAt`, the
project-local power series whose own `/mathlibable` assessment is
`NO-composable-from-mathlib` (it is `C(extLog p (u−1)) + (PowerSeries.log K).rescale
(u/(u−1))`, i.e. a 2-call composition of `PowerSeries.log`/`rescale`/`C` plus the
project-only Iwasawa-branch `extLog`). A theorem can only be upstreamed once the
*object it mentions* has a mathlib home and name. So the mathlib-worthiness of this
lemma is downstream of, and inseparable from, the upstreaming decision for the §6.2
Leopoldt-value tower (`logSeriesAt`, `Ftilde`, the genuine measure `ρ_θ`, and the
value `L_p(θ,1)` itself) — and from the `extLog`/`padicLog` decision, since that is
the one genuinely-novel ingredient anywhere in this cluster.

This is the **exact analog**, one decomposition level down, of the sibling
`PadicLFunctions.one_add_mul_derivative_FtildeA` — the §7 antiderivative identity
`∂F̃_a = F_a` (RJW Lemma 7.3), which a prior run also placed at
`BORDERLINE-needs-human` for the identical reason (true, non-trivial, absent, but
stated via project-local `FtildeA`/`Fa` whose upstreaming is the human call). The
present theorem is *more* elementary than that one (its RHS is a bare
`Ring.inverse` of an affine series — **no Mahler transform, no `Fa`, no measure
content, and no `extLog` in the statement**, since the constant is killed by the
derivative), and it is the per-root building block of the §6.2 analog
(`one_add_mul_derivative_Ftilde`). Phase 4c additionally identified the *actual*
mathlib contribution this work points at: a **generic `deriv_logOf`** lemma
(logarithmic derivative of `PowerSeries.logOf`), which mathlib lacks — but
proposing and naming that is a design call. With K = 1 internal call site and 0
external consumers, today this is a private step in one paper-formalisation. The
packaging-and-timing call belongs to the maintainer, not the search.

**Numbered questions (≤5):**

1. Is the **§6.2 Leopoldt-value development as a whole** (`logSeriesAt`, `Ftilde`,
   the genuine measure `ρ_θ`, and the value `L_p(θ,1)` of Thm 6.1(ii)) bound for
   upstreaming to mathlib, or is it a standalone AINTLIB formalisation of
   arXiv:2309.15692? (If standalone → drop this lemma from mathlib consideration;
   it is correctly project-local, an in-proof step of Thm 6.1(ii).)
2. If yes to (1): should the base object `logSeriesAt` (and `extLog`/`padicLog`,
   the one genuinely-novel ingredient) be upstreamed first under mathlib-canonical
   names, at which point this lemma ships *with* them as `YES-add-as-is`? (Mathlib
   currently has **no** `p`-adic logarithm at all — that is the real headline gap.)
3. Independent of (1)/(2): would you like the **generic `deriv_logOf`** lemma —
   the logarithmic derivative of `PowerSeries.logOf` (`d⁄dX (logOf f) = (d⁄dX f) ·
   Ring.inverse f`), or its `(1+T)d/dT` form — proposed to mathlib as a standalone
   companion to the existing `PowerSeries.deriv_log`? It is a real gap (Phase 5),
   and *this* theorem would become its `subst`-specialisation. (A "yes" makes the
   mathlib contribution the generic lemma, not this `p`-adic per-root form.)
4. For any upstreamed version, keep the `(1+T)·derivativeFun` spelling, or repackage
   behind a *named* `∂ = (1+T)d/dT` derivation (RJW's `∂`) so the API reads
   `∂(log f) = 1 + 1/f`? (A named `∂` would be reusable formal-NT infrastructure,
   shared with the §7 `FtildeA` cluster.)
5. Is the abstract coefficient field `K` the form mathlib should carry, or should
   any upstreamed version be pinned to `ℂ_p` to match RJW and a future
   p-adic-L-function API?

**Next action:** user answers the questions; re-run
`/mathlibable PadicLFunctions.MeasureR.one_add_mul_derivative_logSeriesAt` to
resolve the verdict. Likely outcomes based on the answers:
  - **(1) standalone / project-local** → drop from mathlib consideration; keep as
    the project lemma it is (the per-root step of RJW Thm 6.1(ii)), no rename needed.
  - **(1) yes-upstream + (2) base objects first** → flips to **`YES-add-as-is`**,
    shipped in the same PR series as `logSeriesAt`/`extLog`/`Ftilde` under a mathlib
    namespace (proposed home: `Mathlib/NumberTheory/Padics/LFunction/...`, a
    directory that does not yet exist — itself confirming the area is the real gap).
  - **(3) yes** → the mathlib contribution becomes the **generic `deriv_logOf`**
    lemma (`Mathlib/RingTheory/PowerSeries/Log.lean`, next to `deriv_log`), and this
    `p`-adic theorem stays a project-local specialisation that calls it.

---

## Next step

User answers the five Phase-7 questions; re-run
`/mathlibable PadicLFunctions.MeasureR.one_add_mul_derivative_logSeriesAt`. The
pivotal question is (1): whether the §6.2 Leopoldt-value tower is bound for mathlib
at all. A "no" keeps this correctly project-local (it is an in-proof step of RJW
Thm 6.1(ii), used once at `ValuesAtOne.lean:268` to assemble
`one_add_mul_derivative_Ftilde`). A "yes (base defs first)" flips it to
`YES-add-as-is` alongside `logSeriesAt`/`extLog`. Orthogonally, question (3) offers
the cleanest standalone win: contribute the **generic `deriv_logOf`** log-derivative
lemma to `Mathlib/RingTheory/PowerSeries/Log.lean` (mathlib has `deriv_log` but no
`logOf`/affine version), of which this theorem is a specialisation. This verdict
matches the directly-analogous sibling `one_add_mul_derivative_FtildeA`
(also `BORDERLINE-needs-human`).
