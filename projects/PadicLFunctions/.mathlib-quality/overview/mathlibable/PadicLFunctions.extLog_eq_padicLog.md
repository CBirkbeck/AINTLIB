# `/mathlibable` report — `PadicLFunctions.extLog_eq_padicLog`

Mode A — full 10-phase workflow with the exhaustive 9-channel literature search.

## Baseline (Phase 0)

- lake build:               build not re-run (stale/slow per task note); **reasoned from source** — Phase-0 fallback. The decl and all its dependencies (`extLog`, `extLog_eq_of_witness`, `padicLog`, `InExpBall`, `ExtLogDomain`) were read directly from source and elaborate consistently.
- decl `PadicLFunctions.extLog_eq_padicLog`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:351`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  the extended (Iwasawa-branch) p-adic logarithm `extLog` (RJW §6 / Washington §5.1), which extends `padicLog` from the convergence ball to the rational-valuation domain `x^m = p^k·y` via `extLog x := m⁻¹·padicLog y`, junk-0 off domain.

---

## Statement (Phase 1)

`PadicLFunctions.extLog_eq_padicLog` is a theorem stating the following:

Let `L` be a complete ultrametric normed field that is a normed `ℚ_p`-algebra. The **extended (Iwasawa-branch) p-adic logarithm** `extLog` — defined on the rational-valuation domain and equal to `m⁻¹·log_p y` for a witness `x^m = p^k·y` — **agrees with the ordinary convergent power-series p-adic logarithm `padicLog`** on the open exponential ball: for every `x` with `‖x−1‖^{p−1} < p⁻¹` (i.e. `x` in the ball where the power series already converges), `extLog p x = padicLog p x`.

Mathematically this is the **consistency / base-case property** of the Iwasawa extension: the extension restricts to the original logarithm wherever the original is already defined. In the standard factoring `w = p^r·ζ·z` with `|z−1| < 1` and `log_p w := log_p z`, the case `w = z` in the ball gives `log_p w = log_p z` — i.e. the extension *is* the power series there. This is exactly what makes "extended log" an honest extension.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic / prime.
- `L : Type*`, `[NormedField L]`, `[NormedAlgebra ℚ_[p] L]`, `[IsUltrametricDist L]`, `[CompleteSpace L]` — a complete ultrametric normed field extension of `ℚ_p`.
- `x : L` — the point at which both logarithms are evaluated.

Hypotheses (Lean side):
- `(hx : InExpBall p (x - 1))` — i.e. `‖x−1‖^{p−1} < p⁻¹`, membership of `x−1` in the open convergence ball of the p-adic exp/log.

Conclusion (math): on the convergence ball, the extended logarithm equals the convergent power-series logarithm.

Conclusion (Lean): `extLog p x = padicLog p x`.

Proof body (1 line): apply `extLog_eq_of_witness` with the trivial witness `m = 1, k = 0, y = x` (since `x^1 = p^0 · x = x`), giving `extLog p x = (1:ℚ_[p])⁻¹ • padicLog p x`, then `Nat.cast_one, inv_one, one_smul` collapse the scalar to give `padicLog p x`.

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: it is a consistency/glue lemma between two definitions (`extLog`, `padicLog`), with a one-line proof; it is not a named theorem, not a new structure, and not a top-level "Main result" (it is plumbing W6a-a8 that supports the genuinely-big object `extLog`).

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only and does not gate which channels Phase 3 runs — all nine were run.)

## One-line check (Phase 2b)

Kind is **theorem**, not a `def`/`abbrev`/`structure`. One-liner check is **n/a** (the one-line-def negative signal applies only to definitions; this is a propositional lemma). The proof being one line is recorded under Phase 1; it informs the composition analysis (Phase 6), not a def-one-liner exemption.

---

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic logarithm Iwasawa branch extended to all nonzero elements log p = 0 definition"                | yes  | Iwasawa log on `C_p^×`; `w=p^r·ζ·z ↦ log_p z`, `log_p p = 0`; restricts to power series on the ball | arXiv 1907.06437; MIT 18.785 PS10; arXiv math/0512015 — extension is *defined by* agreeing with the series where `|z−1|<1` |
|  2 | WebSearch (general form)         | "p-adic logarithm agrees with power series on convergence ball extension Iwasawa"                       | yes  | series `∑(−1)^{n−1}xⁿ/n` on the convergence ball; Iwasawa extends to `p^ℤ(1+m_{C_p})` "maintaining consistency with the power-series definition on the original domain" | Warwick p-adic L-functions notes; arXiv 1005.4152 — the consistency-on-the-ball property is the named hallmark of the extension |
|  3 | WebSearch (named-after / aliases)| "Iwasawa logarithm restricts to standard p-adic logarithm on 1 + maximal ideal consistency Washington cyclotomic fields" | yes  | `L(x)=∑(−1)^{n−1}xⁿ/n` is an isometry `{‖x‖<p^{−1/(p−1)}} → 1+(…)`; Iwasawa log on principal units | arXiv 1904.09850 (image of p-adic log on principal units); Hida ELEMENTARY IWASAWA THEORY; matches Washington §5.1 (the docstring's own cite) |
|  4 | ChatGPT MCP                      | (intended: "standard def of the extended/Iwasawa p-adic log, its generality, and that it agrees with the convergent series on the ball; historical evolution") | n/a  | —                                | **ChatGPT MCP not configured in this environment** (no `chatgpt`/`openai` MCP tool in the deferred-tool list; `~/.claude/mcp-needs-auth-cache.json` only). Compensated by 6 WebSearch queries (3 generality levels) + PlanetMath + the cited Washington §5.1. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`               | n/a  | (no references dir; no `refs` symlink) | both absent — recorded n/a per protocol. The module docstring cites Washington, *Introduction to Cyclotomic Fields*, §5.1 and RJW Thm 6.1(ii) as the construction sources. |
|  6 | nLab                             | `p-adic logarithm` page                                                                                 | n/a  | (no dedicated page; HTTP 404)    | nLab has no `p-adic logarithm` entry; the abstract Iwasawa-log statement is not catalogued there |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                | not a categorical concept (an analytic function on a valued field); no universal-property framing in the literature |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | —                                | not an algebraic-geometry concept (p-adic analysis, not schemes/sheaves) |
|  9 | MathOverflow / Math.StackExchange| "Iwasawa logarithm restricts to … on 1 + maximal ideal" (folded into #3)                               | yes  | confirms the convergent-series-on-the-ball / Iwasawa-extension split is textbook | surfaced via #3; same standard form, no dissent |
| 10 | recent arXiv (last 5 years)      | "p-adic logarithm complete nonarchimedean field … arbitrary complete valued field" (#5 query)          | yes  | extension stated over `C_p` / complete nonarchimedean char-0 fields, **not** restricted to `ℚ_p`-algebras | arXiv 2507.21801 (perfectoid/Iwasawa); PlanetMath "p-adic exp and log"; confirms the char-0-field generality |

The protocol passed: WebSearch ran 6 distinct queries across 3 generality levels (specific / most-general / named-after-aliases); local refs checked (absent → n/a); nLab checked (404); Stacks / nCatLab recorded n/a with reasons; MathOverflow and recent arXiv each returned hits. The single unmet mandatory channel is **ChatGPT MCP (not configured)**, recorded n/a with the over-compensation noted.

### Literature summary (Phase 3)

Concept identified as: the **agreement / consistency property of the (Iwasawa-branch) p-adic logarithm** — "the extended `log_p` restricts to the convergent power-series `log_p` on the open convergence ball." The base object is `log_p`; the lemma is its compatibility with the Iwasawa extension `extLog`.

Sources agree on the standard form: **yes**. Every source (Wikipedia/MIT/arXiv/PlanetMath/Washington) builds the extension *by declaring it to agree with the convergent series where `|x−1|<1`* and `log_p p = 0`. The agreement-on-the-ball statement is not a curiosity — it is the *definition* of the extension being an extension.

Most general standard form: for `x` in the convergence ball `‖x−1‖ < 1` of a complete nonarchimedean **char-0** field `K` (e.g. `C_p`, finite extensions of `ℚ_p`), the Iwasawa/extended logarithm equals the convergent power series `∑_{n≥1}(−1)^{n+1}(x−1)ⁿ/n`.

Generality dimensions where the literature varies:
- **Ball used**: the standard convergence ball is the *full* `‖x−1‖ < 1` (where the log series converges nonarchimedeanly). The *exp* ball `‖x−1‖^{p−1} < p⁻¹` (the target's `InExpBall` hypothesis) is the strictly smaller ball where exp also converges / the log is an isometry. The agreement statement is standardly given on the full log ball; the target restricts to the smaller exp ball.
- **Base field**: literature states it over arbitrary complete nonarchimedean char-0 fields (`C_p`, finite extensions), taking the rational coefficients `1/n` in the field itself — never restricting to `ℚ_p`-*algebras* with the coefficients pulled from `ℚ_p`.

Disagreement with the literature: none on the mathematical content; the target is a correct (narrower) instance of the standard consistency property.

---

## Generality analysis — `PadicLFunctions.extLog_eq_padicLog`

Literature-standard form (from Phase 3): for `x` with `‖x−1‖ < 1` in a complete ultrametric **char-0** field `K`, `extLog p x = padicLog p x` (the extended log restricts to the convergent series on the full log ball).

| # | Parameter / hypothesis            | Current Lean form                         | Literature-standard form                      | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|-------------------------------------------|-----------------------------------------------|---------------------|---------------------------------|
| 1 | `[NormedAlgebra ℚ_[p] L]`         | normed `ℚ_p`-algebra; coeffs `1/n ∈ ℚ_p`  | complete nonarchimedean **char-0** field; `1/n ∈ K` | **yes**             | inherited verbatim from `padicLog`/`extLog`: the series needs only `CharZero K`; `ℚ_p`-algebra is redundant. (Sibling reports `padicLog.md`/`extLog.md` both flag this exact weakening.) |
| 2 | `(hx : InExpBall p (x − 1))` i.e. `‖x−1‖^{p−1} < p⁻¹` | the **exp** ball (strictly smaller)        | the **full log** ball `‖x−1‖ < 1`             | **yes**             | the agreement holds on all of `‖x−1‖<1` (both sides are the convergent series there); the exp ball is an artificial restriction. **The project itself already proves the full-ball version** as `MeasureR.extLog_eq_padicLog_of_norm_lt_one` (`ValuesAtOne.lean:590`). |
| 3 | `[IsUltrametricDist L] [CompleteSpace L]` | ultrametric + complete                      | same (needed for nonarchimedean summation)    | NO                  | essential — the log series only sums in a complete nonarchimedean field |
| 4 | `[Fact p.Prime]`                  | `p` prime                                  | `p` prime                                     | NO                  | essential — `p`-adic object |

This is `/generalise`'s mechanical pass with a literature-grounded target: the standard form is the full-log-ball, `CharZero`-field statement.

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: **2** (rows 1 and 2)

Proposed restatement (full log ball + char-0 field; matches the existing project sibling):

```lean
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

/-- The extended (Iwasawa-branch) p-adic logarithm agrees with the convergent
power-series logarithm on the whole open unit ball `‖x − 1‖ < 1`. -/
theorem extLog_eq_padicLog {x : K} (hx : ‖x - 1‖ < 1) :
    extLog p x = padicLog p x := by
  sorry  -- = the existing `extLog_eq_padicLog_of_norm_lt_one`, stated on the generalised defs
```

Cost of restatement: **MODERATE** — the *statement* widening is mechanical, but it rides on the prior generalisation of `extLog` and `padicLog` themselves (both `YES-but-generalise-first`), and on having `extLog_eq_of_witness` / the `p`-power witness laws on the wider `CharZero`-field / full-log-ball setting. Cost does **not** downgrade the verdict (mathlib values the right form).

Because Phase 4b is STRICTLY NARROWER, Phase 7 considers **YES-but-generalise-first** prominently.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                   | Applies? | Proposed reformulation                                                              | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------------|----------|-------------------------------------------------------------------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                         | partly   | replace `[NormedAlgebra ℚ_[p] L]` with `[CharZero K]` (row-1 weakening)              | unifies `ℚ_p` / `C_p` / finite-extension instances under one statement |
|  2 | sequences/metric where filters/topological would generalise?                                               | no       | the hypothesis is a single ball-membership inequality; nothing to filter-ise        | — |
|  3 | constructs an object where a universal-property class would characterise it?                                | no       | this is an equation between two already-defined functions; no construction to bundle | (the *parent* `extLog` could be a `MonoidHom` per `extLog.md`; this agreement lemma would then read as "the hom restricts to the series" — but that is the parent's modernisation, not this lemma's) |
|  4 | set-with-closure-predicate → bundled substructure?                                                          | no       | `InExpBall` / `‖x−1‖<1` is a one-off ball predicate, not a substructure lattice      | — |
|  5 | vector-space/metric/field-specific result mathlib's typeclasses would weaken?                               | yes      | drop `ℚ_p`-algebra → complete nonarchimedean `CharZero` field (= row 1)             | scalar-tower-free; the agreement lemma applies to every such field at once |
|  6 | 1-categorical statement with a higher-categorical generalisation?                                           | no       | a scalar equation; no categorification target                                       | — |
|  7 | concrete index (ℕ/ℤ/ℝ) generalising to arbitrary additive/ordered structures?                              | no       | the only "index" is the prime `p`, which must stay `p : ℕ` prime                     | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**, but it is the **same direction** as the literature-weakening (rows 1 + 5 coincide: `ℚ_p`-algebra → `CharZero` field; widen to the full log ball). There is no *separate* modern reformulation of this agreement lemma — its modernisation is exactly to be restated against the already-modernised `extLog`/`padicLog`.
- Proposed mathlib-idiomatic restatement: as in Phase 4b (full log ball, `CharZero` field).
- Cost: **MODERATE** (sequenced behind the parent-def generalisations).
- Mathlib downstream this enables: the single agreement lemma serves `ℚ_p`, finite extensions, and `C_p` uniformly; it is the consistency glue that lets every `padicLog` lemma (multiplicativity, `p`-power law, isometry) transport to the extended `extLog` over the whole rational-valuation domain.
- Real mathematical improvement: removes a redundant scalar-algebra restriction and states the agreement on the function's true convergence ball `‖x−1‖<1` rather than the artificially small exp ball — eliminating the need for the *separate* full-ball lemma the project currently maintains (`extLog_eq_padicLog_of_norm_lt_one`).

Honesty bar: the improvement is a genuine organisational one (one statement instead of two ball-specific ones; one field hypothesis instead of a redundant algebra tower), not "looks cooler".

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **theorem** (a proposition introduces no definitional equalities or typeclass-search paths). Skipped per scope.

---

## Mathlib search-status: `PadicLFunctions.extLog_eq_padicLog`

[A] Lean-Finder       "p-adic logarithm extension agrees power series ball"   n/a: endpoint not reachable from here; covered by [C] natural-language attempt + [D] authoritative source grep
[B] Loogle            `padicLog` (name); `Padic, Real.log` (type+name)        **no hits** — Loogle returns `unknown identifier 'padicLog'` (the constant does not exist in mathlib); `Padic, Real.log` → "Found 0 declarations"
[C] LeanSearch        "p-adic logarithm agrees with power series on convergence ball"  n/a: API endpoint returned 404 (moved); compensated by [B] + [D]
[D] Grep mathlib src  `padicLog` / `pAdicLog` / `adicLog` over `.lake/packages/mathlib/Mathlib/`; `def .*[Ll]og` in `Mathlib/NumberTheory/Padics/`; `iwasawa.*log` | all **no hits** — `Mathlib/NumberTheory/Padics/` has no logarithm of any kind; the only `log` defs in `NumberTheory/` are `VonMangoldt.log`, `logHeight`, `logEmbedding`, `eulerMascheroniSeq` (all unrelated, archimedean/discrete)
[E] Name pattern      grep for `extLog`, `ExtLogDomain`, `InExpBall`, `padicExp` in mathlib src   **no hits** — none of these names exist in mathlib

Searched for both:
  - the user's current form (`extLog = padicLog` on the exp ball) — nothing, because neither `extLog` nor `padicLog` exists in mathlib.
  - the literature-standard form (agreement on `‖x−1‖<1` over a `CharZero` field) — also nothing; mathlib has **no nonarchimedean analytic logarithm at all** (only the *formal* `PowerSeries.log` and the *archimedean* `Real.log` / `Complex.log` / `NormedSpace.exp`).

Concluded: **not in mathlib** (all methods exhausted — Loogle name + type, full mathlib-source grep, name patterns — plus the literature-standard form). The agreement lemma cannot exist in mathlib because the two objects it relates are themselves absent from mathlib.

---

## Call sites — `PadicLFunctions.extLog_eq_padicLog`

Internal use count: **2** (within the project, excluding the declaring line `ExtLog.lean:351`)
External-to-file callers: **1 distinct file** (`ResidueZeta.lean`); plus 1 same-file caller (`ExtLog.lean`)

| Caller file:line                | Usage pattern (one-line excerpt)                                                        |
|---------------------------------|-----------------------------------------------------------------------------------------|
| ExtLog.lean:420                 | `extLog_eq_padicLog p (inExpBall_one_sub_one p), padicLog_one]` (base case of `extLog_prod`) |
| ResidueZeta.lean:1768           | `extLog_eq_padicLog p hanball, ← pZpLog_coe p hp2 (PadicInt.angleUnit_sub_one_mem p u)]`     |

Related (a strictly more general sibling, NOT this decl): `MeasureR.extLog_eq_padicLog_of_norm_lt_one` (`ValuesAtOne.lean:590`) proves the *same agreement on the full ball* `‖x−1‖<1`, and is itself used at `ResidueZeta.lean:1377` and `ValuesAtOne.lean:1083`. This is the project's own evidence that the full-ball form is the one wanted.

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?): the full-ball version is *separately stated* (not inline-re-derived) as `extLog_eq_padicLog_of_norm_lt_one` — i.e. the project maintains two agreement lemmas (exp ball + full ball) precisely because the def is currently keyed to the smaller ball. Generalising the def collapses these two into one.

Call-sites signal: **K = 2 internal uses, no inline re-derivation** → a real (if small) piece of API that consumers depend on. Combined with the existence of a more-general sibling, this leans toward a **YES-\*** bucket (it is genuine content), with the generalisation being the obvious next move.

---

## Composition check (Phase 6)

Can `extLog_eq_padicLog` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: the actual proof — `extLog_eq_of_witness p one_pos (witness m=1,k=0,y=x) hx` then collapse `1⁻¹ • · = ·`.
  - Mathlib decls used: `one_pos`, `Nat.cast_one`, `inv_one`, `one_smul`, `pow_one`, `zpow_zero`, `one_mul` (all mathlib) — **but the load-bearing step is `extLog_eq_of_witness`, a PROJECT decl, not mathlib.**
  - Result: **fails as a mathlib composition.** The "1-line proof" is a composition on `extLog_eq_of_witness`, which is itself a project theorem built on the project-only `extLog` def. Mathlib has neither `extLog`, `padicLog`, nor `extLog_eq_of_witness`.
  - Notes: there is nothing in mathlib to inline this into — you cannot replace the call site with a mathlib expression, because the very objects (`extLog`, `padicLog`) do not exist in mathlib.

Attempt 2 (different angle): could the agreement be obtained from a mathlib general logarithm specialised? — no: there is no mathlib nonarchimedean log to specialise (Phase 5).

Conclusion: **NOT-COMPOSABLE (from mathlib).** Within the project it is a thin specialisation of `extLog_eq_of_witness`, but that is a project decl; from mathlib's primitives the form is unreachable. This rules out `NO-composable-from-mathlib`.

---

## Verdict: `PadicLFunctions.extLog_eq_padicLog`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): the agreement-on-the-ball / consistency property is the **defining hallmark of the Iwasawa extension** of `log_p` — every source (Wikipedia, MIT 18.785, arXiv math/0512015 / 1907.06437 / 1005.4152, PlanetMath, Washington §5.1) builds the extension by requiring it to coincide with the convergent power series where `|x−1|<1`. Standard form is over a complete nonarchimedean **char-0** field on the **full** log ball `‖x−1‖<1`.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — 2 weakenings (drop `[NormedAlgebra ℚ_[p] L]` → `[CharZero K]`; widen `InExpBall` exp ball → full log ball `‖x−1‖<1`), both inherited from the parent defs `extLog`/`padicLog` (each independently assessed `YES-but-generalise-first`). Phase 4c agrees (same direction).
- Mathlib search (Phase 5): **not in mathlib** under either form — mathlib has *no* nonarchimedean logarithm at all (Loogle: `unknown identifier 'padicLog'`; full-source grep: zero hits), so neither the lemma nor the objects it relates exist there.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (the 1-line proof rides on the *project* decl `extLog_eq_of_witness`; mathlib has nothing to inline into).

**Rationale (1–2 paragraphs):**

`extLog_eq_padicLog` is the **consistency lemma of the Iwasawa logarithm**: it states that the extended logarithm `extLog` agrees with the convergent power-series logarithm `padicLog` on the ball where the series converges. This is not incidental plumbing — the literature *defines* the Iwasawa extension precisely by this agreement (`w = p^r·ζ·z`, `log_p w := log_p z`, restricting to the series on `|z−1|<1` with `log_p p = 0`). Mathlib has no nonarchimedean logarithm whatsoever — Loogle does not recognise the identifier `padicLog`, and grepping the pinned mathlib source for any p-adic/Iwasawa log returns nothing — so the lemma is genuinely missing for mathlib, and it cannot be a `NO`: there is no existing decl to cite (`NO-mathlib-has-it` is impossible) and no mathlib primitive to inline (`NO-composable-from-mathlib` is impossible — the one-line proof depends on the *project's* `extLog_eq_of_witness`, not on mathlib). It is real, consumer-backed API (K = 2 internal uses, no inline re-derivation), so it belongs in the same eventual upstreaming as `extLog`/`padicLog`.

The verdict is **not** `YES-add-as-is` because Phase 4b found the Lean form **strictly narrower than the literature standard** on the very two axes already flagged for both parent objects (whose sibling verdicts are likewise `YES-but-generalise-first`): (1) it gratuitously carries `[NormedAlgebra ℚ_[p] L]` and pulls the scalar `m⁻¹`/`1/n` through `ℚ_p`, whereas the standard statement needs only a complete ultrametric **char-0** field; and (2) its hypothesis is `InExpBall` (the smaller **exp** ball `‖x−1‖^{p−1}<p⁻¹`) rather than the **full log convergence ball** `‖x−1‖<1` on which the agreement standardly holds — and the project itself already proves the full-ball version separately as `MeasureR.extLog_eq_padicLog_of_norm_lt_one`. Because `extLog = m⁻¹·padicLog y` is built directly on `padicLog`, this lemma cannot be generalised in isolation: it must ride on the `extLog`/`padicLog` generalisation. Per the skill's gate, a known weakening forces `YES-but-generalise-first`; the MODERATE cost (sequenced behind the parent-def generalisations) is explicitly **not** a downgrade factor.

**Reason for the generalisation:**
  - **LITERATURE-WEAKENING (primary):** Phase 4b found the user's form strictly narrower than the literature-standard form — the redundant `ℚ_p`-algebra assumption, and the agreement stated on the exp ball rather than the standard full log ball `‖x−1‖<1`.
  - **MODERN-IDIOM (secondary, same direction):** Phase 4c — the `CharZero` complete-nonarchimedean-field form on the full log ball is the mathlib-idiomatic target; it is the consistency glue accompanying the generalised `extLog`/`padicLog`, and it collapses the project's current two ball-specific agreement lemmas into one.

  Proposed restatement:
  ```lean
  variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

  /-- The extended (Iwasawa-branch) p-adic logarithm agrees with the convergent
  power-series logarithm on the whole open unit ball `‖x − 1‖ < 1`. -/
  theorem extLog_eq_padicLog {x : K} (hx : ‖x - 1‖ < 1) :
      extLog p x = padicLog p x := by
    sorry  -- restated against the generalised extLog/padicLog; coincides with the
           -- project's existing `extLog_eq_padicLog_of_norm_lt_one`
  ```
  Estimated cost of regeneralisation: **MODERATE** — the statement widening is mechanical, but it must follow the `extLog`/`padicLog` generalisations (the def is `m⁻¹ • padicLog y`) and reuse the wider-setting witness machinery. EXPENSIVE/MODERATE does **not** downgrade the verdict.

  Mathlib downstream this enables (MODERN-IDIOM):
  - one agreement lemma serving `ℚ_p`, finite extensions, and `C_p` uniformly — the consistency bridge that lets every `padicLog` law (multiplicativity, the `p`-power law, the `norm`/isometry results) transport onto the extended `extLog` across the whole rational-valuation domain;
  - collapses the project's current **two** ball-specific agreement lemmas (`extLog_eq_padicLog` on the exp ball + `extLog_eq_padicLog_of_norm_lt_one` on the full ball) into a single statement on `‖x−1‖<1`;
  - removes the scalar-tower restriction, so the bridge no longer needs a `ℚ_p`-algebra structure on the target field.

  Proposed mathlib location (post-generalisation): alongside the generalised `extLog`/`padicLog`, e.g. `Mathlib/NumberTheory/Padics/Logarithm.lean` (new), shipped as part of the coherent "p-adic exp/log" PR group (with `padicExp`, `padicLog`, `InExpBall`, `extLog`).

  Next action: run `/generalise PadicLFunctions.extLog_eq_padicLog` **after** the parent generalisations `/generalise PadicLFunctions.padicLog` and `/generalise PadicLFunctions.extLog` land — it will tension against both the literature-standard form (full log ball, `CharZero` field) from Phase 3 and the modern-idiom form from Phase 4c, and should be unified with the existing `extLog_eq_padicLog_of_norm_lt_one`. Then `/cleanup` and open the mathlib PR with the p-adic-exp/log group.

---

## Next step

Run `/generalise PadicLFunctions.extLog_eq_padicLog` — but **sequenced behind** the generalisations of its parent objects `PadicLFunctions.padicLog` and `PadicLFunctions.extLog` (both `YES-but-generalise-first`), since the agreement lemma rides on those defs. Target: the full-log-ball (`‖x−1‖<1`), complete-ultrametric-`CharZero`-field form, unified with the project's existing `extLog_eq_padicLog_of_norm_lt_one`. Then `/cleanup` and open the mathlib PR as part of the coherent p-adic exp/log group.
