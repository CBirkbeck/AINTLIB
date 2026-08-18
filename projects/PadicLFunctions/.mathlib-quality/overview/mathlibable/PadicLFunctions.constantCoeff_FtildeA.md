# /mathlibable report — `PadicLFunctions.constantCoeff_FtildeA`

**Final verdict: `NO-composable-from-mathlib`.** This is a per-definition
constant-coefficient computation about the *project-specific* power series
`FtildeA` (which bakes in the project-specific `extLog = log_p`). It is not a
standalone mathematical fact: the reusable engine — "the constant coefficient
of `log` substituted at a series with constant term 1 is `0`" — is **already in
mathlib** (`PowerSeries.constantCoeff_logOf` / `PowerSeries.constantCoeff_subst_eq_zero`),
and the whole statement is a ≤3-call linearity unfold of `constantCoeff` (a ring
hom) over the three summands of `FtildeA`. It can only ever live wherever
`FtildeA` lives, and the sibling assessment already placed that machinery
(`uA`) at `NO-composable-from-mathlib`.

---

### Baseline (Phase 0)
- lake build:               **not re-run** (stale/slow per task note) — **reasoned from source**
- decl `PadicLFunctions.constantCoeff_FtildeA`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:479`
- kind:                      `theorem`
- has sorry:                 no (`ResidueZeta.lean` contains 0 `sorry`/`admit`)
- module docstring summary:  "The residue of ζ_p at s = 1 (RJW §7, TeX 2181–2360)" — the simple
  pole of `ζ_{p,p−1}` and the mass `∫x⁻¹μ_a = −(1−p⁻¹)·log_p(a)` via the explicit
  antiderivative `F̃_a` (TeX 2268).

---

### Statement (Phase 1)

`PadicLFunctions.constantCoeff_FtildeA` is **a theorem** stating the following.

Let `p` be prime and `K` a complete normed `ℚ_p`-algebra of characteristic zero
(an ultrametric field containing `ℚ_p(μ_p)`, e.g. `ℂ_p`). For a nonzero natural
number `a`, the constant coefficient of the formal antiderivative

  F̃_a(T) := C(−log_p(a))  −  log(1+(u_a−1))  +  (a−1)·log(1+T)   ∈ K⟦T⟧

equals `−log_p(a)`. In RJW's notation (TeX eq:F_a(0)) this is `F̃_a(0) = −log_p(a)`,
where `log_p` is the project's branch-normalised p-adic logarithm (`extLog`,
with `log_p p = 0`) and the middle term is the formal logarithm `log = Σ_{n≥1}
(−1)^{n−1} n⁻¹ Tⁿ` substituted at `u_a − 1` (constant term 0). The three summands
of `F̃_a` carry constant coefficients `−log_p(a)`, `0`, and `0` respectively, and
`constantCoeff` is additive, so the total is `−log_p(a)`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue characteristic.
- `K : Type*` with `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K] [CharZero K]` — the coefficient field (declared once for the
  whole `section mass`). **The analytic instances `[IsUltrametricDist K]` and
  `[CompleteSpace K]` are `omit`-ted on this lemma** (line 474) — only the *algebraic*
  structure of `K` (char-zero `ℚ_p`-algebra) is actually used.
- `a : ℕ` — the exponent in `(1+T)^a − 1 = a·T·u_a`.

Hypotheses (Lean side):
- `ha0 : a ≠ 0` — required because `uA K 0 = 0` makes the formal substitution junk
  (`HasSubst` fails at constant coefficient `−1`); recorded in the docstring as
  statement note T704.

Conclusion (math): the constant term of the antiderivative `F̃_a` is `−log_p(a)`.

Conclusion (Lean): `PowerSeries.constantCoeff (FtildeA p K a) = -(extLog p ((a : K)))`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a per-definition constant-coefficient computation (a corollary that ships
with the `FtildeA` definition), not a new structure, not a `## Main results`
headline, not named after a person. It is the `F̃_a(0)` bookkeeping step (RJW
TeX eq:F_a(0)) feeding the §7 residue computation.

(Note: literature width was run EXHAUSTIVE regardless. BIG/SMALL is recorded for
the report's framing only and did not gate which Phase 3 channels ran.)

### One-line check (Phase 2b)

Body line count: 4 substantive lines (two `have`s + one `rw` chain).
One-liner verdict: **n/a — kind is `theorem`, not `def`.** The one-line/exemption
machinery applies to `def`/`abbrev`/`structure`. Recorded as a one-line note and skipped.

---

## PHASE 3 — Literature search (EXHAUSTIVE protocol)

### Literature search table

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                                                 | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|-------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific/general engine) | "formal power series logarithm log(1+X) constant term zero substitution constant coefficient"         | yes  | `log(1+X) = X − X²/2 + X³/3 − ⋯` has **zero constant term**; substituting a series with no constant term preserves zero constant term | ProofWiki "Power Series Expansion for Logarithm of 1+x"; UWaterloo CO430 §7 *Formal Power Series* lecture notes. This is the **reusable engine**, and it is textbook-standard. |
|  2 | WebSearch (project-specific form)| "p-adic L-function residue Iwasawa logarithm antiderivative F_a constant coefficient -log_p(a) measure" | yes  | The untwisted p-adic zeta has a simple pole at `s=1`; residue/value-at-1 expressed via `log_p` of principal units (Iwasawa) | Top hit was **arXiv:2309.15692** — the project's *own* source (RJW). No source other than RJW states a `F̃_a(0) = −log_p(a)` for an explicit antiderivative; it is internal bookkeeping inside one paper's residue derivation. |
|  3 | WebSearch (named-after / aliases)| "\"shift operator\" OR \"translation\" formal power series antiderivative constant term value at zero binomial unit cofactor (1+T)^a − 1" | partial | "evaluation at zero" = the **constant-term functional** `φ ↦ φ(0) = c₀^{(φ)}` (umbral calculus) | Umbral-calculus literature (arXiv:2601.10443, math.okstate L24). Confirms "value at 0 of a formal series = its constant coefficient" is the standard notion (`PowerSeries.constantCoeff` in mathlib). No literature attaches `−log_p(a)` to this. |
|  4 | ChatGPT MCP                      | (intended) "standard form + generality + historical evolution of: constant term of a formal log-antiderivative" | n/a  | —                                                                                   | **n/a — no ChatGPT/OpenAI MCP server is installed** in this environment (`mcp_server/` absent from the plugin cache; no `chatgpt`/`openai` tool surfaced). Compensated by an extra grep-of-mathlib-source channel (the authoritative source for the mathlib half of the question) + WebFetch of nLab and the arXiv source. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and repo `refs/`                          | n/a  | (directory absent)                                                                  | No `references/` under this project's `.mathlib-quality/`; no `refs/` symlink in this checkout (local-only PDFs, never committed). The **module docstring + RJW citations** in-file (TeX 2268, eq:tilde F_a 2, eq:F_a(0)) give the source form directly. |
|  6 | nLab                             | WebFetch `ncatlab.org/nlab/show/logarithm`                                                              | yes  | Mercator series `x − ½x² + ⅓x³ − ⋯` for `ln(1+x)`                                    | nLab gives the series but **no commentary on constant terms or substitution composition**. Confirms the series; not the specific result. |
|  7 | nCatLab (categorical angle)      | (same page; categorical content)                                                                       | n/a  | —                                                                                   | n/a — not a categorical concept. A constant-coefficient computation of a specific p-adic antiderivative has no 1-/∞-categorical content. |
|  8 | Stacks Project                   | —                                                                                                      | n/a  | —                                                                                   | n/a — not an algebraic-geometry concept (formal-power-series constant term over a p-adic field; no schemes/sites/cohomology). |
|  9 | MathOverflow / Math.StackExchange| "constant term of formal logarithm / value at 0 of antiderivative" (covered by #1, #3 result sets)     | partial | Confirms "constant term of `log(1+X)` is 0" is folklore/textbook                    | Surfaced via the #1/#3 result sets (ProofWiki, lecture notes, umbral refs). No MO/MSE thread on the project-specific `−log_p(a)` value. |
| 10 | recent arXiv (last 5 years)      | arXiv:2309.15692 (RJW) via WebFetch; arXiv:2601.10443 (umbral)                                           | yes  | RJW = "An introduction to p-adic L-functions", Rodrigues Jacinto & Williams         | The source paper. Its three constructions (measure / Coleman / Iwasawa) culminate in the Iwasawa Main Conjecture; `F̃_a(0)` is an **internal computational step** in the §7 residue analysis, not a standalone named theorem. |

**Protocol pass check.** WebSearch ran 3 distinct queries at different generality
levels (specific engine fact / project-specific p-adic form / named-after-and-aliases).
ChatGPT MCP is genuinely unavailable (recorded `n/a` with reason + compensating
channels). Local references checked (`n/a`, directory absent). nLab checked (hit).
nCatLab / Stacks / MO-MSE / arXiv each checked or `n/a` with a one-line reason. ✓

### Literature summary (Phase 3)

Concept identified as: there are **two** layers.
  - **Reusable layer:** "constant coefficient (≡ value at 0) of the formal logarithm
    `log(1+X)`, and of `log` substituted at a series with constant term 1, is `0`."
    This is **standard formal-power-series algebra** (textbook / ProofWiki / umbral
    calculus). It is mathlib-shaped and **already in mathlib**.
  - **Project layer:** "the constant term of RJW's explicit antiderivative
    `F̃_a` equals `−log_p(a)`" (`F̃_a(0) = −log_p(a)`, TeX eq:F_a(0)). This appears
    **only in RJW (arXiv:2309.15692)**, the project's source, as an internal step.

Sources agree on the standard form: **yes** for the reusable layer (zero constant
term of `log`; constant-term functional = "evaluation at 0"). The project layer has
no independent literature life.

Most general standard form (reusable layer): for any commutative `ℚ`-algebra `A`
and any `f ∈ A⟦X⟧` with `constantCoeff f = 1`, `constantCoeff (logOf f) = 0`; more
primitively, `constantCoeff (g.subst h) = 0` whenever `constantCoeff g = 0` and
`constantCoeff h = 0`.

Generality dimensions where the literature varies:
  - **Coefficient ring:** literature/mathlib state the reusable fact over any
    commutative `ℚ`-algebra; the project pins `K` to a char-zero normed ultrametric
    `ℚ_p`-algebra (far narrower, but irrelevant — the analytic instances are `omit`-ted).
  - **Constant of integration / the `−log_p(a)` term:** purely project-specific;
    `extLog`/`log_p` is not a literature-standard object outside the p-adic-L-function
    setting, and the *combination* into `F̃_a` is RJW's bookkeeping.

Disagreement with the literature: **none.** The reusable half matches the standard
form exactly; the project half is a faithful Lean rendering of RJW's `F̃_a(0)` step.

---

## PHASE 4 — Generality analysis

### Generality analysis — `PadicLFunctions.constantCoeff_FtildeA`

Literature-standard form (from Phase 3): the reusable engine is `constantCoeff
(log.subst (f − 1)) = 0` for `constantCoeff f = 1` over any commutative `ℚ`-algebra.
But note: **this theorem is not a statement of the reusable engine** — it is the
constant-term value of a *named, project-specific def* `FtildeA` whose RHS involves
the project-specific `extLog`. So the "generality" question is really about the
parent object, which cannot be generalised into mathlib (mathlib has neither
`FtildeA` nor `extLog`).

| # | Parameter / hypothesis            | Current Lean form                                  | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|----------------------------------------------------|-------------------------------------------|---------------------|----------------------------------|
| 1 | `[NormedField K]` + 4 analytic instances | char-zero complete ultrametric normed `ℚ_p`-algebra | the reusable engine needs only `[CommRing A] [Algebra ℚ A]` | yes (for the engine) | `[IsUltrametricDist]`,`[CompleteSpace]` are `omit`-ted here; only `[CharZero]`+`[NormedAlgebra ℚ_[p] K]` (⇒ `ℚ`-algebra) are used. But this is moot — the *statement* references `extLog p (a:K)`, which is defined only for this p-adic `K`. |
| 2 | `(ha0 : a ≠ 0)`                    | `a ≠ 0`                                             | n/a (no literature analog of `F̃_a`)       | NO                  | genuinely needed: `uA K 0 = 0` ⇒ the substitution argument has constant coeff `−1` ⇒ `HasSubst` fails. Cannot be dropped. |
| 3 | the object `FtildeA p K a`         | RJW antiderivative with `extLog` constant term     | no literature-standard form               | NO                  | `FtildeA`/`extLog` are project objects; mathlib has no counterpart to generalise toward. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL within its scope** — but its scope is
intrinsically project-local. The hypotheses are tight (`a ≠ 0` is forced; the
analytic instances are already `omit`-ted), and the *statement itself* is bound to
the project objects `FtildeA`/`extLog`, so there is no "more general literature
form of this theorem" to aim at. (The *reusable engine* it leans on is maximally
general and already in mathlib.)

Number of weakening opportunities found: **0** (for the theorem as stated; the
only "weakening" is on the engine, which is mathlib's, not ours).

Proposed restatement (if STRICTLY NARROWER): n/a — not strictly narrower than a
literature standard, because there is no literature standard for "`F̃_a(0)`".

Cost of restatement: n/a.

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                        | no       | already typeclass-based (`[NormedAlgebra ℚ_[p] K]` etc.) | — |
|  2 | sequences/metric → filters/topology?                                                                      | no       | a constant-coefficient identity; no limits/convergence (the analytic instances are `omit`-ted) | — |
|  3 | construct an object where a universal property would characterise it?                                     | no       | this is a value computation, not a construction | — |
|  4 | set-with-closure-predicate → bundled substructure?                                                        | no       | no substructure here | — |
|  5 | vector-space/metric/field-specific → weaken via mathlib's typeclass hierarchy?                            | partial  | the *engine* is already weakened in mathlib (`[CommRing A] [Algebra ℚ A]`); but the statement is bound to the p-adic `extLog`, so weakening the field is impossible while keeping the RHS | — (the modernisation is mathlib's `logOf` API, which *already exists*) |
|  6 | 1-categorical → higher-categorical?                                                                       | no       | no categorical content | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive monoid/group?                                                 | no       | `a : ℕ` is the binomial exponent and the `nsmul` count; no algebraic generalisation in scope | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for this theorem as a mathlib contribution). The
contemporary mathlib idiom for the *engine* — `PowerSeries.logOf` together with
`PowerSeries.constantCoeff_logOf` and `PowerSeries.constantCoeff_subst_eq_zero` —
**already exists in mathlib** (`Mathlib/RingTheory/PowerSeries/Log.lean`,
`…/Substitution.lean`). The right "modernisation" is therefore not to upstream this
theorem in a new form; it is for the *project* to lean on that existing mathlib API
(this is a local-cleanup observation, recorded in Phase 6). One-line reason this is
not a modernisation-to-upstream move: the statement is a value computation tied to
the project-specific `FtildeA`/`extLog`, which have no mathlib home.

---

## PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional
equalities or typeclass-search paths; the six-row risk table is skipped.

---

## PHASE 5 — Mathlib search (five-method)

### Mathlib search-status: `PadicLFunctions.constantCoeff_FtildeA`

[A] **Lean-Finder**   — natural-language + type queries        **n/a: no Lean-Finder MCP tool surfaced** in this environment. Compensated by [B]/[C] equivalents below being run as direct grep over the pinned mathlib clone (`.lake/packages/mathlib`), which is authoritative.
[B] **Loogle**        — `PowerSeries.constantCoeff (_ + _ - _)` / `constantCoeff (subst _ _) = 0`   **n/a as MCP** (no `lean_loogle` tool); the equivalent pattern was resolved by reading `Mathlib/RingTheory/PowerSeries/{Log,Substitution,Basic}.lean` directly — **hits** (see [D]).
[C] **LeanSearch**    — "constant coefficient of formal logarithm substituted at series" **n/a as MCP** (no `lean_leansearch` tool); resolved via the same direct source read — the natural-language target maps exactly to `constantCoeff_logOf`.
[D] **Grep mathlib src** — `constantCoeff_log`, `constantCoeff_logOf`, `constantCoeff_subst_eq_zero`, `constantCoeff_C`, `extLog`, `FtildeA`   **HITS for the building blocks; NO hit for the exact statement.** Found:
  - `PowerSeries.constantCoeff_C`           — `Mathlib/RingTheory/PowerSeries/Basic.lean:307`
  - `PowerSeries.constantCoeff_log`         — `Mathlib/RingTheory/PowerSeries/Log.lean:53`  (`constantCoeff (log A) = 0`)
  - `PowerSeries.constantCoeff_logOf`       — `Mathlib/RingTheory/PowerSeries/Log.lean:87`  (`constantCoeff f = 1 → constantCoeff (logOf f) = 0`)
  - `PowerSeries.constantCoeff_subst_eq_zero` — `Mathlib/RingTheory/PowerSeries/Substitution.lean:271`
  - `constantCoeff` is a `RingHom` ⇒ `map_add` / `map_sub` / `map_nsmul` all apply.
  - `extLog`, `FtildeA`: **0 hits in mathlib** (project-only objects).
[E] **Name pattern**  — `lean_local_search` (project) for re-derivations; grep mathlib `RingTheory/PowerSeries/` for an "antiderivative/primitive constant-term" lemma   **no hit for a packaged `F̃_a`-shaped lemma** (Derivative.lean has no "constant term of an explicit log-combination antiderivative"). Within the project, the value is computed in exactly one place — this theorem (no inline re-derivation; see Phase 6.0).

Searched for both:
  - the **user's current form** — `constantCoeff (FtildeA p K a) = -(extLog p a)`: **not in mathlib** (references project objects with no mathlib counterpart).
  - the **literature-standard / reusable engine** — `constantCoeff (log.subst (f−1)) = 0`: **found in mathlib** as `PowerSeries.constantCoeff_logOf` (Log.lean:87) and `PowerSeries.constantCoeff_subst_eq_zero` (Substitution.lean:271).

Concluded: **"found the building blocks (`PowerSeries.constantCoeff_C`,
`PowerSeries.constantCoeff_log` / `constantCoeff_logOf`,
`PowerSeries.constantCoeff_subst_eq_zero`, plus `RingHom` linearity of
`constantCoeff`); the exact statement is not — and cannot be — in mathlib because
it names the project-specific `FtildeA` and `extLog`."** The composition of those
blocks yields our form (Phase 6).

---

## PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `PadicLFunctions.constantCoeff_FtildeA`

Internal use count: **1** (within the project, excluding the declaring line).
External-to-file callers: **0**.

| Caller file:line             | Usage pattern (one-line excerpt)                                                          |
|------------------------------|-------------------------------------------------------------------------------------------|
| `ResidueZeta.lean:1595`      | `rw [constantCoeff_FtildeA p K ha0, sum_seriesEval_FtildeA …] at hp_mul`  (inside `constantCoeff_mahlerK_rhoA`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using
`constantCoeff_FtildeA`?): **(none)** — the only place that needs `F̃_a(0)` calls
this lemma. `FtildeA` itself is used in ~25 lines across the file (derivative,
norm-bound, seriesEval, mass identities), but the *constant-term value* is taken
only here.

What the call-sites pattern tells you: **K = 1 internal use, no external callers,
no inline re-derivation.** Per the Phase-6 table this is the "possibly the wrong
*standalone* abstraction — could be inlined / leans toward NO-composable" signal:
it is a single-consumer corollary of the parent def, exactly the kind of
"ships-with-the-def" computation that does not travel to mathlib on its own.

### Composition check (Phase 6)

Can `constantCoeff_FtildeA` be derived from mathlib (+ the parent def `FtildeA`)
in ≤3 chained calls? **Yes — the proof body *is* the composition.**

Attempt 1 (the actual proof, lines 482–488):
```lean
rw [FtildeA, map_add, map_sub, PowerSeries.constantCoeff_C, hsubst, sub_zero,
    map_nsmul, constantCoeff_formalLog, smul_zero, add_zero]
```
where the only two substantive inputs are:
  - `hsubst : constantCoeff (formalLog.subst (uA K a − 1)) = 0`
    `:= PowerSeries.constantCoeff_subst_eq_zero hc _ constantCoeff_formalLog`
    — i.e. **mathlib's** `constantCoeff_subst_eq_zero` (the same step mathlib packages
    as `constantCoeff_logOf`), applied to the project's `formalLog`/`uA`;
  - `constantCoeff_formalLog` (the project's clone of mathlib's `constantCoeff_log`).
  - Mathlib decls used: `map_add`, `map_sub`, `map_nsmul`, `PowerSeries.constantCoeff_C`,
    `PowerSeries.constantCoeff_subst_eq_zero` — all linearity of the `constantCoeff`
    ring hom plus one substitution-vanishing lemma.
  - Result: **succeeds.** It is a pure unfold-and-evaluate: `constantCoeff` distributes
    over the three summands of `FtildeA`, two of which vanish.
  - Notes: this is the textbook Phase-6 "`Foo.bar (Bar.baz hx)` + a `.symm`/linearity
    chain" pattern — a composition, not a proof with non-trivial intermediate reasoning.

**Conclusion: COMPOSABLE.** The statement is `constantCoeff`-linearity over the
`FtildeA` summands, with the one non-trivial summand discharged by mathlib's
`constantCoeff_subst_eq_zero` / `constantCoeff_logOf`. No new mathlib lemma is
warranted; the computation belongs wherever `FtildeA` is defined.

---

## Verdict: `PadicLFunctions.constantCoeff_FtildeA`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the *reusable engine* (zero constant term of `log`;
  constant-term-of-substitution) is textbook-standard and **already in mathlib**; the
  *specific* `F̃_a(0) = −log_p(a)` appears only in the project's own source RJW
  (arXiv:2309.15692) as internal bookkeeping. No independent standard form.
- Generality analysis (Phase 4): MAXIMALLY GENERAL *within an intrinsically
  project-local scope* (0 weakenings; `a ≠ 0` forced; analytic instances already
  `omit`-ted); Phase 4c found the modern idiom (`PowerSeries.logOf` + its API)
  already in mathlib — nothing new to upstream.
- Mathlib search (Phase 5): building blocks found by qualified name
  (`PowerSeries.constantCoeff_C`, `constantCoeff_log`/`constantCoeff_logOf`,
  `constantCoeff_subst_eq_zero`, `RingHom` linearity of `constantCoeff`); the exact
  statement is not — and cannot be — in mathlib (`FtildeA`/`extLog` are project-only).
- Composition check (Phase 6): **COMPOSABLE** — the proof itself is a ≤3-call
  linearity unfold over the `FtildeA` summands; K = 1 internal caller, 0 external,
  no inline re-derivation.

**Rationale.**
`constantCoeff_FtildeA` is not a candidate mathlib *theorem* in its own right: it
is the "compute the constant term of this specific definition" corollary that ships
with the project's antiderivative `FtildeA`, and its right-hand side `−log_p(a)` is
phrased with the project's branch-normalised p-adic logarithm `extLog` — an object
mathlib does not (and on this route should not) contain. Strip away the
project-specific wrapping and what remains is a single application of the linearity
of the `constantCoeff` ring homomorphism over a three-term sum, where the only
non-formal summand (`log` substituted at `u_a − 1`) is killed by a lemma mathlib
*already has*: `PowerSeries.constantCoeff_subst_eq_zero` (the very lemma the proof
calls), packaged for logarithms as `PowerSeries.constantCoeff_logOf`. The proof body
(`rw [FtildeA, map_add, map_sub, constantCoeff_C, hsubst, sub_zero, map_nsmul,
constantCoeff_formalLog, smul_zero, add_zero]`) is exactly such a composition, not a
proof carrying new mathematical content.

This dovetails with the def-first context: the parent machinery `uA` was already
assessed `NO-composable-from-mathlib`, and `FtildeA` itself is a project-local
construction with no mathlib counterpart. A constant-coefficient lemma cannot
graduate to mathlib while the object it is about stays project-local; and even if
`FtildeA` were upstreamed, *this* lemma would remain a one-line `simp`/`rw`
consequence of mathlib's `logOf` API, not a separately-PR'd result. K = 1 internal
consumer with no inline re-derivation and no external users confirms it is a
single-use "ships-with-the-def" corollary, not reusable API.

**WHY not (refactor-actionable detail).**
Mathlib has the building blocks; the statement is `constantCoeff`-linearity plus one
substitution-vanishing lemma. The project notably **re-implements** the formal
logarithm: `formalLog K := mk fun n => if n = 0 then 0 else (-1)^(n-1)·n⁻¹`
(`MeasureR/FormalPsi.lean:1217`) duplicates mathlib's `PowerSeries.log`
(`Mathlib/RingTheory/PowerSeries/Log.lean:42`, same series since `(-1)^(n-1) =
(-1)^(n+1)`), and `formalLog.subst (uA − 1)` duplicates mathlib's
`PowerSeries.logOf`. So the cleanest refactor is local, not a mathlib PR.

Mathlib building blocks (qualified names with paths):
  - `PowerSeries.constantCoeff_C`            — `Mathlib/RingTheory/PowerSeries/Basic.lean:307`
  - `PowerSeries.constantCoeff_log`          — `Mathlib/RingTheory/PowerSeries/Log.lean:53`
  - `PowerSeries.constantCoeff_logOf`        — `Mathlib/RingTheory/PowerSeries/Log.lean:87`
  - `PowerSeries.constantCoeff_subst_eq_zero` — `Mathlib/RingTheory/PowerSeries/Substitution.lean:271`
  - `RingHom` linearity of `constantCoeff`: `map_add`, `map_sub`, `map_nsmul`.

Composition sketch (≤3 lines — what the proof already is, in mathlib-direct terms):
```lean
-- with FtildeA unfolded, constantCoeff distributes over the three summands;
-- the C-term gives -log_p(a), the nsmul·log term and the log-substitution term vanish:
example {a : ℕ} (ha0 : a ≠ 0) :
    PowerSeries.constantCoeff (FtildeA p K a) = -(extLog p (a : K)) := by
  rw [FtildeA, map_add, map_sub, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_subst_eq_zero (by rw [map_sub, constantCoeff_uA K ha0,
        map_one, sub_self]) _ constantCoeff_formalLog,
      sub_zero, map_nsmul, constantCoeff_formalLog, smul_zero, add_zero]
```

Call sites in our project (from Phase 6.0): **K = 1** (`ResidueZeta.lean:1595`).

Refactor plan:
  1. **Keep the lemma** as a project-local convenience next to `FtildeA` — it is the
     correct grain for the single consumer `constantCoeff_mahlerK_rhoA` (inlining the
     10-rewrite chain at that one site would only obscure it). It is **not** a mathlib
     PR target: do not file a `feat(RingTheory/PowerSeries)` PR for it.
  2. **Optional local cleanup (separate from this verdict):** migrate the project's
     `formalLog` to mathlib's `PowerSeries.log` and `formalLog.subst (uA − 1)` to
     `PowerSeries.logOf`, then derive `hsubst` from `PowerSeries.constantCoeff_logOf`
     directly. This removes a duplicated definition and shortens this proof to two
     rewrites. This is a `/cleanup`-lane task on `main`, not a mathlib contribution.
  3. There is **nothing to delete and re-point at a mathlib name** at the call site
     (unlike a `NO-mathlib-has-it` case): mathlib has no `constantCoeff_FtildeA`,
     only the engine the proof already uses.

Next action: **do not upstream.** Treat as project-local glue. If desired, open a
project `/cleanup` ticket to replace `formalLog`/its substitution with mathlib's
`PowerSeries.log`/`PowerSeries.logOf` (and lean on `constantCoeff_logOf`), which
collapses this proof and removes the duplicated formal-logarithm definition.

---

## Next step

Do not upstream `constantCoeff_FtildeA` to mathlib — it is a single-consumer,
constant-coefficient computation about the project-specific def `FtildeA` (RHS uses
the project-specific `extLog`), provable in ≤3 calls from mathlib's
`constantCoeff_subst_eq_zero` / `constantCoeff_logOf` plus `constantCoeff`-ring-hom
linearity. Keep it project-local next to `FtildeA`. Optionally file a project
`/cleanup` ticket to migrate `formalLog` → mathlib `PowerSeries.log` and its
substitution → `PowerSeries.logOf`, deriving the vanishing substitution term from
`PowerSeries.constantCoeff_logOf` and deleting the duplicated formal-logarithm
definition.
