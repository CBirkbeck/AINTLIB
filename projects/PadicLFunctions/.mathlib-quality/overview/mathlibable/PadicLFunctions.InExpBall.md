# `PadicLFunctions.InExpBall` — mathlibable assessment

**Verdict: `NO-composable-from-mathlib`**

`InExpBall p x` is a thin `Prop` abbreviation for the single inequality
`‖x‖ ^ (p - 1) < (p : ℝ)⁻¹` — the rpow-free form of membership in the open
convergence ball `‖x‖ < p^{-1/(p-1)}` of the `p`-adic exponential. It bundles no
data, no API, and no instances; it is one `<` between two terms. Mathlib's own
exp framework expresses "in the convergence ball" inline as
`x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius`, not as a named `def`, and the
literature states this region uniformly as an *inequality hypothesis*, never as a
bundled object. The substantive mathematics (the `p`-adic `exp`/`log`, the
isometry, the functional equation, RJW Lem 5.14) lives in the surrounding
theorems, which are assessed separately. The abbreviation itself is project-local
sugar with 0 external consumers and should not be PR'd to mathlib as a standalone
definition.

- **Target:** `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:65` (kind: `def`)
- **Mode:** A (single declaration), full 10-phase workflow with the exhaustive 9-channel literature search.

---

## Phase 0 — Doctor / baseline

Per the task's BUILD NOTE, the build was **not re-run; reasoned from source.**
The declaration and its full dependency context were read directly from
`PadicExp.lean` (1169 lines, read in full) and from the mathlib package under
`.lake/packages/mathlib/`. Baseline commit `d71766e`. No `sorry` in the target
or its dependents. This is the Phase-0 source-fallback path the skill permits.

---

## Phase 1 — Comprehend

```lean
/-- Membership in the open convergence ball `‖x‖ < p^{−1/(p−1)}` of the
`p`-adic exponential, stated rpow-free: `‖x‖^{p−1} < p⁻¹`. -/
def InExpBall (p : ℕ) {L : Type*} [NormedField L] (x : L) : Prop :=
  ‖x‖ ^ (p - 1) < (p : ℝ)⁻¹
```

**Mathematical content.** Over a nonarchimedean complete normed `ℚ_[p]`-algebra
field `L`, the `p`-adic exponential `exp(x) = ∑ xⁿ/n!` converges exactly on the
open ball `‖x‖ < p^{-1/(p-1)}` (Legendre: `v_p(n!) = (n − s_p(n))/(p−1)`).
`InExpBall p x` is the membership predicate for that ball, written **rpow-free**:
raising `‖x‖ < p^{-1/(p-1)}` to the `(p−1)`-th power and clearing the root gives
the equivalent `‖x‖^{p−1} < p⁻¹`, which avoids `Real.rpow` and a `(p−1)`-th root
entirely. Here `p - 1` is a **natural-number** exponent (truncated subtraction),
valid because `p` is prime so `p ≥ 2`.

**Type-class context (file-level):** `variable (p : ℕ) [hp : Fact p.Prime]` and
`{L : Type*} [NormedField L]`. The `def` itself takes `p` and `L` with only
`[NormedField L]` — it does **not** require `Fact p.Prime`,
`[IsUltrametricDist L]`, `[NormedAlgebra ℚ_[p] L]`, or `[CompleteSpace L]`. Those
enter only in the theorems that *use* the predicate.

**Role in the development.** It is the shared hypothesis threaded through the
entire `exp`/`log` API of the file: `summable_padicExp_terms`,
`norm_padicExp_sub_padicExp` (isometry), `padicExp_add` (functional equation),
`summable_padicLog_terms`, `norm_padicLog`, the two inversion theorems
`padicExp_padicLog` / `padicLog_padicExp`, `padicLog_mul`, and the `pℤ_p`
integral-branch results (`inExpBall_of_mem_span`, `pZpExp`, `pZpLog`, up to RJW
Lem 5.14's `padicExp_smul_padicLog_eq_onePAdicPow`).

---

## Phase 2 — Preliminary BIG/SMALL + one-line check

**SMALL.** The definition is a single strict inequality between two real numbers.
There is no construction, no recursion, no bundling, no field, no instance — the
body is `‖x‖ ^ (p - 1) < (p : ℝ)⁻¹`, a `Prop` that is *already* its own one-liner.

**One-line check:** the predicate **is** a one-line expression. Any consumer can
write `‖x‖ ^ (p - 1) < (p : ℝ)⁻¹` (or the standard-idiom `‖x‖ < p^{-1/(p-1)}` /
`x ∈ Metric.ball 0 r`) directly in place of `InExpBall p x`. This already signals
the def is sugar, not content.

**Exemptions considered (defeq-abuse / diamond / API-stability):** none apply. The
def introduces no `instance`/`class`, so there is no diamond risk; it is not used
to repair a defeq; and it provides no stabilising API surface (no `@[simp]`
lemmas, no `Iff` characterisation, no bundled projections) — every use in the file
immediately `rw [InExpBall]`s it back to the raw inequality (lines 262, 982, 1018,
953, 978–979, …). It is an abbreviation, full stop.

---

## Phase 3 — Exhaustive literature search (9 channels)

Goal: identify the **literature-standard form** of "the `p`-adic exponential's
convergence region" and whether it is ever a *named bundled object* rather than an
inequality hypothesis.

| # | Channel | Query | Finding |
|---|---------|-------|---------|
| 1 | WebSearch | "p-adic exponential convergence radius open ball norm < p^{-1/(p-1)}" | Radius of convergence of `exp` is `p^{-1/(p-1)}`; converges on the open ball of valuative radius `1/(p−1)` about 0; image is the ball about 1. Canonical. |
| 2 | WebSearch | "p-adic exponential radius of convergence Cassels Washington cyclotomic fields" | Confirms `r = p^{-1/(p-1)}`; `exp(x)` converges for `\|x\| < 1`-type statements; cites **Cassels, *Local Fields*** and **Washington, *Intro. to Cyclotomic Fields* §5.1** — exactly the references in the file's docstring. |
| 3 | WebFetch — **Wikipedia**, "p-adic exponential function" | exact convergence-domain wording | "exp_p only converges on the disc `\|z\|_p < p^{−1/(p−1)}`." Stated as an **inequality**; the word "disc" is descriptive prose, **not** a named formal object. Logarithm: converges for `\|x\|_p < 1`. |
| 4 | **nLab / PlanetMath** (via search) | "p-adic exponential and p-adic logarithm" (planetmath.org), nLab convergence-ball usage | `exp` converges on open ball `𝔻_p` of valuative radius `1/(p−1)` about 0; image is `1 + 𝔻_p`; `log` converges for `\|z−1\|_p < 1`. Region presented as a *ball described by an inequality*, not a bundled definitional structure. |
| 5 | **MathOverflow / course notes** (via search) | K. Conrad, "Infinite series in p-adic fields"; MIT 18.785 PS10 ("The p-adic logarithm"); D. Vogan "Exponential and logarithm in p-adic fields" | All state the domain as the hypothesis `\|x\| < p^{-1/(p-1)}` (resp. `\|x−1\| < 1`). None introduce a named "InExpBall"-style object; the inequality is carried as a side condition on theorems. |
| 6 | **arXiv** (via search) | "Hensel minimality, p-adic exponentiation and Tate uniformization" (2602.16433); "Dirichlet Series Expansions of p-adic L-Functions" (2102.02851); overconvergent-Frobenius papers | Contemporary research uses the same inequality hypothesis; `exp`/`log` discs are the open balls of the stated radii. No bundled convergence-region type. |
| 7 | **Cambridge p-adic analysis notes** (jat58/all.pdf, Lecture 1) | radius of convergence of `exp` | Confirms radius `p^{-1/(p-1)}`; presented as the disc of convergence (inequality). |
| 8 | **World Scientific** — "Logarithm and exponential in a p-adic field" (Value Distribution in p-adic Analysis, ch.) | named treatment of the two functions | Standard chapter-level treatment: `exp`/`log` defined on their respective discs given by inequalities; no separate named "ball-membership" predicate. |
| 9 | **ChatGPT MCP** (historical-formulation question) | not available in this environment | **Channel unavailable** (no ChatGPT MCP configured for this session). Compensated by channels 1–8, which already converge unanimously; recorded for completeness per the skill's gate. |

**Literature-standard form (synthesised).** The convergence region of the
`p`-adic exponential is *universally* expressed as the **side condition**
`|x|_p < p^{-1/(p-1)}` on the point `x` (Wikipedia "disc", nLab/PlanetMath "open
ball `𝔻_p`", Cassels §12, Washington §5.1, Conrad, MIT 18.785, Cambridge notes).
It is **never** packaged as a named bundled mathematical object — there is no
"standard definition" to PR; the standard *form* is an inequality hypothesis,
which is exactly what `InExpBall` abbreviates (in rpow-free form).

---

## Phase 4 — Generality vs literature-standard

**Verdict: not a generalisation question.** `InExpBall` is a Prop abbreviation,
so "weaken the hypotheses" doesn't apply in the usual lemma sense. Two observations:

- **The def is already maximally general in its type-class footprint:** only
  `[NormedField L]` is required (no `Fact p.Prime`, no ultrametric, no
  `ℚ_[p]`-algebra). It is as general as the bare inequality allows.
- **The rpow-free encoding (`‖x‖^{p−1} < p⁻¹` with a `ℕ` exponent) is narrower in
  *spirit* than the literature form `‖x‖ < p^{-1/(p-1)}`** (which uses a real
  `(p−1)`-th root): the two are equivalent only because `p ≥ 2` makes `p − 1` a
  genuine positive `ℕ`. This is an *encoding convenience for the proofs in this
  file*, not a mathematical object the literature recognises. It is a presentation
  detail, not a generalisation axis.

No literature-supported weakening or strengthening of the *predicate* is on the
table; the only question is whether the wrapper should exist at all (Phases 5–6).

---

## Phase 4c — Modern-mathlib-idiom restatement (the Bourbaki 2.0 check)

This is the decisive phase. **Does contemporary mathlib re-state "membership in
the exp convergence ball" with a bespoke `def`?** No — and mathlib already shows
its hand:

`Mathlib/Analysis/Normed/Algebra/Exponential.lean` develops the entire normed-
algebra exponential and writes "in the convergence ball" **inline** as

```lean
(hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
```

across `norm_expSeries_summable_of_mem_ball`, `expSeries_summable_of_mem_ball`,
`exp_add_of_mem_ball`, `invertibleExpOfMemBall`, etc. The mathlib idiom for "the
exponential converges here" is **`Metric.eball`/`Metric.ball` membership against a
`FormalMultilinearSeries.radius`**, or simply a `‖x‖ < r` side condition — *never*
a one-field `def` named after the ball.

Consequences:

1. The modern-idiom restatement of `InExpBall p x` is either the literal
   inequality `‖x‖ < p^{-1/(p-1)}` (or its rpow-free twin) used inline, or
   `x ∈ Metric.ball (0 : L) (p^{-1/(p-1)})`. Both are already in mathlib's
   vocabulary.
2. There are **no downstream consequences** that a `def InExpBall` unlocks. It
   carries no `@[simp]` set, no `Iff` lemma, no instances; every internal use
   immediately unfolds it (`rw [InExpBall]`). It composes with *nothing* in
   mathlib that the bare inequality wouldn't compose with.
3. Per the verdicts reference's rule 5 ("modernisation has to be a real
   improvement in mathematical organisation… 'it looks cooler' is not enough"),
   there is no modernisation contribution here: the *idiomatic* form already
   exists, and the bespoke def is the *less* idiomatic option.

This is the opposite of a Bourbaki-2.0 win: shipping `InExpBall` would *add* a
non-idiomatic wrapper that mathlib deliberately avoids.

---

## Phase 5 — Mathlib five-method search

Searched for (a) any `p`-adic exponential/logarithm, and (b) any
convergence-ball-membership predicate.

| Method | Query | Result |
|--------|-------|--------|
| grep (decl names) | `padicExp`, `padicLog`, `padic_exp`, `Padic.exp`, `Padic.log` in `mathlib/Mathlib/` | **None.** Mathlib has no `p`-adic exponential or logarithm at all. |
| grep (concept) | `nonarchimedean.*exp`, `ultrametric.*exp` in mathlib | **None.** |
| grep (ball-as-def) | `def .*: Prop := ‖`, `def .*Ball`/`def .*ball` with `conv\|exp\|radius` in `Analysis/` | **No** convergence-region `def`. The only hit, `invertibleExpOfMemBall`, is a *lemma/def about* `Metric.eball` membership, confirming the idiom is `eball`, not a named predicate. |
| read (the idiom) | `Analysis/Normed/Algebra/Exponential.lean` `_of_mem_ball` family | Confirms `x ∈ Metric.eball 0 (expSeries 𝕂 𝔸).radius` as the standard hypothesis. For the **classical** field exp, `expSeries_radius_eq_top` makes the ball all of `𝔸` — so this machinery does **not** capture the *bounded* `p`-adic ball. |
| Loogle/LeanSearch (offline proxy) | "norm pow lt inv as convergence predicate", "p-adic exp ball" | No matching declaration; the inequality `‖x‖^{p-1} < p⁻¹` is not a named mathlib lemma/def. |

**Conclusion of Phase 5.** Mathlib has **neither** a `p`-adic exponential **nor**
a named convergence-ball predicate. The user's *form* (a bespoke `def` for the
ball) does not exist in mathlib — and mathlib's evidence (the `eball` idiom +
`radius = ⊤` for classical exp) shows it deliberately does **not** name such a
predicate. So Phase 5 finds no direct hit to cite for `NO-mathlib-has-it`; the
question correctly falls to the composition check.

---

## Phase 6 — Composition check (≤3 mathlib calls?)

### Phase 6.0 — Call-sites table (required artifact)

| Location | Uses of `InExpBall` | Nature |
|----------|--------------------|--------|
| `PadicExp.lean` (own file) | **30** occurrences | Always a hypothesis `(hx : InExpBall p x)` or an unfold target `rw [InExpBall]`. |
| Rest of `projects/` (all other `.lean`) | **0** | Grep `InExpBall` over `projects/` minus `PadicExp.lean`: **no matches.** Not used in `Branches.lean`, `Coefficients.lean`, or anywhere downstream. |
| Mathlib | 0 | N/A. |

**K = 0 external uses.** By the verdicts reference's call-sites heuristic, a
predicate with **K = 0 external uses** that is repeatedly **unfolded inline** at
its own use sites (`rw [InExpBall]` at lines 262, 953, 978, 979, 982, 1018) is a
**wrapper consumers bypass** → the signal leans `NO-composable-from-mathlib`
(there being no more-general mathlib `D'` to re-aim at, see Phase 5).

### Composition

`InExpBall p x` **is** its own composition: the body `‖x‖ ^ (p - 1) < (p : ℝ)⁻¹`
is a single `<` applied to `norm`, `HPow` (`ℕ`-power), and `Inv` — **0 auxiliary
mathlib lemma calls** needed to *state* it; it is a direct expression, the
shortest possible "composition" (the term itself). Equivalently, the idiomatic
mathlib spelling `x ∈ Metric.ball (0 : L) ((p : ℝ)^(-(1/(p-1) : ℝ)))` is a single
membership. Either way the replacement is **≤1 expression**, far inside the ≤3
budget, and it is a genuine composition (a literal inequality / ball membership),
not a proof in disguise.

**COMPOSABLE.** Every call site can inline `‖x‖ ^ (p - 1) < (p : ℝ)⁻¹` (which is
what they already do via `rw [InExpBall]`), so no named declaration is justified
for mathlib.

---

## Phase 7 — Synthesis and verdict

- Phase 2: SMALL; the def is already a one-liner Prop (sugar, no API).
- Phase 3 (9 channels): the convergence region is a **canonical inequality
  hypothesis** in the literature (Wikipedia, Cassels §12, Washington §5.1,
  Conrad, nLab/PlanetMath, MIT, Cambridge, arXiv), **never a named bundled
  object**.
- Phase 4c (Bourbaki 2.0): mathlib's *own* exp framework expresses ball
  membership inline as `Metric.eball`/`‖·‖ < r`, **not** a `def`; the bespoke
  wrapper is the *less* idiomatic choice and unlocks no downstream API.
- Phase 5: mathlib has no `p`-adic exp/log and no named convergence-ball
  predicate; nothing to cite for `NO-mathlib-has-it`.
- Phase 6: **K = 0** external consumers; the def is a wrapper its own call sites
  unfold; the body is a 0-call inequality expression → **COMPOSABLE**.

These converge on **`NO-composable-from-mathlib`** for the *definition itself*.
The predicate is project-local convenience sugar; mathlib would carry the
inequality inline (or as a `Metric.ball` membership), exactly as it does for the
classical exponential. The genuinely contributable mathematics — a `p`-adic
`padicExp`/`padicLog`, their isometry/functional-equation/inversion API, and RJW
Lem 5.14 — is **entirely separate** from this abbreviation and is assessed under
those declarations (the file's `padicExp`, `padicLog`, `norm_padicExp_sub_padicExp`,
`padicExp_add`, `padicExp_padicLog`, `padicLog_padicExp`, `pZpExp`, `pZpLog`, …),
several of which are strong mathlib candidates in their own right.

**Note for the broader PR (not a downgrade of those theorems):** if the `p`-adic
`exp` API is ever upstreamed, the idiomatic move is to drop `InExpBall` and state
the convergence hypothesis as `‖x‖ < p^{-1/(p-1)}` / `x ∈ Metric.ball 0 r`
inline, matching `Mathlib/Analysis/Normed/Algebra/Exponential.lean`. Keeping
`InExpBall` project-local (as readable sugar across this one file) is fine; it
simply does not travel to mathlib as a standalone `def`.

### Final verdict (five-bucket)

> ## **`NO-composable-from-mathlib`**

**Next action:** keep `InExpBall` as project-local sugar; do **not** PR it as a
standalone definition. If/when the surrounding `p`-adic exp/log API is prepared
for mathlib, inline the inequality (`‖x‖ < p^{-1/(p-1)}`) or use
`x ∈ Metric.ball 0 r`, matching mathlib's existing exponential idiom. Assess the
substantive theorems (`padicExp`, `padicLog`, isometry, functional equation,
inversions, RJW Lem 5.14) under their own declarations.
