# `/mathlibable` report — `PadicLFunctions.norm_factorial_inv_smul_pow_le`

**Final verdict: `BORDERLINE-needs-human`**

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task BUILD NOTE — build is stale/slow here; Phase-0 source fallback used)
- decl `PadicLFunctions.norm_factorial_inv_smul_pow_le`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:81`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=∑xⁿ/n!` converges and is an isometry on the open ball `‖x‖ < p^{−1/(p−1)}`; `log` inverts it; realises RJW Lemma 5.14. This theorem is decomposition node E2-adjacent: the per-term geometric decay estimate that powers summability of the exp series.

The declaration, its dependencies (`norm_factorial_le` at line 52, `norm_factorial_inv_pow_le` at line 69, `InExpBall` at line 65), and both call sites (`PadicExp.lean:124`, `ResidueZeta.lean:62`) were read directly from source, plus the mathlib package under `.lake/packages/mathlib/` (present and grep-able). Baseline commit `d71766e`.

---

### Statement (Phase 1)

`norm_factorial_inv_smul_pow_le` is a **theorem** stating the following:

> Let `L` be a normed field that is a normed `ℚ_p`-algebra (no completeness or ultrametricity needed for *this* lemma — both are `omit`-ted at line 77). For every `x ∈ L` and every `n ≥ 1`, the `n`-th term of the p-adic exponential series, raised to the `(p−1)`-th power, satisfies the geometric bound
> `‖(n!)⁻¹ · xⁿ‖^{p−1} ≤ ‖x‖^{p−1} · (p · ‖x‖^{p−1})^{n−1}`.

Mathematically this is the **normwise, rpow-free, `(p−1)`-power-level repackaging of the standard per-term valuation estimate `ord(xⁿ/n!) ≥ n·ord(x) − n/(p−1)`** for the p-adic exponential series. Raising the term's norm to the `(p−1)` power clears the `(p−1)`-th root in `p^{−1/(p−1)}`, turning the valuation inequality into an honest geometric bound with ratio `p·‖x‖^{p−1}` — which is `< 1` exactly on the convergence ball `InExpBall`. That geometric form is precisely what feeds the cofinite/`atTop`-tends-to-zero summability criterion.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime; needed so `p − 1 ≥ 1` and for Legendre's formula (via the dependency `norm_factorial_le`).
- `L : Type*`, `[NormedField L] [NormedAlgebra ℚ_[p] L]` — a normed `ℚ_p`-algebra field; the `ℚ_p`-algebra structure is what makes `(n! : ℚ_[p])⁻¹ • xⁿ` and its norm meaningful (the scalar lives in `ℚ_[p]`, the vector in `L`). `[IsUltrametricDist L]` and `[CompleteSpace L]` are **explicitly omitted** for this lemma (line 77) — it is a pure norm estimate.
- `x : L` — the series argument.

Hypotheses (Lean side):
- `hn : 1 ≤ n` — the bound is stated for `n ≥ 1` (the `n = 0` term is the constant `1`, handled separately).

Conclusion (math): each exponential term decays geometrically (at the `(p−1)`-power level) with ratio `p·‖x‖^{p−1}`.

Conclusion (Lean): `‖(n.factorial : ℚ_[p])⁻¹ • x ^ n‖ ^ (p - 1) ≤ ‖x‖ ^ (p - 1) * ((p : ℝ) * ‖x‖ ^ (p - 1)) ^ (n - 1)`.

**Proof shape.** `norm_smul` / `norm_inv` / `norm_pow` / `mul_pow` / `inv_pow` reduce the LHS to `(‖n!‖^{p−1})⁻¹ · (‖x‖ⁿ)^{p−1}`; the inverted Legendre bound `norm_factorial_inv_pow_le p hn : (‖n!‖^{p−1})⁻¹ ≤ p^{n−1}` (itself derived from the project-local `norm_factorial_le`, which calls mathlib's Legendre `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`) gives `≤ p^{n−1}·(‖x‖ⁿ)^{p−1}`; a `pow`/exponent identity `n·(p−1) = (p−1) + (n−1)·(p−1)` plus `ring` rearranges to the geometric RHS.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma — the per-term decay estimate (decomposition cluster R5.E) that supplies the summand bound for `summable_padicExp_terms`. Not a `def`/structure, not a named theorem, not a `## Main results` entry (the file's main results are the isometry `norm_padicExp_sub_padicExp`, the functional equation `padicExp_add`, and the inversion theorems — this is plumbing beneath them).

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only and does not gate the lit search.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-liner check **n/a** (the body is a multi-step `calc`, not a one-line definition body).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | p-adic exponential series term bound factorial valuation geometric decay convergence ball              | yes  | `ord(xⁿ/n!) ≥ n·ord(x) − n/(p−1)`; `∑⌊n/pⁱ⌋ ≤ n/(p−1)` | UChicago REU (Gupta), Conrad "Infinite series in p-adic fields", Wikipedia "P-adic exponential function", arXiv math-ph/0402050 — the per-term valuation bound is the canonical convergence mechanism |
|  2 | WebSearch (general / sharp form) | p-adic exponential radius of convergence Legendre formula v_p(n!) norm of xⁿ/n!                         | yes  | radius `p^{−1/(p−1)}`; `v_p(n!) = (n − s_p(n))/(p−1)`; `‖xⁿ/n!‖` decreases via Legendre | Wikipedia "Legendre's formula", MIT exp.pdf (Vogan), Conrad notes, Eremin arXiv:1907.11902 — confirms the most general standard setting is any complete nonarchimedean field |
|  3 | WebSearch (named-after / aliases)| p-adic logarithm exponential isometry term-by-term valuation estimate ord(xⁿ/n!) geometric series bound | yes  | **`|1/n!|_F ≤ q^{ne/(p−1)}`, explicitly "provides a geometric series bound for the factorial terms"** | MIT exp.pdf (Vogan), Conrad, Jack Thorne Cambridge notes, World Scientific "Logarithm and exponential in a p-adic field" — the *geometric-bound* framing of the per-term estimate is exactly the target's content |
|  4 | ChatGPT MCP                      | (intended: "standard p-adic per-term bound for xⁿ/n!, its generality, geometric-series framing, history") | n/a  | —                                | ChatGPT MCP server referenced in `~/.claude.json` (`chatgpt-math/server.js`) but **no `mcp__chatgpt*` tool is exposed/callable in this session** (`/setup-chatgpt` MCP not active here). Recorded n/a with reason; WebSearch (3 channels) + the module's own citations (RJW Lem 5.14, Cassels §12, Washington §5.1) cover the standard-form question. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                | n/a  | (no references dir; no `refs/` store) | both directories absent — recorded n/a. The module docstring's inline citations (RJW TeX 1892–1897 "as stated"; Cassels §12; Washington §5.1) serve as the literature anchor. |
|  6 | nLab                             | p-adic exponential nonarchimedean disk of convergence isometry                                          | partial | nLab "p-adic number" routes the exp/log through the general nonarchimedean-analytic picture; radius `p^{−1/(p−1)}` and the isometry are the headline facts; for `p=2` ball is `< 1/2`, odd `p` strictly contains `< 1/p` | not a categorical concept; nLab has no standalone "per-term geometric bound" lemma — it is folklore plumbing beneath the isometry |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                | not a categorical concept (a real-valued metric estimate on the terms of a p-adic series). |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                | not an algebraic-geometry concept (an analytic/valuation term estimate, not scheme/sheaf theory). |
|  9 | MathOverflow / Math.StackExchange| p-adic exponential convergence "xⁿ/n!" norm bound each term valuation                                   | yes  | community consensus: convergence ⟺ terms → 0; explicit `N_p(xⁿ/n!)` upper bounds via Legendre; `v_p(n!) = (n − δ_p(n))/(p−1)`, `|n!|_p = p^{−(n−δ_p(n))/(p−1)}` | recurring Q&A; the per-term bound is treated as a routine valuation computation, never named — the geometric-decay packaging is implicit |
| 10 | recent arXiv (last 5 years)      | arXiv 2024–2025 p-adic exponential logarithm convergence factorial valuation bound nonarchimedean field | partial | arXiv:2408.00353 (bounds on `v_p(n!)` via Legendre-de Polignac), arXiv:2504.03430 (P-adic L-series convergence in nonarchimedean/Tate-algebra setting) | modern work reuses the classical Legendre per-term bound; no new canonical reformulation supersedes `ord(xⁿ/n!) ≥ n·ord(x) − n/(p−1)` |

The protocol passed: WebSearch ran ≥3 distinct queries at three generality levels (specific geometric-decay form / general radius+Legendre form / named-isometry+geometric-bound aliases); ChatGPT MCP recorded n/a with reason (no callable tool in session); local references recorded n/a with reason (dirs absent); nLab checked; nCatLab / Stacks recorded n/a with reason; MathOverflow and recent arXiv each checked.

### Literature summary (Phase 3)

Concept identified as: **the per-term estimate for the p-adic exponential series `∑ xⁿ/n!` — i.e. the bound `ord(xⁿ/n!) ≥ n·ord(x) − n/(p−1)` (equivalently `|xⁿ/n!|` is geometrically dominated), the engine of convergence on the disk `‖x‖ < p^{−1/(p−1)}`.**

Sources agree on the standard form: **yes** — every source (Conrad, MIT exp.pdf, Wikipedia, the REU notes, MathOverflow, recent arXiv) gives the *same* per-term mechanism: `v_p(n!) = (n − s_p(n))/(p−1)` (Legendre), hence `|1/n!|_p` grows at most like `p^{n/(p−1)}`, hence `|xⁿ/n!|` is bounded by a geometric series with ratio `< 1` precisely when `‖x‖ < p^{−1/(p−1)}`. The MIT/Vogan notes state it verbatim as "`|1/n!|_F ≤ q^{ne/(p−1)}`, which provides a geometric series bound for the factorial terms" — this is the target lemma's exact mathematical content.

Most general standard form: over **any complete nonarchimedean field extending `ℚ_p`** (the target's general `L` already matches this), each term `xⁿ/n!` satisfies the geometric per-term bound; the bound is the standard route to summability. The literature uses the **valuation form** (`ord(xⁿ/n!) ≥ …`); the target uses the **normwise `(p−1)`-power-level form**, which is the rpow-free Lean-friendly transcription of the identical inequality.

Generality dimensions where the literature varies:
- **Underlying field**: `ℚ_p` → any complete nonarchimedean field / `ℂ_p`. The target's `L` (a normed `ℚ_p`-algebra field, with completeness/ultrametricity *not even required* for this lemma) is at or above the most general standard setting. ✓ already maximal.
- **Encoding**: valuation inequality (`ord ≥ …`) vs. normwise geometric bound (target). These are equivalent; the target's is the formalisation-idiomatic, rpow-free spelling.
- **Constant in the ratio**: literature ratio is effectively `p^{1/(p−1)}·‖x‖` per term; the target's `(p−1)`-power-level ratio `p·‖x‖^{p−1}` is the exact algebraic image of that (raise to the `(p−1)` power). No looseness — this is a faithful, not a weakened, transcription.

Disagreement with the literature: **none on content.** The only "disagreement" is presentational: the literature never isolates this as a *named standalone lemma* — it is folklore plumbing stated en route to the headline isometry `‖exp x − 1‖ = ‖x‖`. The target makes it a first-class reusable lemma, which is a Lean-engineering choice, not a mathematical divergence.

---

### Generality analysis — `norm_factorial_inv_smul_pow_le`

Literature-standard form (from Phase 3): on the convergence disk over any complete nonarchimedean field ⊇ `ℚ_p`, `ord(xⁿ/n!) ≥ n·ord(x) − n/(p−1)`, equivalently each term is dominated by a geometric series in `‖x‖`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|---------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L] [NormedAlgebra ℚ_[p] L]` (with `IsUltrametricDist`, `CompleteSpace` **omitted**) | normed `ℚ_p`-algebra field | any (complete) nonarchimedean field ⊇ `ℚ_p` | NO | already maximal — and notably *more* general than the rest of the file, since this lemma drops completeness AND ultrametricity (it is a pure factorial-norm × power estimate). The `ℚ_p`-algebra structure is genuinely needed: the scalar `(n!)⁻¹` lives in `ℚ_[p]` and Legendre is a `ℚ_p` fact. |
| 2 | `hn : 1 ≤ n` | `n ≥ 1` | `n ≥ 1` (the `n = 0` constant term is separate) | NO | the geometric form `…^{n−1}` requires `n ≥ 1` for the truncated `n − 1` to behave; `n = 0` is the trivial constant term, correctly excluded. |
| 3 | conclusion: `(p−1)`-power-level geometric bound with ratio `p·‖x‖^{p−1}` | rpow-free normwise form | valuation form `ord(xⁿ/n!) ≥ n·ord(x) − n/(p−1)` (equivalent) | NO (not a weakening) | the two are equivalent; the target's ratio `p·‖x‖^{p−1}` is the *exact* `(p−1)`-power image of the standard `p^{1/(p−1)}‖x‖`. No constant looseness (contrast the sibling `norm_padicExp_sub_one_sub_self_le`, whose constant `p` *was* loose). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.**
Number of weakening opportunities found: **0.** Hypotheses are maximal (indeed broader than the file default — completeness and ultrametricity are omitted); the conclusion is a faithful, constant-tight transcription of the literature per-term bound. There is no narrower-than-standard axis. (This is *stronger* than the sibling tail-bound lemma, whose constant was non-sharp.)

Proposed restatement: **none** (no weakening available).
Cost of any restatement: n/a.

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses / instances? | no | — | hypotheses are already typeclasses (`NormedField`/`NormedAlgebra`); nothing bundled to unbundle. |
|  2 | sequences / metric → filters / nets / topological? | no | — | this is a single per-term inequality, no sequential limit to filter-ise. (The *consumer* `summable_padicExp_terms` already uses the filter/cofinite criterion `summable_iff_tendsto_cofinite_zero`.) |
|  3 | construct an object → universal-property class? | no | — | an estimate, not a construction. |
|  4 | set-with-closure-predicate → bundled substructure? | no | — | n/a. |
|  5 | vector-space/metric/field-specific → weaken typeclass hierarchy? | partial | already maximally general `L`; the only real organisational lever is one layer **down**: there is no nonarchimedean/p-adic `exp` (with a convergence-ball + per-term-bound API) in mathlib at all, so the idiomatic move is to introduce that namespace and host this lemma in it | the win lives at the *definition* layer (a mathlib `PadicExp` / nonarchimedean-exp development), not in this lemma's signature. |
|  6 | 1-categorical → higher-categorical? | no | — | n/a. |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive/ordered structure? | no | — | the only concrete object is `(p:ℝ)` in the ratio, which is intrinsic (it *is* the prime); the `(p−1)`-power encoding is the rpow-avoidance idiom, already idiomatic. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for the lemma as stated). The lemma's signature is already idiomatic — rpow-free `(p−1)`-power encoding, maximal typeclass generality, the scalar correctly in `ℚ_[p]`. The only organisational improvement is one layer down: mathlib has **no** p-adic / nonarchimedean exponential definition, so the mathlib-idiomatic home for this estimate is a yet-to-exist nonarchimedean-`exp` namespace (with `InExpBall`/convergence-ball + summability + isometry API), where this would be the per-term decay lemma. That is a def-development decision, not a reformulation of this signature. One-line reason it is not itself a modernisation move: it is a concrete, already-idiomatic valuation-derived norm estimate; the modernisation question is entirely about whether to upstream the underlying `padicExp` machinery.

---

### Diamond / defeq risk — `norm_factorial_inv_smul_pow_le`

**n/a — declaration kind is `theorem`.** (Phase 4.5 runs only for `def`/`class`/`instance`.)

---

### Mathlib search-status: `norm_factorial_inv_smul_pow_le`

[A] Lean-Finder       "p-adic exponential term bound", "norm of x^n over n! geometric"   n/a: Lean-Finder web UI not callable in this environment — substituted with exhaustive grep over the mathlib tree (method D) for every candidate name/shape.
[B] Loogle            `‖_⁻¹ • _ ^ _‖ ^ _ ≤ _ * (_ * _) ^ _`, `‖(_ !)⁻¹ • _ ^ _‖ ≤ _`   no hits: grep for `‖…•…‖…≤…*…^` restricted to factorial/geometric shapes in `Mathlib/Analysis/Normed/` returns empty. The `(n!)⁻¹ • _ ^ n` shape DOES occur in mathlib, but only in `Mathlib/Analysis/Complex/TaylorSeries.lean` (Taylor coefficients `(n!)⁻¹•(z−c)ⁿ•iteratedDeriv…`, archimedean ℂ) and `Mathlib/Analysis/Complex/Liouville.lean` — neither is a p-adic per-term decay bound.
[C] LeanSearch        "p-adic exponential per-term geometric bound", "norm factorial inverse times power bound"   no hits (web UI not callable; substituted with method D): the only `‖exp-term‖ ≤ …` artifacts in mathlib are archimedean (`Complex.exp_bound`, `Complex.norm_exp_sub_one_sub_id_le`).
[D] Grep mathlib src  `factorial.*⁻¹.*•`, `padicExp`, `InExpBall`, `expRadius`, `norm_factorial`, geometric-bound shapes over `.lake/packages/mathlib/Mathlib/`   no relevant hits: (i) NO `padicExp`/`InExpBall`/`expRadius` anywhere in `Mathlib/NumberTheory/Padics/` (the only file mentioning exp there is `PadicNumbers.lean`, unrelated). (ii) NO `norm_factorial` lemma exists at all. (iii) The `(n!)⁻¹•xⁿ` matches are all in `Mathlib/Analysis/Complex/` (Taylor/Liouville/Exponential — archimedean) plus `QuaternionExponential.lean` — none p-adic.
[E] Name pattern      `padicExp`, `expSeries`, `NormedSpace.exp`, `norm_expSeries`, `norm_factorial`   `padicExp` does not exist in mathlib. `NormedSpace.exp` exists but its API (`expSeries_radius_eq_top : radius = ∞`, `norm_expSeries_summable*`) is the **archimedean** regime (`radius = ∞` is *false* p-adically) with **no** `IsUltrametricDist` / nonarchimedean support and **no** per-term decay bound. `norm_factorial` returns nothing.

Searched for both:
- the user's current form (`‖(n!)⁻¹ • xⁿ‖^{p−1} ≤ ‖x‖^{p−1}·(p‖x‖^{p−1})^{n−1}`) — not in mathlib.
- the literature-standard form (the valuation bound `ord(xⁿ/n!) ≥ n·ord(x) − n/(p−1)`; the geometric per-term domination; the general-`NormedSpace.exp` analogue) — none exists p-adically in mathlib.

Concluded: **not in mathlib (all five methods exhausted, plus the literature-standard form).** Mathlib has the **building blocks** — Legendre's formula `sub_one_mul_padicValNat_factorial_lt_of_ne_zero` (`Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:591`), `Padic.norm_eq_zpow_neg_valuation` (`Mathlib/NumberTheory/Padics/PadicNumbers.lean:1053`), `zpow_le_zpow_right₀`, `inv_anti₀`, `mul_pow`/`pow_add`/`pow_mul` — but **not** the packaged per-term geometric bound, **no** p-adic exponential, and **no** nonarchimedean tail/decay lemma on `NormedSpace.exp`. The archimedean analogues (`Complex.exp_bound`, `Complex.norm_exp_sub_one_sub_id_le`) are inapplicable to a p-adic field `L`.

---

### Call sites — `norm_factorial_inv_smul_pow_le`

Internal use count: **2** (within the project, NOT counting the declaring theorem) — one of them in a **different file**.
External-to-file callers: **1 distinct file** (`ResidueZeta.lean`); the second use is in the same file (`PadicExp.lean`, a different theorem).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `PadicExp.lean:124` | `lt_of_le_of_lt (norm_factorial_inv_smul_pow_le p x (by omega)) hsmall` — supplies the per-term bound that, combined with the geometric tendsto-zero, proves `summable_padicExp_terms` (THE summability of the p-adic exponential series — the foundational result the whole file's isometry / functional-equation / inversion theory rests on). |
| `ResidueZeta.lean:62` | `≤ ‖w‖ ^ (p − 1) * ((p : ℝ) * ‖w‖ ^ (p − 1)) ^ (n − 1) := norm_factorial_inv_smul_pow_le p w (by omega)` — the first `calc` step of the private `norm_factorial_inv_smul_pow_le_quad`, which derives the quadratic per-term bound `‖(n!)⁻¹•wⁿ‖ ≤ p·‖w‖²` (n≥2) that powers `norm_padicExp_sub_one_sub_self_le` → the residue/pole proof of `ζ_p` at `s=1` (RJW §7, Lemma 7.2(ii)). |

Inline-derivation grep (was the equivalent re-derived elsewhere without calling the lemma?):
  - (none) — the RHS pattern `‖·‖^(p−1) * ((p:ℝ)*‖·‖^(p−1))^(·−1)` occurs at only three sites: this lemma's statement+proof (`PadicExp.lean:83,89`) and `ResidueZeta.lean:61`, which is the line *receiving* the call result (not an independent re-derivation). No consumer bypasses the lemma; the two proof-dependency lemmas (`norm_factorial_le`, `norm_factorial_inv_pow_le`) are used *only* inside `PadicExp.lean` to build this lemma, never to re-derive its conclusion downstream.

What the call-sites pattern tells you: **K = 2 internal uses, including 1 cross-file consumer, no inline re-derivation.** Per the Phase-6 signal table this is a *real-API* signal (consumers genuinely depend on it; one across a file boundary) — it leans toward a YES-family bucket on composability grounds. The lemma is not junk and not a one-off wrapper. But — exactly as with the sibling `norm_padicExp_sub_one_sub_self_le` — its mathlib-worth does not ultimately rest on local reuse; it rests on whether the *p-adic exponential development it is about* is upstreamed at all (see Verdict).

---

### Composition check (Phase 6)

Can `norm_factorial_inv_smul_pow_le` be derived from mathlib in ≤3 chained calls?

Attempt 1: a mathlib per-term exp-series bound, specialised.
  - Mathlib decls used: `Complex.exp_bound` / `NormedSpace.norm_expSeries_*`.
  - Result: **fails** — `Complex.exp_bound` is archimedean (`ℂ`, ratio governed by `n!` growing the *other* way); `NormedSpace.expSeries` is built on `radius = ∞` (false p-adically) and has no per-term *decay* bound. Neither transfers to a p-adic field `L`.

Attempt 2: compose Legendre + norm-of-cast directly inline.
  - Mathlib decls used: `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`, `Padic.norm_eq_zpow_neg_valuation`, `zpow_le_zpow_right₀`.
  - Result: **fails as a ≤3-call composition** — this is exactly the *internal* structure the project already factored into `norm_factorial_le` → `norm_factorial_inv_pow_le` → this lemma. Reaching the geometric RHS additionally needs `norm_smul`/`norm_inv`/`norm_pow`/`mul_pow`/`inv_pow` rewrites, a `mul_le_mul_of_nonneg_right`, and a non-trivial exponent identity `n·(p−1) = (p−1) + (n−1)·(p−1)` closed by `ring`. That is a genuine multi-step proof (≈10 rewrite/lemma steps across two helper lemmas), not a 1–3-call composition.

Attempt 3: `simp`/`gcongr` one-liner.
  - Result: **fails** — no `simp` set or `gcongr` lemma knows the p-adic factorial-norm Legendre bound; the inverted-Legendre step is the load-bearing inequality and is project-local.

Conclusion: **NOT-COMPOSABLE.** There is no p-adic exponential or per-term decay bound in mathlib to compose against; the only exp per-term bounds are archimedean and do not transfer. The lemma rests on a genuine (multi-lemma) p-adic argument, with mathlib supplying only the atomic Legendre/valuation facts.

---

## Verdict: `norm_factorial_inv_smul_pow_le`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the lemma is the **normwise, rpow-free transcription of the standard per-term bound `ord(xⁿ/n!) ≥ n·ord(x) − n/(p−1)`** — universally agreed across sources (Conrad, MIT/Vogan exp.pdf, Wikipedia, MathOverflow, recent arXiv), and explicitly framed in the MIT notes as "a geometric series bound for the factorial terms." It is the convergence engine of the p-adic exp series. It is *folklore plumbing*, never isolated as a named lemma in the literature.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — hypotheses are maximal (and broader than the file default: completeness + ultrametricity omitted), and the conclusion is a faithful, constant-tight transcription with no weakening axis. Phase 4c: no modern-idiom reformulation of *this signature*; the only organisational lever is one layer down (a nonarchimedean-`exp` namespace mathlib lacks).
- Mathlib search (Phase 5): **not in mathlib** — no p-adic / nonarchimedean exp; no per-term decay bound on `NormedSpace.exp`; no `norm_factorial` lemma. Building blocks (Legendre `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`, `Padic.norm_eq_zpow_neg_valuation`) exist; the packaged statement does not.
- Composition check (Phase 6): **NOT-COMPOSABLE** (a genuine multi-lemma p-adic argument; the only exp per-term bounds in mathlib are archimedean).
- Call sites (Phase 6.0): **K = 2**, including **1 cross-file consumer** (`ResidueZeta.lean`), no inline re-derivation — a real-API composability signal.

**Rationale (why BORDERLINE, not a clean YES/NO):**

This is a *true, genuinely missing-from-mathlib, maximally-general, constant-tight, sorry-free, actually-reused* p-adic estimate (K = 2, one cross-file). On its own merits — generality MAXIMAL (Phase 4b), NOT-COMPOSABLE (Phase 6), no mathlib hit (Phase 5), real consumers — it reads like a strong `YES-add-as-is`. It is decidedly **not** a NO: mathlib has no analogue, and it cannot be inlined as a ≤3-call composition. So why BORDERLINE?

Because the lemma **cannot be PR'd standalone — it is inseparable from a definition layer mathlib does not have**, and that makes the decision a project/community-policy judgment the skill must defer:

1. **It presupposes the p-adic exponential series itself.** The lemma's *content* is "the `n`-th term of `exp(x) = ∑xⁿ/n!` decays geometrically." Its direct downstream purpose is `summable_padicExp_terms` — i.e. it exists *to make the p-adic `exp` converge*. Mathlib has **no** p-adic / nonarchimedean exponential (`NormedSpace.exp` is archimedean: `expSeries_radius_eq_top`, no `IsUltrametricDist` support). Upstreaming this lemma in isolation would be orphaned — there is no `padicExp`, no `InExpBall`, no convergence-ball API for it to live beside. The honest mathlib contribution is a *whole nonarchimedean-`exp` development* (def + convergence ball + summability + the isometry `norm_padicExp_sub_one` + log + inversion), with this per-term bound as one supporting lemma. **Whether to undertake that BIG, multi-decl upstreaming is a human/community decision** — the same one flagged for the sibling `norm_padicExp_sub_one_sub_self_le` (BORDERLINE in the ledger) and consistent with `InExpBall` (NO-composable: a bare predicate that only makes sense inside such a development).

2. **Packaging / naming within that development is a taste call.** In the literature this per-term bound is *never a named lemma* — it is an inline valuation computation en route to the headline isometry. A mathlib reviewer might want it (a) as a public `@[simp]`-able geometric per-term bound, (b) folded into the summability proof as a `have`, or (c) restated against a general nonarchimedean-`exp` `expSeries`-style object rather than the bare `(n!)⁻¹•xⁿ` family. The `(p−1)`-power-level rpow-free encoding (excellent for *this* project's rpow-avoidance) might also be re-expressed via `Real.rpow` / valuation directly in a general mathlib setting. Which packaging is "right" is exactly the judgment the skill should not make alone.

3. **This is the per-term *engine*, not a headline result.** The named, textbook p-adic-exp facts are the isometry `‖exp x − 1‖ = ‖x‖` and the functional equation `exp(x+y)=exp(x)·exp(y)` (both proved in this file). If anything from this circle is "the" mathlib contribution, it is the def + isometry + functional equation, with this per-term bound as plumbing. Whether plumbing of this kind ships as first-class public API or as a `private`/inlined step is a packaging judgment for the human.

The K = 2 (cross-file) call pattern reinforces that the lemma is *genuinely useful infrastructure* — but its mathlib-worth is entirely contingent on the upstreaming decision about the p-adic-exp machinery as a whole, not on standalone novelty. That contingency is the BORDERLINE.

**Numbered questions (≤5):**

1. Do you intend to upstream the project's p-adic / nonarchimedean **exponential development** to mathlib as a unit (the `padicExp` definition + `InExpBall` convergence ball + `summable_padicExp_terms` + the isometry `norm_padicExp_sub_one` + `padicExp_add` + the `log` and inversion)? This per-term bound should travel *with* that development — it is meaningless without the `exp` series, which mathlib does not have.
2. If yes to (1): should this lemma ship as **first-class public API** (a named per-term geometric bound), or be **folded into the `summable_padicExp_terms` proof** as a local `have`/private step (its only "headline" role is feeding summability + the residue-proof quadratic tail)?
3. If yes to (1): within a general mathlib nonarchimedean-`exp` namespace, do you want the bound stated against a **general `expSeries`-style object** (a `PadicExp`/nonarchimedean-`exp` API), or kept against the concrete `(n!)⁻¹•xⁿ` family as here? And keep the **rpow-free `(p−1)`-power encoding**, or restate via `Real.rpow`/valuation in the general setting?
4. If you do **not** plan to upstream the p-adic-exp machinery: then this lemma is correctly a permanent project-local helper (K = 2, feeding `summable_padicExp_terms` and the residue proof), and should be dropped from mathlib consideration. Is that the case?

**Next action:** user answers the questions; re-run `/mathlibable norm_factorial_inv_smul_pow_le` — ideally **together with `/mathlibable PadicLFunctions.padicExp`**, since the def's upstreaming verdict governs this lemma's. Likely resolutions:
  - "Upstream the p-adic-exp development" → flips to **YES-add-as-is** (the lemma is maximally general, constant-tight, NOT-COMPOSABLE, and reused — it qualifies cleanly *once* the `padicExp` def it depends on is also being upstreamed), shipped as part of the nonarchimedean-`exp` PR series; packaging (public vs. inlined, concrete vs. general-`expSeries`) per the answers to Q2/Q3.
  - "Keep project-local" → drop from mathlib consideration; it stays fit-for-purpose infrastructure feeding the exp summability and the residue/pole proof.

---

## Next step

User answers the four numbered questions above; re-run `/mathlibable norm_factorial_inv_smul_pow_le` (preferably alongside `/mathlibable PadicLFunctions.padicExp`, since this lemma's verdict is governed by the upstreaming decision on the `padicExp` definition it underpins) to resolve to either `YES-add-as-is` (upstream the nonarchimedean-exp development; this lemma ships with it as a maximally-general per-term decay bound) or drop-from-consideration (keep as project-local infrastructure for `summable_padicExp_terms` and the §7 residue proof).
