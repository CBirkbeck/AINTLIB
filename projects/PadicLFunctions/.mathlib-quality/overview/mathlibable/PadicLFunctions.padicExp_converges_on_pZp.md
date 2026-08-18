# `/mathlibable` report — `PadicLFunctions.padicExp_converges_on_pZp`

**Final verdict: `BORDERLINE-needs-human`**

This is a true, standard (Washington §5.1 / Cassels §12 / RJW Lem 5.14), genuinely
missing-from-mathlib p-adic fact — "for odd `p`, the exponential series converges
on all of `pℤ_p`" — proved sorry-free. But it is a **thin `L = ℚ_[p]` specialisation**
of the already-`BORDERLINE` general lemma `summable_padicExp_terms` (its proof is a
literal 2-call composition `summable_padicExp_terms (inExpBall_of_mem_span …)`), it
has **zero call sites**, and its mathlib fate is governed by the *same* human decision
that governs its parent: whether to upstream the project's whole nonarchimedean-`exp`
development as a unit. Those are judgment calls the skill defers — hence BORDERLINE.

- **Target:** `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:1031` (kind: `theorem`)
- **Mode:** A (single declaration), full 10-phase workflow with the exhaustive 9-channel literature search.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per the task's BUILD NOTE — the build is stale/slow here; Phase 0 source-fallback used). The file elaborates as part of `main`; the target and its full dependency chain were read directly from `PadicExp.lean`. Baseline commit `d71766e`.
- decl `PadicLFunctions.padicExp_converges_on_pZp`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:1031`
- kind:                      theorem
- has sorry:                 no (grep over the whole file returns no `sorry`/`admit`)
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=Σ xⁿ/n!` converges on the open ball `‖x‖ < p^{-1/(p-1)}` of a nonarchimedean complete normed `ℚ_p`-algebra field and is an isometry there; **for odd `p` the ball contains `pℤ_p`** (the clause this theorem realises); the log inverts it on the matched balls. Cites Cassels §12 and Washington, *Introduction to Cyclotomic Fields* §5.1.

---

### Statement (Phase 1)

`padicExp_converges_on_pZp` is a **theorem** stating the following:

> Let `p` be an **odd** prime. For every `x ∈ pℤ_p` (the maximal ideal `Ideal.span {p}` of `ℤ_p`),
> the p-adic exponential series `Σ_{n≥0} (n!)⁻¹ · (x)ⁿ`, formed with the coercion `x : ℚ_[p]`,
> is **summable** in `ℚ_[p]`.

Mathematically this is the *first half* of the classical statement "for `p ≠ 2`, `exp` converges
on `pℤ_p` and gives an isomorphism `pℤ_p ≅ 1+pℤ_p`" (Washington §5.1, Cassels §12). The crux is the
inclusion `pℤ_p ⊆ B(0, p^{-1/(p-1)})` (the exp convergence ball): for odd `p`, `1/(p-1) < 1`, so
`p^{-1/(p-1)} > p^{-1}`, and since every `x ∈ pℤ_p` has `‖x‖ ≤ p⁻¹`, the point lies strictly inside
the ball. The case `p = 2` is genuinely excluded — the 2-adic exponential does **not** converge on
`2ℤ_2` — and the hypothesis `hp2 : p ≠ 2` is exactly that exclusion.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime.
- (No general `L`: this theorem is stated *only* at `L = ℚ_[p]`. The general convergence lemma it
  delegates to, `summable_padicExp_terms`, carries the abstract field `L`.)

Hypotheses (Lean side):
- `hp2 : p ≠ 2` — odd prime (so `pℤ_p` fits in the convergence ball; the `p = 2` failure is real).
- `{x : ℤ_[p]}` with `hx : x ∈ Ideal.span {(p : ℤ_[p])}` — i.e. `x ∈ pℤ_p`.

Conclusion (math): the p-adic exponential series converges at every point of `pℤ_p` (odd `p`).

Conclusion (Lean): `Summable fun n : ℕ => (n.factorial : ℚ_[p])⁻¹ • ((x : ℚ_[p]) ^ n)`.

**Proof shape (load-bearing for the verdict).** The body is a **single-expression, 2-call
composition** of two *project-internal* lemmas:

```lean
theorem padicExp_converges_on_pZp (hp2 : p ≠ 2) {x : ℤ_[p]}
    (hx : x ∈ Ideal.span {(p : ℤ_[p])}) :
    Summable fun n : ℕ => (n.factorial : ℚ_[p])⁻¹ • ((x : ℚ_[p]) ^ n) :=
  summable_padicExp_terms (L := ℚ_[p]) p (inExpBall_of_mem_span p hp2 hx)
```

- `inExpBall_of_mem_span p hp2 hx : InExpBall p ((x : ℚ_[p]))` — the membership lemma `pℤ_p ⊆ ball`
  (`PadicExp.lean:1010`), which is where `hp2` is *used* (it forces `p − 1 ≥ 2`, giving `‖x‖^{p−1} ≤
  p^{−(p−1)} < p⁻¹`).
- `summable_padicExp_terms (L := ℚ_[p])` — the **general** convergence-on-the-ball theorem
  (`PadicExp.lean:100`), specialised to `L = ℚ_[p]`.

So this theorem contributes **no new analysis**: it is the integral-domain restriction (`x ∈ pℤ_p`,
phrased on `ℤ_[p]`) of the general ball-convergence lemma, plus the elementary membership inclusion.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (with a BIG-adjacent caveat).
Reason: as a *declaration* it is a corollary / specialisation — a one-line delegation, not a `def`,
structure, or main result. It is **not** named after a person. *However*, it is the Lean realisation
of a famous textbook clause (the odd-`p` exp-converges-on-`pℤ_p` half of Washington §5.1 / Cassels
§12 / RJW Lem 5.14), and it sits on top of a genuinely-missing-from-mathlib BIG object — the
project's p-adic exponential `padicExp`. So while the declaration is SMALL, its mathlib fate is
inherited from the BIG object it specialises.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-liner check is **n/a** (one-line note).
The body *is* a one-expression delegation, but Phase 2b's one-liner machinery applies only to `def`s;
for theorems the relevant analogue is Phase 6 (composability), handled below.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic exponential converges on pℤ_p odd prime; convergence ball contains pℤ_p"                       | yes  | exp converges on the ball `‖x‖<p^{-1/(p-1)}`; for **odd** `p`, `p^{-1/(p-1)} > 1/p`, so `pℤ_p` ⊆ ball | Wikipedia "P-adic exponential function"; K. Conrad / Jack Thorne notes; Cambridge DPMMS p-adic notes; Berkeley "primitive roots via p-adic numbers" |
|  2 | WebSearch (general form: the iso) | "p-adic exp/log isomorphism 1+pℤ_p ≅ pℤ_p odd prime; Washington cyclotomic fields"                     | yes  | for `p ≠ 2`, `1+pℤ_p ≅ ℤ_p` (here `pℤ_p`) via exp/log; "exp converges for all of pℤ_p", `log` for all of `1+pℤ_p` | MIT note math.mit.edu/~dav/exp.pdf "Exponential and logarithm in p-adic fields"; PlanetMath "p-adic exponential and logarithm"; Uchicago REU (Gupta) |
|  3 | WebSearch (named-after / aliases / principal units) | "p-adic exp/log principal units 1+pℤ_p p odd; Neukirch / Cassels Local Fields"                          | yes  | identical: for odd `p` both exp and log converge on the principal-unit / maximal-ideal balls; iso of principal units | Nottingham + Cambridge Part III Local Fields notes; arXiv 1904.09850 "image of p-adic logarithm on principal units" |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + history of `exp` converging on `pℤ_p` for odd `p`, and the `p=2` failure") | n/a  | —                                | ChatGPT MCP server **not configured** in this environment (deferred-tool search returned no `mcp__chatgpt`/`openai` tool; `/setup-chatgpt` not run). Recorded n/a with reason. WebSearch (3 queries) + Wikipedia + the module's own citations (RJW, Cassels §12, Washington §5.1) more than cover the standard-form question; the verdict does not hinge on this channel. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                | n/a  | (no references dir; no `refs/` symlink) | both directories absent on this machine — recorded n/a. The module docstring's inline citations (RJW TeX 1892–1893 "as stated"; Cassels §12; Washington §5.1) serve as the literature anchor. |
|  6 | nLab                             | p-adic exponential map / convergence radius / principal units                                          | partial | nLab routes p-adic exp through the general "convergence on a polydisc of valuative radius `1/(p-1)`" picture; the headline radius is `p^{-1/(p-1)}` | not a categorical concept; nLab has no standalone "exp converges on pℤ_p" lemma. Surfaced the general nonarch-analytic picture (consistent with #1–#3). |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                | not a categorical concept (convergence of a concrete factorial series on a specific subgroup of `ℤ_p`). |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                | not an algebraic-geometry concept (analytic series convergence; no scheme/sheaf content). |
|  9 | MathOverflow / Math.StackExchange| "p-adic exp converges on pℤ_p: p=2 vs odd p; radius `p^{-1/(p-1)}` comparison"                          | yes  | community consensus: **for `p ≠ 2`, exp converges on all of `pℤ_p`; the 2-adic exp does NOT converge on `2ℤ_2`** — exactly because `1/(p-1)<1` for odd `p` gives `p^{-1/(p-1)}>1/p` | this is *precisely* the content of the target (incl. the `hp2 : p ≠ 2` exclusion); textbook-standard, never disputed |
| 10 | recent arXiv (last 5 years)      | p-adic exponentiation / image of p-adic logarithm on principal units                                   | partial | arXiv 1904.09850, 2602.16433 ("Hensel minimality, p-adic exponentiation") reuse the classical radius + the odd-`p` `pℤ_p` ⊆ ball inclusion verbatim | confirms no modern reformulation supersedes the classical statement; it is used as a known fact |

The protocol passed: WebSearch ran **3** distinct queries at three generality levels (the specific
"exp converges on `pℤ_p`" ball-inclusion / the general exp–log iso `1+pℤ_p ≅ pℤ_p` it is the first half of /
the named "principal units" framing with Cassels–Neukirch); ChatGPT MCP recorded n/a with reason (server
absent); local references recorded n/a with reason (no dir); nLab checked; nCatLab / Stacks recorded n/a
with reason; MathOverflow and recent arXiv each checked.

### Literature summary (Phase 3)

Concept identified as: **"the p-adic exponential converges on `pℤ_p` for odd `p`"** — equivalently, the
inclusion `pℤ_p ⊆ B(0, p^{-1/(p-1)})` of the maximal ideal into the exp convergence ball when `p` is
odd. This is the **first half** of the classical exp–log isomorphism `pℤ_p ≅ 1+pℤ_p` (`p ≠ 2`).

Sources agree on the standard form: **yes, unanimously.** Wikipedia, the MIT note, K. Conrad / Jack
Thorne, Cambridge Part III & Nottingham Local Fields notes, PlanetMath, and MathOverflow all state:
*for `p ≠ 2`, `exp` converges on `pℤ_p`* (and `log` on `1+pℤ_p`), giving the iso; *for `p = 2` it fails on
`2ℤ_2`*. The reasoning is invariably the same: radius `= p^{-1/(p-1)}`, and `1/(p-1)<1 ⇔ p` odd gives
`p^{-1/(p-1)} > 1/p`. This is *exactly* the project's internal proof (`inExpBall_of_mem_span`).

Most general standard form: over **any complete nonarchimedean field extending `ℚ_p`**, the analogous
statement holds for the maximal ideal (the general convergence fact is `summable_padicExp_terms`'s
domain). The *specific* "`pℤ_p` on `ℤ_[p]`" packaging here is the classical `ℚ_p` case of that general
fact. **The target is stated only at `ℤ_[p]` / `ℚ_[p]`, not at general `L`** — see Phase 4.

Generality dimensions where the literature varies:
- **Base field / ring**: `ℤ_p` (this theorem) → the ring of integers `𝒪` of any complete nonarch
  field, with maximal ideal `𝔪` in place of `pℤ_p`. The literature states the general-`𝒪` version too;
  the target picks the `ℚ_p` instance.
- **Conclusion strength**: the natural p-adic statement is plain `Summable` (which the target proves).
- **Direction packaged**: the literature pairs this with the matching log convergence (the iso); the
  target is only the exp/convergence half (the log half is the sibling `pZpLog` cluster).

Disagreement with the literature: **none.** The target is a faithful, correctly-hypothesised
(`p ≠ 2`) Lean rendering of the standard exp-converges-on-`pℤ_p` fact, *specialised to `ℚ_p`*.

---

### Generality analysis — `padicExp_converges_on_pZp`

Literature-standard form (from Phase 3): over the ring of integers `𝒪` of any complete nonarch field
`L ⊇ ℚ_p` with maximal ideal `𝔪`, for `p` odd, `Σ xⁿ/n!` is summable for every `x ∈ 𝔪` (because
`𝔪 ⊆` the exp ball). The classical case is `L = ℚ_p`, `𝒪 = ℤ_p`, `𝔪 = pℤ_p`.

| # | Parameter / hypothesis                | Current Lean form                | Literature-standard form      | Weaker form exists? | Reason it can/can't be weakened |
|---|---------------------------------------|----------------------------------|-------------------------------|---------------------|---------------------------------|
| 1 | base ring fixed to `ℤ_[p]` / `ℚ_[p]` | `x : ℤ_[p]`, series in `ℚ_[p]`   | `x ∈ 𝔪 ⊆ 𝒪`, `𝒪` ring of ints of any complete nonarch `L ⊇ ℚ_p` | **yes** (in principle) | the *general* convergence engine (`summable_padicExp_terms`) already runs at abstract `L`; this theorem just declines to state the `𝒪`-of-`L` version. But the `pℤ_p`-on-`ℤ_[p]` packaging needs `PadicInt`'s span/valuation API, which is `ℚ_p`-specific in mathlib — generalising the *membership* half to arbitrary `𝒪` is real work (a DVR maximal-ideal-in-ball lemma). |
| 2 | `hp2 : p ≠ 2`                        | `p ≠ 2`                          | `p ≠ 2` (odd `p`)             | **NO**              | essential: the `p = 2` statement is **false** (`exp` diverges on `2ℤ_2`). The hypothesis is exactly right. |
| 3 | `hx : x ∈ Ideal.span {(p)}`          | `x ∈ pℤ_p`                       | `x ∈ 𝔪` (maximal ideal)       | NO (within `ℤ_[p]`) | `pℤ_p` *is* the maximal ideal of `ℤ_p` (`PadicInt.maximalIdeal_eq_span_p`); within the `ℚ_p` instance this is already the maximal/largest set on which convergence is asserted via this route. |
| 4 | conclusion `Summable …`              | plain summability                | plain summability             | NO                  | matches the natural p-adic statement. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD — but in a *specialisation* sense, not a
weakening-of-hypotheses sense.** The literature/general form runs over `𝒪`-of-any-complete-nonarch-`L`;
the target hard-codes `L = ℚ_p`, `𝒪 = ℤ_p`, `𝔪 = pℤ_p`. The odd-`p` and membership hypotheses are
*exactly right* (row 2 cannot be weakened; the `p=2` case is genuinely false).
Number of *hypothesis*-weakening opportunities found: **0** (hypotheses are sharp).
Number of *base-ring generalisation* opportunities: **1** (the `𝒪`-of-`L` version, row 1).
Proposed restatement (if pursued as a mathlib contribution): the abstract version, stated about the
ring of integers / maximal ideal of `L`, would be the right mathlib form. Its convergence half is
already `summable_padicExp_terms`; the membership half (`𝔪 ⊆ ball`) needs a general DVR lemma, not the
`PadicInt`-specific `inExpBall_of_mem_span`.
Cost of restatement: **MODERATE** (the general membership lemma `𝔪 ⊆ exp-ball for odd residue char`
is new work; the convergence engine already generalises).

Crucially, this Phase-4 finding is **subordinate to** the parent's verdict: the whole `padicExp`
machinery is `BORDERLINE`/governed by an upstreaming decision, so "which generality to state this
specialisation at" is itself part of that deferred design question, not a self-resolving downgrade.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                        | no       | — | hypotheses are already an inequality + membership; nothing to bundle |
|  2 | sequences/metric → filters/nets/topological?                                                              | no       | — | the underlying convergence is already filter-based (inherited from `summable_padicExp_terms`); the statement is the right filter-free `Summable` packaging |
|  3 | construct an object → universal-property class?                                                            | partial  | the *mathematically* idiomatic mathlib object is the exp/log **isomorphism `pℤ_p ≃+* (1+pℤ_p)`** (an `MulEquiv`/`AddEquiv`), of which this summability is a sub-fact; mathlib would likely want the bundled iso, with convergence as a private step | the bundled iso composes with mathlib's group/unit API — but this is a property of the *whole development*, not this corollary; it reinforces that the corollary should not travel alone |
|  4 | set-with-closure-predicate → bundled substructure?                                                         | no       | — | `pℤ_p` is already `Ideal.span {p}` / the maximal ideal (`PadicInt.maximalIdeal_eq_span_p`); bundled |
|  5 | field-specific → weaken typeclass hierarchy?                                                               | yes      | the `ℚ_p`/`ℤ_p` hard-coding could be a general complete-nonarch-field-with-ring-of-integers statement (Phase 4b row 1) — but the convergence engine is already general; only this wrapper is specialised | a general-`𝒪` version would unify with the abstract `L`-API the project already has — again a *development*-level point |
|  6 | 1-categorical → higher-categorical?                                                                        | no       | — | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive structure?                                                      | no       | — | the index `n : ℕ` is intrinsic to the factorial series |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for *this corollary's* signature as a standalone). The two real
organisational levers — (5) state it over a general ring of integers `𝒪`, and (3) bundle the exp–log
`pℤ_p ≃ 1+pℤ_p` iso — are both properties of the **surrounding p-adic-exp development**, not of this
one-line specialisation. They are the *parent's* design questions. One-line reason this corollary is
not itself a modernisation move: it is a concrete summability statement already in idiomatic
`Summable` form; the only modernisation choices live one (or two) layers up, in the `padicExp` /
`summable_padicExp_terms` upstreaming decision.

---

### Diamond / defeq risk — `padicExp_converges_on_pZp`

**n/a — declaration kind is `theorem`.** (Phase 4.5 runs only for `def`/`class`/`instance`.)

---

### Mathlib search-status: `padicExp_converges_on_pZp`

[A] Lean-Finder       "p-adic exp summable on pℤ_p", "exp converges maximal ideal odd p"   n/a: Lean-Finder web UI not callable in this environment — substituted with exhaustive grep over the mathlib tree (method D), plus reading the candidate decls' actual statements.
[B] Loogle            `Summable (fun n => (↑n.factorial)⁻¹ • (↑_ ^ n))`, `_ ∈ Ideal.span {↑p} → Summable _`, `p ≠ 2 → _ ∈ Ideal.span {↑p} → Summable _`   no nonarch hit: same as the parent — the only same-shape mathlib lemma is `NormedSpace.expSeries_summable_of_mem_ball'`, archimedean, with an eball hypothesis mathlib cannot supply p-adically (see parent report). Nothing keyed to `pℤ_p`/`Ideal.span {p}`.
[C] LeanSearch        "p-adic exponential converges on p Z_p", "exponential summable maximal ideal odd prime"   no p-adic hit: surfaces the archimedean `NormedSpace.expSeries_summable*` family only; nothing nonarchimedean and nothing about `pℤ_p`.
[D] Grep mathlib src  `grep -rniE "Summable.*factorial|converges_on|exp.*span|exp.*pZp|onePAdicPow"` over `.lake/packages/mathlib/Mathlib/NumberTheory/Padics/` and `Analysis/`   **NO p-adic exp anywhere** in `Mathlib/NumberTheory/Padics/` (confirmed: no `padicExp`, no exp-on-`pℤ_p`). `PadicIntegers.lean` has only the *infrastructure* this proof's parent uses: `norm_le_pow_iff_mem_span_pow` (L467), `maximalIdeal_eq_span_p` (L506). The archimedean `expSeries_summable*` lives in `Analysis/Normed/Algebra/Exponential.lean`.
[E] Name pattern      `padicExp`, `converges_on_pZp`, `expSeries_summable`, `exp_mem_span`   `padicExp` / `converges_on_pZp` do **not** exist in mathlib. `NormedSpace.expSeries_summable'` exists but is *unconditional* (radius `= ∞`), the **archimedean** regime, **false** p-adically.

Searched for both:
- the user's current form (`Summable (fun n => (n!)⁻¹ • (x:ℚ_p)ⁿ)` for `x ∈ pℤ_p`, `p ≠ 2`) — **not** in mathlib.
- the literature-standard / general form (exp summable on the maximal ideal of a complete nonarch field,
  and the archimedean `NormedSpace.exp` family) — mathlib has neither the p-adic statement nor a usable
  bridge to it (the parent report establishes the eball-hypothesis obstruction in detail).

**Why the close archimedean match does NOT settle this as NO-mathlib-has-it.** Identical to the parent
`summable_padicExp_terms` analysis: mathlib's `NormedSpace.expSeries_summable_of_mem_ball'` is the same
term *shape* but (i) proves the stronger *norm*-summability by archimedean geometric domination, and
(ii) its hypothesis `x ∈ EMetric.ball 0 (expSeries ℚ_[p] L).radius` is **uncomputable in mathlib
p-adically** (`expSeries_radius_eq_top` is `ℝ`/`ℂ`-only; the scalar ratio test
`ofScalars_radius_eq_inv_of_tendsto` needs `‖cₙ₊₁‖/‖cₙ‖` to converge, but for `cₙ=(n!)⁻¹` that ratio is
`p^{-v_p(n+1)}`, which oscillates and has no limit). So even the *parent* general lemma is missing from
mathlib; a fortiori, this `pℤ_p` specialisation of it is missing too.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the literature-standard general form). And —
the decisive structural point for this corollary — its sole non-trivial building block,
`summable_padicExp_terms`, is itself **not in mathlib** (it is the `BORDERLINE` parent). The only genuine
mathlib pieces in the dependency chain are the `PadicInt` membership/norm lemmas
(`PadicInt.norm_le_pow_iff_mem_span_pow`, `maximalIdeal_eq_span_p`) used inside `inExpBall_of_mem_span`.

---

### Call sites — `padicExp_converges_on_pZp`

Internal use count: **0** (within the project, NOT counting the declaring theorem)
External-to-file callers: **0 distinct files**

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (none)           | the qualified name `padicExp_converges_on_pZp` appears **only** at its own definition (`PadicExp.lean:1031`); a repo-wide grep across all `projects/**/*.lean` returns no other occurrence |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this theorem?):
  - **Yes, in effect** — every place the project actually needs "exp is integral / converges on `pℤ_p`"
    routes through the *underlying* pieces directly, **not** through this theorem. Specifically
    `pZpExp_coe` (`PadicExp.lean:1046`) and `pZpExp_sub_one_mem` (L1062) re-derive integrality from
    `inExpBall_of_mem_span` + `norm_padicExp_sub_one` / `coe_norm_le_inv_of_mem_span`, and the `L=ℚ_p`
    summability that *this* theorem packages is obtained at `PadicExp.lean:1034` by calling
    `summable_padicExp_terms (L := ℚ_[p]) p (inExpBall_of_mem_span …)` **inline** — i.e. the exact body
    of this theorem is re-inlined at the one place it would be used, bypassing the named wrapper.

What the call-sites pattern tells you: **K = 0 internal uses, and the wrapper is bypassed (its body is
re-inlined at `:1034`).** Per the Phase-6 signal table, `K = 0` for a thin wrapper whose statement is
re-derived inline elsewhere is a **NO-leaning** signal — the named theorem currently earns its keep only
as a *human-readable milestone* ("RJW Lemma 5.14, first half"), not as load-bearing API. (Sharp contrast
with the parent `summable_padicExp_terms`, which had K=8+1 and is genuinely load-bearing.)

---

### Composition check (Phase 6)

Can `padicExp_converges_on_pZp` be derived **from mathlib** in ≤3 chained calls?

Attempt 1: `NormedSpace.expSeries_summable_of_mem_ball' (x : ℚ_[p]) hball`.
  - Mathlib decls used: `NormedSpace.expSeries_summable_of_mem_ball'`.
  - Result: **fails** — its hypothesis `x ∈ EMetric.ball 0 (expSeries ℚ_[p] ℚ_[p]).radius` is
    uncomputable in mathlib p-adically (parent report, Phase 5/6). Supplying it is a missing-lemma, not
    a call. (Even granting it, the conclusion is the wrong/stronger norm-summability via archimedean
    domination, and a `.congr`/coercion bridge would be needed for the `smul` shape.)

Attempt 2: the project's actual body — `summable_padicExp_terms (L := ℚ_[p]) p (inExpBall_of_mem_span p hp2 hx)`.
  - Decls used: `summable_padicExp_terms` + `inExpBall_of_mem_span`.
  - Result: **this is a clean 2-call composition — but of PROJECT lemmas, not mathlib.** `inExpBall_of_mem_span`
    is itself a 3-step `calc` (`pow_le_pow_left₀` + `pow_lt_pow_right_of_lt_one₀` + `coe_norm_le_inv_of_mem_span`),
    and `summable_padicExp_terms` is the genuine ~25-line nonarchimedean-convergence proof. Neither is in
    mathlib. So the composition does **not** discharge the theorem from *mathlib* building blocks.

Attempt 3: assemble from mathlib's genuine pieces (the nonarch criterion
`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` + Legendre via `Padic` valuation API +
`tendsto_pow_atTop_nhds_zero_of_lt_one` + `PadicInt.norm_le_pow_iff_mem_span_pow`).
  - Result: **this just re-proves the parent `summable_padicExp_terms` and then adds the membership
    step** — a multi-lemma (~30-line) argument spanning ≥4 sub-lemmas, not a ≤3-call composition.

Conclusion: **NOT-COMPOSABLE *from mathlib*.** The theorem *is* a 2-call composition, but of two
project-internal lemmas (one of which, `summable_padicExp_terms`, is the genuine missing-from-mathlib
analysis and is itself `BORDERLINE`). Assembling it from mathlib's actual primitives is a real
multi-lemma proof. This rules out `NO-composable-from-mathlib` (which requires composition from
*mathlib* decls in ≤3 calls).

---

## Verdict: `padicExp_converges_on_pZp`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the target **is** a textbook-standard fact — "for odd `p`, `exp`
  converges on `pℤ_p`" (the first half of the exp–log iso `pℤ_p ≅ 1+pℤ_p`; Washington §5.1, Cassels §12,
  RJW Lem 5.14). Sources unanimous, including the sharp `p ≠ 2` distinction (`exp` diverges on `2ℤ_2`).
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** in the *specialisation* sense —
  hypotheses are sharp (`p ≠ 2` cannot be dropped), but the theorem is hard-coded to `L = ℚ_p` / `ℤ_p`
  whereas the standard fact holds over the ring of integers of any complete nonarch field. Modern-idiom
  (4c): the real organisational moves (general-`𝒪` version; bundle the exp–log iso) are *parent/
  development*-level, not this corollary's.
- Mathlib search (Phase 5): **not in mathlib** — no p-adic exp at all; and its key building block
  `summable_padicExp_terms` is itself missing/`BORDERLINE`. Only the `PadicInt` membership/norm lemmas
  are genuine mathlib.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** — the body is a 2-call composition of
  *project* lemmas; assembling from mathlib's real primitives is a multi-lemma proof.
- Call sites (Phase 6.0): **K = 0**, and the wrapper is **bypassed** (its body is re-inlined at
  `PadicExp.lean:1034`). NO-leaning composability signal *locally*.

**Rationale (why BORDERLINE — not YES, not NO):**

This theorem sits at the intersection of two pulls that the search evidence cannot itself reconcile,
which is the textbook trigger for BORDERLINE. On one side, it is a *true, named, textbook-standard,
genuinely-missing-from-mathlib* p-adic fact with sharp hypotheses (the `p ≠ 2` exclusion is real and
correct), proved sorry-free — that profile would normally push toward a YES bucket. On the other side,
**as a declaration it is a thin `L = ℚ_p` specialisation** of the general `summable_padicExp_terms`
(its proof is the literal 2-call composition `summable_padicExp_terms (inExpBall_of_mem_span …)`),
it adds **no new analysis**, it has **zero call sites**, and its body is **re-inlined** at the single
site that would consume it. Those facts pull toward NO. But it is decisively **not** `NO-mathlib-has-it`
(mathlib has no p-adic exp, and the parent lemma is itself absent — Phase 5) and **not**
`NO-composable-from-mathlib` (the composition is from *project* lemmas, not mathlib; from mathlib it is
a real multi-lemma proof — Phase 6). So neither NO bucket is groundable in the evidence either.

What actually decides this theorem's mathlib fate is **not** anything intrinsic to it — it is the *same*
upstreaming decision that governs its parent `summable_padicExp_terms` (assessed `BORDERLINE`) and the
def `padicExp` (assessed `NO-mathlib-has-it`, with the surrounding *theorems* flagged as the real
missing API). Mathlib has **no** nonarchimedean exponential development. If the project upstreams that
development as a unit, then the natural mathlib form of *this* fact is the **general-`𝒪`** statement
("for odd residue characteristic, `exp` converges on the maximal ideal", quite possibly bundled into the
exp–log iso `𝔪 ≃ 1+𝔪`), **not** the `ℚ_p`-hard-coded `pℤ_p` wrapper — so the right move would be to
*generalise-and-absorb* this into that PR, not ship it verbatim. If the project keeps the development
local, this wrapper is a (currently bypassed, K=0) human-readable milestone that need not go to mathlib
at all. The skill cannot choose between "upstream the whole exp development (and restate this generally)"
and "keep local" without the human; per the anti-pattern guidance, a whole-development /
EXPENSIVE-generalisation tradeoff is itself a BORDERLINE question, not a self-resolving downgrade.

**Numbered questions (≤5):**

1. Do you intend to upstream the project's p-adic / nonarchimedean **exponential development** to mathlib
   as a unit (the convergence engine `summable_padicExp_terms`, the isometry, the log, and the exp–log
   isomorphism `pℤ_p ≅ 1+pℤ_p`)? This theorem is a *corollary* of that development and should travel with
   it (most likely **generalised**, see Q2), not alone. (This is the same governing question as for
   `summable_padicExp_terms` and `padicExp`.)
2. If yes to (1): should the mathlib statement be the **general** form — "for a complete nonarchimedean
   field `L ⊇ ℚ_p` of odd residue characteristic, `exp` converges on the maximal ideal `𝔪` of its ring of
   integers" (which needs a new `𝔪 ⊆ exp-ball` lemma; the convergence half is already
   `summable_padicExp_terms`) — rather than the `ℚ_p`-hard-coded `pℤ_p`-on-`ℤ_[p]` wrapper this theorem
   is? (The general form is the mathlib-idiomatic target; cost MODERATE.)
3. If yes to (1): should this convergence fact be exposed as a standalone lemma at all, or only as a
   private step inside the bundled exp–log isomorphism `MulEquiv`/`AddEquiv` (Phase 4c row 3)? Mathlib
   would likely prefer the bundled iso as the public API.
4. Given that this wrapper currently has **K = 0** call sites and its body is **re-inlined** at
   `PadicExp.lean:1034`: even setting mathlib aside, do you want to keep it as a named project-local
   "RJW Lemma 5.14, first half" milestone, or inline it and delete the wrapper? (If you delete it, the
   mathlib question is moot; if you keep it, it stays a project-local readability anchor.)

**Next action:** user answers the questions; re-run `/mathlibable padicExp_converges_on_pZp` —
preferably **together with `/mathlibable summable_padicExp_terms` and `/mathlibable PadicLFunctions.padicExp`**,
since this corollary's verdict is entirely governed by the (BIG, multi-decl) upstreaming decision on the
p-adic exponential development it specialises. Likely resolutions:
  - "Upstream the nonarchimedean-exp development" → this fact ships **as the general-`𝒪` statement
    (Q2), or as a private step in the bundled exp–log iso (Q3)** — i.e. effectively
    `YES-but-generalise-first` *folded into* the development PR, **not** as this verbatim `pℤ_p` wrapper.
  - "Keep project-local" → drop from mathlib consideration; and consider inlining the wrapper (Q4) since
    it has no consumers.

---

## Next step

User answers the four numbered questions above; re-run `/mathlibable padicExp_converges_on_pZp` —
preferably alongside `/mathlibable summable_padicExp_terms` and `/mathlibable PadicLFunctions.padicExp`,
since this corollary's mathlib fate is governed by the (BIG, multi-decl) upstreaming decision on the
p-adic exponential definition and convergence engine it specialises — to resolve to either
`YES-but-generalise-first` (folded into the nonarchimedean-`exp` development PR as the general-`𝒪`
statement / a step in the bundled exp–log iso) or drop-from-consideration (keep — or inline — as a
project-local milestone).
