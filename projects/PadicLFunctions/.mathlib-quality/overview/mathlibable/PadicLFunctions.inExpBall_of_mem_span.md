# `PadicLFunctions.inExpBall_of_mem_span` — mathlibable assessment

**Verdict: `NO-composable-from-mathlib`**

`inExpBall_of_mem_span` states the canonical p-adic-analysis fact that, for an **odd**
prime `p`, the ideal `pℤ_p` lies inside the convergence disc of the `p`-adic exponential
(`‖x‖ < p^{−1/(p−1)}`, here in the project's rpow-free form `‖x‖^{p−1} < p⁻¹`). The
mathematics is textbook-standard (Keith Conrad, *Infinite series in p-adic fields*, verbatim:
"∑ xⁿ/n! in Q_p has disc of convergence pZ_p when p ≠ 2 and 4Z_2 when p = 2"), but in the
literature it is **always an inline computation** inside the construction of the exp/log
isomorphism `pℤ_p ≅ 1 + pℤ_p` — never a separately-named theorem. The lemma's *conclusion*
is `InExpBall p x`, a **project-local predicate that mathlib does not have** (mathlib carries
no `p`-adic exponential or logarithm at all), and whose own mathlibable assessment is
`NO-composable-from-mathlib`. Stripped of that wrapper the result is a ≤3-call composition
(`coe_norm_le_inv_of_mem_span` → `‖x‖ ≤ p⁻¹`, then `pow_le_pow_left₀` +
`pow_lt_pow_right_of_lt_one₀`). It is a bridge lemma connecting one mathlib norm fact to a
project-local predicate; it should stay project-local. The substantive, genuinely
contributable mathematics lives in the surrounding `p`-adic `exp`/`log` API (isometry,
functional equation, inversions, RJW Lem 5.14), which is assessed under those declarations.

- **Target:** `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:1010` (kind: `theorem`)
- **Mode:** A (single declaration), full 10-phase workflow with the exhaustive 9-channel literature search.
- **Refs:** `--refs=/Users/mcu22seu/.claude/plugins/cache/mathlib-quality-plugins/mathlib-quality/0.50.0/skills/mathlib-quality/references` (read: `mathlibable-verdicts.md`, `mathlibable.md`).

---

## Phase 0 — Doctor / baseline

```
### Baseline (Phase 0)
- lake build:               build NOT re-run; reasoned from source (per task BUILD NOTE)
- decl `inExpBall_of_mem_span`: ✓ resolved at PadicExp.lean:1010
- kind:                      theorem
- has sorry:                 no (target and all dependents are sorry-free)
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — exp/log
                             on a nonarchimedean complete normed ℚ_p-algebra field; for odd p
                             the convergence ball contains pℤ_p.
```

Per the task's BUILD NOTE, the build was **not re-run; reasoned from source.** The target,
its proof body, its immediate dependency `coe_norm_le_inv_of_mem_span` (`PadicExp.lean:998`),
the parent predicate `InExpBall` (`PadicExp.lean:65`), and the relevant mathlib decls under
`.lake/packages/mathlib/` were read directly. Baseline commit `d71766e`. This is the Phase-0
source-fallback path the skill explicitly permits.

**Section/variable context.** The theorem sits in `section pZp` under the file-level
`variable (p : ℕ) [hp : Fact p.Prime]`; the L-typeclasses
(`[NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`) are explicitly **`omit`-ed**
for this theorem (line 1006). It works entirely inside `ℤ_[p]` / `ℚ_[p]`, needing only
`p` prime.

---

## Phase 1 — Comprehend

```lean
omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L] in
/-- E5: for odd `p`, `pℤ_p` lies strictly inside the exponential convergence
ball: `‖x‖^{p−1} ≤ p^{−(p−1)} < p⁻¹` since `p − 1 ≥ 2` (where `hp2` enters;
RJW Lem 5.14, TeX 1892–1893). -/
theorem inExpBall_of_mem_span (hp2 : p ≠ 2) {x : ℤ_[p]}
    (hx : x ∈ Ideal.span {(p : ℤ_[p])}) : InExpBall p ((x : ℚ_[p])) := by
  have hp3 : 3 ≤ p := by ...                              -- p odd prime ⇒ p ≥ 3
  have hppos : (0 : ℝ) < p := ...
  have hnorm := coe_norm_le_inv_of_mem_span p hx          -- ‖(x:ℚ_p)‖ ≤ p⁻¹
  rw [InExpBall]                                          -- goal: ‖(x:ℚ_p)‖^(p-1) < p⁻¹
  calc ‖(x : ℚ_[p])‖ ^ (p - 1)
      ≤ ((p : ℝ)⁻¹) ^ (p - 1) := pow_le_pow_left₀ (norm_nonneg _) hnorm _
    _ < ((p : ℝ)⁻¹) ^ 1 := by                            -- strict: base ∈ (0,1), p-1 ≥ 2 > 1
        refine pow_lt_pow_right_of_lt_one₀ (inv_pos.mpr hppos) ?_ (by omega)
        rw [inv_lt_one_iff₀]; exact .inr (by exact_mod_cast hp.out.one_lt)
    _ = (p : ℝ)⁻¹ := pow_one _
```

### Statement (Phase 1)

`inExpBall_of_mem_span` is a **theorem** stating:

> Let `p` be an odd prime (`p ≠ 2`) and let `x ∈ ℤ_p` lie in the ideal `(p)` — i.e.
> `x ∈ pℤ_p`. Then the image of `x` in `ℚ_p` lies in the convergence ball of the `p`-adic
> exponential: `‖x‖_p^{p−1} < p⁻¹` (equivalently `‖x‖_p < p^{−1/(p−1)}`).

Mathematically this is the standard remark that, for an odd prime, the exponential series
`exp(z) = ∑ zⁿ/n!` converges on all of `pℤ_p` — because `x ∈ pℤ_p` gives `‖x‖_p ≤ p⁻¹`, and
for `p ≠ 2` one has `p⁻¹ < p^{−1/(p−1)}` (strict, since `p − 1 ≥ 2`), so `x` sits strictly
inside the disc. For `p = 2` the analogous statement needs `4ℤ_2`, which is exactly why
`hp2 : p ≠ 2` is a hypothesis.

Variables / typeclasses (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime; `Fact p.Prime` supplies `p ≥ 2`, `p.pos`, `p.one_lt`.
- `x : ℤ_[p]` (implicit) — a `p`-adic integer.

Hypotheses (Lean side):
- `hp2 : p ≠ 2` — `p` is **odd**. Combined with primality forces `p ≥ 3`, hence `p − 1 ≥ 2`,
  which is the *only* place the strict inequality `p⁻¹ < p^{−1/(p−1)}` comes from.
- `hx : x ∈ Ideal.span {(p : ℤ_[p])}` — `x ∈ pℤ_p`.

Conclusion (math): `‖x‖_p < p^{−1/(p−1)}`, i.e. `x` lies in the convergence disc of `exp_p`.

Conclusion (Lean): `InExpBall p ((x : ℚ_[p]))`, where
`InExpBall p y := ‖y‖ ^ (p - 1) < (p : ℝ)⁻¹` (project def, `PadicExp.lean:65`).

---

## Phase 2 — Preliminary checks (size + one-line)

### Size classification (Phase 2a)

**Verdict: SMALL.** It is a corollary/specialisation: a single side-condition lemma feeding
the `pℤ_p` integral-branch API. It introduces no new structure, is not named after a
person/place (it is one step of "RJW Lem 5.14"), and is not itself a headline `## Main
result` — the main results of the file are the exp/log functional equation, isometry, and
the `x^s := exp(s·log x)` characterisation. (Literature width is EXHAUSTIVE regardless; this
classification is for narrative framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure` — **the one-line-`def` check does not
apply** (one-line note, skipped). For the record, the proof body is a genuine 3-step `calc`,
not a one-liner.

---

## Phase 3 — Literature search (EXHAUSTIVE, 9-channel protocol)

Goal: identify the **literature-standard form** of "for odd `p`, `pℤ_p` lies in the
convergence disc of the `p`-adic exponential", and whether it is ever stated as a *named
theorem* rather than an inline computation feeding the exp/log isomorphism.

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic exponential converges on pZ_p odd prime convergence radius p^{-1/(p-1)}" | yes | `exp_p` converges for `\|z\|_p < p^{−1/(p−1)}`; **"for p ≠ 2, exp converges for all elements of pℤ_p"** | Wikipedia + Conrad + MIT 18.785 + UChicago REU all agree. |
| 2 | WebSearch (general form) | "Washington cyclotomic fields p-adic exp/log pZ_p isomorphism 1+pZ_p odd prime" | yes | log is an isometry between `{‖x‖<(1/p)^{1/(p−1)}}` (additive) and matching multiplicative ball; `1+pℤ_p` is the kernel structure for `p>2` | Washington §5.1 is exactly the file's cited reference. |
| 3 | WebSearch (named-after / aliases) | "p-adic log/exp mutually inverse 1+pZ_p group isomorphism Koblitz Neukirch" | yes | "exp/log give mutually inverse topological isomorphisms between `1+pⁿℤ_p` and `pⁿℤ_p`"; **"exp maps p′ℤ_p → 1+p′ℤ_p, p′ = p if p>2, p′ = 4 if p=2"** | The `p>2` vs `p=2`→`4` split is *the* standard framing — matches `hp2` precisely. |
| 4 | ChatGPT MCP | (historical-formulation question) | n/a | — | **Channel unavailable** — `chatgpt-math` MCP server is installed (`~/.claude/mcp-servers/chatgpt-math`) but not connected/authenticated in this session (no `ask` tool surfaced). Compensated by channels 1–3, 5–10, which converge unanimously; recorded for completeness per the skill's gate (same situation as the sibling `InExpBall.md` report). |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/` | n/a | (no references dir; `refs/` absent) | Project has no `.mathlib-quality/references/`; the gitignored `refs/` store is not present in this checkout. Recorded n/a with reason. |
| 6 | nLab | "p-adic exponential map" (ncatlab.org) | partial | exp converges on open ball `𝔻_p` of valuative radius `1/(p−1)`; **image is `1+𝔻_p`; exp is a bijection `𝔻_p → 1+𝔻_p`** with inverse log; for `K=Q_p`, `1+𝔻_p = 1+pℤ_p` for `p≠2`, `1+4ℤ_2` for `p=2` | No dedicated `p-adic+exponential+map` page (404); content surfaced via search of nLab/PlanetMath. Presented as a ball described by an inequality, not a bundled object. |
| 7 | nCatLab (if categorical) | — | n/a | — | Not a categorical concept (a normed-field convergence side condition). Brief look confirms nothing categorical to add beyond #6. |
| 8 | Stacks Project (if alg geom) | — | n/a | — | Not an algebraic-geometry concept; Stacks has no `p`-adic-analysis exp/log convergence material. |
| 9 | MathOverflow / Math.StackExchange | "p-adic exp converges on pZp for p odd" generality | yes | Consistent with #1–#3; the `\|x\| ≤ 1/p < (1/p)^{1/(p−1)}` (`p>2`) computation is the standard one-line justification carried as a side condition. | No separately-named theorem; it is the universal "disc of convergence is pℤ_p" remark. |
| 10 | recent arXiv (last 5 years) | "p-adic exponentiation Tate uniformization" (2602.16433); "Dirichlet series expansions of p-adic L-functions" (2102.02851); class-formula / overconvergent-Frobenius papers | yes | Contemporary research uses the identical inequality hypothesis; `exp`/`log` discs are the open balls of the stated radii; no bundled "in-the-ball" predicate or named "pℤ_p ⊆ ball" lemma | The fact is assumed background, cited inline. |

**Primary verbatim source — Keith Conrad, *Infinite series in p-adic fields*** (extracted
locally via `pdftotext`; the canonical graduate treatment):

> "Therefore `ord_p(n!)/n → 1/(p−1)` as `n → ∞`, … which means the radius of convergence of
> `∑_{n≥0} xⁿ/n!` in `K` is `(1/p)^{1/(p−1)} = 1/p^{1/(p−1)}`. … So the disc of convergence of
> `∑ xⁿ/n!` in `K` is `{x ∈ K : |x| < (1/p)^{1/(p−1)}}`. For example, when `K = Q_p` the
> inequality `|x|_p < (1/p)^{1/(p−1)}` is the same as `|x|_p ≤ 1/p` for `p ≠ 2` and `|x|_2 ≤ 1/4`
> for `p = 2`. **Thus `∑_{n≥0} xⁿ/n!` in `Q_p` has disc of convergence `pZ_p` when `p ≠ 2` and
> `4Z_2` when `p = 2`.**"

This passage **is** the mathematical statement of `inExpBall_of_mem_span`. Note the rendering:
in the literature it is part of an **Example** (Conrad's Example 3.11), i.e. an inline
computation, not a numbered theorem/lemma.

### Literature summary (Phase 3)

- **Concept identified as:** "the disc of convergence of the `p`-adic exponential is `pℤ_p`
  (for odd `p`)" / "`exp` converges on `pℤ_p` for `p > 2`". A specialisation of the
  convergence-radius fact `R = p^{−1/(p−1)}`.
- **Sources agree on the standard form:** **yes**, unanimously (Conrad, Wikipedia, Washington
  §5.1, Koblitz, MIT 18.785, Cambridge/jat58 notes, nLab/PlanetMath, arXiv). The `p > 2` ⇒
  `pℤ_p` vs `p = 2` ⇒ `4ℤ_2` dichotomy is universal and is exactly what `hp2 : p ≠ 2` encodes.
- **Most general standard form:** the convergence region is the **inequality side condition**
  `‖x‖ < p^{−1/(p−1)}` on the argument; the corollary for `Q_p` (odd `p`) is `pℤ_p ⊆` that disc.
- **Is it ever a *named* result?** No. Across all channels it appears as an inline
  computation/example en route to the exp/log isomorphism `pℤ_p ≅ 1 + pℤ_p`. There is no
  standard *named theorem* "InExpBall_of_mem_span" to upstream; the standard *form* is a side
  condition.
- **Disagreement with the literature:** none. The Lean statement is faithful; the only
  non-literature element is the *encoding* — the project states the disc rpow-free as
  `‖x‖^{p−1} < p⁻¹` (a `ℕ`-power, valid since `p ≥ 2`) and wraps it in the project-local
  `InExpBall` predicate, where the literature writes the real inequality `‖x‖ < p^{−1/(p−1)}`.

---

## Phase 4 — Generality analysis

### 4a. Generality status table

Literature-standard form (Phase 3): for an odd prime `p`, every `x ∈ pℤ_p` satisfies
`‖x‖ < p^{−1/(p−1)}` (the exponential converges on `pℤ_p`).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[Fact p.Prime]` | `p` prime | `p` prime (Legendre `v_p(n!)` needs a prime) | NO | The radius `p^{−1/(p−1)}` and the bound `‖x‖ ≤ p⁻¹ < p^{−1/(p−1)}` are prime-specific (Legendre). Not a generalisation axis. |
| 2 | `hp2 : p ≠ 2` | `p` odd | `p > 2` (else `4ℤ_2`, not `pℤ_p`) | NO | Genuinely necessary: for `p = 2`, `‖x‖ ≤ 1/2 = (1/p)^{1/(p−1)}` is **not strict**, so `2ℤ_2 ⊄` disc; one needs `4ℤ_2`. Conrad/Koblitz/Wikipedia all carry this. The hypothesis is exactly right. |
| 3 | `x ∈ Ideal.span {(p)}` (`= pℤ_p`) | membership in `(p)` | `x ∈ pℤ_p` | — | This *is* the literature hypothesis. Could be phrased `‖x‖ ≤ p⁻¹` (slightly more general — any element of norm ≤ p⁻¹, not just multiples of `p`; but in `ℤ_p` these coincide), but that loses the "pℤ_p" idiom and is a presentation choice, not a real generalisation. |
| 4 | conclusion `InExpBall p (x:ℚ_p)` (`= ‖x‖^{p−1} < p⁻¹`) | rpow-free `ℕ`-power form | `‖x‖ < p^{−1/(p−1)}` (real root) | — | Equivalent only because `p ≥ 2` makes `p−1` a positive `ℕ`. An *encoding convenience*, not a generality axis. The predicate itself is project-local (see Phase 4c / 5). |

### 4b. Generality verdict

```
The current form is: MAXIMALLY GENERAL (within the p-adic setting the literature uses).
Number of weakening opportunities found: 0 substantive.
```

Both substantive hypotheses (`p` prime, `p` odd) are necessary and match the literature exactly;
`hp2` is not removable (the `p = 2` case is genuinely `4ℤ_2`). There is no
literature-supported weakening. The result is stated at the standard generality for this fact.
The only "narrowing" is the rpow-free encoding and the `InExpBall` wrapper — both presentation
details, addressed in 4c/5/6, not generalisation axes. So this is **not** a
YES-but-generalise-first (LITERATURE-WEAKENING) case.

Cost of any restatement: n/a (no weakening proposed).

### 4c. Modern mathlib-idiom restatement — the Bourbaki 2.0 check

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preamble → typeclass/instance? | no | — | Hypotheses are already typeclasses (`Fact p.Prime`) + a membership; nothing to bundle. |
| 2 | sequences/metric → filters/topological? | no | — | A single static norm inequality; no limit/sequence to filter-ise. |
| 3 | construction → universal-property class? | no | — | It is an inequality, not a constructed object. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | `pℤ_p` is `Ideal.span {p}` (already a bundled `Ideal`); fine. |
| 5 | vector-space/metric/field-specific → weakened typeclass? | no | — | Already at the natural `ℤ_p`/`ℚ_p` level; the fact is intrinsically about `Q_p`'s valuation. |
| 6 | 1-categorical → higher-categorical? | no | — | No categorical content. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid? | no | — | `p` ranges over primes already; `p−1` is the (necessary) Legendre exponent, not a free index. |

```
### Modern-idiom verdict (Phase 4c)
Modern idiom available: no — for the lemma itself.
One-line reason: every hypothesis is already a typeclass or a bundled Ideal membership, and
the content is a static valuation inequality with no sequence/construction/categorical
structure to modernise. The ONE idiom observation is about the *conclusion type*: mathlib's
own exponential API writes "in the convergence ball" inline as
`x ∈ Metric.eball 0 (expSeries 𝕂 𝔸).radius` / `‖x‖ < r`, NOT as a bespoke `def` like
`InExpBall` — so the idiomatic mathlib form would drop the `InExpBall` wrapper and conclude
the bare inequality. That is a property of `InExpBall` (assessed in its own report), and it
points to NO-composable, not to a modern-idiom YES.
```

This is **not** a Bourbaki-2.0 contribution: the modernisation move (drop `InExpBall`, inline
the inequality) makes the lemma *less* of a standalone object, not more. No downstream mathlib
API is unlocked by adding it.

---

## Phase 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional equalities or
typeclass-search paths, so this phase is skipped per the skill's scope rule.

---

## Phase 5 — Mathlib five-method search

Searched for (a) the user's form (`pℤ_p ⊆ exp ball` / `InExpBall … of mem_span`), and (b) the
literature-standard form (the `p`-adic exponential and its convergence radius `p^{−1/(p−1)}`).
The Loogle / LeanSearch / Lean-Finder MCP back-ends are **not connected** in this session;
methods [D] (exhaustive grep over the mathlib source tree) and [E] (name-pattern grep) are the
available substitutes and are conclusive here because the *concept* (a `p`-adic exponential) is
entirely absent from mathlib.

```
### Mathlib search-status: `inExpBall_of_mem_span`

[A] Lean-Finder   n/a — MCP not connected this session
[B] Loogle        n/a — MCP not connected this session
[C] LeanSearch    n/a — MCP not connected this session
[D] Grep mathlib src:
      - `padicExp`, `padicLog`, `Padic.exp`, `Padic.log`, `padic_exp`, `expPadic` in Mathlib/  → NO HITS
      - `exp`/`Exp` decls under `Mathlib/NumberTheory/Padics/`                                 → only an unrelated
        tactic `index_simp` + the word "expressed"; NO p-adic exponential
      - `InExpBall` / `inExpBall` anywhere in Mathlib/                                          → NO HITS
      - `exp … mem_span` / `mem_span … exp`                                                     → NO HITS
      - `expSeries`/`Metric.eball` convergence-ball idiom (Analysis/.../Exponential.lean)       → the abstract
        Banach-algebra exp; uses `x ∈ Metric.eball 0 (expSeries 𝕂 𝔸).radius`; for fields the
        radius is ⊤ (`expSeries_radius_eq_top`), so it does NOT model the bounded p-adic ball
[E] Name pattern  `*InExpBall*`, `*_of_mem_span` returning a norm/ball bound in mathlib        → NO HITS
                  (mathlib's `PadicInt.norm_le_pow_iff_mem_span_pow` is the closest — see Phase 6)

Searched both:
  - user's current form (`InExpBall p x` from `x ∈ pℤ_p`, odd p)            → not in mathlib
  - literature-standard form (`p`-adic `exp` convergence radius / disc)      → not in mathlib AT ALL

Concluded: "not in mathlib (all available methods exhausted, plus the literature-standard
form). Mathlib has NEITHER a p-adic exponential/logarithm NOR an `InExpBall` predicate. The
only adjacent mathlib decl is the building block `PadicInt.norm_le_pow_iff_mem_span_pow`
(Mathlib/NumberTheory/Padics/PadicIntegers.lean:466) — an iff between span-membership and a
norm bound — which the project's `coe_norm_le_inv_of_mem_span` already wraps."
```

Because the lemma's **conclusion type `InExpBall p x` is not a mathlib concept**, the verdict
cannot be `NO-mathlib-has-it`: there is no mathlib decl, in identical or more general form,
stating this. (The anti-pattern "mathlib has the general form so we don't need this" does not
apply — there is no general mathlib form of a thing mathlib does not define.)

---

## Phase 6 — Composition check (+ call-sites signal)

### 6.0. Call sites — `inExpBall_of_mem_span`

```bash
grep -rn "inExpBall_of_mem_span" projects/ --include="*.lean" | grep -v "PadicExp.lean:1010"
```

Internal use count (within the project, excluding the declaring line): **13 use sites**
across **2 files** — a genuinely load-bearing API lemma.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| PadicExp.lean:1034 | `summable_padicExp_terms (L := ℚ_[p]) p (inExpBall_of_mem_span p hp2 hx)` (in `padicExp_converges_on_pZp`) |
| PadicExp.lean:1049 | `have hball := inExpBall_of_mem_span p hp2 hx` (in `pZpExp_coe`) |
| PadicExp.lean:1067 | `norm_padicExp_sub_one (L := ℚ_[p]) p (inExpBall_of_mem_span p hp2 hx)` (in `pZpExp_sub_one_mem`) |
| PadicExp.lean:1087 | `rw [hxsub]; exact inExpBall_of_mem_span p hp2 hx` (in `pZpLog_coe`) |
| PadicExp.lean:1100 | `rw [hxsub]; exact inExpBall_of_mem_span p hp2 hx` (in `pZpLog_mem`) |
| PadicExp.lean:1132–1133 | `padicExp_add (L := ℚ_[p]) p (inExpBall_of_mem_span …) (inExpBall_of_mem_span …)` (AddChar construction) |
| PadicExp.lean:1145–1146 | `norm_padicExp_sub_padicExp (L := ℚ_[p]) p (inExpBall_of_mem_span …) (inExpBall_of_mem_span …)` (Lipschitz/continuity) |
| PadicExp.lean:1160 | `exact inExpBall_of_mem_span p hp2 hx` (value-at-1 step) |
| ResidueZeta.lean:113 | `norm_padicExp_sub_one (L := ℚ_[p]) p (inExpBall_of_mem_span p hp2 htℓmem)` |
| ResidueZeta.lean:120 | `exact inExpBall_of_mem_span p hp2 hy` |
| ResidueZeta.lean:287 | `inExpBall_of_mem_span p hp2 (Ideal.mul_mem_left _ _ hLmem)` |
| ResidueZeta.lean:1763 | `exact inExpBall_of_mem_span p hp2 (PadicInt.angleUnit_sub_one_mem p u)` |

External-to-project callers (downstream library): 0 (no consumers outside `projects/`).

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
**(none)** — every consumer routes through `inExpBall_of_mem_span`; the `pℤ_p`-in-the-ball
fact is not re-proved inline anywhere.

**What the call-sites pattern tells us.** K = 13 internal uses with no inline re-derivation is
a strong "real internal API" signal — *within this project*. But the API it serves is built on
the project-local `InExpBall` predicate (every use feeds `summable_padicExp_terms`,
`padicExp_add`, `norm_padicExp_sub_padicExp`, … — all of which take an `InExpBall` hypothesis).
The signal is "load-bearing project glue", not "mathlib-bound": the consumers are exactly the
project's own `p`-adic-exp API, which mathlib does not have. So the call-sites evidence
reinforces that this is the connective tissue of a project-local development, not a standalone
mathlib contribution.

### 6a. Composition attempt

Strip the project-local `InExpBall` wrapper (the conclusion is *definitionally*
`‖(x:ℚ_p)‖^{p−1} < p⁻¹`). Can the bare inequality be derived from mathlib (+ the one project
building block) in ≤3 chained calls?

```
Attempt 1 (the actual proof, lightly compressed):
  calc ‖(x:ℚ_[p])‖ ^ (p-1)
      ≤ ((p:ℝ)⁻¹) ^ (p-1) := pow_le_pow_left₀ (norm_nonneg _) (coe_norm_le_inv_of_mem_span p hx) _
    _ < (p:ℝ)⁻¹           := by
        have : ((p:ℝ)⁻¹)^(p-1) < ((p:ℝ)⁻¹)^1 :=
          pow_lt_pow_right_of_lt_one₀ (inv_pos.mpr (by positivity)) (by ...) (by omega)
        simpa using this
  - Mathlib decls used: `pow_le_pow_left₀`, `pow_lt_pow_right_of_lt_one₀`, `norm_nonneg`,
    `inv_pos` (+ `inv_lt_one_iff₀` for the `‹p⁻¹ < 1›` side goal).
  - Project decl used: `coe_norm_le_inv_of_mem_span` (which itself is a ≤2-line wrapper of the
    mathlib lemma `PadicInt.norm_le_pow_iff_mem_span_pow` at exponent 1).
  - Result: succeeds — 3 substantive `calc` steps; the middle strict step needs `p − 1 ≥ 2`
    (i.e. `p ≥ 3`, from `hp2` + primality).
  - Notes: this is a 3-call composition but the strict middle step (and its `p ≥ 3` side
    reasoning) sits right at the boundary between "composition" and "small proof".

Conclusion: COMPOSABLE (≤3 mathlib/project calls), but borderline — the strict-inequality
step carries real `p ≥ 3` content.
```

### 6b. Composition heuristics check

The chain is `calc step1 _ < step2 _ = step3`, with each step one lemma application. By the
Phase-6 heuristics this is on the composable side of the line (a `.trans`/calc chain of
single lemma calls), though the `pow_lt_pow_right_of_lt_one₀` step plus its `p ≥ 3` derivation
gives it more substance than a pure `.symm`/`.trans`. The decisive point, however, is **not**
the call count but the **conclusion type**: the result targets `InExpBall`, a predicate
mathlib has chosen not to carry — so even if one judged the body a "small proof", the lemma
cannot be added to mathlib *as stated* without first introducing a p-adic exponential and its
convergence-ball hypothesis (a much larger effort assessed elsewhere).

---

## Phase 7 — Verdict

```
## Verdict: `inExpBall_of_mem_span`

Category: NO-composable-from-mathlib

Evidence:
- Literature search (Phase 3): the fact is canonical (Conrad verbatim: "∑ xⁿ/n! in Q_p has
  disc of convergence pZ_p when p ≠ 2 and 4Z_2 when p = 2"; Washington §5.1, Koblitz, nLab,
  MIT, arXiv all agree, incl. the p>2 vs 4ℤ_2 split = exactly `hp2`), but it is ALWAYS an
  inline computation/example feeding the exp/log isomorphism — NEVER a named theorem.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; both hypotheses (p prime, p odd) are
  necessary and match the literature; `hp2` is not removable. No literature-supported
  weakening. Phase 4c: no Bourbaki-2.0 win — the idiomatic move drops the `InExpBall` wrapper.
- Mathlib search (Phase 5): NOT in mathlib; mathlib has no p-adic exp/log and no `InExpBall`
  predicate. Only adjacent decl is the building block
  `PadicInt.norm_le_pow_iff_mem_span_pow`. Hence NOT `NO-mathlib-has-it`.
- Composition check (Phase 6): COMPOSABLE — a 3-call `calc` over `coe_norm_le_inv_of_mem_span`
  (itself a wrapper of `norm_le_pow_iff_mem_span_pow`) + `pow_le_pow_left₀` +
  `pow_lt_pow_right_of_lt_one₀`. K = 13 internal uses, 0 external — load-bearing PROJECT glue.
```

**Rationale.** `inExpBall_of_mem_span` is a bridge lemma, not a standalone mathlib
contribution. Its *conclusion* is the project-local predicate `InExpBall p x` — a thing
mathlib deliberately does not have: mathlib carries **no** `p`-adic exponential or logarithm
(exhaustive grep of `Mathlib/NumberTheory/Padics/` returns nothing), and its abstract
Banach-algebra `expSeries` machinery has radius `⊤` over fields, so it does not model the
bounded `p`-adic disc. The sibling report on `InExpBall` itself already verdicts the predicate
`NO-composable-from-mathlib` (project sugar to be inlined as `‖x‖ < p^{−1/(p−1)}` if the API
is ever upstreamed). A lemma whose statement *names* a not-for-mathlib predicate inherits that
fate: it only makes sense inside this project's `InExpBall`-based `exp`/`log` API. Mechanically
it is also a clean ≤3-call composition: peel off the wrapper and the content is
`coe_norm_le_inv_of_mem_span p hx` (giving `‖x‖ ≤ p⁻¹`, itself a one-line wrap of the mathlib
iff `PadicInt.norm_le_pow_iff_mem_span_pow` at exponent 1) chained with `pow_le_pow_left₀` and
`pow_lt_pow_right_of_lt_one₀`. Per the skill's re-aim rule this is **not** a blanket-inherited
NO — the parent def's verdict was `NO-composable-from-mathlib` (not `NO-mathlib-has-it`, so
there is no more-general mathlib `D'` to re-aim at), and the lemma's own Phase-5/Phase-6
analysis independently lands on the same bucket.

**WHY not (refactor-actionable detail).** Mathlib has the building blocks but not the form, and
the form is a small composition whose *conclusion* is project-local. The lemma should remain
**project-local plumbing**; there is nothing to upstream as a standalone declaration.

Mathlib building blocks:
- `PadicInt.norm_le_pow_iff_mem_span_pow` — `Mathlib/NumberTheory/Padics/PadicIntegers.lean:466`
  (`‖x‖ ≤ p^{−n} ↔ x ∈ (p)ⁿ`). At `n = 1` this gives `x ∈ pℤ_p ⟹ ‖(x:ℚ_p)‖ ≤ p⁻¹` — the
  project already packages this as `coe_norm_le_inv_of_mem_span` (`PadicExp.lean:998`).
- `pow_le_pow_left₀` — `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:470` (monotonicity of `·^n`).
- `pow_lt_pow_right_of_lt_one₀` — strict antitonicity of `b^·` for `b ∈ (0,1)` (used for the
  `(p⁻¹)^{p−1} < p⁻¹` step; needs `p − 1 ≥ 2`, supplied by `hp2` + primality).

Composition sketch (≤3 lines, the existing proof body):
```lean
example (hp2 : p ≠ 2) {x : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])}) :
    ‖(x : ℚ_[p])‖ ^ (p - 1) < (p : ℝ)⁻¹ :=
  calc ‖(x : ℚ_[p])‖ ^ (p - 1)
      ≤ ((p : ℝ)⁻¹) ^ (p - 1) := pow_le_pow_left₀ (norm_nonneg _) (coe_norm_le_inv_of_mem_span p hx) _
    _ < (p : ℝ)⁻¹ := by
        have h3 : 3 ≤ p := by rcases hp.out.eq_two_or_odd' with h | h
                               · exact absurd h hp2
                               · have := hp.out.two_le; omega
        simpa using pow_lt_pow_right_of_lt_one₀ (inv_pos.mpr (by positivity))
          (by rw [inv_lt_one_iff₀]; exact .inr (by exact_mod_cast hp.out.one_lt)) (by omega)
```

Call sites in our project (from Phase 6.0): **K = 13** (PadicExp.lean ×9 / 10 occurrences,
ResidueZeta.lean ×4).

**Refactor plan.** Do **not** delete this lemma — unlike a redundant wrapper, it is genuinely
load-bearing project glue (13 uses, no inline re-derivation, and it threads the `hp2 → p ≥ 3`
reasoning that the call sites should not each repeat). The actionable conclusion is the
*negative* one for **mathlib**: it should **not** be PR'd as a standalone declaration, because
its conclusion type `InExpBall` is itself not mathlib-bound (sibling verdict
`NO-composable-from-mathlib`). If and when the surrounding `p`-adic `exp`/`log` API is prepared
for mathlib, this lemma travels *with* that API, restated to conclude the bare inequality
`‖(x:ℚ_p)‖ < p^{−1/(p−1)}` (or `x ∈ Metric.ball 0 r`) — matching mathlib's existing exponential
idiom — rather than the project-local `InExpBall`. As an independent decl it is just the ≤3-call
composition above and contributes no new mathlib API.

**Next action:** keep `inExpBall_of_mem_span` as project-local plumbing; do **not** PR it as a
standalone lemma. Re-assess it only as part of a larger "upstream the `p`-adic exp/log API"
effort, at which point it should be restated against mathlib's convergence-ball idiom (bare
inequality / `Metric.ball`), not the `InExpBall` predicate. The substantive, genuinely
contributable mathematics — `padicExp`/`padicLog`, the isometry
(`norm_padicExp_sub_padicExp`), the functional equation (`padicExp_add`), the inversions, and
RJW Lem 5.14 — is assessed under its own declarations.

---

## Phase 8 — Report summary

| Phase | Artifact | Outcome |
|-------|----------|---------|
| 0 Doctor | baseline | theorem, sorry-free, build reasoned-from-source |
| 1 Comprehend | prose statement | "for odd `p`, `pℤ_p ⊆` exp's convergence disc (`‖x‖ < p^{−1/(p−1)}`)" |
| 2 Prelim | size / one-line | SMALL; `theorem` (one-line def check n/a) |
| 3 Literature | 9-channel table | canonical (Conrad verbatim ✔) but always an INLINE computation, never a named theorem; ChatGPT MCP unavailable, compensated by 8 channels |
| 4 Generality | status + verdict + 4c | MAXIMALLY GENERAL; `hp2` necessary; no weakening; no Bourbaki-2.0 win |
| 4.5 Risk | — | n/a (kind = theorem) |
| 5 Mathlib | 5-method (D/E live; A/B/C MCP n/a) | NOT in mathlib; mathlib has no p-adic exp/log and no `InExpBall`; building block = `norm_le_pow_iff_mem_span_pow` |
| 6 Composition | call-sites + sketch | K = 13 internal / 0 external; COMPOSABLE (≤3 calls) |
| 7 Verdict | bucket + evidence | **`NO-composable-from-mathlib`** |

### Final verdict (five-bucket)

> ## **`NO-composable-from-mathlib`**

**Next step.** Keep `inExpBall_of_mem_span` as project-local plumbing (it is real, load-bearing
internal glue: 13 uses, no inline re-derivation). Do **not** PR it as a standalone mathlib
declaration: its conclusion names the project-local `InExpBall` predicate (sibling verdict
`NO-composable-from-mathlib`), and stripped of that wrapper it is a ≤3-call composition of
`PadicInt.norm_le_pow_iff_mem_span_pow` (via `coe_norm_le_inv_of_mem_span`), `pow_le_pow_left₀`,
and `pow_lt_pow_right_of_lt_one₀`. Revisit only inside a future "upstream the p-adic exp/log
API" PR, restated against mathlib's convergence-ball idiom (`‖x‖ < p^{−1/(p−1)}` /
`x ∈ Metric.ball 0 r`).
