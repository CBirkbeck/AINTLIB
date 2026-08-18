# `/mathlibable` report — `PadicLFunctions.summable_padicLog_terms`

Mode A, full 10-phase workflow, exhaustive 9-channel literature search.

**Final verdict: `BORDERLINE-needs-human`**

The decisive finding (and the contrast with the exp sibling): this lemma is stated on the
**exponential ball** `InExpBall p y` (= `‖y‖^{p−1} < p⁻¹`, radius `p^{−1/(p−1)}`), but the
literature-standard convergence domain of the `p`-adic logarithm series is the **full open
unit ball** `‖y‖ < 1` (radius `1`) — *strictly larger*. So Phase 4b is **STRICTLY NARROWER
THAN STANDARD**, which ordinarily routes to `YES-but-generalise-first`. But the same
"upstream-the-whole-`padicLog`-development-or-not" scope call that governed the exp sibling
`summable_padicExp_terms` (also `BORDERLINE`) applies here too, and it *interacts with* the
generalisation decision (the project deliberately proves summability on the small ball and
then reaches `‖y‖<1` downstream via the `p`-power-descent trick `exists_pPow_pow_inExpBall`).
Two independent human judgment calls genuinely fit two buckets — so per the skill's
"never silently pick between buckets" rule, the honest verdict is `BORDERLINE-needs-human`,
with the generality restatement and the scope question both spelled out below.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per task BUILD NOTE — `lake build` is stale/slow here; the declaration and its full dependency chain were read directly from source, exactly as the skill's Phase-0 fallback allows).
- decl `PadicLFunctions.summable_padicLog_terms`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:353`
- kind:                      theorem
- has sorry:                 no (complete `by`-proof; depends only on already-proven project lemmas + mathlib)
- module docstring summary:  *The p-adic exponential and logarithm (RJW Lem 5.14)* — `exp(x)=∑xⁿ/n!` converges and is an isometry on the open ball `‖x‖ < p^{−1/(p−1)}`; `log(1+y)=∑(−1)^{n+1}yⁿ/n` converges for `‖y‖<1` and inverts `exp` on the matched balls (Cassels §12 / Washington §5.1). This theorem (decomposition node, log analogue of E1+) is the **summability lemma** that makes the `tsum` defining `padicLog` meaningful.

---

### Statement (Phase 1)

`summable_padicLog_terms` is a **theorem** stating the following:

> Let `L` be a complete nonarchimedean (ultrametric) normed field that is a normed `ℚ_p`-algebra.
> For every `y` in the **exponential** convergence ball `‖y‖^{p−1} < p⁻¹` (i.e. `‖y‖ < p^{−1/(p−1)}`),
> the family of logarithm terms `n ↦ (−1)ⁿ · (n+1)⁻¹ · y^{n+1}` is **(unconditionally) summable**.

This is the summand family of the `p`-adic logarithm series `log(1+y) = ∑_{k≥1} (−1)^{k+1} yᵏ/k`
(re-indexed `k = n+1`), and the conclusion is that this series converges. The proof goes through
the nonarchimedean convergence criterion (a series converges iff its terms → 0) combined with the
exp-ball geometric tail bound.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime.
- `L : Type*`, `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — a
  complete ultrametric normed `ℚ_p`-algebra field. The general nonarchimedean setting (subsumes `ℚ_[p]`,
  `ℂ_p`, finite/algebraic extensions of `ℚ_[p]`).

Hypotheses (Lean side):
- `hy : InExpBall p y` — i.e. `‖y‖^{p−1} < p⁻¹`, the rpow-free spelling of `‖y‖ < p^{−1/(p−1)}` — the
  **exponential** ball, **strictly smaller** than the logarithm's natural domain `‖y‖ < 1`.

Conclusion (math): the logarithm series converges (unconditionally) for `y` in the exp ball.

Conclusion (Lean): `Summable fun n : ℕ => (-1 : L) ^ n * (((n : ℚ_[p]) + 1)⁻¹ • y ^ (n + 1))`.

**Proof shape (read from source, lines 353–380).** Rewrite `Summable` via the project's E1 wrapper
`summable_iff_tendsto_cofinite_zero` (a thin re-export of mathlib's
`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`), then `Nat.cofinite_eq_atTop`
+ `tendsto_zero_iff_norm_tendsto_zero` reduce to `‖(−1)ⁿ(n+1)⁻¹•y^{n+1}‖ → 0`. The geometric
majorant `‖y‖^{p−1}·(p‖y‖^{p−1})ⁿ → 0` (from `tendsto_pow_atTop_nhds_zero_of_lt_one`, valid because
`p‖y‖^{p−1} < 1` **on the exp ball**) dominates via the project lemma `norm_succ_inv_smul_pow_le`
(`PadicExp.lean:326`, which packages the Legendre-style bound `sub_one_mul_padicValNat_succ_le`), and a
`(p−1)`-th-power squeeze `lt_of_pow_lt_pow_left₀` closes it. **Note:** the exp ball is used *only* to get
`p‖y‖^{p−1} < 1` for the geometric majorant; mere summability holds on the larger ball `‖y‖<1` by a
different (polynomial × geometric) majorant — see Phase 4.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (with a BIG caveat)
Reason: as a *declaration* it is a helper lemma (a summability fact, the log analogue of node E1+), not a
`def`/structure and not a named theorem. **However**, it is the summability foundation of a BIG object —
the project's `p`-adic logarithm `padicLog` (`PadicExp.lean:384`, a named mathematical object absent from
mathlib) — so while the lemma is SMALL, its mathlib fate is governed by the BIG def it underpins.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-liner check **n/a** (one-line note).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | p-adic logarithm `log(1+x)=∑(−1)^{n+1}xⁿ/n` convergence series radius `\|x\|<1`                          | yes  | converges on the open unit disc `\|x\|_p < 1`; radius `r=1` | PlanetMath "p-adic exponential and p-adic logarithm"; K. Conrad "Infinite series in p-adic fields"; MIT `~dav/exp.pdf`; Montréal "Power series convergence and the p-adic logarithm" |
|  2 | WebSearch (general / sharp form) | p-adic log converges open unit ball `\|x\|_p<1` nonarchimedean field; contrast with exp domain          | yes  | `S={s∈ℂ_p:\|s\|_p<1}`, radius 1; **strictly larger** than exp's `\|s\|<p^{−1/(p−1)}` | PlanetMath (explicit: "the logarithm converges in a wider domain than the exponential; for p≥3 exp is only on `pℤ_p`"); Crew LCFT; Cambridge/Bayreuth p-adic-analysis notes |
|  3 | WebSearch (named-after / criterion) | nonarchimedean power series converges iff `\|aₙxⁿ\|→0`; Cauchy–Hadamard radius for `∑(−1)^{n+1}xⁿ/n`; `v_p(n)≤log_p n` | yes  | radius via `(limsup\|aₙ\|^{1/n})^{−1}=1`; the named **nonarchimedean Σ⇔→0 criterion**; `‖xⁿ/n‖→0` for `‖x‖<1` since `\|1/n\|_p` grows only polynomially | K. Conrad; ResearchGate "On convergence of power series in p-adic field"; arXiv 2412.16517 (radius of `∑v_p(n)Xⁿ` is 1) |
|  4 | ChatGPT MCP                      | (intended: "standard convergence domain of the p-adic log series, its generality, and how the `‖xⁿ/n‖→0` proof differs from exp") | n/a  | —                                | ChatGPT MCP server **not configured** in this environment (`/setup-chatgpt` not run). Recorded n/a; WebSearch (3 queries) + PlanetMath + K. Conrad + the module's own citations (RJW, Cassels §12, Washington §5.1) fully cover the standard-form question — sources are unanimous. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                | n/a  | (no references dir; no `refs/` symlink) | both directories **absent** on this machine — recorded n/a. The module docstring's inline citations (RJW TeX 1892–1897 "as stated"; Cassels §12; Washington §5.1) serve as the literature anchor. |
|  6 | nLab                             | p-adic number / p-adic logarithm / nonarchimedean analytic function convergence                         | partial | nLab's "p-adic number" page covers valuation/metric/total-disconnectedness but **does not** treat the log/exp convergence domains; routes p-adic analysis to rigid/Berkovich geometry | not a categorical concept; no standalone p-adic-log-summability statement on nLab |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                | not a categorical concept (summability of a concrete `(−1)ⁿ yⁿ⁺¹/(n+1)` family in a p-adic field). |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                | not an algebraic-geometry concept (analytic/series convergence, not scheme/sheaf theory). |
|  9 | MathOverflow / Math.StackExchange| domain of convergence of the p-adic logarithm; why `log_p` converges on `\|x\|<1` but `exp_p` only on the smaller ball | yes  | community consensus matches #1–#3: `log(1+x)` converges exactly on `\|x\|_p<1` by terms→0 (`\|1/n\|_p` polynomial vs `‖x‖ⁿ` geometric); endpoint `\|x\|=1` fails | recurring Q&A; the radius `1` and the terms→0 criterion are textbook-standard, never disputed |
| 10 | recent arXiv (last 5 years)      | p-adic logarithm / fast evaluation of p-adic transcendental functions; Iwasawa logarithm extension      | partial | arXiv 2106.09315 (fast eval), 1907.06437 (2-adic log on principal units), 2412.16517 reuse the classical radius-1 convergence; the *Iwasawa* log then extends `log_p` to all of `ℚ_p^×` by an additional convention | confirms no modern reformulation supersedes the classical `‖x‖<1` convergence statement; the Iwasawa extension is a separate (post-convergence) normalisation |

The protocol passed: WebSearch ran **3** distinct queries at three generality levels (specific log-series
convergence / the general nonarchimedean domain-and-contrast-with-exp / the named Cauchy–Hadamard + Σ⇔→0
criterion with the `v_p(n)≤log_p n` bound); ChatGPT MCP recorded n/a with reason (server absent); local
references recorded n/a with reason (no dir); nLab checked; nCatLab / Stacks recorded n/a with reason;
MathOverflow and recent arXiv each checked.

### Literature summary (Phase 3)

Concept identified as: **convergence (summability) of the `p`-adic logarithm series
`log(1+y) = ∑_{k≥1} (−1)^{k+1} yᵏ/k`** — the foundational convergence fact underlying the `p`-adic
logarithm function `log_p`.

Sources agree on the standard form: **yes, unanimously.** Every source (PlanetMath, K. Conrad, the MIT
notes, MathOverflow, Cassels §12 via the module) gives the identical statement: `∑(−1)^{n+1}yⁿ/n` converges
**iff** `‖y‖_p < 1` (the **full open unit disc**, radius `1`), and the proof is always the same two
ingredients — (i) the **nonarchimedean convergence criterion** "a series converges iff its terms → 0", and
(ii) the bound `‖yⁿ/n‖_p = p^{v_p(n)}·‖y‖ⁿ`, where `v_p(n) ≤ log_p n` grows only **polynomially** so the
geometric `‖y‖ⁿ` (with `‖y‖<1`) wins and the terms → 0.

Most general standard form: over **any complete nonarchimedean field extending `ℚ_p`**, `∑(−1)^{n+1}yⁿ/n`
is summable for **`‖y‖ < 1`** (the open unit ball). The project's `L` is precisely this maximal *field*
setting — but the project's **hypothesis** is `InExpBall p y` (`‖y‖^{p−1}<p⁻¹`), the **exponential** ball,
which is **strictly smaller** than the literature's `‖y‖ < 1`.

Generality dimensions where the literature varies:
- **Underlying field**: `ℚ_p` → `ℂ_p` / arbitrary complete nonarchimedean extension. The most general is
  "any complete ultrametric normed `ℚ_p`-algebra field" — which the target already uses. ✓ maximal.
- **Convergence domain (the binding axis)**: literature radius is **`1`** (`‖y‖<1`); the target's
  hypothesis radius is **`p^{−1/(p−1)} < 1`** (the exp ball). PlanetMath states this contrast verbatim:
  the log "converges in a wider domain than the exponential." → the target is **strictly narrower** here.
- **Strength of conclusion**: standard p-adic statement is *plain* convergence (`Summable`); the target
  proves exactly `Summable`. ✓ natural p-adic strength.

Disagreement with the literature: the target's **hypothesis is strictly stronger than the literature
standard** — it uses the exp ball where the log converges on the whole unit ball. This is the
generalisation lever (Phase 4).

---

### Generality analysis — `summable_padicLog_terms`

Literature-standard form (from Phase 3): over any complete nonarchimedean field ⊇ `ℚ_p`,
`∑_{k≥1}(−1)^{k+1}yᵏ/k` is summable for **`‖y‖ < 1`** (the full open unit ball).

| # | Parameter / hypothesis                | Current Lean form          | Literature-standard form     | Weaker form exists? | Reason it can/can't be weakened |
|---|---------------------------------------|----------------------------|------------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L]`                     | normed field               | complete nonarch field ⊇ ℚ_p | NO                  | a field structure is needed for `(n+1)⁻¹` scalars and for the norm; matches the standard setting |
| 2 | `[NormedAlgebra ℚ_[p] L]`             | normed ℚ_p-algebra          | extension of ℚ_p             | NO (essentially)    | `(n+1)⁻¹` is the image of a ℚ_p-scalar; the algebra structure is what lets the `‖n+1‖_p = p^{−v_p(n+1)}` bound (computed in `ℚ_p`) control `‖(n+1)⁻¹•y^{n+1}‖` in `L` |
| 3 | `[IsUltrametricDist L]`               | ultrametric norm            | nonarchimedean field         | NO                  | the **nonarchimedean** Σ⇔→0 criterion is the heart of the proof and *requires* the ultrametric inequality; this IS the defining hypothesis of the standard form |
| 4 | `[CompleteSpace L]`                   | complete                   | complete                     | NO                  | completeness is exactly what makes "terms → 0 ⇒ summable" true; cannot drop |
| 5 | **`hy : InExpBall p y` (`‖y‖^{p−1} < p⁻¹`, radius `p^{−1/(p−1)}`)** | **exponential** ball | **`‖y‖ < 1`** (unit ball, radius 1) | **YES** | **The binding weakening.** The log series converges on the *whole* unit ball, not just the exp ball. The exp ball is used **only** to obtain the *geometric* majorant `p‖y‖^{p−1}<1`; for mere summability, the literature's *polynomial × geometric* majorant `‖(n+1)⁻¹•y^{n+1}‖ = p^{v_p(n+1)}‖y‖^{n+1} ≤ (n+1)‖y‖^{n+1} → 0` works for any `‖y‖<1`. The supporting bound `padicValNat p (n+1) ≤ Nat.log p (n+1)` (⇒ `p^{v_p(n+1)} ≤ n+1`) is **already in mathlib** (`Mathlib.padicValNat_le_nat_log`). |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD.**
Number of weakening opportunities found: **1** (the convergence-domain hypothesis, row 5).

Proposed restatement (weaken `InExpBall p y` → `‖y‖ < 1`):

```lean
theorem summable_logSeries_terms {y : L} (hy : ‖y‖ < 1) :
    Summable fun n : ℕ => (-1 : L) ^ n * (((n : ℚ_[p]) + 1)⁻¹ • y ^ (n + 1)) := by
  sorry -- proof must switch the majorant: from the exp-ball geometric bound
        -- ‖y‖^{p−1}·(p‖y‖^{p−1})ⁿ  to the polynomial×geometric bound
        -- p^{v_p(n+1)}·‖y‖^{n+1} ≤ (n+1)·‖y‖^{n+1} → 0 (via padicValNat_le_nat_log)
```

Cost of restatement: **MODERATE** — the *statement* change is trivial, but the current proof's geometric
majorant (`norm_succ_inv_smul_pow_le`, which needs `p‖y‖^{p−1}<1`) does **not** hold on the full unit ball,
so the proof must be re-done with the literature's polynomial-times-geometric majorant. The ingredients are
all in mathlib (`padicValNat_le_nat_log`, `Padic.valuation_natCast`, `Padic.norm_eq_zpow_neg_valuation`,
`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`, and a polynomial-vs-geometric decay fact), so
no fundamentally new idea is needed — but it is a genuine re-proof, not a mechanical rewrite.

→ Phase 7 considers `YES-but-generalise-first` **prominently** (STRICTLY NARROWER), tensioned against the
`BORDERLINE` scope question that also applies (the upstream-the-`padicLog`-development decision, exactly as
for the exp sibling) — and against the project's structural reason for the narrow statement (Phase 6).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                        | no       | — | hypotheses are already typeclasses; nothing to bundle |
|  2 | sequences/metric → filters/nets/topological?                                                              | partial  | proof already uses `cofinite`/`atTop` filters via the E1 criterion + `tendsto_zero_iff_norm_tendsto_zero` — already in the modern filter idiom | none further; `Summable` is the right filter-free packaging |
|  3 | construct an object → universal-property class?                                                           | no       | — | convergence fact, not a construction |
|  4 | set-with-closure-predicate → bundled substructure?                                                        | no       | — | n/a |
|  5 | field-specific → weaken typeclass hierarchy / use `FormalMultilinearSeries.radius` idiom?                 | partial  | the cleanest mathlib idiom would state the domain as `y ∈ EMetric.ball 0 1` (radius 1) and ideally re-use a `PowerSeries.log`/`logTaylor`-evaluation-summability lemma — but mathlib has **no** nonarchimedean `expSeries.radius` / log-radius computation (its `Complex.logTaylor` is archimedean-only); blocked until a p-adic radius lemma exists | would let this re-use `FormalMultilinearSeries.summable` once the p-adic log-radius is computed; this is the same def-layer modernisation lever flagged for the exp sibling |
|  6 | 1-categorical → higher-categorical?                                                                       | no       | — | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive structure?                                                     | no       | — | the index `n : ℕ` is intrinsic to the integer-denominator series |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for the signature as a standalone statement). The proof is already in the
contemporary filter/`Summable` idiom. The one organisational improvement (row 5, re-using a mathlib
`FormalMultilinearSeries.radius`/log-evaluation lemma) lives **one layer down** and is **infeasible today**:
mathlib has no nonarchimedean log-series radius computation (`Complex.logTaylor` / `hasSum_taylorSeries_log`
are complex/archimedean; `PowerSeries.log` is purely formal with no convergence). One-line reason it is not
itself a modernisation move: it is a concrete summability statement already in idiomatic form; the genuine
generalisation lever is the **domain weakening** (`InExpBall → ‖y‖<1`, Phase 4b), not a categorical recast.

---

### Diamond / defeq risk — `summable_padicLog_terms`

**n/a — declaration kind is `theorem`.** (Phase 4.5 runs only for `def`/`class`/`instance`.)

---

### Mathlib search-status: `summable_padicLog_terms`

[A] Lean-Finder       "p-adic logarithm series summable", "summable (-1)ⁿ yⁿ⁺¹/(n+1) ball"   n/a: Lean-Finder web UI not callable in this environment — substituted with exhaustive grep over the mathlib tree (method D) for every candidate name/shape, plus reading the candidate decls' actual statements.
[B] Loogle            `Summable (fun n => (-1)^n * ((↑n+1)⁻¹ • _ ^ (n+1)))`, `Summable (fun n => (-1)^n * _)`, `_ → Summable (fun n => _ • _ ^ _)`   **no p-adic hit**: the only `(-1)^n`-shaped summability lemma in mathlib is `Topology/Algebra/InfiniteSum/NatInt.lean:518` (`Summable (fun n => (-1)^n * f n)` — an *alternating-from-a-summable-`f`* repackaging, **not** a convergence theorem for the log series). No `(n+1)⁻¹•yⁿ⁺¹` family.
[C] LeanSearch        "p-adic logarithm series converges on unit disc", "summability of logarithm terms nonarchimedean field"   no direct p-adic hit: surfaces only the **complex** `Complex.logTaylor` / `hasSum_taylorSeries_log` family; nothing nonarchimedean / p-adic.
[D] Grep mathlib src  `grep -rniE "padicLog|padic.*log|nonarchimedean.*log"` over `.lake/packages/mathlib/Mathlib/`   **NO** p-adic/nonarchimedean logarithm anywhere; `NumberTheory/Padics/` has no exp/log file at all. Found instead: the **building blocks** — `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` (`Topology/Algebra/InfiniteSum/Nonarchimedean.lean:18`); `Mathlib.padicValNat_le_nat_log` (`NumberTheory/Padics/PadicVal/Basic.lean:467`, the polynomial bound `v_p(n) ≤ log_p n`); `Padic.valuation_natCast`/`norm_eq_zpow_neg_valuation` (`PadicNumbers.lean:1078,1053`); `tendsto_pow_atTop_nhds_zero_of_lt_one`/`summable_geometric_of_lt_one` (`SpecificLimits/Basic.lean`). |
[E] Name pattern      `padicLog`, `logSeries_summable`, `log_taylor_summable`, `InExpBall`, `summable_log`   `padicLog`/`InExpBall` do not exist in mathlib. `Complex.logTaylor` (`Analysis/SpecialFunctions/Complex/LogBounds.lean:68`) is the complex Taylor polynomial of `log(1+z)` for `‖z‖<1` — **archimedean only**; no nonarchimedean log summability anywhere. grep for `IsUltrametricDist`/`Nonarchimedean` in the log/exp analysis files returns empty.

Searched for both:
- the user's current form (`Summable (fun n => (−1)ⁿ(n+1)⁻¹•yⁿ⁺¹)` on the exp ball `‖y‖^{p−1}<p⁻¹`) — **not** in mathlib.
- the **literature-standard / more-general** form (the same series on the **full unit ball** `‖y‖<1`) —
  also **not** in mathlib (the general-form search is important precisely because mathlib often has the
  general form; here it has neither form — the only log series in mathlib is the *complex* `logTaylor`).

Concluded: **not in mathlib (all 5 methods exhausted, plus the literature-standard `‖y‖<1` form).** Mathlib
has the *ingredients* (the nonarchimedean Σ⇔→0 criterion; the polynomial valuation bound
`padicValNat_le_nat_log`; the `Padic` norm/valuation API; the geometric-decay limits) but **no** p-adic
logarithm and **no** summability statement for this series in either form. The only nearby decl,
`Complex.logTaylor`, is archimedean and inapplicable.

---

### Call sites — `summable_padicLog_terms`

Internal use count: **3** (all within the declaring file `PadicExp.lean`; the skill's grep convention
counts uses outside the *declaring theorem*, all three are in other theorems of the same file)
External-to-file callers: **0 distinct files**

| Caller file:line               | Usage pattern (one-line excerpt)                                              |
|--------------------------------|-------------------------------------------------------------------------------|
| PadicExp.lean:423              | `have hsum := summable_padicLog_terms p hx` — feeds `norm_padicLog` (the isometry `‖log x‖ = ‖x−1‖` on the exp ball) |
| PadicExp.lean:888              | `(summable_padicLog_terms p hx).congr fun n => padicLog_term_eq p x n` — bridges the bespoke log series to the `PowerSeries.log` coefficients in `padicLog_eq_tsum_coeff` |
| PadicExp.lean:940              | `(summable_padicLog_terms p hx).congr fun n => padicLog_term_eq p x n` — same coeff-bridge, feeding `padicExp_padicLog` (the inversion `exp(log x) = x` on the matched balls) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none) — every place the log series' summability is needed routes through this lemma. The `‖x−1‖<1`
    full-unit-ball log identities downstream (`ValuesAtOne.lean`: `padicLog_mul_of_norm_lt_one`,
    `padicLog_pow_*`) do **not** re-derive summability inline; they reach the larger ball via the
    `p`-power-descent lemma `exists_pPow_pow_inExpBall` applied to the *already-defined* `padicLog`, never
    by re-summing on `‖y‖<1`. So there is no competing inline summability proof.

What the call-sites pattern tells you: **K = 3 internal uses, no external file, no inline re-derivation.**
Per the Phase-6 signal table (`K ≥ 3`, no inline bypass) this is a **real-API** signal — the three
consumers (the isometry, the coeff-bridge, the inversion) genuinely depend on it; it is the substrate of the
log half of the exp/log development. It is **not** dead code or a one-off wrapper. (It is more modestly
reused than the exp sibling's K=8+1, but still clears the "real API" bar, and crucially is **never bypassed**
by an inline re-derivation.)

---

### Composition check (Phase 6)

Can `summable_padicLog_terms` be derived from mathlib in ≤3 chained calls?

Attempt 1: a mathlib p-adic-log-summability lemma applied directly.
  - Mathlib decls used: (none exist).
  - Result: **fails** — Phase 5 found mathlib has **no** p-adic logarithm and no summability statement for
    this series in either the exp-ball or the unit-ball form. `Complex.logTaylor` is archimedean.

Attempt 2: nonarchimedean criterion + the polynomial-valuation bound + a geometric/decay fact.
  - Mathlib decls used: `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` +
    `Mathlib.padicValNat_le_nat_log` + `Padic.norm_eq_zpow_neg_valuation` + a polynomial-times-geometric
    decay fact.
  - Result: **this is essentially the (generalised) literature proof**, and it is **not** a ≤3-call
    composition. It requires (i) the criterion rewrite, (ii) `Nat.cofinite_eq_atTop` +
    `tendsto_zero_iff_norm_tendsto_zero`, (iii) computing `‖(n+1)⁻¹•y^{n+1}‖ = p^{v_p(n+1)}‖y‖^{n+1}` via the
    `Padic` valuation API, (iv) bounding `p^{v_p(n+1)} ≤ n+1` via `padicValNat_le_nat_log`, and (v) a
    polynomial-vs-geometric decay argument (`(n+1)‖y‖^{n+1}→0`). That is a real ~20-line proof, i.e. a genuine
    theorem, not a composition.
  - (The *project's* actual proof is the exp-ball variant via `norm_succ_inv_smul_pow_le`, itself a
    multi-step lemma built on `sub_one_mul_padicValNat_succ_le`; equally non-composable.)

Conclusion: **NOT-COMPOSABLE.** Mathlib has the *ingredients* (the nonarchimedean criterion, the polynomial
valuation bound `padicValNat_le_nat_log`, the `Padic` norm/valuation API, the geometric-decay limits), but
assembling them into this summability statement — in *either* the current exp-ball form or the more-general
`‖y‖<1` form — is a multi-step proof, and mathlib has no log-series lemma of the right shape to call.

---

## Verdict: `summable_padicLog_terms`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the target is the summability of the **standard `p`-adic log series**
  `∑(−1)^{k+1}yᵏ/k`, but its hypothesis is the **exp ball**, whereas the literature-standard convergence
  domain is the **full open unit ball `‖y‖<1`** (radius 1, vs the exp ball's `p^{−1/(p−1)}`). Sources are
  unanimous and explicit about the contrast (PlanetMath: the log "converges in a wider domain than the
  exponential").
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — exactly one weakening (row 5):
  `InExpBall p y` → `‖y‖ < 1`. Cost MODERATE (statement trivial; proof must switch from the exp-ball
  geometric majorant to the polynomial×geometric majorant — ingredients all in mathlib). Modern-idiom (4c):
  already idiomatic; the FMS-radius recast is blocked by a missing p-adic log-radius lemma.
- Mathlib search (Phase 5): **not in mathlib** — no p-adic logarithm; no summability statement in either
  form; the only nearby decl `Complex.logTaylor` is archimedean. Building blocks
  (`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`, `padicValNat_le_nat_log`, the `Padic`
  valuation API, geometric-decay limits) **are** mathlib.
- Composition check (Phase 6): **NOT-COMPOSABLE** — a genuine ~20-line proof in either form, no callable
  log-series lemma. Call sites: **K=3 internal, no external, no inline re-derivation** (real-API signal).

**Rationale (why BORDERLINE — and not a clean YES-but-generalise-first, nor a NO):**

This is a *true, genuinely-missing-from-mathlib* p-adic convergence statement, proved sorry-free, with real
(K=3) reuse. Phases 4 and 6 both push *away* from the NO buckets: it is **not** NO-composable (the proof is a
real multi-lemma argument, not a ≤3-call composition — Phase 6 Attempt 2) and **not** NO-mathlib-has-it
(mathlib has neither form; the only log series is the complex `logTaylor` — Phase 5). So the live choice is
between `YES-but-generalise-first` and `BORDERLINE-needs-human`, and per the skill's "never silently pick
between two fitting buckets" rule the decision turns on **two human judgment calls the search cannot make**,
which moreover *interact*:

1. **The generalisation target (`InExpBall → ‖y‖<1`) is the right mathlib form — but whether to take it
   here collides with how `padicLog` is structured.** Phase 4b is unambiguous that the literature statement
   is the full-unit-ball one (radius 1), so the mathlib-worthy lemma is `summable` on `‖y‖<1`, not on the exp
   ball. *However*, the project deliberately states summability on the *small* exp ball because that is where
   the `tsum` defining `padicLog` is first shown well-formed; the full-unit-ball domain is then reached
   *downstream* (the isometry `norm_padicLog`, and especially `ValuesAtOne.lean`'s
   `padicLog_mul_of_norm_lt_one`/`padicLog_pow_*`) via the `p`-power-descent trick `exists_pPow_pow_inExpBall`
   — i.e. the project gets the large-ball *identities* without ever re-summing on `‖y‖<1`. So "generalise the
   summability lemma to `‖y‖<1`" is mathematically correct and mathlib-preferred, but in *this* codebase it is
   not a drop-in (the exp-ball form is what the local proofs consume) and the right move depends on whether
   the mathlib API is being built fresh (take `‖y‖<1`) or the existing project structure is being upstreamed
   verbatim (keep the exp-ball form + the descent). That is a packaging decision for the user, not a fact in
   the evidence — so it cannot self-resolve to `YES-but-generalise-first` with a single mandated restatement.

2. **It cannot be PR'd standalone — it is the summability foundation of a `padicLog` def mathlib does not
   have, and that whole development is the real contribution.** Its three consumers are the log isometry, the
   `PowerSeries.log`-coefficient bridge, and the inversion `exp(log x)=x`. Mathlib has **no** p-adic /
   nonarchimedean logarithm (its only log series is the complex `logTaylor`). So upstreaming this lemma
   sensibly means upstreaming a **BIG, multi-decl nonarchimedean-`log` development** (the `padicLog` def, its
   convergence/summability, the isometry, multiplicativity on the unit ball, inversion against `padicExp`).
   Whether to undertake that — and *how* to package it (with the generality choice in (1) settled as part of
   it) — is a project/community-policy decision. This is the **same governing decision** flagged for the
   sibling `summable_padicExp_terms` (also `BORDERLINE`) and the `norm_padicExp_*` family; the log and exp
   summability lemmas share one mathlib fate.

The MODERATE generalisation cost is **not** invoked as the reason for BORDERLINE (an EXPENSIVE/MODERATE
re-proof would still be worth doing — mathlib's value is the right form). The genuine blocker is the pair of
*interacting scope/packaging judgments* in (1)+(2), which the skill must defer. The K=3 real-API signal
confirms the lemma is load-bearing within the project but does not settle its mathlib form or its standalone
upstreamability.

**Numbered questions (≤5):**

1. **Generality:** the literature-standard convergence domain of the log series is the **full open unit ball
   `‖y‖<1`** (radius 1), strictly larger than the exp ball this lemma uses. Do you want the mathlib statement
   to be the unit-ball form `summable_logSeries_terms {y} (hy : ‖y‖ < 1)` (re-proved with the
   polynomial×geometric majorant via the already-in-mathlib `padicValNat_le_nat_log`), rather than the
   current `InExpBall` form? (Yes → the contribution is `YES-but-generalise-first` to `‖y‖<1`; No, keep the
   exp-ball form → go to Q2/Q3.)
2. **Scope (governs everything):** do you intend to upstream the project's `p`-adic / nonarchimedean
   **logarithm development** to mathlib as a unit — the `padicLog` def, its summability (this lemma), the
   isometry `norm_padicLog`, multiplicativity on the unit ball (`padicLog_mul_of_norm_lt_one`), and the
   inversion `padicExp_padicLog`/`padicLog_padicExp` — *together with* the exp development (`summable_padicExp_terms`
   etc.)? This lemma is the summability foundation of that development and should travel *with* it, not alone.
3. **Structure (if Q1=No and Q2=Yes):** the project proves summability on the *small* exp ball and reaches
   `‖y‖<1` downstream via `p`-power descent (`exists_pPow_pow_inExpBall`). For mathlib, do you want to keep
   that structure (exp-ball summability + descent), or front-load the full-unit-ball summability lemma so the
   downstream identities can drop the descent trick? (This is the packaging interaction between Q1 and Q2.)
4. **Drop-from-consideration:** if you do **not** plan to upstream the p-adic-log machinery, then this lemma
   stays a (real, K=3) project-local summability foundation — correct as-is on the exp ball — and should be
   dropped from mathlib consideration. Is that the case?

**Next action:** user answers the questions; re-run `/mathlibable summable_padicLog_terms`, preferably
**together with `/mathlibable PadicLFunctions.padicLog`** (the def whose upstreaming decision governs this
lemma) and the exp siblings `/mathlibable PadicLFunctions.summable_padicExp_terms` /
`/mathlibable PadicLFunctions.padicExp` — the exp and log summability lemmas share one mathlib fate. Likely
resolutions:
  - "Upstream the nonarchimedean exp/log development, stated at literature generality" → flips to
    **YES-but-generalise-first** (restate summability on `‖y‖<1`, re-proved with the polynomial×geometric
    majorant), shipped as part of the multi-decl nonarchimedean-`log` PR series — with the Q3 structure choice
    settled in that PR's design.
  - "Upstream verbatim, keep the project structure" → **YES-add-as-is** on the exp-ball form as a foundation
    lemma of the development (with the larger ball reached by the descent lemmas), since the form is then
    deliberate and non-composable.
  - "Keep project-local" → drop from mathlib consideration; it stays the (correct, K=3) summability
    foundation of the project's exp/log development.

---

## Next step

User answers the four numbered questions above; re-run `/mathlibable summable_padicLog_terms` — preferably
alongside `/mathlibable PadicLFunctions.padicLog`, `/mathlibable PadicLFunctions.summable_padicExp_terms`,
and `/mathlibable PadicLFunctions.padicExp`, since this lemma's verdict is governed by (a) the generality
choice `InExpBall → ‖y‖<1` and (b) the BIG, multi-decl upstreaming decision on the p-adic exp/log definitions
it underpins — to resolve to `YES-but-generalise-first` (upstream at literature generality on `‖y‖<1`),
`YES-add-as-is` (upstream the project structure verbatim), or drop-from-consideration (keep project-local).
