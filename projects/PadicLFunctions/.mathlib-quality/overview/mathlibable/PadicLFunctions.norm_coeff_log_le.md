# `/mathlibable` report — `PadicLFunctions.norm_coeff_log_le`

**Final verdict: `BORDERLINE-needs-human`**

---

### Baseline (Phase 0)

- lake build:               build not re-run (stale/slow per task note); reasoned from source — decl + dependency chain read directly.
- decl `PadicLFunctions.norm_coeff_log_le`:  ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:853`
- kind:                      theorem
- has sorry:                 no (the file is sorry-free at and around the target)
- module docstring summary:  The p-adic exponential and logarithm (RJW Lem 5.14): `exp`/`log` as evaluations of the formal power series `PowerSeries.exp`/`PowerSeries.log` on matched balls of a complete ultrametric `ℚ_[p]`-algebra field; `x^s := exp(s·log x)`.

---

### Statement (Phase 1)

`PadicLFunctions.norm_coeff_log_le` is a theorem stating the following:

For a prime `p` and every `n ≥ 1`, the n-th coefficient of the formal logarithm power series `PowerSeries.log` over `ℚ_[p]` — which is `(-1)^(n+1)/n` — satisfies the **Legendre-type bound**
```
‖ [Xⁿ] log ‖_p ^(p−1)  ≤  p^(n−1).
```
Equivalently (taking p-adic valuations), `(p−1)·v_p(1/n) ≥ −(n−1)`, i.e. `(p−1)·v_p(n) ≤ n−1`. This is the **rpow-free integer-exponent encoding** of the radius-of-convergence estimate for the p-adic logarithm: it is the bound on the size of the Taylor coefficients `1/n` that makes `log(1+y) = ∑ (−1)^{n+1} yⁿ/n` converge on the unit ball. It is the logarithm analogue of `norm_coeff_exp_le` (the `1/n!` / Legendre bound for `exp`).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime; coefficients live in `ℚ_[p]`.
- `PowerSeries.log ℚ_[p]` — mathlib's formal log power series specialised to the `ℚ`-algebra `ℚ_[p]`.

Hypotheses (Lean side):
- `(n : ℕ)` — the coefficient index.
- `(hn : 1 ≤ n)` — excludes the (zero) constant coefficient.

Conclusion (math): the `(p−1)`-th power of the p-adic norm of the n-th log coefficient is at most `p^(n−1)`.

Conclusion (Lean): `‖(coeff n (PowerSeries.log ℚ_[p]) : ℚ_[p])‖ ^ (p - 1) ≤ (p : ℝ) ^ (n - 1)`.

**Proof shape (from source).** Three lines: rewrite the coefficient via `PowerSeries.coeff_log` + `if_neg`, push the norm through `map_div₀`/`map_pow`/`map_neg`/`norm_*` to reach `(‖(n:ℚ_[p])‖^(p−1))⁻¹`, then close with the project lemma `norm_natCast_inv_pow_le p n hn`. The mathematical weight is entirely in `norm_natCast_inv_pow_le`, whose core is the valuation inequality `(p−1)·v_p(n) ≤ n−1` (project lemma `sub_one_mul_padicValNat_succ_le`, proved from Bernoulli `one_add_mul_le_pow` + `pow_padicValNat_dvd`).

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: A helper/specialisation lemma — one of a family (`norm_coeff_exp_le`, `norm_natCast_inv_pow_le`, `norm_factorial_inv_pow_le`) feeding the convergence/inversion proofs `padicExp_padicLog` / `padicLog_padicExp`. Not a named theorem, not a structure, not listed as a standalone "Main result". (Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 4 substantive lines (a `rw` chain + `rw` + `exact`).
One-liner verdict: n/a — kind is `theorem`, not a `def`.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                       | Hit? | Standard form found | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic logarithm radius of convergence valuation coefficients log(1+x) converges unit ball"                | yes  | `log(1+x)=∑(−1)^{n+1}xⁿ/n`, radius 1, converges on the open unit ball; `\|1/n\|_p = p^{v_p(n)}` controls convergence | MIT 18.785 PS10; K. Conrad "Infinite series in p-adic fields"; Koblitz Ch. on log/Γ/Artin–Hasse |
|  2 | WebSearch (general form / exp sibling) | "p-adic exponential logarithm convergence Washington cyclotomic fields v_p(n) bound coefficients"    | yes  | exp radius `p^{−1/(p−1)}` via Legendre `v_p(n!)=(n−S_n)/(p−1)`; log radius 1 via Cauchy–Hadamard `1/r=limsup\|a_n\|_p^{1/n}` | PlanetMath "p-adic exponential and logarithm"; Wikipedia "P-adic exponential function"; MIT exp.pdf |
|  3 | WebSearch (named-after / aliases) | "p-adic valuation n divides logarithm series term y^n/n nonarchimedean convergence Koblitz"               | yes  | `\|xⁿ/n\|_p ≤ λⁿ p^{v_p(n)} → 0` for `\|x\|<1`; `v_p(n) ≤ ⌊log n/log p⌋` | Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions* (ProofWiki index); Leiden Dio ch.8 |
|  4 | WebSearch (idiom: bound form)    | `"v_p(n)" inequality "(n-1)/(p-1)" p-adic logarithm coefficient bound exp log isometry`                     | yes  | Confirms the `1/(p−1)`-radius framing for exp; log uses the `v_p(n)` denominator estimate; exp/log are isometries on matched balls | Montreal Appendix 16 "Power series convergence and the p-adic logarithm"; Dion report |
|  5 | WebSearch (MO / refinements)     | "mathoverflow p-adic logarithm exp coefficient valuation bound 1/n converges open unit ball isometry strassmann" | yes  | `r=1` because `\sqrt[n]{\|n\|_p}→1`; exp converges/bijects on valuative radius `1/(p−1)`; Strassmann/Hensel context | Cambridge p-adic notes (Thorne); UChicago REU (Chen, Gupta) |
|  6 | ChatGPT MCP                      | n/a — MCP server **not installed** in this environment (ToolSearch for a ChatGPT/openai tool returned none) | n/a  | —                   | Channel unavailable; compensated by 5 WebSearch queries at distinct generality levels + direct source fetches |
|  7 | Local references                 | `projects/PadicLFunctions/.mathlib-quality/references/` — directory **absent** (only `overview/` present)    | n/a  | —                   | No project PDFs/notes to consult; recorded n/a per protocol |
|  8 | nLab                             | WebFetch `ncatlab.org/nlab/show/p-adic+logarithm`                                                           | n/a  | 404 — no dedicated nLab page under that title | The classical analytic p-adic log is not an nLab-categorical entry; WebSearch nLab query (#5 cluster) surfaced only arXiv, not nLab |
|  9 | nCatLab (if categorical)         | (same as #8)                                                                                                | n/a  | —                   | Not a categorical concept — an elementary coefficient/valuation estimate |
| 10 | Stacks Project (if alg geom)     | —                                                                                                           | n/a  | —                   | Not an algebraic-geometry concept (no schemes/sheaves); a `ℚ_[p]`-analysis estimate |
| 11 | MathOverflow / Math.StackExchange| (covered by query #5)                                                                                       | yes  | Confirms radius-1 + isometry framing | Folded into #5 |
| 12 | recent arXiv (last 5 years)      | surfaced across #1–#5 (e.g. 1904.09850 "image of p-adic log on principal units"; 1907.06437)                | yes  | Modern work assumes the convergence/coefficient bound as standard background, not a result to cite | The estimate is textbook-level; contemporary papers use it without proof |

Protocol pass check: WebSearch ran **5 distinct queries** at specific / general / aliased / idiom / refinement levels (≥3 ✓). ChatGPT MCP recorded n/a with reason (not installed). Local references checked (absent → n/a). nLab checked (404 → n/a, not categorical). Stacks / nCatLab / MathOverflow / arXiv each checked or n/a with reason. **Protocol satisfied.**

### Literature summary (Phase 3)

Concept identified as: **the radius-of-convergence / coefficient-size estimate for the p-adic logarithm** `log(1+y)=∑(−1)^{n+1}yⁿ/n`. The governing fact is the p-adic valuation of the denominators, `v_p(1/n) = −v_p(n)`, with `v_p(n) ≤ log_p(n)`.

Sources agree on the standard form: yes. Universally: `log(1+y)` converges on the open unit ball `{‖y‖<1}` of `ℂ_p` (radius 1), because `‖yⁿ/n‖ = ‖y‖ⁿ p^{v_p(n)} → 0`; the exp sibling converges on the smaller ball of valuative radius `1/(p−1)` via Legendre's `v_p(n!)` formula, and exp/log are mutually inverse isometries on matched balls (Washington §5.1; Cassels §12; Koblitz; Conrad).

Most general standard form: the convergence/coefficient statement is made for `ℂ_p` (or any complete nonarchimedean extension of `ℚ_p`), with the *function* `log` defined on `1 + 𝔪`. The underlying coefficient bound is an arithmetic statement about `v_p(n)` and is field-independent (it is about the rationals `1/n`).

Generality dimensions where the literature varies:
- **The estimate's exact constant.** Literature most often quotes `v_p(n) ≤ ⌊log_p n⌋` (sharp, "logarithmic"). The Lean lemma uses the *weaker linear* bound `(p−1)·v_p(n) ≤ n−1` (equivalently `v_p(n) ≤ (n−1)/(p−1)`). The linear form is what is needed to match the `p^{n−1}` RHS and to align the log series term-by-term with the exp series in this development's inversion proof. Both are standard; they serve different purposes (the linear bound is exactly the exp/log-matching bound).
- **What is bounded.** Literature bounds `‖yⁿ/n‖` (the whole term) to conclude convergence; the Lean lemma isolates the *coefficient* `‖1/n‖` raised to `p−1`. The coefficient form is a bookkeeping refactor of the same content for use inside `summable_prod_family` / `master_bridge`.

Disagreement with the literature: none. The Lean form is a correct, standard (if deliberately non-sharp) special case of the textbook estimate, transported to the integer-exponent `^(p−1)` encoding to stay `rpow`-free.

---

### Generality analysis — `PadicLFunctions.norm_coeff_log_le`

Literature-standard form (from Phase 3): the p-adic log converges on the open unit ball of any complete nonarchimedean extension of `ℚ_p`; the coefficient `1/n` has valuation `−v_p(n)` with `v_p(n) ≤ log_p n` (sharp) or `≤ (n−1)/(p−1)` (linear, exp-matching).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | coefficient ring fixed to `ℚ_[p]` | `coeff n (PowerSeries.log ℚ_[p]) : ℚ_[p]`, norm = the `ℚ_[p]` norm | the estimate is about `1/n ∈ ℚ ⊂ ℚ_p` and holds over any nonarch. extension `K/ℚ_p` | partially | The *content* is `v_p(1/n)` in `ℚ`, so the statement could be phrased over `PadicVal`/`padicValRat` independent of `ℚ_[p]`. But as written it bounds the *norm in `ℚ_[p]`*, which is the form the convergence proof consumes. Generalising the coefficient field (to `K/ℚ_p`) is plausible but not what the literature singles out as "the" form. |
| 2 | exponent `(p−1)` (the rpow-free trick) | integer power `^(p−1)` to avoid real `rpow` | textbook writes `v_p(coeff) ≥ −(n−1)/(p−1)` directly with rational/real valuations | n/a | The `^(p−1)` is a deliberate mathlib-idiom choice (stay in ℤ-exponent `zpow`/`pow`, dodge `Real.rpow`), not a generality axis. It is a *narrowing of presentation*, not of mathematics. |
| 3 | RHS constant `p^(n−1)` (linear, non-sharp) | `(p:ℝ)^(n−1)` | sharp form gives `p^{log_p n}=n`; linear form gives `p^{(n−1)/(p−1)}` | yes (sharper exists) | The *sharp* bound `‖1/n‖ ≤ n` is stronger. But the linear `p^(n−1)`-after-`^(p−1)` shape is **deliberately matched to `norm_coeff_exp_le`** so the two series can be compared termwise in `master_bridge`. Sharpening would *break* that matching. So "weaker constant" here is a feature, not a defect. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** along axis 1 (fixed to `ℚ_[p]` rather than a general complete nonarchimedean `ℚ_p`-extension `K`), and uses a deliberately non-sharp constant (axis 3) chosen to match the exp sibling.
Number of weakening opportunities found: 1 substantive (coefficient field `ℚ_[p] → K/ℚ_p`); the other two axes are presentation choices, not generality.
Proposed restatement (if STRICTLY NARROWER): one *could* state, for any complete nonarchimedean field `K` that is a `ℚ_[p]`-algebra,
`‖(algebraMap ℚ_[p] K) (coeff n (PowerSeries.log ℚ_[p]))‖ ^ (p−1) ≤ (p:ℝ)^(n−1)`.
But this is almost certainly *not* the right mathlib target: mathlib has no analytic p-adic log at all, so the "right form" question is dominated by the larger missing object, not by this lemma's field parameter.
Cost of restatement: CHEAP–MODERATE (norm is multiplicative under `algebraMap` for an isometric embedding; the valuation content is unchanged). **Cost does not drive the verdict.**

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses? | no | Already fully typeclassed (`Fact p.Prime`); no bundled hypotheses to convert | — |
|  2 | sequences/metric → filters/topological? | no | A pointwise coefficient inequality; no limit/net to filter-ise | — |
|  3 | construct an object → universal-property class? | no | It is an inequality, not a construction | — |
|  4 | set-with-closure-predicate → bundled substructure? | no | No substructure involved | — |
|  5 | vector-space/metric/field-specific → weaken typeclass? | **partially** | The valuation content lives in `padicValRat`/`PadicVal`; the norm-in-`ℚ_[p]` wrapper could be stated for a general nonarch. extension (see 4b axis 1) | A `K/ℚ_p`-level statement would compose with a (currently nonexistent) general p-adic-analysis API |
|  6 | 1-categorical → higher-categorical? | no | Not categorical | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | `n : ℕ` is intrinsic (it indexes the power series and appears as the denominator); not a generalisable index | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (no real organisational improvement). The only candidate (row 5 / 4b axis 1) — restating over a general nonarchimedean extension `K/ℚ_p` — is a plain field-generalisation, not a Bourbaki-2.0 reorganisation, and it cannot be honestly justified by "downstream mathlib API it unlocks" because **mathlib has no p-adic analytic log/exp API for it to compose with**. The real organisational question is the *parent* object (`padicExp` / `padicLog`), not this coefficient lemma. One-line reason: this is an elementary `ℚ_[p]`-coefficient valuation estimate; there is no contemporary idiom that makes it materially better-organised in isolation.

---

### Diamond / defeq risk — `PadicLFunctions.norm_coeff_log_le`

n/a — declaration kind is `theorem`. (No definitional equalities or typeclass-search paths introduced.)

### Risk verdict (Phase 4.5)

Overall risk: n/a (theorem).

---

### Mathlib search-status: `PadicLFunctions.norm_coeff_log_le`

[A] Lean-Finder       n/a — MCP/tool not installed in this environment (no `lean_finder` tool surfaced by ToolSearch)
[B] Loogle            n/a — MCP/tool not installed (no `loogle` tool surfaced by ToolSearch)
[C] LeanSearch        n/a — MCP/tool not installed (no `lean_search` tool surfaced by ToolSearch)
[D] Grep mathlib src  Queried `norm.*coeff.*log` / `‖.*log.*‖` / `coeff_log.*‖` / `norm_coeff` over `Mathlib/RingTheory/PowerSeries/` and `Mathlib/` — **no hits** for any norm/valuation bound on `PowerSeries.log` (or `exp`) coefficients. Also queried `def padicLog` / `def padicExp` / `noncomputable def …log…Padic` over all of `Mathlib/` — **no hits**: mathlib has **no analytic p-adic logarithm or exponential** at all.
[E] Name pattern      Queried `theorem (norm_coeff|coeff_log_|.*log_le|padic.*log)` over `Mathlib/`. Hits are all unrelated: `Real.log` inequalities (`log_le_log_iff`, `log_le_sub_one_of_pos`), `MahlerMeasure.norm_coeff_le_choose_mul_*` (complex polynomial coeffs), `padicValNat_factorial`/`padicValNat_choose`/`padicValNat_le_nat_log` (the *valuation building blocks*, not the log-coefficient bound), `padicValRat_two_harmonic`. None states a norm bound on `PowerSeries.log`'s `ℚ_[p]` coefficients.

Searched for both:
  - the user's current form (`‖coeff n (PowerSeries.log ℚ_[p])‖^(p−1) ≤ p^(n−1)`) — not present.
  - the literature-standard form (radius-1 convergence of p-adic log; `v_p(n) ≤ log_p n`; analytic `padicLog`) — mathlib has the **valuation building blocks** (`padicValNat_le_nat_log`, `pow_padicValNat_dvd`, `Padic.norm_eq_zpow_neg_valuation`, `Padic.valuation_natCast`) and the **formal** `PowerSeries.log`/`PowerSeries.exp`, but **not** the coefficient-norm bound and **not** any analytic p-adic log/exp.

Concluded: **not in mathlib** (grep + name-pattern exhausted, plus the literature-standard analytic object is also absent). The dedicated Lean search engines (Loogle / LeanSearch / Lean-Finder) were unavailable in this environment; the two source-level methods (D, E) were run thoroughly and are decisive for a `ℚ_[p]`-specific statement of this kind.

---

### Call sites — `PadicLFunctions.norm_coeff_log_le`

Internal use count: **K = 2**  (within `PadicLFunctions`, excluding the declaring line)
External-to-file callers: 0 distinct files (both uses are in the same file, `PadicExp.lean`)

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| PadicExp.lean:944 | `summable_prod_family p (exp ℚ_[p]) (PowerSeries.log ℚ_[p]) (x-1) hx (norm_coeff_exp_le p) (norm_coeff_log_le p) constantCoeff_log` — convergence input for `padicExp_padicLog` |
| PadicExp.lean:968 | `summable_prod_family p (PowerSeries.log ℚ_[p]) (exp ℚ_[p] - 1) x hx (norm_coeff_log_le p) hGc hG0` — convergence input for `padicLog_padicExp` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `norm_coeff_log_le`?): **(none)** — the coefficient bound is only ever obtained through this lemma; its exp-sibling `norm_coeff_exp_le` is used the same way alongside it.

What this tells us: K = 2 internal uses, no inline re-derivation → it is **real API** for *this development's* convergence/inversion proofs (the `summable_prod_family` → `master_bridge` route that proves `exp∘log = id` and `log∘exp = id`). It is a genuine, used helper — but a *project-internal* one, tightly coupled to a parent object (`padicExp`/`padicLog`) that mathlib does not have. Not a 0-use wrapper; not an externally-consumed public API either.

---

### Composition check (Phase 6)

Can `norm_coeff_log_le` be derived from mathlib in ≤3 chained calls?

Attempt 1: `rw [coeff_log, …norm lemmas…]; exact <mathlib valuation lemma>`
  - Mathlib decls used: `PowerSeries.coeff_log`, `Padic.norm_eq_zpow_neg_valuation`, `Padic.valuation_natCast`, then a bound on `padicValNat p n`.
  - Result: **fails** as a clean ≤3-call composition.
  - Notes: After reducing to `(p−1)·v_p(n) ≤ n−1`, the *only* directly-applicable mathlib bound is `padicValNat_le_nat_log : v_p(n) ≤ log_p n`. That gives `(p−1)·v_p(n) ≤ (p−1)·log_p n`, which is **not** `≤ n−1` for small `n` (e.g. `p=2, n=2`: `(p−1)·log_p n = 1·1 = 1 = n−1` ok, but the inequality `(p−1)log_p n ≤ n−1` is false in general, e.g. it fails as `n` grows only slowly relative to `log`… and more to the point the chain `v_p(n) ≤ log_p n ⟹ (p−1)v_p(n) ≤ n−1` is simply not valid). The needed estimate `(p−1)·v_p(n) ≤ n−1` is the project lemma `sub_one_mul_padicValNat_succ_le`, which mathlib does **not** have; it is proved from Bernoulli's inequality `one_add_mul_le_pow` together with `pow_padicValNat_dvd` — i.e. a real (short but non-mechanical) argument, not a 1–3-call glue.

Attempt 2 (different angle): use `padicValRat` directly on `1/n`.
  - Mathlib decls used: `padicValRat`, `padicValRat.neg`, etc.
  - Result: **partial/fails** — still bottoms out at the same missing inequality `(p−1)·v_p(n) ≤ n−1`. Changing the valuation API does not supply the arithmetic content.

Conclusion: **NOT-COMPOSABLE**. The surface proof of `norm_coeff_log_le` is 3 lines, but it delegates the entire mathematical content to `norm_natCast_inv_pow_le` ⟶ `sub_one_mul_padicValNat_succ_le`, an inequality mathlib lacks. So this is not a "1–3 mathlib-call composition" in the Phase-6 sense; a NO-composable verdict would be wrong.

---

## Verdict: `PadicLFunctions.norm_coeff_log_le`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the concept (radius-1 convergence of the p-adic log; coefficient bound via `v_p(n)`) is fully standard (Washington §5.1, Cassels §12, Koblitz, Conrad). The *sharp* literature bound is `v_p(n) ≤ log_p n`; the Lean lemma uses the deliberately weaker linear bound `(p−1)·v_p(n) ≤ n−1`, chosen to match `norm_coeff_exp_le` termwise.
- Generality analysis (Phase 4): **STRICTLY NARROWER** on one real axis (coefficient field fixed to `ℚ_[p]`; could be a general `K/ℚ_p`), with two presentation choices (`^(p−1)` rpow-free encoding; non-sharp `p^(n−1)` constant) that are intentional and *should not* be "fixed". Phase 4c found **no** honest modern-idiom improvement (the only candidate cannot cite downstream API because mathlib has no p-adic analytic log/exp).
- Mathlib search (Phase 5): **not in mathlib** under either form; mathlib has the valuation *building blocks* and the *formal* `PowerSeries.log`, but no coefficient-norm bound and **no analytic p-adic log/exp at all**.
- Composition check (Phase 6): **NOT-COMPOSABLE** — the content reduces to an inequality (`(p−1)·v_p(n) ≤ n−1`) that mathlib lacks; mathlib's `padicValNat_le_nat_log` does not give it.

**Rationale.**
Three findings pull in different directions, and reconciling them is a judgment call about *mathlib taste and packaging* rather than something the evidence settles. (1) The result is mathematically standard and genuinely *used* (K=2, feeding the `exp∘log`/`log∘exp` inversions), and it is **not** in mathlib nor a cheap mathlib composition — those facts push *away* from both NO buckets. (2) But it is a **specialised, project-internal coefficient lemma whose natural home is an analytic p-adic logarithm that mathlib does not yet have**: in isolation it is an oddly-specific statement (`‖[Xⁿ]log‖^(p−1) ≤ p^(n−1)` over `ℚ_[p]`), with a deliberately non-sharp constant tuned to this development's series-matching trick. Whether mathlib wants *this* lemma is essentially the question "does mathlib want the p-adic exp/log package this lemma belongs to, and in what form?" — a packaging/taste decision. (3) Phase 4 found a real generality narrowing (field `ℚ_[p]` vs `K/ℚ_p`), which would normally suggest `YES-but-generalise-first`; but the right generalisation target is unclear precisely because the parent object is absent, and per the verdicts reference an empty/structural literature signal of "this is a sub-lemma of a larger missing object" is a BORDERLINE indicator, not an automatic YES. The honest call is to surface the packaging question to a human rather than silently pick `YES-but-generalise-first` (wrong target) or `YES-add-as-is` (Phase 4b was STRICTLY NARROWER, which the gate forbids for `YES-add-as-is`).

**Refactor-actionable bar — BORDERLINE-needs-human.**

Numbered questions (≤5):

  1. **Scope/packaging.** Do you intend to upstream the *whole* p-adic exp/log package (`padicExp`, `padicLog`, the convergence + inversion theorems) to mathlib? If yes, this lemma should travel **with** that package (as supporting API for the radius-of-convergence estimate), not as a standalone PR — and its form would be fixed by the package's needs. If no (project-internal only), it stays project-local and needs no further mathlib work.

  2. **Sharp vs. matched constant.** For a mathlib contribution, would you prefer the **sharp** coefficient bound `‖[Xⁿ]log‖ ≤ n` (equivalently `v_p(n) ≤ log_p n`, which mathlib *almost* has via `padicValNat_le_nat_log`) as the public lemma, with the deliberately weaker `^(p−1) ≤ p^(n−1)` matched form derived locally only where the exp/log termwise comparison needs it? Mathlib would likely want the sharp statement as the canonical fact.

  3. **Coefficient-field generality.** Should the bound be stated over a general complete nonarchimedean `ℚ_[p]`-algebra field `K` (Phase 4b axis 1), rather than fixed to `ℚ_[p]`? This is a CHEAP–MODERATE generalisation, but only worth doing if the parent analytic-log object is itself stated over `K` (which the project's `padicExp`/`padicLog` already are — so the field-general form may in fact be the natural one for the package).

  4. **Reusable valuation lemma split.** The mathematical content is the inequality `(p−1)·v_p(n) ≤ n−1` (`sub_one_mul_padicValNat_succ_le`) — a clean, field-free `padicValNat` fact. Independent of the log lemma, is *that* inequality a worthwhile standalone mathlib contribution to `Mathlib/NumberTheory/Padics/PadicVal/`? (It is arguably more mathlib-shaped than the coefficient wrapper, and it composes with the exp side too.)

Next action: user answers these; re-run `/mathlibable PadicLFunctions.norm_coeff_log_le` to resolve. Likely outcomes:
  - "Upstreaming the whole exp/log package, sharp form preferred, over `K`" → re-run flips toward **`YES-but-generalise-first`**, target = the sharp, `K`-general coefficient bound shipped as supporting API alongside `padicExp`/`padicLog`; and additionally split out `sub_one_mul_padicValNat_succ_le` as its own `PadicVal` lemma (likely `YES-add-as-is`).
  - "Project-internal only" → drop `norm_coeff_log_le` from mathlib consideration; keep as-is in the project (the matched non-sharp constant is correct for the local proof).

---

## Next step

User answers the four numbered questions above; re-run `/mathlibable PadicLFunctions.norm_coeff_log_le` to resolve the verdict (or commit to a verdict directly). The pivotal question is Q1 — whether the parent p-adic exp/log package is mathlib-bound — because this lemma's fate (and its correct form) is determined by that package, not by the lemma in isolation. Strongly consider Q4 independently: the underlying valuation inequality `(p−1)·v_p(n) ≤ n−1` is a clean, field-free `padicValNat` fact that is a more obviously mathlib-shaped contribution than the `ℚ_[p]`-coefficient wrapper.

---

*Search-tooling note for this run:* `lake build` was not re-run (stale/slow per task instruction); the declaration and its full dependency chain were read directly from source. The ChatGPT MCP and the dedicated Lean search engines (Loogle / LeanSearch / Lean-Finder) were not installed in this environment and are recorded `n/a`; the literature protocol was satisfied with 5 WebSearch queries at distinct generality levels plus direct source fetches, and the mathlib search was done thoroughly via source-level grep (method D) + name-pattern (method E), which are decisive for a `ℚ_[p]`-specific coefficient bound with no analytic-log machinery present in mathlib.
