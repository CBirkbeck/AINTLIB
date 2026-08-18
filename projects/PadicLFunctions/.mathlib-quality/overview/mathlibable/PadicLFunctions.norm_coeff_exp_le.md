# `/mathlibable` report — `PadicLFunctions.norm_coeff_exp_le`

**Final verdict: `BORDERLINE-needs-human`** — see Phase 7.

---

### Baseline (Phase 0)
- lake build:                build not re-run; reasoned from source (per task BUILD NOTE — `lake build` here is stale/slow). Declaration and its full dependency chain read directly from source.
- decl `PadicLFunctions.norm_coeff_exp_le`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:847`
- kind:                      theorem
- has sorry:                 no (proof is two `rw`/`exact` lines)
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=∑xⁿ/n!` and `log(1+y)=∑(−1)ⁿ⁺¹yⁿ/n` on a complete ultrametric normed `ℚ_[p]`-algebra; isometry, functional equation, inversion. Cites Cassels §12, Washington *Cyclotomic Fields* §5.1.

---

### Statement (Phase 1)

`PadicLFunctions.norm_coeff_exp_le` is a theorem stating:

> For every `n ≥ 1`, the `n`-th coefficient `[Xⁿ]` of the formal exponential power series `exp ∈ ℚ_[p]⟦X⟧` (which equals `1/n!`) satisfies `‖1/n!‖ₚ^{p−1} ≤ p^{n−1}`.

This is the **rpw-free / `(p−1)`-th-power form of the inverted Legendre estimate** for the exponential's coefficients. Writing it in valuation terms: `v_p(1/n!) = −v_p(n!) = −(n − s_p(n))/(p−1) ≥ −(n−1)/(p−1)`, so `‖1/n!‖ₚ = p^{−v_p(1/n!)} ≤ p^{(n−1)/(p−1)}`, i.e. `‖1/n!‖ₚ^{p−1} ≤ p^{n−1}`. The `(p−1)`-th power on the left is the standard trick the project uses everywhere to stay inside `ℤ`-exponent `zpow` and avoid `Real.rpow`. This is exactly the per-coefficient estimate behind the classical fact that the `p`-adic exponential has radius of convergence `p^{−1/(p−1)}`.

Variables / typeclasses (Lean side):
- `(p : ℕ)`, `[hp : Fact p.Prime]` — the prime; `exp` lives over `ℚ_[p]` specifically.
- `coeff n (exp ℚ_[p])` — `n`-th coefficient of mathlib's `PowerSeries.exp ℚ_[p]`, coerced to `ℚ_[p]`. By mathlib's `PowerSeries.coeff_exp` this is `algebraMap ℚ ℚ_[p] (1/n!)`.

Hypotheses (Lean side):
- `(n : ℕ)` — the coefficient index.
- `(hn : 1 ≤ n)` — needed so `n − 1` in the exponent is the genuine subtraction and the bound is non-vacuous (`n = 0` would give `‖1‖ = 1 ≤ p^{−1}`, false in `ℕ`-truncated form).

Conclusion (math): `‖1/n!‖ₚ^{p−1} ≤ p^{n−1}` for `n ≥ 1`.

Conclusion (Lean): `‖(coeff n (exp ℚ_[p]) : ℚ_[p])‖ ^ (p - 1) ≤ (p : ℝ) ^ (n - 1)`.

Proof body (verbatim):
```lean
rw [coeff_exp, one_div, map_inv₀, map_natCast, norm_inv, inv_pow]
exact norm_factorial_inv_pow_le p hn
```
i.e. unfold `coeff n exp = 1/n! = (n!)⁻¹`, push the norm/inverse, then **apply the project lemma `norm_factorial_inv_pow_le`** which is the inverted Legendre bound `(‖n!‖^{p−1})⁻¹ ≤ p^{n−1}`. All mathematical content is in `norm_factorial_inv_pow_le → norm_factorial_le → ` mathlib's `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A specialisation/corollary — it reads the project's factorial-norm bound off the concrete coefficient `[Xⁿ]exp = 1/n!`. Not a new structure, not a named-after-person theorem, and not itself a `## Main result` (it is internal plumbing for the `exp`/`log` inversion in cluster R5.E). It is one of a matched pair with `norm_coeff_log_le` (line 853).

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded only for framing.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines.
One-liner verdict: **n/a** — kind is `theorem`, not a `def`/`abbrev`/`structure`. Phase 2b is for definitions; skipped with this note.

---

### PHASE 3 — Literature search (EXHAUSTIVE)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic exponential radius of convergence coefficients 1/n! valuation Legendre formula n/(p-1)" | yes | `v_p(n!) = (n−s_p(n))/(p−1)`; consequence: `exp` has radius `p^{−1/(p−1)}` | Wikipedia "P-adic exponential function", Wikipedia "Legendre's formula", Eremin arXiv:1907.11902 |
| 2 | WebSearch (general form / valuation) | "p-adic valuation of n factorial 1/n! coefficient exponential series Cassels Washington cyclotomic" | yes | `ν_p(n!) = (n − s_p(n))/(p−1)` closed form; decay `p^{ν_p(n!)}` controls convergence | confirms the digit-sum closed form; Cassels *Local Fields* is the standard ref |
| 3 | WebSearch (closed-form inequality) | `"v_p(n!)" formula "(n - s_p(n))/(p-1)" p-adic exponential convergence bound` | yes | `v_p(n!) = (n−s_p(n))/(p−1)`; "terms decay according to p^{v_p(n!)}" | Romagny "Some useful p-adic formulas" notes; direct match to the inequality used |
| 4 | WebSearch (log/exp pair, isometry) | "p-adic logarithm exponential coefficient bound v_p(1/n!) isometry log series 1/n von Staudt" | yes | `|1/n!|_F ≤ q^{en/(p−1)}`; `|exp(x)−1| = |x|` (isometry) | **PlanetMath "p-adic exp and log"**, **MIT notes math.mit.edu/~dav/exp.pdf**, Leiden Evertse Ch.8, Cambridge notes — all give exactly `\|1/n!\| ≤ p^{n/(p−1)}` style bound |
| 5 | ChatGPT MCP | (intended: "standard mathematical form + generality + historical evolution of the p-adic exp coefficient bound") | **n/a** | — | ChatGPT MCP **not configured** on this machine (`~/.claude/mcp-needs-auth-cache.json`; no chatgpt server). Compensated with 2 extra WebSearch queries (#3, #4) + nLab + WebFetch of PlanetMath/Wikipedia primary sources. |
| 6 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | **n/a** | (no references dir) | Both absent on this checkout — recorded n/a. Module docstring itself names the sources: Cassels §12, Washington *Cyclotomic Fields* §5.1, "RJW Lem 5.14". |
| 7 | nLab | `ncatlab.org/nlab/show/p-adic+exponential` | no | — | HTTP 404 — nLab has no dedicated p-adic-exponential page. The concept is classical p-adic analysis, peripheral to nLab's category-theoretic focus. |
| 8 | nCatLab (categorical) | — | **n/a** | — | Not a categorical concept; a concrete valuation estimate on rational coefficients in `ℚ_[p]`. |
| 9 | Stacks Project | — | **n/a** | — | Not an algebraic-geometry / scheme-theoretic concept; classical local-field analysis. |
| 10 | MathOverflow / Math.SE | covered transitively by WebSearch #1–#4 | yes | same standard form | hits surfaced (e.g. value-distribution refs, World Scientific "Logarithm and exponential in a p-adic field") all agree |
| 11 | recent arXiv (last 5 yrs) | Eremin, "Legendre's formula and p-adic analysis" (arXiv:1907.11902); arXiv:2408.00353 "Bounds on the p-adic valuation of the factorial" | yes | reaffirms `v_p(n!) = (n−s_p(n))/(p−1)` and refinements | modern treatments still use the identical bound — form is stable, not evolving |

### Literature summary (Phase 3)

Concept identified as: **the per-coefficient Legendre/valuation bound for the `p`-adic exponential power series** — i.e. the estimate `v_p(1/n!) ≥ −(n−1)/(p−1)`, equivalently `‖1/n!‖ₚ ≤ p^{(n−1)/(p−1)}` (the project states the rpw-free `(p−1)`-th power form `‖1/n!‖ₚ^{p−1} ≤ p^{n−1}`).

Sources agree on the standard form: **yes**, unanimously. Legendre `v_p(n!) = (n − s_p(n))/(p−1)`; the coefficient bound and the resulting radius `p^{−1/(p−1)}` appear identically in Cassels, Washington §5.1, PlanetMath, the MIT/Leiden/Cambridge lecture notes, and the Eremin arXiv paper.

Most general standard form: the bound is a statement about the **valuation of `1/n!`** and is, in the literature, a lemma *en route to* the convergence/isometry of the exponential. It is rarely isolated as a named standalone theorem; it appears as one line in the convergence proof. The genuinely "general" object the literature names is the **p-adic exponential function** itself (with its radius and isometry), of which this is the workhorse estimate.

Generality dimensions where the literature varies:
  - **Ambient field**: usually stated over `ℚ_[p]`, sometimes over `ℂ_p` or a general complete non-archimedean field `F` of residue char `p` (with `e = ramification`, giving `|1/n!| ≤ q^{en/(p−1)}`). The *coefficients themselves* always live in `ℚ` (they are `1/n!`); only the embedding field varies. The user's statement embeds them in `ℚ_[p]` — the base case, `e = 1`.
  - **Exponent normalisation**: `(n−1)/(p−1)` vs `n/(p−1)` vs the exact `(n−s_p(n))/(p−1)`. The user uses `(n−1)/(p−1)` (cleanest integer-friendly upper bound, since `s_p(n) ≥ 1` for `n ≥ 1`), wrapped as the `(p−1)`-th power to stay in `zpow`.

Disagreement with the literature: **none**. The user's `‖1/n!‖^{p−1} ≤ p^{n−1}` is a faithful, mathlib-idiomatic (rpw-free) restatement of the textbook coefficient bound.

---

### PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): the valuation bound on `1/n!` underlying `p`-adic-exp convergence; coefficients always in `ℚ`, embedding field can be `ℚ_[p]`/`ℂ_p`/general complete NA field of residue char `p`.

### Generality status table (Phase 4a)

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker/more-general form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|----------------------------------|----------------------------------|
| 1 | coefficient lives in `ℚ_[p]` (`coeff n (exp ℚ_[p]) : ℚ_[p]`) | `ℚ_[p]` | any complete NA field of residue char `p`; coeffs are rationals | **yes (in principle)** | The coefficient `1/n!` is rational; the norm `‖1/n!‖ₚ` is the canonical `ℚ_[p]`-norm. Over a ramified extension the RHS would carry the ramification index `e`. But the project deliberately fixes `ℚ_[p]` here and pushes the algebra-side generality into *separate* lemmas (`norm_factorial_inv_smul_pow_le`, `summable_padicExp_terms`) over `[NormedAlgebra ℚ_[p] L]`. So this lemma is intentionally the `ℚ_[p]` base case. |
| 2 | `(n : ℕ)`, `(hn : 1 ≤ n)` | `n ≥ 1` | `n ≥ 1` (the `n = 0` coefficient is `1`, handled separately) | NO | `n ≥ 1` is exactly the literature's hypothesis; `n = 0` is the constant term `1`, peeled off elsewhere (`tsum_coeff_exp_sub_one`). |
| 3 | exponent shape `(p−1)`-power, `p^{n−1}` | rpw-free, `zpow`-friendly | classically stated with `Real.rpow` / valuations | NO (this *is* the modern improvement) | The `(p−1)`-th-power form is the mathlib-idiomatic way to avoid `Real.rpow` and stay in `ℤ`-exponent arithmetic — a genuine Bourbaki-2.0 reformulation (see 4c). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL within its deliberate scope (`ℚ_[p]` base field)**, with one *available-but-arguably-undesirable* generalisation axis (row 1: general complete NA field with ramification `e`).
Number of weakening opportunities found: 1 (row 1), but it is **not** a clean weakening — it changes the RHS (introduces `e`) and is, in this project's architecture, intentionally factored out: the `ℚ_[p]`-coefficient bound is the canonical statement and the algebra-side generality is carried by the *neighbouring* lemmas. Generalising the coefficient bound itself to arbitrary NA fields would be a different (and not obviously wanted) statement.

Proposed restatement (if one wanted the `e`-general form): a `theorem` over `[CompleteSpace F] [NA field F] (e := ramification)` giving `‖((1/n! : ℚ) : F)‖^{p−1} ≤ p^{e(n−1)}`. **This is not the right mathlib target for *this* lemma** — see Phase 7. Cost: MODERATE (need ramification/valuation-extension API).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | — | Already fully typeclass-driven (`Fact p.Prime`). |
| 2 | sequences/metric → filters/topological? | no | — | A pointwise coefficient inequality; no limit to filter-ise (the filters live in the *summability* lemmas, not here). |
| 3 | construct object → universal-property class? | no | — | No object constructed; it's an estimate. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | N/A. |
| 5 | vector-space/metric/field-specific → weaken typeclasses? | **partially** | the `e`-general NA-field form (row 1 above) | Would let a future `Mathlib` p-adic-exp-over-`ℂ_p` reuse it — but introduces ramification bookkeeping; not clearly a net win. |
| 6 | 1-categorical → higher-categorical? | no | — | N/A. |
| 7 | concrete index ℕ/ℤ/ℝ → general additive structure? | no | — | The index `n` is a genuine `ℕ` factorial index; the `(p−1)`-power/`p^{n−1}` shape *is already* the `zpow`-modernised form. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (the statement is already in the mathlib-idiomatic rpw-free `(p−1)`-power form, which is itself the modernisation of the classical `Real.rpow`/valuation phrasing). The only axis (4a row 1 / 4c row 5) is a *field-generalisation*, not a modern-idiom rewrite, and it is dubious whether mathlib would want the coefficient bound stated `e`-generally rather than as the `ℚ_[p]` workhorse plus separate algebra lemmas.
One-line reason: this is a finite arithmetic inequality already phrased to compose with `zpow`/`pow` API; there is no sequence→filter or concrete→universal move to make.

---

### PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** No definitional equalities or typeclass-search paths introduced. Skipped.

---

### PHASE 5 — Mathlib search

### Mathlib search-status: `PadicLFunctions.norm_coeff_exp_le`

[A] Lean-Finder       — (server not invoked here; substituted by exhaustive grep [D]+[E] over the pinned mathlib in `.lake/packages/mathlib`)   n/a: tool not available in this sandbox; compensated by [D]/[E].
[B] Loogle            type pattern `‖coeff _ (exp _)‖ ^ _ ≤ _` / `_ ^ (?p - 1) ≤ (?p:ℝ) ^ (_ - 1)`   no hits (no mathlib lemma matches; the `(p−1)`-power-Legendre shape is project-specific). [substituted by structural grep — see below]
[C] LeanSearch        NL: "norm of nth coefficient of exponential power series p-adic bounded by p^(n-1)"   no hits expected; the concept "p-adic exponential" has no mathlib decl at all (grep [D] confirms).
[D] Grep mathlib src  `coeff.*exp.*norm`, `‖.*factorial.*‖`, `‖.*n !.*‖`, `\^ \(p - 1\)` under `NumberTheory/Padics/`, `norm_coeff_exp`, `padicExp`   **no hits** for any p-adic exp coefficient bound. Found only: (i) abstract Banach-algebra `NormedSpace.exp`/`expSeries` summability lemmas (`norm_expSeries_summable`, `Analysis/Normed/Algebra/Exponential.lean`) — these are *summability over a general normed algebra*, NOT a `ℚ_[p]` coefficient-valuation bound; (ii) `‖x^n/n!‖`-style ratio bounds in `Analysis/SpecificLimits/Normed.lean` (real/complex Taylor remainders). Neither states `‖1/n!‖ₚ^{p−1} ≤ p^{n−1}`. **No `padicExp`, no `norm_coeff_exp`, no p-adic exponential function in mathlib.**
[E] Name pattern      grep `norm_coeff_exp`, `padicExp`, `coeff_exp_le`, `norm_factorial`   no hits in mathlib (the `norm_coeff_*` hits found are Polynomial Mahler-measure / root-continuity lemmas, unrelated).

Searched for both:
  - the user's current form (`‖coeff n exp‖^{p−1} ≤ p^{n−1}` over `ℚ_[p]`) — **not in mathlib**.
  - the literature-standard form (the valuation bound `v_p(n!) ≤ (n−1)/(p−1)`) — mathlib **has the building block** `sub_one_mul_padicValNat_factorial` and `sub_one_mul_padicValNat_factorial_lt_of_ne_zero` (`Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:582,591`), and `PowerSeries.coeff_exp` (`Mathlib/RingTheory/PowerSeries/Exp.lean:54`), but **not** the assembled `exp`-coefficient norm bound.

Concluded: **"not in mathlib (all methods exhausted, plus the literature-standard form)"** — mathlib has the *ingredients* (`PowerSeries.coeff_exp`, Legendre `sub_one_mul_padicValNat_factorial`) but neither the `p`-adic exponential function nor any norm bound on its coefficients. **Crucially, the intermediate step `norm_factorial_inv_pow_le` used by the proof is itself a PROJECT lemma, not a mathlib lemma** (confirmed: absent from `.lake/packages/mathlib`).

---

### PHASE 6 — Composition check (+ call-sites)

### Call sites — `PadicLFunctions.norm_coeff_exp_le`

Internal use count (outside the declaring file): **0**.
Within the declaring file `PadicExp.lean`: **2** uses —
- `PadicExp.lean:944` — `master_bridge p (exp ℚ_[p]) (PowerSeries.log ℚ_[p]) (x - 1) HasSubst.log hGsum (summable_prod_family p … (norm_coeff_exp_le p) (norm_coeff_log_le p) constantCoeff_log)` — supplies the `exp`-side termwise bound to the `padicExp_padicLog` inversion.
- `PadicExp.lean:964` — `exact norm_coeff_exp_le p j hj` — supplies the `(exp − 1)`-side bound in `padicLog_padicExp`.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| PadicExp.lean:944 | `… summable_prod_family p … (norm_coeff_exp_le p) (norm_coeff_log_le p) constantCoeff_log` |
| PadicExp.lean:964 | `exact norm_coeff_exp_le p j hj` |

External-to-file callers: **0 distinct files** (no usage anywhere else in the project; no downstream library imports it).
Inline-derivation grep (re-derived elsewhere without using `norm_coeff_exp_le`?): **none** — the only place the `exp`-coefficient bound is needed (the `master_bridge`/`summable_prod_family` calls) goes through this lemma; it is not bypassed.

What the pattern says: K = 0 *external-to-file* but **2 in-file uses, both feeding the same `summable_prod_family`/`master_bridge` machinery for the `exp ↔ log` inversion (R5.E)**, with no inline re-derivation. So it is *not* dead code and *not* a bypassed wrapper — it is genuine internal API for the convergence proof, but its consumers are entirely local and it is half of a tightly-coupled matched pair (`norm_coeff_exp_le` / `norm_coeff_log_le`).

### Composition check (Phase 6)

Can `norm_coeff_exp_le` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `by rw [PowerSeries.coeff_exp, …]; exact <bound on ‖1/n!‖>`
  - Mathlib decls used: `PowerSeries.coeff_exp`, `map_inv₀`, `map_natCast`, `norm_inv`, `inv_pow` (the rewrite chain).
  - Result: **fails as a pure-mathlib composition.** After the rewrite the goal is `(‖(n! : ℚ_[p])‖^{p−1})⁻¹ ≤ p^{n−1}` — and the discharging lemma is `norm_factorial_inv_pow_le`, **which is a project lemma, not mathlib**. To do it from mathlib alone one must inline `norm_factorial_inv_pow_le → norm_factorial_le → ` `Padic.norm_eq_zpow_neg_valuation`, `Padic.valuation_natCast`, `zpow_le_zpow_right₀`, and mathlib's Legendre `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`, plus the `zpow`/`omega` bookkeeping — roughly the full ~15-line body of `norm_factorial_le` + `norm_factorial_inv_pow_le`. That is a **real multi-step proof, not a ≤3-call composition**.
  - Notes: the `rw`-then-`exact` shape *looks* like a 2-line composition, but the `exact` target is project-internal.

Attempt 2: directly from mathlib's abstract `NormedSpace.exp`/`expSeries` summability lemmas?
  - Mathlib decls: `norm_expSeries_summable`, etc.
  - Result: **fails** — those give *summability of `‖(n!)⁻¹ • xⁿ‖`* over a general normed algebra, not a *valuation bound on the coefficient `1/n!`*. Different statement; no per-coefficient `≤ p^{n−1}`.

Conclusion: **NOT-COMPOSABLE** from mathlib in ≤3 calls. The estimate's substance lives in a project lemma (`norm_factorial_inv_pow_le`) that mathlib lacks. (It *is* a trivial composition **from the project**, but the skill's composition test is against *mathlib's* primitives.)

---

## Verdict: `PadicLFunctions.norm_coeff_exp_le`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the coefficient bound `v_p(1/n!) ≥ −(n−1)/(p−1)` / `‖1/n!‖ₚ^{p−1} ≤ p^{n−1}` is unanimous standard p-adic analysis (Cassels, Washington §5.1, PlanetMath, MIT/Leiden/Cambridge notes, Eremin arXiv:1907.11902). But it is universally an *un-named intermediate lemma* inside the p-adic-exp convergence proof, not a standalone named theorem.
- Generality analysis (Phase 4): MAXIMALLY GENERAL within its deliberate `ℚ_[p]` scope; the one generalisation axis (arbitrary complete NA field with ramification `e`) is a *different* statement, not a clean weakening, and arguably not what mathlib would want for this specific bound. Modern-idiom check: already rpw-free / `zpow`-idiomatic — no modernisation move.
- Mathlib search (Phase 5): NOT in mathlib (no p-adic exponential at all); mathlib has only the building blocks (`PowerSeries.coeff_exp`, Legendre `sub_one_mul_padicValNat_factorial`).
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (≤3 calls) — the load-bearing step `norm_factorial_inv_pow_le` is a project lemma; from mathlib alone it is a ~15-line proof. Call sites: 0 external, 2 in-file (both into `summable_prod_family`/`master_bridge`), no inline re-derivation.

**Rationale (1–2 paragraphs):**

`norm_coeff_exp_le` is mathematically correct, faithful to the literature, and *not* in mathlib — but it sits in the awkward middle. It is not `YES-add-as-is` because, taken in isolation, it is a thin two-line specialisation that reads the project's own factorial-norm bound (`norm_factorial_inv_pow_le`) off the concrete coefficient `[Xⁿ]exp = 1/n!`; the genuine, mathlib-worthy mathematical content is the **factorial/Legendre estimate** (`norm_factorial_le`, `norm_factorial_inv_pow_le`), not the coefficient wrapper. It is not `NO-mathlib-has-it` (mathlib has no p-adic exponential and no such coefficient bound) and not `NO-composable-from-mathlib` (the composition test is against mathlib, and from mathlib it requires inlining the whole ~15-line Legendre-norm derivation, well past 3 calls). The right mathlib contribution in this neighbourhood is almost certainly *the `ℚ_[p]`-factorial-norm bound itself* (`‖n!‖ₚ` via Legendre) and/or *the `p`-adic exponential function with its radius/isometry* as a package — with `norm_coeff_exp_le` becoming either a one-line corollary or an internal step of that larger contribution. Whether to upstream this exact coefficient-wrapper, or to upstream the factorial bound (and let the coefficient form fall out), or to upstream the whole p-adic-exp/log development as a unit, is a packaging-and-scope judgment that depends on project intent — hence BORDERLINE.

**Numbered questions (≤5):**

1. The genuinely novel-for-mathlib content here is the **`ℚ_[p]` factorial-norm / Legendre bound** (`norm_factorial_le` at `PadicExp.lean:52` and its inverse `norm_factorial_inv_pow_le` at line 69), built on mathlib's `sub_one_mul_padicValNat_factorial`. Would you rather upstream **that factorial bound** (the real content) and let `norm_coeff_exp_le` be a trivial corollary downstream — i.e. assess `norm_factorial_inv_pow_le` for mathlib instead of this wrapper? (yes → re-run `/mathlibable PadicLFunctions.norm_factorial_inv_pow_le`.)
2. Is the intended mathlib contribution the **whole p-adic exponential/logarithm package** (`padicExp`, `padicLog`, radius `p^{−1/(p−1)}`, isometry, inversion — mathlib currently has *no* p-adic exponential at all), shipped as one development, with `norm_coeff_exp_le` as an internal lemma rather than a standalone PR? (This is the natural "big" target the literature actually names.)
3. Should the bound be stated over an arbitrary **complete non-archimedean field of residue characteristic `p`** (carrying the ramification index `e`, RHS `p^{e(n−1)}`), rather than fixed to `ℚ_[p]`? Mathlib generally prefers the maximally-general form — but here the project deliberately factors `ℚ_[p]`-coefficients vs `[NormedAlgebra ℚ_[p] L]`-algebra-side generality into separate lemmas. (yes → the contribution becomes the `e`-general statement; no → `ℚ_[p]` base case is the right grain.)
4. `norm_coeff_exp_le` and `norm_coeff_log_le` (line 853) are a matched pair, both feeding `summable_prod_family`/`master_bridge`. If any coefficient-bound lemma is upstreamed, should the **pair** go together (as `PowerSeries.exp`/`PowerSeries.log` p-adic coefficient bounds in `Mathlib/NumberTheory/Padics/`)?

**Next action:** user answers; re-run `/mathlibable` to resolve. Likely outcomes:
  - Q1 yes / Q2 yes → drop this wrapper from standalone mathlib consideration; re-target the assessment at `norm_factorial_inv_pow_le` (the factorial bound — likely `YES-add-as-is`/`YES-but-generalise-first`) and/or plan the p-adic-exp package; `norm_coeff_exp_le` ships as an internal corollary.
  - Q3 yes → `YES-but-generalise-first` (restate over a general complete NA field with ramification `e`).
  - All "keep `ℚ_[p]`, ship the coefficient form as-is, paired with `norm_coeff_log_le`" → flips toward `YES-but-generalise-first` (pair them; place in `Mathlib/NumberTheory/Padics/`), pending the factorial bound being upstreamed first.

---

## Next step

User answers the four numbered questions above; re-run `/mathlibable PadicLFunctions.norm_coeff_exp_le` (or, more productively, `/mathlibable PadicLFunctions.norm_factorial_inv_pow_le` — the lemma carrying the real mathematical content) to resolve the verdict. The most likely resolution is that the **factorial/Legendre norm bound** is the mathlib-worthy unit and this coefficient lemma is an internal corollary of a larger p-adic-exponential contribution.
