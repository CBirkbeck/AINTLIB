# `/mathlibable` report — `PadicLFunctions.norm_coeff_prod_le`

**Final verdict (five-bucket): `BORDERLINE-needs-human`.**

The lemma is a genuine, correct fragment of standard p-adic analysis (a Legendre/Dwork-type
valuation bound on a single multinomial term of `[Xᵏ](Gⁿ)`), it is **not** in mathlib in any
form, and it is **not** a ≤3-call composition. But it is also (i) an internal helper with exactly
one call site, feeding the exp-convergence machinery rather than being a headline result; (ii)
stated in a hyper-specific rpow-free encoding (`‖[Xʲ]G‖^{p-1} ≤ p^{j-1}`) that is bespoke
bookkeeping for this project; and (iii) fixed to `ℚ_[p]` although the mathematics is general over
any complete nonarchimedean field. Whether to upstream the *generalised* form (likely
`YES-but-generalise-first`) or to keep it project-local is a judgment call the skill cannot make
alone — hence BORDERLINE, with the numbered questions in Phase 7.

---

### Baseline (Phase 0)

- lake build:               **not re-run; reasoned from source** (per task BUILD NOTE — `lake build` is stale/slow in this monorepo; the declaration and every dependency were read directly from source and from the vendored mathlib under `.lake/packages/mathlib/Mathlib/`).
- decl `PadicLFunctions.norm_coeff_prod_le`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:711`
- kind:                      `theorem`
- has sorry:                 no
- module docstring summary:  The p-adic exponential and logarithm (RJW Lem 5.14): `exp = ∑xⁿ/n!` / `log = ∑(−1)ⁿ⁺¹yⁿ/n` convergence + isometry on matched balls via Legendre's factorial-valuation formula, the substitution/evaluation bridge, and `x^s := exp(s·log x)` on `1+pℤ_p`.

Dependencies (all resolve):
- `coeff` = `PowerSeries.coeff` (the file does `open PowerSeries` at line 463; the target is in the namespace-scope opened there). For `G : PowerSeries ℚ_[p]`, `coeff j G : ℚ_[p]`, so `(coeff j G : ℚ_[p])` is an **identity coercion** (no nontrivial cast).
- `Finset.finsuppAntidiag` — **mathlib**, `Mathlib/Algebra/Order/Antidiag/Finsupp.lean:45`; `Finset.mem_finsuppAntidiag` is the membership characterisation used at line 724.
- `norm_prod` (= `‖∏ f‖ = ∏ ‖f‖` over a `NormedField`) — **mathlib**, `Mathlib/Analysis/Normed/Ring/Basic.lean:757`.
- `Finset.prod_le_prod` — **mathlib**, `Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean:38`.
- `Finset.prod_pow` (`∏ f^n = (∏ f)^n`) — **mathlib**, `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:616`.
- `Finset.prod_pow_eq_pow_sum` (`∏ aˡⁱ = a^(∑lᵢ)`) — **mathlib**, `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:648`.
- `Finset.sum_tsub_distrib` (truncated-subtraction distributes over `∑` under a pointwise `≤`) — **mathlib**, `Basic.lean:945`.
- `pow_le_pow_left₀`, `Finset.prod_eq_zero`, `Finset.sum_const`, `Finset.card_range` — all **mathlib**.
- The line-690 `omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L]` confirms the statement uses none of the ambient `L`-algebra structure: it lives entirely in `ℚ_[p]`. (The `[IsUltrametricDist L]` is the only ambient instance retained, and only because `L = ℚ_[p]` already satisfies it; the statement itself never mentions `L`.)

---

### Statement (Phase 1)

`norm_coeff_prod_le` is a **theorem** stating the following:

> Let `G ∈ ℚ_p⟦X⟧` be a formal power series with `[X⁰]G = 0`, whose coefficients obey the
> Legendre-type bound `‖[Xʲ]G‖^{p−1} ≤ p^{j−1}` for every `j ≥ 1`. Fix `n, k ∈ ℕ` and a
> composition (multi-index) `l : ℕ →₀ ℕ` of `k` supported on `{0,…,n−1}` — i.e.
> `l ∈ finsuppAntidiag (range n) k`, so `∑_{i<n} l i = k`. Then the single multinomial product
> term satisfies
> `‖∏_{i<n} [X^{l i}]G‖^{p−1} ≤ p^{k−n}`.

Mathematical content. This is the per-tuple (per-monomial) estimate underlying the bound on
`[Xᵏ](Gⁿ)`. Writing `aₗ = ∏_{i<n}[X^{lᵢ}]G`, raising to the `(p−1)`-th power converts the
hypothesis into an additive valuation statement: `(p−1)·v_p([X^{lᵢ}]G) ≥ −(lᵢ−1)`, i.e.
`‖[X^{lᵢ}]G‖^{p−1} ≤ p^{lᵢ−1}` for each nonzero `lᵢ` (if any `lᵢ = 0`, then `[X⁰]G = 0` kills the
whole product). Multiplying over `i` and telescoping `∑_{i<n}(lᵢ−1) = (∑ lᵢ) − n = k − n` (using
that all `lᵢ ≥ 1` on the support) gives the claimed `p^{k−n}`. This is exactly the "`(p−1)·v_p(lᵢ)
≤ lᵢ−1` telescoping" the docstring describes. It is the inner half of the Dwork-region coefficient
bound `‖[Xᵏ](Gⁿ)‖^{p−1} ≤ p^{k−n}` (its consumer, `norm_coeff_pow_le`, sums these tuple bounds via
the ultrametric `pow_norm_sum_le`).

Variables / typeclasses (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime; only `ℚ_[p]` and `p−1 ≥ 1` are used.
- `G : PowerSeries ℚ_[p]` — the inner series.
- `n k : ℕ` — the outer power and the output degree.
- `l : ℕ →₀ ℕ` — the multi-index (composition) tuple.

Hypotheses (Lean side):
- `hcoeff : ∀ j, 1 ≤ j → ‖[Xʲ]G‖^{p−1} ≤ p^{j−1}` — the **per-coefficient Legendre bound**, rpow-free.
- `hc0 : [X⁰]G = 0` — zero constant coefficient (`G ∈ X·ℚ_p⟦X⟧`).
- `hl : l ∈ Finset.finsuppAntidiag (Finset.range n) k` — `l` is a composition of `k` over `{0,…,n−1}`.

Conclusion (math): `‖∏_{i<n} [X^{l i}]G‖^{p−1} ≤ p^{k−n}`.

Conclusion (Lean): `‖∏ i ∈ Finset.range n, (coeff (l i) G : ℚ_[p])‖ ^ (p - 1) ≤ (p : ℝ) ^ (k - n)`.

---

### Size classification (Phase 2a)

**Verdict: SMALL.**
Reason: a single-term (per-tuple) inequality used purely as the inner step of `norm_coeff_pow_le`
(its only caller, line 748). It introduces no new structure, is not a `## Main results` entry (the
file's headline is the `exp`/`log` correspondence `x^s := exp(s·log x)`), and is not named after a
person — although it *is* an instance of the named circle of results around Legendre's formula and
Dwork's lemma (see Phase 3), which is why the literature width was run exhaustively.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~25 substantive tactic lines (`by_cases` on a vanishing factor; ultrametric
`norm_prod`; `prod_le_prod` with `hcoeff`; `prod_pow_eq_pow_sum`; a `Nat`-subtraction telescoping
sub-proof `hsumeq`).
One-liner verdict: **n/a — kind is `theorem`, not a `def`.**

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic exponential power series coefficients Legendre valuation bound v_p multinomial telescoping convergence radius" | yes | `exp` has radius `p^{−1/(p−1)}` *because* `v_p(n!) = (n−s_p(n))/(p−1)`; Dwork exponential coeff valuation bounds `v(dₘ) ≥ c·m` | Wikipedia "p-adic exponential function"; Eremin, *Legendre's formula and p-adic analysis* (arXiv 1907.11902); Krattenthaler–Müller truncated-Dwork (arXiv 1412.7014). The `(p−1)·v_p` telescoping is exactly the mechanism here. |
| 2 | WebSearch (general / mechanism) | "\"formal power series\" composition coefficient valuation bound p-adic substitution norm estimate multinomial expansion" | yes | for `f∘g` with `g(0)=0`, `g^j` expands multinomially and per-term valuations add; ultrametric: `‖∑aₙxⁿ‖→0 ⟺` converges | Gupta REU (U. Chicago); Cambridge p-adic notes (Thorne); arXiv 1502.04607. Confirms the per-monomial valuation-additivity mechanism. |
| 3 | WebSearch (named-after / Dwork) | "Dwork lemma exp power series integral coefficients p-1 valuation bound coefficient of G^n composition substitution proof" | yes | Dwork's lemma: `exp f ∈ 1+Xℤₚ⟦X⟧ ⟺ f(Xᵖ)−p·f(X) ∈ pXℤₚ⟦X⟧`; **truncated** versions give *lower bounds on `v_p` of coefficient sequences under weaker hypotheses* | Krattenthaler–Müller (Adv. Math. 2015 / arXiv 1412.7014); MIT Kriz notes on Dwork's rationality proof. The target's hypothesis is precisely a "weaker than integral" coefficient-valuation bound, in the truncated-Dwork spirit. |
| 4 | ChatGPT MCP | (intended: "standard form, generality, and historical evolution of the per-monomial valuation bound `‖∏ᵢ[X^{lᵢ}]G‖^{p−1} ≤ p^{k−n}` underlying `[Xᵏ](Gⁿ)` estimates in p-adic analysis") | n/a | — | **ChatGPT MCP server not installed** in this environment (only `claude.ai`-proxy auth tools — Asana/Atlassian/Linear/etc. — are exposed; no `chatgpt`/`ask` tool). Recorded n/a per protocol; compensated by running **6** distinct WebSearch queries (3 generality levels + Robert textbook + 2 nLab/ncatlab) instead of the minimum 3. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | n/a | (no references dir; no `refs/` symlink) | `.mathlib-quality/references/` is **absent**; `refs/` symlink is **absent**. Recorded n/a with reason. The module docstring itself cites the sources (RJW Lem 5.14 / TeX 1892–1897; Cassels §12; Washington §5.1) — see #9 for textbook-channel coverage of those. |
| 6 | nLab | "p-adic exponential radius of convergence Legendre formula formal group ultrametric" + ncatlab "power series" | yes | nLab *power series*: substitution = "clone multiplication"; `ord(∑aᵥXᵥ) = min{v : aᵥ≠0}` is the valuation; ring of FPS over a field is a DVR | ncatlab.org/nlab/show/power+series; ncatlab.org/nlab/show/restricted+formal+power+series. The order/valuation framing is standard; no dedicated per-monomial *norm bound* page (it's elementary). |
| 7 | nCatLab (categorical) | (same page family as #6; also "formal group in nLab") | yes | substitution/composition is clone multiplication; formal-group exponentials converge on `v_p(x) > 1/(e·(q−1))` | ncatlab.org/nlab/show/formal+group — categorical packaging of the same convergence/valuation content; nothing more specific than #6. |
| 8 | Stacks Project (alg geom) | "formal power series substitution composition order vanishing coefficient" (general AG channel) | n/a | corroborating-only: Stacks treats `R[[X]]`, completion, order of products (`ord(fg)=ord f+ord g`), but has **no** p-adic-norm / Legendre coefficient-bound tag | This is an *analytic* p-adic estimate, not a scheme-theoretic statement; recorded n/a-with-corroboration. The `ord` additivity is the algebraic shadow of the valuation telescoping used here. |
| 9 | MathOverflow / Math.StackExchange / textbook channel | "Robert \"Course in p-adic Analysis\" exponential logarithm power series coefficient valuation estimate composition substitution lemma" | yes | Robert, *A Course in p-adic Analysis* — Ch.3 "p-adic valuation of a factorial" (Legendre), Ch.4 "Exponential and Logarithm" (convergence via Legendre), Ch.6 "formal substitutions, Newton/valuation polygons". The estimate is textbook-standard; **not isolated as a named lemma** | Springer link + ProofWiki book page. Matches the docstring's own Cassels §12 / Washington §5.1 citations: the bound is a standard step, never a headline theorem. |
| 10 | recent arXiv (last 5 yr) | (covered by #1, #3) | yes | arXiv 1412.7014 (truncated Dwork, 2014/2015), 1907.11902 (Legendre & p-adic analysis, 2019), 2509.26295 (p-adic Gamma / overconvergent Frobenius, 2025) | The coefficient-valuation bounds are treated as standard analytic infrastructure; no source isolates the per-tuple multinomial bound as a named result. |

The protocol passes: WebSearch ran **3+** queries at distinct generality levels (specific
`exp`/Legendre form / general composition-valuation mechanism / Dwork named-after); ChatGPT MCP
recorded n/a with a concrete reason (server not installed) and over-compensated with extra
WebSearch channels; local refs checked (absent → n/a, with the docstring's own citations noted);
nLab + nCatLab + Stacks + MathOverflow/textbook + arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: **a per-monomial p-adic valuation (norm) bound on the multinomial terms of
`[Xᵏ](Gⁿ)`**, instantiating the Legendre-formula / Dwork-lemma circle of results that govern the
convergence radius and coefficient integrality of the p-adic exponential and of formal
substitutions. Concretely: under a per-coefficient bound `‖[Xʲ]G‖^{p−1} ≤ p^{j−1}` (a "(p−1)·v_p ≥
−(j−1)" condition, weaker than integrality), the product over a composition `l` of `k` telescopes
to `‖∏[X^{lᵢ}]G‖^{p−1} ≤ p^{k−n}`.

Sources agree on the standard form: **yes**, on the *mechanism* — every source treats
valuation-additivity under multiplication plus the Legendre/Dwork per-coefficient bound as
elementary, standard p-adic analysis. **No** source isolates this exact per-tuple inequality as a
*named* lemma; it is universally an unnamed intermediate step inside the convergence-radius / Dwork
arguments (Robert Ch.4/6, Cassels §12, Washington §5.1, Krattenthaler–Müller).

Most general standard form: for **any** complete nonarchimedean (ultrametric) field `K` (or even a
ring with a suitable multiplicative valuation), a series `G ∈ K⟦X⟧` with `[X⁰]G = 0` and a
per-coefficient valuation bound `v(·)`, the product over a composition telescopes to a sum of
valuations. The p-adic specialisation fixes `K = ℚ_[p]` and packages the bound rpow-free as
`‖·‖^{p−1} ≤ p^{·}` (to avoid real `rpow`).

Generality dimensions where the literature varies:
- **Base field**: classical statements are over any complete nonarchimedean field `K` (ℂ_p, finite
  extensions of ℚ_p, Lubin–Tate ground fields). The target fixes **`ℚ_[p]`** — strictly narrower,
  and the `omit [NormedAlgebra ℚ_[p] L]` makes clear this is a deliberate `ℚ_[p]`-only statement,
  not the ambient `L`.
- **Hypothesis encoding**: the literature uses additive valuations `v_p([Xʲ]G) ≥ −(j−1)/(p−1)`. The
  target encodes this rpow-free as `‖[Xʲ]G‖^{p−1} ≤ p^{j−1}`. Equivalent over `ℚ_[p]`, but a
  bespoke project convention rather than a literature-canonical form.
- **Conclusion target**: the literature cares about `[Xᵏ](Gⁿ)` (the *summed* bound, = the target's
  consumer `norm_coeff_pow_le`); the per-tuple product bound is the unnamed inner step.

Disagreement with the literature: **none.** The target is a true, faithful, but specialised
(`ℚ_[p]`-fixed, rpow-free-encoded) instance of standard p-adic analysis.

---

### Generality analysis — `PadicLFunctions.norm_coeff_prod_le`

Literature-standard form (from Phase 3): for any complete nonarchimedean field `K`, `G ∈ K⟦X⟧` with
`[X⁰]G = 0` and `‖[Xʲ]G‖^{p−1} ≤ p^{j−1}` for `j ≥ 1`, and a composition `l` of `k` over
`{0,…,n−1}`: `‖∏_{i<n}[X^{lᵢ}]G‖^{p−1} ≤ p^{k−n}`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | base field | `ℚ_[p]` (the prime field) | any complete nonarchimedean field `K` (ℂ_p, `[K:ℚ_p]<∞`, …) | **yes** | The proof uses only `norm_prod` (any `NormedField`), `IsUltrametricDist`, `pow_le_pow_left₀`, and the hypothesis. Nothing is `ℚ_[p]`-specific *in the proof of this lemma* — the `p`-arithmetic lives in `hcoeff`, which is taken as a hypothesis. Restating over `[NormedField K] [IsUltrametricDist K]` (or `[NontriviallyNormedField K]` with an ultrametric) is mechanical. **Note:** the *consumer* `norm_coeff_pow_le` and ultimately `norm_factorial_le` are where the genuine `ℚ_[p]` Legendre input enters; this lemma itself is field-agnostic given `hcoeff`. |
| 2 | hypothesis encoding `‖[Xʲ]G‖^{p−1} ≤ p^{j−1}` | rpow-free real-power encoding with the literal exponent `p−1` | additive valuation `v_p([Xʲ]G) ≥ −(j−1)/(p−1)`, or `‖·‖ ≤ p^{−(j−1)/(p−1)}` (rpow) | partial | The `p−1` exponent is intrinsic to the rpow-free trick (it clears the `1/(p−1)` denominator in Legendre). A genuinely more general statement would replace `p−1` by an *arbitrary* exponent `m ≥ 1` and `p` by an arbitrary base `b > 1` (`‖[Xʲ]G‖^m ≤ b^{j−1} ⟹ ‖∏…‖^m ≤ b^{k−n}`) — at which point the lemma is **pure ordered-field/telescoping algebra with no `p` at all** (see Phase 4c row 7). |
| 3 | `hc0 : [X⁰]G = 0` | zero constant coeff | identical (`G ∈ X·K⟦X⟧`) | NO | Exactly the literature hypothesis (needed so any `lᵢ = 0` factor vanishes and so `finsuppAntidiag` indexing is meaningful). Maximally general. |
| 4 | index set `finsuppAntidiag (range n) k` | compositions of `k` over `{0,…,n−1}` | identical (multi-indices summing to `k`) | NO | This is mathlib's canonical antidiagonal type and is exactly the multinomial index set. Maximally general / idiomatic. |

This is the `/generalise`-style mechanical pass with a **literature-grounded target**. The headline
finding: **the `p` and `ℚ_[p]` are not load-bearing in *this* lemma's proof** — they are inputs via
`hcoeff`. The mathematically honest general form is an *arbitrary-base, arbitrary-exponent ordered-field
product-telescoping inequality*, which is barely about p-adics at all (Phase 4c row 7).

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD.**

Number of weakening opportunities found: **2 substantive** (base field `ℚ_[p]` → general
nonarchimedean field, row 1; and the fully-degenerated "arbitrary base `b`, exponent `m`" algebra
form, rows 1+2 combined — which removes p-adics entirely).

Proposed restatement (field-general, minimal change — keeps the `p`-flavoured `hcoeff`):
```lean
theorem norm_coeff_prod_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    (p : ℕ) [Fact p.Prime] (G : PowerSeries K)
    (hcoeff : ∀ j : ℕ, 1 ≤ j → ‖coeff j G‖ ^ (p - 1) ≤ (p : ℝ) ^ (j - 1))
    (hc0 : coeff 0 G = 0) (n k : ℕ) (l : ℕ →₀ ℕ)
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range n) k) :
    ‖∏ i ∈ Finset.range n, (coeff (l i) G)‖ ^ (p - 1) ≤ (p : ℝ) ^ (k - n) := …
```

Cost of restatement: **CHEAP** for row 1 (the proof is already field-agnostic — replace `ℚ_[p]` by
`K` and drop the unused algebra instances). **CHEAP–MODERATE** for the full row-2 abstraction
(replace `p−1 ↦ m`, `(p:ℝ) ↦ b`; the telescoping `hsumeq` and `prod_pow_eq_pow_sum` steps are
already base/exponent-agnostic, only the `0 < b`/`1 ≤ m` side conditions change).

EXPENSIVE is **not** in play here, so cost is not a verdict factor.

Per Phase 7: STRICTLY NARROWER → consider `YES-but-generalise-first` prominently; but see the
composability/call-site signal (one internal caller) and Phase 4c — the most general form is
"generic ordered-field product telescoping", which raises a real question about whether the *named*
lemma belongs in mathlib at all or should be inlined / replaced by a generic algebra lemma. That
tension is what tips the final verdict to BORDERLINE.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
| 1 | bundled hyps → typeclasses/instances? | no | — | `hcoeff`/`hc0` are genuine running hypotheses about a *specific* `G`, not "let `G` be a foo" preambles; there is no typeclass to extract. |
| 2 | sequences/metric → filters/topology? | no | — | A finite-product inequality; no limit/sequence/net to filter-ise. |
| 3 | construct object → universal-property class? | no | — | An inequality, not a construction. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | No substructure in play. |
| 5 | field/metric-specific → weaken typeclass to module/(semi)ring? | **yes** | `[NormedField K] [IsUltrametricDist K]` in place of `ℚ_[p]` (Phase 4b row 1). | the bound becomes reusable for `ℂ_[p]`, finite extensions of `ℚ_p`, Lubin–Tate ground fields — exactly the settings the *rest of this project* uses (`ResidueZeta.lean` works over a generic `K`; `GaloisAction.lean` over `ℂ_[p]`). |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index/base (ℕ, `p`, ℝ) → arbitrary additive/ordered structure? | **yes** | replace the prime base `(p:ℝ)` and exponent `(p−1)` by an arbitrary base `b > 1` and exponent `m ≥ 1`: *"if `‖[Xʲ]G‖^m ≤ b^{j−1}` and `[X⁰]G = 0`, then `‖∏_{i<n}[X^{lᵢ}]G‖^m ≤ b^{k−n}`"*. This form is **pure ordered-field algebra** — it never mentions `p`, primality, or p-adics. | unifies with the analogous `‖[Xʲ]G‖ ≤ 1 ⟹ ‖∏‖ ≤ 1` bound the project re-derives in `ResidueZeta.norm_coeff_pow_le_one` and `GaloisAction.norm_coeff_pow_le_one'`; both are instances of the *same* product-telescoping pattern at different bases. A single generic lemma would subsume all three. |

**Modern-idiom verdict (Phase 4c):** Modern idiom available: **yes** — and it is the *decisive*
observation. Rows 5 + 7 together say the mathematically right object is a **base/exponent-generic,
nonarchimedean-field-generic product-telescoping inequality** with essentially no p-adic content.
Proposed mathlib-idiomatic restatement:
```lean
-- in e.g. Mathlib/Analysis/Normed/Ring/Ultra.lean or a PowerSeries.Norm file
theorem PowerSeries.norm_prod_finsuppAntidiag_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    {G : PowerSeries K} {m : ℕ} (hm : 1 ≤ m) {b : ℝ} (hb : 0 ≤ b)
    (hcoeff : ∀ j : ℕ, 1 ≤ j → ‖coeff j G‖ ^ m ≤ b ^ (j - 1))
    (hc0 : coeff 0 G = 0) {n k : ℕ} {l : ℕ →₀ ℕ}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range n) k) :
    ‖∏ i ∈ Finset.range n, coeff (l i) G‖ ^ m ≤ b ^ (k - n) := …
```
  - Cost: **CHEAP–MODERATE** (the current proof is already structured exactly this way; `p`, `p−1`
    are only ever used as "some base / some exponent ≥ 1").
  - Mathlib downstream this enables: a single lemma subsuming (i) the exp-region bound
    `‖[Xᵏ](Gⁿ)‖^{p−1} ≤ p^{k−n}` (this project, via `norm_coeff_pow_le`), and (ii) the unit-ball
    bound `‖[Xᵏ](Gⁿ)‖ ≤ 1` re-derived twice in `ResidueZeta`/`GaloisAction` (with `m = 1`, `b = 1`).
  - Real mathematical improvement: it isolates the *actual* content (ultrametric `norm_prod` +
    `prod_pow_eq_pow_sum` + `Nat`-telescoping) as one reusable estimate, instead of three bespoke
    `ℚ_[p]`/`K`/`ℂ_[p]` copies — a genuine de-duplication, not abstraction for its own sake.

Because Phase 4c finds a real modern-idiom improvement, Phase 7 may produce
`YES-but-generalise-first` even though there is novel content — the "generalise first" target being
the base/exponent-generic form above. The *reason* this does not land cleanly on
`YES-but-generalise-first` is the judgment question (Phase 7): once the lemma is degenerated to
"generic product telescoping with no p-adics", is the *named* lemma still wanted, or is it close
enough to a 1–2-line `Finset` composition (`norm_prod` + `prod_pow_eq_pow_sum` + `prod_le_prod`)
that mathlib would prefer it inlined? That is the line Phase 6 probes and Phase 7 surfaces.

---

### Diamond / defeq risk — Phase 4.5

**n/a — declaration kind is `theorem`** (introduces no definitional equalities or typeclass-search
paths). Skipped.

---

### Mathlib search-status: `PadicLFunctions.norm_coeff_prod_le`

[A] Lean-Finder — n/a: AI-search service not reachable from this CLI environment. Compensated by [D]+[E] grep over the vendored mathlib tree (`.lake/packages/mathlib/Mathlib/`) and by reading the relevant `PowerSeries` / `Normed` files directly.

[B] Loogle (`lean_loogle`) — n/a: no `lean_loogle` MCP tool available in this environment. Intended type-pattern queries: `‖∏ _ ∈ Finset.range _, PowerSeries.coeff _ _‖ ^ _ ≤ _ ^ _` and `_ ∈ Finset.finsuppAntidiag _ _ → ‖∏ _, _‖ ≤ _`. Resolved by direct grep instead.

[C] LeanSearch (`lean_leansearch`) — n/a: no `lean_leansearch` MCP tool available. Intended NL queries: "norm of product of power series coefficients over a composition is bounded by a power of p" / "p-adic valuation bound on multinomial term of a power of a power series".

[D] Grep mathlib src — **NO HIT** (for the lemma; building blocks all present). Terms tried:
  - `‖.*coeff.*pow` / `coeff.*pow.*‖` / `finsuppAntidiag.*norm` / `norm.*finsuppAntidiag` over all of `Mathlib/` → **no** norm-of-coefficient-product or `finsuppAntidiag`-norm bound exists.
  - `norm_coeff` / `coeff_norm` in `RingTheory/`, `NumberTheory/Padics/`, `Analysis/` → only **unrelated** hits: `Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt` (continuity of roots), `Polynomial.sum_sq_norm_coeff_eq_circleAverage` (Parseval), `mahlerMeasure_le_sqrt_sum_sq_norm_coeff` (Landau) — all about *polynomials* and *archimedean* `ℂ`-norms, none about p-adic power-series coefficient products.
  - Closest *thematic* mathlib material: **`Mathlib/RingTheory/PowerSeries/Restricted.lean`** — the `IsRestricted c f := ‖coeff i f‖·cⁱ → 0` API (convergence/restricted series), with `convergenceSet`, `IsRestricted.mul`, etc. This is the *convergence-radius* framing of coefficient norms, **not** a Legendre/Dwork per-monomial p-power valuation bound; it provides no usable specialisation of the target.
  - Building blocks confirmed present and used by the proof: `Finset.finsuppAntidiag` + `mem_finsuppAntidiag` (`Algebra/Order/Antidiag/Finsupp.lean`), `norm_prod` (`Analysis/Normed/Ring/Basic.lean:757`), `Finset.prod_le_prod` (`.../GroupWithZero/Finset.lean:38`), `Finset.prod_pow` (`.../Group/Finset/Defs.lean:616`), `Finset.prod_pow_eq_pow_sum` (`.../Group/Finset/Basic.lean:648`), `Finset.sum_tsub_distrib` (`Basic.lean:945`), `pow_le_pow_left₀` (`Algebra/Order/GroupWithZero/Basic.lean:470`), `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` (`NumberTheory/Padics/MahlerBasis.lean` uses it). `PowerSeries.coeff_pow` (`RingTheory/PowerSeries/Basic.lean:631`) is the multinomial expansion the *consumer* uses.

[E] Name-pattern search (`lean_local_search` unavailable → grep) — **NO HIT** for the assembled lemma. Terms: `norm_coeff_prod`, `coeff_prod_le`, `finsuppAntidiag` + `norm`/`‖`, `prod` + `coeff` + `le`. Only the project's own `norm_coeff_prod_le` (and its cousins `norm_coeff_pow_le`, `norm_coeff_pow_le_one`) surface — no mathlib decl.

Searched for both:
  - the user's current `ℚ_[p]`/rpow-free form — **not present** in mathlib;
  - the literature-standard / general form (nonarchimedean-field-generic, base/exponent-generic product-telescoping bound) — **also not present**. Mathlib has the *components* (ultrametric `norm_prod`, `prod_pow_eq_pow_sum`, the antidiagonal) but no assembled coefficient-product valuation bound, and nothing in the Dwork / p-adic-exp direction.

**Concluded:** *not in mathlib (all methods exhausted, plus the literature-standard general form). Mathlib has only the generic `Finset`/`norm`/ultrametric building blocks and the convergence-flavoured `IsRestricted` API — neither the target nor its field-general form is present.*

---

### Call sites — `PadicLFunctions.norm_coeff_prod_le`

Internal use count: **K = 1** (within the project, excluding the declaring line `PadicExp.lean:711`).
External-to-file callers: **0 distinct files** (the single use is in the same file).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `PadicExp.lean:748` | `fun l hl => norm_coeff_prod_le p G hcoeff hc0 n k l hl` (the per-tuple argument to `pow_norm_sum_le` inside `norm_coeff_pow_le`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `norm_coeff_prod_le`?):
  - **(none verbatim)** — but a *thematically identical, structurally different* bound is re-derived
    by hand twice in the project at a different base/exponent (`m=1`, `b=1`):
    - `ResidueZeta.norm_coeff_pow_le_one` (`ResidueZeta.lean:1053`): `‖[Xᵏ](Gᵈ)‖ ≤ 1` via *induction on `d`* through `coeff_mul` + ultrametric (`IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty`) — **not** via `finsuppAntidiag`/`prod_pow_eq_pow_sum`.
    - `GaloisAction.norm_coeff_pow_le_one'` (`GaloisAction.lean:682`): the same fact over `ℂ_[p]`, explicitly labelled "re-derivation of `ResidueZeta.norm_coeff_pow_le_one`".
  - These are the `m=1,b=1` siblings flagged in Phase 4c row 7: the project already proves the same
    *kind* of coefficient bound three times, by two different methods, at two bases.

Signal (per Phase 6.0.1): **K = 1 internal use only → "possibly the wrong abstraction; could be
inlined"** → leans toward NO-composable. **But** the combination with the Phase-5 result (mathlib
has neither this nor the general form) and Phase 6 (genuinely *not* a ≤3-call composition) blocks a
clean NO. The honest read is: the lemma is real and non-trivial, but its *current grain* (one
caller, `ℚ_[p]`-fixed, rpow-free-encoded, inner-helper) is project-shaped, while its *general grain*
(Phase 4c) would deduplicate three project lemmas and could plausibly go to mathlib. Choosing
between "inline/keep local" and "generalise + upstream" is the human judgment — recorded as
BORDERLINE.

### Composition check (Phase 6)

Can `norm_coeff_prod_le` be derived from mathlib in ≤3 chained calls? **No.**

Attempt 1 (the only plausible direct route):
```lean
-- ‖∏ coeff (l i) G‖^(p-1) = (∏ ‖coeff (l i) G‖)^(p-1)        -- norm_prod
--                          = ∏ ‖coeff (l i) G‖^(p-1)          -- Finset.prod_pow
--                          ≤ ∏ p^(l i - 1)                    -- Finset.prod_le_prod + hcoeff   (needs l i ≥ 1)
--                          = p^(∑ (l i - 1))                  -- Finset.prod_pow_eq_pow_sum
--                          = p^(k - n)                        -- Finset.sum_tsub_distrib + the antidiagonal sum
```
  - Mathlib decls used: `norm_prod`, `Finset.prod_pow`, `Finset.prod_le_prod`, `Finset.prod_pow_eq_pow_sum`, `Finset.sum_tsub_distrib`, plus `Finset.prod_eq_zero` for the vanishing-factor branch.
  - Result: **fails as a ≤3-call composition.** This is 5–6 distinct mathlib calls *plus* (a) a
    `by_cases` split on whether some `lᵢ = 0` (handled via `prod_eq_zero` + `hc0`), (b) establishing
    `∀ i ∈ range n, 1 ≤ l i` from `not_exists`, and (c) the `Nat`-truncated-subtraction telescoping
    lemma `hsumeq : ∑(lᵢ−1) = k−n` (its own `sum_tsub_distrib` + `sum_const` + `card_range` proof).
    That is a ~25-line proof with case analysis and an arithmetic sub-lemma — **a genuine proof, not
    a 1–3-call glue**.
  - Notes: per the Phase-6 heuristics table, "multiple `have`s with non-trivial reasoning between"
    and "requires `by_cases` + an arithmetic side-lemma" are explicitly **NO** (proof in disguise).

**Conclusion: NOT-COMPOSABLE.** (Mathlib has the *primitives*, but assembling them is real work with
case analysis and a `Nat`-subtraction telescoping argument — far beyond a ≤3-call composition.)
This rules out `NO-composable-from-mathlib` and pushes Phase 7 toward a YES bucket or BORDERLINE.

---

## Verdict: `PadicLFunctions.norm_coeff_prod_le`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): standard p-adic analysis (Legendre's factorial formula / Dwork-lemma circle; Robert *Course in p-adic Analysis* Ch.4/6; Cassels §12; Washington §5.1). The *mechanism* is unanimous and elementary; the *exact per-tuple inequality* is an unnamed intermediate step nowhere isolated as a named result.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — fixed to `ℚ_[p]` (rows 1) where the math is nonarchimedean-field-generic, with a bespoke rpow-free hypothesis encoding; Phase 4c row 7 shows the maximally-honest form is a *base/exponent-generic, p-adic-free* product-telescoping inequality that would also subsume two other project lemmas.
- Mathlib search (Phase 5): **not in mathlib** in either the user's form or the general form; only the generic `Finset`/ultrametric building blocks and the unrelated `IsRestricted` convergence API exist.
- Composition check (Phase 6): **NOT-COMPOSABLE** (a ~25-line proof with a `by_cases` split and a `Nat`-subtraction telescoping sub-lemma; 5–6 mathlib calls, not ≤3).

**Rationale (1–2 paragraphs):**

Three of the four phases point at a YES-family verdict and none supports a clean NO: the result is
mathematically real and correct, it is genuinely absent from mathlib (both as stated and in its
field-general form), and it is not a short composition of mathlib primitives. Phase 4/4c then say
the *current* form is strictly narrower than what mathlib would want — fixed to `ℚ_[p]`, encoded
rpow-free with the literal `p−1` exponent, when the lemma's own proof never uses `p` for anything
but "a base > 1 / an exponent ≥ 1". The honest general form (Phase 4c row 7) is a
nonarchimedean-field-generic, arbitrary-base/exponent **product-telescoping inequality with no
p-adic content**, which would additionally deduplicate the two hand-rolled `m=1,b=1` siblings the
project already carries (`ResidueZeta.norm_coeff_pow_le_one`, `GaloisAction.norm_coeff_pow_le_one'`).
On the standard `/mathlibable` flow (STRICTLY NARROWER + not in mathlib + not composable) this would
resolve to **`YES-but-generalise-first`**.

What stops the skill from committing to that bucket on its own is a real judgment call it must not
make unilaterally. (1) Once degenerated to "generic product telescoping", the lemma sits *near* the
boundary of a 1–2-line `Finset` composition (`norm_prod` ▸ `prod_pow` ▸ `prod_le_prod` ▸
`prod_pow_eq_pow_sum`) — mathlib reviewers might prefer it inlined or replaced by a tiny generic
`Finset` lemma rather than shipped as a named p-adic result; the call-site signal (exactly **one**
internal caller) reinforces "possibly the wrong grain". (2) Conversely, the project's *threefold*
re-derivation of the same coefficient-bound pattern is exactly the kind of duplication that argues
*for* one named general lemma. (3) The lemma is an inner helper of an inner helper (`→
norm_coeff_pow_le → summable_prod_family → master_bridge`), never a headline result, so its mathlib
audience is unclear. These are taste/grain/audience questions — the defining trigger for BORDERLINE
— so the verdict is BORDERLINE with the questions below, the most likely resolution being
`YES-but-generalise-first` against the Phase-4c generic form.

**Numbered questions (≤5):**

  1. Should the lemma be **generalised before any upstreaming** to the Phase-4c form — arbitrary
     complete nonarchimedean field `K`, arbitrary base `b > 0` and exponent `m ≥ 1`
     (`‖[Xʲ]G‖^m ≤ b^{j−1} ∧ [X⁰]G = 0 ⟹ ‖∏_{i<n}[X^{lᵢ}]G‖^m ≤ b^{k−n}`)? (CHEAP–MODERATE; the
     proof is already base/exponent-agnostic.) **yes/no**
  2. If generalised, do you want it to **subsume** the project's two hand-rolled `m=1,b=1` copies
     (`ResidueZeta.norm_coeff_pow_le_one`, `GaloisAction.norm_coeff_pow_le_one'`) — i.e. is the
     deduplication target real and wanted? **yes/no**
  3. Is this lemma intended as **public, reusable mathlib API**, or purely an internal step of the
     `exp`/`log`-convergence proof (current state: one caller, `norm_coeff_pow_le`)? If internal
     only, it should stay project-local and is **out of mathlib scope**. **public / internal**
  4. Given the generic form is *close to* a short `Finset` composition (`norm_prod` +
     `prod_pow_eq_pow_sum` + `prod_le_prod`), would you prefer to **inline it** (or ship a tiny
     generic `Finset.prod_le_pow_sum`-style lemma) rather than a named p-adic-coefficient lemma?
     **inline / named-lemma**
  5. For the rpow-free encoding `‖·‖^{p−1} ≤ p^{·}` vs the additive-valuation form
     `v_p(·) ≥ −(·)/(p−1)`: if it *does* go to mathlib, which is the canonical statement you'd want
     (the project uses rpow-free deliberately to avoid `Real.rpow`)? **rpow-free / valuation**

Next action: user answers the questions; re-run `/mathlibable PadicLFunctions.norm_coeff_prod_le` to
resolve the verdict. Most likely outcomes:
  - Q1 yes + Q2 yes + Q3 public + Q4 named-lemma → **`YES-but-generalise-first`** against the
    Phase-4c generic form (then run `/generalise`, then `/cleanup`, then PR to
    `Mathlib/Analysis/Normed/Ring/Ultra.lean` or a new `Mathlib/RingTheory/PowerSeries/Norm.lean`).
  - Q3 internal-only → drop from mathlib consideration; keep project-local (and optionally still do
    Q1/Q2 generalisation *inside the project* to delete the two duplicate siblings).
  - Q4 inline → **`NO-composable-from-mathlib` in spirit**: replace all three project copies with a
    single small generic `Finset`/ultrametric lemma used inline (the composition is >3 calls, so a
    one-line *named* helper, not a literal inline, is the realistic form).

---

## Next step

User answers the 5 numbered questions above; re-run `/mathlibable PadicLFunctions.norm_coeff_prod_le`
to commit the verdict. The single most likely resolution is `YES-but-generalise-first` against the
Phase-4c base/exponent/field-generic product-telescoping form (which would also deduplicate
`ResidueZeta.norm_coeff_pow_le_one` and `GaloisAction.norm_coeff_pow_le_one'`); the competing
resolution is "keep project-local" if the lemma is internal-only (it currently has exactly one
caller, `norm_coeff_pow_le` at `PadicExp.lean:748`).

Sources (literature, Phase 3): [p-adic exponential function — Wikipedia](https://en.wikipedia.org/wiki/P-adic_exponential_function); [Eremin, *Legendre's formula and p-adic analysis* (arXiv 1907.11902)](https://arxiv.org/abs/1907.11902); [Krattenthaler–Müller, *Truncated versions of Dwork's lemma for exponentials of power series* (arXiv 1412.7014)](https://arxiv.org/abs/1412.7014); [MIT 18.785 notes — Dwork's p-adic proof of rationality of the ζ-function](https://math.mit.edu/nt/Kriz2020-12-07.pdf); [Robert, *A Course in p-adic Analysis* (Springer)](https://link.springer.com/book/10.1007/978-1-4757-3254-2) (Ch.3 factorial valuation, Ch.4 exp/log, Ch.6 formal substitution); [power series — nLab](https://ncatlab.org/nlab/show/power+series); [restricted formal power series — nLab](https://ncatlab.org/nlab/show/restricted+formal+power+series); [Some aspects of analysis related to p-adic numbers (arXiv 1502.04607)](https://arxiv.org/pdf/1502.04607).
