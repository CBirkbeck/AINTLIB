# `/mathlibable` report — `PadicLFunctions.norm_succ_inv_smul_pow_le`

**Final verdict: `BORDERLINE-needs-human`**

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task instruction — build is stale/slow here; Phase 0 fallback used)
- decl `PadicLFunctions.norm_succ_inv_smul_pow_le`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:326`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=Σxⁿ/n!` and `log(1+y)=Σ(−1)ⁿ⁺¹yⁿ/n` on a complete nonarchimedean normed `ℚ_p`-algebra field; this theorem is the per-term geometric-decay estimate that drives summability of the logarithm series (decomposition node R5.E, cluster E4).

---

### Statement (Phase 1)

`norm_succ_inv_smul_pow_le` is a **theorem** stating the following:

> Let `L` be a complete nonarchimedean (ultrametric) normed field that is a normed `ℚ_p`-algebra.
> For every `y ∈ L` and every `n ∈ ℕ`, the `n`-th logarithm-series term, raised to the `(p−1)`-th
> power, decays geometrically:
> `‖(−1)ⁿ · (n+1)⁻¹·yⁿ⁺¹‖^{p−1} ≤ ‖y‖^{p−1} · (p·‖y‖^{p−1})ⁿ`.

This is the logarithm analogue of the exponential decay estimate
`norm_factorial_inv_smul_pow_le` in the same file. Where the exponential term `(n!)⁻¹xⁿ` is
controlled by Legendre's bound on `v_p(n!)`, the logarithm term `(n+1)⁻¹yⁿ⁺¹` is controlled by the
much milder denominator valuation `v_p(n+1)` (a single integer, not a factorial). The `(p−1)`-th
power is taken purely to make the estimate **rpow-free**: it converts `‖n+1‖^{−1} = p^{v_p(n+1)/(p−1)}`
(a fractional power of `p`) into the integer power `p^{v_p(n+1)}`, so the whole inequality lives in
`ℝ` with integer exponents and no `Real.rpow`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime.
- `L : Type*`, `[NormedField L] [NormedAlgebra ℚ_[p] L]` — a normed `ℚ_p`-algebra field. The two
  heavier instances `[IsUltrametricDist L] [CompleteSpace L]` from the file's `variable` block are
  **explicitly `omit`-ted** for this theorem (line 323: `omit [IsUltrametricDist L] [CompleteSpace L] in`):
  the per-term bound is purely a norm computation and needs neither ultrametricity nor completeness.
- `y : L` — the base point (the logarithm is centred so this is `x − 1`).
- `n : ℕ` — the term index. Note: holds for **all** `n` (no `1 ≤ n` hypothesis), because the `(n+1)`
  shift means the denominator is never the problematic `0`.

Hypotheses (Lean side): none beyond the variables (no convergence-ball hypothesis — this is a raw
per-term estimate, true unconditionally).

Conclusion (math): each logarithm-series term is `O((p‖y‖^{p−1})ⁿ)` at the `(p−1)`-power level, with
explicit leading factor `‖y‖^{p−1}`; when `‖y‖^{p−1} < p⁻¹` (i.e. `‖y‖ < p^{−1/(p−1)}`, the
exponential ball) the geometric ratio `p‖y‖^{p−1} < 1` and the series converges.

Conclusion (Lean): `‖(-1 : L) ^ n * (((n : ℚ_[p]) + 1)⁻¹ • y ^ (n + 1))‖ ^ (p - 1) ≤ ‖y‖ ^ (p - 1) * ((p : ℝ) * ‖y‖ ^ (p - 1)) ^ n`.

**Proof shape.** Strip `(−1)ⁿ` (norm 1) and expand the norm of the scalar multiple; the denominator
norm is computed via `Padic.norm_eq_zpow_neg_valuation` + `Padic.valuation_natCast`, giving
`‖n+1‖ = p^{−v_p(n+1)}`. The inverted `(p−1)`-power bound `(‖n+1‖^{p−1})⁻¹ ≤ pⁿ` is then exactly the
integer valuation inequality `(p−1)·v_p(n+1) ≤ n`, supplied by the project-local
`sub_one_mul_padicValNat_succ_le` (line 309), which is itself the composition of `p^{v_p(n+1)} ∣ n+1`
(mathlib `pow_padicValNat_dvd`) with the Bernoulli inequality `one_add_mul_le_pow`. A final `calc` /
`ring` rearrangement produces the stated geometric form.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: it is a helper lemma (decomposition cluster E4) supplying a single per-term decay estimate
that feeds `summable_padicLog_terms`; it is not a `def`/structure, not a named theorem, and not a
`## Main results` entry (the file's main results are `padicExp_add`, `padicLog_mul`, and the
`exp`/`log` inversion `padicExp_padicLog` / `padicLog_padicExp`, not this bound).

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only — it does
not gate which channels Phase 3 runs.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-liner check **n/a**.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | p-adic logarithm series convergence norm bound nonarchimedean term decay valuation                     | yes  | `log(1+t)=Σ(−1)ⁿ tⁿ⁺¹/(n+1)` converges for `\|t\|_p<1`; convergence ⇔ terms `\|aₙtⁿ\|_p → 0` | Montréal Appendix 16 "Power series convergence and the p-adic logarithm"; arXiv 1809.07705 (rational summation of p-adic power series); the term-decay condition is exactly what this lemma bounds |
|  2 | WebSearch (general / standard form) | p-adic logarithm log(1+x) radius of convergence isometry nonarchimedean field standard form          | yes  | radius of convergence **= 1**; `log_p: 1+pℤ_p → ℚ_p` via the usual series; extends to `ℂ_p` | Cambridge Thorne notes (dpmms `jat58/all.pdf`); MIT 18.785 PS10; PlanetMath "p-adic exponential and p-adic logarithm"; Conrad/Thorne UConn notes — the radius-1 / open-unit-ball statement is the canonical one everywhere |
|  3 | WebSearch (term-valuation / denominator estimate) | p-adic logarithm term valuation `v_p(n)` growth `(p−1)v_p(n+1) ≤ n` logarithm denominator estimate | partial | the denominator valuation `v_p(n)` and the convergence-controlling growth appear, but the exact integer inequality `(p−1)v_p(n+1) ≤ n` is **not** a named result — it is an en-route computation | K. Conrad "p-adic growth of harmonic sums"; arXiv 1312.7789 (log-growth Newton polygons); Wikipedia "p-adic valuation"; the bound is folklore/elementary, never headlined |
|  4 | ChatGPT MCP                      | (intended: "standard p-adic form of the per-term decay bound for the log series + its generality + history") | n/a  | —                                | ChatGPT MCP server **configured but failed to connect** (`plugin:mathlib-quality:chatgpt-math` points at `/home/chris/.claude/mcp-servers/chatgpt-math/server.js`, a Linux path absent on this Darwin machine → "✘ Failed to connect"). Recorded n/a; WebSearch ×3 + nLab + PlanetMath + the module's own citations (RJW, Cassels §12, Washington §5.1) cover the standard-form question. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                | n/a  | (no references dir; no `refs/` dir/symlink) | both directories absent — recorded n/a. The module docstring's inline citations (RJW TeX 1892–1897 "as stated"; Cassels §12; Washington *Introduction to Cyclotomic Fields* §5.1) serve as the literature anchor. |
|  6 | nLab                             | p-adic logarithm / p-adic exponential                                                                   | partial | nLab routes the p-adic log through the general nonarchimedean-analytic-function / Iwasawa-log picture; the radius-1 convergence and the `log:1+𝔪 → field` homomorphism are the headline facts | not a categorical concept; nLab has no dedicated per-term-decay lemma |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                | not a categorical concept (a real-valued metric estimate on a p-adic field). |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                | not an algebraic-geometry concept (analytic norm estimate, not scheme/sheaf theory). |
|  9 | MathOverflow / Math.StackExchange| p-adic logarithm series term bound; convergence `\|x\|_p<1`; isometry / Iwasawa log                     | yes  | community consensus: log converges on `\|x−1\|_p<1`, the homomorphism to the additive group is "the" object; term decay is "obvious from `v_p(n)` growth" | recurring Q&A; nobody states a standalone `≤ ‖y‖^{p−1}(p‖y‖^{p−1})ⁿ` lemma — it is an internal computation |
| 10 | recent arXiv (last 5 years)      | p-adic logarithm series convergence / rational summation / log-growth                                   | partial | modern arXiv (1809.07705 summation of p-adic power series; 2107.00971 linear forms in p-adic logs; 1312.7789 log-growth Newton polygons) reuses the classical radius-1 + term-decay; no new canonical per-term-bound form | confirms no modern reformulation supersedes the classical convergence picture |

The protocol passed: WebSearch ran ≥3 distinct queries at three generality levels (specific
series/convergence form / the canonical radius-1 + general-`ℂ_p` form / the named-after term-valuation
estimate); ChatGPT MCP recorded n/a with a concrete reason (server present but unreachable); local
references recorded n/a with reason (dirs absent); nLab checked; nCatLab / Stacks recorded n/a with
reason; MathOverflow and recent arXiv each checked.

### Literature summary (Phase 3)

Concept identified as: **the per-term geometric-decay estimate for the p-adic logarithm series**
`log(1+y) = Σ_{n≥0} (−1)ⁿ (n+1)⁻¹ yⁿ⁺¹` on its disk of convergence `‖y‖<1` (here pre-restricted to the
exponential ball `‖y‖<p^{−1/(p−1)}` by the downstream consumer, so the geometric ratio is `<1`).

Sources agree on the standard form: **yes for the underlying object, no for this specific lemma.** The
*canonical, named* facts in every source (Cassels §12, Koblitz Ch. IV, Conrad/Thorne, PlanetMath,
MIT 18.785, nLab) are (i) the **series** `log_p(x)=Σ(−1)ⁿ⁺¹(x−1)ⁿ/n`, (ii) its **radius of convergence
= 1** (domain `‖x−1‖_p<1`), and (iii) the **group homomorphism** `log_p: 1+𝔪 → (field, +)` /
Iwasawa-log extension. The *per-term decay bound* this theorem states is universally treated as the
**en-route convergence computation** ("terms `→ 0` because `v_p(n)` grows slower than the geometric
gain"), never as a standalone named theorem, and never with this rpow-free `(p−1)`-power packaging.

Most general standard form: over **any complete nonarchimedean field extending `ℚ_p`** (`ℂ_p`, finite
extensions, etc.), the series `Σ(−1)ⁿ⁺¹(x−1)ⁿ/n` converges for `‖x−1‖<1`, with the `n`-th term norm
`‖(x−1)ⁿ/n‖ = ‖x−1‖ⁿ / ‖n‖ = ‖x−1‖ⁿ · p^{v_p(n)}` and `p^{v_p(n)} ≤ n`. The target's general `L`
matches this maximal setting exactly; the convergence-controlling fact is precisely that `‖n‖⁻¹` grows
only polynomially while `‖y‖ⁿ` decays geometrically.

Generality dimensions where the literature varies:
- **Underlying field**: ℚ_p → any complete nonarchimedean field / ℂ_p — the target's general `L`
  matches the most general setting. ✓ already maximal.
- **Convergence region**: literature uses the full log ball `‖y‖<1`; the target proves a bound valid
  for **all** `y` (unconditional), with the geometric ratio only becoming `<1` on the exp ball — the
  target is, if anything, *more* general than the literature statement (it is a pure inequality, not a
  convergence claim).
- **Packaging/exponent**: the literature works directly with valuations `v_p(·)`; the target uses the
  rpow-free `(p−1)`-power device to stay in integer exponents — a Lean-formalisation convenience, not
  a mathematical object the literature names.

Disagreement with the literature: **none on content** — the bound is true and is exactly the standard
convergence mechanism. The only "disagreement" is *framing*: the literature never isolates this as a
named lemma, and never in the `(p−1)`-power rpow-free form (which exists only to dodge `Real.rpow` in
Lean).

---

### Generality analysis — `norm_succ_inv_smul_pow_le`

Literature-standard form (from Phase 3): over any complete nonarchimedean field `⊇ ℚ_p`, the log series
`Σ(−1)ⁿ⁺¹(x−1)ⁿ/n` converges on `‖x−1‖<1`, driven by the per-term estimate
`‖(x−1)ⁿ/n‖ = ‖x−1‖ⁿ·p^{v_p(n)} ≤ n·‖x−1‖ⁿ`.

| # | Parameter / hypothesis                          | Current Lean form                  | Literature-standard form     | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------------------|------------------------------------|------------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L] [NormedAlgebra ℚ_[p] L]` (with `IsUltrametricDist`/`CompleteSpace` `omit`-ted) | normed `ℚ_p`-algebra field | any complete nonarchimedean field ⊇ ℚ_p | NO (already minimal) | the proof needs only the `ℚ_p`-algebra structure (to read `‖n+1‖` via `Padic.norm_eq_zpow_neg_valuation`) and the multiplicative norm; it already `omit`s ultrametricity + completeness, so its hypotheses are **weaker** than the file default and match/undershoot the literature setting |
| 2 | `y : L` (free, no ball hypothesis)              | unrestricted                       | `‖y‖<1` (or `‖y‖<p^{−1/(p−1)}`) | n/a (already maximal) | the lemma is an unconditional inequality; it imposes **no** convergence hypothesis — strictly more general than any "on the ball" literature statement |
| 3 | `n : ℕ` (all `n`, no `1 ≤ n`)                   | all `n`                            | `n ≥ 1` (log has no `n=0` term) | n/a | the `(n+1)` index shift makes it hold for all `n`; no narrowing |
| 4 | conclusion's geometric factor `(p·‖y‖^{p−1})ⁿ` | `≤ ‖y‖^{p−1}·(p‖y‖^{p−1})ⁿ`        | `‖y‖ⁿ·p^{v_p(n+1)}` (sharp per-term) | **YES (constant)** | the `pⁿ` factor over-counts: the sharp factor is `p^{v_p(n+1)}`, which is `≤ pⁿ` but usually far smaller (it is `1` whenever `p ∤ n+1`). The project uses `pⁿ` because it is what dominates the *whole* geometric series uniformly and avoids carrying `v_p(n+1)` into the summability proof |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL in its hypotheses** (it is, in fact, *more* general than the
literature statement — unconditional in `y`, ultrametricity/completeness `omit`-ted), but its
**conclusion is non-sharp**: the geometric factor `pⁿ` is looser than the sharp per-term `p^{v_p(n+1)}`.
Number of weakening opportunities found: **0 on hypotheses**, **1 (non-sharp constant)** on the
conclusion — and that "looseness" is deliberate and *correct* for the lemma's purpose (a uniform
geometric majorant suitable for `tendsto_pow_atTop_nhds_zero_of_lt_one`; the sharp `p^{v_p(n+1)}` factor
would make the downstream geometric-series comparison harder, not easier).

Proposed restatement: **none warranted.** Sharpening `pⁿ → p^{v_p(n+1)}` would make the statement
*less* useful (it no longer reads as a clean geometric series), so this is not a "generalise-first"
lever — it is a fit-for-purpose majorant. The hypotheses are already minimal.

Cost of restatement: **n/a** (no restatement proposed; the form is already at or beyond the literature
generality on every hypothesis axis).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                        | no       | — | hypotheses are already typeclasses (`NormedField`/`NormedAlgebra`); the heavier ones are even `omit`-ted. Nothing to bundle |
|  2 | sequences/metric → filters/nets/topological?                                                              | no       | — | this is a single per-term norm inequality; there is no sequential limit *in this lemma* to filter-ise (the *consumer* `summable_padicLog_terms` already uses `Filter.cofinite`/`tendsto`/`tendsto_pow_atTop_nhds_zero_of_lt_one`) |
|  3 | construct an object → universal-property class?                                                            | no       | — | this is an estimate, not a construction |
|  4 | set-with-closure-predicate → bundled substructure?                                                         | no       | — | n/a |
|  5 | vector-space/metric/field-specific → weaken typeclass hierarchy?                                           | partial  | already general `L`; the only real-content lever is at the *definition* layer — if a mathlib nonarchimedean `padicLog`/`expSeries`-analogue existed, this would be a term-bound lemma in that namespace | the right move is to introduce a mathlib p-adic log/exp **development**, not to reshape this signature |
|  6 | 1-categorical → higher-categorical?                                                                        | no       | — | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive/ordered structure?                                              | no       | — | the index `n` and the `(p−1)`-power are intrinsic to the p-adic valuation arithmetic; nothing to abstract |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for the lemma as stated). The lemma is already an idiomatic, maximally-
weak-hypothesis norm inequality. The only organisational improvement lives one layer down: mathlib has
**no** p-adic / nonarchimedean **logarithm** (nor exponential) analytic function at all (its
`RingTheory/PowerSeries/Log.lean` is the *formal* power series `log` — purely algebraic, no norm /
convergence content; `NormedSpace.exp` is archimedean-only via `expSeries_radius_eq_top`). So the
mathlib-idiomatic move is to introduce a nonarchimedean `padicLog` (with its convergence-ball API,
summability, and the `log`/`exp` inversion) and state this as the per-term decay lemma *in that
namespace* — a def-development decision, not a reformulation of this signature. One-line reason it is
not itself a modernisation move: it is a concrete metric estimate whose form is already idiomatic and
already at minimal hypotheses; the modernisation question is entirely about whether to upstream the
underlying `padicLog`/`padicExp` machinery.

---

### Diamond / defeq risk — `norm_succ_inv_smul_pow_le`

**n/a — declaration kind is `theorem`.** (Phase 4.5 runs only for `def`/`class`/`instance`.)

---

### Mathlib search-status: `norm_succ_inv_smul_pow_le`

[A] Lean-Finder       "p-adic logarithm series term bound", "norm (x^n / n) p-adic decay"   n/a: Lean-Finder web UI not callable in this environment — substituted with exhaustive grep over the mathlib tree (method D) for every candidate name/shape.
[B] Loogle            `‖_ * (_⁻¹ • _ ^ _)‖ ^ _ ≤ _`, `‖_ ^ _ / _‖ ≤ _ * _ ^ _`, p-adic log term   no hits: there is no `‖(n+1)⁻¹ • yⁿ⁺¹‖ ≤ …` shape in mathlib; the only nearby `‖xⁿ/n‖`-style facts are archimedean (`Complex`/`Real` log/exp), not nonarchimedean.
[C] LeanSearch        "p-adic logarithm series term norm bound", "geometric decay of p-adic log terms"   no hits: surfaces formal-power-series `PowerSeries.log` (no norm) and archimedean `Real.log`/`Complex.log` estimates only.
[D] Grep mathlib src  `grep -rln "padicLog\|padicExp\|PadicLog"` and `"IsUltrametricDist"` under `Analysis/SpecialFunctions/`   **zero** p-adic log/exp anywhere in mathlib; **zero** `IsUltrametricDist` support in `Analysis/SpecialFunctions/`. The only `log` in a power-series setting is `Mathlib/RingTheory/PowerSeries/Log.lean` — the **formal** series `log : A⟦X⟧` (`coeff_log`, `deriv_log`, `logOf`), which carries **no norm / convergence / analytic content** at all.
[E] Name pattern      `padicLog`, `padicExp`, `logSeries`, `norm_log`, `succ_inv_smul`   `padicLog`/`padicExp` do **not** exist in mathlib (only in *this* project). `PowerSeries.log` exists but is algebraic. No nonarchimedean term-decay lemma under any name.

Searched for both:
- the user's current form (`‖(−1)ⁿ·(n+1)⁻¹•yⁿ⁺¹‖^{p−1} ≤ ‖y‖^{p−1}(p‖y‖^{p−1})ⁿ`) — not in mathlib.
- the literature-standard forms (the convergence-driving per-term estimate `‖(x−1)ⁿ/n‖ ≤ n‖x−1‖ⁿ`; the
  radius-1 convergence; and any general-`NormedSpace` log analogue) — none of these exist p-adically /
  nonarchimedeanly in mathlib either.

Concluded: **not in mathlib (all methods exhausted, plus the literature-standard forms).** Mathlib has
**no** p-adic / nonarchimedean logarithm or exponential as analytic functions; the only `log` is the
*formal* power series `PowerSeries.log` (no norm), and the only analytic exp (`NormedSpace.exp`) is
archimedean (`expSeries_radius_eq_top`, no `IsUltrametricDist` support). The proof's *infrastructure*
is genuine mathlib (`Padic.norm_eq_zpow_neg_valuation`, `Padic.valuation_natCast`, `pow_padicValNat_dvd`,
`one_add_mul_le_pow`); only the assembled per-term log estimate is project-local.

---

### Call sites — `norm_succ_inv_smul_pow_le`

Internal use count: **2**  (within the project, NOT counting the declaring theorem)
External-to-file callers: **0 distinct files** (both uses are in the *same* file, different theorems)

| Caller file:line               | Usage pattern (one-line excerpt)                                              |
|--------------------------------|-------------------------------------------------------------------------------|
| PadicExp.lean:378              | `lt_of_le_of_lt (norm_succ_inv_smul_pow_le p y n) hsmall` — inside `summable_padicLog_terms`, the geometric majorant that drives the log series to `0` along `Filter.cofinite` (via `tendsto_pow_atTop_nhds_zero_of_lt_one` on ratio `p‖y‖^{p−1}<1`), giving summability on the exp ball |
| PadicExp.lean:407              | `refine lt_of_le_of_lt (norm_succ_inv_smul_pow_le p y m) ?_` — inside `norm_succ_inv_smul_pow_lt`, the strict tail-domination `‖(−1)ᵐ(m+1)⁻¹•yᵐ⁺¹‖ < ‖y‖` for `m ≥ 1` on the open ball |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none) — the only occurrences of the `(((n:ℚ_[p])+1)⁻¹ • y^(n+1))` term pattern are in `padicLog`
    itself (line 385, the def `Σ(−1)ⁿ(n+1)⁻¹•(x−1)ⁿ⁺¹`) and in the two callers above, which *call* this
    lemma rather than re-deriving the bound.

What the call-sites pattern tells you: **K = 2 internal uses**, no external/downstream consumers, no
inline re-derivation. Per the Phase-6 signal table this is a genuine (non-junk) internal API: two
distinct downstream theorems (`summable_padicLog_terms`, `norm_succ_inv_smul_pow_lt`) both depend on it
non-trivially. But both consumers are `padicLog`-specific (about the project's logarithm), so the
lemma's value to mathlib does **not** rest on heavy *cross-project* reuse — it rests entirely on whether
the *p-adic logarithm development itself* is upstreamed (see Verdict).

---

### Composition check (Phase 6)

Can `norm_succ_inv_smul_pow_le` be derived from mathlib in ≤3 chained calls?

Attempt 1: a mathlib p-adic-log term-bound lemma, specialised.
  - Mathlib decls used: — (none exist).
  - Result: **fails** — mathlib has no p-adic / nonarchimedean logarithm at all, so there is nothing to
    specialise. `PowerSeries.log` is the formal series and carries no norm.

Attempt 2: assemble directly from the mathlib valuation/Bernoulli primitives.
  - Mathlib decls used: `Padic.norm_eq_zpow_neg_valuation`, `Padic.valuation_natCast`,
    `pow_padicValNat_dvd`, `one_add_mul_le_pow`.
  - Result: **this is essentially the project's proof** — and it is *not* a ≤3-call composition. It needs
    (i) the norm-rewrite chain `norm_mul`/`norm_smul`/`norm_inv`/`mul_pow`/`inv_pow`; (ii) the valuation
    identity `hval : ‖n+1‖ = p^{−v_p(n+1)}`; (iii) the project-local integer inequality
    `sub_one_mul_padicValNat_succ_le` (`(p−1)v_p(n+1) ≤ n`), which is itself `pow_padicValNat_dvd`
    composed with the Bernoulli bound `one_add_mul_le_pow` plus `nlinarith`; and (iv) a `calc`/`ring`
    rearrangement into geometric form. That is a genuine multi-lemma proof, not a 1–3 call composition.

Attempt 3: any archimedean log/exp tail bound transported to `L`.
  - Mathlib decls used: `Real.log`/`Complex.log` estimates, `Complex.norm_exp_sub_one_sub_id_le`.
  - Result: **fails** — those are archimedean (constant `1`, ball `‖x‖≤1` in the *real* norm) and there
    is no coercion `L → ℂ` making the p-adic statement correspond; the whole archimedean special-function
    API is inapplicable nonarchimedeanly.

Conclusion: **NOT-COMPOSABLE.** There is no p-adic logarithm in mathlib to compose against, and the
estimate is a real multi-step valuation argument (not a `.symm`/`.trans`/single-call composition).

---

## Verdict: `norm_succ_inv_smul_pow_le`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the *standard named* objects are the p-adic **log series**, its
  **radius-1 convergence** (`‖x−1‖_p<1`), and the **`log:1+𝔪 → (field,+)` homomorphism** (Cassels §12 /
  Koblitz Ch. IV / Conrad–Thorne / PlanetMath / MIT 18.785 / nLab). This per-term geometric-decay bound
  is the universally-used *convergence step*, but it is **never** isolated as a named theorem, and never
  in this rpow-free `(p−1)`-power form.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL on hypotheses** — in fact *more* general than the
  literature statement (unconditional in `y`; `IsUltrametricDist`/`CompleteSpace` `omit`-ted). The only
  non-sharpness is the deliberately-loose geometric factor `pⁿ` (vs. sharp `p^{v_p(n+1)}`), which is the
  *correct* choice for a uniform geometric majorant — not a generalise-first lever.
- Mathlib search (Phase 5): **not in mathlib** — no p-adic/nonarchimedean log or exp exists; the only
  `log` is the formal power series `PowerSeries.log` (no norm); no `IsUltrametricDist` support in
  `Analysis/SpecialFunctions/`.
- Composition check (Phase 6): **NOT-COMPOSABLE** (nothing p-adic to compose from; the proof is a genuine
  multi-step valuation argument).

**Rationale (why BORDERLINE, not a YES/NO):**

This is a *true, genuinely missing-from-mathlib* p-adic estimate, proved sorry-free at minimal (indeed
beyond-literature) hypotheses — so it is **not** a NO-mathlib-has-it and **not** a NO-composable. But
three things block a clean YES, and each is a judgment call the skill cannot ground in evidence alone —
mirroring the sibling exponential bound `norm_padicExp_sub_one_sub_self_le` (also BORDERLINE) and its
twin `norm_factorial_inv_smul_pow_le`:

1. **It cannot be PR'd standalone — it is inseparable from a development mathlib lacks.** The lemma is
   the per-term decay estimate *for* `PadicLFunctions.padicLog` (line 385), the project's p-adic
   logarithm. Mathlib has **no** p-adic / nonarchimedean logarithm or exponential as an analytic function
   (only the *formal* `PowerSeries.log`, which has no norm). Upstreaming this lemma meaningfully requires
   upstreaming a whole nonarchimedean-`log`/`exp` development (`InExpBall`/convergence ball, summability
   `summable_padicLog_terms`, the radius-1 / isometry facts, the `log`/`exp` inversion `padicLog_padicExp`
   / `padicExp_padicLog`, `padicLog_mul`, etc.). Whether to undertake that BIG, multi-decl upstreaming is
   a project/community-policy decision — exactly what the skill defers to the human.

2. **It is not the literature's canonical object — it is a convergence-step packaging choice.** Every
   source names the *series*, the *radius 1*, and the *homomorphism*; nobody names this per-term bound, and
   nobody states it in the rpow-free `(p−1)`-power form (which exists only to avoid `Real.rpow` in Lean).
   If anything from this circle is "the" mathlib contribution, it is the `padicLog` def + its radius-of-
   convergence / summability API, with this estimate as an internal helper. Which pieces deserve to be
   first-class mathlib API vs. private proof scaffolding is a packaging judgment for the human.

3. **The shape is a Lean-formalisation convenience, not a mathematical object.** The `(p−1)`-power and the
   uniform `pⁿ` majorant are exactly tuned to make the *downstream* Lean proofs (geometric-series
   comparison via `tendsto_pow_atTop_nhds_zero_of_lt_one`) clean; the mathematically natural statement a
   reviewer would expect is per-term valuation `v_p((x−1)ⁿ/n) = n·v_p(x−1) − v_p(n)`. A mathlib reviewer
   would likely want the estimate restated in valuation terms, or folded into the summability lemma — a
   taste/API call.

The two internal call sites (K=2, both `padicLog`-specific, no external consumers — Phase 6.0) reinforce
that the lemma's mathlib-worth comes **not** from cross-project reuse pressure but entirely from the
upstreaming decision about the p-adic-log machinery as a whole. That is a human call.

**Numbered questions (≤5):**

1. Do you intend to upstream the project's p-adic / nonarchimedean **logarithm + exponential
   development** to mathlib as a unit (the `padicLog` / `padicExp` definitions + convergence ball
   `InExpBall` + summability + the radius-1 / isometry facts + the `log`/`exp` inversion)? This lemma
   should travel *with* that development, not alone — it is meaningless without the `padicLog` def, which
   mathlib does not have.
2. If yes to (1): should this per-term bound be a **public API lemma** in the new namespace, or kept as a
   **private proof helper** feeding the summability lemma `summable_padicLog_terms` (which is the
   mathematically meaningful, citable statement)?
3. If yes to (1): is the rpow-free `(p−1)`-power packaging acceptable in mathlib, or should the estimate
   be restated in **valuation terms** (`v_p((x−1)ⁿ⁺¹/(n+1)) = (n+1)v_p(x−1) − v_p(n+1)`) / folded into
   the summability proof — the form a reviewer would expect?
4. Should this PR be **co-developed with the exponential analogues** (`norm_factorial_inv_smul_pow_le`,
   `norm_padicExp_sub_one_sub_self_le`, both also BORDERLINE for the same reason) as one
   nonarchimedean-`exp`/`log` contribution series, rather than as isolated lemmas?
5. If you do **not** plan to upstream the p-adic-log machinery: then this lemma is correctly a permanent
   project-local helper (K=2 uses, both `padicLog`-specific), and it should be dropped from mathlib
   consideration entirely. Is that the case?

**Next action:** user answers the questions; re-run `/mathlibable norm_succ_inv_smul_pow_le` (ideally
after, or together with, a `/mathlibable PadicLFunctions.padicLog` run, since the def's verdict governs
this lemma's). Likely resolutions:
  - "Upstreaming the p-adic exp/log development" → likely flips to **YES-add-as-is** (the hypotheses are
    already maximal, so there is no generalise-first lever) as part of the nonarchimedean-`log`/`exp` PR
    series — possibly restated in valuation terms or absorbed into the summability lemma per Q2/Q3.
  - "Keep project-local" → drop from mathlib consideration; it stays a fit-for-purpose private-grade
    helper feeding `summable_padicLog_terms` and `norm_succ_inv_smul_pow_lt`.

---

## Next step

User answers the five numbered questions above; re-run `/mathlibable norm_succ_inv_smul_pow_le`
(preferably alongside `/mathlibable PadicLFunctions.padicLog`, since this lemma's verdict is governed by
the upstreaming decision on the `padicLog` definition it is stated about, and ideally batched with the
exponential twins `norm_factorial_inv_smul_pow_le` / `norm_padicExp_sub_one_sub_self_le`) to resolve to
either `YES-add-as-is` (upstream the nonarchimedean-exp/log development as a unit) or
drop-from-consideration (keep as a project-local helper).
