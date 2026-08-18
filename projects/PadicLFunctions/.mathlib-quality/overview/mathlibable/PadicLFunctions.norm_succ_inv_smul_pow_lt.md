# `/mathlibable` report — `PadicLFunctions.norm_succ_inv_smul_pow_lt`

**Final verdict: `BORDERLINE-needs-human`** (scope/grain call — the lemma is a true, maximally-general, sorry-free, missing-from-mathlib p-adic estimate, but it is inseparable from a p-adic / nonarchimedean **logarithm development that mathlib does not have**; whether to upstream that whole cluster — and how to package this helper within it — is a human/community decision. See Phase 7. This mirrors its exponential twin `norm_factorial_inv_smul_pow_sub_lt` and the `_le` companion `norm_succ_inv_smul_pow_le`, both BORDERLINE in this ledger for the same reason.)

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per task BUILD NOTE — `lake build` is stale/slow here; Phase-0 fallback used). Every mathlib building block invoked by the proof was verified present in the pinned tree at `.lake/packages/mathlib/Mathlib/` (see Phase 5).
- decl `PadicLFunctions.norm_succ_inv_smul_pow_lt`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:396`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  *The p-adic exponential and logarithm (RJW Lem 5.14)* — `exp(x)=∑xⁿ/n!` converges and is an isometry on the open ball `‖x‖ < p^{−1/(p−1)}`; `log(1+y)=∑(−1)ⁿ⁺¹yⁿ/n` converges for `‖y‖<1` and inverts `exp` on the matched balls; realises RJW Lemma 5.14 (TeX 1892–1897, citing Cassels §12; cross-ref Washington §5.1). This theorem is the **strict tail-domination** step that makes the logarithm an isometry on the ball.

---

### Statement (Phase 1)

`norm_succ_inv_smul_pow_lt` is a **theorem** stating the following:

> Let `L` be a normed `ℚ_[p]`-algebra field. Fix `y ∈ L` in the **open** convergence ball of the
> `p`-adic exponential (`‖y‖^{p−1} < p⁻¹`, i.e. `‖y‖ < p^{−1/(p−1)}`) with `y ≠ 0`. Then for every
> `m ≥ 1` the `m`-th term of the logarithm series `log(1+y) = ∑ (−1)ⁿ (n+1)⁻¹ yⁿ⁺¹` is **strictly**
> smaller in norm than the linear (`m = 0`) term `y`:
> `‖(−1)ᵐ (m+1)⁻¹·yᵐ⁺¹‖ < ‖y‖`.

This is the **strict tail-domination** step behind the headline fact that the `p`-adic logarithm is an **isometry** on its convergence ball — `‖log(1+y)‖ = ‖y‖` (the file's consumer `norm_padicLog`, line 417: `‖padicLog x‖ = ‖x − 1‖`). Once every term beyond the linear one is *strictly* dominated, the ultrametric "norm of a sum equals the max when the maximal term is unique" (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`) pins the total norm to the linear term. The strictness is genuinely a property of the **open** ball: on the closed boundary the geometric factor `p·‖y‖^{p−1}` would equal `1`, degrading the `<` to `≤`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue prime; the radius `p^{−1/(p−1)}` and the valuation arithmetic are intrinsically about a prime `p`.
- `{L : Type*}`, `[NormedField L]`, `[NormedAlgebra ℚ_[p] L]` — a normed `ℚ_[p]`-algebra field. **Both heavier instances `[IsUltrametricDist L]` and `[CompleteSpace L]` from the file's `variable` block are explicitly `omit`-ted** for this theorem (line 387: `omit [IsUltrametricDist L] [CompleteSpace L] in`): the strict per-term bound is a pure norm computation and needs neither ultrametricity nor completeness. (Contrast the exp twin `norm_factorial_inv_smul_pow_sub_lt`, which keeps `IsUltrametricDist` because it factors a `geom_sum₂` over an ultrametric sum bound; the log term is a *single* monomial `(m+1)⁻¹yᵐ⁺¹`, so no ultrametric sum estimate is needed and ultrametricity too is dropped.)
- `{y : L}` — the base point (the logarithm is centred so this is `x − 1`).
- `{m : ℕ}` — the term index.

Hypotheses (Lean side):
- `(hy : InExpBall p y)` — `y` lies in the open exp ball `‖y‖^{p−1} < p⁻¹` (so the geometric ratio `p·‖y‖^{p−1} < 1`). The lemma is stated on the *exp* ball, not the full log ball `‖y‖<1` — the project only needs the log on the smaller ball where it inverts `exp`.
- `(hy0 : y ≠ 0)` — so `‖y‖ > 0`, making the strict bound `< ‖y‖` meaningful.
- `(hm : 1 ≤ m)` — the term is genuinely beyond the linear (`m = 0`) one; for `m = 0` the term *equals* `y`, so strictness needs `m ≥ 1`.

Conclusion (math): every higher logarithm-series term is strictly norm-dominated by the linear term `y`.

Conclusion (Lean): `‖(-1 : L) ^ m * (((m : ℚ_[p]) + 1)⁻¹ • y ^ (m + 1))‖ < ‖y‖`.

**Proof shape.** From `InExpBall` derive `hT1 : p·‖y‖^{p−1} < 1` (via `mul_lt_mul_of_pos_left` + `mul_inv_cancel₀`). Apply the `_le` companion `norm_succ_inv_smul_pow_le` (line 326) to bound the `(p−1)`-power of the term by `‖y‖^{p−1}·(p‖y‖^{p−1})ᵐ`; a two-step `calc` then shows this is `< ‖y‖^{p−1}` using `pow_le_pow_of_le_one` (the geometric factor `(p‖y‖^{p−1})ᵐ ≤ (p‖y‖^{p−1})¹` for `m ≥ 1`, since the base is in `[0,1)`) followed by `mul_lt_of_lt_one_right` (multiplying `‖y‖^{p−1}` by `p‖y‖^{p−1} < 1` strictly shrinks it). Finally `lt_of_pow_lt_pow_left₀` removes the `(p−1)`-power. So the lemma is, precisely, *"upgrade the geometric `_le` bound to a strict `<` using the open-ball ratio `<1`."*

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma in decomposition cluster **R5.E** (E4, the logarithm) supplying the per-term strict-domination estimate that feeds the log isometry `norm_padicLog`. It is not a `def`/structure, not a named theorem, and not a `## Main results` entry (the file's headline results are `padicExp_add`, the exp isometry `norm_padicExp_sub_padicExp`, `norm_padicLog`, `padicLog_mul`, and the `exp`/`log` inversion — not this bound).

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only — it does not gate which channels Phase 3 runs.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-liner check **n/a** (the defeq / diamond / API-name exemptions apply only to definitions). Body is a multi-step `calc` proof (~20 substantive lines).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form: isometry + tail domination) | "p-adic logarithm isometry norm preserving log(1+y) tail terms dominated by linear term nonarchimedean" | **yes** | `log(1+t)=∑(−1)ⁿ(n+1)⁻¹tⁿ⁺¹` converges for `‖t‖_p<1`; convergence is governed by **term decay** under the strong triangle inequality (sum's norm = max term; "based on the terms going to zero, not cancellation") | Montréal *Appendix 16* "Power series convergence and the p-adic logarithm" (dms.umontreal.ca); Cédric Dion *Arithmetic properties of the p-adic logarithm* (ism.uqam.ca); K. Conrad / J. Thorne UConn notes (kconrad.math.uconn.edu). The term-decay mechanism this lemma quantifies is the universally-used convergence engine. |
|  2 | WebSearch (general / per-term form) | "p-adic logarithm series term norm bound \|yⁿ/n\|_p < \|y\|_p for n ≥ 2 strict domination convergence" | **yes** | radius of convergence **= 1**, disc `{x : ‖x‖_p < 1}`; "the logarithm series converges *better* than the exponential series … due to factorials in the numerator vs. denominator"; term norms `‖yⁿ/n‖` drive convergence | MIT `dav/exp.pdf` *Exponential and logarithm in p-adic fields*; Montréal App. 16; Cambridge `jat58/all.pdf`; Wikipedia *P-adic exponential function*; UChicago REU `Gupta.pdf`. The radius-1 / open-unit-ball statement is canonical everywhere. |
|  3 | WebSearch (named-after / isometry aliases: Iwasawa log) | "p-adic logarithm isometry \|log(x)\|_p = \|x−1\|_p Iwasawa logarithm 1+pZp norm preserving proof" | **yes** | `logₚ` induces an **isomorphism** `1+m_K^r ≅ m_K^r` for `r > e/(p−1)`; the 2-adic log is an isometry `1+4ℤ₂ → 4ℤ₂`; Iwasawa's normalisation `log p = 0` | Iwasawa-theory sources (projecteuclid Kato; arXiv math/0512015 "A Note on a result of Iwasawa"; arXiv 1907.06437; Wikipedia *Iwasawa algebra*). **Directly confirms the isometry our lemma serves** (`norm_padicLog`): on the appropriate ball the log is norm-preserving / a local isomorphism. |
|  4 | ChatGPT MCP                      | (intended: "standard p-adic form of the strict per-term tail-domination bound for the log series; its generality; historical evolution") | n/a  | —                                | ChatGPT MCP server **configured but failed to connect**: `plugin:mathlib-quality:chatgpt-math` points at `node /home/chris/.claude/mcp-servers/chatgpt-math/server.js`, a **Linux** path absent on this **Darwin** machine (`claude mcp list` → "✘ Failed to connect"). Recorded n/a; the three WebSearch queries above explicitly requested the standard form + its generality + named sources (Cassels/Washington/Iwasawa) + the proof mechanism (strict domination), covering the MCP brief. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                | n/a  | (no `references/` dir; no `refs/` dir/symlink in this checkout) | both absent — recorded n/a. The module docstring's inline citations (RJW TeX 1892–1897 "as stated"; Cassels *Local Fields* §12; Washington *Introduction to Cyclotomic Fields* §5.1) serve as the literature anchor; the project's `worklist.json`/decomposition labels this cluster **R5.E** (E4). |
|  6 | nLab                             | `ncatlab.org/nlab/show/p-adic+logarithm`                                                                | n/a  | **HTTP 404 — no dedicated page** | Verified by fetch: nLab has no standalone p-adic-logarithm entry. The concept lives under classical p-adic-analysis references, not a categorical nLab page (consistent with the sibling reports' nLab findings). |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | not a categorical concept        | a strict scalar inequality between norms of two power-series terms; nothing categorical to look up. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | not an algebraic-geometry concept | nonarchimedean analytic norm estimate, not scheme/sheaf theory. |
|  9 | MathOverflow / Math.StackExchange| p-adic log term bound; convergence `‖x−1‖_p<1`; isometry / Iwasawa log (covered transitively by #1–#3)   | yes  | community consensus: log converges on `‖x−1‖_p<1`, is the isometry/homomorphism to `(field,+)`; term decay "obvious from `v_p(n)` growth" | surfaced via the lecture-note hits; nobody states a standalone `‖(m+1)⁻¹yᵐ⁺¹‖ < ‖y‖` strict-tail lemma — it is an internal convergence/isometry step. |
| 10 | recent arXiv (last 5 years)      | p-adic logarithm: rational summation / linear forms in p-adic logs / Iwasawa (1907.06437, 2107.00971, 2304.02789) | partial | modern work reuses the classical radius-1 convergence + the log-as-isometry/homomorphism; no new canonical per-term-bound form | confirms no contemporary reformulation supersedes the classical convergence/isometry picture; the strict tail bound stays an en-route step. |

**Protocol pass check:** WebSearch ran **3 distinct queries at three generality levels** (specific isometry + tail-domination form #1; the general per-term / radius-1 form #2; the named-after Iwasawa-log isometry / aliases #3) — all three hit, #3 confirming the isometry the lemma serves. ChatGPT MCP unavailable (Linux path on Darwin) → explicitly substituted by the three queries. Local refs checked (n/a, absent). nLab checked (404, no page). nCatLab / Stacks recorded n/a with reasons. MathOverflow covered transitively. Recent arXiv (1907.06437, 2107.00971, 2304.02789) checked. **All nine channels addressed.**

### Literature summary (Phase 3)

Concept identified as: **the strict per-term tail-domination underlying the isometry of the `p`-adic logarithm on its convergence ball** — for `y` in the (exp-)ball and `m ≥ 1`, `‖(−1)ᵐ(m+1)⁻¹yᵐ⁺¹‖ < ‖y‖`, the engine of `‖log(1+y)‖ = ‖y‖` (the file's `norm_padicLog`).

Sources agree on the standard form: **yes for the underlying objects, no for this specific lemma.** The *canonical, named* facts in every source (Cassels §12, Koblitz Ch. IV, Conrad/Thorne, MIT `dav/exp.pdf`, Montréal App. 16, Iwasawa-theory literature) are (i) the **series** `log_p(x)=∑(−1)ⁿ⁺¹(x−1)ⁿ/n`, (ii) its **radius of convergence = 1** (domain `‖x−1‖_p<1`), and (iii) the **isometry / group isomorphism** `log_p : 1+m^r ≅ m^r` (norm-preserving), Iwasawa's `log p = 0` normalisation. The *strict per-term tail bound* this theorem states is universally treated as an **en-route step** toward the isometry/convergence — never isolated as a standalone named theorem, and never in this rpow-free `(p−1)`-power packaging.

Most general standard form: over **any complete nonarchimedean field extending `ℚ_p`** (`ℂ_p`, finite extensions), the log series converges on `‖x−1‖<1` and is a norm-preserving isomorphism onto its image on the appropriate sub-ball; the per-term norm `‖yⁿ⁺¹/(n+1)‖ = ‖y‖ⁿ⁺¹·p^{v_p(n+1)}` is dominated by `‖y‖` once `‖y‖` is small enough that the geometric gain beats the polynomial `p^{v_p(n+1)} ≤ n+1`. The target's general `L` matches this maximal setting; in fact, by `omit`-ting `IsUltrametricDist`/`CompleteSpace` and dropping any "complete field" assumption, the target's hypotheses **undershoot** the literature framing.

Generality dimensions where the literature varies:
- **Underlying field**: ℚ_p → any complete nonarchimedean field / ℂ_p — the target's general `L` matches the most general setting. ✓ already maximal (indeed weaker: completeness `omit`-ted).
- **Convergence region**: the literature isometry lives on a ball `1+m^r` with `r > e/(p−1)`; the target works on the **exp** ball `‖y‖^{p−1}<p⁻¹` (where log inverts exp — the project's need), with `y≠0`, `m≥1` the sharp range for strictness. The target is a pure inequality, not a convergence claim — if anything more elementary than the literature statement.
- **Packaging/exponent**: the literature works directly with valuations `v_p(·)` / `Real.rpow` radius `p^{−1/(p−1)}`; the target uses the rpow-free `(p−1)`-power device to stay in integer exponents — a Lean-formalisation convenience, not a mathematical object the literature names.

Disagreement with the literature: **none on content** — the bound is true and is exactly the standard convergence/isometry mechanism. The only "disagreement" is *framing*: the literature never isolates this strict per-term step as a named lemma, and never in the rpow-free `(p−1)`-power form (which exists only to dodge `Real.rpow` in Lean).

---

### Generality analysis — `norm_succ_inv_smul_pow_lt`

Literature-standard form (from Phase 3): over any complete nonarchimedean field `⊇ ℚ_p`, the log series is a norm-preserving isomorphism on the appropriate ball, driven by per-term domination `‖yⁿ⁺¹/(n+1)‖ < ‖y‖` for the higher terms.

| # | Parameter / hypothesis                          | Current Lean form                  | Literature-standard form     | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------------------|------------------------------------|------------------------------|---------------------|---------------------------------|
| 1 | `p : ℕ`, `[Fact p.Prime]`                       | a rational prime                   | a rational prime             | NO                  | the radius `p^{−1/(p−1)}` and the valuation bound `(p−1)v_p(m+1) ≤ m` are intrinsically about a prime `p`. |
| 2 | `L` field: `[NormedField L] [NormedAlgebra ℚ_[p] L]` (with `IsUltrametricDist` **and** `CompleteSpace` both `omit`-ted) | normed `ℚ_p`-algebra field | any complete nonarchimedean field ⊇ ℚ_p | NO (already minimal — in fact *below* the literature) | the proof needs only the `ℚ_p`-algebra structure (to read `‖m+1‖` via `Padic.norm_eq_zpow_neg_valuation`, inside the `_le` companion) and a multiplicative norm; it `omit`s **both** ultrametricity and completeness, so its hypotheses are strictly weaker than the file default and undershoot the literature setting. |
| 3 | `y : L` (with `hy : InExpBall p y`, `hy0 : y ≠ 0`) | open exp ball, `y≠0`            | log ball `‖y‖<1` (or `1+m^r`) | NO (sharp)          | the project deliberately works on the *exp* ball (where log inverts exp); `y≠0` is needed for `‖y‖>0` making the strict `<` meaningful. Both are the sharp range for this strict statement, not narrowings to weaken. |
| 4 | `m : ℕ` with `1 ≤ m`                             | `m ≥ 1`                            | `n ≥ 2` (for `‖yⁿ/n‖<‖y‖`)   | NO (sharp)          | the `(m+1)` index shift means `m ≥ 1` corresponds to the literature's `n ≥ 2`; for `m = 0` the term *equals* `y` (not `<`). Exactly the sharp strictness range. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** — and on the field axis it is *more* general than the literature statement (stated over an arbitrary normed `ℚ_[p]`-algebra field with **both** `IsUltrametricDist` and `CompleteSpace` `omit`-ted, whereas textbooks assume a complete nonarchimedean field). Every numeric hypothesis (`InExpBall`, `y≠0`, `m≥1`) is exactly the sharp range where the strict inequality holds.
Number of weakening opportunities found: **0**.
Proposed restatement: **none warranted for generality.** The only cosmetic move is the rpow-free `‖y‖^{p−1}<p⁻¹` (`InExpBall`) ↔ `Real.rpow` radius `p^{−1/(p−1)}` packaging — a presentation choice, not a weakening (Phase 4c).
Cost of restatement: **n/a** (no restatement proposed; the form is already at or beyond the literature generality on every axis).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                        | no       | — | hypotheses are already typeclasses (`NormedField`/`NormedAlgebra`); the heavier ones (`IsUltrametricDist`/`CompleteSpace`) are even `omit`-ted. The only bundled `Prop`s (`InExpBall`, `y≠0`, `m≥1`) are genuine data. Nothing to bundle. |
|  2 | sequences/metric → filters/nets/topological?                                                              | no       | — | this is a single fixed-`m` scalar inequality; there is no limit/convergence *in this lemma* to filter-ise (that lives one layer up, in `summable_padicLog_terms`/`norm_padicLog`, which already use `Filter`/`tendsto`/`norm_tsum_le`). |
|  3 | construct an object → universal-property class?                                                            | no       | — | this is an estimate, not a construction. |
|  4 | set-with-closure-predicate → bundled substructure?                                                         | no       | — | n/a. |
|  5 | vector-space/metric/field-specific → weaken typeclass hierarchy?                                           | no (already general) | — | already stated over a general normed `ℚ_p`-algebra field with both heavy instances dropped; cannot weaken further. The only real lever is one layer down — see verdict. |
|  6 | 1-categorical → higher-categorical?                                                                        | no       | — | n/a. |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive/ordered structure?                                              | no       | — | the index `m` and the `(p−1)`-power are intrinsic to the p-adic valuation arithmetic; nothing to abstract. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for the lemma as stated). It is already an idiomatic, maximally-weak-hypothesis strict norm inequality (it even drops both `IsUltrametricDist` and `CompleteSpace`). The only organisational improvement lives **one layer down**: mathlib has **no** p-adic / nonarchimedean **logarithm** (nor exponential) as an analytic function — its `RingTheory/PowerSeries/Log.lean` is the *formal* power-series `log` (purely algebraic, no norm/convergence), and `NormedSpace.exp` is archimedean-only (`expSeries_radius_eq_top`, no `IsUltrametricDist` support). So the mathlib-idiomatic move is to introduce a nonarchimedean `padicLog` (with its convergence-ball API, summability, and the `log`/`exp` inversion + isometry) and state this strict-domination estimate as a lemma *in that namespace* — a def-development decision, not a reformulation of this signature. One-line reason it is not itself a modernisation move: it is a concrete strict scalar inequality whose form is already idiomatic and already at minimal hypotheses; the modernisation question is entirely about whether to upstream the underlying `padicLog`/`padicExp` machinery.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** (Phase 4.5 runs only for `def`/`abbrev`/`structure`/`inductive`/`class`/`instance`; a proposition introduces no definitional equalities or typeclass-search paths.)

---

### Mathlib search-status: `norm_succ_inv_smul_pow_lt`

[A] Lean-Finder       "p-adic log isometry per-term strict bound", "‖yⁿ⁺¹/(n+1)‖ < ‖y‖ nonarchimedean"   n/a: Lean-Finder web service not reachable from this sandboxed environment — substituted by [D] grep + [E] name-pattern over the pinned mathlib tree.
[B] Loogle            `‖_ * (_⁻¹ • _ ^ _)‖ < ‖_‖`, `‖(_ : ℚ_[_])⁻¹ • _ ^ _‖ < ‖_‖`, p-adic log term strict   n/a (service not reachable) → substituted by [D] type-shape grep `‖.*•.*\^.*‖ < ‖`: **no hits** — there is no `‖(n+1)⁻¹ • yⁿ⁺¹‖ < ‖y‖`-shaped strict tail-domination lemma anywhere in mathlib.
[C] LeanSearch        "p-adic logarithm isometry", "norm of power-series term strictly less than linear term"   n/a (service not reachable) → substituted by [D]/[E]; the natural-language target surfaces only formal-power-series `PowerSeries.log` (no norm) and archimedean `Real.log`/`Complex.log` material.
[D] Grep mathlib src  `padicLog|padicExp|PadicLog|PadicExp` (zero); `nonarchimedean.*exp|nonarchimedean.*log` (only Topology/Analysis **infrastructure** files — `Nonarchimedean/Basic.lean`, `Normed/Group/Ultra.lean` — no exp/log function); building blocks below all present.   **partial — building blocks only.**
[E] Name pattern      `_smul_pow_lt`, `inv_smul_pow`, `norm_term_lt`, `tail.*dominat`, `padicLog`, `norm_padicLog`   `padicLog`/`padicExp` do **not** exist in mathlib (only in *this* project). `PowerSeries.log` exists but is algebraic (no norm). The `norm_padicLog`/`Isometry` hits are generic metric-space isometry infrastructure (`Topology/MetricSpace/Isometry.lean`), **not** the p-adic-log isometry. No nonarchimedean strict-tail-domination lemma under any name.

Searched for both:
  - the user's current form (`‖(−1)ᵐ(m+1)⁻¹•yᵐ⁺¹‖ < ‖y‖`) — **no hit** anywhere in mathlib.
  - the literature-standard forms (the log isometry `‖log(1+y)‖=‖y‖` / `1+m^r ≅ m^r`; the per-term `‖yⁿ/n‖ < ‖y‖`, `n≥2`) — **no packaged hit**; mathlib has no p-adic log at all.

Building blocks confirmed present in mathlib (each used by the proof):
  - `norm_succ_inv_smul_pow_le` — the geometric `_le` companion. **PROJECT-LOCAL** (`PadicExp.lean:326`), itself **absent from mathlib** (its own report is BORDERLINE). This is the substantive p-adic input that this `_lt` lemma sharpens.
  - `lt_of_pow_lt_pow_left₀` — `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:699` (removes the `(p−1)` power).
  - `pow_le_pow_of_le_one` — `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:393` (the geometric factor `(p‖y‖^{p−1})ᵐ ≤ (p‖y‖^{p−1})¹` for `m≥1`, base in `[0,1)`).
  - `mul_lt_of_lt_one_right` — `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:343` (`a·b < a` when `0<a`, `b<1`).
  - `mul_lt_mul_of_pos_left` — `Mathlib/Algebra/Order/GroupWithZero/Defs.lean:234`; `mul_le_mul_of_nonneg_left` — `Defs.lean:226`; `mul_inv_cancel₀`, `norm_pos_iff` — present in `Analysis/Normed/Group/Basic.lean` / field API.

Adjacent (different) facts in mathlib — checked and rejected:
  - `PowerSeries.log` (`Mathlib/RingTheory/PowerSeries/Log.lean`) — the **formal** power-series `log` (`coeff_log`, `deriv_log`); purely algebraic, **no norm / convergence / analytic content**. Cannot supply a norm bound.
  - `NormedSpace.exp` / `expSeries` (`Mathlib/Analysis/SpecialFunctions/Exponential.lean`) — the **archimedean** Banach-algebra exponential (`expSeries_radius_eq_top`, converges everywhere); no `IsUltrametricDist` support, no nonarchimedean log, and the complex/real `exp`/`log` are **not** isometries — the opposite regime. Inapplicable nonarchimedeanly.

Concluded: **not in mathlib (all substituted methods exhausted, plus the literature-standard isometry / per-term forms).** Mathlib has the generic ordered-field collapse lemmas the proof uses (`pow_le_pow_of_le_one`, `mul_lt_of_lt_one_right`, `lt_of_pow_lt_pow_left₀`), but **not** the strict per-term log-tail bound this lemma states, and **no p-adic logarithm** for it to belong to. The substantive p-adic input (`norm_succ_inv_smul_pow_le`) is itself project-local and absent from mathlib.

---

### Call sites — `norm_succ_inv_smul_pow_lt`

Internal use count: **K = 1** (within `PadicLFunctions`, not counting the declaration itself).
External-to-file callers: **0** distinct other files (and **0** other projects — repo-wide grep returns only `PadicExp.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| PadicExp.lean:431 | `fun n => norm_succ_inv_smul_pow_lt p hx hy0 (by omega)` — inside `norm_padicLog` (the headline log isometry `‖padicLog x‖ = ‖x − 1‖`, line 417), supplying the per-term strict bound `hterm : ∀ n, ‖…‖ < ‖x−1‖` that feeds the ultrametric `IsUltrametricDist.norm_tsum_le_of_forall_le` tail estimate, which (with `norm_add_eq_max_of_norm_ne_norm`) pins the total log norm to the linear term. |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `norm_succ_inv_smul_pow_lt`?):
  - The structurally analogous **exp** lemma `norm_factorial_inv_smul_pow_sub_lt` (`PadicExp.lean:141`) proves the same kind of strict tail-domination for the *exponential difference* series, and re-runs the same `norm_*_inv_pow_le` + `pow_le_pow_of_le_one` + `lt_of_pow_lt_pow_left₀` pattern rather than calling this lemma — because the `xᵐ−yᵐ` difference vs. single-`yᵐ⁺¹` term shapes differ. So the *strict-domination pattern* recurs (once for exp-difference, once for log), each tied to a different term shape. **Not a literal re-derivation of this exact lemma.** No other occurrence of the log term pattern outside `PadicExp.lean`.

What the pattern tells us: **K = 1** internal use, no external/downstream consumers, no inline re-derivation of this exact lemma. Per the Phase-6.0.1 table, `K = 1` ("possibly the wrong abstraction — could be inlined") nominally *leans NO-composable*. But the single consumer (`norm_padicLog`) calls it inside a `∀ n` quantifier (`hterm := fun n => norm_succ_inv_smul_pow_lt …`), so it is genuinely a *parametrised family* of strict bounds, not a one-off `have` — extracting it as a named lemma is the natural factoring (the alternative is an inline block inside the isometry proof). The composability question therefore turns on **mathlib composability** (Phase 6), not on the local call count — exactly as for the exp twin `norm_factorial_inv_smul_pow_sub_lt` (also K=1, also feeding an isometry, also BORDERLINE).

---

### Composition check (Phase 6)

Can `norm_succ_inv_smul_pow_lt` be derived **from mathlib** in ≤3 chained calls?

Attempt 1 — direct mathlib one-liner:
  - Sketch: a mathlib p-adic-log per-term strict bound, specialised.
  - Decls used: — (none exist).
  - Result: **fails** — mathlib has no p-adic / nonarchimedean logarithm at all, so there is nothing to specialise. `PowerSeries.log` is the formal series and carries no norm.

Attempt 2 — composing from mathlib primitives (the actual proof skeleton):
  - Sketch: (i) derive `hT1 : p·‖y‖^{p−1} < 1` from `InExpBall` via `mul_lt_mul_of_pos_left` + `mul_inv_cancel₀`; (ii) apply the **project-local** `norm_succ_inv_smul_pow_le` for the geometric `(p−1)`-power bound; (iii) a two-step `calc` collapsing it `< ‖y‖^{p−1}` via `pow_le_pow_of_le_one` (geometric factor for `m≥1`) then `mul_lt_of_lt_one_right`; (iv) `lt_of_pow_lt_pow_left₀` to remove the `(p−1)` power.
  - Decls used: `norm_succ_inv_smul_pow_le` **(project-local, absent from mathlib)**, `mul_lt_mul_of_pos_left`, `mul_inv_cancel₀`, `pow_le_pow_of_le_one`, `mul_lt_of_lt_one_right`, `lt_of_pow_lt_pow_left₀`, plus `norm_pos_iff`.
  - Result: **fails the ≤3-call bar.** This is a multi-step `calc` proof (derive the ratio bound, invoke the geometric `_le` lemma, run a nested `calc` with `pow_le_pow_of_le_one`/`mul_lt_of_lt_one_right`, then strip the power). By the Phase-6 heuristics ("multiple `have`s with nontrivial reasoning / `calc` is a proof, not a composition") this is unambiguously a **proof**. Crucially, its substantive p-adic input `norm_succ_inv_smul_pow_le` is **itself not in mathlib** — so even granting the generic ordered-field collapse as "composition", the chain bottoms out at a project-local p-adic estimate that mathlib lacks.

Attempt 3 — any archimedean log tail bound transported to `L`:
  - Decls used: `Real.log`/`Complex.log` estimates, `PowerSeries.log`.
  - Result: **fails** — those are archimedean (real norm) or purely formal (no norm); there is no coercion making the p-adic statement correspond, and the archimedean log is not an isometry. Inapplicable nonarchimedeanly.

Conclusion: **NOT-COMPOSABLE from mathlib.** No ≤3-call mathlib derivation exists; the genuine proof is a multi-step nonarchimedean argument that routes through a project-local geometric bound (`norm_succ_inv_smul_pow_le`) absent from mathlib. The generic collapse lemmas (`pow_le_pow_of_le_one`, `mul_lt_of_lt_one_right`, `lt_of_pow_lt_pow_left₀`) are present but only do the *final* `≤ → <` upgrade; they do not produce the p-adic geometric bound itself.

---

## Verdict: `PadicLFunctions.norm_succ_inv_smul_pow_lt`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the lemma is the **strict per-term tail-domination** behind the `p`-adic **logarithm isometry** `‖log(1+y)‖ = ‖y‖` (`norm_padicLog`). The underlying objects — the log series, its **radius-1 convergence**, and the **norm-preserving isomorphism** `1+m^r ≅ m^r` (Iwasawa log) — are textbook/canonical (MIT `dav/exp.pdf`, Montréal App. 16, Cassels §12, Washington §5.1, Iwasawa-theory literature, Phase-3 #1–#3). But the strict per-term step is **never isolated as a standalone named lemma**, and never in the rpow-free `(p−1)`-power form.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (Phase 4b — stated over a general normed `ℚ_[p]`-algebra field, with **both** `IsUltrametricDist` and `CompleteSpace` `omit`-ted, so even weaker than the literature framing; every numeric hypothesis `InExpBall`/`y≠0`/`m≥1` is sharp). **No modern-idiom reformulation** (Phase 4c — the only lever is the absent nonarchimedean-`log` namespace, one layer down). **0 weakening opportunities.**
- Mathlib search (Phase 5): **not in mathlib** — no `padicLog`/nonarchimedean logarithm at all (only the formal `PowerSeries.log`, no norm; archimedean `NormedSpace.exp`/`Complex.log`, the opposite regime); no strict per-term log-tail bound of this shape (`[B]/[D]` shape grep empty); the substantive input `norm_succ_inv_smul_pow_le` is itself project-local and absent.
- Composition check (Phase 6): **NOT-COMPOSABLE** — a multi-step `calc` nonarchimedean proof, past the ≤3-call bar, routing through the project-local geometric `_le` bound; the generic ordered-field collapse lemmas present in mathlib only perform the final `≤ → <` upgrade.
- Call sites (Phase 6.0): **K = 1** (`norm_padicLog`, the log isometry), used as a parametrised `∀ n` family — no inline re-derivation of this exact lemma, no external/cross-project consumers.

**Rationale (1–2 paragraphs):**

On its own technical merits this reads like a strong YES-add-as-is: it is a *true, maximally-general (Phase 4b — in fact below the literature's hypotheses), sorry-free, NOT-COMPOSABLE (Phase 6), genuinely-missing-from-mathlib (Phase 5)* p-adic estimate whose mathematical content is squarely textbook (Phase 3 — the log-isometry mechanism, Cassels/MIT/Iwasawa). It is decidedly **not** any NO bucket: mathlib has no p-adic logarithm or any strict per-term tail bound of this shape (the only `log`s are the formal `PowerSeries.log` with no norm, and the archimedean `Complex.log`/`Real.log`, which are *not* isometries — the opposite regime), and it cannot be inlined as a ≤3-call composition (the genuine proof routes through the project-local geometric bound `norm_succ_inv_smul_pow_le`, itself absent from mathlib).

What blocks a clean YES is **not** novelty or generality but a **scope/grain judgment the skill must defer** — exactly as for its exponential twin `norm_factorial_inv_smul_pow_sub_lt`, the `_le` companion `norm_succ_inv_smul_pow_le`, `summable_padicExp_terms`, and `norm_padicExp_sub_one_sub_self_le` (all BORDERLINE in this ledger for the same reason). (i) **The lemma is inseparable from a definition layer mathlib does not have.** Its entire purpose is to make `norm_padicLog` — the isometry of the project's `padicLog` (line 384) — go through; but mathlib has **no** p-adic / nonarchimedean logarithm, no `InExpBall` convergence-ball API, and the lemma's substantive input even names `ℚ_[p]`-valuations through `norm_succ_inv_smul_pow_le`. Upstreamed in isolation it would be orphaned. The honest mathlib unit is a **whole nonarchimedean-`log`/`exp` development** (the `padicLog`/`padicExp` defs + the open ball `InExpBall` + summability `summable_padicLog_terms`/`summable_padicExp_terms` + the isometries `norm_padicLog`/`norm_padicExp_sub_padicExp` + the functional equations `padicLog_mul`/`padicExp_add` + the `log`/`exp` inversion), with this strict-domination estimate as one supporting lemma — and whether to undertake that BIG, multi-decl upstreaming is a human/community decision. (ii) **Packaging within such a development is a taste call.** In the literature this is *never a named lemma*; a mathlib reviewer might want it public (a named per-term strict bound), folded into the `norm_padicLog` proof as a `have`/`private` step, or restated against a general nonarchimedean-`log` object / in valuation terms rather than the concrete `(−1)ᵐ(m+1)⁻¹yᵐ⁺¹` family — and the rpow-free `‖·‖^{p−1}<p⁻¹` encoding (ideal for *this* project) might be re-expressed via `Real.rpow`/valuation in a general setting. The verdict therefore hinges on the upstreaming decision about the p-adic-log machinery as a whole, not on standalone merit — and per the skill, a verdict that hinges on scope + packaging taste is `BORDERLINE-needs-human`, not a self-resolved YES. (**Cost is *not* invoked as the reason** — an EXPENSIVE upstreaming would still be worth doing; the genuine blocker is the human scope/packaging call. Per the verdict gate, "too expensive to generalise/upstream" would itself be a BORDERLINE question, not a downgrade — but that is not the reason here; the lemma is already maximally general and the proof is cheap. The blocker is purely *which* pieces of the missing p-adic-log development become first-class mathlib API.)

**Numbered questions (≤5):**

1. **Scope (governs everything):** Do you intend to upstream the project's p-adic / nonarchimedean **logarithm development** to mathlib as a unit — the `padicLog` definition + the `InExpBall` convergence ball + `summable_padicLog_terms` + the isometry `norm_padicLog` (`‖log x‖ = ‖x−1‖`) + the functional equation `padicLog_mul` + the `exp`/`log` inversion `padicLog_padicExp`/`padicExp_padicLog`? This strict-domination lemma is meaningless without the `padicLog` series, which mathlib does not have, so it must travel *with* that development. (No → this is a permanent project-local helper; drop from mathlib consideration. Yes → go to Q2.)
2. **Packaging (if Q1 = yes):** Should this lemma ship as **first-class public API** (a named per-term strict bound `‖(−1)ᵐ(m+1)⁻¹yᵐ⁺¹‖ < ‖y‖`), or be **folded into the `norm_padicLog` proof** as a local `have`/`private` step? Its only role is supplying the `∀ n` per-term family to that isometry's tail estimate (K = 1).
3. **Generality of the named object (if Q1 = yes):** Within a general mathlib nonarchimedean-`log` namespace, do you want it stated against a **general `expSeries`/`logSeries`-style object** (a nonarchimedean-`log` API), or kept against the concrete `(−1)ᵐ(m+1)⁻¹•yᵐ⁺¹` term family as here? And keep the **rpow-free `‖·‖^{p−1}<p⁻¹` encoding**, or restate the ball via `Real.rpow` / valuation in the general setting (the form a reviewer might expect)?
4. **Ball choice (if Q1 = yes):** This lemma is stated on the **exp** ball (`InExpBall`, where log inverts exp — the project's need), whereas the literature log isometry lives on the full log ball `‖y‖<1` (or `1+m^r`). For a mathlib contribution, do you want the bound on the **exp ball** (as here, feeding the `exp`/`log` inversion), the **full log ball `‖y‖<1`**, or **both**?
5. **Batch with the twins:** Should this PR be **co-developed with the exponential analogue `norm_factorial_inv_smul_pow_sub_lt` and the `_le` companion `norm_succ_inv_smul_pow_le`** (both also BORDERLINE here for the same reason) as one nonarchimedean-`exp`/`log` contribution series, rather than as isolated lemmas?

**Next action:** user answers Q1–Q5; re-run `/mathlibable PadicLFunctions.norm_succ_inv_smul_pow_lt` — ideally **together with `/mathlibable PadicLFunctions.padicLog`** (and the exp twin), since the def's upstreaming verdict governs this lemma's. Likely resolutions:
  - **"Upstream the p-adic-log development"** → flips to **YES-add-as-is** (the lemma is maximally general — indeed below the literature's hypotheses — sharp, NOT-COMPOSABLE, and genuinely missing; it qualifies cleanly *once* the `padicLog` def + isometry it underpins are also being upstreamed), shipped as part of the nonarchimedean-`log`/`exp` PR series to `Mathlib/NumberTheory/Padics/`; packaging (public vs. folded; concrete vs. general; exp-ball vs. log-ball) per the answers to Q2–Q4.
  - **"Keep project-local"** → drop from mathlib consideration; it stays fit-for-purpose infrastructure feeding `norm_padicLog` (the RJW Lem 5.14 log isometry).

---

## Next step

User answers the five numbered questions above; re-run `/mathlibable PadicLFunctions.norm_succ_inv_smul_pow_lt` (preferably alongside `/mathlibable PadicLFunctions.padicLog` and the exponential twin `/mathlibable PadicLFunctions.norm_factorial_inv_smul_pow_sub_lt`, since this lemma's verdict is governed by the upstreaming decision on the `padicLog` definition + isometry it underpins) to resolve to either **`YES-add-as-is`** (upstream the nonarchimedean-log/exp development as a unit; this lemma ships with it as a maximally-general strict per-term tail-domination bound — the engine of the log isometry `norm_padicLog`) or **drop-from-consideration** (keep as project-local infrastructure for the RJW Lem 5.14 log isometry).
