# `/mathlibable` report — `PadicLFunctions.norm_factorial_inv_smul_pow_sub_lt`

**Final verdict: `BORDERLINE-needs-human`** (scope/grain call — the lemma is a true, maximally-general, missing-from-mathlib p-adic estimate, but it is inseparable from a p-adic/nonarchimedean **exponential development that mathlib does not have**; whether to upstream that whole cluster is a human/community decision. See Phase 7.)

---

### Baseline (Phase 0)

- lake build:               **build not re-run** (stale/slow per task BUILD NOTE); **reasoned from source** — Phase-0 fallback. All mathlib building blocks used by the proof were verified to exist in the pinned tree at `.lake/packages/mathlib/Mathlib/`.
- decl `PadicLFunctions.norm_factorial_inv_smul_pow_sub_lt`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:141`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  *The p-adic exponential and logarithm (RJW Lem 5.14)* — `exp(x)=∑xⁿ/n!` converges and is an **isometry** on the open ball `‖x‖ < p^{−1/(p−1)}`; `log(1+y)` inverts it; realises RJW Lemma 5.14 (Cassels §12 / Washington §5.1).

---

### Statement (Phase 1)

`norm_factorial_inv_smul_pow_sub_lt` is a theorem stating the following:

> Let `L` be a complete ultrametric normed field that is a normed `ℚ_[p]`-algebra. Fix two points `x, y` in the **open** convergence ball of the `p`-adic exponential (`‖x‖^{p−1} < p⁻¹` and `‖y‖^{p−1} < p⁻¹`, i.e. `‖·‖ < p^{−1/(p−1)}`) with `x ≠ y`. Then for every `m ≥ 2` the `m`-th term of the difference series `exp(x) − exp(y) = ∑ (xⁿ − yⁿ)/n!` is **strictly** smaller in norm than the linear (`m = 1`) term:
> `‖(m!)⁻¹·(xᵐ − yᵐ)‖ < ‖x − y‖`.

This is the **strict tail-domination** step behind the headline fact that `exp` is an isometry on its convergence ball: once every term beyond the linear one is strictly dominated, the ultrametric "norm of a sum equals the max when the maxes are distinct" gives `‖exp(x) − exp(y)‖ = ‖x − y‖`. The strictness is genuinely a property of the **open** ball (on the closed boundary the `p`-power term would only be `≤`, not `<`). Specialising to `y = 0` recovers the textbook per-term statement `‖xᵐ/m!‖ < ‖x‖` for `m ≥ 2`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue prime.
- `{L : Type*}`, `[NormedField L]`, `[NormedAlgebra ℚ_[p] L]`, `[IsUltrametricDist L]` — a nonarchimedean normed field over `ℚ_[p]`. (Note: `[CompleteSpace L]` is **omitted** for this lemma via `omit [CompleteSpace L]` — the per-term inequality needs no completeness.)
- `{x y : L}` — the two evaluation points.
- `{m : ℕ}` — the term index.

Hypotheses (Lean side):
- `(hx : InExpBall p x)`, `(hy : InExpBall p y)` — both points lie in the open convergence ball (`‖·‖^{p−1} < p⁻¹`).
- `(hxy : x ≠ y)` — distinctness (so `‖x − y‖ > 0`, making the strict bound meaningful).
- `(hm : 2 ≤ m)` — the term is genuinely beyond the linear one.

Conclusion (math): the `m`-th difference term is strictly norm-dominated by the linear difference `x − y`.

Conclusion (Lean): `‖(m.factorial : ℚ_[p])⁻¹ • x ^ m - (m.factorial : ℚ_[p])⁻¹ • y ^ m‖ < ‖x - y‖`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper lemma in the decomposition cluster **R5.E** (E3 attack [3], per the docstring) feeding the isometry theorem `norm_padicExp_sub_padicExp`. It is not a named/main result and introduces no structure; it is the strict per-term domination estimate. The *headline* result is the isometry it serves.

(Note: literature width was EXHAUSTIVE regardless — all nine channels run below. BIG/SMALL is for the report's framing only.)

### One-line check (Phase 2b)

Body line count: ~55 substantive lines (a multi-`calc` proof: a geometric `geom_sum₂_mul` factorisation under the ultrametric `norm_sum_le_of_forall_le_of_nonneg`, then a four-step `(p−1)`-power `calc` ending in `lt_of_pow_lt_pow_left₀`).
One-liner verdict: **n/a — kind is `theorem`, not a `def`.** The defeq/diamond/API exemptions apply only to definitions; this is a proposition.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form: isometry + strict domination) | "p-adic exponential isometry on convergence ball p^{-1/(p-1)} proof strict domination" | **yes** | `exp : 𝔻 → 1+𝔻` bijection on `‖·‖ < p^{−1/(p−1)}`; "**\|xⁿ/n!\|_p < \|x\|_p for n ≥ 2** … strict domination of higher-order terms" | Direct hit. Berkeley `Upn_cyclic.pdf`; Cambridge `jat58/all.pdf`; Wikipedia *P-adic exponential function*; Keith Conrad / Jack Thorne notes. The `< ‖x‖` per-term statement (our `y=0` case) is stated **verbatim**. |
| 2 | WebSearch (general / named-source form) | "nonarchimedean exponential isometry open ball norm preserving Cassels local fields Washington cyclotomic" | yes | ultrametric `‖·‖` field structure; `exp`/`log` on `1+𝔪`; **Cassels *Local Fields*** cited as the foundational source | Columbia CFT notes; Warwick `local_fieldstcc.pdf` (Browning); arXiv 2105.00516 (ultrametric/Ulam). Confirms the Cassels §12 / Washington §5.1 lineage the file cites; the isometry is treated as standard, uncontested plumbing. |
| 3 | WebSearch (difference form / aliases: injective isometry) | "p-adic exp injective isometry \|exp(x)−exp(y)\|=\|x−y\| higher order terms dominated proof" | **yes** | `‖exp z − 1‖ = ‖z‖` on `𝔻(0,ρ)`, `ρ=p^{−1/(p−1)}`; **"when computing exp(x)−exp(y)=∑(xⁿ−yⁿ)/n!, the higher-order terms get increasingly smaller p-adically … the first-order terms control the overall p-adic distance"** | **Exact match for our *difference* form.** MIT `dav/exp.pdf` *Exponential and logarithm in p-adic fields*; Uchicago REU `Chen,Yuchen.pdf` (Strassman); `numberanalytics` ultrametric guide. The `(xⁿ−yⁿ)/n!` regrouping and "first-order term dominates" is precisely what this lemma formalises. |
| 4 | ChatGPT MCP | (MCP server **not configured** in this environment) — substituted by the three WebSearch queries above, which explicitly requested the standard form, its generality, named sources (Cassels/Washington), and the proof mechanism (strict domination) | yes | as #1–#3 | n/a for the MCP tool itself; recorded as substituted. The substitute queries covered "standard form + generality + classical source + historical lineage," the MCP brief. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | n/a | (no `references/` dir; `refs/` absent in this checkout — PDFs are local-only and not present here) | Recorded n/a. The project's own `worklist.json`/decomposition labels the cluster **R5.E** and cites RJW Lem 5.14, Cassels §12, Washington §5.1. |
| 6 | nLab | `ncatlab.org/nlab/show/p-adic+exponential+map` | n/a | **HTTP 404 — no dedicated nLab page** | nLab has no standalone p-adic-exponential entry (verified by fetch); the concept lives under classical p-adic-analysis references, not a categorical nLab page. Consistent with the sibling reports. |
| 7 | nCatLab (categorical) | — | n/a | not a categorical concept | A scalar strict inequality between norms of power-series terms; nothing categorical to look up. |
| 8 | Stacks Project | — | n/a | not an algebraic-geometry concept | p-adic exp convergence / isometry is nonarchimedean analysis, not scheme theory. |
| 9 | MathOverflow / Math.StackExchange | (covered transitively by #1–#3 — the `‖xⁿ/n!‖ < ‖x‖` and isometry facts are textbook, surfaced via the lecture-note hits) | yes | same as #1–#3 | No MO-specific subtlety; the strict-domination argument is standard and uncontested. |
| 10 | recent arXiv (last 5 years) | "p-adic exponentiation Hensel minimality Tate uniformization" (arXiv 2602.16433) + Anderson t-module class formula (2504.03430) | yes | the convergence ball `p^{−1/(p−1)}` and `exp`-isometry remain the standard tool in current work | Confirms the object is still the same textbook gadget in contemporary p-adic analysis; no modern restatement of *this* per-term bound. |

**Protocol pass check:** WebSearch ran **3 distinct queries** at three generality levels (specific isometry+domination form #1; named-source/general nonarchimedean form #2; the *difference* `exp(x)−exp(y)` injective-isometry form #3) — all three hit, #3 matching our exact statement. ChatGPT MCP unavailable → explicitly substituted. Local refs checked (n/a, absent). nLab checked (404, no page). nCatLab / Stacks recorded n/a with reasons. MathOverflow covered transitively. Recent arXiv (2602.16433, 2504.03430) checked. All nine channels addressed.

### Literature summary (Phase 3)

Concept identified as: **the strict per-term domination underlying the isometry of the `p`-adic exponential on its open convergence ball** — i.e. for `‖x‖, ‖y‖ < p^{−1/(p−1)}` and `m ≥ 2`, `‖(xᵐ − yᵐ)/m!‖ < ‖x − y‖`, the engine of `‖exp x − exp y‖ = ‖x − y‖`.
Sources agree on the standard form: **yes** — the per-term statement `‖xⁿ/n!‖_p < ‖x‖_p` (n ≥ 2) and the isometry `‖exp x − 1‖ = ‖x‖` / `‖exp x − exp y‖ = ‖x − y‖` are textbook (Conrad/Thorne, MIT `dav/exp.pdf`, Cassels *Local Fields* §12, Washington §5.1, Wikipedia). The *difference*-series regrouping `∑(xⁿ−yⁿ)/n!` with "first-order term dominates" is stated essentially verbatim in the MIT notes (Phase-3 #3).
Most general standard form: the difference statement `‖(xᵐ−yᵐ)/m!‖ < ‖x−y‖` for `m ≥ 2` over a complete nonarchimedean field with `‖·‖` extending the `p`-adic norm — exactly the project's form (which even drops completeness for this step).
Generality dimensions where the literature varies:
  - **Ambient field**: most sources state it over `ℚ_p` or `ℂ_p`; the modern/general form (and the project's) is any complete ultrametric `ℚ_[p]`-algebra field. The project is *already at* the general form.
  - **`y=0` vs. difference**: the per-term `‖xᵐ/m!‖ < ‖x‖` (most common textbook phrasing) is the `y=0` specialisation of the project's bilinear difference form.
  - **Encoding**: literature uses valuations / `Real.rpow` radius `p^{−1/(p−1)}`; the project uses the rpow-free `‖·‖^{p−1} < p⁻¹` packaging (`InExpBall`) for ultrametric `pow`-monotonicity.
Disagreement with the literature: **none.** The mathematics is exactly the standard strict-domination step; the project re-packages it rpow-free and over a general ultrametric `ℚ_[p]`-algebra.

---

### Generality analysis — `norm_factorial_inv_smul_pow_sub_lt`

Literature-standard form (from Phase 3): for `‖x‖, ‖y‖ < p^{−1/(p−1)}` and `m ≥ 2`, `‖(xᵐ − yᵐ)/m!‖ < ‖x − y‖`, over a complete nonarchimedean field whose norm extends `|·|_p`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `p : ℕ`, `[Fact p.Prime]` | a rational prime | a rational prime | NO | The radius `p^{−1/(p−1)}` and the Legendre bound are intrinsically about a prime `p`. |
| 2 | `L` field: `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L]` | complete ultrametric normed `ℚ_[p]`-algebra **field** | a complete nonarchimedean field with `‖·‖` extending `|·|_p` (e.g. `ℚ_p`, `ℂ_p`, finite extensions) | NO (this *is* the general form) | The lemma is stated at the maximally-general ambient already; literature often restricts to `ℚ_p`/`ℂ_p`. The proof uses ultrametricity essentially (`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`). |
| 3 | `[CompleteSpace L]` | **omitted** (`omit [CompleteSpace L] in`) | usually assumed (for the series to exist) | already dropped | The per-term inequality needs no completeness — the project correctly omits it, a *strengthening* over the textbook framing where exp is assumed to converge. |
| 4 | `(hx hy : InExpBall p ·)` | open ball `‖·‖^{p−1} < p⁻¹` | open ball `‖·‖ < p^{−1/(p−1)}` | NO | Strictness is a property of the **OPEN** ball (the docstring flags this); on the boundary the `p`-power factor `(p·rᵖ⁻¹)` would be `= 1`, killing strictness. Cannot weaken to closed ball. |
| 5 | `(hxy : x ≠ y)` | `x ≠ y` | needed for the RHS `‖x−y‖ > 0` | NO | With `x = y` both sides are `0`, and `0 < 0` is false; the hypothesis is necessary for the *strict* `<`. |
| 6 | `(hm : 2 ≤ m)` | `m ≥ 2` | `m ≥ 2` | NO | For `m = 1` the term equals the linear term (`= ‖x−y‖`, not `<`); for `m = 0` it is `0`. `m ≥ 2` is exactly the range where strict domination holds. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.** It is stated over an arbitrary complete ultrametric normed `ℚ_[p]`-algebra field (broader than the textbook `ℚ_p`/`ℂ_p`), it even drops `[CompleteSpace L]`, and every numeric hypothesis (`open` ball, `x ≠ y`, `m ≥ 2`) is exactly the sharp range where the strict inequality holds.
Number of weakening opportunities found: **0**.
Proposed restatement: none for generality. (The only cosmetic move is `‖·‖^{p−1}<p⁻¹` ↔ `Real.rpow` ball — see Phase 4c; it is a packaging choice, not a weakening.)
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | — | All ambient hypotheses are already typeclasses; the only bundled `Prop`s (`InExpBall`) are the genuine ball-membership data. |
| 2 | sequences/metric → filters/topology? | no | — | This is a single fixed-`m` scalar inequality; there is no limit/convergence here to filter-ise (that lives in the downstream `summable_*`/`norm_padicExp_sub_padicExp`). |
| 3 | construct an object → universal property? | no | — | No object constructed; it is an estimate. |
| 4 | set-with-closure → bundled substructure? | no | — | n/a. |
| 5 | vector-space/metric/field-specific → weaken typeclass? | no (already general) | — | Already stated over a general ultrametric `ℚ_[p]`-algebra field; cannot weaken the field structure (ultrametricity is used). |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/ordered structure? | no | — | The index `m` is the power-series term number; intrinsically ℕ, and the bound holds only for `m ≥ 2`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.**
One-line reason: This is a concrete strict scalar inequality between norms of two power-series terms; there is no preamble to typeclass-ify, no construction to characterise, and no sequence/metric notion to filter-ise (the convergence machinery is one layer up). The only "reformulation" is the rpow-free `‖·‖^{p−1}<p⁻¹` ↔ `Real.rpow`-radius packaging — a presentation choice within a hypothetical mathlib nonarchimedean-`exp` namespace, not a Bourbaki-2.0 organisational improvement. The real organisational lever is one layer down: a nonarchimedean-`exp` API that **mathlib lacks entirely** (Phase 5), which is the scope question Phase 7 defers.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (introduces no definitional equalities or typeclass-search paths).

---

### Mathlib search-status: `norm_factorial_inv_smul_pow_sub_lt`

[A] Lean-Finder       "p-adic exp isometry per-term strict bound", "‖(xⁿ−yⁿ)/n!‖ < ‖x−y‖"   n/a: Lean-Finder web service not reachable from this sandboxed environment — substituted by [D] grep + [E] name-pattern over the pinned mathlib tree.
[B] Loogle            `‖_ • _ ^ _ - _ • _ ^ _‖ < ‖_ - _‖`, `‖(Nat.factorial _ : ℚ_[_])⁻¹ • _‖ < _`   n/a: Loogle web service not reachable — substituted by [D] type-shape grep below.
[C] LeanSearch        "p-adic exponential isometry", "norm of power series term strictly less than linear term"   n/a: LeanSearch web service not reachable — substituted by [D]/[E].
[D] Grep mathlib src  `padicExp`, `expSeries.*Padic`, `IsUltrametricDist.*exp`, `geom_sum₂_mul`, `abs_pow_sub_pow_le`, `norm_pow_sub_pow`, `pow_sub_pow.*norm`   **partial hits only** — see below.
[E] Name pattern      `norm_factorial`, `*_smul_pow_sub*`, `norm_pow_sub*`, `exp.*isometr*`, `padicExp*`   hits only on **project-local** names; nothing in mathlib.

Searched for both:
  - the user's current form `‖(m!)⁻¹•(xᵐ−yᵐ)‖ < ‖x−y‖` — **no hit** anywhere in mathlib.
  - the literature-standard isometry/per-term forms (`‖exp x − exp y‖ = ‖x−y‖`, `‖xᵐ/m!‖ < ‖x‖`) and the underlying `‖xⁿ−yⁿ‖ ≤ ‖x−y‖·rⁿ⁻¹` factorisation — **no packaged hit**; see building blocks.

Building blocks confirmed present in mathlib (each used by the proof):
  - `geom_sum₂_mul` — `Mathlib/Algebra/Ring/GeomSum.lean:306` (the identity `(∑ᵢ xⁱyⁿ⁻¹⁻ⁱ)·(x−y) = xⁿ−yⁿ`; also `Commute.geom_sum₂_mul`:182). **The raw algebraic factorisation only.**
  - `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` — present (used at `Mathlib/NumberTheory/Padics/MahlerBasis.lean:126`); the ultrametric "max" bound on `‖∑ …‖`.
  - `lt_of_pow_lt_pow_left₀` — `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:699`; `pow_le_pow_left₀`, `pow_le_pow_of_le_one` (`…Basic.lean:393`), `mul_lt_of_lt_one_right` (`…Basic.lean:343`) — all standard ordered-field lemmas.
  - `norm_factorial_inv_pow_le` — **PROJECT-LOCAL** (`PadicExp.lean:69`, the inverted Legendre bound), itself **absent from mathlib** (its own report is BORDERLINE). This is the substantive p-adic input.

Adjacent (different) facts in mathlib — checked and rejected:
  - `abs_pow_sub_pow_le` — `Mathlib/Algebra/Order/Ring/Abs.lean:189`: bounds `|aⁿ − bⁿ|` in an **ordered ring** by `n·max(|a|,|b|)ⁿ⁻¹·|a−b|`. This is the **absolute-value / ordered-ring** analogue, `≤` (not `<`), with a spurious `n` factor and **no factorial weighting** — it is *not* the normed-field, factorial-weighted **strict** bound this lemma states. Cannot be used directly.
  - `NormedSpace.exp` / `expSeries` (`Mathlib/Analysis/SpecialFunctions/Exponential.lean`, `CStarAlgebra/Exponential.lean`) — the **archimedean** Banach-algebra exponential; `expSeries_radius_eq_top` (converges everywhere). No `IsUltrametricDist` support, no per-term strict-domination bound, and crucially the complex/real exp is **not** an isometry — the opposite regime.
  - **No `padicExp` / nonarchimedean exponential exists anywhere in mathlib** (`grep -rln "padicExp|PadicExp|nonarchimedean.*exp|expPadic" Mathlib/` is **empty**). The entire supporting API — `InExpBall`, `summable_padicExp_terms`, the isometry, the functional equation — is genuinely absent.

Concluded: **"not in mathlib (all substituted methods exhausted, plus the literature-standard isometry/per-term forms)."** Mathlib has the raw factorisation identity (`geom_sum₂_mul`), the ultrametric sum bound, and an `abs`-version of a *coarser* power-difference bound — but **not** the factorial-weighted, normed-field, **strict** per-term domination this lemma states, and **no p-adic exponential** for it to belong to.

---

### Call sites — `norm_factorial_inv_smul_pow_sub_lt`

Internal use count: **K = 1** (within `PadicLFunctions`, not counting the declaration itself).
External-to-file callers: **0** distinct other files.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| PadicExp.lean:227 | `norm_factorial_inv_smul_pow_sub_lt p hx hy hxy (by omega)` — inside `norm_padicExp_sub_padicExp` (the headline isometry `‖exp x − exp y‖ = ‖x − y‖`), supplying the per-term strict bound `hterm` that feeds the ultrametric `norm_tsum_le_of_forall_le` tail estimate |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `norm_factorial_inv_smul_pow_sub_lt`?):
  - The structurally analogous **log** lemma `norm_succ_inv_smul_pow_lt` (`PadicExp.lean:396`) proves the same kind of strict tail-domination `‖(−1)ᵐ(m+1)⁻¹•yᵐ⁺¹‖ < ‖y‖` for the logarithm series, and it re-runs the same `norm_*_inv_pow_le` + `pow_le_pow_of_le_one` + `lt_of_pow_lt_pow_left₀` pattern rather than calling this lemma — because the `xᵐ−yᵐ` difference vs. single-`yᵐ⁺¹` shapes differ. So the *strict-domination pattern* recurs (once for exp-difference here, once for log), each tied to a different term shape. **Not a literal re-derivation of this exact lemma.**

What the pattern tells us: **K = 1** internal use, no inline re-derivation of this exact lemma. Per the Phase-6.0.1 table, `K = 1` ("possibly the wrong abstraction — could be inlined") nominally *leans NO-composable*. But the single consumer (`norm_padicExp_sub_padicExp`) calls it inside a `∀ n` quantifier (`hterm := fun n => norm_factorial_inv_smul_pow_sub_lt …`), so it is genuinely a *parametrised family* of strict bounds, not a one-off `have` — extracting it as a named lemma is the natural factoring (the alternative is a ~55-line `have` block inside the isometry proof). The composability question therefore turns on **mathlib composability** (Phase 6), not on the local call count.

---

### Composition check (Phase 6)

Can `norm_factorial_inv_smul_pow_sub_lt` be derived **from mathlib** in ≤3 chained calls?

Attempt 1 — direct mathlib one-liner:
  - Sketch: there is no single mathlib lemma (or 2–3 chain) producing `‖(m!)⁻¹•(xᵐ−yᵐ)‖ < ‖x−y‖`. The nearest, `abs_pow_sub_pow_le`, is the wrong setting (ordered-ring `abs`, `≤`, no factorial, extra `n` factor).
  - Result: **fails** — no direct mathlib statement.

Attempt 2 — composing from mathlib primitives (the actual proof skeleton):
  - Sketch: (i) `geom_sum₂_mul` to factor `xᵐ − yᵐ = (∑ᵢ xⁱyᵐ⁻¹⁻ⁱ)(x−y)`; (ii) bound `‖∑ᵢ xⁱyᵐ⁻¹⁻ⁱ‖ ≤ rᵐ⁻¹` via `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` + per-summand `pow_le_pow_left₀` (a ~10-line nested `calc`); (iii) multiply by the **project-local** `norm_factorial_inv_pow_le` (Legendre bound); (iv) collapse the `(p−1)`-power `calc` through `pow_le_pow_of_le_one` and `mul_lt_of_lt_one_right`, using `hT1 : p·rᵖ⁻¹ < 1` (itself derived from `InExpBall` + `mul_inv_cancel₀`); (v) `lt_of_pow_lt_pow_left₀` to remove the `(p−1)` power.
  - Decls used: `geom_sum₂_mul`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `pow_le_pow_left₀`, `norm_factorial_inv_pow_le` **(project-local)**, `pow_le_pow_of_le_one`, `mul_lt_of_lt_one_right`, `lt_of_pow_lt_pow_left₀`, plus `norm_smul`/`norm_inv`/`mul_pow`/`ring`.
  - Result: **fails the ≤3-call bar by a wide margin** — this is a ~55-line, multi-`calc` proof with `geom_sum₂_mul` rewriting, an ultrametric sum estimate, `ring`, and `linarith`-style collapses. By the Phase-6 heuristics ("anything requiring `rw […]; … ring`/multiple `have`s with nontrivial reasoning is a proof, not a composition") this is unambiguously a **proof**. Moreover its substantive p-adic input `norm_factorial_inv_pow_le` is itself **not in mathlib**.

Conclusion: **NOT-COMPOSABLE from mathlib.** No ≤3-call mathlib derivation exists; the genuine proof is a multi-step nonarchimedean argument, and even that routes through a project-local Legendre bound absent from mathlib. The `abs_pow_sub_pow_le` analogue is the wrong regime and cannot be substituted.

---

## Verdict: `PadicLFunctions.norm_factorial_inv_smul_pow_sub_lt`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the lemma is the **strict per-term/difference domination** behind the `p`-adic-exp **isometry** — `‖(xᵐ−yᵐ)/m!‖ < ‖x−y‖` for `m ≥ 2`. Stated essentially verbatim in the literature (MIT `dav/exp.pdf` #3: "exp(x)−exp(y)=∑(xⁿ−yⁿ)/n! … first-order term controls the p-adic distance"; the `‖xⁿ/n!‖<‖x‖`, `n≥2` per-term form in #1; Cassels §12 / Washington §5.1 lineage in #2). Textbook, uncontested — and **never isolated as a standalone named lemma**; it is always an inline step en route to the isometry.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (Phase 4b — stated over a general complete ultrametric `ℚ_[p]`-algebra field, completeness even dropped, all numeric hypotheses sharp); **no modern-idiom reformulation** (Phase 4c — the only lever is the absent nonarchimedean-`exp` namespace, one layer down).
- Mathlib search (Phase 5): **not in mathlib** — no `padicExp`/nonarchimedean exponential at all; no factorial-weighted strict power-difference norm bound; the closest, `abs_pow_sub_pow_le`, is the wrong (ordered-ring `abs`, `≤`) regime; the substantive input `norm_factorial_inv_pow_le` is itself project-local and absent.
- Composition check (Phase 6): **NOT-COMPOSABLE** — a ~55-line multi-`calc` nonarchimedean proof, far past the ≤3-call bar, routing through a project-local Legendre bound.
- Call sites (Phase 6.0): **K = 1** (`norm_padicExp_sub_padicExp`, the isometry), used as a parametrised `∀ n` family — no inline re-derivation of this exact lemma.

**Rationale (1–2 paragraphs):**

On its own technical merits this reads like a strong YES-add-as-is: it is a *true, maximally-general (Phase 4b), constant-tight, sorry-free, NOT-COMPOSABLE (Phase 6), genuinely-missing-from-mathlib (Phase 5)* p-adic estimate whose mathematical content is squarely textbook (Phase 3, MIT/Conrad/Cassels). It is decidedly **not** any NO bucket: mathlib has no analogue (the only power-difference bound, `abs_pow_sub_pow_le`, is the wrong ordered-ring/`abs`/`≤` regime, and mathlib's only `exp` is the *archimedean* one, which is **not** an isometry), and it cannot be inlined as a ≤3-call composition.

What blocks a clean YES is **not** novelty or generality but a **scope/grain judgment the skill must defer** — exactly as for its siblings `norm_factorial_inv_smul_pow_le`, `summable_padicExp_terms`, and `norm_padicExp_sub_one_sub_self_le` (all BORDERLINE in this ledger). (i) **The lemma is inseparable from a definition layer mathlib does not have.** Its entire purpose is to make `norm_padicExp_sub_padicExp` — the isometry of `padicExp` — go through; but mathlib has **no** p-adic/nonarchimedean exponential, no `InExpBall` convergence-ball API, and the lemma even *names* `ℚ_[p]`-factorials and the project-local Legendre bound `norm_factorial_inv_pow_le`. Upstreamed in isolation it would be orphaned. The honest mathlib unit is a **whole nonarchimedean-`exp` development** (the `padicExp` def + the open ball + summability + the isometry `norm_padicExp_sub_padicExp`/`norm_padicExp_sub_one` + the functional equation `padicExp_add` + log + inversion), with this strict-domination estimate as one supporting lemma — and whether to undertake that BIG, multi-decl upstreaming is a human/community decision. (ii) **Packaging within such a development is a taste call.** In the literature this is *never a named lemma*; a mathlib reviewer might want it public (a per-term/difference strict bound), folded into the isometry proof as a `have`, or restated against a general `expSeries`-style nonarchimedean object rather than the concrete `(m!)⁻¹•(xᵐ−yᵐ)` family — and the rpow-free `‖·‖^{p−1}<p⁻¹` encoding (ideal for *this* project) might be re-expressed via `Real.rpow`/valuation in a general setting. The verdict therefore hinges on the upstreaming decision about the p-adic-exp machinery as a whole, not on standalone merit — and per the skill, a verdict that hinges on scope + packaging taste is `BORDERLINE-needs-human`, not a self-resolved YES. (Cost is *not* invoked as the reason — an EXPENSIVE upstreaming would still be worth it; the genuine blocker is the human scope/packaging call.)

**Numbered questions (≤5):**

1. **Scope (governs everything):** Do you intend to upstream the project's p-adic / nonarchimedean **exponential development** to mathlib as a unit — the `padicExp` definition + the `InExpBall` convergence ball + `summable_padicExp_terms` + the isometry `norm_padicExp_sub_padicExp`/`norm_padicExp_sub_one` + the functional equation `padicExp_add` + the `log` and inversion? This strict-domination lemma is meaningless without the `exp` series, which mathlib does not have, so it must travel *with* that development. (No → this is a permanent project-local helper; drop from mathlib consideration. Yes → go to Q2.)
2. **Packaging (if Q1 = yes):** Should this lemma ship as **first-class public API** (a named per-term/difference strict bound `‖(xᵐ−yᵐ)/m!‖ < ‖x−y‖`), or be **folded into the `norm_padicExp_sub_padicExp` proof** as a local `have`/`private` step? Its only role is supplying the `∀ n` per-term family to that isometry's tail estimate.
3. **Generality of the named object (if Q1 = yes):** Within a general mathlib nonarchimedean-`exp` namespace, do you want it stated against a **general `expSeries`-style object** (a `PadicExp`/nonarchimedean-`exp` API), or kept against the concrete `(m!)⁻¹•(xᵐ−yᵐ)` family as here? And keep the **rpow-free `‖·‖^{p−1}<p⁻¹` encoding**, or restate the ball via `Real.rpow` / valuation in the general setting?
4. **`y=0` vs. difference (if Q1 = yes):** The literature's most common phrasing is the `y=0` per-term form `‖xᵐ/m!‖ < ‖x‖` (`m ≥ 2`); this lemma proves the stronger bilinear difference form (with the `y=0` case as a corollary). For mathlib, do you want the **difference form** (directly feeds the isometry, as here) or **both** (the per-term form as a named corollary)?

**Next action:** user answers Q1–Q4; re-run `/mathlibable PadicLFunctions.norm_factorial_inv_smul_pow_sub_lt` — ideally **together with `/mathlibable PadicLFunctions.padicExp`**, since the def's upstreaming verdict governs this lemma's. Likely resolutions:
  - **"Upstream the p-adic-exp development"** → flips to **YES-add-as-is** (the lemma is maximally general, constant-tight, NOT-COMPOSABLE, and genuinely missing — it qualifies cleanly *once* the `padicExp` def it underpins is also being upstreamed), shipped as part of the nonarchimedean-`exp` PR series to `Mathlib/NumberTheory/Padics/`; packaging (public vs. folded; concrete vs. general-`expSeries`; difference-only vs. with per-term corollary) per the answers to Q2–Q4.
  - **"Keep project-local"** → drop from mathlib consideration; it stays fit-for-purpose infrastructure feeding `norm_padicExp_sub_padicExp` (the RJW Lem 5.14 isometry).

---

## Next step

User answers the four numbered questions above; re-run `/mathlibable PadicLFunctions.norm_factorial_inv_smul_pow_sub_lt` (preferably alongside `/mathlibable PadicLFunctions.padicExp`, since this lemma's verdict is governed by the upstreaming decision on the `padicExp` definition it underpins) to resolve to either **`YES-add-as-is`** (upstream the nonarchimedean-exp development; this lemma ships with it as a maximally-general strict per-term domination bound — the engine of the exp isometry) or **drop-from-consideration** (keep as project-local infrastructure for the RJW Lem 5.14 isometry `norm_padicExp_sub_padicExp`).
