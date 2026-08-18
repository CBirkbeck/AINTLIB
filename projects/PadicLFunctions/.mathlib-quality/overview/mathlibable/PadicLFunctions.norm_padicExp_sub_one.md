# `/mathlibable` report — `PadicLFunctions.norm_padicExp_sub_one`

**Final verdict: `BORDERLINE-needs-human`**

---

### Baseline (Phase 0)

- lake build:               build not re-run (stale/slow per task note); reasoned from source — the file elaborates as part of `main`, and the target + its dependencies were read directly from source (Phase 0 fallback).
- decl `PadicLFunctions.norm_padicExp_sub_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:259`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=Σ xⁿ/n!` converges on the open ball `‖x‖ < p^{-1/(p-1)}` of a nonarchimedean complete normed `ℚ_p`-algebra field and **is an isometry there**; the log inverts it on matched balls. This theorem is the isometry's headline corollary `‖exp x − 1‖ = ‖x‖` (decomposition node E3).

---

### Statement (Phase 1)

`norm_padicExp_sub_one` is a **theorem** stating the following:

> Let `L` be a complete nonarchimedean (ultrametric) normed field that is a normed `ℚ_p`-algebra,
> and let `padicExp p` denote the p-adic exponential `exp(x) = Σ_{n≥0} xⁿ/n!`. For every `x` in the
> open convergence ball `‖x‖^{p−1} < p⁻¹` (equivalently `‖x‖ < p^{-1/(p-1)}`), the exponential is
> norm-preserving relative to `1`:
> `‖exp(x) − 1‖ = ‖x‖`.

This is **the** canonical "p-adic exponential is an isometry" statement, in its `exp(0)=1` headline
form: on the disc of convergence, `exp` moves a point `x` away from `1` by exactly `‖x‖`. It is the
`y = 0` specialisation of the two-point isometry `‖exp x − exp y‖ = ‖x − y‖`
(`norm_padicExp_sub_padicExp`, `PadicExp.lean:202`), using `exp(0) = 1`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime.
- `L : Type*`, `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — a
  complete ultrametric normed `ℚ_p`-algebra field (the general nonarchimedean setting; subsumes `ℂ_p`
  and finite extensions of `ℚ_p`; instantiated downstream at `L = ℚ_[p]`).

Hypotheses (Lean side):
- `hx : InExpBall p x` — i.e. `‖x‖^{p−1} < p⁻¹`, the rpow-free spelling of `‖x‖ < p^{-1/(p-1)}`, the
  exponential's exact radius of convergence.

Conclusion (math): on the disc of convergence the p-adic exponential is an isometry (here in its
`‖exp x − 1‖ = ‖x‖` headline form).

Conclusion (Lean): `‖padicExp p x - 1‖ = ‖x‖`.

**Proof shape (2 lines).** Establish `h0 : InExpBall p (0 : L)` (the origin lies in the ball, since
`‖0‖^{p−1} = 0 < p⁻¹`), then `simpa using norm_padicExp_sub_padicExp p hx h0` — i.e. instantiate the
two-point isometry at `y = 0` and let `simp` rewrite `padicExp p 0 = 1` (via the `@[simp]` lemma
`padicExp_zero`) and `x − 0 = x`. The entire mathematical content lives in the parent
`norm_padicExp_sub_padicExp`; this theorem is its `y=0` specialisation.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (governed by a BIG object)
Reason: as a *declaration* it is a corollary/specialisation (decomposition node E3) of the two-point
isometry — not a `def`/structure, not a `## Main results` entry. **However**, it is the literature's
*named, canonical* p-adic-exp fact ("exp is an isometry"), and it is a property of a BIG object the
project introduces and mathlib lacks — `PadicLFunctions.padicExp`. So while the declaration is SMALL,
its mathlib fate is tied to the BIG `padicExp` development (same governing decision as its siblings
`summable_padicExp_terms` and `norm_padicExp_sub_one_sub_self_le`, both `BORDERLINE`).

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-liner check **n/a** (one-line note).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | p-adic exponential isometry `\|exp(x)−1\|` norm equals `\|x\|` convergence ball                          | yes  | `\|e^t − 1\| = \|t\|` on `D_p`; "the p-adic exponential series preserves distances" | Wikipedia "P-adic exponential function"; MIT 18.785 PS10; MIT `exp.pdf`; Montréal Appendix 16; Cambridge/Thorne notes |
|  2 | WebSearch (general / disc form)  | p-adic exponential isometry on disc of convergence `p^{-1/(p-1)}` norm-preserving                        | yes  | isometry on the disc `\|x\| < p^{-1/(p-1)}`; "the p-adic exponential map is an isometry on its domain of convergence" | Wikipedia; Thorne notes; uchicago REU (Chen); arXiv 1912.10411 "p-adic metric preserving functions" |
|  3 | WebSearch (named-after / source / aliases) | Conrad "Infinite series in p-adic fields" exponential isometry `\|exp(x)−1\|=\|x\|`            | **yes (verbatim)** | **"if t ∈ Dp then \|e^t − 1\| = \|t\|, and for x and y in Dp, \|e^x − e^y\| = \|x − y\|"** — i.e. BOTH the target's form AND its two-point parent are stated as named facts | **K. Conrad, "Infinite Series in p-Adic Fields"** (kconrad.math.uconn.edu) — the project's-circle canonical reference; "a striking contrast with real analysis is that the p-adic exponential series preserves distances" |
|  4 | ChatGPT MCP                      | (intended: "standard form of the p-adic exp isometry `\|exp x−1\|=\|x\|`, its generality, history")     | n/a  | —                                | ChatGPT MCP server (`plugin:mathlib-quality:chatgpt-math`) present in config but **fails to connect** in this environment (its command points at `/home/chris/.claude/...`, a different machine; `claude mcp list` → "Failed to connect"). Recorded n/a; WebSearch (≥3 queries, incl. a verbatim Conrad hit) + the module's own citations (RJW, Cassels §12, Washington §5.1) cover the standard-form + history question. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                | n/a  | (no references dir; no `refs/` symlink) | both directories absent on this machine — recorded n/a. The module docstring's inline citations (RJW TeX 1892–1897 "as stated"; Cassels §12; Washington *Cyclotomic Fields* §5.1) serve as the literature anchor. |
|  6 | nLab                             | p-adic exponential / nonarchimedean analytic function isometry                                          | partial | nLab routes p-adic exp through the general nonarchimedean-analytic-function picture; radius `p^{-1/(p-1)}` and the exp/log isometry are the headline facts | not a categorical concept; no dedicated standalone isometry lemma page |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                | not a categorical concept (a real-valued metric identity on a p-adic field). |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                | not an algebraic-geometry concept (analytic isometry, not scheme/sheaf theory). |
|  9 | MathOverflow / Math.StackExchange| p-adic exp `\|exp(x)−1\|=\|x\|` isometry; p-adic logarithm isometry principal units                     | yes  | community consensus: `\|exp x − 1\| = \|x\|` is **the** standard isometry; log is its inverse isometry `\|log(1+y)\|=\|y\|` on the matched ball | recurring Q&A; never disputed; the isometry is the textbook headline |
| 10 | recent arXiv (last 5 years)      | p-adic exp/log isometry over `C_p` / complete extensions of `ℚ_p`                                       | yes  | arXiv 1904.09850 "On the image of p-adic logarithm on principal units" + arXiv 1912.10411 restate the exp/log isometry on `\|x\|<p^{-1/(p-1)}` over `C_p`; no modern reformulation supersedes it | confirms the isometry is stated over `C_p` / general complete nonarch extensions — exactly the project's generality |

The protocol passed: WebSearch ran **≥3** distinct queries at three generality levels (the specific
`‖exp x−1‖=‖x‖` form / the general "isometry on the disc" form / the named-source Conrad query, which
returned a **verbatim** statement of *both* the target and its two-point parent); ChatGPT MCP recorded
n/a with a concrete reason (server fails to connect, wrong-machine path); local references recorded n/a
with reason (no dir); nLab checked; nCatLab / Stacks recorded n/a with reason; MathOverflow and recent
arXiv each checked (and confirm the `C_p`/general-extension generality).

### Literature summary (Phase 3)

Concept identified as: **"the p-adic exponential is an isometry on its disc of convergence", in the
`exp(0)=1` headline form `‖exp(x) − 1‖ = ‖x‖`** — together with its two-point parent
`‖exp(x) − exp(y)‖ = ‖x − y‖`.

Sources agree on the standard form: **yes — emphatically.** This is the single most-cited distinguishing
feature of p-adic vs. real analysis. K. Conrad ("Infinite Series in p-Adic Fields") states it verbatim:
"if t ∈ Dp then |e^t − 1| = |t|, and for x and y in Dp, |e^x − e^y| = |x − y|." Wikipedia, the MIT
18.785 notes, Thorne's Cambridge notes, and MathOverflow all give the identical statement. The disc is
`D_p = {x : ‖x‖ < p^{-1/(p-1)}}`, the exact radius of convergence. The matching log isometry
`‖log(1+y)‖ = ‖y‖` is its inverse on the same ball.

Most general standard form: over **any complete nonarchimedean field extending `ℚ_p`** (Wikipedia and
the arXiv references state it on `ℂ_p`; the proof — term-by-term valuation + the ultrametric
sup-principle — works for any such field), `‖exp(x) − 1‖ = ‖x‖` for `‖x‖ < p^{-1/(p-1)}`. The
project's `L` (`[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`) is
precisely this maximal setting.

Generality dimensions where the literature varies:
- **Underlying field**: `ℚ_p` → `ℂ_p` / arbitrary complete nonarchimedean extension. Most general =
  "any complete ultrametric normed `ℚ_p`-algebra field" — which the target already uses. ✓ maximal.
- **One-point vs. two-point**: the literature states BOTH `‖exp x − 1‖ = ‖x‖` (the headline) and the
  two-point `‖exp x − exp y‖ = ‖x − y‖` (the full isometry). The target is the one-point form; the
  project's `norm_padicExp_sub_padicExp` is the two-point form. Both are "standard."

Disagreement with the literature: **none.** The target *is* the literature's canonical named isometry
fact, at the literature's maximal generality, in its headline `exp(0)=1` form.

---

### Generality analysis — `norm_padicExp_sub_one`

Literature-standard form (from Phase 3): on `‖x‖ < p^{-1/(p-1)}` over any complete nonarchimedean
field ⊇ `ℚ_p`, `‖exp(x) − 1‖ = ‖x‖` (the headline isometry; equivalently the `y=0` case of
`‖exp x − exp y‖ = ‖x − y‖`).

| # | Parameter / hypothesis                          | Current Lean form                  | Literature-standard form     | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------------------|------------------------------------|------------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L]`                               | normed field                       | complete nonarch field ⊇ ℚ_p | NO                  | a field structure is needed for `(n!)⁻¹` as scalars and the norm; matches the standard setting |
| 2 | `[NormedAlgebra ℚ_[p] L]`                        | normed ℚ_p-algebra                  | extension of ℚ_p             | NO                  | the factorial-inverse scalars and Legendre `‖n!‖_p` bound (computed in ℚ_p) act through this algebra structure; this IS "L is an extension of ℚ_p", the literature hypothesis |
| 3 | `[IsUltrametricDist L]`                          | ultrametric norm                    | nonarchimedean field         | NO                  | the isometry rests on the ultrametric sup-principle `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` (the linear term dominates the tail); intrinsically nonarchimedean |
| 4 | `[CompleteSpace L]`                             | complete                           | complete                     | NO                  | needed for the series to sum (the `padicExp` `tsum` and `summable_padicExp_terms`); cannot drop |
| 5 | `hx : InExpBall p x` (`‖x‖^{p−1} < p⁻¹`)        | open convergence ball              | open convergence ball (same) | NO                  | the ball is exactly the radius of convergence; the series **diverges** outside, and the isometry's strictness argument (every term beyond the linear one is *strictly* smaller) needs the OPEN ball |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.** All four typeclass hypotheses are precisely the defining
features of the standard setting ("complete nonarchimedean field extending `ℚ_p`"), and the ball is the
exact (non-enlargeable) radius of convergence. The conclusion is the literature's headline equality.
Number of weakening opportunities found: **0** (in hypotheses or conclusion).
Proposed restatement: none (already maximal).
Cost of restatement: n/a.

→ Phase 7 therefore considers `YES-add-as-is` vs the NO buckets (and runs 4c). [Contrast with the
sibling `norm_padicExp_sub_one_sub_self_le`, whose *conclusion constant* was non-sharp → STRICTLY
NARROWER. Here the conclusion is an exact equality with nothing to tighten.]

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                        | no       | — | hypotheses are already typeclasses (`NormedField`/`IsUltrametricDist`/…); nothing to bundle |
|  2 | sequences/metric → filters/nets/topological?                                                              | no       | — | already a clean norm equality; no sequential limit to filter-ise |
|  3 | construct an object → universal-property class?                                                            | no       | — | this is a metric identity, not a construction |
|  4 | set-with-closure-predicate → bundled substructure?                                                         | no       | — | n/a |
|  5 | field-specific → weaken typeclass hierarchy?                                                               | partial  | already general `L`; the cleanest mathlib idiom would phrase the isometry as an `Isometry`/`LipschitzWith 1` statement about a `padicExp` *bundled map on the ball*, once a mathlib `PadicExp`/nonarchimedean-exp namespace exists | the right move is at the **definition layer** (introduce a nonarchimedean `exp` with its ball + an `Isometry`-packaged isometry lemma), not a reformulation of *this* lemma's bare signature |
|  6 | 1-categorical → higher-categorical?                                                                        | no       | — | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive structure?                                                      | no       | — | the only concrete object is the prime `p`/`ℚ_[p]`, intrinsic to the p-adic setting |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for the lemma's bare signature). The statement is already an idiomatic
norm equality. There is one genuine organisational improvement, but it lives **one layer down** and is
a *def-development* decision, not a reformulation of this signature: mathlib has **no** p-adic /
nonarchimedean exponential at all, so the mathlib-idiomatic move is to introduce a nonarchimedean `exp`
(with its convergence-ball API) and expose the isometry as an `Isometry`/`LipschitzWith 1`-style fact
about a bundled map on the ball — possibly stating the two-point `norm_padicExp_sub_padicExp` as
`Isometry (padicExp p ∘ ball-coe)` with this `‖exp x − 1‖ = ‖x‖` as a corollary. One-line reason it is
not itself a modernisation move: it is a concrete metric identity already in idiomatic form; the
modernisation question is entirely about whether (and how) to upstream the underlying `padicExp`
machinery — a BIG, multi-decl development decision (Phase 7).

---

### Diamond / defeq risk — `norm_padicExp_sub_one`

**n/a — declaration kind is `theorem`.** (Phase 4.5 runs only for `def`/`class`/`instance`.)

---

### Mathlib search-status: `norm_padicExp_sub_one`

[A] Lean-Finder       "p-adic exponential isometry", "norm exp x - 1 equals norm x"   n/a: Lean-Finder web UI not callable in this environment — substituted with exhaustive grep over the mathlib tree (method D), reading each candidate's actual statement.
[B] Loogle            `‖NormedSpace.exp _ - 1‖ = ‖_‖`, `‖_ - 1‖ = ‖_‖`, `Isometry NormedSpace.exp`   n/a: `lean_loogle` MCP tool unavailable in this environment — substituted with method-D grep for every candidate shape (`‖exp _ - 1‖ = _`, `Isometry … exp`, `‖exp _ - exp _‖`).
[C] LeanSearch        "p-adic exponential is an isometry", "norm of exp minus one equals norm"   n/a: `lean_leansearch` MCP tool unavailable — substituted with method D; the only natural-language matches in mathlib are the archimedean `Complex`/`Real` exp bounds.
[D] Grep mathlib src  `grep -rn` over `.lake/packages/mathlib/Mathlib/` for: `padicExp\|PadicExp\|nonarchimedean.*[Ee]xp`; `norm_exp_sub_one\|‖.*exp.* - 1‖ =`; `Isometry.*exp\|exp.*Isometry`; `expSeries_radius_eq_top`   **hits**: (i) `Mathlib/Analysis/Complex/Exponential.lean` — `Complex.norm_exp_sub_one_le` (L439, `≤ 2‖x‖`), `Complex.norm_exp_sub_one_sub_id_le` (L446, `≤ ‖x‖²`); (ii) `Mathlib/Analysis/Complex/Trigonometric.lean:986` — `norm_exp_I_mul_ofReal_sub_one` (an **equality** `‖exp(I·x) − 1‖ = ‖2 sin(x/2)‖`, a trig identity, unrelated); (iii) `Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean` — `norm_exp_I_mul_ofReal_sub_one_le` family (`≤ ‖x‖`, archimedean trig). **NONE** in `Mathlib/NumberTheory/Padics/` (the dir has no exp/log file at all — only `AddChar`, `Complex`, `Hensel`, `MahlerBasis`, `PadicIntegers`, `PadicNorm`, `PadicNumbers`, `PadicVal`, `ProperSpace`, `RingHoms`, `ValuativeRel`, `WithVal`, `HeightOneSpectrum`). **NO** `Isometry`/isometry statement for any `exp` (the lone `isometry_…exp` hit, `isometry_vertical_line`, is the hyperbolic upper-half-plane metric — unrelated). **NO** nonarchimedean `exp` anywhere (`padicExp`/`PadicExp`/`nonarchimedean.*exp` grep returns empty).
[E] Name pattern      `padicExp`, `norm_padicExp`, `expSeries`, `NormedSpace.exp`, `InExpBall`   `padicExp`/`norm_padicExp`/`InExpBall` do not exist in mathlib. `NormedSpace.exp` exists but its entire API rests on `expSeries_radius_eq_top : radius = ∞` (`Exponential.lean:451`) — the **archimedean** regime, **false** p-adically — and it has **no** isometry/`‖exp−1‖` lemma at all (grep of `Exponential.lean` for `Isometry`/`norm_exp`/`‖exp` returns only summability lemmas). grep for `Nonarchimedean`/`IsUltrametricDist` in `Exponential.lean` returns empty.

Searched for both:
- the user's current form (`‖padicExp p x − 1‖ = ‖x‖`) — **not** in mathlib.
- the literature-standard forms (the two-point isometry `‖exp x − exp y‖ = ‖x − y‖`; an `Isometry`-packaged
  exp; the general-`NormedSpace.exp` analogue) — **none** exist p-adically/nonarchimedeanly in mathlib.

Concluded: **not in mathlib (all methods exhausted — A/B/C substituted with method-D grep per the
unavailable-tool rule — plus the literature-standard forms).** The closest artifacts are archimedean
exp bounds on `Complex.exp` (`norm_exp_sub_one_le`, `norm_exp_sub_one_sub_id_le`) — inequalities, ball
`‖x‖≤1`, on a different function over `ℂ` — and the trig equality `norm_exp_I_mul_ofReal_sub_one`
(`= ‖2 sin(x/2)‖`, unrelated). None transfer to a p-adic field `L`. Mathlib has **no** p-adic /
nonarchimedean exponential, and its `NormedSpace.exp` is archimedean-only with no isometry lemma.

Dependency note: the proof's actual infrastructure (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`,
`IsUltrametricDist.norm_tsum_le_of_forall_le`, `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`)
*is* genuine mathlib — only `padicExp` itself and the two-point parent `norm_padicExp_sub_padicExp` are
project-local.

---

### Call sites — `norm_padicExp_sub_one`

Internal use count: **5**  (within the project, NOT counting the declaring theorem at PadicExp.lean:259)
External-to-file callers: **1 distinct file** (`ResidueZeta.lean`)

| Caller file:line               | Usage pattern (one-line excerpt)                                              |
|--------------------------------|-------------------------------------------------------------------------------|
| PadicExp.lean:953              | `rw [InExpBall, norm_padicExp_sub_one p hx]; exact hx` — closes that `exp x` stays in the ball (the isometry is exactly what shows `‖exp x − 1‖ = ‖x‖ < radius`), feeding the exp/log inversion machinery |
| PadicExp.lean:1051             | `norm_padicExp_sub_one (L := ℚ_[p]) p hball` — `L = ℚ_[p]` specialisation in the `pℤ_p` / `pZpExp`-coercion bridge |
| PadicExp.lean:1067             | `norm_padicExp_sub_one (L := ℚ_[p]) p (inExpBall_of_mem_span p hp2 hx)` — same bridge cluster (membership-from-span hypothesis) |
| ResidueZeta.lean:113           | `norm_padicExp_sub_one (L := ℚ_[p]) p (inExpBall_of_mem_span p hp2 htℓmem)` — the key step of `norm_onePAdicPow_sub_one` (R7.1b): `‖y^t − 1‖ = ‖t‖·‖y−1‖` via the bridge `y^t = exp(t·log y)`, `‖exp w − 1‖ = ‖w‖` |
| (ResidueZeta.lean:300 — indirect) | `norm_padicExp_sub_one_sub_self_le` (a *different* lemma) is used here; `norm_padicExp_sub_one` reaches this proof only via `norm_onePAdicPow_sub_one` at :113 |

Inline-derivation grep (was `‖exp _ − 1‖ = ‖_‖` re-derived elsewhere without using the lemma?):
  - (none) — every place the isometry-to-1 is needed routes through this lemma; no inline
    `norm_padicExp_sub_padicExp p _ h0`-style re-derivation appears at any other site.

What the call-sites pattern tells you: **K = 5 internal uses + 1 external-to-file caller
(`ResidueZeta.lean`), no inline re-derivation.** Per the Phase-6 signal table (`K ≥ 3` AND a
downstream-file consumer) this is a **real-API** signal — consumers genuinely depend on the
`‖exp x − 1‖ = ‖x‖` *headline* form (not the two-point parent): it is what shows `exp x` stays in the
ball, drives the `pℤ_p` exp/log bridge, and underpins the character-isometry
`norm_onePAdicPow_sub_one`. It is not dead code and not a one-off wrapper. The signal confirms the
*specialisation* (`y=0`) is the genuinely-used API surface — but, as with its siblings, the lemma's
*mathlib* fate rests entirely on the upstreaming decision for the `padicExp` machinery as a whole, not
on local reuse pressure.

---

### Composition check (Phase 6)

Can `norm_padicExp_sub_one` be derived from mathlib in ≤3 chained calls?

Attempt 1: a mathlib exp-isometry / `‖exp x − 1‖` lemma, specialised.
  - Mathlib decls used: (none available) — `Complex.norm_exp_sub_one_le` / `…_sub_id_le`.
  - Result: **fails** — those are *inequalities* about `Complex.exp` in the **archimedean** norm (ball
    `‖x‖≤1`, constants `2`/`1`), on a different function over `ℂ`; `padicExp p` is a distinct function
    on a p-adic field `L` with a different ball, and the conclusion is an **equality**. No coercion
    `L → ℂ` makes them correspond, and mathlib has **no** isometry statement for any exp.

Attempt 2: derive from the two-point isometry `norm_padicExp_sub_padicExp` at `y = 0`.
  - Decls used: `norm_padicExp_sub_padicExp p hx h0` + `padicExp_zero` (both **project-local**) — this
    is literally the project's 2-line proof.
  - Result: **succeeds as a composition — but from a PROJECT-LOCAL parent, not from mathlib.** The
    Phase-6 question is specifically "can *mathlib's* primitives compose to give the form?" — and the
    answer is no, because the parent `norm_padicExp_sub_padicExp` (and `padicExp_zero`, and `padicExp`
    itself) are not in mathlib. (Per the Phase-6 heuristics this 2-call `simpa` *would* be a valid
    composition — `NO-composable` — **if** the parent were a mathlib decl. It is not.)

Attempt 3: assemble the isometry from mathlib's ultrametric primitives directly.
  - Decls used: `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` + the tail bound
    `IsUltrametricDist.norm_tsum_le_of_forall_le` + `summable_padicExp_terms` + a term-strictness lemma.
  - Result: **this is the parent `norm_padicExp_sub_padicExp`'s own ~50-line proof** — peel the `n=0,1`
    terms, show the tail is *strictly* smaller than the linear term on the OPEN ball
    (`norm_factorial_inv_smul_pow_sub_lt`), then conclude by the ultrametric "norm of a sum where one
    summand strictly dominates" principle. Genuine multi-lemma theorem, not a composition.

Conclusion: **NOT-COMPOSABLE from mathlib.** Mathlib has the ultrametric *infrastructure* but **no**
p-adic exponential to compose against; the only exp isometry/bound lemmas are archimedean and do not
transfer. The lemma *is* a trivial 2-call composition from its **project-local** parent
`norm_padicExp_sub_padicExp` — which is the crux of the verdict (Phase 7): it is not standalone-PR-able,
and its content is carried by the two-point isometry sibling.

---

## Verdict: `norm_padicExp_sub_one`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the target **is** the literature's *canonical, named* p-adic-exp fact —
  "exp is an isometry", headline form `‖exp x − 1‖ = ‖x‖`. K. Conrad ("Infinite Series in p-Adic
  Fields") states it **verbatim** alongside the two-point form: "if t ∈ Dp then |e^t − 1| = |t|, and
  for x and y in Dp, |e^x − e^y| = |x − y|." Wikipedia / MIT 18.785 / Thorne / MathOverflow unanimous;
  stated over `C_p`/any complete nonarch extension (the project's generality).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — all four typeclasses are the defining
  hypotheses of the standard setting; the ball is the exact radius of convergence; the conclusion is the
  literature's headline equality (nothing to tighten). Modern-idiom (4c): already idiomatic; the only
  improvement (an `Isometry`-packaged exp) lives at the missing-`padicExp`-def layer.
- Mathlib search (Phase 5): **not in mathlib** — no p-adic/nonarchimedean exp; no isometry lemma for any
  exp; the only `‖exp−1‖` lemmas are archimedean `Complex` bounds (inequalities) + an unrelated trig
  equality. The proof's ultrametric infrastructure **is** mathlib; `padicExp` + the two-point parent are
  project-local.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** — but it **is** a trivial 2-call
  composition from the *project-local* parent `norm_padicExp_sub_padicExp` (`+ padicExp_zero`). Call
  sites: **K=5 internal + 1 external** (real-API signal for the `y=0` specialisation).

**Rationale (why BORDERLINE, not YES-add-as-is, not a NO):**

On pure search mechanics this reads like the strongest `YES` candidate in the whole `padicExp` circle:
it is the literature's *single canonical named fact* about the p-adic exponential, proved sorry-free at
maximal generality, genuinely missing from mathlib, and with real downstream consumers (K=5+1). Yet the
*same three governing judgment calls* that put its siblings `summable_padicExp_terms` and
`norm_padicExp_sub_one_sub_self_le` in `BORDERLINE` apply here with full force, and a fourth, lemma-
specific one is added — none groundable in the search evidence, all exactly the kind the skill must
defer:

1. **It cannot be PR'd standalone — it is a property of a `def` mathlib does not have, and that whole
   development is the real contribution.** The statement is *about* `PadicLFunctions.padicExp`; mathlib
   has **no** p-adic / nonarchimedean exponential (its `NormedSpace.exp` is archimedean-only —
   `expSeries_radius_eq_top`, no `IsUltrametricDist` support; the `Padics/` dir has no exp/log file).
   Upstreaming this isometry sensibly means upstreaming a **BIG, multi-decl nonarchimedean-`exp`
   development** (the convergence-ball predicate / a p-adic radius computation, `summable_padicExp_terms`,
   the def `padicExp`, this isometry + its two-point parent, the functional equation `padicExp_add`, the
   log + its inverse isometry). Whether to undertake that — and how to package it — is a
   project/community-policy decision. This is the **same governing decision** already flagged `BORDERLINE`
   for the two siblings; the `padicExp` def itself has **not yet been assessed** (no ledger entry), and
   its verdict governs this one.

2. **Redundancy against the two-point isometry parent — a packaging call (lemma-specific).** Phase 6
   shows this lemma is a 2-line `simpa` from `norm_padicExp_sub_padicExp` (the `y=0` case). Conrad
   states **both** the two-point form and this `exp(0)=1` form as named facts, so it is a *legitimate*
   literature-grade specialisation, not junk — and the K=5+1 call sites consume *this* headline form
   directly (it is the convenient API surface downstream code actually calls; the two-point form is used
   only at PadicExp.lean:202's own proof). But for **mathlib**, whether to ship the `‖exp x − 1‖ = ‖x‖`
   corollary *alongside* the two-point isometry, or to expose only the two-point form (or an
   `Isometry`-bundled map) and let the `y=0` case be `by simpa`, is a deliberate API-granularity decision
   a reviewer would want made — not silently here. (This redundancy is why the verdict is *not*
   `YES-add-as-is`: the gate requires naming the specific mathlib gap, and the honest gap is "the p-adic
   exp *isometry* (most naturally the two-point form / a bundled `Isometry`)", of which this is one face.)

3. **The right mathlib *shape* is unsettled (Phase 4c).** The mathlib-idiomatic statement of "exp is an
   isometry" is plausibly an `Isometry (padicExp p ∘ ball-coe)` or `LipschitzWith 1` fact on a bundled
   ball map, with `‖exp x − 1‖ = ‖x‖` as a derived corollary — but that depends on the def-layer design
   in (1) (how the ball and `padicExp` get bundled), which should be decided deliberately (likely on
   Zulip) as part of the whole development.

Per the skill's anti-pattern guidance, an EXPENSIVE/whole-development cost (here: the entire
nonarchimedean-`exp` upstreaming) is itself a `BORDERLINE` question to the user, not a self-resolving
downgrade — and the strong call-site signal confirms the lemma is real and load-bearing *within the
project* without resolving its mathlib fate. (Note the gate: this is *not* `NO-composable-from-mathlib`,
because Phase 6's composition is from a **project-local** parent, not mathlib primitives — the whole
point is mathlib has nothing to compose from.)

**Numbered questions (≤5):**

1. Do you intend to upstream the project's p-adic / nonarchimedean **exponential development** to mathlib
   as a unit (the convergence-ball predicate / a p-adic `expSeries.radius` computation, `summable_padicExp_terms`,
   the def `padicExp`, the isometry + its two-point parent `norm_padicExp_sub_padicExp`, the functional
   equation `padicExp_add`, and the log)? This isometry is the literature's headline fact of that circle
   and should travel *with* the development, not alone — it is meaningless without the `padicExp` def,
   which mathlib lacks. (Same governing decision as `summable_padicExp_terms` / `norm_padicExp_sub_one_sub_self_le`.)
2. If yes to (1): in mathlib, should "exp is an isometry" be the **two-point form**
   `‖exp x − exp y‖ = ‖x − y‖` (or an `Isometry`/`LipschitzWith 1`-bundled map on the ball) as primary,
   with this `‖exp x − 1‖ = ‖x‖` shipped as a named corollary — or should both be first-class API? (The
   project's K=5+1 consumers use the `y=0` form directly, so a named corollary is well-motivated; the
   question is granularity, not whether the content belongs.)
3. If yes to (1): should the convergence ball be stated via mathlib's `FormalMultilinearSeries.radius`
   idiom (needs a first-contributed p-adic-radius lemma `(expSeries ℚ_[p] L).radius = p^{1/(p-1)}`) or
   kept as the bespoke `InExpBall` predicate the project uses? (Mirrors Q2 of the `summable_padicExp_terms`
   report; should be decided once for the whole development.)
4. If you do **not** plan to upstream the p-adic-exp machinery: then this isometry stays a (real,
   heavily-used) project-local result — correct as-is — and should be dropped from mathlib consideration
   along with the rest of the circle. Is that the case?

**Next action:** user answers the questions; re-run `/mathlibable norm_padicExp_sub_one` — **preferably
together with `/mathlibable PadicLFunctions.padicExp`** (the def whose upstreaming decision governs this
lemma) and `/mathlibable PadicLFunctions.norm_padicExp_sub_padicExp` (its two-point parent, the more
general isometry). Likely resolutions:
  - "Upstream the nonarchimedean-exp development" → flips to **YES-add-as-is** (statement is maximally
    general, non-composable-from-mathlib, the canonical named fact), shipped as part of the multi-decl
    nonarchimedean-`exp` PR series — most likely as a **named corollary of the two-point isometry / a
    bundled `Isometry`** (Q2), with the radius idiom (Q3) settled in that PR's design.
  - "Keep project-local" → drop from mathlib consideration; it stays the (correct, real-API) headline
    isometry feeding the exp/log inversion and the character-isometry `norm_onePAdicPow_sub_one`.

---

## Next step

User answers the four numbered questions above; re-run `/mathlibable norm_padicExp_sub_one` —
preferably alongside `/mathlibable PadicLFunctions.padicExp` and `/mathlibable
PadicLFunctions.norm_padicExp_sub_padicExp`, since this lemma's verdict is governed by the (BIG,
multi-decl) upstreaming decision on the p-adic exponential it is a property of, and by the API-granularity
choice between the two-point isometry and this `‖exp x − 1‖ = ‖x‖` corollary — to resolve to either
`YES-add-as-is` (upstream the nonarchimedean-`exp` development as a unit, shipping this most likely as a
named corollary of the two-point isometry) or drop-from-consideration (keep as a project-local result).
