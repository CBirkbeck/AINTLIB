# `/mathlibable` report — `PadicLFunctions.norm_padicExp_sub_one_sub_self_le`

**Final verdict: `BORDERLINE-needs-human`**

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task instruction — build is stale/slow here; Phase 0 fallback used)
- decl `PadicLFunctions.norm_padicExp_sub_one_sub_self_le`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:81`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "The residue of ζ_p at s = 1 (RJW §7)" — analyticity/pole of the p-adic L-function branches at s=1; this theorem is helper R7.1a (the quadratic tail of the p-adic exponential).

---

### Statement (Phase 1)

`norm_padicExp_sub_one_sub_self_le` is a **theorem** stating the following:

> Let `L` be a complete nonarchimedean (ultrametric) normed field that is a normed `ℚ_p`-algebra,
> and let `padicExp p` be the p-adic exponential `exp(w) = Σ_{n≥0} wⁿ/n!`. For every `w` in the open
> convergence ball `‖w‖^{p-1} < p⁻¹` (i.e. `‖w‖ < p^{-1/(p-1)}`), the second-order Taylor remainder
> of the exponential is bounded quadratically:
> `‖exp(w) − 1 − w‖ ≤ p · ‖w‖²`.

This is the p-adic analogue of the classical `‖e^z − 1 − z‖ ≤ ‖z‖²` (for `‖z‖ ≤ 1`), but with the
nonarchimedean convergence ball in place of `‖z‖ ≤ 1` and a constant of `p` instead of `1`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime.
- `L : Type*`, `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — a
  complete ultrametric normed `ℚ_p`-algebra field (the setting in which `padicExp` converges and is
  well-behaved; instantiated downstream at `L = ℚ_[p]`).

Hypotheses (Lean side):
- `hw : InExpBall p w` — i.e. `‖w‖^{p−1} < p⁻¹`, the rpow-free spelling of `‖w‖ < p^{-1/(p-1)}`, the
  exponential's radius of convergence.

Conclusion (math): the exponential tail past the linear term is `O(‖w‖²)` on the convergence ball,
with explicit constant `p`.

Conclusion (Lean): `‖padicExp p w - 1 - w‖ ≤ (p : ℝ) * ‖w‖ ^ 2`.

**Proof shape.** Peel the `n=0` and `n=1` terms via `summable_padicExp_terms` + `tsum_eq_zero_add`,
leaving `Σ_{n≥2} (n!)⁻¹ wⁿ`; then bound the whole tsum by the ultrametric sup-bound
`IsUltrametricDist.norm_tsum_le_of_forall_le` (the `@[to_additive]` form of mathlib's
`norm_tprod_le_of_forall_le`), with the per-term bound `‖(n!)⁻¹•wⁿ‖ ≤ p·‖w‖²` (`n≥2`) supplied by the
project-private `norm_factorial_inv_smul_pow_le_quad`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: it is a helper lemma (decomposition node R7.1a) supplying a single quadratic estimate; it is
not a `def`/structure, not a named theorem, and not a `## Main results` entry (the file's main result
is the residue/pole statement, not this tail bound).

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-liner check **n/a**.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | p-adic exponential inequality "exp(x) − 1 − x" norm bound nonarchimedean                                | partial | standard emphasised result is `\|exp(x) − 1\|_p = \|x\|_p` (the isometry); the quadratic remainder is acknowledged-elementary but not named | Wikipedia "P-adic exponential function"; Conrad "Infinite series in p-adic fields"; Cambridge/J.Thorne notes; MIT exp.pdf |
|  2 | WebSearch (general / sharp form) | p-adic exponential estimate `\|exp(x)−1−x\| ≤ \|x\|²` valuation Cassels Koblitz                          | partial | "remainder after first two terms bounded by \|x\|² and higher powers" — stated as a routine truncation fact, constant `1`, not `p` | Koblitz §; Cassels *Local Fields* §12 (cited by the module docstring); academia.edu p-adic-series surveys |
|  3 | WebSearch (named-after / aliases / nLab-style) | nLab p-adic exponential isometry `p^{-1/(p-1)}` radius convergence logarithm                  | yes  | the **isometry** `\|exp(x)−1\| = \|x\|` on `\|x\|<p^{-1/(p-1)}` is the canonical/named statement | PlanetMath "p-adic exponential and p-adic logarithm"; MIT 18.785 problem sets; World Scientific "Logarithm and exponential in a p-adic field" |
|  4 | ChatGPT MCP                      | (intended: "standard p-adic form of the second-order exp tail bound + its generality + history")        | n/a  | —                                | ChatGPT MCP server not configured in this environment (`/setup-chatgpt` not run). Recorded n/a; WebSearch + nLab/PlanetMath + the module's own citations (RJW, Cassels §12, Washington §5.1) cover the standard-form question. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                | n/a  | (no references dir; no `refs/` symlink) | directory absent — recorded n/a. The module docstring's inline citations (RJW TeX 1892–1897 "as stated"; Cassels §12; Washington §5.1) serve as the literature anchor. |
|  6 | nLab                             | p-adic exponential / p-adic logarithm                                                                   | partial | nLab routes p-adic exp through the general nonarchimedean-analytic-function picture; the radius `p^{-1/(p-1)}` and isometry are the headline facts | not a categorical concept; nLab has no dedicated quadratic-remainder lemma |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                | not a categorical concept (a real-valued metric estimate on a p-adic field). |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                | not an algebraic-geometry concept (analytic estimate, not scheme/sheaf theory). |
|  9 | MathOverflow / Math.StackExchange| p-adic exp `exp(x)−1−x` second order bound; \|exp(x)−1\|=\|x\|                                          | yes  | community consensus: `\|exp(x)−1\| = \|x\|` is the standard isometry; the quadratic tail is "obvious from term-by-term valuation" | recurring Q&A on p-adic exp/log; nobody states the `≤ p·‖w‖²` constant — sharp form is `‖w‖²` for odd p |
| 10 | recent arXiv (last 5 years)      | p-adic exponential factorial series convergence / fast evaluation                                       | partial | modern arXiv (e.g. "Fast evaluation of p-adic transcendental functions", "On some p-adic series with factorials") reuses the classical radius + isometry; no new canonical tail-bound form | confirms no modern reformulation supersedes the classical isometry |

The protocol passed: WebSearch ran ≥3 distinct queries at three generality levels (specific quadratic
form / sharp `≤|x|²` form / named-isometry+aliases); ChatGPT MCP recorded n/a with reason (server
absent); local references recorded n/a with reason; nLab checked; nCatLab / Stacks recorded n/a with
reason; MathOverflow and recent arXiv each checked.

### Literature summary (Phase 3)

Concept identified as: **the second-order Taylor remainder (the "`exp(x) − 1 − x` tail") of the p-adic
exponential on its disk of convergence `‖x‖ < p^{-1/(p-1)}`.**

Sources agree on the standard form: **no, on this specific object.** The *canonical, named* p-adic
exp result in every source (Wikipedia, Koblitz, Cassels §12, PlanetMath, MathOverflow) is the
**isometry** `‖exp(x) − 1‖ = ‖x‖` (which the project itself separately proves as
`PadicLFunctions.norm_padicExp_sub_one` at `PadicExp.lean:259`). The *quadratic remainder*
`‖exp(x) − 1 − x‖ ≤ ‖x‖²` appears only as an "obvious from term-by-term valuation" remark, never as a
headline result, and is universally stated with constant `1` (for odd p) — **not** `p`.

Most general standard form: on `‖x‖ < p^{-1/(p-1)}` over any complete nonarchimedean field extending
`ℚ_p`, `‖exp(x) − 1 − x‖ = ‖x²/2 + x³/6 + …‖ ≤ sup_{n≥2} ‖xⁿ/n!‖`. By the ultrametric sup principle and
Legendre's bound this is `‖x²/2‖ = ‖x‖²` for odd `p` (since `‖2⁻¹‖_p = 1`), and the `n≥3` terms are
strictly smaller on the ball. So the **sharp** constant is `1` for odd p; the target's `p` is loose.

Generality dimensions where the literature varies:
- **Underlying field**: ℚ_p → any complete nonarchimedean field / ℂ_p (the target's general `L` matches
  the most general setting). ✓ already maximal.
- **Constant**: literature `1` (odd p) vs. target `p` — the target is **non-sharp**.
- **Framing**: literature treats this only en route to the isometry, never as a standalone named lemma.

Disagreement with the literature: the literature's standard object is the **isometry** (an equality),
not this **inequality**; and where the inequality is mentioned the constant is `1`, not `p`. The target
is a deliberately-loose, fit-for-purpose (derivative-squeeze) variant, not the textbook form.

---

### Generality analysis — `norm_padicExp_sub_one_sub_self_le`

Literature-standard form (from Phase 3): on `‖x‖ < p^{-1/(p-1)}`, `‖exp(x) − 1‖ = ‖x‖` (isometry) and,
as a corollary, `‖exp(x) − 1 − x‖ ≤ ‖x‖²` (sharp constant `1` for odd p).

| # | Parameter / hypothesis                          | Current Lean form                  | Literature-standard form     | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------------------|------------------------------------|------------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` | complete ultrametric normed ℚ_p-algebra field | any complete nonarchimedean field ⊇ ℚ_p | NO              | this is already the maximal setting where `padicExp` (the `tsum` of `wⁿ/n!`) converges and is summable; matches ℂ_p/general-extension generality |
| 2 | `hw : InExpBall p w` (`‖w‖^{p−1} < p⁻¹`)         | open convergence ball              | open convergence ball (same) | NO                  | the ball is exactly the radius of convergence; cannot enlarge (series diverges outside) |
| 3 | conclusion constant `(p : ℝ)`                   | `≤ p · ‖w‖²`                        | `≤ ‖w‖²` (sharp, odd p)      | **YES**             | the per-term bound `norm_factorial_inv_smul_pow_le_quad` proves `≤ p‖w‖²`; the ultrametric sup of the actual tail is `‖w‖²` for odd p — the project chose the loose `p` because it suffices for the squeeze and avoids the p=2 case split |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — not in its hypotheses (those are maximal),
but in its **conclusion**: the constant `p·‖w‖²` is weaker than the literature/sharp `‖w‖²`.
Number of weakening opportunities found: **1** (the constant).
Proposed restatement (sharp):

```lean
theorem norm_padicExp_sub_one_sub_self_le_sharp {w : L} (hw : InExpBall p w) :
    ‖padicExp p w - 1 - w‖ ≤ ‖w‖ ^ 2 := by
  sorry  -- for odd p: ultrametric sup of {‖wⁿ/n!‖ : n≥2} = ‖w²/2‖ = ‖w‖² (‖2⁻¹‖=1);
         -- p=2 needs care (‖2⁻¹‖_2 = 2), so the clean sharp form may itself want `p≠2`,
         -- or the bound `≤ ‖2⁻¹‖·‖w‖² = (p=2 ? 2 : 1)·‖w‖²`.
```

Cost of restatement: **MODERATE** — the proof reshapes (per-term bound must be sharpened from `p‖w‖²`
to `‖2⁻¹‖·‖w‖²`, and the `p=2` corner produces constant `2`, so the clean unconditional `‖w‖²` may
require `p≠2` or a `p`-dependent constant). EXPENSIVE is not in play; this is a constant-tightening, not
a new idea. (Cost does not change the bucket — see gate.)

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                        | no       | — | hypotheses are already typeclasses (`NormedField`/`IsUltrametricDist`/…); nothing to bundle |
|  2 | sequences/metric → filters/nets/topological?                                                              | no       | — | already a clean norm inequality; no sequential limit to filter-ise (the *consumer* `tendsto_branch_denom_div` already uses filters/`squeeze_zero_norm'`) |
|  3 | construct an object → universal-property class?                                                            | no       | — | this is an estimate, not a construction |
|  4 | set-with-closure-predicate → bundled substructure?                                                         | no       | — | n/a |
|  5 | vector-space/metric/field-specific → weaken typeclass hierarchy?                                           | partial  | already general `L`; could phrase the radius via `‖·‖ < expRadius` once a `padicExp` def lands in mathlib | the right move is at the *definition* layer (a mathlib `PadicExp`/nonarchimedean-exp namespace), not this lemma's signature |
|  6 | 1-categorical → higher-categorical?                                                                        | no       | — | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive/ordered structure?                                              | no       | — | the only concrete object is `(p:ℝ)` in the constant; tightening it (Phase 4b) is the real lever |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for the lemma as stated). The only organisational improvement lives one
layer down: there is no p-adic / nonarchimedean exponential **definition** in mathlib at all, so the
mathlib-idiomatic move is to introduce a nonarchimedean `exp` (with its convergence-ball API) and state
this as a tail-bound lemma *in that namespace* — a def-development decision, not a reformulation of this
signature. One-line reason it is not itself a modernisation move: it is a concrete metric estimate whose
form is already idiomatic; the modernisation question is entirely about whether to upstream the
underlying `padicExp` machinery.

---

### Diamond / defeq risk — `norm_padicExp_sub_one_sub_self_le`

**n/a — declaration kind is `theorem`.** (Phase 4.5 runs only for `def`/`class`/`instance`.)

---

### Mathlib search-status: `norm_padicExp_sub_one_sub_self_le`

[A] Lean-Finder       "p-adic exponential remainder bound", "exp x - 1 - x norm"   n/a: Lean-Finder web UI not callable in this environment — substituted with exhaustive grep over the mathlib tree (method D) for every candidate name/shape.
[B] Loogle            `‖NormedSpace.exp _ - 1 - _‖ ≤ _`, `‖_ - 1 - _‖ ≤ _ * ‖_‖^2`   no hits: the only `‖exp _ - 1 - _‖ ≤ ‖_‖^2` shape in mathlib is `Complex.norm_exp_sub_one_sub_id_le` (archimedean, `Complex.exp`); no generic/p-adic form.
[C] LeanSearch        "norm of p-adic exponential minus one minus identity", "quadratic bound exponential tail"   no hits: surfaces `Complex.norm_exp_sub_one_sub_id_le` / `Complex.exp_bound_sq` only.
[D] Grep mathlib src  `grep -rn "sub_one_sub\|exp.*- 1 - \|norm_exp_sub_one"` over `.lake/packages/mathlib/Mathlib/`   hits ONLY in `Mathlib/Analysis/Complex/Exponential.lean` (`norm_exp_sub_one_sub_id_le`, line 444; `Real.norm_exp_sub_one_sub_id_le`, line 453) and `Mathlib/Analysis/SpecialFunctions/Exp.lean` (`exp_bound_sq`). NONE in `Mathlib/NumberTheory/Padics/` (no p-adic exp exists) and NONE on the general `NormedSpace.exp` (`Mathlib/Analysis/Normed/Algebra/Exponential.lean` has only `norm_expSeries_summable*` — summability, no tail/remainder bound).
[E] Name pattern      `padicExp`, `expSeries`, `NormedSpace.exp`, `norm_exp`   `padicExp` does not exist in mathlib; `NormedSpace.exp` exists but its entire API (`expSeries_radius_eq_top`, `norm_expSeries_summable`) is built on the series converging *everywhere* — `expSeries_radius_eq_top : radius = ∞` — which is the **archimedean** regime and is **false** p-adically. No nonarchimedean/`IsUltrametricDist` support anywhere in that file (grep for `Nonarchimedean`/`IsUltrametricDist` returns empty).

Searched for both:
- the user's current form (`‖padicExp p w − 1 − w‖ ≤ p·‖w‖²`) — not in mathlib.
- the literature-standard forms (the isometry `‖exp x − 1‖ = ‖x‖`; the sharp `≤ ‖x‖²`; and the
  general-`NormedSpace.exp` analogue) — none of these exist p-adically in mathlib either.

Concluded: **not in mathlib (all methods exhausted, plus the literature-standard forms).** The closest
artifact is `Complex.norm_exp_sub_one_sub_id_le`, but it is about `Complex.exp` in the **archimedean**
setting (constant `1`, ball `‖x‖≤1`) and is *inapplicable* to a p-adic field `L`. Mathlib has **no**
p-adic / nonarchimedean exponential at all, and its general `NormedSpace.exp` has **no** tail-remainder
lemma and **no** nonarchimedean instance support.

Dependency note (resolved): the proof uses `IsUltrametricDist.norm_tsum_le_of_forall_le`, which *is*
genuine mathlib — the `@[to_additive]` image of `norm_tprod_le_of_forall_le` in
`Mathlib/Analysis/Normed/Group/Ultra.lean:342` (invisible to a plain source grep because the additive
name is generated). So the proof's infrastructure is mathlib; only `padicExp` itself is project-local.

---

### Call sites — `norm_padicExp_sub_one_sub_self_le`

Internal use count: **1**  (within the project, NOT counting the declaring theorem)
External-to-file callers: **0 distinct files** (the single use is in the *same* file, a different theorem)

| Caller file:line               | Usage pattern (one-line excerpt)                                              |
|--------------------------------|-------------------------------------------------------------------------------|
| ResidueZeta.lean:300           | `exact norm_padicExp_sub_one_sub_self_le p hwball` — supplies the key bound in the `‖(s−1)⁻¹·(exp w − 1 − w)‖ ≤ ‖s−1‖⁻¹·(p‖w‖²)` step that drives the squeeze `(s−1)⁻¹(exp w − 1 − w) → 0` in `tendsto_branch_denom_div` (RJW Lemma 7.2(ii), the simple zero of the branch denominator) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none) — the only other occurrences of the `padicExp p w - 1 - w` pattern are inside
    `tendsto_branch_denom_div` itself (lines 293, 297), which *call* this lemma rather than re-deriving it.

What the call-sites pattern tells you: **K = 1 internal use only**, no external/downstream consumers,
no inline re-derivation. Per the Phase-6 signal table this leans toward "possibly the wrong abstraction
/ could be inlined" — but here the single use is non-trivial (a real squeeze argument, not a one-liner),
and the lemma is a clean reusable estimate, so it is not junk. The signal mainly says: this lemma's
value to mathlib does **not** rest on heavy local reuse; it rests entirely on whether the *p-adic
exponential development itself* is upstreamed (see Verdict).

---

### Composition check (Phase 6)

Can `norm_padicExp_sub_one_sub_self_le` be derived from mathlib in ≤3 chained calls?

Attempt 1: `Complex.norm_exp_sub_one_sub_id_le` (or `Real.…`), specialised.
  - Mathlib decls used: `Complex.norm_exp_sub_one_sub_id_le`.
  - Result: **fails** — that lemma is about `Complex.exp : ℂ → ℂ` in the archimedean norm; `padicExp p`
    is a different function on a p-adic field `L`, with a different convergence ball and a different
    constant. No coercion `L → ℂ` makes the statements correspond.

Attempt 2: unfold `padicExp` to `NormedSpace.exp` and use a mathlib tail bound.
  - Mathlib decls used: `NormedSpace.exp`, `NormedSpace.expSeries_*`.
  - Result: **fails** — (i) mathlib has no tail/remainder bound on `NormedSpace.exp` at all; (ii)
    mathlib's `NormedSpace.exp` API is built on `expSeries_radius_eq_top` (radius = ∞), which is false
    over a p-adic `L`, so even the summability lemmas don't apply; the whole archimedean exp API is
    unusable nonarchimedeanly.

Attempt 3: assemble from the ultrametric tsum bound directly.
  - Mathlib decls used: `IsUltrametricDist.norm_tsum_le_of_forall_le` + a per-term factorial-norm bound.
  - Result: **this is exactly the project's proof** — and it is *not* a ≤3-call composition: it needs
    `summable_padicExp_terms`, a `tsum_eq_zero_add` peel of two terms, and the project-private
    quadratic per-term bound `norm_factorial_inv_smul_pow_le_quad` (which itself rests on Legendre's
    `v_p(n!)` estimate `norm_factorial_le`). That is a genuine multi-lemma proof, not a composition.

Conclusion: **NOT-COMPOSABLE.** There is no p-adic exponential in mathlib to compose against; the only
exp tail bounds are archimedean (`Complex`/`Real`) and do not transfer.

---

## Verdict: `norm_padicExp_sub_one_sub_self_le`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the *standard named* p-adic exp fact is the **isometry**
  `‖exp x − 1‖ = ‖x‖` (Wikipedia/Koblitz/Cassels §12/PlanetMath/MathOverflow); this quadratic remainder
  is acknowledged-elementary, never canonical, and the literature constant is `1` (odd p), not `p`.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — hypotheses are maximal, but the
  conclusion's constant `p·‖w‖²` is loose vs. the sharp `‖w‖²`.
- Mathlib search (Phase 5): **not in mathlib** — no p-adic/nonarchimedean exp exists; no tail bound on
  the general `NormedSpace.exp`; the only analogue (`Complex.norm_exp_sub_one_sub_id_le`) is archimedean
  and inapplicable.
- Composition check (Phase 6): **NOT-COMPOSABLE** (nothing p-adic to compose from).

**Rationale (why BORDERLINE, not a YES/NO):**

This is a *true, genuinely missing-from-mathlib* p-adic estimate, proved sorry-free at the right
nonarchimedean generality — so it is not a NO. But three things block a clean YES, and each is a
judgment call the skill cannot ground in evidence alone:

1. **It cannot be PR'd standalone — it is inseparable from a def that mathlib lacks.** The statement is
   *about* `PadicLFunctions.padicExp`, the project's p-adic exponential. Mathlib has **no** p-adic /
   nonarchimedean exponential (its `NormedSpace.exp` is archimedean-only — `expSeries_radius_eq_top`,
   no `IsUltrametricDist` support). So upstreaming this lemma necessarily means upstreaming a whole
   nonarchimedean-`exp` development (`InExpBall`/convergence ball, summability, the isometry
   `norm_padicExp_sub_one`, the log, etc.). Whether to undertake that BIG, multi-decl upstreaming is a
   project/community-policy decision — exactly the kind of thing the skill defers to the human.

2. **The constant is non-sharp (Phase 4b).** Mathlib's bar is "the right statement." The
   literature/sharp form is `‖exp w − 1 − w‖ ≤ ‖w‖²` (constant 1, odd p); the target uses `p` because it
   suffices for the downstream squeeze and dodges the `p=2` case. A mathlib reviewer would likely ask
   for the sharp constant (or a `p`-explicit `‖2⁻¹‖·‖w‖²`). Whether to tighten before upstreaming —
   versus keeping the fit-for-purpose `p` form locally — is a taste/scope call.

3. **It is not the literature's canonical object.** The named, textbook p-adic-exp result is the
   *isometry* (which the project already has as `norm_padicExp_sub_one`). This inequality is a secondary,
   derived estimate. If anything from this circle is "the" mathlib contribution, it is the isometry +
   the def, with this quadratic tail as a minor corollary — a packaging judgment for the human.

The single internal call site (K=1, no external consumers — Phase 6.0) reinforces that the lemma's
mathlib-worth does *not* come from local reuse pressure; it comes entirely from the upstreaming decision
about the p-adic-exp machinery as a whole. That is a human call.

**Numbered questions (≤5):**

1. Do you intend to upstream the project's p-adic / nonarchimedean **exponential development** to
   mathlib as a unit (the `padicExp` definition + convergence ball + the isometry `norm_padicExp_sub_one`
   + log)? This lemma should travel *with* that development, not alone — it is meaningless without the
   `padicExp` def, which mathlib does not have.
2. If yes to (1): should this tail bound be **sharpened** to the standard constant first
   (`‖exp w − 1 − w‖ ≤ ‖w‖²`, possibly with `p ≠ 2`, per Phase 4b) before the PR, or is the loose
   `p·‖w‖²` acceptable as a convenience corollary alongside the sharp form?
3. Within a mathlib p-adic-exp namespace, is the **isometry** `‖exp x − 1‖ = ‖x‖` (the project's
   `norm_padicExp_sub_one`) the primary contribution, with this quadratic tail kept only as a derived
   helper — or do you want both stated as first-class API?
4. If you do **not** plan to upstream the p-adic-exp machinery: then this lemma is correctly a
   permanent project-local helper (K=1 use in `tendsto_branch_denom_div`), and it should be dropped from
   mathlib consideration entirely. Is that the case?

**Next action:** user answers the questions; re-run `/mathlibable norm_padicExp_sub_one_sub_self_le`
(ideally after, or together with, a `/mathlibable PadicLFunctions.padicExp` run, since the def's verdict
governs this lemma's). Likely resolutions:
  - "Upstreaming the p-adic-exp development" + sharpen → flips to **YES-but-generalise-first** (target =
    the sharp-constant form, shipped as part of the nonarchimedean-`exp` PR series).
  - "Keep project-local" → drop from mathlib consideration; it stays a fit-for-purpose private-grade
    helper feeding the residue/pole proof.

---

## Next step

User answers the four numbered questions above; re-run `/mathlibable norm_padicExp_sub_one_sub_self_le`
(preferably alongside `/mathlibable PadicLFunctions.padicExp`, since this lemma's verdict is governed by
the upstreaming decision on the `padicExp` definition it is stated about) to resolve to either
`YES-but-generalise-first` (upstream the nonarchimedean-exp development, with the constant sharpened) or
drop-from-consideration (keep as a project-local helper).
