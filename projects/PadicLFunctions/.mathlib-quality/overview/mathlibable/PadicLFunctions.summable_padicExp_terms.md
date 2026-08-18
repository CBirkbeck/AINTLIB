# `/mathlibable` report — `PadicLFunctions.summable_padicExp_terms`

**Final verdict: `BORDERLINE-needs-human`**

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task instruction — build is stale/slow here; Phase 0 fallback used)
- decl `PadicLFunctions.summable_padicExp_terms`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:100`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=Σ xⁿ/n!` converges on the open ball `‖x‖ < p^{-1/(p-1)}` of a nonarchimedean complete normed `ℚ_p`-algebra field (Legendre: `v_p(n!)=(n−s_p(n))/(p−1)`) and is an isometry there; with the matching log inverting it. This theorem (decomposition node E1+) is the **foundational summability lemma** that makes the `tsum` defining `padicExp` meaningful.

---

### Statement (Phase 1)

`summable_padicExp_terms` is a **theorem** stating the following:

> Let `L` be a complete nonarchimedean (ultrametric) normed field that is a normed `ℚ_p`-algebra.
> For every `x` in the open convergence ball `‖x‖^{p-1} < p⁻¹` (equivalently `‖x‖ < p^{-1/(p-1)}`,
> the radius of convergence of the p-adic exponential), the family of exponential terms
> `n ↦ (n!)⁻¹ · xⁿ` is **(unconditionally) summable**.

This is the p-adic statement "the exponential series `Σ xⁿ/n!` converges on the disc `|x|_p < p^{-1/(p-1)}`",
proved through the nonarchimedean convergence criterion (a series converges iff its terms → 0) combined with
Legendre's valuation formula for `n!`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime.
- `L : Type*`, `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — a
  complete ultrametric normed `ℚ_p`-algebra field. This is the general nonarchimedean setting (it
  subsumes `ℂ_p` and finite extensions of `ℚ_p`); it is instantiated downstream at `L = ℚ_[p]`
  (`PadicExp.lean:1034`, in `ResidueZeta`).

Hypotheses (Lean side):
- `hx : InExpBall p x` — i.e. `‖x‖^{p−1} < p⁻¹`, the rpow-free spelling of `‖x‖ < p^{-1/(p-1)}`.

Conclusion (math): the exponential series converges (unconditionally) at every point of the open
convergence ball.

Conclusion (Lean): `Summable fun n : ℕ => (n.factorial : ℚ_[p])⁻¹ • x ^ n`.

**Proof shape.** Rewrite `Summable` via the project's E1 wrapper `summable_iff_tendsto_cofinite_zero`
(a thin re-export of mathlib's `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`), then
`Nat.cofinite_eq_atTop` + `tendsto_zero_iff_norm_tendsto_zero` reduce the goal to `‖(n!)⁻¹•xⁿ‖ → 0`.
The geometric majorant `‖x‖^{p-1}·(p‖x‖^{p-1})ⁿ → 0` (from `tendsto_pow_atTop_nhds_zero_of_lt_one`,
since `p‖x‖^{p-1} < 1` on the ball) dominates via the project lemma `norm_factorial_inv_smul_pow_le`
(which packages Legendre's bound `norm_factorial_le`), and the `(p−1)`-th-power squeeze
`lt_of_pow_lt_pow_left₀` closes it.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (with a BIG caveat)
Reason: as a *declaration* it is a helper lemma (a summability fact, decomposition node E1+), not a
`def`/structure and not a named theorem. **However**, it is the foundational lemma of a BIG object —
the project's p-adic exponential `padicExp` (a named mathematical structure absent from mathlib) — and
it is the single most-reused lemma in that development (Phase 6.0: 9 call sites). So while the lemma
itself is SMALL, its mathlib fate is governed by the BIG def it underpins.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-liner check **n/a** (one-line note).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | p-adic exponential function convergence ball radius factorial summable Legendre formula                | yes  | `exp(x)=Σ xⁿ/n!` converges on `\|x\|_p < p^{-1/(p-1)}`; radius via Legendre `v_p(n!)=(n−s_p(n))/(p−1)` | Wikipedia "P-adic exponential function" + "Legendre's formula"; arXiv 1907.11902 "Legendre's formula and p-adic analysis"; ResearchGate "On convergence of power series in p-adic field" |
|  2 | WebSearch (general / sharp form) | p-adic exp Σ xⁿ/n! converges \|x\| < p^{-1/(p-1)} nonarchimedean (over extensions of ℚ_p)               | yes  | convergence on `B(0, p^{-1/(p-1)})`; criterion is "terms → 0"; `\|exp(x)\|=1`, `\|exp(x)−1\|=\|x\|` on the ball | Wikipedia (states it on `ℂ_p`); K. Conrad "Infinite series in p-adic fields"; J. Thorne Cambridge p-adic-analysis notes (DPMMS) |
|  3 | WebSearch (named-after / aliases / criterion) | nonarchimedean complete normed field power series converges iff terms tend to zero, Cassels Local Fields | yes  | the **nonarchimedean convergence criterion** "Σ aₙ converges ⇔ aₙ → 0" is the named foundational fact; cited to Cassels *Local Fields* §12 (the project's own citation) | Cassels *Local Fields* (CUP 1986) §12; Crew LCFT notes; Berkeley/Cambridge Local Fields notes |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + history of p-adic exp convergence & the nonarchimedean Σ⇔→0 criterion") | n/a  | —                                | ChatGPT MCP server **not configured** in this environment (present in `~/.claude/mcp-needs-auth-cache.json`; `/setup-chatgpt` not run). Recorded n/a; WebSearch (3 queries) + Wikipedia + the module's own citations (RJW, Cassels §12, Washington §5.1) cover the standard-form question. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                | n/a  | (no references dir; no `refs/` symlink) | both directories absent on this machine — recorded n/a. The module docstring's inline citations (RJW TeX 1892–1897 "as stated"; Cassels §12; Washington §5.1) serve as the literature anchor. |
|  6 | nLab                             | p-adic exponential / nonarchimedean analytic function convergence                                       | partial | nLab routes p-adic exp through the general nonarchimedean-analytic-function / "convergence on a polydisc" picture; the radius `p^{-1/(p-1)}` is the headline | not a categorical concept; nLab has no dedicated standalone p-adic-exp-summability lemma |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                | not a categorical concept (summability of a concrete factorial series in a p-adic field). |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                | not an algebraic-geometry concept (analytic/series convergence, not scheme/sheaf theory). |
|  9 | MathOverflow / Math.StackExchange| p-adic exp series radius of convergence p^{-1/(p-1)}; when does Σ xⁿ/n! converge p-adically              | yes  | community consensus matches #1–#2: converges exactly on the open ball `\|x\|<p^{-1/(p-1)}` by terms→0 + Legendre | recurring Q&A; the radius and the terms→0 criterion are textbook-standard, never disputed |
| 10 | recent arXiv (last 5 years)      | p-adic exponential factorial series convergence / fast evaluation of p-adic transcendental functions    | partial | modern arXiv (e.g. 1809.07705 "On convergence … of power series in p-adic field"; fast-evaluation papers) reuses the classical radius + terms→0 criterion verbatim | confirms no modern reformulation supersedes the classical convergence statement |

The protocol passed: WebSearch ran **3** distinct queries at three generality levels (specific p-adic-exp
convergence ball / the convergence statement over general extensions / the named nonarchimedean Σ⇔→0
criterion); ChatGPT MCP recorded n/a with reason (server absent); local references recorded n/a with
reason (no dir); nLab checked; nCatLab / Stacks recorded n/a with reason; MathOverflow and recent arXiv
each checked.

### Literature summary (Phase 3)

Concept identified as: **convergence (summability) of the p-adic exponential series `Σ_{n} xⁿ/n!` on its
disc of convergence `‖x‖ < p^{-1/(p-1)}`** — the foundational convergence fact underlying the p-adic
exponential function.

Sources agree on the standard form: **yes.** Every source (Wikipedia, K. Conrad, Cassels §12, the
arXiv "Legendre's formula and p-adic analysis", MathOverflow) gives the identical statement: `Σ xⁿ/n!`
converges **iff** `‖x‖ < p^{-1/(p-1)}`, and the proof is always the same two ingredients —
(i) the **nonarchimedean convergence criterion** "a series converges iff its terms tend to 0", and
(ii) **Legendre's formula** `v_p(n!) = (n − s_p(n))/(p−1)` bounding `‖(n!)⁻¹‖_p`. This is *exactly* the
project's proof (E1 = the criterion; `norm_factorial_le` = Legendre).

Most general standard form: over **any complete nonarchimedean field extending `ℚ_p`** (Wikipedia states
it on `ℂ_p`; the criterion + Legendre work for any such field), `Σ xⁿ/n!` is summable for `‖x‖ <
p^{-1/(p-1)}`. The project's `L` (`[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L]
[CompleteSpace L]`) is precisely this maximal setting.

Generality dimensions where the literature varies:
- **Underlying field**: `ℚ_p` → `ℂ_p` / arbitrary complete nonarchimedean extension. The most general is
  "any complete ultrametric normed `ℚ_p`-algebra field" — which the target already uses. ✓ maximal.
- **Strength of conclusion**: the standard p-adic statement is *plain* convergence (`Summable`), because
  nonarchimedean convergence is automatically unconditional and (here) equivalent to norm-convergence.
  The target proves exactly `Summable` (the natural p-adic conclusion). [Contrast: mathlib's
  archimedean exp API proves the stronger *norm*-summability — see Phase 5.]

Disagreement with the literature: **none.** The target *is* the literature-standard convergence
statement, at the literature's maximal generality, proved by the literature's canonical method.

---

### Generality analysis — `summable_padicExp_terms`

Literature-standard form (from Phase 3): over any complete nonarchimedean field ⊇ `ℚ_p`, `Σ xⁿ/n!` is
summable for `‖x‖ < p^{-1/(p-1)}`.

| # | Parameter / hypothesis                          | Current Lean form                  | Literature-standard form     | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------------------|------------------------------------|------------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L]`                               | normed field                       | complete nonarch field ⊇ ℚ_p | NO                  | a field structure is needed for `(n!)⁻¹` to make sense as scalars and for the norm; matches the standard setting |
| 2 | `[NormedAlgebra ℚ_[p] L]`                        | normed ℚ_p-algebra                  | extension of ℚ_p             | NO (essentially)    | `(n!)⁻¹` is the image of a ℚ_p-scalar; the algebra structure is what lets the Legendre bound on `‖n!‖_p` (computed in `ℚ_p`) control `‖(n!)⁻¹ • xⁿ‖` in `L`. This is exactly "L is an extension of ℚ_p", the literature hypothesis. |
| 3 | `[IsUltrametricDist L]`                          | ultrametric norm                    | nonarchimedean field         | NO                  | the **nonarchimedean** criterion (E1, Σ⇔→0) is the heart of the proof and *requires* the ultrametric inequality; this IS the defining hypothesis of the standard form |
| 4 | `[CompleteSpace L]`                             | complete                           | complete                     | NO                  | completeness is exactly what makes "terms → 0 ⇒ summable" true (mathlib's `multipliable_of_tendsto_cofinite_one` needs it); cannot drop |
| 5 | `hx : InExpBall p x` (`‖x‖^{p−1} < p⁻¹`)        | open convergence ball              | open convergence ball (same) | NO                  | the ball is exactly the radius of convergence; the series **diverges** outside it, so the hypothesis cannot be weakened |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.** All four typeclass hypotheses are precisely the defining
features of the standard setting ("complete nonarchimedean field extending `ℚ_p`"), and the ball is the
exact (non-enlargeable) radius of convergence. The conclusion (`Summable`) is the natural p-adic
strength.
Number of weakening opportunities found: **0.**
Proposed restatement: none (already maximal).
Cost of restatement: n/a.

→ Phase 7 therefore considers `YES-add-as-is` vs the NO buckets (and runs 4c).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                        | no       | — | hypotheses are already typeclasses; nothing to bundle |
|  2 | sequences/metric → filters/nets/topological?                                                              | partial  | the proof already uses `cofinite`/`atTop` filters via the E1 criterion and `tendsto_zero_iff_norm_tendsto_zero` — i.e. it is *already* in the modern filter idiom | no further filter-isation needed; the statement (`Summable`) is the right filter-free packaging |
|  3 | construct an object → universal-property class?                                                            | no       | — | this is a convergence fact, not a construction |
|  4 | set-with-closure-predicate → bundled substructure?                                                         | no       | — | n/a |
|  5 | field-specific → weaken typeclass hierarchy?                                                               | partial  | the cleanest mathlib idiom would phrase the hypothesis as `x ∈ EMetric.ball 0 (expSeries ℚ_[p] L).radius` (reusing mathlib's `FormalMultilinearSeries.radius` / `expSeries`) rather than the bespoke `InExpBall` predicate — **but** mathlib cannot currently compute that radius p-adically (see Phase 5/6), so the reformulation is blocked until a p-adic-radius lemma exists | would let this lemma re-use mathlib's `FormalMultilinearSeries.summable` once the p-adic radius is computed; this is the real (def-layer) modernisation lever |
|  6 | 1-categorical → higher-categorical?                                                                        | no       | — | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive structure?                                                      | no       | — | the index `n : ℕ` is intrinsic to the factorial series |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for the lemma's signature as a standalone statement). The proof is
*already* written in the contemporary filter/`Summable` idiom. The one organisational improvement
(row 5) — restating the hypothesis in terms of mathlib's `(expSeries ℚ_[p] L).radius` and re-using
`FormalMultilinearSeries.summable` — lives **one layer down** and is currently **infeasible**: mathlib
has no way to compute the p-adic `expSeries` radius (its `expSeries_radius_eq_top` is archimedean-only;
its scalar-radius ratio test `ofScalars_radius_eq_inv_of_tendsto` requires `‖cₙ₊₁‖/‖cₙ‖` to *converge*,
but for `cₙ=(n!)⁻¹` that ratio is `p^{-v_p(n+1)}`, which **oscillates and has no limit**). One-line
reason it is not itself a modernisation move: it is a concrete summability statement already in idiomatic
form; the only modernisation question is whether to upstream the underlying nonarchimedean-`exp`
machinery (a def-development decision, Phase 7).

---

### Diamond / defeq risk — `summable_padicExp_terms`

**n/a — declaration kind is `theorem`.** (Phase 4.5 runs only for `def`/`class`/`instance`.)

---

### Mathlib search-status: `summable_padicExp_terms`

[A] Lean-Finder       "p-adic exponential series summable", "summable n!⁻¹ • xⁿ ball"   n/a: Lean-Finder web UI not callable in this environment — substituted with exhaustive grep over the mathlib tree (method D) for every candidate name/shape, plus reading the candidate decls' actual statements.
[B] Loogle            `Summable (fun n => (↑n.factorial)⁻¹ • _ ^ n)`, `Summable (fun n => (_ !⁻¹ : _) • _ ^ n)`, `_ ∈ EMetric.ball _ _ → Summable _`   **partial hit**: the shape `Summable (fun n => (n !⁻¹ : 𝕂) • x ^ n)` matches mathlib's `NormedSpace.expSeries_summable_of_mem_ball'` and `NormedSpace.expSeries_summable'` — but with a different hypothesis (eball-of-FMS-radius) and a different proof regime (archimedean). See below.
[C] LeanSearch        "p-adic exponential series converges on disc", "summability of exponential terms nonarchimedean field"   no direct p-adic hit: surfaces the archimedean `NormedSpace.expSeries_summable*` family only; nothing nonarchimedean.
[D] Grep mathlib src  `grep -rn "expSeries_summable\|summable.*factorial\|padic.*[Ee]xp"` over `.lake/packages/mathlib/Mathlib/`   hits: `Mathlib/Analysis/Normed/Algebra/Exponential.lean` (`norm_expSeries_summable_of_mem_ball'` L280, `expSeries_summable_of_mem_ball'` L296, `expSeries_summable'` L298, `Real.summable_pow_div_factorial` in `SpecificLimits/Normed.lean` L896). NONE in `Mathlib/NumberTheory/Padics/` (no p-adic exp exists). The nonarchimedean **summability criterion** the proof uses *is* mathlib: `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` (`Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean:18`).
[E] Name pattern      `padicExp`, `expSeries_summable`, `InExpBall`, `summable_exp`   `padicExp`/`InExpBall` do not exist in mathlib. `NormedSpace.expSeries_summable'` exists but is unconditional (`Summable (fun n => (n!⁻¹:𝕂)•xⁿ)` for **all** x), resting on `expSeries_radius_eq_top : radius = ∞` — the **archimedean** regime, which is **false** p-adically. grep for `Nonarchimedean`/`IsUltrametricDist` in `Exponential.lean` returns empty: the entire `NormedSpace.exp` API has no nonarchimedean support.

Searched for both:
- the user's current form (`Summable (fun n => (n!)⁻¹ • xⁿ)` on the ball `‖x‖^{p−1}<p⁻¹`) — **not** in mathlib.
- the literature-standard / general-`NormedSpace.exp` form — mathlib's `expSeries_summable_of_mem_ball'`
  is **the same term shape** at general `[NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]`, but it is **not applicable**
  here (details below).

**Why the close mathlib match (`NormedSpace.expSeries_summable_of_mem_ball'`) does NOT settle this as
NO-mathlib-has-it.** Two independent obstructions:

1. **Wrong conclusion / wrong proof regime.** Mathlib's lemma is the `.of_norm` shadow of
   `norm_expSeries_summable_of_mem_ball'`, which proves the **stronger norm-summability** by dominating
   with a *real geometric series* `‖p n‖ · rⁿ` (`FormalMultilinearSeries.summable_norm_mul_pow`,
   `ConvergenceRadius.lean:227`, via `summable_geometric_of_lt_one`). That domination is the *archimedean*
   mechanism. The natural p-adic statement (and the project's) is plain `Summable` via terms→0; they are
   logically related but the mathlib lemma's hypothesis is the binding obstruction (point 2).

2. **The hypothesis cannot be supplied — mathlib cannot compute the p-adic radius.** To invoke
   `expSeries_summable_of_mem_ball'` one must provide `x ∈ EMetric.ball 0 (expSeries ℚ_[p] L).radius`.
   Mathlib has **no** lemma giving `(expSeries ℚ_[p] L).radius` for a nonarchimedean `L`:
   `expSeries_radius_eq_top` requires `𝕂 = ℝ`/`ℂ` (`[CharZero 𝕂] [ContinuousSMul ℚ 𝕂]` + its proof uses
   `tendsto_inv_atTop_nhds_zero_nat`, false for `‖n!‖_p`), and the only general scalar-radius computer,
   `ofScalars_radius_eq_inv_of_tendsto`, needs `‖cₙ₊₁‖/‖cₙ‖ → r`; for `cₙ=(n!)⁻¹` that ratio is
   `‖n+1‖_p = p^{-v_p(n+1)}`, which **does not converge** (it equals 1 whenever `p∤n+1` and dips at
   multiples of `p`). So bridging `InExpBall p x` → eball-membership is itself a genuine, currently-missing
   p-adic radius-of-convergence computation, not a one-liner.

Concluded: **found building blocks (the nonarchimedean criterion `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`; Legendre via `Padic.valuation_natCast`/`sub_one_mul_padicValNat_factorial_lt_of_ne_zero`; the geometric limit `tendsto_pow_atTop_nhds_zero_of_lt_one`); a *near-match statement* (`NormedSpace.expSeries_summable_of_mem_ball'`, same term shape) that is NOT applicable because mathlib cannot supply its eball hypothesis p-adically.** The exact p-adic summability statement is **not** in mathlib.

---

### Call sites — `summable_padicExp_terms`

Internal use count: **8** (within the project, NOT counting the declaring theorem)
External-to-file callers: **1 distinct file** (`ResidueZeta.lean`)

| Caller file:line               | Usage pattern (one-line excerpt)                                              |
|--------------------------------|-------------------------------------------------------------------------------|
| PadicExp.lean:208              | `have hsx := summable_padicExp_terms p hx` — feeds `norm_padicExp_sub_padicExp` (the isometry on the ball) |
| PadicExp.lean:209              | `have hsy := summable_padicExp_terms p hy` — same isometry proof (other point) |
| PadicExp.lean:272              | `have hsx := summable_padicExp_terms p hx` — feeds `padicExp_add` (the functional equation `exp(x+y)=exp x · exp y`) |
| PadicExp.lean:273              | `have hsy := summable_padicExp_terms p hy` — same functional-equation proof |
| PadicExp.lean:899              | `refine (summable_padicExp_terms p hy).congr fun n => ?_` — bridges the bespoke series to `expSeries`/`coeff_exp` in the formal-power-series inversion (`exp_subst_log` evaluation) |
| PadicExp.lean:955              | `(summable_padicExp_terms p hx).congr fun n => by rw [coeff_exp, …]` — same evaluation-bridge cluster |
| PadicExp.lean:1034             | `summable_padicExp_terms (L := ℚ_[p]) p (inExpBall_of_mem_span p hp2 hx)` — the `L = ℚ_[p]` specialisation used for `pℤ_p` membership |
| ResidueZeta.lean:83            | `have hsd := summable_padicExp_terms p hw` — peels the `n=0,1` terms in `norm_padicExp_sub_one_sub_self_le` (the residue/pole proof, RJW §7) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none) — every place the exp series' summability is needed routes through this lemma; there is no
    inline `summable_iff_tendsto_cofinite_zero … (n!)⁻¹•xⁿ` re-derivation anywhere else.

What the call-sites pattern tells you: **K = 8 internal uses + 1 external-to-file caller, no inline
re-derivation.** Per the Phase-6 signal table (`K ≥ 3` and a downstream-file consumer) this is a strong
**real-API** signal — consumers genuinely depend on it; it is the substrate for the isometry, the
functional equation, the power-series inversion bridge, and the residue proof. It is emphatically **not**
dead code or a one-off wrapper. (This is the key contrast with the sibling `norm_padicExp_sub_one_sub_self_le`,
which had K=1: *this* lemma carries real reuse pressure.)

---

### Composition check (Phase 6)

Can `summable_padicExp_terms` be derived from mathlib in ≤3 chained calls?

Attempt 1: `NormedSpace.expSeries_summable_of_mem_ball' x hball`.
  - Mathlib decls used: `NormedSpace.expSeries_summable_of_mem_ball'`.
  - Result: **fails** — its hypothesis is `x ∈ EMetric.ball 0 (expSeries ℚ_[p] L).radius`, and (Phase 5)
    mathlib provides **no** way to compute that radius for a nonarchimedean `L` (the archimedean
    `expSeries_radius_eq_top` is inapplicable; the scalar ratio test `ofScalars_radius_eq_inv_of_tendsto`
    needs a ratio limit that does not exist for `(n!)⁻¹`). Supplying the hypothesis is a genuine missing
    lemma, not a call. Even if supplied, the term-order/`smul`-shape would need a `.congr`/coercion bridge.

Attempt 2: nonarchimedean criterion + a mathlib geometric/factorial summability fact.
  - Mathlib decls used: `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` +
    `tendsto_pow_atTop_nhds_zero_of_lt_one` + a Legendre `‖n!‖_p` bound.
  - Result: **this is exactly the project's proof**, and it is **not** a ≤3-call composition. It requires:
    (i) the criterion rewrite, (ii) `Nat.cofinite_eq_atTop` + `tendsto_zero_iff_norm_tendsto_zero`,
    (iii) the per-term geometric majorant lemma `norm_factorial_inv_smul_pow_le` — which is itself a
    multi-step lemma built on `norm_factorial_inv_pow_le` ← `norm_factorial_le` ← Legendre
    (`sub_one_mul_padicValNat_factorial_lt_of_ne_zero` + `Padic.valuation_natCast`) — and (iv) an explicit
    `Metric.tendsto_atTop` ε-argument with a `(p−1)`-th-power squeeze. That is a real ~25-line proof
    spanning ≥3 project-private lemmas, i.e. a genuine theorem, not a composition.

Attempt 3: `(norm_expSeries_summable_of_mem_ball' …).of_norm` after computing the radius.
  - Mathlib decls used: `norm_expSeries_summable_of_mem_ball'`, `Summable.of_norm`.
  - Result: **fails for the same reason as Attempt 1** — blocked on the missing p-adic radius computation;
    and it would route through the *stronger* norm-summability, requiring the archimedean geometric
    domination that the p-adic setting does not naturally provide.

Conclusion: **NOT-COMPOSABLE.** Mathlib has the *ingredients* (the nonarchimedean criterion, Legendre via
`Padic` valuation API, the geometric limit), but assembling them into this statement is a multi-lemma
proof, and the one mathlib lemma of the right *shape* (`expSeries_summable_of_mem_ball'`) is unusable
p-adically because its convergence-radius hypothesis is itself uncomputable in mathlib today.

---

## Verdict: `summable_padicExp_terms`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the target **is** the literature-standard convergence statement (`Σ xⁿ/n!`
  summable on `‖x‖<p^{-1/(p-1)}`), at the literature's maximal generality (any complete nonarch field ⊇ ℚ_p),
  proved by the canonical method (nonarchimedean Σ⇔→0 criterion + Legendre). Sources unanimous.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — all four typeclasses are the defining hypotheses
  of the standard setting; the ball is the exact radius of convergence; conclusion is the natural p-adic
  `Summable`. Modern-idiom check (4c): already idiomatic; the only improvement (re-use mathlib's
  `expSeries.radius`) is blocked by a missing p-adic-radius lemma.
- Mathlib search (Phase 5): **not in mathlib** — no p-adic exp; mathlib's same-shape lemma
  `NormedSpace.expSeries_summable_of_mem_ball'` is inapplicable (its eball hypothesis is uncomputable
  p-adically; it also proves the wrong/stronger norm-summability via archimedean geometric domination).
  The building blocks (`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`, Legendre via `Padic`
  valuation API, `tendsto_pow_atTop_nhds_zero_of_lt_one`) **are** mathlib.
- Composition check (Phase 6): **NOT-COMPOSABLE** — assembling the building blocks is a genuine ~25-line,
  ≥3-private-lemma proof; the shape-matching mathlib lemma is blocked on the missing radius computation.
  Call sites: **K=8 internal + 1 external** (strong real-API signal).

**Rationale (why BORDERLINE, not YES-add-as-is and not a NO):**

This is a *true, maximally-general, genuinely-missing-from-mathlib* p-adic convergence statement, proved
sorry-free, and — unlike the sibling tail-bound — it carries heavy reuse (K=8+1). Phases 4 and 6 both
point *away* from the NO buckets: it is **not** NO-composable (the proof is a real multi-lemma argument,
not a ≤3-call composition — see Phase 6 Attempt 2), and it is **not** NO-mathlib-has-it (the only
same-shape mathlib lemma is unusable p-adically, and supplying its hypothesis is itself a missing lemma —
see Phase 5). On the pure mechanics, the lemma reads like `YES-add-as-is`. But three judgment calls — none
groundable in the search evidence — block a clean YES, and they are exactly the kind the skill must defer:

1. **It cannot be PR'd standalone — it is the foundation of a `def` mathlib does not have, and that whole
   development is the real contribution.** The statement is the summability fact that makes the `tsum`
   *defining* `PadicLFunctions.padicExp` well-formed; its 8 internal consumers are the isometry, the
   functional equation `exp(x+y)=exp x·exp y`, the power-series inversion bridge, and the `pℤ_p`
   specialisation. Mathlib has **no** p-adic / nonarchimedean exponential (its `NormedSpace.exp` is
   archimedean-only — `expSeries_radius_eq_top`, no `IsUltrametricDist` support). So upstreaming this lemma
   sensibly means upstreaming a **BIG, multi-decl nonarchimedean-`exp` development** (a convergence-ball
   predicate or a p-adic-radius computation, this summability lemma, the log, the isometry, the functional
   equation). Whether to undertake that — and *how* it should be packaged into mathlib — is a
   project/community-policy decision. This is the **same governing decision** flagged for the sibling
   `norm_padicExp_sub_one_sub_self_le` (also `BORDERLINE`), and this lemma is even more central to it.

2. **The hypothesis spelling (`InExpBall`) vs. mathlib's `expSeries.radius` idiom is unresolved (Phase 4c
   row 5).** The mathlib-idiomatic form would state the ball as `x ∈ EMetric.ball 0 (expSeries ℚ_[p] L).radius`
   and ideally re-use `FormalMultilinearSeries.summable` — but that requires first contributing a **p-adic
   radius-of-convergence lemma** (computing `(expSeries ℚ_[p] L).radius = p^{1/(p-1)}` in the `ENNReal`
   sense), which mathlib lacks and whose own proof needs the limsup/Legendre machinery (the ratio test
   `ofScalars_radius_eq_inv_of_tendsto` does not apply — no ratio limit). So the *right mathlib statement*
   of this very lemma depends on a design choice (bespoke `InExpBall` predicate vs. the FMS-radius idiom)
   that should be made deliberately, likely on Zulip, as part of the development in (1) — not silently here.

3. **Conclusion strength is a design choice mathlib would want decided.** mathlib's exp API proves
   *norm*-summability; the natural p-adic statement is plain `Summable`. Both hold here. A mathlib reviewer
   would likely want the API to expose both (a `norm_…` variant and the plain one), matching the
   `norm_expSeries_summable'` / `expSeries_summable'` pairing. Which to make primary is a packaging call.

The strong call-site signal (K=8+1) does **not** override these — it confirms the lemma is real and
load-bearing *within the project*, but its mathlib fate is entirely tied to the upstreaming decision on
the p-adic-exp machinery as a whole, which is a human call. Per the skill's anti-pattern guidance, an
EXPENSIVE/whole-development cost is itself a BORDERLINE question to the user, not a self-resolving downgrade.

**Numbered questions (≤5):**

1. Do you intend to upstream the project's p-adic / nonarchimedean **exponential development** to mathlib
   as a unit (a convergence-ball predicate *or* a p-adic `expSeries.radius` computation, **this**
   summability lemma, the isometry `norm_padicExp_sub_one`, the functional equation `padicExp_add`, and the
   log)? This lemma is the foundation of that development and should travel *with* it, not alone.
2. If yes to (1): should the convergence ball be stated via mathlib's `FormalMultilinearSeries.radius`
   idiom (i.e. first contribute a lemma computing `(expSeries ℚ_[p] L).radius = p^{1/(p-1)}` and re-use
   `expSeries_summable_of_mem_ball'` / `FormalMultilinearSeries.summable`), or kept as a bespoke
   `InExpBall`-style predicate? (The former is more mathlib-idiomatic but needs the missing p-adic-radius
   lemma proved first; the latter is what the project has.)
3. If yes to (1): should the mathlib API expose **both** a norm-summability lemma (`norm_…`, matching
   mathlib's `norm_expSeries_summable'`) and this plain `Summable` form, or only the plain p-adic one?
4. If you do **not** plan to upstream the p-adic-exp machinery: then this lemma stays a (heavily-reused)
   project-local foundation — correct as-is — and should be dropped from mathlib consideration. Is that the
   case?

**Next action:** user answers the questions; re-run `/mathlibable summable_padicExp_terms`, preferably
**together with `/mathlibable PadicLFunctions.padicExp`** (the def whose upstreaming decision governs this
lemma's verdict) and the sibling `/mathlibable PadicLFunctions.norm_padicExp_sub_one`. Likely resolutions:
  - "Upstream the nonarchimedean-exp development" → flips to **YES-add-as-is** (statement is already
    maximally general and proof is non-composable), shipped as part of the multi-decl
    nonarchimedean-`exp` PR series — with the Q2 radius-idiom and Q3 norm-variant decisions settled in
    that PR's design.
  - "Keep project-local" → drop from mathlib consideration; it stays the (correct, heavily-reused)
    summability foundation of the project's exp/log development.

---

## Next step

User answers the four numbered questions above; re-run `/mathlibable summable_padicExp_terms` —
preferably alongside `/mathlibable PadicLFunctions.padicExp` and `/mathlibable PadicLFunctions.norm_padicExp_sub_one`,
since this lemma's verdict is governed by the (BIG, multi-decl) upstreaming decision on the p-adic
exponential definition it underpins — to resolve to either `YES-add-as-is` (upstream the
nonarchimedean-`exp` development as a unit, with the radius-idiom and norm-variant design choices made
in that PR) or drop-from-consideration (keep as a project-local foundation).
