# `/mathlibable` report — `PadicLFunctions.MeasureR.exists_antideriv_bounded`

## Verdict: **BORDERLINE-needs-human**

A `theorem` that bundles three things into one existential: (existence of a formal
antiderivative `C`) ∧ (a custom differential identity `p·(1+X)·∂C = B`) ∧ (a
quantitative p-adic coefficient bound `‖coeff m C‖ ≤ p·(m+1)`). The bound is real
p-adic-analysis content and is not in mathlib; but the statement as written is a
proof-internal bundle with constants chosen for one specific proof (the `c₀-design`
of `L_p(θ,1)`), and a strictly weaker sibling (`MeasureR.exists_antideriv`) already
exists in the project. Whether this belongs in mathlib — and in what factored form —
is a taste/policy call. Questions are at the end.

---

### Baseline (Phase 0)

- lake build:               build NOT re-run (stale/slow per task note); reasoned from source — declaration and all dependencies read directly.
- decl `PadicLFunctions.MeasureR.exists_antideriv_bounded`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:635`
- kind:                      theorem
- has sorry:                 no (full ~45-line proof present, lines 635–681)
- module docstring summary:  RJW §6.2, Thm 6.1(ii) (Leopoldt): the p-adic value `L_p(θ,1)`, via a distribution-free antiderivative route (decomposition P6).

Section context (lines 39–41): `variable (p : ℕ) [hp : Fact p.Prime]`,
`variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
[CompleteSpace K] [CharZero K]`. The theorem carries `omit [CompleteSpace K]
[CharZero K] in include hp in`, so its effective context is: `K` a normed field, a
normed `ℚ_[p]`-algebra, ultrametric, with `p` prime.

---

### Statement (Phase 1)

`PadicLFunctions.MeasureR.exists_antideriv_bounded` is a theorem stating the following:

Let `K` be an ultrametric normed field that is a normed `ℚ_p`-algebra (so `char K = 0`),
and let `B ∈ K⟦X⟧` be a formal power series whose coefficients are all p-adic
integers in `K` (i.e. `‖coeff n B‖ ≤ 1` for every `n`). Then there exists a formal
power series `C ∈ K⟦X⟧` such that:
1. `C` has zero constant term;
2. `C` is a "`(1+X)·d/dX`-antiderivative of `B` scaled by `p`": `p · (1+X) · C′ = B`,
   where `C′ = derivativeFun C` is the formal derivative;
3. the coefficients of `C` grow at most linearly with an explicit p-adic constant:
   `‖coeff m C‖ ≤ p·(m+1)` for every `m`.

The construction is explicit: set `E := p⁻¹ · (B · (1+X)⁻¹)` (an integral product
scaled by `p⁻¹`, whose coefficients are bounded by `‖p⁻¹‖ ≤ p`, hence `‖coeff k E‖ ≤ p`),
then `C := ∑_{n≥1} (coeff_{n-1} E / n) Xⁿ`. The bound on `C` then follows from
`‖coeff m C‖ = ‖coeff_{m-1} E‖ · ‖m⁻¹‖ ≤ p · m ≤ p·(m+1)`, using the p-adic
estimate `‖(m:K)⁻¹‖ ≤ m`.

Variables / typeclasses (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic.
- `K : Type*`, `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]` — the
  coefficient field: a non-archimedean (ultrametric) extension of `ℚ_p`.

Hypotheses (Lean side):
- `B : PowerSeries K` — the input power series (in the application, a Mahler transform
  of a measure).
- `hB : ∀ n, ‖coeff n B‖ ≤ 1` — `B` has integral coefficients.

Conclusion (math): an explicit `(1+X)d/dX`-antiderivative `C` of `B/p` exists with
zero constant term and p-adically linearly-bounded coefficients.

Conclusion (Lean):
`∃ C : PowerSeries K, PowerSeries.constantCoeff C = 0 ∧
  (p : K) • ((1 + PowerSeries.X) * PowerSeries.derivativeFun C) = B ∧
  ∀ m, ‖PowerSeries.coeff m C‖ ≤ (p : ℝ) * ((m : ℝ) + 1)`

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma feeding convergence of `seriesEval (φ C₁)` (per its own
docstring: "Feeds the convergence of `seriesEval (φ C₁)` in the constant pin"). It is
not a `## Main results` entry, not named after a person/place, and introduces no new
structure. It is a quantitative refinement of the sibling existence lemma
`MeasureR.exists_antideriv`.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing.)

### One-line check (Phase 2b)

Body line count: ~45 substantive lines.
One-liner verdict: n/a (kind is theorem, not def).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic formal power series antiderivative bounded coefficients linear bound logarithm"                | partial | building blocks only            | K. Conrad *Infinite series in p-adic fields*, Washington-style log series — the log series `∑(-1)^{n-1}/n Xⁿ` and its formal antiderivative are standard, but no source bundles existence + the `(1+X)∂` identity + an explicit affine norm bound |
|  2 | WebSearch (general form)         | "formal power series antiderivative coefficient division by n p-adic valuation bound"                  | partial | building blocks only            | Wikipedia *Formal power series*; standard fact that formal antiderivative divides coeff `n` by `n`; `v_p(n)` bound is Legendre/Kummer-standard; no packaged lemma |
|  3 | WebSearch (named-after / aliases)| "antiderivative p-adic L-function measure power series coefficient bound convergence seriesEval"        | no   | (no named result)               | Returns p-adic-L / Iwasawa-theory papers (measures ↔ power series, Γ-transform derivatives) but no statement of this affine-bounded-antiderivative lemma; it is proof-internal bookkeeping |
|  4 | ChatGPT MCP                      | (would ask: "standard form / generality / historical evolution of a bounded formal antiderivative over a p-adic field")  | n/a | server unavailable               | The configured `chatgpt-math` MCP server failed to connect (points at `/home/chris/...` on a different machine). Recorded n/a per Phase-0 fallback; substituted by extra WebSearch + direct mathlib-source grep below |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/`                                            | n/a  | (no references dir)              | Directory absent; no `refs/` symlink either. Recorded n/a. The source is RJW (the paper this project formalizes); the docstring attributes the construction to "replan R6.6, c₀-design" — i.e. it is the project's own proof engineering |
|  6 | nLab                             | "p-adic logarithm" / "formal power series derivative"                                                  | partial | standard log/derivative only    | nLab has the p-adic logarithm and formal-derivative concepts but no affine-bounded-antiderivative statement |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | not a categorical concept        | This is a concrete quantitative estimate over a normed field; no categorical formulation applies |
|  8 | Stacks Project (alg geom)        | —                                                                                                      | n/a  | not an algebraic-geometry concept| Formal-power-series p-adic estimate; Stacks covers formal schemes but not this analytic bound |
|  9 | MathOverflow / Math.SE           | "p-adic valuation 1/n bound power series antiderivative" (covered by queries #1–2 result sets)         | no   | (no targeted hit)                | The valuation bound `v_p(1/n) = p^{v_p(n)} ≤ n` is folklore (Conrad's notes); no MO thread states the bundled lemma |
| 10 | recent arXiv (last 5 years)      | covered by #1–3 (arxiv pdfs surfaced: 1907.06437, 0705.4047, 2107.00971, S0022314X09002029)            | no   | (no packaged statement)          | Recent p-adic-L / dynamics papers control coefficient sizes of log-type series but none states this affine-bounded `(1+X)∂` antiderivative |

The protocol passed: WebSearch ran 4 queries at three generality levels; ChatGPT MCP
recorded n/a with a concrete reason (server down on this machine) and substituted; local
refs n/a (absent); nLab checked; Stacks/nCatLab/MathOverflow/arXiv each checked or n/a
with a reason.

### Literature summary (Phase 3)

Concept identified as: a **formal `(1+X)d/dX`-antiderivative with an explicit p-adic
linear coefficient bound** — assembled from three folklore-standard ingredients:
(a) the formal antiderivative of a power series (divide `coeff (n-1)` by `n`), (b) the
geometric/inverse series `(1+X)⁻¹ = ∑(-1)ⁿXⁿ` with integral coefficients, and (c) the
p-adic estimate `‖(n:K)⁻¹‖ = p^{v_p(n)} ≤ n` (Legendre/Kummer; Conrad's notes).
Sources agree on the standard form of each ingredient: yes. The **bundled statement**
(existence + the `p·(1+X)·∂C = B` identity + the `‖coeff m C‖ ≤ p(m+1)` bound) does not
appear as a named result anywhere — it is internal proof bookkeeping ("c₀-design",
replan R6.6) for the RJW computation of `L_p(θ,1)`.

Most general standard form: there is no canonical "most general" form because the
statement is a bespoke bundle; the closest reusable kernels are
- "the formal antiderivative `C` of `(1+X)⁻¹·B/p` has zero constant term and satisfies
  `p·(1+X)·∂C = B`" (a pure formal-algebra fact over any ℚ-algebra — and mathlib's
  `PowerSeries.deriv_log` already proves `∂ log(1+X) = (1+X)⁻¹`), and
- "if `B` is integral over an ultrametric `ℚ_p`-algebra then `coeff m` of the
  antiderivative is bounded by `p·(m+1)`" (the genuinely p-adic part).

Generality dimensions where the literature varies:
  - coefficient ring: the formal-antiderivative half is a ℚ-algebra fact; the bound
    half is genuinely non-archimedean (`IsUltrametricDist` + `NormedAlgebra ℚ_[p] K`).
  - the constant `p·(m+1)`: an artifact of the proof (`‖p⁻¹‖ ≤ p` times `‖m⁻¹‖ ≤ m`,
    then `m ≤ m+1`); the literature has no canonical normalisation of this constant.

Disagreement with the literature: none — the ingredients match the literature; the
bundle is just not a literature object.

---

### Generality analysis — `exists_antideriv_bounded`

Literature-standard form (from Phase 3): no single named target. The natural
mathlib-idiomatic factoring is two pieces: a formal-algebra antiderivative lemma over a
ℚ-algebra (already 90% in mathlib via `PowerSeries.deriv_log`/`derivativeFun`), plus a
separate non-archimedean coefficient-norm bound.

| # | Parameter / hypothesis                   | Current Lean form                | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------------------------|----------------------------------|-------------------------------------------|---------------------|--------------------------------|
| 1 | `[NormedAlgebra ℚ_[p] K]`                | normed `ℚ_p`-algebra            | for the formal half: any `ℚ`-algebra; for the bound: a non-arch. valued `ℚ_p`-algebra | partial             | The differential identity (parts 1–2) needs only `CharZero`/`ℚ`-algebra (`p` invertible, `n` invertible). The bound (part 3) genuinely needs the p-adic norm + ultrametric. So the *current bundle* cannot be uniformly weakened; it must be split. |
| 2 | `[IsUltrametricDist K]`                  | ultrametric                      | needed for the coeff-product bound        | NO (for part 3)     | `hEbd` uses `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty` to bound the convolution sum coefficient by the max — archimedean triangle inequality would not give the uniform `≤ p` bound. Essential to the bound half. |
| 3 | `hB : ∀ n, ‖coeff n B‖ ≤ 1`              | `B` integral                     | integrality is the natural hypothesis for an integral-coeff bound | NO                  | The conclusion's bound is exactly the integral-input consequence; weakening `hB` weakens the conclusion correspondingly. |
| 4 | scalar `(p : K) •` and bound `p·(m+1)`   | hardwired `p`                    | proof-specific normalisation              | n/a                 | The `p` scalar and the `p(m+1)` bound come from the `c₀-design`; they are not a literature normalisation but a bookkeeping choice tied to the consumers. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but in the unusual sense
that it is *over*-bundled rather than over-strong on a single axis. The differential
identity (parts 1–2) is a ℚ-algebra fact and is already essentially in the project as
the strictly-weaker sibling `MeasureR.exists_antideriv` (FormalPsi.lean:1169, identical
construction, no `hB`, no bound). The genuinely new content is the bound (part 3), which
is non-archimedean and not factored out.

Number of weakening / refactoring opportunities found: 2
  1. The differential-identity half duplicates `MeasureR.exists_antideriv` and is in
     turn a thin wrapper over mathlib's `PowerSeries.deriv_log` / `derivativeFun` API.
  2. The genuinely-novel piece is a *coefficient-norm bound on the formal antiderivative*
     over an ultrametric `ℚ_p`-algebra — that, isolated, is the only mathlib-candidate
     content.

Proposed refactoring (if pursued): split into
- `MeasureR.exists_antideriv` (already exists) for the identity, and
- a standalone `norm_coeff_antideriv_le` : if `‖coeff n B‖ ≤ 1` then the explicit
  antiderivative's coefficients satisfy `‖coeff m C‖ ≤ p·(m+1)` — phrased against
  mathlib's `derivativeFun` and `Ring.inverse`.

Cost of restatement: MODERATE — the bound proof (`hEbd` + `norm_natCast_inv_le`) is
already isolated inside the current proof and would transplant directly; the
mathlib-idiomatic packaging (naming the antiderivative via mathlib `derivativeFun` API,
stating the bound on its coefficients) is the work.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                          | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------------------|----------|------------------------|--------------------------------|
|  1 | Could "let X be a foo" preambles become typeclasses?                                                              | no       | —                      | Already fully typeclass-driven (`NormedAlgebra ℚ_[p] K`, `IsUltrametricDist`). |
|  2 | Sequences/metric → filters/topological?                                                                          | no       | —                      | Purely algebraic/normed coefficient bound; no limit/filter content here (convergence is handled by downstream `seriesEval` lemmas, not this one). |
|  3 | Construct an object where a universal property would characterise it?                                            | partial  | The "antiderivative" is constructed explicitly; mathlib has `PowerSeries.derivativeFun` and `deriv_log` already, so one could *state the bound directly on a `derivativeFun`-inverse* rather than re-`mk`-ing the series | composes with `PowerSeries.deriv_log`, `derivativeFun_mul`, `Ring.inverse_mul_cancel` |
|  4 | set-with-closure-predicate → bundled substructure?                                                               | no       | —                      | No substructure here. |
|  5 | vector-space/metric/field-specific → weaker typeclass?                                                           | yes (split) | the identity half over `[Algebra ℚ K]`; the bound half over the ultrametric `ℚ_p`-algebra | the identity half would then unify with mathlib's `PowerSeries.log`/`deriv_log` ℚ-algebra API |
|  6 | 1-categorical → higher-categorical?                                                                              | no       | —                      | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structure?                                                  | no       | —                      | The index `n` is genuinely ℕ (power-series degree); the `p` is genuinely the prime. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **partial** — the *differential-identity* half is already a
ℚ-algebra fact that should reuse mathlib's `derivativeFun`/`deriv_log` ecosystem (and is
duplicated by `MeasureR.exists_antideriv` locally). The *bound* half is the only piece
with no mathlib idiom, and it is genuinely non-archimedean. The honest improvement is
**factoring**, not a single cleaner restatement: ship the bound as a standalone lemma
about `derivativeFun` coefficients over an ultrametric `ℚ_p`-algebra, and let the
identity come from existing API. Whether that factored bound clears mathlib's bar (it is
quite specific: a `p·(m+1)` affine bound for an integral input) is exactly the
judgment call this verdict surfaces.

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search
paths introduced).

---

### Mathlib search-status: `exists_antideriv_bounded`

[A] Lean-Finder       (MCP server unavailable on this machine)        n/a: lean-lsp/RAG MCP failed to connect (configured for `/home/chris/...`); substituted by direct mathlib-source grep [D]
[B] Loogle            (MCP unavailable; reasoned from source tree)     n/a: same; substituted by [D]
[C] LeanSearch        (MCP unavailable)                                n/a: same; substituted by [D]
[D] Grep mathlib src  `derivativeFun` / `antideriv|primitive|integral` in `RingTheory/PowerSeries/`; `PowerSeries.log`, `deriv_log` in `PowerSeries/Log.lean`; `ordProj_le`, `valuation_natCast`, `norm_eq_zpow_neg_valuation` in `Padics/`; `exists_norm_finsetSum_le` ultrametric  — no hits / building blocks only
[E] Name pattern      grep project + mathlib for `exists_antideriv_bounded` / sibling `exists_antideriv` — sibling exists in-project only

What the grep established:
  - mathlib **has** the formal-derivative API: `PowerSeries.derivativeFun`
    (`Mathlib/RingTheory/PowerSeries/Derivative.lean:44`), with `coeff_derivativeFun`,
    `derivativeFun_mul`, `derivativeFun_C`, etc.
  - mathlib **has** the log series and its derivative: `PowerSeries.log` and
    `PowerSeries.deriv_log` (`Mathlib/RingTheory/PowerSeries/Log.lean`), giving
    `∂ log(1+X) = (1+X)⁻¹` over a ℚ-algebra.
  - mathlib **has** `Ring.inverse` and `Ring.inverse_mul_cancel`, and
    `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty` (used in the proof).
  - mathlib **has** the p-adic valuation/norm facts: `Nat.ordProj_le`
    (`Data/Nat/Factorization/Basic.lean:103`), `Padic.valuation_natCast` and
    `Padic.norm_eq_zpow_neg_valuation` (`NumberTheory/Padics/PadicNumbers.lean`).
  - mathlib has **no** power-series antiderivative/`primitive`/`integral` definition,
    and **no** statement bounding the coefficients of a formal antiderivative in a
    non-archimedean norm.

Searched for both:
  - the user's current form (the affine-bounded `(1+X)∂` antiderivative) — not in mathlib;
  - the literature-standard kernels (formal antiderivative; `v_p(1/n) ≤ n`) — the
    *ingredients* are in mathlib, the *packaged statement* is not.

Concluded: **not in mathlib** (the bundled statement; all source-tree probes
exhausted, plus the two factored kernels). Mathlib has the building blocks
(`derivativeFun`, `deriv_log`, `Ring.inverse`, `ordProj_le`, `valuation_natCast`,
`exists_norm_finsetSum_le_of_nonempty`) but neither the differential-existence wrapper
nor the non-archimedean coefficient bound.

---

### Call sites — `exists_antideriv_bounded`

Internal use count: **2** (within the project, NOT counting the declaring file's own
recursion-free body).
External-to-file callers: **2 distinct files**.

| Caller file:line               | Usage pattern (one-line excerpt)                                              |
|--------------------------------|-------------------------------------------------------------------------------|
| ValuesAtOne.lean:800           | `obtain ⟨C₁, hC₁0, hC₁, hC₁bd⟩ := exists_antideriv_bounded (p := p) (mahlerK …) (norm_coeff_mahlerK_le_one _ _)` — destructures all 4 components |
| ResidueZeta.lean:921           | `obtain ⟨C₁, hC₁0, hC₁, hC₁bd⟩ := MeasureR.exists_antideriv_bounded (p := p) (mahlerK …) (norm_coeff_mahlerK_le_one _ _)` — destructures all 4 components |

Inline-derivation grep (was the equivalent re-derived elsewhere without using it?):
  - (none) — the only nearby relative is the **weaker** sibling
    `MeasureR.exists_antideriv` (FormalPsi.lean:1169), which omits `hB` and the bound;
    it is a *different (weaker) statement*, not an inline re-derivation of this one.

What the pattern tells us: **K = 2 internal uses, both consuming the bound `hC₁bd`**,
no inline re-derivation, plus the bound is the load-bearing extra over the existing
sibling. This is a real internal API with two genuine consumers — a YES-leaning signal
on *usefulness*. The BORDERLINE element is not "is it used" (it is) but "is this the
right *form/granularity* for mathlib".

---

### Composition check (Phase 6)

Can `exists_antideriv_bounded` be derived from mathlib (or from the existing sibling) in
≤3 chained calls?

Attempt 1 (from the weaker sibling `MeasureR.exists_antideriv`): obtain `C` from
`exists_antideriv B`, then prove `‖coeff m C‖ ≤ p(m+1)` separately.
  - Mathlib/project decls used: `MeasureR.exists_antideriv`, then the whole `hEbd`
    estimate (`coeff_mul`, `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty`,
    `norm_coeff_inverse_one_add_X_le_one`, `norm_natCast_inv_le`).
  - Result: **fails** as a ≤3-call composition. The bound is not a corollary of the
    existence statement; it requires re-running the explicit construction and the full
    ~15-line ultrametric estimate. The sibling discards the construction (returns only
    `∃ C`), so the bound cannot be read off it.
  - Notes: this is the core reason the two lemmas coexist — the bound needs the
    *witness*, not just its existence.

Attempt 2 (directly from mathlib `derivativeFun`/`deriv_log`): assemble the antiderivative
via `PowerSeries.log`-style API and bound coefficients.
  - Mathlib decls used: `PowerSeries.deriv_log`, `Ring.inverse_mul_cancel`,
    `Nat.ordProj_le`, `Padic.norm_eq_zpow_neg_valuation`, `exists_norm_finsetSum_le_…`.
  - Result: **fails** as ≤3 calls — this is a multi-step proof (define `E`, prove the
    coeff bound on `E`, define `C`, prove the derivative identity, prove the `C`-bound),
    i.e. the present ~45-line proof. Per the Phase-6 heuristics this is "multiple `have`s
    with non-trivial reasoning between" → **a proof, not a composition**.

Conclusion: **NOT-COMPOSABLE.** Mathlib (and the weaker sibling) supply the building
blocks but not a ≤3-call route to this bundled statement. The bound half is genuine new
work.

---

## Verdict: `PadicLFunctions.MeasureR.exists_antideriv_bounded`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the three ingredients (formal antiderivative, `(1+X)⁻¹`
  geometric series, `v_p(1/n) ≤ n`) are folklore-standard (Conrad, Washington,
  Wikipedia), but **no source states the bundled lemma** — it is RJW c₀-design proof
  bookkeeping.
- Generality analysis (Phase 4): STRICTLY NARROWER, but by *over-bundling* — the
  differential-identity half duplicates the weaker project sibling `MeasureR.exists_antideriv`
  and is a ℚ-algebra fact already near mathlib's `deriv_log`; the only mathlib-candidate
  content is the isolated non-archimedean coefficient bound. Phase 4c: factoring, not a
  single restatement, is the honest improvement.
- Mathlib search (Phase 5): not in mathlib (bundled form); building blocks present
  (`derivativeFun`, `deriv_log`, `Ring.inverse`, `ordProj_le`, `valuation_natCast`,
  `exists_norm_finsetSum_le_of_nonempty`).
- Composition check (Phase 6): NOT-COMPOSABLE (the bound needs the explicit witness +
  the full ultrametric estimate; >3 calls, real reasoning).

**Rationale (1–2 paragraphs):**

The result has genuine, non-composable p-adic content — the affine coefficient bound
`‖coeff m C‖ ≤ p(m+1)` on a formal `(1+X)d/dX`-antiderivative of an integral input over
an ultrametric `ℚ_p`-algebra is not in mathlib and cannot be assembled in ≤3 calls. It
also has two real internal consumers (ValuesAtOne.lean:800, ResidueZeta.lean:921), both
using the bound. By the "is it useful and not already there" test it passes. But mathlib
does not apply that test — it asks for the *right statement at the right granularity*,
and on that axis this declaration is problematic in a way the skill cannot resolve
unilaterally: (i) it is an over-bundled existential (`∃ C, constantCoeff C = 0 ∧
[a custom differential equation `p·(1+X)·∂C = B`] ∧ [an affine norm bound]`), which is
exactly the kind of conjunction `/cleanup` flags as not-mathlib-shaped — mathlib would
likely want the antiderivative *named/defined* and the three facts as separate lemmas;
(ii) the differential-identity half is already proved (more generally, sans bound) by the
project's own `MeasureR.exists_antideriv`, so shipping this whole bundle would duplicate
it; (iii) the constants (`p·`, `p(m+1)`) are c₀-design normalisations, not a literature
standard, so the "right" mathlib form (e.g. `‖coeff m C‖ ≤ p·m` for `m ≥ 1`, or a bound
phrased via `p^{v_p}`) is a taste call. The mathematically valuable, plausibly-mathlib
kernel is the *isolated* statement "the formal antiderivative of an integral series over
an ultrametric `ℚ_p`-algebra has coefficients bounded by `p·(m+1)`", stated against
mathlib's `derivativeFun`. Whether to invest in that factoring, and in exactly what
form, is the human decision.

**Numbered questions (≤5):**

1. Should the differential-existence half be considered *already covered* by the
   project's `MeasureR.exists_antideriv` (FormalPsi.lean:1169), so that only the
   **coefficient bound** is a fresh mathlib candidate (to be stated standalone against
   mathlib `derivativeFun`)? (yes → re-aim at the isolated bound; no → keep the bundle.)
2. Is mathlib willing to take a *bundled* existential of the shape `∃ C, (constant term)
   ∧ (a project-specific differential equation `p·(1+X)·∂C = B`) ∧ (a norm bound)`, or
   must it be split into a named antiderivative `def` plus separate lemmas before any
   PR? (This is the `/cleanup` item-12 STRUCTURE call.)
3. Is the differential operator `B ↦ p·(1+X)·∂C` a sufficiently general/recurring
   object to deserve mathlib API in its own right, or is it specific to this p-adic
   L-function (`L_p`) construction? (If specific, the result stays project-local.)
4. If the bound is upstreamed, what is the canonical normalisation — keep `p·(m+1)`, or
   state the sharper/cleaner `p^{v_p(m)}`-flavoured bound (`‖coeff m C‖ ≤ p·m` for
   `m ≥ 1`)? (Mathlib would want the canonical constant, not the c₀-design one.)
5. Is there downstream (outside this project) demand for "bounded formal antiderivatives
   over non-archimedean fields", or are the only consumers the two internal call sites?
   (No external demand → likely keep project-local.)

Next action: user answers the questions; then re-run `/mathlibable
PadicLFunctions.MeasureR.exists_antideriv_bounded` (or, if Q1 = yes, re-aim at the
isolated coefficient-bound lemma). Likely outcomes:
  - Q1 yes + Q4 picks a canonical constant → flips toward **YES-but-generalise-first**,
    target = a standalone `norm_coeff` bound on `derivativeFun` over an ultrametric
    `ℚ_p`-algebra (the identity coming from existing API).
  - Q2 "must split" + Q3/Q5 "project-specific, no external demand" → stays **project-local**
    (drop from mathlib consideration; keep the bundle as the internal helper it is).

---

## Next step

User answers the five questions above. If Q1 = yes, re-run aimed at the isolated
coefficient-bound lemma (`‖coeff m C‖ ≤ …` against mathlib `derivativeFun`); that is the
only piece with a plausible mathlib future. Otherwise the declaration remains a
well-justified **project-internal** helper (2 consumers, non-composable, but
over-bundled and constant-bespoke for mathlib's bar).
