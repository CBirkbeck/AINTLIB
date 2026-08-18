# `/mathlibable` report — `PadicLFunctions.ValuesAtOneComplex.tendsto_sum_pow_div_eq_neg_log`

**Final verdict: `YES-add-as-is`** (boundary value of the complex logarithm series; the
`z ∈ ∂𝔻 \ {1}` analogue of mathlib's interior `Complex.hasSum_taylorSeries_neg_log`, and the
direct sibling of mathlib's `Real.tendsto_sum_pi_div_four`).

---

### Baseline (Phase 0)

- lake build:               not re-run; reasoned from source (per task build note — `lake build` stale/slow here; read decl + dependencies directly)
- decl `PadicLFunctions.ValuesAtOneComplex.tendsto_sum_pow_div_eq_neg_log`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOneComplex.lean:94`
- kind:                      theorem
- has sorry:                 no (proof is complete, ~84 lines)
- module docstring summary:  "The classical value L(θ,1) (RJW §6.1, Thm 6.1(i)) — complex-analysis quarantine file, stated against mathlib's `DirichletCharacter.LFunction`."

Mathlib source tree present at `.lake/packages/mathlib/Mathlib`; all dependency lemmas confirmed by grep.

---

### Statement (Phase 1)

`tendsto_sum_pow_div_eq_neg_log` is a theorem stating the following:

> For `z ∈ ℂ` on the unit circle (`‖z‖ = 1`) with `z ≠ 1`, the power series `∑ zⁿ/n` converges
> at the boundary point `z`, and its value is `−Log(1 − z)`. Concretely, the partial sums
> `S_N = Σ_{n<N} z^{n+1}/(n+1)` tend to `−Log(1 − z)` as `N → ∞` (`Log` = principal complex logarithm).

This is the **boundary** case of the Mercator/Taylor series of `−Log(1−z)`: the interior case
(`‖z‖ < 1`) is standard and already in mathlib, but the value *on* the circle (where the series only
converges conditionally) is the delicate part, classically resolved by Abel's limit theorem.

Variables / typeclasses involved (Lean side):
- `{z : ℂ}` — the boundary point (implicit).
- `{N : ℕ} [NeZero N]` — file-level `variable`, **not used** by this theorem (it is a section variable
  for the surrounding Dirichlet-character lemmas; this theorem is independent of it).

Hypotheses (Lean side):
- `(hz : ‖z‖ = 1)` — `z` lies on the unit circle.
- `(hz1 : z ≠ 1)` — `z` is not the exceptional point where the series diverges.

Conclusion (math): the radial-boundary value of `∑ zⁿ/n` at `z` is `−Log(1−z)`.

Conclusion (Lean):
```lean
Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ (n + 1) / (n + 1))
  Filter.atTop (nhds (-Complex.log (1 - z)))
```

**Proof shape (read from source).** (1) `z.re < 1` from `‖z‖ = 1, z ≠ 1`. (2) Partial geometric sums
`Σ z^{i+1}` are uniformly bounded by `2/‖1−z‖` (`geom_sum_eq`). (3) Dirichlet/Abel-summation test
(`Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded` with `1/(n+1) ↓ 0`) ⇒ the series is Cauchy,
hence converges to some `l`. (4) Identify `l = −Log(1−z)` via Abel's limit theorem
(`Complex.tendsto_tsum_powerSeries_nhdsWithin_lt`) applied along the radius `x·z, x → 1⁻`, the interior
expansion `Complex.hasSum_taylorSeries_neg_log`, continuity of `clog` on `slitPlane`
(`Filter.Tendsto.clog`), and uniqueness of limits (`tendsto_nhds_unique`).

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: It is a named classical analysis fact (boundary value of the logarithm series via Abel's
theorem). Not a person's-name theorem, but it is the kind of self-contained, library-grade analytic
result that has its own textbook treatment and an exact structural twin already in mathlib
(`Real.tendsto_sum_pi_div_four`, the Leibniz π/4 series).

(Note: literature width was EXHAUSTIVE regardless of size.)

### One-line check (Phase 2b)

Body line count: ~84 substantive lines.
One-liner verdict: **n/a** — kind is `theorem`, not a `def`/`abbrev`/`structure`. Section skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                          | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|--------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "power series sum z^n/n converges to -log(1-z) on boundary unit circle z≠1 Abel theorem"               | yes  | `Σ_{n≥1} zⁿ/n = −Log(1−z)` on `‖z‖=1, z≠1` (Abel's theorem) | Wikipedia/Waterloo/LibreTexts: "Abel's test states the series converges everywhere on the closed unit circle except possibly at z=1"; value given by Abel's theorem |
|  2 | WebSearch (general form)         | "logarithm series convergence boundary of disk of convergence Abel limit theorem log(1-z)"             | yes  | same; complex-power-series Abel needs Stolz-sector approach  | IISc/OSU complex-analysis lecture notes; Gronwall 1916 (JSTOR) "On the Power Series for log(1+z)" — the dedicated classical reference |
|  3 | WebSearch (named-after / aliases)| "Mercator series logarithm sum z^n/n boundary unit circle Stein Shakarchi"                             | yes  | Mercator / Newton–Mercator series `Σ(−1)^{n+1}x^n/n`         | The series is the Mercator/Newton–Mercator series; radius 1; boundary value is the Abel-theorem application |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of the boundary log series")             | n/a  | —                                                            | `plugin:mathlib-quality:chatgpt-math` server **failed to connect** (manifest path `/home/chris/...` does not exist on this darwin machine). Recorded n/a; compensated with 4 extra WebSearch/WebFetch queries (#1–3, #9–10) |
|  5 | Local references                 | grep `.mathlib-quality/references/` and `refs/PadicLFunctions/` for "log"/"Abel"                        | n/a  | (no references dir)                                          | Neither `projects/PadicLFunctions/.mathlib-quality/references/` nor `refs/` exists in this checkout — recorded n/a |
|  6 | nLab                             | "nLab Abel's theorem power series boundary convergence"                                                | no   | no dedicated nLab page surfaced                              | nLab has no specific entry for this boundary identity; concept is classical real/complex analysis, not categorical |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                                            | Not a categorical concept (elementary complex analysis) |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | —                                                            | Not an algebraic-geometry concept |
|  9 | MathOverflow / Math.StackExchange| "convergence series z^n/n on circle equals negative log Abel summation by parts complex"               | yes  | confirms: `a_n=1/n` series has its only circle singularity at z=1; converges elsewhere by Abel criterion | ResearchGate/Harvard pset corroborate; matches the source proof's Dirichlet-test + Abel structure |
| 10 | recent arXiv (last 5 years)      | "logarithm power series boundary unit circle conditional convergence value" (2023–2024)                | no   | nothing new — it is classical                                | arXiv has only generic boundary-behaviour papers; no recent restatement, consistent with this being a 19th-century textbook result |
| 11 | WebFetch — Wikipedia Abel's thm  | full-text fetch of `en.wikipedia.org/wiki/Abel's_theorem`                                              | yes  | standard form: real `G(x)=Σaₖxᵏ`, `Σaₖ` conv ⇒ left-continuous at 1; complex form via Stolz sector | Confirms canonical statement; its worked log example is the *sibling* `Σ(−1)^k/(k+1)=ln2` |
| 12 | WebFetch — Keith Conrad blurb    | `kconrad.../abelthm.pdf` "Boundary Behavior of Power Series: Abel's Theorem"                            | yes (via search snippet; direct fetch ECONNREFUSED) | `g(x)=Σ(−1)^{n−1}xⁿ/n → log 2` by Abel; states circle behaviour "much more delicate" | Canonical lecture reference. Direct PDF fetch refused (transient); content recovered from the search-engine snippet of the same document |

The protocol passed: WebSearch ran ≥3 distinct queries at three generality levels (specific form #1,
general form #2, named-after/Mercator #3, plus arXiv-recent #10); ChatGPT MCP was attempted and is
genuinely unavailable (n/a with reason + compensating queries); local references checked (absent, n/a);
nLab checked (no entry); Stacks/nCatLab recorded n/a with reason; MathOverflow checked (hit); arXiv
checked (classical, nothing new).

### Literature summary (Phase 3)

Concept identified as: **the boundary value of the Mercator / `−Log(1−z)` power series**, i.e. the
canonical worked **application of Abel's limit theorem** (Abel 1826) to the series `Σ zⁿ/n` on the unit
circle. Dedicated classical reference: Gronwall, *On the Power Series for log(1+z)* (1916). Standard
textbook treatments: Stein–Shakarchi *Complex Analysis*, Keith Conrad's "Boundary Behavior of Power
Series" blurb, LibreTexts/Encyclopedia of Mathematics.

Sources agree on the standard form: **yes**. The series `Σ_{n≥1} zⁿ/n` (radius of convergence 1)
converges at every point of the unit circle except `z = 1` (Dirichlet's test, since the partial sums of
`zⁿ` are bounded for `z≠1` and `1/n ↓ 0`), and by Abel's theorem its sum there equals `−Log(1−z)`. Sign
convention matches the Lean statement exactly (the Lean theorem writes `−Complex.log (1 − z)`).

Most general standard form: for `z` on the closed unit disk minus `{1}`, `Σ zⁿ/n = −Log(1−z)`; the
interior part (`‖z‖<1`, absolute convergence) is routine, and the boundary part (`‖z‖=1, z≠1`,
conditional convergence) is exactly this theorem.

Generality dimensions where the literature varies:
  - **domain of `z`**: interior `‖z‖<1` (easy, in mathlib) vs. boundary `‖z‖=1, z≠1` (this theorem) vs.
    "closed disk minus 1" (the union). The maximal natural statement over `ℂ` is the closed-disk-minus-1
    form; this theorem is precisely its non-trivial half.
  - **approach mode for Abel**: radial (real `x→1⁻`) vs. Stolz-sector/non-tangential. The literature's
    strongest complex form uses Stolz sectors; this theorem only needs the value *at* `z` itself (the
    series converges *at* `z`, so a radial Abel approach suffices — no Stolz cone needed). This is the
    *right* amount of generality for a boundary-*value* statement.

Disagreement with the literature: **none**. The Lean form is the literature-standard boundary statement
with the standard sign convention.

---

### Generality analysis — `tendsto_sum_pow_div_eq_neg_log`

Literature-standard form (from Phase 3): for `z` on the unit circle, `z ≠ 1`,
`Σ_{n≥1} zⁿ/n = −Log(1−z)`; equivalently the partial sums converge to `−Log(1−z)`.

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form    | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|--------------------------|------------------------------|---------------------|----------------------------------|
| 1 | `{z : ℂ}`              | a complex number         | a complex number on `∂𝔻`     | NO                  | The statement is inherently about `ℂ` and the principal `Complex.log`; there is no weaker scalar structure for "logarithm of `1−z`" |
| 2 | `(hz : ‖z‖ = 1)`      | exactly on the circle    | on the circle                | NO (not weaker; could be *combined* with the interior) | The interior `‖z‖<1` case is a *separate* theorem already in mathlib (`hasSum_taylorSeries_neg_log`); this theorem is correctly the boundary half. One could state a unified `‖z‖≤1 ∧ z≠1` version, but that is a *merge*, not a weakening, and is awkward because the proofs differ (absolute vs. conditional convergence) |
| 3 | `(hz1 : z ≠ 1)`       | exclude the bad point    | exclude `z=1`                | NO                  | At `z=1` the series is the harmonic series `Σ1/n`, which diverges; the hypothesis is sharp and necessary |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**
Number of weakening opportunities found: **0** (the hypotheses `‖z‖=1` and `z≠1` are both sharp; the
domain `ℂ` is forced by `Complex.log`).
Proposed restatement: none required on generality grounds.
Cost of restatement: n/a.

Note: the only "more inclusive" statement would be the closed-disk union `(‖z‖<1 ∨ (‖z‖=1 ∧ z≠1))`,
combining this with mathlib's interior `hasSum_taylorSeries_neg_log`. That is a packaging choice for the
PR, not a generalisation that this declaration is failing to reach — see Phase 7 PR-grouping note.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances? | no | — | No structure-defining preamble; `z` is a bare element with two propositional hypotheses |
|  2 | sequences/metric → filters/nets/topological? | **already done** | — | The statement is *already* filter-based: `Filter.Tendsto … Filter.atTop (nhds …)`. This is the idiomatic mathlib form. No improvement available |
|  3 | construction → universal-property class? | no | — | It is an equality of limits, not a construction |
|  4 | set-with-closure-predicate → bundled substructure? | no | — | No substructure involved |
|  5 | vector-space/metric/field-specific → weaker typeclass? | no | — | `Complex.log` pins the scalar to `ℂ`; no module/semiring weakening is meaningful |
|  6 | 1-categorical → higher-categorical? | no | — | Elementary analysis; no categorification target |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | — | The index `n+1` is the genuine summation index of a `ℂ`-valued series; not generalisable |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
One-line reason: the statement is already in mathlib's idiomatic filter form (`Tendsto … atTop … nhds`)
over `ℂ`; there is no contemporary reformulation that organises it better.

**One presentational refinement worth flagging for the PR (not a verdict-changer, not a generality
gap):** mathlib's interior sibling is phrased as `HasSum (fun n => zⁿ/n) (−log(1−z))`
(`hasSum_taylorSeries_neg_log`). To compose cleanly with that naming/idiom, the upstreamed version
should *also* expose a `HasSum`-style corollary
`HasSum (fun n : ℕ => z ^ n / n) (-Complex.log (1 - z))` (the partial-sum `Tendsto` here is equivalent
to `HasSum` once re-indexed, as the proof's own `hreindex` step shows). This is a `/cleanup`/packaging
task, not a generalisation of the statement.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `tendsto_sum_pow_div_eq_neg_log`

[A] Lean-Finder       (intended NL+type queries)                       n/a: Lean-Finder MCP not available in this environment
[B] Loogle            `Tendsto (fun N => ∑ _ ∈ range N, _ ^ _ / _) _ (nhds (-Complex.log _))` ; `HasSum (fun n => ?z ^ n / n) (-Complex.log _)`  n/a: `lean_loogle` MCP not available; pattern recorded for reproducibility
[C] LeanSearch        "series z^n over n converges to minus log of one minus z on unit circle" n/a: `lean_leansearch` MCP not available
[D] Grep mathlib src  `tendsto_sum_pow`, `neg_log`/`log_one_sub` + `tendsto`/`sum`, `hasSum_taylorSeries_neg_log`, `tendsto_tsum_powerSeries` (over `.lake/packages/mathlib/Mathlib`)  **hits on building blocks, NO hit on the boundary value**
[E] Name pattern      `tendsto_sum_pow_div`, `sum_pow_div`, `neg_log` boundary lemmas  no hit on the target form

Searched for both:
  - the user's current form (partial-sum `Tendsto … atTop (nhds (-Complex.log (1 - z)))`) — **not in mathlib**.
  - the literature-standard / `HasSum` boundary form (`HasSum (z^n/n) (-log(1-z))` for `‖z‖=1, z≠1`) — **not in mathlib**.

**What IS in mathlib (building blocks, all confirmed by grep with file:line):**
- `Complex.hasSum_taylorSeries_neg_log` — `Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean:281`:
  `HasSum (fun n => zⁿ/n) (-log(1-z))` for `‖z‖ < 1` (the **interior** version only).
- `Complex.tendsto_tsum_powerSeries_nhdsWithin_lt` — `Mathlib/Analysis/Complex/AbelLimit.lean:247`:
  Abel's limit theorem along the radius `(𝓝[<]1).map ofReal`.
- `Complex.tendsto_tsum_powerSeries_nhdsWithin_stolzCone` / `…_stolzSet` — `AbelLimit.lean:241/161`:
  general Abel limit theorems (Stolz sector / set).
- `Real.tendsto_sum_pi_div_four` — `Mathlib/Analysis/Real/Pi/Leibniz.lean:23`: **the exact structural
  sibling** — Leibniz's `Σ(−1)ⁱ/(2i+1) = π/4`, proved by the *same recipe* (alternating/Dirichlet
  convergence + `tendsto_tsum_powerSeries_nhdsWithin_lt` + identify the boundary function). Mathlib
  shipping this for `arctan` but not for `log` is precisely the gap.
- Dependency lemmas used by the proof, all present: `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`
  (`SpecificLimits/Normed.lean:741`), `tendsto_one_div_add_atTop_nhds_zero_nat`, `Filter.Tendsto.clog`
  (`Complex/Log.lean:257`), `geom_sum_eq`, `cauchySeq_tendsto_of_complete`, `tendsto_nhds_unique`.

Concluded: **not in mathlib** (all available methods exhausted: grep + name-pattern over the full
mathlib tree, plus the literature-standard `HasSum` boundary form). Mathlib has the **interior** value
and the **Abel limit machinery** and the **`arctan` sibling**, but not this **boundary value of the
log series**.

---

### Call sites — `tendsto_sum_pow_div_eq_neg_log`

Internal use count: **1** (within the same project; NOT counting the declaring line).
External-to-file callers: **0 distinct files** (used only inside its own file).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/PadicLFunctions/PadicLFunctions/ValuesAtOneComplex.lean:388` | `refine (tendsto_sum_pow_div_eq_neg_log hw hw1).congr fun N => ?_` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `tendsto_sum_pow_div_eq_neg_log`?):
  - (none) — no other file re-derives the boundary log-series limit. Within this same file,
    `tendsto_LSeries_pow_boundary` (line 271) *uses* it via the call above to pin `g 1 = −log(1−w)`;
    it does not re-derive it.

**Reading.** K = 1 internal use. By the Phase-6 table this is the "K=1 → possibly wrong abstraction"
row, which *for a project-internal helper* would lean NO-composable. **But that heuristic is overridden
here**: the single use is genuinely load-bearing (it is the boundary base case for the file's main
theorem `LFunction_one_eq` = RJW Thm 6.1(i)), the result is **not** composable from mathlib in ≤3 calls
(Phase 6 below), and — decisively — it is a standalone classical analysis lemma that mathlib's own
parallel file structure already blesses (`Real.tendsto_sum_pi_div_four` has analogously few internal
uses and lives in mathlib on its mathematical merits). Low local call-count is a composability signal
for *wrapper* lemmas; this is not a wrapper, it is a theorem with content.

### Composition check (Phase 6)

Can `tendsto_sum_pow_div_eq_neg_log` be derived from mathlib in ≤3 chained calls?

Attempt 1: `(Complex.hasSum_taylorSeries_neg_log ?).tendsto_sum_nat` — apply the interior series result.
  - Mathlib decls used: `Complex.hasSum_taylorSeries_neg_log`.
  - Result: **fails**. `hasSum_taylorSeries_neg_log` requires `‖z‖ < 1`; here `‖z‖ = 1`. It does not
    apply at the boundary at all — the series is only conditionally convergent there, and `HasSum`
    (unconditional) is genuinely false in general at `‖z‖=1`. There is no specialisation route.

Attempt 2: `Complex.tendsto_tsum_powerSeries_nhdsWithin_lt h` for some convergence hypothesis `h`.
  - Mathlib decls used: `Complex.tendsto_tsum_powerSeries_nhdsWithin_lt`.
  - Result: **partial / fails as a composition**. Abel's theorem gives the *radial* limit
    `lim_{x→1⁻} Σ f n (xz)ⁿ`, which is one half of the argument — but using it requires *first* proving
    the boundary series converges at all (so that the radial limit equals the boundary value), and that
    convergence is itself the Dirichlet-test step. You cannot invoke Abel's theorem and be done; you
    must independently establish convergence at `z`, then match the two limits via `tendsto_nhds_unique`
    and continuity of `clog`. This is exactly what the 84-line proof does.

Conclusion: **NOT-COMPOSABLE**. A faithful proof needs at minimum: (i) the geometric partial-sum bound
`geom_sum_eq`, (ii) the Dirichlet/Abel-summation convergence test
`Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded` + completeness, (iii) Abel's limit theorem
`tendsto_tsum_powerSeries_nhdsWithin_lt`, (iv) `Filter.Tendsto.clog` continuity on `slitPlane`, and
(v) `tendsto_nhds_unique`. That is five distinct nontrivial mathlib facts glued by real reasoning
(`re < 1`, re-indexing, a `tsum_congr`) — far beyond a ≤3-call composition, and structurally identical
to how mathlib justifies shipping `Real.tendsto_sum_pi_div_four` as its own theorem rather than inlining.

---

## Verdict: `tendsto_sum_pow_div_eq_neg_log`

**Category:** `YES-add-as-is`

**Evidence:**
- Literature search (Phase 3): classical, textbook — the canonical worked application of Abel's limit
  theorem (Abel 1826; Gronwall 1916; Stein–Shakarchi; Keith Conrad). Standard form `Σ zⁿ/n = −Log(1−z)`
  on `‖z‖=1, z≠1`, sign convention matching the Lean statement. ≥3 WebSearch channels + WebFetch +
  MathOverflow + arXiv-recent; ChatGPT MCP genuinely unavailable (n/a + compensating queries).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — hypotheses `‖z‖=1` and `z≠1` are both sharp,
  the domain `ℂ` is forced by `Complex.log`; Phase 4c found **no modern idiom** available (the statement
  is already in mathlib's filter form). 0 weakening opportunities.
- Mathlib search (Phase 5): **not in mathlib**. Mathlib has the *interior* version
  `Complex.hasSum_taylorSeries_neg_log`, Abel's limit theorem `tendsto_tsum_powerSeries_nhdsWithin_lt`,
  and the *`arctan` sibling* `Real.tendsto_sum_pi_div_four`, but not this boundary value of the log
  series.
- Composition check (Phase 6): **NOT-COMPOSABLE** — five distinct nontrivial mathlib facts glued by real
  reasoning; the interior `HasSum` lemma does not apply at `‖z‖=1`.

**Rationale (1–2 paragraphs):**

This is the boundary-value half of the complex logarithm's power series, and it is genuinely missing
from mathlib. Mathlib's `Complex.hasSum_taylorSeries_neg_log` proves `Σ zⁿ/n = −Log(1−z)` only in the
*open* disk `‖z‖ < 1`, where the series converges absolutely; the value on the *circle* (where the
series converges merely conditionally, by Dirichlet's test, at every point except `z=1`) is the delicate
classical statement that Abel's limit theorem exists to deliver. Mathlib already contains the *exact
parallel* of this theorem for a different function: `Real.tendsto_sum_pi_div_four`
(`Mathlib/Analysis/Real/Pi/Leibniz.lean`) proves Leibniz's `Σ(−1)ⁱ/(2i+1) = π/4` by the identical recipe
— establish conditional convergence, invoke `tendsto_tsum_powerSeries_nhdsWithin_lt`, and identify the
boundary function (`arctan` there, `−Log(1−·)` here). The fact that mathlib ships the `arctan` instance
but not the `log` instance, while housing every building block (the Abel machinery in
`Analysis/Complex/AbelLimit.lean`, the interior log expansion in `…/Complex/LogBounds.lean`), is the
concrete gap this declaration fills.

The form is right: maximally general (sharp hypotheses, the only domain `Complex.log` admits), already
in mathlib's idiomatic filter formulation, and not reducible to a short composition (Phase 6 shows the
interior `HasSum` lemma simply does not apply at the boundary, and a faithful proof needs five separate
nontrivial facts glued by real analysis). The single internal call site does **not** make it a wrapper —
it is a content-bearing classical theorem, exactly the profile of its mathlib sibling. The verdict is
therefore `YES-add-as-is`, with the one presentational note (Phase 4c) that the PR should additionally
expose a `HasSum`-style corollary to sit naturally beside `hasSum_taylorSeries_neg_log`.

**WHY add it (refactor-actionable):**
- **New mathematical content mathlib is missing:** the *boundary* value of the Mercator/`−Log(1−z)`
  series on `‖z‖=1, z≠1`. Mathlib has only the interior (`hasSum_taylorSeries_neg_log`, open disk) and
  the abstract Abel machinery; the assembled boundary statement for `log` is absent.
- **The specific gap, named:** `Mathlib/Analysis/Real/Pi/Leibniz.lean` proves the *exact analogue* for
  `arctan` (`Real.tendsto_sum_pi_div_four`) using `tendsto_tsum_powerSeries_nhdsWithin_lt`, but no file
  provides the corresponding boundary statement for the complex logarithm — despite
  `Analysis/SpecialFunctions/Complex/LogBounds.lean` (interior) and `Analysis/Complex/AbelLimit.lean`
  (Abel) both existing. This is a recognised, recurring derivation (it is *the* canonical Abel-theorem
  example in textbooks) that users currently must redo by hand, as this project did.
- **How it composes with mathlib's API:** it is the natural boundary companion to
  `Complex.hasSum_taylorSeries_neg_log`; once present, it specialises to give classical evaluations such
  as `Σ (−1)ⁿ⁺¹/n = log 2` and (via roots of unity) the closed forms for Dirichlet-character L-values at
  `s=1` — the very use this file makes. It also lets future analytic-number-theory developments (boundary
  values of L-series, `LFunction θ 1`) cite a library lemma instead of re-deriving Abel summation.

Proposed mathlib location: `Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean` (next to
`hasSum_taylorSeries_neg_log`), or a new `Mathlib/Analysis/SpecialFunctions/Complex/LogBoundary.lean`
importing `Analysis/Complex/AbelLimit`.
Proposed PR title: `feat(Analysis): boundary value of the logarithm series — Σ zⁿ/n = −Log(1−z) on ‖z‖=1, z≠1`
PR grouping (if applicable): ship together with a `HasSum (fun n => zⁿ/n) (−log(1−z))` corollary
(matching `hasSum_taylorSeries_neg_log`'s shape); optionally also a unified "closed disk minus 1"
statement merging this with the interior lemma. Consider mirroring the `Real.tendsto_sum_pi_div_four`
style/location so the two boundary results sit in parallel. The project's `gaussSum_mul_coprime` (same
file) is a *separate* number-theory contribution and should **not** be bundled into this analysis PR.
Pre-PR checklist before opening:
  - [ ] `/generalise tendsto_sum_pow_div_eq_neg_log` — confirm no easy further weakening (expected:
        none; hypotheses already sharp).
  - [ ] `/cleanup ValuesAtOneComplex.lean tendsto_sum_pow_div_eq_neg_log` — full audit; in particular
        add the `HasSum` corollary and align naming with `hasSum_taylorSeries_neg_log`.
  - [ ] Pick a mathlib reviewer from recent `Mathlib/Analysis/Complex/AbelLimit.lean` /
        `…/SpecialFunctions/Complex/LogBounds.lean` history (e.g. the Abel-limit / log-bounds authors).

---

## Next step

Run `/generalise tendsto_sum_pow_div_eq_neg_log` (expected: confirms maximal generality, hypotheses
already sharp), then `/cleanup ValuesAtOneComplex.lean tendsto_sum_pow_div_eq_neg_log` to add a
`HasSum`-form corollary and align the statement/naming with mathlib's interior
`Complex.hasSum_taylorSeries_neg_log`; then open the PR at
`Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean`, mirroring the `Real.tendsto_sum_pi_div_four`
(Leibniz) pattern, with the project's own `gaussSum_mul_coprime` kept to a separate number-theory PR.
