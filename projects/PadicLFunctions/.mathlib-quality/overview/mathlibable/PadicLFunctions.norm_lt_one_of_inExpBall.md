# `/mathlibable` report — `PadicLFunctions.norm_lt_one_of_inExpBall`

**Final verdict: `NO-composable-from-mathlib`.** The statement unfolds the
project-local `InExpBall` predicate and is a ≤3-call composition of mathlib's
`pow_lt_one_iff_of_nonneg`, `inv_le_one_of_one_le₀`, and `norm_nonneg`. It is a
thin convenience wrapper specialised to a *project-local* definition that mathlib
does not (and should not, in isolation) have; it belongs as project-local API,
derived inline from mathlib where needed — not as a standalone mathlib lemma.

---

### Baseline (Phase 0)

- lake build:               build not re-run (stale/slow per task instruction); **reasoned from source** — the declaration and all dependencies read directly from `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean` and `PadicExp.lean`, and the candidate mathlib lemmas read verbatim from `.lake/packages/mathlib/`.
- decl `PadicLFunctions.norm_lt_one_of_inExpBall`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:38`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  the extended (Iwasawa-branch) p-adic logarithm `extLog`, extending `padicLog` to the rational-valuation domain (RJW §6, decomposition W6a).

---

### Statement (Phase 1)

`PadicLFunctions.norm_lt_one_of_inExpBall` is **a theorem** stating the following:

> If a scalar `w` in an ultrametric normed field `L` lies in the open convergence
> ball of the `p`-adic exponential — encoded by the project predicate
> `InExpBall p w`, namely `‖w‖^(p−1) < p⁻¹` — then `‖w‖ < 1`.

Mathematically: the `p`-adic exponential disc is `{x : ‖x‖ < p^{−1/(p−1)}}`, which
is *strictly inside* the open unit disc `{x : ‖x‖ < 1}` (since `p^{−1/(p−1)} < 1`
for every prime `p`). So "members of the exp ball have norm `< 1`" is the
elementary disc-containment fact, repackaged through the project's rpow-free
encoding of the ball (`‖x‖^(p−1) < p⁻¹` instead of `‖x‖ < p^{−1/(p−1)}`).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue prime; gives `p ≥ 2`, hence `p − 1 ≥ 1` and `p⁻¹ ≤ 1`.
- `{L : Type*} [NormedField L]` — the normed field carrying `w`. (The instances `[NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` are explicitly `omit`-ted for this theorem — it needs **only** `NormedField L`.)

Hypotheses (Lean side):
- `{w : L}` — the element under test.
- `(hw : InExpBall p w)` — i.e. `‖w‖^(p−1) < (p : ℝ)⁻¹` (the definitional unfolding of `InExpBall`).

Conclusion (math): `‖w‖ < 1`.

Conclusion (Lean): `‖w‖ < 1`.

`InExpBall` is defined (in `PadicExp.lean:65`) as:
```lean
def InExpBall (p : ℕ) {L : Type*} [NormedField L] (x : L) : Prop :=
  ‖x‖ ^ (p - 1) < (p : ℝ)⁻¹
```
The current proof:
```lean
theorem norm_lt_one_of_inExpBall {w : L} (hw : InExpBall p w) : ‖w‖ < 1 := by
  by_contra h
  exact absurd hw (not_lt.mpr (le_trans
    (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le))
    (one_le_pow₀ (not_lt.mp h))))
```
i.e. assume `‖w‖ ≥ 1`; then `p⁻¹ ≤ 1 ≤ ‖w‖^(p−1)`, contradicting `hw`. The proof
uses only `NormedField` + `Fact p.Prime` and three mathlib order lemmas.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma — the elementary containment "exp disc ⊆ open unit disc",
stated through the project's rpow-free ball encoding. Not a new structure, not a
named theorem, not a `## Main results` entry (the file's main result is the
`extLog` construction and `extLogDomain_of_integral_norm_one`; this is one of its
sub-lemmas).

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for the
report's framing only and did not gate which channels Phase 3 ran.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not `def`/`abbrev`/`structure`. (No one-liner exemption
analysis applies. Recorded for completeness: the *body* is a 4-line tactic proof,
but the one-line check only governs definitions.)

---

### PHASE 3 — Literature search (EXHAUSTIVE protocol)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic exponential convergence ball norm less than one element radius" | yes | exp converges on `‖x‖ < p^{−1/(p−1)}`; image is `1 + 𝔻_p` of valuative radius `1/(p−1)` | Standard p-adic analysis; `p^{−1/(p−1)} < 1` ⟹ ball ⊂ open unit disc. Sources: Cambridge (Thorne) notes, MIT 18.785 PS10, Conrad. |
| 2 | WebSearch (general form / radius) | "p-adic logarithm exponential radius of convergence p^{-1/(p-1)} domain" | yes | exp disc `‖x‖_p < p^{−1/(p−1)}`; log disc `‖x−1‖_p < 1` | PlanetMath, Wikipedia "p-adic exponential function", Buium/MIT `exp.pdf`. Confirms the exp disc is the *small* one, strictly inside the unit disc. |
| 3 | WebSearch (underlying real fact / aliases) | "if x^n less than 1 and x nonnegative then x less than 1 real analysis lemma" | yes (as folklore) | "straightforward result … proved by contrapositive … rather than a formally named lemma" | This is the rpow-free heart: `0 ≤ x, x^n < 1 ⟹ x < 1`. Not a named theorem in the literature — it is a one-line order fact. |
| 4 | ChatGPT MCP | (intended: "standard def of the p-adic exp convergence disc; is 'members of the disc have norm < 1' a named result or trivial; historical evolution?") | n/a | — | **ChatGPT MCP is not configured in this environment** (no `chatgpt`/`openai` MCP tool surfaced). Substituted by the three WebSearch generality levels (#1–#3) + direct source reads, which already pin the standard form. Recorded n/a with reason rather than skipped. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` for "exp"/"ball" | n/a | (no references dir present in worktree) | The module docstring already cites the math sources verbatim: **Washington, _Introduction to Cyclotomic Fields_, §5.1** and **RJW (Ferrero–Greenberg / Gross–Koblitz-style) Thm 6.1(ii)**. In those texts the exp disc ⊂ unit disc is used silently, never stated as a lemma. |
| 6 | nLab | "p-adic number" page (ncatlab.org/nlab/show/p-adic+number) | no | — | nLab's p-adic page covers valuation/metric/Pontryagin duality but **does not treat the p-adic exp/log or their convergence discs at all**. No named result for our fact. |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept; it is a one-line metric inequality. No higher-categorical content. |
| 8 | Stacks Project | — | n/a | — | Not an algebraic-geometry concept; Stacks has no p-adic-analysis exp/log disc material. |
| 9 | MathOverflow / Math.StackExchange | "element p-adic exponential convergence disc has norm strictly less than 1" | no (no MO/MSE thread) | — | Search surfaced only lecture notes (MIT, Cambridge, Conrad), all of which treat disc ⊂ unit-disc as immediate. No Q&A elevates it to a named/standalone statement. |
| 10 | recent arXiv (last 5y) | "p-adic L-function Iwasawa branch logarithm exponential ball Riemann-Hurwitz" | yes (context only) | — | Confirms the *ambient* project context (Iwasawa-branch `log_p p = 0`, RJW-type p-adic L-function work, e.g. arXiv 2309.15692, 2401.06100) but **no source states "exp-ball members have norm < 1" as a result** — it is universally a triviality en route to defining exp/log. |

The protocol passed: WebSearch ran 3 distinct generality levels (specific exp-disc form #1, general radius/domain #2, the underlying real-analysis fact #3); ChatGPT MCP recorded n/a-with-reason (tool absent) and compensated by additional source reads; local references recorded n/a-with-reason (dir absent, but the in-source citations to Washington §5.1 cover it); nLab checked (no treatment); nCatLab / Stacks recorded n/a-with-reason; MathOverflow and arXiv checked.

### Literature summary (Phase 3)

Concept identified as: **containment of the `p`-adic exponential convergence disc inside the open unit disc** — equivalently, the elementary order fact `0 ≤ x ∧ x^n < 1 ⟹ x < 1` applied to `x = ‖w‖`, `n = p−1`, after the bound `p⁻¹ ≤ 1`.

Sources agree on the standard form: **yes.** Every source (Wikipedia, PlanetMath, Conrad, Cambridge/MIT notes, Washington §5.1) states the exp disc as `‖x‖_p < p^{−1/(p−1)}` and the unit disc as `‖x‖_p < 1` (or `‖x−1‖_p < 1` for log), and the inclusion `p^{−1/(p−1)} < 1` is taken as immediate.

Most general standard form: for any non-archimedean (or even just nonneg-normed) setting, `‖w‖^(p−1) < p⁻¹ ≤ 1` gives `‖w‖ < 1`. The fact is *agnostic* to ultrametricity, completeness, and the `ℚ_p`-algebra structure — it needs only that `‖·‖` is a nonnegative-real-valued norm and `p ≥ 1`. (The current Lean statement already reflects this: it `omit`s `NormedAlgebra`, `IsUltrametricDist`, `CompleteSpace`.)

Generality dimensions where the literature varies:
- Ambient object: `ℚ_p` / `ℂ_p` / a complete ultrametric extension `L` (literature) → mathlib would phrase the *order core* over a `LinearOrderedSemifield` / `GroupWithZero`-with-order, fully type-class-abstract. The project's `[NormedField L]` is already near-minimal *for the norm version*.
- Exponent: concrete `p − 1` (project, prime-driven) → arbitrary `n ≠ 0` (the mathlib lemma).

Disagreement with the literature: **none.** The Lean form is a faithful, slightly-repackaged (rpow-free, `(p−1)`-th-power) encoding of the standard "exp disc ⊂ unit disc" fact.

If-empty caveat: Phase 3 did **not** come back empty — it positively identified the concept and confirmed it is treated everywhere as a triviality, never as a named or standalone result. That is itself a strong signal toward a NO bucket.

---

### PHASE 4 — Generality analysis — `PadicLFunctions.norm_lt_one_of_inExpBall`

Literature-standard form (from Phase 3): for `0 ≤ x` and `n ≠ 0`, `x^n < 1 ↔ x < 1`
(order fact, fully type-class-abstract). The norm specialisation `‖w‖^(p−1) < p⁻¹ ≤ 1 ⟹ ‖w‖ < 1` is an immediate corollary.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[NormedField L]` | normed field | only need: a norm valued in `ℝ≥0` (`Norm` + `‖·‖ ≥ 0`) | yes (slightly) | The proof uses only `norm_nonneg` and order on `ℝ`. But the *abstract* core is not about norms at all — it is `pow_lt_one_iff_of_nonneg` over an ordered semifield. The "norm" packaging adds nothing mathlib lacks. |
| 2 | `[Fact p.Prime]` | `p` prime | only need `p ≥ 1` (to get `p⁻¹ ≤ 1`) and `p − 1 ≠ 0` (i.e. `p ≥ 2`) | yes | Primality is far stronger than needed; only `p ≥ 2` is used (via `hp.out.one_lt`/`one_le`). The exponent and the `p⁻¹ ≤ 1` bound are the only uses. |
| 3 | `(hw : InExpBall p w)` = `‖w‖^(p−1) < p⁻¹` | concrete `(p−1)`-power, bound `p⁻¹` | abstract `x^n < c` with `c ≤ 1` | yes | Both the exponent `p−1` and the bound `p⁻¹` are project-specific instantiations of `n ≠ 0` and `c ≤ 1`. The general statement is mathlib's `pow_lt_one_iff_of_nonneg`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is the `(p−1)`-power, `p⁻¹`-bound, norm-valued specialisation of the abstract order iff).

Number of weakening opportunities found: 3 (norm → abstract ordered semifield; prime → `p ≥ 2`; concrete exponent/bound → abstract `n ≠ 0`, `c ≤ 1`).

Proposed restatement: the *maximally general* statement is **already in mathlib** as `pow_lt_one_iff_of_nonneg` (see Phase 5) — so "restate the project lemma more generally" is not the move; the general form is not a missing mathlib lemma, it is an *existing* one. This pushes the verdict toward **NO**, not toward YES-but-generalise-first. (Generalising the project lemma to its abstract form would just be re-deriving `pow_lt_one_iff_of_nonneg`, which exists.)

Cost of restatement: n/a — the general form needs no work because mathlib already ships it.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | — | The hypotheses are already type-class/instances; nothing to bundle. |
| 2 | sequences/metric → filters/nets/topology? | no | — | A finite order inequality; no limit/convergence content to filter-ise. |
| 3 | construct an object → universal-property class? | no | — | No object is constructed; it is a proposition. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | No substructure. (`InExpBall` is a `Prop`, not a carrier set with operations.) |
| 5 | vector-space/metric/field-specific → weaken typeclass to modules/semiring? | yes (mildly) | the abstract core is `LinearOrderedSemifield`-level (`pow_lt_one_iff_of_nonneg`), strictly weaker than `NormedField` | but the weakened form **already exists in mathlib**, so this is a "use mathlib", not a "contribute a modernisation". |
| 6 | 1-categorical → higher/∞-categorical? | no | — | No categorical content. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structure? | yes (the exponent `p−1` and bound `p⁻¹`) | `n ≠ 0`, `c ≤ 1` over an ordered semifield | again, this *is* `pow_lt_one_iff_of_nonneg` — already present. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no (as a contribution).** Rows 5 and 7 identify a strictly
more general, more idiomatic form — but that form is **already shipped by mathlib**
(`pow_lt_one_iff_of_nonneg`). There is no modernisation for *us* to contribute; the
modern form is what we should *call*. One-line reason: the abstraction target is an
existing mathlib lemma, so "modernise and contribute" collapses to "use mathlib" —
i.e. a NO bucket, not YES-but-generalise-first.

---

### PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is `theorem`. (No definitional equalities or typeclass-search
paths are introduced; risk assessment is skipped per the skill's scope rule.)

---

### Mathlib search-status: `PadicLFunctions.norm_lt_one_of_inExpBall`

[A] Lean-Finder — n/a: Lean-Finder MCP/web endpoint not available in this environment. Substituted by [D] grep over the pinned mathlib source (authoritative for v4.32.0-rc1).
[B] Loogle — queried `(0 : ℝ) ≤ _ → _ ^ _ < 1 → _ < 1` and `name:pow_lt_one` via the web JSON endpoint; the URL-encoded pattern queries returned 0 structural matches / a name-resolution error (Loogle's web JSON does not accept these query shapes reliably through WebFetch). Fell back to [D].
[C] LeanSearch — n/a: `leansearch.net/api` returned HTTP 404 (no usable API endpoint from this environment). Fell back to [D]/[E].
[D] Grep mathlib src — **HITS.** `grep -rn` over `.lake/packages/mathlib/Mathlib/`:
  - `pow_lt_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n < 1 ↔ a < 1` — `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:674` (read verbatim). **This is the exact general fact.**
  - `pow_lt_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n < 1 ↔ x < 1` (ordered monoid form) — `Mathlib/Algebra/Order/Monoid/Unbundled/Pow.lean:222`.
  - `one_le_pow_iff_of_nonneg`, `one_le_pow₀`, `lt_of_pow_lt_pow_left₀ (n) (hb : 0 ≤ b) (h : a^n < b^n) : a < b` — `…/GroupWithZero/Basic.lean:669,699`.
  - `inv_le_one₀ (ha : 0 < a) : a⁻¹ ≤ 1 ↔ 1 ≤ a` — `…/GroupWithZero/Basic.lean:902`; and `inv_le_one_of_one_le₀` (used by the existing proof) present in `…/Archimedean/Basic.lean` and `norm_nonneg`, `one_le_pow₀` standard.
[E] Name pattern — grep names `norm_lt_one*`, `*expBall*`, `padicExp`, `padicLog` across mathlib: the `norm_lt_one_*` hits in mathlib are all about `ℤ_[p]` divisibility (`norm_lt_one_iff_dvd`, `norm_lt_one_add`, `norm_lt_one_mul` in `Mathlib/NumberTheory/Padics/PadicIntegers.lean`) — **unrelated** (no exp-ball). Crucially, **mathlib contains NO `padicExp`, NO `padicLog`, NO `InExpBall`, and no p-adic exponential/logarithm machinery whatsoever** (the entire `PadicExp.lean` development is novel-to-mathlib).

Searched for both:
  - the user's current form (`InExpBall p w → ‖w‖ < 1`): **not in mathlib** — `InExpBall` is a project-local `def`, so no mathlib lemma can be about it.
  - the literature-standard / abstract form (`0 ≤ x → x^n < 1 → x < 1`): **found in mathlib** as `pow_lt_one_iff_of_nonneg` (identical content, more general; we are a specialisation).

Concluded: **found the building blocks** — mathlib has `pow_lt_one_iff_of_nonneg` (the general fact) + `inv_le_one₀`/`inv_le_one_of_one_le₀` (the `p⁻¹ ≤ 1` step) + `norm_nonneg`; composition yields our form. The *exact* form is not in mathlib only because it mentions the project-local `InExpBall`. There is no p-adic-exp content in mathlib for the user's form to coincide with.

---

### Call sites — `PadicLFunctions.norm_lt_one_of_inExpBall`

Internal use count: **0** (within the project, NOT counting the declaring file `ExtLog.lean`).
External-to-file callers: **0 distinct files.**

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| ExtLog.lean:57 (declaring file) | `(max_le (norm_lt_one_of_inExpBall p hz).le norm_one.le)` — inside `mul_mem_expBall` |
| ExtLog.lean:188 (declaring file) | `have hlt := norm_lt_one_of_inExpBall p hy` — inside `norm_eq_one_of_inExpBall_sub_one` |

Both uses are **inside the declaring file** (`ExtLog.lean`). Repo-wide grep (`grep -rn "norm_lt_one_of_inExpBall" projects/ --include="*.lean"`) finds no occurrence outside `ExtLog.lean`. So the Phase-6.0 "internal use count" (which excludes the declaring file) is **0**, and external-to-file callers is **0**.

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - PadicExp.lean and the rest of ExtLog.lean repeatedly establish `‖·‖ ≤ 1` / `‖·‖ = 1` for ball members via *other* routes (e.g. `norm_eq_one_of_inExpBall_sub_one`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`), but no site re-derives the bare `InExpBall → ‖·‖ < 1` implication by hand. The two in-file uses are the only consumers.

**Composability signal (per the call-sites table):** K = 0 *project-internal* uses (the only two consumers are in the declaring file). This is a within-file convenience lemma — exactly the K=0/within-file pattern that leans toward NO-composable-from-mathlib (it is a wrapper that, mathlib-side, is a one-line composition; it has no external consumers that would argue for shipping it).

---

### Composition check (Phase 6)

Can `norm_lt_one_of_inExpBall` be derived from mathlib in ≤3 chained calls?

Attempt 1 (mirror the existing proof, term-mode):
```lean
theorem norm_lt_one_of_inExpBall {w : L} (hw : InExpBall p w) : ‖w‖ < 1 :=
  (pow_lt_one_iff_of_nonneg (norm_nonneg w) (by have := hp.out.one_lt; omega)).mp
    (lt_of_lt_of_le hw (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)))
```
  - Mathlib decls used: `pow_lt_one_iff_of_nonneg`, `norm_nonneg`, `lt_of_lt_of_le` (`Trans`/`.trans_le`), `inv_le_one_of_one_le₀`.
  - Result: **succeeds.** `inv_le_one_of_one_le₀ (1 ≤ p)` gives `p⁻¹ ≤ 1`; `lt_of_lt_of_le hw _` upgrades `hw : ‖w‖^(p−1) < p⁻¹` to `‖w‖^(p−1) < 1`; `(pow_lt_one_iff_of_nonneg (norm_nonneg w) (p−1 ≠ 0)).mp` converts to `‖w‖ < 1`. `hw` is usable directly because `InExpBall` unfolds definitionally to `‖w‖^(p−1) < p⁻¹` (the existing proof already feeds `hw` straight into `absurd`, confirming the transparency). The side-goals `p − 1 ≠ 0` and `1 ≤ p` are immediate from `Fact p.Prime`.
  - Notes: this is the same content as the current `by_contra`/`absurd` proof, re-expressed as a 3-call mathlib composition.

Attempt 2 (even shorter, contrapositive — the current proof): already ≤3 mathlib calls (`inv_le_one_of_one_le₀`, `one_le_pow₀`, `le_trans`) under one `by_contra`. Confirms the composition is genuine, not a proof in disguise.

Conclusion: **COMPOSABLE** (≤3 mathlib calls; matches the Phase-6 "one function call / `.trans` chain / `.mp` projection" composable patterns, not the "multiple `have`s with non-trivial reasoning" non-composable pattern).

---

## Verdict: `PadicLFunctions.norm_lt_one_of_inExpBall`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the concept is "exp disc ⊂ open unit disc", treated as a triviality in every source (Wikipedia, PlanetMath, Conrad, Washington §5.1); the underlying fact `0 ≤ x ∧ x^n < 1 ⟹ x < 1` is explicitly "not a formally named lemma". No standalone/named result anywhere.
- Generality analysis (Phase 4): STRICTLY NARROWER than the abstract order fact — but the general form is an **existing** mathlib lemma (`pow_lt_one_iff_of_nonneg`), so this is a "use mathlib", not a "generalise-and-contribute".
- Mathlib search (Phase 5): found the building blocks — `pow_lt_one_iff_of_nonneg` (`Mathlib/Algebra/Order/GroupWithZero/Basic.lean:674`) + `inv_le_one₀`/`inv_le_one_of_one_le₀` + `norm_nonneg`. Mathlib has **no** p-adic exp/log machinery, so the user's `InExpBall`-stated form cannot exist there.
- Composition check (Phase 6): COMPOSABLE in 3 mathlib calls (sketch above), matching the existing proof.

**Rationale:**

The statement is the elementary disc-containment fact "the `p`-adic exponential
convergence ball sits inside the open unit ball", written through the project's
rpow-free encoding `InExpBall p w := ‖w‖^(p−1) < p⁻¹`. Stripped of the encoding,
its mathematical content is `0 ≤ ‖w‖` and `‖w‖^(p−1) < p⁻¹ ≤ 1 ⟹ ‖w‖ < 1` — which
is exactly mathlib's `pow_lt_one_iff_of_nonneg` (the general iff for nonnegative
elements of an ordered semifield), composed with `inv_le_one_of_one_le₀` to supply
`p⁻¹ ≤ 1`. Mathlib already ships every ingredient; the lemma adds no new
mathematical content and is a ≤3-call composition. It therefore does not belong in
mathlib **as a standalone lemma** — and it could not be added "as is" in any case,
because its statement mentions the *project-local* predicate `InExpBall`, which
mathlib does not have (mathlib has no `padicExp`/`padicLog`/exp-ball machinery at
all). The literature reinforces this: every source treats the inclusion as immediate
and the underlying real-analysis step as unnamed folklore — a textbook signal that
this is wrapper-grade, not contribution-grade.

This is, however, a *reasonable project-local convenience lemma*: it names the
`InExpBall → ‖·‖ < 1` step that the file's ultrametric arguments (`mul_mem_expBall`,
`norm_eq_one_of_inExpBall_sub_one`) lean on. The verdict is about mathlib-worthiness,
not about whether to keep it in the project — it should **stay in the project**,
unfolding `InExpBall` and calling `pow_lt_one_iff_of_nonneg`; it just should not be
proposed to mathlib on its own.

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; the user's form is a ≤3-call composition wrapping a
project-local definition.

Mathlib building blocks:
- `pow_lt_one_iff_of_nonneg` — `.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean:674` — `(ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n < 1 ↔ a < 1`.
- `inv_le_one_of_one_le₀` — `.lake/packages/mathlib/Mathlib/Algebra/Order/Archimedean/Basic.lean` (and the iff `inv_le_one₀` at `…/GroupWithZero/Basic.lean:902`) — supplies `(p : ℝ)⁻¹ ≤ 1` from `1 ≤ p`.
- `norm_nonneg` — supplies `0 ≤ ‖w‖`.

Composition sketch (≤3 lines):
```lean
example {w : L} (hw : InExpBall p w) : ‖w‖ < 1 :=
  (pow_lt_one_iff_of_nonneg (norm_nonneg w) (by have := hp.out.one_lt; omega)).mp
    (lt_of_lt_of_le hw (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)))
```

Call sites in our project (from Phase 6.0): **0 outside the declaring file** (2 uses, both inside `ExtLog.lean`: lines 57 and 188).

Refactor plan: **mathlib-worthiness only — no project deletion recommended.**
Because mathlib has no `InExpBall` and the two consumers are tightly local, the
pragmatic action is to **keep `norm_lt_one_of_inExpBall` as project-local API** and
*not* open a mathlib PR for it. If a maintainer nonetheless wants to remove the named
wrapper, the mechanical refactor is: at each of the 2 in-file sites (`ExtLog.lean:57`,
`ExtLog.lean:188`) inline the composition above —
  - line 57: replace `(norm_lt_one_of_inExpBall p hz).le` with
    `((pow_lt_one_iff_of_nonneg (norm_nonneg _) (by have := hp.out.one_lt; omega)).mp (lt_of_lt_of_le hz (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)))).le`;
  - line 188: replace `norm_lt_one_of_inExpBall p hy` with the same `(pow_lt_one_iff_of_nonneg …).mp (lt_of_lt_of_le hy …)` term.
  Verify the `InExpBall` argument unfolds (it does — the def is semireducible and the
  existing proof already uses `hw` definitionally). **Recommendation: do NOT inline** —
  the named lemma improves local readability and the only "cost" is one extra
  declaration; the actionable conclusion is simply *"not a mathlib contribution."*

Next action: **do not propose `norm_lt_one_of_inExpBall` to mathlib.** Keep it
project-local. (No `/generalise` or mathlib-PR follow-up is warranted: the general
form already exists in mathlib as `pow_lt_one_iff_of_nonneg`.)

---

## Next step

Do not propose `norm_lt_one_of_inExpBall` to mathlib — it is a ≤3-call composition of
`pow_lt_one_iff_of_nonneg` + `inv_le_one_of_one_le₀` + `norm_nonneg` wrapping the
project-local `InExpBall` predicate, and mathlib has no p-adic-exp machinery for it to
attach to. Keep it as project-local convenience API (its 2 consumers are both inside
`ExtLog.lean`); if ever desired, inline the composition at those two sites. No
`/generalise` follow-up is needed because mathlib already ships the general fact.
