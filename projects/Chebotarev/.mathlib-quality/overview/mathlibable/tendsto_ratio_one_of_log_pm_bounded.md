# /mathlibable report — `tendsto_ratio_one_of_log_pm_bounded`

Project: Chebotarev (CebotarevDensity)
Decl site: `projects/Chebotarev/CebotarevDensity/ForMathlib/LogOneDivSubOne.lean:79`
Run date: 2026-06-18
Tooling note: `ChatGPT MCP` (Codex) was down this session (`Codex failed`); used WebSearch + Loogle (JSON endpoint) + mathlib-source grep as fallbacks. Local Lean build not re-run (stale per task brief); reasoned from source + mathlib source tree at `.lake/packages/mathlib`.

---

## Baseline (Phase 0)
- lake build:               not re-run (stale per task brief); mathlib source tree present at `.lake/packages/mathlib`
- decl `tendsto_ratio_one_of_log_pm_bounded`: ✓ resolved at `…/ForMathlib/LogOneDivSubOne.lean:79`
- kind:                      theorem
- has sorry:                 no
- qualified name:            `tendsto_ratio_one_of_log_pm_bounded` (ROOT namespace — file has **no** `namespace` block, only `noncomputable section` + `open Filter Topology`)
- module docstring summary:  "Limit lemmas for `log (1 / (s - 1))` near `s = 1`" — purely analytic limit facts; module explicitly says these "live in the root namespace as candidates for upstreaming to mathlib."

---

## Statement (Phase 1)

`tendsto_ratio_one_of_log_pm_bounded` states: for any `f : ℝ → ℝ`, if on a right
neighbourhood of `1` we have `f(s) ≤ log(1/(s−1)) + C₁` and `log(1/(s−1)) − C₂ ≤ f(s)`
(i.e. `f` differs from `log(1/(s−1))` by a two-sided additive bounded error), then
`f(s) / log(1/(s−1)) → 1` as `s ↓ 1`.

Mathematically this is the standard "asymptotic equivalence under bounded additive
perturbation of a divergent function", **specialised** to the single denominator
`g(s) = log(1/(s−1))` and the single filter `l = 𝓝[>] 1`. The analytic content is
entirely carried by the fact `log(1/(s−1)) → +∞` as `s ↓ 1`.

Variables / typeclasses (Lean side):
- `f : ℝ → ℝ` — an arbitrary real function (the numerator).
- (no typeclass parameters; everything is concrete `ℝ`.)

Hypotheses (Lean side):
- `h_le : ∃ C, ∀ᶠ s in 𝓝[>] 1, f s ≤ log(1/(s−1)) + C` — eventual upper bound.
- `h_lower : ∃ C, ∀ᶠ s in 𝓝[>] 1, log(1/(s−1)) − C ≤ f s` — eventual lower bound.

Conclusion (math): `f(s)/log(1/(s−1)) → 1` as `s ↓ 1`.
Conclusion (Lean): `Tendsto (fun s : ℝ ↦ f s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1)`.

**Proof body (verbatim):**
```lean
tendsto_ratio_one_of_div_atTop_pm_bounded tendsto_log_one_div_sub_one_atTop h_le h_lower
```
A single function application: it plugs the project's own divergence lemma
`tendsto_log_one_div_sub_one_atTop` (`log(1/(s−1)) → atTop`) and the two bound
hypotheses into the project's own **general** squeeze
`tendsto_ratio_one_of_div_atTop_pm_bounded`. There is **no** new analytic reasoning
in this lemma beyond instantiating `g := log(1/(s−1))`, `l := 𝓝[>] 1`.

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper specialisation — not a `def`/`class`/`structure`, not named after a
person/place, not a `## Main results` primary goal in its own right (it IS listed in the
file's local "Main results", but only as the `g = log(1/(s−1))` specialisation of the
generic squeeze immediately above it). Its proof is a one-line instantiation of a sibling
lemma. (Literature width run EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure` — the one-liner def signal does not
formally apply. **However** the spirit applies strongly: the proof body is a single
substantive line (`tendsto_ratio_one_of_div_atTop_pm_bounded … … …`), a pure
specialisation of a sibling lemma. Recorded as a one-line *theorem* wrapper; carried into
Phase 6/7 as a strong "inline / specialise-at-use" signal.

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                          | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|--------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "limit f/g = 1 when f − g bounded and g → ∞ asymptotic equivalence"                                     | yes  | `f/g = 1 + (f−g)/g → 1`, with `(f−g)/g → 0`                  | Physics Forums / Rice big-O notes / Wolfram AsymptoticEqual: the textbook one-line algebra |
|  2 | WebSearch (general form)         | "f ~ g asymptotically if f−g bounded and g → ∞ standard analysis"                                       | yes  | def of asymptotic equivalence: `f ~ g ⟺ f/g → 1`            | Wikipedia "Asymptotic analysis"; bounded-difference ⇒ ratio→1 is a derived remark, not a named theorem |
|  3 | WebSearch (named-after / aliases)| "mathlib4 IsEquivalent bounded difference tendsto atTop ratio one"                                      | yes  | `Asymptotics.IsEquivalent`, `isEquivalent_iff_tendsto_one`   | leanprover-community docs; the mathlib API name for `f/g → 1` is `IsEquivalent` |
|  4 | ChatGPT MCP                      | (standard-form + shortest-mathlib-proof question)                                                       | n/a  | —                                                            | **Codex backend DOWN this session** (`Codex failed: Command failed`); substituted by channels 1–3 + Loogle + mathlib-source reading |
|  5 | Local references                 | grep `.mathlib-quality/references/`                                                                     | n/a  | (directory absent)                                           | `projects/Chebotarev/.mathlib-quality/` has only `overview/`; no `references/` dir |
|  6 | nLab                             | "asymptotic equivalence" / "asymptotic order"                                                           | n/a  | —                                                            | nLab has no dedicated page for this elementary real-analysis fact; it is not a categorical concept |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | —                                                            | Not a categorical concept |
|  8 | Stacks Project (alg geom)        | —                                                                                                      | n/a  | —                                                            | Not an algebraic-geometry concept |
|  9 | MathOverflow / Math.SE           | (covered via WebSearch #1–#2; Physics Forums + StackExchange-style notes surfaced)                      | yes  | same as #1: `1 + (f−g)/g → 0`                               | Confirms it is folklore one-line algebra, not a citable named theorem |
| 10 | recent arXiv (last 5 yr)         | "Sharifi Algebraic Number Theory Dirichlet density log(1/(s−1)) prime ideal zeta"                       | yes  | density def uses `Σ N𝔭⁻ˢ / log(1/(s−1)) → δ`                | Kedlaya 18.785 / Harvard 229 notes: confirms the *application* (Dirichlet density) but the ratio→1 step is again unnamed folklore |

### Literature summary (Phase 3)

Concept identified as: **asymptotic equivalence under a bounded additive perturbation of a divergent function** — i.e. "if `g → ∞` and `f − g` is bounded then `f ~ g`, hence `f/g → 1`."
Sources agree on the standard form: **yes**. Every source reduces it to the same one line: `f/g = 1 + (f−g)/g`, and `(f−g)/g → 0` because the numerator is bounded and the denominator diverges.
Most general standard form: `f ~[l] g` (equivalently `f/g →[l] 1`) whenever `g →[l] atTop` (or `‖g‖ → ∞`) and `f − g =O[l] 1` (eventually bounded). This is **denominator-agnostic and filter-agnostic**.
Generality dimensions where the literature varies:
  - denominator `g`: the literature states it for an **arbitrary** divergent `g`; the target lemma fixes `g = log(1/(s−1))`.
  - filter / variable: literature uses an arbitrary filter / `x → ∞`; the target fixes `l = 𝓝[>] 1`.
  - scalar field: literature is over `ℝ` (or any `LinearOrderedField`/normed field); target is `ℝ`.
Disagreement with the literature: **none** — but the literature standard is *strictly more general* than the target on two axes (denominator and filter). It is NOT a named theorem; it is the definition of `~` plus one line of algebra.

---

## Generality analysis (Phase 4)

Literature-standard form (Phase 3): `g →[l] atTop` ∧ `(f − g)` eventually bounded ⟹ `f/g →[l] 1`, for **arbitrary** `g`, `l`.

### 4a. Generality status table

| # | Parameter / hypothesis             | Current Lean form                        | Literature-standard form          | Weaker / more general form exists? | Reason |
|---|------------------------------------|------------------------------------------|-----------------------------------|------------------------------------|--------|
| 1 | denominator                        | fixed `g = Real.log (1/(s−1))`           | arbitrary divergent `g`           | **YES** — and it already exists in this very file | The general `g` version is the sibling `tendsto_ratio_one_of_div_atTop_pm_bounded` (line 60), of which this lemma is a one-application instance |
| 2 | filter                             | fixed `l = 𝓝[>] (1 : ℝ)`                 | arbitrary filter `l`              | **YES** — sibling lemma already takes `{l : Filter ℝ}` | The only use of `𝓝[>] 1` here is to feed `tendsto_log_one_div_sub_one_atTop`; the squeeze itself is filter-generic |
| 3 | numerator `f`                      | arbitrary `f : ℝ → ℝ`                    | arbitrary `f`                     | no (already fully general)         | — |
| 4 | scalar field                       | `ℝ`                                      | normed/linear-ordered field       | yes (in principle)                 | sibling lemma is also `ℝ`-only; orthogonal to this lemma's role |

### 4b. Generality verdict

The current form is: **STRICTLY NARROWER THAN STANDARD** (and narrower than its own in-file sibling).
Number of weakening opportunities: 2 primary (denominator, filter) — both *already realised* by the sibling `tendsto_ratio_one_of_div_atTop_pm_bounded`.
Proposed "restatement": there is nothing to restate — the maximally-general project form **already exists one declaration above** (`tendsto_ratio_one_of_div_atTop_pm_bounded`, line 60). The target lemma is the *specialisation*, not a candidate to be generalised in place.
Cost: n/a (no regeneralisation needed; the general form is already present).

### 4c. Modern mathlib-idiom check (Bourbaki 2.0)

| # | Question                                                                 | Applies? | Proposed reformulation | Downstream this enables |
|---|--------------------------------------------------------------------------|----------|------------------------|--------------------------|
| 1 | bundled hyps → typeclasses/instances?                                     | no       | hypotheses are eventual inequalities, not structure | — |
| 2 | sequences/metric → filters/topological?                                  | partial  | already filter-based via `Tendsto`/`𝓝[>]`; the *general* form (sibling) is the filter-clean one | the general sibling already composes with all filter limit API |
| 3 | construction → universal-property class?                                  | no       | nothing constructed | — |
| 4 | set+predicate → bundled substructure?                                     | no       | — | — |
| 5 | field-specific → weaken typeclasses?                                      | partial  | could go to normed/ordered field, but that's a property of the *sibling*, not this wrapper | scalar generality |
| 6 | 1-categorical → higher-categorical?                                       | no       | — | — |
| 7 | concrete index → arbitrary group/monoid?                                  | **YES**  | replace fixed `g = log(1/(s−1))` by arbitrary divergent `g` (and `𝓝[>]1` by arbitrary `l`) | **this is exactly the sibling lemma `tendsto_ratio_one_of_div_atTop_pm_bounded`** |

Modern idiom verdict: The modern/idiomatic form is precisely the **denominator-and-filter-general** statement — which is the sibling lemma, already in the file. For *that* general lemma, mathlib's idiomatic route is the `IsEquivalent` API:
`(f − g) =O[l] (1) → (g →[l] atTop) → (1 : _) =o[l] g → (f − g) =o[l] g → IsLittleO.isEquivalent → f ~[l] g → isEquivalent_iff_tendsto_one → f/g → 1`.
So the upstreaming question belongs to the **sibling**, not to this log-specific wrapper. For this wrapper specifically: no modernisation move exists that keeps the `log(1/(s−1))` denominator and still belongs in mathlib — a `log(1/(s−1))`-specific lemma is not a general mathlib object.

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

## Mathlib search-status (Phase 5)

[A] Lean-Finder       (web endpoint not reachable this session)            n/a: endpoint down; substituted by [B]+[D]
[B] Loogle            `Tendsto _ _ atTop → Tendsto (fun _ => _ / _) _ (nhds 1)`   **no hits** (JSON: count 0; 124 decls scanned, 0 match pattern) — mathlib has NO lemma concluding `f/g → 1` directly from `g → atTop`
[B'] Loogle           `Asymptotics.IsEquivalent, Filter.atTop`              24 hits; **none** derive `IsEquivalent` from bounded-difference + divergence (hits are: add-const, tendsto-of-equiv, summability, log-equiv, polynomial, Akra–Bazzi)
[C] LeanSearch        natural-language query                                n/a: leansearch.net returned 404/405 this session
[D] Grep mathlib src  `tendsto_bdd_div_atTop_nhds_zero`, `isEquivalent_iff_tendsto_one`, `IsLittleO.isEquivalent`, `IsEquivalent.add_isLittleO` over `.lake/packages/mathlib`  **building blocks found** (see below); no packaged end-to-end lemma
[E] Name pattern      grep `tendsto_ratio_one`, `ratio_one`, `log_one_div_sub_one` in mathlib tree  **no hits** — these names are project-local only

Building blocks confirmed present in mathlib (by source line):
- `tendsto_bdd_div_atTop_nhds_zero` — `Mathlib/Topology/Algebra/Order/Field.lean:264` (`b ≤ f ≤ B` eventually ∧ `g → atTop` ⟹ `f/g → 0`). **This is what the sibling lemma uses.**
- `Filter.Tendsto.inv_tendsto_nhdsGT_zero` — `Mathlib/Topology/Algebra/Order/Field.lean:80` (used in `tendsto_log_one_div_sub_one_atTop`).
- `Asymptotics.isEquivalent_iff_tendsto_one` — `Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:208`.
- `Asymptotics.IsLittleO.isEquivalent` — same file, line 166 (`(u−v) =o[l] v → u ~[l] v`).
- `Asymptotics.IsEquivalent.add_isLittleO` / `isEquivalent_of_tendsto_one` — same file, lines 147 / 196.

Searched for both:
  - the user's current (log-specific) form → **not in mathlib** (a `log(1/(s−1))`-specific limit lemma is not, and should not be, in mathlib).
  - the literature-standard (general `g`) form → **not packaged as a single lemma in mathlib**, but its building blocks are all present, and the project itself already packages it as the sibling `tendsto_ratio_one_of_div_atTop_pm_bounded`.

Concluded: **not in mathlib as a named lemma (the log-specific target nor the general bounded-perturbation lemma); the building blocks are all present (`tendsto_bdd_div_atTop_nhds_zero`, the `IsEquivalent` API), and the general form is a ≤3-call composition.** For the *target* specifically: it is a one-application specialisation of a project-local general lemma to a project-specific denominator — it composes from the project's own sibling in **one** call.

---

## Composition check (Phase 6)

### 6.0 Call sites — `tendsto_ratio_one_of_log_pm_bounded`

Internal use count: **1** (within the project, excluding the declaring file).
External-to-file callers: **1 distinct file**.

| Caller file:line          | Usage pattern (one-line excerpt)                                                         |
|---------------------------|-------------------------------------------------------------------------------------------|
| `Density.lean:528`        | `tendsto_ratio_one_of_log_pm_bounded (primeIdealZetaSum (univ …)) (…_le_log_plus_bounded K) (log_minus_bounded_le_… K)` |

Inline-derivation grep: the denominator `Real.log (1 / (s - 1))` appears across
`Density.lean`, `ZetaProduct.lean`, `CyclotomicNormResidue.lean`, `Cyclotomic.lean`, but
those call sites use the **general** sibling `tendsto_ratio_one_of_div_atTop_pm_bounded` or
the divergence lemma `tendsto_log_one_div_sub_one_atTop` directly — **not** this wrapper.
So this wrapper has a single consumer (`primeIdealZetaSum_univ_tendsto_log`).

Call-sites signal (per skill table): **K = 1 internal use only ⟹ "possibly the wrong abstraction — could be inlined; lean toward NO-composable."**

### 6a. Composition attempt

Can `tendsto_ratio_one_of_log_pm_bounded` be derived in ≤3 chained calls? **Yes, in ONE.**

Attempt 1 (using the project's own general lemma — its actual proof body):
```lean
tendsto_ratio_one_of_div_atTop_pm_bounded tendsto_log_one_div_sub_one_atTop h_le h_lower
```
  - Decls used: `tendsto_ratio_one_of_div_atTop_pm_bounded` (project sibling) + `tendsto_log_one_div_sub_one_atTop` (project divergence lemma).
  - Result: **succeeds** — this *is* the lemma's body. A single application.

Attempt 2 (purely from mathlib, for the general sibling — to confirm even the parent is composable):
```lean
-- (f - g) =O 1 (from the two-sided bound) and g → atTop give (f-g) =o g; then:
(IsLittleO.isEquivalent (hbd.trans_isLittleO (isLittleO_one_left_of_tendsto_atTop hg))
  ).tendsto_div_nhds_one  -- ≈ via isEquivalent_iff_tendsto_one
```
  - Decls used: `IsLittleO.isEquivalent`, `isLittleO` of `1` vs a divergent `g`, `isEquivalent_iff_tendsto_one`. ~3 calls.
  - Result: **succeeds** (idiomatic mathlib route for the general parent).

Conclusion: **COMPOSABLE.** The target is a single application of a project-local general lemma; that general lemma is in turn a ≤3-call mathlib composition.

### 6b. Heuristic check
The composition is a single function application (`f (g) h₁ h₂`) — squarely in the
"composable: one function call" row, not a disguised proof.

---

## Verdict: `tendsto_ratio_one_of_log_pm_bounded`

**Category: NO-composable-from-mathlib**

**Evidence:**
- Literature (Phase 3): textbook folklore (`f/g = 1 + (f−g)/g → 1`); not a named theorem; the standard form is denominator- and filter-**general**, strictly broader than the target.
- Generality (Phase 4): **STRICTLY NARROWER THAN STANDARD** — the target fixes `g = log(1/(s−1))` and `l = 𝓝[>]1`; the maximally-general project form already exists one declaration above (the sibling `tendsto_ratio_one_of_div_atTop_pm_bounded`).
- Mathlib search (Phase 5): no packaged lemma (Loogle: 0 hits for `g → atTop ⟹ f/g → 1`; 0 of 24 `IsEquivalent` hits derive it from bounded difference); all building blocks present (`tendsto_bdd_div_atTop_nhds_zero`, `IsLittleO.isEquivalent`, `isEquivalent_iff_tendsto_one`).
- Composition (Phase 6): **COMPOSABLE** — the target's own body is a single application of the project sibling; K = 1 call site.

**Rationale:**

`tendsto_ratio_one_of_log_pm_bounded` is not a mathlib candidate in its own right: it is a
`log(1/(s−1))`-specific, `𝓝[>]1`-specific **specialisation** of the general bounded-perturbation
squeeze. Its denominator is a Dirichlet-density object, not a general mathlib quantity, so a
"as-is" upstreaming would put a number-theory-flavoured limit lemma into mathlib's analysis
library — exactly the wrong grain. The mathlibable object, if any, is the **general** sibling
`tendsto_ratio_one_of_div_atTop_pm_bounded` (arbitrary `g`, arbitrary `l`), and even that is a
≤3-call composition of existing mathlib primitives (`tendsto_bdd_div_atTop_nhds_zero`, or the
`IsLittleO.isEquivalent` + `isEquivalent_iff_tendsto_one` route). The target lemma itself
composes in a **single** application from that sibling, and has exactly **one** consumer
(`primeIdealZetaSum_univ_tendsto_log`, `Density.lean:528`). This is the canonical "one-call
wrapper, K = 1, narrower than its own sibling" pattern → NO-composable, keep it project-local.

(The relevant upstreaming conversation — "should mathlib have the general bounded-additive-
perturbation ⟹ asymptotic-equivalence lemma?" — is about the **sibling**
`tendsto_ratio_one_of_div_atTop_pm_bounded`, and should be run as a separate `/mathlibable`
on that declaration. This report is only about the log specialisation.)

**WHY not (refactor-actionable):**
Mathlib has the building blocks; the target's form is a **1-call** specialisation of a
project-local general lemma (whose own derivation from mathlib is ≤3 calls). No new mathlib
lemma is warranted for the log-specific form.

Mathlib building blocks (for the general parent, should it be upstreamed separately):
- `tendsto_bdd_div_atTop_nhds_zero` — `Mathlib/Topology/Algebra/Order/Field.lean:264`
- `Asymptotics.IsLittleO.isEquivalent` — `Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:166`
- `Asymptotics.isEquivalent_iff_tendsto_one` — `Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:208`

Composition sketch (the target's actual body — a single application of the project sibling):
```lean
example (f : ℝ → ℝ)
    (h_le : ∃ C, ∀ᶠ s in 𝓝[>] (1:ℝ), f s ≤ Real.log (1/(s-1)) + C)
    (h_lower : ∃ C, ∀ᶠ s in 𝓝[>] (1:ℝ), Real.log (1/(s-1)) - C ≤ f s) :
    Tendsto (fun s : ℝ ↦ f s / Real.log (1/(s-1))) (𝓝[>] 1) (𝓝 1) :=
  tendsto_ratio_one_of_div_atTop_pm_bounded tendsto_log_one_div_sub_one_atTop h_le h_lower
```

Call sites in our project (from Phase 6.0): **K = 1** (`Density.lean:528`).

Refactor plan:
1. **Keep the general sibling `tendsto_ratio_one_of_div_atTop_pm_bounded`** — it is the real reusable analytic content and the legitimate upstreaming candidate (run `/mathlibable tendsto_ratio_one_of_div_atTop_pm_bounded` separately to decide YES-add vs YES-generalise-to-`IsEquivalent`).
2. **`tendsto_ratio_one_of_log_pm_bounded` is optional sugar.** Because it has exactly one consumer, it may be inlined at `Density.lean:528`: replace
   `tendsto_ratio_one_of_log_pm_bounded (primeIdealZetaSum (univ …)) (…_le_… K) (…_le_… K)`
   with
   `tendsto_ratio_one_of_div_atTop_pm_bounded tendsto_log_one_div_sub_one_atTop (…_le_… K) (…_le_… K)`
   (argument order is identical; only the head lemma changes and `tendsto_log_one_div_sub_one_atTop` is threaded explicitly). The wrapper can then be deleted, OR kept as a readability convenience — but it is **not** a mathlib contribution either way.
3. **Do NOT upstream the log-specific form.** A `log(1/(s−1))`-specific limit lemma does not belong in mathlib's analysis tree.

Next action: do not submit this declaration to mathlib. Inline at `Density.lean:528` (or keep as local sugar), and run a **separate** `/mathlibable` on the general sibling `tendsto_ratio_one_of_div_atTop_pm_bounded` — that is where the genuine upstreaming decision lives (likely `YES-but-generalise-first`, restating via `Asymptotics.IsEquivalent`).
