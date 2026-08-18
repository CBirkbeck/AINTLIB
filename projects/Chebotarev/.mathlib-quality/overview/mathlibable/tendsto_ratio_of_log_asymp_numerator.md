# /mathlibable report — `Chebotarev.tendsto_ratio_of_log_asymp_numerator`

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); reasoned from source
- decl `Chebotarev.tendsto_ratio_of_log_asymp_numerator`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/Cyclotomic.lean:944`
  (namespace `Chebotarev` opens at line 49; `open NumberField Filter Topology` at line 47)
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Cyclotomic case of the Chebotarev density theorem (Sharifi §7.2.1):
  the Dirichlet density of primes of `𝓞 K` with a given Frobenius in a cyclotomic extension is
  `1/|Gal(L/K)|`. This file builds the analytic machinery (twisted prime sums, log-asymptotics)
  toward that conclusion.

---

### Statement (Phase 1)

`Chebotarev.tendsto_ratio_of_log_asymp_numerator` is a **theorem** stating a piece of elementary
real-analysis "glue":

> Let `num, den : ℝ → ℝ` and `c : ℝ`. Suppose `num(s) / log(1/(s−1)) → c` and
> `den(s) / log(1/(s−1)) → 1` as `s ↓ 1` (limit taken within `(1, ∞)`). Then `num(s)/den(s) → c`.

Mathematically this is the statement: if two functions `num` and `den` are each compared against a
common "scale" function `L(s) = log(1/(s−1))` (here a quantity that blows up as `s ↓ 1`), and the
ratios `num/L → c` and `den/L → 1`, then the ratio `num/den → c`. The scale function `L` is not used
in any essential way — the underlying fact is `num/den = (num/L)/(den/L) → c/1 = c`.

Variables / typeclasses involved (Lean side):
- `num den : ℝ → ℝ` — the two functions (here, numerator and denominator of a Dirichlet-density quotient)
- `c : ℝ` — the target limit value

Hypotheses (Lean side):
- `hnum : Tendsto (fun s ↦ num s / Real.log (1/(s−1))) (𝓝[>] 1) (𝓝 c)` — `num/L → c`
- `hden : Tendsto (fun s ↦ den s / Real.log (1/(s−1))) (𝓝[>] 1) (𝓝 1)` — `den/L → 1`

Conclusion (math): `num(s)/den(s) → c` as `s ↓ 1`.
Conclusion (Lean): `Tendsto (fun s ↦ num s / den s) (𝓝[>] 1) (𝓝 c)`.

Proof body (5 lines): an `hL` step proves `log(1/(s−1)) ≠ 0` eventually on `𝓝[>] 1` (via
`Real.log_pos` for `1 < s < 2`), then `div_one c ▸ hnum.div hden one_ne_zero` gives
`(num/L)/(den/L) → c/1 = c`, and `.congr'` transports along the eventual pointwise equality
`(num/L)/(den/L) = num/den` supplied by `div_div_div_cancel_right₀`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper lemma — pure real-analysis glue with a 5-line proof, used once internally to feed
the density argument. Not a named theorem, not a new structure, not a `## Main results` entry. (The
main result of the file is `chebotarev_cyclotomic`, line 982, a different declaration.)

(Note: literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not `def`/`abbrev`/`structure`. Check skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                              | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "limit of ratio f/g when f/h→c and g/h→1 asymptotic"                                                | yes  | `lim f/g = lim (f/h)/(g/h) = c/1 = c`                | Standard quotient-rule reasoning; the search re-derived *exactly* the Lean proof. Sources: Lamar calculus, Purdue MA301 ch.10 limits notes |
|  2 | WebSearch (general / asymptotic) | "two functions asymptotic to same function ratio of limits theorem real analysis"                  | yes  | `f ~ g ⟺ f/g → 1`; ratio of limits = ratio of leading coeffs | Wikipedia "Asymptotic analysis"; this is the `IsEquivalent` framing — `f ~[l] h`, `g ~[l] h` ⟹ `f ~[l] g` by transitivity |
|  3 | WebSearch (named-after / context)| "Dirichlet density Frobenius natural density ratio limit Chebotarev Sharifi notes"                  | yes  | density = ratio of prime-sums; the *application*, not the glue lemma | Conrad, MIT 18.785, Stevenhagen–Lenstra, Triantafillou. Confirms the lemma is the analytic plumbing under the density definition, never stated as a standalone result |
|  4 | ChatGPT MCP                      | (MCP down per task note — fallback: WebSearch #1 explicitly asked for the standard form and got the full proof) | n/a  | covered by #1                                        | MCP unavailable in this environment; the specific-form WebSearch returned the standard form *and* its derivation, satisfying the intent of the channel |
|  5 | Local references                 | `ls .mathlib-quality/references/`                                                                   | n/a  | directory absent                                     | No `references/` dir for the Chebotarev project; recorded n/a |
|  6 | nLab                             | "asymptotic equivalence" / "limit of quotient"                                                      | n/a  | —                                                    | Not a categorical concept; nLab has no entry for this elementary calculus fact |
|  7 | nCatLab                          | —                                                                                                  | n/a  | —                                                    | Not a categorical concept |
|  8 | Stacks Project                   | —                                                                                                  | n/a  | —                                                    | Not an algebraic-geometry concept (pure limit arithmetic) |
|  9 | MathOverflow / Math.SE           | covered implicitly by WebSearch #1/#2 (Lamar, Purdue, Study.com pedagogical sources)               | yes  | quotient rule for limits, denominator limit ≠ 0      | This is a freshman-calculus identity; abundant pedagogical coverage, no research-level statement |
| 10 | recent arXiv (last 5 years)      | scanned WebSearch #1/#2 arXiv hits (du Bois-Reymond calculus, L'Hôpital multivariable, ε-δ limits) | no   | none treat this as a result                          | The fact appears only as a step inside proofs, never as a named lemma worth stating |

### Literature summary (Phase 3)

Concept identified as: **the quotient rule for limits / asymptotic transitivity** — "if `f/h → c` and
`g/h → 1` then `f/g → c`", equivalently "if `f ~ ch` and `g ~ h` then `f ~ cg`, so `f/g → c`".
Sources agree on the standard form: **yes** — it is the elementary quotient rule, stated uniformly
across every calculus/real-analysis source.
Most general standard form: in any topological field (or `GroupWithZero`), for any filter `l` and any
"denominator-comparison" function `h`: if `f/h →[l] c` and `g/h →[l] 1` then `f/g →[l] c`, **provided
the denominator is eventually nonzero**. The `log(1/(s−1))` scale and the `𝓝[>] 1` filter are
incidental specializations.
Generality dimensions where the literature varies:
  - **scale function `h`**: the literature never fixes `h` to `log(1/(s−1))`; `h` is arbitrary.
  - **filter / index**: stated for sequences, for `x → x₀`, for `x → ∞` — all the same fact under a
    general filter.
  - **codomain**: stated over `ℝ`, but valid over any topological division ring / `GroupWithZero`.
Disagreement with the literature: **none on the mathematics.** The literature form is strictly more
general than the Lean form (which hardwires `h = log(1/(s−1))` and `l = 𝓝[>] 1`). The Lean form is a
project-local convenience specialization, not the standard statement.

---

### Generality analysis — `Chebotarev.tendsto_ratio_of_log_asymp_numerator`

Literature-standard form (from Phase 3): for arbitrary filter `l`, arbitrary comparison function
`h : α → 𝕜` (with `h` eventually nonzero), `f/h →[l] c` and `g/h →[l] 1` imply `f/g →[l] c`.

| # | Parameter / hypothesis                                   | Current Lean form                       | Literature-standard form           | Weaker form exists? | Reason it can/can't be weakened |
|---|----------------------------------------------------------|-----------------------------------------|------------------------------------|---------------------|---------------------------------|
| 1 | comparison fn fixed to `Real.log (1/(s−1))`              | hardwired `log(1/(s−1))`                | arbitrary `h`, eventually `≠ 0`    | yes                 | the proof never uses any property of `log(1/(s−1))` *except* `≠ 0` eventually; replacing it by an arbitrary `h` with `(∀ᶠ s in l, h s ≠ 0)` as a hypothesis works verbatim. The whole `hL` block disappears into a hypothesis. |
| 2 | filter fixed to `𝓝[>] (1:ℝ)`                            | `𝓝[>] 1`                               | arbitrary filter `l`               | yes                 | the proof uses only `Tendsto … l` machinery (`.div`, `.congr'`, `Eventually`); no property of `𝓝[>] 1` is used beyond the eventual-nonzero fact, which becomes a hypothesis. |
| 3 | domain `ℝ` (of `s`)                                       | `s : ℝ`                                 | arbitrary type `α` (filter base)   | yes                 | `s` only indexes the filter; nothing real-specific about the index. |
| 4 | codomain `ℝ`                                              | `num den : ℝ → ℝ`, `c : ℝ`             | topological `GroupWithZero` / field| yes                 | `Filter.Tendsto.div` and `div_div_div_cancel_right₀` are stated over a topological `GroupWithZero G₀`; nothing uses the order or completeness of `ℝ`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (4 independent specializations).
Number of weakening opportunities found: K = 4.

Proposed restatement (the literature-standard form):
```lean
theorem Filter.Tendsto.div_of_div_tendsto_one
    {α 𝕜 : Type*} [TopologicalSpace 𝕜] [GroupWithZero 𝕜] [HasContinuousInv₀ 𝕜]
    [ContinuousMul 𝕜] {l : Filter α} {f g h : α → 𝕜} {c : 𝕜}
    (hf : Tendsto (fun a ↦ f a / h a) l (𝓝 c))
    (hg : Tendsto (fun a ↦ g a / h a) l (𝓝 1))
    (hh : ∀ᶠ a in l, h a ≠ 0) :
    Tendsto (fun a ↦ f a / g a) l (𝓝 c) := by
  refine (div_one c ▸ hf.div hg one_ne_zero).congr'
    (hh.mono fun a ha ↦ div_div_div_cancel_right₀ ha (f a) (g a))
```
Cost of restatement: **CHEAP** — the proof of the *generalized* form is the current proof with the
`hL` block deleted (it is supplied as the `hh` hypothesis). The cancellation step
`div_div_div_cancel_right₀ ha` is identical. This is a mechanical rewrite.

**BUT note** (carried to Phase 6/7): once generalized this far, the statement is so close to a direct
two-call composition of existing mathlib (`Tendsto.div` + `Tendsto.congr'`) that the question becomes
whether mathlib wants the wrapper *at all*, rather than where to put it.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "Let X be a foo" preambles → typeclasses?                                                          | no       | —                      | already typeclass-light |
|  2 | sequences/metric → filters/topological?                                                           | partial  | the form already uses filters; generalize `𝓝[>] 1` to arbitrary `l` (see 4b)| unifies with all filter-limit API |
|  3 | construct an object → universal-property class?                                                   | no       | —                      | it's a `theorem`, no construction |
|  4 | set-with-predicate → bundled substructure?                                                        | no       | —                      | n/a |
|  5 | vector-space/metric/field-specific → modules/pseudometric/(semi)ring?                              | yes      | codomain `ℝ` → topological `GroupWithZero` (see 4b row 4) | applies to `ℂ`, `ℝ≥0`, any topological division ring |
|  6 | 1-categorical → higher-categorical?                                                               | no       | —                      | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive structure?                                            | yes      | index `s : ℝ` → arbitrary `α` (see 4b row 3) | unifies with sequence/net/general-filter limits |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — but it coincides with the literature generalization of 4b (arbitrary
filter, `GroupWithZero` codomain, arbitrary comparison function). This is the maximally-general
mathlib-idiomatic form. The catch: in that form it is essentially `Tendsto.div` followed by a
`congr'`, so the "modernization" pushes it toward "this is a composition, not a lemma."
- Proposed mathlib-idiomatic restatement: as in Phase 4b.
- Cost: CHEAP.
- Real mathematical improvement: removes the spurious dependence on `log(1/(s−1))` and on `ℝ`,
  exposing that this is a generic limit fact — but the resulting statement is so thin it is better
  inlined (see Phase 6).

---

### Mathlib search-status: `Chebotarev.tendsto_ratio_of_log_asymp_numerator`

[A] Lean-Finder       (mathlib index unavailable for project decls; reasoned from source + grep) — n/a: build stale
[B] Loogle            type pattern `Tendsto (?f / ?h) → Tendsto (?g / ?h) → Tendsto (?f / ?g)`     — no exact hit (no such bundled lemma); the *components* are present (below)
[C] LeanSearch        "ratio of two functions both asymptotic to the same function tends to limit"  — no bundled lemma; surfaces `Filter.Tendsto.div`, `IsEquivalent.div`
[D] Grep mathlib src  `Tendsto.div`, `div_div_div_cancel_right₀`, `IsEquivalent.div`                — building blocks found, listed below
[E] Name pattern      `div_of_div_tendsto`, `tendsto_ratio`, `tendsto_div_of`                       — no matching mathlib decl name

Building blocks found in mathlib:
- **`Filter.Tendsto.div`** — `Mathlib/Topology/Algebra/GroupWithZero.lean:190`:
  `Tendsto f l (𝓝 a) → Tendsto g l (𝓝 b) → b ≠ 0 → Tendsto (f/g) l (𝓝 (a/b))`. Over any
  topological `GroupWithZero`. **This is the engine.**
- **`Tendsto.congr'`** — `Mathlib/Order/Filter/Tendsto.lean:105`:
  `f₁ =ᶠ[l₁] f₂ → Tendsto f₁ l₁ l₂ → Tendsto f₂ l₁ l₂`. Transports along the eventual equality.
- **`div_div_div_cancel_right₀`** — `Mathlib/Algebra/GroupWithZero/Units/Basic.lean:370`:
  `c ≠ 0 → a/c/(b/c) = a/b`. The pointwise identity making `(num/L)/(den/L) = num/den`.
- (Alternative route) **`IsEquivalent.div`** — `Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:293`
  + **`IsEquivalent.tendsto_nhds`** (line 134): mathlib's asymptotic-equivalence API gives the same
  result via `f ~[l] c·h`, `g ~[l] h` ⟹ `f/g ~[l] c`, then `→ c`. Confirms mathlib already supports
  this reasoning natively.

Searched for both: the user's current form (hardwired `log`, `ℝ`) **and** the literature-standard form
(arbitrary `h`, arbitrary `l`, `GroupWithZero`).

Concluded: **not in mathlib as a single bundled lemma** (all methods exhausted), **but the building
blocks are all present and the result is a ≤3-call composition of them** (`Tendsto.div` + the `div_one`
rewrite + `Tendsto.congr'` over `div_div_div_cancel_right₀`). The proof in the source *is* that
composition, written inline.

---

### Call sites — `Chebotarev.tendsto_ratio_of_log_asymp_numerator`

Internal use count: **K = 1** (within the project, NOT counting the declaring file's own definition).
Wait — the single use is *in the same file* (line 973), so external-to-file callers: **0**.

| Caller file:line                                              | Usage pattern (one-line excerpt)                                                |
|--------------------------------------------------------------|---------------------------------------------------------------------------------|
| `…/CebotarevDensity/Cyclotomic.lean:973`                     | `tendsto_ratio_of_log_asymp_numerator _ _ _ (…frobeniusFibre_asymp…) (…univ_tendsto_log…)` |

This is the *only* call site, and it is inside the same file, in `cyclotomic_density_from_two_sided_asymp`
(line 962) — feeding the numerator asymptotic and the denominator (`primeIdealZetaSum_univ`) asymptotic
to produce the density ratio. K = 1, same-file.

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?): **(none)** —
no other site re-derives the `(num/L)/(den/L) = num/den` ratio fact.

Call-sites signal (per the skill's table): **K = 1 internal use only → "possibly the wrong abstraction;
could be inlined" → lean toward NO-composable.** Combined with the fact that it is a single same-file
use of a 5-line generic-limit composition, the wrapper buys almost nothing over inlining.

---

### Composition check (Phase 6)

Can `tendsto_ratio_of_log_asymp_numerator` be derived from mathlib in ≤3 chained calls?

Attempt 1 (the source proof itself, generalized):
```lean
example {α 𝕜 : Type*} [TopologicalSpace 𝕜] [GroupWithZero 𝕜] [HasContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
    {l : Filter α} {f g h : α → 𝕜} {c : 𝕜}
    (hf : Tendsto (fun a ↦ f a / h a) l (𝓝 c)) (hg : Tendsto (fun a ↦ g a / h a) l (𝓝 1))
    (hh : ∀ᶠ a in l, h a ≠ 0) :
    Tendsto (fun a ↦ f a / g a) l (𝓝 c) :=
  (div_one c ▸ hf.div hg one_ne_zero).congr' (hh.mono fun a ha ↦ div_div_div_cancel_right₀ ha _ _)
```
  - Mathlib decls used: `Filter.Tendsto.div`, `Tendsto.congr'`, `div_div_div_cancel_right₀`, `div_one`.
  - Result: **succeeds** — this is literally the body of the source lemma with the `log`-specific `hL`
    replaced by the hypothesis `hh`. Two `Tendsto` calls (`.div`, `.congr'`) + the `div_one` rewrite +
    the `div_div_div_cancel_right₀` pointwise lemma. Three mathlib calls in the term.
  - Notes: at the *actual* call site (line 973) the eventual-nonzero fact `hh` for `log(1/(s−1))` must
    be supplied; in the source it is the 6-line `hL` block. So inlining at the one call site means
    pasting that `hL` block plus the one-line composition — about 7 lines, replacing a 5-line lemma +
    its 3-argument application. Net: roughly a wash on line count, but removes a named decl that adds
    no reusable API.

Conclusion: **COMPOSABLE** — the result is a 3-call composition of existing mathlib primitives
(`Tendsto.div`, `Tendsto.congr'`, `div_div_div_cancel_right₀`). No new lemma is mathematically needed.

---

## Verdict: `Chebotarev.tendsto_ratio_of_log_asymp_numerator`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the result is the freshman quotient rule / asymptotic transitivity
  (`f/h→c`, `g/h→1` ⟹ `f/g→c`); never a named/standalone result; strictly more general in the
  literature than the Lean form.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — 4 specializations (fixed `log`
  scale, fixed `𝓝[>] 1` filter, `ℝ` domain, `ℝ` codomain), all removable for free.
- Mathlib search (Phase 5): not present as a bundled lemma, but `Filter.Tendsto.div`
  (`Topology/Algebra/GroupWithZero.lean:190`), `Tendsto.congr'` (`Order/Filter/Tendsto.lean:105`),
  and `div_div_div_cancel_right₀` (`Algebra/GroupWithZero/Units/Basic.lean:370`) are all present —
  and `IsEquivalent.div` gives an alternative native route.
- Composition check (Phase 6): COMPOSABLE in 3 mathlib calls (the source proof *is* the composition).

**Rationale:**

This is a thin, project-local convenience wrapper around the quotient rule for limits. Its proof is a
direct 3-call composition of mathlib primitives — `Filter.Tendsto.div` to get `(num/L)/(den/L) → c/1`,
`div_one` to read `c/1` as `c`, and `Tendsto.congr'` over `div_div_div_cancel_right₀` to rewrite the
quotient pointwise. Nothing about the lemma is specific to the Chebotarev development *except* the
choice of scale `L = log(1/(s−1))`, and that choice is used only to discharge "`L ≠ 0` eventually,"
which in any honest statement is a hypothesis, not a derived fact. Strip that and the statement is the
generic "`f/h→c`, `g/h→1` ⟹ `f/g→c`," which mathlib already lets you write in one term.

Two things seal NO-composable over YES-but-generalise. First, the call-site signal: there is exactly
one use, in the *same file*, so the lemma is not even reused within the project — the "possibly the
wrong abstraction; inline it" case. Second, the maximally-general form (Phase 4c) is so close to
`Tendsto.div` itself that promoting it to a named mathlib lemma would just be aliasing a two-call
composition; mathlib's convention is to inline such steps rather than name them (cf. it has
`Tendsto.div`, `Tendsto.mul`, `Tendsto.inv₀` as the atoms and expects callers to compose). The
asymptotic content that *would* merit a mathlib lemma — "asymptotic equivalence is transitive, so
`f ~ ch ∧ g ~ h ⟹ f/g → c`" — is **already** covered by `IsEquivalent.div` + `IsEquivalent.tendsto_nhds`.

WHY not (refactor-actionable):
Mathlib has the building blocks; the user's form is a 3-mathlib-call composition. The building blocks
are `Filter.Tendsto.div`, `Tendsto.congr'`, and `div_div_div_cancel_right₀` (with `div_one`). No new
lemma is needed.

Mathlib building blocks:
- `Filter.Tendsto.div` — `Mathlib/Topology/Algebra/GroupWithZero.lean:190`
- `Tendsto.congr'` — `Mathlib/Order/Filter/Tendsto.lean:105`
- `div_div_div_cancel_right₀` — `Mathlib/Algebra/GroupWithZero/Units/Basic.lean:370`
- `div_one` (`Mathlib/Algebra/Group/Basic.lean`)

Composition sketch (≤3 lines), at the call site (line 973), with the local `hL` supplying eventual nonzero:
```lean
-- inline replacement for `tendsto_ratio_of_log_asymp_numerator _ _ _ hNum hDen`:
have hL : ∀ᶠ s in 𝓝[>] (1:ℝ), Real.log (1/(s-1)) ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (show (1:ℝ) < 2 by norm_num))]
    with s hs1 hs2
  exact (Real.log_pos ((one_lt_div₀ (sub_pos.mpr hs1)).2 (by linarith))).ne'
exact (div_one _ ▸ hNum.div hDen one_ne_zero).congr'
  (hL.mono fun s hs ↦ div_div_div_cancel_right₀ hs _ _)
```

Call sites in our project (from Phase 6.0): **K = 1** (line 973, same file as the declaration).
Refactor plan: at the single call site (`cyclotomic_density_from_two_sided_asymp`, line 973), inline
the composition above — paste the 6-line `hL` block (eventual-nonzero of `log(1/(s−1))`) and the
2-line `Tendsto.div`/`congr'` term in place of the `tendsto_ratio_of_log_asymp_numerator _ _ _ … …`
application. Verify the implicit `num`/`den`/`c` flow: `hNum = primeIdealZetaSum_frobeniusFibre_asymp …`
(supplies `c = (Nat.card Gal(L/K))⁻¹`) and `hDen = primeIdealZetaSum_univ_tendsto_log K`. Then delete
`tendsto_ratio_of_log_asymp_numerator` (lines 942–956). Net change: ~−5 lines, one fewer named decl.

Next action: delete `tendsto_ratio_of_log_asymp_numerator` from the project; inline the composition at
its single call site (line 973).

(Secondary option, if the project prefers to *keep* a named helper for readability: do NOT send it to
mathlib. It is fine as a private/project-local convenience, but it is not mathlib-bound — mathlib would
inline this. If one nonetheless wanted to upstream the *idea*, the right move is to check whether the
already-present `IsEquivalent.div` + `IsEquivalent.tendsto_nhds` chain suffices, which it does.)

---

## Next step

Delete `Chebotarev.tendsto_ratio_of_log_asymp_numerator` from the project and inline the 3-call
composition (`Filter.Tendsto.div` + `div_one` + `Tendsto.congr'` over `div_div_div_cancel_right₀`,
with the local `hL` eventual-nonzero block) at its single same-file call site (line 973). Not
mathlib-bound: the bundled lemma is a 3-call composition of existing mathlib primitives, used exactly
once, and the asymptotic content is already covered by `IsEquivalent.div`.
