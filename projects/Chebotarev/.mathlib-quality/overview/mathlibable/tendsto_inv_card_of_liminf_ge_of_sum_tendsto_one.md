# /mathlibable report — `Chebotarev.tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one`

_Step-9 overview mathlibable assessment, single declaration, full workflow._

### Baseline (Phase 0)
- lake build:               ✗ stale (local build is stale per task note; target name is
  `Chebotarev.CebotarevDensity.Abelian` via module `CebotarevDensity.Abelian`, not directly buildable
  in this session). Assessment reasons from source — the statement + proof were read in full.
- decl `Chebotarev.tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/Abelian.lean:1502`
- kind:                      theorem
- has sorry:                 no
- namespace:                 `Chebotarev` (opened `Abelian.lean:56`, closed `:1595`; no nested namespace)
- module docstring summary:  Chebotarev density theorem, abelian case (Sharifi 7.2.2 Step 2) — proves the
  Dirichlet density of Frobenius-fibre primes is `1/|G|`.

---

### Statement (Phase 1)

`tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` is a **pure real-analysis pigeonhole lemma**:

> Let `ι` be a finite type with `N = |ι|`, and let `g : ι → ℝ → ℝ` be a finite family of real
> functions. Along the filter `l = 𝓝[>] (1 : ℝ)` (the right neighbourhood of `1`), suppose
> (1) each `gᵢ` has `liminf gᵢ ≥ 1/N`; (2) each `gᵢ` is bounded below; (3) the pointwise sum
> `s ↦ Σᵢ gᵢ(s)` tends to `1`. Then every `gᵢ` tends to `1/N`.

The mechanism is an asymmetric pigeonhole on `liminf`/`limsup`: the `N` lower bounds `1/N` sum to `1`,
which is exactly the limit of the total; this leaves no slack, so each `gᵢ` is pinned to `1/N` from
below (hypothesis) and from above (the complementary sum already accounts for `(N-1)/N` of the total
`limsup`).

Variables / typeclasses (Lean side):
- `{ι : Type*} [Fintype ι]` — the (finite) index set; `N := Fintype.card ι`.
- `(g : ι → ℝ → ℝ)` — the family, with fixed domain/codomain `ℝ`.
- `(i₀ : ι)` — the index whose convergence is concluded (also witnesses `Nonempty ι`).

Hypotheses (Lean side):
- `hlo : ∀ i, (Fintype.card ι : ℝ)⁻¹ ≤ Filter.liminf (g i) (𝓝[>] 1)` — uniform lower bound `1/N`.
- `hbelow : ∀ i, Filter.IsBoundedUnder (· ≥ ·) (𝓝[>] 1) (g i)` — below-boundedness (genuinely needed,
  per docstring; in a conditionally complete order a finite `liminf` bound alone does not force it).
- `hsum : Filter.Tendsto (fun s ↦ ∑ i, g i s) (𝓝[>] 1) (𝓝 1)` — the total tends to `1`.

Conclusion (math): `gᵢ₀ → 1/N` along `𝓝[>] 1`.
Conclusion (Lean): `Filter.Tendsto (g i₀) (𝓝[>] 1) (𝓝 (Fintype.card ι : ℝ)⁻¹)`.

The proof body uses: `isBoundedUnder_le_of_isBoundedUnder_le_sum` (private helper, derives above-bound
of each `gᵢ` from above-bound of the sum + below-bounds), `sum_liminf_le_liminf_sum` (private helper,
**superadditivity of liminf over a `Finset.sum`**, proved by `Finset.induction` on top of mathlib's
binary `le_liminf_add`), mathlib's `le_limsup_add`, `Filter.isBoundedUnder_le_sum` /
`isBoundedUnder_ge_sum`, and the squeeze `tendsto_of_le_liminf_of_limsup_le`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a private-helper-flavoured real-analysis glue lemma — not a named theorem, not a `## Main
results` entry, not a new structure. It is the "pigeonhole glue" that closes the abelian Chebotarev
proof; the module docstring describes it as exactly that. (Literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`. (Body is a ~55-line tactic proof.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | finite family functions liminf ≥ 1/n, sum→1 ⟹ each→1/n, pigeonhole limsup                              | no   | —                                | Returned generic liminf/limsup/Bolzano–Weierstrass notes (MIT 18.100A, Cornean, Drury); no source states this composite as a lemma. |
|  2 | WebSearch (general form)         | liminf fᵢ bounded below, Σfᵢ converges ⟹ liminf Σ = Σ liminf, squeeze each summand                      | partial | superadditivity: Σ liminf fᵢ ≤ liminf Σ fᵢ; Fatou-flavoured | The *ingredient* (superadditivity of liminf / Fatou) is standard and named; the *pinning conclusion* is not stated as a result. |
|  3 | WebSearch (named-after / aliases)| mathlib4 tendsto_of_le_liminf_of_limsup_le liminf limsup squeeze convergence                            | yes  | the squeeze: `a ≤ liminf u`, `limsup u ≤ a` ⟹ `u → a` | This is the final step; lives in `Mathlib.Topology.Order.LiminfLimsup`. Standard "squeeze via liminf=limsup". |
|  4 | ChatGPT MCP                      | "is the pin-each-to-1/N statement a recognised standalone result, what generality, is below-boundedness needed?" | n/a | — | **MCP down this session** (Codex exec failed — matches task note). Substituted by direct mathlib-source reading (Phase 5 method D) + the analytic generality reasoning in Phase 4. |
|  5 | Local references                 | grep `projects/Chebotarev/.mathlib-quality/references/`                                                 | n/a  | (no references dir)                | Directory absent (`ls` → no such file). Recorded n/a. |
|  6 | nLab                             | "limit inferior" page — sums-of-functions / pinning lemmas                                              | no   | only definitional content          | nLab "inferior limit" is definition-only (lattices/filters/nets); no sum-superadditivity or pinning result. |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | —                                | Not a categorical concept; nLab/nCatLab share the page checked in #6. |
|  8 | Stacks Project (alg geom)        | —                                                                                                      | n/a  | —                                | Not an algebraic-geometry concept (elementary real analysis). |
|  9 | MathOverflow / Math.SE           | (covered by WebSearch #1–#2 result sets, which surface SE/Quora)                                        | no   | —                                | Quora/SE hits only restate liminf/limsup defs and Fatou; none give the composite lemma. |
| 10 | recent arXiv (last 5 yr)         | (covered by WebSearch #1–#2 — arXiv "Univariate Real Analysis" 2508.19405, "A sampler in analysis", etc.) | no | —                                | arXiv expository analysis notes restate superadditivity/Fatou; no standalone pinning result. |

### Literature summary (Phase 3)

Concept identified as: **an ad-hoc "no-slack pigeonhole / squeeze" argument** — not a named lemma.
Its two named ingredients are (i) *superadditivity of `liminf` over sums* (sum of liminfs ≤ liminf of
sum; the discrete-order cousin of **Fatou's lemma**), and (ii) the *liminf=limsup squeeze* criterion.

Sources agree on the standard form: **no** — there is no standard standalone form, because the result
is the routine combination of two standard facts. The literature treats each ingredient as standard but
never packages the conclusion.

Most general standard form (of the ingredients): superadditivity holds in any conditionally complete
linear order with a compatible monotone `+` (mathlib's `le_liminf_add` hypotheses); the squeeze holds in
any conditionally complete linear order with order topology. The *pinning conclusion* generalises (see
Phase 4) to: **arbitrary index/filter/order, with per-index bounds `cᵢ` whose sum equals the limit of the
total sum, forcing each `gᵢ → cᵢ`.** The equal-weight `1/N` and the filter `𝓝[>] 1` are pure
specialisations.

Generality dimensions where the literature varies:
  - Order/codomain: from `ℝ` up to a conditionally-complete linearly-ordered topological additive group
    (the project's own `LiminfSumGlue` section already states its helpers at this generality).
  - Index: from `Fin N` / `Fintype` up to any `Finset`.
  - Filter: any `NeBot` filter (nothing uses that it is specifically `𝓝[>] 1`).
  - Target constants: the uniform `1/N` is a special case of arbitrary `cᵢ` with `Σ cᵢ = lim Σ gᵢ`.

Disagreement with the literature: none — the analytic content matches; the issue is purely that the
Lean statement is **far narrower** than the argument supports.

---

### Generality analysis — `Chebotarev.tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one`

Literature-standard form (from Phase 3): *finite family in a cond.-complete lin.-ordered topological
add. group, along any `NeBot` filter, each `liminf gᵢ ≥ cᵢ` and bounded below, total `→ L` with
`Σ cᵢ = L` ⟹ each `gᵢ → cᵢ`.*

| # | Parameter / hypothesis                          | Current Lean form                | Literature-standard form            | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------------------|----------------------------------|-------------------------------------|---------------------|----------------------------------|
| 1 | codomain `ℝ`                                    | `g : ι → ℝ → ℝ`, target `ℝ`      | cond.-complete lin-ord top. add grp | yes                 | The two private helpers (`LiminfSumGlue`) are *already* stated over `[AddCommGroup α] [ConditionallyCompleteLinearOrder α] [DenselyOrdered α] [AddLeftMono α]`; only the final arithmetic (`field_simp`, `1 - (N-1)/N = 1/N`) is ℝ-specific, and that disappears once `1/N` becomes abstract `cᵢ`. |
| 2 | domain `ℝ` + filter `𝓝[>] (1 : ℝ)`              | hard-wired `𝓝[>] 1`             | any `{l : Filter β} [l.NeBot]`      | yes                 | Nothing in the proof uses that the filter is a right-neighbourhood of `1`; it only needs `NeBot` (for liminf/limsup to behave). `l` is `set` as an abbreviation and never destructured. |
| 3 | uniform lower bound `(Fintype.card ι)⁻¹`        | `1/N` for every `i`              | per-index `cᵢ` with `Σ cᵢ = L`      | yes                 | Proof sums the bounds (`Finset.sum_le_sum (fun j _ ↦ hlo j)`) to get `(N-1)/N` on the complement; with general `cᵢ` this is `Σ_{j≠i} cⱼ`, and `limsup gᵢ ≤ L − Σ_{j≠i} cⱼ = cᵢ`. Pure rewriting, same steps. |
| 4 | limit of the sum `= 1`                          | `Tendsto … (𝓝 1)`               | `Tendsto … (𝓝 L)` with `Σ cᵢ = L`  | yes                 | `1` only enters via `hFlimsup : limsup F l = 1`; replacing by `L` and using `Σ cᵢ = L` closes identically. |
| 5 | index `[Fintype ι]`                             | `Fintype`                        | a `Finset`                          | yes (mild)          | The proof already works with `t = univ.erase i₀ : Finset ι`; a `Finset`-indexed restatement is routine but slightly less ergonomic at the call site. Fintype is acceptable. |
| 6 | `hbelow` (below-boundedness)                    | hypothesis                       | hypothesis (genuinely needed)       | NO                  | Docstring is correct: in a cond.-complete order a finite `liminf` lower bound does **not** force below-boundedness; without `hbelow` the statement is false. Keep it. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: **4 substantive** (codomain/order, domain+filter, per-index
constants, limit value) **+1 mild** (Fintype→Finset).

Proposed restatement (the literature-standard form the argument actually proves):

```lean
theorem tendsto_of_liminf_ge_of_sum_tendsto
    {ι β α : Type*} [Fintype ι]
    [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [DenselyOrdered α]
    [AddLeftMono α] [TopologicalSpace α] [OrderTopology α]
    {l : Filter β} [l.NeBot] {g : ι → β → α} {c : ι → α} {L : α}
    (hlo    : ∀ i, c i ≤ Filter.liminf (g i) l)
    (hbelow : ∀ i, l.IsBoundedUnder (· ≥ ·) (g i))
    (hsum   : Filter.Tendsto (fun s ↦ ∑ i, g i s) l (𝓝 L))
    (hcsum  : ∑ i, c i = L) (i₀ : ι) :
    Filter.Tendsto (g i₀) l (𝓝 (c i₀)) := by
  sorry -- the existing proof carries over; only the final ℝ-arithmetic step is replaced by `hcsum`
```

The original is the corollary `c := fun _ ↦ (Fintype.card ι : ℝ)⁻¹`, `L := 1`, `l := 𝓝[>] 1`, with
`hcsum` discharged by `Finset.sum_const` + `Fintype.card • (N:ℝ)⁻¹ = 1`.

Cost of restatement: **MODERATE** — mechanical for the order/filter/index axes (the helpers are already
abstract); the per-index-`cᵢ` + `L` axis replaces the closing `field_simp; ring` block with a one-line
use of `hcsum`, and the complement bound becomes `Σ_{j≠i₀} cⱼ` instead of `(N-1)/N`. No new ideas.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Proposed reformulation                                              | Mathlib downstream this enables |
|----|-------------------------------------------------------------------------------------------|----------|--------------------------------------------------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                        | no       | already typeclass-driven (`Fintype`, order classes)                | — |
|  2 | sequences/metric → filters/nets/topological?                                              | yes      | replace `𝓝[>] 1` (a specific filter on ℝ) by a general `[l.NeBot]` | unifies with the whole `Filter.liminf`/`Tendsto` API; the lemma then composes with *any* filter limit, not just one-sided real limits |
|  3 | construct an object → universal-property class?                                           | no       | no object constructed                                              | — |
|  4 | set-with-closure-predicate → bundled substructure?                                        | no       | no substructure here                                              | — |
|  5 | vector-space/metric/field-specific → weakened typeclass (modules/pseudometric/semiring)?  | yes      | `ℝ` → cond.-complete lin-ord top. add group (matches the helpers)  | applies to `EReal`, `ℝ≥0∞`-adjacent ordered groups, any such codomain |
|  6 | 1-categorical → higher-categorical?                                                       | no       | n/a                                                                | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structure?                            | yes      | uniform `1/N` → per-index `cᵢ` with `Σ cᵢ = L`                      | the general weighted form is the genuinely reusable statement; equal weights are one instance |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — and it largely coincides with the literature-standard generalisation
of Phase 4b (filter-generalisation + order-generalisation + weight-generalisation).
  - Proposed mathlib-idiomatic restatement: as in Phase 4b (the `c : ι → α`, `{l : Filter β} [l.NeBot]`,
    cond.-complete-ordered-group form).
  - Cost: **MODERATE** (same as 4b).
  - Mathlib downstream this enables: the general form is a clean companion to mathlib's existing
    `le_liminf_add`/`le_limsup_add`/`tendsto_of_le_liminf_of_limsup_le`; it would also want the missing
    **Finset-sum superadditivity** lemma `∑ liminf ≤ liminf ∑` (currently the project's private
    `sum_liminf_le_liminf_sum`) to be upstreamed alongside, since that is the genuinely reusable
    sub-result.
  - Real mathematical improvement (not just "looks cooler"): yes — the weighted/filtered form is the
    statement an analyst would actually cite ("a finite family whose liminfs already exhaust the limit
    of the sum converges termwise"); the `1/N`-on-`𝓝[>]1` form is a single application.

---

### Diamond / defeq risk — `Chebotarev.tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one`

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `Chebotarev.tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one`

[A] Lean-Finder       (mathlib lean MCP unavailable this session)   n/a: tool not loaded; substituted by [D]
[B] Loogle            via web — `Tendsto _ _ (𝓝 (Fintype.card _)⁻¹)` shape; liminf+sum+tendsto    no hits
[C] LeanSearch        web — "sum of liminf ≤ liminf of sum Finset", "liminf bound each summand sum converges each converges"   no hits for either the superadditivity-over-Finset form or the pinning conclusion
[D] Grep mathlib src  `tendsto.*Fintype.card.*⁻¹`, `sum_liminf`, `liminf_sum`, `liminf_ge_of_sum`, `of_liminf_ge`, `pigeonhole.*liminf`   only unrelated hits: `ENNReal.tsum_eq_liminf_sum_nat`, `mkMetric_le_liminf_sum`/`hausdorffMeasure_le_liminf_sum` (Hausdorff measure). **None is the superadditivity-over-Finset lemma; none is the pinning lemma.**
[E] Name pattern      (lean_local_search unavailable; project grep)   only the decl itself + its 1 call site

Building blocks confirmed present in mathlib (read in source):
  - `tendsto_of_le_liminf_of_limsup_le` — `Mathlib/Topology/Order/LiminfLimsup.lean:306` (the squeeze).
  - `le_liminf_add`, `le_limsup_add`, `limsup_add_le`, `liminf_add_le` — `Mathlib/Topology/Algebra/Order/LiminfLimsup.lean:42–82` (**binary** add only).
  - `Filter.isBoundedUnder_le_sum`, `Filter.isBoundedUnder_ge_sum` — `Mathlib/Order/Filter/IsBounded.lean:363,368`.

Searched for both the user's current form and the literature-standard (general `cᵢ`/filter/order) form.

Concluded: **not in mathlib** (five-method search exhausted incl. the general form). Mathlib has the
*binary* liminf/limsup-of-sum lemmas and the squeeze, but **not** (i) the Finset-sum superadditivity of
`liminf` (the project proves it privately as `sum_liminf_le_liminf_sum` by `Finset.induction`), nor
(ii) the pinning/no-slack conclusion in any form.

---

### Call sites — `Chebotarev.tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one`

Internal use count: **1** (within the project, excluding the declaring lines)
External-to-file callers: **0** distinct files (entirely internal to `Abelian.lean`)

| Caller file:line                                   | Usage pattern (one-line excerpt)                                        |
|----------------------------------------------------|-------------------------------------------------------------------------|
| CebotarevDensity/Abelian.lean:1585 (`chebotarev_abelian`) | `refine tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one (fun τ s ↦ …ratio…) (fun τ ↦ ?_) (fun τ ↦ isBoundedUnder_ge_ratio_zetaSum K _) (ratioSum_frobeniusFibres_tendsto_one K L) σ` |

(The other two grep hits at `:1502` and `:1576` are the declaration itself and its mention inside the
`chebotarev_abelian` docstring — not call sites.)

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?): (none) — the
pigeonhole argument appears only here.

What the pattern tells us: **K = 1 internal use, 0 external, no inline re-derivation.** Per the
call-sites heuristic table this is the "possibly the wrong abstraction / could be inlined" signal —
i.e. it leans *away* from a YES-add-as-is on the *current narrow form*. It does **not** mean the
*content* is junk: it is load-bearing for `chebotarev_abelian`. The signal reinforces that what is
mathlib-worthy is the **general** statement (which would attract its own consumers), not the bespoke
`1/N`-on-`𝓝[>]1` wrapper, which exists only to close this one proof.

---

### Composition check (Phase 6)

Can the statement be derived from mathlib in ≤3 chained calls?

Attempt 1: squeeze directly — `tendsto_of_le_liminf_of_limsup_le hlo_i₀ ?hlimsup (hgle i₀) (hbelow i₀)`.
  - Mathlib decls used: `tendsto_of_le_liminf_of_limsup_le`.
  - Result: **partial** — the lower-bound hypothesis is `hlo i₀` directly, but the *upper* bound
    `limsup gᵢ₀ ≤ 1/N` is not available from mathlib; it requires the whole sub-argument.
  - Notes: producing `limsup gᵢ₀ ≤ 1/N` needs (a) `limsup gᵢ₀ + liminf(Σ_{j≠i₀} gⱼ) ≤ limsup(Σ) = 1`
    via `le_limsup_add`, plus (b) `liminf(Σ_{j≠i₀} gⱼ) ≥ (N-1)/N`, which itself needs **Finset-sum
    superadditivity of liminf** — not in mathlib (proved privately by induction), plus (c)
    above-boundedness of each `gᵢ` from the sum's above-boundedness (another private helper). Also `hgle`
    (above-bound of `gᵢ₀`) is itself derived, not given.

Attempt 2: assume the helpers — even granting `sum_liminf_le_liminf_sum` and
`isBoundedUnder_le_of_isBoundedUnder_le_sum`, the body is still: erase `i₀`, build the complement
liminf bound by `Finset.sum_le_sum` + a `Finset.sum_const`/cast computation, apply `le_limsup_add`,
rewrite `limsup F = 1`, do the `1 - (N-1)/N = 1/N` arithmetic, then squeeze. That is **~5 distinct
reasoning steps with `have`s and arithmetic between them** — a genuine proof, not a `.trans`/`.symm`/
single-application chain.

Conclusion: **NOT-COMPOSABLE** — it is not a ≤3-call mathlib composition. The decisive obstruction is
that the Finset-sum superadditivity of `liminf` (`∑ liminf ≤ liminf ∑`) is itself **absent from
mathlib**, so even the *first ingredient* of the composition has to be proved by induction. (This is
exactly why the project carries `sum_liminf_le_liminf_sum` and `isBoundedUnder_le_of_isBoundedUnder_le_sum`
as private helpers.)

---

## Verdict: `Chebotarev.tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one`

**Category:** **YES-but-generalise-first**

**Evidence:**
- Literature search (Phase 3): the analytic content is standard (superadditivity of `liminf` / Fatou +
  the `liminf=limsup` squeeze) but **no source states the composite as a lemma**, and every source treats
  it at full generality (arbitrary order/filter, per-index bounds) — the `1/N`-on-`𝓝[>]1` packaging is
  not the literature form.
- Generality analysis (Phase 4): verdict **STRICTLY NARROWER THAN STANDARD** — 4 substantive weakenings
  (codomain/order, domain+filter, per-index constants `cᵢ`, limit value `L`); Phase 4c independently
  flags the same filter/order/weight generalisation as a real modern-idiom improvement.
- Mathlib search (Phase 5): **not in mathlib** (neither the pinning conclusion nor the prerequisite
  Finset-sum superadditivity of `liminf`); only binary `le_liminf_add`/`le_limsup_add` and the squeeze
  exist.
- Composition check (Phase 6): **NOT-COMPOSABLE** (>3 steps; the first ingredient, `∑ liminf ≤ liminf ∑`
  over a `Finset`, is itself missing from mathlib).

**Rationale:**

The *content* is mathlib-worthy: a clean, reusable real-analysis fact ("if a finite family's liminfs
already exhaust the limit of its sum, the family converges termwise") whose proof is non-trivial and
whose first ingredient — Finset-sum superadditivity of `liminf` — is a genuine gap in mathlib (mathlib
stops at the *binary* `le_liminf_add`; the project had to write `sum_liminf_le_liminf_sum` by induction).
So this is **not** NO-mathlib-has-it and **not** NO-composable-from-mathlib (the composition needs a lemma
mathlib lacks). But the *current statement* is far too narrow to ship as-is: it bakes in the specific
filter `𝓝[>] (1 : ℝ)`, the codomain `ℝ`, the uniform weight `1/N = (Fintype.card ι)⁻¹`, and the limit
value `1` — none of which the proof uses. Mathlib's iron rule (add the most general form) and the
`YES-add-as-is`→`YES-but-generalise-first` gate (Phase 4b was STRICTLY NARROWER; Phase 4c found a real
modern-idiom improvement) both force the generalise-first bucket. The right mathlib contribution is the
two-part upstreaming below: (i) the missing Finset-sum superadditivity lemma, then (ii) the general
weighted/filtered pinning theorem, with the present `1/N` statement recovered as a one-line corollary at
the `chebotarev_abelian` call site. The K=1/0-external call-site signal reinforces this: the narrow form
has exactly one consumer (this proof), whereas the general form is what would attract independent use.

**Reason for the generalisation:**
- LITERATURE-WEAKENING: Phase 4b found the user's form strictly narrower than the standard argument
  (order, filter, per-index constants, limit value).
- MODERN-IDIOM (Bourbaki 2.0): Phase 4c — filter-generalisation (`𝓝[>] 1` → any `NeBot` filter),
  order-generalisation (`ℝ` → cond.-complete lin-ord top. add group, matching the project's own helper
  typeclasses), and weight-generalisation (`1/N` → arbitrary `cᵢ` with `Σ cᵢ = L`).

**Proposed restatement:**

```lean
-- Prerequisite to upstream first (currently the project's private `sum_liminf_le_liminf_sum`):
theorem sum_liminf_le_liminf_sum {ι κ α : Type*}
    [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [DenselyOrdered α] [AddLeftMono α]
    {l : Filter ι} [l.NeBot] (g : κ → ι → α) (t : Finset κ)
    (hbelow : ∀ j ∈ t, l.IsBoundedUnder (· ≥ ·) (g j))
    (habove : ∀ j ∈ t, l.IsBoundedUnder (· ≤ ·) (g j)) :
    ∑ j ∈ t, Filter.liminf (g j) l ≤ Filter.liminf (fun x ↦ ∑ j ∈ t, g j x) l := by
  sorry -- Finset.induction on top of mathlib's binary `le_liminf_add`

-- The general pinning theorem:
theorem tendsto_of_liminf_ge_of_sum_tendsto
    {ι β α : Type*} [Fintype ι]
    [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [DenselyOrdered α]
    [AddLeftMono α] [TopologicalSpace α] [OrderTopology α]
    {l : Filter β} [l.NeBot] {g : ι → β → α} {c : ι → α} {L : α}
    (hlo    : ∀ i, c i ≤ Filter.liminf (g i) l)
    (hbelow : ∀ i, l.IsBoundedUnder (· ≥ ·) (g i))
    (hsum   : Filter.Tendsto (fun s ↦ ∑ i, g i s) l (𝓝 L))
    (hcsum  : ∑ i, c i = L) (i₀ : ι) :
    Filter.Tendsto (g i₀) l (𝓝 (c i₀)) := by
  sorry -- existing proof; closing ℝ-arithmetic replaced by `hcsum`
```

Estimated cost of regeneralisation: **MODERATE** (the helpers are already abstract; the closing
`field_simp; ring`/`1 - (N-1)/N = 1/N` block is replaced by `hcsum` and `Σ_{j≠i₀} cⱼ`; no new ideas).
Note: cost does not downgrade the verdict.

Mathlib downstream this enables (MODERN-IDIOM):
- Composes with the existing `Filter.liminf`/`Filter.limsup`/`Tendsto` API for *any* filter, not just
  one-sided real limits — the lemma becomes citable in any "termwise convergence from a tight sum"
  situation (Dirichlet-density-style arguments, equidistribution, measure-pinning, etc.).
- The prerequisite `sum_liminf_le_liminf_sum` is itself a reusable companion to mathlib's binary
  `le_liminf_add`/`le_limsup_add` and the obvious `Finset`-level gap next to them; upstreaming it closes
  that gap independently of Chebotarev.
- Works over `EReal`/ordered-group codomains (mathlib already develops `le_liminf_add` for `EReal`).

Next action: run `/generalise Chebotarev.tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` (tensioning
against both the literature-standard form and the modern-idiom form above), upstream
`sum_liminf_le_liminf_sum` first (it is the load-bearing missing piece), then ship the general pinning
theorem with the `1/N`-on-`𝓝[>]1` statement recovered as a corollary at the `chebotarev_abelian` call
site. `/cleanup` + `/pre-submit` before opening the mathlib PR.

---

## Next step

Run `/generalise Chebotarev.tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one`; upstream the missing
Finset-sum superadditivity lemma `sum_liminf_le_liminf_sum` to
`Mathlib/Topology/Algebra/Order/LiminfLimsup.lean` (next to `le_liminf_add`), then add the general
weighted/filtered pinning theorem, deriving the project's `1/N` form as a one-line corollary.
