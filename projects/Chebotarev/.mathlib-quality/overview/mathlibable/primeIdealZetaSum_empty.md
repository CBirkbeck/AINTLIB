# /mathlibable report — `Chebotarev.primeIdealZetaSum_empty`

## Baseline (Phase 0)

- lake build:               (not re-run; local build known stale — reasoned from source per task)
- decl `Chebotarev.primeIdealZetaSum_empty`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/Density.lean:174`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Dirichlet density of a set of prime ideals of `𝓞 K` for a number
  field `K` — defines the partial Dirichlet series `primeIdealZetaSum` and density variants
  (Sharifi, *Algebraic Number Theory* §7.1.13).
- qualified name:            namespace `Chebotarev` opened at `Density.lean:44`; the parsed
  qualified name `Chebotarev.primeIdealZetaSum_empty` is **confirmed correct**.

---

## Statement (Phase 1)

`Chebotarev.primeIdealZetaSum_empty` is a theorem stating: the partial Dirichlet series taken over
the **empty** set of prime ideals is identically `0`.

For a number field `K`, `primeIdealZetaSum S s` is defined (Density.lean:50) as the unconditional
sum `∑' 𝔭, (N𝔭)^{-s}` indexed by the subtype `{𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}`
of nonzero prime ideals lying in `S`. The theorem specialises `S = ∅`: since no ideal lies in `∅`,
the indexing subtype is empty, and the empty `tsum` is `0`.

Variables / typeclasses involved (Lean side):
- `{K : Type*} [Field K] [NumberField K]` — the base number field.
- `(s : ℝ)` — the real exponent (no convergence hypothesis needed; over `∅` the series is the
  empty sum, summable trivially).

Hypotheses (Lean side): none beyond the ambient `[Field K] [NumberField K]`.

Conclusion (math): `Σ_{𝔭 ∈ ∅} N𝔭^{-s} = 0`.

Conclusion (Lean): `primeIdealZetaSum (∅ : Set (Ideal (𝓞 K))) s = 0`.

Proof body (Density.lean:174–177):
```lean
have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
  ⟨fun x ↦ x.2.1⟩
rw [primeIdealZetaSum_def, tsum_empty]
```
i.e. exhibit `IsEmpty` of the index subtype (the membership component `x.2.1 : 𝔭 ∈ ∅` is `False`),
unfold the definition, and close with mathlib's `tsum_empty`.

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper equation lemma about the project-local definition `primeIdealZetaSum`; not a new
mathematical structure, not a named theorem, not a `## Main results` entry (the main definitions
are `primeIdealZetaSum`, `HasDirichletDensity`, and the upper/lower variants — this is a basic fact
*about* the first one). It is the `S = ∅` base case feeding the finite-additivity lemma
`primeIdealZetaSum_biUnion_of_pairwiseDisjoint`.

(Literature width is EXHAUSTIVE regardless; recorded for framing only.)

## One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` — the one-liner gate is **n/a**. (Note for
narrative: the *statement* is itself a near-trivial specialisation, which the buckets below treat
as the analogue of a "one-liner" — a wrapper whose content collapses to one mathlib `simp` lemma
plus an `IsEmpty` observation.)

---

## PHASE 3 — Literature search (EXHAUSTIVE)

The mathematical content is the **empty-sum convention**: a sum (here a `tsum`) over an empty
index set is `0`. This is universal convention, not a named theorem; for a Dirichlet/Dedekind zeta
restricted to a set of primes `S`, the `S = ∅` value being `0` is immediate from that convention.

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Dirichlet series sum over empty set of primes equals zero number field zeta"          | partial | no *named* result; standard sources (Wikipedia *Dirichlet series*, Sharifi) treat the partial-sum-over-`S` series and its `S=∅` value as a trivial convention | nobody states "sum over ∅ = 0" as a lemma — it is the empty-sum convention |
|  2 | WebSearch (general form)         | "empty sum convention sum over empty index set equals zero mathlib tsum"               | yes  | "sum over an empty index set conventionally equals zero"; mathlib `tsum f = 0` when index `IsEmpty` | confirms the convention is the only content; cites `has_sum_empty`, `summable_empty`, `tsum`'s zero-on-empty behaviour |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2) "partial zeta over set of primes S, value at S empty"               | n/a  | none — no eponym | the underlying object (partial Dedekind zeta / prime-restricted Dirichlet series) is standard (Sharifi §7.1), but the `∅` evaluation is never named |
|  4 | ChatGPT MCP                      | intended: "standard form + generality + historical evolution of empty-sum convention"   | n/a  | — | MCP unavailable this session (task note: ChatGPT math MCP may be down). Covered by #1,#2 + direct mathlib source read (Phase 5) — the convention and its mathlib home are fully pinned down without it. |
|  5 | Local references                 | `.mathlib-quality/references/` and `refs/Chebotarev/`                                   | n/a  | — | **both directories absent** on this checkout (only `.mathlib-quality/overview/` exists). Recorded n/a. |
|  6 | nLab                             | "empty sum" / "Dedekind zeta function"                                                  | n/a  | empty sum = 0 (additive unit of the empty family); standard | nLab treats the empty sum as the monoid unit over the empty family — exactly mathlib's `IsEmpty ⇒ 0`. No project-specific content. |
|  7 | nCatLab (if categorical)         | —                                                                                       | n/a  | — | not a categorical concept (a real-valued infinite sum); no categorical generalisation at stake. |
|  8 | Stacks Project (if alg geom)     | —                                                                                       | n/a  | — | not an algebraic-geometry concept; Stacks has no notion of "Dirichlet series over a set of primes". |
|  9 | MathOverflow / Math.StackExchange| "sum over empty set zero convention" generality                                         | yes  | the empty sum is `0` by convention (identity of `+`); universally agreed | standard; nothing field- or zeta-specific. |
| 10 | recent arXiv (last 5 years)      | (covered by #1) "partial zeta function set of primes Dirichlet density"                | n/a  | — | partial zeta / Dirichlet density (Stevenhagen–Lenstra, Sharifi) is classical; modern arXiv does not restate the `∅` evaluation as a result. |

The protocol passed: WebSearch ran ≥3 distinct queries at different generality levels; the
standard-form question is fully answered by #2 + #6 + #9 (empty sum = 0); local refs checked
(absent → n/a); nLab/Stacks/nCatLab/MathOverflow/arXiv each checked or n/a with reason. ChatGPT MCP
is the one channel not run (down this session) — it is non-load-bearing here because the convention
and its exact mathlib home are established directly from the mathlib source.

### Literature summary (Phase 3)

Concept identified as: the **empty-sum convention** — `∑_{i ∈ ∅} a_i = 0` — applied to the
prime-restricted Dirichlet series `Σ_{𝔭 ∈ S} N𝔭^{-s}` at `S = ∅`.
Sources agree on the standard form: **yes** — universally, the empty sum is the additive identity `0`.
Most general standard form: for *any* family `f : β → M` into an additive (topological commutative)
monoid with `β` empty, `∑' b, f b = 0`. The prime-ideal / `ℝ^{-s}` data is irrelevant to the fact.
Generality dimensions where the literature varies:
  - index type: the convention holds for any empty index — the most general is "`β` is empty",
    with no structure on `β` at all (here `β = {𝔭 // 𝔭 ∈ ∅ ∧ …}`).
  - codomain: any additive commutative monoid with a compatible topology — the most general is the
    `tsum` setting (here specialised to `ℝ`).
Disagreement with the literature: none. The literature has no *named* result here at all; it is a
convention, and the only nontrivial step in the Lean lemma is recognising that the index subtype is
empty (`𝔭 ∈ ∅` is `False`).

---

## PHASE 4 — Generality analysis

### Generality analysis — `Chebotarev.primeIdealZetaSum_empty`

Literature-standard form (from Phase 3): "the empty sum is `0`", i.e. `[IsEmpty β] → ∑' b, f b = 0`
for any `f : β → M` in a topological additive commutative monoid.

| # | Parameter / hypothesis        | Current Lean form                         | Literature-standard form                 | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|-------------------------------------------|------------------------------------------|---------------------|----------------------------------|
| 1 | `[Field K] [NumberField K]`   | base is a number field                    | irrelevant — empty sum needs no codomain/index structure | YES (drop entirely) | the fact never uses anything about `K`; it is pure empty-sum bookkeeping. The general statement has *no* `K` at all. |
| 2 | index `{𝔭 // 𝔭 ∈ ∅ ∧ …}`      | this specific prime-ideal subtype         | "any empty index type `β`"               | YES                 | the subtype matters only insofar as it is empty; the general lemma abstracts it to `[IsEmpty β]`. |
| 3 | codomain `ℝ`, term `N𝔭^{-s}`  | real, `rpow` summand                       | "any `f : β → M`, `M` a top. add. comm. monoid" | YES          | the value of the summand is never inspected; over an empty index every summand is vacuous. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — it is the `K`-number-field, prime-ideal,
real-`rpow` specialisation of "empty sum = 0".
Number of weakening opportunities found: 3 (all three parameter families are inessential).
Proposed restatement: the maximally-general form is *exactly mathlib's existing `tsum_empty`*
(`[IsEmpty β] : ∑' b, f b = 0`). There is nothing project-specific left to state once generalised —
which is the decisive signal that this belongs to **NO-mathlib-has-it / NO-composable**, not YES.
Cost of restatement: n/a — the general form is already in mathlib (Phase 5).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses?                                 | no       | — | already typeclass-driven (`[IsEmpty β]` in the general lemma). |
|  2 | sequences/metric → filters/topological?                                  | no       | — | `tsum` is already the filter-based notion; no metric phrasing present. |
|  3 | construct an object → universal-property class?                          | no       | — | no construction; it is an equation. |
|  4 | set-with-closure-predicate → bundled substructure?                       | no       | — | no substructure. |
|  5 | vector-space/metric/field-specific → weaken typeclasses?                 | yes      | drop `ℝ` and the number-field data; state over a topological additive comm. monoid | this *is* `tsum_empty`; the modern form already exists in mathlib. |
|  6 | 1-categorical → higher-categorical?                                      | no       | — | n/a. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive structure?                   | yes      | replace the prime-ideal subtype with an arbitrary `[IsEmpty β]` index | again exactly `tsum_empty`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — but the modernised/maximally-general form *is already mathlib's
`tsum_empty`*. So the "generalise first" target is not a new project lemma; it is the existing
mathlib lemma. This pushes the verdict to a NO bucket (mathlib has the general form), not
YES-but-generalise-first (which would require the general form to be *absent* from mathlib).
Real mathematical improvement: n/a — there is no project-side statement worth keeping after
generalisation.

---

## PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is `theorem` (introduces no definitional equality or typeclass-search path).

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `Chebotarev.primeIdealZetaSum_empty`

[A] Lean-Finder       (tool unavailable this session)                          n/a: lean_leansearch/lean_loogle not resolvable; substituted by direct mathlib-source grep [D]
[B] Loogle            intended `∑' _ : ?β, _ = 0` and `tsum_empty`             n/a: lean_loogle not available; resolved by [D]+[web] instead
[C] LeanSearch        "tsum over empty type is zero"                            n/a: tool unavailable; WebSearch #2 returned the mathlib doc pages directly
[D] Grep mathlib src  `tprod_empty`, `tsum_empty`, `tsum_eq_zero_of_*`, `primeIdealZetaSum`  **HITS** (see below)
[E] Name pattern      `(theorem|lemma) tsum_empty` over `.lake/packages/`      hit indirectly: the *source* is `tprod_empty`; `tsum_empty` is `@[to_additive]`-generated

Grep findings (the load-bearing search):
- **`Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:466–468`**:
  ```lean
  @[to_additive (attr := simp)]
  theorem tprod_empty [IsEmpty β] : ∏'[L] b, f b = 1 := by convert! tprod_one (L := L)
  ```
  The `@[to_additive (attr := simp)]` attribute generates the additive **`tsum_empty [IsEmpty β] :
  ∑' b, f b = 0`**, marked `@[simp]`, at full generality (any index `β`, any topological additive
  commutative monoid codomain).
- This generated `tsum_empty` is **used verbatim** elsewhere in mathlib:
  `Mathlib/Analysis/Normed/Group/Tannery.lean:48` (`simpa only [tsum_empty] using tendsto_const_nhds`)
  and `Mathlib/MeasureTheory/Measure/MeasureSpace.lean:1364` (`rw [… , tsum_empty]`) — confirming
  the additive name exists and fires off the `IsEmpty` instance.
- The project itself already relies on `tsum_empty` for the analogous density lemma
  `hasDirichletDensity_empty` (Density.lean:99: `simpa only [HasDirichletDensity,
  primeIdealZetaSum_def, tsum_empty, zero_div] using tendsto_const_nhds`).
- Collision check: grep for `primeIdealZetaSum` over `.lake/packages/mathlib/` → **no hits**, as
  expected (the definition is project-local; no mathlib name collision).

Searched for both: the user's current form (prime-ideal, `ℝ`) — not present in mathlib (project
def) — **and** the literature-standard / general form (empty `tsum`) — **present** as `tsum_empty`.

Concluded: **found the general form in mathlib as `tsum_empty`** (additive image of
`tprod_empty`, `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:466`, `@[simp]`). Our form is a
specialisation reachable in ≤1 added step (supply `IsEmpty` of the index subtype, then `simp`/`rw`
with `tsum_empty` after unfolding the definition).

---

## PHASE 6 — Composition check

### Call sites — `Chebotarev.primeIdealZetaSum_empty`

Internal use count: **1** (within the project, excluding the declaring file's own definition).
External-to-file callers: 1 site, **same file** (`Density.lean`).

| Caller file:line       | Usage pattern (one-line excerpt)                        |
|------------------------|----------------------------------------------------------|
| Density.lean:186       | `| empty => simp [primeIdealZetaSum_empty]` — base case of `primeIdealZetaSum_biUnion_of_pairwiseDisjoint` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - `hasDirichletDensity_empty` (Density.lean:97–100) re-derives the *same* `IsEmpty` fact and uses
    `tsum_empty` inline (it does **not** call `primeIdealZetaSum_empty`). So the one nontrivial
    ingredient — `IsEmpty {𝔭 // 𝔭 ∈ ∅ ∧ …}` — is already duplicated inline at a second site, and
    that site reaches for mathlib's `tsum_empty` directly rather than this wrapper.

Call-sites signal: **K = 1 internal use, and the analogous fact is re-derived inline at a second
site** → per the skill's table this leans **NO-composable-from-mathlib**: it is a thin wrapper its
own neighbours partly bypass, sitting one `simp` away from mathlib's `tsum_empty`.

### Composition check (Phase 6)

Can `primeIdealZetaSum_empty` be derived from mathlib in ≤3 chained calls? **Yes.**

Attempt 1 (the existing proof, ≤3 lines, all-mathlib once `primeIdealZetaSum_def` is unfolded):
```lean
example (s : ℝ) : primeIdealZetaSum (∅ : Set (Ideal (𝓞 K))) s = 0 := by
  have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    ⟨fun x ↦ x.2.1⟩
  rw [primeIdealZetaSum_def, tsum_empty]
```
  - Mathlib decls used: `tsum_empty` (the `@[simp]` general lemma). `primeIdealZetaSum_def` is the
    project's own definitional `rfl`-lemma (unfold), and the `IsEmpty` term is a one-liner.
  - Result: **succeeds** — this *is* the current 3-line body.
  - Notes: the only non-mathlib piece is unfolding the project definition; the mathematical content
    is entirely `tsum_empty`.

Conclusion: **COMPOSABLE** — `primeIdealZetaSum_empty` = unfold + `IsEmpty`-instance + mathlib's
`tsum_empty`, a ≤3-line composition with exactly one mathlib lemma carrying the content.

---

## Verdict: `Chebotarev.primeIdealZetaSum_empty`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the only content is the empty-sum convention `∑_{∅} = 0`; no named
  result exists; the prime-ideal / `ℝ^{-s}` data is irrelevant.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — all three parameter families
  (number field, prime-ideal index, real `rpow`) are inessential; the general form is precisely
  mathlib's `tsum_empty`.
- Mathlib search (Phase 5): the general form **is in mathlib** as `tsum_empty` (`@[simp]`,
  `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:466`, additive image of `tprod_empty`).
- Composition check (Phase 6): COMPOSABLE — unfold + `IsEmpty` instance + `tsum_empty`, ≤3 lines.

**Rationale.**
`primeIdealZetaSum_empty` carries no mathematical content beyond the universal empty-sum convention,
which mathlib already ships as the `@[simp]` lemma `tsum_empty` (`[IsEmpty β] → ∑' b, f b = 0`,
generated by `@[to_additive]` from `tprod_empty` at `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:466`).
It is not a *direct* specialisation of `tsum_empty` — because `primeIdealZetaSum ∅ s` is a `tsum`
over the subtype `{𝔭 // 𝔭 ∈ ∅ ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}`, whose emptiness is the one extra observation
(`𝔭 ∈ ∅` is `False`, witnessed by `⟨fun x ↦ x.2.1⟩`). But that observation plus `tsum_empty` is a
≤3-line composition with a single mathlib lemma doing the work, which is exactly the existing proof
body. The decl is therefore a thin project-local wrapper, not a mathlib candidate: mathlib has the
general fact, and the specialisation is mechanical glue. It would never be stated as a standalone
lemma in mathlib — at a `primeIdealZetaSum ∅`-shaped call site one simply writes `by simp` (or
`by rw [primeIdealZetaSum_def, tsum_empty]`).

This is decisively *not* YES-but-generalise-first: the "generalised form" is not a new lemma to
contribute — it already exists in mathlib (`tsum_empty`). The verdict gate's NO-composable
conditions are met (Phase 5 cites the building block by qualified name; Phase 6 conclusion is
COMPOSABLE with a ≤3-line sketch).

**WHY not (refactor-actionable).** Mathlib has the building block `tsum_empty` (the `@[simp]`
empty-`tsum` lemma). The user's form is the unfold-then-`tsum_empty` composition; the one
non-mathlib ingredient is recognising the index subtype is empty, which is a single `IsEmpty`
term. No new lemma is warranted — inline at the (single) call site.

Mathlib building blocks:
- `tsum_empty` — `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:466` (additive `@[simp]` image
  of `tprod_empty`; `[IsEmpty β] : ∑' b, f b = 0`).
- `Chebotarev.primeIdealZetaSum_def` — the project's own `rfl` equation lemma (Density.lean:55) to
  unfold the definition first.

Composition sketch (≤3 lines):
```lean
example (s : ℝ) : primeIdealZetaSum (∅ : Set (Ideal (𝓞 K))) s = 0 := by
  have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    ⟨fun x ↦ x.2.1⟩
  rw [primeIdealZetaSum_def, tsum_empty]
```

Call sites in our project (from Phase 6.0): **K = 1** (`Density.lean:186`, the `empty` base case of
`primeIdealZetaSum_biUnion_of_pairwiseDisjoint`).

Refactor plan: this is a **judgement-call deletion**, not a clear win. At the single call site
(`Density.lean:186`, currently `simp [primeIdealZetaSum_empty]`) one could inline the composition —
e.g. replace with `simp [primeIdealZetaSum_def]` augmented by the `IsEmpty` instance, since
`tsum_empty` is already `@[simp]`. **However**, because the `IsEmpty {𝔭 // 𝔭 ∈ ∅ ∧ …}` fact is the
genuine (if tiny) ingredient and it is *already duplicated inline* at a second site
(`hasDirichletDensity_empty`, Density.lean:97), a reasonable project may instead choose to **keep
this lemma and route the duplicate through it** (have `hasDirichletDensity_empty` use
`primeIdealZetaSum_empty` rather than re-deriving `IsEmpty` + `tsum_empty`). Either way the lemma is
firmly **out of scope for mathlib** — the only open question is internal project hygiene (delete-and-
inline vs. keep-as-the-single-home-for-the-`IsEmpty`-fact), which is a `/cleanup`-lane decision, not
a mathlibability one.

Next action: do **not** propose `primeIdealZetaSum_empty` to mathlib. As project cleanup, either
inline the ≤3-line composition at `Density.lean:186` (relying on `tsum_empty`'s `@[simp]`), or keep
the lemma and de-duplicate `hasDirichletDensity_empty` through it. No mathlib PR.

---

## Next step

Do not propose to mathlib (NO-composable-from-mathlib). Mathlib already has the content via
`tsum_empty` (`@[simp]`, `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:466`). As project hygiene,
inline the ≤3-line composition at the one call site (`Density.lean:186`) — or, if the project
prefers a single home for the `IsEmpty {𝔭 // 𝔭 ∈ ∅ ∧ …}` fact, retain the lemma and de-duplicate
`hasDirichletDensity_empty` (Density.lean:97) through it. This internal-hygiene choice is a
`/cleanup`-lane call, not a mathlibability one.
