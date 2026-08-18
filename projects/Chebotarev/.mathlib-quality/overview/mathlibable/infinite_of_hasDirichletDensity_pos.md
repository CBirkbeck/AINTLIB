# /mathlibable report — `Chebotarev.infinite_of_hasDirichletDensity_pos`

## Baseline (Phase 0)
- lake build:               stale (per task; reasoned from source — decl is a one-line term proof, elaboration not in doubt)
- decl `Chebotarev.infinite_of_hasDirichletDensity_pos`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/Main.lean:113`
- qualified name:           `Chebotarev.infinite_of_hasDirichletDensity_pos` (namespace `Chebotarev`, confirmed from source `namespace Chebotarev` at Main.lean:60)
- kind:                     theorem
- has sorry:                no
- module docstring summary: Chebotarev's density theorem for finite Galois extensions of number fields, plus corollaries (Dirichlet on primes in AP, density of split-completely primes).

## Statement (Phase 1)

`infinite_of_hasDirichletDensity_pos` states: **a set `S` of prime ideals of `𝓞 K` that has Dirichlet
density `δ > 0` is infinite.**

Here `HasDirichletDensity S δ` is a *project-local* definition (`Density.lean:64`):
```
HasDirichletDensity S δ  :=  Tendsto (fun s ↦ primeIdealZetaSum S s / primeIdealZetaSum univ s) (𝓝[>] 1) (𝓝 δ)
```
i.e. the ratio of partial Dirichlet series `(Σ_{𝔭∈S} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})` tends to `δ` as `s ↓ 1`.

Variables / typeclasses (Lean side):
- `{K : Type*} [Field K] [NumberField K]` — `K` a number field; `𝓞 K` its ring of integers.

Hypotheses (Lean side):
- `{S : Set (Ideal (𝓞 K))}` — the set of ideals.
- `{δ : ℝ}` — the claimed density.
- `(h : HasDirichletDensity S δ)` — `S` has Dirichlet density `δ`.
- `(hδ : 0 < δ)` — the density is positive.

Conclusion (math): `S` is an infinite set.
Conclusion (Lean): `S.Infinite`.

**Proof** (one line, term mode):
```lean
fun hfin ↦ hδ.ne' (tendsto_nhds_unique h (hasDirichletDensity_of_finite K hfin))
```
By contradiction: if `S` were finite (`hfin`), then `hasDirichletDensity_of_finite K hfin` gives
`HasDirichletDensity S 0` (a project lemma, `Density.lean:588`); since both `HasDirichletDensity S δ`
and `HasDirichletDensity S 0` unfold to `Tendsto … (𝓝 δ)` resp. `(𝓝 0)`, `tendsto_nhds_unique` forces
`δ = 0`, contradicting `0 < δ` via `hδ.ne'`.

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper corollary — not a new structure, not a `## Main results` entry (the main results are
`chebotarev_density`, `dirichlet_primes_in_AP`, `density_split_completely`), not named after a person.
It is the qualitative "positive density ⟹ infinite" step feeding `infinite_setOf_frobenius_class`.

(Literature width run EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` — the one-liner *definition* check does not apply.
Recorded for narrative: the proof body is a single term-mode line, which is itself a strong signal the
result is a thin composition (developed further in Phases 5–6).

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | "positive Dirichlet density implies infinitely many primes set"                                | yes  | "a set of primes with positive Dirichlet density is necessarily infinite" | Wikipedia *Dirichlet density*; Kedlaya ANT ch.4; MIT 18.785 dirichlet notes — ubiquitous, unnamed |
| 2  | WebSearch (general form)         | "natural density positive set infinite finite set has density zero"                            | yes  | finite ⟹ density 0; positive density ⟹ infinite | Wikipedia *Natural density*; the dual fact for natural density. Same one-line argument |
| 3  | WebSearch (named-after/aliases)  | "Dirichlet density finite set density zero positive density infinite corollary Neukirch Serre" | yes  | "upper Dirichlet density of `S` is 0 iff `S` has density 0"; finite ⟹ 0 | Wikipedia; cited against Neu99 / Serre. No special name attached |
| 4  | WebSearch (textbook trail)       | "set of primes with positive density is infinite proof"                                        | yes  | confirmed as standard principle behind Dirichlet's theorem | multiple arXiv + Kedlaya; always a one-line corollary |
| 5  | ChatGPT MCP                      | (asked for standard form, generality, historical evolution)                                    | n/a  | — | **MCP down** (Codex exec failed); fell back to extra WebSearch queries #2–#4 per the skill's fallback guidance |
| 6  | Local references                 | grep `.mathlib-quality/references/`                                                            | n/a  | — | directory absent in this project; recorded n/a |
| 7  | nLab                             | "Dirichlet density" / "analytic density"                                                       | n/a  | — | not a category-theoretic concept; nLab has no dedicated page; the analytic-NT fact lives in textbooks, already covered by #1–#4 |
| 8  | nCatLab                          | —                                                                                              | n/a  | — | not categorical |
| 9  | Stacks Project                   | —                                                                                              | n/a  | — | not an algebraic-geometry / scheme-theoretic concept |
| 10 | MathOverflow / Math.SE           | covered via WebSearch #1–#4 (results surfaced SE/Wikipedia threads)                            | yes  | same one-line corollary | no deeper or more general statement than #1–#4 |
| 11 | recent arXiv (≤5y)               | surfaced in #2/#4 (e.g. sumsets-of-positive-density papers)                                     | yes  | uses the fact as a black-box corollary | no paper *states* it as a lemma; all treat it as immediate |

### Literature summary (Phase 3)

Concept identified as: **"a set of primes of positive Dirichlet density is infinite"** — the immediate
corollary of "finite sets have Dirichlet density 0."
Sources agree on the standard form: **yes**. Every source states it the same way and treats it as a
one-line consequence; it carries **no name** and **no dedicated theorem number** in any reference.
Most general standard form: the underlying abstract fact is *"any set-function density that (a) vanishes
on finite sets and (b) is well-defined (unique) cannot be positive on a finite set"* — but the literature
**never abstracts it this way**; it is always stated for Dirichlet (or natural) density concretely, in one line.
Generality dimensions where the literature varies:
  - density notion: Dirichlet/analytic vs. natural density — both admit the identical one-line argument;
    neither is "more general", they are parallel instances of the same triviality.
Disagreement with the literature: **none**. The project's statement is exactly the standard corollary.

## Generality analysis — `infinite_of_hasDirichletDensity_pos` (Phase 4)

Literature-standard form (from Phase 3): "if `S` has positive Dirichlet density then `S` is infinite",
stated concretely for the Dirichlet density of prime sets.

### Generality status table (Phase 4a)

| # | Parameter / hypothesis              | Current Lean form                | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------|----------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `[NumberField K]`                  | `S` is a set of ideals of `𝓞 K` | density of prime sets of a number field | NO (within this notion) | `HasDirichletDensity` is *defined* only for `Set (Ideal (𝓞 K))` with `[NumberField K]`; the statement cannot be stated without that scaffold |
| 2 | `(h : HasDirichletDensity S δ)`    | full two-sided density (`Tendsto … 𝓝 δ`) | density exists and is positive | yes (upper density) | Could be weakened to `HasUpperDirichletDensity` (`limsup`), which still vanishes on finite sets — but that is a *project* generalisation of a *project* definition, not a mathlib-relevant one |
| 3 | `(hδ : 0 < δ)`                     | positive real density            | positive density                 | NO                  | positivity is the essential hypothesis; without it the conclusion is false (density-0 sets can be finite) |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *for the project's `HasDirichletDensity` predicate.*
Number of weakening opportunities found: 1 (state against `HasUpperDirichletDensity`/`limsup`) — but this is
a weakening *internal to a project-local definition*, with no bearing on mathlib (which has neither predicate).
Cost of restatement: CHEAP, but irrelevant — see Phase 5/6 (mathlib has no Dirichlet-density notion, so the
restatement target does not exist in mathlib either).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1  | "let X be a foo" preambles → typeclasses? | no | — | hypotheses are already a propositional predicate + positivity |
| 2  | sequences/metric → filters/nets/topology? | no | `HasDirichletDensity` is *already* filter-based (`Tendsto … (𝓝[>] 1)`); the proof already uses `tendsto_nhds_unique`. Nothing to filter-ise | — |
| 3  | construction → universal-property class? | no | nothing is constructed | — |
| 4  | set-with-closure-predicate → bundled substructure? | no | `S` is a bare `Set`; no lattice structure relevant | — |
| 5  | vector-space/metric/field-specific → weaker typeclass? | no | already over `ℝ` with `Tendsto`; the only "structure" is the project predicate | — |
| 6  | 1-categorical → higher-categorical? | no | not categorical | — |
| 7  | concrete index (ℕ/ℤ/ℝ) → arbitrary additive structure? | no | the "index" is the analytic parameter `s : ℝ` in a genuine real limit; not an artificial concretisation | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The statement is already maximally idiomatic for what it is — a one-line
contrapositive over a filter-limit predicate. There is no Bourbaki-2.0 reformulation, because the only
abstraction available (the project's `HasDirichletDensity`) is the very thing the statement is *about*, and
the genuinely-abstract kernel (`tendsto_nhds_unique`) is already a mathlib lemma being invoked directly.

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (introduces no definitional equalities or typeclass-search paths).

## Mathlib search-status: `infinite_of_hasDirichletDensity_pos` (Phase 5)

[A] Lean-Finder       (MCP unavailable in this env)                                  n/a: tool not present; substituted by authoritative grep of mathlib source [D]
[B] Loogle            (MCP unavailable in this env)                                  n/a: tool not present; substituted by [D]
[C] LeanSearch        (MCP unavailable in this env)                                  n/a: tool not present; substituted by [D]
[D] Grep mathlib src  `HasDirichletDensity` / `DirichletDensity` / `NaturalDensity` / `hasDensity` over `.lake/packages/mathlib/Mathlib/` → **0 hits**. Also grepped `Infinite` ∧ (`tendsto_nhds_unique`|`density`|`pos`) across `Mathlib/` → no "positive-limit ⟹ infinite-support" lemma. `tendsto_nhds_unique` found (Topology/Separation/Hausdorff.lean:179). | hits for building block only
[E] Name pattern      grep for `infinite_of_*density*` in mathlib                    no hits

Searched for both:
  - the user's current form (`HasDirichletDensity … → S.Infinite`) — **not in mathlib**: mathlib has **no
    Dirichlet-density concept at all**, so the statement is unstatable in mathlib as written.
  - the literature-standard / abstract form ("density vanishing on finite sets, positive ⟹ infinite") —
    **not in mathlib** as a packaged lemma; only the generic engine `tendsto_nhds_unique` exists.

Concluded:
  - **not in mathlib** (all methods exhausted; mathlib has neither `HasDirichletDensity` nor any
    "positive-density ⟹ infinite" wrapper). The only mathlib ingredient is the building block
    `tendsto_nhds_unique` (`Mathlib/Topology/Separation/Hausdorff.lean:179`).

## Composition check (+ call-sites) (Phase 6)

### Call sites — `infinite_of_hasDirichletDensity_pos`

Internal use count: **1** (within the project, excluding the declaring file).
External-to-file callers: 1 file (the same file `Main.lean`).

| Caller file:line  | Usage pattern (one-line excerpt)                                        |
|-------------------|-------------------------------------------------------------------------|
| Main.lean:133     | `refine infinite_of_hasDirichletDensity_pos (chebotarev_density C) ?_`  |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?):
  - (none) — across the entire monorepo, `tendsto_nhds_unique` is used in ~50 places, but **nowhere** is the
    specific "finite ⟹ `hasDirichletDensity_of_finite` ⟹ contradiction with positivity" pattern re-derived
    inline. The lemma is the unique home of that two-line argument; it just has only one consumer so far.

Call-site signal: K = 1 internal use, no inline re-derivation → "possibly the wrong abstraction / could be
inlined" — leans NO-composable. The single consumer is `infinite_setOf_frobenius_class` (the qualitative
"infinitely many primes per Frobenius class" corollary of `chebotarev_density`).

### Composition check (Phase 6a)

Can `infinite_of_hasDirichletDensity_pos` be derived in ≤3 chained calls?

Attempt 1 (the actual proof): `fun hfin ↦ hδ.ne' (tendsto_nhds_unique h (hasDirichletDensity_of_finite K hfin))`
  - decls used: `tendsto_nhds_unique` (**mathlib**), `hδ.ne'` (**mathlib**, `ne_of_gt`-flavour), and
    `hasDirichletDensity_of_finite` (**PROJECT-LOCAL**, `Density.lean:588`).
  - Result: **succeeds** — it is literally a 2-mathlib-call composition over one project lemma.
  - Notes: the composition is genuine and trivial (term-mode, one line). BUT its load-bearing argument
    `hasDirichletDensity_of_finite` is **not** a mathlib lemma — it is project-local, and itself is *also*
    unstatable in mathlib (mathlib has no `HasDirichletDensity`).

Conclusion: **NOT-COMPOSABLE *from mathlib primitives alone*** — the composition needs the project lemma
`hasDirichletDensity_of_finite`. Equivalently: the statement is not even *expressible* in mathlib, because
`HasDirichletDensity` is a project definition mathlib does not contain. (It *is* a trivial composition over
**project** code — which is exactly why it should be inlined at its one call site, not upstreamed.)

## Verdict: `Chebotarev.infinite_of_hasDirichletDensity_pos`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): standard *unnamed* one-line corollary ("positive Dirichlet density ⟹
  infinite"); never abstracted; ≥4 WebSearch channels + nLab/Stacks/arXiv triaged.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for the project predicate; no modern-idiom move (the
  abstract kernel `tendsto_nhds_unique` is already invoked directly).
- Mathlib search (Phase 5): **not in mathlib** — mathlib has no Dirichlet-density notion whatsoever; only
  the building block `tendsto_nhds_unique` exists.
- Composition check (Phase 6): NOT-COMPOSABLE *from mathlib alone* (needs project-local
  `hasDirichletDensity_of_finite`); but it IS a trivial 2-line composition over **project** code.

**Rationale.**
The statement is phrased entirely in terms of `HasDirichletDensity`, a definition that lives **only in this
project** — mathlib has no Dirichlet (or analytic) density concept at all (Phase 5, [D] grep = 0 hits). So
this theorem cannot be added to mathlib *as written*: its very signature mentions a project-private predicate.
Mathematically the content is the textbook one-liner "positive density ⟹ infinite" (Phase 3), which every
source proves in a single line and none dignifies with a name. In Lean it unfolds to exactly that: a
two-call composition `hδ.ne' (tendsto_nhds_unique h (hasDirichletDensity_of_finite K hfin))`, where the only
mathlib ingredient is `tendsto_nhds_unique`; the substantive input `hasDirichletDensity_of_finite` is itself
project-local (and itself unstatable in mathlib). The right home for this is therefore the project, not
mathlib — and with a single call site and a one-line proof, it is a textbook NO-composable: inline it (or
keep it as the project's own thin convenience wrapper, which is the natural choice).

**WHY not (refactor-actionable).**
Mathlib has the *generic* building block `tendsto_nhds_unique` but neither this exact form nor the predicate
it is stated over. The wrapper is a 2-call composition over project code:
- `hasDirichletDensity_of_finite K hfin : HasDirichletDensity S 0` — **project**, `Density.lean:588`
  (this is the real mathematical content: "finite ⟹ density 0"; it is itself project-local and not a
  mathlib candidate, since `HasDirichletDensity` is project-only).
- `tendsto_nhds_unique h (…) : δ = 0` — **mathlib**, `Mathlib/Topology/Separation/Hausdorff.lean:179`
  (works because `HasDirichletDensity _ _` is definitionally a `Tendsto … (𝓝 _)` into `ℝ`, which is `T2`).
- `hδ.ne' (…)` — **mathlib**, closes `False` from `0 < δ` and `δ = 0`.

Mathlib building blocks:      `tendsto_nhds_unique` (`Mathlib/Topology/Separation/Hausdorff.lean:179`),
                              `LT.lt.ne'` (`Mathlib/Order/Basic.lean`).
Composition sketch (≤3 lines):
```lean
-- inlined at the single call site, given `hdens : HasDirichletDensity S δ` and `hδ : 0 < δ`:
fun (hfin : S.Finite) =>
  hδ.ne' (tendsto_nhds_unique hdens (hasDirichletDensity_of_finite K hfin))
```
Call sites in our project (from Phase 6.0):  **K = 1** (`Main.lean:133`, inside `infinite_setOf_frobenius_class`).
Refactor plan: there is exactly one consumer. Either (a) **inline** the one-line term at `Main.lean:133` —
replace `refine infinite_of_hasDirichletDensity_pos (chebotarev_density C) ?_` with the body above, applied to
`chebotarev_density C`, supplying the positivity proof already assembled there (the `div_pos` block at
Main.lean:134–136); or (b) **keep the wrapper as a project-local convenience lemma** — it is harmless,
well-named, and documents intent. Recommended: keep it local (it is genuinely useful project API and the
inlining saves nothing meaningful), but do **not** upstream it. This is NOT a mathlib contribution.

**Note.** The result is *not* `NO-mathlib-has-it`: mathlib has neither the statement nor the predicate. It is
*not* a YES bucket: the statement references a project-private definition, so it is unstatable upstream, and
the mathematical content is a universally-known nameless one-liner. The honest classification under the
five-bucket scheme is **NO-composable-from-mathlib**, read as "this is a trivial wrapper that should be
inlined / kept local rather than upstreamed" — with the caveat (recorded here for the human) that the
composition leans on a project lemma rather than pure mathlib, because the entire `HasDirichletDensity` API is
project-local.

---

## Next step

Delete-or-keep is a project-local call. Do **not** open a mathlib PR. Either inline the one-line proof at
the single call site `Main.lean:133`, or retain `infinite_of_hasDirichletDensity_pos` as a documented
project convenience wrapper (recommended). No upstreaming action.
