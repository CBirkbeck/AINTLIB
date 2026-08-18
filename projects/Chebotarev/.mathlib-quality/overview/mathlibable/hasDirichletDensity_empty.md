# /mathlibable report — `Chebotarev.hasDirichletDensity_empty`

> Step-9 (overview) mathlibable assessment, run as the full 10-phase `/mathlibable`
> workflow on a single declaration. ChatGPT-math MCP was **down** (documented
> fallback) — the literature channel used WebSearch + nLab/Wikipedia/lecture-note +
> arXiv. The Lean MCP search tools (loogle / leansearch / lean_local_search) are
> **not exposed** in this environment and the local build is stale, so Phase 5
> relies on direct `grep` over the vendored mathlib tree `.lake/packages/mathlib/`
> (commit `d90090f`, toolchain `v4.31.0-rc2`), which is authoritative for "is it
> in mathlib". This mirrors the sibling `HasDirichletDensity.md` run.

---

## Phase 0 — Baseline

```
### Baseline (Phase 0)
- lake build:               (stale — not rebuilt; reasoned from source per task note)
- decl `Chebotarev.hasDirichletDensity_empty`:  resolved at
                            projects/Chebotarev/CebotarevDensity/Density.lean:95
- true qualified name:      Chebotarev.hasDirichletDensity_empty
                            (namespace `Chebotarev` opened Density.lean:44, closed
                            line 603; theorem at line 95) — the parsed guess
                            Chebotarev.hasDirichletDensity_empty is CORRECT.
- kind:                     theorem  (Phase 4.5 diamond/defeq risk is n/a)
- has sorry:                no  (proof is a total `simpa … using tendsto_const_nhds`)
- module docstring summary: Dirichlet density of a set S of prime ideals of 𝓞 K,
                            δ(S) = lim_{s→1⁺} (Σ_{𝔭∈S} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s});
                            plus limsup/liminf upper & lower variants.
```

Source (verbatim, Density.lean:94–100):

```lean
/-- The Dirichlet density of the empty set is `0`. -/
theorem hasDirichletDensity_empty :
    HasDirichletDensity (∅ : Set (Ideal (𝓞 K))) 0 := by
  have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧
      𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := ⟨fun x ↦ x.2.1⟩
  simpa only [HasDirichletDensity, primeIdealZetaSum_def, tsum_empty, zero_div]
    using tendsto_const_nhds
```

Context: `variable {K : Type*} [Field K] [NumberField K]` (Density.lean:46).
`primeIdealZetaSum S s := ∑' 𝔭 : {𝔭 // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)`
(Density.lean:50). `HasDirichletDensity S δ := Tendsto (fun s ↦ primeIdealZetaSum S s / primeIdealZetaSum univ s) (𝓝[>] 1) (𝓝 δ)`
(Density.lean:64).

---

## Phase 1 — Statement (prose)

### Statement (Phase 1)

`Chebotarev.hasDirichletDensity_empty` is **a theorem** stating:

> Let `K` be a number field with ring of integers `𝓞 K`. The empty set of prime
> ideals has Dirichlet density `0`: `δ(∅) = 0`.

Unfolding the definition, the claim is that the ratio
`P_∅(s) / P_univ(s) = (Σ_{𝔭 ∈ ∅} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})` tends to `0` as
`s ↓ 1⁺`. Since the numerator is an empty sum it is identically `0`, so the ratio
is the constant function `0 / P_univ(s) = 0`, whose limit is `0`. This is the
trivial boundary value of the Dirichlet-density measure (`δ(∅) = 0`, the bottom of
the `[0,1]` range it takes), and the multiplicative-zero base case for any additive
manipulation of densities.

**Variables / typeclasses (Lean side):**
- `{K : Type*} [Field K] [NumberField K]` — the number field; `NumberField`
  supplies the finiteness making `absNorm` and the prime-ideal zeta series
  meaningful (used by the parent def, not the proof of this lemma).

**Hypotheses (Lean side):** none.

**Conclusion (math):** `δ(∅) = 0`.

**Conclusion (Lean):** `HasDirichletDensity (∅ : Set (Ideal (𝓞 K))) 0`, i.e.
`Tendsto (fun s ↦ primeIdealZetaSum ∅ s / primeIdealZetaSum univ s) (𝓝[>] 1) (𝓝 0)`.

---

## Phase 2 — Preliminary checks

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-property *companion / basic-API* lemma about the project's
`HasDirichletDensity` def — the trivial `δ(∅) = 0` boundary value. Not a new
structure, not a `## Main results` entry, not named after a person.

(Literature width is EXHAUSTIVE regardless — recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure`. One-liner check **n/a** (the
one-liner negative signal is about definitions; basic-API *lemmas* are expected
to be short). The proof is a 2-line term (`have … ; simpa … using
tendsto_const_nhds`).

---

## Phase 3 — Literature search (EXHAUSTIVE)

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                      | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "Dirichlet density empty set of primes equals zero analytic number theory"                 | yes  | `δ(∅)=0` follows from the def (empty numerator → 0)  | Wikipedia "Dirichlet density"; MIT 18.785 (Kedlaya) & Harvard M229 (Elkies) lecture notes — density ∈ [0,1], `δ(∅)=0` is the trivial bottom, not stated as a named theorem |
|  2 | WebSearch (general form)         | "mathlib4 analytic density of primes Dirichlet density formalization"                      | yes  | density = lim Σ_{p∈A} p^{-s} / Σ_p p^{-s} as s↓1     | confirms the standard ratio definition; arXiv 2503.00959 "Formalizing zeta and L-functions in Lean" formalizes Dirichlet's theorem but NO density measure for prime ideals |
|  3 | WebSearch (named-after/aliases)  | (covered by #1/#2) "analytic density" alias of "Dirichlet density"                         | yes  | same; "analytic density" is the synonym              | HandWiki/Wikipedia: the boundary fact `δ(∅)=0` is universally a one-liner remark, never a citable theorem |
|  4 | ChatGPT MCP                      | (standard-form + generality + history)                                                     | n/a  | MCP DOWN (documented fallback)                       | substituted by #1–#3 + nLab; the concept is elementary so the loss is minimal |
|  5 | Local references                 | grep `.mathlib-quality/references/` and `refs/Chebotarev/`                                  | n/a  | neither directory present                            | recorded n/a — references not provisioned for this project |
|  6 | nLab                             | "Dirichlet density" / "analytic density of primes"                                         | no   | nLab has no dedicated entry                          | nLab does not separately axiomatise Dirichlet density; the elementary `δ(∅)=0` has no nLab statement |
|  7 | nCatLab (if categorical)         | —                                                                                          | n/a  | not a categorical concept                            | a real-analytic limit of a Dirichlet ratio; nothing categorical |
|  8 | Stacks Project (if alg geom)     | —                                                                                          | n/a  | not an algebraic-geometry concept                    | analytic-NT density, not a scheme-theoretic notion |
|  9 | MathOverflow / Math.SE           | "Dirichlet density of empty / finite set of primes"                                        | yes  | δ(finite)=0, hence δ(∅)=0                             | standard folklore: any finite (a fortiori empty) set of primes has Dirichlet density 0; treated as immediate from the definition |
| 10 | recent arXiv (last 5 years)      | "Dirichlet density formalization Lean" → 2503.00959                                         | yes  | zeta/L-function formalization, Dirichlet's theorem   | the active Lean ANT effort; does NOT contain a prime-ideal Dirichlet-density measure — so neither it nor this `δ(∅)=0` lemma is upstream yet |

Protocol pass: WebSearch ran 3 distinct generality levels (#1 specific, #2
general/Lean, #3 aliases). ChatGPT MCP recorded n/a-with-reason (down). Local
references n/a-with-reason (absent). nLab checked. Stacks/nCatLab/MathOverflow/
arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: **Dirichlet density (= analytic density) of a set of
primes**, and specifically its **trivial boundary value `δ(∅) = 0`**.
Sources agree on the standard form: **yes** — the density is the `s↓1⁺` limit of
the ratio of partial prime zeta sums; for the empty (or any finite) set the
numerator vanishes, so `δ = 0`. Every source (Wikipedia, MIT/Harvard notes,
MathOverflow) treats `δ(∅)=0` as an *immediate consequence of the definition*,
never as a separately-named theorem.
Most general standard form: for **any** number field and **any** set of prime
ideals, `δ(∅) = 0`; more generally `δ` of a finite set is `0`. The `δ(∅)=0`
instance is the minimal special case.
Generality dimensions where the literature varies:
  - ground field: ℚ (classical Dirichlet) vs. arbitrary number field `K` — the
    project's `K`-level statement is already the general one.
  - emptiness vs. finiteness: `δ(∅)=0` is the special case of `δ(finite)=0`.
Disagreement with the literature: **none**. The Lean statement is exactly the
textbook boundary value, at the general (arbitrary-`K`) level.

If the literature returned NOTHING the decl would look project-specific; here the
*concept* is fully standard but the specific fact is sub-citable folklore — which
points the verdict at "ships as basic API of the parent def", not "novel result".

---

## Phase 4 — Generality analysis

### Generality analysis — `Chebotarev.hasDirichletDensity_empty`

Literature-standard form (from Phase 3): for any number field `K`, `δ(∅) = 0`
(a special case of `δ(finite set) = 0`).

| # | Parameter / hypothesis            | Current Lean form          | Literature-standard form    | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|----------------------------|------------------------------|---------------------|----------------------------------|
| 1 | `[Field K] [NumberField K]`       | number field               | number field                 | NO                  | the parent def `HasDirichletDensity` is stated over `[NumberField K]`; this companion lemma cannot be more general than its def. Already the literature-general field level (arbitrary `K`, not just ℚ). |
| 2 | the set is `∅`                    | empty set                  | empty (⊂ finite)             | yes (→ finite)      | could be generalised to "any finite set has density 0" — but that is a *strictly stronger, separate* lemma, not a weakening of this one's hypotheses; see 4b. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *as a statement about the empty set*.
Number of weakening opportunities found: **0** (on the stated hypotheses — `K` is
already arbitrary; there are no hypotheses to weaken).

The "generalise to finite sets" option (`δ(finite) = 0`) is a **stronger sibling
theorem**, not a weakening of `hasDirichletDensity_empty`'s assumptions. It would
be its own declaration (`hasDirichletDensity_of_finite` or similar) that this
empty-case follows from in one line. Mathlib convention (see Phase 6) is to keep
the `_empty` simp-lemma *and* offer the finite version — they coexist (cf.
`schnirelmannDensity_empty` living beside the general API). So this does not flip
the verdict to YES-but-generalise-first: the empty-set lemma stays as the canonical
basic-API/`@[simp]`-shaped fact.

Proposed restatement: none required.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                       | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                            | no       | —                      | no bundled hypotheses here; just `[NumberField K]` |
|  2 | sequences/metric → filters/nets/topological?                                                   | no       | —                      | the statement is *already* filter-native: `Tendsto … (𝓝[>] 1) (𝓝 0)` |
|  3 | construct an object where a universal-property class would characterise it?                    | no       | —                      | nothing is constructed; it's a limit equality |
|  4 | set-with-closure-predicate → bundled substructure?                                             | no       | —                      | `∅ : Set _` is the genuine empty set, not a substructure |
|  5 | vector/metric/field-specific → modules/pseudometric/(semi)ring?                                | no       | —                      | the number-field hypothesis is intrinsic to the density def |
|  6 | 1-categorical → higher-categorical?                                                            | no       | —                      | not categorical |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive group/monoid?                                      | no       | —                      | the `∅` here is a *set of ideals*; the only generalisation axis is ∅ ⊂ finite (a stronger theorem, see 4b), not an index swap |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The statement is already in the contemporary
mathlib idiom (filter `Tendsto` over `𝓝[>] 1`, the genuine empty set). The only
neighbouring move is the *stronger* `δ(finite)=0` theorem, handled in 4b — not a
"modernisation" of this lemma.

---

## Phase 4.5 — Diamond / defeq risk

n/a — declaration kind is `theorem` (no definitional equalities or
typeclass-search paths introduced).

---

## Phase 5 — Mathlib search

### Mathlib search-status: `Chebotarev.hasDirichletDensity_empty`

```
[A] Lean-Finder       (MCP unavailable in this env)                    n/a: tool not exposed
[B] Loogle            (MCP unavailable in this env)                    n/a: tool not exposed
[C] LeanSearch        (MCP unavailable in this env)                    n/a: tool not exposed
[D] Grep mathlib src  DirichletDensity / density.*empty / hasDirichletDensity
                      / Dirichlet.*ensity over Mathlib/NumberTheory/   no hits — NO Dirichlet density notion in mathlib
[E] Name pattern      hasDirichletDensity_empty / *Density_empty over .lake mathlib
                      → only schnirelmannDensity_empty, edgeDensity_empty_{left,right}
                                                                       hits are DIFFERENT density concepts
```

Searched for both:
  - the user's current form (`HasDirichletDensity ∅ 0`) — mathlib has **no**
    `HasDirichletDensity` / Dirichlet density of prime ideals at all
    (grep over `Mathlib/NumberTheory/` returns nothing; the only "density"
    hits in NumberTheory are `Liouville/Residual.lean`, a topological
    residuality, unrelated).
  - the literature-standard form (`δ(∅)=0`, and the stronger `δ(finite)=0`) —
    also absent, for the same reason: the parent measure isn't in mathlib.

The only `*Density_empty = 0` lemmas in mathlib are
`Combinatorics/Schnirelmann.lean:190` `schnirelmannDensity_empty` (`@[simp]`)
and `Combinatorics/SimpleGraph/Density.lean:140,361` `edgeDensity_empty_{left,
right}` — Schnirelmann density of natural numbers and graph edge-density
respectively, **different mathematical objects**. They are *precedent* for the
convention (Phase 6), not the same theorem.

Concluded: **not in mathlib** (grep over the vendored tree exhausted, plus the
literature-standard and the stronger finite form; the parent `HasDirichletDensity`
def is itself absent from mathlib, so no specialisation source exists).

---

## Phase 6 — Composition check (+ call-sites signal)

### Call sites — `Chebotarev.hasDirichletDensity_empty`

Internal use count: **1** (within the project, excluding the declaring file).
External-to-file callers: **1 distinct file**.

| Caller file:line              | Usage pattern (one-line excerpt)                                   |
|-------------------------------|---------------------------------------------------------------------|
| Abelian.lean:115              | `| empty => simpa using hasDirichletDensity_empty (K := F)`         |

Context (Abelian.lean:108–115): it is the **base case** of the induction in the
private lemma `hasDirichletDensity_biUnion_const` (density of a finite disjoint
union of equal-density sets) — the empty `Finset` gives the empty union with
density `0 • c = 0`. This is exactly the role basic-API `_empty` lemmas play:
they discharge the `Finset.induction` base case.

Inline-derivation grep (was `δ(∅)=0` re-derived elsewhere without this lemma?):
  - (none) — the only place needing `δ(∅)=0` calls this lemma.

Call-sites signal: **K = 1 internal use**, no inline re-derivation. Per the
Phase-6 table that alone leans "possibly inlinable". BUT the decisive factor is
Phase 5: the thing it would be inlined *from* (the parent def + the mathlib
2-call composition) is not enough to make it NO, because the parent def is not in
mathlib — see the composition analysis and verdict below.

### Composition check (Phase 6)

Can `hasDirichletDensity_empty` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `by simpa only [HasDirichletDensity, primeIdealZetaSum_def, tsum_empty, zero_div] using tendsto_const_nhds`
  - Mathlib decls used: `tsum_empty`, `tendsto_const_nhds` (`Topology/Neighborhoods.lean:190`),
    `zero_div`.
  - Result: **succeeds** — but only after unfolding the **project-only** defs
    `HasDirichletDensity` and `primeIdealZetaSum` (and supplying the project
    `IsEmpty` instance for the subtype). This is precisely the idiom mathlib
    itself uses verbatim at `Mathlib/Analysis/Normed/Group/Tannery.lean:48`:
    `simpa only [tsum_empty] using tendsto_const_nhds`.
  - Notes: the mathlib *primitives* (`tsum_empty`, `tendsto_const_nhds`) compose
    trivially, **conditional on the parent `HasDirichletDensity` definition
    existing**. They do not, on their own, mention Dirichlet density.

Conclusion: **NOT-COMPOSABLE from mathlib alone.** The composition closes only by
unfolding a project definition that mathlib does not contain. Composition-from-
mathlib (the NO-composable bucket) requires that the *statement itself* be
expressible and dischargeable purely from mathlib decls inlined at the call site;
here the statement names `HasDirichletDensity`, which is not in mathlib. Therefore
this lemma cannot be "inlined away into mathlib calls" — it is the basic API of a
project def. Whether that def (and hence this lemma) *belongs* in mathlib is the
Phase-5/Phase-3 question, answered below.

---

## Phase 7 — Verdict

## Verdict: `Chebotarev.hasDirichletDensity_empty`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): standard concept (Dirichlet/analytic density of a
  set of primes); `δ(∅)=0` is its universally-acknowledged trivial boundary
  value (Wikipedia, MIT 18.785, Harvard M229, MathOverflow). No disagreement with
  the literature; statement is at the general arbitrary-`K` level.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** as an empty-set statement
  (0 weakenings; `K` already arbitrary). Phase 4c: no modern-idiom move — already
  filter-native `Tendsto … (𝓝[>] 1) (𝓝 0)`. The only neighbour is the *stronger*
  `δ(finite)=0` sibling, which would coexist, not replace it.
- Mathlib search (Phase 5): **not in mathlib** — mathlib has no Dirichlet density
  of prime ideals at all; the only `*Density_empty` lemmas are Schnirelmann /
  graph edge density (different objects).
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib alone — the
  2-call mathlib idiom closes the proof only after unfolding the project-only
  `HasDirichletDensity` def, which mathlib lacks. K=1 internal call (the
  `Finset.induction` base case in `hasDirichletDensity_biUnion_const`).

**Rationale:**

This lemma is the trivial-boundary basic-API fact `δ(∅) = 0` for the project's
`HasDirichletDensity` definition. Its mathlib-fate is bound to that def's: the
sibling run on `Chebotarev.HasDirichletDensity` returned **YES-add-as-is**
(`HasDirichletDensity.md`, Phase 7), and a density definition is essentially
useless in a library without its zero/empty base case. Mathlib's own convention
confirms this pairing — `schnirelmannDensity_empty` ships as an `@[simp]` lemma
right beside the Schnirelmann density def (`Combinatorics/Schnirelmann.lean:190`),
and `edgeDensity_empty_left/right` beside graph edge density. So when
`HasDirichletDensity` goes upstream, `hasDirichletDensity_empty` should go **with
it, in the same PR**, ideally tagged `@[simp]` (its whole purpose is to fire
automatically in density manipulations, exactly as in its only call site, the
`Finset.induction` empty base case at Abelian.lean:115).

The composition check (Phase 6) explains why this is YES-add-as-is and not
NO-composable: although the *proof* is the 2-call mathlib idiom `simpa only
[tsum_empty] using tendsto_const_nhds` (used verbatim at mathlib's
`Tannery.lean:48`), that composition discharges the goal only after unfolding
`HasDirichletDensity`/`primeIdealZetaSum`, which are not mathlib decls. You cannot
inline this at a mathlib call site, because the *statement* references a definition
mathlib does not have. It is genuine new API attached to a genuinely-new (and
separately YES-rated) definition, not a re-derivation of something mathlib already
provides. The K=1 call-site count is the expected footprint of a `_empty` simp
lemma — low local use, but indispensable API surface for any downstream density
calculus (and mathlib's `schnirelmannDensity_empty` precedent has the identical
"few direct uses, kept anyway as canonical basic API" profile).

WHY add it (refactor-actionable):
- **New content / the gap.** Mathlib has *no* analytic (Dirichlet) density of
  prime ideals — the active Lean ANT effort (arXiv 2503.00959, "Formalizing zeta
  and L-functions in Lean") formalizes Dirichlet's theorem and L-functions but
  ships no prime-ideal density *measure*. The named gap: there is no
  `Dirichlet density` API in `Mathlib/NumberTheory/`, hence no `_empty` base
  case for it. This lemma is the bottom of that missing API.
- **Composes with mathlib.** As an `@[simp]`-shaped fact `δ(∅)=0`, it lets every
  `Finset.induction` / `Set.Finite.induction_on` over a family of prime-ideal sets
  discharge its base case automatically (its actual use at Abelian.lean:115), and
  it is the additive-zero anchor for the density-of-disjoint-union API
  (`hasDirichletDensity_biUnion_const` and the union/subset lemmas in Main.lean).

Proposed mathlib location: ships **with** `HasDirichletDensity` — wherever that
def lands. Natural home `Mathlib/NumberTheory/Density/Dirichlet.lean` (a new file
for the prime-ideal Dirichlet-density API), adjacent to
`Mathlib/NumberTheory/NumberField/DedekindZeta.lean` whose Euler product /
norm-summability the def depends on.
Proposed PR title: ship inside `"feat(NumberTheory): Dirichlet density of a set of
prime ideals"` (the def's PR), as one of its basic-API lemmas — NOT a standalone
PR.
PR grouping (REQUIRED): bundle with `Chebotarev.HasDirichletDensity` (YES-add-as-is,
the parent def), `primeIdealZetaSum` + `primeIdealZetaSum_def`, and the other
foundational density-API lemmas from Density.lean that earned YES (e.g. the
`HasUpperDirichletDensity` / `HasLowerDirichletDensity` defs and their empty/basic
facts). The right grain is "Dirichlet-density-of-prime-ideals foundations" as a
single feature PR; `hasDirichletDensity_empty` is one line of it. Consider also
adding the *stronger* `δ(finite set) = 0` lemma in the same PR (Phase 4b) so the
empty case is a one-line corollary and downstream callers have both.
Pre-PR checklist before opening:
- [ ] `/generalise Chebotarev.hasDirichletDensity_empty` — confirm no further
      weakening (expected: none; consider adding `δ(finite)=0` as the stronger form).
- [ ] `/cleanup .../Density.lean Chebotarev.hasDirichletDensity_empty` — full
      audit; add `@[simp]` and confirm the `IsEmpty` instance is the cleanest spelling.
- [ ] Pick a reviewer from recent `Mathlib/NumberTheory/NumberField/` /
      L-function commits (the zeta/L-function formalization authors).

---

## Next step

`/generalise Chebotarev.hasDirichletDensity_empty` (confirm no further weakening
and consider the stronger `δ(finite)=0` form), then ship **with** the parent
`HasDirichletDensity` def — one feature PR, `"feat(NumberTheory): Dirichlet
density of a set of prime ideals"` — tagged `@[simp]`. Do **not** submit standalone.
```
