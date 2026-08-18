# /mathlibable report — `compl₂EDSAux_one`

> Step-9 mathlibable assessment (AINTLIB /overview), NagellLutz project
> (Nagell–Lutz theorem; elliptic curves; division polynomials; EDS).
> Source: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1020`.
> Assessment reasoned from the pinned mathlib source (local build stale per task).
> Pinned mathlib rev: `09b373db6e247a35cfa5e44578c09a20e7c97271`.

## Baseline (Phase 0)

- lake build:               not rebuilt (stale per task; reasoned from source)
- decl `compl₂EDSAux_one`:  ✓ resolved at `EllipticDivisibilitySequence.lean:1020`
  (prompt cited 1021; the lemma *head* is L1020 — `compl₂EDSAux_neg_one` is L1021.)
- kind:                     `@[simp] lemma`
- has sorry:                no
- qualified name:           **`compl₂EDSAux_one`** (ROOT namespace) — VERIFIED:
  file opens `namespace EllSequence` at L90 but **closes** it at L597. The lemma is
  inside `section NormEDS` (L881, a *section*) and `section Complement` (L1010, a
  *section*); the next `namespace EllSequence` opens at L1079, *after* L1020. No
  namespace is active at L1020, so bare = qualified = `compl₂EDSAux_one`.
- module docstring summary: "Elliptic divisibility sequences (EDS) and normalised
  EDSs from initial terms" — this file is a **fork** of
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, extended with a
  `Complement` section feeding the Nagell–Lutz `ω`-division-polynomial machinery.

## Statement (Phase 1)

```lean
/-- An auxiliary expression that appears in the definition of the numerator of
the reduced invariant and in the definition of the `ω` family of division polynomials. -/
def compl₂EDSAux : R :=
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * if Even m then 1 else b

@[simp] lemma compl₂EDSAux_one : compl₂EDSAux b c d 1 = -b := by simp [compl₂EDSAux]
```

`compl₂EDSAux_one` evaluates the project-local auxiliary `compl₂EDSAux` at `m = 1`,
asserting `= −b`. With `p := preNormEDS (b⁴) c d`: at `m = 1`,
`p(−1)·p(2)²·b = (−1)·1²·b = −b`.

Via `compl₂EDSAux_mul_b` (L1025): `compl₂EDSAux(m)·b = W(m−2)·W(m+1)²`, where
`W = normEDS b c d`. So `compl₂EDSAux` is **one of the two subtracted products**
inside the 2-complement difference `Wᶜ₂(m)·b = W(m−1)²W(m+2) − W(m−2)W(m+1)²`,
divided by `b`, isolated as its own def because it independently appears in the
reduced-invariant numerator and the `ω` division-polynomial family. It is a
summand-shaped piece of the genuine 2-complement, not the 2-complement itself.

- Variables: `b c d : R` (`R` an arbitrary comm ring).
- Hypotheses: none.
- Conclusion (math): `A(1) = −b`.
- Conclusion (Lean): `compl₂EDSAux b c d 1 = -b`.

## Size classification (Phase 2a)

Verdict: **SMALL** — a base-case `@[simp]` value lemma (the def at literal `m=1`);
not a named theorem, structure, or `## Main results` entry. (Lit width EXHAUSTIVE
regardless.)

## One-line check (Phase 2b)

Kind is `lemma` → n/a. Proof body is a single `by simp [compl₂EDSAux]` (a value/glue
lemma), reinforcing SMALL and pointing away from a standalone contribution.

## Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific) | EDS division polynomial `W(m-2) W(m+1)` complement witness `W(k)∣W(2k)` | yes (parent only) | 2-complement `Wᶜ₂`: `W(k)·Wᶜ₂(k)=W(2k)` | Wikipedia + mathlib docs confirm the **full** 2-complement; isolated single term unnamed |
| 2 | WebSearch (general) | normalised EDS initial values division polynomial ω auxiliary term (Stange/Shipsey) | yes (context) | `preNormEDS`/`normEDS` recursion; `ω` family | Stange eprint 2025/521; no isolated `W(m−2)W(m+1)²` term named |
| 3 | WebSearch (aliases) | `"complEDS"`/`"compl₂EDS"` mathlib 2-complement witness divides | yes | mathlib `complEDS₂`/`complEDS`; arXiv 2604.05280 "On Elliptic Sequences over Commutative Rings" | upstream object is `complEDS₂` (whole difference), not a half-term |
| 4 | ChatGPT MCP (gpt-5.4, high) | standard name of `W(m−2)W(m+1)²`; is `A(1)=−b` notable; do treatments isolate it? | **n/a — tool errored** | — | Codex backend failed (`Command failed`), as task warned; fell back to WebSearch ×3 + direct mathlib-source reading |
| 5 | Local references | grep `.mathlib-quality/references/` "complement"/"EDS" | n/a | (no references dir for NagellLutz) | recorded n/a |
| 6 | nLab | "elliptic divisibility sequence" | no | — | no nLab page; not categorical |
| 7 | nCatLab | (categorical?) | n/a | — | not a categorical concept |
| 8 | Stacks Project | (alg-geom concept?) | n/a | — | EDS/division-poly bookkeeping; out of Stacks scope |
| 9 | MathOverflow/MSE | isolate single product term of EDS 2-complement | no | — | discussions use the full complement difference, never the half-term |
| 10 | recent arXiv (≤5y) | Stange isogeny division polynomials; arXiv 2604.05280 | yes (parent) | `ω`/division-poly families; 2-complement | confirms parent objects; no named isolated term; `A(1)=−b` not a noted identity |

Protocol pass: WebSearch ran ≥3 queries at distinct generality levels; ChatGPT MCP
attempted, recorded n/a-with-reason (backend down); local refs n/a-with-reason;
nLab/Stacks/MO/arXiv each checked or n/a-with-reason. The **pinned mathlib source**
was read directly (authoritative for the existence question).

### Literature summary (Phase 3)

Concept: the **second subtracted product** `W(m−2)·W(m+1)²` of the **2-complement**
of a normalised EDS (parent: the 2-complement `Wᶜ₂`, a standard object). The decl is
the *value at `m=1`* of the `/b` auxiliary `compl₂EDSAux`.

Sources agree on the standard form: yes for the **2-complement** `Wᶜ₂`
(= mathlib `complEDS₂`). **No** source isolates the single product as a named object;
it is internal bookkeeping the project pulls out because that term reappears in `ω`.
`A(1) = −b` is trivial base-case bookkeeping, not a noted identity.

Most general standard form: the 2-complement difference
`Wᶜ₂(k)·b = W(k−1)²W(k+2) − W(k−2)W(k+1)²`. The isolated half-term has no standard form.

Disagreement with the literature: none on the math; the literature simply does not
name this half-term.

## Generality analysis — `compl₂EDSAux_one`

| # | Param/hyp | Current Lean form | Literature-standard | Weaker? | Reason |
|---|-----------|-------------------|----------------------|---------|--------|
| 1 | `(b c d : R)` | arbitrary comm ring `R` | arbitrary comm ring | NO | already maximal (`preNormEDS` over any comm ring) |
| 2 | index `1` | literal `m=1` | (a base case) | NO | this *is* the specialisation; "more general" = the parent def itself |

### Generality verdict (Phase 4b)

Current form is **MAXIMALLY GENERAL** over `R`; a deliberate specialisation (value at
`m=1`). Weakening opportunities: 0. Cost: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reason |
|---|----------|----------|--------|
| 1 | bundled hyps → typeclasses? | no | already plain ring elements |
| 2 | sequences/metric → filters/topology? | no | finite ring identity, no topology |
| 3 | construction → universal property? | no | a numeric evaluation |
| 4 | set+closure → bundled substructure? | no | n/a |
| 5 | vector-space/field → module/semiring? | no | already arbitrary comm ring |
| 6 | 1-cat → higher-cat? | no | n/a |
| 7 | concrete index → general additive structure? | no | intrinsically the `m=1` base case |

Modern idiom available: **no** — a base-case `simp` value of a comm-ring auxiliary;
no organisational abstraction applies.

## Diamond / defeq risk (Phase 4.5)

n/a — kind is `lemma` (no definitional equality / typeclass-search path introduced).

## Mathlib search-status: `compl₂EDSAux_one`

Method note: `lean_loogle`/`lean_leansearch`/`lean_local_search` were unavailable in
this environment; substituted **direct grep over the pinned mathlib source**
(`.lake/packages/mathlib/Mathlib/`, rev `09b373db6e`) — strictly more authoritative
than the index for an existence question.

- [A] Lean-Finder — n/a (tool down); covered by source grep.
- [B] Loogle (type pattern) — grep for body
  `preNormEDS … (·−2) · preNormEDS … (·+1) ^ 2 * if Even` → **no hit** in mathlib.
- [C] LeanSearch (NL) — n/a (tool down); WebSearch ch.3 covered the NL form.
- [D] Grep mathlib src — `EDSAux`, `compl.*Aux`, `compl₂EDSAux`, `complEDS` across all
  of `Mathlib/`:
  - `EDSAux` / `compl₂EDSAux` / single-term `*Aux`: **no hit** (only unrelated `Aux`,
    e.g. `MeasureTheory/.../WithDensityFinite.lean`).
  - `complEDS` family: **PRESENT** — `complEDS₂` (L246), `complEDS₂_zero/one/two/
    three/four/neg` (L251–272), `complEDS₂_mul_b` (L329), `complEDS'` (L392),
    `complEDS` (L427), `complEDSRec'`/`complEDSRec` (L482/497).
- [E] Name pattern — n/a (tool down); the grep above is the name search.

Searched for both:
  - user's form (`compl₂EDSAux 1 = −b`): **not in mathlib** (def absent).
  - parent/literature object (2-complement `complEDS₂`): **IS in mathlib**, as the
    *single combined difference*, with **no split-out half-term**.

Concluded: **the isolated `compl₂EDSAux` is not in mathlib (all channels exhausted),
hence neither is its `m=1` value lemma.** Decisive structural fact: **mathlib has
evolved and absorbed this project's entire `section Complement`** under `complEDS`
naming — project↔mathlib correspondences:
`compl₂EDS`↔`complEDS₂`, `compl₂EDS_mul_b`↔`complEDS₂_mul_b`,
`compl₂EDS_zero/one/two/neg`↔`complEDS₂_zero/one/two/neg`,
`compl`/`compl'`↔`complEDS`/`complEDS'`, `normEDS_mul_compl₂EDS`↔
`normEDS_mul_complEDS₂`, `map_compl₂EDS`↔`map_complEDS₂`.
(The `.mathlib-quality/overview/mathlibable/` dir shows BOTH name-tracks side by side,
confirming the duplication.) What mathlib did **not** lift is the further split of the
2-complement difference into the single product `compl₂EDSAux` — that stays a
project-only refactoring, motivated by the `ω` construction.

## Call sites — `compl₂EDSAux_one`

Internal use count (the `_one` lemma, outside its own def line): **0**.
External-to-file callers: 0.

| Caller file:line | Usage pattern |
|------------------|----------------|
| (none) | `compl₂EDSAux_one` is never referenced by name anywhere in the repo |

Inline-derivation grep: surrounding code uses **sibling** value lemmas of the family —
`compl₂EDSAux_two` (`ZSMul.lean:279`), `compl₂EDSAux_mul_b` / `map_compl₂EDSAux`
(`EllipticDivisibilitySequence.lean:1374,1421`; `DivisionPolynomialOmega.lean:112`) —
but **not** `_one`.

Composability reading: `compl₂EDSAux_one` is `@[simp]`, intended to fire *inside*
`simp` (establishing simp-normal-form for the def's small values) rather than be
invoked by name — exactly as mathlib does for `complEDS₂_one/two/…`. Its parent **def**
`compl₂EDSAux` has ≥3 essential uses (`DivisionPolynomialOmega.lean:78`,
`EllipticDivisibilitySequence.lean:1365/1369`, `ZSMul.lean:279`) — so the family is
real API; the `_one` value lemma is the def's standard `@[simp]` companion.

## Composition check (Phase 6)

Can `compl₂EDSAux_one` be derived from mathlib in ≤3 chained calls?

Attempt 1: not derivable from mathlib **as stated** — the LHS names `compl₂EDSAux`,
a def absent from mathlib. The only "composition" first introduces the project's def,
then evaluates:
```lean
-- given `compl₂EDSAux` (project def):
example : compl₂EDSAux b c d 1 = -b := by simp [compl₂EDSAux]
-- unfolds to preNormEDS (b^4) c d (-1) * preNormEDS (b^4) c d 2 ^ 2 * b
--   = (-1)·1²·b = -b, via mathlib's preNormEDS base values.
```
Mathlib decls used: `preNormEDS` + base evaluations (`preNormEDS_one`,
`preNormEDS_two`, `preNormEDS_neg`/`Int.sign`) — all present.
Result: one `simp` line **once the def is in scope**.

Conclusion: **COMPOSABLE** (trivially, `simp [compl₂EDSAux]`), but only relative to the
project's own `compl₂EDSAux` def — a definitional unfolding + mathlib `preNormEDS` base
values, no new content. It cannot be a standalone mathlib lemma: its statement names a
non-mathlib def.

## Verdict: `compl₂EDSAux_one`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature (Phase 3): the 2-complement `Wᶜ₂` is standard (= mathlib `complEDS₂`);
  the **isolated half-term** `W(m−2)W(m+1)²` (`compl₂EDSAux`) has **no** literature
  name; `A(1) = −b` is trivial base-case bookkeeping.
- Generality (Phase 4): MAXIMALLY GENERAL; no modern-idiom move.
- Mathlib search (Phase 5): `compl₂EDSAux` (and `_one`) **not in mathlib**; mathlib
  already absorbed the *full* complement family as `complEDS₂`/`complEDS`, but not
  this further split.
- Composition (Phase 6): COMPOSABLE — `by simp [compl₂EDSAux]` from the def + mathlib
  `preNormEDS` base values.

**Rationale:**

`compl₂EDSAux_one` is the `@[simp]` base-case value of `compl₂EDSAux`, a
project-internal auxiliary def that isolates the single product `W(m−2)·W(m+1)²` out of
the standard 2-complement difference. The 2-complement *itself* is a genuine,
literature-standard object — and mathlib already has it, in full, as `complEDS₂` (this
project's `section Complement` is an older fork of exactly that, with names
`compl₂EDS`/`compl₂EDS_mul_b`/`compl`/`compl'` corresponding 1:1 to mathlib's
`complEDS₂`/`complEDS₂_mul_b`/`complEDS`/`complEDS'`). What mathlib did **not** lift is
the extra split into `compl₂EDSAux`; the project keeps it only because that single term
reappears verbatim in the `ω` construction (`DivisionPolynomialOmega.lean:78`) and the
reduced-invariant numerator. The lemma under review is one rung below even that: a
trivial evaluation (`= −b`) of a half-term def, proved by a single
`simp [compl₂EDSAux]` that unfolds the def and applies mathlib's existing `preNormEDS`
base values. It carries no independent mathematical content, has zero by-name call
sites, and its statement cannot even be phrased in mathlib (it names a non-mathlib def).
It belongs *with* `compl₂EDSAux` as the def's standard `@[simp]` companion — never as a
standalone mathlib lemma.

The correct disposition is consolidation, not upstreaming: the project's whole
`compl₂EDS*`/`compl*` track should be **re-aimed onto mathlib's now-upstream
`complEDS₂`/`complEDS` family** (a cleanup/dedup task), after which `compl₂EDSAux`
survives only as the small project-local extension feeding the `ω` polynomials, and
`compl₂EDSAux_one` survives as its one-line `@[simp]` value lemma.

**WHY not (refactor-actionable):**
Mathlib has the building blocks — `preNormEDS`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, def L176) with base lemmas
`preNormEDS_one` (L190), `preNormEDS_two` (L194), `preNormEDS_neg`; plus the *full*
complement def `complEDS₂` (L246) and `complEDS₂_one` (L255). The user's form is a
1-call composition off the project's own `compl₂EDSAux` def, not a new lemma.

Mathlib building blocks: `preNormEDS`, `preNormEDS_one`, `preNormEDS_two`,
`preNormEDS_neg`, `complEDS₂`, `complEDS₂_one`
(all in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`).

Composition sketch (≤3 lines), relative to the project def:
```lean
example : compl₂EDSAux b c d 1 = -b := by simp [compl₂EDSAux]
```

Call sites in our project (Phase 6.0): **0** by-name uses of `compl₂EDSAux_one`
(it fires as `@[simp]`); the parent def `compl₂EDSAux` has ≥3 essential uses.

Refactor plan:
1. Do **not** migrate `compl₂EDSAux_one` to mathlib — not expressible there, adds
   nothing over `simp [compl₂EDSAux]`.
2. File a **cleanup/dedup** ticket: re-aim the project's `section Complement`
   (`compl₂EDS`, `compl₂EDS_mul_b`, `compl₂EDS_neg`, `compl₂EDS_zero/one/two`,
   `compl`, `compl'`, `normEDS_mul_compl₂EDS`, `normEDS_dvd_two_mul`, `map_compl₂EDS`,
   L1031–1112 + the `Map` block) onto mathlib's upstream `complEDS₂`/`complEDS` family,
   deleting the duplicated defs and their value/`map`/recursion lemmas in favour of the
   mathlib ones.
3. After the re-aim, **keep** `compl₂EDSAux` (and its `@[simp]` value lemmas
   `compl₂EDSAux_zero/one/neg_one/two/neg_two`, plus `compl₂EDSAux_mul_b`,
   `compl₂EDSAux_neg`, `map_compl₂EDSAux`) as the small project-local extension feeding
   `WeierstrassCurve.ω` — ideally restated against mathlib's `complEDS₂` (note
   `compl₂EDSAux b c d m * b = W(m−2)·W(m+1)²` is the second term of
   `complEDS₂_mul_b`). `compl₂EDSAux_one` stays as-is: a one-line `@[simp]` companion of
   that surviving def.

Next action: do **not** open a mathlib PR for `compl₂EDSAux_one`. Open an AINTLIB
cleanup ticket "dedup NagellLutz `section Complement` against upstream mathlib
`complEDS₂`/`complEDS`", and decide whether `compl₂EDSAux` should be restated in terms
of `complEDS₂`.

---

## Next step

Do not open a mathlib PR for `compl₂EDSAux_one` (it names a non-mathlib def and is a
one-line `simp [compl₂EDSAux]` evaluation). Open an AINTLIB cleanup/dedup ticket to
re-aim the project's `section Complement` onto mathlib's already-upstream
`complEDS₂`/`complEDS` family; retain `compl₂EDSAux` + this `@[simp]` value lemma as the
small project-local extension feeding `WeierstrassCurve.ω`.
