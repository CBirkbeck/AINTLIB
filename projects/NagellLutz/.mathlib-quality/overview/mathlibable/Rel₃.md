# Mathlibable assessment: `EllSequence.Rel₃`

**Verdict: NO-composable-from-mathlib**

- **Qualified name:** `EllSequence.Rel₃`
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:130`
- **Date:** 2026-06-18
- **One-line summary:** a `Prop`-valued `def` that names the *body* of mathlib's existing
  `IsEllSequence` predicate at a single index triple `(m, n, r)`; it is a quantifier-stripping
  refactor handle, recoverable from `Mathlib.IsEllSequence` by a zero-step definitional unfold
  (`IsEllSequence W ↔ ∀ m n r, Rel₃ W m n r` is `Iff.rfl`). Not standalone mathlib material.

## Baseline (Phase 0)

- lake build:               not re-run (local build stale per task brief); decl reasoned from source
- decl `EllSequence.Rel₃`:  ✓ resolved at `EllipticDivisibilitySequence.lean:130`, inside
                            `namespace EllSequence` (opened line 90)
- kind:                     `def` (returns `Prop`)
- has sorry:                no
- module docstring summary: defines elliptic divisibility sequences and constructs normalised EDSs
                            from initial terms (a fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`).

## Statement (Phase 1) — verified from source

```lean
namespace EllSequence
variable {R : Type u} [CommRing R] (W : ℤ → R)

/-- The three-index elliptic relation, obtained by
specializing to `d = 0` in the four-index relation. -/
def Rel₃ (m n r : ℤ) : Prop :=
  W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2
```

The parsed qualified name in the prompt (`EllSequence.Rel₃`) is **correct**.

In prose: for a sequence `W : ℤ → R` over a commutative ring `R`, and a fixed triple of integers
`(m, n, r)`, `Rel₃ W m n r` is the proposition that Ward's **three-index elliptic relation** holds
*at that triple*:

  `W(m+n)·W(m−n)·W(r)² = W(m+r)·W(m−r)·W(n)² − W(n+r)·W(n−r)·W(m)²`.

The accompanying `def _root_.IsEllSequence := ∀ m n r : ℤ, Rel₃ W m n r` (line 135) closes the
quantifier, giving "W is an elliptic sequence."

- Parameters (Lean): `R` a `CommRing`; `W : ℤ → R` the sequence (fixed in the namespace `variable`);
  `(m n r : ℤ)` the index triple.
- Hypotheses: none.
- Conclusion (math): the three-index identity holds at `(m, n, r)`.
- Conclusion (Lean): `Prop` (it is a definition of a proposition, not a proof).

## Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: not a new mathematical structure (it is the pointwise instance of an already-formalised
condition), not a named theorem, not a `## Main results` entry. It is a one-line helper predicate.

## One-line check (Phase 2b)

Body line count: **1 substantive line** (a single equation).
One-liner verdict: **ONE-LINER** (kind is `def`).

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                | no       | The def is *not* sealed against unfolding — quite the opposite. Every one of its ~10 call sites immediately does `rw [Rel₃]` / `simp only [Rel₃]` (lines 309, 364, 369, 610, 625, 655, 662) to expand it straight back to the raw equation. It is used *as* an unfolding handle, not as a defeq barrier. |
| Avoid typeclass diamonds         | no       | `Rel₃ : Prop` carries no instances and sits on a fixed `R`/`ℤ`; there is no instance-search path to disambiguate. |
| Mark semantic intent / API name  | partial→no | It does carry a docstring and a readable name, and it is reused inside this file. But mathlib itself already provides the semantic anchor at the *quantified* level (`IsEllSequence`) and deliberately **inlines** the per-index body rather than naming it. The stable-API surface other developments depend on is `IsEllSequence`, not `Rel₃`. No external consumer needs the per-index name. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** → biases the verdict toward a NO bucket (carried into
Phase 7).

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence defining recurrence W(m+n)W(m-n) Ward three index relation"            | yes  | `W(m+n)W(m−n)W(r)² = W(m+r)W(m−r)W(n)² − W(n+r)W(n−r)W(m)²` for **all** m,n,r | Mathlib docs, Wikipedia, arXiv 2102.07573, 0710.1316 all give this exact identity as the *defining* property |
|  2 | WebSearch (general / equivalent) | "Ward elliptic sequence W_{m+n}W_{m-n}W_r^2 = …"                                                        | yes  | same identity; Ward's antisymmetric form `W_{h-m}W_{h+m}W_n² + W_{n-h}W_{n+h}W_m² + W_{m-n}W_{m+n}W_h² = 0` | Wikipedia "Elliptic divisibility sequence"; equivalent under `W_{-h} = -W_h` |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2) "Morgan Ward elliptic sequence definition"                                            | yes  | attributed to Morgan Ward (1940s); "three-index relation" / "defining recursion" | name of the *condition* is "elliptic sequence"; no name for the per-triple predicate |
|  4 | ChatGPT MCP                      | (MCP down per task brief — fallback to web + sibling report `addMulSub.md`, same author/paper)          | n/a  | — | ChatGPT MCP unavailable; covered by WebSearch ×3 + the project's own companion paper, see #5 |
|  5 | Local references                 | `ls projects/NagellLutz/.mathlib-quality/references/`                                                   | n/a  | (no references dir) | dir absent. Companion math paper for this development is Angdinata–Xu, *On Elliptic Sequences over Commutative Rings* (arXiv:2604.05280), per sibling report `addMulSub.md` |
|  6 | nLab                             | "elliptic divisibility sequence"                                                                        | n/a  | — | nLab has no dedicated EDS page; not a category-theoretic notion |
|  7 | nCatLab                          | —                                                                                                      | n/a  | — | not a categorical concept |
|  8 | Stacks Project                   | —                                                                                                      | n/a  | — | not an algebraic-geometry / scheme-theoretic concept (it is a sequence identity) |
|  9 | MathOverflow / MSE               | "three index relation elliptic divisibility sequence"                                                   | yes  | matches #1; always stated with universal quantifier | recurrence is standard folklore; no per-index named predicate |
| 10 | recent arXiv (≤5 yr)             | "recurrence relation for elliptic divisibility sequences"                                               | yes  | arXiv 2102.07573 (2021); 2307.05866 (Somos-4); 1702.08102 | confirm the identity is *the* definition; none introduce a per-triple predicate name |

### Literature summary (Phase 3)

Concept identified as: **Ward's three-index elliptic (divisibility) sequence relation** — the
*defining property* of an elliptic sequence.
Sources agree on the standard form: **yes** (Wikipedia, mathlib docstring, arXiv 2102.07573 /
0710.1316 / math/0402415, MathOverflow all identical, up to the antisymmetric rearrangement).
Most general standard form: a sequence `W : ℤ → R` over a commutative ring is an *elliptic sequence*
iff the identity holds **for all** `m, n, r ∈ ℤ`.
Generality dimensions where the literature varies:
  - coefficient domain: classically `ℤ`, but the modern (mathlib / Angdinata) form is **any
    `CommRing R`** — which the project already uses. Maximal.
  - quantification: the literature object is the **universally-quantified** condition. The per-triple
    predicate `Rel₃` is *not* a literature object; it is a Lean-side decomposition of that condition.
Disagreement with the literature: **the literature never isolates a single-triple predicate.** The
standard object is the `∀ m n r` condition — exactly mathlib's `IsEllSequence`. `Rel₃` exists only to
let the Lean proof reason one triple at a time.

## Generality analysis (Phase 4)

Literature-standard form (from Phase 3): the `∀ m n r : ℤ` elliptic-sequence condition over any
`CommRing R` — i.e. mathlib's `IsEllSequence`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring (classically `ℤ`) | NO | already maximal; the identity uses `+`, `−`, `*`, `^2`, all available in any `CommRing`. Cannot drop to `CommSemiring` (the RHS has a subtraction). |
| 2 | `W : ℤ → R`            | `ℤ`-indexed       | `ℤ`-indexed              | NO | the relation's index arithmetic (`m+n`, `m−n`) needs `ℤ`'s additive-group structure; this is the literature index set. |
| 3 | `(m n r : ℤ)` free     | per-triple predicate | universally quantified condition | n/a (this *is* the narrowing) | `Rel₃` is the **specialisation-to-a-point** of the standard quantified object; it is narrower *by design*, not by oversight. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** on its typeclass/index axes (`CommRing R`, `ℤ` index —
both already match the most general literature form and mathlib's own `IsEllSequence`).

But on the *quantification* axis it is the deliberate **pointwise** form of an object that the
literature (and mathlib) state quantified. There is no standalone "more general `Rel₃`" to aim at —
the more general object simply *is* `IsEllSequence` (`= ∀ m n r, Rel₃`). So this is not a
"generalise the typeclasses" situation; it is a "this is a pointwise fragment of an existing
quantified decl" situation, which Phase 6 handles.

Number of typeclass/index weakening opportunities found: **0**.
Cost of restatement: n/a (no weakening to perform).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Notes |
|----|----------|----------|-------|
| 1 | bundled-hypotheses → typeclasses? | no | already a plain `Prop`; the only "structure" (elliptic-sequence-ness) is the *quantified* version, already a `def` in mathlib. |
| 2 | sequences/metric → filters/topology? | no | this is a finite algebraic identity in a ring; no limiting process to filter-ise. |
| 3 | construction → universal-property class? | no | it is a relation, not a construction of an object. |
| 4 | set+closure-predicate → bundled substructure? | no | not a substructure. |
| 5 | vector-space/field-specific → weaken typeclass? | no | already at `CommRing`; nothing field-specific. |
| 6 | 1-categorical → higher-categorical? | no | not categorical. |
| 7 | concrete index ℕ/ℤ/ℝ → general additive structure? | no | `ℤ` is the literature-canonical index for EDS; generalising the index away from `ℤ` would *leave* the standard concept. |

Modern idiom available: **no**. One-line reason: the contemporary mathlib idiom for this exact
concept already exists and is the *quantified* `IsEllSequence`; the per-triple `Rel₃` is a proof-time
fragment of it, not a candidate for a different/better mathlib formulation.

## Diamond / defeq risk (Phase 4.5) — kind is `def`, so this runs

| # | Risk | Verdict | Rationale |
|---|------|---------|-----------|
| 1 | Typeclass diamond | none | `Rel₃ : Prop` declares no instance and triggers no instance search; nothing to collide. |
| 2 | Reducibility leak | none | not `@[reducible]`; even if it were, the body is a single ring equation (no heavy computation) and every consumer unfolds it deliberately. |
| 3 | Non-canonical unfolding | none | it unfolds (via `rw`/`simp only [Rel₃]`) to exactly the equation the user wrote; no surprise. This is in fact its intended use. |
| 4 | Instance priority collision | n/a | not an `instance`. |
| 5 | Universe-polymorphism issues | none | lives entirely in the fixed `R : Type u` / `ℤ`; no forced universe annotation. |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**. (Not that it matters for the chosen bucket — NO-composable does not add the
def to mathlib at all.)

## Mathlib search-status (Phase 5)

[A] Lean-Finder       n/a (index unavailable locally; reasoned from mathlib source)
[B] Loogle            type pattern `(ℤ → ?R) → ℤ → ℤ → ℤ → Prop` — no *named* per-triple decl; the
                      only `Prop`-valued elliptic-sequence decl is the quantified `IsEllSequence`
[C] LeanSearch        "elliptic sequence three index relation" → returns `IsEllSequence`
                      (`Mathlib.NumberTheory.EllipticDivisibilitySequence`)
[D] Grep mathlib src  `grep -rn "Rel₃\|Rel3\|rel₃\|three_index\|threeIndex" .lake/.../Mathlib/`
                      → **0 hits**. Mathlib has no `Rel₃`. It inlines the body directly into
                      `def IsEllSequence` (`EllipticDivisibilitySequence.lean:82`).
[E] Name pattern      grep for `IsEllSequence` → found at mathlib `…:82`; its body is **verbatim**
                      the body of `Rel₃` under `∀ m n r`.

Searched for both:
  - the user's current form (per-triple `Rel₃`) → **not in mathlib** (mathlib never names it).
  - the literature-standard form (`∀ m n r` condition) → **in mathlib as
    `IsEllSequence`** (`Mathlib.NumberTheory.EllipticDivisibilitySequence`, line 82), defined
    identically to `∀ m n r, Rel₃ W m n r`.

Concluded: **found the building block** — mathlib's `IsEllSequence` *is* `∀ m n r, Rel₃ W m n r`
(confirmed: the HasseWeil fork proves `isEllSequence_iff_rel₃ : IsEllSequence W ↔ ∀ m n r, Rel₃ W m n r`
by **`Iff.rfl`**). `Rel₃ W m n r` is recovered from `IsEllSequence` by specialising the universal to
the triple `(m, n, r)` — a zero-step definitional unfold.

## Composition check (Phase 6)

### Call sites — `EllSequence.Rel₃`

Internal use count (this file, excluding the declaring line): **K ≈ 10** —
`EllipticDivisibilitySequence.lean` lines 136 (`IsEllSequence := ∀ m n r, Rel₃`), 308–309, 363–364,
368–369, 610, 624–625, 655, 662.
External-to-file callers (NagellLutz project): the quantified wrapper `IsEllSequence` is used in
`ZSMul.lean`, `DivisionPolynomialOmega.lean` — but those consume **`IsEllSequence`**, not `Rel₃`
directly.

| Caller (line) | Usage pattern |
|---------------|---------------|
| `:136` | `def IsEllSequence := ∀ m n r : ℤ, Rel₃ W m n r` (the wrapper) |
| `:308–309` | `Rel₃ W m n r ↔ rel₄ … = 0` then `rw [rel₄, …, Rel₃]` (unfold) |
| `:363–364`, `:368–369` | `rel₃_iff_oddRec` / `rel₃_iff_evenRec`: `rw [Rel₃, OddRec]; ring` (unfold) |
| `:610` | `fun _ _ _ ↦ by simp only [Rel₃, id_eq]; ring1` (unfold) |
| `:624–625`, `:655`, `:662` | `simp only [Rel₃, …]` / `rw [Rel₃, …]` (unfold) |

Inline-derivation grep: the **same `Rel₃` def is independently re-declared verbatim** in two sibling
forks — `HasseWeil/.../EllipticDivisibilitySequence.lean:75` and
`NagellLutz/.../EllipticDivisibilitySequenceOriginal.lean:129` — plus mathlib *inlines* the identical
body into `IsEllSequence`. So the concept is re-derived in ≥3 places; none is a downstream consumer of
*this* declaration (they are parallel copies / inlinings).

Call-sites reading: every internal use either (a) is the wrapper that closes the quantifier, or
(b) immediately unfolds `Rel₃` back to the raw equation. No consumer relies on `Rel₃` as an opaque
API. This is the "K≥1 but every use unfolds it / it is re-derived elsewhere" pattern → lean **NO**.

### Composition attempt

Can `Rel₃ W m n r` be obtained from mathlib in ≤3 chained calls?

Attempt 1: `Rel₃ W m n r` is *definitionally* the body of `Mathlib.IsEllSequence W` at the triple
`(m, n, r)`. Concretely:
```lean
-- the predicate itself is just the unfolded IsEllSequence body:
example (W : ℤ → R) (m n r : ℤ) :
    Rel₃ W m n r ↔
      W (m+n) * W (m-n) * W r ^ 2 = W (m+r) * W (m-r) * W n ^ 2 - W (n+r) * W (n-r) * W m ^ 2 :=
  Iff.rfl
-- and to *use* it from a hypothesis `h : IsEllSequence W`, you just apply:
example (h : IsEllSequence W) (m n r : ℤ) : <the equation at (m,n,r)> := h m n r
```
  - Mathlib decls used: `Mathlib.IsEllSequence` (applied to `m n r`); `Iff.rfl`.
  - Result: **succeeds** (0–1 trivial calls; the predicate *is* the unfolded mathlib def).
  - Notes: there is genuinely nothing to prove — `IsEllSequence W` already means
    `∀ m n r, (that equation)`, so `h m n r` *is* `Rel₃ W m n r`.

Conclusion: **COMPOSABLE** (trivially — it is a definitional projection of one existing mathlib
declaration, not even a real composition).

## Verdict: `EllSequence.Rel₃`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the standard object is the **universally-quantified** Ward three-index
  relation; the literature has no per-triple predicate. Mathlib encodes the standard object as
  `IsEllSequence`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL on typeclass/index axes; the "more general" form
  is simply the quantified `IsEllSequence`. No modern-idiom move (4c = no).
- Mathlib search (Phase 5): no `Rel₃` in mathlib (0 grep hits); the body lives verbatim inside
  `Mathlib.IsEllSequence` (`EllipticDivisibilitySequence.lean:82`).
- Composition check (Phase 6): COMPOSABLE — `Rel₃ W m n r` is the definitional unfold of
  `IsEllSequence W` at `(m, n, r)` (`IsEllSequence W ↔ ∀ m n r, Rel₃ W m n r` is `Iff.rfl`).

**Rationale.**
`Rel₃` adds no mathematical content beyond what mathlib already ships. Mathlib's `IsEllSequence`
*is* `∀ m n r : ℤ, (the three-index identity)`, and `Rel₃ W m n r` is exactly that identity at a
single triple — i.e. the quantifier-stripped body. Mathlib made the deliberate design choice to
**inline** this body into `IsEllSequence` rather than name it; the project's `Rel₃` is a local
refactor that re-exposes the body so the elliptic-sequence proofs can reason one index triple at a
time. That this is a pure definitional split is confirmed by the fork's own
`isEllSequence_iff_rel₃ … := Iff.rfl`. Every call site is either the wrapper `∀ m n r, Rel₃` (which
*is* `IsEllSequence`) or an immediate `rw [Rel₃]` / `simp only [Rel₃]` that unfolds it back — so no
consumer treats `Rel₃` as opaque API, and the identical def is independently duplicated across three
places (NagellLutz, NagellLutz-Original, HasseWeil) plus mathlib's inlining. A stand-alone mathlib
`Rel₃` would be a redundant name for the inside of an existing definition.

This lands in NO-composable-from-mathlib rather than NO-mathlib-has-it because mathlib has **no
declaration named `Rel₃` to delete-and-replace against** — it has the *quantified* `IsEllSequence`,
from which the per-triple form is recovered by unfolding/applying, not by citing an existing
identical lemma. The one-liner (Phase 2b) has **no defeq/diamond/API exemption**, reinforcing NO.

**WHY not (refactor-actionable):**
Mathlib's building block is the single decl `Mathlib.IsEllSequence`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:82`), whose body is *verbatim* the body of
`Rel₃` under `∀ m n r`. To obtain the per-triple statement you specialise/unfold it:

```lean
-- from `h : IsEllSequence W`, the triple-(m,n,r) identity is just:
example (h : IsEllSequence W) (m n r : ℤ) :
    W (m+n) * W (m-n) * W r ^ 2 = W (m+r) * W (m-r) * W n ^ 2 - W (n+r) * W (n-r) * W m ^ 2 :=
  h m n r
-- and `Rel₃ W m n r` is defeq to that RHS proposition (Iff.rfl).
```

Mathlib building blocks: `Mathlib.IsEllSequence` (one decl).
Composition sketch (≤3 lines): see above — `h m n r` (0 non-trivial calls; the rest is definitional).

Call sites in this project (Phase 6.0): K ≈ 10 in-file (all either the `IsEllSequence` wrapper or an
immediate unfold), 0 external consumers of `Rel₃` itself.

**Refactor plan — caveat (do NOT mechanically delete in isolation).** `Rel₃` is the bottom atom of a
larger *elliptic-relation algebra* in this file (`rel₄`, `net`, `addMulSub`, `invar…`, etc.) that the
project uses to prove the standing mathlib TODO "`normEDS` satisfies `IsEllDivSequence`" (mathlib's
own `## Main statements` lists this as `TODO`). That layer is the genuinely mathlib-bound contribution
(see the sibling `addMulSub.md` verdict). The correct disposition of `Rel₃` is therefore **tied to
that upstreaming**, two cases:
  1. **If/when the layer is upstreamed:** follow mathlib's existing choice — keep `IsEllSequence` as
     the public quantified def and **inline** the per-triple body at proof sites (as mathlib already
     does), so `Rel₃` does **not** become public mathlib API. If the proofs are cleaner with a named
     handle, it may survive only as a `private`/`local` unfolding abbreviation in the same file — never
     as an exported declaration.
  2. **Within the project, independently:** the three duplicated copies (NagellLutz,
     NagellLutz-Original, HasseWeil) should be de-duplicated into one shared `Common/` decl (a
     cross-project cleanup ticket), and `IsEllSequence` should be defined directly as `∀ m n r, Rel₃`
     or aliased to `Mathlib.IsEllSequence` (they are `Iff.rfl`-equal) to avoid forking mathlib's
     predicate at all.

Next action: do **not** ship `Rel₃` as a standalone mathlib PR. Treat it as a proof-time helper of
the elliptic-relation layer; resolve its fate when that layer is upstreamed (inline per mathlib's
convention, or keep `private`). Separately, file an AINTLIB cleanup ticket to de-duplicate the three
identical `Rel₃`/`IsEllSequence` forks and reconcile them with `Mathlib.IsEllSequence`.

---

## Next step

Do not open a mathlib PR for `Rel₃`. It is the definitional body of `Mathlib.IsEllSequence` at one
index triple, recovered by `h m n r` / `Iff.rfl`. Keep it as an in-file proof helper of the
elliptic-relation layer (to be inlined, per mathlib's convention, or kept `private`, if/when that
layer is upstreamed), and file a cleanup ticket to de-duplicate the three identical forks against
`Mathlib.IsEllSequence`.
