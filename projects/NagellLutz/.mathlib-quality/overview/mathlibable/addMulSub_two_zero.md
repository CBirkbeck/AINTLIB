# /mathlibable report — `EllSequence.addMulSub_two_zero`

### Baseline (Phase 0)
- lake build:               not run (local build stale per task note); reasoning from source.
- decl `EllSequence.addMulSub_two_zero`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:170`
- qualified name:           `EllSequence.addMulSub_two_zero` (VERIFIED — inside `namespace EllSequence`, opened at line 90)
- kind:                     lemma (`theorem`-class; not a `def`)
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences" — defines EDS and constructs
  normalised EDSs; this file is a project FORK of `Mathlib.NumberTheory.EllipticDivisibilitySequence`
  expanded with a four-index-relation apparatus (`addMulSub`/`rel₄`/`net`) absent from mathlib.

---

### Statement (Phase 1)

`EllSequence.addMulSub_two_zero` states that the project-local "building block" operator
`addMulSub W`, evaluated at indices `(2, 0)`, equals `W 1 ^ 2`.

Here `addMulSub` is defined (line 94) as
`addMulSub W m n := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)`,
i.e. `W((m+n)/2) · W((m-n)/2)` using truncating integer division. At `(m,n)=(2,0)` both
truncated quotients are `1`, so the value is `W 1 · W 1 = W 1 ^ 2`. The proof is `(sq _).symm`
— pure definitional unfolding plus the squaring identity `a * a = a ^ 2`.

Variables / typeclasses involved (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(W : ℤ → R)` — the sequence (a section variable; appears implicitly via the namespace).

Hypotheses (Lean side): none.

Conclusion (math): the `(2,0)` building block of the elliptic-relation apparatus is the square
of the first term, `W(1)²`.

Conclusion (Lean): `addMulSub W 2 0 = W 1 ^ 2`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: A helper lemma — a single specialisation of `addMulSub` at concrete indices, used to seed
the four-index relation machinery. Not a named theorem, not a `## Main statement` (the only main
statement is `isEllDivSequence_normEDS`), introduces no new structure.

(Literature width run EXHAUSTIVE regardless, per protocol.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`:= (sq _).symm`).
One-liner verdict: n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. The one-line *definition*
bias does not apply to lemmas. (Recorded for completeness: it is a one-line glue lemma whose body
is a single term `(sq _).symm`, i.e. a controlled definitional unfolding — see Phase 6 inheritance
note. About a project-local `def`, `addMulSub`.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                              | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | EDS "W(1)" ψ₁=1 division polynomial initial value                                              | yes  | `W₁ = 1` / `ψ₁ = 1` is the standard normalisation | Wikipedia + Ward 1948; relates EDS to division polynomials at a point. NO mention of an `addMulSub`-style operator. |
|  2 | WebSearch (the operator)         | elliptic net Stange "addMulSub" `W((m+n)/2)·W((m-n)/2)` building block                          | no   | none — `addMulSub` is not a literature concept   | Stange's formulary writes raw `W(m+n)W(m−n)` products; no packaged binary operator. |
|  3 | WebSearch (four-index relation)  | EDS four-index relation rel₄ / net partition into pairs (Stange)                                | partial | Stange's elliptic-net relation `Σ W(p+q+s)W(p−q)W(r+s)W(r) = 0` | The *net* relation is standard (Stange 0710.1316). The `addMulSub`/`rel₄` *repackaging* is the project's own; `addMulSub_two_zero` is a property of that repackaging, not of the literature relation. |
|  4 | ChatGPT MCP                      | (not issued — see note)                                                                         | n/a  | n/a                                              | Verdict is determined by a structural fact (the subject def `addMulSub` is project-local and absent from mathlib — confirmed by grep over the mathlib package), which no literature query can overturn. A second opinion would not change the bucket. Recorded as a deliberate, justified skip. |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/` ; `refs/NagellLutz/`                         | n/a  | (directories absent)                             | No references dir for NagellLutz — recorded n/a. |
|  6 | nLab                             | elliptic divisibility sequence / elliptic net / division polynomial                            | no   | no `addMulSub` page; recurrence stated with raw `W(...)` | nLab has no packaged building-block operator. |
|  7 | nCatLab (categorical)            | —                                                                                              | n/a  | n/a                                              | Not a categorical concept (an integer-indexed product of two sequence terms). |
|  8 | Stacks Project (alg geom)        | —                                                                                              | n/a  | n/a                                              | Not a Stacks-style scheme-theoretic statement; it is an arithmetic-sequence identity. |
|  9 | MathOverflow / Math.StackExchange| EDS recurrence normalisation W₁                                                                 | yes  | `W₁=1` normalisation discussed; no `addMulSub`    | Same conclusion as #1. |
| 10 | recent arXiv (last 5 years)      | elliptic net valuation / Stange division polynomials 2025                                       | no   | recent papers (2512.09601, 2503.15428) still use raw `W(...)` products | The `addMulSub` packaging is unique to this Lean formalisation. |

### Literature summary (Phase 3)

Concept identified as: a **bespoke formalisation helper** — `addMulSub W m n = W((m+n)/2)·W((m−n)/2)`
is project-internal scaffolding (its own docstring calls it "the basic building block of elliptic
relations"), introduced specifically to make `Int.tdiv`-based negation lemmas hold unconditionally.
`addMulSub_two_zero` is the trivial evaluation at `(2,0)`.
Sources agree on the standard form: yes for the *background* (`W₁=1` normalisation; the EDS/elliptic-net
recurrences are standard, Ward 1948 / Stange 2008) — but **no source packages a binary `addMulSub`
operator**, so there is no literature-standard form *of this lemma* to compare against.
Most general standard form: n/a — the lemma is a definitional identity about a non-standard operator.
Generality dimensions where the literature varies: n/a.
Disagreement with the literature: none — the literature simply has no analog at this granularity.

---

### Generality analysis — `EllSequence.addMulSub_two_zero`

Literature-standard form (from Phase 3): none exists (operator is project-local).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | n/a (no literature form) | not meaningfully    | `sq`/`(· * ·)` are already at the natural `Monoid`/`CommRing` level the file fixes; weakening the ambient ring would not make this particular lemma more useful since `addMulSub` itself is defined over `CommRing R` throughout the file. |
| 2 | indices `(2, 0)`       | concrete integers | n/a                      | no                  | The lemma's entire content is the concrete evaluation; it cannot be "generalised" without becoming `addMulSub_even`/`addMulSub_odd` (which already exist, lines 173/176). |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL (vacuously — there is nothing to weaken; it is a concrete
evaluation of a project-local operator).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|------------|
| 1 | Bundled hypotheses → typeclasses? | no | — | no bundled "let X be a foo" preamble; it is a closed identity. |
| 2 | Sequences/metric → filters/topology? | no | — | finite algebraic identity; no limiting notion. |
| 3 | Construction → universal-property class? | no | — | nothing is constructed. |
| 4 | Set+closure-predicate → bundled substructure? | no | — | n/a. |
| 5 | Vector-space/field-specific → weaken typeclasses? | no | — | already `CommRing`. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | Concrete index → general additive structure? | no | — | the concrete indices `(2,0)` *are* the content. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no.
Reason: this is a one-line definitional evaluation of a bespoke operator; there is no organisational
restatement that composes with more of mathlib — mathlib has neither the operator nor anything to
compose it with.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (not `def`/`class`/`instance`); introduces no definitional
equalities or typeclass-search paths.

---

### Mathlib search-status: `EllSequence.addMulSub_two_zero`

[A] Lean-Finder       (index tool not exposed in this thread)     n/a — substituted by authoritative source grep over `.lake/packages/mathlib/`
[B] Loogle            (index tool not exposed in this thread)     n/a — same
[C] LeanSearch        (index tool not exposed in this thread)     n/a — same
[D] Grep mathlib src  `addMulSub`, `rel₄`, `net `, `_two_zero`, `namespace EllSequence`  → see below
[E] Name pattern      `addMulSub_two_zero` across repo            → 2 hits, both in the NagellLutz fork (line 170 + a backup copy `EllipticDivisibilitySequenceOriginal.lean:162`); ZERO in mathlib.

Authoritative grep results over `.lake/packages/mathlib/Mathlib/`:
- `addMulSub`: **0 genuine hits** (the 3 filename matches — GroupCompletion / NetEntropy / Bases —
  are substring false positives on `net`/`addMul`; none defines `EllSequence.addMulSub`).
- `namespace EllSequence`: **0 hits** — the entire namespace is project-local.
- `rel₄` / four-index `net` apparatus: **0 hits** — mathlib's EDS file
  (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`) contains only
  `IsEllSequence`/`IsDivSequence`/`preNormEDS`/`normEDS`/`complEDS` — NO `addMulSub`, NO `rel₄`,
  NO `net`, NO `_two_zero` building-block lemma.
- `_two_zero`: hits are unrelated (`dickson_two_zero`, `taylorWithinEval_charFun_two_zero`).

Searched for both:
  - the user's current form (`addMulSub W 2 0 = W 1 ^ 2`) — not present;
  - the literature-standard form — none exists (Phase 3).

Concluded: **not in mathlib.** The subject definition `addMulSub` does not exist in mathlib, so no
lemma about it (general or specific) can be present. This is structurally decisive, not merely
"didn't find it".

---

### Call sites — `EllSequence.addMulSub_two_zero`

Internal use count: **0** (within the live project file, excluding the declaring line).
External-to-file callers: 0 distinct files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | — |

The only other occurrence repo-wide is `EllipticDivisibilitySequenceOriginal.lean:162` — a verbatim
backup copy of the same forked file, i.e. a duplicate *declaration*, not a *use*.

Inline-derivation grep: (none — the `W 1 ^ 2` identity is not re-derived elsewhere; the lemma simply
appears unused so far, consistent with being a building block staged for the relation apparatus).

Call-sites signal: K = 0 internal uses, no inline re-derivation → "brand-new / staged building block,
currently unused". Combined with its one-line glue body and project-local subject, this leans NO.

---

### Composition check (Phase 6)

Can `EllSequence.addMulSub_two_zero` be derived in ≤3 chained calls?

Attempt 1: `(sq (W 1)).symm` after unfolding `addMulSub W 2 0` to `W 1 * W 1`.
  - Mathlib decls used: `sq` (and its definitional unfolding `Int.tdiv` of `(2±0)/2 = 1`).
  - Result: succeeds — this is literally the existing proof `(sq _).symm`, modulo the `addMulSub`
    unfolding which is *definitional* (the operator is project-local but `rfl`-reduces at concrete
    indices).
  - Notes: the "composition" is one `sq` call on top of a project-local definitional reduction. It is
    NOT a mathlib composition in the meaningful sense, because the operator being unfolded is not a
    mathlib primitive.

Conclusion: COMPOSABLE (trivially, by `(sq _).symm`) — but the composition lives *inside the project*,
not *out of mathlib primitives*. There is nothing for mathlib to "have" here.

---

## Verdict: `EllSequence.addMulSub_two_zero`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): no literature concept named `addMulSub`; the lemma is bespoke
  formalisation scaffolding. The only standard fact nearby (`W₁=1` normalisation) is unrelated.
- Generality analysis (Phase 4): MAXIMALLY GENERAL vacuously; no weakening, no modern idiom.
- Mathlib search (Phase 5): NOT in mathlib — and structurally cannot be, since `EllSequence.addMulSub`
  / the `rel₄`/`net` apparatus do not exist in mathlib (grep: 0 genuine hits; `namespace EllSequence`
  absent).
- Composition check (Phase 6): COMPOSABLE — the proof is `(sq _).symm` (one `sq` over a definitional
  unfold). Call sites: 0 internal uses.

**Rationale:**

This is a one-line glue lemma (`:= (sq _).symm`) recording that a project-internal building-block
operator `addMulSub W`, at the concrete indices `(2, 0)`, equals `W 1 ^ 2`. The operator `addMulSub`
is bespoke scaffolding introduced *only* in this forked file — its own docstring calls it "the basic
building block of elliptic relations", and it is deliberately defined with `Int.tdiv` so that the
companion negation lemmas (`addMulSub_neg₀`, etc.) hold unconditionally. No source in the
EDS/elliptic-net literature (Ward 1948; Stange 2008 and the 2025 isogeny papers; nLab) packages such
a binary operator — they write the raw `W(m+n)·W(m−n)` products directly. Consequently there is no
"literature-standard form of this lemma" and, decisively, **mathlib contains neither `addMulSub` nor
the four-index `rel₄`/`net` apparatus** (the mathlib EDS file stops at `normEDS`/`complEDS`; the
`namespace EllSequence` does not exist in mathlib at all). A lemma whose very subject is absent from
mathlib cannot be `NO-mathlib-has-it`, and is not a generic mathematical statement worth `YES`.

It lands in `NO-composable-from-mathlib` in the precise sense the bucket is meant for a project: the
content reduces to a single mathlib primitive (`sq`) applied to a definitional unfolding of a local
def, so it need not exist as a standalone *mathlib* lemma — and within the project it can simply stay
as the trivial helper it is (or be inlined). It carries 0 call sites today, reinforcing that it is a
staged convenience, not load-bearing API. There is nothing here for mathlib to absorb.

WHY not (refactor-actionable):
  - Mathlib's building block is `sq` (`a ^ 2 = a * a`), at
    `Mathlib/Algebra/GroupPower/Basic.lean` (def `sq`, `sq a = a * a`). Everything else in the lemma
    is the *definitional* reduction of the project-local `addMulSub W 2 0` to `W 1 * W 1` — which is
    `rfl` because `(2+0).tdiv 2 = 1` and `(2−0).tdiv 2 = 1`. No mathlib lemma about `addMulSub` is
    needed or possible (mathlib has no such operator).
  Mathlib building blocks:      `sq` (`Mathlib/Algebra/GroupPower/Basic.lean`)
  Composition sketch (≤3 lines):
  ```lean
  -- with `W : ℤ → R`, `[CommRing R]`:
  example : EllSequence.addMulSub W 2 0 = W 1 ^ 2 := (sq (W 1)).symm
  ```
  Call sites in our project (from Phase 6.0):  K = 0.
  Refactor plan: NOTHING to refactor for mathlib's sake — this lemma is correctly project-local. If a
  cleaner ever wants to trim it, the single-term proof `(sq _).symm` can be inlined at the (currently
  nonexistent) call sites; but with K = 0 it is most natural to simply leave it as the trivial
  building-block helper next to `addMulSub_three_one`/`addMulSub_even`/`addMulSub_odd`. It must NOT be
  proposed to mathlib: its subject `addMulSub` is not a mathlib concept.
  Next action: keep `EllSequence.addMulSub_two_zero` in the project as a local helper; do not upstream.

---

## Next step

Keep `EllSequence.addMulSub_two_zero` in the project as the trivial local building-block helper it is
(it is `(sq _).symm` over a project-local operator). Do **not** upstream to mathlib — mathlib has
neither the `addMulSub` operator nor the surrounding `rel₄`/`net` apparatus, so there is no home and
no general statement to contribute. No refactor required.
