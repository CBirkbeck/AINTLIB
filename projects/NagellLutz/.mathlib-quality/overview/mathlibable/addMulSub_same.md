# /mathlibable report — `EllSequence.addMulSub_same`

## Verdict: **BORDERLINE-needs-human**

One-line rationale: trivial helper (`addMulSub W m m = W m · W 0 = 0`) about the
project-local `addMulSub` building block, which is itself absent from mathlib; its
fate rides on whether the whole `EllSequence` elliptic-nets layer is upstreamed — a
maintainer scope/taste call.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoning from source — `.lake/build/lib` empty)
- decl `EllSequence.addMulSub_same`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:181`
- qualified name:           `EllSequence.addMulSub_same` (namespace `EllSequence` opens line 90, first `end` at line 597; line 181 is inside it) — VERIFIED, matches the prompt's guess
- kind:                     `lemma`
- has sorry:                no
- module docstring summary: defines elliptic divisibility sequences (EDS) and constructs normalised EDSs from initial terms; this file is a project **extension** of mathlib's EDS file adding Stange-style elliptic-net machinery (`addMulSub`, `rel₄`, `net`, transformation lemmas)

---

### Statement (Phase 1)

`EllSequence.addMulSub_same` states: for a commutative ring `R`, a sequence
`W : ℤ → R` with `W 0 = 0`, and any integer `m`, the building block `addMulSub W m m`
equals `0`.

Here `addMulSub W m n := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)` (line 94). So
`addMulSub W m m = W ((2m).tdiv 2) * W (0.tdiv 2) = W m * W 0`, which is `0` once
`W 0 = 0`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring (arbitrary commutative ring)
- `(W : ℤ → R)` — the integer-indexed sequence
- `(m : ℤ)` — the index

Hypotheses (Lean side):
- `(zero : W 0 = 0)` — the sequence vanishes at 0 (a defining property of any
  elliptic net / EDS; Stange, Ward)

Conclusion (math): the symmetric building block `W((m+m)/2)·W((m−m)/2)` is `0`.
Conclusion (Lean): `addMulSub W m m = 0`.

Proof body (1 line):
`rw [addMulSub, sub_self, Int.zero_tdiv, zero, mul_zero]`
— unfold the def, `m − m = 0`, `0.tdiv 2 = 0`, apply the `W 0 = 0` hypothesis,
then `_ * 0 = 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line vanishing lemma about a project-defined building block; not a
named theorem, not a `## Main statement`, not a new structure. (It is *adjacent* to
a BIG concept — the `addMulSub`/`rel₄`/`net` elliptic-net layer — but the lemma
itself is a helper.)

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line.
One-liner verdict: n/a for the exemption table — kind is `lemma`, not `def`. The
def-oriented defeq/diamond/API-name exemptions do not apply to a propositional
lemma. Recorded: this is a **trivial one-line lemma**, a strong negative signal for
standalone inclusion; its value is purely as local API sugar over `addMulSub` +
`mul_zero`.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                   | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | `elliptic net "addMulSub" OR "W((m+n)/2)" building block ... Stange`                      | no (for the term) | — | Stange formulary / elliptic-nets papers surfaced, but `addMulSub` / `W((m±n)/2)` is **not** standard notation; it is the formalization's own building block |
|  2 | WebSearch (general fact)         | `elliptic divisibility sequence W(0)=0 vanishes at zero defining property Ward`           | yes  | `W(0) = 0` is a defining axiom of an elliptic net / EDS (Ward 1948; Stange) | confirms the *hypothesis* is the standard EDS axiom — but the lemma `addMulSub_same` is the Lean consequence `W(m)·W(0)=0`, not a named result |
|  3 | WebSearch (named-after/aliases)  | (covered by #1/#2: "elliptic net", "Ward", "Stange formulary")                            | partial | EDS / elliptic-net axioms | the vanishing-at-0 axiom is standard; no source names a "addMulSub same-index" lemma |
|  4 | ChatGPT MCP                      | n/a — MCP flagged down in this environment (task note); compensated with extra WebSearch + direct mathlib-source grep | n/a | — | recorded as unavailable, not skipped silently |
|  5 | Local references                 | `.mathlib-quality/references/` for NagellLutz                                             | n/a  | — | directory ABSENT (confirmed) — channel n/a |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                         | n/a  | — | not a category-theoretic concept; nLab has no EDS/elliptic-net entry of relevance to a `W(0)=0` helper |
|  7 | nCatLab (categorical)            | —                                                                                        | n/a  | — | not a categorical concept |
|  8 | Stacks Project (alg geom)        | "elliptic divisibility sequence"                                                          | n/a  | — | Stacks has no EDS / division-polynomial-sequence section; not covered |
|  9 | MathOverflow / MSE               | EDS `W_0 = 0` / division-polynomial vanishing                                             | yes  | `ψ_0 = 0`, `W_0 = 0` standard | confirms the axiom is folklore-standard; nothing on this exact Lean building-block lemma |
| 10 | recent arXiv (≤5 yr)             | elliptic nets valuation (2512.09601 etc. surfaced in #1)                                  | partial | elliptic-net axioms incl. `W(0)=0` | modern usage agrees `W(0)=0`; no `addMulSub` notation anywhere |

### Literature summary (Phase 3)

Concept identified as: the symmetric two-term building block `W((m+n)/2)·W((m−n)/2)`
of the elliptic-net relations (David Angdinata's `addMulSub`), evaluated at the
diagonal `n = m`. The mathematical content reduces to the standard EDS/elliptic-net
axiom **`W(0) = 0`** (Ward 1948; Stange's formulary and elliptic-nets papers).
Sources agree on the standard form: yes — `W(0)=0` is a defining axiom; the
"diagonal building block vanishes" statement is an immediate consequence, not an
independently named result.
Most general standard form: in any integral domain / commutative ring, an
elliptic net satisfies `W(0)=0`, hence any product carrying a `W(0)` factor is `0`.
Generality dimensions where the literature varies: coefficient ring (`ℤ` →
integral domain → arbitrary comm ring); the lemma already sits at the most general
(arbitrary `CommRing`, no domain needed).
Disagreement with the literature: none — but note the literature has **no
`addMulSub` notion at all**; it is a formalization-internal device (the docstring
at line 95–98 explicitly says `Int.tdiv` is used so neg/abs lemmas hold
*unconditionally*, an implementation choice).

---

### Generality analysis — `EllSequence.addMulSub_same`

Literature-standard form: an elliptic net over any integral domain has `W(0)=0`;
products with a `W(0)` factor vanish.

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form exists? | Reason |
|---|------------------------|-------------------|---------------------|---------------------|--------|
| 1 | `[CommRing R]`        | arbitrary comm ring | integral domain (lit) | NO (already weaker/more general) | proof uses only `mul_zero`; no domain/cancellation needed — current form is *more* general than literature |
| 2 | `(W : ℤ → R)`        | arbitrary function | EDS/elliptic net | NO | no EDS structure used; only `W 0 = 0` |
| 3 | `(zero : W 0 = 0)`   | single hypothesis | the EDS axiom | NO | minimal — exactly the axiom needed |
| 4 | `(m : ℤ)`            | integer index | integer index | NO | matches |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (in fact more general than the
literature, which usually fixes an integral domain — here only `mul_zero` is used).
Number of weakening opportunities found: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Reformulation | Downstream |
|----|----------|----------|---------------|------------|
| 1 | typeclass-ify a "let W be …" preamble? | no | — | `W 0 = 0` is one equational hypothesis, not a structure-worth-of-data |
| 2 | sequences/metric → filters/topology? | no | — | finite algebraic identity; no limiting notion |
| 3 | construction → universal property? | no | — | it's an equation, nothing constructed |
| 4 | set+closure-pred → bundled substructure? | no | — | n/a |
| 5 | vector-space/field → module/(semi)ring weakening? | no | — | already arbitrary `CommRing` |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index ℤ → general add. group/monoid? | borderline-no | could state `addMulSub` over an arbitrary `[AddGroup]`-indexed elliptic net | the *whole `addMulSub` layer* is `ℤ`-indexed by design (it encodes the half-sum/half-difference via `Int.tdiv 2`); generalising the index is a property of the **`addMulSub` definition**, not of this lemma — out of scope for a single helper |

Modern idiom available: **no** (for this lemma). One-line reason: it is a finite
ring identity; the only conceivable generalisation (index group) belongs to the
`addMulSub` *definition*, not the vanishing lemma.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search
paths introduced).

---

### Mathlib search-status: `EllSequence.addMulSub_same`

[A] Lean-Finder       n/a — MCP/index not available in this environment
[B] Loogle            n/a — Loogle MCP not available in this environment
[C] LeanSearch        n/a — LeanSearch MCP not available in this environment
[D] Grep mathlib src  `addMulSub`, `namespace EllSequence`, `def rel₄`, `def net `, `addMulSub_same`, `_same … W 0 = 0` over `.lake/packages/mathlib/Mathlib/` → **zero hits**. Also read `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` in full-head: it uses `IsEllSequence`/`preNormEDS`/`complEDS₂`/`normEDS`, **no `tdiv` building block, no `addMulSub`, no `rel₄`/`net`**.
[E] Name pattern      grep for `addMulSub*` / `EllSequence` names in mathlib → none.

Searched for both:
  - the user's current form (`addMulSub … = 0`) — not present (subject `addMulSub` absent)
  - the literature-standard fact (`W 0 = 0` ⇒ product vanishes) — mathlib's EDS file
    has no `addMulSub`-style product, so there is nothing to specialise from

Concluded: **not in mathlib.** The *subject* of the lemma — the `addMulSub`
building block and the surrounding `EllSequence` elliptic-net layer (`rel₄`, `net`,
`addMulSub_even/odd/neg₀/neg₁/abs/swap`, the transformation lemmas) — does not
exist in mathlib at all. Mathlib's EDS development is a different, smaller
formulation. (Method [D] grep is authoritative against the pinned source; the
MCP-index methods [A][B][C] are recorded n/a due to environment, not skipped.)

---

### Call sites — `EllSequence.addMulSub_same`

Internal use count (NagellLutz, excluding declaring file region): **3**
(`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` lines 554, 558,
562 — but these are in the SAME file as the def). External-to-file callers: 0.

Cross-project census (the same lemma is **triplicated** across the monorepo —
the duplicated tracks the prompt warned about):

| Copy file:line | Usage pattern |
|----------------|---------------|
| NagellLutz/.../EllipticDivisibilitySequence.lean:554 | `simp_rw [rel₄, addMulSub_same W zero]; ring` (proves `rel₄_same₀₁`) |
| NagellLutz/.../EllipticDivisibilitySequence.lean:558 | `simp_rw [rel₄, addMulSub_same W zero]; ring` (proves `rel₄_same₁₂`) |
| NagellLutz/.../EllipticDivisibilitySequence.lean:562 | `simp_rw [rel₄, addMulSub_same W zero]; ring` (proves `rel₄_same₂₃`) |
| HasseWeil/.../Auxiliary/EllipticDivisibilitySequence.lean:109 | duplicate definition of the same lemma |
| HasseWeil/.../Auxiliary/EllipticDivisibilitySequence.lean:469/473/477 | same three `rel₄_same*` call sites |
| NagellLutz/.../EllipticDivisibilitySequenceOriginal.lean:173 + 531/534/537 | a third (original) copy, same lemma + call sites |

Inline-derivation grep: the three call sites all consume it; no site re-derives
`addMulSub W m m = 0` inline (they rely on the lemma). So K = 3 *real* uses per
copy, all feeding the `rel₄_same*` trio.

Signal: K ≥ 3 within-project uses, no inline bypass → this is *real local API* for
the `rel₄_same*` lemmas. But all uses are intra-project, tied to `addMulSub`/`rel₄`
which are themselves project-local.

---

### Composition check (Phase 6)

Can `EllSequence.addMulSub_same` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `by simp [addMulSub, zero]` (unfold def; `sub_self`/`Int.zero_tdiv` are
simp-normal; `mul_zero` closes it).
  - Mathlib decls used: `Int.zero_tdiv`, `sub_self`, `mul_zero` — **plus the
    project-local `addMulSub` definition** (NOT a mathlib decl).
  - Result: succeeds *as written in the proof*, but it is a composition over a
    **project-local** definition, not over mathlib primitives. Mathlib alone cannot
    state the LHS — `addMulSub` is not in mathlib.

Conclusion: **NOT-COMPOSABLE from mathlib** in the strict sense — mathlib does not
have the building block `addMulSub`, so there is no mathlib expression to inline
this into. (It IS a trivial composition over the *project's own* `addMulSub` def +
`mul_zero`, which is why standalone mathlib inclusion is dubious.) This makes both
`NO-mathlib-has-it` and `NO-composable-from-mathlib` inapplicable as stated: the
former is false (mathlib lacks it), the latter is false (mathlib lacks the
building block to compose from).

---

## Verdict: `EllSequence.addMulSub_same`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): `addMulSub` is formalization-internal notation; the
  underlying fact (`W(0)=0` ⇒ diagonal building block vanishes) reduces to the
  standard EDS/elliptic-net axiom (Ward/Stange). No independently named result.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (arbitrary `CommRing`; only
  `mul_zero` used). No modern-idiom restatement of the *lemma* (any index
  generalisation lives on the `addMulSub` *definition*).
- Mathlib search (Phase 5): not in mathlib — and crucially the **subject**
  (`addMulSub`, `rel₄`, `net`, the whole `EllSequence` elliptic-net layer) is
  absent from mathlib; mathlib's EDS file is a different, smaller formulation.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (mathlib lacks the
  `addMulSub` building block); trivially composable from the *project's own* def +
  `mul_zero`.

**Rationale:**

`addMulSub_same` is a one-line vanishing lemma whose entire mathematical content is
"`W(m)·W(0) = 0` given `W(0)=0`". On its own it is too trivial to ship to mathlib —
it is `def`-unfold + `mul_zero`. The reason it cannot be cleanly bucketed as
`NO-composable-from-mathlib` (and inlined away) is that the thing it unfolds,
`addMulSub`, **does not exist in mathlib**: it is a bespoke `Int.tdiv 2`-based
building block introduced in this project specifically so that the neg/abs/swap
lemmas (`addMulSub_neg₀`, `addMulSub_abs₀`, …) hold *unconditionally* (see the
implementation note at lines 95–98). So the lemma's mathlib-worthiness is not an
independent question — it is **entirely contingent on whether the surrounding
elliptic-nets layer (`addMulSub`, `rel₄`, `net`, the same-parity transformation
machinery, the `rel₄_same*` trio it feeds) should be upstreamed**. That is a real
maintainer decision: this layer is a substantial Stange-style development distinct
from mathlib's existing `IsEllSequence`/`normEDS` formulation, and it is currently
**triplicated** across NagellLutz, HasseWeil, and an `…Original` copy — itself a
consolidation question. A single-declaration check cannot settle "adopt David
Angdinata's `addMulSub`/`rel₄` elliptic-net API into mathlib"; that is the
load-bearing judgment, and it is squarely human/maintainer scope and taste.

If the `addMulSub`/`rel₄` layer **is** adopted, `addMulSub_same` rides along as
part of that API (a `@[simp]`-candidate vanishing lemma next to `addMulSub_even` /
`addMulSub_odd`) — `YES-add-as-is`, but only *bundled with its def*, never alone.
If the layer is **not** adopted, the lemma stays project-local (and should be
de-duplicated to one shared copy, e.g. in `Common/`, rather than living in three
places). Both branches hinge on the same human call.

**Numbered questions for the human:**

1. Should the project's `EllSequence` elliptic-net layer — the `addMulSub`
   building block, `rel₄`, `net`, and their algebra (`addMulSub_even/odd/neg/abs/
   swap`, `net_eq_rel₄`, the `HaveSameParity₄` transformation lemmas) — be
   upstreamed to mathlib as an extension of `Mathlib/NumberTheory/
   EllipticDivisibilitySequence.lean`? (If **yes**, `addMulSub_same` ships with it
   as `YES-add-as-is`, likely `@[simp]`. If **no**, it stays project-local.)
2. Independently of mathlib: the identical `addMulSub_same` (and its `rel₄_same*`
   consumers) is **triplicated** across `NagellLutz`, `HasseWeil/Auxiliary`, and
   `EllipticDivisibilitySequenceOriginal.lean`. Should these be consolidated into
   one shared copy (e.g. `Common/`) first, so any mathlib decision is made once?
3. Is the `Int.tdiv 2`-based design of `addMulSub` (chosen so neg/abs lemmas hold
   unconditionally) the form you would want in mathlib, or would mathlib prefer a
   different (e.g. same-parity-restricted, `/`-based) building block — which would
   change what the upstreamed `addMulSub_same` looks like?

**Next action:** user answers Q1–Q3. If Q1 = yes, re-run `/mathlibable` on the
`addMulSub`/`rel₄` definitions (the defs are the real units of the decision), then
ship `addMulSub_same` in the same PR. If Q1 = no, file a consolidation/dedup
cleanup ticket per Q2 (one shared copy) and keep the lemma out of mathlib.

---

## Next step

User answers the three numbered questions. The verdict on this helper is inherited
from the upstreaming decision on the `addMulSub`/`rel₄` elliptic-net layer (the
defs are the real decision units); on its own the lemma is a trivial
`def`-unfold + `mul_zero` and not independently mathlibable.
