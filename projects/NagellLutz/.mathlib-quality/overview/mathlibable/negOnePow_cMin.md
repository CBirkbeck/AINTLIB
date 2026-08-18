# /mathlibable report — `EllSequence.negOnePow_cMin`

## Verdict: NO-composable-from-mathlib (a glue lemma about a project-local helper def)

---

### Baseline (Phase 0)
- lake build:               not run (env: local build stale per task); reasoned from source.
- decl `EllSequence.negOnePow_cMin`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:398`
  (inside `namespace EllSequence`, opened L90, closed L597; **not** inside the
  nested `HaveSameParity₄` namespace which closes at L297). Qualified name **VERIFIED**:
  `EllSequence.negOnePow_cMin`.
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS); defines `IsEllSequence`,
  `preNormEDS`, `normEDS`, and (in this fork) a four-index elliptic-relation `Rel₄` induction
  apparatus. This file is a **fork/extension** of `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

---

### Statement (Phase 1)

`EllSequence.negOnePow_cMin` states: for any integer `a`,

> `(cMin a).negOnePow = a.negOnePow`

i.e. the value `(-1)^(cMin a)` (as a unit in ℤ) equals `(-1)^a`, where `cMin` and `dMin`
are project-local helpers defined just above it:

```lean
def dMin (a : ℤ) : ℤ := if Even a then 0 else 1   -- minimal 4th index given a
def cMin (a : ℤ) : ℤ := dMin a + 2                 -- minimal 3rd index given a
```

So `cMin a ∈ {2, 3}` (2 if `a` even, 3 if `a` odd). The lemma says `cMin a` has the **same
parity as `a`** — restated through `Int.negOnePow`. Its proof is one line, chaining two sibling
glue lemmas:

```lean
lemma negOnePow_cMin (a : ℤ) : (cMin a).negOnePow = a.negOnePow := by
  rw [negOnePow_cMin_eq_dMin, negOnePow_dMin]
```

where `negOnePow_cMin_eq_dMin` (L390: `(cMin a).negOnePow = (dMin a).negOnePow`, proved by
`Int.negOnePow_add` since `cMin = dMin + 2` and `(2).negOnePow = 1`) and `negOnePow_dMin`
(L393: `(dMin a).negOnePow = a.negOnePow`, proved by `split_ifs` + `Int.negOnePow_even/odd`).

Variables (Lean side):
- `a : ℤ` — the first index of the four-index elliptic relation `rel₄ W a b c d`.

Hypotheses: none.

Conclusion (math): `cMin a ≡ a (mod 2)`, expressed via the sign unit `(-1)^•`.
Conclusion (Lean): `(EllSequence.cMin a).negOnePow = a.negOnePow` (an equation in `ℤˣ`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A one-line helper lemma about a project-local `if-then-else` definition (`cMin`);
not a named theorem, not a `## Main statement`, not a new structure. It is pure parity
bookkeeping feeding the `Rel₄` strict-descent induction. (Lit width below is still run in full.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`rw [negOnePow_cMin_eq_dMin, negOnePow_dMin]`).
One-liner verdict: **n/a — kind is `lemma`, not `def`** (the 2b def-exemption table applies to
`def`/`abbrev`/`structure`). Recorded as a note: the lemma is a 1-line `rw` chain of two
sibling lemmas, both of which themselves reduce to mathlib's `Int.negOnePow_*` API. This is a
strong "composable / not standalone" signal carried into Phase 7.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific) | "elliptic divisibility sequence four-index relation minimal index parity Ward division polynomial" | yes (for EDS) | classical EDS recursion `W(n+m)W(n−m)W(r)² = W(n+r)W(n−r)W(m)² − W(m+r)W(m−r)W(n)²`, `n>m>r` | Wikipedia + arXiv (Ward, Silverman, Stange). Confirms the four-index relation and the strict order `n>m>r` — the reason `dMin`/`cMin` exist. **No literature name for "cMin" or its parity.** |
| 2 | WebSearch (general form) | (same channel) — EDS valuation / division-polynomial literature | yes | EDS = sequence of division-polynomial values `Wn = ψn(P)`; relation holds for all integer indices | The four-index relation is the object of study; the *minimal valid third/fourth index given parity* is a bookkeeping device of a particular **formalisation strategy**, absent from the math literature. |
| 3 | WebSearch (named-after/alias) | "Ward elliptic divisibility sequence recursion three-index two-term" | yes | Ward's recursion; the 2-/3-term special cases (`OddRec`/`EvenRec` in this file) | The parity of the minimal index is implicit; never isolated as a named fact. |
| 4 | ChatGPT MCP | (unavailable — task notes "ChatGPT MCP may be down") | n/a | — | Fallback: WebSearch ×3 + reasoning from source. The math content ("cMin a has the same parity as a") is *elementary parity arithmetic* — `cMin a ∈ {2,3}`, even iff `a` even — for which no source attribution exists or is needed. |
| 5 | Local references | `ls projects/NagellLutz/.mathlib-quality/references/` | n/a | — | **Directory absent** (only `overview/` exists). Recorded n/a. |
| 6 | nLab | "elliptic divisibility sequence" | n/a | — | nLab has no EDS page; and "negOnePow of minimal index" is not a categorical concept. |
| 7 | nCatLab | — | n/a | — | Not a categorical concept. |
| 8 | Stacks Project | — | n/a | — | EDS/division-sequence parity bookkeeping is not in Stacks' algebraic-geometry scope. |
| 9 | MathOverflow / MSE | "elliptic divisibility sequence index parity recursion" | partial | discussions of Ward's recursion and EDS sign rules | No isolated statement matching `cMin`; confirms it is folklore parity arithmetic. |
| 10 | arXiv (last 5y) | EDS division-polynomial recursion | yes | Stange, Silverman et al. on EDS/division polynomials | Confirms the four-index relation; none isolate a "cMin parity" lemma — it is an artefact of this Lean formalisation's descent argument. |

### Literature summary (Phase 3)

Concept identified as: **not a named mathematical concept.** `cMin`/`dMin` are *implementation
helpers* introduced by this Lean formalisation to express "the smallest valid (third, fourth)
index pair of the same parity as `a`", used to anchor the strictly-decreasing-index induction
(`StrictAnti₄`, `rel₄_of_min₂`) that proves the four-index elliptic relation. The four-index
relation itself (with `n>m>r`) is classical (Ward); the parity-of-minimal-index lemma is a
bookkeeping step, not a result anyone states on a board.
Sources agree on the standard form: n/a — there is no standard form for this helper.
Most general standard form: n/a.
Generality dimensions where the literature varies: none applicable.
Disagreement with the literature: none — the underlying parity fact (`cMin a ≡ a mod 2`) is
trivially true and the literature simply never names it.

---

### Generality analysis — `EllSequence.negOnePow_cMin`

Literature-standard form (from Phase 3): n/a (no standard form). The lemma is maximally general
*within its own scope* — it quantifies over all `a : ℤ` with no hypotheses.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `a : ℤ` | arbitrary integer | n/a | NO | already fully general; no typeclass to weaken — `cMin` is defined only on `ℤ`. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (trivially — `∀ a : ℤ`, no hypotheses).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

This is moot for mathlib: the statement mentions the **project-local `cMin`**, so it cannot be
stated in mathlib at all without first importing `cMin` — and `cMin` is itself a
formalisation-internal helper (see Phase 6), not a concept mathlib would host.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reason |
|---|----------|----------|--------|
| 1 | typeclasses vs bundled hyps? | no | no hypotheses; nothing to bundle. |
| 2 | filters/topology vs sequences/metric? | no | finite parity arithmetic over ℤ; no limiting process. |
| 3 | universal-property class vs construction? | no | `cMin` is an `ite`, not a constructed object with a UP. |
| 4 | bundled substructure vs set-with-predicate? | no | not a substructure. |
| 5 | weaken vector-space/field to module/ring? | no | already over ℤ; the result is about the sign unit `(-1)^•`. |
| 6 | 1-categorical → higher-categorical? | no | not categorical. |
| 7 | concrete index → general additive structure? | no | `cMin`/`dMin` are intrinsically ℤ-valued parity selectors; generalising the index would dissolve the lemma's purpose. |

Modern idiom available: **no.** Reason: this is a finite parity identity about an
`if Even a then … else …` helper; there is no contemporary mathlib idiom that reorganises it —
the only "idiom" is to not have the lemma at all and inline `Int.negOnePow_add`/`even`/`odd`.

---

### Diamond / defeq risk — (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or instance-search paths introduced).

---

### Mathlib search-status: `EllSequence.negOnePow_cMin`

[A] Lean-Finder       — unavailable in env (lean MCP index offline)   n/a
[B] Loogle            — unavailable in env (lean MCP index offline)   n/a
[C] LeanSearch        — unavailable in env (lean MCP index offline)   n/a
[D] Grep mathlib src  `negOnePow_cMin`, `def cMin`, `def dMin`, `negOnePow_dMin`, `negOnePow_add_two`, `negOnePow.*+ 2` over `.lake/packages/mathlib/`  →  **no hits**
[E] Name pattern      grep `EllSequence` / `Rel₄` / `cMin` in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`  →  **no hits** (mathlib's EDS file is 547 lines and has none of the four-index `Rel₄`/`dMin`/`cMin` apparatus)

Searched for both:
- the user's current form (`negOnePow_cMin`) — absent from mathlib.
- the underlying building blocks — **present**: `Int.negOnePow_add`, `Int.negOnePow_even`,
  `Int.negOnePow_odd`, `Int.negOnePow_eq_one_iff` all in
  `.lake/packages/mathlib/Mathlib/Algebra/Ring/NegOnePow.lean` (full inventory inspected).

**Important fork finding:** `cMin`, `dMin`, `negOnePow_cMin`, and the entire `Rel₄`/four-index
descent machinery are **NOT in mathlib**. They are new development added by this project. The
identical block also appears in:
  - `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:324` and
  - `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:377`
i.e. a **duplicated track** across two AINTLIB projects (a cross-project dedup target on its own,
but orthogonal to the mathlib question).

Concluded: **not in mathlib** (the named lemma); **building blocks present** (the
`Int.negOnePow_*` API). The lemma is a 2-step composition of those building blocks specialised
to the local `cMin`.

---

### Call sites — `EllSequence.negOnePow_cMin`

Internal use count (NagellLutz, excluding declaring file): **1**
External-to-file callers: **0** (the one use is in the same file).

| Caller file:line | Usage pattern |
|------------------|---------------|
| `EllipticDivisibilitySequence.lean:470` | `rw [← negOnePow_eq_iff, negOnePow_cMin, same.same₀₃]` — inside `rel₄_of_min₂`, to discharge a parity side-goal of the four-index descent. |

Inline-derivation grep: the same one-line idea also lives verbatim in the duplicate files
(`EllipticDivisibilitySequenceOriginal.lean:448`, HasseWeil `...:390`) — not an *inline
re-derivation that bypasses the lemma*, but the same lemma copied. Within NagellLutz, used once,
exactly where the `Rel₄` descent needs `cMin a`'s parity.

Signal (per Phase 6.0.1): **K = 1 internal use only → lean toward NO-composable** (single
consumer, the wrong grain for a standalone mathlib lemma; it exists purely to keep the descent
proof readable).

---

### Composition check (Phase 6)

Can `EllSequence.negOnePow_cMin` be derived from mathlib in ≤3 chained calls? — **about the
underlying ℤ-fact, yes; but it cannot live in mathlib because it names `cMin`.**

Two readings:

1. **As-stated (mentions `cMin`):** *cannot* go to mathlib at all — `cMin`/`dMin` are
   project-local helpers absent from mathlib. So the only mathlib-relevant question is whether
   the supporting *general* fact already exists. It does (`Int.negOnePow_add`, etc.), and the
   lemma is glue specialising it to `cMin`.

2. **The general fact it encodes** — "`(-1)^(n+2) = (-1)^n` and `(-1)^•` respects parity" — is
   already fully covered by mathlib:

   Attempt 1 (the `cMin = dMin + 2` step): `negOnePow_cMin_eq_dMin` is literally
   `by rw [cMin, Int.negOnePow_add]; exact mul_one _` — **1 mathlib call** (`Int.negOnePow_add`),
   using `(2 : ℤ).negOnePow = 1`. Succeeds.

   Attempt 2 (the `dMin a ≡ a` step): `negOnePow_dMin` is
   `by rw [dMin]; split_ifs <;> simp [Int.negOnePow_even/odd, …]` — `split_ifs` + two
   `Int.negOnePow_even`/`Int.negOnePow_odd` calls. This is a tiny case-split, **not** a single
   composition, but it is purely `Int.negOnePow_*` API applied to the two branches of an `ite`.

   Conclusion: the math is `Int.negOnePow_add` + `Int.negOnePow_even/odd` (all in mathlib). The
   only "new" content is gluing them onto the local `ite` helper `cMin`.

Conclusion: **COMPOSABLE** — from mathlib's `Int.negOnePow_*` building blocks. There is no
new mathematical content to upstream; the lemma is a project-internal convenience over `cMin`.

---

## Verdict: `EllSequence.negOnePow_cMin`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the four-index EDS relation is classical (Ward), but no source
  names a "parity of the minimal index" lemma — `cMin`/`dMin` are a formalisation device, not a
  math concept.
- Generality analysis (Phase 4): MAXIMALLY GENERAL within its scope, but the scope mentions a
  project-local `def` (`cMin`) that mathlib does not and would not host. No modern idiom.
- Mathlib search (Phase 5): the named lemma is NOT in mathlib; the **building blocks ARE**
  (`Int.negOnePow_add`, `Int.negOnePow_even`, `Int.negOnePow_odd` in `Mathlib/Algebra/Ring/NegOnePow.lean`).
- Composition check (Phase 6): COMPOSABLE from those building blocks; the lemma is 2-step glue.

**Rationale:**

`EllSequence.negOnePow_cMin` is a one-line bookkeeping lemma whose entire content is "the
project-local helper `cMin a = (if Even a then 0 else 1) + 2` has the same parity as `a`",
re-expressed through `Int.negOnePow`. Because its *statement* mentions `cMin` — a
formalisation-internal `if-then-else` selector that exists only to anchor the
strictly-decreasing-same-parity induction in `rel₄_of_min₂` — it is not a candidate for mathlib
on its own terms: mathlib has no `cMin`, and there is no mathematical reason it should. The
mathematics underneath is wholly standard and already in mathlib: `Int.negOnePow_add` gives the
`+2` step (since `(2).negOnePow = 1`) and `Int.negOnePow_even`/`Int.negOnePow_odd` handle the two
branches of the `ite`. The lemma is glue, used exactly once (its sole call site is L470 in the
same file, inside the `Rel₄` descent), which is the wrong grain for a standalone library lemma.

**WHY not (refactor-actionable):** Mathlib already provides every building block — the lemma adds
no mathematical content, only a name local to the `cMin` apparatus. It should **not** be
upstreamed. It is, however, fine to **keep as a private helper in the project**: it makes the one
`Rel₄` descent step readable. If anything, the cross-project concern is that the whole
`cMin`/`dMin`/`negOnePow_cMin` block is **duplicated** in HasseWeil and in
`EllipticDivisibilitySequenceOriginal.lean` — that is a cleanup/dedup matter, independent of
mathlib.

Mathlib building blocks:
- `Int.negOnePow_add`  — `.lake/packages/mathlib/Mathlib/Algebra/Ring/NegOnePow.lean:34`
- `Int.negOnePow_even` — `…/NegOnePow.lean:47`
- `Int.negOnePow_odd`  — `…/NegOnePow.lean:55`
- (`Int.negOnePow` itself; `(2 : ℤ).negOnePow = 1` via `negOnePow_two_mul`/`negOnePow_even`)

Composition sketch (the math, as already realised by the two sibling lemmas, ≤3 lines):
```lean
-- the +2 step:
example (a : ℤ) : (EllSequence.cMin a).negOnePow = (EllSequence.dMin a).negOnePow := by
  rw [EllSequence.cMin, Int.negOnePow_add]; exact mul_one _
-- the parity step:
example (a : ℤ) : (EllSequence.dMin a).negOnePow = a.negOnePow := by
  rw [EllSequence.dMin]; split_ifs with h
  · simp [Int.negOnePow_even, h]
  · simp [Int.negOnePow_odd, Int.not_even_iff_odd.mp h]
```

Call sites in our project (from Phase 6.0): **K = 1** (`EllipticDivisibilitySequence.lean:470`).

Refactor plan (mathlib-direction): **no mathlib PR.** Keep the lemma project-local (it is
correctly scoped as a helper for `cMin`). The mathlib-relevant takeaway is only that the
underlying facts are mathlib's `Int.negOnePow_*` — nothing here is missing from mathlib. The
single call site at L470 already uses the lemma correctly; no inlining is required (the
abstraction earns its keep precisely because the descent proof is already dense). The genuinely
actionable item is the **cross-project dedup** of the shared EDS-`Rel₄` block (NagellLutz ⇄
HasseWeil ⇄ the `Original` snapshot) — a `/cleanup` dedup ticket on `main`, not a mathlib
submission.

---

## Next step

No mathlib PR. Treat as a correctly-scoped project-local helper over `cMin`; its mathematics is
already fully in mathlib (`Int.negOnePow_add` / `negOnePow_even` / `negOnePow_odd`). If acting on
anything, file a cross-project dedup ticket for the duplicated `cMin`/`dMin`/`Rel₄` block shared
by NagellLutz and HasseWeil.

---

### Sources
- Elliptic divisibility sequence — Wikipedia: https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence
- Sequences associated to elliptic curves (Stange): https://arxiv.org/pdf/1909.12654
- Integral points on elliptic curves and explicit valuations of division polynomials: https://arxiv.org/pdf/1108.3051
- p-adic properties of division polynomials and EDS: https://arxiv.org/pdf/math/0404412
