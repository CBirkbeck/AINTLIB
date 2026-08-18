# /mathlibable report — `normEDS_odd`

> Mode A (single declaration), full 10-phase workflow.
> **Headline: `normEDS_odd` is a verbatim fork of an existing mathlib lemma.**
> The project file `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a
> fork/extension of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same Apache header,
> same author "David Kurniadi Angdinata"). `normEDS_odd` already lives in that mathlib file at
> line 342 — **same statement, same `[CommRing R]` context, same `variable (b c d : R)`, same proof.**
> Verdict: **NO-mathlib-has-it.**

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task note); decl read directly from source
- decl `normEDS_odd`:        ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:951`
- kind:                      `lemma` (theorem)
- has sorry:                 no
- qualified name:            **`normEDS_odd`** — declared inside `section NormEDS` (lines 881–1520) with `variable (b c d : R)`; the file's last `namespace` (`EllSequence`) closed at line 597, so there is **no enclosing namespace prefix**. Bare `normEDS_odd`, matching mathlib's own bare name.
- module docstring summary:  "Elliptic divisibility sequences (EDS) and the construction of normalised EDSs from initial terms" — a fork of mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

---

### Statement (Phase 1)

`normEDS_odd` is the **odd-index recurrence** for the canonical normalised elliptic divisibility
sequence `normEDS b c d : ℤ → R`. For every `m : ℤ`,

$$ W(2m+1) \;=\; W(m+2)\,W(m)^3 \;-\; W(m-1)\,W(m+1)^3, $$

where `W = normEDS b c d` is the EDS with initial values `W(0)=0, W(1)=1, W(2)=b, W(3)=c,
W(4)=d·b`. This is one of the two recurrences (the even one is `normEDS_even`) that *define* a
normalised EDS — it is the relation that lets you compute the odd-indexed terms from earlier terms,
and is precisely the recurrence satisfied by the odd-degree division polynomials `ψ_{2m+1}` of an
elliptic curve (Morgan Ward, 1948).

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring (general commutative ring).
- `(b c d : R)` — the three free initial parameters of the normalised EDS.
- `(m : ℤ)` — the index argument.

Hypotheses (Lean side): none — it is an unconditional identity.

Conclusion (math): the odd-index three-term-style recurrence displayed above.

Conclusion (Lean):
```lean
normEDS b c d (2 * m + 1) =
  normEDS b c d (m + 2) * normEDS b c d m ^ 3 -
    normEDS b c d (m - 1) * normEDS b c d (m + 1) ^ 3
```

Proof body (project, lines 954–956 — identical to mathlib 345–347):
```lean
simp_rw [normEDS, preNormEDS_odd, if_neg m.not_even_two_mul_add_one, Int.even_add, Int.even_sub,
  even_two, iff_true, Int.not_even_one, iff_false]
split_ifs <;> ring1
```

---

### Size classification (Phase 2a)

Verdict: **SMALL** (recorded for framing; literature width is EXHAUSTIVE regardless).
Reason: a `lemma` giving one recurrence identity for an already-defined object; not a new
structure, not a person-named theorem, not a `## Main results` entry. (It is, however, a *core*
defining lemma of the EDS API — not an incidental helper.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → **n/a**. One-line check skipped.

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence recurrence W(2n+1) odd terms division polynomial formula" | yes  | `h_{2n+1} = h_{n+2} h_n^3 − h_{n−1} h_{n+1}^3` (the "even–odd recurrence", odd half) | Wikipedia "Elliptic divisibility sequence"; arXiv math/0402415 (Silverman–Stephens, "The sign of an EDS"); arXiv 0710.1316 (Stange, "Elliptic nets and elliptic curves") — all state exactly this odd recurrence |
|  2 | WebSearch (general form / origin)| (same results) Morgan Ward generality, commutative-ring EDS                            | yes  | Ward's defining recurrences; arXiv 2604.05280 "On Elliptic Sequences over Commutative Rings" — EDS over a general commutative ring | the recurrence is stated identically over an arbitrary commutative ring; `[CommRing R]` is already the literature-general setting |
|  3 | WebSearch (named-after / aliases)| "Ward elliptic divisibility sequence division polynomial psi recurrence"               | yes  | `W_n = λ^{n²−1} ψ_n(x,y)`; odd-degree `ψ_{2n+1}` recurrence | the odd recurrence is exactly the division-polynomial duplication formula for `ψ_{2m+1}` (Silverman, *Arithmetic of Elliptic Curves*, Exercise 3.7) |
|  4 | ChatGPT MCP                      | (server down per task note — fallback to WebSearch #1–3 + Wikipedia + arXiv)           | n/a  | covered by #1–3     | MCP unavailable; the three WebSearch passes at distinct generality levels + the canonical references (Ward, Silverman, Stange) supply the standard-form determination |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` for "EDS"/"divisibility"/"Ward" | n/a  | —                   | no source-paper PDFs present for this concept; recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence"                                                       | n/a  | —                   | nLab has no dedicated EDS page; not a category-theoretic concept |
|  7 | nCatLab (categorical)            | —                                                                                     | n/a  | —                   | not a categorical concept |
|  8 | Stacks Project (alg geom)        | —                                                                                     | n/a  | —                   | Stacks has no EDS / division-polynomial entry; arithmetic-of-elliptic-curves topic, not scheme-theoretic foundations |
|  9 | MathOverflow / Math.SE           | "elliptic divisibility sequence even odd recurrence"                                   | yes  | same odd recurrence | multiple Q&A reproduce `W_{2n+1} = W_{n+2} W_n^3 − W_{n−1} W_{n+1}^3` as the standard EDS recursion |
| 10 | recent arXiv (last 5 yr)         | "elliptic sequences commutative rings"                                                 | yes  | arXiv 2604.05280 (2026) | confirms the recurrence is the modern standard over a general commutative ring — matching mathlib's `[CommRing R]` exactly |

### Literature summary (Phase 3)

Concept identified as: the **odd-index recurrence of an elliptic divisibility sequence** (Morgan
Ward's even–odd recurrence; equivalently the division-polynomial formula for `ψ_{2m+1}`).
Sources agree on the standard form: **yes** — Ward (1948), Silverman–Stephens (math/0402415),
Stange (0710.1316), Wikipedia, and the 2026 commutative-rings paper all state
`W_{2n+1} = W_{n+2} W_n^3 − W_{n−1} W_{n+1}^3` verbatim.
Most general standard form: stated over an **arbitrary commutative ring** — exactly mathlib's (and
the project's) `[CommRing R]` setting; the literature does not weaken below a commutative ring,
because the recurrence multiplies four sequence values.
Generality dimensions where the literature varies: **none material** — the coefficient ring ranges
over commutative rings in every source; `[CommRing R]` is the literature-general form.
Disagreement with the literature: **none.** The Lean statement is the textbook recurrence at the
textbook generality.

---

## PHASE 4 — Generality analysis

### Generality analysis — `normEDS_odd`

Literature-standard form (Phase 3): `W_{2m+1} = W_{m+2} W_m^3 − W_{m−1} W_{m+1}^3` over an arbitrary
commutative ring, `W = normEDS b c d`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring          | **NO** | the recurrence multiplies four ring elements (`W(m+2)·W(m)^3` etc.); commutativity is used by `ring1`. Below `CommRing` there is no recurrence to state. Already maximal. |
| 2 | `(b c d : R)`          | three free params | three free params         | NO | these are the defining parameters of `normEDS`; cannot be weakened. |
| 3 | `(m : ℤ)`              | integer index     | integer index             | NO | `normEDS` is a `ℤ → R` sequence by definition; the index domain is intrinsic. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (identical to the literature-standard generality, which
is also exactly mathlib's).
Number of weakening opportunities found: **0**.
Proposed restatement: none needed.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | already typeclass-based (`[CommRing R]`) | — |
| 2 | sequences/metric → filters/topological? | no | finite algebraic identity; no limiting process | — |
| 3 | construct → universal-property class? | no | it is an equation about a fixed construction | — |
| 4 | set-with-closure → bundled substructure? | no | not a substructure statement | — |
| 5 | vector-space/field-specific → weaken typeclasses? | no | already at `CommRing`, the weakest sensible ring class | — |
| 6 | 1-categorical → higher-categorical? | no | not categorical | — |
| 7 | concrete index (ℕ,ℤ,ℝ) → arbitrary group/monoid? | no | the index is `ℤ` intrinsically (EDS are `ℤ`-indexed; `2m+1` parametrises odd integers) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is a finite algebraic recurrence identity at the weakest
sensible ring generality; there is no contemporary reformulation that organises it better. (And in
any case mathlib already states it in exactly this form — see Phase 5.)

---

## PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `lemma`** (theorems introduce no definitional equalities or
typeclass-search paths). Skipped.

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `normEDS_odd`

[A] Lean-Finder       "normalised EDS odd recurrence", "elliptic divisibility sequence odd terms"   → mathlib index returns `normEDS_odd` (NumberTheory.EllipticDivisibilitySequence)
[B] Loogle            `normEDS _ _ _ (2 * _ + 1) = _`                                                → matches `normEDS_odd`
[C] LeanSearch        "recurrence for odd-index normalised elliptic divisibility sequence"           → top hit `normEDS_odd`
[D] **Grep mathlib src**  `(lemma|theorem) normEDS_odd` over `.lake/packages/mathlib/Mathlib/`       → **exact hit**: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:342`
[E] Name pattern      `normEDS_odd` / `normEDS_*`                                                     → exact-name hit in the same file

Searched for both:
  - the user's current form — found verbatim.
  - the literature-standard form — identical to the user's form, so the same hit.

**Concluded: found in mathlib as `normEDS_odd` (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:342`); identical form.**

Byte-for-byte comparison (pinned mathlib `09b373db6e24`, the version this monorepo builds against):

| | mathlib (lines 342–347) | project (lines 951–956) |
|---|---|---|
| signature | `lemma normEDS_odd (m : ℤ) : normEDS b c d (2 * m + 1) = normEDS b c d (m + 2) * normEDS b c d m ^ 3 - normEDS b c d (m - 1) * normEDS b c d (m + 1) ^ 3` | **identical** |
| context | `variable (b c d : R)` in `section NormEDS`, `{R} [CommRing R]` | **identical** |
| proof | `simp_rw [normEDS, preNormEDS_odd, if_neg m.not_even_two_mul_add_one, Int.even_add, Int.even_sub, even_two, iff_true, Int.not_even_one, iff_false]; split_ifs <;> ring1` | **identical** |
| file header | `Copyright (c) 2024 David Kurniadi Angdinata … Authors: David Kurniadi Angdinata` | **identical** |

The local `normEDS` definition the project's lemma is *about* is itself a verbatim copy of mathlib's
`normEDS` (`normEDS n := preNormEDS (b ^ 4) c d n * if Even n then b else 1`, mathlib line 289 vs the
project's local copy). So the project's `normEDS_odd` and mathlib's `normEDS_odd` are the same
statement about the same object — the entire file is a fork.

---

## PHASE 6 — Composition check (+ call-sites)

### Call sites — `normEDS_odd`

Internal use count (NagellLutz project, excluding the declaring file): **1**
- `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:359` — `normEDS_odd ..`
  (mirrors mathlib's own downstream use of `normEDS_odd` in `DivisionPolynomial/Basic.lean`).

Within the declaring file: `EllipticDivisibilitySequence.lean:966` —
`convert normEDS_odd b c d (↑k + 2) using 2` (inside `IsEllSequence.normEDS_of_mem_nonZeroDivisors`).

External-to-project: `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:594` —
`have h := normEDS_odd b c d (↑k + 2)`. **This is a *second, independent fork*** of the same mathlib
file in a different project, with its own re-declared `normEDS_odd` and its own consumer. (Confirms
the fork pattern is repo-wide, not one-off.)

| Caller file:line | Usage pattern |
|------------------|---------------|
| NagellLutz/.../DivisionPolynomial.lean:359 | `normEDS_odd ..` |
| NagellLutz/.../EllipticDivisibilitySequence.lean:966 | `convert normEDS_odd b c d (↑k + 2) using 2` (same file) |
| HasseWeil/.../EllipticDivisibilitySequence.lean:594 | `have h := normEDS_odd b c d (↑k + 2)` (separate fork) |

Inline-derivation grep: the recurrence is **not** re-derived inline anywhere — consumers always go
through `normEDS_odd`. (Good API hygiene; it just happens to be mathlib's API, copied.)

Composability signal: real API, used downstream — but the API is **mathlib's**, duplicated here.
Leaning: NO-mathlib-has-it (the consumers should resolve to the mathlib lemma).

### Composition check (Phase 6)

Can `normEDS_odd` be derived from mathlib in ≤3 chained calls? **It need not be derived — mathlib
*is* it.** The only "composition" is the trivial alias `normEDS_odd := normEDS_odd` (the mathlib
lemma). This is not a composition of primitives; it is the same declaration. Per the composition
heuristics, an exact-name exact-statement mathlib hit is **NO-mathlib-has-it**, not
NO-composable-from-mathlib.

Conclusion: **NOT-COMPOSABLE (because it is not a composition case at all — it is a direct duplicate).**

---

## Verdict: `normEDS_odd`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): the odd EDS recurrence `W_{2m+1} = W_{m+2}W_m^3 − W_{m−1}W_{m+1}^3`
  is the standard form (Ward 1948; Silverman–Stephens; Stange; Wikipedia), stated over a general
  commutative ring — exactly the Lean form.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL**; `[CommRing R]` is the literature-general
  setting; no weakening and no modern-idiom restatement available.
- Mathlib search (Phase 5): **found in mathlib as `normEDS_odd`,
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:342`; identical form** (same signature,
  same `[CommRing R]` context, same proof, same Apache/author header).
- Composition check (Phase 6): NOT-COMPOSABLE (direct duplicate, not a primitive composition).

**Rationale.**
The project file `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a *fork* of
the mathlib file `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` — same copyright line
(2024, David Kurniadi Angdinata), same author, same module docstring, same `normEDS` definition, and
the same downstream API. `normEDS_odd` specifically is **byte-for-byte identical** between the
project (lines 951–956) and the pinned mathlib `09b373db6e24` (lines 342–347): identical statement,
identical `variable (b c d : R)` / `{R} [CommRing R]` context, identical proof script. This is not a
near-miss or a specialisation — it is the literal mathlib lemma re-typed inside a forked file.

This is a pure **consolidation** finding: the NagellLutz EDS file forks-and-extends mathlib's EDS
file (to add the project's new `EllSequence` / `IsEllSequence` / complement-EDS / transfer API on
top), and in doing so re-declares the entire upstream API, of which `normEDS_odd` is one verbatim
leaf. The HasseWeil project carries a *second* independent fork of the same file with its own
`normEDS_odd` — so this is a repo-wide duplication of an upstream mathlib module, not a one-off.

**WHY not (refactor-actionable).** Mathlib already has `normEDS_odd` in identical form. The project's
copy contributes nothing new — the new content of the file is the surrounding `EllSequence` API, not
this lemma. The right move is to stop forking the upstream EDS module: `import
Mathlib.NumberTheory.EllipticDivisibilitySequence` and build the project's additions on top of it,
deleting every re-declared upstream lemma (`normEDS_odd`, `normEDS_even`, `normEDS_zero..four`,
`normEDS_neg`, `normEDSRec`, the `preNormEDS*` family, the `normEDS` def itself, etc.). `normEDS_odd`
is one representative leaf of that whole-file de-fork.

Existing mathlib decl:        `normEDS_odd`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:342`
Our form follows in ≤1 line (it *is* the mathlib lemma):
```lean
-- after `import Mathlib.NumberTheory.EllipticDivisibilitySequence`, the name
-- `normEDS_odd` already refers to the mathlib lemma — no local copy needed.
example (b c d : R) (m : ℤ) :
    normEDS b c d (2 * m + 1) =
      normEDS b c d (m + 2) * normEDS b c d m ^ 3 -
        normEDS b c d (m - 1) * normEDS b c d (m + 1) ^ 3 :=
  normEDS_odd ..   -- the mathlib lemma
```
Call sites in our project (from Phase 6.0): **K = 1** external (DivisionPolynomial.lean:359) + 1
in-file (EllipticDivisibilitySequence.lean:966); plus 1 in the separate HasseWeil fork.

Refactor plan:
1. **De-fork the file.** Replace the project's hand-rolled copy of mathlib's EDS API with `import
   Mathlib.NumberTheory.EllipticDivisibilitySequence`; keep only the genuinely-new declarations
   (`EllSequence.*`, `IsEllSequence.*`, the complement-EDS / transfer machinery) that mathlib lacks.
   Delete the duplicated `normEDS_odd` at `EllipticDivisibilitySequence.lean:951` along with the
   other re-declared upstream lemmas.
2. **Call sites need no edit.** `normEDS_odd ..` (DivisionPolynomial.lean:359) and
   `normEDS_odd b c d (↑k + 2)` (EllipticDivisibilitySequence.lean:966) resolve to the mathlib lemma
   unchanged once it is imported — identical signature, identical argument order.
3. **Apply the same de-fork to the HasseWeil copy** (HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean),
   a separate consolidation ticket.

Caveat for the human consolidator: confirm the *whole* forked file is mathlib-current. The fork
sits on mathlib `09b373db6e24`; if the producer added local tweaks to any upstream lemma elsewhere
in the file, de-forking must preserve those. For `normEDS_odd` specifically there are **no** local
changes — it is identical — so deleting it and importing is safe.

Next action: file a consolidation ticket to de-fork
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` against
`Mathlib.NumberTheory.EllipticDivisibilitySequence`; delete the duplicated `normEDS_odd` (and its
upstream-duplicate siblings) and import. `normEDS_odd` is one verbatim-duplicated leaf of that
whole-file consolidation.

---

## Next step

File a consolidation ticket to **de-fork** the NagellLutz EDS file against mathlib's
`Mathlib.NumberTheory.EllipticDivisibilitySequence`: delete the duplicated `normEDS_odd` at
`EllipticDivisibilitySequence.lean:951` (together with the other re-declared upstream EDS lemmas)
and replace the hand-rolled upstream API with an `import`. The two call sites resolve to the mathlib
lemma with no edit. (`normEDS_odd` is byte-for-byte identical to mathlib `…:342`; the HasseWeil fork
needs the same treatment as a separate ticket.)
