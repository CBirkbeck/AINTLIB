# /mathlibable report — `preNormEDS_even`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences).
> **Headline:** this declaration is a **verbatim fork of a mathlib lemma** — same
> qualified name, byte-identical statement, byte-identical proof. Verdict is
> `NO-mathlib-has-it`, decided at Phase 0/Phase 5. The remaining phases are filled
> for the record but the exact-name exact-statement mathlib hit is dispositive.

---

### Baseline (Phase 0)
- lake build:               not run (env: local build stale per task brief); reasoning is from source + the vendored mathlib tree, which is sufficient here because the assessment turns on an exact textual match against mathlib, not on elaboration.
- decl `preNormEDS_even`:    ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:807`
- qualified name:           **`preNormEDS_even`** (VERIFIED — at line 807 every `namespace` block is already closed: last `end EllSequence` is line 597 / `end IsEllSequence` line 702; the enclosing `section PreNormEDS` at line 704 adds **no** name prefix. Identical situation in the mathlib copy. So the base name *is* the qualified name.)
- kind:                     `lemma` (theorem)
- has sorry:                no
- module docstring summary: Elliptic divisibility sequences — `preNormEDS'` (ℕ-indexed) and `preNormEDS` (ℤ-indexed) auxiliary sequences for a normalised EDS; this file is a fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence` (the section/var layout, the docstrings, and the lemma bodies match).

---

### Statement (Phase 1)

`preNormEDS_even` states the **even-index (doubling) recurrence** for the ℤ-indexed
auxiliary sequence `preNormEDS b c d : ℤ → R` of a normalised elliptic divisibility
sequence. For every `m ∈ ℤ` and any `b, c, d` in a commutative ring `R`:

$$
W(2m) \;=\; W(m-1)^2\,W(m)\,W(m+2)\;-\;W(m-2)\,W(m)\,W(m+1)^2,
\qquad W := \texttt{preNormEDS}\ b\ c\ d .
$$

This is the standard EDS / division-polynomial doubling identity expressing the
`2m`-th term via terms near `m`. It is proved by `Int.negInduction`, reducing to the
ℕ-indexed `preNormEDS'_even` on the non-negative side and to `preNormEDS_neg` on the
negative side.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring; fully general commutative ring.
- `(b c d : R)` — the three abstract initial-data parameters of the normalised EDS.
- `(m : ℤ)` — the index.

Hypotheses: none.

Conclusion (math): the displayed identity `W(2m) = …`.
Conclusion (Lean):
```lean
preNormEDS b c d (2 * m)
  = preNormEDS b c d (m - 1) ^ 2 * preNormEDS b c d m * preNormEDS b c d (m + 2)
  - preNormEDS b c d (m - 2) * preNormEDS b c d m * preNormEDS b c d (m + 1) ^ 2
```

---

### Size classification (Phase 2a)

Verdict: **SMALL** (recurrence lemma about an existing definition; not a new
structure, not a named-after-a-person theorem, not a project main result).
Reason: it is one of the defining recurrences of `preNormEDS`, used downstream to
prove divisibility facts; a helper identity, not a headline.

(Literature width is EXHAUSTIVE regardless — but see the note below: an exact-name
exact-statement mathlib hit already settles the verdict, so the lit sweep is
recorded for provenance rather than to decide generality.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → **n/a**. No one-liner analysis needed.

---

### Literature search (Phase 3)

**Pre-empted by an exact mathlib hit (see Phase 5).** Mathlib already contains this
lemma under the *same qualified name* with a *byte-identical statement and proof*;
the literature question ("is this the right form at the right generality?") is
therefore already answered by mathlib itself — mathlib's reviewers accepted this
exact form. The lit table below records the mathematical provenance for completeness.

| #  | Channel                          | Query / action                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | not run — moot: exact decl already in mathlib (`Mathlib.NumberTheory.EllipticDivisibilitySequence:209`) | n/a | — | Searching the web cannot displace an exact-name + identical-statement + identical-proof mathlib hit; verdict fixed at Phase 5. |
|  2 | WebSearch (general form)         | n/a — same reason                                                              | n/a | — | mathlib form is already over a general `CommRing R`. |
|  3 | WebSearch (named-after/aliases)  | n/a — same reason                                                              | n/a | — | concept = Ward elliptic divisibility sequence doubling recurrence. |
|  4 | ChatGPT MCP                      | n/a — MCP flagged possibly-down in brief; moot given exact mathlib hit         | n/a | — | not needed to resolve a verbatim fork. |
|  5 | Local references                 | `.mathlib-quality/references/` — not consulted; moot                           | n/a | — | exact mathlib hit is dispositive. |
|  6 | nLab                             | n/a                                                                            | n/a | — | EDS recurrence is not an nLab/categorical topic. |
|  7 | nCatLab                          | n/a                                                                            | n/a | — | not categorical. |
|  8 | Stacks Project                   | n/a                                                                            | n/a | — | not the Stacks level of abstraction (it is a concrete recurrence). |
|  9 | MathOverflow / MSE               | n/a                                                                            | n/a | — | moot. |
| 10 | recent arXiv                     | n/a                                                                            | n/a | — | moot. |

**Mathematical provenance (for the record):** the identity is the classical
even-index recurrence for elliptic divisibility sequences (M. Ward, *Memoir on
elliptic divisibility sequences*, Amer. J. Math. 1948) equivalently the doubling
relation among division polynomials of an elliptic curve. Mathlib's
`preNormEDS`/`preNormEDS'` API (author: David Kurniadi Angdinata, 2024)
formalises exactly this, abstractly over `CommRing R` with parameters `b, c, d`.

### Literature summary (Phase 3)

Concept identified as: even-index (doubling) recurrence of the normalised elliptic
divisibility sequence auxiliary sequence.
Sources agree on the standard form: yes — and crucially mathlib already encodes it.
Most general standard form: stated over an arbitrary commutative ring `R` with
abstract data `b, c, d` — which is precisely the mathlib (and project) form.
Generality dimensions where the literature varies: none relevant — the ring-agnostic
form is the maximal sensible generality and both mathlib and the project use it.
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard form: even-index recurrence over a general commutative ring,
abstract `b c d`, index `m ∈ ℤ`.

| # | Parameter / hypothesis | Current Lean form           | Literature-standard form     | Weaker form exists? | Reason |
|---|------------------------|-----------------------------|------------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring            | commutative ring             | NO                  | Already the maximal sensible base; the recurrence is a polynomial identity in `b c d` over a commutative ring. Identical to mathlib. |
| 2 | `(b c d : R)`          | abstract ring elements      | abstract ring elements       | NO                  | Already fully abstract. |
| 3 | `(m : ℤ)`              | integer index               | integer index                | NO                  | The ℤ-indexed sequence is the natural home; the ℕ case is the separate `preNormEDS'_even`. |

#### Generality verdict (Phase 4b)
The current form is: **MAXIMALLY GENERAL** (and identical to mathlib's accepted form).
Number of weakening opportunities found: 0.
Cost of restatement: n/a — no restatement warranted.

#### Modern-idiom check (Phase 4c)
| #  | Question | Applies? | Note |
|----|----------|----------|------|
| 1 | typeclassify "let X be a foo" preambles? | no | already typeclass-based (`[CommRing R]`); `b c d` are genuine data, not a structure to bundle. |
| 2 | sequences/metric → filters/topological? | no | purely algebraic finite recurrence; no limits/topology. |
| 3 | construction → universal-property class? | no | `preNormEDS` is an inherently recursive construction; this lemma is one of its defining identities. |
| 4 | set+closure-predicate → bundled substructure? | no | no substructure here. |
| 5 | vector-space/field-specific → weaken typeclass? | no | already at `CommRing`. |
| 6 | 1-categorical → higher-categorical? | no | n/a. |
| 7 | concrete index ℕ/ℤ/ℝ → general monoid/group? | no | the ℤ index is intrinsic to a two-sided EDS; this is exactly mathlib's formulation. |

Modern idiom available: **no** — the form already matches the contemporary mathlib
EDS API verbatim (it *is* that API). No modernisation move applies.

---

### Diamond / defeq risk (Phase 4.5)
**n/a — declaration kind is `lemma`.** Lemmas introduce no definitional equalities
or typeclass-search paths.

---

### Mathlib search (Phase 5)

```
[A] Lean-Finder       — (not needed)              n/a: superseded by a direct exact-name grep hit in the vendored mathlib tree.
[B] Loogle            — (not needed)              n/a: same.
[C] LeanSearch        — (not needed)              n/a: same.
[D] Grep mathlib src  grep "preNormEDS_even" over .lake/packages/mathlib/…/EllipticDivisibilitySequence.lean
                                                  HIT — line 209: `lemma preNormEDS_even (m : ℤ) : preNormEDS b c d (2 * m) = …`
[E] Name pattern      grep "preNormEDS"           HIT — the ENTIRE preNormEDS API (preNormEDS', preNormEDS, _ofNat, _zero…_four, _neg, _even, _odd, complEDS₂, map_preNormEDS) is present in mathlib.
```

Searched for both the user's current form and the literature-standard form — they
are the same form, and mathlib has it.

**Exact-match evidence (verified by `diff`):**
- Project decl: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:807-820`
- Mathlib decl: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:209-222`
- `diff` of the **statement** lines (project 807–809 vs mathlib 209–211): **no output — IDENTICAL.**
- `diff` of the **proof** lines (project 810–820 vs mathlib 212–222): **no output — IDENTICAL.**
- Same qualified name (`preNormEDS_even`, no namespace prefix in either file).
- Same surrounding API and `section PreNormEDS` layout; mathlib file authored by
  David Kurniadi Angdinata (2024). mathlib pin in `lakefile.toml`: `rev = "d90090f647ca"`.

Concluded: **found in mathlib as `preNormEDS_even` (`Mathlib.NumberTheory.EllipticDivisibilitySequence`); identical form (verbatim — same statement and proof).** This is a vendored fork of the mathlib file, consistent with the project's stated practice of forking `Mathlib.NumberTheory.EllipticDivisibilitySequence` and the division-polynomial files.

---

### Composition check (Phase 6)

#### Call sites — `preNormEDS_even`
Repo-wide grep (`projects/`, excluding `.lake`):

Internal use count (excluding the declaring file `EllipticDivisibilitySequence.lean`): **1** live consumer (the other two hits are in `EllipticDivisibilitySequenceOriginal.lean`, which is itself a second forked copy of the same mathlib file — a duplicate of the duplicate, not an independent consumer).

| Caller file:line | Usage pattern |
|------------------|----------------|
| `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:151` | `preNormEDS_even ..` (applied with auto-filled args) |
| `…/EllipticDivisibilitySequenceOriginal.lean:830` | `rw [complEDS₂, preNormEDS_even]` (inside the duplicate fork) |
| `…/EllipticDivisibilitySequenceOriginal.lean:1003` | `… preNormEDS_even]` (inside the duplicate fork) |

Inline-derivation grep: the only re-derivations are inside `EllipticDivisibilitySequenceOriginal.lean`, which re-declares `preNormEDS_even` itself (line 761) — i.e. a *third* copy of the lemma, not an inline re-proof bypassing it.

Signal: the lemma is real API (it has a genuine downstream consumer in
`DivisionPolynomial.lean`), but that consumer resolves equally well against the
mathlib decl, whose signature is identical.

#### Composition attempt (Phase 6)
Not applicable in the usual sense: this is not a composition-from-primitives
question, because mathlib already contains the **exact lemma**. There is nothing to
inline — the right action is to use mathlib's `preNormEDS_even` directly (drop the
fork). Conclusion: **NOT-COMPOSABLE-AS-NEW** — it is simply *present* in mathlib.

---

## Verdict: `preNormEDS_even`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): moot — exact mathlib hit; the concept is Ward's EDS doubling recurrence, already formalised in mathlib at full `CommRing` generality.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; identical to the mathlib form; no modern-idiom move (4c all "no").
- Mathlib search (Phase 5): **found in mathlib as `preNormEDS_even` (`Mathlib.NumberTheory.EllipticDivisibilitySequence:209`); statement and proof byte-identical (verified by `diff`).**
- Composition check (Phase 6): N/A — present verbatim; the sole real consumer (`DivisionPolynomial.lean:151`) is signature-compatible with the mathlib decl.

**WHY not (refactor-actionable):**
Mathlib already contains this lemma — not merely an equivalent or a more general
form, but the **same declaration**: same qualified name `preNormEDS_even`, same
type, same proof, authored upstream by David Angdinata. The project's
`EllipticDivisibilitySequence.lean` is a vendored fork of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (the docstrings, section
layout, and the whole `preNormEDS` API line up). The project even carries a
*second* fork (`EllipticDivisibilitySequenceOriginal.lean`) re-declaring the lemma
a third time. There is no mathlib gap to fill and nothing to upstream; the
contribution already lives in mathlib.

Existing mathlib decl:  `preNormEDS_even` (namespace-free) in `Mathlib.NumberTheory.EllipticDivisibilitySequence`
Located at:             `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:209`
Our form follows in 0 lines — it **is** the mathlib lemma:
```lean
-- nothing to prove: identical declaration already in mathlib
example (b c d : R) (m : ℤ) :
    preNormEDS b c d (2 * m)
      = preNormEDS b c d (m - 1) ^ 2 * preNormEDS b c d m * preNormEDS b c d (m + 2)
      - preNormEDS b c d (m - 2) * preNormEDS b c d m * preNormEDS b c d (m + 1) ^ 2 :=
  preNormEDS_even m   -- the mathlib lemma
```

Call sites in our project (from Phase 6.0): **1** genuine consumer
(`DivisionPolynomial.lean:151`), plus self-references inside the duplicate fork
`EllipticDivisibilitySequenceOriginal.lean`.

**Refactor plan:**
1. This is a **consolidation/dedup** action, not a per-call-site rewrite. The fix is
   to stop forking the file: have the project `import
   Mathlib.NumberTheory.EllipticDivisibilitySequence` and **delete** the local
   re-declaration of the `preNormEDS` API (including `preNormEDS_even`) from both
   `EllipticDivisibilitySequence.lean` and the redundant
   `EllipticDivisibilitySequenceOriginal.lean`.
2. After deletion, the call at `DivisionPolynomial.lean:151` (`preNormEDS_even ..`)
   resolves to the mathlib decl unchanged — the signature is identical, so **no
   edit is needed at that call site** beyond ensuring the mathlib import is in scope.
3. Caveat: the fork may exist because the project needs *adjacent* results in this
   file that mathlib does **not** yet have (e.g. `complEDS₂`, `preNormEDS_mul_complEDS₂`,
   the `EllSequence`/`HaveSameParity₄`/`Rel₄OfValid` machinery in the first ~700
   lines). Those are out of scope for *this* decl. The dedup here is specifically:
   drop the **mathlib-identical** `preNormEDS*` block and import it instead; keep
   only the genuinely-new surrounding lemmas. (Whether the whole file can be reduced
   to "import mathlib + the new lemmas" is a separate `/overview`-level consolidation
   question.)

**Next action:** delete the forked `preNormEDS_even` (and the rest of the
mathlib-identical `preNormEDS*` API) from the project; `import
Mathlib.NumberTheory.EllipticDivisibilitySequence`; the lone real call site in
`DivisionPolynomial.lean` then binds to the mathlib lemma with no change.

---

## Next step

Delete `preNormEDS_even` from the project and rely on
`Mathlib.NumberTheory.EllipticDivisibilitySequence.preNormEDS_even` (import the
mathlib file); update nothing at the call site (`DivisionPolynomial.lean:151`),
whose usage is already signature-compatible. Treat the broader fork as a
consolidation item: keep only the surrounding lemmas mathlib lacks.
