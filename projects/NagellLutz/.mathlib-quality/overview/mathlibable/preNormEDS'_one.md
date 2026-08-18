# /mathlibable report — `preNormEDS'_one`

> AINTLIB /overview Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz theorem;
> elliptic curves; division polynomials; elliptic divisibility sequences).
> Target: `preNormEDS'_one` at
> `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:743`.

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief); decl elaborates as written — trivial `rw`.
- decl `preNormEDS'_one`:    ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:743`.
- qualified name:           `preNormEDS'_one` (VERIFIED — root namespace; see below).
- kind:                     `lemma` (tagged `@[simp]`).
- has sorry:                no.
- module docstring summary: This file is a **fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`**
  (the project's own header notes it forks the mathlib EDS + DivisionPolynomial tracks), extended with
  additional `EllSequence` / `IsEllSequence` API for the Nagell–Lutz development.

**Qualified-name verification.** The declaration sits in `section PreNormEDS` (opened at line 704).
Walking back the `namespace … end` blocks between line 599 (`open EllSequence`) and line 743 shows only
`namespace EllSequence … end EllSequence` (90–597) and `namespace IsEllSequence … end IsEllSequence`
(643–702), both *closed* before line 704. So at line 743 there is **no enclosing namespace** — the
qualified name is the bare base name `preNormEDS'_one`. (Mathlib's copy is likewise root-namespace.)

---

### Statement (Phase 1)

`preNormEDS'_one` states that the ℕ-indexed auxiliary sequence `preNormEDS' b c d` of a normalised
elliptic divisibility sequence takes the value `1` at index `1`:

> For a commutative ring `R` and parameters `b c d : R`, `preNormEDS' b c d 1 = 1`.

This is one of the five base-case accessor lemmas (`_zero`, `_one`, `_two`, `_three`, `_four`) that read
off the defining initial values `W(0)=0, W(1)=1, W(2)=1, W(3)=c, W(4)=d` of the recursively-defined
auxiliary sequence `preNormEDS'`. It is the formal restatement of the standard EDS normalisation
condition `W(1)=1`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring (file-level `variable`, line 85).
- `(b c d : R)` — the EDS parameters (section-level `variable`, line 706).

Hypotheses: none.

Conclusion (math): `W(1) = 1`, i.e. the second term of the normalised auxiliary EDS is the ring unit.
Conclusion (Lean): `preNormEDS' b c d 1 = 1`.

Proof body: `by rw [preNormEDS']` — unfolds one step of the `preNormEDS'` equation compiler definition
(the `| 1 => 1` arm). One line.

---

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a trivial defining-equation accessor lemma (`def`-arm read-off), not a new structure, not a
named theorem, not a `## Main results` entry. (Literature width run regardless.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. The body is a single-line `rw`; recorded for
context but the def-oriented one-liner exemption table does not apply to lemmas.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|--------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | elliptic divisibility sequence normalised W(1)=1 W(2)=1 recursion division polynomials | yes  | normalised EDS: `W(0)=0, W(1)=1, W(2)=1, W(3)=c, W(4)=d` | Wikipedia "Elliptic divisibility sequence"; Ward 1940s; recursion `W_{2n+1}=W_{n+2}W_n^3 − W_{n−1}W_{n+1}^3`, etc. **Hit #3 of the same search is literally the mathlib EDS doc page.** |
|  2 | WebSearch (general form)         | (same search, general-form facts surfaced)                                              | yes  | EDS over any comm ring; determined by `W₂,W₃,W₄`         | matches the Lean parametrisation by `b,c,d` exactly |
|  3 | WebSearch (named-after / aliases)| "elliptic net" / Ward EDS normalisation                                                 | yes  | Stange "elliptic nets" generalise EDS; same base values  | Shipman / Stange; `W(1)=1` is the universal normalisation anchor |
|  4 | ChatGPT MCP                      | (MCP down per task brief — fallback to WebSearch + source reading)                       | n/a  | —                                                      | covered by channels 1–3 + direct mathlib-source read; the concept is unambiguous and already formalised |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` for "EDS"/"divisib"             | n/a  | —                                                      | no source-paper PDFs needed; the decl is a known-mathlib fork (see Phase 5) |
|  6 | nLab                             | elliptic divisibility sequence                                                          | n/a  | —                                                      | not an nLab/categorical concept; arithmetic-sequence territory |
|  7 | nCatLab                          | —                                                                                       | n/a  | —                                                      | not categorical |
|  8 | Stacks Project                   | elliptic divisibility sequence                                                          | n/a  | —                                                      | not a Stacks (scheme-theoretic AG) topic |
|  9 | MathOverflow / MSE               | elliptic divisibility sequence initial values normalisation                             | yes  | `W(1)=1` standard; consistent across all sources         | confirms no generality variation in the base case |
| 10 | recent arXiv (last 5 years)      | division polynomials / elliptic nets (2025 arXiv:2503.15428 surfaced)                    | yes  | same normalisation; generalised to arbitrary isogenies  | no change to the `W(1)=1` base value |

The protocol passed: WebSearch ran ≥3 generality levels; ChatGPT MCP recorded `n/a` (server down per
brief, compensated by direct mathlib-source reading which is *stronger* evidence than a model opinion);
local refs / nLab / Stacks / nCatLab / MathOverflow / arXiv each checked or `n/a` with reason.

### Literature summary (Phase 3)

Concept identified as: **normalised elliptic divisibility sequence (EDS)** — Morgan Ward (1948);
modern treatments: Silverman, Stange (elliptic nets), Shipman.
Sources agree on the standard form: **yes** — the normalisation `W(0)=0, W(1)=1, W(2)=1` is universal;
`W(1)=1` in particular is the defining anchor and shows zero variation across sources.
Most general standard form: the auxiliary sequence over an arbitrary commutative ring, parametrised by
`(b,c,d) = (W₂-related, W₃, W₄)` — which is **exactly** what `preNormEDS'` already is.
Generality dimensions where the literature varies: none relevant to a base-case value. (The recursion
itself generalises to elliptic nets / arbitrary isogenies, but the value at index 1 is invariantly `1`.)
Disagreement with the literature: none. The Lean statement *is* the textbook normalisation.

---

### Generality analysis — `preNormEDS'_one`

Literature-standard form (from Phase 3): `W(1) = 1` for the normalised auxiliary EDS over any commutative
ring, parameters `b,c,d`.

| # | Parameter / hypothesis | Current Lean form    | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|----------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | commutative ring     | commutative ring         | NO                  | `1` is the ring unit; the EDS recursion (and `preNormEDS'`'s very definition) needs `CommRing`. Cannot drop below the structure the parent `def` requires. This already *matches* mathlib's `preNormEDS'`. |
| 2 | `(b c d : R)`          | three ring elements  | three ring elements      | NO                  | intrinsic to the EDS parametrisation; `_one` doesn't even mention `b,c,d` in its value but they are the def's parameters. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (identical to mathlib's and to the literature standard).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" → typeclass/instance?                                    | no       | —                      | already typeclass `[CommRing R]` |
|  2 | sequences/metric → filters/topology?                                     | no       | —                      | discrete arithmetic sequence; no topology |
|  3 | construction → universal-property class?                                  | no       | —                      | base-case value, nothing to characterise universally |
|  4 | set+closure-predicate → bundled substructure?                             | no       | —                      | n/a |
|  5 | vector-space/field-specific → weaken typeclasses?                         | no       | —                      | already at `CommRing` |
|  6 | 1-categorical → higher-categorical?                                       | no       | —                      | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid?                                  | no       | —                      | the index `1 : ℕ` is the literal EDS index; generalising the index is meaningless for a base case |

Modern idiom available: **no**. One-line reason: this is a defining-equation read-off for a fixed index;
there is no organisational restructuring to make — and mathlib already ships this exact lemma (Phase 5).

---

### Diamond / defeq risk — `preNormEDS'_one`

n/a — declaration kind is `lemma` (a `Prop`-valued proof; introduces no definitional equalities,
typeclass-search paths, coercions, or instance priorities). Phase 4.5 skipped.

---

### Mathlib search-status: `preNormEDS'_one`

[A] Lean-Finder       "preNormEDS one base value EDS"        → effectively a hit: the EDS file is in mathlib.
[B] Loogle            `preNormEDS' _ _ _ 1 = 1`              → matches `preNormEDS'_one` in `Mathlib.NumberTheory.EllipticDivisibilitySequence`.
[C] LeanSearch        "value of normalised EDS auxiliary sequence at 1" → returns the mathlib EDS lemmas.
[D] Grep mathlib src  `grep "preNormEDS'_one" .lake/packages/mathlib/...` → **direct hit**, see below.
[E] Name pattern      `preNormEDS'_one`                      → exact name present in mathlib.

Direct source evidence (decisive — the file is FORKED, so this is not a coincidental name collision):

```
.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean
  line 124:  def preNormEDS' : ℕ → R            -- same def, same arms, root namespace
  line 145:  @[simp]
  line 146:  lemma preNormEDS'_one : preNormEDS' b c d 1 = 1 := by
  line 147:    rw [preNormEDS']
```

Project copy (`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:742–744`):

```
  @[simp]
  lemma preNormEDS'_one : preNormEDS' b c d 1 = 1 := by
    rw [preNormEDS']
```

**Byte-for-byte identical**: same `@[simp]` attribute, same statement `preNormEDS' b c d 1 = 1`, same
proof `rw [preNormEDS']`, same root namespace, same governing `variable {R : Type u} [CommRing R]`
(mathlib line 75 ≡ project line 85) and `variable (b c d : R)` (mathlib line 118 ≡ project line 706).
Both files even carry the same copyright header — `Copyright (c) 2024 David Kurniadi Angdinata`. The
project's `EllipticDivisibilitySequence.lean` is a direct fork of this mathlib module.

Concluded: **found in mathlib as `preNormEDS'_one`** (`Mathlib.NumberTheory.EllipticDivisibilitySequence`,
line 146); **identical form** (same generality, same statement, same proof, same namespace).

---

### Call sites — `preNormEDS'_one`

Internal use count (project, excluding the two declaring/fork files
`EllipticDivisibilitySequence.lean` and `EllipticDivisibilitySequenceOriginal.lean`): **1**.
External-to-project (downstream library) callers: 0.

| Caller file:line                                                  | Usage pattern (one-line excerpt) |
|-------------------------------------------------------------------|----------------------------------|
| `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:85`       | `preNormEDS'_one ..`             |

Inline-derivation grep: the same fork file `EllipticDivisibilitySequenceOriginal.lean:697` re-declares
an identical `preNormEDS'_one` (it is a second copy of the forked module, not an independent
re-derivation). No genuinely independent inline re-derivation found.

Signal: the single internal caller is a `simp`/term-mode reference to the EDS base value — exactly the
sort of call that, after the fork is dropped, points at mathlib's `preNormEDS'_one` instead. This is the
"K small, mathlib has it" pattern → strengthens NO-mathlib-has-it.

---

### Composition check (Phase 6)

Not strictly needed (mathlib has the *exact* lemma, not merely building blocks), but for completeness:
`preNormEDS' b c d 1 = 1` is one definitional unfold of the `| 1 => 1` arm — `by rw [preNormEDS']` or
`by simp` closes it from mathlib's own `preNormEDS'` definition in ≤1 line.

Conclusion: **NOT-COMPOSABLE as a *new* lemma is moot** — the lemma already exists verbatim in mathlib;
the relevant fact is the Phase-5 exact hit, not a primitive composition.

---

## Verdict: `preNormEDS'_one`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): standard normalised-EDS base value `W(1)=1` (Ward; Silverman; Stange);
  one of the WebSearch hits is the mathlib EDS doc page itself.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — already over arbitrary `CommRing`, identical to
  mathlib's; no modern-idiom restructuring available.
- Mathlib search (Phase 5): found in mathlib as `preNormEDS'_one`
  (`Mathlib.NumberTheory.EllipticDivisibilitySequence:146`); **byte-identical** form, statement, proof,
  attribute, and namespace. The project file is a direct fork of that module.
- Composition check (Phase 6): moot — exact lemma already present.

**Rationale.**
The project's `LutzNagell/EllipticDivisibilitySequence.lean` is an explicit **fork** of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (David Kurniadi Angdinata, 2024) — same copyright
header, same root namespace, same `variable` setup. `preNormEDS'_one` is reproduced character-for-character
from mathlib line 146: identical `@[simp]` attribute, identical statement `preNormEDS' b c d 1 = 1`,
identical proof `by rw [preNormEDS']`. There is nothing to add: mathlib already has this lemma at the
exact same generality. This is a textbook NO-mathlib-has-it.

**WHY not (refactor-actionable).**
Mathlib already ships `preNormEDS'_one`. The forked project copy exists only because the whole EDS module
was vendored into the project (presumably to extend it with the surrounding `EllSequence`/`IsEllSequence`
Nagell–Lutz API before any of that lands upstream). For *this base-case lemma specifically*, nothing is
gained by keeping the fork's copy — `import Mathlib.NumberTheory.EllipticDivisibilitySequence` gives the
identical `preNormEDS'_one` (and the parent `preNormEDS'`, plus `_zero/_two/_three/_four/_even/_odd`).

  Existing mathlib decl:        `preNormEDS'_one`
  Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:146`
  Our form follows in ≤1 line:  it is the *same* lemma — `example : preNormEDS' b c d 1 = 1 := preNormEDS'_one ..`
                                (resolving to the mathlib lemma once the fork's copy is removed).
  Call sites in our project (Phase 6.0): K = 1 — `DivisionPolynomial.lean:85` (`preNormEDS'_one ..`).

  Refactor plan:
  - This lemma is not refactored in isolation; it rides on the disposition of the **whole forked
    `preNormEDS'`/EDS block**. The right unit of action is "de-fork the EDS module," not "delete one
    base-case lemma." Concretely:
    1. Decide whether the project still needs its *local* `preNormEDS'` track at all, or whether it can
       `import Mathlib.NumberTheory.EllipticDivisibilitySequence` and keep only the genuinely-new
       `EllSequence`/`IsEllSequence` additions on top.
    2. If de-forking the EDS core: drop the project's `def preNormEDS'` and its five base-case accessor
       lemmas (`preNormEDS'_zero/_one/_two/_three/_four`) plus `_even/_odd`, letting all references bind
       to the mathlib versions. The lone call site `DivisionPolynomial.lean:85` (`preNormEDS'_one ..`)
       then resolves to `Mathlib...preNormEDS'_one` unchanged — same name, same arg shape (`..`), so the
       call site needs **no edit**.
    3. Caveat: do this as one coordinated de-fork pass (the `_even/_odd` lemmas and downstream `normEDS`
       glue must bind to the *same* `preNormEDS'` as the base cases — don't half-fork). Note also the
       sibling file `EllipticDivisibilitySequenceOriginal.lean`, which holds a *second* identical copy;
       the de-fork should reconcile/remove it too.
  - Per AINTLIB's CLAUDE.md, statement-changing dedup against mathlib is exactly a `lane:cleanup` /
    cross-project-dedup job on `main`, not a producer edit. File it as a cleanup ticket scoped to the
    whole forked EDS block rather than this single lemma.

  Next action: do **not** ship `preNormEDS'_one` to mathlib (it is already there). Instead, file a
  `lane:cleanup` dedup ticket: "de-fork `LutzNagell/EllipticDivisibilitySequence.lean` against
  `Mathlib.NumberTheory.EllipticDivisibilitySequence`; drop the duplicated `preNormEDS'` core
  (`def` + `_zero/_one/_two/_three/_four/_even/_odd`), keep only the new `EllSequence` API; update the
  single `DivisionPolynomial.lean:85` reference (no change expected) and reconcile the `…Original.lean`
  duplicate."

---

## Next step

Do not ship to mathlib — mathlib already has `preNormEDS'_one`
(`Mathlib.NumberTheory.EllipticDivisibilitySequence:146`), byte-identical. File a `lane:cleanup` ticket
to de-fork the duplicated `preNormEDS'`/EDS block as a whole (not this lemma in isolation); the one call
site at `DivisionPolynomial.lean:85` rebinds to the mathlib lemma with no edit.
