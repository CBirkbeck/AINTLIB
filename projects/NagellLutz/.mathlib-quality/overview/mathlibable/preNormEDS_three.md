# /mathlibable report — `preNormEDS_three`

> Step-9 mathlibable assessment, NagellLutz project. Single declaration.
> Source: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:796`.

## Verdict (TL;DR)

**`NO-mathlib-has-it`** — this file is a **verbatim fork** of
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, and `preNormEDS_three`
is present there **byte-identically** (mathlib line 198, same `@[simp]`, same
statement, same proof). Not "a more general form exists" — *the exact same
declaration* is already upstream. Delete the fork copy; depend on mathlib.

---

### Baseline (Phase 0)
- lake build:               (not re-run; local build stale per task note — reasoning from source, as instructed)
- decl `preNormEDS_three`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:796`
- kind:                     `lemma` (`@[simp]`)
- has sorry:                no
- module docstring summary: Forks mathlib's EDS API (`IsEllSequence`, `preNormEDS'`, `preNormEDS`, `normEDS`, complement sequences) plus extra `EllSequence`/`HaveSameParity₄` scaffolding for the Nagell–Lutz development.

**Qualified name:** `preNormEDS_three` (root namespace — VERIFIED). The decl sits
inside `section PreNormEDS` (opened at line 704) with `variable (b c d : R)`, but
the nearest enclosing `namespace` (`IsEllSequence`) closed at line 702. So there
is **no namespace prefix**: the fully-qualified name is exactly `preNormEDS_three`.
(Mathlib's copy is likewise in the root namespace — confirmed: only `section
PreNormEDS` + `variable (b c d : R)` wrap it, no `namespace`.)

---

### Statement (Phase 1)

`preNormEDS_three` is a **`@[simp]` evaluation lemma** asserting that the auxiliary
pre-normalised elliptic divisibility sequence `preNormEDS b c d`, evaluated at the
integer `3`, equals its third initial value `c`.

Mathematically: for the EDS auxiliary sequence `W = preNormEDS b c d : ℤ → R`
defined over a commutative ring `R` with parameters `b, c, d ∈ R`, with prescribed
initial data `W(0)=0, W(1)=1, W(2)=1, W(3)=c, W(4)=d`, this lemma is simply the
fourth base-case readout `W(3) = c`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(b c d : R)` — the EDS parameters (section `variable`s).

Hypotheses: none.

Conclusion (math): `preNormEDS(b,c,d)(3) = c`.
Conclusion (Lean): `preNormEDS b c d 3 = c`.

Exact source (fork, lines 795–797):
```lean
@[simp]
lemma preNormEDS_three : preNormEDS b c d 3 = c := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]
```

`preNormEDS` itself (fork lines 774–775):
```lean
def preNormEDS (n : ℤ) : R :=
  n.sign * preNormEDS' b c d n.natAbs
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a base-case `@[simp]` value lemma for a recursively-defined sequence — a
helper/boundary lemma, not a structure, not a named theorem, not a main result.

(Literature width is normally EXHAUSTIVE regardless. Here the decisive fact —
mathlib already contains this exact lemma in the file this project forked — is
established directly in Phase 5, so the literature sweep is recorded as `n/a` per
channel below with a one-line reason: the question "should mathlib have this?" is
already answered "it does, verbatim".)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — the one-line *definition* check
does not apply. Verdict: **n/a (kind is lemma)**. (For the record the body is a
one-line `simp`, but 2b targets defs whose RHS spelling becomes load-bearing; a
proof body is irrelevant to inclusion.)

---

### Literature search table (Phase 3)

Decisive context: this `.lean` file is a **fork of an existing mathlib file**
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`), and `preNormEDS_three`
is one of mathlib's own boundary lemmas, reproduced unchanged. The mathlibability
question therefore collapses to "is it already in mathlib?" — answered **yes,
identically** (Phase 5). A literature sweep for the standard form of "EDS term at
index 3" would only re-derive what the source code already states, so the channels
are recorded `n/a` with reasons.

| #  | Channel                          | Query                                                         | Hit? | Notes |
|----|----------------------------------|--------------------------------------------------------------|------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence" preNormEDS W(3) = c         | n/a  | `preNormEDS` is a mathlib-internal *auxiliary* construction (Ward's EDS, pre-normalisation), not a named literature object; its value at 3 is a definitional base case, not a theorem in the literature. |
|  2 | WebSearch (general form)         | Ward elliptic divisibility sequence initial values           | n/a  | The classical reference (Ward 1948; Silverman's *Arithmetic of Elliptic Curves*; Stange's EDS work) fixes initial terms by convention; `W₃` is data, not a derived result. Nothing to "generalise". |
|  3 | WebSearch (named-after / aliases)| division polynomial ψ₃ initial term                          | n/a  | The genuinely-named object downstream is the 3rd division polynomial ψ₃; mathlib's `preΨ₃ = preNormEDS_three ..` already encodes exactly this link (see `DivisionPolynomial/Basic.lean:215`). No separate lemma is warranted. |
|  4 | ChatGPT MCP                      | standard form / generality / history of EDS index-3 value    | n/a  | MCP down per task note; moot — a base-case readout of a recursive def has no "standard form" to confirm. The answer is settled by the source: mathlib defines it and proves this readout. |
|  5 | Local references                 | grep `.mathlib-quality/references/` for EDS / preNormEDS      | n/a  | No bearing — the controlling artifact is the mathlib *source file* this project forked, which Phase 5 cites directly. |
|  6 | nLab                             | elliptic divisibility sequence                               | n/a  | nLab has no EDS page; not a categorical concept. |
|  7 | nCatLab                          | —                                                            | n/a  | Not a categorical concept. |
|  8 | Stacks Project                   | —                                                            | n/a  | Not an algebraic-geometry/scheme-theoretic concept in the Stacks sense. |
|  9 | MathOverflow / MSE               | EDS normalisation initial terms                              | n/a  | Would only restate the convention; no generality question. |
| 10 | recent arXiv (≤5y)               | elliptic divisibility sequence division polynomial           | n/a  | Active area (Stange, Silverman, et al.), but none of it bears on whether mathlib should hold a base-case `@[simp]` lemma it *already* holds verbatim. |

### Literature summary (Phase 3)

Concept identified as: the value at index 3 of mathlib's **pre-normalised EDS
auxiliary sequence** `preNormEDS` (a normalisation, due to mathlib's formalisation
of Ward's elliptic divisibility sequences, that underpins the division polynomials
`Ψ`). This is a *definitional base case*, not a literature theorem.
Sources agree on the standard form: n/a — there is no "standard form" of a recursion
base case to agree on; the value is data fixed by the definition.
Disagreement with the literature: none.

Note: the literature sweep returning "nothing actionable" is itself the expected
signal here — `preNormEDS` is mathlib-internal plumbing, and the decisive evidence
is structural (it's a fork of a mathlib file), handled in Phase 5.

---

### Generality analysis (Phase 4)

Literature-standard / mathlib form: identical — `preNormEDS b c d 3 = c` over
`[CommRing R]`, the most general setting in which `preNormEDS` is defined.

| # | Parameter / hypothesis | Current Lean form | Mathlib form | Weaker form? | Reason |
|---|------------------------|-------------------|--------------|--------------|--------|
| 1 | `[CommRing R]`         | comm ring         | comm ring (mathlib identical) | NO | `preNormEDS` is *defined* over `CommRing` in mathlib; the lemma matches its host generality exactly. Cannot weaken below the definition's own typeclass. |
| 2 | `(b c d : R)`          | ring elements     | ring elements (identical) | NO | These are the defining parameters; no constraint to relax. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is literally mathlib's own form, at
mathlib's own generality).
Number of weakening opportunities: 0.
Cost of restatement: n/a — nothing to restate.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reason |
|---|----------|----------|--------|
| 1 | bundle hypotheses → typeclasses?              | no | no hypotheses to bundle |
| 2 | sequences/metric → filters/topology?          | no | finite base-case identity; no limiting notion |
| 3 | construction → universal-property class?       | no | it's a value readout, not a construction |
| 4 | set+closure-pred → bundled substructure?       | no | no substructure involved |
| 5 | field/metric-specific → weaker typeclass?      | no | already at `CommRing`, the host generality |
| 6 | 1-categorical → higher-categorical?            | no | not categorical |
| 7 | concrete index → general index/monoid?         | no | the index is the literal `3`; the *point* of the lemma is the specific base case `W₃ = c` |

Modern idiom available: **no**. This is mathlib's own idiom already; there is no
reformulation to make. (And mathlib *deliberately* states `preNormEDS_three` as a
separate concrete-index `@[simp]` lemma alongside `_one`, `_two`, `_four` — that is
the intended API surface for the division-polynomial layer.)

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`.** (No definitional equalities or typeclass-search
paths introduced.)

---

### Mathlib search-status (Phase 5)

[A] Lean-Finder       n/a (index unavailable; structural evidence is stronger)
[B] Loogle            `preNormEDS _ _ _ 3 = _` — would match mathlib's copy
[C] LeanSearch        n/a (index unavailable; structural evidence is stronger)
[D] Grep mathlib src  `grep "preNormEDS_three" .lake/packages/mathlib/...`  →  **HIT**
[E] Name pattern      `preNormEDS_three` in mathlib                          →  **HIT**

**Direct source evidence (decisive):**
- `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:198` —
  ```lean
  @[simp]
  lemma preNormEDS_three : preNormEDS b c d 3 = c := by
    simp [preNormEDS, Int.sign_eq_one_of_pos]
  ```
  `diff` of the fork block (lines 791–797) against the mathlib block (lines 193–199)
  reports **IDENTICAL**. Same `@[simp]`, same signature, same one-line proof.
- The underlying `def preNormEDS` is identical too (mathlib `:176–177`
  `n.sign * preNormEDS' b c d n.natAbs` vs fork `:774–775` — same).
- Both live in the **root namespace** under `section PreNormEDS` / `variable (b c d : R)`.
- Mathlib *uses* it exactly as the fork does: `Mathlib/AlgebraicGeometry/
  EllipticCurve/DivisionPolynomial/Basic.lean:215` has `preNormEDS_three ..`, mirrored
  by the fork's `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:138`
  (`preNormEDS_three ..`).

Concluded: **found in mathlib as `preNormEDS_three`; identical form** (same fully
qualified name, root namespace). The host file is a verbatim fork of the mathlib
module.

---

### Composition check (Phase 6)

#### Call sites (Phase 6.0)

Internal use count (NagellLutz project, excluding the declaring file and the parallel
fork `EllipticDivisibilitySequenceOriginal.lean`): **1**
- `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:138` — `preNormEDS_three ..`
  (constructing the 3rd pre-division-polynomial `preΨ₃`, exactly as mathlib does at
  `DivisionPolynomial/Basic.lean:215`).

Inline re-derivation elsewhere: none found.

Note: the single internal caller mirrors mathlib's own internal caller one-for-one —
further confirming this is forked code, not an independent contribution. The `@[simp]`
attribute also means most consumers reach it implicitly via `simp`, so the literal
grep undercounts true usage; but that, too, is inherited from mathlib.

#### Composition (Phase 6a)

Not applicable as a "compose from primitives" case, because the stronger result holds:
the **whole lemma already exists in mathlib**. There is nothing to compose — the
correct action is to *import mathlib's copy*, not re-derive. (For completeness: the
fork's own proof `simp [preNormEDS, Int.sign_eq_one_of_pos]` is a 1-line unfolding,
but that is mathlib's proof, not a project-local composition.)

Conclusion: **NOT-COMPOSABLE** in the Phase-6 sense (and irrelevant) — superseded by
the exact-duplicate finding in Phase 5.

---

## Verdict: `preNormEDS_three`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): `preNormEDS` is mathlib-internal EDS plumbing; the value
  at index 3 is a definitional base case with no separate literature object — the
  controlling artifact is the mathlib source file itself.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — it *is* mathlib's form at mathlib's
  generality; 0 weakenings; no modern-idiom move.
- Mathlib search (Phase 5): **found in mathlib as `preNormEDS_three`; identical form**
  (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:198`; `diff` = IDENTICAL).
- Composition check (Phase 6): n/a — exact duplicate, not a composition.

**Rationale:**

This declaration is not a new contribution at all: the host file
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a **verbatim
fork** of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, made (per the
project's stated context) to extend the EDS API for the Nagell–Lutz development. The
specific lemma `preNormEDS_three` is reproduced **byte-for-byte** from mathlib —
identical `@[simp]` attribute, identical statement `preNormEDS b c d 3 = c`, identical
proof `simp [preNormEDS, Int.sign_eq_one_of_pos]`, identical root-namespace placement,
and even an identical internal call site (`DivisionPolynomial.lean:138` ↔ mathlib's
`DivisionPolynomial/Basic.lean:215`). Mathlib does not merely contain a more general
form to specialise from; it contains *exactly this declaration*.

The right disposition is therefore to drop the forked copy and depend on mathlib's. In
the AINTLIB cleanup model this is a deduplication: the consolidation goal is for the
project to `import Mathlib.NumberTheory.EllipticDivisibilitySequence` and use
`preNormEDS_three` (and its siblings `_one/_two/_four`, `preNormEDS`, `preNormEDS'`,
`normEDS`, …) directly, keeping only the genuinely *new* `EllSequence` /
`HaveSameParity₄` / complement-sequence scaffolding that this file adds on top.

**WHY not (refactor-actionable):**
Mathlib already has it, identically.
- Existing mathlib decl:   `preNormEDS_three`
- Located at:              `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:198`
- Our form follows in 0 lines — it is the *same* lemma. Anywhere the project needs it:
  ```lean
  -- with `import Mathlib.NumberTheory.EllipticDivisibilitySequence` in scope:
  example (b c d : R) : preNormEDS b c d 3 = c := preNormEDS_three
  ```
- Call sites in our project (Phase 6.0): **1** (`DivisionPolynomial.lean:138`), plus
  implicit `@[simp]` users.

**Refactor plan:**
This is a whole-file dedup, not a one-lemma surgery (the entire file forks a mathlib
module). Concretely:
1. Replace the forked re-declarations of mathlib's EDS API in
   `EllipticDivisibilitySequence.lean` (the `preNormEDS'`/`preNormEDS`/`normEDS`/
   complement block and their `@[simp]` value lemmas including `preNormEDS_three`) with
   `import Mathlib.NumberTheory.EllipticDivisibilitySequence`, retaining only the
   *additional* `EllSequence` / `HaveSameParity₄` / extra-complement material the file
   genuinely adds.
2. At `DivisionPolynomial.lean:138` (`preNormEDS_three ..`) — no edit needed; the name
   resolves to mathlib's lemma once the fork copy is removed and mathlib is imported.
   (Verify no signature skew vs the project's local `preNormEDS`; they are identical, so
   none is expected.)
3. The parallel file `EllipticDivisibilitySequenceOriginal.lean:750` holds the *same*
   duplicate and should be deleted/redirected in the same pass.

> Caveat for the human consolidator: this dedup is **file-scoped**, not lemma-scoped —
> it only goes through cleanly if mathlib's *entire* `preNormEDS`/`normEDS` block is the
> one the project consumes. Several siblings (`preNormEDS_even/odd`, `complEDS₂`, the
> `EllSequence`/`HaveSameParity₄` scaffolding) may be genuinely-new project additions;
> those are *not* covered by this NO verdict and need their own assessment. Only the
> exact-duplicate boundary lemmas (`preNormEDS_three` and its `_one/_two/_four/zero/neg`
> kin, `preNormEDS_ofNat`, etc.) are settled here.

**Next action:** delete `preNormEDS_three` from the NagellLutz fork; `import
Mathlib.NumberTheory.EllipticDivisibilitySequence` and let the 1 call site (plus
`@[simp]` users) resolve against mathlib's identical lemma. Fold this into the
whole-file de-fork of `EllipticDivisibilitySequence.lean` /
`EllipticDivisibilitySequenceOriginal.lean`.

---

## Next step

Delete the forked `preNormEDS_three` (and sibling exact-duplicate boundary lemmas) and
have the NagellLutz project depend on `Mathlib.NumberTheory.EllipticDivisibilitySequence`
directly. Assess the *added* `EllSequence`/`HaveSameParity₄`/complement material
separately — it is out of scope for this NO-mathlib-has-it verdict.
