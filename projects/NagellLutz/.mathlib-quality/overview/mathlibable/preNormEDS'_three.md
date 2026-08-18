# /mathlibable report — `preNormEDS'_three`

## Verdict: **NO-mathlib-has-it**

Mathlib already contains this declaration **character-for-character identical** —
same (top-level) namespace, same statement, same `@[simp]` attribute, same proof —
at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:153`. The project file is
a deliberate **fork** of that mathlib module.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief; reasoned from source — the decl is a 2-line `rw` unfold and elaborates trivially)
- decl `preNormEDS'_three`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:751`
- qualified name:            `preNormEDS'_three` (no namespace — declared inside `section PreNormEDS` which opens no `namespace`; the enclosing `@[expose] public section` likewise adds no namespace)
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  forked copy of mathlib's elliptic-divisibility-sequence development (normalised EDS, `preNormEDS'`/`preNormEDS`/`normEDS`), with an extra `EllSequence` framework for the Nagell–Lutz project

### Statement (Phase 1)

`preNormEDS'_three` states that the auxiliary normalised-EDS sequence `preNormEDS' b c d`
takes the value `c` at index `3`:

> For a commutative ring `R` and `b c d : R`, the natural-number-indexed auxiliary
> elliptic-divisibility sequence `preNormEDS' b c d : ℕ → R` — defined by the initial
> values `W(0)=0, W(1)=1, W(2)=1, W(3)=c, W(4)=d` together with the EDS recursion for
> `n ≥ 5` — satisfies `W(3) = c`.

This is simply one of the five base-case "defining value" unfold lemmas for the recursive
definition `preNormEDS'` (alongside `_zero`, `_one`, `_two`, `_four`).

- Variables: `R : Type u`, `[CommRing R]`, `b c d : R` (the three sequence parameters).
- Hypotheses: none.
- Conclusion (math): `W(3) = c` where `W = preNormEDS' b c d`.
- Conclusion (Lean): `preNormEDS' b c d 3 = c`.
- Proof: `by rw [preNormEDS']` — a single unfold of the recursive definition at the literal `3` branch.

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-step defining-value unfold lemma for a recursive `def`; not a named theorem,
not a project main result, not a new structure.

### One-line / glue-lemma check (Phase 2b)

Kind is `lemma`, so the one-line *definition* check is n/a. However it is a textbook
**glue lemma** in the skill's sense: the body is a single definitional unfold
(`:= by rw [preNormEDS']`) of the parent def `preNormEDS'`. Per the skill's verdict-
inheritance rule, its verdict follows the parent def `preNormEDS'`. The parent def is
present in mathlib verbatim (see Phase 5), so the parent verdict is NO-mathlib-has-it,
and this glue lemma **inherits NO-mathlib-has-it**.

### Literature search (Phase 3) — n/a (short-circuited by an exact mathlib hit)

The exhaustive literature protocol is **moot** here. The standard `/mathlibable` question
is "*should* mathlib have this, in the right form?" — but Phase 5 establishes that mathlib
**already has the exact declaration**, identical name, statement, and proof. There is no
generality/standard-form judgment left to ground in the literature: a verbatim match settles
the verdict directly. (For completeness: `preNormEDS'` is the standard normalised
elliptic-divisibility-sequence / division-polynomial auxiliary recurrence — Ward 1948, and
in mathlib's own EDS development; the value `W(3)=c` is just a chosen normalisation constant,
not a literature theorem.)

Concept identified as: defining value of the normalised-EDS auxiliary recurrence `preNormEDS'`.
Sources agree on the standard form: n/a — settled by exact mathlib match, not by literature.

### Generality analysis (Phase 4) — n/a

No generality gap to analyse: the project lemma and the mathlib lemma have **identical**
signatures (`{R} [CommRing R] (b c d : R) : preNormEDS' b c d 3 = c`). `CommRing` is already
the natural minimal typeclass for the polynomial EDS recursion (it needs subtraction and
multiplication). Phase 4b verdict: **MAXIMALLY GENERAL** (equal to the mathlib form).
Phase 4c modern-idiom: no idiom move applies — it is a base case of a concrete `ℕ`-indexed
recurrence; mathlib itself states it exactly this way.

### Diamond / defeq risk (Phase 4.5) — n/a
Declaration kind is `lemma`; no definitional equality or typeclass-search path introduced.

### Mathlib search (Phase 5)

Five-method search collapses to a **direct source hit** — the decisive evidence:

```
[D] Grep mathlib src   "preNormEDS'_three", "def preNormEDS'"
    → HIT: Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:153
      lemma preNormEDS'_three : preNormEDS' b c d 3 = c := by rw [preNormEDS']
      (def preNormEDS' at line 124; @[simp] lemmas _zero/_one/_two/_three/_four at 141–158)
[E] Name pattern       grep tree for "preNormEDS'_three" across .lake/packages/mathlib/Mathlib
    → HIT at the same file:153; also USED BY mathlib at
      Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:170 (`preNormEDS'_three ..`)
[A] Lean-Finder / [B] Loogle / [C] LeanSearch  → n/a (a verbatim source grep already resolves it)
```

Searched for: the project's current form. The mathlib form is **identical** (same name,
same namespace, same statement, same `@[simp]`, same proof `by rw [preNormEDS']`).

Mathlib lines 122–158 (`def preNormEDS'` plus the five base-value lemmas) match the project's
lines 708–757 character-for-character; the only divergence in the *surrounding* code is the
recursion's termination scaffolding (mathlib: `let m := n/2`; fork: `letI m := n/2` with
explicit `have h1..h4`), which does not touch `preNormEDS'_three` — its statement and proof
are independent of that cosmetic change.

Concluded: **found in mathlib as `preNormEDS'_three`; identical form** (the verbatim source
appears at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:153`).

### Composition check (Phase 6)

#### Call sites — `preNormEDS'_three`
Internal use count (this project, excluding the declaring file and the duplicate
`EllipticDivisibilitySequenceOriginal.lean`): **2**

| Caller file:line                                   | Usage pattern                                      |
|----------------------------------------------------|----------------------------------------------------|
| `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:93`            | `preNormEDS'_three ..`                  |
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1126`| `| three => rw [preNormEDS'_three, preNormEDS'_three]` |

(There is also a second forked copy of the identical lemma in the same project at
`EllipticDivisibilitySequenceOriginal.lean:705`, used at `:1073` — an intra-project
duplicate of the duplicate.) These call sites **mirror mathlib's own** use of
`preNormEDS'_three` at `DivisionPolynomial/Basic.lean:170` — i.e. the project is re-deriving
locally exactly what mathlib already provides and already consumes.

Inline-derivation grep: the lemma is the canonical unfold; consumers use it by name (no inline
re-derivations bypassing it).

#### Composition
n/a in the usual sense — this isn't a "compose from mathlib primitives" case; mathlib has the
**exact lemma**. Conclusion: **NO-mathlib-has-it** (not NO-composable).

### Verdict block (Phase 7)

## Verdict: `preNormEDS'_three`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): n/a — short-circuited by an exact mathlib match.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — signature identical to mathlib's (`CommRing` minimal).
- Mathlib search (Phase 5): found in mathlib as `preNormEDS'_three`; **identical form**, `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:153`.
- Composition check (Phase 6): NO-mathlib-has-it (verbatim lemma exists; not a composition case).

**Rationale.**
`preNormEDS'_three` is one of five base-value unfold lemmas for the recursive normalised-EDS
auxiliary sequence `preNormEDS'`. The entire `preNormEDS'`/`preNormEDS`/`normEDS` development
in this project file is a **fork of mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence`**
(the task brief flags exactly this). Mathlib contains `def preNormEDS'` and the lemma
`preNormEDS'_three : preNormEDS' b c d 3 = c := by rw [preNormEDS']` at lines 124 and 153 of
that module — same top-level namespace, same `@[simp]`, same statement, same proof as the
project's `EllipticDivisibilitySequence.lean:751`. Mathlib even *uses* this lemma itself
(`DivisionPolynomial/Basic.lean:170`), and the project's own call sites
(`DivisionPolynomial.lean:93`, `:1126`) mirror that usage. There is nothing to upstream:
mathlib has it, verbatim, at full generality.

**WHY not (refactor-actionable).**
Mathlib already has this lemma in identical form. Once the project re-bases its EDS work onto
mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence` (rather than carrying a forked
copy), `preNormEDS'_three` should simply be **deleted** and references resolved to the mathlib
lemma of the same name — no statement change, no argument-order change (signatures are identical).

Existing mathlib decl:        `preNormEDS'_three`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:153`
Our form follows in ≤1 line:  it *is* the same line — `example : preNormEDS' b c d 3 = c := preNormEDS'_three ..` (mathlib's).
Call sites in our project:    K = 2 (live file) + 2 (the `…Original.lean` duplicate)
Refactor plan:
  - This is a glue lemma; it inherits the verdict of the parent def `preNormEDS'`. The real
    unit of work is the **fork as a whole**, not this lemma in isolation — `preNormEDS'_three`
    cannot be deleted while the project keeps its own `def preNormEDS'` (the two would otherwise
    be the same name in the same namespace). So: handle this lemma together with the parent def
    `preNormEDS'` and its siblings `preNormEDS'_{zero,one,two,four,even,odd}`.
  - When the EDS fork is retired in favour of `import Mathlib.NumberTheory.EllipticDivisibilitySequence`:
    delete the project's `def preNormEDS'` + the five base-value lemmas; the two call sites
    (`DivisionPolynomial.lean:93`, `EllipticDivisibilitySequence.lean:1126`) then resolve against
    the mathlib lemma unchanged (identical name and signature). Also drop the duplicate copy in
    `EllipticDivisibilitySequenceOriginal.lean`.
  - If the fork must persist (e.g. the project genuinely needs the alternative termination
    scaffolding or the extra `EllSequence` framework that mathlib lacks), then keep the lemma but
    record it as a known intentional duplication of mathlib — it is still **not** a mathlib
    contribution.

**Next action:** do **not** upstream. Fold this lemma into the fork-retirement / dedup ticket
for the whole `preNormEDS'` block (parent def + `preNormEDS'_{zero,one,two,three,four,even,odd}`)
against `Mathlib.NumberTheory.EllipticDivisibilitySequence`; delete on re-base, or mark as an
intentional fork duplicate if the fork is kept.

---

## Next step

Do not upstream. NO-mathlib-has-it: mathlib has `preNormEDS'_three` verbatim at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:153`. Delete it (with the rest of the
forked `preNormEDS'` block) when the project re-bases onto mathlib's EDS module; until then it is
an intentional fork duplicate, never a mathlib PR.
