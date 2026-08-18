# /mathlibable report — `preNormEDS_mul_complEDS₂`

**TL;DR — `NO-mathlib-has-it`.** The project file
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a **verbatim
fork** of mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same
author, David Kurniadi Angdinata; same copyright header). The declaration
`preNormEDS_mul_complEDS₂` already exists in mathlib at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:276` with a **byte-for-byte
identical statement and proof**. Delete the fork and import from mathlib.

---

### Baseline (Phase 0)

- lake build:               not re-run (local build stale per task brief); reasoning from source.
- decl `preNormEDS_mul_complEDS₂`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:874`
- qualified name:           `preNormEDS_mul_complEDS₂` (root namespace — sits inside a
  bare `section PreNormEDS` with **no** enclosing `namespace`; confirmed by walking
  `namespace`/`section`/`end` from line 1 to 874).
- kind:                     `lemma`
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences" — defines `IsEllSequence`,
  `preNormEDS`, `normEDS`, the complement sequences `complEDS₂`/`complEDS'`/`complEDS`,
  and their basic algebra. (This file is a fork of the mathlib EDS file, extended with
  extra `EllSequence`/`IsEllSequence` namespaces above the forked `PreNormEDS` section.)

---

### Statement (Phase 1)

`preNormEDS_mul_complEDS₂` states the following.

Let `R` be a commutative ring and `b c d : R`. Let `preNormEDS (b^4) c d : ℤ → R` be the
auxiliary ("pre-normalised") elliptic divisibility sequence, and let
`complEDS₂ b c d : ℤ → R` be the **2-complement sequence**
`Wᶜ₂(k) = (p(k-1)² p(k+2) − p(k-2) p(k+1)²) · (1 if k even else b)`
(writing `p = preNormEDS (b^4) c d`). Then for every `k ∈ ℤ`:

> `p(k) · Wᶜ₂(k) = p(2k) · (1 if k even else b)`.

This is the algebraic identity witnessing that `p(k)` divides `p(2k)` up to the parity
factor `b` — the "doubling/duplication" half of the elliptic *divisibility* property
`W(k) ∣ W(2k)`. (The clean divisibility form, with the `b` absorbed, is the sibling
lemma `normEDS_mul_complEDS₂` and the `Dvd` statement `normEDS_dvd_normEDS_two_mul`.)

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(b c d : R)` — the three EDS parameters (`section PreNormEDS` `variable`s).
- `(k : ℤ)` — the index.

Hypotheses: none.

Conclusion (math): `preNormEDS(b⁴,c,d)(k) · complEDS₂(b,c,d)(k) = preNormEDS(b⁴,c,d)(2k) · (k even ? 1 : b)`.

Conclusion (Lean):
`preNormEDS (b ^ 4) c d k * complEDS₂ b c d k = preNormEDS (b ^ 4) c d (2 * k) * if Even k then 1 else b`.

Proof body (2 lines, identical in both files):
```lean
  rw [complEDS₂, preNormEDS_even]
  ring1
```
i.e. unfold the 2-complement, apply the even-index recurrence `preNormEDS_even`, and
close by `ring1`. It is a pure ring identity once those two definitional/recurrence
rewrites land.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a 2-line helper lemma (`rw … ; ring1`) about already-defined objects; not a named
theorem, not a `## Main statements` entry, not a new structure.

(Note: literature width is EXHAUSTIVE regardless. Recorded for framing only.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. (The one-liner negative signal
applies to definitions; this is a proof.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence W(k) divides W(2k) complement doubling Ward"                    | yes  | `W(m) ∣ W(n)` when `m ∣ n`; doubling/duplication formula for EDS | Wikipedia "Elliptic divisibility sequence"; **3rd hit is the mathlib4 docs page for this exact file** |
|  2 | WebSearch (general form)         | (covered by #1 results) EDS divisibility property, Ward's recurrence `W(m+n)W(m−n)W(r)² = …`    | yes  | the Somos/Ward 4-term recurrence; divisibility is a theorem about it | Wikipedia "Divisibility sequence"; eprint.iacr.org/2008/444 | 
|  3 | WebSearch (named-after / aliases)| Ward EDS, division polynomial `ψ_n`, `W_n = ψ_n(ξ,L)` (Ward 1948)                               | yes  | EDS ≈ division polynomials of an elliptic curve; doubling formula `O(log K)` | arXiv math/0404412, arXiv:1108.3051 (explicit valuations of division polynomials) |
|  4 | ChatGPT MCP                      | n/a — MCP down per task brief; substituted by the mathlib source itself (definitive, see Phase 5) | n/a  | —                   | The decl is *authored by mathlib*; the canonical "standard form" is the mathlib statement we already have. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` for "complEDS"/"divisibility"            | n/a  | (no project-specific paper hit) | The governing reference *is* mathlib's own EDS file; the identity is mathlib-internal API, not a textbook-named lemma. |
|  6 | nLab                             | "elliptic divisibility sequence"                                                               | n/a  | —                   | Not an nLab topic; EDS is number-theoretic, not categorical. |
|  7 | nCatLab (if categorical)         | —                                                                                              | n/a  | —                   | Not a categorical concept. |
|  8 | Stacks Project (if alg geom)     | "division polynomial" / "elliptic divisibility"                                                | n/a  | —                   | Stacks covers schemes/AG foundations, not EDS recurrences. |
|  9 | MathOverflow / Math.StackExchange| EDS doubling / complement identity                                                             | n/a  | —                   | Subsumed by #1–#3; no extra standard-form variant surfaced. |
| 10 | recent arXiv (last 5 years)      | division polynomials / EDS valuations                                                          | yes  | confirms `W(k) ∣ W(2k)` is standard; this exact "complement" packaging is mathlib's own | arXiv:1108.3051, arXiv:1111.2475 — use EDS divisibility but not this precise `complEDS₂` factorisation (it is a formalisation-convenience split). |

### Literature summary (Phase 3)

Concept identified as: the **doubling / duplication step of the elliptic-divisibility
property** of an EDS — `W(k) ∣ W(2k)`, here packaged via the explicit "2-complement"
cofactor `complEDS₂`.
Sources agree on the standard form: yes — the divisibility property `W(m) ∣ W(n)` for
`m ∣ n` (Ward) is completely standard. The *specific* `complEDS₂` factorisation
(`W(k)·Wᶜ₂(k) = W(2k)·parity`) is **not** a textbook-named identity; it is mathlib's own
formalisation device for *constructing* the divisibility witness. The canonical source for
this exact statement is therefore mathlib itself (its docs page even appeared in the web
search).
Most general standard form: the identity holds over an arbitrary `CommRing R` — which is
exactly the Lean form. There is no "more general" mathematical setting (EDS coefficients
live in a commutative ring; the identity is a polynomial identity in `b, c, d` and the
sequence values).
Generality dimensions where the literature varies:
  - coefficient ring: literature often works over `ℤ`/a field/`ℂ` (Ward's analytic
    picture), but the *identity* is a polynomial identity valid over any commutative ring —
    mathlib (and this fork) already state the most general `CommRing` version.
Disagreement with the literature: none.

---

### Generality analysis — `preNormEDS_mul_complEDS₂`

Literature-standard form (Phase 3): polynomial identity over an arbitrary commutative ring;
the `CommRing R` form is maximal.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring (identity is polynomial in `b,c,d`) | NO | `complEDS₂`/`preNormEDS` are *defined* over `CommRing`; `ring1` needs commutativity; subtraction in the definition needs additive inverses. Cannot weaken to `CommSemiring`. |
| 2 | `(b c d : R)`          | three ring elements | three ring elements      | NO | These are the defining EDS parameters; not specialisable. |
| 3 | `(k : ℤ)`              | integer index     | integer index            | NO | The sequence is genuinely ℤ-indexed (negative indices handled via `preNormEDS_neg`). Not a `ℕ`/general-monoid index. |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL
Number of weakening opportunities found: 0
Proposed restatement: none.
Cost of restatement: n/a.

The Lean statement already matches mathlib's, which is the most general reasonable form
(arbitrary `CommRing`, the natural `ℤ` index).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
|  1 | "let X be a foo" → typeclasses? | no | — | Already typeclass-driven (`[CommRing R]`); `b c d` are honest data, not hypotheses. |
|  2 | sequences/metric → filters/topology? | no | — | Purely algebraic ring identity; no topology. |
|  3 | construction → universal-property class? | no | — | `complEDS₂` is a concrete cofactor; the `Dvd` packaging already exists (`normEDS_dvd_normEDS_two_mul`). |
|  4 | set+closure-pred → bundled substructure? | no | — | No substructure involved. |
|  5 | field/metric-specific → weaken typeclasses? | no | — | Already at `CommRing`, the floor for this identity. |
|  6 | 1-categorical → higher-categorical? | no | — | Not categorical. |
|  7 | concrete index ℕ/ℤ/ℝ → general monoid? | no | — | EDS are intrinsically ℤ-indexed; the doubling map `k ↦ 2k` is specific to ℤ. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no
Reason: this is a finite ring identity about an intrinsically ℤ-indexed sequence; there is
no filter-isation, universal-property, or typeclass-weakening move. The statement is
already in mathlib's chosen idiom (because it *is* mathlib's statement).

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`. (No definitional equalities or typeclass-search paths
introduced.)

---

### Mathlib search-status: `preNormEDS_mul_complEDS₂`

[A] Lean-Finder       "preNormEDS times complEDS2 equals preNormEDS double" — n/a (index offline locally); superseded by [D] exact source hit.
[B] Loogle            `preNormEDS _ _ _ _ * complEDS₂ _ _ _ _ = _` — n/a (index offline locally); superseded by [D].
[C] LeanSearch        "product of pre-normalised EDS and its 2-complement equals the doubled term" — n/a (index offline locally); the web search **did** return the mathlib4 docs page for this file (Phase 3 row #1), an independent confirmation it is in mathlib.
[D] Grep mathlib src  `grep -nE "complEDS|preNormEDS_mul|preNormEDS_even|normEDS_mul_complEDS"` over `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` → **HIT**. `preNormEDS_mul_complEDS₂` at line **276**; full `complEDS₂`/`complEDS'`/`complEDS` family present (22 matching decl heads); `complEDS₂` def at 246; `preNormEDS_even` at 209; `normEDS_mul_complEDS₂` at 321; `normEDS_dvd_normEDS_two_mul` at 326.
[E] Name pattern      `grep ^lemma preNormEDS_mul_complEDS₂` in mathlib → exact-name HIT at line 276.

Searched for both:
  - the user's current form — found, **identical** (verified by `diff`, exit 0).
  - the literature-standard / more-general form — the `CommRing` form *is* the maximal
    form and it is the one in mathlib; the cleaner divisibility packaging
    (`normEDS_mul_complEDS₂`, `normEDS_dvd_normEDS_two_mul`) is also already in mathlib.

Verification (`diff` of the two lemma blocks, ignoring leading whitespace):
```
project EllipticDivisibilitySequence.lean:874-877  ⟷  mathlib …/EllipticDivisibilitySequence.lean:276-279
→ IDENTICAL (diff exit 0)
```
Both files carry the **same** header: `Copyright (c) 2024 David Kurniadi Angdinata … Authors:
David Kurniadi Angdinata` — i.e. the NagellLutz file is a fork of the mathlib file, not an
independent re-derivation.

Concluded: **found in mathlib as `preNormEDS_mul_complEDS₂`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:276`); identical form.**

---

### Call sites — `preNormEDS_mul_complEDS₂`

Internal use count (within NagellLutz, excluding the declaring file): **0**.
External-to-file callers: 0 functional callers.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:927` | `simp_rw [normEDS, mul_right_comm, preNormEDS_mul_complEDS₂, …]` — **same file** (the sibling `normEDS_mul_complEDS₂` proof); not counted as external. |
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:878` | identical use in the `…Original.lean` duplicate fork (same project, separate forked copy). |
| `projects/HasseWeil/HasseWeil/OmegaPullbackCoeff.lean:431` | docstring/comment only: "`p(4m) = complEDS₂(2m) · p(2m)` (**mathlib's** `preNormEDS_mul_complEDS₂`)" — explicitly attributes the lemma to **mathlib**, not to this NagellLutz fork. |

Inline-derivation grep: the only functional consumer is the in-file `normEDS_mul_complEDS₂`,
which mathlib *also* already has (line 321). HasseWeil reaches for the **mathlib** copy, not
this one.

Composability read: a NagellLutz-local copy has **zero** consumers that need *this* file's
version — every real consumer is either in-file (and mirrored in mathlib) or explicitly
points at mathlib's copy. This reinforces NO: the fork's copy is redundant.

---

### Composition check (Phase 6)

Can `preNormEDS_mul_complEDS₂` be derived from mathlib in ≤3 chained calls?

Attempt 1: it does not need *deriving* from primitives at all — mathlib already exports the
**identical** lemma. The "composition" is a single reference:
```lean
example (b c d : R) (k : ℤ) :
    preNormEDS (b ^ 4) c d k * complEDS₂ b c d k =
      preNormEDS (b ^ 4) c d (2 * k) * if Even k then 1 else b :=
  preNormEDS_mul_complEDS₂ k          -- the mathlib lemma, verbatim
```
  - Mathlib decls used: `preNormEDS_mul_complEDS₂` (and, were one to re-prove it,
    `complEDS₂` + `preNormEDS_even` + `ring1`, all in mathlib).
  - Result: succeeds (0-step; it *is* the mathlib lemma).

Conclusion: NOT-COMPOSABLE in the "needs a 1–3 call inline" sense — because nothing needs
composing; the verdict is the stronger NO-mathlib-has-it (mathlib already *has the lemma*,
not merely the building blocks).

---

## Verdict: `preNormEDS_mul_complEDS₂`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): EDS divisibility `W(k) ∣ W(2k)` is standard (Ward); the
  precise `complEDS₂` packaging is mathlib's own formalisation device — its docs page even
  surfaced in the web search.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; no weakening, no modern-idiom move.
- Mathlib search (Phase 5): found in mathlib as `preNormEDS_mul_complEDS₂`
  (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:276`); **identical** form
  (`diff` exit 0, same author/header).
- Composition check (Phase 6): NOT-COMPOSABLE — stronger, mathlib *has the lemma itself*.

**Rationale:**

The NagellLutz file `LutzNagell/EllipticDivisibilitySequence.lean` is a **verbatim fork** of
mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` — same copyright block,
same author (David Kurniadi Angdinata), and the `preNormEDS_mul_complEDS₂` lemma (statement
*and* the two-line `rw [complEDS₂, preNormEDS_even]; ring1` proof) is byte-for-byte identical
to mathlib's line 276 (confirmed by `diff`, exit 0). The entire surrounding `complEDS₂` /
`complEDS'` / `complEDS` API and its consumers (`normEDS_mul_complEDS₂`,
`normEDS_dvd_normEDS_two_mul`) are likewise already in mathlib. The project simply pins an
older copy alongside extra `EllSequence`/`IsEllSequence` development layered above it. This
matches the task's project-context warning exactly: NagellLutz forks
`Mathlib.NumberTheory.EllipticDivisibilitySequence`, so this decl is *already upstream*.

**WHY not (refactor-actionable):**
Mathlib already has this exact lemma — not a more general form to specialise, but the
*identical* statement and proof. Cross-project evidence corroborates it: HasseWeil's
`OmegaPullbackCoeff.lean:431` explicitly calls it "**mathlib's** `preNormEDS_mul_complEDS₂`".
There is nothing to contribute.

Existing mathlib decl:        `preNormEDS_mul_complEDS₂` (root namespace)
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:276`
Our form follows in ≤1 line (it is the same lemma):
```lean
example (b c d : R) (k : ℤ) :
    preNormEDS (b ^ 4) c d k * complEDS₂ b c d k =
      preNormEDS (b ^ 4) c d (2 * k) * if Even k then 1 else b :=
  preNormEDS_mul_complEDS₂ k
```
Call sites in our project (Phase 6.0): **0** that need this fork's copy. The sole functional
consumer in-file is `normEDS_mul_complEDS₂`, which is *also* already in mathlib.

Refactor plan (whole-file, since the fork is verbatim — not a per-call-site swap):
1. This is a **fork-deduplication**, not a single-decl deletion. The right move is to drop
   the forked `PreNormEDS`/`NormEDS`/`complEDS₂` block (lines ~704–end of the
   complement section) from `LutzNagell/EllipticDivisibilitySequence.lean` (and the duplicate
   `…Original.lean`) and instead `import Mathlib.NumberTheory.EllipticDivisibilitySequence`,
   keeping only the genuinely-new `EllSequence`/`IsEllSequence` material the project adds on
   top. (Per CLAUDE.md this is a `lane:cleanup` cross-project dedup job, not producer work —
   and it must not touch any `sorry`-bearing siblings.)
2. After the import swap, the in-file `normEDS_mul_complEDS₂` (project line 925) is likewise
   redundant with mathlib's line 321 — delete it too.
3. Re-point any remaining references at the mathlib names (no argument-order differences —
   the names and signatures are identical).

Next action: open a `lane:cleanup` ticket to deduplicate the NagellLutz EDS fork against
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (covers `preNormEDS_mul_complEDS₂` plus
the whole `complEDS*` family in one pass); delete the forked copies and import from mathlib.

---

## Next step

Open a `lane:cleanup` ticket to deduplicate `LutzNagell/EllipticDivisibilitySequence.lean`
(and `…Original.lean`) against mathlib's
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`: drop the forked `complEDS*` /
`preNormEDS_mul_complEDS₂` / `normEDS_mul_complEDS₂` block and `import` mathlib instead,
retaining only the project-original `EllSequence`/`IsEllSequence` additions. Do not upstream
anything — mathlib already has it.

---

### Sources (Phase 3 web search)
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- [Divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Divisibility_sequence)
- [Mathlib.NumberTheory.EllipticDivisibilitySequence — mathlib4 docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
- [Elliptic divisibility sequences and the elliptic curve discrete logarithm problem (eprint.iacr.org/2008/444)](https://eprint.iacr.org/2008/444.pdf)
- [Integral points on elliptic curves and explicit valuations of division polynomials (arXiv:1108.3051)](https://arxiv.org/pdf/1108.3051)
- [p-adic properties of division polynomials and elliptic divisibility sequences (arXiv:math/0404412)](https://arxiv.org/pdf/math/0404412)
