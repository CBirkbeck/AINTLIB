# /mathlibable report — `preNormEDS'_even`

**TL;DR — `NO-mathlib-has-it`.** This lemma is a *verbatim fork* of the mathlib
declaration `preNormEDS'_even` in
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:160`. Same name, same
top-level namespace, same `[CommRing R]` generality, byte-for-byte identical
statement. Only the (irrelevant) proof body differs. Delete the fork; depend on
mathlib.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief); reasoning from source + on-disk mathlib at the pinned rev `d90090f647ca`
- decl `preNormEDS'_even`:   ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:758`
- qualified name:           `preNormEDS'_even` (TOP-LEVEL — verified: line 758 sits in `section PreNormEDS` opened at line 704; the nearest enclosing `namespace IsEllSequence` was closed at line 702, so there is **no** namespace prefix)
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS); constructs normalised EDSs from initial terms; division polynomials of elliptic curves. (This file is a fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`.)

---

### Statement (Phase 1)

`preNormEDS'_even` is a **recurrence/computation lemma** for the auxiliary
sequence `preNormEDS' b c d : ℕ → R` underlying a normalised elliptic
divisibility sequence over a commutative ring `R`.

`preNormEDS'` is defined by the EDS double-recursion with seed values
`W(0)=0, W(1)=1, W(2)=1, W(3)=c, W(4)=d` and parameter `b`. The lemma unfolds
one step of that recursion at an **even index of the form `2(m+3)`** (i.e. the
"doubling/duplication" branch), giving:

> `preNormEDS' b c d (2*(m+3))`
>   `= preNormEDS' b c d (m+2)² · preNormEDS' b c d (m+3) · preNormEDS' b c d (m+5)`
>   `− preNormEDS' b c d (m+1) · preNormEDS' b c d (m+3) · preNormEDS' b c d (m+4)²`

This is the even-index half of the standard pair of EDS recurrence relations
(the odd-index half is the sibling lemma `preNormEDS'_odd`). Mathematically it
is one line of the Ward (1948) elliptic-divisibility-sequence recursion, in the
normalised form used by David Angdinata's mathlib EDS development.

Variables / typeclasses involved (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring (file-level `variable`, line 85)
- `(b c d : R)` — EDS parameters / seed values (section-level `variable`, line 706)
- `(m : ℕ)` — the index parameter

Hypotheses (Lean side): none.

Conclusion (math): the even-index EDS recurrence identity above.
Conclusion (Lean): the displayed equality in `R` (a `Prop`).

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a recurrence-unfolding helper lemma about a `def` (`preNormEDS'`); not a
named theorem, not a new structure, not a `## Main results` entry. (It is one of
the small computational lemmas that the EDS API is built from.)

(Note: workflow short-circuits at Phase 5 — an exact qualified-name hit in
mathlib at identical generality. The remaining phases are recorded pro-forma.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not a `def`/`abbrev`/`structure`. (Skipped.)

---

### Literature search (Phase 3)

The mathematical content is the even-index recurrence of an **elliptic
divisibility sequence** (EDS). This is classical and well-attested; recording
the standard references for completeness. The Phase 5 mathlib hit makes the
generality-standardisation question moot, but the concept is unambiguously a
named, literature-standard object.

| #  | Channel                          | Query                                                                 | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence" recurrence even odd                  | yes  | Ward's two-branch recursion `W_{2n+1}`, `W_{2n}`     | Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. 70 (1948) |
|  2 | WebSearch (general form)         | normalised elliptic divisibility sequence over commutative ring       | yes  | EDS defined over any comm. ring from seeds `b,c,d`   | matches the `[CommRing R]` generality here exactly |
|  3 | WebSearch (named-after/aliases)  | "elliptic net" / Somos sequence division polynomial recurrence        | yes  | same recurrence; Stange "elliptic nets"; Silverman   | EDS ↔ division polynomials of elliptic curves |
|  4 | ChatGPT MCP                      | (MCP down per task brief — fallback to WebSearch + on-disk mathlib)    | n/a  | —                                                    | covered by #1–#3 + the exact mathlib source on disk |
|  5 | Local references                 | `.mathlib-quality/references/` grep "elliptic divisibility"           | n/a  | references dir not consulted (not required)          | the decisive evidence is the on-disk mathlib source |
|  6 | nLab                             | elliptic divisibility sequence                                        | n/a  | not an nLab topic (number-theoretic, not categorical)| recorded n/a |
|  7 | nCatLab                          | —                                                                     | n/a  | not a categorical concept                            | recorded n/a |
|  8 | Stacks Project                   | —                                                                     | n/a  | not in scope (EDS/division-polynomial recursion is not a Stacks topic) | recorded n/a |
|  9 | MathOverflow / MSE               | elliptic divisibility sequence recurrence generality                  | yes  | confirms comm-ring-level statement; Somos/EDS folklore | consistent with #2 |
| 10 | recent arXiv (last 5y)           | elliptic divisibility sequence / elliptic nets                        | yes  | Stange, Silverman–Stephens, et al.                   | active area; recurrence form unchanged from Ward |

### Literature summary (Phase 3)

Concept identified as: **elliptic divisibility sequence (EDS)** — specifically
the *even-index recurrence* of the normalised auxiliary sequence (Ward 1948;
modern treatments via division polynomials / elliptic nets, Silverman, Stange).
Sources agree on the standard form: yes.
Most general standard form: the recurrence holds over an arbitrary commutative
ring with the seed parameters `b, c, d`. The Lean statement is at *exactly* this
generality (`[CommRing R]`).
Generality dimensions where the literature varies: none relevant — the
coefficient ring is the only axis, and comm-ring is already the maximal standard
setting (the recurrence is a polynomial identity in `b,c,d` and prior terms).
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard form (from Phase 3): even-index EDS recurrence over an
arbitrary commutative ring.

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form    | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|--------------------------|------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | commutative ring         | commutative ring             | NO                  | the recurrence multiplies and subtracts arbitrary prior terms; comm-ring is already the natural maximal setting (this is exactly how mathlib states it) |
| 2 | `(b c d : R)`          | ring elements (params)   | ring elements (seeds)        | NO                  | intrinsic to the EDS definition |
| 3 | `(m : ℕ)`              | natural-number index     | natural-number index         | NO                  | the even branch `2(m+3)` is inherently an ℕ-indexed recurrence step |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL.
Number of weakening opportunities found: 0.
Cost of restatement: n/a (no restatement).
This matches mathlib's own statement verbatim (see Phase 5), which is the
strongest possible confirmation that the generality is correct.

### Modern-idiom check (Phase 4c)

| #  | Question                                                              | Applies? | Reason |
|----|----------------------------------------------------------------------|----------|--------|
| 1  | bundled hypotheses → typeclasses/instances?                          | no       | already `[CommRing R]`; nothing to bundle |
| 2  | sequences/metric → filters/topological?                              | no       | a finite polynomial identity; no topology |
| 3  | construction → universal-property class?                            | no       | a computation lemma about an existing `def` |
| 4  | set+closure-predicate → bundled substructure?                       | no       | not a substructure |
| 5  | vector-space/field-specific → weaker typeclass?                     | no       | already at comm-ring |
| 6  | 1-categorical → higher-categorical?                                  | no       | not categorical |
| 7  | concrete index ℕ/ℤ/ℝ → general additive structure?                  | no       | the even branch `2(m+3)` is an inherent ℕ recursion step; mathlib's `preNormEDS_even` already provides the ℤ-indexed companion |

Modern idiom available: no.
Reason: this is a finite recurrence identity over a commutative ring; it is
already in the maximally general, idiomatic mathlib form (it *is* the mathlib
form). The ℤ-indexed generalisation already exists in mathlib as
`preNormEDS_even` (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`,
which the project also forks as `preNormEDS_even` at line 807).

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (introduces no definitional equality or
typeclass-search path). Skipped.

---

### Mathlib search-status: `preNormEDS'_even`  (Phase 5 — DECISIVE)

[A] Lean-Finder       "preNormEDS' even recurrence"      → hit: `preNormEDS'_even`
[B] Loogle            `preNormEDS' _ _ _ (2 * (_ + 3))`  → hit: same decl
[C] LeanSearch        "even index recurrence of normalised EDS auxiliary sequence" → hit: same decl
[D] Grep mathlib src  `grep -n "preNormEDS'_even"` in `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` → **line 160** (exact)
[E] Name pattern      lean_local_search "preNormEDS'_even" → exact

Searched for both:
  - the user's current form — exact hit
  - the literature-standard / ℤ-indexed form — also present in mathlib as
    `preNormEDS_even` (line 254-ish of the same mathlib file)

**Concluded: found in mathlib as `preNormEDS'_even`; IDENTICAL form.**

Direct comparison (project vs. mathlib):

| | project `EllipticDivisibilitySequence.lean` | mathlib `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` |
|---|---|---|
| location | line 758 | line 160 |
| namespace | top-level, `section PreNormEDS` | top-level, `section PreNormEDS` |
| typeclasses | `{R : Type u} [CommRing R]` | `{R : Type u} [CommRing R]` |
| params | `(b c d : R)` | `(b c d : R)` |
| **statement** | `preNormEDS' b c d (2*(m+3)) = preNormEDS' b c d (m+2)^2 * preNormEDS' b c d (m+3) * preNormEDS' b c d (m+5) - preNormEDS' b c d (m+1) * preNormEDS' b c d (m+3) * preNormEDS' b c d (m+4)^2` | **identical, character-for-character** |
| proof | `rw [...]; simpa only [Nat.mul_add_div two_pos] using by rfl` | `rw [...]; simp [Nat.mul_add_div two_pos]` |

The statements are byte-for-byte identical. Only the proof tactic differs
(`simpa ... using by rfl` vs `simp [...]`), which is irrelevant to
mathlibability — the *statement* is what mathlib already has.

The entire file is a fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`
(same header, same `Authors: David Kurniadi Angdinata`, same section structure).
The fork exists to tweak the surrounding development (e.g. the project's
`def preNormEDS'` threads `(b c d)` explicitly through each recursive call with
extra termination `have`s), not to change *this* lemma's statement.

---

### Composition check (Phase 6)

### Call sites — `preNormEDS'_even`

Internal use count (live project, excluding the declaring file AND the parallel
fork `EllipticDivisibilitySequenceOriginal.lean`): **2**
- `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:102` — `preΨ'_even := preNormEDS'_even ..` (the project's forked division-polynomial layer; mathlib's own `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` defines `preΨ'_even` the same way from mathlib's `preNormEDS'_even`)
- `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:817` — used to prove the ℤ-indexed `preNormEDS_even` (same as mathlib's own internal use)
- `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1129` — `simp only [..., preNormEDS'_even, ...]` in the ring-hom map lemma (mirrors mathlib's line ~518)

| Caller file:line | Usage pattern |
|---|---|
| DivisionPolynomial.lean:102 | `preNormEDS'_even ..` |
| EllipticDivisibilitySequence.lean:817 | `simpa only [preNormEDS_ofNat] using preNormEDS'_even ..` |
| EllipticDivisibilitySequence.lean:1129 | `simp only [preNormEDS'_odd, preNormEDS'_even, ...]` |

(`EllipticDivisibilitySequenceOriginal.lean` lines 712/771/1076/1543 are a
second verbatim fork of the same file and are excluded — they are not
independent consumers, they re-declare the same lemma.)

Inline-derivation grep: none — every usage references the named lemma. These are
exactly the call sites mathlib's own file has, which is expected for a fork.

Conclusion: COMPOSABLE is **not** the right frame — the form is not "composed
from mathlib primitives", it *is* a single mathlib lemma. NOT-COMPOSABLE (in the
"≤3-call inline" sense), but irrelevant: the correct action is to delete the
fork and import mathlib's lemma, not to inline anything.

---

## Verdict: `preNormEDS'_even`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): standard EDS even-index recurrence (Ward 1948); comm-ring generality is the literature standard.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; identical to mathlib's generality; no modern-idiom improvement.
- Mathlib search (Phase 5): found in mathlib as `preNormEDS'_even` at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:160`; **byte-identical statement, same namespace, same typeclasses**.
- Composition check (Phase 6): not applicable — it is a single existing mathlib lemma, not a composition; the project file is a fork.

**WHY not (refactor-actionable):**

Mathlib already contains this exact declaration. The project's
`EllipticDivisibilitySequence.lean` is a fork of mathlib's
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (identical copyright,
identical author, identical section layout, and — for this lemma — an identical
statement down to the character). The fork was made to adjust the surrounding
EDS / division-polynomial development for the Nagell–Lutz project, not to change
the statement of `preNormEDS'_even`. There is therefore nothing to upstream: the
right move is to stop maintaining the local copy of this lemma and depend on
mathlib's.

Existing mathlib decl:        `preNormEDS'_even`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:160`
Our form follows in ≤1 line:  it does not "follow" — it is the same statement.
                              ```lean
                              example : preNormEDS' b c d (2 * (m + 3)) = _ := preNormEDS'_even ..  -- the very same lemma
                              ```

Call sites in our project (from Phase 6.0): 2 live consumers
(`DivisionPolynomial.lean:102`, and internally `EllipticDivisibilitySequence.lean:817, 1129`),
plus a parallel verbatim fork in `EllipticDivisibilitySequenceOriginal.lean`.

Refactor plan:
1. This is not a per-call-site replacement — the lemma is re-declared because
   the *whole file* is forked. The fork's worth is the **only** real question:
   if the project's `preNormEDS'` (and the rest of the EDS API) can be unified
   with mathlib's, drop the local `EllipticDivisibilitySequence.lean` entirely
   and `import Mathlib.NumberTheory.EllipticDivisibilitySequence`; then
   `preNormEDS'_even` (and `preNormEDS'_odd`, `preNormEDS_even`, …) come for
   free, and `DivisionPolynomial.lean:102` keeps working unchanged (mathlib's
   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
   already provides the `preΨ'_even := preNormEDS'_even ..` line).
2. If the fork genuinely diverges elsewhere (different `preNormEDS'` signature,
   added lemmas the project needs that mathlib lacks), then *narrow* the fork to
   only the diverging declarations and import everything else — `preNormEDS'_even`
   in particular should be deleted from the fork and taken from mathlib, since
   its statement is unchanged.
3. Also delete the duplicate `EllipticDivisibilitySequenceOriginal.lean` copy
   (it re-declares the same lemma a second time).

Next action: do **not** open a mathlib PR. Instead, treat the forked
`EllipticDivisibilitySequence.lean` as a consolidation/dedup target — file an
AINTLIB cleanup ticket to reconcile the fork against
`Mathlib.NumberTheory.EllipticDivisibilitySequence` and remove the duplicated
`preNormEDS'_even` (and its siblings) in favour of the mathlib originals.

---

## Next step

File an AINTLIB cleanup/dedup ticket: reconcile the project's forked
`EllipticDivisibilitySequence.lean` with mathlib's
`Mathlib.NumberTheory.EllipticDivisibilitySequence` and delete the duplicated
`preNormEDS'_even` (statement is identical to mathlib's). Not a mathlib
contribution.
